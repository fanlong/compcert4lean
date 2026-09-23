import CompCert4Lean.Allocator.Analyses

namespace CompCert4Lean.Allocator

open Common.AST Backend.Locations X86.Machregs Foundation.Numbers.Rocq.Coq

structure ColoringState where
  graph : Interference
  parents : Array Nat
  active : IndexSet
  simplify : IndexSet := {}
  freeze : IndexSet := {}
  spill : IndexSet := {}
  moves : Array (Nat × Nat) := #[]
  nodeMoves : Array IndexSet
  workMoves : IndexSet := {}
  activeMoves : IndexSet := {}
  stack : List Nat := []
  coalesced : Nat := 0
  degrees : Array Nat := #[]

def nodeClass (function : XFunction) (graph : Interference) (index : Nat) : Nat :=
  match (variableInfo function index).fixed with
  | some (.R register) => machineClass register
  | _ => if (graph.costs[index]?.getD {}).stackOnly then 2
      else registerClass (variableInfo function index).type

def nodeCapacity (context : AllocationContext) (function : XFunction)
    (state : ColoringState) (index : Nat) : Nat :=
  let classId := nodeClass function state.graph index
  if classId == 2 then 0 else (registerPool context classId).length

def precolored (function : XFunction) (index : Nat) : Bool :=
  (variableInfo function index).fixed.isSome

def registerNode (function : XFunction) (index : Nat) : Bool :=
  match (variableInfo function index).fixed with
  | some (.S ..) => false
  | _ => true

def adjacent (function : XFunction) (state : ColoringState) (index : Nat) : IndexSet :=
  (state.graph.adjacency[index]?.getD {}).foldl (fun result other =>
    if (state.active.contains other || precolored function other) && registerNode function other &&
        nodeClass function state.graph other == nodeClass function state.graph index
    then result.insert other else result) {}

def uncachedDegree (function : XFunction) (state : ColoringState) (index : Nat) : Nat :=
  (state.graph.adjacency[index]?.getD {}).foldl (fun count other =>
    if (state.active.contains other || precolored function other) && registerNode function other &&
        nodeClass function state.graph other == nodeClass function state.graph index
    then count + 1 else count) 0

def degree (function : XFunction) (state : ColoringState) (index : Nat) : Nat :=
  match state.degrees[index]? with
  | some value => value
  | none => uncachedDegree function state index

def refreshDegrees (function : XFunction) (indices : IndexSet) (state : ColoringState) : ColoringState :=
  let degrees := indices.foldl (fun degrees index =>
    degrees.set! index (uncachedDegree function state index)) state.degrees
  { state with degrees }

def pendingMoves (state : ColoringState) (index : Nat) : IndexSet :=
  (state.nodeMoves[index]?.getD {}).foldl (fun result move =>
    if state.workMoves.contains move || state.activeMoves.contains move then result.insert move else result) {}

def classify (context : AllocationContext) (function : XFunction)
    (index : Nat) (state : ColoringState) : ColoringState :=
  let state := { state with
    simplify := state.simplify.erase index
    freeze := state.freeze.erase index
    spill := state.spill.erase index }
  if !state.active.contains index then state
  else if degree function state index >= nodeCapacity context function state index then
    { state with spill := state.spill.insert index }
  else if !(pendingMoves state index).isEmpty then
    { state with freeze := state.freeze.insert index }
  else { state with simplify := state.simplify.insert index }

def enableMoves (indices : IndexSet) (state : ColoringState) : ColoringState :=
  indices.foldl (fun state index =>
    (pendingMoves state index).foldl (fun state move =>
      { state with activeMoves := state.activeMoves.erase move, workMoves := state.workMoves.insert move }) state) state

def refreshNodes (context : AllocationContext) (function : XFunction)
    (indices : IndexSet) (state : ColoringState) : ColoringState :=
  indices.foldl (fun state index => classify context function index state) state

def removeNode (context : AllocationContext) (function : XFunction)
    (index : Nat) (state : ColoringState) : ColoringState :=
  let neighbors := adjacent function state index
  let state := { state with active := state.active.erase index, stack := index :: state.stack }
  let degrees := neighbors.foldl (fun degrees neighbor =>
    degrees.set! neighbor ((degrees[neighbor]?.getD 0) - 1)) state.degrees
  let state := { state with degrees }
  let state := enableMoves (neighbors.insert index) state
  refreshNodes context function (neighbors.insert index) state

def freezeMoves (context : AllocationContext) (function : XFunction)
    (index : Nat) (state : ColoringState) : ColoringState := Id.run do
  let mut state := state
  let mut affected : IndexSet := { index }
  for move in (pendingMoves state index).toList do
    if let some (source, destination) := state.moves[move]? then
      affected := (affected.insert (rangeRoot state.parents source)).insert (rangeRoot state.parents destination)
    state := { state with workMoves := state.workMoves.erase move, activeMoves := state.activeMoves.erase move }
  return refreshNodes context function affected state

def briggs (context : AllocationContext) (function : XFunction)
    (state : ColoringState) (left right : Nat) : Bool :=
  let capacity := nodeCapacity context function state left
  let leftAdjacent := adjacent function state left
  let rightAdjacent := adjacent function state right
  let high := (setUnion leftAdjacent rightAdjacent).foldl (fun count neighbor =>
    let adjustment := if leftAdjacent.contains neighbor && rightAdjacent.contains neighbor then 1 else 0
    if precolored function neighbor || degree function state neighbor - adjustment >= capacity
      then count + 1 else count) 0
  high < capacity

def george (context : AllocationContext) (function : XFunction)
    (state : ColoringState) (left right : Nat) : Bool :=
  (adjacent function state right).toList.all fun neighbor =>
    let edge := (state.graph.adjacency[left]?.getD {}).contains neighbor
    if precolored function neighbor then precolored function left || edge
    else degree function state neighbor < nodeCapacity context function state left || edge

def canCoalesce (context : AllocationContext) (function : XFunction)
    (state : ColoringState) (left right : Nat) : Bool :=
  if precolored function left then george context function state left right
  else
    let leftCost := state.graph.costs[left]?.getD {}
    let rightCost := state.graph.costs[right]?.getD {}
    briggs context function state left right ||
      (!leftCost.unspillable && !rightCost.unspillable &&
        ((rightCost.accesses <= 3 && george context function state left right) ||
         (leftCost.accesses <= 3 && george context function state right left)))

def combineNodes (context : AllocationContext) (function : XFunction)
    (left right : Nat) (state : ColoringState) : ColoringState := Id.run do
  let mut state := state
  let neighbors := state.graph.adjacency[right]?.getD {}
  let mut graph := state.graph
  for neighbor in neighbors.toList do
    graph := { graph with adjacency := graph.adjacency.set! neighbor ((graph.adjacency[neighbor]?.getD {}).erase right) }
    if neighbor != left then graph := graphEdge left neighbor graph
  for neighbor in (graph.preferences[right]?.getD {}).toList do
    graph := { graph with preferences := graph.preferences.set! neighbor ((graph.preferences[neighbor]?.getD {}).erase right) }
    if neighbor != left then graph := graphPreference left neighbor graph
  let leftCost := graph.costs[left]?.getD {}
  let rightCost := graph.costs[right]?.getD {}
  graph := { graph with costs := graph.costs.set! left {
    amount := leftCost.amount + rightCost.amount
    accesses := leftCost.accesses + rightCost.accesses
    unspillable := leftCost.unspillable || rightCost.unspillable
    stackOnly := leftCost.stackOnly || rightCost.stackOnly } }
  let combinedMoves := setUnion (state.nodeMoves[left]?.getD {}) (state.nodeMoves[right]?.getD {})
  state := { state with
    graph
    parents := state.parents.set! right left
    active := state.active.erase right
    nodeMoves := state.nodeMoves.set! left combinedMoves
    coalesced := state.coalesced + 1 }
  state := enableMoves (neighbors.insert left) state
  let affected := (neighbors.insert left).insert right
  state := refreshDegrees function affected state
  return refreshNodes context function affected state

def coalesceMove (context : AllocationContext) (function : XFunction)
    (move : Nat) (state : ColoringState) : ColoringState :=
  let state := { state with workMoves := state.workMoves.erase move }
  let (source, destination) := state.moves[move]?.getD (0, 0)
  let source := rangeRoot state.parents source
  let destination := rangeRoot state.parents destination
  let (left, right) := if precolored function destination then (destination, source) else (source, destination)
  if left == right || precolored function right ||
      (state.graph.adjacency[left]?.getD {}).contains right then
    refreshNodes context function (setOfList [left, right]) state
  else if canCoalesce context function state left right then
    combineNodes context function left right state
  else { state with activeMoves := state.activeMoves.insert move }

def cheaperSpill (function : XFunction) (state : ColoringState) (left right : Nat) : Bool :=
  let leftCost := state.graph.costs[left]?.getD {}
  let rightCost := state.graph.costs[right]?.getD {}
  if leftCost.unspillable != rightCost.unspillable then !leftCost.unspillable
  else
    let leftDegree := max 1 (degree function state left)
    let rightDegree := max 1 (degree function state right)
    leftCost.amount * rightDegree * rightDegree < rightCost.amount * leftDegree * leftDegree

def colorWorklists (context : AllocationContext) (function : XFunction) :
    Nat → ColoringState → Except String ColoringState
  | 0, _ => .error "register coalescing exhausted its worklist bound"
  | fuel + 1, state => do
      if let some index := state.simplify.toList.head? then
        colorWorklists context function fuel (removeNode context function index state)
      else if let some move := state.workMoves.toList.head? then
        colorWorklists context function fuel (coalesceMove context function move state)
      else if let some index := state.freeze.toList.head? then
        colorWorklists context function fuel (freezeMoves context function index state)
      else if let some first := state.spill.toList.head? then
        let index := state.spill.foldl (fun best candidate =>
          if cheaperSpill function state candidate best then candidate else best) first
        colorWorklists context function fuel
          (removeNode context function index (freezeMoves context function index state))
      else return state

def initialColoring (context : AllocationContext) (function : XFunction)
    (graph : Interference) : ColoringState := Id.run do
  let active := graph.present.foldl (fun result index =>
    if precolored function index then result else result.insert index) {}
  let mut state : ColoringState := {
    graph, active
    parents := (List.range function.variables.size).toArray
    nodeMoves := Array.replicate function.variables.size {} }
  for left in graph.present.toList do
    for right in (graph.preferences[left]?.getD {}).toList do
      if left < right && nodeClass function graph left == nodeClass function graph right &&
          registerNode function left && registerNode function right &&
          !(precolored function left && precolored function right) then
        let allowed := fun index => match (variableInfo function index).fixed with
          | some (.R register) => (registerPool context (machineClass register)).any (regEqual register)
          | _ => true
        if allowed left && allowed right then
          let move := state.moves.size
          let nodeMoves := state.nodeMoves.set! left ((state.nodeMoves[left]?.getD {}).insert move)
          state := { state with
            moves := state.moves.push (left, right)
            workMoves := state.workMoves.insert move
            nodeMoves := nodeMoves.set! right ((state.nodeMoves[right]?.getD {}).insert move) }
  let degrees := (List.range function.variables.size).toArray.map (uncachedDegree function state)
  state := { state with degrees }
  return refreshNodes context function active state

def slotWords (type : typ) : Nat := (intOfZ (Backend.Locations.typesize type)).toNat
def slotAlignment (type : typ) : Nat := (intOfZ (Backend.Locations.typealign type)).toNat

def lowestSlot (conflicts : List loc) (type : typ) : loc := Id.run do
  let slots := conflicts.filterMap fun
    | .S .Local offset type => some ((intOfZ offset).toNat, slotWords type)
    | _ => none
  let slots := slots.mergeSort (fun left right => left.1 <= right.1)
  let alignment := slotAlignment type
  let mut current := 0
  for (offset, size) in slots do
    if current + slotWords type <= offset then
      return .S .Local (ZArith.BinInt.Z.of_nat current) type
    current := max current ((offset + size + alignment - 1) / alignment * alignment)
  return .S .Local (ZArith.BinInt.Z.of_nat current) type

structure Coloring where
  locations : Array loc
  coalesced : Nat

def assignColors (context : AllocationContext) (function : XFunction)
    (state : ColoringState) : Except String Coloring := do
  let mut colors := function.variables.map Variable.fixed
  let mut starts : Array Nat := #[0, 0]
  for index in state.stack do
    let conflicts := (state.graph.adjacency[index]?.getD {}).toList.filterMap fun neighbor =>
      (colors[rangeRoot state.parents neighbor]?).join
    let availableLocation := fun location => conflicts.all (locDisjoint location)
    let classId := nodeClass function state.graph index
    let preferred := if classId == 2 then [] else preferredRegisters context classId
    let start := starts[classId]?.getD 0
    let pool := preferred.drop start ++ preferred.take start ++
      (if classId == 2 then [] else remainingRegisters context classId)
    let location ← match pool.find? (fun register => availableLocation (.R register)) with
      | some register =>
          if preferred.any (regEqual register) then
            starts := starts.set! classId ((start + 1) % preferred.length)
          pure (.R register)
      | none => do
          if (state.graph.costs[index]?.getD {}).unspillable then
            throw "unspillable temporary has no available machine register"
          let reused := (state.graph.preferences[index]?.getD {}).toList.findSome? fun neighbor =>
            match (colors[rangeRoot state.parents neighbor]?).join with
            | some (.S .Local offset type) =>
                let ownType := (variableInfo function index).type
                let location := loc.S .Local offset ownType
                if slotWords ownType <= slotWords type &&
                    (intOfZ offset).toNat % slotAlignment ownType == 0 && availableLocation location then some location else none
            | _ => none
          pure (reused.getD (lowestSlot conflicts (variableInfo function index).type))
    colors := colors.set! index (some location)
  let mut locations := #[]
  for index in [:function.variables.size] do
    let location ← match (colors[rangeRoot state.parents index]?).join with
      | some location => pure location
      | none =>
          if state.graph.present.contains index then throw "missing color for an interference node"
          else match (registerPool context (registerClass (variableInfo function index).type)).head? with
            | some register => pure (.R register)
            | none => throw "empty machine register class"
    locations := locations.push location
  return { locations, coalesced := state.coalesced }

def findColoring (configuration : Config.CompilerConfig) (context : AllocationContext)
    (function : XFunction) (liveness : Liveness) : Except String Coloring := do
  let graph := buildInterference configuration function liveness
  let initial := initialColoring context function graph
  let bound := function.variables.size + initial.moves.size + 1
  let state ← colorWorklists context function (bound * bound * bound) initial
  assignColors context function state

end CompCert4Lean.Allocator
