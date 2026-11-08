import CompCert4Lean.Allocator.Analyses
import CompCert4Lean.Allocator.IndexSetCache

namespace CompCert4Lean.Allocator

open Common.AST Backend.Locations X86.Machregs Foundation.Numbers.Rocq.Coq

structure ColoringState where
  graph : Interference
  parents : Array Nat
  active : IndexSet
  activeCache : IndexSetCache active := IndexSetCache.empty active
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

@[inline] def nodeClass (function : XFunction) (graph : Interference) (index : Nat) : Nat :=
  match (variableInfo function index).fixed with
  | some (.R register) => machineClass register
  | _ => if (graph.costs[index]?.getD {}).stackOnly then 2
      else registerClass (variableInfo function index).type

def nodeCapacity (context : AllocationContext) (function : XFunction)
    (state : ColoringState) (index : Nat) : Nat :=
  let classId := nodeClass function state.graph index
  if classId == 2 then 0 else
  if context.reserved.isEmpty then
    if classId == 0 then integerPreferred.length + integerRemaining.length else floatRegisters.length
  else
    let allowed := fun register => !context.reserved.any (regEqual register)
    if classId == 0 then integerPreferred.countP allowed + integerRemaining.countP allowed
    else floatRegisters.countP allowed

@[inline] def precolored (function : XFunction) (index : Nat) : Bool :=
  (variableInfo function index).fixed.isSome

@[inline] def registerNode (function : XFunction) (index : Nat) : Bool :=
  match (variableInfo function index).fixed with
  | some (.S ..) => false
  | _ => true

@[inline] def countsNeighbor (function : XFunction) (state : ColoringState)
    (classId other : Nat) : Bool :=
  let info := variableInfo function other
  match info.fixed with
  | some (.R register) => machineClass register == classId
  | some (.S ..) => false
  | none => IndexSetCache.contains state.active state.activeCache other &&
      (if (state.graph.costs[other]?.getD {}).stackOnly then 2
       else registerClass info.type) == classId

def adjacent (function : XFunction) (state : ColoringState) (index : Nat) : IndexSet :=
  let classId := nodeClass function state.graph index
  (state.graph.adjacency[index]?.getD {}).foldl (fun result other =>
    if countsNeighbor function state classId other
    then result.insert other else result) {}

def uncachedDegree (function : XFunction) (state : ColoringState) (index : Nat) : Nat :=
  let classId := nodeClass function state.graph index
  (state.graph.adjacency[index]?.getD {}).foldl (fun count other =>
    if countsNeighbor function state classId other
    then count + 1 else count) 0

def degree (function : XFunction) (state : ColoringState) (index : Nat) : Nat :=
  match state.degrees[index]? with
  | some value => value
  | none => uncachedDegree function state index

def refreshDegrees (function : XFunction) (indices : IndexSet) (state : ColoringState) : ColoringState :=
  let updates := indices.toList.map (fun index => (index, uncachedDegree function state index))
  let degrees := updates.foldl (fun degrees (index, value) => degrees.set! index value) state.degrees
  { state with degrees }

def pendingMoves (state : ColoringState) (index : Nat) : IndexSet :=
  (state.nodeMoves[index]?.getD {}).foldl (fun result move =>
    if state.workMoves.contains move || state.activeMoves.contains move then result.insert move else result) {}

def hasPendingMoves (state : ColoringState) (index : Nat) : Bool :=
  (state.nodeMoves[index]?.getD {}).any fun move =>
    state.workMoves.contains move || state.activeMoves.contains move

def classify (context : AllocationContext) (function : XFunction)
    (index : Nat) (state : ColoringState) : ColoringState :=
  if !IndexSetCache.contains state.active state.activeCache index then
    { state with
      simplify := state.simplify.erase index
      freeze := state.freeze.erase index, spill := state.spill.erase index }
  else if degree function state index >= nodeCapacity context function state index then
    { state with
      simplify := state.simplify.erase index
      freeze := state.freeze.erase index, spill := state.spill.insert index }
  else if hasPendingMoves state index then
    { state with
      simplify := state.simplify.erase index
      freeze := state.freeze.insert index, spill := state.spill.erase index }
  else
    { state with
      simplify := state.simplify.insert index
      freeze := state.freeze.erase index, spill := state.spill.erase index }

def enableMoves (indices : IndexSet) (state : ColoringState) : ColoringState :=
  if state.activeMoves.isEmpty then state else
  indices.foldl (fun state index =>
    let moves := state.nodeMoves[index]?.getD {}
    if state.activeMoves.size < moves.size then
      state.activeMoves.foldl (fun state move =>
        if moves.contains move then
          { state with activeMoves := state.activeMoves.erase move, workMoves := state.workMoves.insert move }
        else state) state
    else
      moves.foldl (fun state move =>
        if state.activeMoves.contains move then
          { state with activeMoves := state.activeMoves.erase move, workMoves := state.workMoves.insert move }
        else state) state) state

def refreshNodes (context : AllocationContext) (function : XFunction)
    (indices : IndexSet) (state : ColoringState) : ColoringState :=
  indices.foldl (fun state index => classify context function index state) state

def removeNode (context : AllocationContext) (function : XFunction)
    (index : Nat) (state : ColoringState) : ColoringState :=
  let neighbors := adjacent function state index
  let state := { state with
    active := state.active.erase index
    activeCache := IndexSetCache.erase state.active state.activeCache index
    stack := index :: state.stack }
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
    (state : ColoringState) (left right : Nat) : Bool := Id.run do
  let capacity := nodeCapacity context function state left
  if capacity == 0 then return false
  let leftClass := nodeClass function state.graph left
  let rightClass := nodeClass function state.graph right
  let leftNeighbors := state.graph.adjacency[left]?.getD {}
  let rightNeighbors := state.graph.adjacency[right]?.getD {}
  let mut high := 0
  for neighbor in leftNeighbors do
    let neighborDegree := degree function state neighbor
    if (neighborDegree > capacity || precolored function neighbor ||
        (neighborDegree == capacity &&
          !(rightNeighbors.contains neighbor && countsNeighbor function state rightClass neighbor))) &&
        countsNeighbor function state leftClass neighbor then
      high := high + 1
      if high >= capacity then return false
  for neighbor in rightNeighbors do
    if (degree function state neighbor >= capacity || precolored function neighbor) &&
        countsNeighbor function state rightClass neighbor &&
        !(leftNeighbors.contains neighbor && countsNeighbor function state leftClass neighbor) then
      high := high + 1
      if high >= capacity then return false
  return true

def george (context : AllocationContext) (function : XFunction)
    (state : ColoringState) (left right : Nat) : Bool :=
  let classId := nodeClass function state.graph right
  let capacity := nodeCapacity context function state left
  let leftFixed := precolored function left
  let neighbors := state.graph.adjacency[left]?.getD {}
  (state.graph.adjacency[right]?.getD {}).all fun neighbor =>
    !countsNeighbor function state classId neighbor ||
      (if precolored function neighbor then leftFixed || neighbors.contains neighbor
       else degree function state neighbor < capacity || neighbors.contains neighbor)

def canCoalesce (context : AllocationContext) (function : XFunction)
    (state : ColoringState) (left right : Nat) : Bool :=
  if precolored function left then george context function state left right
  else
    let leftCost := state.graph.costs[left]?.getD {}
    let rightCost := state.graph.costs[right]?.getD {}
    briggs context function state left right ||
      (!leftCost.unspillable && !rightCost.unspillable &&
        ((rightCost.accesses <= 1 && george context function state left right) ||
         (leftCost.accesses <= 1 && george context function state right left)))

def combineNodes (context : AllocationContext) (function : XFunction)
    (left right : Nat) (state : ColoringState) : ColoringState := Id.run do
  let neighbors := state.graph.adjacency[right]?.getD {}
  let previousCounts := neighbors.foldl (fun counts neighbor =>
    if neighbor == left || neighbor == right then counts else
      let oldClass := nodeClass function state.graph neighbor
      let removedRight := if countsNeighbor function state oldClass right then 1 else 0
      let removedLeft := if (state.graph.adjacency[neighbor]?.getD {}).contains left &&
          countsNeighbor function state oldClass left then 1 else 0
      counts.push (neighbor, degree function state neighbor - removedRight - removedLeft)) #[]
  let mut graph := state.graph
  let mut state := { state with graph := { adjacency := #[], preferences := #[], costs := #[] } }
  for neighbor in neighbors.toList do
    graph := { graph with adjacency := graph.adjacency.modify neighbor (·.erase right) }
    if neighbor != left then graph := graphEdge left neighbor graph
  for neighbor in (graph.preferences[right]?.getD {}).toList do
    graph := { graph with preferences := graph.preferences.modify neighbor (·.erase right) }
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
    activeCache := IndexSetCache.erase state.active state.activeCache right
    nodeMoves := state.nodeMoves.set! left combinedMoves
    coalesced := state.coalesced + 1 }
  state := enableMoves (neighbors.insert left) state
  let affected := (neighbors.insert left).insert right
  let updates := previousCounts.map fun (neighbor, count) =>
    let newClass := nodeClass function state.graph neighbor
    let addedLeft := if countsNeighbor function state newClass left then 1 else 0
    (neighbor, count + addedLeft)
  let degrees := updates.foldl (fun degrees (neighbor, value) => degrees.set! neighbor value) state.degrees
  state := { state with degrees }
  state := refreshDegrees function (setOfList [left, right]) state
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
      if let some index := state.simplify.min? then
        colorWorklists context function fuel (removeNode context function index state)
      else if let some move := state.workMoves.min? then
        colorWorklists context function fuel (coalesceMove context function move state)
      else if let some index := state.freeze.min? then
        colorWorklists context function fuel (freezeMoves context function index state)
      else if let some first := state.spill.min? then
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
    activeCache := IndexSetCache.ofSet active function.variables.size
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
          let leftMoves := (state.nodeMoves[left]?.getD {}).insert move
          let rightMoves := (state.nodeMoves[right]?.getD {}).insert move
          let nodeMoves := state.nodeMoves.set! left leftMoves
          state := { state with
            moves := state.moves.push (left, right)
            workMoves := state.workMoves.insert move
            nodeMoves := nodeMoves.set! right rightMoves }
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

namespace CompilerOptimization.GeorgeSingleLookup

open CompCert4Lean.Allocator
open CompCert4Lean.Backend.Locations

@[inline] def neighborAllowed (function : XFunction) (state : ColoringState)
    (classId capacity : Nat) (leftFixed : Bool) (neighbors : IndexSet) (neighbor : Nat) : Bool :=
  let info := variableInfo function neighbor
  match info.fixed with
  | some (.R register) =>
      !(machineClass register == classId) || (leftFixed || neighbors.contains neighbor)
  | some (.S ..) => true
  | none =>
      !(IndexSetCache.contains state.active state.activeCache neighbor &&
        (if (state.graph.costs[neighbor]?.getD {}).stackOnly then 2
         else registerClass info.type) == classId) ||
        (degree function state neighbor < capacity || neighbors.contains neighbor)

theorem neighborAllowed_eq (function : XFunction) (state : ColoringState)
    (classId capacity : Nat) (leftFixed : Bool) (neighbors : IndexSet) (neighbor : Nat) :
    neighborAllowed function state classId capacity leftFixed neighbors neighbor =
      (!countsNeighbor function state classId neighbor ||
        (if precolored function neighbor then leftFixed || neighbors.contains neighbor
         else degree function state neighbor < capacity || neighbors.contains neighbor)) := by
  cases fixed : (variableInfo function neighbor).fixed with
  | none => simp [neighborAllowed, countsNeighbor, precolored, fixed]
  | some location =>
      cases location <;> simp [neighborAllowed, countsNeighbor, precolored, fixed]

def georgeOnce (context : AllocationContext) (function : XFunction)
    (state : ColoringState) (left right : Nat) : Bool :=
  let classId := nodeClass function state.graph right
  let capacity := nodeCapacity context function state left
  let leftFixed := precolored function left
  let neighbors := state.graph.adjacency[left]?.getD {}
  (state.graph.adjacency[right]?.getD {}).all
    (neighborAllowed function state classId capacity leftFixed neighbors)

theorem georgeOnce_eq (context : AllocationContext) (function : XFunction)
    (state : ColoringState) (left right : Nat) :
    georgeOnce context function state left right = george context function state left right := by
  simp only [georgeOnce, george]
  congr 1
  funext neighbor
  exact neighborAllowed_eq function state _ _ _ _ neighbor


end CompilerOptimization.GeorgeSingleLookup

namespace CompilerOptimization.BoundedTreeCount

open Std.DTreeMap.Internal
open Std.DTreeMap.Internal.Impl

universe keyLevel valueLevel

@[specialize] def countRaw {Key : Type keyLevel} {Value : Key → Type valueLevel}
    (predicate : (key : Key) → Value key → Bool) (limit initial : Nat)
    (values : @& Impl Key Value) : Nat :=
  match values with
  | .leaf => initial
  | .inner _ key value left right =>
      let leftCount := countRaw predicate limit initial left
      if leftCount >= limit then leftCount else
      let updated := if predicate key value then leftCount + 1 else leftCount
      if updated >= limit then updated else countRaw predicate limit updated right

def countStep {Key : Type keyLevel} {Value : Key → Type valueLevel}
    (predicate : (key : Key) → Value key → Bool) (limit : Nat)
    (key : Key) (value : Value key) (state : Option Bool × Nat) :
    Id (ForInStep (Option Bool × Nat)) :=
  if predicate key value then
    let updated := state.2 + 1
    if updated >= limit then .done (some false, updated) else .yield (none, updated)
  else .yield (none, state.2)

def outcome (limit count : Nat) : ForInStep (Option Bool × Nat) :=
  if count >= limit then .done (some false, count) else .yield (none, count)

theorem countRaw_loop {Key : Type keyLevel} {Value : Key → Type valueLevel}
    (predicate : (key : Key) → Value key → Bool) (limit initial : Nat)
    (values : Impl Key Value) (valid : initial < limit) :
    values.forInStep (countStep predicate limit) (none, initial) =
      outcome limit (countRaw predicate limit initial values) := by
  induction values generalizing initial with
  | leaf => simp [Impl.forInStep, countRaw, outcome, Nat.not_le.mpr valid, pure]
  | inner size key value left right leftHypothesis rightHypothesis =>
      simp only [Impl.forInStep, leftHypothesis initial valid, bind, pure]
      by_cases leftFull : countRaw predicate limit initial left >= limit
      · simp [outcome, leftFull, countRaw]
      · have leftValid : countRaw predicate limit initial left < limit := Nat.lt_of_not_ge leftFull
        cases rootResult : predicate key value with
        | false =>
            simpa [outcome, countStep, rootResult, leftFull, countRaw, bind, pure] using
              rightHypothesis (countRaw predicate limit initial left) leftValid
        | true =>
            by_cases rootFull : countRaw predicate limit initial left + 1 >= limit
            · simp [outcome, countStep, rootResult, leftFull, rootFull, countRaw, bind, pure]
            · have rootValid : countRaw predicate limit initial left + 1 < limit :=
                Nat.lt_of_not_ge rootFull
              simpa [outcome, countStep, rootResult, leftFull, rootFull, countRaw, bind, pure] using
                rightHypothesis (countRaw predicate limit initial left + 1) rootValid

theorem countRaw_forIn {Key : Type keyLevel} {Value : Key → Type valueLevel}
    (predicate : (key : Key) → Value key → Bool) (limit initial : Nat)
    (values : Impl Key Value) (valid : initial < limit) :
    values.forIn (m := Id)
      (fun key value (state : Option Bool × Nat) =>
        if predicate key value then
          if state.2 + 1 >= limit then .done (some false, state.2 + 1)
          else .yield (none, state.2 + 1)
        else .yield (none, state.2)) (none, initial) =
      if countRaw predicate limit initial values >= limit
      then (some false, countRaw predicate limit initial values)
      else (none, countRaw predicate limit initial values) := by
  change values.forIn (countStep predicate limit) (none, initial) = _
  simp only [Impl.forIn, countRaw_loop predicate limit initial values valid, outcome, bind, pure]
  by_cases full : countRaw predicate limit initial values >= limit <;> simp [full]

open CompCert4Lean.Allocator

@[inline] def countSet (predicate : Nat → Bool) (limit initial : Nat) (values : IndexSet) : Nat :=
  countRaw (fun key _ => predicate key) limit initial values.inner.inner.inner

def briggsCount (context : AllocationContext) (function : XFunction)
    (state : ColoringState) (left right : Nat) : Bool :=
  let capacity := nodeCapacity context function state left
  if capacity == 0 then false else
  let leftClass := nodeClass function state.graph left
  let rightClass := nodeClass function state.graph right
  let leftNeighbors := state.graph.adjacency[left]?.getD {}
  let rightNeighbors := state.graph.adjacency[right]?.getD {}
  let leftPredicate := fun neighbor =>
    let neighborDegree := degree function state neighbor
    (neighborDegree > capacity || precolored function neighbor ||
      (neighborDegree == capacity &&
        !(rightNeighbors.contains neighbor && countsNeighbor function state rightClass neighbor))) &&
      countsNeighbor function state leftClass neighbor
  let high := countSet leftPredicate capacity 0 leftNeighbors
  if high >= capacity then false else
  let rightPredicate := fun neighbor =>
    (degree function state neighbor >= capacity || precolored function neighbor) &&
      countsNeighbor function state rightClass neighbor &&
      !(leftNeighbors.contains neighbor && countsNeighbor function state leftClass neighbor)
  countSet rightPredicate capacity high rightNeighbors < capacity

theorem briggsCount_eq (context : AllocationContext) (function : XFunction)
    (state : ColoringState) (left right : Nat) :
    briggsCount context function state left right = briggs context function state left right := by
  simp only [briggsCount, briggs]
  generalize capacityEq : nodeCapacity context function state left = capacity
  cases capacity with
  | zero => rfl
  | succ capacity =>
      simp only [Nat.succ_ne_zero, beq_iff_eq, Bool.false_eq_true, if_false,
        ForIn.forIn, Std.TreeSet.forIn, Std.TreeMap.forIn, Std.DTreeMap.forIn, pure]
      rw [countRaw_forIn _ _ _ _ (Nat.succ_pos capacity)]
      simp only [countSet, bind, Id.run]
      split
      · rename_i full
        simp_all
      · rename_i notFull
        rw [countRaw_forIn _ _ _ _ (Nat.lt_of_not_ge notFull)]
        simp_all [apply_ite] <;> split <;> simp_all <;> omega

def canCoalesceCount (context : AllocationContext) (function : XFunction)
    (state : ColoringState) (left right : Nat) : Bool :=
  if precolored function left then CompilerOptimization.GeorgeSingleLookup.georgeOnce context function state left right
  else
    let leftCost := state.graph.costs[left]?.getD {}
    let rightCost := state.graph.costs[right]?.getD {}
    briggsCount context function state left right ||
      (!leftCost.unspillable && !rightCost.unspillable &&
        ((rightCost.accesses <= 1 && CompilerOptimization.GeorgeSingleLookup.georgeOnce context function state left right) ||
         (leftCost.accesses <= 1 && CompilerOptimization.GeorgeSingleLookup.georgeOnce context function state right left)))

theorem canCoalesceCount_eq (context : AllocationContext) (function : XFunction)
    (state : ColoringState) (left right : Nat) :
    canCoalesceCount context function state left right =
      canCoalesce context function state left right := by
  simp only [canCoalesceCount, canCoalesce, briggsCount_eq,
    CompilerOptimization.GeorgeSingleLookup.georgeOnce_eq]

def coalesceMoveCount (context : AllocationContext) (function : XFunction)
    (move : Nat) (state : ColoringState) : ColoringState :=
  let state := { state with workMoves := state.workMoves.erase move }
  let (source, destination) := state.moves[move]?.getD (0, 0)
  let source := rangeRoot state.parents source
  let destination := rangeRoot state.parents destination
  let (left, right) := if precolored function destination then (destination, source) else (source, destination)
  if left == right || precolored function right ||
      (state.graph.adjacency[left]?.getD {}).contains right then
    refreshNodes context function (setOfList [left, right]) state
  else if canCoalesceCount context function state left right then
    combineNodes context function left right state
  else { state with activeMoves := state.activeMoves.insert move }

theorem coalesceMoveCount_eq (context : AllocationContext) (function : XFunction)
    (move : Nat) (state : ColoringState) :
    coalesceMoveCount context function move state = coalesceMove context function move state := by
  simp only [coalesceMoveCount, coalesceMove, canCoalesceCount_eq]

def colorWorklistsCount (context : AllocationContext) (function : XFunction) :
    Nat → ColoringState → Except String ColoringState
  | 0, _ => .error "register coalescing exhausted its worklist bound"
  | fuel + 1, state => do
      if let some index := state.simplify.min? then
        colorWorklistsCount context function fuel (removeNode context function index state)
      else if let some move := state.workMoves.min? then
        colorWorklistsCount context function fuel (coalesceMoveCount context function move state)
      else if let some index := state.freeze.min? then
        colorWorklistsCount context function fuel (freezeMoves context function index state)
      else if let some first := state.spill.min? then
        let index := state.spill.foldl (fun best candidate =>
          if cheaperSpill function state candidate best then candidate else best) first
        colorWorklistsCount context function fuel
          (removeNode context function index (freezeMoves context function index state))
      else return state

theorem colorWorklistsCount_eq (context : AllocationContext) (function : XFunction)
    (fuel : Nat) (state : ColoringState) :
    colorWorklistsCount context function fuel state = colorWorklists context function fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp only [colorWorklistsCount, colorWorklists, inductionHypothesis,
        coalesceMoveCount_eq] <;> rfl

def findColoringCount (configuration : CompCert4Lean.Config.CompilerConfig)
    (context : AllocationContext) (function : XFunction) (liveness : Liveness) :
    Except String Coloring := do
  let graph := buildInterference configuration function liveness
  let initial := initialColoring context function graph
  let bound := function.variables.size + initial.moves.size + 1
  let state ← colorWorklistsCount context function (bound * bound * bound) initial
  assignColors context function state

@[csimp] theorem findColoringCount_csimp : findColoring = findColoringCount := by
  funext configuration context function liveness
  simp only [findColoringCount, findColoring, colorWorklistsCount_eq]

@[csimp] theorem briggsCount_csimp : briggs = briggsCount := by
  funext context function state left right
  exact (briggsCount_eq context function state left right).symm

@[csimp] theorem canCoalesceCount_csimp : canCoalesce = canCoalesceCount := by
  funext context function state left right
  exact (canCoalesceCount_eq context function state left right).symm

@[csimp] theorem coalesceMoveCount_csimp : coalesceMove = coalesceMoveCount := by
  funext context function move state
  exact (coalesceMoveCount_eq context function move state).symm

@[csimp] theorem colorWorklistsCount_csimp : colorWorklists = colorWorklistsCount := by
  funext context function fuel state
  exact (colorWorklistsCount_eq context function fuel state).symm



end CompilerOptimization.BoundedTreeCount
