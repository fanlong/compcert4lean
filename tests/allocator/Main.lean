import CompCert4Lean.Prototype.Services

namespace AllocatorTests

open CompCert4Lean CompCert4Lean.Allocator Common.AST Backend Backend.Registers Backend.Locations
open Foundation.Numbers.Rocq.Coq Lib.Maps Lib.Integers X86.Machregs X86.Op

theorem mem_insertFold (values : List Nat) (initial : IndexSet) (element : Nat) :
    element ∈ values.foldl (fun result value => result.insert value) initial ↔
      element ∈ initial ∨ element ∈ values := by
  induction values generalizing initial with
  | nil => simp
  | cons value values induction =>
      simp only [List.foldl_cons, induction, Std.TreeSet.mem_insert, List.mem_cons,
        Std.LawfulEqOrd.compare_eq_iff_eq]
      constructor
      · rintro ((same | present) | member)
        · exact Or.inr (Or.inl same.symm)
        · exact Or.inl present
        · exact Or.inr (Or.inr member)
      · rintro (present | same | member)
        · exact Or.inl (Or.inr present)
        · exact Or.inl (Or.inl same.symm)
        · exact Or.inr member

theorem setUnion_preserves_order (left right : IndexSet) :
    (setUnion left right).toList =
      (right.foldl (fun result value => result.insert value) left).toList := by
  apply Std.TreeSet.equiv_iff_toList_eq.mp
  apply Std.TreeSet.Equiv.of_forall_mem_iff
  intro element
  simp [setUnion, Std.TreeSet.mem_union_iff, Std.TreeSet.foldl_eq_foldl_toList,
    mem_insertFold]

theorem setChange_preserves_liveness (left right : IndexSet) :
    (left.size != right.size || left.toList != right.toList) =
      (left.toList != right.toList) := by
  by_cases same : left.toList = right.toList
  · have sizes := congrArg List.length same
    simp only [Std.TreeSet.length_toList] at sizes
    simp [same, sizes]
  · simp [same]

def testFixedLocationLookup : Except String Unit := do
  let mut locations := X86.Machregs.all_mregs.map loc.R
  for slot in [slot.Local, slot.Incoming, slot.Outgoing] do
    for offset in [-16, 0, 8, 64] do
      for type in [typ.Tint, typ.Tlong, typ.Tsingle, typ.Tfloat, typ.Tany32, typ.Tany64] do
        locations := locations ++ [.S slot (zOfInt offset) type]
  for count in [0, 1, 32, 1024] do
    let repeated := loc.S .Incoming (zOfInt 8) .Tlong
    let duplicate : Variable := { type := .Tlong, fixed := some repeated }
    let variables := (Array.replicate count { type := .Tint }).push duplicate |>.push duplicate
    let action : BuildM Unit := do
      for _ in [:3] do
        for location in repeated :: locations do
          let before ← get
          let expected := (List.range before.variables.size).find? fun index =>
            match (before.variables[index]?.getD { type := .Tint }).fixed with
            | some previous => locEqual previous location
            | none => false
          let actual ← fixed location
          unless actual == expected.getD before.variables.size do
            throw "fixed-location lookup changed the earliest matching index"
          let after ← get
          let expectedSize := before.variables.size + if expected.isSome then 0 else 1
          unless after.variables.size == expectedSize do
            throw "fixed-location lookup changed variable creation"
          match (after.variables[actual]?.getD { type := .Tint }).fixed with
          | some previous =>
              unless locEqual previous location do
                throw "fixed-location lookup returned the wrong location"
          | none => throw "fixed-location lookup returned a pseudo-register"
        let _ ← fresh .Tfloat
        let _ ← fresh .Tint
    let _ ← action.run { variables }
    let machineVariables : Array Variable := X86.Machregs.all_mregs.toArray.map fun register =>
      { type := X86.Machregs.mreg_type register, fixed := some (.R register) }
    let _ ← action.run {
      variables := machineVariables ++ Array.replicate count { type := .Tint }
      fixedLocations := some fixedMachineLocations }
  return ()

def positiveOf (value : Nat) : positive := PArith.BinPos.Pos.of_nat value
def number (value : Nat) := ZArith.BinInt.Z.of_nat value
def text (value : String) : Foundation.RocqString.Rocq.Coq.Strings.String.string :=
  value.toUTF8.toList.foldr .String .EmptyString
def sign (arguments : List xtype := []) (result : xtype := .Xint) : signature :=
  { sig_args := arguments, sig_res := result, sig_cc := cc_default }

def linear (signature : signature) (parameters : List Nat)
    (instructions : List (RTL.node → RTL.instruction)) : RTL.function :=
  { fn_sig := signature
    fn_params := parameters.map positiveOf
    fn_stacksize := number 512
    fn_entrypoint := positiveOf 1
    fn_code := instructions.zipIdx.foldl (fun code (instruction, index) =>
      PTree.set (positiveOf (index + 1)) (instruction (positiveOf (index + 2))) code)
      (PTree.empty RTL.instruction) }

def operation (op : operation) (arguments : List Nat) (destination : Nat) : RTL.node → RTL.instruction :=
  .Iop op (arguments.map positiveOf) (positiveOf destination)

def integer (value destination : Nat) := operation (.Ointconst (Lib.Integers.Int.repr (number value))) [] destination
def floating (destination : Nat) := operation (.Ofloatconst Lib.Floats.Float.zero) [] destination
def copy (source destination : Nat) := operation .Omove [source] destination
def ret (source : Nat) : RTL.node → RTL.instruction := fun _ => .Ireturn (some (positiveOf source))

def annotation (registers : List Nat) (type : typ := .Tint) : RTL.node → RTL.instruction :=
  .Ibuiltin (.EF_annot (positiveOf 1) (text "allocator fixture") (registers.map fun _ => type))
    (registers.map fun index => .BA (positiveOf index)) .BR_none

def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def validate (name : String) (source : RTL.function) (context : AllocationContext := {})
    : Except String (LTL.function × AllocationStats) := do
  let (target, stats) ← (allocate Prototype.cfg context source).mapError (name ++ ": " ++ ·)
  let types ← match RTLtyping.type_function Prototype.cfg source with
    | .OK types => pure types
    | .Error errors => throw (name ++ ": typing: " ++ Prototype.errorText errors)
  match Allocation.check_function Prototype.cfg source target types with
  | .OK () => return (target, stats)
  | .Error errors => throw (name ++ ": validator: " ++ Prototype.errorText errors)

def pressureBody (count : Nat) (float : Bool) : List (RTL.node → RTL.instruction) :=
  let constants := (List.range count).map fun index =>
    if float then floating (index + 1) else integer (index + 1) (index + 1)
  let reductions := (List.range (count - 1)).map fun index =>
    operation (if float then .Oaddf else .Osub) [1, index + 2] 1
  constants ++ reductions

def pressure (count : Nat) (float : Bool) : RTL.function :=
  linear (sign [] (if float then .Xfloat else .Xint)) [] (pressureBody count float ++ [ret 1])

def instructionRegisters : LTL.instruction → List mreg
  | .Lop _ arguments result | .Lload _ _ arguments result | .Lstore _ _ arguments result => result :: arguments
  | .Lgetstack _ _ _ result | .Lsetstack result _ _ _ => [result]
  | .Lcall _ (.inl target) | .Ltailcall _ (.inl target) => [target]
  | .Lbuiltin _ arguments result =>
      (params_of_builtin_args arguments).filterMap (fun | .R register => some register | _ => none) ++
      params_of_builtin_res result
  | .Lcond _ arguments _ _ => arguments
  | .Ljumptable argument _ => [argument]
  | _ => []

def stackOperations (function : LTL.function) : Nat :=
  (PTree.elements function.fn_code).foldl (fun count (_, block) =>
    block.foldl (fun count instruction => match instruction with
      | .Lgetstack .. | .Lsetstack .. => count + 1
      | _ => count) count) 0

def copies (function : LTL.function) : Nat :=
  (PTree.elements function.fn_code).foldl (fun count (_, block) =>
    block.foldl (fun count instruction => match instruction with
      | .Lop .Omove _ _ => count + 1
      | _ => count) count) 0

def locationKey : loc → Nat
  | .R register => machineIndex register
  | .S .Local offset _ => 100 + (intOfZ offset).toNat
  | .S .Incoming offset _ => 1000 + (intOfZ offset).toNat
  | .S .Outgoing offset _ => 2000 + (intOfZ offset).toNat

def simulateMoves (code : List LTL.instruction) : Except String (Std.TreeMap Nat Nat) := do
  let mut values : Std.TreeMap Nat Nat := {}
  for instruction in code do
    let (source, destination) ← match instruction with
      | .Lop .Omove [source] destination => pure (loc.R source, loc.R destination)
      | .Lgetstack slot offset type destination => pure (.S slot offset type, .R destination)
      | .Lsetstack source slot offset type => pure (.R source, .S slot offset type)
      | _ => throw "unexpected instruction in parallel move test"
    values := values.insert (locationKey destination) ((values[locationKey source]?).getD (locationKey source))
  return values

def checkParallel (sources destinations : List loc) : Except String Unit := do
  let (code, _) ← resolveParallelMoves sources destinations .R11 .X15 40
  let values ← simulateMoves code
  for (source, destination) in sources.zip destinations do
    require (((values[locationKey destination]?).getD (locationKey destination)) == locationKey source)
      "parallel move cycle changed a value"

def testBasic : Except String Unit := do
  let source := linear (sign [.Xint]) [1]
    ([integer 999 90] ++ (List.range 8).map (fun index => copy (index + 1) (index + 2)) ++ [ret 9])
  let (target, stats) ← validate "copy chain" source
  require (stackOperations target == 0 && copies target <= 1 && stats.coalesced >= 8 && stats.deadInstructions > 0)
    "copy chain failed the optimization witness"
  let types ← match RTLtyping.type_function Prototype.cfg source with
    | .OK types => pure types
    | .Error _ => throw "copy chain typing"
  let xtl ← buildXTL Prototype.cfg source types
  let live ← analyzeLiveness xtl
  let first ← findColoring Prototype.cfg {} xtl live
  let second ← findColoring Prototype.cfg {} xtl live
  require (first.locations.size == second.locations.size &&
    (first.locations.toList.zip second.locations.toList).all (fun (left, right) => locEqual left right))
    "allocation is not deterministic"
  let corrupted := { target with fn_stacksize := number 513 }
  require (match Allocation.check_function Prototype.cfg source corrupted types with | .Error _ => true | _ => false)
    "validator accepted corrupted allocation"
  let disconnected := linear (sign []) []
    [integer 1 1, annotation [1], integer 2 1, annotation [1], ret 1]
  let _ ← validate "disconnected ranges" disconnected
  let types ← match RTLtyping.type_function Prototype.cfg disconnected with
    | .OK types => pure types
    | .Error _ => throw "disconnected typing"
  let (ranges, _, _) ← splitLiveRanges disconnected types
  let first := ((ranges.entries[0]?.getD ({} : RangeInfo)).definitions[1]?).getD 0
  let second := ((ranges.entries[2]?.getD ({} : RangeInfo)).definitions[1]?).getD 0
  require (rangeRoot ranges.parents first != rangeRoot ranges.parents second) "independent ranges were merged"
  let sparse := linear (sign [.Xint]) [1000000000] [copy 1000000000 2000000000, ret 2000000000]
  let (_, sparseStats) ← validate "sparse register identifiers" sparse
  require (sparseStats.pseudoRegisters < 10) "source identifiers were used as array sizes"
  let debug := linear (sign []) [] [integer 17 9,
    (.Ibuiltin (.EF_debug (positiveOf 1) (positiveOf 100) [.Tint]) [.BA (positiveOf 9)] .BR_none),
    integer 0 1, ret 1]
  let (debugTarget, debugStats) ← validate "dead debug operands" debug
  require (debugStats.deadInstructions > 0 && (PTree.elements debugTarget.fn_code).any fun (_, block) =>
    block.any fun | .Lbuiltin (.EF_debug ..) arguments _ => arguments.isEmpty | _ => false)
    "debug-only values stayed live"

def testPressure : Except String (List (String × AllocationStats)) := do
  let mut results := []
  for (name, float) in [("integer pressure", false), ("float pressure", true)] do
    let source := pressure 24 float
    let (target, stats) ← validate name source
    require (stats.rounds > 1 && stackOperations target > 0) (name ++ " did not exercise spilling")
    let twice := linear source.fn_sig [] (pressureBody 24 float ++
      [annotation [1] (if float then .Tfloat else .Tint)] ++ pressureBody 24 float ++ [ret 1])
    let (_, twiceStats) ← validate (name ++ " stack reuse") twice
    require (twiceStats.stackWords < 2 * stats.stackWords) (name ++ " did not reuse stack slots")
    results := results ++ [(name, stats), (name ++ " twice", twiceStats)]
  let context : AllocationContext := { reserved := integerRemaining }
  let (target, stats) ← validate "reserved registers" (pressure 20 false) context
  require ((PTree.elements target.fn_code).all fun (_, block) =>
    block.all fun instruction => (instructionRegisters instruction).all fun register =>
      !context.reserved.any (regEqual register)) "reserved register was allocated"
  return results ++ [("reserved registers", stats)]

def testCallsAndConstraints : Except String Unit := do
  let callSign := sign [.Xint] .Xint
  let direct := linear (sign [.Xint]) [1]
    [(.Icall callSign (.inr (positiveOf 100)) [positiveOf 1] (positiveOf 2)),
     operation .Osub [1, 2] 1, ret 1]
  let _ ← validate "live across call" direct
  let indirect := linear (sign [.Xptr, .Xint]) [1, 2]
    [(.Icall callSign (.inl (positiveOf 1)) [positiveOf 2] (positiveOf 3)),
     operation .Osub [2, 3] 2, ret 2]
  let _ ← validate "indirect call" indirect
  for op in [X86.Op.operation.Odiv, .Odivu, .Omod, .Omodu, .Oshl, .Oshr, .Oshru, .Osub] do
    let _ ← validate "fixed/two-address constraint"
      (linear (sign [.Xint, .Xint]) [1, 2] [operation op [1, 2] 2, ret 2])
  for op in [X86.Op.operation.Odivl, .Odivlu, .Omodl, .Omodlu, .Osubl] do
    let _ ← validate "long fixed/two-address constraint"
      (linear (sign [.Xlong, .Xlong] .Xlong) [1, 2] [operation op [1, 2] 2, ret 2])
  for op in [X86.Op.operation.Oshll, .Oshrl, .Oshrlu] do
    let _ ← validate "long variable shift"
      (linear (sign [.Xlong, .Xint] .Xlong) [1, 2] [operation op [1, 2] 1, ret 1])
  checkParallel [.R .AX, .R .CX, .R .DX] [.R .CX, .R .DX, .R .AX]
  checkParallel [.S .Local (number 0) .Tint, .S .Local (number 1) .Tint, .S .Local (number 2) .Tint]
    [.S .Local (number 1) .Tint, .S .Local (number 2) .Tint, .S .Local (number 0) .Tint]
  checkParallel [.R .X0, .R .X1] [.R .X1, .R .X0]

def testBuiltins : Except String Unit := do
  let stack := builtin_arg.BA_addrstack (Ptrofs.repr (number 64))
  for size in [16, 128] do
    for arguments in [[.BA (positiveOf 1), .BA (positiveOf 2)],
        [.BA (positiveOf 1), .BA (positiveOf 1)], [stack, .BA (positiveOf 1)],
        [.BA (positiveOf 1), stack], [stack, stack]] do
      let source := linear (sign [.Xptr, .Xptr]) [1, 2]
        [(.Ibuiltin (.EF_memcpy (number size) (number 8)) arguments .BR_none), integer 0 3, ret 3]
      let _ ← validate "memcpy placement" source
  let variadic := { sign [.Xptr] with sig_cc := { cc_default with cc_vararg := some (number 1) } }
  let vaStart := .EF_builtin (text "__builtin_va_start") (sign [.Xptr] .Xvoid)
  let _ ← validate "va_start" (linear variadic [1]
    [(.Ibuiltin vaStart [.BA (positiveOf 1)] .BR_none), integer 0 2, ret 2])
  let annotations := linear (sign []) []
    ((List.range 30).map (fun index => integer index (index + 1)) ++ [annotation ((List.range 30).map (· + 1)), ret 1])
  let (target, _) ← validate "large annotation" annotations
  require ((PTree.elements target.fn_code).any fun (_, block) => block.any fun
    | .Lbuiltin (.EF_annot ..) arguments _ => arguments.length == 30 &&
        (params_of_builtin_args arguments).any (fun | .S .. => true | _ => false)
    | _ => false) "large annotation did not use permitted stack locations"

def testReloadReuse : Except String Unit := do
  let variables := #[{ type := typ.Tint }, { type := typ.Tint }, { type := typ.Tint }]
  let function : XFunction := {
    signature := sign [], stacksize := number 0, variables, entry := 0
    blocks := #[{
      source := positiveOf 1
      instructions := [.op .Osub [0, 1] 2, .branch (positiveOf 2)]
      successors := [1] }, {
      source := positiveOf 2
      instructions := [.op .Osub [0, 1] 2, .op .Osub [0, 1] 2, .ret [2]]
      predecessors := [0] }] }
  let (_, reused) ← insertSpills function (setOfList [1]) 1
  let (_, reduced) ← insertSpills function (setOfList [1]) 21
  require (reused >= 2 && reduced < reused) "reload reuse or progressive reduction failed"

def testDegreeCache : Except String Unit := do
  let source := pressure 35 false
  let types ← match RTLtyping.type_function Prototype.cfg source with
    | .OK types => pure types
    | .Error _ => throw "degree cache fixture typing"
  let function ← buildXTL Prototype.cfg source types
  let live ← analyzeLiveness function
  let graph := buildInterference Prototype.cfg function live
  let mut state := initialColoring {} function graph
  for _ in [:300] do
    for index in state.active.toList do
      require (degree function state index == uncachedDegree function state index) "stale interference degree"
    if let some move := state.workMoves.toList.head? then
      state := coalesceMove {} function move state
    else if let some index := state.active.toList.head? then
      state := removeNode {} function index (freezeMoves {} function index state)
    else break
  require state.active.isEmpty "degree cache fixture did not drain"

def checkDegrees (function : XFunction) (state : ColoringState) : Except String Unit := do
  for index in [:function.variables.size + 3] do
    require (IndexSetCache.contains state.active state.activeCache index == state.active.contains index)
      "active membership cache differs from ordered set"
  for index in state.graph.present.toList do
    if state.active.contains index || (precolored function index && registerNode function index) then
      require (degree function state index == uncachedDegree function state index)
        ("stale interference degree at " ++ toString index)
    require (hasPendingMoves state index == !(pendingMoves state index).isEmpty)
      "pending-move predicate changed"

def checkCoalescingCriteria (function : XFunction) (state : ColoringState)
    (context : AllocationContext := {}) : Except String Unit := do
  for left in state.graph.present.toList do
    for right in state.graph.present.toList do
      let capacity := nodeCapacity context function state left
      let leftAdjacent := adjacent function state left
      let rightAdjacent := adjacent function state right
      let high := (setUnion leftAdjacent rightAdjacent).foldl (fun count neighbor =>
        let adjustment := if leftAdjacent.contains neighbor && rightAdjacent.contains neighbor then 1 else 0
        if precolored function neighbor || degree function state neighbor - adjustment >= capacity
          then count + 1 else count) 0
      require (briggs context function state left right == (high < capacity)) "Briggs criterion changed"
      let conservative := rightAdjacent.toList.all fun neighbor =>
        let edge := (state.graph.adjacency[left]?.getD {}).contains neighbor
        if precolored function neighbor then precolored function left || edge
        else degree function state neighbor < capacity || edge
      require (george context function state left right == conservative) "George criterion changed"

def enableMovesReference (indices : IndexSet) (state : ColoringState) : ColoringState :=
  indices.foldl (fun state index =>
    (state.nodeMoves[index]?.getD {}).foldl (fun state move =>
      if state.activeMoves.contains move then
        { state with activeMoves := state.activeMoves.erase move, workMoves := state.workMoves.insert move }
      else state) state) state

def combineNodesReference (context : AllocationContext) (function : XFunction)
    (left right : Nat) (state : ColoringState) : ColoringState := Id.run do
  let previous := state
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
    activeCache := IndexSetCache.empty (state.active.erase right)
    nodeMoves := state.nodeMoves.set! left combinedMoves
    coalesced := state.coalesced + 1 }
  state := enableMovesReference (neighbors.insert left) state
  let affected := (neighbors.insert left).insert right
  let degrees := neighbors.foldl (fun degrees neighbor =>
    if neighbor == left || neighbor == right then degrees else
      let oldClass := nodeClass function previous.graph neighbor
      let newClass := nodeClass function state.graph neighbor
      let removedRight := if countsNeighbor function previous oldClass right then 1 else 0
      let removedLeft := if (previous.graph.adjacency[neighbor]?.getD {}).contains left &&
          countsNeighbor function previous oldClass left then 1 else 0
      let addedLeft := if countsNeighbor function state newClass left then 1 else 0
      degrees.set! neighbor (degree function previous neighbor - removedRight - removedLeft + addedLeft))
      state.degrees
  state := { state with degrees }
  let degrees := (setOfList [left, right]).foldl (fun degrees index =>
    degrees.set! index (uncachedDegree function state index)) state.degrees
  state := { state with degrees }
  return refreshNodes context function affected state

def coloringStateKey (state : ColoringState) :=
  (state.graph.adjacency.map (fun indices => indices.toList), state.graph.preferences.map (fun indices => indices.toList),
   state.graph.costs.map (fun cost => (cost.amount, cost.accesses, cost.unspillable, cost.stackOnly)),
   state.graph.present.toList, state.parents, state.active.toList, state.simplify.toList,
   state.freeze.toList, state.spill.toList, state.moves, state.nodeMoves.map (fun indices => indices.toList),
   state.workMoves.toList, state.activeMoves.toList, state.stack, state.coalesced, state.degrees)

def checkCombine (context : AllocationContext) (function : XFunction)
    (left right : Nat) (state : ColoringState) : Except String Unit := do
  require (coloringStateKey (combineNodes context function left right state) ==
      coloringStateKey (combineNodesReference context function left right state))
    "coalescing ownership rewrite changed state"

def classifyReference (context : AllocationContext) (function : XFunction)
    (index : Nat) (state : ColoringState) : ColoringState :=
  let state := { state with
    simplify := state.simplify.erase index
    freeze := state.freeze.erase index
    spill := state.spill.erase index }
  if !state.active.contains index then state
  else if degree function state index >= nodeCapacity context function state index then
    { state with spill := state.spill.insert index }
  else if hasPendingMoves state index then
    { state with freeze := state.freeze.insert index }
  else { state with simplify := state.simplify.insert index }

def testClassification : Except String Unit := do
  for count in [0, 1, 17, 65] do
    for seed in [:12] do
      let variables := (List.range count).toArray.map fun index =>
        ({ type := if index % 3 == 1 then .Tfloat else .Tint
           fixed := if index == 0 then some (.R .AX)
             else if index == 1 then some (.R .X0)
             else if index == 2 then some (.S .Local (number 0) .Tint) else none } : Variable)
      let function : XFunction := {
        signature := sign [], stacksize := number 0, variables, blocks := #[], entry := 0 }
      let indices := List.range (count + 3)
      let setWhere := fun predicate => setOfList (indices.filter predicate)
      let active := setWhere fun index => index % 5 != seed % 5
      for width in [0, count / 2, count + 3] do
        let state : ColoringState := {
          graph := {
            adjacency := Array.replicate count (setWhere fun index => index % 2 == seed % 2)
            preferences := #[]
            costs := indices.toArray.map fun index => { stackOnly := index % 7 == seed % 7 } }
          parents := #[], active, activeCache := IndexSetCache.ofSet active width
          nodeMoves := indices.toArray.map fun index => setOfList [index, index + 1]
          workMoves := setWhere fun index => index % 3 == seed % 3
          activeMoves := setWhere fun index => index % 7 == seed % 7
          simplify := setWhere fun index => index % 2 == seed % 2
          freeze := setWhere fun index => index % 3 == seed % 3
          spill := setWhere fun index => index % 4 == seed % 4
          degrees := (List.range (count / 2)).toArray.map fun index => index % 20 }
        for context in [({} : AllocationContext), { reserved := integerRemaining }] do
          for index in [:count + 5] do
            require (coloringStateKey (classify context function index state) ==
                coloringStateKey (classifyReference context function index state))
              "worklist classification changed state"

def testMoveActivation : Except String Unit := do
  let setWhere := fun (count : Nat) (predicate : Nat → Bool) =>
    (List.range count).foldl (fun result index =>
      if predicate index then result.insert index else result) ({} : IndexSet)
  for nodeCount in [0, 1, 4, 17, 65] do
    for moveCount in [0, 1, 4, 19, 64, 127] do
      for seed in [:12] do
        let nodeMoves := (List.range nodeCount).toArray.map fun index =>
          setWhere moveCount (fun move => (move * 13 + index * 7 + seed) % 17 < seed + 1)
        let state : ColoringState := {
          graph := { adjacency := #[], preferences := #[], costs := #[] }
          parents := #[], active := {}, nodeMoves
          activeMoves := setWhere (moveCount + 3) (fun move => move % (seed + 1) == 0)
          workMoves := setWhere (moveCount + 3) (fun move => (move + seed) % 3 == 0) }
        for indices in [{}, setWhere (nodeCount + 2) (fun _ => true),
            setWhere (nodeCount + 2) (fun index => index % 3 == seed % 3)] do
          require (coloringStateKey (enableMoves indices state) ==
              coloringStateKey (enableMovesReference indices state))
            "move reactivation changed state"

def testCoalescingDegrees : Except String Unit := do
  for seed in [:12] do
    let variables := (List.range 28).toArray.map fun index =>
      ({ type := if index % 3 == 1 then .Tfloat else .Tint
         fixed := if index == 0 then some (.R .AX)
           else if index == 1 then some (.R .X0)
           else if index == 2 then some (.S .Local (number 0) .Tint) else none } : Variable)
    let function : XFunction := {
      signature := sign [], stacksize := number 0, variables, blocks := #[], entry := 0 }
    let mut graph : Interference := {
      adjacency := Array.replicate variables.size {}
      preferences := Array.replicate variables.size {}
      costs := (List.range variables.size).toArray.map fun index =>
        { amount := index + 1, stackOnly := index > 2 && index % 7 == 0 } }
    for left in [:variables.size] do
      graph := graphTouch left graph
      for right in [:left] do
        if (left * 17 + right * 13 + seed) % 7 < seed % 5 then
          graph := graphEdge left right (graphEdge left right graph)
        else graph := graphPreference left right graph
    let mut state := initialColoring {} function graph
    checkDegrees function state
    checkCoalescingCriteria function state
    for left in [0, 1, 2, 5, 17, 27] do
      for right in [0, 1, 2, 5, 17, 27] do
        checkCombine {} function left right state
    for fixed in [0, 1] do
      if let some right := state.active.toList.find? fun right =>
          registerNode function right &&
          nodeClass function state.graph fixed == nodeClass function state.graph right &&
          !(state.graph.adjacency[fixed]?.getD {}).contains right then
        checkCombine {} function fixed right state
        state := combineNodes {} function fixed right state
        checkDegrees function state
    for _ in [:variables.size] do
      if let some left := state.active.min? then
        let partner := state.active.toList.find? fun right =>
          left != right && nodeClass function state.graph left == nodeClass function state.graph right &&
            !(state.graph.adjacency[left]?.getD {}).contains right
        if let some right := partner then
          checkCombine {} function left right state
          state := combineNodes {} function left right state
        else state := removeNode {} function left (freezeMoves {} function left state)
        checkDegrees function state
      else break
    require state.active.isEmpty "synthetic degree fixture did not drain"

def testCoalescingThresholds : Except String Unit := do
  for density in [0, 1, 4, 8, 12, 16, 17] do
    let variables := (List.range 64).toArray.map fun index =>
      ({ type := if index % 3 == 1 then .Tfloat else .Tint
         fixed := if index == 0 then some (.R .AX)
           else if index == 1 then some (.R .X0)
           else if index == 2 then some (.S .Local (number 0) .Tint) else none } : Variable)
    let function : XFunction := {
      signature := sign [], stacksize := number 0, variables, blocks := #[], entry := 0 }
    let mut graph : Interference := {
      adjacency := Array.replicate variables.size {}
      preferences := Array.replicate variables.size {}
      costs := (List.range variables.size).toArray.map fun index =>
        { amount := index + 1, stackOnly := index > 2 && index % 11 == 0 } }
    for left in [:variables.size] do
      graph := graphTouch left graph
      for right in [:left] do
        if (left * 19 + right * 13) % 17 < density then
          graph := graphEdge left right graph
    let state := initialColoring {} function graph
    checkCoalescingCriteria function state
    checkCoalescingCriteria function state { reserved := integerRemaining }
    let active := state.active.filter (fun index => index % 5 != density % 5)
    let state := { state with active, activeCache := IndexSetCache.empty active, degrees := #[] }
    let degrees := (List.range variables.size).toArray.map (uncachedDegree function state)
    checkCoalescingCriteria function { state with degrees }

def testIndexSetCache : Except String Unit := do
  for size in [0, 1, 2, 15, 64, 257] do
    for density in [:5] do
      let indices := setOfList ((List.range (size + 5)).filter fun index => index % 5 < density)
      for width in [0, size / 2, size, size + 10] do
        let mut state : ColoringState := {
          graph := { adjacency := #[], preferences := #[], costs := #[] }
          parents := #[], active := indices, nodeMoves := #[]
          activeCache := IndexSetCache.ofSet indices width }
        for removed in (List.range (size + 5)).reverse ++ [size + 10, 0] do
          for query in [:size + 11] do
            require (IndexSetCache.contains state.active state.activeCache query == state.active.contains query)
              "bounded membership cache changed a query"
          state := { state with
            active := state.active.erase removed
            activeCache := IndexSetCache.erase state.active state.activeCache removed }

def tests : Except String (List (String × AllocationStats)) := do
  testIndexSetCache
  testClassification
  testFixedLocationLookup
  testBasic
  let results ← testPressure
  testCallsAndConstraints
  testBuiltins
  testReloadReuse
  testMoveActivation
  testDegreeCache
  testCoalescingDegrees
  testCoalescingThresholds
  return results

end AllocatorTests

def main : IO UInt32 := do
  match AllocatorTests.tests with
  | .error message =>
      (← IO.getStderr).putStrLn ("allocator tests: FAIL: " ++ message)
      return 1
  | .ok results =>
      for (name, stats) in results do IO.println (name ++ ": " ++ reprStr stats)
      IO.println "allocator tests: PASS"
      return 0
