import CompCert4Lean.Allocator.TargetConstraints
import CompCert4Lean.Backend.RTLtyping

namespace CompCert4Lean.Allocator

open Backend Backend.Registers Lib.Maps
open Foundation.Numbers.Rocq.Coq

def regKey (register : reg) : Nat := PArith.BinPos.Pos.to_nat register

structure Variable where
  type : Common.AST.typ
  fixed : Option Backend.Locations.loc := none

structure RangeInfo where
  before : IndexMap := {}
  after : IndexMap := {}
  uses : IndexMap := {}
  definitions : IndexMap := {}
  successors : List Nat := []
  predecessors : List Nat := []

structure RangeState where
  variables : Array Variable := #[]
  parents : Array Nat := #[]
  entries : Array RangeInfo := #[]

def rangeRoot (parents : Array Nat) (index : Nat) : Nat :=
  let rec search : Nat → Nat → Nat
    | 0, current => current
    | fuel + 1, current =>
        let parent := parents[current]?.getD current
        if parent == current then current else search fuel parent
  search parents.size index

def unifyRanges (left right : Nat) (state : RangeState) : RangeState :=
  let left := rangeRoot state.parents left
  let right := rangeRoot state.parents right
  if left == right then state
  else { state with parents := state.parents.set! (max left right) (min left right) }

def mergeRanges (left right : IndexMap) (state : RangeState) : IndexMap × RangeState :=
  right.foldl (fun (result, state) key value =>
    match result[key]? with
    | none => (result.insert key value, state)
    | some previous => (result, unifyRanges previous value state)) (left, state)

def newRange (type : Common.AST.typ) (state : RangeState) : Nat × RangeState :=
  let index := state.variables.size
  (index, { state with
    variables := state.variables.push { type }
    parents := state.parents.push index })

def addRanges (types : RTLtyping.regenv) (registers : List reg)
    (state : RangeState) : IndexMap × RangeState :=
  registers.foldl (fun (result, state) register =>
    if result.contains (regKey register) then (result, state)
    else
      let (index, state) := newRange (types register) state
      (result.insert (regKey register) index, state)) ({}, state)

def splitStep (index : Nat) (state : RangeState) : RangeState × Bool := Id.run do
  let some entry := state.entries[index]? | return (state, false)
  let mut state := state
  let mut after := entry.after
  for successor in entry.successors do
    let next := (state.entries[successor]?.getD {}).before
    let (merged, nextState) := mergeRanges after next state
    after := merged
    state := nextState
  for (key, definition) in entry.definitions.toList do
    if let some liveRange := after[key]? then
      state := unifyRanges definition liveRange state
  let across := entry.definitions.foldl (fun result key _ => result.erase key) after
  let (before, state') := mergeRanges entry.before across state
  let (before, state') := mergeRanges before entry.uses state'
  let changed := before.size != entry.before.size
  return ({ state' with entries := state'.entries.set! index { entry with before, after } }, changed)

def splitFixpoint : Nat → List Nat → IndexSet → RangeState → Except String RangeState
  | 0, _, _, _ => .error "live-range splitting exhausted its worklist bound"
  | _ + 1, [], _, state => .ok state
  | fuel + 1, index :: pending, queued, state =>
      let queued := queued.erase index
      let (state, changed) := splitStep index state
      let (pending, queued) :=
        if changed then
          (state.entries[index]?.getD {}).predecessors.foldl
            (fun (pending, queued) predecessor =>
              if queued.contains predecessor then (pending, queued)
              else (predecessor :: pending, queued.insert predecessor)) (pending, queued)
        else (pending, queued)
      splitFixpoint fuel pending queued state

def splitLiveRanges (source : RTL.function) (types : RTLtyping.regenv)
    : Except String (RangeState × IndexMap × Array (RTL.node × RTL.instruction)) := do
  let instructions := (PTree.elements source.fn_code).toArray
  let indices : Std.HashMap Nat Nat :=
    instructions.foldl (fun result pair => result.insert (regKey pair.1) result.size) {}
  let initialVariables := X86.Machregs.all_mregs.toArray.map fun register =>
    { type := X86.Machregs.mreg_type register
      fixed := some (.R register) : Variable }
  let mut state : RangeState :=
    { variables := initialVariables
      parents := (List.range initialVariables.size).toArray }
  for (_, instruction) in instructions do
    let (uses, nextState) := addRanges types (RTL.instr_uses instruction) state
    let (definitions, nextState) :=
      addRanges types (RTL.instr_defs instruction).toList nextState
    let successors ← (RTL.successors_instr instruction).mapM fun successor =>
      match indices[regKey successor]? with
      | some index => pure index
      | none => throw "RTL successor has no instruction"
    state := { nextState with entries := nextState.entries.push {
      before := uses, uses, definitions, successors } }
  for index in [:state.entries.size] do
    for successor in (state.entries[index]?.getD {}).successors do
      let next := state.entries[successor]?.getD {}
      let updated := { next with predecessors := index :: next.predecessors }
      state := { state with entries := state.entries.set! successor updated }
  let worklist := (List.range state.entries.size).reverse
  let fuel := (state.entries.size + 1) * (state.entries.size + 1) * (state.variables.size + 1)
  state ← splitFixpoint fuel worklist (setOfList worklist) state
  let some entry := indices[regKey source.fn_entrypoint]? |
    throw "RTL entry point has no instruction"
  let (parameters, nextState) := addRanges types source.fn_params state
  let (_, nextState) := mergeRanges parameters (state.entries[entry]?.getD {}).before nextState
  return (nextState, parameters, instructions)

end CompCert4Lean.Allocator
