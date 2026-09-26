import CompCert4Lean.Allocator.Coloring

namespace CompilerOptimization

open CompCert4Lean.Allocator

theorem insert_after_erase (indices : IndexSet) (index : Nat) :
    ((indices.erase index).insert index).toList = (indices.insert index).toList := by
  apply Std.TreeSet.Equiv.toList_eq
  apply Std.TreeSet.Equiv.of_forall_mem_iff
  intro query
  simp only [Std.TreeSet.mem_insert, Std.TreeSet.mem_erase]
  grind

def classifyDirect (context : AllocationContext) (function : XFunction)
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

def worklistView (state : ColoringState) : List Nat × List Nat × List Nat :=
  (state.simplify.toList, state.freeze.toList, state.spill.toList)

def omitWorklists (state : ColoringState) : ColoringState :=
  { state with simplify := {}, freeze := {}, spill := {} }

def classifyOriginal (context : AllocationContext) (function : XFunction)
    (index : Nat) (state : ColoringState) : ColoringState :=
  let state := { state with
    simplify := state.simplify.erase index
    freeze := state.freeze.erase index
    spill := state.spill.erase index }
  if !IndexSetCache.contains state.active state.activeCache index then state
  else if degree function state index >= nodeCapacity context function state index then
    { state with spill := state.spill.insert index }
  else if hasPendingMoves state index then
    { state with freeze := state.freeze.insert index }
  else { state with simplify := state.simplify.insert index }

theorem classifyDirect_worklists (context : AllocationContext) (function : XFunction)
    (index : Nat) (state : ColoringState) :
    worklistView (classifyDirect context function index state) =
      worklistView (classifyOriginal context function index state) := by
  unfold classifyDirect classifyOriginal
  change worklistView (if !IndexSetCache.contains state.active state.activeCache index then _
      else if degree function state index >= nodeCapacity context function state index then _
      else if hasPendingMoves state index then _ else _) =
    worklistView (if !IndexSetCache.contains state.active state.activeCache index then _
      else if degree function state index >= nodeCapacity context function state index then _
      else if hasPendingMoves state index then _ else _)
  by_cases active : (!IndexSetCache.contains state.active state.activeCache index) = true <;>
    by_cases high : degree function state index >= nodeCapacity context function state index <;>
    by_cases pending : hasPendingMoves state index = true <;>
    simp [active, high, pending, worklistView, insert_after_erase]

theorem classifyDirect_otherFields (context : AllocationContext) (function : XFunction)
    (index : Nat) (state : ColoringState) :
    omitWorklists (classifyDirect context function index state) =
      omitWorklists (classifyOriginal context function index state) := by
  unfold classifyDirect classifyOriginal
  change omitWorklists (if !IndexSetCache.contains state.active state.activeCache index then _
      else if degree function state index >= nodeCapacity context function state index then _
      else if hasPendingMoves state index then _ else _) =
    omitWorklists (if !IndexSetCache.contains state.active state.activeCache index then _
      else if degree function state index >= nodeCapacity context function state index then _
      else if hasPendingMoves state index then _ else _)
  by_cases active : (!IndexSetCache.contains state.active state.activeCache index) = true <;>
    by_cases high : degree function state index >= nodeCapacity context function state index <;>
    by_cases pending : hasPendingMoves state index = true <;>
    simp only [active, high, pending, Bool.false_eq_true, if_true, if_false]
  all_goals rfl

#print axioms insert_after_erase
#print axioms classifyDirect_worklists
#print axioms classifyDirect_otherFields

theorem productionClassify_eq (context : AllocationContext) (function : XFunction)
    (index : Nat) (state : ColoringState) :
    classify context function index state = classifyDirect context function index state := rfl

theorem productionClassify_worklists (context : AllocationContext) (function : XFunction)
    (index : Nat) (state : ColoringState) :
    worklistView (classify context function index state) =
      worklistView (classifyOriginal context function index state) :=
  classifyDirect_worklists context function index state

theorem productionClassify_otherFields (context : AllocationContext) (function : XFunction)
    (index : Nat) (state : ColoringState) :
    omitWorklists (classify context function index state) =
      omitWorklists (classifyOriginal context function index state) :=
  classifyDirect_otherFields context function index state

#print axioms productionClassify_eq
#print axioms productionClassify_worklists
#print axioms productionClassify_otherFields

end CompilerOptimization
