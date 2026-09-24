import CompCert4Lean.Allocator.Coloring

namespace CompilerOptimization

open CompCert4Lean.Allocator

def activateMove (state : ColoringState) (move : Nat) : ColoringState :=
  { state with activeMoves := state.activeMoves.erase move, workMoves := state.workMoves.insert move }

def activateIfPresent (state : ColoringState) (move : Nat) : ColoringState :=
  if state.activeMoves.contains move then activateMove state move else state

theorem activationList_eq (items : List Nat)
    (distinct : items.Pairwise (fun left right => compare left right ≠ .eq))
    (state : ColoringState) :
    items.foldl activateIfPresent state =
      (items.filter state.activeMoves.contains).foldl activateMove state := by
  induction items generalizing state with
  | nil => rfl
  | cons move remaining inductionHypothesis =>
      have properties := List.pairwise_cons.mp distinct
      simp only [List.foldl_cons]
      cases present : state.activeMoves.contains move with
      | false =>
          rw [show activateIfPresent state move = state by simp [activateIfPresent, present]]
          rw [inductionHypothesis properties.2 state]
          simp only [List.filter_cons, present, Bool.false_eq_true, if_false]
      | true =>
          have remainingFilter : remaining.filter (activateMove state move).activeMoves.contains =
              remaining.filter state.activeMoves.contains := by
            apply List.filter_congr
            intro other member
            simp [activateMove, Std.TreeSet.contains_erase, properties.1 other member]
          rw [show activateIfPresent state move = activateMove state move by
            simp [activateIfPresent, present]]
          rw [inductionHypothesis properties.2 (activateMove state move), remainingFilter]
          simp [present, List.foldl_cons]

theorem intersectionSequence_eq (left right : IndexSet) :
    left.toList.filter right.contains = right.toList.filter left.contains := by
  rw [← Std.TreeSet.toList_filter, ← Std.TreeSet.toList_filter]
  apply Std.TreeSet.Equiv.toList_eq
  apply Std.TreeSet.Equiv.of_forall_mem_iff
  intro element
  simp [Std.TreeSet.mem_filter, Std.TreeSet.get_eq, Std.TreeSet.contains_iff_mem, and_comm]

def enableNodeMovesOriginal (moves : IndexSet) (state : ColoringState) : ColoringState :=
  moves.foldl activateIfPresent state

def enableNodeMovesReversed (moves : IndexSet) (state : ColoringState) : ColoringState :=
  state.activeMoves.foldl (fun state move =>
    if moves.contains move then activateMove state move else state) state

theorem enableNodeMovesReversed_eq (moves : IndexSet) (state : ColoringState) :
    enableNodeMovesReversed moves state = enableNodeMovesOriginal moves state := by
  unfold enableNodeMovesReversed enableNodeMovesOriginal
  rw [Std.TreeSet.foldl_eq_foldl_toList, Std.TreeSet.foldl_eq_foldl_toList]
  rw [activationList_eq moves.toList moves.distinct_toList state]
  rw [← List.foldl_filter, intersectionSequence_eq]

def enableNodeMovesSmaller (moves : IndexSet) (state : ColoringState) : ColoringState :=
  if state.activeMoves.size < moves.size then enableNodeMovesReversed moves state
  else enableNodeMovesOriginal moves state

theorem enableNodeMovesSmaller_eq (moves : IndexSet) (state : ColoringState) :
    enableNodeMovesSmaller moves state = enableNodeMovesOriginal moves state := by
  unfold enableNodeMovesSmaller
  split
  next => exact enableNodeMovesReversed_eq moves state
  next => rfl

def enableMovesOriginal (indices : IndexSet) (state : ColoringState) : ColoringState :=
  indices.foldl (fun state index =>
    enableNodeMovesOriginal (state.nodeMoves[index]?.getD {}) state) state

def enableMovesSmaller (indices : IndexSet) (state : ColoringState) : ColoringState :=
  indices.foldl (fun state index =>
    enableNodeMovesSmaller (state.nodeMoves[index]?.getD {}) state) state

theorem enableMovesSmaller_eq (indices : IndexSet) (state : ColoringState) :
    enableMovesSmaller indices state = enableMovesOriginal indices state := by
  simp only [enableMovesSmaller, enableMovesOriginal, enableNodeMovesSmaller_eq]

#print axioms enableMovesSmaller_eq

theorem productionEnableMoves_eq (indices : IndexSet) (state : ColoringState) :
    CompCert4Lean.Allocator.enableMoves indices state =
      if state.activeMoves.isEmpty then state else enableMovesOriginal indices state := by
  change (if state.activeMoves.isEmpty then state else enableMovesSmaller indices state) = _
  rw [enableMovesSmaller_eq]

#print axioms productionEnableMoves_eq

end CompilerOptimization
