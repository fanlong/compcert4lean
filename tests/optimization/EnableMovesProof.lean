import CompCert4Lean.Allocator.Coloring

namespace CompilerOptimization

open CompCert4Lean.Allocator

def enableNodeMovesOriginal (moves : IndexSet) (state : ColoringState) : ColoringState :=
  moves.foldl (fun state move =>
    if state.activeMoves.contains move then
      { state with activeMoves := state.activeMoves.erase move, workMoves := state.workMoves.insert move }
    else state) state

def enableMovesOriginal (indices : IndexSet) (state : ColoringState) : ColoringState :=
  indices.foldl (fun state index => enableNodeMovesOriginal (state.nodeMoves[index]?.getD {}) state) state

theorem enableNodeMoves_empty (moves : IndexSet) (state : ColoringState)
    (empty : state.activeMoves.isEmpty) : enableNodeMovesOriginal moves state = state := by
  have absent := Std.TreeSet.isEmpty_iff_forall_contains.mp empty
  unfold enableNodeMovesOriginal
  rw [Std.TreeSet.foldl_eq_foldl_toList]
  have loop (items : List Nat) : items.foldl (fun state move =>
      if state.activeMoves.contains move then
        { state with activeMoves := state.activeMoves.erase move, workMoves := state.workMoves.insert move }
      else state) state = state := by
    induction items with
    | nil => rfl
    | cons move remaining inductionHypothesis =>
        simpa only [List.foldl_cons, absent move, Bool.false_eq_true, if_false] using inductionHypothesis
  exact loop moves.toList

theorem enableMoves_empty (indices : IndexSet) (state : ColoringState)
    (empty : state.activeMoves.isEmpty) : enableMovesOriginal indices state = state := by
  unfold enableMovesOriginal
  rw [Std.TreeSet.foldl_eq_foldl_toList]
  have loop (items : List Nat) : items.foldl (fun state index =>
      enableNodeMovesOriginal (state.nodeMoves[index]?.getD {}) state) state = state := by
    induction items with
    | nil => rfl
    | cons index remaining inductionHypothesis =>
        simpa only [List.foldl_cons, enableNodeMoves_empty _ state empty] using inductionHypothesis
  exact loop indices.toList

def enableMovesGuarded (indices : IndexSet) (state : ColoringState) : ColoringState :=
  if state.activeMoves.isEmpty then state else enableMovesOriginal indices state

theorem enableMovesGuarded_eq (indices : IndexSet) (state : ColoringState) :
    enableMovesGuarded indices state = enableMovesOriginal indices state := by
  unfold enableMovesGuarded
  split
  next empty => exact (enableMoves_empty indices state empty).symm
  next => rfl

#print axioms enableMovesGuarded_eq

end CompilerOptimization
