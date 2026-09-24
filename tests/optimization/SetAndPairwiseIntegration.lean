import CompCert4Lean.Allocator.Analyses

open CompCert4Lean CompCert4Lean.Allocator

namespace SetAndPairwiseIntegration

theorem sameIndexSet_eq (left right : IndexSet) :
    sameIndexSet left right = (left.toList == right.toList) := by
  unfold sameIndexSet withPtrEq
  by_cases same : left.toList = right.toList
  · have sizes := congrArg List.length same
    simp only [Std.TreeSet.length_toList] at sizes
    simp [same, sizes]
  · simp [same]

theorem sharedSetChange_eq (left right : IndexSet) :
    (!sameIndexSet left right) = (left.toList != right.toList) := by
  rw [sameIndexSet_eq]
  rfl

theorem graphPairwise_eq_original (indices : List Nat) (graph : Interference) :
    graphPairwise indices graph =
      indices.foldl (fun graph index => graphLive index (setOfList indices) graph) graph := rfl

def checkSetEquality : Except String Unit := do
  for count in [0, 1, 2, 7, 31, 32, 33, 100, 1000] do
    let values := List.range count
    let original := setOfList values
    let independent := setOfList values.reverse
    let replacement := (original.erase 0).insert (count + 2)
    let added := original.insert (count + 1)
    for left in [original, independent, replacement, added] do
      for right in [left, original, independent, replacement, added] do
        unless sameIndexSet left right == (left.toList == right.toList) do
          throw "shared-set equality changed its result"
  return ()

end SetAndPairwiseIntegration

def main : IO UInt32 := do
  match SetAndPairwiseIntegration.checkSetEquality with
  | .error message => IO.eprintln message; return 1
  | .ok () => IO.println "integrated shared-set equality: PASS"; return 0

#print axioms CompCert4Lean.Allocator.sameIndexSet
#print axioms SetAndPairwiseIntegration.sameIndexSet_eq
#print axioms SetAndPairwiseIntegration.sharedSetChange_eq
#print axioms SetAndPairwiseIntegration.graphPairwise_eq_original
