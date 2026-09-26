import CompCert4Lean.Allocator.Coloring

open CompCert4Lean.Allocator

example (indices : IndexSet) (size index : Nat) :
    IndexSetCache.contains indices (IndexSetCache.ofSet indices size) index =
      indices.contains index := IndexSetCache.contains_eq _ _ _

example (indices : IndexSet) (cache : IndexSetCache indices) (removed query : Nat) :
    IndexSetCache.contains (indices.erase removed)
      (IndexSetCache.erase indices cache removed) query =
      (indices.erase removed).contains query := IndexSetCache.contains_eq _ _ _

#print axioms IndexSetCache.ofSet
#print axioms IndexSetCache.erase
#print axioms IndexSetCache.contains_eq
#print axioms CompCert4Lean.Allocator.findColoring
