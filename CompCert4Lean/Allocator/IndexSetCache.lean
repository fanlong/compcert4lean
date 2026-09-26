import CompCert4Lean.Allocator.TargetConstraints
import Std.Data.TreeSet.Lemmas

namespace CompCert4Lean.Allocator

def IndexSetCache (indices : IndexSet) :=
  { flags : Array Bool // ∀ index (bound : index < flags.size),
      flags[index] = indices.contains index }

namespace IndexSetCache

def empty (indices : IndexSet) : IndexSetCache indices :=
  ⟨#[], by intro index bound; simp at bound⟩

def ofSet (indices : IndexSet) (size : Nat) : IndexSetCache indices :=
  ⟨Array.ofFn (fun index : Fin size => indices.contains index.val), by
    intro index bound
    simp⟩

@[inline] def contains (indices : IndexSet) (cache : IndexSetCache indices)
    (index : Nat) : Bool :=
  if bound : index < cache.val.size then cache.val[index] else indices.contains index

theorem contains_eq (indices : IndexSet) (cache : IndexSetCache indices)
    (index : Nat) : contains indices cache index = indices.contains index := by
  unfold contains
  split
  · exact cache.property _ _
  · rfl

def erase (indices : IndexSet) (cache : IndexSetCache indices)
    (index : Nat) : IndexSetCache (indices.erase index) :=
  ⟨cache.val.setIfInBounds index false, by
    intro query bound
    have oldBound : query < cache.val.size := by simpa using bound
    rw [Array.getElem_setIfInBounds oldBound]
    by_cases same : index = query
    · simp [same]
    · simp [same, cache.property query oldBound, Std.compare_eq_iff_eq]⟩

def insert (indices : IndexSet) (cache : IndexSetCache indices)
    (index : Nat) : IndexSetCache (indices.insert index) :=
  ⟨cache.val.setIfInBounds index true, by
    intro query bound
    have oldBound : query < cache.val.size := by simpa using bound
    rw [Array.getElem_setIfInBounds oldBound]
    by_cases same : index = query
    · simp [same]
    · simp [same, cache.property query oldBound, Std.compare_eq_iff_eq]⟩

end IndexSetCache

end CompCert4Lean.Allocator
