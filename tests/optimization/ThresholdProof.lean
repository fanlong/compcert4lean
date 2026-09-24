import CompCert4Lean.Allocator.Coloring

namespace CompilerOptimization

theorem threshold_equivalence (degree capacity : Nat) (overlap : Bool)
    (positive : 0 < capacity) :
    (decide (degree - (if overlap then 1 else 0) >= capacity)) =
      (decide (degree > capacity) || (degree == capacity && !overlap)) := by
  cases overlap <;> apply Bool.eq_iff_iff.mpr <;> simp <;> omega

theorem contribution_equivalence (degree capacity : Nat)
    (overlap precolored active : Bool) (positive : 0 < capacity) :
    (active && (precolored || decide (degree - (if overlap then 1 else 0) >= capacity))) =
      ((decide (degree > capacity) || precolored || (degree == capacity && !overlap)) && active) := by
  rw [threshold_equivalence degree capacity overlap positive]
  simp only [Bool.or_comm, Bool.or_left_comm, Bool.and_comm]

#print axioms threshold_equivalence
#print axioms contribution_equivalence

end CompilerOptimization
