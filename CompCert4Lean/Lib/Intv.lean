import CompCert4Lean.Foundation.Numbers

/-!
# Definitions and theorem surfaces for semi-open integer intervals

This module translates the definition-bearing surface of CompCert's
`lib/Intv.v`.  Proof-bearing declarations assigned to the later proof phase
are retained as exact proposition descriptors rather than theorem stubs.
-/

namespace CompCert4Lean.Lib.Intv

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

def interv : Type := Z × Z

/-! Membership in a semi-open interval. -/

def In (x : Z) (i : interv) : Prop :=
  ZArith.BinInt.Z.le i.1 x ∧ ZArith.BinInt.Z.lt x i.2

/-! Empty intervals have their lower bound at or above their upper bound. -/

def empty (i : interv) : Prop :=
  ZArith.BinInt.Z.ge i.1 i.2

/-! Two intervals are disjoint when no element belongs to both. -/

def disjoint (i j : interv) : Prop :=
  ∀ x, In x i → ¬ In x j

/-!
Exact proposition surfaces for the theorem declarations whose proof bodies
belong to the later proof-migration phase.
-/

def disjoint_rangeStatement : Prop :=
  ∀ i j : interv,
    (ZArith.BinInt.Z.le i.2 j.1 ∨
      ZArith.BinInt.Z.le j.2 i.1) →
      disjoint i j

def range_disjointStatement : Prop :=
  ∀ i j : interv,
    disjoint i j →
      empty i ∨ empty j ∨
        ZArith.BinInt.Z.le i.2 j.1 ∨
          ZArith.BinInt.Z.le j.2 i.1

def range_disjoint'Statement : Prop :=
  ∀ i j : interv,
    disjoint i j →
      ZArith.BinInt.Z.lt i.1 i.2 →
        ZArith.BinInt.Z.lt j.1 j.2 →
          ZArith.BinInt.Z.le i.2 j.1 ∨
            ZArith.BinInt.Z.le j.2 i.1

end CompCert4Lean.Lib.Intv

namespace CompCert4Lean.Lib.Intv

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem disjoint_range : disjoint_rangeStatement := by
  unfold disjoint_rangeStatement disjoint
  intro i j h x hxi hxj
  unfold In at hxi hxj
  rcases h with h | h
  · unfold ZArith.BinInt.Z.le at h
    unfold ZArith.BinInt.Z.le ZArith.BinInt.Z.lt at hxi hxj
    omega
  · unfold ZArith.BinInt.Z.le at h
    unfold ZArith.BinInt.Z.le ZArith.BinInt.Z.lt at hxi hxj
    omega

theorem range_disjoint : range_disjointStatement := by
  unfold range_disjointStatement
  intro i j hd
  by_cases hi : ZArith.BinInt.Z.lt i.1 i.2
  · by_cases hj : ZArith.BinInt.Z.lt j.1 j.2
    · right; right
      by_cases hstart : ZArith.BinInt.Z.lt i.1 j.1
      · by_cases hend : ZArith.BinInt.Z.le i.2 j.1
        · exact Or.inl hend
        · exfalso
          exact (hd j.1
            (by
              unfold In
              constructor
              · unfold ZArith.BinInt.Z.lt at hstart
                unfold ZArith.BinInt.Z.le
                omega
              · unfold ZArith.BinInt.Z.lt at hi ⊢
                unfold ZArith.BinInt.Z.le at hend
                omega))
            (by
              unfold In
              constructor
              · exact Int.le_refl _
              · unfold ZArith.BinInt.Z.lt at hj ⊢
                omega)
      · by_cases hend : ZArith.BinInt.Z.le j.2 i.1
        · exact Or.inr hend
        · exfalso
          exact (hd i.1
            (by
              unfold In
              constructor
              · exact Int.le_refl _
              · unfold ZArith.BinInt.Z.lt at hi ⊢
                omega)
            (by
              unfold In
              constructor
              · unfold ZArith.BinInt.Z.lt at hstart
                unfold ZArith.BinInt.Z.le
                omega
              · unfold ZArith.BinInt.Z.lt at hj ⊢
                unfold ZArith.BinInt.Z.le at hend
                omega))
    · right; left
      unfold empty ZArith.BinInt.Z.ge
      unfold ZArith.BinInt.Z.lt at hj
      omega
  · left
    unfold empty ZArith.BinInt.Z.ge
    unfold ZArith.BinInt.Z.lt at hi
    omega

theorem range_disjoint' : range_disjoint'Statement := by
  unfold range_disjoint'Statement
  intro i j hd hi hj
  rcases range_disjoint i j hd with hei | hrest
  · exfalso
    unfold empty ZArith.BinInt.Z.ge at hei
    unfold ZArith.BinInt.Z.lt at hi
    omega
  rcases hrest with hej | horders
  · exfalso
    unfold empty ZArith.BinInt.Z.ge at hej
    unfold ZArith.BinInt.Z.lt at hj
    omega
  exact horders

end CompCert4Lean.Lib.Intv
