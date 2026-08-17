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
