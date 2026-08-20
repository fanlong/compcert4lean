import CompCert4Lean.Lib.FSetFacts

/-!
# Generic finite-set decision surface

The Rocq file is tactic-heavy.  This translation preserves its nested
functor/carrier layout and the proposition/type descriptors used by later
specializations; executable decisions remain ordinary Lean definitions.
-/

namespace CompCert4Lean.Lib.FSetDecide

open CompCert4Lean.Lib.FSetInterface
open CompCert4Lean.Lib.FSetFacts

abbrev F (E : DecidableType) (M : WSfun E) := WFacts_fun E M

def F.make (E : DecidableType) (M : WSfun E) : F E M :=
  WFacts_fun.make E M

namespace F

abbrev elt {E : DecidableType} {M : WSfun E} (f : F E M) : Type := f.E.t
abbrev t {E : DecidableType} {M : WSfun E} (f : F E M) : Type := f.M.t
abbrev In {E : DecidableType} {M : WSfun E} (f : F E M) := f.M.In
abbrev Equal {E : DecidableType} {M : WSfun E} (f : F E M) := f.M.Equal
abbrev Subset {E : DecidableType} {M : WSfun E} (f : F E M) := f.M.Subset
abbrev Empty {E : DecidableType} {M : WSfun E} (f : F E M) := f.M.Empty

end F

structure WDecide_fun (E : DecidableType) (M : WSfun E) : Type 2 where
  F : F E M := F.make E M

abbrev WDecide := WDecide_fun
abbrev Decide := WDecide

namespace WDecide_fun

def make (E : DecidableType) (M : WSfun E) : WDecide_fun E M := ⟨F.make E M⟩

structure FSetLogicalFacts (E : DecidableType) (M : WSfun E) : Type 3 where
  source : WDecide_fun E M

structure FSetDecideAuxiliary (E : DecidableType) (M : WSfun E) : Type 3 where
  source : WDecide_fun E M

structure FSetDecideTestCases (E : DecidableType) (M : WSfun E) : Type 3 where
  source : WDecide_fun E M

namespace FSetLogicalFacts

def test_push (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ P Q R : Prop, (P ∨ ¬ P) → (Q ∨ ¬ Q) →
    (¬ True) → (¬ False) → (¬ ¬ P) →
    (¬ (P ∧ Q) → ¬ R) → ((P ∧ Q) ∨ ¬ R) →
    (¬ (P ∧ Q) ∨ R) → (R ∨ ¬ (P ∧ Q)) →
    (¬ R ∨ (P ∧ Q)) → (¬ P → R) →
    (¬ ((R → P) ∨ (Q → R))) → ¬ (P ∧ R) →
    ¬ (P → R) → True

def test_pull (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ P Q R : Prop, (P ∨ ¬ P) → (Q ∨ ¬ Q) →
    (¬ True) → (¬ False) → (¬ ¬ P) →
    ((¬ (P ∧ Q) → ¬ R)) → ((P ∧ Q) ∨ ¬ R) →
    (¬ (P ∧ Q) ∨ R) → (R ∨ ¬ (P ∧ Q)) →
    (¬ R ∨ (P ∧ Q)) → (¬ P → R) →
    ((¬ (R → P) ∧ ¬ (Q → R))) →
    (¬ P ∨ ¬ R) → (P ∧ ¬ R) → (¬ R ∧ P) → True

end FSetLogicalFacts

namespace FSetDecideAuxiliary

inductive FSet_elt_Prop {E : DecidableType} {M : WSfun E} : Prop → Prop where
  | eq_Prop {S : Type} (x y : S) : FSet_elt_Prop (x = y)
  | eq_elt_prop (x y : E.t) : FSet_elt_Prop (E.eq x y)
  | In_elt_prop (x : E.t) (s : M.t) : FSet_elt_Prop (M.In x s)
  | True_elt_prop : FSet_elt_Prop True
  | False_elt_prop : FSet_elt_Prop False
  | conj_elt_prop {P Q : Prop} : FSet_elt_Prop P → FSet_elt_Prop Q →
      FSet_elt_Prop (P ∧ Q)
  | disj_elt_prop {P Q : Prop} : FSet_elt_Prop P → FSet_elt_Prop Q →
      FSet_elt_Prop (P ∨ Q)
  | impl_elt_prop {P Q : Prop} : FSet_elt_Prop P → FSet_elt_Prop Q →
      FSet_elt_Prop (P → Q)
  | not_elt_prop {P : Prop} : FSet_elt_Prop P → FSet_elt_Prop (¬ P)

inductive FSet_Prop {E : DecidableType} {M : WSfun E} : Prop → Prop where
  | elt_FSet_Prop {P : Prop} : FSet_elt_Prop (E := E) (M := M) P → FSet_Prop P
  | Empty_FSet_Prop (s : M.t) : FSet_Prop (M.Empty s)
  | Subset_FSet_Prop (s s' : M.t) : FSet_Prop (M.Subset s s')
  | Equal_FSet_Prop (s s' : M.t) : FSet_Prop (M.Equal s s')

def eq_refl_iff (E : DecidableType) (x : E.t) : Prop := E.eq x x ↔ True

def dec_In (E : DecidableType) (M : WSfun E) (x : E.t) (s : M.t) : Prop :=
  M.In x s ∨ ¬ M.In x s

def dec_eq (E : DecidableType) (x y : E.t) : Prop :=
  E.eq x y ∨ ¬ E.eq x y

end FSetDecideAuxiliary

namespace FSetDecideTestCases

def test_eq_trans_1 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ x y z s, E.eq x y → ¬ ¬ E.eq z y → M.In x s → M.In z s

def test_eq_trans_2 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ x y z r s, M.In x (M.singleton y) → ¬ M.In z r →
    ¬ ¬ M.In z (M.add y r) → M.In x s → M.In z s

def test_eq_neq_trans_1 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ w x y z s, E.eq x w → ¬ ¬ E.eq x y → ¬ E.eq y z →
    M.In w s → M.In w (M.remove z s)

def test_eq_neq_trans_2 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ w x y z r1 r2 s, M.In x (M.singleton w) → ¬ M.In x r1 →
    M.In x (M.add y r1) → M.In y r2 → M.In y (M.remove z r2) →
    M.In w s → M.In w (M.remove z s)

def test_In_singleton (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ x, M.In x (M.singleton x)

def test_add_In (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ x y s, M.In x (M.add y s) → ¬ E.eq x y → M.In x s

def test_Subset_add_remove (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ x s, M.Subset s (M.add x (M.remove x s))

def test_eq_disjunction (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ w x y z, M.In w (M.add x (M.add y (M.singleton z))) →
    E.eq w x ∨ E.eq w y ∨ E.eq w z

def test_not_In_disj (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ x y s1 s2 s3 s4,
    ¬ M.In x (M.union s1 (M.union s2 (M.union s3 (M.add y s4)))) →
    ¬ (M.In x s1 ∨ M.In x s4 ∨ E.eq y x)

def test_not_In_conj (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ x y s1 s2 s3 s4,
    ¬ M.In x (M.union s1 (M.union s2 (M.union s3 (M.add y s4)))) →
    (¬ M.In x s1 ∧ ¬ M.In x s4 ∧ ¬ E.eq y x)

def test_iff_conj (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ a x s s', (M.In a s' ↔ E.eq x a ∨ M.In a s) →
    (M.In a s' ↔ M.In a (M.add x s))

def test_set_ops_1 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ x q r s, M.Subset (M.singleton x) s → M.Empty (M.union q r) →
    M.Empty (M.inter (M.diff s q) (M.diff s r)) → ¬ M.In x s

def eq_chain_test (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ x1 x2 x3 x4 s1 s2 s3 s4, M.Empty s1 →
    M.In x2 (M.add x1 s1) → M.In x3 s2 →
    ¬ M.In x3 (M.remove x2 s2) → ¬ M.In x4 s3 →
    M.In x4 (M.add x3 s3) → M.In x1 s4 →
    M.Subset (M.add x4 s4) s4

def test_too_complex (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ (x y z : E.t) (r s : M.t), E.eq x y →
    (M.In x (M.singleton y) → M.Subset r s) → M.In z r → M.In z s

def function_test_1 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ (f : M.t → M.t) (g : E.t → E.t) (s1 s2 : M.t) (x1 x2 : E.t),
    M.Equal s1 (f s2) → E.eq x1 (g (g x2)) → M.In x1 s1 →
    M.In (g (g x2)) (f s2)

def function_test_2 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ (f : M.t → M.t) (g : E.t → E.t) (s1 s2 : M.t) (x1 x2 : E.t),
    M.Equal s1 (f s2) → E.eq x1 (g x2) → M.In x1 s1 →
    g x2 = g (g x2) → M.In (g (g x2)) (f s2)

def test_baydemir (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ (f : M.t → M.t) (s : M.t) (x y : E.t),
    M.In x (M.add y (f s)) → ¬ E.eq x y → M.In x (f s)

end FSetDecideTestCases

end WDecide_fun

namespace WDecide

def ofWS (M : WS) : WDecide_fun M.E M.toWSfun := WDecide_fun.make M.E M.toWSfun

end WDecide

end CompCert4Lean.Lib.FSetDecide
