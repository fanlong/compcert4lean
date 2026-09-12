import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.Ordered

/-!
# Rocq well-founded recursion compatibility surface

The executable adapters in this module reuse Lean's checked accessibility and
well-founded fixpoint primitives.  Theorems assigned to later proof migration
are represented only by their exact statement descriptors.
-/

namespace CompCert4Lean.Foundation.Recursion
namespace Rocq.Coq

namespace Init.Wf

/-! The source accessibility predicate is a carrier in its own right.  Keep
    the relation as an explicit parameter and expose the source constructor
    name, rather than abbreviating Lean's similarly shaped primitive. -/

inductive Acc {A : Type} (R : A → A → Prop) : A → Prop where
  | Acc_intro (x : A) (h : ∀ y : A, R y x → Acc R y) : Acc R x

export Acc (Acc_intro)

abbrev well_founded {A : Type} (R : A → A → Prop) : Prop :=
  ∀ a : A, Acc R a

private theorem toLeanAcc {A : Type} {R : A → A → Prop} {x : A}
    (h : Acc R x) : _root_.Acc R x := by
  induction h with
  | Acc_intro x h ih =>
      exact _root_.Acc.intro x (fun y hy => ih y hy)

private theorem sourceAccOfLean {A : Type} {R : A → A → Prop} {x : A}
    (h : _root_.Acc R x) : Acc R x := by
  induction h with
  | intro x h ih =>
      exact Acc.Acc_intro x (fun y hy => ih y hy)

instance {A : Type} {R : A → A → Prop} :
    Coe (_root_.WellFounded R) (well_founded R) where
  coe h x := sourceAccOfLean (h.apply x)

def Fix {A : Type} {R : A → A → Prop}
    (Rwf : well_founded R) (P : A → Type)
    (F : ∀ x : A, (∀ y : A, R y x → P y) → P x) (x : A) : P x :=
  _root_.WellFounded.fix
    (⟨fun a => toLeanAcc (Rwf a)⟩ : _root_.WellFounded R) F x

def Fix_eqStatement :=
  ∀ {A : Type} {R : A → A → Prop}
    (Rwf : well_founded R) (P : A → Type)
    (F : ∀ x : A, (∀ y : A, R y x → P y) → P x)
    (_ : ∀ (x : A) (f g : ∀ y : A, R y x → P y),
      (∀ (y : A) (p : R y x), f y p = g y p) → F x f = F x g)
    (x : A),
    Fix Rwf P F x = F x (fun (y : A) (_ : R y x) => Fix Rwf P F y)

def well_founded_indStatement :=
  ∀ {A : Type} {R : A → A → Prop}
    (_ : well_founded R) (P : A → Prop)
    (_ : ∀ x : A, (∀ y : A, R y x → P y) → P x) (a : A), P a

def well_founded_induction_typeStatement :=
  ∀ {A : Type} {R : A → A → Prop}
    (_ : well_founded R) (P : A → Type)
    (_ : ∀ x : A, (∀ y : A, R y x → P y) → P x) (a : A), P a

end Init.Wf

namespace Arith.Wf_nat

abbrev iter_nat (n : Nat) (A : Type) (f : A → A) (x : A) : A :=
  Nat.rec x (fun _ value => f value) n

def ltof (A : Type) (f : A → Nat) (a b : A) : Prop :=
  f a < f b

def lt_wf_indStatement :=
  ∀ (n : Nat) (P : Nat → Prop)
    (_ : ∀ n₀ : Nat, (∀ m : Nat, m < n₀ → P m) → P n₀), P n

def lt_wfStatement :=
  Init.Wf.well_founded (fun x y : Nat => x < y)

def well_founded_lt_compatStatement :=
  ∀ (A : Type) (f : A → Nat) (R : A → A → Prop)
    (_ : ∀ x y : A, R x y → f x < f y), Init.Wf.well_founded R

def well_founded_ltofStatement :=
  ∀ (A : Type) (f : A → Nat), Init.Wf.well_founded (ltof A f)

end Arith.Wf_nat

namespace Wellfounded.Inverse_Image

def wf_inverse_imageStatement :=
  ∀ (A B : Type) (R : B → B → Prop) (f : A → B)
    (_ : Init.Wf.well_founded R),
    Init.Wf.well_founded (fun x y : A => R (f x) (f y))

end Wellfounded.Inverse_Image

namespace Wellfounded.Transitive_Closure

def wf_clos_transStatement :=
  ∀ (A : Type) (R : A → A → Prop) (_ : Init.Wf.well_founded R),
    Init.Wf.well_founded
      (_root_.CompCert4Lean.Foundation.Ordered.Rocq.Coq.Relations.Relation_Operators.clos_trans
        A R)

end Wellfounded.Transitive_Closure

namespace ZArith.Wf_Z

def natlike_indStatement :=
  ∀ (P : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z → Prop)
    (_ : P _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0)
    (_ : ∀ x : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z,
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0 x →
      P x →
      P (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.succ x))
    (x : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (_ : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0 x), P x

end ZArith.Wf_Z

namespace ZArith.Zwf

def Zwf
    (c x y : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : Prop :=
  _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le c y ∧
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt x y

def Zwf_up
    (c x y : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : Prop :=
  _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt y x ∧
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le x c

def Zwf_up_well_foundedStatement :=
  ∀ c : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z,
    Init.Wf.well_founded (Zwf_up c)

def Zwf_well_foundedStatement :=
  ∀ c : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z,
    Init.Wf.well_founded (Zwf c)

end ZArith.Zwf

end Rocq.Coq
end CompCert4Lean.Foundation.Recursion

namespace CompCert4Lean.Foundation.Recursion
namespace Rocq.Coq
namespace Arith.Wf_nat

theorem well_founded_lt_compat : well_founded_lt_compatStatement := by
  intro A f R compat
  have H : ∀ n (a : A), f a < n → Init.Wf.Acc R a := by
    intro n
    induction n with
    | zero =>
        intro a ha
        exact False.elim (Nat.not_lt_zero _ ha)
    | succ n ih =>
        intro a ha
        apply Init.Wf.Acc_intro a
        intro b hba
        apply ih b
        exact Nat.lt_of_lt_of_le (compat b a hba) (Nat.le_of_lt_succ ha)
  intro a
  exact H (Nat.succ (f a)) a (Nat.lt_succ_self _)

theorem well_founded_ltof : well_founded_ltofStatement := by
  intro A f
  exact well_founded_lt_compat A f (ltof A f) (by
    intro x y h
    exact h)

theorem lt_wf : lt_wfStatement := by
  exact well_founded_ltof Nat (fun x : Nat => x)

theorem lt_wf_ind : lt_wf_indStatement := by
  intro n P step
  induction lt_wf n with
  | Acc_intro x h ih =>
      exact step x (fun y hy => ih y hy)

end Arith.Wf_nat
end Rocq.Coq
end CompCert4Lean.Foundation.Recursion

namespace CompCert4Lean.Foundation.Recursion
namespace Rocq.Coq

namespace Init.Wf

def well_founded_induction_type : well_founded_induction_typeStatement := by
  intro A R Rwf P step a
  exact Fix Rwf P step a

theorem well_founded_ind : well_founded_indStatement := by
  intro A R Rwf P step a
  exact (_root_.WellFounded.induction
    (⟨fun x => toLeanAcc (Rwf x)⟩ : _root_.WellFounded R) a step)

theorem Fix_eq : Fix_eqStatement := by
  intro A R Rwf P F F_ext x
  simpa [Fix] using
    (_root_.WellFounded.fix_eq
      (⟨fun a => toLeanAcc (Rwf a)⟩ : _root_.WellFounded R) F x)

end Init.Wf

namespace Wellfounded.Inverse_Image

theorem wf_inverse_image : wf_inverse_imageStatement := by
  intro A B R f Rwf
  have acc_inverse :
      ∀ (b : B), Init.Wf.Acc R b →
        ∀ (x : A), b = f x →
          Init.Wf.Acc (fun x y : A => R (f x) (f y)) x := by
    intro b hb
    induction hb with
    | Acc_intro b h ih =>
        intro x hx
        apply Init.Wf.Acc_intro x
        intro y hy
        apply ih (f y) ?_ y rfl
        simpa [hx] using hy
  intro x
  exact acc_inverse (f x) (Rwf (f x)) x rfl

end Wellfounded.Inverse_Image

end Rocq.Coq
end CompCert4Lean.Foundation.Recursion

namespace CompCert4Lean.Foundation.Recursion
namespace Rocq.Coq
namespace Wellfounded.Transitive_Closure

theorem wf_clos_trans : wf_clos_transStatement := by
  intro A R Rwf
  have acc_clos : ∀ (x : A), Init.Wf.Acc R x →
      Init.Wf.Acc
        (_root_.CompCert4Lean.Foundation.Ordered.Rocq.Coq.Relations.Relation_Operators.clos_trans
          A R) x := by
    intro x hx
    induction hx with
    | Acc_intro x h ih =>
        apply Init.Wf.Acc_intro x
        intro y hy
        induction hy with
        | t_step y x hR =>
            exact ih y hR
        | t_trans y z x h1 h2 ih1 ih2 =>
            have hz : Init.Wf.Acc
                (_root_.CompCert4Lean.Foundation.Ordered.Rocq.Coq.Relations.Relation_Operators.clos_trans
                  A R) z := ih2 h ih
            cases hz with
            | Acc_intro z hz => exact hz y h1
  intro x
  exact acc_clos x (Rwf x)

end Wellfounded.Transitive_Closure
end Rocq.Coq
end CompCert4Lean.Foundation.Recursion

namespace CompCert4Lean.Foundation.Recursion
namespace Rocq.Coq.ZArith.Zwf

open _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq
open _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt

theorem Zwf_well_founded : Zwf_well_foundedStatement := by
  intro c
  have H : ∀ (n : Nat) (a : Z),
      Int.toNat (intOfZ a - intOfZ c) < n ∨ intOfZ a < intOfZ c →
      Init.Wf.Acc (Zwf c) a := by
    intro n
    induction n with
    | zero =>
        intro a ha
        rcases ha with ha | ha
        · omega
        · apply Init.Wf.Acc_intro a
          intro b hab
          unfold Zwf at hab
          rcases hab with ⟨hca, hba⟩
          change intOfZ c ≤ intOfZ a at hca
          change intOfZ b < intOfZ a at hba
          omega
    | succ n ih =>
        intro a ha
        rcases ha with ha | ha
        · apply Init.Wf.Acc_intro a
          intro b hab
          unfold Zwf at hab
          rcases hab with ⟨hca, hba⟩
          change intOfZ c ≤ intOfZ a at hca
          change intOfZ b < intOfZ a at hba
          by_cases hbc : intOfZ b < intOfZ c
          · exact ih b (Or.inr hbc)
          · apply ih b
            left
            have hcb : intOfZ c ≤ intOfZ b := by omega
            have hdiffb : 0 ≤ intOfZ b - intOfZ c := by omega
            have hdiffa : 0 ≤ intOfZ a - intOfZ c := by omega
            have hltInt : intOfZ b - intOfZ c < intOfZ a - intOfZ c := by omega
            have hposA : 0 < intOfZ a - intOfZ c := by omega
            have hltNat := (Int.toNat_lt_toNat hposA).2 hltInt
            exact Nat.lt_of_lt_of_le hltNat (Nat.lt_succ_iff.mp ha)
        · apply Init.Wf.Acc_intro a
          intro b hab
          unfold Zwf at hab
          rcases hab with ⟨hca, hba⟩
          change intOfZ c ≤ intOfZ a at hca
          change intOfZ b < intOfZ a at hba
          omega
  intro a
  exact H (Int.toNat (intOfZ a - intOfZ c) + 1) a (Or.inl (Nat.lt_succ_self _))

end CompCert4Lean.Foundation.Recursion.Rocq.Coq.ZArith.Zwf
