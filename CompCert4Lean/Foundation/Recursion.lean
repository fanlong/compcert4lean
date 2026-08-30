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
