import CompCert4Lean.Foundation.Recursion

/-!
# Well-founded recursive function adapters

This module translates the executable `Fix` and `Fixm` definitions from
CompCert's `lib/Wfsimpl.v`.  The corresponding unrolling theorems are retained
as exact statement descriptors for the later proof-migration phase.
-/

namespace CompCert4Lean.Lib.Wfsimpl

def Fix {A B : Type} {R : A → A → Prop}
    (Rwf : CompCert4Lean.Foundation.Recursion.Rocq.Coq.Init.Wf.well_founded R)
    (F : ∀ x : A, (∀ y : A, R y x → B) → B)
    (x : A) : B :=
  CompCert4Lean.Foundation.Recursion.Rocq.Coq.Init.Wf.Fix
    Rwf (fun _ => B) F x

def unroll_FixStatement : Prop :=
  ∀ {A B : Type} {R : A → A → Prop}
    (Rwf : CompCert4Lean.Foundation.Recursion.Rocq.Coq.Init.Wf.well_founded R)
    (F : ∀ x : A, (∀ y : A, R y x → B) → B)
    (x : A),
    Fix Rwf F x = F x (fun (y : A) (_ : R y x) => Fix Rwf F y)

private theorem measureWellFounded {A : Type} (measure : A → Nat) :
    WellFounded (fun y x : A => measure y < measure x) := by
  exact @InvImage.wf A Nat (fun a b : Nat => a < b) measure Nat.lt_wfRel.wf

def Fixm {A B : Type}
    (measure : A → Nat)
    (F : ∀ x : A, (∀ y : A, measure y < measure x → B) → B)
    (x : A) : B :=
  Fix (R := fun y x : A => measure y < measure x)
    (measureWellFounded measure) F x

def unroll_FixmStatement : Prop :=
  ∀ {A B : Type}
    (measure : A → Nat)
    (F : ∀ x : A, (∀ y : A, measure y < measure x → B) → B)
    (x : A),
    Fixm measure F x = F x (fun (y : A) (_ : measure y < measure x) => Fixm measure F y)

end CompCert4Lean.Lib.Wfsimpl
