import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Wfsimpl

/-!
# Bounded and well-founded iteration

Executable definitions from CompCert's `lib/Iteration.v` are translated here.
The two proof-bearing invariants remain exact statement descriptors for the
later proof-migration phase.
-/

namespace CompCert4Lean.Lib.Iteration

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

namespace WfIter

section ITERATION

variable {A B : Type}
variable (step : A → Sum B A)
variable (ord : A → A → Prop)
variable (ord_wf : WellFounded ord)
variable (step_decr : ∀ a a', step a = Sum.inr a' → ord a' a)

def step_info (step : A → Sum B A) (ord : A → A → Prop)
    (step_decr : ∀ a a', step a = Sum.inr a' → ord a' a) (a : A) :
    Sum {b : B // step a = Sum.inl b}
      {a' : A // step a = Sum.inr a' ∧ ord a' a} := by
  cases h : step a with
  | inl b => exact .inl ⟨b, rfl⟩
  | inr a' =>
      have hord : ord a' a := step_decr a a' h
      exact .inr ⟨a', rfl, hord⟩

def iterate_F (step : A → Sum B A) (ord : A → A → Prop)
    (step_decr : ∀ a a', step a = Sum.inr a' → ord a' a)
    (a : A) (rec : ∀ a', ord a' a → B) : B :=
  match step_info step ord step_decr a with
  | Sum.inl b => b.1
  | Sum.inr a' => rec a'.1 a'.2.2

def iterate (step : A → Sum B A) (ord : A → A → Prop)
    (ord_wf : WellFounded ord)
    (step_decr : ∀ a a', step a = Sum.inr a' → ord a' a) (a : A) : B :=
  CompCert4Lean.Lib.Wfsimpl.Fix ord_wf
    (iterate_F step ord step_decr) a

end ITERATION

end WfIter

namespace PrimIter

section ITERATION

variable {A B : Type}
variable (step : A → Sum B A)

def num_iterations : positive :=
  PArith.BinPos.Pos.of_nat 1000000000000

private theorem pred_double_lt (p : positive) :
    PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.pred_double p) <
      2 * PArith.BinPos.Pos.to_nat p := by
  cases p with
  | xH =>
      change 1 < 2 * 1
      omega
  | xI q =>
      change 2 * PArith.BinPos.Pos.to_nat (xO q) + 1 <
        2 * (2 * PArith.BinPos.Pos.to_nat q + 1)
      change 2 * (2 * PArith.BinPos.Pos.to_nat q) + 1 <
        2 * (2 * PArith.BinPos.Pos.to_nat q + 1)
      omega
  | xO q =>
      change 2 * PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.pred_double q) + 1 <
        2 * (2 * PArith.BinPos.Pos.to_nat q)
      have ih := pred_double_lt q
      omega

private theorem pred_lt (p : positive) (h : p ≠ xH) :
    PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.pred p) <
      PArith.BinPos.Pos.to_nat p := by
  cases p with
  | xH => contradiction
  | xI q =>
      change 2 * PArith.BinPos.Pos.to_nat q <
        2 * PArith.BinPos.Pos.to_nat q + 1
      omega
  | xO q =>
      change PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.pred_double q) <
        2 * PArith.BinPos.Pos.to_nat q
      exact pred_double_lt q

private theorem plt_wf : WellFounded (CompCert4Lean.Lib.Coqlib.Plt) := by
  exact InvImage.wf PArith.BinPos.Pos.to_nat Nat.lt_wfRel.wf

def iter_step (x : positive)
    (next : ∀ y, CompCert4Lean.Lib.Coqlib.Plt y x → A → Option B)
    (s : A) : Option B :=
  match CompCert4Lean.Lib.Coqlib.peq x xH with
  | .left _ => none
  | .right hne =>
      match step s with
      | .inl res => some res
      | .inr s' => next (PArith.BinPos.Pos.pred x)
          (pred_lt x hne) s'

def iter : positive → A → Option B :=
  CompCert4Lean.Lib.Wfsimpl.Fix plt_wf (iter_step step)

def iterate : A → Option B :=
  iter step num_iterations

def iter_propStatement (P : A → Prop) (Q : B → Prop)
    (step_prop : ∀ a : A, P a →
      match step a with
      | .inl b => Q b
      | .inr a' => P a') : Prop :=
  ∀ n a b, P a → iter step n a = some b → Q b

def iterate_propStatement (P : A → Prop) (Q : B → Prop)
    (step_prop : ∀ a : A, P a →
      match step a with
      | .inl b => Q b
      | .inr a' => P a') : Prop :=
  ∀ a b, iterate step a = some b → P a → Q b

end ITERATION

end PrimIter

end CompCert4Lean.Lib.Iteration
