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

variable (A B : Type)
variable (step : A → Sum B A)
variable (ord : A → A → Prop)
variable (ord_wf : WellFounded ord)
variable (step_decr : ∀ a a', step a = Sum.inr a' → ord a' a)

def step_info (step : A → Sum B A) (ord : A → A → Prop)
    (step_decr : ∀ a a', step a = Sum.inr a' → ord a' a) (a : A) :
    Sum
      (CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Specif.sig
        (fun b : B => step a = Sum.inl b))
      (CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Specif.sig2
        (fun a' : A => step a = Sum.inr a')
        (fun a' : A => ord a' a)) := by
  cases h : step a with
  | inl b => exact .inl (.exist b rfl)
  | inr a' =>
      have hord : ord a' a := step_decr a a' h
      exact .inr (.exist2 a' rfl hord)

def iterate_F (step : A → Sum B A) (ord : A → A → Prop)
    (step_decr : ∀ a a', step a = Sum.inr a' → ord a' a)
    (a : A) (rec : ∀ a', ord a' a → B) : B :=
  match step_info A B step ord step_decr a with
  | Sum.inl (.exist b _) => b
  | Sum.inr next => rec next.1 next.2.2

def iterate (step : A → Sum B A) (ord : A → A → Prop)
    (ord_wf : WellFounded ord)
    (step_decr : ∀ a a', step a = Sum.inr a' → ord a' a) (a : A) : B :=
  CompCert4Lean.Lib.Wfsimpl.Fix ord_wf
    (iterate_F A B step ord step_decr) a

def iterate_propStatement (P : A → Prop) (Q : B → Prop)
    (step_prop : ∀ a : A, P a →
      match step a with
      | .inl b => Q b
      | .inr a' => P a') : Prop :=
  ∀ a, P a → Q (iterate A B step ord ord_wf step_decr a)

end ITERATION

end WfIter

namespace PrimIter

section ITERATION

variable (A B : Type)
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
  CompCert4Lean.Lib.Wfsimpl.Fix plt_wf (iter_step A B step)

def iterate : A → Option B :=
  iter A B step num_iterations

def iter_propStatement (P : A → Prop) (Q : B → Prop)
    (step_prop : ∀ a : A, P a →
      match step a with
      | .inl b => Q b
      | .inr a' => P a') : Prop :=
  ∀ n a b, P a → iter A B step n a = some b → Q b

def iterate_propStatement (P : A → Prop) (Q : B → Prop)
    (step_prop : ∀ a : A, P a →
      match step a with
      | .inl b => Q b
      | .inr a' => P a') : Prop :=
  ∀ a b, iterate A B step a = some b → P a → Q b

end ITERATION

end PrimIter

end CompCert4Lean.Lib.Iteration

namespace CompCert4Lean.Lib.Iteration.WfIter

theorem iterate_prop :
    ∀ (A B : Type) (step : A → Sum B A) (ord : A → A → Prop)
      (ord_wf : WellFounded ord)
      (step_decr : ∀ (a a' : A), step a = Sum.inr a' → ord a' a)
      (P : A → Prop) (Q : B → Prop)
      (step_prop : ∀ (a : A), P a →
        match step a with
        | Sum.inl b => Q b
        | Sum.inr a' => P a'),
      iterate_propStatement A B step ord ord_wf step_decr P Q step_prop := by
  intro A B step ord ord_wf step_decr P Q step_prop
  unfold iterate_propStatement
  intro a
  refine ord_wf.induction (C := fun a => P a →
    Q (iterate A B step ord ord_wf step_decr a)) a ?_
  intro a ih hPa
  unfold CompCert4Lean.Lib.Iteration.WfIter.iterate
  rw [CompCert4Lean.Lib.Wfsimpl.unroll_Fix]
  unfold CompCert4Lean.Lib.Iteration.WfIter.iterate_F
  cases h : step_info A B step ord step_decr a with
  | inl binfo =>
      cases binfo with
      | mk b hb =>
          have hstep := step_prop a hPa
          rw [hb] at hstep
          exact hstep
  | inr next =>
      cases next with
      | mk a' hpair =>
          rcases hpair with ⟨ha', hord⟩
          apply ih a' hord
          have hstep := step_prop a hPa
          rw [ha'] at hstep
          exact hstep

end CompCert4Lean.Lib.Iteration.WfIter

namespace CompCert4Lean.Lib.Iteration.PrimIter

theorem iter_prop :
    ∀ (A B : Type) (step : A → Sum B A) (P : A → Prop) (Q : B → Prop)
      (step_prop : ∀ (a : A), P a →
        match step a with
        | Sum.inl b => Q b
        | Sum.inr a' => P a'),
      iter_propStatement A B step P Q step_prop := by
  intro A B step P Q step_prop
  unfold iter_propStatement
  intro n
  refine plt_wf.induction (C := fun n => ∀ a b, P a →
    iter A B step n a = some b → Q b) n ?_
  intro n ih a b hPa hiter
  unfold CompCert4Lean.Lib.Iteration.PrimIter.iter at hiter
  rw [CompCert4Lean.Lib.Wfsimpl.unroll_Fix] at hiter
  unfold CompCert4Lean.Lib.Iteration.PrimIter.iter_step at hiter
  cases hpeq : CompCert4Lean.Lib.Coqlib.peq n
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH with
  | left heq =>
      rw [hpeq] at hiter
      simp at hiter
  | right hne =>
      rw [hpeq] at hiter
      cases hstep : step a with
      | inl b' =>
          rw [hstep] at hiter
          cases hiter
          have hq := step_prop a hPa
          rw [hstep] at hq
          exact hq
      | inr a' =>
          rw [hstep] at hiter
          have hPa' := step_prop a hPa
          rw [hstep] at hPa'
          apply ih
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.pred n)
            (pred_lt n hne) a' b hPa'
          exact hiter

end CompCert4Lean.Lib.Iteration.PrimIter

namespace CompCert4Lean.Lib.Iteration.PrimIter

theorem iterate_prop :
    ∀ (A B : Type) (step : A → Sum B A) (P : A → Prop) (Q : B → Prop)
      (step_prop : ∀ (a : A), P a →
        match step a with
        | Sum.inl b => Q b
        | Sum.inr a' => P a'),
      iterate_propStatement A B step P Q step_prop := by
  intro A B step P Q step_prop
  unfold iterate_propStatement
  intro a b hiter hPa
  apply iter_prop A B step P Q step_prop num_iterations a b hPa
  exact hiter

end CompCert4Lean.Lib.Iteration.PrimIter
