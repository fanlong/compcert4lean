import CompCert4Lean.Flocq.Core.Float_prop
import CompCert4Lean.Flocq.Core.Zaux
import CompCert4Lean.Lib.Floats.Model

/-!
# Flocq bracket locations

This module translates the executable and statement-bearing surface selected
from `Flocq.Calc.Bracket`.  Proofs assigned to the later proof-migration phase
are represented by exact source-shaped proposition descriptors.
-/

namespace CompCert4Lean.Flocq.Calc.Bracket

/-! The canonical Bracket specification is parameterized by the injected
    exact-real context.  No ambient runtime carrier is used at this boundary. -/
abbrev ExactRealContext := CompCert4Lean.Flocq.Core.Float_prop.ExactRealContext
abbrev R (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Float_prop.Exact.R ctx
abbrev Z := CompCert4Lean.Flocq.Core.Float_prop.Z
abbrev radix := CompCert4Lean.Flocq.Core.Float_prop.radix
abbrev comparison := CompCert4Lean.Flocq.Core.Zaux.comparison

abbrev Lt : comparison := CompCert4Lean.Flocq.Core.Zaux.Lt
abbrev Eq : comparison := CompCert4Lean.Flocq.Core.Zaux.Eq
abbrev Gt : comparison := CompCert4Lean.Flocq.Core.Zaux.Gt

abbrev Z0 : Z := CompCert4Lean.Flocq.Core.Zaux.Z0
abbrev Zone : Z := CompCert4Lean.Flocq.Core.Zaux.Zone
abbrev Ztwo : Z := CompCert4Lean.Flocq.Core.Zaux.Ztwo
abbrev Zadd := CompCert4Lean.Flocq.Core.Zaux.Zadd
abbrev Zmul := CompCert4Lean.Flocq.Core.Zaux.Zmul
abbrev Zdiv := CompCert4Lean.Flocq.Core.Raux.Zdiv
abbrev Zmod := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Zmod
abbrev Zpower := CompCert4Lean.Flocq.Core.Zaux.Zpower
abbrev Zeven := CompCert4Lean.Flocq.Core.Zaux.Zeven
abbrev Zeq_bool := CompCert4Lean.Flocq.Core.Zaux.Zeq_bool
abbrev Zcompare := CompCert4Lean.Flocq.Core.Zaux.Zcompare
abbrev Zle := CompCert4Lean.Flocq.Core.Zaux.Zle
abbrev Zlt := CompCert4Lean.Flocq.Core.Zaux.Zlt

abbrev IZR (ctx : ExactRealContext) : Z → R ctx :=
  CompCert4Lean.Flocq.Core.Float_prop.Exact.IZR ctx
abbrev R0 (ctx : ExactRealContext) : R ctx :=
  CompCert4Lean.Flocq.Core.Raux.Exact.R0 ctx
abbrev Rtwo (ctx : ExactRealContext) : R ctx :=
  CompCert4Lean.Flocq.Core.Raux.Exact.Rtwo ctx
abbrev Rplus (ctx : ExactRealContext) : R ctx → R ctx → R ctx :=
  CompCert4Lean.Flocq.Core.Raux.Exact.Rplus ctx
abbrev Rmult (ctx : ExactRealContext) : R ctx → R ctx → R ctx :=
  CompCert4Lean.Flocq.Core.Raux.Exact.Rmult ctx
abbrev Rdiv (ctx : ExactRealContext) : R ctx → R ctx → R ctx :=
  CompCert4Lean.Flocq.Core.Raux.Exact.Rdiv ctx
abbrev Rlt (ctx : ExactRealContext) : R ctx → R ctx → Prop :=
  CompCert4Lean.Flocq.Core.Raux.Exact.Rlt ctx
abbrev Rle (ctx : ExactRealContext) : R ctx → R ctx → Prop :=
  CompCert4Lean.Flocq.Core.Raux.Exact.Rle ctx
noncomputable abbrev Rcompare (ctx : ExactRealContext) :
    R ctx → R ctx → comparison :=
  CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx

abbrev location := CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.location
abbrev loc_Exact : location := CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.loc_Exact
abbrev loc_Inexact (c : comparison) : location :=
  CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.loc_Inexact c

abbrev Float (beta : radix) (m e : Z) : CompCert4Lean.Flocq.Core.Float_prop.float beta :=
  CompCert4Lean.Flocq.Core.Float_prop.Float beta m e
abbrev F2R (ctx : ExactRealContext) {beta : radix}
    (f : CompCert4Lean.Flocq.Core.Float_prop.float beta) : R ctx :=
  CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx f

section ExactSpecification

variable (ctx : ExactRealContext)

local notation "R" => R ctx
local notation "IZR" => IZR ctx
local notation "R0" => R0 ctx
local notation "Rtwo" => Rtwo ctx
local notation "Rplus" => Rplus ctx
local notation "Rmult" => Rmult ctx
local notation "Rdiv" => Rdiv ctx
local notation "Rlt" => Rlt ctx
local notation "Rle" => Rle ctx
local notation "Rcompare" => Rcompare ctx
local notation "F2R" => F2R ctx

inductive inbetween (d u x : R) : location → Prop where
  | inbetween_Exact (h : x = d) : inbetween d u x loc_Exact
  | inbetween_Inexact (l : comparison)
      (h_bounds : Rlt d x ∧ Rlt x u)
      (h_middle : Rcompare x (Rdiv (Rplus d u) Rtwo) = l) :
      inbetween d u x (loc_Inexact l)

export inbetween (inbetween_Exact inbetween_Inexact)

local notation "inbetween" => inbetween ctx

def new_location_even (nb_steps k : Z) (l : location) : location :=
  if Zeq_bool k Z0 then
    match l with
    | .loc_Exact => l
    | .loc_Inexact _ => loc_Inexact Lt
  else
    loc_Inexact
      (match Zcompare (Zmul Ztwo k) nb_steps with
       | .Lt => Lt
       | .Eq =>
           match l with
           | .loc_Exact => Eq
           | .loc_Inexact _ => Gt
       | .Gt => Gt)

def new_location_odd (nb_steps k : Z) (l : location) : location :=
  if Zeq_bool k Z0 then
    match l with
    | .loc_Exact => l
    | .loc_Inexact _ => loc_Inexact Lt
  else
    loc_Inexact
      (match Zcompare (Zadd (Zmul Ztwo k) Zone) nb_steps with
       | .Lt => Lt
       | .Eq =>
           match l with
           | .loc_Inexact c => c
           | .loc_Exact => Lt
       | .Gt => Gt)

def new_location (nb_steps k : Z) (l : location) : location :=
  if Zeven nb_steps then
    new_location_even nb_steps k l
  else
    new_location_odd nb_steps k l

def inbetween_float (beta : radix) (m e : Z) (x : R) (l : location) : Prop :=
  inbetween (F2R (Float beta m e))
    (F2R (Float beta (Zadd m Zone) e)) x l

local notation "inbetween_float" => inbetween_float ctx

def inbetween_int (m : Z) (x : R) (l : location) : Prop :=
  inbetween (IZR m) (IZR (Zadd m Zone)) x l

local notation "inbetween_int" => inbetween_int ctx

/-! Exact source proposition descriptors for later proof migration. -/

def inbetween_uniqueStatement : Prop :=
  ∀ (d u x : R) (l l' : location),
    inbetween d u x l → inbetween d u x l' → l = l'

def inbetween_boundsStatement : Prop :=
  ∀ (d u : R), Rlt d u →
    ∀ (x : R) (l : location),
      inbetween d u x l → Rle d x ∧ Rlt x u

def inbetween_bounds_not_EqStatement : Prop :=
  ∀ (d u x : R) (l : location),
    inbetween d u x l → l ≠ loc_Exact → Rlt d x ∧ Rlt x u

def inbetween_exStatement : Prop :=
  ∀ (d u : R) (l : location), Rlt d u → ∃ x : R, inbetween d u x l

def ordered_stepsStatement : Prop :=
  ∀ (start step : R), Rlt (IZR Z0) step →
    ∀ k : Z,
      Rlt
        (Rplus start (Rmult (IZR k) step))
        (Rplus start (Rmult (IZR (Zadd k Zone)) step))

def middle_rangeStatement : Prop :=
  ∀ (start step : R) (k : Z),
    Rdiv (Rplus start (Rplus start (Rmult (IZR k) step))) Rtwo =
      Rplus start (Rmult (Rdiv (IZR k) Rtwo) step)

def inbetween_step_not_EqStatement : Prop :=
  ∀ (start step : R) (nb_steps : Z), Rlt (IZR Z0) step →
    ∀ (x : R) (k : Z) (l : location) (l' : comparison),
      inbetween
        (Rplus start (Rmult (IZR k) step))
        (Rplus start (Rmult (IZR (Zadd k Zone)) step)) x l →
      Zlt Z0 k ∧ Zlt k nb_steps →
      Rcompare x (Rplus start (Rmult (Rdiv (IZR nb_steps) Rtwo) step)) = l' →
      inbetween start (Rplus start (Rmult (IZR nb_steps) step)) x (loc_Inexact l')

def inbetween_step_LoStatement : Prop :=
  ∀ (start step : R) (nb_steps : Z), Rlt (IZR Z0) step → Zlt Zone nb_steps →
    ∀ (x : R) (k : Z) (l : location),
      inbetween
        (Rplus start (Rmult (IZR k) step))
        (Rplus start (Rmult (IZR (Zadd k Zone)) step)) x l →
      Zlt Z0 k →
      Zlt (Zadd (Zmul Ztwo k) Zone) nb_steps →
      inbetween start (Rplus start (Rmult (IZR nb_steps) step)) x (loc_Inexact Lt)

def inbetween_step_HiStatement : Prop :=
  ∀ (start step : R) (nb_steps : Z), Rlt (IZR Z0) step → Zlt Zone nb_steps →
    ∀ (x : R) (k : Z) (l : location),
      inbetween
        (Rplus start (Rmult (IZR k) step))
        (Rplus start (Rmult (IZR (Zadd k Zone)) step)) x l →
      Zlt nb_steps (Zmul Ztwo k) →
      Zlt k nb_steps →
      inbetween start (Rplus start (Rmult (IZR nb_steps) step)) x (loc_Inexact Gt)

def inbetween_step_Lo_not_EqStatement : Prop :=
  ∀ (start step : R) (nb_steps : Z), Rlt (IZR Z0) step → Zlt Zone nb_steps →
    ∀ (x : R) (l : location),
      inbetween start (Rplus start step) x l →
      l ≠ loc_Exact →
      inbetween start (Rplus start (Rmult (IZR nb_steps) step)) x (loc_Inexact Lt)

def middle_oddStatement : Prop :=
  ∀ (start step : R) (nb_steps k : Z),
    Zadd (Zmul Ztwo k) Zone = nb_steps →
      Rdiv
          (Rplus
            (Rplus start (Rmult (IZR k) step))
            (Rplus start (Rmult (IZR (Zadd k Zone)) step))) Rtwo =
        Rplus start (Rmult (Rdiv (IZR nb_steps) Rtwo) step)

def inbetween_step_any_Mi_oddStatement : Prop :=
  ∀ (start step : R) (nb_steps : Z), Rlt (IZR Z0) step → Zlt Zone nb_steps →
    ∀ (x : R) (k : Z) (l : comparison),
      inbetween
        (Rplus start (Rmult (IZR k) step))
        (Rplus start (Rmult (IZR (Zadd k Zone)) step)) x (loc_Inexact l) →
      Zadd (Zmul Ztwo k) Zone = nb_steps →
      inbetween start (Rplus start (Rmult (IZR nb_steps) step)) x (loc_Inexact l)

def inbetween_step_Lo_Mi_Eq_oddStatement : Prop :=
  ∀ (start step : R) (nb_steps : Z), Rlt (IZR Z0) step → Zlt Zone nb_steps →
    ∀ (x : R) (k : Z),
      inbetween
        (Rplus start (Rmult (IZR k) step))
        (Rplus start (Rmult (IZR (Zadd k Zone)) step)) x loc_Exact →
      Zadd (Zmul Ztwo k) Zone = nb_steps →
      inbetween start (Rplus start (Rmult (IZR nb_steps) step)) x (loc_Inexact Lt)

def inbetween_step_Hi_Mi_evenStatement : Prop :=
  ∀ (start step : R) (nb_steps : Z), Rlt (IZR Z0) step → Zlt Zone nb_steps →
    ∀ (x : R) (k : Z) (l : location),
      inbetween
        (Rplus start (Rmult (IZR k) step))
        (Rplus start (Rmult (IZR (Zadd k Zone)) step)) x l →
      l ≠ loc_Exact →
      Zmul Ztwo k = nb_steps →
      inbetween start (Rplus start (Rmult (IZR nb_steps) step)) x (loc_Inexact Gt)

def inbetween_step_Mi_Mi_evenStatement : Prop :=
  ∀ (start step : R) (nb_steps : Z), Rlt (IZR Z0) step → Zlt Zone nb_steps →
    ∀ (x : R) (k : Z),
      inbetween
        (Rplus start (Rmult (IZR k) step))
        (Rplus start (Rmult (IZR (Zadd k Zone)) step)) x loc_Exact →
      Zmul Ztwo k = nb_steps →
      inbetween start (Rplus start (Rmult (IZR nb_steps) step)) x (loc_Inexact Eq)

def new_location_even_correctStatement : Prop :=
  ∀ (start step : R) (nb_steps : Z), Rlt (IZR Z0) step → Zlt Zone nb_steps →
    Zeven nb_steps = true →
    ∀ (x : R) (k : Z) (l : location),
      Zle Z0 k ∧ Zlt k nb_steps →
      inbetween
        (Rplus start (Rmult (IZR k) step))
        (Rplus start (Rmult (IZR (Zadd k Zone)) step)) x l →
      inbetween start (Rplus start (Rmult (IZR nb_steps) step)) x
        (new_location_even nb_steps k l)

def new_location_odd_correctStatement : Prop :=
  ∀ (start step : R) (nb_steps : Z), Rlt (IZR Z0) step → Zlt Zone nb_steps →
    Zeven nb_steps = false →
    ∀ (x : R) (k : Z) (l : location),
      Zle Z0 k ∧ Zlt k nb_steps →
      inbetween
        (Rplus start (Rmult (IZR k) step))
        (Rplus start (Rmult (IZR (Zadd k Zone)) step)) x l →
      inbetween start (Rplus start (Rmult (IZR nb_steps) step)) x
        (new_location_odd nb_steps k l)

def new_location_correctStatement : Prop :=
  ∀ (start step : R) (nb_steps : Z), Rlt (IZR Z0) step → Zlt Zone nb_steps →
    ∀ (x : R) (k : Z) (l : location),
      Zle Z0 k ∧ Zlt k nb_steps →
      inbetween
        (Rplus start (Rmult (IZR k) step))
        (Rplus start (Rmult (IZR (Zadd k Zone)) step)) x l →
      inbetween start (Rplus start (Rmult (IZR nb_steps) step)) x
        (new_location nb_steps k l)

def inbetween_mult_compatStatement : Prop :=
  ∀ (x d u : R) (l : location) (s : R), Rlt (IZR Z0) s →
    inbetween x d u l →
    inbetween (Rmult x s) (Rmult d s) (Rmult u s) l

def inbetween_mult_regStatement : Prop :=
  ∀ (x d u : R) (l : location) (s : R), Rlt (IZR Z0) s →
    inbetween (Rmult x s) (Rmult d s) (Rmult u s) l →
    inbetween x d u l

def inbetween_float_boundsStatement : Prop :=
  ∀ (beta : radix) (x : R) (m e : Z) (l : location),
    inbetween_float beta m e x l →
    Rle (F2R (Float beta m e)) x ∧
      Rlt x (F2R (Float beta (Zadd m Zone) e))

def inbetween_float_new_locationStatement : Prop :=
  ∀ (beta : radix) (x : R) (m e : Z) (l : location) (k : Z), Zlt Z0 k →
    inbetween_float beta m e x l →
    inbetween_float beta (Zdiv m (Zpower (beta : Z) k)) (Zadd e k) x
      (new_location (Zpower (beta : Z) k) (Zmod m (Zpower (beta : Z) k)) l)

def inbetween_float_exStatement : Prop :=
  ∀ (beta : radix) (m e : Z) (l : location), ∃ x : R, inbetween_float beta m e x l

def inbetween_float_uniqueStatement : Prop :=
  ∀ (beta : radix) (x : R) (e m : Z) (l : location) (m' : Z) (l' : location),
    inbetween_float beta m e x l → inbetween_float beta m' e x l' → m = m' ∧ l = l'

end ExactSpecification

end CompCert4Lean.Flocq.Calc.Bracket

namespace CompCert4Lean.Flocq.Calc.Bracket

theorem inbetween_bounds_not_Eq (ctx : ExactRealContext) :
    inbetween_bounds_not_EqStatement ctx := by
  intro d u x l hx hl
  cases hx with
  | inbetween_Exact h => exact (hl rfl).elim
  | inbetween_Inexact l hbounds hmiddle => exact hbounds

end CompCert4Lean.Flocq.Calc.Bracket

namespace CompCert4Lean.Flocq.Calc.Bracket

private theorem middle_mul_add_right (ctx : ExactRealContext)
    (x y z : ctx.spec.carrier) :
    ctx.spec.mul (ctx.spec.add x y) z =
      ctx.spec.add (ctx.spec.mul x z) (ctx.spec.mul y z) := by
  calc
    ctx.spec.mul (ctx.spec.add x y) z =
        ctx.spec.mul z (ctx.spec.add x y) :=
      ctx.certificate.orderedField.mul_comm _ _
    _ = ctx.spec.add (ctx.spec.mul z x) (ctx.spec.mul z y) :=
      ctx.certificate.orderedField.left_distrib _ _ _
    _ = ctx.spec.add (ctx.spec.mul x z) (ctx.spec.mul y z) := by
      rw [ctx.certificate.orderedField.mul_comm z x,
        ctx.certificate.orderedField.mul_comm z y]

private theorem middle_zero_lt_one (ctx : ExactRealContext) :
    ctx.spec.lt ctx.spec.zero ctx.spec.one := by
  rcases ctx.certificate.total_order ctx.spec.zero ctx.spec.one with h | h
  · rcases h with h | h
    · exact h
    · exact (ctx.certificate.orderedField.zero_ne_one h).elim
  · have hneg : ctx.spec.lt ctx.spec.zero (ctx.spec.neg ctx.spec.one) := by
      have h' := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.neg ctx.spec.one) ctx.spec.one ctx.spec.zero h
      rw [ctx.certificate.orderedField.neg_add_cancel,
        ctx.certificate.orderedField.add_zero] at h'
      exact h'
    have hmul : ctx.spec.lt (ctx.spec.neg ctx.spec.one) ctx.spec.zero := by
      have h' := ctx.certificate.orderedField.mul_lt_compat_l
        (ctx.spec.neg ctx.spec.one) ctx.spec.one ctx.spec.zero hneg h
      rw [ctx.certificate.orderedField.mul_one,
        ctx.certificate.orderedField.mul_zero] at h'
      exact h'
    exact False.elim ((ctx.certificate.orderedField.lt_irrefl _)
      (ctx.certificate.orderedField.lt_trans _ _ _ hneg hmul))

private theorem middle_two_ne_zero (ctx : ExactRealContext) :
    ctx.spec.add ctx.spec.one ctx.spec.one ≠ ctx.spec.zero := by
  have h1two : ctx.spec.lt ctx.spec.one
      (ctx.spec.add ctx.spec.one ctx.spec.one) := by
    have h := ctx.certificate.orderedField.add_lt_compat_l
      ctx.spec.one ctx.spec.zero ctx.spec.one (middle_zero_lt_one ctx)
    rw [ctx.certificate.orderedField.add_zero] at h
    exact h
  have h0two : ctx.spec.lt ctx.spec.zero
      (ctx.spec.add ctx.spec.one ctx.spec.one) :=
    ctx.certificate.orderedField.lt_trans _ _ _
      (middle_zero_lt_one ctx) h1two
  intro h
  exact (ctx.certificate.orderedField.lt_irrefl _)
    (h ▸ h0two)

private theorem middle_two_mul (ctx : ExactRealContext) (x : ctx.spec.carrier) :
    ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one) x =
      ctx.spec.add x x := by
  calc
    ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one) x =
        ctx.spec.mul x (ctx.spec.add ctx.spec.one ctx.spec.one) :=
      ctx.certificate.orderedField.mul_comm _ _
    _ = ctx.spec.add (ctx.spec.mul x ctx.spec.one)
        (ctx.spec.mul x ctx.spec.one) :=
      ctx.certificate.orderedField.left_distrib _ _ _
    _ = ctx.spec.add x x := by
      rw [ctx.certificate.orderedField.mul_one]

private theorem middle_range_core (ctx : ExactRealContext)
    (start step : ctx.spec.carrier) (k : Z) :
    ctx.spec.div
        (ctx.spec.add start
          (ctx.spec.add start (ctx.spec.mul (ctx.spec.ofZ k) step)))
        (ctx.spec.add ctx.spec.one ctx.spec.one) =
      ctx.spec.add start
        (ctx.spec.mul
          (ctx.spec.div (ctx.spec.ofZ k)
            (ctx.spec.add ctx.spec.one ctx.spec.one)) step) := by
  let two : ctx.spec.carrier := ctx.spec.add ctx.spec.one ctx.spec.one
  let invTwo : ctx.spec.carrier := ctx.spec.inv two
  have htwo : two ≠ ctx.spec.zero := by
    exact middle_two_ne_zero ctx
  have htwo_inv : ctx.spec.mul two invTwo = ctx.spec.one := by
    calc
      ctx.spec.mul two invTwo = ctx.spec.mul invTwo two :=
        ctx.certificate.orderedField.mul_comm _ _
      _ = ctx.spec.one :=
        ctx.certificate.orderedField.inv_mul_cancel _ htwo
  have hfirst :
      ctx.spec.mul (ctx.spec.add start start) invTwo = start := by
    calc
      ctx.spec.mul (ctx.spec.add start start) invTwo =
          ctx.spec.mul (ctx.spec.mul two start) invTwo := by
            rw [middle_two_mul]
      _ = ctx.spec.mul two (ctx.spec.mul start invTwo) :=
        ctx.certificate.orderedField.mul_assoc _ _ _
      _ = ctx.spec.mul two (ctx.spec.mul invTwo start) := by
        rw [ctx.certificate.orderedField.mul_comm start]
      _ = ctx.spec.mul (ctx.spec.mul two invTwo) start := by
        rw [ctx.certificate.orderedField.mul_assoc]
      _ = ctx.spec.mul ctx.spec.one start := by rw [htwo_inv]
      _ = start := ctx.certificate.orderedField.one_mul _

  have hsecond :
      ctx.spec.mul (ctx.spec.mul (ctx.spec.ofZ k) step) invTwo =
        ctx.spec.mul
          (ctx.spec.div (ctx.spec.ofZ k) two) step := by
    calc
      ctx.spec.mul (ctx.spec.mul (ctx.spec.ofZ k) step) invTwo =
          ctx.spec.mul (ctx.spec.ofZ k)
            (ctx.spec.mul step invTwo) :=
        ctx.certificate.orderedField.mul_assoc _ _ _
      _ = ctx.spec.mul (ctx.spec.ofZ k)
            (ctx.spec.mul invTwo step) := by
        rw [ctx.certificate.orderedField.mul_comm step]
      _ = ctx.spec.mul
          (ctx.spec.mul (ctx.spec.ofZ k) invTwo) step := by
        rw [ctx.certificate.orderedField.mul_assoc]
      _ = ctx.spec.mul
          (ctx.spec.div (ctx.spec.ofZ k) two) step := by
        rw [ctx.certificate.orderedField.div_eq_mul_inv]

  change ctx.spec.div
      (ctx.spec.add start
        (ctx.spec.add start (ctx.spec.mul (ctx.spec.ofZ k) step)))
      (ctx.spec.add ctx.spec.one ctx.spec.one) =
    ctx.spec.add start
      (ctx.spec.mul
        (ctx.spec.div (ctx.spec.ofZ k)
          (ctx.spec.add ctx.spec.one ctx.spec.one)) step)
  rw [ctx.certificate.orderedField.div_eq_mul_inv]
  change ctx.spec.mul
      (ctx.spec.add start
        (ctx.spec.add start (ctx.spec.mul (ctx.spec.ofZ k) step)))
      (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)) = _
  calc
    ctx.spec.mul
        (ctx.spec.add start
          (ctx.spec.add start (ctx.spec.mul (ctx.spec.ofZ k) step)))
        (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)) =
      ctx.spec.mul
        (ctx.spec.add
          (ctx.spec.add start start)
          (ctx.spec.mul (ctx.spec.ofZ k) step))
        (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)) := by
          rw [ctx.certificate.orderedField.add_assoc]
    _ = ctx.spec.add
        (ctx.spec.mul (ctx.spec.add start start)
          (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)))
        (ctx.spec.mul (ctx.spec.mul (ctx.spec.ofZ k) step)
          (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))) :=
          middle_mul_add_right ctx _ _ _
    _ = ctx.spec.add start
        (ctx.spec.mul (ctx.spec.mul (ctx.spec.ofZ k) step)
          (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))) := by
          rw [hfirst]
    _ = ctx.spec.add start
        (ctx.spec.mul
          (ctx.spec.div (ctx.spec.ofZ k)
            (ctx.spec.add ctx.spec.one ctx.spec.one)) step) := by
          rw [hsecond]

theorem middle_range (ctx : ExactRealContext) :
    middle_rangeStatement ctx := by
  intro start step k
  exact middle_range_core ctx start step k

end CompCert4Lean.Flocq.Calc.Bracket

namespace CompCert4Lean.Flocq.Calc.Bracket

private theorem bracket_Rcompare_lt (ctx : ExactRealContext)
    {x y : R ctx} (hxy : Rlt ctx x y) :
    Rcompare ctx x y = Lt := by
  change CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx x y = Lt
  unfold CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare
  unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.total_order_T
  cases hdec : ctx.spec.lt_dec x y with
  | left _ => rfl
  | right hnxy => exact (hnxy hxy).elim

private theorem bracket_Rcompare_eq (ctx : ExactRealContext)
    {x y : R ctx} (hxy : x = y) :
    Rcompare ctx x y = Eq := by
  change CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx x y = Eq
  subst y
  cases hdec : ctx.spec.lt_dec x x with
  | left hlt => exact (ctx.certificate.orderedField.lt_irrefl x hlt).elim
  | right _ =>
      simp [CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare,
        CompCert4Lean.Foundation.FlocqReal.ExactReal.total_order_T, hdec]

private theorem bracket_Rcompare_gt (ctx : ExactRealContext)
    {x y : R ctx} (hyx : Rlt ctx y x) :
    Rcompare ctx x y = Gt := by
  have hnxy : ¬ Rlt ctx x y := by
    intro hxy
    exact ctx.certificate.orderedField.lt_irrefl x
      (ctx.certificate.orderedField.lt_trans x y x hxy hyx)
  change CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx x y = Gt
  unfold CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare
  unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.total_order_T
  cases hxy : ctx.spec.lt_dec x y with
  | left hlt => exact (hnxy hlt).elim
  | right _ =>
      cases hyx_dec : ctx.spec.lt_dec y x with
      | left _ => rfl
      | right hnyx => exact (hnyx hyx).elim

private theorem bracket_Rcompare_mult_r (ctx : ExactRealContext)
    (z x y : R ctx) (hz : Rlt ctx (R0 ctx) z) :
    Rcompare ctx (Rmult ctx x z) (Rmult ctx y z) = Rcompare ctx x y := by
  change CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx (ctx.spec.mul x z)
      (ctx.spec.mul y z) = CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx x y
  change ctx.spec.lt ctx.spec.zero z at hz
  rcases ctx.certificate.total_order x y with h | h
  · rcases h with hlt | heq
    · have hmul := ctx.certificate.orderedField.mul_lt_compat_l z x y hz hlt
      rw [ctx.certificate.orderedField.mul_comm z x,
        ctx.certificate.orderedField.mul_comm z y] at hmul
      have hleft :
          CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx
              (ctx.spec.mul x z) (ctx.spec.mul y z) = Lt :=
        bracket_Rcompare_lt ctx hmul
      have hright :
          CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx x y = Lt :=
        bracket_Rcompare_lt ctx hlt
      rw [hleft, hright]
    · subst y
      have hleft :
          CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx
              (ctx.spec.mul x z) (ctx.spec.mul x z) = Eq :=
        bracket_Rcompare_eq ctx rfl
      have hright :
          CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx x x = Eq :=
        bracket_Rcompare_eq ctx rfl
      rw [hleft, hright]
  · have hmul := ctx.certificate.orderedField.mul_lt_compat_l z y x hz h
    rw [ctx.certificate.orderedField.mul_comm z y,
      ctx.certificate.orderedField.mul_comm z x] at hmul
    have hleft :
        CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx
            (ctx.spec.mul x z) (ctx.spec.mul y z) = Gt :=
      bracket_Rcompare_gt ctx hmul
    have hright :
        CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx x y = Gt :=
      bracket_Rcompare_gt ctx h
    rw [hleft, hright]

private theorem bracket_middle_mult (ctx : ExactRealContext)
    (x d s : R ctx) :
    Rdiv ctx (Rplus ctx (Rmult ctx x s) (Rmult ctx d s)) (Rtwo ctx) =
      Rmult ctx (Rdiv ctx (Rplus ctx x d) (Rtwo ctx)) s := by
  change ctx.spec.div
      (ctx.spec.add (ctx.spec.mul x s) (ctx.spec.mul d s))
      (ctx.spec.add ctx.spec.one ctx.spec.one) =
    ctx.spec.mul
      (ctx.spec.div (ctx.spec.add x d) (ctx.spec.add ctx.spec.one ctx.spec.one)) s
  rw [ctx.certificate.orderedField.div_eq_mul_inv,
    ctx.certificate.orderedField.div_eq_mul_inv]
  calc
    ctx.spec.mul (ctx.spec.add (ctx.spec.mul x s) (ctx.spec.mul d s))
        (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)) =
      ctx.spec.mul (ctx.spec.mul (ctx.spec.add x d) s)
        (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)) := by
          congr 1
          calc
            ctx.spec.add (ctx.spec.mul x s) (ctx.spec.mul d s) =
                ctx.spec.add (ctx.spec.mul s x) (ctx.spec.mul s d) := by
                  rw [ctx.certificate.orderedField.mul_comm s x,
                    ctx.certificate.orderedField.mul_comm s d]
            _ = ctx.spec.mul s (ctx.spec.add x d) :=
              (ctx.certificate.orderedField.left_distrib s x d).symm
            _ = ctx.spec.mul (ctx.spec.add x d) s :=
              ctx.certificate.orderedField.mul_comm _ _
    _ = ctx.spec.mul (ctx.spec.add x d)
        (ctx.spec.mul s (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))) :=
      ctx.certificate.orderedField.mul_assoc _ _ _
    _ = ctx.spec.mul (ctx.spec.add x d)
        (ctx.spec.mul (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)) s) := by
          rw [ctx.certificate.orderedField.mul_comm s]
    _ = ctx.spec.mul
        (ctx.spec.mul (ctx.spec.add x d)
          (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))) s := by
          rw [ctx.certificate.orderedField.mul_assoc]

theorem inbetween_mult_compat (ctx : ExactRealContext) :
    inbetween_mult_compatStatement ctx := by
  intro x d u l s hs hbetween
  have hs0 : Rlt ctx (R0 ctx) s := by
    change ctx.spec.lt ctx.spec.zero s
    have hzero : IZR ctx Z0 = ctx.spec.zero :=
      ctx.certificate.sourceLaws.ofZ_zero
    rw [← hzero]
    exact hs
  cases hbetween with
  | inbetween_Exact h =>
      constructor
      rw [h]
  | inbetween_Inexact l hbounds hmiddle =>
      constructor
      · constructor
        · exact
            CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_compat_r
              ctx s x u hs hbounds.1
        · exact
            CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_compat_r
              ctx s u d hs hbounds.2
      · calc
          Rcompare ctx (Rmult ctx u s)
              (Rdiv ctx (Rplus ctx (Rmult ctx x s) (Rmult ctx d s)) (Rtwo ctx)) =
            Rcompare ctx (Rmult ctx u s)
              (Rmult ctx (Rdiv ctx (Rplus ctx x d) (Rtwo ctx)) s) := by
                rw [bracket_middle_mult]
          _ = Rcompare ctx u (Rdiv ctx (Rplus ctx x d) (Rtwo ctx)) :=
            bracket_Rcompare_mult_r ctx s u
              (Rdiv ctx (Rplus ctx x d) (Rtwo ctx)) hs0
          _ = l := hmiddle

end CompCert4Lean.Flocq.Calc.Bracket

namespace CompCert4Lean.Flocq.Calc.Bracket

theorem inbetween_bounds (ctx : ExactRealContext) :
    inbetween_boundsStatement ctx := by
  intro d u hdu x l hx
  cases hx with
  | inbetween_Exact h =>
      subst x
      constructor
      · exact
          CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_refl
            ctx d
      · exact hdu
  | inbetween_Inexact l hbounds hmiddle =>
      constructor
      · exact
          CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le
            ctx d x hbounds.1
      · exact hbounds.2

private theorem bracket_bpow_pos (ctx : ExactRealContext) (beta : radix) (e : Z) :
    ctx.spec.lt ctx.spec.zero
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e) := by
  have hnum : Zlt Z0
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH) := by
    change (0 : Int) < 1
    omega
  have h := CompCert4Lean.Flocq.Core.Float_prop.F2R_gt_0 ctx beta
      (CompCert4Lean.Flocq.Core.Float_prop.Float beta
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH) e) hnum
  change ctx.spec.lt ctx.spec.zero
      (ctx.spec.mul
        (ctx.spec.ofZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH))
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e)) at h
  rw [ctx.certificate.sourceLaws.ofZ_one,
    ctx.certificate.orderedField.one_mul] at h
  exact h

private theorem bracket_float_endpoint_lt (ctx : ExactRealContext)
    (beta : radix) (m e : Z) :
    Rlt ctx (F2R ctx (Float beta m e))
      (F2R ctx (Float beta (Zadd m Zone) e)) := by
  change ctx.spec.lt
      (ctx.spec.mul (ctx.spec.ofZ m)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e))
      (ctx.spec.mul (ctx.spec.ofZ (Zadd m Zone))
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e))
  have hm : Zlt m (Zadd m Zone) := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd m Zone)
    have hZone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by
      rfl
    simp only [Zadd,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    rw [hZone]
    omega
  have hm' : ctx.spec.lt (ctx.spec.ofZ m) (ctx.spec.ofZ (Zadd m Zone)) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt ctx m
      (Zadd m Zone) hm
  have hs := bracket_bpow_pos ctx beta e
  have hzero : IZR ctx Z0 = ctx.spec.zero :=
    ctx.certificate.sourceLaws.ofZ_zero
  have hs' : Rlt ctx (IZR ctx Z0)
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e) := by
    rw [hzero]
    exact hs
  exact
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_compat_r
      ctx (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e)
      (ctx.spec.ofZ m) (ctx.spec.ofZ (Zadd m Zone)) hs' hm'

theorem inbetween_float_bounds (ctx : ExactRealContext) :
    inbetween_float_boundsStatement ctx := by
  intro beta x m e l hx
  unfold inbetween_float at hx
  exact inbetween_bounds ctx _ _ (bracket_float_endpoint_lt ctx beta m e) _ _ hx

end CompCert4Lean.Flocq.Calc.Bracket

namespace CompCert4Lean.Flocq.Calc.Bracket

theorem ordered_steps :
    ∀ (ctx : ExactRealContext), ordered_stepsStatement ctx := by
  intro ctx start step hstep k
  apply CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Raxioms.Rplus_lt_compat_l
    ctx start
  apply CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_compat_r
    ctx step
  exact hstep
  apply CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt
    ctx k (Zadd k Zone)
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd k Zone)
  have hZone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by
    rfl
  simp only [Zadd,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add]
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  rw [hZone]
  omega

end CompCert4Lean.Flocq.Calc.Bracket

namespace CompCert4Lean.Flocq.Calc.Bracket

theorem inbetween_step_not_Eq (ctx : ExactRealContext) :
    inbetween_step_not_EqStatement ctx := by
  intro start step nb_steps hstep x k l l' hx hk hcmp
  have hk_izr : Rlt ctx (IZR ctx Z0) (IZR ctx k) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt
      ctx Z0 k hk.1
  have hkmul : Rlt ctx (IZR ctx Z0)
      (Rmult ctx (IZR ctx k) step) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_0_compat
      ctx (IZR ctx k) step hk_izr hstep
  have hstart_lower' : Rlt ctx
      (Rplus ctx start (IZR ctx Z0))
      (Rplus ctx start (Rmult ctx (IZR ctx k) step)) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Raxioms.Rplus_lt_compat_l
      ctx start (IZR ctx Z0) (Rmult ctx (IZR ctx k) step) hkmul
  have hstart_lower : Rlt ctx start
      (Rplus ctx start (Rmult ctx (IZR ctx k) step)) := by
    change ctx.spec.lt start
      (ctx.spec.add start (ctx.spec.mul (ctx.spec.ofZ k) step))
    change ctx.spec.lt
      (ctx.spec.add start (ctx.spec.ofZ Z0))
      (ctx.spec.add start (ctx.spec.mul (ctx.spec.ofZ k) step)) at hstart_lower'
    rw [ctx.certificate.sourceLaws.ofZ_zero,
      ctx.certificate.orderedField.add_zero] at hstart_lower'
    exact hstart_lower'
  have hinner := inbetween_bounds ctx
      (Rplus ctx start (Rmult ctx (IZR ctx k) step))
      (Rplus ctx start (Rmult ctx (IZR ctx (Zadd k Zone)) step))
      (ordered_steps ctx start step hstep k) x l hx
  have hlower : Rlt ctx start x :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
      ctx start
        (Rplus ctx start (Rmult ctx (IZR ctx k) step)) x
      hstart_lower hinner.1
  have hk1_le : Zle (Zadd k Zone) nb_steps := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd k Zone) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ nb_steps
    simp only [Zadd,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add]
    rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    have hZone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone =
        (1 : Int) := by rfl
    rw [hZone]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k + 1 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ nb_steps
    have hk_int := hk.2
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ nb_steps at hk_int
    omega
  have hk1_izr_le : Rle ctx
      (IZR ctx (Zadd k Zone)) (IZR ctx nb_steps) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_le
      ctx (Zadd k Zone) nb_steps hk1_le
  have hstep_le : Rle ctx (IZR ctx Z0) step :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le
      ctx (IZR ctx Z0) step hstep
  have hkmul_le : Rle ctx
      (Rmult ctx (IZR ctx (Zadd k Zone)) step)
      (Rmult ctx (IZR ctx nb_steps) step) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
      ctx step (IZR ctx (Zadd k Zone)) (IZR ctx nb_steps)
      hstep_le hk1_izr_le
  have hupper_le : Rle ctx
      (Rplus ctx start (Rmult ctx (IZR ctx (Zadd k Zone)) step))
      (Rplus ctx start (Rmult ctx (IZR ctx nb_steps) step)) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_le_compat_l
      ctx start _ _ hkmul_le
  have hupper : Rlt ctx x
      (Rplus ctx start (Rmult ctx (IZR ctx nb_steps) step)) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
      ctx x
        (Rplus ctx start (Rmult ctx (IZR ctx (Zadd k Zone)) step))
        (Rplus ctx start (Rmult ctx (IZR ctx nb_steps) step))
      hinner.2 hupper_le
  apply inbetween_Inexact l'
  · exact ⟨hlower, hupper⟩
  · rw [middle_range]
    exact hcmp

end CompCert4Lean.Flocq.Calc.Bracket

namespace CompCert4Lean.Flocq.Calc.Bracket

theorem inbetween_step_Hi :
    ∀ (ctx : ExactRealContext), inbetween_step_HiStatement ctx := by
  intro ctx start step nb_steps hstep hnb x k l hx hk1 hk2
  apply inbetween_step_not_Eq ctx start step nb_steps hstep x k l Gt hx
  · have hkpos : Zlt Z0 k := by
      change (0 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ nb_steps <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zmul Ztwo k) at hk1
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ nb_steps at hk2
      simp only [Zmul,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hk1
      have htwo_int :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = (2 : Int) := by
        rfl
      rw [htwo_int] at hk1
      omega
    exact ⟨hkpos, hk2⟩
  · have htwo_pos : Rlt ctx (R0 ctx) (Rtwo ctx) := by
      change ctx.spec.lt ctx.spec.zero
        (ctx.spec.add ctx.spec.one ctx.spec.one)
      have hone : ctx.spec.lt ctx.spec.zero ctx.spec.one :=
        middle_zero_lt_one ctx
      have hone_two := ctx.certificate.orderedField.add_lt_compat_l
        ctx.spec.one ctx.spec.zero ctx.spec.one hone
      rw [ctx.certificate.orderedField.add_zero] at hone_two
      exact ctx.certificate.orderedField.lt_trans _ _ _ hone hone_two
    have htwo_ne : ctx.spec.add ctx.spec.one ctx.spec.one ≠ ctx.spec.zero :=
      middle_two_ne_zero ctx
    have hz2 : IZR ctx Ztwo = Rtwo ctx := by
      change ctx.spec.ofZ Ztwo =
        ctx.spec.add ctx.spec.one ctx.spec.one
      have hZtwo : Ztwo = Zadd Zone Zone := by
        rfl
      rw [hZtwo, ctx.certificate.sourceLaws.ofZ_add,
        ctx.certificate.sourceLaws.ofZ_one]
    have hkreal : Rlt ctx (IZR ctx nb_steps)
        (Rmult ctx (Rtwo ctx) (IZR ctx k)) := by
      change ctx.spec.lt (ctx.spec.ofZ nb_steps)
        (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
          (ctx.spec.ofZ k))
      have hofz2 : ctx.spec.ofZ Ztwo =
          ctx.spec.add ctx.spec.one ctx.spec.one := by
        change ctx.spec.ofZ Ztwo =
          ctx.spec.add ctx.spec.one ctx.spec.one
        have hZtwo : Ztwo = Zadd Zone Zone := by
          rfl
        rw [hZtwo, ctx.certificate.sourceLaws.ofZ_add,
          ctx.certificate.sourceLaws.ofZ_one]
      rw [← hofz2]
      have hmult :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR
          ctx Ztwo k
      change ctx.spec.ofZ (Zmul Ztwo k) =
        ctx.spec.mul (ctx.spec.ofZ Ztwo) (ctx.spec.ofZ k) at hmult
      rw [← hmult]
      exact
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt
          ctx nb_steps (Zmul Ztwo k) hk1
    have htwo_pos' : Rlt ctx (IZR ctx Z0) (Rtwo ctx) := by
      change ctx.spec.lt (ctx.spec.ofZ Z0)
        (ctx.spec.add ctx.spec.one ctx.spec.one)
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact htwo_pos
    have hinv_pos : ctx.spec.lt ctx.spec.zero
        (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)) := by
      have h :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rinv_0_lt_compat
          ctx (Rtwo ctx) htwo_pos'
      change ctx.spec.lt (ctx.spec.ofZ Z0)
        (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)) at h
      rw [ctx.certificate.sourceLaws.ofZ_zero] at h
      exact h
    have hmul_inv : ctx.spec.lt (ctx.spec.mul (ctx.spec.inv
        (ctx.spec.add ctx.spec.one ctx.spec.one)) (ctx.spec.ofZ nb_steps))
        (ctx.spec.mul (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))
          (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
            (ctx.spec.ofZ k))) := by
      change ctx.spec.lt (ctx.spec.ofZ nb_steps)
        (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
          (ctx.spec.ofZ k)) at hkreal
      exact ctx.certificate.orderedField.mul_lt_compat_l
        (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))
        (ctx.spec.ofZ nb_steps)
        (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
          (ctx.spec.ofZ k)) hinv_pos hkreal
    have hdiv : Rlt ctx (Rdiv ctx (IZR ctx nb_steps) (Rtwo ctx))
        (IZR ctx k) := by
      change ctx.spec.lt
        (ctx.spec.div (ctx.spec.ofZ nb_steps)
          (ctx.spec.add ctx.spec.one ctx.spec.one))
        (ctx.spec.ofZ k)
      rw [ctx.certificate.orderedField.div_eq_mul_inv]
      rw [ctx.certificate.orderedField.mul_comm
        (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))
        (ctx.spec.ofZ nb_steps)] at hmul_inv
      have hright : ctx.spec.mul
          (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))
          (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
            (ctx.spec.ofZ k)) = ctx.spec.ofZ k := by
        rw [← ctx.certificate.orderedField.mul_assoc,
          ctx.certificate.orderedField.inv_mul_cancel _ htwo_ne,
          ctx.certificate.orderedField.one_mul]
      rw [hright] at hmul_inv
      exact hmul_inv
    have hmiddle : Rlt ctx
        (Rplus ctx start
          (Rmult ctx (Rdiv ctx (IZR ctx nb_steps) (Rtwo ctx)) step))
        (Rplus ctx start (Rmult ctx (IZR ctx k) step)) := by
      apply
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Raxioms.Rplus_lt_compat_l
          ctx start
      exact
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_compat_r
          ctx step (Rdiv ctx (IZR ctx nb_steps) (Rtwo ctx)) (IZR ctx k)
          hstep hdiv
    have hxbounds := inbetween_bounds ctx
      (Rplus ctx start (Rmult ctx (IZR ctx k) step))
      (Rplus ctx start (Rmult ctx (IZR ctx (Zadd k Zone)) step))
      (ordered_steps ctx start step hstep k) x l hx
    have hmiddle_x : Rlt ctx
        (Rplus ctx start
          (Rmult ctx (Rdiv ctx (IZR ctx nb_steps) (Rtwo ctx)) step)) x :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
        ctx _ _ _ hmiddle hxbounds.1
    exact bracket_Rcompare_gt ctx hmiddle_x

end CompCert4Lean.Flocq.Calc.Bracket

namespace CompCert4Lean.Flocq.Calc.Bracket

private theorem bracket_Rcompare_plus_l (ctx : ExactRealContext)
    (z x y : R ctx) :
    Rcompare ctx (Rplus ctx z x) (Rplus ctx z y) = Rcompare ctx x y := by
  change CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx
      (ctx.spec.add z x) (ctx.spec.add z y) =
    CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx x y
  rcases ctx.certificate.total_order x y with h | h
  · rcases h with hlt | heq
    · have hadd := ctx.certificate.orderedField.add_lt_compat_l z x y hlt
      have hleft :
          CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx
              (ctx.spec.add z x) (ctx.spec.add z y) = Lt :=
        bracket_Rcompare_lt ctx hadd
      have hright :
          CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx x y = Lt :=
        bracket_Rcompare_lt ctx hlt
      rw [hleft, hright]
    · subst y
      have hleft :
          CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx
              (ctx.spec.add z x) (ctx.spec.add z x) = Eq :=
        bracket_Rcompare_eq ctx rfl
      have hright :
          CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx x x = Eq :=
        bracket_Rcompare_eq ctx rfl
      rw [hleft, hright]
  · have hadd := ctx.certificate.orderedField.add_lt_compat_l z y x h
    have hleft :
        CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx
            (ctx.spec.add z x) (ctx.spec.add z y) = Gt :=
      bracket_Rcompare_gt ctx hadd
    have hright :
        CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx x y = Gt :=
      bracket_Rcompare_gt ctx h
    rw [hleft, hright]

theorem inbetween_step_Lo_Mi_Eq_odd :
    ∀ (ctx : ExactRealContext), inbetween_step_Lo_Mi_Eq_oddStatement ctx := by
  intro ctx start step nb_steps hstep hnb x k hx hEq
  apply inbetween_step_not_Eq ctx start step nb_steps hstep x k loc_Exact Lt hx
  · have hkpos : Zlt Z0 k := by
      change (0 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k
      have hnb' := hnb
      rw [← hEq] at hnb'
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Zadd (Zmul Ztwo k) Zone) at hnb'
      simp only [Zadd, Zmul,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hnb'
      have htwo_int :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = (2 : Int) := by
        rfl
      have hone_int :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by
        rfl
      rw [htwo_int, hone_int] at hnb'
      omega
    constructor
    · exact hkpos
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ nb_steps
      have hkpos_int := hkpos
      change (0 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k at hkpos_int
      rw [← hEq]
      simp only [Zadd, Zmul,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      have htwo_int :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = (2 : Int) := by
        rfl
      have hone_int :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by
        rfl
      rw [htwo_int, hone_int]
      omega
  · cases hx with
    | inbetween_Exact hxeq =>
        rw [hxeq]
        rw [bracket_Rcompare_plus_l ctx]
        have hstep0 : Rlt ctx (R0 ctx) step := by
          change ctx.spec.lt ctx.spec.zero step
          change ctx.spec.lt (ctx.spec.ofZ Z0) step at hstep
          rw [ctx.certificate.sourceLaws.ofZ_zero] at hstep
          exact hstep
        rw [bracket_Rcompare_mult_r ctx step _ _ hstep0]
        change CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx
            (ctx.spec.ofZ k)
            (CompCert4Lean.Flocq.Core.Raux.Exact.Rdiv ctx
              (ctx.spec.ofZ nb_steps)
              (CompCert4Lean.Flocq.Core.Raux.Exact.Rtwo ctx)) = Lt
        rw [CompCert4Lean.Flocq.Core.Raux.Rcompare_half_r ctx]
        have hz2 : IZR ctx Ztwo = Rtwo ctx := by
          change ctx.spec.ofZ Ztwo =
            ctx.spec.add ctx.spec.one ctx.spec.one
          have hZtwo : Ztwo = Zadd Zone Zone := by
            rfl
          rw [hZtwo, ctx.certificate.sourceLaws.ofZ_add,
            ctx.certificate.sourceLaws.ofZ_one]
        have hz2' :
            CompCert4Lean.Flocq.Core.Raux.Exact.Rtwo ctx =
              ctx.spec.ofZ Ztwo := by
          exact hz2.symm
        rw [hz2']
        have hmult :=
          CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR
            ctx Ztwo k
        change ctx.spec.ofZ (Zmul Ztwo k) =
          ctx.spec.mul (ctx.spec.ofZ Ztwo) (ctx.spec.ofZ k) at hmult
        change CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx
            (ctx.spec.mul (ctx.spec.ofZ Ztwo) (ctx.spec.ofZ k))
            (ctx.spec.ofZ nb_steps) = Lt
        rw [← hmult]
        rw [← hEq]
        apply bracket_Rcompare_lt ctx
        apply
          CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt
            ctx (Zmul Ztwo k) (Zadd (Zmul Ztwo k) Zone)
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zmul Ztwo k) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zadd (Zmul Ztwo k) Zone)
        simp only [Zadd, Zmul,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        have htwo_int :
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = (2 : Int) := by
          rfl
        have hone_int :
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by
          rfl
        rw [htwo_int, hone_int]
        omega

end CompCert4Lean.Flocq.Calc.Bracket

namespace CompCert4Lean.Flocq.Calc.Bracket

theorem inbetween_step_Hi_Mi_even :
    ∀ (ctx : ExactRealContext), inbetween_step_Hi_Mi_evenStatement ctx := by
  intro ctx start step nb_steps hstep hnb x k l hx hl hEq
  apply inbetween_step_not_Eq ctx start step nb_steps hstep x k l Gt hx
  · have hkpos : Zlt Z0 k := by
      change (0 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k
      have hnb' := hnb
      rw [← hEq] at hnb'
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zmul Ztwo k) at hnb'
      simp only [Zmul,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hnb'
      have htwo_int :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = (2 : Int) := by
        rfl
      have hone_int :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by
        rfl
      rw [htwo_int, hone_int] at hnb'
      omega
    constructor
    · exact hkpos
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ nb_steps
      have hkpos_int := hkpos
      change (0 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k at hkpos_int
      rw [← hEq]
      simp only [Zmul,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      have htwo_int :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = (2 : Int) := by
        rfl
      rw [htwo_int]
      omega
  · apply bracket_Rcompare_gt ctx
    have hxbounds := inbetween_bounds_not_Eq ctx
      (Rplus ctx start (Rmult ctx (IZR ctx k) step))
      (Rplus ctx start (Rmult ctx (IZR ctx (Zadd k Zone)) step)) x l hx hl
    have hmid_eq :
        Rplus ctx start
          (Rmult ctx (Rdiv ctx (IZR ctx nb_steps) (Rtwo ctx)) step) =
          Rplus ctx start (Rmult ctx (IZR ctx k) step) := by
      have hdiv_eq :
          Rdiv ctx (IZR ctx nb_steps) (Rtwo ctx) = IZR ctx k := by
        change ctx.spec.div (ctx.spec.ofZ nb_steps)
            (ctx.spec.add ctx.spec.one ctx.spec.one) = ctx.spec.ofZ k
        rw [ctx.certificate.orderedField.div_eq_mul_inv]
        rw [← hEq]
        have hmult :=
          CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR
            ctx Ztwo k
        change ctx.spec.ofZ (Zmul Ztwo k) =
          ctx.spec.mul (ctx.spec.ofZ Ztwo) (ctx.spec.ofZ k) at hmult
        rw [hmult]
        have hz2 : ctx.spec.ofZ Ztwo =
            ctx.spec.add ctx.spec.one ctx.spec.one := by
          have hZtwo : Ztwo = Zadd Zone Zone := by
            rfl
          rw [hZtwo, ctx.certificate.sourceLaws.ofZ_add,
            ctx.certificate.sourceLaws.ofZ_one]
        rw [hz2]
        calc
          ctx.spec.mul
              (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
                (ctx.spec.ofZ k))
              (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)) =
            ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
              (ctx.spec.mul (ctx.spec.ofZ k)
                (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))) :=
            ctx.certificate.orderedField.mul_assoc _ _ _
          _ = ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
              (ctx.spec.mul (ctx.spec.inv
                (ctx.spec.add ctx.spec.one ctx.spec.one))
                (ctx.spec.ofZ k)) := by
            congr 1
            exact ctx.certificate.orderedField.mul_comm _ _
          _ = ctx.spec.mul
              (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
                (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)))
              (ctx.spec.ofZ k) := by
            exact (ctx.certificate.orderedField.mul_assoc _ _ _).symm
          _ = ctx.spec.mul
              (ctx.spec.mul (ctx.spec.inv
                (ctx.spec.add ctx.spec.one ctx.spec.one))
                (ctx.spec.add ctx.spec.one ctx.spec.one))
              (ctx.spec.ofZ k) := by
            congr 1
            exact ctx.certificate.orderedField.mul_comm _ _
          _ = ctx.spec.mul ctx.spec.one (ctx.spec.ofZ k) := by
            rw [ctx.certificate.orderedField.inv_mul_cancel _
              (middle_two_ne_zero ctx)]
          _ = ctx.spec.ofZ k := ctx.certificate.orderedField.one_mul _
      rw [hdiv_eq]
    rw [hmid_eq]
    exact hxbounds.1

end CompCert4Lean.Flocq.Calc.Bracket

namespace CompCert4Lean.Flocq.Calc.Bracket

theorem inbetween_step_Mi_Mi_even :
    ∀ (ctx : ExactRealContext), inbetween_step_Mi_Mi_evenStatement ctx := by
  intro ctx start step nb_steps hstep hnb x k hx hEq
  have hkpos : Zlt Z0 k := by
    change (0 : Int) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k
    have hnb' := hnb
    rw [← hEq] at hnb'
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zmul Ztwo k) at hnb'
    simp only [Zmul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hnb'
    have htwo_int :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = (2 : Int) := by
      rfl
    have hone_int :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by
      rfl
    rw [htwo_int, hone_int] at hnb'
    omega
  have hklt : Zlt k nb_steps := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ nb_steps
    have hkpos_int := hkpos
    change (0 : Int) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k at hkpos_int
    rw [← hEq]
    simp only [Zmul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    have htwo_int :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = (2 : Int) := by
      rfl
    rw [htwo_int]
    omega
  apply inbetween_step_not_Eq ctx start step nb_steps hstep x k loc_Exact Eq hx
  · exact ⟨hkpos, hklt⟩
  · cases hx with
    | inbetween_Exact hxeq =>
        apply bracket_Rcompare_eq ctx
        rw [hxeq]
        have hdiv_eq : Rdiv ctx (IZR ctx nb_steps) (Rtwo ctx) = IZR ctx k := by
          change ctx.spec.div (ctx.spec.ofZ nb_steps)
              (ctx.spec.add ctx.spec.one ctx.spec.one) = ctx.spec.ofZ k
          rw [ctx.certificate.orderedField.div_eq_mul_inv]
          rw [← hEq]
          have hmult :=
            CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR
              ctx Ztwo k
          change ctx.spec.ofZ (Zmul Ztwo k) =
            ctx.spec.mul (ctx.spec.ofZ Ztwo) (ctx.spec.ofZ k) at hmult
          rw [hmult]
          have hz2 : ctx.spec.ofZ Ztwo =
              ctx.spec.add ctx.spec.one ctx.spec.one := by
            have hZtwo : Ztwo = Zadd Zone Zone := by
              rfl
            rw [hZtwo, ctx.certificate.sourceLaws.ofZ_add,
              ctx.certificate.sourceLaws.ofZ_one]
          rw [hz2]
          calc
            ctx.spec.mul
                (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
                  (ctx.spec.ofZ k))
                (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)) =
              ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
                (ctx.spec.mul (ctx.spec.ofZ k)
                  (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))) :=
              ctx.certificate.orderedField.mul_assoc _ _ _
            _ = ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
                (ctx.spec.mul (ctx.spec.inv
                  (ctx.spec.add ctx.spec.one ctx.spec.one))
                  (ctx.spec.ofZ k)) := by
              congr 1
              exact ctx.certificate.orderedField.mul_comm _ _
            _ = ctx.spec.mul
                (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
                  (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)))
                (ctx.spec.ofZ k) := by
              exact (ctx.certificate.orderedField.mul_assoc _ _ _).symm
            _ = ctx.spec.mul
                (ctx.spec.mul (ctx.spec.inv
                  (ctx.spec.add ctx.spec.one ctx.spec.one))
                  (ctx.spec.add ctx.spec.one ctx.spec.one))
                (ctx.spec.ofZ k) := by
              congr 1
              exact ctx.certificate.orderedField.mul_comm _ _
            _ = ctx.spec.mul ctx.spec.one (ctx.spec.ofZ k) := by
              rw [ctx.certificate.orderedField.inv_mul_cancel _
                (middle_two_ne_zero ctx)]
            _ = ctx.spec.ofZ k := ctx.certificate.orderedField.one_mul _
        rw [hdiv_eq]

end CompCert4Lean.Flocq.Calc.Bracket

namespace CompCert4Lean.Flocq.Calc.Bracket

theorem inbetween_unique :
    ∀ (ctx : ExactRealContext), inbetween_uniqueStatement ctx := by
  intro ctx d u x l l' h h'
  cases h with
  | inbetween_Exact hd =>
      cases h' with
      | inbetween_Exact hd' => rfl
      | inbetween_Inexact _ hb _ =>
          exfalso
          rw [hd] at hb
          exact (ctx.certificate.orderedField.lt_irrefl _ hb.1)
  | inbetween_Inexact c hb hm =>
      cases h' with
      | inbetween_Exact hd' =>
          exfalso
          rw [hd'] at hb
          exact (ctx.certificate.orderedField.lt_irrefl _ hb.1)
      | inbetween_Inexact c' hb' hm' =>
          have hc : c = c' := by simpa [hm] using hm'
          cases hc
          rfl

end CompCert4Lean.Flocq.Calc.Bracket

namespace CompCert4Lean.Flocq.Calc.Bracket

private theorem bracket_mul_inv_right (ctx : ExactRealContext)
    (x s : R ctx) (hsne : s ≠ ctx.spec.zero) :
    Rmult ctx (Rmult ctx x s)
        (CompCert4Lean.Flocq.Core.Raux.Exact.Rinv ctx s) = x := by
  change ctx.spec.mul (ctx.spec.mul x s) (ctx.spec.inv s) = x
  rw [ctx.certificate.orderedField.mul_assoc,
    ctx.certificate.orderedField.mul_comm s (ctx.spec.inv s),
    ctx.certificate.orderedField.inv_mul_cancel s hsne,
    ctx.certificate.orderedField.mul_one]

theorem inbetween_mult_reg :
    ∀ (ctx : ExactRealContext), inbetween_mult_regStatement ctx := by
  intro ctx x d u l s hs hbetween
  have hs0 : Rlt ctx (R0 ctx) s := by
    change ctx.spec.lt ctx.spec.zero s
    have hzero : IZR ctx Z0 = ctx.spec.zero :=
      ctx.certificate.sourceLaws.ofZ_zero
    rw [← hzero]
    exact hs
  have hsne : s ≠ ctx.spec.zero := by
    intro hzero
    subst s
    exact ctx.certificate.orderedField.lt_irrefl _ hs0
  have hs_inv : Rlt ctx (IZR ctx Z0)
      (CompCert4Lean.Flocq.Core.Raux.Exact.Rinv ctx s) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rinv_0_lt_compat
      ctx s hs
  have hscaled :=
    inbetween_mult_compat ctx
      (Rmult ctx x s) (Rmult ctx d s) (Rmult ctx u s) l
      (CompCert4Lean.Flocq.Core.Raux.Exact.Rinv ctx s) hs_inv hbetween
  rw [bracket_mul_inv_right ctx x s hsne,
    bracket_mul_inv_right ctx d s hsne,
    bracket_mul_inv_right ctx u s hsne] at hscaled
  exact hscaled

end CompCert4Lean.Flocq.Calc.Bracket

namespace CompCert4Lean.Flocq.Calc.Bracket

theorem inbetween_float_unique :
    ∀ (ctx : ExactRealContext), inbetween_float_uniqueStatement ctx := by
  intro ctx beta x e m l m' l' h h'
  have hb := inbetween_float_bounds ctx beta x m e l h
  have hb' := inbetween_float_bounds ctx beta x m' e l' h'
  have hmm1 : Zlt m (Zadd m' Zone) := by
    apply CompCert4Lean.Flocq.Core.Float_prop.lt_F2R ctx beta e m
      (Zadd m' Zone)
    exact
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
        ctx _ x _ hb.1 hb'.2
  have hmm2 : Zlt m' (Zadd m Zone) := by
    apply CompCert4Lean.Flocq.Core.Float_prop.lt_F2R ctx beta e m'
      (Zadd m Zone)
    exact
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
        ctx _ x _ hb'.1 hb.2
  have hmm1' := hmm1
  have hmm2' := hmm2
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd m' Zone) at hmm1'
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m' <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd m Zone) at hmm2'
  simp only [Zadd,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hmm1' hmm2'
  have hZone :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by
    rfl
  rw [hZone] at hmm1' hmm2'
  have hmm : m = m' := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    omega
  rw [← hmm] at h'
  unfold inbetween_float at h h'
  have hloc : l = l' := by
    exact inbetween_unique ctx
      (F2R ctx (Float beta m e))
      (F2R ctx (Float beta (Zadd m Zone) e)) x l l' h h'
  exact ⟨hmm, hloc⟩

end CompCert4Lean.Flocq.Calc.Bracket

namespace CompCert4Lean.Flocq.Calc.Bracket

private theorem pg_zero_lt_one (ctx : ExactRealContext) :
    ctx.spec.lt ctx.spec.zero ctx.spec.one := by
  rcases ctx.certificate.total_order ctx.spec.zero ctx.spec.one with h | h
  · rcases h with hlt | heq
    · exact hlt
    · exact (ctx.certificate.orderedField.zero_ne_one heq).elim
  · have hz := ctx.certificate.orderedField.add_lt_compat_l
      (ctx.spec.neg ctx.spec.one) ctx.spec.one ctx.spec.zero h
    rw [ctx.certificate.orderedField.neg_add_cancel,
      ctx.certificate.orderedField.add_zero] at hz
    have hm := ctx.certificate.orderedField.mul_lt_compat_l
      (ctx.spec.neg ctx.spec.one) ctx.spec.one ctx.spec.zero hz h
    rw [ctx.certificate.orderedField.mul_one,
      ctx.certificate.orderedField.mul_zero] at hm
    exact (ctx.certificate.orderedField.lt_irrefl _
      (ctx.certificate.orderedField.lt_trans _ _ _ hz hm)).elim

private theorem pg_two_ne_zero (ctx : ExactRealContext) :
    ctx.spec.add ctx.spec.one ctx.spec.one ≠ ctx.spec.zero := by
  have h1 := ctx.certificate.orderedField.add_lt_compat_l
    ctx.spec.one ctx.spec.zero ctx.spec.one (pg_zero_lt_one ctx)
  rw [ctx.certificate.orderedField.add_zero] at h1
  have h2 := ctx.certificate.orderedField.lt_trans _ _ _
    (pg_zero_lt_one ctx) h1
  intro h
  rw [h] at h2
  exact ctx.certificate.orderedField.lt_irrefl _ h2

private theorem pg_two_cancel_left (ctx : ExactRealContext) (a : R ctx) :
    Rmult ctx (Rmult ctx (Rtwo ctx) a) (ctx.spec.inv (Rtwo ctx)) = a := by
  change ctx.spec.mul
      (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one) a)
      (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)) = a
  calc
    ctx.spec.mul
        (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one) a)
        (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)) =
      ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
        (ctx.spec.mul a (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))) :=
      ctx.certificate.orderedField.mul_assoc _ _ _
    _ = ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
        (ctx.spec.mul (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)) a) := by
      rw [ctx.certificate.orderedField.mul_comm a]
    _ = ctx.spec.mul
        (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
          (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))) a := by
      rw [ctx.certificate.orderedField.mul_assoc]
    _ = ctx.spec.mul ctx.spec.one a := by
      rw [ctx.certificate.orderedField.mul_comm
          (ctx.spec.add ctx.spec.one ctx.spec.one)
          (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)),
        ctx.certificate.orderedField.inv_mul_cancel _ (pg_two_ne_zero ctx)]
    _ = a := ctx.certificate.orderedField.one_mul _

private theorem pg_upper_le_mid (ctx : ExactRealContext)
    (start step : R ctx) (nb_steps k : Z)
    (hstep : Rlt ctx (IZR ctx Z0) step)
    (hk2 : Zlt (Zadd (Zmul Ztwo k) Zone) nb_steps) :
    Rle ctx
      (Rplus ctx start (Rmult ctx (IZR ctx (Zadd k Zone)) step))
      (Rplus ctx start (Rmult ctx (Rdiv ctx (IZR ctx nb_steps) (Rtwo ctx)) step)) := by
  have hk2_le : Zle (Zmul Ztwo (Zadd k Zone)) nb_steps := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zmul Ztwo (Zadd k Zone)) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ nb_steps
    simp only [Zmul, Zadd,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add]
    repeat rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    have hh := hk2
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zadd (Zmul Ztwo k) Zone) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ nb_steps at hh
    simp only [Zmul, Zadd,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add] at hh
    repeat rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hh
    have htwo : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = (2 : Int) := by rfl
    have hone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by rfl
    rw [htwo, hone] at hh ⊢
    omega
  have hk2_izr_le : Rle ctx (IZR ctx (Zmul Ztwo (Zadd k Zone)))
      (IZR ctx nb_steps) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_le ctx _ _ hk2_le
  have htwo_izr : IZR ctx Ztwo = Rtwo ctx := by
    change CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR ctx.spec Ztwo =
      ctx.spec.add ctx.spec.one ctx.spec.one
    unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR
    rw [show Ztwo = Zadd Zone Zone by rfl,
      ctx.certificate.sourceLaws.ofZ_add, ctx.certificate.sourceLaws.ofZ_one]
  have hmultip :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR
      ctx Ztwo (Zadd k Zone)
  have hk2_izr_le2 : Rle ctx
      (Rmult ctx (IZR ctx Ztwo) (IZR ctx (Zadd k Zone)))
      (IZR ctx nb_steps) := by
    rw [← show IZR ctx (Zmul Ztwo (Zadd k Zone)) =
      Rmult ctx (IZR ctx Ztwo) (IZR ctx (Zadd k Zone)) by exact hmultip]
    exact hk2_izr_le
  rw [htwo_izr] at hk2_izr_le2
  have htwo_pos : Rlt ctx (IZR ctx Z0) (Rtwo ctx) := by
    change ctx.spec.lt (ctx.spec.ofZ Z0)
      (ctx.spec.add ctx.spec.one ctx.spec.one)
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    have h1 := ctx.certificate.orderedField.add_lt_compat_l
      ctx.spec.one ctx.spec.zero ctx.spec.one (pg_zero_lt_one ctx)
    rw [ctx.certificate.orderedField.add_zero] at h1
    exact ctx.certificate.orderedField.lt_trans _ _ _ (pg_zero_lt_one ctx) h1
  have hinv_le : Rle ctx (IZR ctx Z0) (ctx.spec.inv (Rtwo ctx)) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le ctx _ _
      (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rinv_0_lt_compat
        ctx _ htwo_pos)
  have hscaled :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
      ctx (ctx.spec.inv (Rtwo ctx)) _ _ hinv_le hk2_izr_le2
  have hdiv_le : Rle ctx (IZR ctx (Zadd k Zone))
      (Rdiv ctx (IZR ctx nb_steps) (Rtwo ctx)) := by
    have hscaled' := hscaled
    change ctx.spec.le
      (ctx.spec.mul
        (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
          (ctx.spec.ofZ (Zadd k Zone)))
        (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)))
      (ctx.spec.mul (ctx.spec.ofZ nb_steps)
        (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))) at hscaled'
    have hcancel := pg_two_cancel_left ctx (IZR ctx (Zadd k Zone))
    change ctx.spec.mul
        (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
          (ctx.spec.ofZ (Zadd k Zone)))
        (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)) =
      ctx.spec.ofZ (Zadd k Zone) at hcancel
    rw [hcancel] at hscaled'
    change ctx.spec.le (ctx.spec.ofZ (Zadd k Zone))
      (ctx.spec.div (ctx.spec.ofZ nb_steps)
        (ctx.spec.add ctx.spec.one ctx.spec.one))
    rw [ctx.certificate.orderedField.div_eq_mul_inv]
    exact hscaled'
  have hmult_le :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
      ctx step (IZR ctx (Zadd k Zone))
      (Rdiv ctx (IZR ctx nb_steps) (Rtwo ctx))
      (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le
        ctx _ _ hstep) hdiv_le
  exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_le_compat_l
    ctx start _ _ hmult_le

theorem inbetween_step_Lo (ctx : ExactRealContext) :
    inbetween_step_LoStatement ctx := by
  intro start step nb_steps hstep hnb x k l hx hk1 hk2
  have hk_lt : Zlt k nb_steps := by
    have hh := hk2
    have hh0 := hk1
    change (0 : Int) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k at hh0
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zadd (Zmul Ztwo k) Zone) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ nb_steps at hh
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ nb_steps
    simp only [Zmul, Zadd,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hh
    have htwo : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = (2 : Int) := by rfl
    have hone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by rfl
    rw [htwo, hone] at hh
    omega
  apply inbetween_step_not_Eq ctx start step nb_steps hstep x k l Lt hx
  · exact ⟨hk1, hk_lt⟩
  · have hinner := inbetween_bounds ctx
      (Rplus ctx start (Rmult ctx (IZR ctx k) step))
      (Rplus ctx start (Rmult ctx (IZR ctx (Zadd k Zone)) step))
      (ordered_steps ctx start step hstep k) x l hx
    have hupper_le := pg_upper_le_mid ctx start step nb_steps k hstep hk2
    have hmid :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
        ctx x (Rplus ctx start (Rmult ctx (IZR ctx (Zadd k Zone)) step)) _
        hinner.2 hupper_le
    exact bracket_Rcompare_lt ctx hmid

end CompCert4Lean.Flocq.Calc.Bracket

namespace CompCert4Lean.Flocq.Calc.Bracket

theorem inbetween_step_Lo_not_Eq (ctx : ExactRealContext) :
    inbetween_step_Lo_not_EqStatement ctx := by
  intro start step nb_steps hstep hnb x l hx hl
  have hx' := inbetween_bounds_not_Eq ctx start
    (Rplus ctx start step) x l hx hl
  have hstep0 : Rlt ctx (R0 ctx) step := by
    change ctx.spec.lt ctx.spec.zero step
    change ctx.spec.lt (ctx.spec.ofZ Z0) step at hstep
    rw [ctx.certificate.sourceLaws.ofZ_zero] at hstep
    exact hstep
  have hstep_lt : Rlt ctx step
      (Rmult ctx (IZR ctx nb_steps) step) := by
    have h :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_compat_r
        ctx step (IZR ctx Zone) (IZR ctx nb_steps) hstep
        (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt
          ctx Zone nb_steps hnb)
    change ctx.spec.lt
      (ctx.spec.mul (ctx.spec.ofZ Zone) step)
      (ctx.spec.mul (ctx.spec.ofZ nb_steps) step) at h
    rw [ctx.certificate.sourceLaws.ofZ_one,
      ctx.certificate.orderedField.one_mul] at h
    exact h
  have hupper_step : Rlt ctx
      (Rplus ctx start step)
      (Rplus ctx start (Rmult ctx (IZR ctx nb_steps) step)) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Raxioms.Rplus_lt_compat_l
      ctx start step (Rmult ctx (IZR ctx nb_steps) step) hstep_lt
  have hupper : Rlt ctx x
      (Rplus ctx start (Rmult ctx (IZR ctx nb_steps) step)) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Raxioms.Rlt_trans
      ctx x (Rplus ctx start step)
      (Rplus ctx start (Rmult ctx (IZR ctx nb_steps) step)) hx'.2 hupper_step
  apply inbetween_Inexact Lt
  · exact ⟨hx'.1, hupper⟩
  · apply bracket_Rcompare_lt ctx
    rw [middle_range ctx start step nb_steps]
    have hk2 : Zlt (Zadd (Zmul Ztwo Z0) Zone) nb_steps := by
      have hh := hnb
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ nb_steps at hh
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Zadd (Zmul Ztwo Z0) Zone) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ nb_steps
      simp only [Zmul, Zadd,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      exact hh
    have hmid := pg_upper_le_mid ctx start step nb_steps Z0 hstep hk2
    have hleft_eq :
        Rplus ctx start (Rmult ctx (IZR ctx (Zadd Z0 Zone)) step) =
          Rplus ctx start step := by
      congr 1
      change ctx.spec.mul (ctx.spec.ofZ (Zadd Z0 Zone)) step = step
      change ctx.spec.mul (ctx.spec.ofZ Zone) step = step
      rw [ctx.certificate.sourceLaws.ofZ_one,
        ctx.certificate.orderedField.one_mul]
    rw [hleft_eq] at hmid
    exact
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
        ctx x (Rplus ctx start step)
        (Rplus ctx start (Rmult ctx (Rdiv ctx (IZR ctx nb_steps) (Rtwo ctx)) step))
        hx'.2 hmid

end CompCert4Lean.Flocq.Calc.Bracket

namespace CompCert4Lean.Flocq.Calc.Bracket

private theorem middle_odd_num (ctx : ExactRealContext)
    (start step : R ctx) (k : Z) :
    Rplus ctx (Rplus ctx start (Rmult ctx (IZR ctx k) step))
        (Rplus ctx start (Rmult ctx (IZR ctx (Zadd k Zone)) step)) =
      Rplus ctx start
        (Rplus ctx start
          (Rmult ctx (IZR ctx (Zadd k (Zadd k Zone))) step)) := by
  have hzadd :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.plus_IZR
      ctx k (Zadd k Zone)
  change ctx.spec.ofZ (Zadd k (Zadd k Zone)) =
      ctx.spec.add (ctx.spec.ofZ k)
        (ctx.spec.ofZ (Zadd k Zone)) at hzadd
  change ctx.spec.add
      (ctx.spec.add start (ctx.spec.mul (ctx.spec.ofZ k) step))
      (ctx.spec.add start
        (ctx.spec.mul (ctx.spec.ofZ (Zadd k Zone)) step)) = _
  calc
    ctx.spec.add
        (ctx.spec.add start (ctx.spec.mul (ctx.spec.ofZ k) step))
        (ctx.spec.add start
          (ctx.spec.mul (ctx.spec.ofZ (Zadd k Zone)) step)) =
      ctx.spec.add
        (ctx.spec.add
          (ctx.spec.add start (ctx.spec.mul (ctx.spec.ofZ k) step)) start)
        (ctx.spec.mul (ctx.spec.ofZ (Zadd k Zone)) step) := by
          exact (ctx.certificate.orderedField.add_assoc
            (ctx.spec.add start (ctx.spec.mul (ctx.spec.ofZ k) step))
            start (ctx.spec.mul (ctx.spec.ofZ (Zadd k Zone)) step)).symm
    _ = ctx.spec.add
        (ctx.spec.add start
          (ctx.spec.add (ctx.spec.mul (ctx.spec.ofZ k) step) start))
        (ctx.spec.mul (ctx.spec.ofZ (Zadd k Zone)) step) := by
          congr 1
          exact ctx.certificate.orderedField.add_assoc start
            (ctx.spec.mul (ctx.spec.ofZ k) step) start
    _ = ctx.spec.add
        (ctx.spec.add start
          (ctx.spec.add start (ctx.spec.mul (ctx.spec.ofZ k) step)))
        (ctx.spec.mul (ctx.spec.ofZ (Zadd k Zone)) step) := by
          congr 2
          exact ctx.certificate.orderedField.add_comm
            (ctx.spec.mul (ctx.spec.ofZ k) step) start
    _ = ctx.spec.add start
        (ctx.spec.add
          (ctx.spec.add start (ctx.spec.mul (ctx.spec.ofZ k) step))
          (ctx.spec.mul (ctx.spec.ofZ (Zadd k Zone)) step)) := by
          exact ctx.certificate.orderedField.add_assoc start
            (ctx.spec.add start (ctx.spec.mul (ctx.spec.ofZ k) step))
            (ctx.spec.mul (ctx.spec.ofZ (Zadd k Zone)) step)
    _ = ctx.spec.add start
        (ctx.spec.add start
          (ctx.spec.add
            (ctx.spec.mul (ctx.spec.ofZ k) step)
            (ctx.spec.mul (ctx.spec.ofZ (Zadd k Zone)) step))) := by
          exact congrArg (fun q => ctx.spec.add start q)
            (ctx.certificate.orderedField.add_assoc start
              (ctx.spec.mul (ctx.spec.ofZ k) step)
              (ctx.spec.mul (ctx.spec.ofZ (Zadd k Zone)) step))
    _ = ctx.spec.add start
        (ctx.spec.add start
          (ctx.spec.mul
            (ctx.spec.add (ctx.spec.ofZ k)
              (ctx.spec.ofZ (Zadd k Zone))) step)) := by
          congr 2
          calc
            ctx.spec.add
                (ctx.spec.mul (ctx.spec.ofZ k) step)
                (ctx.spec.mul (ctx.spec.ofZ (Zadd k Zone)) step) =
              ctx.spec.add
                (ctx.spec.mul step (ctx.spec.ofZ k))
                (ctx.spec.mul step (ctx.spec.ofZ (Zadd k Zone))) := by
                  rw [ctx.certificate.orderedField.mul_comm
                    (ctx.spec.ofZ k) step,
                    ctx.certificate.orderedField.mul_comm
                      (ctx.spec.ofZ (Zadd k Zone)) step]
            _ = ctx.spec.mul step
                (ctx.spec.add (ctx.spec.ofZ k)
                  (ctx.spec.ofZ (Zadd k Zone))) :=
              (ctx.certificate.orderedField.left_distrib step _ _).symm
            _ = ctx.spec.mul
                (ctx.spec.add (ctx.spec.ofZ k)
                  (ctx.spec.ofZ (Zadd k Zone))) step :=
              ctx.certificate.orderedField.mul_comm _ _
    _ = ctx.spec.add start
        (ctx.spec.add start
          (ctx.spec.mul (ctx.spec.ofZ (Zadd k (Zadd k Zone))) step)) := by
          rw [hzadd]

end CompCert4Lean.Flocq.Calc.Bracket

namespace CompCert4Lean.Flocq.Calc.Bracket

theorem middle_odd (ctx : ExactRealContext) :
    middle_oddStatement ctx := by
  intro start step nb_steps k hEq
  have hk : Zadd k (Zadd k Zone) = nb_steps := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    have hEq' := congrArg
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hEq
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zadd (Zmul Ztwo k) Zone) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ nb_steps at hEq'
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zadd k (Zadd k Zone)) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ nb_steps
    simp only [Zadd, Zmul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hEq' ⊢
    have htwo :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = (2 : Int) := by
      rfl
    have hone :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by
      rfl
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k +
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k + 1) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ nb_steps
    change 2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k + 1 =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ nb_steps at hEq'
    omega
  rw [middle_odd_num ctx start step k]
  rw [middle_range ctx start step (Zadd k (Zadd k Zone))]
  rw [hk]

end CompCert4Lean.Flocq.Calc.Bracket

namespace CompCert4Lean.Flocq.Calc.Bracket

open CompCert4Lean.Foundation.Numbers.Rocq.Coq in
theorem inbetween_step_any_Mi_odd (ctx : ExactRealContext) :
    inbetween_step_any_Mi_oddStatement ctx := by
  intro start step nb_steps hstep hnb x k l hx hmid
  have hnb_int : (1 : Int) < intOfZ nb_steps := hnb
  have hmid_int := congrArg intOfZ hmid
  simp only [Zadd, Zmul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
    intOfZ_zOfInt] at hmid_int
  change 2 * intOfZ k + 1 = intOfZ nb_steps at hmid_int
  apply inbetween_step_not_Eq ctx start step nb_steps hstep x k (loc_Inexact l) l hx
  · change 0 < intOfZ k ∧ intOfZ k < intOfZ nb_steps
    omega
  · cases hx with
    | inbetween_Inexact _ _ hcompare =>
      rw [middle_odd ctx start step nb_steps k hmid] at hcompare
      exact hcompare

end CompCert4Lean.Flocq.Calc.Bracket

namespace CompCert4Lean.Flocq.Calc.Bracket

open CompCert4Lean.Foundation.Numbers.Rocq.Coq in
theorem new_location_even_correct (ctx : ExactRealContext) :
    new_location_even_correctStatement ctx := by
  intro start step nb_steps hstep hnb heven x k l hk hx
  unfold new_location_even
  by_cases hk0 : k = Z0
  · have hbool : Zeq_bool k Z0 = true :=
      CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_true k Z0 hk0
    rw [hbool]
    simp only [↓reduceIte]
    subst k
    have hzero : Rplus ctx start (Rmult ctx (IZR ctx Z0) step) = start := by
      change ctx.spec.add start (ctx.spec.mul (ctx.spec.ofZ Z0) step) = start
      rw [ctx.certificate.sourceLaws.ofZ_zero,
        ctx.certificate.orderedField.zero_mul, ctx.certificate.orderedField.add_zero]
    have hone : Rplus ctx start (Rmult ctx (IZR ctx (Zadd Z0 Zone)) step) =
        Rplus ctx start step := by
      change ctx.spec.add start (ctx.spec.mul (ctx.spec.ofZ Zone) step) =
        ctx.spec.add start step
      rw [ctx.certificate.sourceLaws.ofZ_one, ctx.certificate.orderedField.one_mul]
    rw [hzero, hone] at hx
    cases l with
    | loc_Exact =>
      cases hx with
      | inbetween_Exact hxeq => exact inbetween_Exact hxeq
    | loc_Inexact c =>
      exact inbetween_step_Lo_not_Eq ctx start step nb_steps hstep hnb x
        (loc_Inexact c) hx (by intro h; cases h)
  · have hbool : Zeq_bool k Z0 = false :=
      CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false k Z0 hk0
    rw [hbool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hkpos : Zlt Z0 k := by
      have hk_nonneg : (0 : Int) ≤ intOfZ k := hk.1
      have hk_ne : intOfZ k ≠ 0 := by
        intro h
        exact hk0 (intOfZ_injective h)
      change (0 : Int) < intOfZ k
      omega
    generalize hcompare : Zcompare (Zmul Ztwo k) nb_steps = c
    have hspec : CompCert4Lean.Flocq.Core.Zaux.Zcompare_prop
        (Zmul Ztwo k) nb_steps c := by
      rw [← hcompare]
      exact CompCert4Lean.Flocq.Core.Zaux.Zcompare_spec (Zmul Ztwo k) nb_steps
    cases hspec with
    | Zcompare_Lt_ hcmp =>
      apply inbetween_step_Lo ctx start step nb_steps hstep hnb x k l hx hkpos
      obtain ⟨p, hp⟩ := CompCert4Lean.Flocq.Core.Zaux.Zeven_ex nb_steps
      change nb_steps = Zadd (Zmul Ztwo p) (if Zeven nb_steps then Z0 else Zone) at hp
      rw [heven] at hp
      simp only [↓reduceIte] at hp
      have hp_int := congrArg intOfZ hp
      have hcmp_int := hcmp
      change intOfZ (Zmul Ztwo k) < intOfZ nb_steps at hcmp_int
      change intOfZ (Zadd (Zmul Ztwo k) Zone) < intOfZ nb_steps
      simp only [Zadd, Zmul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
        intOfZ_zOfInt] at hp_int hcmp_int ⊢
      change intOfZ nb_steps = 2 * intOfZ p + 0 at hp_int
      change 2 * intOfZ k < intOfZ nb_steps at hcmp_int
      change 2 * intOfZ k + 1 < intOfZ nb_steps
      omega
    | Zcompare_Eq_ hcmp =>
      cases l with
      | loc_Exact =>
        exact inbetween_step_Mi_Mi_even ctx start step nb_steps hstep hnb x k hx hcmp
      | loc_Inexact c =>
        exact inbetween_step_Hi_Mi_even ctx start step nb_steps hstep hnb x k
          (loc_Inexact c) hx (by intro h; cases h) hcmp
    | Zcompare_Gt_ hcmp =>
      exact inbetween_step_Hi ctx start step nb_steps hstep hnb x k l hx hcmp hk.2

end CompCert4Lean.Flocq.Calc.Bracket

namespace CompCert4Lean.Flocq.Calc.Bracket

open CompCert4Lean.Foundation.Numbers.Rocq.Coq in
theorem new_location_odd_correct (ctx : ExactRealContext) :
    new_location_odd_correctStatement ctx := by
  intro start step nb_steps hstep hnb hodd x k l hk hx
  unfold new_location_odd
  by_cases hk0 : k = Z0
  · have hbool : Zeq_bool k Z0 = true :=
      CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_true k Z0 hk0
    rw [hbool]
    simp only [↓reduceIte]
    subst k
    have hzero : Rplus ctx start (Rmult ctx (IZR ctx Z0) step) = start := by
      change ctx.spec.add start (ctx.spec.mul (ctx.spec.ofZ Z0) step) = start
      rw [ctx.certificate.sourceLaws.ofZ_zero,
        ctx.certificate.orderedField.zero_mul, ctx.certificate.orderedField.add_zero]
    have hone : Rplus ctx start (Rmult ctx (IZR ctx (Zadd Z0 Zone)) step) =
        Rplus ctx start step := by
      change ctx.spec.add start (ctx.spec.mul (ctx.spec.ofZ Zone) step) =
        ctx.spec.add start step
      rw [ctx.certificate.sourceLaws.ofZ_one, ctx.certificate.orderedField.one_mul]
    rw [hzero, hone] at hx
    cases l with
    | loc_Exact =>
      cases hx with
      | inbetween_Exact hxeq => exact inbetween_Exact hxeq
    | loc_Inexact c =>
      exact inbetween_step_Lo_not_Eq ctx start step nb_steps hstep hnb x
        (loc_Inexact c) hx (by intro h; cases h)
  · have hbool : Zeq_bool k Z0 = false :=
      CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false k Z0 hk0
    rw [hbool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hkpos : Zlt Z0 k := by
      have hk_nonneg : (0 : Int) ≤ intOfZ k := hk.1
      have hk_ne : intOfZ k ≠ 0 := by
        intro h
        exact hk0 (intOfZ_injective h)
      change (0 : Int) < intOfZ k
      omega
    generalize hcompare : Zcompare (Zadd (Zmul Ztwo k) Zone) nb_steps = c
    have hspec : CompCert4Lean.Flocq.Core.Zaux.Zcompare_prop
        (Zadd (Zmul Ztwo k) Zone) nb_steps c := by
      rw [← hcompare]
      exact CompCert4Lean.Flocq.Core.Zaux.Zcompare_spec
        (Zadd (Zmul Ztwo k) Zone) nb_steps
    cases hspec with
    | Zcompare_Lt_ hcmp =>
      exact inbetween_step_Lo ctx start step nb_steps hstep hnb x k l hx hkpos hcmp
    | Zcompare_Eq_ hcmp =>
      cases l with
      | loc_Exact =>
        exact inbetween_step_Lo_Mi_Eq_odd ctx start step nb_steps hstep hnb x k hx hcmp
      | loc_Inexact c =>
        exact inbetween_step_any_Mi_odd ctx start step nb_steps hstep hnb x k c hx hcmp
    | Zcompare_Gt_ hcmp =>
      apply inbetween_step_Hi ctx start step nb_steps hstep hnb x k l hx _ hk.2
      obtain ⟨p, hp⟩ := CompCert4Lean.Flocq.Core.Zaux.Zeven_ex nb_steps
      change nb_steps = Zadd (Zmul Ztwo p) (if Zeven nb_steps then Z0 else Zone) at hp
      rw [hodd] at hp
      simp only [Bool.false_eq_true, ↓reduceIte] at hp
      have hp_int := congrArg intOfZ hp
      have hcmp_int := hcmp
      change intOfZ nb_steps < intOfZ (Zadd (Zmul Ztwo k) Zone) at hcmp_int
      change intOfZ nb_steps < intOfZ (Zmul Ztwo k)
      simp only [Zadd, Zmul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
        intOfZ_zOfInt] at hp_int hcmp_int ⊢
      change intOfZ nb_steps = 2 * intOfZ p + 1 at hp_int
      change intOfZ nb_steps < 2 * intOfZ k + 1 at hcmp_int
      change intOfZ nb_steps < 2 * intOfZ k
      omega

end CompCert4Lean.Flocq.Calc.Bracket

namespace CompCert4Lean.Flocq.Calc.Bracket

private theorem bracket_ex_midpoint_bounds (ctx : ExactRealContext)
    (a b : R ctx) (hab : Rlt ctx a b) :
    Rlt ctx a (Rdiv ctx (Rplus ctx a b) (Rtwo ctx)) ∧
      Rlt ctx (Rdiv ctx (Rplus ctx a b) (Rtwo ctx)) b := by
  have htwo : ctx.spec.lt ctx.spec.zero (Rtwo ctx) := by
    have h := ctx.certificate.orderedField.add_lt_compat_l
      ctx.spec.one ctx.spec.zero ctx.spec.one (middle_zero_lt_one ctx)
    rw [ctx.certificate.orderedField.add_zero] at h
    exact ctx.certificate.orderedField.lt_trans _ _ _ (middle_zero_lt_one ctx) h
  have hinv : ctx.spec.lt ctx.spec.zero (ctx.spec.inv (Rtwo ctx)) := by
    have htwo' : Rlt ctx (IZR ctx Z0) (Rtwo ctx) := by
      change ctx.spec.lt (ctx.spec.ofZ Z0) (Rtwo ctx)
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact htwo
    have h := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rinv_0_lt_compat
      ctx (Rtwo ctx) htwo'
    change ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.inv (Rtwo ctx)) at h
    rw [ctx.certificate.sourceLaws.ofZ_zero] at h
    exact h
  have hdouble (x : R ctx) :
      ctx.spec.mul (ctx.spec.inv (Rtwo ctx)) (ctx.spec.add x x) = x := by
    rw [ctx.certificate.orderedField.mul_comm, ← middle_two_mul ctx x]
    exact pg_two_cancel_left ctx x
  have hmid : Rdiv ctx (Rplus ctx a b) (Rtwo ctx) =
      ctx.spec.mul (ctx.spec.inv (Rtwo ctx)) (ctx.spec.add a b) := by
    change ctx.spec.div (ctx.spec.add a b) (Rtwo ctx) = _
    rw [ctx.certificate.orderedField.div_eq_mul_inv,
      ctx.certificate.orderedField.mul_comm]
  rw [hmid]
  constructor
  · have h := ctx.certificate.orderedField.mul_lt_compat_l
      (ctx.spec.inv (Rtwo ctx)) _ _ hinv
      (ctx.certificate.orderedField.add_lt_compat_l a a b hab)
    rw [hdouble] at h
    exact h
  · have h := ctx.certificate.orderedField.add_lt_compat_l b a b hab
    rw [ctx.certificate.orderedField.add_comm b a] at h
    have h' := ctx.certificate.orderedField.mul_lt_compat_l
      (ctx.spec.inv (Rtwo ctx)) _ _ hinv h
    rw [hdouble] at h'
    exact h'

theorem inbetween_ex (ctx : ExactRealContext) : inbetween_exStatement ctx := by
  intro d u l hdu
  cases l with
  | loc_Exact => exact ⟨d, inbetween_Exact rfl⟩
  | loc_Inexact c =>
      let m := Rdiv ctx (Rplus ctx d u) (Rtwo ctx)
      have hm : Rlt ctx d m ∧ Rlt ctx m u := bracket_ex_midpoint_bounds ctx d u hdu
      cases c with
      | Eq =>
          exact ⟨m, inbetween_Inexact Eq hm (bracket_Rcompare_eq ctx rfl)⟩
      | Lt =>
          let x := Rdiv ctx (Rplus ctx d m) (Rtwo ctx)
          have hx : Rlt ctx d x ∧ Rlt ctx x m :=
            bracket_ex_midpoint_bounds ctx d m hm.1
          exact ⟨x, inbetween_Inexact Lt
            ⟨hx.1, ctx.certificate.orderedField.lt_trans _ _ _ hx.2 hm.2⟩
            (bracket_Rcompare_lt ctx hx.2)⟩
      | Gt =>
          let x := Rdiv ctx (Rplus ctx m u) (Rtwo ctx)
          have hx : Rlt ctx m x ∧ Rlt ctx x u :=
            bracket_ex_midpoint_bounds ctx m u hm.2
          exact ⟨x, inbetween_Inexact Gt
            ⟨ctx.certificate.orderedField.lt_trans _ _ _ hm.1 hx.1, hx.2⟩
            (bracket_Rcompare_gt ctx hx.1)⟩

end CompCert4Lean.Flocq.Calc.Bracket

namespace CompCert4Lean.Flocq.Calc.Bracket

theorem new_location_correct (ctx : ExactRealContext) :
    new_location_correctStatement ctx := by
  intro start step nb_steps hstep hnb x k l hk hx
  unfold new_location
  by_cases heven : Zeven nb_steps = true
  · simp only [heven, ↓reduceIte]
    exact new_location_even_correct ctx start step nb_steps hstep hnb heven x k l hk hx
  · have hodd : Zeven nb_steps = false := by
      cases h : Zeven nb_steps <;> simp_all
    simp only [hodd, Bool.false_eq_true, ↓reduceIte]
    exact new_location_odd_correct ctx start step nb_steps hstep hnb hodd x k l hk hx

theorem inbetween_float_ex (ctx : ExactRealContext) :
    inbetween_float_exStatement ctx := by
  intro beta m e l
  apply inbetween_ex ctx
  exact CompCert4Lean.Flocq.Core.Float_prop.F2R_lt ctx beta e m
    (Zadd m Zone)
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zorder.Zlt_succ_proof m)

end CompCert4Lean.Flocq.Calc.Bracket
