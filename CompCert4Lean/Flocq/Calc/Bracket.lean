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
