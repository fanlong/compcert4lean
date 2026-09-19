import CompCert4Lean.Flocq.Core.Generic_fmt

/-!
# Unit in the last place

This module contains the definition-bearing surface selected from
`Flocq.Core.Ulp`.  The four proof-bearing declarations assigned to the later
proof phase are represented by exact proposition descriptors below.
-/

namespace CompCert4Lean.Flocq.Core.Ulp

abbrev R := CompCert4Lean.Flocq.Core.Raux.R
abbrev Z := CompCert4Lean.Flocq.Core.Zaux.Z
abbrev radix := CompCert4Lean.Flocq.Core.Zaux.radix
abbrev Z0 := CompCert4Lean.Flocq.Core.Zaux.Z0
abbrev Zle := CompCert4Lean.Flocq.Core.Zaux.Zle
abbrev IZR := CompCert4Lean.Flocq.Core.Raux.IZR
abbrev R0 := CompCert4Lean.Flocq.Core.Raux.R0
abbrev Rabs := CompCert4Lean.Flocq.Core.Raux.Rabs
abbrev Rminus := CompCert4Lean.Flocq.Core.Raux.Rminus
abbrev Rlt := CompCert4Lean.Flocq.Core.Raux.Rlt
abbrev Req_bool := CompCert4Lean.Flocq.Core.Raux.Req_bool
abbrev cexp := CompCert4Lean.Flocq.Core.Generic_fmt.cexp
abbrev generic_format := CompCert4Lean.Flocq.Core.Generic_fmt.generic_format
abbrev round := CompCert4Lean.Flocq.Core.Generic_fmt.round
abbrev Valid_exp := CompCert4Lean.Flocq.Core.Generic_fmt.Valid_exp
abbrev Valid_rnd := CompCert4Lean.Flocq.Core.Generic_fmt.Valid_rnd
abbrev Zceil := CompCert4Lean.Flocq.Core.Raux.Zceil
abbrev Zfloor := CompCert4Lean.Flocq.Core.Raux.Zfloor
abbrev Sumor := CompCert4Lean.Foundation.Logic.Support.Sumor
abbrev Rle_bool := CompCert4Lean.Flocq.Core.Raux.Rle_bool
abbrev Rplus := CompCert4Lean.Flocq.Core.Raux.Rplus
abbrev Ropp := CompCert4Lean.Flocq.Core.Raux.Ropp
abbrev Rge := CompCert4Lean.Flocq.Core.Raux.Rge
abbrev Rgt := CompCert4Lean.Flocq.Core.Raux.Rgt
abbrev Rle := CompCert4Lean.Flocq.Core.Raux.Rle
abbrev Rdiv := CompCert4Lean.Flocq.Core.Raux.Rdiv
abbrev Rtwo := CompCert4Lean.Flocq.Core.Raux.Rtwo
abbrev mag := CompCert4Lean.Flocq.Core.Raux.mag
abbrev Zone := CompCert4Lean.Flocq.Core.Zaux.Zone
abbrev Zopp := CompCert4Lean.Flocq.Core.Zaux.Zopp
abbrev Zsub := CompCert4Lean.Flocq.Core.Zaux.Zsub
abbrev Zlt := CompCert4Lean.Flocq.Core.Zaux.Zlt
abbrev Ztrunc := CompCert4Lean.Flocq.Core.Raux.Ztrunc
abbrev Znearest := CompCert4Lean.Flocq.Core.Generic_fmt.Znearest
abbrev Rnd_DN_pt := CompCert4Lean.Flocq.Core.Defs.Rnd_DN_pt
abbrev Rnd_UP_pt := CompCert4Lean.Flocq.Core.Defs.Rnd_UP_pt
abbrev Rnd_N_pt := CompCert4Lean.Flocq.Core.Defs.Rnd_N_pt
abbrev Zrnd_opp := CompCert4Lean.Flocq.Core.Generic_fmt.Zrnd_opp

/- The source notation is a local abbreviation for the provider's bpow. -/
def bpow (beta : radix) (e : Z) : R :=
  CompCert4Lean.Flocq.Core.Raux.bpow beta e

noncomputable def negligible_exp (fexp : Z → Z) : Option Z :=
  match CompCert4Lean.Flocq.Core.Raux.LPO_Z
      (fun z => Zle z (fexp z))
      (fun z =>
        match CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.ZArith_dec.Z_le_dec
            z (fexp z) with
        | .left h => Or.inl h
        | .right h => Or.inr h) with
  | .inleft witness => some witness.val
  | .inright _ => none

inductive negligible_exp_prop (fexp : Z → Z) : Option Z → Prop where
  | negligible_None : (∀ n : Z, Raux.Zlt (fexp n) n) → negligible_exp_prop fexp none
  | negligible_Some : ∀ n : Z, Zle n (fexp n) → negligible_exp_prop fexp (some n)

abbrev negligible_None (fexp : Z → Z) :=
  negligible_exp_prop.negligible_None (fexp := fexp)
abbrev negligible_Some (fexp : Z → Z) :=
  negligible_exp_prop.negligible_Some (fexp := fexp)

noncomputable def ulp (beta : radix) (fexp : Z → Z) (x : R) : R :=
  match Req_bool x R0 with
  | true =>
      match negligible_exp fexp with
      | some n => bpow beta (fexp n)
      | none => R0
  | false => bpow beta (cexp beta fexp x)

def F (beta : radix) (fexp : Z → Z) (x : R) : Prop :=
  generic_format beta fexp x

noncomputable def pred_pos (beta : radix) (fexp : Z → Z) (x : R) : R :=
  if Req_bool x (bpow beta (Zsub (mag beta x : Z) Zone)) then
    Rminus x (bpow beta (fexp (Zsub (mag beta x : Z) Zone)))
  else Rminus x (ulp beta fexp x)

noncomputable def succ (beta : radix) (fexp : Z → Z) (x : R) : R :=
  if Rle_bool R0 x then Rplus x (ulp beta fexp x)
  else Ropp (pred_pos beta fexp (Ropp x))

noncomputable def pred (beta : radix) (fexp : Z → Z) (x : R) : R :=
  Ropp (succ beta fexp (Ropp x))

/-! The theorem-facing layer is parameterised by the exact carrier. -/

abbrev ExactRealContext := CompCert4Lean.Flocq.Core.Generic_fmt.ExactRealContext

namespace Exact

abbrev Context := ExactRealContext
abbrev Magnitude (ctx : Context) := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Magnitude ctx
abbrev R (ctx : Context) := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R ctx
abbrev R0 := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R0
abbrev Ropp := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ropp
abbrev Rplus := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rplus
abbrev Rminus := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rminus
abbrev Rabs := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rabs
abbrev Rlt := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rlt
abbrev Rle := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rle
abbrev Rge := CompCert4Lean.Flocq.Core.Raux.Exact.Rge
abbrev Rgt := CompCert4Lean.Flocq.Core.Raux.Exact.Rgt
noncomputable abbrev Req_bool := CompCert4Lean.Flocq.Core.Raux.Exact.Req_bool
noncomputable abbrev Rle_bool := CompCert4Lean.Flocq.Core.Raux.Exact.Rle_bool
abbrev bpow := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.bpow
abbrev mag (ctx : Context) (magnitude : Magnitude ctx) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.mag magnitude
abbrev cexp (ctx : Context) (magnitude : Magnitude ctx) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude
abbrev generic_format (ctx : Context) (magnitude : Magnitude ctx) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.generic_format ctx magnitude
abbrev round (ctx : Context) (magnitude : Magnitude ctx) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round ctx magnitude
abbrev Valid_rnd := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Valid_rnd
noncomputable abbrev Znearest := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Znearest
abbrev Rnd_DN_pt := CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_DN_pt
abbrev Rnd_UP_pt := CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_UP_pt
abbrev Rnd_N_pt := CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_N_pt

noncomputable def ulp (ctx : Context) (magnitude : Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (x : R ctx) : R ctx :=
  match Req_bool ctx x (R0 ctx) with
  | true =>
      match negligible_exp fexp with
      | some n => bpow ctx beta (fexp n)
      | none => R0 ctx
  | false => bpow ctx beta (cexp ctx magnitude beta fexp x)

def F (ctx : Context) (magnitude : Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (x : R ctx) : Prop :=
  generic_format ctx magnitude beta fexp x

noncomputable def pred_pos (ctx : Context) (magnitude : Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (x : R ctx) : R ctx :=
  if Req_bool ctx x (bpow ctx beta (Zsub (mag ctx magnitude beta x) Zone)) then
    Rminus ctx x (bpow ctx beta (fexp (Zsub (mag ctx magnitude beta x) Zone)))
  else Rminus ctx x (ulp ctx magnitude beta fexp x)

noncomputable def succ (ctx : Context) (magnitude : Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (x : R ctx) : R ctx :=
  if Rle_bool ctx (R0 ctx) x then
    Rplus ctx x (ulp ctx magnitude beta fexp x)
  else Ropp ctx (pred_pos ctx magnitude beta fexp (Ropp ctx x))

noncomputable def pred (ctx : Context) (magnitude : Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (x : R ctx) : R ctx :=
  Ropp ctx (succ ctx magnitude beta fexp (Ropp ctx x))

end Exact

/-! Exact source proposition descriptors for the later proof phase. -/

def Z_le_dec_auxStatement : Prop :=
  ∀ (x y : Z), Zle x y ∨ ¬ Zle x y

section ExactStatements

variable (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)

local notation "R" => Exact.R ctx
local notation "R0" => Exact.R0 ctx
local notation "Rabs" => Exact.Rabs ctx
local notation "Rminus" => Exact.Rminus ctx
local notation "Rlt" => Exact.Rlt ctx
local notation "Rle" => Exact.Rle ctx
local notation "Rge" => Exact.Rge ctx
local notation "Rgt" => Exact.Rgt ctx
local notation "Rplus" => Exact.Rplus ctx
local notation "Ropp" => Exact.Ropp ctx
local notation "Rdiv" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rdiv ctx
local notation "Rtwo" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rtwo ctx
local notation "Zfloor" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx
local notation "Zceil" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx
local notation "Req_bool" => Exact.Req_bool ctx
local notation "Rle_bool" => Exact.Rle_bool ctx
local notation "bpow" => Exact.bpow ctx
local notation "mag" => Exact.mag ctx magnitude
local notation "cexp" => Exact.cexp ctx magnitude
local notation "generic_format" => Exact.generic_format ctx magnitude
local notation "round" => Exact.round ctx magnitude
local notation "ulp" => Exact.ulp ctx magnitude
local notation "pred_pos" => Exact.pred_pos ctx magnitude
local notation "succ" => Exact.succ ctx magnitude
local notation "pred" => Exact.pred ctx magnitude
local notation "Valid_rnd" => Exact.Valid_rnd ctx
local notation "Rnd_DN_pt" => Exact.Rnd_DN_pt ctx
local notation "Rnd_UP_pt" => Exact.Rnd_UP_pt ctx
local notation "Rnd_N_pt" => Exact.Rnd_N_pt ctx
local notation "Znearest" => Exact.Znearest ctx

def ulp_neq_0Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (x : R),
    x ≠ R0 →
      ulp beta fexp x = bpow beta (cexp beta fexp x)

def round_UP_DN_ulpStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (x : R),
    ¬ generic_format beta fexp x →
      round beta fexp Zceil x =
        Rplus
          (round beta fexp Zfloor x) (ulp beta fexp x)

def error_lt_ulpStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z),
    Valid_exp fexp →
      ∀ (rnd : R → Z),
        Valid_rnd rnd →
          ∀ (x : R), x ≠ R0 →
            Rlt
              (Rabs (Rminus (round beta fexp rnd x) x))
              (ulp beta fexp x)

def negligible_exp_specStatement : Prop :=
  ∀ (fexp : Z → Z),
    negligible_exp_prop fexp (negligible_exp fexp)

def negligible_exp_spec'Statement : Prop :=
  ∀ (fexp : Z → Z),
    (negligible_exp fexp = none ∧ ∀ n, Raux.Zlt (fexp n) n) ∨
      ∃ n, negligible_exp fexp = some n ∧ Zle n (fexp n)

def fexp_negligible_exp_eqStatement : Prop :=
  ∀ (fexp : Z → Z), Valid_exp fexp →
    ∀ n m, Zle n (fexp n) → Zle m (fexp m) → fexp n = fexp m

def generic_format_ulp_0Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    generic_format beta fexp (ulp beta fexp R0)

def ulp_ge_0Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (x : R), Rle R0 (ulp beta fexp x)

def ulp_le_idStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), ∀ x,
    Rlt R0 x → generic_format beta fexp x → Rle (ulp beta fexp x) x

def generic_format_succ_aux1Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x,
    Rlt R0 x → generic_format beta fexp x →
      generic_format beta fexp (Rplus x (ulp beta fexp x))

def generic_format_pred_aux1Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), ∀ x,
    Rlt R0 x → generic_format beta fexp x →
      x ≠ bpow beta (Zsub (mag beta x : Z) Zone) →
      generic_format beta fexp (Rminus x (ulp beta fexp x))

def generic_format_pred_aux2Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x,
    Rlt R0 x → generic_format beta fexp x →
      let e := (mag beta x : Z)
      x = bpow beta (Zsub e Zone) →
      generic_format beta fexp (Rminus x (bpow beta (fexp (Zsub e Zone))))

def generic_format_pred_posStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x,
    generic_format beta fexp x → Rlt R0 x →
      generic_format beta fexp (pred_pos beta fexp x)

def generic_format_succStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x,
    generic_format beta fexp x → generic_format beta fexp (succ beta fexp x)

def id_m_ulp_ge_bpowStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), ∀ x e,
    generic_format beta fexp x → x ≠ ulp beta fexp x →
      Rlt (bpow beta e) x →
      Rle (bpow beta e) (Rminus x (ulp beta fexp x))

def id_p_ulp_le_bpowStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), ∀ x e,
    Rlt R0 x → generic_format beta fexp x →
      Rlt x (bpow beta e) →
      Rle (Rplus x (ulp beta fexp x)) (bpow beta e)

def le_pred_pos_ltStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x y,
    generic_format beta fexp x → generic_format beta fexp y →
      (Rle R0 x ∧ Rlt x y) → Rle x (pred_pos beta fexp y)

def mag_plus_epsStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), ∀ x,
    Rlt R0 x → generic_format beta fexp x →
      ∀ eps, (Rle R0 eps ∧ Rlt eps (ulp beta fexp x)) →
      (mag beta (Rplus x eps) : Z) = (mag beta x : Z)

def pred_eq_posStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), ∀ x,
    Rle R0 x → pred beta fexp x = pred_pos beta fexp x

def pred_lt_idStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), ∀ x,
    x ≠ R0 → Rlt (pred beta fexp x) x

def pred_le_idStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), ∀ x,
    Rle (pred beta fexp x) x

def pred_oppStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), ∀ x,
    pred beta fexp (Ropp x) = Ropp (succ beta fexp x)

def pred_pos_lt_idStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), ∀ x,
    x ≠ R0 → Rlt (pred_pos beta fexp x) x

def pred_pos_ge_0Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x,
    Rlt R0 x → generic_format beta fexp x →
      Rle R0 (pred_pos beta fexp x)

def pred_pos_plus_ulpStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x,
    Rlt R0 x → generic_format beta fexp x →
      Rplus (pred_pos beta fexp x) (ulp beta fexp (pred_pos beta fexp x)) = x

def pred_pos_plus_ulp_aux1Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), ∀ x,
    Rlt R0 x → generic_format beta fexp x →
      x ≠ bpow beta (Zsub (mag beta x : Z) Zone) →
      Rplus (Rminus x (ulp beta fexp x))
        (ulp beta fexp (Rminus x (ulp beta fexp x))) = x

def pred_pos_plus_ulp_aux2Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x,
    Rlt R0 x → generic_format beta fexp x →
      let e := (mag beta x : Z)
      x = bpow beta (Zsub e Zone) →
      Rminus x (bpow beta (fexp (Zsub e Zone))) ≠ R0 →
      Rplus (Rminus x (bpow beta (fexp (Zsub e Zone))))
        (ulp beta fexp (Rminus x (bpow beta (fexp (Zsub e Zone))))) = x

def pred_pos_plus_ulp_aux3Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x,
    Rlt R0 x → generic_format beta fexp x →
      let e := (mag beta x : Z)
      x = bpow beta (Zsub e Zone) →
      Rminus x (bpow beta (fexp (Zsub e Zone))) = R0 →
      ulp beta fexp R0 = x

def pred_succStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x,
    generic_format beta fexp x → pred beta fexp (succ beta fexp x) = x

def pred_succ_posStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x,
    generic_format beta fexp x → Rlt R0 x → pred beta fexp (succ beta fexp x) = x

def pred_ulp_0Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    pred beta fexp (ulp beta fexp R0) = R0

def pred_ge_0Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x,
    Rlt R0 x → generic_format beta fexp x → Rle R0 (pred beta fexp x)

def pred_ge_gtStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x y,
    generic_format beta fexp x → generic_format beta fexp y →
      Rlt x y → Rle x (pred beta fexp y)

def pred_leStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x y,
    generic_format beta fexp x → generic_format beta fexp y →
      Rle x y → Rle (pred beta fexp x) (pred beta fexp y)

def round_DN_plus_eps_posStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x,
    Rle R0 x → generic_format beta fexp x →
      ∀ eps, (Rle R0 eps ∧ Rlt eps (ulp beta fexp x)) →
      round beta fexp Zfloor (Rplus x eps) = x

def round_DN_minus_eps_posStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x,
    Rlt R0 x → generic_format beta fexp x →
      ∀ eps, (Rlt R0 eps ∧ Rle eps (ulp beta fexp (pred beta fexp x))) →
      round beta fexp Zfloor (Rminus x eps) = pred beta fexp x

def round_N_le_midpStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ (choice : Z → Bool) u v,
    generic_format beta fexp u →
      Rlt v (Rdiv (Rplus u (succ beta fexp u)) Rtwo) →
      Rle (round beta fexp (Znearest choice) v) u

def round_N_ge_midpStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ (choice : Z → Bool) u v,
    generic_format beta fexp u →
      Rlt (Rdiv (Rplus u (pred beta fexp u)) Rtwo) v →
      Rle u (round beta fexp (Znearest choice) v)

def round_N_eq_DNStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ (choice : Z → Bool) x,
    let d := round beta fexp Zfloor x
    let u := round beta fexp Zceil x
    Rlt x (Rdiv (Rplus d u) Rtwo) →
    round beta fexp (Znearest choice) x = d

def round_N_eq_DN_ptStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ (choice : Z → Bool) x d u,
    Rnd_DN_pt (generic_format beta fexp) x d →
      Rnd_UP_pt (generic_format beta fexp) x u →
      Rlt x (Rdiv (Rplus d u) Rtwo) →
      round beta fexp (Znearest choice) x = d

def round_N_eq_UPStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ (choice : Z → Bool) x,
    let d := round beta fexp Zfloor x
    let u := round beta fexp Zceil x
    Rlt (Rdiv (Rplus d u) Rtwo) x →
    round beta fexp (Znearest choice) x = u

def round_N_eq_UP_ptStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ (choice : Z → Bool) x d u,
    Rnd_DN_pt (generic_format beta fexp) x d →
      Rnd_UP_pt (generic_format beta fexp) x u →
      Rlt (Rdiv (Rplus d u) Rtwo) x →
      round beta fexp (Znearest choice) x = u

def round_UP_eqStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x u,
    generic_format beta fexp u →
      Rlt (pred beta fexp u) x ∧ Rle x u →
      round beta fexp Zceil x = u

def round_UP_le_DN_ltStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x y,
    generic_format beta fexp y →
      Rlt (round beta fexp Zfloor x) y →
      Rle (round beta fexp Zceil x) y

def round_DN_eqStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x d,
    generic_format beta fexp d →
      Rle d x ∧ Rlt x (succ beta fexp d) →
      round beta fexp Zfloor x = d

def round_DN_ge_UP_gtStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x y,
    generic_format beta fexp y →
      Rlt y (round beta fexp Zceil x) →
      Rle y (round beta fexp Zfloor x)

def pred_UP_le_DNStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x,
    Rle (pred beta fexp (round beta fexp Zceil x)) (round beta fexp Zfloor x)

def pred_UP_eq_DNStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x,
    ¬ generic_format beta fexp x →
      pred beta fexp (round beta fexp Zceil x) = round beta fexp Zfloor x

def succ_eq_posStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), ∀ x,
    Rle R0 x → succ beta fexp x = Rplus x (ulp beta fexp x)

def succ_gt_idStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), ∀ x,
    x ≠ R0 → Rlt x (succ beta fexp x)

def succ_ge_idStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), ∀ x,
    Rle x (succ beta fexp x)

def succ_le_lt_auxStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x y,
    generic_format beta fexp x → generic_format beta fexp y →
      Rle R0 x → Rlt x y → Rle (succ beta fexp x) y

def succ_le_ltStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x y,
    generic_format beta fexp x → generic_format beta fexp y →
      Rlt x y → Rle (succ beta fexp x) y

def succ_le_invStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x y,
    generic_format beta fexp x → generic_format beta fexp y →
      Rle (succ beta fexp x) (succ beta fexp y) → Rle x y

def succ_oppStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), ∀ x,
    succ beta fexp (Ropp x) = Ropp (pred beta fexp x)

def succ_predStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x,
    generic_format beta fexp x → succ beta fexp (pred beta fexp x) = x

def succ_pred_posStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x,
    generic_format beta fexp x → Rlt R0 x → succ beta fexp (pred beta fexp x) = x

def succ_0Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), succ beta fexp R0 = ulp beta fexp R0

def succ_DN_eq_UPStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x,
    ¬ generic_format beta fexp x →
      succ beta fexp (round beta fexp Zfloor x) = round beta fexp Zceil x

def round_neq_0_negligible_expStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    negligible_exp fexp = none →
      ∀ (rnd : R → Z), Valid_rnd rnd → ∀ x, x ≠ R0 →
        round beta fexp rnd x ≠ R0

def generic_format_predStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x,
    generic_format beta fexp x →
      generic_format beta fexp (pred beta fexp x)

def pred_0Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z),
    pred beta fexp R0 = Ropp (ulp beta fexp R0)

end ExactStatements

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

theorem Z_le_dec_aux : Z_le_dec_auxStatement := by
  intro x y
  cases CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.ZArith_dec.Z_le_dec x y with
  | left h => exact Or.inl h
  | right h => exact Or.inr h

theorem negligible_exp_spec : negligible_exp_specStatement := by
  intro fexp
  unfold negligible_exp
  cases h : CompCert4Lean.Flocq.Core.Raux.LPO_Z
      (fun z => Zle z (fexp z))
      (fun z =>
        match CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.ZArith_dec.Z_le_dec
            z (fexp z) with
        | .left h => Or.inl h
        | .right h => Or.inr h) with
  | inleft witness =>
      exact negligible_exp_prop.negligible_Some witness.val witness.property
  | inright hnone =>
      apply negligible_exp_prop.negligible_None
      intro n
      have hn := hnone n
      change ¬ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp n)) at hn
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp n) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n
      exact Int.lt_of_not_ge hn

theorem fexp_negligible_exp_eq : fexp_negligible_exp_eqStatement := by
  intro fexp hvalid n m hn hm
  by_cases hnm : Zle n m
  · have hnm' : Zle n (fexp m) := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp m)
      exact Int.le_trans hnm hm
    exact ((hvalid.valid_exp m).2 hm).2 n hnm'
  · have hlt : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n :=
      Int.lt_of_not_ge hnm
    have hmn : Zle m n := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n
      exact Int.le_of_lt hlt
    have hmn' : Zle m (fexp n) := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp n)
      exact Int.le_trans hmn hn
    exact (((hvalid.valid_exp n).2 hn).2 m hmn').symm

theorem ulp_neq_0 :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      ulp_neq_0Statement ctx magnitude := by
  intro ctx magnitude beta fexp x hx
  have hreq : Exact.Req_bool ctx x (Exact.R0 ctx) = false := by
    change (match CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx x
        (CompCert4Lean.Flocq.Core.Raux.Exact.R0 ctx) with
      | .Eq => true
      | _ => false) = false
    unfold CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare
    cases horder : CompCert4Lean.Foundation.FlocqReal.ExactReal.total_order_T
        ctx x (Exact.R0 ctx) with
    | inleft hleft =>
        cases hleft with
        | left hlt => rfl
        | right heq => exact (hx heq).elim
    | inright hgt => rfl
  unfold Exact.ulp
  rw [hreq]

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

theorem negligible_exp_spec' : negligible_exp_spec'Statement := by
  intro fexp
  unfold negligible_exp
  cases h : CompCert4Lean.Flocq.Core.Raux.LPO_Z
      (fun z => Zle z (fexp z))
      (fun z =>
        match CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.ZArith_dec.Z_le_dec
            z (fexp z) with
        | .left h => Or.inl h
        | .right h => Or.inr h) with
  | inleft witness =>
      exact Or.inr ⟨witness.val, rfl, witness.property⟩
  | inright hnone =>
      apply Or.inl
      constructor
      · rfl
      · intro n
        have hn := hnone n
        change ¬ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp n)) at hn
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp n) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n
        exact Int.lt_of_not_ge hn

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

open CompCert4Lean.Flocq.Core.Raux

private theorem ulp_exact_zero_lt_one_aux (ctx : ExactRealContext) :
    ctx.spec.lt ctx.spec.zero ctx.spec.one := by
  rcases ctx.certificate.total_order ctx.spec.zero ctx.spec.one with h | h
  · rcases h with hlt | heq
    · exact hlt
    · exact (ctx.certificate.orderedField.zero_ne_one heq).elim
  · have hzero_lt_neg : ctx.spec.lt ctx.spec.zero (ctx.spec.neg ctx.spec.one) := by
      have hadd := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.neg ctx.spec.one) ctx.spec.one ctx.spec.zero h
      rw [ctx.certificate.orderedField.neg_add_cancel,
        ctx.certificate.orderedField.add_zero] at hadd
      exact hadd
    have hneg_lt_zero := ctx.certificate.orderedField.mul_lt_compat_l
      (ctx.spec.neg ctx.spec.one) ctx.spec.one ctx.spec.zero hzero_lt_neg h
    rw [ctx.certificate.orderedField.mul_one,
      ctx.certificate.orderedField.mul_zero] at hneg_lt_zero
    exact (ctx.certificate.orderedField.lt_irrefl ctx.spec.zero
      (ctx.certificate.orderedField.lt_trans ctx.spec.zero (ctx.spec.neg ctx.spec.one)
        ctx.spec.zero hzero_lt_neg hneg_lt_zero)).elim

private theorem ulp_exact_IZR_ofNat_pos_aux (ctx : ExactRealContext) :
    ∀ n : Nat, ctx.spec.lt ctx.spec.zero
      (CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR ctx.spec
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (n + 1))) := by
  intro n
  induction n with
  | zero =>
      have honez :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1 =
            Zpos xH := by
        rfl
      have hone := ulp_exact_zero_lt_one_aux ctx
      change ctx.spec.lt ctx.spec.zero
        (ctx.spec.ofZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1))
      rw [honez, ctx.certificate.sourceLaws.ofZ_one]
      exact hone
  | succ n ih =>
      have hzn :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (n + 2) =
            Zadd (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (n + 1))
              (Zpos xH) := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add]
        repeat rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        have hone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos xH) = 1 := rfl
        rw [hone]
        change Int.ofNat (n + 2) = Int.ofNat (n + 1) + Int.ofNat 1
        calc
          Int.ofNat (n + 2) = Int.ofNat ((n + 1) + 1) := by congr 1 <;> omega
          _ = Int.ofNat (n + 1) + Int.ofNat 1 := Int.ofNat_add_ofNat _ _ |>.symm
      change ctx.spec.lt ctx.spec.zero
        (ctx.spec.ofZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (n + 2)))
      rw [hzn, ctx.certificate.sourceLaws.ofZ_add,
        ctx.certificate.sourceLaws.ofZ_one]
      have hone := ulp_exact_zero_lt_one_aux ctx
      have h := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.ofZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (n + 1)))
        ctx.spec.zero ctx.spec.one hone
      rw [ctx.certificate.orderedField.add_zero] at h
      exact ctx.certificate.orderedField.lt_trans _ _ _ ih h

private theorem ulp_exact_IZR_pos_aux (ctx : ExactRealContext) (z : Z)
    (hz : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ z) := by
  have hn : 0 < Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z) := by
    apply (Int.ofNat_lt).mp
    rw [Int.toNat_of_nonneg (Int.le_of_lt hz)]
    simpa using hz
  have hrepr :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z)) = z := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat]
    exact (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt _).trans
      (Int.toNat_of_nonneg (Int.le_of_lt hz))
  rw [← hrepr]
  have hstep : Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z) - 1 + 1 =
      Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z) := by
    omega
  rw [← hstep]
  exact ulp_exact_IZR_ofNat_pos_aux ctx
    (Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z) - 1)

private theorem ulp_radix_int_ge_two_aux (r : radix) : (2 : Int) ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val := by
  have hradix := r.radix_prop
  change (if
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.xO
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH)) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val then true else false) = true at hradix
  have : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.xO
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH)) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val := by
    simpa using hradix
  simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat] using this

private theorem ulp_exact_Zpower_pos_aux (ctx : ExactRealContext) (r : radix) (p : positive) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ (Zpower_pos r.radix_val p)) := by
  apply ulp_exact_IZR_pos_aux
  change 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (Int.pow (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)))
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  apply Int.pow_pos
  exact Int.lt_of_lt_of_le (by omega) (ulp_radix_int_ge_two_aux r)

private theorem ulp_exact_inv_pos_aux (ctx : ExactRealContext) {x : ctx.spec.carrier}
    (hx : ctx.spec.lt ctx.spec.zero x) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.inv x) := by
  have hxne : x ≠ ctx.spec.zero := by
    intro h
    rw [h] at hx
    exact ctx.certificate.orderedField.lt_irrefl ctx.spec.zero hx
  rcases ctx.certificate.total_order ctx.spec.zero (ctx.spec.inv x) with h | h
  · rcases h with hpos | hzero
    · exact hpos
    · have hinv : ctx.spec.mul (ctx.spec.inv x) x = ctx.spec.one :=
        ctx.certificate.orderedField.inv_mul_cancel x hxne
      rw [← hzero, ctx.certificate.orderedField.zero_mul] at hinv
      exact (ctx.certificate.orderedField.zero_ne_one hinv).elim
  · have hmul := ctx.certificate.orderedField.mul_lt_compat_l x
      (ctx.spec.inv x) ctx.spec.zero hx h
    rw [ctx.certificate.orderedField.mul_comm x (ctx.spec.inv x),
      ctx.certificate.orderedField.inv_mul_cancel x hxne,
      ctx.certificate.orderedField.mul_zero] at hmul
    have hone := ulp_exact_zero_lt_one_aux ctx
    exact (ctx.certificate.orderedField.lt_irrefl ctx.spec.zero
      (ctx.certificate.orderedField.lt_trans ctx.spec.zero ctx.spec.one
        ctx.spec.zero hone hmul)).elim

private theorem ulp_bpow_gt_0 (ctx : ExactRealContext) (r : radix) (e : Z) :
    Exact.Rlt ctx (Exact.R0 ctx) (Exact.bpow ctx r e) := by
  cases e with
  | Z0 =>
      change ctx.spec.lt ctx.spec.zero ctx.spec.one
      exact ulp_exact_zero_lt_one_aux ctx
  | Zpos p =>
      change ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ (Zpower_pos r.radix_val p))
      exact ulp_exact_Zpower_pos_aux ctx r p
  | Zneg p =>
      change ctx.spec.lt ctx.spec.zero (ctx.spec.inv (ctx.spec.ofZ (Zpower_pos r.radix_val p)))
      exact ulp_exact_inv_pos_aux ctx (ulp_exact_Zpower_pos_aux ctx r p)

private theorem ulp_bpow_ge_0 (ctx : ExactRealContext) (r : radix) (e : Z) :
    Exact.Rle ctx (Exact.R0 ctx) (Exact.bpow ctx r e) := by
  exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp
    (ulp_bpow_gt_0 ctx r e)).1

theorem ulp_ge_0 : ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
    ulp_ge_0Statement ctx magnitude := by
  intro ctx magnitude beta fexp x
  unfold Exact.ulp
  split
  · split
    · exact ulp_bpow_ge_0 ctx beta _
    · exact ctx.certificate.orderedField.le_refl ctx.spec.zero
  · exact ulp_bpow_ge_0 ctx beta _

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

open CompCert4Lean.Flocq.Core.Raux

private theorem ulp_exact_ofZ_lt_aux (ctx : ExactRealContext) {x y : Z}
    (hxy : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y) :
    ctx.spec.lt (ctx.spec.ofZ x) (ctx.spec.ofZ y) := by
  let d := Zsub y x
  have hsum : y = Zadd x d := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [d, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    omega
  have hd : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d := by
    simp only [d, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    omega
  have hdpos := ulp_exact_IZR_pos_aux ctx d hd
  rw [hsum, ctx.certificate.sourceLaws.ofZ_add]
  have hadd := ctx.certificate.orderedField.add_lt_compat_l
    (ctx.spec.ofZ x) ctx.spec.zero (ctx.spec.ofZ d) hdpos
  rw [ctx.certificate.orderedField.add_zero] at hadd
  exact hadd

private theorem ulp_exact_ofZ_le_aux (ctx : ExactRealContext) {x y : Z}
    (hxy : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y) :
    ctx.spec.le (ctx.spec.ofZ x) (ctx.spec.ofZ y) := by
  rcases Int.lt_or_eq_of_le hxy with h | h
  · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp
      (ulp_exact_ofZ_lt_aux ctx h)).1
  · have hxy' : x = y := CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective h
    subst y
    exact ctx.certificate.orderedField.le_refl _

private theorem ulp_Rmult_le_compat_r_aux (ctx : ExactRealContext)
    (r r1 r2 : ctx.spec.carrier) (hr : ctx.spec.le ctx.spec.zero r)
    (h12 : ctx.spec.le r1 r2) :
    ctx.spec.le (ctx.spec.mul r1 r) (ctx.spec.mul r2 r) := by
  rcases ctx.certificate.total_order ctx.spec.zero r with h | h
  · rcases h with hpos | hzero
    · rcases ctx.certificate.total_order r1 r2 with h' | h'
      · rcases h' with hlt | heq
        · rw [ctx.certificate.orderedField.mul_comm r1 r,
            ctx.certificate.orderedField.mul_comm r2 r]
          exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp
            (ctx.certificate.orderedField.mul_lt_compat_l r r1 r2 hpos hlt)).1
        · subst r2
          exact ctx.certificate.orderedField.le_refl _
      · exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp h').2 h12).elim
    · rw [← hzero, ctx.certificate.orderedField.mul_zero,
        ctx.certificate.orderedField.mul_zero]
      exact ctx.certificate.orderedField.le_refl _
  · exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp h).2 hr).elim

private theorem ulp_left_pos_of_mul_pos_aux (ctx : ExactRealContext)
    {a b : ctx.spec.carrier} (hb : ctx.spec.lt ctx.spec.zero b)
    (hab : ctx.spec.lt ctx.spec.zero (ctx.spec.mul a b)) :
    ctx.spec.lt ctx.spec.zero a := by
  rcases ctx.certificate.total_order ctx.spec.zero a with h | h
  · rcases h with hpos | hzero
    · exact hpos
    · rw [← hzero, ctx.certificate.orderedField.zero_mul] at hab
      exact (ctx.certificate.orderedField.lt_irrefl ctx.spec.zero hab).elim
  · have hmul := ctx.certificate.orderedField.mul_lt_compat_l b a ctx.spec.zero hb h
    rw [ctx.certificate.orderedField.mul_comm b a,
      ctx.certificate.orderedField.mul_zero] at hmul
    exact (ctx.certificate.orderedField.lt_irrefl ctx.spec.zero
      (ctx.certificate.orderedField.lt_trans ctx.spec.zero (ctx.spec.mul a b)
        ctx.spec.zero hab hmul)).elim

private theorem ulp_IZR_ge_one_of_pos_aux (ctx : ExactRealContext) (z : Z)
    (hz : ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ z)) :
    ctx.spec.le ctx.spec.one (ctx.spec.ofZ z) := by
  rcases ctx.certificate.total_order ctx.spec.one (ctx.spec.ofZ z) with h | h
  · rcases h with hlt | heq
    · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp hlt).1
    · rw [← heq]
      exact ctx.certificate.orderedField.le_refl _
  · have hint : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z < 1 := by
      apply Int.lt_of_not_ge
      intro hge
      have hge' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos xH) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z := by
        change (1 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z
        exact hge
      have hle := ulp_exact_ofZ_le_aux ctx (x := Zpos xH) (y := z) hge'
      rw [ctx.certificate.sourceLaws.ofZ_one] at hle
      exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp h).2 hle
    have hnonpos : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z ≤ 0 := by omega
    have hnonpos' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z ≤ 0
      exact hnonpos
    have hle := ulp_exact_ofZ_le_aux ctx (x := z) (y := Z0) hnonpos'
    rw [ctx.certificate.sourceLaws.ofZ_zero] at hle
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp hz).2 hle).elim

theorem ulp_le_id : ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
    ulp_le_idStatement ctx magnitude := by
  intro ctx magnitude beta fexp x hx hformat
  have hxne : x ≠ Exact.R0 ctx := by
    intro hzero
    rw [hzero] at hx
    exact (ctx.certificate.orderedField.lt_irrefl ctx.spec.zero hx).elim
  let e := Exact.cexp ctx magnitude beta fexp x
  let m := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx
    (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
      ctx magnitude beta fexp x)
  have hformat' : x = CompCert4Lean.Flocq.Core.Defs.Exact.F2R ctx
      (CompCert4Lean.Flocq.Core.Defs.Float beta m e) := by
    change x = CompCert4Lean.Flocq.Core.Defs.Exact.F2R ctx
      (CompCert4Lean.Flocq.Core.Defs.Float beta m e) at hformat
    exact hformat
  rw [ulp_neq_0 ctx magnitude beta fexp x hxne]
  change Exact.Rle ctx (Exact.bpow ctx beta e) x
  rw [hformat']
  change Exact.Rle ctx (Exact.bpow ctx beta e)
    (ctx.spec.mul (ctx.spec.ofZ m) (Exact.bpow ctx beta e))
  rw [hformat'] at hx
  change ctx.spec.lt ctx.spec.zero
    (ctx.spec.mul (ctx.spec.ofZ m) (Exact.bpow ctx beta e)) at hx
  have hmpos := ulp_left_pos_of_mul_pos_aux ctx
    (ulp_bpow_gt_0 ctx beta e) hx
  have hmone := ulp_IZR_ge_one_of_pos_aux ctx m hmpos
  have hmulone : ctx.spec.mul (ctx.spec.ofZ (Zpos xH))
      (Exact.bpow ctx beta e) = Exact.bpow ctx beta e := by
    rw [ctx.certificate.sourceLaws.ofZ_one, ctx.certificate.orderedField.one_mul]
  have hcomp : ctx.spec.le (ctx.spec.mul (ctx.spec.ofZ (Zpos xH))
      (Exact.bpow ctx beta e)) (ctx.spec.mul (ctx.spec.ofZ m)
      (Exact.bpow ctx beta e)) := by
    rw [ctx.certificate.sourceLaws.ofZ_one]
    exact ulp_Rmult_le_compat_r_aux ctx _ _ _
      (ulp_bpow_ge_0 ctx beta e) hmone
  rw [hmulone] at hcomp
  exact hcomp

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

private theorem ulp_succ_opp_neg_neg (ctx : ExactRealContext)
    (x : ctx.spec.carrier) : ctx.spec.neg (ctx.spec.neg x) = x := by
  calc
    ctx.spec.neg (ctx.spec.neg x) =
        ctx.spec.add (ctx.spec.neg (ctx.spec.neg x)) ctx.spec.zero :=
      (ctx.certificate.orderedField.add_zero _).symm
    _ = ctx.spec.add (ctx.spec.neg (ctx.spec.neg x))
        (ctx.spec.add (ctx.spec.neg x) x) := by
      rw [ctx.certificate.orderedField.neg_add_cancel]
    _ = ctx.spec.add
        (ctx.spec.add (ctx.spec.neg (ctx.spec.neg x)) (ctx.spec.neg x)) x := by
      rw [ctx.certificate.orderedField.add_assoc]
    _ = ctx.spec.add ctx.spec.zero x := by
      rw [ctx.certificate.orderedField.neg_add_cancel]
    _ = x := ctx.certificate.orderedField.zero_add _

theorem succ_opp :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      succ_oppStatement ctx magnitude := by
  intro ctx magnitude beta fexp x
  unfold Exact.pred
  exact (ulp_succ_opp_neg_neg ctx _).symm

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

theorem pred_opp :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      pred_oppStatement ctx magnitude := by
  intro ctx magnitude beta fexp x
  unfold Exact.pred
  exact congrArg ctx.spec.neg
    (congrArg (fun y => Exact.succ ctx magnitude beta fexp y)
      (ulp_succ_opp_neg_neg ctx x))

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

open CompCert4Lean.Flocq.Core.Raux

private theorem idp_int_pow_gt_one (a : Int) (ha : (2 : Int) ≤ a) :
    ∀ n : Nat, 0 < n → (1 : Int) < a ^ n := by
  intro n hn
  cases n with
  | zero => omega
  | succ n =>
      have hapos : 0 < a := by omega
      have hpow_one_all : ∀ k : Nat, (1 : Int) ≤ a ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
            rw [Int.pow_succ]
            have hmul := Int.mul_le_mul_of_nonneg_right ih (Int.le_of_lt hapos)
            have haone : (1 : Int) ≤ a := by omega
            have hmul' : (1 : Int) * a ≤ a ^ k * a := by
              simpa using hmul
            have hmul'' : a ≤ a ^ k * a := by
              simpa only [Int.one_mul] using hmul'
            exact Int.le_trans haone hmul''
      have hpow_one : (1 : Int) ≤ a ^ n := hpow_one_all n
      rw [Int.pow_succ]
      have hmul := Int.mul_le_mul_of_nonneg_right hpow_one (Int.le_of_lt hapos)
      have haone : (1 : Int) < a := by omega
      have hmul' : (1 : Int) * a ≤ a ^ n * a := by
        simpa using hmul
      have hmul'' : a ≤ a ^ n * a := by simpa using hmul'
      exact Int.lt_of_lt_of_le haone hmul''

private theorem idp_radix_int_ge_two (r : radix) :
    (2 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val := by
  have hr := r.radix_prop
  change (if (2 : Int) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val then true else false) = true at hr
  simpa using hr

private theorem idp_bpow_pos_gt_one (ctx : ExactRealContext) (r : radix)
    {e : Z} (he : Zlt Z0 e) :
    ctx.spec.lt ctx.spec.one (Exact.bpow ctx r e) := by
  cases e with
  | Z0 => change (0 : Int) < 0 at he; omega
  | Zneg p =>
      change (0 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zneg p) at he
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at he
      omega
  | Zpos p =>
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpow : (1 : Int) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zpower_pos r.radix_val p) := by
        simp only [Zpower_pos,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow_pos,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        exact idp_int_pow_gt_one _ (idp_radix_int_ge_two r) _ hp
      have h := ulp_exact_ofZ_lt_aux ctx
        (x := Zpos xH) (y := Zpower_pos r.radix_val p) (by
          change (1 : Int) <
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Zpower_pos r.radix_val p)
          exact hpow)
      change ctx.spec.lt (ctx.spec.ofZ (Zpos xH))
        (ctx.spec.ofZ (Zpower_pos r.radix_val p)) at h
      rw [ctx.certificate.sourceLaws.ofZ_one] at h
      exact h

private theorem idp_zadd_sub_cancel (a b : Z) :
    Zadd a (Zsub b a) = b := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

private theorem idp_bpow_lt (ctx : ExactRealContext) (r : radix)
    {e1 e2 : Z} (h : Zlt e1 e2) :
    Exact.Rlt ctx (Exact.bpow ctx r e1) (Exact.bpow ctx r e2) := by
  let d := Zsub e2 e1
  have hd : Zlt Z0 d := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d
    simp only [d,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 -
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 at h
    omega
  have hsum : Zadd e1 d = e2 := idp_zadd_sub_cancel e1 e2
  have hmul : Exact.bpow ctx r e2 =
      ctx.spec.mul (Exact.bpow ctx r e1) (Exact.bpow ctx r d) := by
    change CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e2 =
      ctx.spec.mul (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r d)
    rw [← hsum, CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx r e1 d]
    rfl
  have hpos : Exact.Rlt ctx (ctx.spec.zero) (Exact.bpow ctx r e1) :=
    Raux.bpow_gt_0 ctx r e1
  have hone : Exact.Rlt ctx (ctx.spec.one) (Exact.bpow ctx r d) :=
    idp_bpow_pos_gt_one ctx r hd
  have hpos' : Exact.Rlt ctx (Exact.IZR ctx Z0) (Exact.bpow ctx r e1) := by
    change ctx.spec.lt (ctx.spec.ofZ Z0) (Exact.bpow ctx r e1)
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hpos
  have hmul' :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_compat_r
      ctx (Exact.bpow ctx r e1) ctx.spec.one (Exact.bpow ctx r d) hpos' hone
  change ctx.spec.lt
    (ctx.spec.mul ctx.spec.one (Exact.bpow ctx r e1))
    (ctx.spec.mul (Exact.bpow ctx r d) (Exact.bpow ctx r e1)) at hmul'
  rw [ctx.certificate.orderedField.mul_comm ctx.spec.one _,
    ctx.certificate.orderedField.mul_one,
    ctx.certificate.orderedField.mul_comm _ (Exact.bpow ctx r e1)] at hmul'
  rw [← hmul] at hmul'
  exact hmul'

private theorem idp_bpow_le (ctx : ExactRealContext) (r : radix) {e1 e2 : Z}
    (h12 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2) :
    ctx.spec.le (Exact.bpow ctx r e1) (Exact.bpow ctx r e2) := by
  by_cases heq : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2
  · have hz : e1 = e2 :=
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective heq
    subst e2
    exact ctx.certificate.orderedField.le_refl _
  · have hlt : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 := by omega
    exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp
      (idp_bpow_lt ctx r hlt)).1

private theorem idp_F2R_p1_le_bpow_aux (ctx : ExactRealContext)
    (r : radix) (m e1 e2 : Z)
    (hm : (0 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m)
    (hlt : ctx.spec.lt
      (CompCert4Lean.Flocq.Core.Defs.Exact.F2R ctx
        (CompCert4Lean.Flocq.Core.Defs.Float r m e1))
      (Exact.bpow ctx r e2)) :
    ctx.spec.le
      (CompCert4Lean.Flocq.Core.Defs.Exact.F2R ctx
        (CompCert4Lean.Flocq.Core.Defs.Float r (Zadd m Zone) e1))
      (Exact.bpow ctx r e2) := by
  have hmle : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m := by
    change (1 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m
    omega
  have hbase := CompCert4Lean.Flocq.Core.Float_prop.F2R_le ctx r Zone m e1 hmle
  have hbase' : ctx.spec.le (Exact.bpow ctx r e1)
      (CompCert4Lean.Flocq.Core.Defs.Exact.F2R ctx
        (CompCert4Lean.Flocq.Core.Defs.Float r m e1)) := by
    change ctx.spec.le
      (ctx.spec.mul (ctx.spec.ofZ Zone)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1))
      (ctx.spec.mul (ctx.spec.ofZ m)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1)) at hbase
    rw [ctx.certificate.sourceLaws.ofZ_one,
      ctx.certificate.orderedField.one_mul] at hbase
    exact hbase
  have he : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 := by
    by_cases h12 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2
    · exact h12
    · have h21 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 := by omega
      have hpow := idp_bpow_lt ctx r h21
      have hpow' : ctx.spec.lt (Exact.bpow ctx r e2)
          (CompCert4Lean.Flocq.Core.Defs.Exact.F2R ctx
            (CompCert4Lean.Flocq.Core.Defs.Float r m e1)) := by
        apply (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
        constructor
        · exact ctx.certificate.orderedField.le_trans _ _ _
            ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hpow).1 hbase'
        · intro hback
          exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hpow).2
            (ctx.certificate.orderedField.le_trans _ _ _ hbase' hback)
      exact False.elim (ctx.certificate.orderedField.lt_irrefl _
        (ctx.certificate.orderedField.lt_trans _ _ _ hpow' hlt))
  let d := Zsub e2 e1
  have hd : Zle Z0 d := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d
    simp only [d, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change (0 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 -
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1
    omega
  have hsum : Zadd d e1 = e2 := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [d, Zadd, Zsub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    omega
  have hpow : ctx.spec.ofZ (Zpower r.radix_val d) =
      CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r d := by
    exact CompCert4Lean.Flocq.Core.Raux.IZR_Zpower ctx r d hd
  have hlt' : ctx.spec.lt
      (ctx.spec.mul (ctx.spec.ofZ m)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1))
      (ctx.spec.mul (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r d)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1)) := by
    change ctx.spec.lt
      (CompCert4Lean.Flocq.Core.Defs.Exact.F2R ctx
        (CompCert4Lean.Flocq.Core.Defs.Float r m e1))
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e2) at hlt
    rw [← hsum, CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx r d e1] at hlt
    change ctx.spec.lt
      (ctx.spec.mul (ctx.spec.ofZ m)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1))
      (ctx.spec.mul (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r d)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1)) at hlt
    change ctx.spec.lt
      (ctx.spec.mul (ctx.spec.ofZ m)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1))
      (ctx.spec.mul (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r d)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1))
    exact hlt
  have hcoef : ctx.spec.lt (ctx.spec.ofZ m)
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r d) := by
    have hbpos := CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx r e1
    have hbpos' : ctx.spec.lt (ctx.spec.ofZ Z0)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1) := by
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact hbpos
    exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_reg_r
      ctx (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1)
      (ctx.spec.ofZ m) (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r d)
      hbpos' hlt'
  have hcoefZ : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpower r.radix_val d) := by
    have hfloatlt : CompCert4Lean.Flocq.Core.Float_prop.Exact.Rlt ctx
        (CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
          (CompCert4Lean.Flocq.Core.Float_prop.Float r m e1))
        (CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
          (CompCert4Lean.Flocq.Core.Float_prop.Float r
            (Zpower r.radix_val d) e1)) := by
      change ctx.spec.lt
        (ctx.spec.mul (ctx.spec.ofZ m)
          (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1))
        (ctx.spec.mul (ctx.spec.ofZ (Zpower r.radix_val d))
          (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1))
      rw [hpow]
      exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_compat_r
        ctx (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1)
        (ctx.spec.ofZ m) (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r d)
        (by
          change ctx.spec.lt (ctx.spec.ofZ Z0)
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1)
          rw [ctx.certificate.sourceLaws.ofZ_zero]
          exact CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx r e1) hcoef
    exact CompCert4Lean.Flocq.Core.Float_prop.lt_F2R ctx r e1 m
      (Zpower r.radix_val d) hfloatlt
  have hcoefZ' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd m Zone) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpower r.radix_val d) := by
    simp only [Zadd,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m + 1 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpower r.radix_val d)
    omega
  have hfloat := CompCert4Lean.Flocq.Core.Float_prop.F2R_le ctx r
      (Zadd m Zone) (Zpower r.radix_val d) e1 hcoefZ'
  change ctx.spec.le
    (ctx.spec.mul (ctx.spec.ofZ (Zadd m Zone))
      (Exact.bpow ctx r e1))
    (ctx.spec.mul (ctx.spec.ofZ (Zpower r.radix_val d))
      (Exact.bpow ctx r e1)) at hfloat
  change ctx.spec.le
    (ctx.spec.mul (ctx.spec.ofZ (Zadd m Zone))
      (Exact.bpow ctx r e1)) (Exact.bpow ctx r e2)
  change ctx.spec.le
    (ctx.spec.mul (ctx.spec.ofZ (Zadd m Zone))
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1))
    (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e2)
  rw [← hsum, CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx r d e1,
    ← hpow]
  exact hfloat

theorem id_p_ulp_le_bpow :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      id_p_ulp_le_bpowStatement ctx magnitude := by
  intro ctx magnitude beta fexp x e hx hformat hxe
  let ce := Exact.cexp ctx magnitude beta fexp x
  let m := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx
    (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
      ctx magnitude beta fexp x)
  have hxne : x ≠ Exact.R0 ctx := by
    intro hzero
    rw [hzero] at hx
    exact (ctx.certificate.orderedField.lt_irrefl ctx.spec.zero hx).elim
  have hformat' : x = CompCert4Lean.Flocq.Core.Defs.Exact.F2R ctx
      (CompCert4Lean.Flocq.Core.Defs.Float beta m ce) := by
    change x = CompCert4Lean.Flocq.Core.Defs.Exact.F2R ctx
      (CompCert4Lean.Flocq.Core.Defs.Float beta m ce) at hformat
    exact hformat
  have hmreal : ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ m) := by
    rw [hformat'] at hx
    change ctx.spec.lt ctx.spec.zero
      (ctx.spec.mul (ctx.spec.ofZ m) (Exact.bpow ctx beta ce)) at hx
    have hbce : ctx.spec.lt ctx.spec.zero (Exact.bpow ctx beta ce) := by
      change ctx.spec.lt ctx.spec.zero
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta ce)
      exact CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta ce
    rcases ctx.certificate.total_order ctx.spec.zero (ctx.spec.ofZ m) with hm | hm
    · rcases hm with hmpos | hmzero
      · exact hmpos
      · rw [← hmzero, ctx.certificate.orderedField.zero_mul] at hx
        exact (ctx.certificate.orderedField.lt_irrefl _ hx).elim
    · have hmul := ctx.certificate.orderedField.mul_lt_compat_l
        (Exact.bpow ctx beta ce) (ctx.spec.ofZ m) ctx.spec.zero hbce hm
      rw [ctx.certificate.orderedField.mul_comm (Exact.bpow ctx beta ce),
        ctx.certificate.orderedField.mul_zero] at hmul
      exact (ctx.certificate.orderedField.lt_irrefl _
        (ctx.certificate.orderedField.lt_trans _ _ _ hx hmul)).elim
  have hmpos : (0 : Int) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m := by
    by_cases hm : (0 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m
    · exact hm
    · have hmle : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m ≤ 0 := by omega
      have hmle' : Zle m Z0 := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0
        simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] using hmle
      have hreal :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_le
          ctx m Z0 hmle'
      change ctx.spec.le (ctx.spec.ofZ m) (ctx.spec.ofZ Z0) at hreal
      rw [ctx.certificate.sourceLaws.ofZ_zero] at hreal
      exact False.elim
        ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hmreal |>.2 hreal)
  have hmain := idp_F2R_p1_le_bpow_aux ctx beta m ce e hmpos (by
    rw [← hformat']
    exact hxe)
  have hadd :
      CompCert4Lean.Flocq.Core.Defs.Exact.F2R ctx
        (CompCert4Lean.Flocq.Core.Defs.Float beta (Zadd m Zone) ce) =
      ctx.spec.add x (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta ce) := by
    rw [hformat']
    change ctx.spec.mul (ctx.spec.ofZ (Zadd m Zone))
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta ce) =
      ctx.spec.add
        (ctx.spec.mul (ctx.spec.ofZ m)
          (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta ce))
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta ce)
    rw [ctx.certificate.sourceLaws.ofZ_add,
      ctx.certificate.sourceLaws.ofZ_one,
      ctx.certificate.orderedField.mul_comm,
      ctx.certificate.orderedField.left_distrib,
      ctx.certificate.orderedField.mul_comm,
      ctx.certificate.orderedField.mul_comm,
      ctx.certificate.orderedField.mul_one]
  rw [CompCert4Lean.Flocq.Core.Ulp.ulp_neq_0 ctx magnitude beta fexp x hxne]
  change ctx.spec.le
    (ctx.spec.add x (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta ce))
    (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e)
  rw [← hadd]
  exact hmain

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

theorem pred_pos_lt_id :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      pred_pos_lt_idStatement ctx magnitude := by
  intro ctx magnitude beta fexp x hx
  unfold Exact.pred_pos
  split
  · rename_i hbranch
    change ctx.spec.lt
      (CompCert4Lean.Foundation.FlocqReal.ExactReal.Rminus ctx.spec x
        (Exact.bpow ctx beta (fexp (Zsub (Exact.mag ctx magnitude beta x) Zone)))) x
    change ctx.spec.lt
      (ctx.spec.add x (ctx.spec.neg
        (Exact.bpow ctx beta
          (fexp (Zsub (Exact.mag ctx magnitude beta x) Zone))))) x
    have hlt := ctx.certificate.orderedField.add_lt_compat_l
      (ctx.spec.neg (Exact.bpow ctx beta
        (fexp (Zsub (Exact.mag ctx magnitude beta x) Zone))))
      ctx.spec.zero
      (Exact.bpow ctx beta (fexp (Zsub (Exact.mag ctx magnitude beta x) Zone)))
      (ulp_bpow_gt_0 ctx beta _)
    rw [ctx.certificate.orderedField.neg_add_cancel,
      ctx.certificate.orderedField.add_zero] at hlt
    have hmain := ctx.certificate.orderedField.add_lt_compat_l x _ _ hlt
    rw [ctx.certificate.orderedField.add_zero] at hmain
    exact hmain
  · rename_i hbranch
    change ctx.spec.lt
      (CompCert4Lean.Foundation.FlocqReal.ExactReal.Rminus ctx.spec x
        (Exact.ulp ctx magnitude beta fexp x)) x
    change ctx.spec.lt
      (ctx.spec.add x (ctx.spec.neg (Exact.ulp ctx magnitude beta fexp x))) x
    have hxne : x ≠ Exact.R0 ctx := by
      intro hzero
      exact hx (by simpa [hzero])
    have hlt := ctx.certificate.orderedField.add_lt_compat_l
      (ctx.spec.neg (Exact.ulp ctx magnitude beta fexp x))
      ctx.spec.zero (Exact.ulp ctx magnitude beta fexp x)
      (by
        rw [ulp_neq_0 ctx magnitude beta fexp x hxne]
        exact CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta _)
    rw [ctx.certificate.orderedField.neg_add_cancel,
      ctx.certificate.orderedField.add_zero] at hlt
    have hmain := ctx.certificate.orderedField.add_lt_compat_l x _ _ hlt
    rw [ctx.certificate.orderedField.add_zero] at hmain
    exact hmain

private theorem ulp_neg_lt_neg (ctx : ExactRealContext) {x y : ctx.spec.carrier}
    (hxy : ctx.spec.lt x y) :
    ctx.spec.lt (ctx.spec.neg y) (ctx.spec.neg x) := by
  have h1 := ctx.certificate.orderedField.add_lt_compat_l
    (ctx.spec.neg x) x y hxy
  rw [ctx.certificate.orderedField.neg_add_cancel] at h1
  have h2 := ctx.certificate.orderedField.add_lt_compat_l
    (ctx.spec.neg y) ctx.spec.zero (ctx.spec.add (ctx.spec.neg x) y) h1
  rw [ctx.certificate.orderedField.add_zero] at h2
  have hxy' : ctx.spec.add (ctx.spec.neg y)
      (ctx.spec.add (ctx.spec.neg x) y) = ctx.spec.neg x := by
    calc
      ctx.spec.add (ctx.spec.neg y)
          (ctx.spec.add (ctx.spec.neg x) y) =
          ctx.spec.add (ctx.spec.add (ctx.spec.neg y) (ctx.spec.neg x)) y := by
            rw [ctx.certificate.orderedField.add_assoc]
      _ = ctx.spec.add (ctx.spec.add (ctx.spec.neg x) (ctx.spec.neg y)) y := by
            rw [ctx.certificate.orderedField.add_comm
              (ctx.spec.neg y) (ctx.spec.neg x)]
      _ = ctx.spec.add (ctx.spec.neg x)
          (ctx.spec.add (ctx.spec.neg y) y) := by
            rw [← ctx.certificate.orderedField.add_assoc]
      _ = ctx.spec.add (ctx.spec.neg x) ctx.spec.zero := by
            rw [ctx.certificate.orderedField.neg_add_cancel]
      _ = ctx.spec.neg x := ctx.certificate.orderedField.add_zero _
  rw [hxy'] at h2
  exact h2

private theorem ulp_neg_neg (ctx : ExactRealContext) (x : ctx.spec.carrier) :
    ctx.spec.neg (ctx.spec.neg x) = x := by
  calc
    ctx.spec.neg (ctx.spec.neg x) =
        ctx.spec.add (ctx.spec.neg (ctx.spec.neg x)) ctx.spec.zero :=
      (ctx.certificate.orderedField.add_zero _).symm
    _ = ctx.spec.add (ctx.spec.neg (ctx.spec.neg x))
        (ctx.spec.add (ctx.spec.neg x) x) := by
      rw [ctx.certificate.orderedField.neg_add_cancel]
    _ = ctx.spec.add
        (ctx.spec.add (ctx.spec.neg (ctx.spec.neg x)) (ctx.spec.neg x)) x := by
      rw [ctx.certificate.orderedField.add_assoc]
    _ = ctx.spec.add ctx.spec.zero x := by
      rw [ctx.certificate.orderedField.neg_add_cancel]
    _ = x := ctx.certificate.orderedField.zero_add _

theorem succ_gt_id :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      succ_gt_idStatement ctx magnitude := by
  intro ctx magnitude beta fexp x hx
  unfold Exact.succ
  split
  · rename_i hbranch
    change ctx.spec.lt x (ctx.spec.add x (Exact.ulp ctx magnitude beta fexp x))
    have hpos : ctx.spec.lt ctx.spec.zero
        (Exact.ulp ctx magnitude beta fexp x) := by
      rw [ulp_neq_0 ctx magnitude beta fexp x hx]
      exact CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta _
    have hlt := ctx.certificate.orderedField.add_lt_compat_l x
      ctx.spec.zero (Exact.ulp ctx magnitude beta fexp x) hpos
    rw [ctx.certificate.orderedField.add_zero] at hlt
    exact hlt
  · rename_i hbranch
    change ctx.spec.lt x
      (ctx.spec.neg (Exact.pred_pos ctx magnitude beta fexp (ctx.spec.neg x)))
    have hxneg : ctx.spec.neg x ≠ Exact.R0 ctx := by
      intro hzero
      apply hx
      have hneg0 : ctx.spec.neg (Exact.R0 ctx) = Exact.R0 ctx := by
        change ctx.spec.neg ctx.spec.zero = ctx.spec.zero
        have h := ctx.certificate.orderedField.neg_add_cancel ctx.spec.zero
        rw [ctx.certificate.orderedField.add_zero] at h
        exact h
      have h := congrArg ctx.spec.neg hzero
      rw [ulp_neg_neg ctx x, hneg0] at h
      exact h
    have hpred := pred_pos_lt_id ctx magnitude beta fexp (ctx.spec.neg x) hxneg
    have hneg := ulp_neg_lt_neg ctx hpred
    rw [ulp_neg_neg ctx x] at hneg
    exact hneg

theorem pred_lt_id :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      pred_lt_idStatement ctx magnitude := by
  intro ctx magnitude beta fexp x hx
  unfold Exact.pred
  have hxneg : ctx.spec.neg x ≠ Exact.R0 ctx := by
    intro hzero
    apply hx
    have hneg0 : ctx.spec.neg (Exact.R0 ctx) = Exact.R0 ctx := by
      change ctx.spec.neg ctx.spec.zero = ctx.spec.zero
      have h := ctx.certificate.orderedField.neg_add_cancel ctx.spec.zero
      rw [ctx.certificate.orderedField.add_zero] at h
      exact h
    have h := congrArg ctx.spec.neg hzero
    rw [ulp_neg_neg ctx x, hneg0] at h
    exact h
  have hsucc := succ_gt_id ctx magnitude beta fexp (ctx.spec.neg x) hxneg
  have hneg := ulp_neg_lt_neg ctx hsucc
  rw [ulp_neg_neg ctx x] at hneg
  exact hneg

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

private theorem ulp_neg_le_neg (ctx : ExactRealContext)
    {x y : ctx.spec.carrier} (hxy : ctx.spec.le x y) :
    ctx.spec.le (ctx.spec.neg y) (ctx.spec.neg x) := by
  rcases ctx.certificate.total_order x y with h | h
  · rcases h with hlt | heq
    · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp
        (ulp_neg_lt_neg ctx hlt)).1
    · subst y
      exact ctx.certificate.orderedField.le_refl _
  · exact False.elim
      ((ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp h).2 hxy)

theorem succ_ge_id :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      succ_ge_idStatement ctx magnitude := by
  intro ctx magnitude beta fexp x
  by_cases hx : x = Exact.R0 ctx
  · subst x
    unfold Exact.succ
    have hbool : Exact.Rle_bool ctx (Exact.R0 ctx) (Exact.R0 ctx) = true := by
      exact CompCert4Lean.Flocq.Core.Raux.Rle_bool_true ctx _ _
        (ctx.certificate.orderedField.le_refl _)
    simp only [hbool, ↓reduceIte]
    change ctx.spec.le ctx.spec.zero
      (ctx.spec.add ctx.spec.zero (Exact.ulp ctx magnitude beta fexp (Exact.R0 ctx)))
    rw [ctx.certificate.orderedField.zero_add]
    exact ulp_ge_0 ctx magnitude beta fexp (Exact.R0 ctx)
  · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp
      (succ_gt_id ctx magnitude beta fexp x hx)).1

theorem pred_le_id :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      pred_le_idStatement ctx magnitude := by
  intro ctx magnitude beta fexp x
  unfold Exact.pred
  have h := succ_ge_id ctx magnitude beta fexp (ctx.spec.neg x)
  have hneg := ulp_neg_le_neg ctx h
  rw [ulp_neg_neg ctx x] at hneg
  exact hneg

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

private theorem ulp_mag_unique (ctx : ExactRealContext) (r : radix)
    (x : Exact.R ctx) {e1 e2 : Z}
    (h1 : Exact.Rle ctx (Exact.bpow ctx r (Zsub e1 Zone)) (Exact.Rabs ctx x) ∧
      Exact.Rlt ctx (Exact.Rabs ctx x) (Exact.bpow ctx r e1))
    (h2 : Exact.Rle ctx (Exact.bpow ctx r (Zsub e2 Zone)) (Exact.Rabs ctx x) ∧
      Exact.Rlt ctx (Exact.Rabs ctx x) (Exact.bpow ctx r e2)) : e1 = e2 := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  by_cases heq : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2
  · exact heq
  · rcases Int.lt_or_gt_of_ne heq with h12 | h21
    · have hle : Zle e1 (Zsub e2 Zone) := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub e2 Zone)
        simp only [Zsub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 - 1
        omega
      have hp := idp_bpow_le ctx r hle
      have hmid := ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp
        (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
          ctx _ _ _ h2.1 h1.2)
      exact (hmid.2 hp).elim
    · have hle : Zle e2 (Zsub e1 Zone) := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub e1 Zone)
        simp only [Zsub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 - 1
        omega
      have hp := idp_bpow_le ctx r hle
      have hmid := ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp
        (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
          ctx _ _ _ h1.1 h2.2)
      exact (hmid.2 hp).elim

private theorem ulp_id_m_ulp_ge_bpow (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) (beta : radix) (fexp : Z → Z)
    (x : Exact.R ctx) (e : Z)
    (hformat : Exact.generic_format ctx magnitude beta fexp x)
    (hxulp : x ≠ Exact.ulp ctx magnitude beta fexp x)
    (hxpow : Exact.Rlt ctx (Exact.bpow ctx beta e) x) :
    Exact.Rle ctx (Exact.bpow ctx beta e)
      (Exact.Rminus ctx x (Exact.ulp ctx magnitude beta fexp x)) := by
  let m := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx
    (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
      ctx magnitude beta fexp x)
  let ce := Exact.cexp ctx magnitude beta fexp x
  have hxrepr : x = CompCert4Lean.Flocq.Core.Defs.Exact.F2R ctx
      (CompCert4Lean.Flocq.Core.Defs.Float beta m ce) := by
    change x = CompCert4Lean.Flocq.Core.Defs.Exact.F2R ctx
      (CompCert4Lean.Flocq.Core.Defs.Float beta m ce) at hformat
    exact hformat
  have hxrepr_fp : x = CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
      (CompCert4Lean.Flocq.Core.Float_prop.Float beta m ce) := by
    change x = CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
      (CompCert4Lean.Flocq.Core.Float_prop.Float beta m ce)
    exact hxrepr
  have hxne : x ≠ Exact.R0 ctx := by
    intro hx0
    have h := hxpow
    rw [hx0] at h
    have hb := CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta e
    exact (ctx.certificate.orderedField.lt_irrefl _
      (ctx.certificate.orderedField.lt_trans _ _ _ hb h)).elim
  have hulp := ulp_neq_0 ctx magnitude beta fexp x hxne
  have hmpos : Zlt Z0 m := by
    apply CompCert4Lean.Flocq.Core.Float_prop.gt_0_F2R ctx beta m ce
    have hb := CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta e
    have hxpow' : Exact.Rlt ctx (Exact.bpow ctx beta e)
        (CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
          (CompCert4Lean.Flocq.Core.Float_prop.Float beta m ce)) := by
      rw [← hxrepr_fp]
      exact hxpow
    exact ctx.certificate.orderedField.lt_trans _ _ _ hb hxpow'
  by_cases hmeq : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m = 1
  · have hmz : m = Zone := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m = 1
      exact hmeq
    have hx_eq : x = Exact.ulp ctx magnitude beta fexp x := by
      calc
        x = CompCert4Lean.Flocq.Core.Defs.Exact.F2R ctx
            (CompCert4Lean.Flocq.Core.Defs.Float beta m ce) := hxrepr
        _ = Exact.bpow ctx beta ce := by
          change ctx.spec.mul (ctx.spec.ofZ m) (Exact.bpow ctx beta ce) =
            Exact.bpow ctx beta ce
          rw [hmz, ctx.certificate.sourceLaws.ofZ_one,
            ctx.certificate.orderedField.one_mul]
        _ = Exact.ulp ctx magnitude beta fexp x := hulp.symm
    exact (hxulp hx_eq).elim
  · have hmgt : Zlt Zone m := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m
      change (1 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m
      have hmpos' : (0 : Int) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m := hmpos
      omega
    have hle := CompCert4Lean.Flocq.Core.Float_prop.bpow_le_F2R_m1 ctx
      beta m ce e hmgt (by
        rw [← hxrepr_fp]
        exact hxpow)
    rw [hulp]
    have hminus : Exact.Rminus ctx x (Exact.bpow ctx beta ce) =
        CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
          (CompCert4Lean.Flocq.Core.Float_prop.Float beta (Zsub m Zone) ce) := by
      rw [hxrepr]
      change ctx.spec.add
          (ctx.spec.mul (ctx.spec.ofZ m) (Exact.bpow ctx beta ce))
          (ctx.spec.neg (Exact.bpow ctx beta ce)) =
        ctx.spec.mul (ctx.spec.ofZ (Zsub m Zone)) (Exact.bpow ctx beta ce)
      have hzsub : CompCert4Lean.Flocq.Core.Zaux.Zadd m (Zopp Zone) = Zsub m Zone := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [CompCert4Lean.Flocq.Core.Zaux.Zadd, Zopp, Zsub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        omega
      have hofz : ctx.spec.ofZ (Zsub m Zone) =
          ctx.spec.add (ctx.spec.ofZ m) (ctx.spec.neg ctx.spec.one) := by
        rw [← hzsub, ctx.certificate.sourceLaws.ofZ_add,
          ctx.certificate.sourceLaws.ofZ_neg,
          ctx.certificate.sourceLaws.ofZ_one]
      have hnegmul : ctx.spec.mul (ctx.spec.neg ctx.spec.one)
          (Exact.bpow ctx beta ce) = ctx.spec.neg (Exact.bpow ctx beta ce) := by
        calc
          ctx.spec.mul (ctx.spec.neg ctx.spec.one)
              (Exact.bpow ctx beta ce) =
              ctx.spec.neg (ctx.spec.mul ctx.spec.one
                (Exact.bpow ctx beta ce)) := by
            exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_mult_distr_l_reverse
              ctx _ _
          _ = ctx.spec.neg (Exact.bpow ctx beta ce) := by
            exact congrArg ctx.spec.neg
              (ctx.certificate.orderedField.one_mul _)
      calc
        ctx.spec.add
            (ctx.spec.mul (ctx.spec.ofZ m) (Exact.bpow ctx beta ce))
            (ctx.spec.neg (Exact.bpow ctx beta ce)) =
            ctx.spec.add
              (ctx.spec.mul (ctx.spec.ofZ m) (Exact.bpow ctx beta ce))
              (ctx.spec.mul (ctx.spec.neg ctx.spec.one)
                (Exact.bpow ctx beta ce)) := by rw [hnegmul]
        _ = ctx.spec.add
              (ctx.spec.mul (Exact.bpow ctx beta ce) (ctx.spec.ofZ m))
              (ctx.spec.mul (Exact.bpow ctx beta ce)
                (ctx.spec.neg ctx.spec.one)) := by
          rw [ctx.certificate.orderedField.mul_comm
            (ctx.spec.ofZ m) (Exact.bpow ctx beta ce),
            ctx.certificate.orderedField.mul_comm
              (ctx.spec.neg ctx.spec.one) (Exact.bpow ctx beta ce)]
        _ = ctx.spec.mul (Exact.bpow ctx beta ce)
              (ctx.spec.add (ctx.spec.ofZ m) (ctx.spec.neg ctx.spec.one)) := by
          rw [ctx.certificate.orderedField.left_distrib]
        _ = ctx.spec.mul (Exact.bpow ctx beta ce)
              (ctx.spec.ofZ (Zsub m Zone)) := by rw [hofz]
        _ = ctx.spec.mul (ctx.spec.ofZ (Zsub m Zone))
              (Exact.bpow ctx beta ce) :=
          ctx.certificate.orderedField.mul_comm _ _
    rw [hminus]
    exact hle

theorem pred_pos_plus_ulp_aux1 :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      pred_pos_plus_ulp_aux1Statement ctx magnitude := by
  intro ctx magnitude beta fexp x hx hformat hxe
  let ex : Z := Exact.mag ctx magnitude beta x
  have hxne : x ≠ Exact.R0 ctx := by
    intro hx0
    rw [hx0] at hx
    exact (ctx.certificate.orderedField.lt_irrefl _ hx).elim
  have hmag := (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_bound hxne
  have habs : Exact.Rabs ctx x = x := by
    change ctx.spec.abs x = x
    exact ctx.certificate.sourceLaws.abs_nonnegative x
      ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hx).1
  have hmag' : Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone)) x ∧
      Exact.Rlt ctx x (Exact.bpow ctx beta ex) := by
    simpa only [ex, habs] using hmag
  have hstrict : Exact.Rlt ctx (Exact.bpow ctx beta (Zsub ex Zone)) x := by
    apply (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
    constructor
    · exact hmag'.1
    · intro hback
      have heq := ctx.certificate.orderedField.le_antisymm _ _ hback hmag'.1
      exact hxe heq
  have hce : Exact.cexp ctx magnitude beta fexp x = fexp ex := by
    exact CompCert4Lean.Flocq.Core.Generic_fmt.cexp_fexp_pos ctx magnitude
      beta fexp x ex hmag'
  have hxulp : x ≠ Exact.ulp ctx magnitude beta fexp x := by
    intro heq
    have hzero : x ≠ Exact.R0 ctx := hxne
    have hulp := ulp_neq_0 ctx magnitude beta fexp x hzero
    have hrepr : x = CompCert4Lean.Flocq.Core.Defs.Exact.F2R ctx
        (CompCert4Lean.Flocq.Core.Defs.Float beta
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx
            (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
              ctx magnitude beta fexp x))
          (Exact.cexp ctx magnitude beta fexp x)) := by
      change x = CompCert4Lean.Flocq.Core.Defs.Exact.F2R ctx
        (CompCert4Lean.Flocq.Core.Defs.Float beta
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx
            (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
              ctx magnitude beta fexp x))
          (Exact.cexp ctx magnitude beta fexp x)) at hformat
      exact hformat
    rw [hulp] at heq
    have hf2r : CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
          (CompCert4Lean.Flocq.Core.Float_prop.Float beta
            (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx
              (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
                ctx magnitude beta fexp x))
            (Exact.cexp ctx magnitude beta fexp x)) =
        CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
          (CompCert4Lean.Flocq.Core.Float_prop.Float beta Zone
            (Exact.cexp ctx magnitude beta fexp x)) := by
      calc
        CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
            (CompCert4Lean.Flocq.Core.Float_prop.Float beta
              (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx
                (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
                  ctx magnitude beta fexp x))
              (Exact.cexp ctx magnitude beta fexp x)) = x := by
                exact hrepr.symm
        _ = Exact.bpow ctx beta (Exact.cexp ctx magnitude beta fexp x) := heq
        _ = CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
              (CompCert4Lean.Flocq.Core.Float_prop.Float beta Zone
                (Exact.cexp ctx magnitude beta fexp x)) := by
          exact (CompCert4Lean.Flocq.Core.Float_prop.F2R_bpow ctx beta
            (Exact.cexp ctx magnitude beta fexp x)).symm
    have hmz := CompCert4Lean.Flocq.Core.Float_prop.eq_F2R ctx beta
      (Exact.cexp ctx magnitude beta fexp x)
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
          ctx magnitude beta fexp x)) Zone hf2r
    have hlowce : Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone))
        (Exact.bpow ctx beta (Exact.cexp ctx magnitude beta fexp x)) := by
      have h := hmag'.1
      rw [heq] at h
      exact h
    have huce : Exact.Rlt ctx (Exact.bpow ctx beta
        (Exact.cexp ctx magnitude beta fexp x)) (Exact.bpow ctx beta ex) := by
      have h := hmag'.2
      rw [heq] at h
      exact h
    have hce_ge : Zle (Zsub ex Zone)
        (Exact.cexp ctx magnitude beta fexp x) := by
      by_cases hge : Zle (Zsub ex Zone)
          (Exact.cexp ctx magnitude beta fexp x)
      · exact hge
      · have hlt : Zlt (Exact.cexp ctx magnitude beta fexp x) (Zsub ex Zone) := by
          change ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub ex Zone) ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Exact.cexp ctx magnitude beta fexp x) at hge
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Exact.cexp ctx magnitude beta fexp x) <
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub ex Zone)
          omega
        have hp := idp_bpow_lt ctx beta hlt
        have hcontra := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hp |>.2
        exact False.elim (hcontra hlowce)
    have hce_lt : Zlt (Exact.cexp ctx magnitude beta fexp x) ex := by
      by_cases hlt : Zlt (Exact.cexp ctx magnitude beta fexp x) ex
      · exact hlt
      · have hge : Zle ex (Exact.cexp ctx magnitude beta fexp x) := by
          change ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Exact.cexp ctx magnitude beta fexp x) <
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex at hlt
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Exact.cexp ctx magnitude beta fexp x)
          omega
        have hp := idp_bpow_le ctx beta hge
        exact False.elim ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
          huce |>.2 hp)
    have hce_eq : Exact.cexp ctx magnitude beta fexp x = Zsub ex Zone := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Exact.cexp ctx magnitude beta fexp x) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub ex Zone)
      have hge' := hce_ge
      have hlt' := hce_lt
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub ex Zone) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Exact.cexp ctx magnitude beta fexp x) at hge'
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Exact.cexp ctx magnitude beta fexp x) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex at hlt'
      simp only [Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hge' ⊢
      have hzone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = 1 := by
        rfl
      rw [hzone] at hge'
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Exact.cexp ctx magnitude beta fexp x) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex - 1
      omega
    apply hxe
    simpa [ex] using heq.trans (congrArg (Exact.bpow ctx beta) hce_eq)
  let y := Exact.Rminus ctx x (Exact.ulp ctx magnitude beta fexp x)
  have hylow : Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone)) y := by
    exact ulp_id_m_ulp_ge_bpow ctx magnitude beta fexp x (Zsub ex Zone)
      hformat hxulp hstrict
  have hyupper : Exact.Rlt ctx y (Exact.bpow ctx beta ex) := by
    have hyle : Exact.Rle ctx y x := by
      change Exact.Rle ctx (ctx.spec.add x
        (ctx.spec.neg (Exact.ulp ctx magnitude beta fexp x))) x
      have hu := ulp_ge_0 ctx magnitude beta fexp x
      have hneg0 : ctx.spec.neg ctx.spec.zero = ctx.spec.zero := by
        have h := ctx.certificate.orderedField.neg_add_cancel ctx.spec.zero
        rw [ctx.certificate.orderedField.add_zero] at h
        exact h
      have hneg := ulp_neg_le_neg ctx hu
      change ctx.spec.le (ctx.spec.neg (Exact.ulp ctx magnitude beta fexp x))
        (ctx.spec.neg ctx.spec.zero) at hneg
      rw [hneg0] at hneg
      have hplus := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_le_compat_l
        ctx x _ _ hneg
      change ctx.spec.le (ctx.spec.add x
          (ctx.spec.neg (Exact.ulp ctx magnitude beta fexp x)))
        (ctx.spec.add x ctx.spec.zero) at hplus
      rw [ctx.certificate.orderedField.add_zero] at hplus
      exact hplus
    apply (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
    constructor
    · exact ctx.certificate.orderedField.le_trans _ _ _ hyle
        ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hmag'.2).1
    · intro hback
      exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hmag'.2).2
        (ctx.certificate.orderedField.le_trans _ _ _ hback hyle)
  have hyne : y ≠ Exact.R0 ctx := by
    intro hy0
    have hsum : ctx.spec.add x
        (ctx.spec.neg (Exact.ulp ctx magnitude beta fexp x)) = ctx.spec.zero := by
      exact hy0
    have hsum' : CompCert4Lean.Foundation.FlocqReal.ExactReal.Rplus ctx.spec x
        (CompCert4Lean.Foundation.FlocqReal.ExactReal.Ropp ctx.spec
          (Exact.ulp ctx magnitude beta fexp x)) =
        CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR ctx.spec
          CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Z0 := by
      change ctx.spec.add x (ctx.spec.neg (Exact.ulp ctx magnitude beta fexp x)) =
        ctx.spec.ofZ CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Z0
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact hsum
    have hneg_eq := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_opp_r_uniq
      ctx x (ctx.spec.neg (Exact.ulp ctx magnitude beta fexp x)) hsum'
    have hxeq : x = Exact.ulp ctx magnitude beta fexp x := by
      have hh := congrArg ctx.spec.neg hneg_eq
      have hnn := ulp_neg_neg ctx (Exact.ulp ctx magnitude beta fexp x)
      have hnx := ulp_neg_neg ctx x
      change ctx.spec.neg (ctx.spec.neg (Exact.ulp ctx magnitude beta fexp x)) =
        ctx.spec.neg (ctx.spec.neg x) at hh
      rw [hnn, hnx] at hh
      exact hh.symm
    exact hxulp hxeq
  have habsy : Exact.Rabs ctx y = y := by
    change ctx.spec.abs y = y
    exact ctx.certificate.sourceLaws.abs_nonnegative y
      ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
        (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
          ctx _ _ _
          (CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta (Zsub ex Zone))
          hylow)).1
  have hylow_abs : Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone))
      (Exact.Rabs ctx y) := by simpa only [habsy] using hylow
  have hyupper_abs : Exact.Rlt ctx (Exact.Rabs ctx y)
      (Exact.bpow ctx beta ex) := by simpa only [habsy] using hyupper
  have hy_mag : (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta y).mag_val = ex := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    have hmy := (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta y).mag_bound hyne
    exact congrArg (fun z => CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z)
      (ulp_mag_unique ctx beta y
        hmy
        ⟨hylow_abs, hyupper_abs⟩)
  have hce_y : Exact.cexp ctx magnitude beta fexp y = fexp ex := by
    exact CompCert4Lean.Flocq.Core.Generic_fmt.cexp_fexp_pos ctx magnitude
      beta fexp y ex ⟨hylow, hyupper⟩
  have hulp_y : Exact.ulp ctx magnitude beta fexp y =
      Exact.ulp ctx magnitude beta fexp x := by
    rw [ulp_neq_0 ctx magnitude beta fexp y hyne,
      ulp_neq_0 ctx magnitude beta fexp x hxne, hce_y, hce]
  change Exact.Rplus ctx y (Exact.ulp ctx magnitude beta fexp y) = x
  rw [hulp_y]
  change Exact.Rplus ctx
      (Exact.Rminus ctx x (Exact.ulp ctx magnitude beta fexp x))
      (Exact.ulp ctx magnitude beta fexp x) = x
  change ctx.spec.add
      (ctx.spec.add x (ctx.spec.neg (Exact.ulp ctx magnitude beta fexp x)))
      (Exact.ulp ctx magnitude beta fexp x) = x
  rw [ctx.certificate.orderedField.add_assoc,
    ctx.certificate.orderedField.neg_add_cancel,
    ctx.certificate.orderedField.add_zero]

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

open CompCert4Lean.Flocq.Core.Raux

private theorem ulp_int_pow_gt_one (a : Int) (ha : (2 : Int) ≤ a) :
    ∀ n : Nat, 0 < n → (1 : Int) < a ^ n := by
  intro n hn
  cases n with
  | zero => omega
  | succ n =>
      have hapos : 0 < a := by omega
      have hpow_one_all : ∀ k : Nat, (1 : Int) ≤ a ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
            rw [Int.pow_succ]
            have hmul := Int.mul_le_mul_of_nonneg_right ih (Int.le_of_lt hapos)
            have haone : (1 : Int) ≤ a := by omega
            have hmul' : (1 : Int) * a ≤ a ^ k * a := by
              simpa using hmul
            have hmul'' : a ≤ a ^ k * a := by
              simpa only [Int.one_mul] using hmul'
            exact Int.le_trans haone hmul''
      have hpow_one : (1 : Int) ≤ a ^ n := hpow_one_all n
      rw [Int.pow_succ]
      have hmul := Int.mul_le_mul_of_nonneg_right hpow_one (Int.le_of_lt hapos)
      have haone : (1 : Int) < a := by omega
      have hmul' : (1 : Int) * a ≤ a ^ n * a := by simpa using hmul
      have hmul'' : a ≤ a ^ n * a := by simpa using hmul'
      exact Int.lt_of_lt_of_le haone hmul''

private theorem ulp_radix_int_ge_two (r : radix) :
    (2 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val := by
  have hr := r.radix_prop
  change (if (2 : Int) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val then true else false) = true at hr
  simpa using hr

private theorem ulp_bpow_pos_gt_one (ctx : ExactRealContext) (r : radix)
    {e : Z} (he : Zlt Z0 e) :
    Exact.Rlt ctx (ctx.spec.one) (Exact.bpow ctx r e) := by
  cases e with
  | Z0 => change (0 : Int) < 0 at he; omega
  | Zneg p =>
      change (0 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zneg p) at he
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at he
      omega
  | Zpos p =>
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpow : (1 : Int) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower_pos
              r.radix_val p) := by
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower_pos,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow_pos,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        exact ulp_int_pow_gt_one _ (ulp_radix_int_ge_two r) _ hp
      have hreal :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt ctx
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH)
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower_pos
            r.radix_val p)
          (by
            change (1 : Int) <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower_pos
                  r.radix_val p)
            exact hpow)
      change ctx.spec.lt (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH))
        (ctx.spec.ofZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower_pos
            r.radix_val p)) at hreal
      rw [ctx.certificate.sourceLaws.ofZ_one] at hreal
      exact hreal

private theorem ulp_zadd_sub_cancel (a b : Z) :
    CompCert4Lean.Flocq.Core.Zaux.Zadd a (Zsub b a) = b := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

private theorem ulp_bpow_lt (ctx : ExactRealContext) (r : radix)
    {e1 e2 : Z} (h : Zlt e1 e2) :
    Exact.Rlt ctx (Exact.bpow ctx r e1) (Exact.bpow ctx r e2) := by
  let d := Zsub e2 e1
  have hd : Zlt Z0 d := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d
    simp only [d,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 -
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 at h
    omega
  have hsum : CompCert4Lean.Flocq.Core.Zaux.Zadd e1 d = e2 :=
    ulp_zadd_sub_cancel e1 e2
  have hmul : Exact.bpow ctx r e2 =
      ctx.spec.mul (Exact.bpow ctx r e1) (Exact.bpow ctx r d) := by
    rw [← hsum]
    change CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r
        (CompCert4Lean.Flocq.Core.Raux.Zadd e1 d) =
      ctx.spec.mul (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r d)
    exact CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx r e1 d
  have hpos : Exact.Rlt ctx (ctx.spec.zero) (Exact.bpow ctx r e1) :=
    CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx r e1
  have hone : Exact.Rlt ctx (ctx.spec.one) (Exact.bpow ctx r d) :=
    ulp_bpow_pos_gt_one ctx r hd
  have hpos' : Exact.Rlt ctx (Exact.IZR ctx Z0) (Exact.bpow ctx r e1) := by
    change ctx.spec.lt (ctx.spec.ofZ Z0) (Exact.bpow ctx r e1)
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hpos
  have hmul' :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_compat_r
      ctx (Exact.bpow ctx r e1) (ctx.spec.one) (Exact.bpow ctx r d) hpos' hone
  change ctx.spec.lt
    (ctx.spec.mul ctx.spec.one (Exact.bpow ctx r e1))
    (ctx.spec.mul (Exact.bpow ctx r d) (Exact.bpow ctx r e1)) at hmul'
  rw [ctx.certificate.orderedField.mul_comm (ctx.spec.one) _,
    ctx.certificate.orderedField.mul_one,
    ctx.certificate.orderedField.mul_comm _ (Exact.bpow ctx r e1)] at hmul'
  rw [← hmul] at hmul'
  exact hmul'

private theorem ulp_bpow_inj (ctx : ExactRealContext) (r : radix)
    {e1 e2 : Z} (h : Exact.bpow ctx r e1 = Exact.bpow ctx r e2) : e1 = e2 := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  by_cases heq : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2
  · exact heq
  · rcases Int.lt_or_gt_of_ne heq with h12 | h21
    · have hp := ulp_bpow_lt ctx r (show Zlt e1 e2 by exact h12)
      rw [h] at hp
      exact (ctx.certificate.orderedField.lt_irrefl _ hp).elim
    · have hp := ulp_bpow_lt ctx r (show Zlt e2 e1 by exact h21)
      rw [h] at hp
      exact (ctx.certificate.orderedField.lt_irrefl _ hp).elim

theorem pred_pos_plus_ulp_aux3 :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      pred_pos_plus_ulp_aux3Statement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x hx hformat e hxe hzero
  have hsum : ctx.spec.add x
      (ctx.spec.neg (Exact.bpow ctx beta (fexp (Zsub e Zone)))) =
      ctx.spec.ofZ Z0 := by
    change Exact.Rminus ctx x (Exact.bpow ctx beta (fexp (Zsub e Zone))) =
      Exact.R0 ctx at hzero
    change ctx.spec.add x
      (ctx.spec.neg (Exact.bpow ctx beta (fexp (Zsub e Zone)))) =
      ctx.spec.ofZ Z0
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hzero
  have hneg_eq :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_opp_r_uniq
      ctx x (ctx.spec.neg (Exact.bpow ctx beta (fexp (Zsub e Zone)))) hsum
  have hxpow : x = Exact.bpow ctx beta (fexp (Zsub e Zone)) := by
    have hh := congrArg ctx.spec.neg hneg_eq
    have hnn := ulp_neg_neg ctx (Exact.bpow ctx beta (fexp (Zsub e Zone)))
    have hnx := ulp_neg_neg ctx x
    change ctx.spec.neg (ctx.spec.neg (Exact.bpow ctx beta (fexp (Zsub e Zone)))) =
      ctx.spec.neg (ctx.spec.neg x) at hh
    rw [hnn, hnx] at hh
    exact hh.symm
  have heq : fexp (Zsub e Zone) = Zsub e Zone := by
    apply ulp_bpow_inj ctx beta
    calc
      Exact.bpow ctx beta (fexp (Zsub e Zone)) = x := hxpow.symm
      _ = Exact.bpow ctx beta (Zsub e Zone) := hxe
  have hreq : Exact.Req_bool ctx (Exact.R0 ctx) (Exact.R0 ctx) = true :=
    CompCert4Lean.Flocq.Core.Raux.Req_bool_true ctx _ _ rfl
  unfold Exact.ulp
  rw [hreq]
  cases hspec : negligible_exp fexp with
  | none =>
      have hs := negligible_exp_spec fexp
      rw [hspec] at hs
      cases hs with
      | negligible_None hnone =>
          have hbad := hnone (Zsub e Zone)
          rw [heq] at hbad
          have hbad' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Zsub e Zone) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (Zsub e Zone) := hbad
          omega
  | some n =>
      have hs := negligible_exp_spec fexp
      rw [hspec] at hs
      cases hs with
      | negligible_Some n hn =>
          have hle : Zle (Zsub e Zone) (fexp (Zsub e Zone)) := by
            rw [heq]
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Zsub e Zone) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Zsub e Zone)
            omega
          have hfeq := fexp_negligible_exp_eq fexp hvalid n (Zsub e Zone) hn hle
          calc
            Exact.bpow ctx beta (fexp n) =
                Exact.bpow ctx beta (fexp (Zsub e Zone)) := congrArg
                  (fun z : Z => Exact.bpow ctx beta z) hfeq
            _ = x := hxpow.symm

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

theorem mag_plus_eps :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      mag_plus_epsStatement ctx magnitude := by
  intro ctx magnitude beta fexp x hx hformat eps heps
  have hx0 : x ≠ Exact.R0 ctx := by
    intro hzero
    subst x
    exact (ctx.certificate.orderedField.lt_irrefl _ hx).elim
  let ex : Z := Exact.mag ctx magnitude beta x
  have hmx := (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_bound hx0
  have habsx : Exact.Rabs ctx x = x := by
    change ctx.spec.abs x = x
    exact ctx.certificate.sourceLaws.abs_nonnegative x
      ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hx).1
  have hmx' : Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone)) x ∧
      Exact.Rlt ctx x (Exact.bpow ctx beta ex) := by
    simpa only [ex, habsx] using hmx
  have hsum_nonneg : Exact.Rle ctx (Exact.R0 ctx)
      (Exact.Rplus ctx x eps) := by
    change ctx.spec.le ctx.spec.zero (ctx.spec.add x eps)
    have h := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_le_compat
      ctx ctx.spec.zero x ctx.spec.zero eps
      ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hx).1 heps.1
    change ctx.spec.le (ctx.spec.add ctx.spec.zero ctx.spec.zero)
      (ctx.spec.add x eps) at h
    rw [ctx.certificate.orderedField.zero_add] at h
    exact h
  have habssum : Exact.Rabs ctx (Exact.Rplus ctx x eps) =
      Exact.Rplus ctx x eps := by
    change ctx.spec.abs (ctx.spec.add x eps) = ctx.spec.add x eps
    exact ctx.certificate.sourceLaws.abs_nonnegative _ hsum_nonneg
  have hupper : Exact.Rle ctx
      (Exact.Rplus ctx x (Exact.ulp ctx magnitude beta fexp x))
      (Exact.bpow ctx beta ex) := by
    exact id_p_ulp_le_bpow ctx magnitude beta fexp x ex hx hformat hmx'.2
  have hsum_bounds :
      Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone))
        (Exact.Rabs ctx (Exact.Rplus ctx x eps)) ∧
      Exact.Rlt ctx (Exact.Rabs ctx (Exact.Rplus ctx x eps))
        (Exact.bpow ctx beta ex) := by
    constructor
    · rw [habssum]
      have hle := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_le_compat
        ctx (Exact.bpow ctx beta (Zsub ex Zone)) x ctx.spec.zero eps
        hmx'.1 heps.1
      change ctx.spec.le
        (ctx.spec.add (Exact.bpow ctx beta (Zsub ex Zone)) ctx.spec.zero)
        (ctx.spec.add x eps) at hle
      rw [ctx.certificate.orderedField.add_zero] at hle
      exact hle
    · rw [habssum]
      have hlt : Exact.Rlt ctx (Exact.Rplus ctx x eps)
          (Exact.Rplus ctx x (Exact.ulp ctx magnitude beta fexp x)) :=
        ctx.certificate.orderedField.add_lt_compat_l x _ _ heps.2
      exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
        ctx _ _ _ hlt hupper
  have hle_sum : Exact.Rle ctx x (Exact.Rplus ctx x eps) := by
    have h := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_le_compat_l
      ctx x ctx.spec.zero eps heps.1
    change ctx.spec.le (ctx.spec.add x ctx.spec.zero)
      (ctx.spec.add x eps) at h
    rw [ctx.certificate.orderedField.add_zero] at h
    exact h
  have hsum_pos : Exact.Rlt ctx (Exact.R0 ctx)
      (Exact.Rplus ctx x eps) := by
    exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
      ctx _ _ _ hx hle_sum
  have hsum0 : Exact.Rplus ctx x eps ≠ Exact.R0 ctx := by
    intro hz
    rw [hz] at hsum_pos
    exact (ctx.certificate.orderedField.lt_irrefl _ hsum_pos).elim
  have hmag_sum :=
    (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta
      (Exact.Rplus ctx x eps)).mag_bound hsum0
  have heq := ulp_mag_unique ctx beta (Exact.Rplus ctx x eps)
      hsum_bounds hmag_sum
  exact heq.symm

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

private theorem pg_sllt_zadd_opp (z : Z) :
    CompCert4Lean.Flocq.Core.Raux.Zadd z (Zopp z) = Z0 := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Flocq.Core.Raux.Zadd, Zopp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z +
    -CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z = 0
  omega

private theorem pg_sllt_bpow_mul_inv (ctx : ExactRealContext)
    (beta : radix) (e : Z) :
    ctx.spec.mul (Exact.bpow ctx beta e)
      (Exact.bpow ctx beta (Zopp e)) = ctx.spec.one := by
  have hpow := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta e (Zopp e)
  change Exact.bpow ctx beta
      (CompCert4Lean.Flocq.Core.Raux.Zadd e (Zopp e)) =
    ctx.spec.mul (Exact.bpow ctx beta e)
      (Exact.bpow ctx beta (Zopp e)) at hpow
  rw [← hpow, pg_sllt_zadd_opp]
  rfl

private theorem pg_sllt_add_sub_cancel (ctx : ExactRealContext)
    (x y : Exact.R ctx) : ctx.spec.add x (Exact.Rminus ctx y x) = y := by
  change ctx.spec.add x (ctx.spec.add y (ctx.spec.neg x)) = y
  calc
    ctx.spec.add x (ctx.spec.add y (ctx.spec.neg x)) =
        ctx.spec.add (ctx.spec.add x y) (ctx.spec.neg x) := by
      rw [ctx.certificate.orderedField.add_assoc]
    _ = ctx.spec.add (ctx.spec.add y x) (ctx.spec.neg x) := by
      rw [ctx.certificate.orderedField.add_comm x y]
    _ = ctx.spec.add y (ctx.spec.add x (ctx.spec.neg x)) := by
      rw [← ctx.certificate.orderedField.add_assoc]
    _ = ctx.spec.add y ctx.spec.zero := by
      rw [ctx.certificate.orderedField.add_comm x (ctx.spec.neg x),
        ctx.certificate.orderedField.neg_add_cancel]
    _ = y := ctx.certificate.orderedField.add_zero y

private theorem pg_sllt_valid_rnd_DN (ctx : ExactRealContext) :
    CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Valid_rnd ctx
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx) := by
  constructor
  · exact CompCert4Lean.Flocq.Core.Raux.Zfloor_le ctx
  · exact CompCert4Lean.Flocq.Core.Raux.Zfloor_IZR ctx

private theorem pg_sllt_round_generic (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) (beta : radix) (fexp : Z → Z)
    (rnd : Exact.R ctx → Z)
    (hrnd : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Valid_rnd ctx rnd)
    (x : Exact.R ctx) (hx : Exact.generic_format ctx magnitude beta fexp x) :
    Exact.round ctx magnitude beta fexp rnd x = x := by
  unfold Exact.round CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
  rw [CompCert4Lean.Flocq.Core.Generic_fmt.scaled_mantissa_generic
    ctx magnitude beta fexp x hx, hrnd.Zrnd_IZR]
  exact hx.symm

private theorem pg_sllt_succ_eq_pos (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) (beta : radix) (fexp : Z → Z)
    (x : Exact.R ctx) (hx : Exact.Rle ctx (Exact.R0 ctx) x) :
    Exact.succ ctx magnitude beta fexp x =
      Exact.Rplus ctx x (Exact.ulp ctx magnitude beta fexp x) := by
  unfold Exact.succ
  have hb : Exact.Rle_bool ctx (Exact.R0 ctx) x = true :=
    CompCert4Lean.Flocq.Core.Raux.Rle_bool_true ctx _ _ hx
  simp only [hb, ↓reduceIte]

private theorem pg_sllt_round_DN_plus_eps_strict
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (x : Exact.R ctx)
    (hx : Exact.Rlt ctx (Exact.R0 ctx) x)
    (hformat : Exact.generic_format ctx magnitude beta fexp x)
    (eps : Exact.R ctx)
    (heps : Exact.Rle ctx (Exact.R0 ctx) eps ∧
      Exact.Rlt ctx eps (Exact.ulp ctx magnitude beta fexp x)) :
    Exact.round ctx magnitude beta fexp
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx)
      (Exact.Rplus ctx x eps) = x := by
  let ce : Z := Exact.cexp ctx magnitude beta fexp x
  let smx : Exact.R ctx :=
    CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
      ctx magnitude beta fexp x
  let smy : Exact.R ctx :=
    CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
      ctx magnitude beta fexp (Exact.Rplus ctx x eps)
  let n : Z := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx smx
  let p : Exact.R ctx := Exact.bpow ctx beta (Zopp ce)
  have hxne : x ≠ Exact.R0 ctx := by
    intro hzero
    rw [hzero] at hx
    exact (ctx.certificate.orderedField.lt_irrefl _ hx).elim
  have hmag := mag_plus_eps ctx magnitude beta fexp x hx hformat eps heps
  have hce : Exact.cexp ctx magnitude beta fexp
      (Exact.Rplus ctx x eps) = ce := by
    change fexp (Exact.mag ctx magnitude beta (Exact.Rplus ctx x eps)) =
      fexp (Exact.mag ctx magnitude beta x)
    exact congrArg fexp hmag
  have hp : Exact.Rlt ctx (Exact.R0 ctx) p :=
    CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta (Zopp ce)
  have hp' : Exact.Rlt ctx
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Z0) p := by
    change ctx.spec.lt (ctx.spec.ofZ Z0) p
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hp
  have hpge' : Exact.Rle ctx
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Z0) p := by
    change ctx.spec.le (ctx.spec.ofZ Z0) p
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hp |>.1
  have hsmx : smx =
      CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx n :=
    CompCert4Lean.Flocq.Core.Generic_fmt.scaled_mantissa_generic
      ctx magnitude beta fexp x hformat
  have hxe : Exact.Rle ctx x (Exact.Rplus ctx x eps) := by
    have h := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_le_compat_l
      ctx x (Exact.R0 ctx) eps heps.1
    change ctx.spec.le (ctx.spec.add x ctx.spec.zero) (ctx.spec.add x eps) at h
    rw [ctx.certificate.orderedField.add_zero] at h
    exact h
  have hlower : Exact.Rle ctx
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx n) smy := by
    change ctx.spec.le (ctx.spec.ofZ n) smy
    change smx = ctx.spec.ofZ n at hsmx
    rw [← hsmx]
    simp only [smx, smy, p,
      CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa, hce]
    exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
      ctx (Exact.bpow ctx beta (Zopp ce)) x (Exact.Rplus ctx x eps)
        hpge' hxe
  have hsumlt : Exact.Rlt ctx (Exact.Rplus ctx x eps)
      (Exact.Rplus ctx x (Exact.ulp ctx magnitude beta fexp x)) :=
    ctx.certificate.orderedField.add_lt_compat_l x _ _ heps.2
  have hmultlt : ctx.spec.lt
      (ctx.spec.mul (Exact.Rplus ctx x eps) p)
      (ctx.spec.mul (Exact.Rplus ctx x
        (Exact.ulp ctx magnitude beta fexp x)) p) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_compat_r
      ctx p _ _ hp' hsumlt
  have hulp : Exact.ulp ctx magnitude beta fexp x = Exact.bpow ctx beta ce := by
    simpa only [ce] using ulp_neq_0 ctx magnitude beta fexp x hxne
  have hupper : Exact.Rlt ctx smy
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx
        (CompCert4Lean.Flocq.Core.Raux.Zadd n Zone)) := by
    have hleft : smy = ctx.spec.mul (Exact.Rplus ctx x eps) p := by
      simp only [smy, p,
        CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa, hce]
      rfl
    have hright : ctx.spec.mul
        (Exact.Rplus ctx x (Exact.ulp ctx magnitude beta fexp x)) p =
        CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx
          (CompCert4Lean.Flocq.Core.Raux.Zadd n Zone) := by
      calc
        ctx.spec.mul
            (Exact.Rplus ctx x (Exact.ulp ctx magnitude beta fexp x)) p =
            ctx.spec.add (ctx.spec.mul x p)
          (ctx.spec.mul (Exact.ulp ctx magnitude beta fexp x) p) := by
          exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_plus_distr_r
            ctx x (Exact.ulp ctx magnitude beta fexp x) p
        _ = ctx.spec.add smx ctx.spec.one := by
          rw [hulp]
          change ctx.spec.add (ctx.spec.mul x p)
            (ctx.spec.mul (Exact.bpow ctx beta ce)
              (Exact.bpow ctx beta (Zopp ce))) = _
          rw [pg_sllt_bpow_mul_inv]
          rfl
        _ = ctx.spec.add
            (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx n)
            ctx.spec.one := by rw [hsmx]
        _ = CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx
            (CompCert4Lean.Flocq.Core.Raux.Zadd n Zone) := by
          change ctx.spec.add (ctx.spec.ofZ n) ctx.spec.one =
            ctx.spec.ofZ (CompCert4Lean.Flocq.Core.Raux.Zadd n Zone)
          rw [ctx.certificate.sourceLaws.ofZ_add,
            ctx.certificate.sourceLaws.ofZ_one]
    rw [hleft, ← hright]
    exact hmultlt
  have hfloor :
      CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx smy = n :=
    CompCert4Lean.Flocq.Core.Raux.Zfloor_imp ctx n smy ⟨hlower, hupper⟩
  unfold Exact.round CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
  change CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
      (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx smy)
        (Exact.cexp ctx magnitude beta fexp (Exact.Rplus ctx x eps))) = x
  rw [hce, hfloor]
  exact hformat.symm

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

private theorem pg_sllt_round_DN_zero_small
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (hvalid : Valid_exp fexp)
    (y : Exact.R ctx) (hy : Exact.Rlt ctx (Exact.R0 ctx) y)
    (hsmall : Exact.Rlt ctx y
      (Exact.ulp ctx magnitude beta fexp (Exact.R0 ctx))) :
    Exact.round ctx magnitude beta fexp
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx) y =
      Exact.R0 ctx := by
  have hreq : Exact.Req_bool ctx (Exact.R0 ctx) (Exact.R0 ctx) = true :=
    CompCert4Lean.Flocq.Core.Raux.Req_bool_true ctx _ _ rfl
  unfold Exact.ulp at hsmall
  rw [hreq] at hsmall
  cases hs : negligible_exp fexp with
  | none =>
      simp only [hs] at hsmall
      exact (ctx.certificate.orderedField.lt_irrefl _
        (ctx.certificate.orderedField.lt_trans _ _ _ hy hsmall)).elim
  | some k =>
      simp only [hs] at hsmall
      have hspec := negligible_exp_spec fexp
      rw [hs] at hspec
      cases hspec with
      | negligible_Some k hk =>
          let ey : Z := Exact.mag ctx magnitude beta y
          have hyne : y ≠ Exact.R0 ctx := by
            intro hzero
            rw [hzero] at hy
            exact (ctx.certificate.orderedField.lt_irrefl _ hy).elim
          have hmag :=
            (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta y).mag_bound hyne
          have habs : Exact.Rabs ctx y = y := by
            change ctx.spec.abs y = y
            exact ctx.certificate.sourceLaws.abs_nonnegative y
              ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hy).1
          have hmag' : Exact.Rle ctx (Exact.bpow ctx beta (Zsub ey Zone)) y ∧
              Exact.Rlt ctx y (Exact.bpow ctx beta ey) := by
            simpa only [ey, habs] using hmag
          have hpwlt : Exact.Rlt ctx (Exact.bpow ctx beta (Zsub ey Zone))
              (Exact.bpow ctx beta (fexp k)) :=
            CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
              ctx _ _ _ hmag'.1 hsmall
          have heylow : Zlt (Zsub ey Zone) (fexp k) := by
            by_cases hlt : Zlt (Zsub ey Zone) (fexp k)
            · exact hlt
            · have hle : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                  (fexp k) ≤
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                    (Zsub ey Zone) := by
                change ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                    (Zsub ey Zone) <
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp k) at hlt
                omega
              exact False.elim
                (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hpwlt).2
                  (idp_bpow_le ctx beta hle))
          have hey : Zle ey (fexp k) := by
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ey ≤
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp k)
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (Zsub ey Zone) <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp k) at heylow
            simp only [Zsub,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at heylow
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ey - 1 <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp k) at heylow
            omega
          have hfexp : fexp ey = fexp k := ((hvalid.valid_exp k).2 hk).2 ey hey
          let p : Exact.R ctx := Exact.bpow ctx beta (Zopp (fexp k))
          have hp : Exact.Rlt ctx (Exact.R0 ctx) p :=
            CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta _
          have hp' : Exact.Rlt ctx
              (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Z0) p := by
            change ctx.spec.lt (ctx.spec.ofZ Z0) p
            rw [ctx.certificate.sourceLaws.ofZ_zero]
            exact hp
          have hscaledlt : ctx.spec.lt (ctx.spec.mul y p) ctx.spec.one := by
            have hmul :=
              CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_compat_r
                ctx p y (Exact.bpow ctx beta (fexp k)) hp' hsmall
            dsimp [p] at hmul
            change ctx.spec.lt
              (ctx.spec.mul y (Exact.bpow ctx beta (Zopp (fexp k))))
              (ctx.spec.mul (Exact.bpow ctx beta (fexp k))
                (Exact.bpow ctx beta (Zopp (fexp k)))) at hmul
            rw [pg_sllt_bpow_mul_inv ctx beta (fexp k)] at hmul
            exact hmul
          have hyge' : Exact.Rle ctx
              (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Z0) y := by
            change ctx.spec.le (ctx.spec.ofZ Z0) y
            rw [ctx.certificate.sourceLaws.ofZ_zero]
            exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hy |>.1
          have hpge' : Exact.Rle ctx
              (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Z0) p := by
            change ctx.spec.le (ctx.spec.ofZ Z0) p
            rw [ctx.certificate.sourceLaws.ofZ_zero]
            exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hp |>.1
          have hscaledge' :=
            CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_pos
              ctx y p hyge' hpge'
          have hfloor :
              CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx
                (ctx.spec.mul y p) = Z0 := by
            apply CompCert4Lean.Flocq.Core.Raux.Zfloor_imp ctx Z0
              (ctx.spec.mul y p)
            constructor
            · exact hscaledge'
            · change ctx.spec.lt (ctx.spec.mul y p)
                (ctx.spec.ofZ
                  (CompCert4Lean.Flocq.Core.Raux.Zadd Z0 Zone))
              change ctx.spec.lt (ctx.spec.mul y p) (ctx.spec.ofZ Zone)
              rw [ctx.certificate.sourceLaws.ofZ_one]
              exact hscaledlt
          unfold Exact.round CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
          change ctx.spec.mul
              (ctx.spec.ofZ
                (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx
                  (ctx.spec.mul y
                    (Exact.bpow ctx beta
                      (Zopp (fexp (Exact.mag ctx magnitude beta y)))))))
              (Exact.bpow ctx beta (fexp (Exact.mag ctx magnitude beta y))) =
            ctx.spec.zero
          change fexp (Exact.mag ctx magnitude beta y) = fexp k at hfexp
          rw [hfexp]
          change ctx.spec.mul
              (ctx.spec.ofZ
                (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx
                  (ctx.spec.mul y p)))
              (Exact.bpow ctx beta (fexp k)) = ctx.spec.zero
          rw [hfloor, ctx.certificate.sourceLaws.ofZ_zero,
            ctx.certificate.orderedField.zero_mul]

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

private theorem pg_pred_ge_gt_succ_le_lt_aux :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      succ_le_lt_auxStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x y hxformat hyformat hxnonneg hxy
  have hypos : Exact.Rlt ctx (Exact.R0 ctx) y :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
      ctx _ _ _ hxnonneg hxy
  by_cases hxzero : x = Exact.R0 ctx
  · subst x
    have hsucc : Exact.succ ctx magnitude beta fexp (Exact.R0 ctx) =
        Exact.ulp ctx magnitude beta fexp (Exact.R0 ctx) := by
      rw [pg_sllt_succ_eq_pos ctx magnitude beta fexp (Exact.R0 ctx)
        (ctx.certificate.orderedField.le_refl _)]
      change ctx.spec.add ctx.spec.zero
        (Exact.ulp ctx magnitude beta fexp (Exact.R0 ctx)) = _
      exact ctx.certificate.orderedField.zero_add _
    rw [hsucc]
    rcases ctx.certificate.total_order
        (Exact.ulp ctx magnitude beta fexp (Exact.R0 ctx)) y with h | hsmall
    · rcases h with hlt | heq
      · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt |>.1
      · rw [heq]
        exact ctx.certificate.orderedField.le_refl _
    · have hround0 := pg_sllt_round_DN_zero_small ctx magnitude beta fexp
        hvalid y hypos hsmall
      have hroundy := pg_sllt_round_generic ctx magnitude beta fexp
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx)
        (pg_sllt_valid_rnd_DN ctx) y hyformat
      have hyzero : y = Exact.R0 ctx := hroundy.symm.trans hround0
      rw [hyzero] at hypos
      exact (ctx.certificate.orderedField.lt_irrefl _ hypos).elim
  · have hxpos : Exact.Rlt ctx (Exact.R0 ctx) x := by
      rcases ctx.certificate.total_order (Exact.R0 ctx) x with h | h
      · rcases h with hlt | heq
        · exact hlt
        · exact (hxzero heq.symm).elim
      · exact False.elim
          (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h).2 hxnonneg)
    rw [pg_sllt_succ_eq_pos ctx magnitude beta fexp x hxnonneg]
    let eps : Exact.R ctx := Exact.Rminus ctx y x
    have hepsnonneg : Exact.Rle ctx (Exact.R0 ctx) eps :=
      CompCert4Lean.Flocq.Core.Raux.Rle_0_minus ctx x y
        ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxy).1
    have hsum : Exact.Rplus ctx x eps = y := pg_sllt_add_sub_cancel ctx x y
    rcases ctx.certificate.total_order
        (Exact.ulp ctx magnitude beta fexp x) eps with h | hepslt
    · have hulp_le : Exact.Rle ctx (Exact.ulp ctx magnitude beta fexp x) eps := by
        rcases h with hlt | heq
        · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt |>.1
        · rw [heq]
          exact ctx.certificate.orderedField.le_refl _
      have hadd :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_le_compat_l
          ctx x _ _ hulp_le
      change ctx.spec.add x eps = y at hsum
      change ctx.spec.le
        (ctx.spec.add x (Exact.ulp ctx magnitude beta fexp x)) y
      rw [← hsum]
      exact hadd
    · have hroundx := pg_sllt_round_DN_plus_eps_strict
        ctx magnitude beta fexp x hxpos hxformat eps ⟨hepsnonneg, hepslt⟩
      rw [hsum] at hroundx
      have hroundy := pg_sllt_round_generic ctx magnitude beta fexp
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx)
        (pg_sllt_valid_rnd_DN ctx) y hyformat
      have hxeq : x = y := hroundx.symm.trans hroundy
      rw [hxeq] at hxy
      exact (ctx.certificate.orderedField.lt_irrefl _ hxy).elim

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

private theorem pg_sp_generic_format_bpow_inv
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (hvalid : Valid_exp fexp)
    (e : Z) (hformat : Exact.generic_format ctx magnitude beta fexp
      (Exact.bpow ctx beta e)) : Zle (fexp e) e := by
  let e1 : Z := CompCert4Lean.Flocq.Core.Raux.Zadd e Zone
  have hee1 : Zlt e e1 := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1
    simp only [e1, CompCert4Lean.Flocq.Core.Raux.Zadd,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e + 1
    omega
  have he1eq : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e + 1 := by
    simp only [e1, CompCert4Lean.Flocq.Core.Raux.Zadd,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    rfl
  have hstep : Zle (fexp e1) e := by
    by_cases hle : Zle (fexp e1) e
    · exact hle
    · have he1le : Zle e1 (fexp e1) := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp e1)
        change ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp e1) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e at hle
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 at hee1
        rw [he1eq]
        omega
      let v : Exact.R ctx := Exact.bpow ctx beta e
      let sm : Exact.R ctx :=
        CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
          ctx magnitude beta fexp v
      let m : Z := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx sm
      have hvpos : Exact.Rlt ctx (Exact.R0 ctx) v :=
        CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta e
      have hvabs : Exact.Rabs ctx v = v := by
        change ctx.spec.abs v = v
        exact ctx.certificate.sourceLaws.abs_nonnegative v
          ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hvpos).1
      have hbnext : Exact.Rlt ctx v (Exact.bpow ctx beta e1) :=
        idp_bpow_lt ctx beta hee1
      have hsmlt_abs :=
        CompCert4Lean.Flocq.Core.Generic_fmt.scaled_mantissa_lt_1
          ctx magnitude beta fexp hvalid v e1 (by simpa only [hvabs] using hbnext) he1le
      have hvpos' : Exact.Rlt ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Z0) v := by
        change ctx.spec.lt (ctx.spec.ofZ Z0) v
        rw [ctx.certificate.sourceLaws.ofZ_zero]
        exact hvpos
      have hfactor : Exact.Rlt ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Z0)
          (Exact.bpow ctx beta
            (Zopp (Exact.cexp ctx magnitude beta fexp v))) := by
        change ctx.spec.lt (ctx.spec.ofZ Z0) _
        rw [ctx.certificate.sourceLaws.ofZ_zero]
        exact CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta _
      have hsmpos : Exact.Rlt ctx (Exact.R0 ctx) sm := by
        have h :=
          CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_0_compat
            ctx v
              (Exact.bpow ctx beta
                (Zopp (Exact.cexp ctx magnitude beta fexp v)))
              hvpos' hfactor
        change ctx.spec.lt (ctx.spec.ofZ Z0) sm at h
        rw [ctx.certificate.sourceLaws.ofZ_zero] at h
        exact h
      have hsmabs : Exact.Rabs ctx sm = sm := by
        change ctx.spec.abs sm = sm
        exact ctx.certificate.sourceLaws.abs_nonnegative sm
          ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hsmpos).1
      have hsmlt : Exact.Rlt ctx sm
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone) := by
        simpa only [sm, hsmabs] using hsmlt_abs
      have hsmint : sm =
          CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx m :=
        CompCert4Lean.Flocq.Core.Generic_fmt.scaled_mantissa_generic
          ctx magnitude beta fexp v hformat
      change sm = ctx.spec.ofZ m at hsmint
      have hfloor0 :
          CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx
            (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx m) = Z0 := by
        apply CompCert4Lean.Flocq.Core.Raux.Zfloor_imp ctx Z0
        constructor
        · change ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.ofZ m)
          rw [ctx.certificate.sourceLaws.ofZ_zero, ← hsmint]
          exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hsmpos |>.1
        · change ctx.spec.lt (ctx.spec.ofZ m)
              (ctx.spec.ofZ
                (CompCert4Lean.Flocq.Core.Raux.Zadd Z0 Zone))
          rw [← hsmint]
          change ctx.spec.lt sm (ctx.spec.ofZ Zone)
          exact hsmlt
      have hmzero : m = Z0 := by
        calc
          m = CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx
              (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx m) :=
            (CompCert4Lean.Flocq.Core.Raux.Zfloor_IZR ctx m).symm
          _ = Z0 := hfloor0
      have hzero : sm = Exact.R0 ctx := by
        rw [hsmint, hmzero]
        exact ctx.certificate.sourceLaws.ofZ_zero
      rw [hzero] at hsmpos
      exact False.elim (ctx.certificate.orderedField.lt_irrefl _ hsmpos)
  have hstep' : Zlt (fexp e1) e1 := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp e1) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp e1) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e at hstep
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 at hee1
    omega
  have hmain := CompCert4Lean.Flocq.Core.Generic_fmt.valid_exp_large'
    fexp hvalid e1 e hstep'
    (by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1
      exact Int.le_of_lt hee1)
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp e) ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp e) <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 at hmain
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 at hee1
  rw [he1eq] at hmain
  omega

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

private theorem pg_sp_pred_pos_ge_zero
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (hvalid : Valid_exp fexp)
    (x : Exact.R ctx) (hx : Exact.Rlt ctx (Exact.R0 ctx) x)
    (hformat : Exact.generic_format ctx magnitude beta fexp x) :
    Exact.Rle ctx (Exact.R0 ctx)
      (Exact.pred_pos ctx magnitude beta fexp x) := by
  unfold Exact.pred_pos
  split
  · rename_i hbranch
    let e : Z := Zsub (Exact.mag ctx magnitude beta x) Zone
    have hspec := CompCert4Lean.Flocq.Core.Raux.Req_bool_spec ctx x
      (Exact.bpow ctx beta e)
    change CompCert4Lean.Flocq.Core.Raux.Exact.Req_bool ctx x
      (Exact.bpow ctx beta e) = true at hbranch
    rw [hbranch] at hspec
    cases hspec with
    | Req_bool_true_ heq =>
        have hbformat : Exact.generic_format ctx magnitude beta fexp
            (Exact.bpow ctx beta e) := by
          rw [← heq]
          exact hformat
        have hfe := pg_sp_generic_format_bpow_inv
          ctx magnitude beta fexp hvalid e hbformat
        have hpowle : Exact.Rle ctx (Exact.bpow ctx beta (fexp e))
            (Exact.bpow ctx beta e) := by
          apply idp_bpow_le ctx beta
          exact hfe
        have hpowle' : Exact.Rle ctx (Exact.bpow ctx beta (fexp e)) x := by
          rw [heq]
          exact hpowle
        apply CompCert4Lean.Flocq.Core.Raux.Rle_0_minus ctx
        exact hpowle'
  · apply CompCert4Lean.Flocq.Core.Raux.Rle_0_minus ctx
    exact ulp_le_id ctx magnitude beta fexp x hx hformat

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

private theorem pg_sp_sub_le_of_add_le (ctx : ExactRealContext)
    {a b c : Exact.R ctx} (h : Exact.Rle ctx (Exact.Rplus ctx a b) c) :
    Exact.Rle ctx a (Exact.Rminus ctx c b) := by
  have h' :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_le_compat_l
      ctx (ctx.spec.neg b) (ctx.spec.add a b) c h
  change ctx.spec.le
    (ctx.spec.add (ctx.spec.neg b) (ctx.spec.add a b))
    (ctx.spec.add (ctx.spec.neg b) c) at h'
  have hleft : ctx.spec.add (ctx.spec.neg b) (ctx.spec.add a b) = a := by
    calc
      ctx.spec.add (ctx.spec.neg b) (ctx.spec.add a b) =
          ctx.spec.add (ctx.spec.add (ctx.spec.neg b) a) b := by
        rw [ctx.certificate.orderedField.add_assoc]
      _ = ctx.spec.add (ctx.spec.add a (ctx.spec.neg b)) b := by
        rw [ctx.certificate.orderedField.add_comm (ctx.spec.neg b) a]
      _ = ctx.spec.add a (ctx.spec.add (ctx.spec.neg b) b) := by
        rw [← ctx.certificate.orderedField.add_assoc]
      _ = ctx.spec.add a ctx.spec.zero := by
        rw [ctx.certificate.orderedField.neg_add_cancel]
      _ = a := ctx.certificate.orderedField.add_zero a
  have hright : ctx.spec.add (ctx.spec.neg b) c =
      ctx.spec.add c (ctx.spec.neg b) :=
    ctx.certificate.orderedField.add_comm _ _
  rw [hleft, hright] at h'
  exact h'

private theorem pg_sp_double_bpow_le_next (ctx : ExactRealContext)
    (beta : radix) (e : Z) :
    Exact.Rle ctx
      (Exact.Rplus ctx (Exact.bpow ctx beta e) (Exact.bpow ctx beta e))
      (Exact.bpow ctx beta
        (CompCert4Lean.Flocq.Core.Raux.Zadd Zone e)) := by
  let ztwo : Z :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.xO
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH)
  have hradixZ : Zle ztwo beta.radix_val := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ztwo ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ beta.radix_val
    change (2 : Int) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ beta.radix_val
    exact ulp_radix_int_ge_two beta
  have hradix :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_le
      ctx ztwo beta.radix_val hradixZ
  have hpnonneg : Exact.Rle ctx
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Z0)
      (Exact.bpow ctx beta e) := by
    change ctx.spec.le (ctx.spec.ofZ Z0) (Exact.bpow ctx beta e)
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact ulp_bpow_ge_0 ctx beta e
  have hmul :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
      ctx (Exact.bpow ctx beta e)
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx ztwo)
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx beta.radix_val)
      hpnonneg hradix
  have htwo : ctx.spec.ofZ ztwo =
      ctx.spec.add ctx.spec.one ctx.spec.one := by
    have hz : CompCert4Lean.Flocq.Core.Raux.Zadd Zone Zone = ztwo := by
      rfl
    rw [← hz, ctx.certificate.sourceLaws.ofZ_add,
      ctx.certificate.sourceLaws.ofZ_one]
  have hb1 : Exact.bpow ctx beta Zone = ctx.spec.ofZ beta.radix_val := by
    change ctx.spec.ofZ
      (CompCert4Lean.Flocq.Core.Raux.Zpower_pos beta.radix_val
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH) =
      ctx.spec.ofZ beta.radix_val
    congr 1
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [CompCert4Lean.Flocq.Core.Raux.Zpower_pos,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow_pos,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat]
    exact Int.pow_one _
  have hpow := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta Zone e
  change Exact.bpow ctx beta
      (CompCert4Lean.Flocq.Core.Raux.Zadd Zone e) =
    ctx.spec.mul (Exact.bpow ctx beta Zone) (Exact.bpow ctx beta e) at hpow
  change ctx.spec.le
    (ctx.spec.mul (ctx.spec.ofZ ztwo) (Exact.bpow ctx beta e))
    (ctx.spec.mul (ctx.spec.ofZ beta.radix_val) (Exact.bpow ctx beta e)) at hmul
  have hdistr : ctx.spec.mul
      (ctx.spec.add ctx.spec.one ctx.spec.one) (Exact.bpow ctx beta e) =
      ctx.spec.add (Exact.bpow ctx beta e) (Exact.bpow ctx beta e) := by
    calc
      ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
          (Exact.bpow ctx beta e) =
          ctx.spec.add
            (ctx.spec.mul ctx.spec.one (Exact.bpow ctx beta e))
            (ctx.spec.mul ctx.spec.one (Exact.bpow ctx beta e)) := by
        exact
          CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_plus_distr_r
            ctx ctx.spec.one ctx.spec.one (Exact.bpow ctx beta e)
      _ = ctx.spec.add (Exact.bpow ctx beta e)
          (Exact.bpow ctx beta e) := by
        rw [ctx.certificate.orderedField.one_mul]
  rw [htwo, hdistr] at hmul
  rw [hpow, hb1]
  exact hmul

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

private theorem pg_sp_pred_pos_plus_ulp_aux2
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) :
    pred_pos_plus_ulp_aux2Statement ctx magnitude := by
  intro beta fexp hvalid x hx hformat e hxe hyne
  let em1 : Z := Zsub e Zone
  let em2 : Z := Zsub em1 Zone
  let fe : Z := fexp em1
  let y : Exact.R ctx := Exact.Rminus ctx x (Exact.bpow ctx beta fe)
  have hformatpow : Exact.generic_format ctx magnitude beta fexp
      (Exact.bpow ctx beta em1) := by
    rw [← hxe]
    exact hformat
  have hfele : Zle fe em1 :=
    pg_sp_generic_format_bpow_inv ctx magnitude beta fexp hvalid em1 hformatpow
  by_cases hfeeq : fe = em1
  · exfalso
    apply hyne
    change y = Exact.R0 ctx
    change ctx.spec.add x (ctx.spec.neg (Exact.bpow ctx beta fe)) = ctx.spec.zero
    rw [hxe, hfeeq]
    rw [ctx.certificate.orderedField.add_comm,
      ctx.certificate.orderedField.neg_add_cancel]
  · have hfelt : Zlt fe em1 := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ fe <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ em1
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ fe ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ em1 at hfele
      by_cases hlt : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ fe <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ em1
      · exact hlt
      · have heqint : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ fe =
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ em1 := by omega
        exact (hfeeq
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective heqint)).elim
    have hfele2 : Zle fe em2 := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ fe ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ em2
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ fe <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ em1 at hfelt
      simp only [em2, Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ fe ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ em1 - 1
      omega
    have hqle : Exact.Rle ctx (Exact.bpow ctx beta fe)
        (Exact.bpow ctx beta em2) := idp_bpow_le ctx beta hfele2
    have hnext : CompCert4Lean.Flocq.Core.Raux.Zadd Zone em2 = em1 := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp only [em2, CompCert4Lean.Flocq.Core.Raux.Zadd, Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      omega
    have hsum0 : Exact.Rle ctx
        (Exact.Rplus ctx (Exact.bpow ctx beta em2) (Exact.bpow ctx beta fe))
        (Exact.Rplus ctx (Exact.bpow ctx beta em2) (Exact.bpow ctx beta em2)) :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_le_compat_l
        ctx (Exact.bpow ctx beta em2) _ _ hqle
    have hdouble := pg_sp_double_bpow_le_next ctx beta em2
    rw [hnext] at hdouble
    have hsum : Exact.Rle ctx
        (Exact.Rplus ctx (Exact.bpow ctx beta em2) (Exact.bpow ctx beta fe))
        (Exact.bpow ctx beta em1) :=
      ctx.certificate.orderedField.le_trans _ _ _ hsum0 hdouble
    have hsumx : Exact.Rle ctx
        (Exact.Rplus ctx (Exact.bpow ctx beta em2) (Exact.bpow ctx beta fe)) x := by
      rw [hxe]
      exact hsum
    have hylow : Exact.Rle ctx (Exact.bpow ctx beta em2) y := by
      exact pg_sp_sub_le_of_add_le ctx hsumx
    have hqpos : Exact.Rlt ctx (Exact.R0 ctx) (Exact.bpow ctx beta fe) :=
      CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta fe
    have hyupperx : Exact.Rlt ctx y x := by
      change ctx.spec.lt (ctx.spec.add x (ctx.spec.neg (Exact.bpow ctx beta fe))) x
      have hnlt : ctx.spec.lt (ctx.spec.neg (Exact.bpow ctx beta fe))
          ctx.spec.zero := by
        have h := ulp_neg_lt_neg ctx hqpos
        have hnegzero : ctx.spec.neg ctx.spec.zero = ctx.spec.zero := by
          have hz := ctx.certificate.orderedField.neg_add_cancel ctx.spec.zero
          rw [ctx.certificate.orderedField.add_zero] at hz
          exact hz
        change ctx.spec.lt (ctx.spec.neg (Exact.bpow ctx beta fe))
          (ctx.spec.neg ctx.spec.zero) at h
        rw [hnegzero] at h
        exact h
      have h := ctx.certificate.orderedField.add_lt_compat_l x _ _ hnlt
      rw [ctx.certificate.orderedField.add_zero] at h
      exact h
    have hyupper : Exact.Rlt ctx y (Exact.bpow ctx beta em1) := by
      rw [← hxe]
      exact hyupperx
    have hypos : Exact.Rlt ctx (Exact.R0 ctx) y :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
        ctx _ _ _ (CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta em2) hylow
    have hyabs : Exact.Rabs ctx y = y := by
      change ctx.spec.abs y = y
      exact ctx.certificate.sourceLaws.abs_nonnegative y
        ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hypos).1
    have hybounds : Exact.Rle ctx
          (Exact.bpow ctx beta (Zsub em1 Zone)) (Exact.Rabs ctx y) ∧
        Exact.Rlt ctx (Exact.Rabs ctx y) (Exact.bpow ctx beta em1) := by
      simpa only [em2, hyabs] using And.intro hylow hyupper
    have hymag :=
      (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta y).mag_bound hyne
    have hm : Exact.mag ctx magnitude beta y = em1 :=
      ulp_mag_unique ctx beta y hymag hybounds
    have hulp : Exact.ulp ctx magnitude beta fexp y =
        Exact.bpow ctx beta fe := by
      rw [ulp_neq_0 ctx magnitude beta fexp y hyne]
      change Exact.bpow ctx beta
        (fexp (Exact.mag ctx magnitude beta y)) = Exact.bpow ctx beta fe
      rw [hm]
    change Exact.Rplus ctx y (Exact.ulp ctx magnitude beta fexp y) = x
    rw [hulp]
    change ctx.spec.add (ctx.spec.add x (ctx.spec.neg (Exact.bpow ctx beta fe)))
      (Exact.bpow ctx beta fe) = x
    rw [ctx.certificate.orderedField.add_assoc,
      ctx.certificate.orderedField.neg_add_cancel,
      ctx.certificate.orderedField.add_zero]

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

private theorem pg_sp_pred_pos_plus_ulp
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (hvalid : Valid_exp fexp)
    (x : Exact.R ctx) (hx : Exact.Rlt ctx (Exact.R0 ctx) x)
    (hformat : Exact.generic_format ctx magnitude beta fexp x) :
    Exact.Rplus ctx (Exact.pred_pos ctx magnitude beta fexp x)
      (Exact.ulp ctx magnitude beta fexp
        (Exact.pred_pos ctx magnitude beta fexp x)) = x := by
  unfold Exact.pred_pos
  split
  · rename_i hbranch
    let e : Z := Exact.mag ctx magnitude beta x
    have hspec := CompCert4Lean.Flocq.Core.Raux.Req_bool_spec ctx x
      (Exact.bpow ctx beta (Zsub e Zone))
    change CompCert4Lean.Flocq.Core.Raux.Exact.Req_bool ctx x
      (Exact.bpow ctx beta (Zsub e Zone)) = true at hbranch
    rw [hbranch] at hspec
    cases hspec with
    | Req_bool_true_ heq =>
        let y : Exact.R ctx :=
          Exact.Rminus ctx x (Exact.bpow ctx beta (fexp (Zsub e Zone)))
        by_cases hyzero : y = Exact.R0 ctx
        · have hzero := pred_pos_plus_ulp_aux3 ctx magnitude beta fexp hvalid
            x hx hformat heq hyzero
          change Exact.Rplus ctx y (Exact.ulp ctx magnitude beta fexp y) = x
          rw [hyzero]
          change ctx.spec.add ctx.spec.zero
            (Exact.ulp ctx magnitude beta fexp (Exact.R0 ctx)) = x
          rw [ctx.certificate.orderedField.zero_add]
          exact hzero
        · exact pg_sp_pred_pos_plus_ulp_aux2 ctx magnitude beta fexp hvalid
            x hx hformat heq hyzero
  · rename_i hbranch
    apply pred_pos_plus_ulp_aux1 ctx magnitude beta fexp x hx hformat
    intro heq
    apply hbranch
    exact CompCert4Lean.Flocq.Core.Raux.Req_bool_true ctx _ _ heq

private theorem pg_pred_ge_gt_succ_pred_pos :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      succ_pred_posStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x hformat hx
  have hplus := pg_sp_pred_pos_plus_ulp ctx magnitude beta fexp hvalid
    x hx hformat
  have hnonneg := pg_sp_pred_pos_ge_zero ctx magnitude beta fexp hvalid
    x hx hformat
  have hnegzero : ctx.spec.neg ctx.spec.zero = ctx.spec.zero := by
    have hz := ctx.certificate.orderedField.neg_add_cancel ctx.spec.zero
    rw [ctx.certificate.orderedField.add_zero] at hz
    exact hz
  have hxneg : Exact.Rlt ctx (Exact.Ropp ctx x) (Exact.R0 ctx) := by
    have h := ulp_neg_lt_neg ctx hx
    change ctx.spec.lt (ctx.spec.neg x) (ctx.spec.neg ctx.spec.zero) at h
    rw [hnegzero] at h
    exact h
  have hbfalse : Exact.Rle_bool ctx (Exact.R0 ctx) (Exact.Ropp ctx x) = false :=
    CompCert4Lean.Flocq.Core.Raux.Rle_bool_false ctx _ _ hxneg
  have hpred : Exact.pred ctx magnitude beta fexp x =
      Exact.pred_pos ctx magnitude beta fexp x := by
    unfold Exact.pred Exact.succ
    rw [hbfalse]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hnnx : Exact.Ropp ctx (Exact.Ropp ctx x) = x := ulp_neg_neg ctx x
    rw [hnnx]
    exact ulp_neg_neg ctx (Exact.pred_pos ctx magnitude beta fexp x)
  rw [hpred]
  rw [pg_sllt_succ_eq_pos ctx magnitude beta fexp
    (Exact.pred_pos ctx magnitude beta fexp x) hnonneg]
  exact hplus

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

private theorem pg_pred_ge_gt_generic_format_zero
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) :
    Exact.generic_format ctx magnitude beta fexp (Exact.R0 ctx) := by
  unfold Exact.generic_format
  change Exact.R0 ctx = CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
    (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
          ctx magnitude beta fexp (Exact.R0 ctx)))
      (Exact.cexp ctx magnitude beta fexp (Exact.R0 ctx)))
  have hzero : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R0 ctx =
      CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Z0 := by
    exact ctx.certificate.sourceLaws.ofZ_zero.symm
  rw [CompCert4Lean.Flocq.Core.Generic_fmt.scaled_mantissa_0
    ctx magnitude beta fexp]
  have htr : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx
      (Exact.R0 ctx) = Z0 := by
    calc
      CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx (Exact.R0 ctx) =
          CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx
            (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Z0) :=
        congrArg _ hzero
      _ = Z0 := CompCert4Lean.Flocq.Core.Raux.Ztrunc_IZR ctx Z0
  rw [htr]
  have hz : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
      (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta Z0
        (Exact.cexp ctx magnitude beta fexp (Exact.R0 ctx))) =
      CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R0 ctx := by
    exact CompCert4Lean.Flocq.Core.Float_prop.F2R_0 ctx beta _
  exact hz.symm

private theorem pg_pred_ge_gt_generic_format_F2R
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (m e : Z)
    (hce : m ≠ Z0 → Zle
      (Exact.cexp ctx magnitude beta fexp
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta m e))) e) :
    Exact.generic_format ctx magnitude beta fexp
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
        (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta m e)) := by
  by_cases hm : m = Z0
  · subst m
    have hz : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
        (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta Z0 e) = Exact.R0 ctx :=
      CompCert4Lean.Flocq.Core.Float_prop.F2R_0 ctx beta e
    rw [hz]
    exact pg_pred_ge_gt_generic_format_zero ctx magnitude beta fexp
  · let v : Exact.R ctx :=
      CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
        (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta m e)
    let e' : Z := Exact.cexp ctx magnitude beta fexp v
    let m' : Z := CompCert4Lean.Flocq.Core.Zaux.Zmul m
      (CompCert4Lean.Flocq.Core.Zaux.Zpower beta.radix_val (Zsub e e'))
    have hchange : v =
        CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta m' e') := by
      change CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
          (CompCert4Lean.Flocq.Core.Float_prop.Float beta m e) = _
      exact CompCert4Lean.Flocq.Core.Float_prop.F2R_change_exp ctx beta e' m e
        (hce hm)
    have hscaled :
        CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
          ctx magnitude beta fexp v =
        CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx m' := by
      unfold CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
      change ctx.spec.mul v (Exact.bpow ctx beta (Zopp e')) = ctx.spec.ofZ m'
      rw [hchange]
      change ctx.spec.mul
          (ctx.spec.mul (ctx.spec.ofZ m') (Exact.bpow ctx beta e'))
          (Exact.bpow ctx beta (Zopp e')) = ctx.spec.ofZ m'
      rw [ctx.certificate.orderedField.mul_assoc,
        pg_sllt_bpow_mul_inv, ctx.certificate.orderedField.mul_one]
    unfold Exact.generic_format
    change v = CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
      (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
            ctx magnitude beta fexp v)) e')
    rw [hscaled]
    have htr : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx m') = m' :=
      CompCert4Lean.Flocq.Core.Raux.Ztrunc_IZR ctx m'
    rw [htr]
    exact hchange

end CompCert4Lean.Flocq.Core.Ulp
namespace CompCert4Lean.Flocq.Core.Ulp

private theorem pg_pred_ge_gt_generic_pred_aux1
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (x : Exact.R ctx)
    (hx : Exact.Rlt ctx (Exact.R0 ctx) x)
    (hformat : Exact.generic_format ctx magnitude beta fexp x)
    (hbranch : x ≠ Exact.bpow ctx beta
      (Zsub (Exact.mag ctx magnitude beta x) Zone)) :
    Exact.generic_format ctx magnitude beta fexp
      (Exact.Rminus ctx x (Exact.ulp ctx magnitude beta fexp x)) := by
  let ce : Z := Exact.cexp ctx magnitude beta fexp x
  let n : Z := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx
    (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
      ctx magnitude beta fexp x)
  let y : Exact.R ctx := Exact.Rminus ctx x
    (Exact.ulp ctx magnitude beta fexp x)
  have hxne : x ≠ Exact.R0 ctx := by
    intro hzero
    rw [hzero] at hx
    exact (ctx.certificate.orderedField.lt_irrefl _ hx).elim
  by_cases hyzero : y = Exact.R0 ctx
  · rw [show Exact.Rminus ctx x
        (Exact.ulp ctx magnitude beta fexp x) = Exact.R0 ctx from hyzero]
    exact pg_pred_ge_gt_generic_format_zero ctx magnitude beta fexp
  · have hsum := pred_pos_plus_ulp_aux1 ctx magnitude beta fexp x hx
      hformat hbranch
    have hcancel : Exact.Rplus ctx y
        (Exact.ulp ctx magnitude beta fexp x) = x := by
      change ctx.spec.add
          (ctx.spec.add x
            (ctx.spec.neg (Exact.ulp ctx magnitude beta fexp x)))
          (Exact.ulp ctx magnitude beta fexp x) = x
      rw [ctx.certificate.orderedField.add_assoc,
        ctx.certificate.orderedField.neg_add_cancel,
        ctx.certificate.orderedField.add_zero]
    have hulp_eq : Exact.ulp ctx magnitude beta fexp y =
        Exact.ulp ctx magnitude beta fexp x := by
      apply CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_eq_reg_l
        ctx y
      exact hsum.trans hcancel.symm
    have hce_y : Exact.cexp ctx magnitude beta fexp y = ce := by
      rw [ulp_neq_0 ctx magnitude beta fexp y hyzero,
        ulp_neq_0 ctx magnitude beta fexp x hxne] at hulp_eq
      exact ulp_bpow_inj ctx beta hulp_eq
    have hxrepr : x =
        CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta n ce) := by
      exact hformat
    let nm1 : Z := Zsub n Zone
    have hzsub : CompCert4Lean.Flocq.Core.Zaux.Zadd n (Zopp Zone) = nm1 := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp only [nm1, CompCert4Lean.Flocq.Core.Zaux.Zadd, Zopp, Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      omega
    have hofz : ctx.spec.ofZ nm1 =
        ctx.spec.add (ctx.spec.ofZ n) (ctx.spec.neg ctx.spec.one) := by
      rw [← hzsub, ctx.certificate.sourceLaws.ofZ_add,
        ctx.certificate.sourceLaws.ofZ_neg,
        ctx.certificate.sourceLaws.ofZ_one]
    have hnegmul : ctx.spec.mul (ctx.spec.neg ctx.spec.one)
        (Exact.bpow ctx beta ce) =
        ctx.spec.neg (Exact.bpow ctx beta ce) := by
      exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_mult_distr_l_reverse
        ctx ctx.spec.one (Exact.bpow ctx beta ce) |>.trans
          (congrArg ctx.spec.neg
            (ctx.certificate.orderedField.one_mul _))
    have hulp_x : Exact.ulp ctx magnitude beta fexp x =
        Exact.bpow ctx beta ce := by
      simpa only [ce] using ulp_neq_0 ctx magnitude beta fexp x hxne
    have hyrepr : y =
        CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta nm1 ce) := by
      change ctx.spec.add x
          (ctx.spec.neg (Exact.ulp ctx magnitude beta fexp x)) =
        ctx.spec.mul (ctx.spec.ofZ nm1) (Exact.bpow ctx beta ce)
      rw [hulp_x, hxrepr]
      change ctx.spec.add
          (ctx.spec.mul (ctx.spec.ofZ n) (Exact.bpow ctx beta ce))
          (ctx.spec.neg (Exact.bpow ctx beta ce)) =
        ctx.spec.mul (ctx.spec.ofZ nm1) (Exact.bpow ctx beta ce)
      rw [hofz]
      calc
        ctx.spec.add
            (ctx.spec.mul (ctx.spec.ofZ n) (Exact.bpow ctx beta ce))
            (ctx.spec.neg (Exact.bpow ctx beta ce)) =
            ctx.spec.add
              (ctx.spec.mul (ctx.spec.ofZ n) (Exact.bpow ctx beta ce))
              (ctx.spec.mul (ctx.spec.neg ctx.spec.one)
                (Exact.bpow ctx beta ce)) := by rw [hnegmul]
        _ = ctx.spec.mul
              (ctx.spec.add (ctx.spec.ofZ n) (ctx.spec.neg ctx.spec.one))
              (Exact.bpow ctx beta ce) := by
          exact (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_plus_distr_r
            ctx _ _ _).symm
    rw [show Exact.Rminus ctx x
        (Exact.ulp ctx magnitude beta fexp x) = y from rfl, hyrepr]
    apply pg_pred_ge_gt_generic_format_F2R ctx magnitude beta fexp nm1 ce
    intro _
    rw [← hyrepr, hce_y]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ce ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ce
    omega

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

private theorem pg_pred_ge_gt_generic_pred_aux2
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (hvalid : Valid_exp fexp)
    (x : Exact.R ctx) (hx : Exact.Rlt ctx (Exact.R0 ctx) x)
    (hformat : Exact.generic_format ctx magnitude beta fexp x)
    (hxe : x = Exact.bpow ctx beta
      (Zsub (Exact.mag ctx magnitude beta x) Zone)) :
    Exact.generic_format ctx magnitude beta fexp
      (Exact.Rminus ctx x
        (Exact.bpow ctx beta
          (fexp (Zsub (Exact.mag ctx magnitude beta x) Zone)))) := by
  let em1 : Z := Zsub (Exact.mag ctx magnitude beta x) Zone
  let fe : Z := fexp em1
  let y : Exact.R ctx := Exact.Rminus ctx x (Exact.bpow ctx beta fe)
  by_cases hyzero : y = Exact.R0 ctx
  · rw [show Exact.Rminus ctx x
        (Exact.bpow ctx beta
          (fexp (Zsub (Exact.mag ctx magnitude beta x) Zone))) =
        Exact.R0 ctx from hyzero]
    exact pg_pred_ge_gt_generic_format_zero ctx magnitude beta fexp
  · have hsum := pg_sp_pred_pos_plus_ulp_aux2 ctx magnitude beta
      fexp hvalid x hx hformat hxe hyzero
    have hcancel : Exact.Rplus ctx y (Exact.bpow ctx beta fe) = x := by
      change ctx.spec.add
          (ctx.spec.add x (ctx.spec.neg (Exact.bpow ctx beta fe)))
          (Exact.bpow ctx beta fe) = x
      rw [ctx.certificate.orderedField.add_assoc,
        ctx.certificate.orderedField.neg_add_cancel,
        ctx.certificate.orderedField.add_zero]
    have hulp : Exact.ulp ctx magnitude beta fexp y =
        Exact.bpow ctx beta fe := by
      apply CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_eq_reg_l
        ctx y
      have hsum' : Exact.Rplus ctx y
          (Exact.ulp ctx magnitude beta fexp y) = x := by
        simpa [y, fe, em1] using hsum
      exact hsum'.trans hcancel.symm
    have hce_y : Exact.cexp ctx magnitude beta fexp y = fe := by
      rw [ulp_neq_0 ctx magnitude beta fexp y hyzero] at hulp
      exact ulp_bpow_inj ctx beta hulp
    have hformatpow : Exact.generic_format ctx magnitude beta fexp
        (Exact.bpow ctx beta em1) := by
      rw [← hxe]
      exact hformat
    have hfele : Zle fe em1 :=
      pg_sp_generic_format_bpow_inv ctx magnitude beta fexp hvalid
        em1 hformatpow
    let d : Z := Zsub em1 fe
    let q : Z := CompCert4Lean.Flocq.Core.Zaux.Zpower beta.radix_val d
    let qm1 : Z := Zsub q Zone
    have hd : Zle Z0 d := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ fe ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ em1 at hfele
      simp only [d, Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      change (0 : Int) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ em1 -
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ fe
      omega
    have hsumexp : CompCert4Lean.Flocq.Core.Zaux.Zadd d fe = em1 := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp only [d, CompCert4Lean.Flocq.Core.Zaux.Zadd, Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      omega
    have hq : ctx.spec.ofZ q = Exact.bpow ctx beta d := by
      exact CompCert4Lean.Flocq.Core.Raux.IZR_Zpower ctx beta d hd
    have hpow : Exact.bpow ctx beta em1 =
        ctx.spec.mul (Exact.bpow ctx beta d) (Exact.bpow ctx beta fe) := by
      have hp := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta d fe
      change Exact.bpow ctx beta
          (CompCert4Lean.Flocq.Core.Zaux.Zadd d fe) = _ at hp
      rw [hsumexp] at hp
      exact hp
    have hzsub : CompCert4Lean.Flocq.Core.Zaux.Zadd q (Zopp Zone) = qm1 := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp only [qm1, CompCert4Lean.Flocq.Core.Zaux.Zadd, Zopp, Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      omega
    have hofz : ctx.spec.ofZ qm1 =
        ctx.spec.add (ctx.spec.ofZ q) (ctx.spec.neg ctx.spec.one) := by
      rw [← hzsub, ctx.certificate.sourceLaws.ofZ_add,
        ctx.certificate.sourceLaws.ofZ_neg,
        ctx.certificate.sourceLaws.ofZ_one]
    have hnegmul : ctx.spec.mul (ctx.spec.neg ctx.spec.one)
        (Exact.bpow ctx beta fe) =
        ctx.spec.neg (Exact.bpow ctx beta fe) := by
      exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_mult_distr_l_reverse
        ctx ctx.spec.one (Exact.bpow ctx beta fe) |>.trans
          (congrArg ctx.spec.neg
            (ctx.certificate.orderedField.one_mul _))
    have hyrepr : y =
        CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta qm1 fe) := by
      change ctx.spec.add x (ctx.spec.neg (Exact.bpow ctx beta fe)) =
        ctx.spec.mul (ctx.spec.ofZ qm1) (Exact.bpow ctx beta fe)
      rw [hxe]
      change ctx.spec.add (Exact.bpow ctx beta em1)
          (ctx.spec.neg (Exact.bpow ctx beta fe)) =
        ctx.spec.mul (ctx.spec.ofZ qm1) (Exact.bpow ctx beta fe)
      rw [hpow, ← hq, hofz]
      calc
        ctx.spec.add
            (ctx.spec.mul (ctx.spec.ofZ q) (Exact.bpow ctx beta fe))
            (ctx.spec.neg (Exact.bpow ctx beta fe)) =
            ctx.spec.add
              (ctx.spec.mul (ctx.spec.ofZ q) (Exact.bpow ctx beta fe))
              (ctx.spec.mul (ctx.spec.neg ctx.spec.one)
                (Exact.bpow ctx beta fe)) := by rw [hnegmul]
        _ = ctx.spec.mul
              (ctx.spec.add (ctx.spec.ofZ q) (ctx.spec.neg ctx.spec.one))
              (Exact.bpow ctx beta fe) := by
          exact (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_plus_distr_r
            ctx _ _ _).symm
    rw [show Exact.Rminus ctx x
        (Exact.bpow ctx beta
          (fexp (Zsub (Exact.mag ctx magnitude beta x) Zone))) = y from rfl,
      hyrepr]
    apply pg_pred_ge_gt_generic_format_F2R ctx magnitude beta fexp qm1 fe
    intro _
    rw [← hyrepr, hce_y]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ fe ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ fe
    omega

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

private theorem pg_pred_ge_gt_generic_pred_pos
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (hvalid : Valid_exp fexp)
    (x : Exact.R ctx)
    (hformat : Exact.generic_format ctx magnitude beta fexp x)
    (hx : Exact.Rlt ctx (Exact.R0 ctx) x) :
    Exact.generic_format ctx magnitude beta fexp
      (Exact.pred_pos ctx magnitude beta fexp x) := by
  unfold Exact.pred_pos
  split
  · rename_i hbranch
    let e : Z := Exact.mag ctx magnitude beta x
    have hspec := CompCert4Lean.Flocq.Core.Raux.Req_bool_spec ctx x
      (Exact.bpow ctx beta (Zsub e Zone))
    change Exact.Req_bool ctx x
      (Exact.bpow ctx beta (Zsub e Zone)) = true at hbranch
    have hspec' : CompCert4Lean.Flocq.Core.Raux.Exact.Req_bool_prop ctx x
        (Exact.bpow ctx beta (Zsub e Zone)) true := by
      simpa only [hbranch] using hspec
    cases hspec' with
    | Req_bool_true_ heq =>
        exact pg_pred_ge_gt_generic_pred_aux2 ctx magnitude beta fexp
          hvalid x hx hformat heq
  · rename_i hbranch
    apply pg_pred_ge_gt_generic_pred_aux1 ctx magnitude beta fexp x hx hformat
    intro heq
    apply hbranch
    exact CompCert4Lean.Flocq.Core.Raux.Req_bool_true ctx _ _ heq

private theorem pg_pred_ge_gt_pred_eq_pos
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (x : Exact.R ctx)
    (hx : Exact.Rlt ctx (Exact.R0 ctx) x) :
    Exact.pred ctx magnitude beta fexp x =
      Exact.pred_pos ctx magnitude beta fexp x := by
  have hnegzero : ctx.spec.neg ctx.spec.zero = ctx.spec.zero := by
    have hz := ctx.certificate.orderedField.neg_add_cancel ctx.spec.zero
    rw [ctx.certificate.orderedField.add_zero] at hz
    exact hz
  have hxneg : Exact.Rlt ctx (Exact.Ropp ctx x) (Exact.R0 ctx) := by
    have h := ulp_neg_lt_neg ctx hx
    change ctx.spec.lt (ctx.spec.neg x) (ctx.spec.neg ctx.spec.zero) at h
    rw [hnegzero] at h
    exact h
  have hbfalse : Exact.Rle_bool ctx (Exact.R0 ctx) (Exact.Ropp ctx x) = false :=
    CompCert4Lean.Flocq.Core.Raux.Rle_bool_false ctx _ _ hxneg
  unfold Exact.pred Exact.succ
  rw [hbfalse]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change ctx.spec.neg (ctx.spec.neg
      (Exact.pred_pos ctx magnitude beta fexp
        (ctx.spec.neg (ctx.spec.neg x)))) =
    Exact.pred_pos ctx magnitude beta fexp x
  rw [ulp_neg_neg ctx x,
    ulp_neg_neg ctx (Exact.pred_pos ctx magnitude beta fexp x)]

theorem pred_ge_gt :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      pred_ge_gtStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x y hxformat hyformat hxy
  rcases ctx.certificate.total_order (Exact.R0 ctx) y with hyord | hyneg
  · rcases hyord with hypos | hyzero
    · have hpnonneg := pg_sp_pred_pos_ge_zero ctx magnitude beta fexp
        hvalid y hypos hyformat
      have hpred := pg_pred_ge_gt_pred_eq_pos ctx magnitude beta fexp y hypos
      rw [hpred]
      rcases ctx.certificate.total_order (Exact.R0 ctx) x with hxord | hxneg
      · rcases hxord with hxpos | hxzero
        · let p : Exact.R ctx := Exact.pred_pos ctx magnitude beta fexp y
          have hpformat : Exact.generic_format ctx magnitude beta fexp p :=
            pg_pred_ge_gt_generic_pred_pos ctx magnitude beta fexp hvalid
              y hyformat hypos
          have hsucc := pg_pred_ge_gt_succ_pred_pos ctx magnitude beta fexp
            hvalid y hyformat hypos
          rw [hpred] at hsucc
          change Exact.succ ctx magnitude beta fexp p = y at hsucc
          rcases ctx.certificate.total_order x p with hxp | hpx
          · rcases hxp with hlt | heq
            · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt |>.1
            · rw [heq]
              exact ctx.certificate.orderedField.le_refl _
          · have hsx := pg_pred_ge_gt_succ_le_lt_aux ctx magnitude beta fexp
                hvalid p x hpformat hxformat hpnonneg hpx
            rw [hsucc] at hsx
            exact False.elim
              ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxy |>.2 hsx)
        · subst x
          exact hpnonneg
      · have hxle : Exact.Rle ctx x (Exact.R0 ctx) :=
          (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxneg |>.1
        exact ctx.certificate.orderedField.le_trans _ _ _ hxle hpnonneg
    · subst y
      have hyformat0 := hyformat
      have hnyformat := CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_opp
        ctx magnitude beta fexp (Exact.R0 ctx) hyformat0
      have hnxformat := CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_opp
        ctx magnitude beta fexp x hxformat
      have hnegzero : ctx.spec.neg ctx.spec.zero = ctx.spec.zero := by
        have hz := ctx.certificate.orderedField.neg_add_cancel ctx.spec.zero
        rw [ctx.certificate.orderedField.add_zero] at hz
        exact hz
      have hnz : Exact.Ropp ctx (Exact.R0 ctx) = Exact.R0 ctx := hnegzero
      have hnyformat0 : Exact.generic_format ctx magnitude beta fexp (Exact.R0 ctx) := by
        simpa only [hnz] using hnyformat
      have hneglt := ulp_neg_lt_neg ctx hxy
      change ctx.spec.lt (ctx.spec.neg (ctx.spec.zero)) (ctx.spec.neg x) at hneglt
      rw [hnegzero] at hneglt
      have hs := pg_pred_ge_gt_succ_le_lt_aux ctx magnitude beta fexp hvalid
        (Exact.R0 ctx) (Exact.Ropp ctx x) hnyformat0 hnxformat
        (ctx.certificate.orderedField.le_refl _) hneglt
      have hn := ulp_neg_le_neg ctx hs
      change Exact.Rle ctx (Exact.Ropp ctx (Exact.Ropp ctx x))
        (Exact.Ropp ctx (Exact.succ ctx magnitude beta fexp (Exact.R0 ctx))) at hn
      change ctx.spec.le (ctx.spec.neg (ctx.spec.neg x))
        (ctx.spec.neg (Exact.succ ctx magnitude beta fexp (Exact.R0 ctx))) at hn
      rw [ulp_neg_neg ctx x] at hn
      unfold Exact.pred
      rw [hnz]
      exact hn
  · have hyformat' := CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_opp
      ctx magnitude beta fexp y hyformat
    have hxformat' := CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_opp
      ctx magnitude beta fexp x hxformat
    have hnegzero : ctx.spec.neg ctx.spec.zero = ctx.spec.zero := by
      have hz := ctx.certificate.orderedField.neg_add_cancel ctx.spec.zero
      rw [ctx.certificate.orderedField.add_zero] at hz
      exact hz
    have hynonneg : Exact.Rle ctx (Exact.R0 ctx) (Exact.Ropp ctx y) := by
      have h := ulp_neg_le_neg ctx
        ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hyneg |>.1)
      change ctx.spec.le (ctx.spec.neg ctx.spec.zero) (ctx.spec.neg y) at h
      rw [hnegzero] at h
      exact h
    have hneglt := ulp_neg_lt_neg ctx hxy
    have hs := pg_pred_ge_gt_succ_le_lt_aux ctx magnitude beta fexp hvalid
      (Exact.Ropp ctx y) (Exact.Ropp ctx x) hyformat' hxformat'
      hynonneg hneglt
    have hn := ulp_neg_le_neg ctx hs
    change Exact.Rle ctx (Exact.Ropp ctx (Exact.Ropp ctx x))
      (Exact.Ropp ctx
        (Exact.succ ctx magnitude beta fexp (Exact.Ropp ctx y))) at hn
    have hn' : Exact.Rle ctx x
        (Exact.Ropp ctx (Exact.succ ctx magnitude beta fexp (Exact.Ropp ctx y))) := by
      change ctx.spec.le (ctx.spec.neg (ctx.spec.neg x))
        (ctx.spec.neg (Exact.succ ctx magnitude beta fexp (Exact.Ropp ctx y))) at hn
      rw [ulp_neg_neg ctx x] at hn
      exact hn
    unfold Exact.pred
    exact hn'

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

theorem succ_pred_pos :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      succ_pred_posStatement ctx magnitude := by
  intro ctx magnitude
  exact pg_pred_ge_gt_succ_pred_pos ctx magnitude

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

theorem succ_0 :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      succ_0Statement ctx magnitude := by
  intro ctx magnitude beta fexp
  unfold Exact.succ
  have hbool : Exact.Rle_bool ctx (Exact.R0 ctx) (Exact.R0 ctx) = true := by
    exact CompCert4Lean.Flocq.Core.Raux.Rle_bool_true ctx _ _
      (ctx.certificate.orderedField.le_refl _)
  simp only [hbool, ↓reduceIte]
  change ctx.spec.add ctx.spec.zero
      (Exact.ulp ctx magnitude beta fexp (Exact.R0 ctx)) = _
  exact ctx.certificate.orderedField.zero_add _

theorem pred_0 :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      pred_0Statement ctx magnitude := by
  intro ctx magnitude beta fexp
  have hs := succ_0 ctx magnitude beta fexp
  unfold Exact.pred
  rw [show Exact.Ropp ctx (Exact.R0 ctx) = Exact.R0 ctx from by
    change ctx.spec.neg ctx.spec.zero = ctx.spec.zero
    have hz := ctx.certificate.orderedField.neg_add_cancel ctx.spec.zero
    rw [ctx.certificate.orderedField.add_zero] at hz
    exact hz]
  rw [hs]

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

private theorem pg_ulp_mag_bpow (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) (beta : radix) (e : Z) :
    Exact.mag ctx magnitude beta (Exact.bpow ctx beta e) =
      CompCert4Lean.Flocq.Core.Raux.Zadd e Zone := by
  have hpos := CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta e
  have hne : Exact.bpow ctx beta e ≠ Exact.R0 ctx := by
    intro hz
    change CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e =
      CompCert4Lean.Flocq.Core.Raux.Exact.R0 ctx at hz
    rw [hz] at hpos
    exact (ctx.certificate.orderedField.lt_irrefl _ hpos).elim
  have hmag :=
    (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta
      (Exact.bpow ctx beta e)).mag_bound hne
  have hsub : Zsub (CompCert4Lean.Flocq.Core.Raux.Zadd e Zone) Zone = e := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [Zsub, CompCert4Lean.Flocq.Core.Raux.Zadd,
      CompCert4Lean.Flocq.Core.Zaux.Zone,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e + 1 - 1 =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e
    omega
  have hnonneg : Exact.Rle ctx (Exact.R0 ctx) (Exact.bpow ctx beta e) :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hpos |>.1
  have habs : Exact.Rabs ctx (Exact.bpow ctx beta e) =
      Exact.bpow ctx beta e := by
    change ctx.spec.abs (Exact.bpow ctx beta e) = Exact.bpow ctx beta e
    exact ctx.certificate.sourceLaws.abs_nonnegative _ hnonneg
  have hbounds :
      Exact.Rle ctx (Exact.bpow ctx beta
        (Zsub (CompCert4Lean.Flocq.Core.Raux.Zadd e Zone) Zone))
          (Exact.Rabs ctx (Exact.bpow ctx beta e)) ∧
        Exact.Rlt ctx (Exact.Rabs ctx (Exact.bpow ctx beta e))
          (Exact.bpow ctx beta (CompCert4Lean.Flocq.Core.Raux.Zadd e Zone)) := by
    rw [hsub, habs]
    constructor
    · exact ctx.certificate.orderedField.le_refl _
    · apply ulp_bpow_lt
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Flocq.Core.Raux.Zadd e Zone)
      simp only [CompCert4Lean.Flocq.Core.Raux.Zadd,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e + 1 >
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e
      omega
  exact ulp_mag_unique ctx beta (Exact.bpow ctx beta e) hmag hbounds

theorem pred_ulp_0 :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      pred_ulp_0Statement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid
  have huge : Exact.Rle ctx (Exact.R0 ctx)
      (Exact.ulp ctx magnitude beta fexp (Exact.R0 ctx)) :=
    ulp_ge_0 ctx magnitude beta fexp (Exact.R0 ctx)
  by_cases huzero : Exact.ulp ctx magnitude beta fexp (Exact.R0 ctx) = Exact.R0 ctx
  · rw [huzero]
    have hp := pred_0 ctx magnitude beta fexp
    rw [hp]
    rw [huzero]
    change ctx.spec.neg ctx.spec.zero = ctx.spec.zero
    have hz := ctx.certificate.orderedField.neg_add_cancel ctx.spec.zero
    rw [ctx.certificate.orderedField.add_zero] at hz
    exact hz
  · have hupos : Exact.Rlt ctx (Exact.R0 ctx)
        (Exact.ulp ctx magnitude beta fexp (Exact.R0 ctx)) := by
      rcases ctx.certificate.total_order (Exact.R0 ctx)
          (Exact.ulp ctx magnitude beta fexp (Exact.R0 ctx)) with h | h
      · rcases h with hlt | heq
        · exact hlt
        · exact (huzero heq.symm).elim
      · exact False.elim
          (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h).2 huge)
    have hpred := pg_pred_ge_gt_pred_eq_pos ctx magnitude beta fexp
      (Exact.ulp ctx magnitude beta fexp (Exact.R0 ctx)) hupos
    rw [hpred]
    have hreq : Exact.Req_bool ctx (Exact.R0 ctx) (Exact.R0 ctx) = true :=
      CompCert4Lean.Flocq.Core.Raux.Req_bool_true ctx _ _ rfl
    have hspec := negligible_exp_spec' fexp
    rcases hspec with hnone | hsome
    · exfalso
      apply huzero
      unfold Exact.ulp
      rw [hreq, hnone.1]
    · rcases hsome with ⟨n, hnexp, hnle⟩
      have huval : Exact.ulp ctx magnitude beta fexp (Exact.R0 ctx) =
          Exact.bpow ctx beta (fexp n) := by
        unfold Exact.ulp
        rw [hreq, hnexp]
      rw [huval]
      unfold Exact.pred_pos
      have hmag := pg_ulp_mag_bpow ctx magnitude beta (fexp n)
      have hsub : Zsub (Exact.mag ctx magnitude beta
          (Exact.bpow ctx beta (fexp n))) Zone = fexp n := by
        rw [hmag]
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [Zsub, CompCert4Lean.Flocq.Core.Raux.Zadd,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        omega
      have heq : Exact.bpow ctx beta (fexp n) =
          Exact.bpow ctx beta (Zsub (Exact.mag ctx magnitude beta
            (Exact.bpow ctx beta (fexp n))) Zone) := by
        rw [hsub]
      have hbool : Exact.Req_bool ctx (Exact.bpow ctx beta (fexp n))
          (Exact.bpow ctx beta (Zsub (Exact.mag ctx magnitude beta
            (Exact.bpow ctx beta (fexp n))) Zone)) = true :=
        CompCert4Lean.Flocq.Core.Raux.Req_bool_true ctx _ _ heq
      simp only [hbool, ↓reduceIte]
      rw [hsub]
      have hrefl : Zle (fexp n) (fexp n) := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp n) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp n)
        omega
      have hfeq : fexp (fexp n) = fexp n :=
        ((hvalid.valid_exp n).2 hnle).2 (fexp n) hrefl
      rw [hfeq]
      change ctx.spec.add (Exact.bpow ctx beta (fexp n))
          (ctx.spec.neg (Exact.bpow ctx beta (fexp n))) = ctx.spec.zero
      rw [ctx.certificate.orderedField.add_comm,
        ctx.certificate.orderedField.neg_add_cancel]

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

private theorem pg_generic_format_succ_pos
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (hvalid : Valid_exp fexp)
    (x : Exact.R ctx) (hformat : Exact.generic_format ctx magnitude beta fexp x)
    (hx : Exact.Rlt ctx (Exact.R0 ctx) x) :
    Exact.generic_format ctx magnitude beta fexp
      (Exact.succ ctx magnitude beta fexp x) := by
  let ex : Z := Exact.mag ctx magnitude beta x
  let ce : Z := fexp ex
  let m : Z := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx
    (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
      ctx magnitude beta fexp x)
  have hxne : x ≠ Exact.R0 ctx := by
    intro hzero
    rw [hzero] at hx
    exact (ctx.certificate.orderedField.lt_irrefl _ hx).elim
  have hformat' : x =
      CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
        (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta m ce) := by
    change x = CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
      (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta m ce) at hformat
    exact hformat
  have hmagx :=
    (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_bound hxne
  have hxabs : Exact.Rabs ctx x = x := by
    change ctx.spec.abs x = x
    exact ctx.certificate.sourceLaws.abs_nonnegative _
      ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hx).1
  have hxupper : Exact.Rlt ctx x (Exact.bpow ctx beta ex) := by
    simpa only [hxabs, ex] using hmagx.2
  have hnonneg : Exact.Rle ctx (Exact.R0 ctx) x :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hx |>.1
  have hsuccpos : Exact.succ ctx magnitude beta fexp x =
      Exact.Rplus ctx x (Exact.ulp ctx magnitude beta fexp x) :=
    pg_sllt_succ_eq_pos ctx magnitude beta fexp x hnonneg
  have hulp : Exact.ulp ctx magnitude beta fexp x = Exact.bpow ctx beta ce := by
    have hu := ulp_neq_0 ctx magnitude beta fexp x hxne
    change Exact.ulp ctx magnitude beta fexp x =
      Exact.bpow ctx beta (fexp (Exact.mag ctx magnitude beta x)) at hu
    change Exact.ulp ctx magnitude beta fexp x = Exact.bpow ctx beta ce
    simpa only [ce, ex] using hu
  let y : Exact.R ctx :=
    Exact.Rplus ctx x (Exact.ulp ctx magnitude beta fexp x)
  have hyle : Exact.Rle ctx y (Exact.bpow ctx beta ex) := by
    simpa only [y, ex] using
      (id_p_ulp_le_bpow ctx magnitude beta fexp x (Exact.mag ctx magnitude beta x)
        hx hformat hxupper)
  by_cases hyeq : y = Exact.bpow ctx beta ex
  · have hmagpow := pg_ulp_mag_bpow ctx magnitude beta ex
    have hcepow : Exact.cexp ctx magnitude beta fexp
        (Exact.bpow ctx beta ex) = fexp (CompCert4Lean.Flocq.Core.Raux.Zadd ex Zone) := by
      change fexp (Exact.mag ctx magnitude beta (Exact.bpow ctx beta ex)) = _
      rw [hmagpow]
    have hpowlt : Exact.Rlt ctx (Exact.bpow ctx beta ce)
        (Exact.bpow ctx beta ex) := by
      have htmp : Exact.Rlt ctx (Exact.ulp ctx magnitude beta fexp x) y := by
        have h := ctx.certificate.orderedField.add_lt_compat_l
          (Exact.ulp ctx magnitude beta fexp x) ctx.spec.zero x hx
        change ctx.spec.lt
          (ctx.spec.add (Exact.ulp ctx magnitude beta fexp x) ctx.spec.zero)
          (ctx.spec.add (Exact.ulp ctx magnitude beta fexp x) x) at h
        rw [ctx.certificate.orderedField.add_zero] at h
        rw [ctx.certificate.orderedField.add_comm] at h
        exact h
      rw [← hulp, ← hyeq]
      exact htmp
    have hce_lt : Zlt ce ex := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ce <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex
      by_cases hlt : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ce <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex
      · exact hlt
      · have hge : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ce := by omega
        have hle := idp_bpow_le ctx beta hge
        exact False.elim
          (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hpowlt).2 hle)
    have hfexp_le : Zle (fexp (CompCert4Lean.Flocq.Core.Raux.Zadd ex Zone)) ex :=
      (hvalid.valid_exp ex).1 hce_lt
    have hreprpow :
        CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta Zone ex) =
          Exact.bpow ctx beta ex := by
      change ctx.spec.mul (ctx.spec.ofZ Zone) (Exact.bpow ctx beta ex) = _
      rw [ctx.certificate.sourceLaws.ofZ_one,
        ctx.certificate.orderedField.one_mul]
    have hformatpow : Exact.generic_format ctx magnitude beta fexp
        (Exact.bpow ctx beta ex) := by
      rw [← hreprpow]
      apply pg_pred_ge_gt_generic_format_F2R ctx magnitude beta fexp Zone ex
      intro _
      rw [hreprpow, hcepow]
      exact hfexp_le
    rw [hsuccpos]
    change Exact.generic_format ctx magnitude beta fexp y
    rw [hyeq]
    exact hformatpow
  · have hylt : Exact.Rlt ctx y (Exact.bpow ctx beta ex) := by
      rcases ctx.certificate.total_order y (Exact.bpow ctx beta ex) with h | h
      · rcases h with hlt | heq
        · exact hlt
        · exact (hyeq heq).elim
      · exact False.elim
          (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h).2 hyle)
    have hypos : Exact.Rlt ctx (Exact.R0 ctx) y := by
      have hxy : Exact.Rlt ctx x y := by
        have h := ctx.certificate.orderedField.add_lt_compat_l x ctx.spec.zero
          (Exact.ulp ctx magnitude beta fexp x) (by
            rw [hulp]
            exact CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta _)
        change ctx.spec.lt (ctx.spec.add x ctx.spec.zero)
          (ctx.spec.add x (Exact.ulp ctx magnitude beta fexp x)) at h
        rw [ctx.certificate.orderedField.add_zero] at h
        exact h
      exact ctx.certificate.orderedField.lt_trans _ _ _ hx hxy
    have hyne : y ≠ Exact.R0 ctx := by
      intro hzero
      rw [hzero] at hypos
      exact (ctx.certificate.orderedField.lt_irrefl _ hypos).elim
    have hyabs : Exact.Rabs ctx y = y := by
      change ctx.spec.abs y = y
      exact ctx.certificate.sourceLaws.abs_nonnegative _
        ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hypos).1
    have hxy_le : Exact.Rle ctx x y := by
      exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp (by
        have h := ctx.certificate.orderedField.add_lt_compat_l x ctx.spec.zero
          (Exact.ulp ctx magnitude beta fexp x) (by
            rw [hulp]
            exact CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta _)
        change ctx.spec.lt (ctx.spec.add x ctx.spec.zero)
          (ctx.spec.add x (Exact.ulp ctx magnitude beta fexp x)) at h
        rw [ctx.certificate.orderedField.add_zero] at h
        exact h) |>.1
    have hylower : Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone)) y := by
      have hlow : Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone)) x := by
        simpa only [hxabs, ex] using hmagx.1
      exact ctx.certificate.orderedField.le_trans _ _ _ hlow hxy_le
    have hymag :=
      (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta y).mag_bound hyne
    have hymageq : Exact.mag ctx magnitude beta y = ex := by
      apply ulp_mag_unique ctx beta y hymag
      simpa only [hyabs] using And.intro hylower hylt
    have hce : Exact.cexp ctx magnitude beta fexp y = ce := by
      change fexp (Exact.mag ctx magnitude beta y) = ce
      rw [hymageq]
    have hrepr :
        CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta
            (CompCert4Lean.Flocq.Core.Raux.Zadd m Zone) ce) = y := by
      change ctx.spec.mul (ctx.spec.ofZ (CompCert4Lean.Flocq.Core.Raux.Zadd m Zone))
          (Exact.bpow ctx beta ce) =
        ctx.spec.add x (Exact.ulp ctx magnitude beta fexp x)
      rw [hulp, hformat']
      change ctx.spec.mul (ctx.spec.ofZ (CompCert4Lean.Flocq.Core.Raux.Zadd m Zone))
          (Exact.bpow ctx beta ce) =
        ctx.spec.add
          (ctx.spec.mul (ctx.spec.ofZ m) (Exact.bpow ctx beta ce))
          (Exact.bpow ctx beta ce)
      rw [ctx.certificate.sourceLaws.ofZ_add,
        ctx.certificate.sourceLaws.ofZ_one,
        ctx.certificate.orderedField.mul_comm,
        ctx.certificate.orderedField.left_distrib,
        ctx.certificate.orderedField.mul_comm,
        ctx.certificate.orderedField.mul_comm,
        ctx.certificate.orderedField.mul_one]
    have hsuccfmt : Exact.generic_format ctx magnitude beta fexp y := by
      rw [← hrepr]
      apply pg_pred_ge_gt_generic_format_F2R ctx magnitude beta fexp
        (CompCert4Lean.Flocq.Core.Raux.Zadd m Zone) ce
      intro _
      have hc : Exact.cexp ctx magnitude beta fexp
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
            (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta
              (CompCert4Lean.Flocq.Core.Raux.Zadd m Zone) ce)) = ce := by
        rw [hrepr]
        exact hce
      rw [hc]
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ce ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ce
      omega
    rw [hsuccpos]
    simpa only [y] using hsuccfmt

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

theorem pred_succ_pos :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      pred_succ_posStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x hformat hx
  have hxne : x ≠ Exact.R0 ctx := by
    intro hxzero
    rw [hxzero] at hx
    exact (ctx.certificate.orderedField.lt_irrefl _ hx).elim
  have hsuccfmt : Exact.generic_format ctx magnitude beta fexp
      (Exact.succ ctx magnitude beta fexp x) :=
    pg_generic_format_succ_pos ctx magnitude beta fexp hvalid x hformat hx
  have hsuccgt : Exact.Rlt ctx x
      (Exact.succ ctx magnitude beta fexp x) :=
    succ_gt_id ctx magnitude beta fexp x hxne
  have hsuccpos : Exact.Rlt ctx (Exact.R0 ctx)
      (Exact.succ ctx magnitude beta fexp x) :=
    ctx.certificate.orderedField.lt_trans _ _ _ hx hsuccgt
  have hpred_eq : Exact.pred ctx magnitude beta fexp
      (Exact.succ ctx magnitude beta fexp x) =
      Exact.pred_pos ctx magnitude beta fexp
        (Exact.succ ctx magnitude beta fexp x) :=
    pg_pred_ge_gt_pred_eq_pos ctx magnitude beta fexp _ hsuccpos
  have hpredfmt_pos : Exact.generic_format ctx magnitude beta fexp
      (Exact.pred_pos ctx magnitude beta fexp
        (Exact.succ ctx magnitude beta fexp x)) :=
    pg_pred_ge_gt_generic_pred_pos ctx magnitude beta fexp hvalid
      _ hsuccfmt hsuccpos
  have hpredfmt : Exact.generic_format ctx magnitude beta fexp
      (Exact.pred ctx magnitude beta fexp
        (Exact.succ ctx magnitude beta fexp x)) := by
    rw [hpred_eq]
    exact hpredfmt_pos
  have hupper : Exact.Rle ctx
      (Exact.pred ctx magnitude beta fexp
        (Exact.succ ctx magnitude beta fexp x)) x := by
    rcases ctx.certificate.total_order x
        (Exact.pred ctx magnitude beta fexp
          (Exact.succ ctx magnitude beta fexp x)) with h | h
    · rcases h with hlt | heq
      · have hsle := pg_pred_ge_gt_succ_le_lt_aux ctx magnitude beta fexp
          hvalid x
          (Exact.pred ctx magnitude beta fexp
            (Exact.succ ctx magnitude beta fexp x))
          hformat hpredfmt
          ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hx).1
          hlt
        have hsneq : Exact.succ ctx magnitude beta fexp x ≠ Exact.R0 ctx := by
          intro hz
          exact (ctx.certificate.orderedField.lt_irrefl _
            (by rw [hz] at hsuccpos; exact hsuccpos)).elim
        have hp_lt := pred_lt_id ctx magnitude beta fexp
          (Exact.succ ctx magnitude beta fexp x) hsneq
        exact (ctx.certificate.orderedField.lt_irrefl _
          (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
            ctx _ _ _ hsle hp_lt)).elim
      · rw [← heq]
        exact ctx.certificate.orderedField.le_refl _
    · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1
  have hlower : Exact.Rle ctx x
      (Exact.pred ctx magnitude beta fexp
        (Exact.succ ctx magnitude beta fexp x)) :=
    pred_ge_gt ctx magnitude beta fexp hvalid x
      (Exact.succ ctx magnitude beta fexp x)
      hformat hsuccfmt hsuccgt
  exact ctx.certificate.orderedField.le_antisymm _ _ hupper hlower

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

theorem succ_pred :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      succ_predStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x hformat
  rcases ctx.certificate.total_order (Exact.R0 ctx) x with h | h
  · rcases h with hx | hzero
    · exact succ_pred_pos ctx magnitude beta fexp hvalid x hformat hx
    · rw [← hzero, pred_0]
      rw [succ_opp]
      rw [pred_ulp_0 ctx magnitude beta fexp hvalid]
      change ctx.spec.neg ctx.spec.zero = ctx.spec.zero
      have hz := ctx.certificate.orderedField.neg_add_cancel ctx.spec.zero
      rw [ctx.certificate.orderedField.add_zero] at hz
      exact hz
  · have hxpos : Exact.Rlt ctx (Exact.R0 ctx) (Exact.Ropp ctx x) := by
      have hneg := ulp_neg_lt_neg ctx h
      change ctx.spec.lt (ctx.spec.neg ctx.spec.zero) (ctx.spec.neg x) at hneg
      have hnegzero : ctx.spec.neg ctx.spec.zero = ctx.spec.zero := by
        have hz := ctx.certificate.orderedField.neg_add_cancel ctx.spec.zero
        rw [ctx.certificate.orderedField.add_zero] at hz
        exact hz
      rw [hnegzero] at hneg
      exact hneg
    have hformatneg : Exact.generic_format ctx magnitude beta fexp
        (Exact.Ropp ctx x) := by
      exact CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_opp ctx magnitude
        beta fexp x hformat
    unfold Exact.pred
    rw [succ_opp]
    rw [pred_succ_pos ctx magnitude beta fexp hvalid
      (Exact.Ropp ctx x) hformatneg hxpos]
    exact ulp_neg_neg ctx x

theorem pred_succ :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      pred_succStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x hformat
  have hsp := succ_pred ctx magnitude beta fexp hvalid
    (Exact.Ropp ctx x)
    (CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_opp ctx magnitude
      beta fexp x hformat)
  rw [pred_opp, succ_opp] at hsp
  have hsp' := congrArg (Exact.Ropp ctx) hsp
  calc
    Exact.pred ctx magnitude beta fexp (Exact.succ ctx magnitude beta fexp x) =
        Exact.Ropp ctx (Exact.Ropp ctx
          (Exact.pred ctx magnitude beta fexp
            (Exact.succ ctx magnitude beta fexp x))) :=
      (ulp_neg_neg ctx _).symm
    _ = Exact.Ropp ctx (Exact.Ropp ctx x) := hsp'
    _ = x := ulp_neg_neg ctx x

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

theorem round_neq_0_negligible_exp :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      round_neq_0_negligible_expStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid hnegligible rnd hrnd x hx
  intro hzero
  let ex : Z := Exact.mag ctx magnitude beta x
  have hmag := (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_bound hx
  have hce : Exact.cexp ctx magnitude beta fexp x = fexp ex := by
    rfl
  have habs_sm :=
    (CompCert4Lean.Flocq.Core.Generic_fmt.scaled_mantissa_abs
      ctx magnitude beta fexp x).symm
  have hce_abs : Exact.cexp ctx magnitude beta fexp (Exact.Rabs ctx x) = fexp ex := by
    exact CompCert4Lean.Flocq.Core.Generic_fmt.cexp_fexp_pos
      ctx magnitude beta fexp (Exact.Rabs ctx x) ex hmag
  have hce_abs' :
      CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp
          ctx magnitude beta fexp (Exact.Rabs ctx x) = fexp ex := hce_abs
  have habs_sm' :
      Exact.Rabs ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
            ctx magnitude beta fexp x) =
        CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rmult ctx (Exact.Rabs ctx x)
          (Exact.bpow ctx beta (Zopp (fexp ex))) := by
    calc
      _ = CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
          ctx magnitude beta fexp (Exact.Rabs ctx x) := habs_sm
      _ = _ := by
        unfold CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
        rw [hce_abs']
  have hpow_nonneg : Exact.Rle ctx (Exact.R0 ctx)
      (Exact.bpow ctx beta (Zopp (fexp ex))) := by
    exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
      (CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta _ ) |>.1
  have hpow_nonneg' : Exact.Rle ctx
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Z0)
      (Exact.bpow ctx beta (Zopp (fexp ex))) := by
    change ctx.spec.le (ctx.spec.ofZ Z0) _
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hpow_nonneg
  have hprod :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
      ctx (Exact.bpow ctx beta (Zopp (fexp ex)))
      (Exact.bpow ctx beta (Zsub ex Zone)) (Exact.Rabs ctx x)
      hpow_nonneg' hmag.1
  have hspec := negligible_exp_spec' fexp
  rw [hnegligible] at hspec
  have hnone : ∀ n : Z, Raux.Zlt (fexp n) n := by
    rcases hspec with hnone | ⟨n, hsome, _⟩
    · exact hnone.2
    · exact False.elim (by simpa [hnegligible] using hsome)
  have hfe : Zlt (fexp ex) ex := by
    exact hnone ex
  have hde : Zle Z0 (Zsub (Zsub ex Zone) (fexp ex)) := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zsub (Zsub ex Zone) (fexp ex))
    simp only [Zsub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change (0 : Int) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex - 1 -
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp ex)
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp ex) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex at hfe
    omega
  have hexp_add :
      CompCert4Lean.Flocq.Core.Raux.Zadd (Zsub ex Zone)
          (CompCert4Lean.Flocq.Core.Raux.Zopp (fexp ex)) =
        Zsub (Zsub ex Zone) (fexp ex) := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [CompCert4Lean.Flocq.Core.Raux.Zadd,
      CompCert4Lean.Flocq.Core.Raux.Zsub,
      CompCert4Lean.Flocq.Core.Raux.Zopp,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    omega
  have hpow_add := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta
      (Zsub ex Zone) (CompCert4Lean.Flocq.Core.Raux.Zopp (fexp ex))
  have hprod' :
      Exact.Rle ctx
        (Exact.bpow ctx beta (Zsub (Zsub ex Zone) (fexp ex)))
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rmult ctx
          (Exact.Rabs ctx x) (Exact.bpow ctx beta (Zopp (fexp ex)))) := by
    rw [← hexp_add]
    change Exact.bpow ctx beta
        (CompCert4Lean.Flocq.Core.Raux.Zadd (Zsub ex Zone)
          (CompCert4Lean.Flocq.Core.Raux.Zopp (fexp ex))) = _ at hpow_add
    rw [hpow_add]
    exact hprod
  have hpow_one :
      Exact.Rle ctx (Exact.bpow ctx beta Z0)
        (Exact.bpow ctx beta (Zsub (Zsub ex Zone) (fexp ex))) := by
    exact CompCert4Lean.Flocq.Core.Raux.bpow_le ctx beta Z0
      (Zsub (Zsub ex Zone) (fexp ex)) hde
  have hsm_lower :
      Exact.Rle ctx (Exact.bpow ctx beta Z0)
        (Exact.Rabs ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
            ctx magnitude beta fexp x)) := by
    exact ctx.certificate.orderedField.le_trans _ _ _ hpow_one
      (habs_sm'.symm ▸ hprod')
  have hone_abs :
      Exact.Rle ctx
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone)
        (Exact.Rabs ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
            ctx magnitude beta fexp x)) := by
    change ctx.spec.le (ctx.spec.ofZ Zone) _
    rw [ctx.certificate.sourceLaws.ofZ_one]
    exact hsm_lower
  have hzero' :
      CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta
            (rnd (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
              ctx magnitude beta fexp x))
            (Exact.cexp ctx magnitude beta fexp x)) = Exact.R0 ctx := by
    change CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta
            (rnd (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
              ctx magnitude beta fexp x))
            (Exact.cexp ctx magnitude beta fexp x)) = Exact.R0 ctx at hzero
    exact hzero
  have hnum :
      rnd (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
        ctx magnitude beta fexp x) = Z0 :=
    CompCert4Lean.Flocq.Core.Float_prop.eq_0_F2R ctx beta _ _ hzero'
  let sm := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
    ctx magnitude beta fexp x
  have hone_abs' : Exact.Rle ctx
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone)
      (Exact.Rabs ctx sm) := by
    exact hone_abs
  rcases ctx.certificate.total_order (Exact.R0 ctx) sm with hsign | hneg
  · rcases hsign with hpos | heq
    · have habs_pos : Exact.Rabs ctx sm = sm := by
        change ctx.spec.abs sm = sm
        exact ctx.certificate.sourceLaws.abs_nonnegative sm
          ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hpos).1
      have hone_sm : Exact.Rle ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone) sm := by
        rw [habs_pos] at hone_abs'
        exact hone_abs'
      have hroundge := hrnd.Zrnd_le
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone) sm hone_sm
      rw [hrnd.Zrnd_IZR, hnum] at hroundge
      change (1 : Int) ≤ 0 at hroundge
      omega
    · have hone_zero := hone_abs'
      rw [← heq] at hone_zero
      change ctx.spec.le (ctx.spec.ofZ Zone) (ctx.spec.abs ctx.spec.zero) at hone_zero
      rw [ctx.certificate.sourceLaws.ofZ_one] at hone_zero
      have habsz : ctx.spec.abs ctx.spec.zero = ctx.spec.zero := by
        exact ctx.certificate.sourceLaws.abs_nonnegative _
          (ctx.certificate.orderedField.le_refl _)
      rw [habsz] at hone_zero
      have h01 := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_0_1 ctx
      unfold CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_0_1Statement at h01
      change ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.ofZ Zone) at h01
      rw [ctx.certificate.sourceLaws.ofZ_zero,
        ctx.certificate.sourceLaws.ofZ_one] at h01
      exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h01).2
        hone_zero
  · have habs_neg : Exact.Rabs ctx sm = ctx.spec.neg sm := by
      change ctx.spec.abs sm = ctx.spec.neg sm
      exact ctx.certificate.sourceLaws.abs_negative sm hneg
    have hone_neg : Exact.Rle ctx
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone)
        (ctx.spec.neg sm) := by
      rw [← habs_neg]
      exact hone_abs'
    have hplus : ctx.spec.le
        (ctx.spec.add sm (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone))
        ctx.spec.zero := by
      have htmp :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_le_compat_l
          ctx sm (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone)
          (ctx.spec.neg sm) hone_neg
      change ctx.spec.le
        (ctx.spec.add sm (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone))
        (ctx.spec.add sm (ctx.spec.neg sm)) at htmp
      rw [ctx.certificate.orderedField.add_comm sm (ctx.spec.neg sm),
        ctx.certificate.orderedField.neg_add_cancel] at htmp
      change ctx.spec.le
        (ctx.spec.add sm
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone))
        ctx.spec.zero
      exact htmp
    have hle_sm : Exact.Rle ctx sm
        (ctx.spec.neg (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone)) := by
      rcases ctx.certificate.total_order sm
          (ctx.spec.neg (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone)) with h | h
      · rcases h with hlt | heq
        · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt |>.1
        · rw [heq]
          exact ctx.certificate.orderedField.le_refl _
      · have hlt := h
        have hltadd := ctx.certificate.orderedField.add_lt_compat_l
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone)
          (ctx.spec.neg (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone)) sm hlt
        have hltadd' : ctx.spec.lt ctx.spec.zero
            (ctx.spec.add (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone) sm) := by
          change ctx.spec.lt
            (ctx.spec.add (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone)
              (ctx.spec.neg (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone)))
            (ctx.spec.add (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone) sm) at hltadd
          rw [ctx.certificate.orderedField.add_comm
                (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone)
                (ctx.spec.neg (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone)),
            ctx.certificate.orderedField.neg_add_cancel] at hltadd
          exact hltadd
        have hplus' : ctx.spec.le
            (ctx.spec.add (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone) sm)
            ctx.spec.zero := by
          rw [ctx.certificate.orderedField.add_comm sm
            (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone)] at hplus
          exact hplus
        exact (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hltadd').2
          hplus').elim
    have hroundle := hrnd.Zrnd_le sm
      (ctx.spec.neg (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone)) hle_sm
    have hneg_izr : ctx.spec.neg
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zone) =
        CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx
          (CompCert4Lean.Flocq.Core.Raux.Zopp Zone) := by
      symm
      exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.opp_IZR ctx Zone
    rw [hneg_izr, hrnd.Zrnd_IZR, hnum] at hroundle
    change (0 : Int) ≤ -1 at hroundle
    omega
end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

theorem pred_le :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      pred_leStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x y hxformat hyformat hxy
  rcases ctx.certificate.total_order x y with h | h
  · rcases h with hlt | heq
    · have hpred := pred_ge_gt ctx magnitude beta fexp hvalid x y
        hxformat hyformat hlt
      exact ctx.certificate.orderedField.le_trans _ _ _
        (pred_le_id ctx magnitude beta fexp x) hpred
    · rw [heq]
      exact ctx.certificate.orderedField.le_refl _
  · exact False.elim
      (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h).2 hxy)

private theorem pg_assignment_generic_format_succ
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (hvalid : Valid_exp fexp)
    (x : Exact.R ctx)
    (hformat : Exact.generic_format ctx magnitude beta fexp x) :
    Exact.generic_format ctx magnitude beta fexp
      (Exact.succ ctx magnitude beta fexp x) := by
  rcases ctx.certificate.total_order (Exact.R0 ctx) x with h | h
  · rcases h with hx | hxzero
    · exact pg_generic_format_succ_pos ctx magnitude beta fexp hvalid
        x hformat hx
    · subst x
      rw [succ_0]
      have hreq : Exact.Req_bool ctx (Exact.R0 ctx) (Exact.R0 ctx) = true :=
        CompCert4Lean.Flocq.Core.Raux.Req_bool_true ctx _ _ rfl
      unfold Exact.ulp
      rw [hreq]
      cases hnegligible : negligible_exp fexp with
      | none =>
          exact pg_pred_ge_gt_generic_format_zero ctx magnitude beta fexp
      | some n =>
          have hspec := negligible_exp_spec fexp
          rw [hnegligible] at hspec
          cases hspec with
          | negligible_Some n hn =>
              let e : Z := fexp n
              have hnext : Zle
                  (fexp (CompCert4Lean.Flocq.Core.Raux.Zadd e Zone)) e := by
                exact ((hvalid.valid_exp n).2 hn).1
              have hmag := pg_ulp_mag_bpow ctx magnitude beta e
              have hrepr :
                  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
                    (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta Zone e) =
                    Exact.bpow ctx beta e := by
                change ctx.spec.mul (ctx.spec.ofZ Zone)
                    (Exact.bpow ctx beta e) = Exact.bpow ctx beta e
                rw [ctx.certificate.sourceLaws.ofZ_one,
                  ctx.certificate.orderedField.one_mul]
              simp only
              change Exact.generic_format ctx magnitude beta fexp
                (Exact.bpow ctx beta e)
              rw [← hrepr]
              apply pg_pred_ge_gt_generic_format_F2R
                ctx magnitude beta fexp Zone e
              intro _
              rw [hrepr]
              change Zle
                (fexp (Exact.mag ctx magnitude beta (Exact.bpow ctx beta e))) e
              rw [hmag]
              exact hnext
  · have hnegzero : ctx.spec.neg ctx.spec.zero = ctx.spec.zero := by
      have hz := ctx.certificate.orderedField.neg_add_cancel ctx.spec.zero
      rw [ctx.certificate.orderedField.add_zero] at hz
      exact hz
    have hxopp : Exact.Rlt ctx (Exact.R0 ctx) (Exact.Ropp ctx x) := by
      have hn := ulp_neg_lt_neg ctx h
      change ctx.spec.lt (ctx.spec.neg ctx.spec.zero) (ctx.spec.neg x) at hn
      rw [hnegzero] at hn
      exact hn
    have hformatopp : Exact.generic_format ctx magnitude beta fexp
        (Exact.Ropp ctx x) :=
      CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_opp
        ctx magnitude beta fexp x hformat
    have hpredformat := pg_pred_ge_gt_generic_pred_pos
      ctx magnitude beta fexp hvalid (Exact.Ropp ctx x) hformatopp hxopp
    have hb : Exact.Rle_bool ctx (Exact.R0 ctx) x = false :=
      CompCert4Lean.Flocq.Core.Raux.Rle_bool_false ctx _ _ h
    unfold Exact.succ
    rw [hb]
    exact CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_opp
      ctx magnitude beta fexp _ hpredformat

theorem succ_le_inv :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      succ_le_invStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x y hxformat hyformat hsucc
  have hsxformat := pg_assignment_generic_format_succ
    ctx magnitude beta fexp hvalid x hxformat
  have hsyformat := pg_assignment_generic_format_succ
    ctx magnitude beta fexp hvalid y hyformat
  rw [← pred_succ ctx magnitude beta fexp hvalid x hxformat,
    ← pred_succ ctx magnitude beta fexp hvalid y hyformat]
  exact pred_le ctx magnitude beta fexp hvalid _ _ hsxformat hsyformat hsucc

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

private theorem pg_rdu_valid_rnd_DN (ctx : ExactRealContext) :
    CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Valid_rnd ctx
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx) := by
  constructor
  · exact CompCert4Lean.Flocq.Core.Raux.Zfloor_le ctx
  · exact CompCert4Lean.Flocq.Core.Raux.Zfloor_IZR ctx

private theorem pg_rdu_valid_rnd_UP (ctx : ExactRealContext) :
    CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Valid_rnd ctx
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx) := by
  constructor
  · exact CompCert4Lean.Flocq.Core.Raux.Zceil_le ctx
  · exact CompCert4Lean.Flocq.Core.Raux.Zceil_IZR ctx

private theorem pg_rdu_scale_cancel (ctx : ExactRealContext)
    (beta : radix) (x : Exact.R ctx) (e : Z) :
    ctx.spec.mul
        (ctx.spec.mul x (Exact.bpow ctx beta (Zopp e)))
        (Exact.bpow ctx beta e) = x := by
  calc
    ctx.spec.mul
        (ctx.spec.mul x (Exact.bpow ctx beta (Zopp e)))
        (Exact.bpow ctx beta e) =
        ctx.spec.mul x
          (ctx.spec.mul (Exact.bpow ctx beta (Zopp e))
            (Exact.bpow ctx beta e)) :=
      ctx.certificate.orderedField.mul_assoc _ _ _
    _ = ctx.spec.mul x
        (ctx.spec.mul (Exact.bpow ctx beta e)
          (Exact.bpow ctx beta (Zopp e))) := by
      rw [ctx.certificate.orderedField.mul_comm
        (Exact.bpow ctx beta (Zopp e))]
    _ = ctx.spec.mul x ctx.spec.one := by
      rw [pg_sllt_bpow_mul_inv ctx beta e]
    _ = x := ctx.certificate.orderedField.mul_one _

private theorem pg_rdu_bpow_split (ctx : ExactRealContext)
    (beta : radix) (a e : Z) :
    ctx.spec.mul
        (Exact.bpow ctx beta (Zsub a e))
        (Exact.bpow ctx beta e) = Exact.bpow ctx beta a := by
  have hsum : CompCert4Lean.Flocq.Core.Raux.Zadd (Zsub a e) e = a := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [CompCert4Lean.Flocq.Core.Raux.Zadd, Zsub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    omega
  have hpow := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta (Zsub a e) e
  change Exact.bpow ctx beta
      (CompCert4Lean.Flocq.Core.Raux.Zadd (Zsub a e) e) =
    ctx.spec.mul (Exact.bpow ctx beta (Zsub a e))
      (Exact.bpow ctx beta e) at hpow
  rw [hsum] at hpow
  exact hpow.symm

private theorem pg_rdu_round_bounded_large_pos
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z)
    (rnd : Exact.R ctx → Z)
    (hrnd : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Valid_rnd ctx rnd)
    (x : Exact.R ctx) (ex : Z)
    (hexp : Zlt (fexp ex) ex)
    (hbounds : Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone)) x ∧
      Exact.Rlt ctx x (Exact.bpow ctx beta ex)) :
    Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone))
        (Exact.round ctx magnitude beta fexp rnd x) ∧
      Exact.Rle ctx (Exact.round ctx magnitude beta fexp rnd x)
        (Exact.bpow ctx beta ex) := by
  let e : Z := fexp ex
  let s : Exact.R ctx :=
    ctx.spec.mul x (Exact.bpow ctx beta (Zopp e))
  have hcexp := CompCert4Lean.Flocq.Core.Generic_fmt.cexp_fexp_pos
    ctx magnitude beta fexp x ex hbounds
  have hscaled :
      CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
        ctx magnitude beta fexp x = s := by
    unfold CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
    rw [hcexp]
    rfl
  have hround : Exact.round ctx magnitude beta fexp rnd x =
      ctx.spec.mul (ctx.spec.ofZ (rnd s)) (Exact.bpow ctx beta e) := by
    unfold Exact.round CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
    rw [hcexp, hscaled]
    rfl
  have hepos : Exact.Rle ctx (Exact.R0 ctx) (Exact.bpow ctx beta e) :=
    CompCert4Lean.Flocq.Core.Raux.bpow_ge_0 ctx beta e
  have hnegepos : Exact.Rle ctx (Exact.R0 ctx)
      (Exact.bpow ctx beta (Zopp e)) :=
    CompCert4Lean.Flocq.Core.Raux.bpow_ge_0 ctx beta (Zopp e)
  have hepos' : ctx.spec.le (ctx.spec.ofZ Z0) (Exact.bpow ctx beta e) := by
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hepos
  have hnegepos' : ctx.spec.le (ctx.spec.ofZ Z0)
      (Exact.bpow ctx beta (Zopp e)) := by
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hnegepos
  have hcancel : ctx.spec.mul s (Exact.bpow ctx beta e) = x := by
    exact pg_rdu_scale_cancel ctx beta x e
  rcases CompCert4Lean.Flocq.Core.Generic_fmt.Zrnd_DN_or_UP
      ctx rnd hrnd s with hfloor | hceil
  · rw [hround, hfloor]
    constructor
    · let d : Z := Zsub (Zsub ex Zone) e
      have hd : Zle Z0 d := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d
        simp only [d, e, Zsub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        change (0 : Int) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex - 1 -
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp ex)
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp ex) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex at hexp
        omega
      let p : Z := CompCert4Lean.Flocq.Core.Raux.Zpower beta.radix_val d
      have hp : ctx.spec.ofZ p = Exact.bpow ctx beta d :=
        CompCert4Lean.Flocq.Core.Raux.IZR_Zpower ctx beta d hd
      have hscaledlower : Exact.Rle ctx (Exact.bpow ctx beta d) s := by
        have hmul :=
          CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
            ctx (Exact.bpow ctx beta (Zopp e))
              (Exact.bpow ctx beta (Zsub ex Zone)) x hnegepos' hbounds.1
        change ctx.spec.le
          (ctx.spec.mul (Exact.bpow ctx beta (Zsub ex Zone))
            (Exact.bpow ctx beta (Zopp e))) s at hmul
        have hsum : CompCert4Lean.Flocq.Core.Raux.Zadd
            (Zsub ex Zone) (Zopp e) = d := by
          apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
          simp only [d, CompCert4Lean.Flocq.Core.Raux.Zadd, Zsub, Zopp,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          omega
        have hpow := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta
          (Zsub ex Zone) (Zopp e)
        change Exact.bpow ctx beta
            (CompCert4Lean.Flocq.Core.Raux.Zadd (Zsub ex Zone) (Zopp e)) =
          ctx.spec.mul (Exact.bpow ctx beta (Zsub ex Zone))
            (Exact.bpow ctx beta (Zopp e)) at hpow
        rw [hsum] at hpow
        rw [← hpow] at hmul
        exact hmul
      have hplub : Zle p
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx s) :=
        CompCert4Lean.Flocq.Core.Raux.Zfloor_lub ctx p s (by
          change ctx.spec.le (ctx.spec.ofZ p) s
          rw [hp]
          exact hscaledlower)
      have hfloat := CompCert4Lean.Flocq.Core.Float_prop.F2R_le ctx beta
        p (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx s) e hplub
      change ctx.spec.le
        (ctx.spec.mul (ctx.spec.ofZ p) (Exact.bpow ctx beta e))
        (ctx.spec.mul (ctx.spec.ofZ
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx s))
          (Exact.bpow ctx beta e)) at hfloat
      rw [hp] at hfloat
      dsimp [d] at hfloat
      rw [pg_rdu_bpow_split ctx beta (Zsub ex Zone) e] at hfloat
      exact hfloat
    · have hlb := CompCert4Lean.Flocq.Core.Raux.Zfloor_lb ctx s
      have hmul :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
          ctx (Exact.bpow ctx beta e)
            (ctx.spec.ofZ
              (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx s))
            s hepos' hlb
      change ctx.spec.le
        (ctx.spec.mul
          (ctx.spec.ofZ
            (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx s))
          (Exact.bpow ctx beta e))
        (ctx.spec.mul s (Exact.bpow ctx beta e)) at hmul
      rw [hcancel] at hmul
      exact ctx.certificate.orderedField.le_trans _ _ _ hmul
        ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hbounds.2).1
  · rw [hround, hceil]
    constructor
    · have hub := CompCert4Lean.Flocq.Core.Raux.Zceil_ub ctx s
      have hmul :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
          ctx (Exact.bpow ctx beta e) s
            (ctx.spec.ofZ
              (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx s))
            hepos' hub
      change ctx.spec.le
        (ctx.spec.mul s (Exact.bpow ctx beta e))
        (ctx.spec.mul
          (ctx.spec.ofZ
            (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx s))
          (Exact.bpow ctx beta e)) at hmul
      rw [hcancel] at hmul
      exact ctx.certificate.orderedField.le_trans _ _ _ hbounds.1 hmul
    · let d : Z := Zsub ex e
      have hd : Zle Z0 d := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d
        simp only [d, e, Zsub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        change (0 : Int) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex -
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp ex)
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp ex) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex at hexp
        omega
      let p : Z := CompCert4Lean.Flocq.Core.Raux.Zpower beta.radix_val d
      have hp : ctx.spec.ofZ p = Exact.bpow ctx beta d :=
        CompCert4Lean.Flocq.Core.Raux.IZR_Zpower ctx beta d hd
      have hscaledupper : Exact.Rle ctx s (Exact.bpow ctx beta d) := by
        have hmul :=
          CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
            ctx (Exact.bpow ctx beta (Zopp e)) x
              (Exact.bpow ctx beta ex) hnegepos'
              ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hbounds.2).1
        change ctx.spec.le s
          (ctx.spec.mul (Exact.bpow ctx beta ex)
            (Exact.bpow ctx beta (Zopp e))) at hmul
        have hsum : CompCert4Lean.Flocq.Core.Raux.Zadd ex (Zopp e) = d := by
          apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
          simp only [d, CompCert4Lean.Flocq.Core.Raux.Zadd, Zsub, Zopp,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          omega
        have hpow := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta ex (Zopp e)
        change Exact.bpow ctx beta
            (CompCert4Lean.Flocq.Core.Raux.Zadd ex (Zopp e)) =
          ctx.spec.mul (Exact.bpow ctx beta ex)
            (Exact.bpow ctx beta (Zopp e)) at hpow
        rw [hsum] at hpow
        rw [← hpow] at hmul
        exact hmul
      have hpglb : Zle
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx s) p :=
        CompCert4Lean.Flocq.Core.Raux.Zceil_glb ctx p s (by
          change ctx.spec.le s (ctx.spec.ofZ p)
          rw [hp]
          exact hscaledupper)
      have hfloat := CompCert4Lean.Flocq.Core.Float_prop.F2R_le ctx beta
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx s) p e hpglb
      change ctx.spec.le
        (ctx.spec.mul (ctx.spec.ofZ
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx s))
          (Exact.bpow ctx beta e))
        (ctx.spec.mul (ctx.spec.ofZ p) (Exact.bpow ctx beta e)) at hfloat
      rw [hp] at hfloat
      dsimp [d] at hfloat
      rw [pg_rdu_bpow_split ctx beta ex e] at hfloat
      exact hfloat

private theorem pg_rdu_round_le_pos
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (hvalid : Valid_exp fexp)
    (rnd : Exact.R ctx → Z)
    (hrnd : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Valid_rnd ctx rnd)
    (x y : Exact.R ctx)
    (hx : Exact.Rlt ctx (Exact.R0 ctx) x)
    (hxy : Exact.Rle ctx x y) :
    Exact.Rle ctx (Exact.round ctx magnitude beta fexp rnd x)
      (Exact.round ctx magnitude beta fexp rnd y) := by
  have hy : Exact.Rlt ctx (Exact.R0 ctx) y :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
      ctx _ _ _ hx hxy
  have hxne : x ≠ Exact.R0 ctx := by
    intro hz
    rw [hz] at hx
    exact (ctx.certificate.orderedField.lt_irrefl _ hx).elim
  have hyne : y ≠ Exact.R0 ctx := by
    intro hz
    rw [hz] at hy
    exact (ctx.certificate.orderedField.lt_irrefl _ hy).elim
  let ex : Z := Exact.mag ctx magnitude beta x
  let ey : Z := Exact.mag ctx magnitude beta y
  have hxabs : Exact.Rabs ctx x = x := by
    change ctx.spec.abs x = x
    exact ctx.certificate.sourceLaws.abs_nonnegative x
      ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hx).1
  have hyabs : Exact.Rabs ctx y = y := by
    change ctx.spec.abs y = y
    exact ctx.certificate.sourceLaws.abs_nonnegative y
      ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hy).1
  have hxbounds :
      Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone)) x ∧
        Exact.Rlt ctx x (Exact.bpow ctx beta ex) := by
    simpa only [ex, hxabs] using
      (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_bound hxne
  have hybounds :
      Exact.Rle ctx (Exact.bpow ctx beta (Zsub ey Zone)) y ∧
        Exact.Rlt ctx y (Exact.bpow ctx beta ey) := by
    simpa only [ey, hyabs] using
      (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta y).mag_bound hyne
  have hexy : Zle ex ey := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ey
    by_cases hle : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ey
    · exact hle
    · have heylt : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ey <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex := by omega
      have heyle : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ey ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub ex Zone) := by
        simp only [Zsub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ey ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex - 1
        omega
      have hp := idp_bpow_le ctx beta heyle
      have hcycle :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
          ctx _ _ _ hybounds.2 hp
      have hcycle' := ctx.certificate.orderedField.le_trans _ _ _
        hxbounds.1 hxy
      exact False.elim
        (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hcycle).2
          hcycle')
  have heq (hfe : fexp ex = fexp ey) :
      Exact.Rle ctx (Exact.round ctx magnitude beta fexp rnd x)
        (Exact.round ctx magnitude beta fexp rnd y) := by
    unfold Exact.round CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
    unfold CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp
    change Exact.Rle ctx
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
        (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta
          (rnd (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
            ctx magnitude beta fexp x)) (fexp ex)))
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
        (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta
          (rnd (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
            ctx magnitude beta fexp y)) (fexp ey)))
    rw [hfe]
    apply CompCert4Lean.Flocq.Core.Float_prop.F2R_le ctx beta
    apply hrnd.Zrnd_le
    unfold CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
    unfold CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp
    change ctx.spec.le
      (ctx.spec.mul x (Exact.bpow ctx beta (Zopp (fexp ex))))
      (ctx.spec.mul y (Exact.bpow ctx beta (Zopp (fexp ey))))
    rw [hfe]
    have hp : ctx.spec.le (ctx.spec.ofZ Z0)
        (Exact.bpow ctx beta (Zopp (fexp ey))) := by
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact CompCert4Lean.Flocq.Core.Raux.bpow_ge_0 ctx beta _
    exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
      ctx _ _ _ hp hxy
  by_cases hysmall : Zle ey (fexp ey)
  · have hexfey : Zle ex (fexp ey) := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp ey)
      exact Int.le_trans hexy hysmall
    exact heq (((hvalid.valid_exp ey).2 hysmall).2 ex hexfey)
  · have hylarge : Zlt (fexp ey) ey := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp ey) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ey
      change ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ey ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp ey) at hysmall
      omega
    by_cases heqxy : ex = ey
    · exact heq (congrArg fexp heqxy)
    · have hexlt : Zlt ex ey := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ey
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ey at hexy
        have hne : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex ≠
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ey := by
          intro h
          exact heqxy (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective h)
        omega
      have hylo := (pg_rdu_round_bounded_large_pos ctx magnitude beta fexp
        rnd hrnd y ey hylarge hybounds).1
      apply ctx.certificate.orderedField.le_trans _ _ _ ?_ hylo
      by_cases hxsmall : Zle ex (fexp ex)
      · rcases CompCert4Lean.Flocq.Core.Generic_fmt.round_bounded_small_pos
          ctx magnitude beta fexp rnd hrnd x ex hxsmall hxbounds with hzero | hpow
        · change ctx.spec.le
            (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
              ctx magnitude beta fexp rnd x)
            (Exact.bpow ctx beta (Zsub ey Zone))
          rw [hzero]
          exact CompCert4Lean.Flocq.Core.Raux.bpow_ge_0 ctx beta (Zsub ey Zone)
        · change ctx.spec.le
            (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
              ctx magnitude beta fexp rnd x)
            (Exact.bpow ctx beta (Zsub ey Zone))
          rw [hpow]
          apply idp_bpow_le ctx beta
          have hfelt : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp ex) <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ey := by
            by_cases hlt :
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp ex) <
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ey
            · exact hlt
            · have heyfe : Zle ey (fexp ex) := by
                change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ey ≤
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp ex)
                omega
              have hsame := ((hvalid.valid_exp ex).2 hxsmall).2 ey heyfe
              change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp ey) <
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ey at hylarge
              rw [hsame] at hylarge
              exact False.elim (Int.not_lt_of_ge heyfe hylarge)
          simp only [Zsub,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp ex) ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ey - 1
          omega
      · have hxlarge : Zlt (fexp ex) ex := by
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp ex) <
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex
          change ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp ex) at hxsmall
          omega
        have hxhi := (pg_rdu_round_bounded_large_pos ctx magnitude beta fexp
          rnd hrnd x ex hxlarge hxbounds).2
        exact ctx.certificate.orderedField.le_trans _ _ _ hxhi
          (idp_bpow_le ctx beta (by
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex ≤
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub ey Zone)
            simp only [Zsub,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex ≤
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ey - 1
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ey at hexlt
            omega))

private theorem pg_rdu_neg_zero (ctx : ExactRealContext) :
    Exact.Ropp ctx (Exact.R0 ctx) = Exact.R0 ctx := by
  change ctx.spec.neg ctx.spec.zero = ctx.spec.zero
  have h := ctx.certificate.orderedField.neg_add_cancel ctx.spec.zero
  rw [ctx.certificate.orderedField.add_zero] at h
  exact h

private theorem pg_rdu_zopp_opp (z : Z) : Zopp (Zopp z) = z := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [Zopp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

private theorem pg_rdu_cexp_opp
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (x : Exact.R ctx) :
    Exact.cexp ctx magnitude beta fexp (Exact.Ropp ctx x) =
      Exact.cexp ctx magnitude beta fexp x := by
  unfold Exact.cexp CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp
  exact congrArg fexp
    (CompCert4Lean.Flocq.Core.Raux.mag_opp ctx magnitude beta x)

private theorem pg_rdu_round_DN_opp
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (x : Exact.R ctx) :
    Exact.round ctx magnitude beta fexp
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx)
        (Exact.Ropp ctx x) =
      Exact.Ropp ctx
        (Exact.round ctx magnitude beta fexp
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx) x) := by
  unfold Exact.round CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
  have hc := pg_rdu_cexp_opp ctx magnitude beta fexp x
  change CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp
      ctx magnitude beta fexp (Exact.Ropp ctx x) =
    CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp
      ctx magnitude beta fexp x at hc
  rw [hc,
    CompCert4Lean.Flocq.Core.Generic_fmt.scaled_mantissa_opp
      ctx magnitude beta fexp x]
  have hz : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ropp ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
            ctx magnitude beta fexp x)) =
      Zopp (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
          ctx magnitude beta fexp x)) := by
    change CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx
        (CompCert4Lean.Flocq.Core.Raux.Exact.Ropp ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
            ctx magnitude beta fexp x)) =
      Zopp (Zopp (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx
        (CompCert4Lean.Flocq.Core.Raux.Exact.Ropp ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
            ctx magnitude beta fexp x))))
    rw [pg_rdu_zopp_opp]
  rw [hz]
  exact CompCert4Lean.Flocq.Core.Float_prop.F2R_Zopp ctx beta _ _

private theorem pg_rdu_neg_round_UP_opp
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (x : Exact.R ctx) :
    Exact.Ropp ctx
        (Exact.round ctx magnitude beta fexp
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx)
          (Exact.Ropp ctx x)) =
      Exact.round ctx magnitude beta fexp
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx) x := by
  have h := pg_rdu_round_DN_opp ctx magnitude beta fexp (Exact.Ropp ctx x)
  change Exact.round ctx magnitude beta fexp
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx)
      (ctx.spec.neg (ctx.spec.neg x)) = _ at h
  rw [ulp_neg_neg ctx x] at h
  exact h.symm

private theorem pg_rdu_round_nonneg
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (rnd : Exact.R ctx → Z)
    (hrnd : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Valid_rnd ctx rnd)
    (x : Exact.R ctx) (hx : Exact.Rle ctx (Exact.R0 ctx) x) :
    Exact.Rle ctx (Exact.R0 ctx)
      (Exact.round ctx magnitude beta fexp rnd x) := by
  unfold Exact.round CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
  apply CompCert4Lean.Flocq.Core.Float_prop.F2R_ge_0 ctx beta
  change Zle Z0
    (rnd (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
      ctx magnitude beta fexp x))
  rw [← hrnd.Zrnd_IZR Z0]
  apply hrnd.Zrnd_le
  unfold CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
  have hp : ctx.spec.le (ctx.spec.ofZ Z0)
      (Exact.bpow ctx beta
        (Zopp (Exact.cexp ctx magnitude beta fexp x))) := by
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact CompCert4Lean.Flocq.Core.Raux.bpow_ge_0 ctx beta _
  have hx' : ctx.spec.le (ctx.spec.ofZ Z0) x := by
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hx
  have hmul := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_pos
    ctx x (Exact.bpow ctx beta
      (Zopp (Exact.cexp ctx magnitude beta fexp x))) hx' hp
  exact hmul

private theorem pg_rdu_round_DN_le
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (hvalid : Valid_exp fexp)
    (x y : Exact.R ctx) (hxy : Exact.Rle ctx x y) :
    Exact.Rle ctx
      (Exact.round ctx magnitude beta fexp
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx) x)
      (Exact.round ctx magnitude beta fexp
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx) y) := by
  let floor := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx
  let ceil := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx
  have hfloor := pg_rdu_valid_rnd_DN ctx
  have hceil := pg_rdu_valid_rnd_UP ctx
  rcases ctx.certificate.total_order (Exact.R0 ctx) x with hxcase | hxneg
  · rcases hxcase with hxpos | hxzero
    · exact pg_rdu_round_le_pos ctx magnitude beta fexp hvalid floor hfloor
        x y hxpos hxy
    · have hx0 : x = Exact.R0 ctx := hxzero.symm
      subst x
      have hy0 : Exact.Rle ctx (Exact.R0 ctx) y := hxy
      have hround0 := CompCert4Lean.Flocq.Core.Generic_fmt.round_0
        ctx magnitude beta fexp floor hfloor
      change CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rle ctx
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
          ctx magnitude beta fexp floor (Exact.R0 ctx))
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
          ctx magnitude beta fexp floor y)
      rw [hround0]
      exact pg_rdu_round_nonneg ctx magnitude beta fexp floor hfloor y hy0
  · rcases ctx.certificate.total_order y (Exact.R0 ctx) with hycase | hypos
    · rcases hycase with hyneg | hyzero
      · have hnypos : Exact.Rlt ctx (Exact.R0 ctx) (Exact.Ropp ctx y) := by
          have h :=
            CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_lt_contravar
              ctx (Exact.R0 ctx) y hyneg
          change ctx.spec.lt (ctx.spec.neg ctx.spec.zero) (ctx.spec.neg y) at h
          have hz : ctx.spec.neg ctx.spec.zero = ctx.spec.zero :=
            pg_rdu_neg_zero ctx
          rw [hz] at h
          exact h
        have hnegxy : Exact.Rle ctx (Exact.Ropp ctx y) (Exact.Ropp ctx x) :=
          CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_le_contravar
            ctx y x hxy
        have hposmono := pg_rdu_round_le_pos ctx magnitude beta fexp hvalid
          ceil hceil (Exact.Ropp ctx y) (Exact.Ropp ctx x) hnypos hnegxy
        have hnegmono :=
          CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_le_contravar
            ctx
              (Exact.round ctx magnitude beta fexp ceil (Exact.Ropp ctx x))
              (Exact.round ctx magnitude beta fexp ceil (Exact.Ropp ctx y))
              hposmono
        change Exact.Rle ctx
          (Exact.Ropp ctx
            (Exact.round ctx magnitude beta fexp ceil (Exact.Ropp ctx x)))
          (Exact.Ropp ctx
            (Exact.round ctx magnitude beta fexp ceil (Exact.Ropp ctx y)))
          at hnegmono
        rw [pg_rdu_neg_round_UP_opp ctx magnitude beta fexp x,
          pg_rdu_neg_round_UP_opp ctx magnitude beta fexp y] at hnegmono
        exact hnegmono
      · have hy0 : y = Exact.R0 ctx := hyzero
        subst y
        have hnxnonneg : Exact.Rle ctx (Exact.R0 ctx) (Exact.Ropp ctx x) := by
          have hxle : Exact.Rle ctx x (Exact.R0 ctx) :=
            (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxneg |>.1
          have h :=
            CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_le_contravar
              ctx (Exact.R0 ctx) x hxle
          change ctx.spec.le (ctx.spec.neg ctx.spec.zero) (ctx.spec.neg x) at h
          have hz : ctx.spec.neg ctx.spec.zero = ctx.spec.zero :=
            pg_rdu_neg_zero ctx
          rw [hz] at h
          exact h
        have hnonneg := pg_rdu_round_nonneg ctx magnitude beta fexp ceil hceil
          (Exact.Ropp ctx x) hnxnonneg
        have hneg :=
          CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_le_contravar
            ctx
              (Exact.round ctx magnitude beta fexp ceil (Exact.Ropp ctx x))
              (Exact.R0 ctx) hnonneg
        change Exact.Rle ctx
          (Exact.Ropp ctx
            (Exact.round ctx magnitude beta fexp ceil (Exact.Ropp ctx x)))
          (Exact.Ropp ctx (Exact.R0 ctx)) at hneg
        rw [pg_rdu_neg_zero ctx,
          pg_rdu_neg_round_UP_opp ctx magnitude beta fexp x] at hneg
        have hround0 := CompCert4Lean.Flocq.Core.Generic_fmt.round_0
          ctx magnitude beta fexp floor hfloor
        change CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rle ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
            ctx magnitude beta fexp floor x)
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
            ctx magnitude beta fexp floor (Exact.R0 ctx))
        rw [hround0]
        exact hneg
    · have hnxnonneg : Exact.Rle ctx (Exact.R0 ctx) (Exact.Ropp ctx x) := by
        have hxle : Exact.Rle ctx x (Exact.R0 ctx) :=
          (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxneg |>.1
        have h :=
          CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_le_contravar
            ctx (Exact.R0 ctx) x hxle
        change ctx.spec.le (ctx.spec.neg ctx.spec.zero) (ctx.spec.neg x) at h
        have hz : ctx.spec.neg ctx.spec.zero = ctx.spec.zero :=
          pg_rdu_neg_zero ctx
        rw [hz] at h
        exact h
      have hxround := pg_rdu_round_nonneg ctx magnitude beta fexp ceil hceil
        (Exact.Ropp ctx x) hnxnonneg
      have hxround' :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_le_contravar
          ctx
            (Exact.round ctx magnitude beta fexp ceil (Exact.Ropp ctx x))
            (Exact.R0 ctx) hxround
      change Exact.Rle ctx
        (Exact.Ropp ctx
          (Exact.round ctx magnitude beta fexp ceil (Exact.Ropp ctx x)))
        (Exact.Ropp ctx (Exact.R0 ctx)) at hxround'
      rw [pg_rdu_neg_zero ctx,
        pg_rdu_neg_round_UP_opp ctx magnitude beta fexp x] at hxround'
      have hyround := pg_rdu_round_nonneg ctx magnitude beta fexp floor hfloor y
        ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hypos).1
      exact ctx.certificate.orderedField.le_trans _ _ _ hxround' hyround

private theorem pg_rdu_round_DN_ge_generic
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (hvalid : Valid_exp fexp)
    (g x : Exact.R ctx)
    (hgformat : Exact.generic_format ctx magnitude beta fexp g)
    (hgx : Exact.Rle ctx g x) :
    Exact.Rle ctx g
      (Exact.round ctx magnitude beta fexp
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx) x) := by
  let floor := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx
  have hfloor := pg_rdu_valid_rnd_DN ctx
  have hmono := pg_rdu_round_DN_le ctx magnitude beta fexp hvalid g x hgx
  have hgeneric := CompCert4Lean.Flocq.Core.Generic_fmt.round_generic
    ctx magnitude beta fexp floor hfloor g hgformat
  change CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rle ctx
    (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
      ctx magnitude beta fexp floor g)
    (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
      ctx magnitude beta fexp floor x) at hmono
  rw [hgeneric] at hmono
  exact hmono

private theorem pg_rdu_round_UP_le_generic
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (hvalid : Valid_exp fexp)
    (x g : Exact.R ctx)
    (hgformat : Exact.generic_format ctx magnitude beta fexp g)
    (hxg : Exact.Rle ctx x g) :
    Exact.Rle ctx
      (Exact.round ctx magnitude beta fexp
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx) x) g := by
  have hnegformat := CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_opp
    ctx magnitude beta fexp g hgformat
  have hnegorder : Exact.Rle ctx (Exact.Ropp ctx g) (Exact.Ropp ctx x) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_le_contravar
      ctx g x hxg
  have hdn := pg_rdu_round_DN_ge_generic ctx magnitude beta fexp hvalid
    (Exact.Ropp ctx g) (Exact.Ropp ctx x) hnegformat hnegorder
  change Exact.Rle ctx (Exact.Ropp ctx g)
    (Exact.round ctx magnitude beta fexp
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx)
      (Exact.Ropp ctx x)) at hdn
  rw [pg_rdu_round_DN_opp ctx magnitude beta fexp x] at hdn
  exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_le_cancel
    ctx
      (Exact.round ctx magnitude beta fexp
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx) x)
      g hdn

theorem round_DN_ge_UP_gt :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      round_DN_ge_UP_gtStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x y hyformat hylt
  apply pg_rdu_round_DN_ge_generic ctx magnitude beta fexp hvalid y x hyformat
  rcases ctx.certificate.total_order x y with hxy | hyx
  · rcases hxy with hlt | heq
    · have hxyle : Exact.Rle ctx x y :=
        (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt |>.1
      have hup := pg_rdu_round_UP_le_generic ctx magnitude beta fexp hvalid
        x y hyformat hxyle
      exact False.elim
        (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hylt).2 hup)
    · rw [heq]
      exact ctx.certificate.orderedField.le_refl _
  · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hyx |>.1

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

theorem round_UP_le_DN_lt :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      round_UP_le_DN_ltStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x y hyformat hfloorlt
  rcases ctx.certificate.total_order
      (Exact.round ctx magnitude beta fexp
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx) x) y with hxy | hyx
  · rcases hxy with hlt | heq
    · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt |>.1
    · rw [heq]
      exact ctx.certificate.orderedField.le_refl _
  · have hdn := round_DN_ge_UP_gt ctx magnitude beta fexp hvalid x y hyformat hyx
    exact False.elim
      (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hfloorlt).2 hdn)

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

private theorem pg_current_generic_format_pred
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (hvalid : Valid_exp fexp)
    (x : Exact.R ctx)
    (hformat : Exact.generic_format ctx magnitude beta fexp x) :
    Exact.generic_format ctx magnitude beta fexp
      (Exact.pred ctx magnitude beta fexp x) := by
  unfold Exact.pred
  apply CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_opp
  apply pg_assignment_generic_format_succ ctx magnitude beta fexp hvalid
  exact CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_opp
    ctx magnitude beta fexp x hformat

private theorem pg_current_generic_format_round_UP
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (hvalid : Valid_exp fexp)
    (x : Exact.R ctx) :
    Exact.generic_format ctx magnitude beta fexp
      (Exact.round ctx magnitude beta fexp
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx) x) := by
  let ceil := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx
  have hceil := pg_rdu_valid_rnd_UP ctx
  rcases ctx.certificate.total_order (Exact.R0 ctx) x with hx | hx
  · rcases hx with hxpos | hxzero
    · exact CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_round_pos
        ctx magnitude beta fexp hvalid ceil hceil x hxpos
    · subst x
      have hround0 := CompCert4Lean.Flocq.Core.Generic_fmt.round_0
        ctx magnitude beta fexp ceil hceil
      change CompCert4Lean.Flocq.Core.Generic_fmt.Exact.generic_format
        ctx magnitude beta fexp
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
            ctx magnitude beta fexp ceil (Exact.R0 ctx))
      rw [hround0]
      exact pg_pred_ge_gt_generic_format_zero ctx magnitude beta fexp
  · have hnegpos : Exact.Rlt ctx (Exact.R0 ctx) (Exact.Ropp ctx x) := by
      have h := ulp_neg_lt_neg ctx hx
      change ctx.spec.lt (ctx.spec.neg ctx.spec.zero) (ctx.spec.neg x) at h
      have hz : ctx.spec.neg ctx.spec.zero = ctx.spec.zero := by
        have hz := ctx.certificate.orderedField.neg_add_cancel ctx.spec.zero
        rw [ctx.certificate.orderedField.add_zero] at hz
        exact hz
      rw [hz] at h
      exact h
    have hformat := CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_round_pos
      ctx magnitude beta fexp hvalid
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx)
      (pg_rdu_valid_rnd_DN ctx) (Exact.Ropp ctx x) hnegpos
    change Exact.generic_format ctx magnitude beta fexp
      (Exact.round ctx magnitude beta fexp
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx)
        (Exact.Ropp ctx x)) at hformat
    rw [pg_rdu_round_DN_opp ctx magnitude beta fexp x] at hformat
    have hneg := CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_opp
      ctx magnitude beta fexp _ hformat
    change Exact.generic_format ctx magnitude beta fexp
      (Exact.Ropp ctx (Exact.Ropp ctx
        (Exact.round ctx magnitude beta fexp
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx) x))) at hneg
    have hnn : Exact.Ropp ctx (Exact.Ropp ctx
        (Exact.round ctx magnitude beta fexp
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx) x)) =
        Exact.round ctx magnitude beta fexp
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx) x := by
      exact ulp_neg_neg ctx _
    rw [hnn] at hneg
    exact hneg

theorem pred_UP_le_DN :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      pred_UP_le_DNStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x
  let floor := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx
  let ceil := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx
  by_cases hxformat : Exact.generic_format ctx magnitude beta fexp x
  · have hfloor := CompCert4Lean.Flocq.Core.Generic_fmt.round_generic
      ctx magnitude beta fexp floor (pg_rdu_valid_rnd_DN ctx) x hxformat
    have hceil := CompCert4Lean.Flocq.Core.Generic_fmt.round_generic
      ctx magnitude beta fexp ceil (pg_rdu_valid_rnd_UP ctx) x hxformat
    change Exact.Rle ctx
      (Exact.pred ctx magnitude beta fexp
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
          ctx magnitude beta fexp ceil x))
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
        ctx magnitude beta fexp floor x)
    rw [hfloor, hceil]
    exact pred_le_id ctx magnitude beta fexp x
  · let u := Exact.round ctx magnitude beta fexp ceil x
    let d := Exact.round ctx magnitude beta fexp floor x
    change Exact.Rle ctx (Exact.pred ctx magnitude beta fexp u) d
    by_cases hu0 : u = Exact.R0 ctx
    · have hx0 : x ≠ Exact.R0 ctx := by
        intro hx0
        apply hxformat
        rw [hx0]
        exact pg_pred_ge_gt_generic_format_zero ctx magnitude beta fexp
      rcases negligible_exp_spec' fexp with hnone | hsome
      · have hune := round_neq_0_negligible_exp ctx magnitude beta fexp hvalid
          hnone.1 ceil (pg_rdu_valid_rnd_UP ctx) x hx0
        exact False.elim (hune hu0)
      · rcases hsome with ⟨n, hn, hnle⟩
        have hulp : Exact.ulp ctx magnitude beta fexp (Exact.R0 ctx) =
            Exact.bpow ctx beta (fexp n) := by
          unfold Exact.ulp
          have hreq : Exact.Req_bool ctx (Exact.R0 ctx) (Exact.R0 ctx) = true :=
            CompCert4Lean.Flocq.Core.Raux.Req_bool_true ctx _ _ rfl
          rw [hreq, hn]
        have hpred0 := pred_0 ctx magnitude beta fexp
        rw [hu0, hpred0, hulp]
        rcases ctx.certificate.total_order
            (Exact.Ropp ctx (Exact.bpow ctx beta (fexp n))) d with h | h
        · rcases h with hlt | heq
          · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt |>.1
          · rw [heq]
            exact ctx.certificate.orderedField.le_refl _
        · have hpowformat : Exact.generic_format ctx magnitude beta fexp
              (Exact.bpow ctx beta (fexp n)) := by
            let e := fexp n
            have hnext : Zle
                (fexp (CompCert4Lean.Flocq.Core.Raux.Zadd e Zone)) e :=
              ((hvalid.valid_exp n).2 hnle).1
            have hrepr :
                CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
                  (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta Zone e) =
                  Exact.bpow ctx beta e := by
              change ctx.spec.mul (ctx.spec.ofZ Zone) (Exact.bpow ctx beta e) = _
              rw [ctx.certificate.sourceLaws.ofZ_one,
                ctx.certificate.orderedField.one_mul]
            rw [← hrepr]
            apply pg_pred_ge_gt_generic_format_F2R
              ctx magnitude beta fexp Zone e
            intro _
            rw [hrepr]
            change Zle
              (fexp (Exact.mag ctx magnitude beta (Exact.bpow ctx beta e))) e
            rw [pg_ulp_mag_bpow ctx magnitude beta e]
            exact hnext
          have hnegformat := CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_opp
            ctx magnitude beta fexp _ hpowformat
          have hup := round_UP_le_DN_lt ctx magnitude beta fexp hvalid x
            (Exact.Ropp ctx (Exact.bpow ctx beta (fexp n))) hnegformat h
          change Exact.Rle ctx u (Exact.Ropp ctx (Exact.bpow ctx beta (fexp n))) at hup
          rw [hu0] at hup
          have hpos := CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta (fexp n)
          have hneg := ulp_neg_lt_neg ctx hpos
          change ctx.spec.lt (ctx.spec.neg (Exact.bpow ctx beta (fexp n)))
            (ctx.spec.neg ctx.spec.zero) at hneg
          have hz : ctx.spec.neg ctx.spec.zero = ctx.spec.zero := by
            have hz := ctx.certificate.orderedField.neg_add_cancel ctx.spec.zero
            rw [ctx.certificate.orderedField.add_zero] at hz
            exact hz
          rw [hz] at hneg
          exact False.elim
            (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hneg).2 hup)
    · have huformat : Exact.generic_format ctx magnitude beta fexp u := by
        exact pg_current_generic_format_round_UP ctx magnitude beta fexp hvalid x
      have hpformat := pg_current_generic_format_pred
        ctx magnitude beta fexp hvalid u huformat
      have hplt : Exact.Rlt ctx (Exact.pred ctx magnitude beta fexp u) u :=
        pred_lt_id ctx magnitude beta fexp u hu0
      exact round_DN_ge_UP_gt ctx magnitude beta fexp hvalid x
        (Exact.pred ctx magnitude beta fexp u) hpformat hplt

private theorem pg_current_generic_format_round_DN
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (hvalid : Valid_exp fexp)
    (x : Exact.R ctx) :
    Exact.generic_format ctx magnitude beta fexp
      (Exact.round ctx magnitude beta fexp
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx) x) := by
  have hup := pg_current_generic_format_round_UP
    ctx magnitude beta fexp hvalid (Exact.Ropp ctx x)
  have hneg := CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_opp
    ctx magnitude beta fexp _ hup
  change Exact.generic_format ctx magnitude beta fexp
    (Exact.Ropp ctx
      (Exact.round ctx magnitude beta fexp
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx)
        (Exact.Ropp ctx x))) at hneg
  rw [pg_rdu_neg_round_UP_opp ctx magnitude beta fexp x] at hneg
  exact hneg

private theorem pg_current_round_DN_le_id
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (x : Exact.R ctx) :
    Exact.Rle ctx
      (Exact.round ctx magnitude beta fexp
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx) x) x := by
  let e := Exact.cexp ctx magnitude beta fexp x
  let s := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
    ctx magnitude beta fexp x
  have hfloor := CompCert4Lean.Flocq.Core.Raux.Zfloor_lb ctx s
  have hpow : ctx.spec.le ctx.spec.zero (Exact.bpow ctx beta e) :=
    CompCert4Lean.Flocq.Core.Raux.bpow_ge_0 ctx beta e
  have hmul :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
      ctx (Exact.bpow ctx beta e)
        (ctx.spec.ofZ
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx s))
        s (by
          change ctx.spec.le (ctx.spec.ofZ Z0) (Exact.bpow ctx beta e)
          rw [ctx.certificate.sourceLaws.ofZ_zero]
          exact hpow) hfloor
  change ctx.spec.le
    (ctx.spec.mul
      (ctx.spec.ofZ
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx s))
      (Exact.bpow ctx beta e))
    (ctx.spec.mul s (Exact.bpow ctx beta e)) at hmul
  change ctx.spec.le
    (ctx.spec.mul
      (ctx.spec.ofZ
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx s))
      (Exact.bpow ctx beta e)) x
  have hcancel : ctx.spec.mul s (Exact.bpow ctx beta e) = x := by
    exact pg_rdu_scale_cancel ctx beta x e
  rw [hcancel] at hmul
  exact hmul

private theorem pg_current_round_UP_ge_id
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (x : Exact.R ctx) :
    Exact.Rle ctx x
      (Exact.round ctx magnitude beta fexp
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx) x) := by
  let e := Exact.cexp ctx magnitude beta fexp x
  let s := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
    ctx magnitude beta fexp x
  have hceil := CompCert4Lean.Flocq.Core.Raux.Zceil_ub ctx s
  have hpow : ctx.spec.le ctx.spec.zero (Exact.bpow ctx beta e) :=
    CompCert4Lean.Flocq.Core.Raux.bpow_ge_0 ctx beta e
  have hmul :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
      ctx (Exact.bpow ctx beta e) s
        (ctx.spec.ofZ
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx s))
        (by
          change ctx.spec.le (ctx.spec.ofZ Z0) (Exact.bpow ctx beta e)
          rw [ctx.certificate.sourceLaws.ofZ_zero]
          exact hpow) hceil
  change ctx.spec.le
    (ctx.spec.mul s (Exact.bpow ctx beta e))
    (ctx.spec.mul
      (ctx.spec.ofZ
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx s))
      (Exact.bpow ctx beta e)) at hmul
  change ctx.spec.le x
    (ctx.spec.mul
      (ctx.spec.ofZ
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx s))
      (Exact.bpow ctx beta e))
  have hcancel : ctx.spec.mul s (Exact.bpow ctx beta e) = x := by
    exact pg_rdu_scale_cancel ctx beta x e
  rw [hcancel] at hmul
  exact hmul

theorem pred_UP_eq_DN :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      pred_UP_eq_DNStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x hxformat
  let floor := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx
  let ceil := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx
  let d := Exact.round ctx magnitude beta fexp floor x
  let u := Exact.round ctx magnitude beta fexp ceil x
  change Exact.pred ctx magnitude beta fexp u = d
  apply ctx.certificate.orderedField.le_antisymm
  · exact pred_UP_le_DN ctx magnitude beta fexp hvalid x
  · have hdformat : Exact.generic_format ctx magnitude beta fexp d :=
      pg_current_generic_format_round_DN ctx magnitude beta fexp hvalid x
    have huformat : Exact.generic_format ctx magnitude beta fexp u :=
      pg_current_generic_format_round_UP ctx magnitude beta fexp hvalid x
    have hdx : Exact.Rle ctx d x :=
      pg_current_round_DN_le_id ctx magnitude beta fexp x
    have hxu : Exact.Rle ctx x u :=
      pg_current_round_UP_ge_id ctx magnitude beta fexp x
    have hdu : Exact.Rle ctx d u :=
      ctx.certificate.orderedField.le_trans _ _ _ hdx hxu
    have hdune : d ≠ u := by
      intro hdu_eq
      apply hxformat
      have hxle : Exact.Rle ctx x d := by
        rw [hdu_eq]
        exact hxu
      have hxd : x = d := ctx.certificate.orderedField.le_antisymm _ _
        hxle hdx
      rw [hxd]
      exact hdformat
    have hdltu : Exact.Rlt ctx d u :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
        ⟨hdu, fun hud => hdune
          (ctx.certificate.orderedField.le_antisymm _ _ hdu hud)⟩
    exact pred_ge_gt ctx magnitude beta fexp hvalid d u
      hdformat huformat hdltu

theorem succ_DN_eq_UP :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      succ_DN_eq_UPStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x hxformat
  let floor := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx
  let ceil := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx
  let d := Exact.round ctx magnitude beta fexp floor x
  let u := Exact.round ctx magnitude beta fexp ceil x
  have hpred : Exact.pred ctx magnitude beta fexp u = d :=
    pred_UP_eq_DN ctx magnitude beta fexp hvalid x hxformat
  have huformat : Exact.generic_format ctx magnitude beta fexp u :=
    pg_current_generic_format_round_UP ctx magnitude beta fexp hvalid x
  calc
    Exact.succ ctx magnitude beta fexp d =
        Exact.succ ctx magnitude beta fexp
          (Exact.pred ctx magnitude beta fexp u) :=
      congrArg (Exact.succ ctx magnitude beta fexp) hpred.symm
    _ = u := succ_pred ctx magnitude beta fexp hvalid u huformat

private theorem pg_current_succ_le_lt
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (beta : radix) (fexp : Z → Z) (hvalid : Valid_exp fexp)
    (x y : Exact.R ctx)
    (hxformat : Exact.generic_format ctx magnitude beta fexp x)
    (hyformat : Exact.generic_format ctx magnitude beta fexp y)
    (hxy : Exact.Rlt ctx x y) :
    Exact.Rle ctx (Exact.succ ctx magnitude beta fexp x) y := by
  have hnxformat := CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_opp
    ctx magnitude beta fexp x hxformat
  have hnyformat := CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_opp
    ctx magnitude beta fexp y hyformat
  have hneglt : Exact.Rlt ctx (Exact.Ropp ctx y) (Exact.Ropp ctx x) :=
    ulp_neg_lt_neg ctx hxy
  have hp := pred_ge_gt ctx magnitude beta fexp hvalid
    (Exact.Ropp ctx y) (Exact.Ropp ctx x) hnyformat hnxformat hneglt
  rw [pred_opp ctx magnitude beta fexp x] at hp
  exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_le_cancel
    ctx (Exact.succ ctx magnitude beta fexp x) y hp

theorem round_DN_eq :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      round_DN_eqStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x d hdformat hbounds
  let floor := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx
  let ceil := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx
  let rd := Exact.round ctx magnitude beta fexp floor x
  have hdrd : Exact.Rle ctx d rd :=
    pg_rdu_round_DN_ge_generic ctx magnitude beta fexp hvalid
      d x hdformat hbounds.1
  apply ctx.certificate.orderedField.le_antisymm
  · by_cases hxformat : Exact.generic_format ctx magnitude beta fexp x
    · have hround := CompCert4Lean.Flocq.Core.Generic_fmt.round_generic
        ctx magnitude beta fexp floor (pg_rdu_valid_rnd_DN ctx) x hxformat
      change ctx.spec.le
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
          ctx magnitude beta fexp floor x) d
      change CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
        ctx magnitude beta fexp floor x = x at hround
      rw [hround]
      rcases ctx.certificate.total_order x d with hxd | hdx
      · rcases hxd with hlt | heq
        · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt |>.1
        · rw [heq]
          exact ctx.certificate.orderedField.le_refl _
      · have hsuccle := pg_current_succ_le_lt
          ctx magnitude beta fexp hvalid d x hdformat hxformat hdx
        exact False.elim
          (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hbounds.2).2
            hsuccle)
    · have hrdformat : Exact.generic_format ctx magnitude beta fexp rd :=
        pg_current_generic_format_round_DN ctx magnitude beta fexp hvalid x
      have hsuccdformat : Exact.generic_format ctx magnitude beta fexp
          (Exact.succ ctx magnitude beta fexp d) :=
        pg_assignment_generic_format_succ
          ctx magnitude beta fexp hvalid d hdformat
      have hxle : Exact.Rle ctx x (Exact.succ ctx magnitude beta fexp d) :=
        (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hbounds.2 |>.1
      have hupp := pg_rdu_round_UP_le_generic
        ctx magnitude beta fexp hvalid x
          (Exact.succ ctx magnitude beta fexp d) hsuccdformat hxle
      have hsuccround := succ_DN_eq_UP
        ctx magnitude beta fexp hvalid x hxformat
      change Exact.succ ctx magnitude beta fexp rd =
        Exact.round ctx magnitude beta fexp ceil x at hsuccround
      rw [← hsuccround] at hupp
      exact succ_le_inv ctx magnitude beta fexp hvalid rd d
        hrdformat hdformat hupp
  · exact hdrd

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

theorem round_UP_eq :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      round_UP_eqStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x u huformat hbounds
  have hdn := round_DN_eq ctx magnitude beta fexp hvalid
    (Exact.Ropp ctx x) (Exact.Ropp ctx u)
    (CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_opp
      ctx magnitude beta fexp u huformat)
    (by
      constructor
      · change ctx.spec.le (ctx.spec.neg u) (ctx.spec.neg x)
        apply CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_le_contravar
          ctx u x
        exact hbounds.2
      · rw [succ_opp ctx magnitude beta fexp u]
        change ctx.spec.lt (ctx.spec.neg x)
          (ctx.spec.neg (Exact.pred ctx magnitude beta fexp u))
        apply CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_lt_contravar
          ctx x (Exact.pred ctx magnitude beta fexp u)
        exact hbounds.1)
  change Exact.round ctx magnitude beta fexp
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx)
      (Exact.Ropp ctx x) = Exact.Ropp ctx u at hdn
  rw [pg_rdu_round_DN_opp ctx magnitude beta fexp x] at hdn
  have hri1 : Exact.Ropp ctx (Exact.Ropp ctx
      (Exact.round ctx magnitude beta fexp
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx) x)) =
      Exact.round ctx magnitude beta fexp
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx) x :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_involutive ctx _
  have hri2 : Exact.Ropp ctx (Exact.Ropp ctx u) = u :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_involutive ctx _
  have hround := congrArg (fun z => Exact.Ropp ctx z) hdn
  change Exact.Ropp ctx (Exact.Ropp ctx
      (Exact.round ctx magnitude beta fexp
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx) x)) =
      Exact.Ropp ctx (Exact.Ropp ctx u) at hround
  rw [hri1, hri2] at hround
  exact hround

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

theorem round_UP_DN_ulp :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      round_UP_DN_ulpStatement ctx magnitude := by
  intro ctx magnitude beta fexp x hxformat
  have hxne : x ≠ Exact.R0 ctx := by
    intro hxzero
    apply hxformat
    rw [hxzero]
    exact pg_pred_ge_gt_generic_format_zero ctx magnitude beta fexp
  have hulp := ulp_neq_0 ctx magnitude beta fexp x hxne
  let sm := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp x
  let ce := Exact.cexp ctx magnitude beta fexp x
  change CompCert4Lean.Flocq.Core.Defs.Exact.F2R ctx
      (CompCert4Lean.Flocq.Core.Float_prop.Float beta
        (CompCert4Lean.Flocq.Core.Raux.Exact.Zceil ctx sm) ce) =
    Exact.Rplus ctx
      (CompCert4Lean.Flocq.Core.Defs.Exact.F2R ctx
        (CompCert4Lean.Flocq.Core.Float_prop.Float beta
          (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx sm) ce))
      (Exact.ulp ctx magnitude beta fexp x)
  unfold CompCert4Lean.Flocq.Core.Defs.Exact.F2R
  rw [hulp]
  have hceil := CompCert4Lean.Flocq.Core.Raux.Zceil_floor_neq ctx sm (by
    intro hsm
    apply hxformat
    change x = CompCert4Lean.Flocq.Core.Defs.Exact.F2R ctx
      (CompCert4Lean.Flocq.Core.Float_prop.Float beta
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx sm) ce)
    have htrunc : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx sm =
        CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx sm := by
      calc
        CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx sm =
            CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx
              (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx
                (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx sm)) := by
          exact congrArg
            (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx) hsm.symm
        _ = CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx sm :=
          CompCert4Lean.Flocq.Core.Raux.Ztrunc_IZR ctx _
    rw [htrunc]
    have hscaled := CompCert4Lean.Flocq.Core.Generic_fmt.scaled_mantissa_mult_bpow
      ctx magnitude beta fexp x
    calc
      x = CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rmult ctx sm
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.bpow ctx beta ce) := hscaled.symm
      _ = CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rmult ctx
          (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx
            (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx sm))
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.bpow ctx beta ce) := by
        congr 1
        exact hsm.symm
      _ = CompCert4Lean.Flocq.Core.Defs.Exact.F2R ctx
          (CompCert4Lean.Flocq.Core.Float_prop.Float beta
            (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx sm) ce) := by rfl)
  rw [hceil]
  -- algebra
  change ctx.spec.mul
      (ctx.spec.ofZ
        (CompCert4Lean.Flocq.Core.Raux.Zadd
          (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx sm)
          CompCert4Lean.Flocq.Core.Zaux.Zone))
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta ce) =
    ctx.spec.add
      (ctx.spec.mul
        (ctx.spec.ofZ (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx sm))
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta ce))
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta ce)
  rw [ctx.certificate.sourceLaws.ofZ_add,
    ctx.certificate.sourceLaws.ofZ_one,
    ctx.certificate.orderedField.mul_comm,
    ctx.certificate.orderedField.left_distrib,
    ctx.certificate.orderedField.mul_comm,
    ctx.certificate.orderedField.mul_comm,
    ctx.certificate.orderedField.mul_one]

end CompCert4Lean.Flocq.Core.Ulp

namespace CompCert4Lean.Flocq.Core.Ulp

theorem generic_format_ulp_0 :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      generic_format_ulp_0Statement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid
  have hreq : Exact.Req_bool ctx (Exact.R0 ctx) (Exact.R0 ctx) = true :=
    CompCert4Lean.Flocq.Core.Raux.Req_bool_true ctx _ _ rfl
  unfold Exact.ulp
  simp only [hreq]
  cases hs : negligible_exp fexp with
  | none =>
      simp only [hs]
      change Exact.R0 ctx =
        CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Float beta
            (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx
              (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp (Exact.R0 ctx)))
            (Exact.cexp ctx magnitude beta fexp (Exact.R0 ctx)))
      rw [CompCert4Lean.Flocq.Core.Generic_fmt.scaled_mantissa_0
        ctx magnitude beta fexp]
      have hz : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx (Exact.R0 ctx) =
          CompCert4Lean.Flocq.Core.Zaux.Z0 := by
        rw [show Exact.R0 ctx = CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx
            CompCert4Lean.Flocq.Core.Zaux.Z0 by
          exact ctx.certificate.sourceLaws.ofZ_zero.symm]
        exact CompCert4Lean.Flocq.Core.Raux.Ztrunc_IZR ctx
          CompCert4Lean.Flocq.Core.Zaux.Z0
      rw [hz]
      exact (CompCert4Lean.Flocq.Core.Float_prop.F2R_0 ctx beta _).symm
  | some n =>
      simp only [hs]
      have hspec := negligible_exp_spec fexp
      rw [hs] at hspec
      cases hspec with
      | negligible_Some n hn =>
          exact CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_bpow
            ctx magnitude beta fexp (fexp n)
            ((hvalid.valid_exp n).2 hn).1

end CompCert4Lean.Flocq.Core.Ulp


namespace CompCert4Lean.Flocq.Core.Ulp

theorem pred_eq_pos :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
      pred_eq_posStatement ctx magnitude := by
  intro ctx magnitude beta fexp x hx
  rcases ctx.certificate.total_order (Exact.R0 ctx) x with h | h
  · rcases h with hpos | hzero
    · exact pg_pred_ge_gt_pred_eq_pos ctx magnitude beta fexp x hpos
    · subst x
      rw [pred_0 ctx magnitude beta fexp]
      have hne : Exact.R0 ctx ≠ Exact.bpow ctx beta
          (Zsub (Exact.mag ctx magnitude beta (Exact.R0 ctx)) Zone) := by
        intro heq
        have hpos : Exact.Rlt ctx (Exact.R0 ctx) (Exact.bpow ctx beta
            (Zsub (Exact.mag ctx magnitude beta (Exact.R0 ctx)) Zone)) :=
          CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta _
        rw [← heq] at hpos
        exact ctx.certificate.orderedField.lt_irrefl _ hpos
      have hbool : Exact.Req_bool ctx (Exact.R0 ctx) (Exact.bpow ctx beta
          (Zsub (Exact.mag ctx magnitude beta (Exact.R0 ctx)) Zone)) = false :=
        CompCert4Lean.Flocq.Core.Raux.Req_bool_false ctx _ _ hne
      unfold Exact.pred_pos
      rw [hbool]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact (ctx.certificate.orderedField.zero_add _).symm
  · exact False.elim
      (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h).2 hx)

end CompCert4Lean.Flocq.Core.Ulp
