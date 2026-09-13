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
