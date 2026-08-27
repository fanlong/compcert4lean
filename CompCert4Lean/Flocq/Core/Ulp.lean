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

def fexp_negligible_exp_eq_auxStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ n m, Zle n (fexp n) → Zle m (fexp m) → fexp n = fexp m

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
