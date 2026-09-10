import CompCert4Lean.Flocq.Core.Defs
import CompCert4Lean.Flocq.Core.Float_prop
import CompCert4Lean.Flocq.Core.Round_pred

/-!
# Generic floating-point formats

This module carries the executable surfaces selected from
`Flocq.Core.Generic_fmt`.  Proof-bearing declarations are represented by
source-named proposition descriptors for the later proof phase.  Source global
rounding instances use an explicit certificate boundary below: the certificate
records the exact source proposition without fabricating its proof term.
-/

namespace CompCert4Lean.Flocq.Core.Generic_fmt

open CompCert4Lean.Flocq.Core

abbrev R := Raux.R
abbrev Z := Raux.Z
abbrev radix := Raux.radix
abbrev positive := Raux.positive
abbrev comparison := Raux.comparison
abbrev float := Defs.float
abbrev Float (beta : radix) (m e : Z) : float beta := Defs.float.mk m e
abbrev Fnum {beta : radix} (f : float beta) : Z := Defs.Fnum f
abbrev Fexp {beta : radix} (f : float beta) : Z := Defs.Fexp f
abbrev F2R {beta : radix} (f : float beta) : R := Defs.F2R f

abbrev Z0 : Z := Zaux.Z0
abbrev Zone : Z := Zaux.Zone
abbrev Zadd := Zaux.Zadd
abbrev Zsub := Zaux.Zsub
abbrev Zmul := Zaux.Zmul
abbrev Zopp := Zaux.Zopp
abbrev Zabs := Zaux.Zabs
abbrev Zle := Zaux.Zle
abbrev Zlt := Zaux.Zlt
abbrev Zle_bool := Zaux.Zle_bool
abbrev Zlt_bool := Zaux.Zlt_bool
abbrev IZR := Raux.IZR
abbrev R0 : R := Raux.R0
abbrev Rone : R := Raux.Rone
abbrev Rtwo : R := Raux.Rtwo
abbrev Ropp := Raux.Ropp
abbrev Rplus := Raux.Rplus
abbrev Rminus := Raux.Rminus
abbrev Rmult := Raux.Rmult
abbrev Rdiv := Raux.Rdiv
abbrev Rabs := Raux.Rabs
abbrev Rmin := Raux.Rmin
abbrev Rlt := Raux.Rlt
abbrev Rle := Raux.Rle
abbrev Rcompare := Raux.Rcompare
abbrev Rcompare_prop := Raux.Rcompare_prop
abbrev bpow := Raux.bpow
abbrev mag := Raux.mag
abbrev Zfloor := Raux.Zfloor
abbrev Zceil := Raux.Zceil
abbrev Ztrunc := Raux.Ztrunc
abbrev Zaway := Raux.Zaway
abbrev Znearest_choice := Zaux.Zle_bool
abbrev Rnd_DN_pt := Defs.Rnd_DN_pt
abbrev Rnd_UP_pt := Defs.Rnd_UP_pt
abbrev Rnd_N_pt := Defs.Rnd_N_pt
abbrev satisfies_any := Round_pred.satisfies_any

class Valid_exp (fexp : Z → Z) : Prop where
  valid_exp : ∀ k : Z,
    (Zlt (fexp k) k → Zle (fexp (Zadd k Zone)) k) ∧
      (Zle k (fexp k) →
        Zle (fexp (Zadd (fexp k) Zone)) (fexp k) ∧
          ∀ l : Z, Zle l (fexp k) → fexp l = fexp k)

abbrev valid_exp (fexp : Z → Z) [h : Valid_exp fexp] := h.valid_exp

def cexp (beta : radix) (fexp : Z → Z) (x : R) : Z :=
  fexp (mag beta x)

def canonical (beta : radix) (fexp : Z → Z) (f : float beta) : Prop :=
  Fexp f = cexp beta fexp (F2R f)

def scaled_mantissa (beta : radix) (fexp : Z → Z) (x : R) : R :=
  Rmult x (bpow beta (Zopp (cexp beta fexp x)))

def generic_format (beta : radix) (fexp : Z → Z) (x : R) : Prop :=
  x = F2R (Float beta (Ztrunc (scaled_mantissa beta fexp x)) (cexp beta fexp x))

class Valid_rnd (rnd : R → Z) : Prop where
  Zrnd_le : ∀ x y : R, Rle x y → Zle (rnd x) (rnd y)
  Zrnd_IZR : ∀ n : Z, rnd (IZR n) = n

abbrev Zrnd_le (rnd : R → Z) [h : Valid_rnd rnd] := h.Zrnd_le
abbrev Zrnd_IZR (rnd : R → Z) [h : Valid_rnd rnd] := h.Zrnd_IZR

def round (beta : radix) (fexp : Z → Z) (rnd : R → Z) (x : R) : R :=
  F2R (Float beta (rnd (scaled_mantissa beta fexp x)) (cexp beta fexp x))

def Zrnd_opp (rnd : R → Z) (x : R) : Z := Zopp (rnd (Ropp x))

class Monotone_exp (fexp : Z → Z) : Prop where
  monotone_exp : ∀ ex ey : Z, Zle ex ey → Zle (fexp ex) (fexp ey)

abbrev monotone_exp (fexp : Z → Z) [h : Monotone_exp fexp] := h.monotone_exp

def Znearest (choice : Z → Bool) (x : R) : Z :=
  match Rcompare (Rminus x (IZR (Zfloor x))) (Rdiv Rone Rtwo) with
  | .Lt => Zfloor x
  | .Eq => if choice (Zfloor x) then Zceil x else Zfloor x
  | .Gt => Zceil x

abbrev ZnearestA (x : R) : Z := Znearest (fun m => Zle_bool Z0 m) x

class Valid_rnd_Certificate : Prop where
  nearest : ∀ choice : Z → Bool, Valid_rnd (Znearest choice)
  down : Valid_rnd Zfloor

/-! Theorem-facing surfaces use the canonical exact-real provider.  The
    executable definitions and classes above intentionally remain on the
    checked runtime carrier. -/
abbrev ExactRealContext := Raux.ExactRealContext

namespace Exact

abbrev Context := ExactRealContext
abbrev Magnitude (ctx : Context) := Raux.Exact.Magnitude ctx
abbrev R (ctx : Context) := Defs.Exact.R ctx
abbrev Valid_exp (fexp : Z → Z) := CompCert4Lean.Flocq.Core.Generic_fmt.Valid_exp fexp
abbrev IZR (ctx : Context) := Raux.Exact.IZR ctx
abbrev R0 (ctx : Context) := Raux.Exact.R0 ctx
abbrev Rone (ctx : Context) := Raux.Exact.Rone ctx
abbrev Rtwo (ctx : Context) := Raux.Exact.Rtwo ctx
abbrev Ropp (ctx : Context) := Raux.Exact.Ropp ctx
abbrev Rplus (ctx : Context) := Raux.Exact.Rplus ctx
abbrev Rminus (ctx : Context) := Raux.Exact.Rminus ctx
abbrev Rmult (ctx : Context) := Raux.Exact.Rmult ctx
abbrev Rdiv (ctx : Context) := Raux.Exact.Rdiv ctx
abbrev Rabs (ctx : Context) := Raux.Exact.Rabs ctx
abbrev Rlt (ctx : Context) := Raux.Exact.Rlt ctx
abbrev Rle (ctx : Context) := Raux.Exact.Rle ctx
noncomputable abbrev Rcompare (ctx : Context) := Raux.Exact.Rcompare ctx
abbrev Zfloor (ctx : Context) := Raux.Exact.Zfloor ctx
abbrev Zceil (ctx : Context) := Raux.Exact.Zceil ctx
noncomputable abbrev Ztrunc (ctx : Context) := Raux.Exact.Ztrunc ctx
noncomputable abbrev Zaway (ctx : Context) := Raux.Exact.Zaway ctx
abbrev bpow (ctx : Context) := Raux.Exact.bpow ctx
abbrev F2R (ctx : Context) {beta : radix} (f : float beta) : R ctx :=
  Defs.Exact.F2R ctx f
abbrev mag (magnitude : Magnitude ctx) (beta : radix) (x : R ctx) : Z :=
  (Raux.Exact.mag magnitude beta x).mag_val

def cexp (ctx : Context) (magnitude : Magnitude ctx) (beta : radix)
    (fexp : Z → Z) (x : R ctx) : Z :=
  fexp (mag magnitude beta x)

def canonical (ctx : Context) (magnitude : Magnitude ctx) (beta : radix)
    (fexp : Z → Z) (f : float beta) : Prop :=
  Fexp f = cexp ctx magnitude beta fexp (F2R ctx f)

def scaled_mantissa (ctx : Context) (magnitude : Magnitude ctx) (beta : radix)
    (fexp : Z → Z) (x : R ctx) : R ctx :=
  Rmult ctx x (bpow ctx beta (Zopp (cexp ctx magnitude beta fexp x)))

noncomputable def generic_format (ctx : Context) (magnitude : Magnitude ctx) (beta : radix)
    (fexp : Z → Z) (x : R ctx) : Prop :=
  x = F2R ctx (Float beta (Ztrunc ctx (scaled_mantissa ctx magnitude beta fexp x))
    (cexp ctx magnitude beta fexp x))

class Valid_rnd (ctx : Context) (rnd : R ctx → Z) : Prop where
  Zrnd_le : ∀ x y : R ctx, Rle ctx x y → Zle (rnd x) (rnd y)
  Zrnd_IZR : ∀ n : Z, rnd (IZR ctx n) = n

def round (ctx : Context) (magnitude : Magnitude ctx) (beta : radix)
    (fexp : Z → Z) (rnd : R ctx → Z) (x : R ctx) : R ctx :=
  F2R ctx (Float beta (rnd (scaled_mantissa ctx magnitude beta fexp x))
    (cexp ctx magnitude beta fexp x))

noncomputable def Znearest (ctx : Context) (choice : Z → Bool) (x : R ctx) : Z :=
  match Rcompare ctx (Rminus ctx x (IZR ctx (Zfloor ctx x)))
      (Rdiv ctx (Rone ctx) (Rtwo ctx)) with
  | .Lt => Zfloor ctx x
  | .Eq => if choice (Zfloor ctx x) then Zceil ctx x else Zfloor ctx x
  | .Gt => Zceil ctx x

def Zrnd_opp (ctx : Context) (rnd : R ctx → Z) (x : R ctx) : Z :=
  Zopp (rnd (Ropp ctx x))

end Exact

def valid_rnd_NStatement (ctx : ExactRealContext) : Prop :=
  ∀ choice : Z → Bool, Exact.Valid_rnd ctx (Exact.Znearest ctx choice)

def valid_rnd_DNStatement (ctx : ExactRealContext) : Prop :=
  Exact.Valid_rnd ctx (Exact.Zfloor ctx)

/- The proof phase constructs the mandatory certificate.  These adapters then
   restore the source Global Instance results without a hidden or fabricated
   inhabitant. -/
instance valid_rnd_N [certificate : Valid_rnd_Certificate]
    (choice : Z → Bool) : Valid_rnd (Znearest choice) :=
  certificate.nearest choice

instance valid_rnd_DN [certificate : Valid_rnd_Certificate] : Valid_rnd Zfloor :=
  certificate.down

/-! Generated and directly implemented surfaces. -/

def Znearest_DN_or_UPStatement (ctx : ExactRealContext) : Prop :=
  ∀ choice x, Exact.Znearest ctx choice x = Exact.Zfloor ctx x ∨ Exact.Znearest ctx choice x = Exact.Zceil ctx x

def Znearest_ge_floorStatement (ctx : ExactRealContext) : Prop :=
  ∀ choice x, Zle (Exact.Zfloor ctx x) (Exact.Znearest ctx choice x)

def Znearest_le_ceilStatement (ctx : ExactRealContext) : Prop :=
  ∀ choice x, Zle (Exact.Znearest ctx choice x) (Exact.Zceil ctx x)

def Znearest_oppStatement (ctx : ExactRealContext) : Prop :=
  ∀ choice x,
    Exact.Znearest ctx choice (Exact.Ropp ctx x) =
      Zopp (Exact.Znearest ctx (fun t => Bool.not (choice (Zopp (Zadd t Zone)))) x)

def Zrnd_DN_or_UPStatement (ctx : ExactRealContext) : Prop :=
  ∀ rnd, Exact.Valid_rnd ctx rnd → ∀ x, rnd x = Exact.Zfloor ctx x ∨ rnd x = Exact.Zceil ctx x

def Zrnd_ZR_or_AWStatement (ctx : ExactRealContext) : Prop :=
  ∀ rnd, Exact.Valid_rnd ctx rnd → ∀ x, rnd x = Exact.Ztrunc ctx x ∨ rnd x = Exact.Zaway ctx x

def canonical_uniqueStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp f1 f2,
    Exact.canonical ctx magnitude beta fexp f1 → Exact.canonical ctx magnitude beta fexp f2 →
      Exact.F2R ctx f1 = Exact.F2R ctx f2 → f1 = f2

def cexp_absStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp x, Exact.cexp ctx magnitude beta fexp (Exact.Rabs ctx x) = Exact.cexp ctx magnitude beta fexp x

def cexp_fexpStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp x ex,
    (Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone)) (Exact.Rabs ctx x) ∧ Exact.Rlt ctx (Exact.Rabs ctx x) (Exact.bpow ctx beta ex)) →
      Exact.cexp ctx magnitude beta fexp x = fexp ex

def cexp_fexp_posStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp x ex,
    (Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone)) x ∧ Exact.Rlt ctx x (Exact.bpow ctx beta ex)) →
      Exact.cexp ctx magnitude beta fexp x = fexp ex

def cexp_oppStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp x, Exact.cexp ctx magnitude beta fexp (Exact.Ropp ctx x) = Exact.cexp ctx magnitude beta fexp x

def cexp_round_geStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → Monotone_exp fexp →
    ∀ rnd, Exact.Valid_rnd ctx rnd →
    ∀ x, Exact.round ctx magnitude beta fexp rnd x ≠ Exact.R0 ctx →
      Zle (Exact.cexp ctx magnitude beta fexp x) (Exact.cexp ctx magnitude beta fexp (Exact.round ctx magnitude beta fexp rnd x))

def generic_format_0Statement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Exact.generic_format ctx magnitude beta fexp (Exact.R0 ctx)

def generic_format_EMStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ x, Exact.generic_format ctx magnitude beta fexp x ∨ ¬ Exact.generic_format ctx magnitude beta fexp x

def generic_format_F2RStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp m e,
    (m ≠ Z0 → Zle (Exact.cexp ctx magnitude beta fexp (Exact.F2R ctx (Float beta m e))) e) →
      Exact.generic_format ctx magnitude beta fexp (Exact.F2R ctx (Float beta m e))

def generic_format_absStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp x, Exact.generic_format ctx magnitude beta fexp x → Exact.generic_format ctx magnitude beta fexp (Exact.Rabs ctx x)

def generic_format_abs_invStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp x, Exact.generic_format ctx magnitude beta fexp (Exact.Rabs ctx x) → Exact.generic_format ctx magnitude beta fexp x

def generic_format_bpowStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp e, Zle (fexp (Zadd e Zone)) e → Exact.generic_format ctx magnitude beta fexp (Exact.bpow ctx beta e)

def generic_format_bpow'Statement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ e, Zle (fexp e) e → Exact.generic_format ctx magnitude beta fexp (Exact.bpow ctx beta e)

def generic_format_bpow_invStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ e, Exact.generic_format ctx magnitude beta fexp (Exact.bpow ctx beta e) → Zle (fexp e) e

def generic_format_bpow_inv'Statement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp e, Exact.generic_format ctx magnitude beta fexp (Exact.bpow ctx beta e) → Zle (fexp (Zadd e Zone)) e

def generic_format_canonicalStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp f, Exact.canonical ctx magnitude beta fexp f → Exact.generic_format ctx magnitude beta fexp (Exact.F2R ctx f)

def generic_format_ge_bpowStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp emin, (∀ e, Zle emin (fexp e)) → ∀ x, Exact.Rlt ctx (Exact.R0 ctx) x → Exact.generic_format ctx magnitude beta fexp x → Exact.Rle ctx (Exact.bpow ctx beta emin) x

def generic_format_oppStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp x, Exact.generic_format ctx magnitude beta fexp x → Exact.generic_format ctx magnitude beta fexp (Exact.Ropp ctx x)

def generic_format_roundStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ rnd, Exact.Valid_rnd ctx rnd → ∀ x, Exact.generic_format ctx magnitude beta fexp (Exact.round ctx magnitude beta fexp rnd x)

def generic_format_round_posStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ rnd, Exact.Valid_rnd ctx rnd → ∀ x, Exact.Rlt ctx (Exact.R0 ctx) x → Exact.generic_format ctx magnitude beta fexp (Exact.round ctx magnitude beta fexp rnd x)

def generic_inclusionStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp1 fexp2, Valid_exp fexp1 → Valid_exp fexp2 → ∀ e, Zle (fexp2 e) (fexp1 e) → ∀ x,
    (Exact.Rle ctx (Exact.bpow ctx beta (Zsub e Zone)) (Exact.Rabs ctx x) ∧ Exact.Rle ctx (Exact.Rabs ctx x) (Exact.bpow ctx beta e)) →
      Exact.generic_format ctx magnitude beta fexp1 x → Exact.generic_format ctx magnitude beta fexp2 x

def generic_inclusion_leStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp1 fexp2, Valid_exp fexp1 → Valid_exp fexp2 → ∀ e2, (∀ e, Zle e e2 → Zle (fexp2 e) (fexp1 e)) → ∀ x,
    Exact.Rle ctx (Exact.Rabs ctx x) (Exact.bpow ctx beta e2) → Exact.generic_format ctx magnitude beta fexp1 x → Exact.generic_format ctx magnitude beta fexp2 x

def generic_inclusion_magStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp1 fexp2 x, (x ≠ Exact.R0 ctx → Zle (fexp2 (Exact.mag magnitude beta x)) (fexp1 (Exact.mag magnitude beta x))) →
    Exact.generic_format ctx magnitude beta fexp1 x → Exact.generic_format ctx magnitude beta fexp2 x

def lt_cexp_posStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Monotone_exp fexp → ∀ x y, Exact.Rlt ctx (Exact.R0 ctx) y → Zlt (Exact.cexp ctx magnitude beta fexp x) (Exact.cexp ctx magnitude beta fexp y) → Exact.Rlt ctx x y

def mag_generic_gtStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ x, x ≠ Exact.R0 ctx → Exact.generic_format ctx magnitude beta fexp x → Zlt (Exact.cexp ctx magnitude beta fexp x) (Exact.mag magnitude beta x)

def mag_round_ZRStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ x, Exact.round ctx magnitude beta fexp (Exact.Ztrunc ctx) x ≠ Exact.R0 ctx → Exact.mag magnitude beta (Exact.round ctx magnitude beta fexp (Exact.Ztrunc ctx) x) = Exact.mag magnitude beta x

def mag_round_geStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ rnd, Exact.Valid_rnd ctx rnd → ∀ x, Exact.round ctx magnitude beta fexp rnd x ≠ Exact.R0 ctx → Zle (Exact.mag magnitude beta x) (Exact.mag magnitude beta (Exact.round ctx magnitude beta fexp rnd x))

def mantissa_small_posStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) x ex, (Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone)) x ∧ Exact.Rlt ctx x (Exact.bpow ctx beta ex)) → Zle ex (fexp ex) →
    Exact.Rlt ctx (Exact.R0 ctx) (Exact.Rmult ctx x (Exact.bpow ctx beta (Zopp (fexp ex)))) ∧ Exact.Rlt ctx (Exact.Rmult ctx x (Exact.bpow ctx beta (Zopp (fexp ex)))) (Exact.IZR ctx Zone)

def round_0Statement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp rnd, Exact.Valid_rnd ctx rnd → Exact.round ctx magnitude beta fexp rnd (Exact.R0 ctx) = Exact.R0 ctx

def round_AW_UPStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp x, Exact.Rle ctx (Exact.R0 ctx) x → Exact.round ctx magnitude beta fexp (Exact.Zaway ctx) x = Exact.round ctx magnitude beta fexp (Exact.Zceil ctx) x

def round_AW_absStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ x, Exact.round ctx magnitude beta fexp (Exact.Zaway ctx) (Exact.Rabs ctx x) = Exact.Rabs ctx (Exact.round ctx magnitude beta fexp (Exact.Zaway ctx) x)

def round_AW_oppStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp x, Exact.round ctx magnitude beta fexp (Exact.Zaway ctx) (Exact.Ropp ctx x) = Exact.Ropp ctx (Exact.round ctx magnitude beta fexp (Exact.Zaway ctx) x)

def round_DN_oppStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp x, Exact.round ctx magnitude beta fexp (Exact.Zfloor ctx) (Exact.Ropp ctx x) = Exact.Ropp ctx (Exact.round ctx magnitude beta fexp (Exact.Zceil ctx) x)

def round_DN_or_UPStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp rnd, Exact.Valid_rnd ctx rnd → ∀ x, Exact.round ctx magnitude beta fexp rnd x = Exact.round ctx magnitude beta fexp (Exact.Zfloor ctx) x ∨ Exact.round ctx magnitude beta fexp rnd x = Exact.round ctx magnitude beta fexp (Exact.Zceil ctx) x

def round_DN_ptStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ x, Defs.Exact.Rnd_DN_pt ctx (Exact.generic_format ctx magnitude beta fexp) x (Exact.round ctx magnitude beta fexp (Exact.Zfloor ctx) x)

def round_UP_oppStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp x, Exact.round ctx magnitude beta fexp (Exact.Zceil ctx) (Exact.Ropp ctx x) = Exact.Ropp ctx (Exact.round ctx magnitude beta fexp (Exact.Zfloor ctx) x)

def round_UP_ptStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ x, Defs.Exact.Rnd_UP_pt ctx (Exact.generic_format ctx magnitude beta fexp) x (Exact.round ctx magnitude beta fexp (Exact.Zceil ctx) x)

def round_ZR_DNStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp x, Exact.Rle ctx (Exact.R0 ctx) x → Exact.round ctx magnitude beta fexp (Exact.Ztrunc ctx) x = Exact.round ctx magnitude beta fexp (Exact.Zfloor ctx) x

def round_ZR_absStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ x, Exact.round ctx magnitude beta fexp (Exact.Ztrunc ctx) (Exact.Rabs ctx x) = Exact.Rabs ctx (Exact.round ctx magnitude beta fexp (Exact.Ztrunc ctx) x)

def round_ZR_oppStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp x, Exact.round ctx magnitude beta fexp (Exact.Ztrunc ctx) (Exact.Ropp ctx x) = Exact.Ropp ctx (Exact.round ctx magnitude beta fexp (Exact.Ztrunc ctx) x)

def round_ZR_or_AWStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp rnd, Exact.Valid_rnd ctx rnd → ∀ x, Exact.round ctx magnitude beta fexp rnd x = Exact.round ctx magnitude beta fexp (Exact.Ztrunc ctx) x ∨ Exact.round ctx magnitude beta fexp rnd x = Exact.round ctx magnitude beta fexp (Exact.Zaway ctx) x

def round_bounded_large_posStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp rnd, Exact.Valid_rnd ctx rnd → ∀ x ex, Zlt (fexp ex) ex → (Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone)) x ∧ Exact.Rlt ctx x (Exact.bpow ctx beta ex)) →
    Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone)) (Exact.round ctx magnitude beta fexp rnd x) ∧ Exact.Rle ctx (Exact.round ctx magnitude beta fexp rnd x) (Exact.bpow ctx beta ex)

def round_bounded_small_posStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp rnd, Exact.Valid_rnd ctx rnd → ∀ x ex, Zle ex (fexp ex) → (Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone)) x ∧ Exact.Rlt ctx x (Exact.bpow ctx beta ex)) →
    Exact.round ctx magnitude beta fexp rnd x = Exact.R0 ctx ∨ Exact.round ctx magnitude beta fexp rnd x = Exact.bpow ctx beta (fexp ex)

def round_ge_genericStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ rnd, Exact.Valid_rnd ctx rnd → ∀ x y, Exact.generic_format ctx magnitude beta fexp x → Exact.Rle ctx x y → Exact.Rle ctx x (Exact.round ctx magnitude beta fexp rnd y)

def round_genericStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp rnd, Exact.Valid_rnd ctx rnd → ∀ x, Exact.generic_format ctx magnitude beta fexp x → Exact.round ctx magnitude beta fexp rnd x = x

def round_large_pos_ge_bpowStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp rnd, Exact.Valid_rnd ctx rnd → ∀ x e, Exact.Rlt ctx (Exact.R0 ctx) (Exact.round ctx magnitude beta fexp rnd x) → Exact.Rle ctx (Exact.bpow ctx beta e) x → Exact.Rle ctx (Exact.bpow ctx beta e) (Exact.round ctx magnitude beta fexp rnd x)

def round_leStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ rnd, Exact.Valid_rnd ctx rnd → ∀ x y, Exact.Rle ctx x y → Exact.Rle ctx (Exact.round ctx magnitude beta fexp rnd x) (Exact.round ctx magnitude beta fexp rnd y)

def round_le_genericStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ rnd, Exact.Valid_rnd ctx rnd → ∀ x y, Exact.generic_format ctx magnitude beta fexp y → Exact.Rle ctx x y → Exact.Rle ctx (Exact.round ctx magnitude beta fexp rnd x) y

def round_le_posStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ rnd, Exact.Valid_rnd ctx rnd → ∀ x y, Exact.Rlt ctx (Exact.R0 ctx) x → Exact.Rle ctx x y → Exact.Rle ctx (Exact.round ctx magnitude beta fexp rnd x) (Exact.round ctx magnitude beta fexp rnd y)

def scaled_mantissa_0Statement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Exact.scaled_mantissa ctx magnitude beta fexp (Exact.R0 ctx) = Exact.R0 ctx

def scaled_mantissa_absStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp x, Exact.scaled_mantissa ctx magnitude beta fexp (Exact.Rabs ctx x) = Exact.Rabs ctx (Exact.scaled_mantissa ctx magnitude beta fexp x)

def scaled_mantissa_genericStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp x, Exact.generic_format ctx magnitude beta fexp x → Exact.scaled_mantissa ctx magnitude beta fexp x = Exact.IZR ctx (Exact.Ztrunc ctx (Exact.scaled_mantissa ctx magnitude beta fexp x))

def scaled_mantissa_lt_1Statement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ x ex, Exact.Rlt ctx (Exact.Rabs ctx x) (Exact.bpow ctx beta ex) → Zle ex (fexp ex) → Exact.Rlt ctx (Exact.Rabs ctx (Exact.scaled_mantissa ctx magnitude beta fexp x)) (Exact.IZR ctx Zone)

def scaled_mantissa_mult_bpowStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp x, Exact.Rmult ctx (Exact.scaled_mantissa ctx magnitude beta fexp x) (Exact.bpow ctx beta (Exact.cexp ctx magnitude beta fexp x)) = x

def scaled_mantissa_oppStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp x, Exact.scaled_mantissa ctx magnitude beta fexp (Exact.Ropp ctx x) = Exact.Ropp ctx (Exact.scaled_mantissa ctx magnitude beta fexp x)

def valid_exp_large'Statement : Prop :=
  ∀ fexp, Valid_exp fexp → ∀ k l, Zlt (fexp k) k → Zle l k → Zlt (fexp l) k

def abs_round_ge_genericStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ rnd, Exact.Valid_rnd ctx rnd → ∀ x y, Exact.generic_format ctx magnitude beta fexp x → Exact.Rle ctx x (Exact.Rabs ctx y) → Exact.Rle ctx x (Exact.Rabs ctx (Exact.round ctx magnitude beta fexp rnd y))

def abs_round_le_genericStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ rnd, Exact.Valid_rnd ctx rnd → ∀ x y, Exact.generic_format ctx magnitude beta fexp y → Exact.Rle ctx (Exact.Rabs ctx x) y → Exact.Rle ctx (Exact.Rabs ctx (Exact.round ctx magnitude beta fexp rnd x)) y

def canonical_0Statement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Exact.canonical ctx magnitude beta fexp (Float beta Z0 (Exact.cexp ctx magnitude beta fexp (Exact.R0 ctx)))

def canonical_absStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp m e, Exact.canonical ctx magnitude beta fexp (Float beta m e) → Exact.canonical ctx magnitude beta fexp (Float beta (Zabs m) e)

def canonical_generic_formatStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp x, Exact.generic_format ctx magnitude beta fexp x → ∃ f : float beta, x = Exact.F2R ctx f ∧ Exact.canonical ctx magnitude beta fexp f

def canonical_oppStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp m e, Exact.canonical ctx magnitude beta fexp (Float beta m e) → Exact.canonical ctx magnitude beta fexp (Float beta (Zopp m) e)

def cexp_DNStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ x, Exact.Rlt ctx (Exact.R0 ctx) (Exact.round ctx magnitude beta fexp (Exact.Zfloor ctx) x) → Exact.cexp ctx magnitude beta fexp (Exact.round ctx magnitude beta fexp (Exact.Zfloor ctx) x) = Exact.cexp ctx magnitude beta fexp x

def exp_small_round_0Statement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ rnd, Exact.Valid_rnd ctx rnd → ∀ x ex, (Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone)) (Exact.Rabs ctx x) ∧ Exact.Rlt ctx (Exact.Rabs ctx x) (Exact.bpow ctx beta ex)) → Exact.round ctx magnitude beta fexp rnd x = Exact.R0 ctx → Zle ex (fexp ex)

def exp_small_round_0_posStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, ∀ rnd, Exact.Valid_rnd ctx rnd → ∀ x ex, (Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone)) x ∧ Exact.Rlt ctx x (Exact.bpow ctx beta ex)) → Exact.round ctx magnitude beta fexp rnd x = Exact.R0 ctx → Zle ex (fexp ex)

def generic_format_F2R'Statement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, ∀ (x : Exact.R ctx) (f : float beta), Exact.F2R ctx f = x → (x ≠ Exact.R0 ctx → Zle (Exact.cexp ctx magnitude beta fexp x) (Fexp f)) → Exact.generic_format ctx magnitude beta fexp x

def generic_format_satisfies_anyStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → Round_pred.satisfies_any ctx (Exact.generic_format ctx magnitude beta fexp)

def mag_DNStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ x, Exact.Rlt ctx (Exact.R0 ctx) (Exact.round ctx magnitude beta fexp (Exact.Zfloor ctx) x) → Exact.mag magnitude beta (Exact.round ctx magnitude beta fexp (Exact.Zfloor ctx) x) = Exact.mag magnitude beta x

def mantissa_DN_small_posStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) x ex, (Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone)) x ∧ Exact.Rlt ctx x (Exact.bpow ctx beta ex)) → Zle ex (fexp ex) → Exact.Zfloor ctx (Exact.Rmult ctx x (Exact.bpow ctx beta (Zopp (fexp ex)))) = Z0

def mantissa_UP_small_posStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) x ex, (Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone)) x ∧ Exact.Rlt ctx x (Exact.bpow ctx beta ex)) → Zle ex (fexp ex) → Exact.Zceil ctx (Exact.Rmult ctx x (Exact.bpow ctx beta (Zopp (fexp ex)))) = Zone

def round_DN_UP_ltStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ x, ¬ Exact.generic_format ctx magnitude beta fexp x → Exact.Rlt ctx (Exact.round ctx magnitude beta fexp (Exact.Zfloor ctx) x) x ∧ Exact.Rlt ctx x (Exact.round ctx magnitude beta fexp (Exact.Zceil ctx) x)

def round_DN_small_posStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp x ex, (Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone)) x ∧ Exact.Rlt ctx x (Exact.bpow ctx beta ex)) → Zle ex (fexp ex) → Exact.round ctx magnitude beta fexp (Exact.Zfloor ctx) x = Exact.R0 ctx

def round_N_oppStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp choice, ∀ x, Exact.round ctx magnitude beta fexp (Exact.Znearest ctx choice) (Exact.Ropp ctx x) = Exact.Ropp ctx (Exact.round ctx magnitude beta fexp (Exact.Znearest ctx (fun t => Bool.not (choice (Zopp (Zadd t Zone))))) x)

def round_N_ptStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ choice x, Defs.Exact.Rnd_N_pt ctx (Exact.generic_format ctx magnitude beta fexp) x (Exact.round ctx magnitude beta fexp (Exact.Znearest ctx choice) x)

def round_UP_small_posStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp x ex, (Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone)) x ∧ Exact.Rlt ctx x (Exact.bpow ctx beta ex)) → Zle ex (fexp ex) → Exact.round ctx magnitude beta fexp (Exact.Zceil ctx) x = Exact.bpow ctx beta (fexp ex)

def round_abs_absStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ (P : Exact.R ctx → Exact.R ctx → Prop), (∀ rnd, Exact.Valid_rnd ctx rnd → ∀ x, Exact.Rle ctx (Exact.R0 ctx) x → P x (Exact.round ctx magnitude beta fexp rnd x)) → ∀ rnd, Exact.Valid_rnd ctx rnd → ∀ x, P (Exact.Rabs ctx x) (Exact.Rabs ctx (Exact.round ctx magnitude beta fexp rnd x))

def round_oppStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ beta fexp rnd x, Exact.round ctx magnitude beta fexp rnd (Exact.Ropp ctx x) = Exact.Ropp ctx (Exact.round ctx magnitude beta fexp (Exact.Zrnd_opp ctx rnd) x)

end CompCert4Lean.Flocq.Core.Generic_fmt

namespace CompCert4Lean.Flocq.Core.Generic_fmt

theorem valid_exp_large' : valid_exp_large'Statement := by
  intro fexp hvalid k l hfk h_lk
  apply Int.lt_of_not_ge
  intro hnot
  have hkl : Zle l (fexp l) := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ l ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp l)
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ l ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k at h_lk
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp l) at hnot
    exact Int.le_trans h_lk hnot
  have heq : fexp k = fexp l := (hvalid.valid_exp l).2 hkl |>.2 k hnot
  have hflk : Zlt (fexp l) k := by simpa [heq] using hfk
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp l) at hnot
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp l) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k at hflk
  exact (Int.not_lt_of_ge hnot) hflk

end CompCert4Lean.Flocq.Core.Generic_fmt
