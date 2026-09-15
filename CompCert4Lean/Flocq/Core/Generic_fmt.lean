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

namespace CompCert4Lean.Flocq.Core.Generic_fmt

theorem canonical_generic_format : ∀ ctx magnitude, canonical_generic_formatStatement ctx magnitude := by
  intro ctx magnitude beta fexp x hx
  unfold Exact.generic_format at hx
  refine ⟨Float beta (Exact.Ztrunc ctx (Exact.scaled_mantissa ctx magnitude beta fexp x))
    (Exact.cexp ctx magnitude beta fexp x), ?_, ?_⟩
  · exact hx
  · unfold Exact.canonical
    rw [← hx]
    rfl

end CompCert4Lean.Flocq.Core.Generic_fmt

namespace CompCert4Lean.Flocq.Core.Generic_fmt

theorem canonical_0 : ∀ ctx magnitude, canonical_0Statement ctx magnitude := by
  intro ctx magnitude beta fexp
  unfold Exact.canonical
  change Exact.cexp ctx magnitude beta fexp (Exact.R0 ctx) =
    Exact.cexp ctx magnitude beta fexp (Exact.F2R ctx (Float beta Z0
      (Exact.cexp ctx magnitude beta fexp (Exact.R0 ctx))))
  have hzero := CompCert4Lean.Flocq.Core.Float_prop.F2R_0 ctx beta
    (Exact.cexp ctx magnitude beta fexp (Exact.R0 ctx))
  exact congrArg (Exact.cexp ctx magnitude beta fexp) hzero.symm

end CompCert4Lean.Flocq.Core.Generic_fmt

namespace CompCert4Lean.Flocq.Core.Generic_fmt

private abbrev Zpos := CompCert4Lean.Flocq.Core.Raux.Zpos
private abbrev Zneg := CompCert4Lean.Flocq.Core.Raux.Zneg
private abbrev xH := CompCert4Lean.Flocq.Core.Raux.xH
private abbrev Zpower_pos := CompCert4Lean.Flocq.Core.Raux.Zpower_pos

private theorem pg_zero_lt_one (ctx : ExactRealContext) :
    ctx.spec.lt ctx.spec.zero ctx.spec.one := by
  have hz : ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ (ctx.spec.up ctx.spec.zero)) := by
    simpa [CompCert4Lean.Foundation.FlocqReal.ExactReal.R0] using
      ctx.certificate.sourceLaws.up_gt ctx.spec.zero
  have hg := ctx.certificate.sourceLaws.up_gap ctx.spec.zero
  have hneg0 : ctx.spec.neg ctx.spec.zero = ctx.spec.zero := by
    calc
      ctx.spec.neg ctx.spec.zero =
          ctx.spec.add (ctx.spec.neg ctx.spec.zero) ctx.spec.zero :=
        (ctx.certificate.orderedField.add_zero _).symm
      _ = ctx.spec.zero := ctx.certificate.orderedField.neg_add_cancel _
  have hz0 : ctx.spec.add (ctx.spec.ofZ (ctx.spec.up ctx.spec.zero))
      (ctx.spec.neg ctx.spec.zero) = ctx.spec.ofZ (ctx.spec.up ctx.spec.zero) := by
    rw [hneg0, ctx.certificate.orderedField.add_zero]
  have hg' : ctx.spec.le (ctx.spec.ofZ (ctx.spec.up ctx.spec.zero)) ctx.spec.one := by
    rw [← hz0, ← ctx.certificate.sourceLaws.ofZ_one]
    exact hg
  apply (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
  constructor
  · have hzle := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hz
    exact ctx.certificate.orderedField.le_trans _ _ _ hzle.1 hg'
  · intro h10
    have hzle := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hz
    exact hzle.2 (ctx.certificate.orderedField.le_trans _ _ _ hg' h10)

private theorem pg_ofZ_pos (ctx : ExactRealContext) (p : positive) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ (Zpos p)) := by
  induction p with
  | xH =>
      rw [ctx.certificate.sourceLaws.ofZ_one]
      exact pg_zero_lt_one ctx
  | xO p ih =>
      have heq : Zadd (Zpos p) (Zpos p) =
          Zpos (CompCert4Lean.Foundation.Numbers.Rocq.Coq.xO p) := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) +
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p))) =
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zpos (CompCert4Lean.Foundation.Numbers.Rocq.Coq.xO p))
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        change Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) +
            Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) =
          Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.xO p))
        rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.xO p) =
              2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p by rfl]
        simp only [Int.ofNat_eq_coe]
        omega
      rw [← heq, ctx.certificate.sourceLaws.ofZ_add]
      have h := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.ofZ (Zpos p)) ctx.spec.zero (ctx.spec.ofZ (Zpos p)) ih
      rw [ctx.certificate.orderedField.add_zero] at h
      exact ctx.certificate.orderedField.lt_trans _ _ _ ih h
  | xI p ih =>
      have heq : Zadd (Zadd (Zpos p) (Zpos p)) (Zpos xH) =
          Zpos (CompCert4Lean.Foundation.Numbers.Rocq.Coq.xI p) := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                  (Zadd (Zpos p) (Zpos p)) +
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos xH))) =
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zpos (CompCert4Lean.Foundation.Numbers.Rocq.Coq.xI p))
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add]
        change Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) +
            Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) + 1 =
          Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.xI p))
        rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.xI p) =
              2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p + 1 by rfl]
        simp only [Int.ofNat_eq_coe]
        omega
      rw [← heq, ctx.certificate.sourceLaws.ofZ_add,
        ctx.certificate.sourceLaws.ofZ_add,
        ctx.certificate.sourceLaws.ofZ_one]
      have hpp := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.ofZ (Zpos p)) ctx.spec.zero (ctx.spec.ofZ (Zpos p)) ih
      rw [ctx.certificate.orderedField.add_zero] at hpp
      have hpp0 := ctx.certificate.orderedField.lt_trans _ _ _ ih hpp
      have h := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.add (ctx.spec.ofZ (Zpos p)) (ctx.spec.ofZ (Zpos p)))
        ctx.spec.zero ctx.spec.one (pg_zero_lt_one ctx)
      rw [ctx.certificate.orderedField.add_zero] at h
      exact ctx.certificate.orderedField.lt_trans _ _ _ hpp0 h

private theorem pg_ofZ_pos_of_int (ctx : ExactRealContext) (d : Z)
    (hd : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ d) := by
  cases d with
  | Z0 => change (0 : Int) < 0 at hd; omega
  | Zpos p => exact pg_ofZ_pos ctx p
  | Zneg p =>
      change (0 : Int) < -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hd
      have hp : 0 ≤ Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) := Int.ofNat_nonneg _
      omega

private theorem pg_ofZ_lt (ctx : ExactRealContext) {x y : Z}
    (hxy : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y) :
    ctx.spec.lt (ctx.spec.ofZ x) (ctx.spec.ofZ y) := by
  let d := Zsub y x
  have hsum : y = Zadd x d := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [d, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x +
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y -
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x)
    omega
  have hd : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d := by
    simp only [d, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    omega
  rw [hsum, ctx.certificate.sourceLaws.ofZ_add]
  have h := ctx.certificate.orderedField.add_lt_compat_l
    (ctx.spec.ofZ x) ctx.spec.zero (ctx.spec.ofZ d) (pg_ofZ_pos_of_int ctx d hd)
  rw [ctx.certificate.orderedField.add_zero] at h
  exact h

private theorem pg_int_pow_gt_one (a : Int) (ha : (2 : Int) ≤ a) :
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
            have hmul' : (1 : Int) * a ≤ a ^ k * a := by simpa using hmul
            have hmul'' : a ≤ a ^ k * a := by simpa only [Int.one_mul] using hmul'
            exact Int.le_trans haone hmul''
      have hpow_one : (1 : Int) ≤ a ^ n := hpow_one_all n
      rw [Int.pow_succ]
      have hmul := Int.mul_le_mul_of_nonneg_right hpow_one (Int.le_of_lt hapos)
      have haone : (1 : Int) < a := by omega
      have hmul' : (1 : Int) * a ≤ a ^ n * a := by simpa using hmul
      have hmul'' : a ≤ a ^ n * a := by simpa using hmul'
      exact Int.lt_of_lt_of_le haone hmul''

private theorem pg_bpow_pos_gt_one (ctx : ExactRealContext) (r : radix)
    {e : Z} (he : Zlt Z0 e) :
    ctx.spec.lt (ctx.spec.one) (Exact.bpow ctx r e) := by
  cases e with
  | Z0 => change (0 : Int) < 0 at he; omega
  | Zneg p =>
      change (0 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zneg p) at he
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at he
      omega
  | Zpos p =>
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpow : (1 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Zpower_pos r.radix_val p) := by
        simp only [Zpower_pos,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow_pos,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        have hr := r.radix_prop
        change (if (2 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val
          then true else false) = true at hr
        exact pg_int_pow_gt_one _ (by simpa using hr) _ hp
      have h := pg_ofZ_lt ctx (x := Zpos xH)
        (y := Zpower_pos r.radix_val p) (by
          change (1 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zpower_pos r.radix_val p)
          exact hpow)
      change ctx.spec.lt (ctx.spec.ofZ (Zpos xH))
        (ctx.spec.ofZ (Zpower_pos r.radix_val p)) at h
      rw [ctx.certificate.sourceLaws.ofZ_one] at h
      exact h

private theorem pg_zadd_sub_cancel (a b : Z) : Zadd a (Zsub b a) = b := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a +
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b -
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b
  omega

private theorem pg_bpow_lt (ctx : ExactRealContext) (r : radix)
    {e1 e2 : Z} (h : Zlt e1 e2) :
    Exact.Rlt ctx (Exact.bpow ctx r e1) (Exact.bpow ctx r e2) := by
  let d := Zsub e2 e1
  have hd : Zlt Z0 d := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d
    simp only [d, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change (0 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 -
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 at h
    omega
  have hsum : Zadd e1 d = e2 := pg_zadd_sub_cancel e1 e2
  have hmul : Exact.bpow ctx r e2 =
      ctx.spec.mul (Exact.bpow ctx r e1) (Exact.bpow ctx r d) := by
    calc
      Exact.bpow ctx r e2 = Exact.bpow ctx r (Zadd e1 d) := by rw [hsum]
      _ = ctx.spec.mul (Exact.bpow ctx r e1) (Exact.bpow ctx r d) :=
        CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx r e1 d
  have hpos : Exact.Rlt ctx (ctx.spec.zero) (Exact.bpow ctx r e1) :=
    CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx r e1
  have hone : Exact.Rlt ctx (ctx.spec.one) (Exact.bpow ctx r d) :=
    pg_bpow_pos_gt_one ctx r hd
  have hpos' : Exact.Rlt ctx (Exact.IZR ctx Z0) (Exact.bpow ctx r e1) := by
    change ctx.spec.lt (ctx.spec.ofZ Z0) (Exact.bpow ctx r e1)
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hpos
  have hmul' :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_compat_r
      ctx (Exact.bpow ctx r e1) (ctx.spec.one) (Exact.bpow ctx r d) hpos' hone
  change ctx.spec.lt (ctx.spec.mul ctx.spec.one (Exact.bpow ctx r e1))
    (ctx.spec.mul (Exact.bpow ctx r d) (Exact.bpow ctx r e1)) at hmul'
  rw [ctx.certificate.orderedField.mul_comm ctx.spec.one _,
    ctx.certificate.orderedField.mul_one,
    ctx.certificate.orderedField.mul_comm _ (Exact.bpow ctx r e1)] at hmul'
  rw [← hmul] at hmul'
  exact hmul'

private theorem pg_bpow_le (ctx : ExactRealContext) (r : radix)
    {e1 e2 : Z} (h : Zle e1 e2) :
    Exact.Rle ctx (Exact.bpow ctx r e1) (Exact.bpow ctx r e2) := by
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 at h
  rcases Int.lt_or_eq_of_le h with hlt | heq
  · have hlt' : Zlt e1 e2 := by exact hlt
    exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
      (pg_bpow_lt ctx r hlt') |>.1
  · have heq' : e1 = e2 := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      exact heq
    subst e2
    exact ctx.certificate.orderedField.le_refl _

private theorem pg_mag_unique (ctx : ExactRealContext) (r : radix)
    (x : Exact.R ctx) {e1 e2 : Z}
    (h1 : Exact.Rle ctx (Exact.bpow ctx r (Zsub e1 Zone)) (Exact.Rabs ctx x) ∧
      Exact.Rlt ctx (Exact.Rabs ctx x) (Exact.bpow ctx r e1))
    (h2 : Exact.Rle ctx (Exact.bpow ctx r (Zsub e2 Zone)) (Exact.Rabs ctx x) ∧
      Exact.Rlt ctx (Exact.Rabs ctx x) (Exact.bpow ctx r e2)) : e1 = e2 := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  by_cases hEq : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2
  · exact hEq
  · rcases Int.lt_or_gt_of_ne hEq with h12 | h21
    · have hleexp : Zle e1 (Zsub e2 Zone) := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub e2 Zone)
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 - 1
        omega
      have hp := pg_bpow_le ctx r hleexp
      have hmid :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
          ctx _ _ _ h2.1 h1.2
      have hnot := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hmid |>.2
      exact (hnot hp).elim
    · have hleexp : Zle e2 (Zsub e1 Zone) := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub e1 Zone)
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 - 1
        omega
      have hp := pg_bpow_le ctx r hleexp
      have hmid :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
          ctx _ _ _ h1.1 h2.2
      have hnot := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hmid |>.2
      exact (hnot hp).elim

private theorem pg_neg_ne_zero (ctx : ExactRealContext) {x : Exact.R ctx}
    (hx : x ≠ Exact.R0 ctx) : ctx.spec.neg x ≠ ctx.spec.zero := by
  intro hn
  have h := congrArg (fun y => ctx.spec.add x y) hn
  rw [ctx.certificate.orderedField.add_comm x (ctx.spec.neg x),
    ctx.certificate.orderedField.neg_add_cancel,
    ctx.certificate.orderedField.add_zero] at h
  exact hx h.symm

private theorem pg_abs_nonneg (ctx : ExactRealContext) (x : Exact.R ctx) :
    ctx.spec.le ctx.spec.zero (ctx.spec.abs x) := by
  rcases ctx.certificate.total_order x ctx.spec.zero with h | h
  · rcases h with hlt | heq
    · rw [ctx.certificate.sourceLaws.abs_negative x hlt]
      have hp : ctx.spec.lt ctx.spec.zero (ctx.spec.neg x) := by
        have hh := ctx.certificate.orderedField.add_lt_compat_l
          (ctx.spec.neg x) x ctx.spec.zero hlt
        rw [ctx.certificate.orderedField.neg_add_cancel,
          ctx.certificate.orderedField.add_zero] at hh
        exact hh
      exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hp |>.1
    · subst x
      rw [ctx.certificate.sourceLaws.abs_nonnegative _
        (ctx.certificate.orderedField.le_refl _)]
      exact ctx.certificate.orderedField.le_refl _
  · have hle := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1
    rw [ctx.certificate.sourceLaws.abs_nonnegative x hle]
    exact hle

private theorem pg_abs_ne_zero (ctx : ExactRealContext) {x : Exact.R ctx}
    (hx : x ≠ Exact.R0 ctx) : ctx.spec.abs x ≠ ctx.spec.zero := by
  rcases ctx.certificate.total_order x ctx.spec.zero with h | h
  · rcases h with hlt | heq
    · rw [ctx.certificate.sourceLaws.abs_negative x hlt]
      exact pg_neg_ne_zero ctx hx
    · exact (hx heq).elim
  · have hle := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1
    rw [ctx.certificate.sourceLaws.abs_nonnegative x hle]
    exact hx

private theorem pg_mag_abs (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (r : radix) (x : Exact.R ctx) :
    (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude r
      (Exact.Rabs ctx x)).mag_val =
      (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude r x).mag_val := by
  by_cases hx : x = Exact.R0 ctx
  · subst x
    have hz : Exact.Rabs ctx (Exact.R0 ctx) = Exact.R0 ctx := by
      change ctx.spec.abs ctx.spec.zero = ctx.spec.zero
      exact ctx.certificate.sourceLaws.abs_nonnegative _
        (ctx.certificate.orderedField.le_refl _)
    rw [hz]
  · have hxa := (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude r
      (Exact.Rabs ctx x)).mag_bound
      (pg_abs_ne_zero ctx hx)
    have hxx := (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude r x).mag_bound hx
    have habs : Exact.Rabs ctx (Exact.Rabs ctx x) = Exact.Rabs ctx x := by
      change ctx.spec.abs (ctx.spec.abs x) = ctx.spec.abs x
      exact ctx.certificate.sourceLaws.abs_nonnegative _ (pg_abs_nonneg ctx x)
    have habs' : CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx
        (CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x) =
        CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x := by exact habs
    rw [habs'] at hxa
    exact pg_mag_unique ctx r x hxa hxx

theorem canonical_abs : ∀ ctx magnitude, canonical_absStatement ctx magnitude := by
  intro ctx magnitude beta fexp m e hcanon
  unfold Exact.canonical at hcanon ⊢
  change e = Exact.cexp ctx magnitude beta fexp
      (Exact.F2R ctx (Float beta m e)) at hcanon
  change e = Exact.cexp ctx magnitude beta fexp
      (Exact.F2R ctx (Float beta (Zabs m) e))
  have hf2r := CompCert4Lean.Flocq.Core.Float_prop.F2R_Zabs ctx beta m e
  change Exact.F2R ctx (Float beta (Zabs m) e) =
    Exact.Rabs ctx (Exact.F2R ctx (Float beta m e)) at hf2r
  rw [hf2r]
  unfold Exact.cexp
  have hm := pg_mag_abs ctx magnitude beta
    (Exact.F2R ctx (Float beta m e))
  have hm' : Exact.mag magnitude beta
      (Exact.Rabs ctx (Exact.F2R ctx (Float beta m e))) =
      Exact.mag magnitude beta (Exact.F2R ctx (Float beta m e)) := by
    exact hm
  rw [hm']
  exact hcanon

end CompCert4Lean.Flocq.Core.Generic_fmt

namespace CompCert4Lean.Flocq.Core.Generic_fmt

theorem canonical_unique : ∀ ctx magnitude, canonical_uniqueStatement ctx magnitude := by
  intro ctx magnitude beta fexp f1 f2 h1 h2 h
  cases f1 with
  | Float m1 e1 =>
      cases f2 with
      | Float m2 e2 =>
          unfold Exact.canonical at h1 h2
          have he : e1 = e2 := by
            calc
              e1 = Exact.cexp ctx magnitude beta fexp
                  (Exact.F2R ctx (Float beta m1 e1)) := h1
              _ = Exact.cexp ctx magnitude beta fexp
                  (Exact.F2R ctx (Float beta m2 e2)) := by rw [h]
              _ = e2 := h2.symm
          subst e2
          have hm : m1 = m2 :=
            CompCert4Lean.Flocq.Core.Float_prop.eq_F2R ctx beta e1 m1 m2 h
          subst m2
          rfl

end CompCert4Lean.Flocq.Core.Generic_fmt

namespace CompCert4Lean.Flocq.Core.Generic_fmt

private theorem pg_scaled_mantissa_exp_cancel (e : Z) :
    Zadd e (Zopp e) = Z0 := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd e (Zopp e)) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0
  simp only [Zadd, Zopp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e +
    -CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e = 0
  omega

theorem scaled_mantissa_generic :
    ∀ ctx magnitude, scaled_mantissa_genericStatement ctx magnitude := by
  intro ctx magnitude beta fexp x hformat
  let m := Exact.Ztrunc ctx
    (Exact.scaled_mantissa ctx magnitude beta fexp x)
  let e := Exact.cexp ctx magnitude beta fexp x
  have hx : x = Exact.F2R ctx (Float beta m e) := by
    simpa [Exact.generic_format, m, e] using hformat
  change Exact.Rmult ctx x (Exact.bpow ctx beta (Zopp e)) = Exact.IZR ctx m
  calc
    Exact.Rmult ctx x (Exact.bpow ctx beta (Zopp e)) =
        Exact.Rmult ctx
          (Exact.F2R ctx (Float beta m e))
          (Exact.bpow ctx beta (Zopp e)) := by rw [hx]
    _ = Exact.Rmult ctx
          (Exact.Rmult ctx (Exact.IZR ctx m) (Exact.bpow ctx beta e))
          (Exact.bpow ctx beta (Zopp e)) := by
      rfl
    _ = Exact.Rmult ctx (Exact.IZR ctx m)
          (Exact.Rmult ctx (Exact.bpow ctx beta e)
            (Exact.bpow ctx beta (Zopp e))) := by
      exact ctx.certificate.orderedField.mul_assoc
        (Exact.IZR ctx m) (Exact.bpow ctx beta e)
        (Exact.bpow ctx beta (Zopp e))
    _ = Exact.Rmult ctx (Exact.IZR ctx m)
          (Exact.bpow ctx beta (Zadd e (Zopp e))) := by
      have hpow := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta e (Zopp e)
      change Exact.bpow ctx beta (Zadd e (Zopp e)) =
        Exact.Rmult ctx (Exact.bpow ctx beta e)
          (Exact.bpow ctx beta (Zopp e)) at hpow
      rw [hpow]
    _ = Exact.Rmult ctx (Exact.IZR ctx m) (Exact.bpow ctx beta Z0) := by
      rw [pg_scaled_mantissa_exp_cancel]
    _ = Exact.IZR ctx m := by
      change ctx.spec.mul (Exact.IZR ctx m) ctx.spec.one = _
      exact ctx.certificate.orderedField.mul_one _

end CompCert4Lean.Flocq.Core.Generic_fmt

namespace CompCert4Lean.Flocq.Core.Generic_fmt

private theorem pg_scaled_mantissa_exp_cancel_left (e : Z) :
    Zadd (Zopp e) e = Z0 := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd (Zopp e) e) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0
  simp only [Zadd, Zopp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change -CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e +
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e = 0
  omega

theorem scaled_mantissa_mult_bpow :
    ∀ ctx magnitude, scaled_mantissa_mult_bpowStatement ctx magnitude := by
  intro ctx magnitude beta fexp x
  unfold Exact.scaled_mantissa
  let e := Exact.cexp ctx magnitude beta fexp x
  change Exact.Rmult ctx
      (Exact.Rmult ctx x (Exact.bpow ctx beta (Zopp e)))
      (Exact.bpow ctx beta e) = x
  calc
    Exact.Rmult ctx
        (Exact.Rmult ctx x (Exact.bpow ctx beta (Zopp e)))
        (Exact.bpow ctx beta e) =
        Exact.Rmult ctx x
          (Exact.Rmult ctx (Exact.bpow ctx beta (Zopp e))
            (Exact.bpow ctx beta e)) := by
      exact ctx.certificate.orderedField.mul_assoc x
        (Exact.bpow ctx beta (Zopp e)) (Exact.bpow ctx beta e)
    _ = Exact.Rmult ctx x
        (Exact.bpow ctx beta (Zadd (Zopp e) e)) := by
      have hpow := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta (Zopp e) e
      change Exact.bpow ctx beta (Zadd (Zopp e) e) =
        Exact.Rmult ctx (Exact.bpow ctx beta (Zopp e))
          (Exact.bpow ctx beta e) at hpow
      rw [hpow]
    _ = Exact.Rmult ctx x (Exact.bpow ctx beta Z0) := by
      rw [pg_scaled_mantissa_exp_cancel_left]
    _ = x := by
      change ctx.spec.mul x ctx.spec.one = x
      exact ctx.certificate.orderedField.mul_one _

end CompCert4Lean.Flocq.Core.Generic_fmt

namespace CompCert4Lean.Flocq.Core.Generic_fmt

theorem scaled_mantissa_0 :
    ∀ ctx magnitude, scaled_mantissa_0Statement ctx magnitude := by
  intro ctx magnitude beta fexp
  unfold Exact.scaled_mantissa
  exact ctx.certificate.orderedField.zero_mul _

end CompCert4Lean.Flocq.Core.Generic_fmt

namespace CompCert4Lean.Flocq.Core.Generic_fmt

private theorem pg_neg_neg (ctx : ExactRealContext) (x : Exact.R ctx) :
    Exact.Ropp ctx (Exact.Ropp ctx x) = x := by
  change ctx.spec.neg (ctx.spec.neg x) = x
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

private theorem pg_neg_zero (ctx : ExactRealContext) :
    Exact.Ropp ctx (Exact.R0 ctx) = Exact.R0 ctx := by
  change ctx.spec.neg ctx.spec.zero = ctx.spec.zero
  have h := ctx.certificate.orderedField.neg_add_cancel ctx.spec.zero
  rw [ctx.certificate.orderedField.add_zero] at h
  exact h

private theorem pg_abs_opp (ctx : ExactRealContext) (x : Exact.R ctx) :
    Exact.Rabs ctx (Exact.Ropp ctx x) = Exact.Rabs ctx x := by
  change ctx.spec.abs (ctx.spec.neg x) = ctx.spec.abs x
  rcases ctx.certificate.total_order x ctx.spec.zero with h | h
  · rcases h with hlt | heq
    · have hneg : ctx.spec.le ctx.spec.zero (ctx.spec.neg x) := by
        have hh := ctx.certificate.orderedField.add_lt_compat_l
          (ctx.spec.neg x) x ctx.spec.zero hlt
        rw [ctx.certificate.orderedField.neg_add_cancel,
          ctx.certificate.orderedField.add_zero] at hh
        exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hh |>.1
      rw [ctx.certificate.sourceLaws.abs_nonnegative _ hneg,
        ctx.certificate.sourceLaws.abs_negative x hlt]
    · subst x
      exact congrArg (fun z => ctx.spec.abs z) (pg_neg_zero ctx)
  · have hneglt : ctx.spec.lt (ctx.spec.neg x) ctx.spec.zero := by
      have hh := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.neg x) ctx.spec.zero x h
      rw [ctx.certificate.orderedField.neg_add_cancel,
        ctx.certificate.orderedField.add_zero] at hh
      exact hh
    calc
      ctx.spec.abs (ctx.spec.neg x) = ctx.spec.neg (ctx.spec.neg x) :=
        ctx.certificate.sourceLaws.abs_negative _ hneglt
      _ = x := pg_neg_neg ctx x
      _ = ctx.spec.abs x :=
        (ctx.certificate.sourceLaws.abs_nonnegative _
          ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1)).symm

private theorem pg_mag_opp (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (r : radix) (x : Exact.R ctx) :
    (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude r
      (Exact.Ropp ctx x)).mag_val =
      (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude r x).mag_val := by
  by_cases hx : x = Exact.R0 ctx
  · subst x
    rw [pg_neg_zero ctx]
  · have hxa := (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude r
      (Exact.Ropp ctx x)).mag_bound (pg_neg_ne_zero ctx hx)
    have hxx := (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude r x).mag_bound hx
    have habs := pg_abs_opp ctx x
    have hxx' :
        Raux.Exact.Rle ctx
            (Raux.Exact.bpow ctx r
              (Raux.Zsub (Raux.Exact.mag magnitude r x).mag_val (Raux.Zpos Raux.xH)))
            (Raux.Exact.Rabs ctx (Exact.Ropp ctx x)) ∧
          Raux.Exact.Rlt ctx (Raux.Exact.Rabs ctx (Exact.Ropp ctx x))
            (Raux.Exact.bpow ctx r (Raux.Exact.mag magnitude r x).mag_val) := by
      simpa only [habs] using hxx
    exact pg_mag_unique ctx r (Exact.Ropp ctx x) hxa hxx'

private theorem pg_cexp_opp (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (r : radix) (fexp : Z → Z) (x : Exact.R ctx) :
    Exact.cexp ctx magnitude r fexp (Exact.Ropp ctx x) =
      Exact.cexp ctx magnitude r fexp x := by
  unfold Exact.cexp
  change fexp ((CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude r
      (Exact.Ropp ctx x)).mag_val) =
    fexp ((CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude r x).mag_val)
  exact congrArg fexp (pg_mag_opp ctx magnitude r x)

private theorem pg_neg_mul_right (ctx : ExactRealContext) (x y : Exact.R ctx) :
    ctx.spec.mul (ctx.spec.neg x) y = ctx.spec.neg (ctx.spec.mul x y) := by
  rw [ctx.certificate.orderedField.mul_comm]
  have h : ctx.spec.mul y (ctx.spec.neg x) =
      ctx.spec.neg (ctx.spec.mul y x) := by
    have hc : ctx.spec.add (ctx.spec.mul y (ctx.spec.neg x))
        (ctx.spec.mul y x) = ctx.spec.zero := by
      rw [← ctx.certificate.orderedField.left_distrib,
        ctx.certificate.orderedField.neg_add_cancel,
        ctx.certificate.orderedField.mul_zero]
    symm
    calc
      ctx.spec.neg (ctx.spec.mul y x) =
          ctx.spec.add (ctx.spec.neg (ctx.spec.mul y x)) ctx.spec.zero :=
        (ctx.certificate.orderedField.add_zero _).symm
      _ = ctx.spec.add (ctx.spec.neg (ctx.spec.mul y x))
          (ctx.spec.add (ctx.spec.mul y (ctx.spec.neg x)) (ctx.spec.mul y x)) := by
        rw [hc]
      _ = ctx.spec.add
          (ctx.spec.add (ctx.spec.neg (ctx.spec.mul y x)) (ctx.spec.mul y x))
          (ctx.spec.mul y (ctx.spec.neg x)) := by
        rw [ctx.certificate.orderedField.add_assoc,
          ctx.certificate.orderedField.add_comm
            (ctx.spec.mul y (ctx.spec.neg x)) (ctx.spec.mul y x)]
      _ = ctx.spec.add ctx.spec.zero (ctx.spec.mul y (ctx.spec.neg x)) := by
        rw [ctx.certificate.orderedField.neg_add_cancel]
      _ = ctx.spec.mul y (ctx.spec.neg x) :=
        ctx.certificate.orderedField.zero_add _
  rw [h, ctx.certificate.orderedField.mul_comm]

theorem scaled_mantissa_opp :
    ∀ ctx magnitude, scaled_mantissa_oppStatement ctx magnitude := by
  intro ctx magnitude beta fexp x
  unfold Exact.scaled_mantissa
  rw [pg_cexp_opp ctx magnitude beta fexp x]
  change ctx.spec.mul (ctx.spec.neg x)
      (Exact.bpow ctx beta (Zopp (Exact.cexp ctx magnitude beta fexp x))) =
    ctx.spec.neg
      (ctx.spec.mul x (Exact.bpow ctx beta (Zopp (Exact.cexp ctx magnitude beta fexp x))))
  exact pg_neg_mul_right ctx x _

private theorem pg_mul_neg_right (ctx : ExactRealContext) (x y : Exact.R ctx) :
    ctx.spec.mul x (ctx.spec.neg y) = ctx.spec.neg (ctx.spec.mul x y) := by
  calc
    ctx.spec.mul x (ctx.spec.neg y) =
        ctx.spec.mul (ctx.spec.neg y) x := ctx.certificate.orderedField.mul_comm _ _
    _ = ctx.spec.neg (ctx.spec.mul y x) := pg_neg_mul_right ctx y x
    _ = ctx.spec.neg (ctx.spec.mul x y) := by
      rw [ctx.certificate.orderedField.mul_comm]

private theorem pg_neg_pos_of_neg (ctx : ExactRealContext) {x : Exact.R ctx}
    (h : ctx.spec.lt x ctx.spec.zero) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.neg x) := by
  have hh := ctx.certificate.orderedField.add_lt_compat_l
    (ctx.spec.neg x) x ctx.spec.zero h
  rw [ctx.certificate.orderedField.neg_add_cancel,
    ctx.certificate.orderedField.add_zero] at hh
  exact hh

private theorem pg_abs_zero (ctx : ExactRealContext) :
    Exact.Rabs ctx (Exact.R0 ctx) = Exact.R0 ctx := by
  change ctx.spec.abs ctx.spec.zero = ctx.spec.zero
  exact ctx.certificate.sourceLaws.abs_nonnegative _
    (ctx.certificate.orderedField.le_refl _)

private theorem pg_abs_zero_spec (ctx : ExactRealContext) :
    ctx.spec.abs ctx.spec.zero = ctx.spec.zero := by
  exact ctx.certificate.sourceLaws.abs_nonnegative _
    (ctx.certificate.orderedField.le_refl _)

private theorem pg_abs_mul (ctx : ExactRealContext) (x y : Exact.R ctx) :
    Exact.Rabs ctx (ctx.spec.mul x y) =
      ctx.spec.mul (Exact.Rabs ctx x) (Exact.Rabs ctx y) := by
  change ctx.spec.abs (ctx.spec.mul x y) =
    ctx.spec.mul (ctx.spec.abs x) (ctx.spec.abs y)
  rcases ctx.certificate.total_order ctx.spec.zero x with hx | hx
  · rcases hx with hxpos | hxzero
    · rcases ctx.certificate.total_order ctx.spec.zero y with hy | hy
      · rcases hy with hypos | hyzero
        · have hp : ctx.spec.lt ctx.spec.zero (ctx.spec.mul x y) := by
            have hh := ctx.certificate.orderedField.mul_lt_compat_l
              x ctx.spec.zero y hxpos hypos
            rw [ctx.certificate.orderedField.mul_zero] at hh
            exact hh
          rw [ctx.certificate.sourceLaws.abs_nonnegative _
              ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hp |>.1),
            ctx.certificate.sourceLaws.abs_nonnegative _
              ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxpos |>.1),
            ctx.certificate.sourceLaws.abs_nonnegative _
              ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hypos |>.1)]
        · subst y
          rw [ctx.certificate.orderedField.mul_zero, pg_abs_zero_spec ctx,
            ctx.certificate.orderedField.mul_zero]
      · have hyneg : ctx.spec.lt y ctx.spec.zero := hy
        have hp : ctx.spec.lt (ctx.spec.mul x y) ctx.spec.zero := by
          have hh := ctx.certificate.orderedField.mul_lt_compat_l
            x y ctx.spec.zero hxpos hyneg
          rw [ctx.certificate.orderedField.mul_zero] at hh
          exact hh
        rw [ctx.certificate.sourceLaws.abs_negative _ hp,
          ctx.certificate.sourceLaws.abs_nonnegative _
            ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxpos |>.1),
          ctx.certificate.sourceLaws.abs_negative _ hyneg,
          pg_mul_neg_right ctx x y]
    · subst x
      rw [ctx.certificate.orderedField.zero_mul, pg_abs_zero_spec ctx,
        ctx.certificate.orderedField.zero_mul]
  · have hxneg : ctx.spec.lt x ctx.spec.zero := hx
    rcases ctx.certificate.total_order ctx.spec.zero y with hy | hy
    · rcases hy with hypos | hyzero
      · have hp : ctx.spec.lt (ctx.spec.mul x y) ctx.spec.zero := by
          have hh := ctx.certificate.orderedField.mul_lt_compat_l
            y x ctx.spec.zero hypos hxneg
          rw [ctx.certificate.orderedField.mul_zero] at hh
          simpa [ctx.certificate.orderedField.mul_comm] using hh
        rw [ctx.certificate.sourceLaws.abs_negative _ hp,
          ctx.certificate.sourceLaws.abs_negative _ hxneg,
          ctx.certificate.sourceLaws.abs_nonnegative _
            ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hypos |>.1),
          ← pg_neg_mul_right ctx x y,
          ctx.certificate.orderedField.mul_comm]
      · subst y
        rw [ctx.certificate.orderedField.mul_zero, pg_abs_zero_spec ctx,
          ctx.certificate.orderedField.mul_zero]
    · have hyneg : ctx.spec.lt y ctx.spec.zero := hy
      have hnx : ctx.spec.lt ctx.spec.zero (ctx.spec.neg x) :=
        pg_neg_pos_of_neg ctx hxneg
      have hny : ctx.spec.lt ctx.spec.zero (ctx.spec.neg y) :=
        pg_neg_pos_of_neg ctx hyneg
      have hpneg : ctx.spec.lt ctx.spec.zero
          (ctx.spec.mul (ctx.spec.neg x) (ctx.spec.neg y)) := by
        have hh := ctx.certificate.orderedField.mul_lt_compat_l
          (ctx.spec.neg x) ctx.spec.zero (ctx.spec.neg y) hnx hny
        rw [ctx.certificate.orderedField.mul_zero] at hh
        exact hh
      have hprod : ctx.spec.mul (ctx.spec.neg x) (ctx.spec.neg y) =
          ctx.spec.mul x y := by
        calc
          ctx.spec.mul (ctx.spec.neg x) (ctx.spec.neg y) =
              ctx.spec.neg (ctx.spec.mul x (ctx.spec.neg y)) :=
            pg_neg_mul_right ctx x (ctx.spec.neg y)
          _ = ctx.spec.neg (ctx.spec.neg (ctx.spec.mul x y)) := by
            rw [pg_mul_neg_right ctx x y]
          _ = ctx.spec.mul x y := pg_neg_neg ctx _
      rw [← hprod,
        ctx.certificate.sourceLaws.abs_nonnegative _
          ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hpneg |>.1),
        ctx.certificate.sourceLaws.abs_negative _ hxneg,
        ctx.certificate.sourceLaws.abs_negative _ hyneg,
        hprod]

private theorem pg_cexp_abs (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (r : radix) (fexp : Z → Z) (x : Exact.R ctx) :
    Exact.cexp ctx magnitude r fexp (Exact.Rabs ctx x) =
      Exact.cexp ctx magnitude r fexp x := by
  unfold Exact.cexp
  have hm := pg_mag_abs ctx magnitude r x
  change fexp ((CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude r
      (Exact.Rabs ctx x)).mag_val) =
    fexp ((CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude r x).mag_val)
  exact congrArg fexp hm

private theorem pg_abs_bpow (ctx : ExactRealContext) (r : radix) (e : Z) :
    Exact.Rabs ctx (Exact.bpow ctx r e) = Exact.bpow ctx r e := by
  change ctx.spec.abs (Exact.bpow ctx r e) = Exact.bpow ctx r e
  exact ctx.certificate.sourceLaws.abs_nonnegative _
    (CompCert4Lean.Flocq.Core.Raux.bpow_ge_0 ctx r e)

theorem scaled_mantissa_abs :
    ∀ ctx magnitude, scaled_mantissa_absStatement ctx magnitude := by
  intro ctx magnitude beta fexp x
  unfold Exact.scaled_mantissa
  rw [pg_cexp_abs ctx magnitude beta fexp x]
  change ctx.spec.mul (Exact.Rabs ctx x)
      (Exact.bpow ctx beta (Zopp (Exact.cexp ctx magnitude beta fexp x))) =
    Exact.Rabs ctx
      (ctx.spec.mul x
        (Exact.bpow ctx beta (Zopp (Exact.cexp ctx magnitude beta fexp x))))
  rw [pg_abs_mul]
  rw [pg_abs_bpow]

end CompCert4Lean.Flocq.Core.Generic_fmt

namespace CompCert4Lean.Flocq.Core.Generic_fmt

private theorem pg_rlt_bool_true_of_lt (ctx : ExactRealContext)
    (x y : Exact.R ctx) (h : Exact.Rlt ctx x y) :
    CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x y = true := by
  unfold CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool
  rw [CompCert4Lean.Flocq.Core.Raux.Rcompare_Lt ctx x y h]

private theorem pg_rlt_bool_false_of_le (ctx : ExactRealContext)
    (x y : Exact.R ctx) (h : Exact.Rle ctx y x) :
    CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x y = false := by
  have hne := CompCert4Lean.Flocq.Core.Raux.Rcompare_not_Lt ctx x y h
  unfold CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool
  cases hcmp : Exact.Rcompare ctx x y with
  | Lt => exact (hne hcmp).elim
  | Eq => simp only [hcmp]
  | Gt => simp only [hcmp]

private theorem pg_lt_of_rlt_bool_true (ctx : ExactRealContext)
    (x y : Exact.R ctx)
    (h : CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x y = true) :
    Exact.Rlt ctx x y := by
  unfold CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool at h
  cases hcmp : Exact.Rcompare ctx x y with
  | Lt => exact CompCert4Lean.Flocq.Core.Raux.Rcompare_Lt_inv ctx x y hcmp
  | Eq => simp [hcmp] at h
  | Gt => simp [hcmp] at h

private theorem pg_le_of_rlt_bool_false (ctx : ExactRealContext)
    (x y : Exact.R ctx)
    (h : CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x y = false) :
    Exact.Rle ctx y x := by
  unfold CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool at h
  apply CompCert4Lean.Flocq.Core.Raux.Rcompare_not_Lt_inv ctx x y
  intro hcmp
  rw [hcmp] at h
  simp at h

end CompCert4Lean.Flocq.Core.Generic_fmt

namespace CompCert4Lean.Flocq.Core.Generic_fmt

private theorem pg_neg_lt_zero_of_pos (ctx : ExactRealContext)
    {x : Exact.R ctx} (h : ctx.spec.lt ctx.spec.zero x) :
    ctx.spec.lt (ctx.spec.neg x) ctx.spec.zero := by
  have hh := ctx.certificate.orderedField.add_lt_compat_l
    (ctx.spec.neg x) ctx.spec.zero x h
  rw [ctx.certificate.orderedField.neg_add_cancel,
    ctx.certificate.orderedField.add_zero] at hh
  exact hh

private theorem pg_zopp_zopp (z : Z) : Zopp (Zopp z) = z := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zopp (Zopp z)) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z
  simp only [Zopp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

private theorem pg_ztrunc_opp (ctx : ExactRealContext) {x : Exact.R ctx}
    (hx0 : x ≠ Exact.R0 ctx) :
    Exact.Ztrunc ctx (Exact.Ropp ctx x) = Zopp (Exact.Ztrunc ctx x) := by
  by_cases hb : CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x
      (Exact.R0 ctx) = true
  · have hxneg : Exact.Rlt ctx x (Exact.R0 ctx) :=
      pg_lt_of_rlt_bool_true ctx x (Exact.R0 ctx) hb
    have hxnegpos : Exact.Rlt ctx (Exact.R0 ctx) (Exact.Ropp ctx x) := by
      exact pg_neg_pos_of_neg ctx hxneg
    have hxneg_nonneg : Exact.Rle ctx (Exact.R0 ctx) (Exact.Ropp ctx x) :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxnegpos |>.1
    have hbn := pg_rlt_bool_false_of_le ctx (Exact.Ropp ctx x)
      (Exact.R0 ctx) hxneg_nonneg
    change (if CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx
        (Exact.Ropp ctx x) (Exact.R0 ctx) then
        CompCert4Lean.Flocq.Core.Raux.Exact.Zceil ctx (Exact.Ropp ctx x)
      else CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx (Exact.Ropp ctx x)) =
      Zopp (if CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x
        (Exact.R0 ctx) then
        CompCert4Lean.Flocq.Core.Raux.Exact.Zceil ctx x
      else CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx x)
    rw [hbn, hb]
    change CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx (Exact.Ropp ctx x) =
      Zopp (CompCert4Lean.Flocq.Core.Raux.Zopp
        (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx (Exact.Ropp ctx x)))
    exact (pg_zopp_zopp _).symm
  · have hb' : CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x
        (Exact.R0 ctx) = false := by
      cases hval : CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x
          (Exact.R0 ctx) with
      | false => rfl
      | true => exact (hb hval).elim
    have hxnonneg : Exact.Rle ctx (Exact.R0 ctx) x :=
      pg_le_of_rlt_bool_false ctx x (Exact.R0 ctx) hb'
    have hxpos : Exact.Rlt ctx (Exact.R0 ctx) x := by
      apply (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
      constructor
      · exact hxnonneg
      · intro hxle
        apply hx0
        exact ctx.certificate.orderedField.le_antisymm _ _ hxle hxnonneg
    have hneg : Exact.Rlt ctx (Exact.Ropp ctx x) (Exact.R0 ctx) := by
      exact pg_neg_lt_zero_of_pos ctx hxpos
    have hbn := pg_rlt_bool_true_of_lt ctx (Exact.Ropp ctx x)
      (Exact.R0 ctx) hneg
    change (if CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx
        (Exact.Ropp ctx x) (Exact.R0 ctx) then
        CompCert4Lean.Flocq.Core.Raux.Exact.Zceil ctx (Exact.Ropp ctx x)
      else CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx (Exact.Ropp ctx x)) =
      Zopp (if CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x
        (Exact.R0 ctx) then
        CompCert4Lean.Flocq.Core.Raux.Exact.Zceil ctx x
      else CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx x)
    simp [hbn, hb']
    unfold CompCert4Lean.Flocq.Core.Raux.Exact.Zceil
    have hnn : CompCert4Lean.Flocq.Core.Raux.Exact.Ropp ctx
        (CompCert4Lean.Flocq.Core.Raux.Exact.Ropp ctx x) = x := by
      exact pg_neg_neg ctx x
    rw [hnn]

end CompCert4Lean.Flocq.Core.Generic_fmt

namespace CompCert4Lean.Flocq.Core.Generic_fmt

private theorem pg_scaled_mantissa_ne_zero (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) (beta : radix) (fexp : Z → Z)
    {x : Exact.R ctx} (hx0 : x ≠ Exact.R0 ctx) :
    Exact.scaled_mantissa ctx magnitude beta fexp x ≠ Exact.R0 ctx := by
  unfold Exact.scaled_mantissa
  intro hz
  let p := Exact.bpow ctx beta
    (Zopp (Exact.cexp ctx magnitude beta fexp x))
  have hpos : Exact.Rlt ctx (Exact.R0 ctx) p := by
    dsimp [p]
    exact CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta
      (Zopp (Exact.cexp ctx magnitude beta fexp x))
  have hp0 : p ≠ Exact.R0 ctx := by
    intro hp
    have hbad := hpos
    rw [hp] at hbad
    exact (ctx.certificate.orderedField.lt_irrefl _ hbad).elim
  have hinv := ctx.certificate.orderedField.inv_mul_cancel p (by
    exact hp0)
  change ctx.spec.mul x
      (Exact.bpow ctx beta (Zopp (Exact.cexp ctx magnitude beta fexp x))) =
      ctx.spec.zero at hz
  have hzero : ctx.spec.mul x p = ctx.spec.zero := by
    simpa [p] using hz
  have hx_eq : x = Exact.R0 ctx := by
    change x = ctx.spec.zero
    calc
      x = ctx.spec.mul ctx.spec.one x :=
        (ctx.certificate.orderedField.one_mul x).symm
      _ = ctx.spec.mul (ctx.spec.mul (ctx.spec.inv p) p) x := by
        rw [hinv]
      _ = ctx.spec.mul (ctx.spec.inv p) (ctx.spec.mul p x) := by
        exact ctx.certificate.orderedField.mul_assoc _ _ _
      _ = ctx.spec.mul (ctx.spec.inv p) (ctx.spec.mul x p) := by
        rw [ctx.certificate.orderedField.mul_comm p x]
      _ = ctx.spec.mul (ctx.spec.inv p) ctx.spec.zero := by rw [hzero]
      _ = ctx.spec.zero := ctx.certificate.orderedField.mul_zero _
  exact hx0 hx_eq

end CompCert4Lean.Flocq.Core.Generic_fmt

namespace CompCert4Lean.Flocq.Core.Generic_fmt

theorem generic_format_opp :
    ∀ ctx magnitude, generic_format_oppStatement ctx magnitude := by
  intro ctx magnitude beta fexp x hx
  by_cases hx0 : x = Exact.R0 ctx
  · subst x
    have hzero : Exact.Ropp ctx (Exact.R0 ctx) = Exact.R0 ctx :=
      pg_neg_zero ctx
    rw [hzero]
    exact hx
  · unfold Exact.generic_format at hx ⊢
    have hsm0 := pg_scaled_mantissa_ne_zero ctx magnitude beta fexp hx0
    have htr := pg_ztrunc_opp ctx hsm0
    have hce := pg_cexp_opp ctx magnitude beta fexp x
    rw [scaled_mantissa_opp ctx magnitude beta fexp x, htr, hce]
    have hf2r := CompCert4Lean.Flocq.Core.Float_prop.F2R_Zopp ctx beta
      (Exact.Ztrunc ctx (Exact.scaled_mantissa ctx magnitude beta fexp x))
      (Exact.cexp ctx magnitude beta fexp x)
    change Exact.F2R ctx
        (Float beta (Zopp (Exact.Ztrunc ctx
          (Exact.scaled_mantissa ctx magnitude beta fexp x)))
          (Exact.cexp ctx magnitude beta fexp x)) =
      Exact.Ropp ctx
        (Exact.F2R ctx (Float beta (Exact.Ztrunc ctx
          (Exact.scaled_mantissa ctx magnitude beta fexp x))
          (Exact.cexp ctx magnitude beta fexp x))) at hf2r
    rw [hf2r]
    exact congrArg (Exact.Ropp ctx) hx

end CompCert4Lean.Flocq.Core.Generic_fmt

namespace CompCert4Lean.Flocq.Core.Generic_fmt

theorem generic_format_abs :
    ∀ ctx magnitude, generic_format_absStatement ctx magnitude := by
  intro ctx magnitude beta fexp x hx
  change Exact.generic_format ctx magnitude beta fexp (ctx.spec.abs x)
  rcases ctx.certificate.total_order x ctx.spec.zero with h | h
  · rcases h with hxneg | hzero
    · rw [ctx.certificate.sourceLaws.abs_negative x hxneg]
      change Exact.generic_format ctx magnitude beta fexp (Exact.Ropp ctx x)
      exact generic_format_opp ctx magnitude beta fexp x hx
    · subst x
      rw [ctx.certificate.sourceLaws.abs_nonnegative _
        (ctx.certificate.orderedField.le_refl _)]
      exact hx
  · have hxle : ctx.spec.le ctx.spec.zero x :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1
    rw [ctx.certificate.sourceLaws.abs_nonnegative x hxle]
    exact hx

end CompCert4Lean.Flocq.Core.Generic_fmt

namespace CompCert4Lean.Flocq.Core.Generic_fmt

theorem cexp_fexp_pos :
    ∀ ctx magnitude, cexp_fexp_posStatement ctx magnitude := by
  intro ctx magnitude beta fexp x ex h
  have hpow_pos : Exact.Rlt ctx (Exact.R0 ctx)
      (Exact.bpow ctx beta (Zsub ex Zone)) :=
    CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta (Zsub ex Zone)
  have hxpos : Exact.Rlt ctx (Exact.R0 ctx) x :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
      ctx _ _ _ hpow_pos h.1
  have hx0 : x ≠ Exact.R0 ctx := by
    intro hxzero
    subst x
    exact (ctx.certificate.orderedField.lt_irrefl _ hxpos).elim
  have hxle : Exact.Rle ctx (Exact.R0 ctx) x :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxpos |>.1
  have habs : Exact.Rabs ctx x = x := by
    change ctx.spec.abs x = x
    exact ctx.certificate.sourceLaws.abs_nonnegative x hxle
  have hposmag :
      Exact.Rle ctx (Exact.bpow ctx beta (Zsub ex Zone)) (Exact.Rabs ctx x) ∧
      Exact.Rlt ctx (Exact.Rabs ctx x) (Exact.bpow ctx beta ex) := by
    simpa only [habs] using h
  have hmag := (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_bound hx0
  have heq := pg_mag_unique ctx beta x hposmag hmag
  unfold Exact.cexp
  change fexp (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_val = fexp ex
  exact congrArg fexp heq.symm

end CompCert4Lean.Flocq.Core.Generic_fmt

namespace CompCert4Lean.Flocq.Core.Generic_fmt

theorem mantissa_small_pos :
    ∀ ctx, mantissa_small_posStatement ctx := by
  intro ctx beta fexp x ex hbounds hexp
  let p := Exact.bpow ctx beta (Zopp (fexp ex))
  let q := Exact.bpow ctx beta (fexp ex)
  have hp : Exact.Rlt ctx (Exact.R0 ctx) p := by
    dsimp [p]
    exact CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta (Zopp (fexp ex))
  have hbase : Exact.Rlt ctx (Exact.R0 ctx)
      (Exact.bpow ctx beta (Zsub ex Zone)) :=
    CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta (Zsub ex Zone)
  have hxpos : Exact.Rlt ctx (Exact.R0 ctx) x :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
      ctx _ _ _ hbase hbounds.1
  have hxpos' : Exact.Rlt ctx (Exact.IZR ctx Z0) x := by
    change ctx.spec.lt (ctx.spec.ofZ Z0) x
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    change ctx.spec.lt ctx.spec.zero x at hxpos
    exact hxpos
  have hp' : Exact.Rlt ctx (Exact.IZR ctx Z0) p := by
    change ctx.spec.lt (ctx.spec.ofZ Z0) p
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    change ctx.spec.lt ctx.spec.zero p at hp
    exact hp
  have hpos : Exact.Rlt ctx (Exact.R0 ctx) (Exact.Rmult ctx x p) := by
    have h :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_0_compat
        ctx x p hxpos' hp'
    change ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.mul x p) at h
    rw [ctx.certificate.sourceLaws.ofZ_zero] at h
    change ctx.spec.lt ctx.spec.zero (ctx.spec.mul x p)
    exact h
  have hpow_le : Exact.Rle ctx (Exact.bpow ctx beta ex) q := by
    dsimp [q]
    exact pg_bpow_le ctx beta hexp
  have hxq : Exact.Rlt ctx x q := by
    exact
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
        ctx _ _ _ hbounds.2 hpow_le
  have hq : Exact.Rlt ctx (Exact.R0 ctx) q := by
    dsimp [q]
    exact CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta (fexp ex)
  have hq' : Exact.Rlt ctx (Exact.IZR ctx Z0) q := by
    change ctx.spec.lt (ctx.spec.ofZ Z0) q
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    change ctx.spec.lt ctx.spec.zero q at hq
    exact hq
  have hpq : Exact.Rmult ctx p q = Exact.Rone ctx := by
    have hpow := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta
      (Zopp (fexp ex)) (fexp ex)
    change Exact.bpow ctx beta (Zadd (Zopp (fexp ex)) (fexp ex)) =
      Exact.Rmult ctx p q at hpow
    rw [pg_scaled_mantissa_exp_cancel_left, show Exact.bpow ctx beta Z0 =
      Exact.Rone ctx by rfl] at hpow
    exact hpow.symm
  change ctx.spec.mul p q = ctx.spec.one at hpq
  have hmul : Exact.Rlt ctx
      (Exact.Rmult ctx (Exact.Rmult ctx x p) q)
      (Exact.Rmult ctx (Exact.IZR ctx Zone) q) := by
    have hleft : Exact.Rmult ctx (Exact.Rmult ctx x p) q = x := by
      change ctx.spec.mul (ctx.spec.mul x p) q = x
      rw [ctx.certificate.orderedField.mul_assoc, hpq,
        ctx.certificate.orderedField.mul_one]
    have hright : Exact.Rmult ctx (Exact.IZR ctx Zone) q = q := by
      change ctx.spec.mul (ctx.spec.ofZ Zone) q = q
      rw [ctx.certificate.sourceLaws.ofZ_one,
        ctx.certificate.orderedField.one_mul]
    rw [hleft, hright]
    exact hxq
  have hlt : Exact.Rlt ctx (Exact.Rmult ctx x p) (Exact.IZR ctx Zone) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_reg_r
      ctx q (Exact.Rmult ctx x p) (Exact.IZR ctx Zone) hq' hmul
  exact ⟨hpos, by simpa [p] using hlt⟩

end CompCert4Lean.Flocq.Core.Generic_fmt

namespace CompCert4Lean.Flocq.Core.Generic_fmt

theorem scaled_mantissa_lt_1 :
    ∀ ctx magnitude, scaled_mantissa_lt_1Statement ctx magnitude := by
  intro ctx magnitude beta fexp _hvalid x ex hbound hexp
  by_cases hx0 : x = Exact.R0 ctx
  · subst x
    rw [scaled_mantissa_0 ctx magnitude beta fexp, pg_abs_zero]
    change ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ Zone)
    rw [ctx.certificate.sourceLaws.ofZ_one]
    exact pg_zero_lt_one ctx
  · rw [← scaled_mantissa_abs ctx magnitude beta fexp x]
    unfold Exact.scaled_mantissa
    rw [pg_cexp_abs ctx magnitude beta fexp x]
    unfold Exact.cexp
    have hm := (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_bound hx0
    have hmag_le : Zle (Exact.mag magnitude beta x) ex := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Exact.mag magnitude beta x) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex
      by_cases hle :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Exact.mag magnitude beta x) ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex
      · exact hle
      · have hlt :
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (Exact.mag magnitude beta x) := by omega
        have hleexp : Zle ex (Zsub (Exact.mag magnitude beta x) Zone) := by
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Zsub (Exact.mag magnitude beta x) Zone)
          simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Exact.mag magnitude beta x) - 1
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex <
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Exact.mag magnitude beta x) at hlt
          omega
        have hp := pg_bpow_le ctx beta hleexp
        have hmid :=
          CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
            ctx _ _ _ hm.1 hbound
        have hnotlt := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hmid |>.2
        exact (hnotlt hp).elim
    have hmag_fexp : Zle (Exact.mag magnitude beta x) (fexp ex) := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Exact.mag magnitude beta x) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp ex)
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Exact.mag magnitude beta x) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex at hmag_le
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexp ex) at hexp
      exact Int.le_trans hmag_le hexp
    have hfeq : fexp (Exact.mag magnitude beta x) = fexp ex :=
      (( _hvalid.valid_exp ex).2 hexp).2 _ hmag_fexp
    have hmag_fexp' : Zle (Exact.mag magnitude beta x)
        (fexp (Exact.mag magnitude beta x)) := by
      rw [hfeq]
      exact hmag_fexp
    exact mantissa_small_pos ctx beta fexp (Exact.Rabs ctx x)
      (Exact.mag magnitude beta x) hm hmag_fexp' |>.2

end CompCert4Lean.Flocq.Core.Generic_fmt

namespace CompCert4Lean.Flocq.Core.Generic_fmt

theorem mantissa_DN_small_pos :
    ∀ ctx, mantissa_DN_small_posStatement ctx := by
  intro ctx beta fexp x ex hbounds hexp
  apply CompCert4Lean.Flocq.Core.Raux.Zfloor_imp ctx Z0
  have h := mantissa_small_pos ctx beta fexp x ex hbounds hexp
  constructor
  · have hle := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h.1 |>.1
    change ctx.spec.le (ctx.spec.ofZ Z0) _
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hle
  · exact h.2

end CompCert4Lean.Flocq.Core.Generic_fmt
