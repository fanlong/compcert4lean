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

def valid_rnd_NStatement : Prop :=
  ∀ choice : Z → Bool, Valid_rnd (Znearest choice)

def valid_rnd_DNStatement : Prop := Valid_rnd Zfloor

/- The proof phase constructs the mandatory certificate.  These adapters then
   restore the source Global Instance results without a hidden or fabricated
   inhabitant. -/
instance valid_rnd_N [certificate : Valid_rnd_Certificate]
    (choice : Z → Bool) : Valid_rnd (Znearest choice) :=
  certificate.nearest choice

instance valid_rnd_DN [certificate : Valid_rnd_Certificate] : Valid_rnd Zfloor :=
  certificate.down

/-! Generated and directly implemented surfaces. -/

def Znearest_DN_or_UPStatement : Prop :=
  ∀ choice x, Znearest choice x = Zfloor x ∨ Znearest choice x = Zceil x

def Znearest_ge_floorStatement : Prop :=
  ∀ choice x, Zle (Zfloor x) (Znearest choice x)

def Znearest_le_ceilStatement : Prop :=
  ∀ choice x, Zle (Znearest choice x) (Zceil x)

def Znearest_oppStatement : Prop :=
  ∀ choice x,
    Znearest choice (Ropp x) =
      Zopp (Znearest (fun t => Bool.not (choice (Zopp (Zadd t Zone)))) x)

def Zrnd_DN_or_UPStatement : Prop :=
  ∀ rnd, Valid_rnd rnd → ∀ x, rnd x = Zfloor x ∨ rnd x = Zceil x

def Zrnd_ZR_or_AWStatement : Prop :=
  ∀ rnd, Valid_rnd rnd → ∀ x, rnd x = Ztrunc x ∨ rnd x = Zaway x

def canonical_uniqueStatement : Prop :=
  ∀ beta fexp f1 f2,
    canonical beta fexp f1 → canonical beta fexp f2 →
      F2R f1 = F2R f2 → f1 = f2

def cexp_absStatement : Prop :=
  ∀ beta fexp x, cexp beta fexp (Rabs x) = cexp beta fexp x

def cexp_fexpStatement : Prop :=
  ∀ beta fexp x ex,
    (Rle (bpow beta (Zsub ex Zone)) (Rabs x) ∧ Rlt (Rabs x) (bpow beta ex)) →
      cexp beta fexp x = fexp ex

def cexp_fexp_posStatement : Prop :=
  ∀ beta fexp x ex,
    (Rle (bpow beta (Zsub ex Zone)) x ∧ Rlt x (bpow beta ex)) →
      cexp beta fexp x = fexp ex

def cexp_oppStatement : Prop :=
  ∀ beta fexp x, cexp beta fexp (Ropp x) = cexp beta fexp x

def cexp_round_geStatement : Prop :=
  ∀ beta fexp rnd,
    Valid_exp fexp → Monotone_exp fexp → Valid_rnd rnd →
      ∀ x, round beta fexp rnd x ≠ R0 →
        Zle (cexp beta fexp x) (cexp beta fexp (round beta fexp rnd x))

def generic_format_0Statement : Prop :=
  ∀ beta fexp, generic_format beta fexp R0

def generic_format_EMStatement : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ x, generic_format beta fexp x ∨ ¬ generic_format beta fexp x

def generic_format_F2RStatement : Prop :=
  ∀ beta fexp m e,
    (m ≠ Z0 → Zle (cexp beta fexp (F2R (Float beta m e))) e) →
      generic_format beta fexp (F2R (Float beta m e))

def generic_format_absStatement : Prop :=
  ∀ beta fexp, ∀ x, generic_format beta fexp x → generic_format beta fexp (Rabs x)

def generic_format_abs_invStatement : Prop :=
  ∀ beta fexp, ∀ x, generic_format beta fexp (Rabs x) → generic_format beta fexp x

def generic_format_bpowStatement : Prop :=
  ∀ beta fexp e,
    Zle (fexp (Zadd e Zone)) e → generic_format beta fexp (bpow beta e)

def generic_format_bpow'Statement : Prop :=
  ∀ beta fexp e, Valid_exp fexp → Zle (fexp e) e → generic_format beta fexp (bpow beta e)

def generic_format_bpow_invStatement : Prop :=
  ∀ beta fexp e, Valid_exp fexp → generic_format beta fexp (bpow beta e) → Zle (fexp e) e

def generic_format_bpow_inv'Statement : Prop :=
  ∀ beta fexp e, generic_format beta fexp (bpow beta e) →
    Zle (fexp (Zadd e Zone)) e

def generic_format_canonicalStatement : Prop :=
  ∀ beta fexp f, canonical beta fexp f → generic_format beta fexp (F2R f)

def generic_format_ge_bpowStatement : Prop :=
  ∀ beta fexp emin,
    (∀ e, Zle emin (fexp e)) → ∀ x, Rlt R0 x → generic_format beta fexp x → Rle (bpow beta emin) x

def generic_format_oppStatement : Prop :=
  ∀ beta fexp, ∀ x, generic_format beta fexp x → generic_format beta fexp (Ropp x)

def generic_format_roundStatement : Prop :=
  ∀ beta fexp rnd, Valid_exp fexp → Valid_rnd rnd → ∀ x,
    generic_format beta fexp (round beta fexp rnd x)

def generic_format_round_posStatement : Prop :=
  ∀ beta fexp rnd x, Valid_exp fexp → Valid_rnd rnd →
    Rlt R0 x → generic_format beta fexp (round beta fexp rnd x)

def generic_inclusionStatement : Prop :=
  ∀ beta fexp1 fexp2 e, Valid_exp fexp1 → Valid_exp fexp2 →
    Zle (fexp2 e) (fexp1 e) → ∀ x,
      (Rle (bpow beta (Zsub e Zone)) (Rabs x) ∧ Rle (Rabs x) (bpow beta e)) →
        generic_format beta fexp1 x → generic_format beta fexp2 x

def generic_inclusion_leStatement : Prop :=
  ∀ beta fexp1 fexp2 e2, Valid_exp fexp1 → Valid_exp fexp2 →
    (∀ e, Zle e e2 → Zle (fexp2 e) (fexp1 e)) → ∀ x,
      Rle (Rabs x) (bpow beta e2) → generic_format beta fexp1 x → generic_format beta fexp2 x

def generic_inclusion_magStatement : Prop :=
  ∀ beta fexp1 fexp2 x,
    (x ≠ R0 → Zle (fexp2 (mag beta x)) (fexp1 (mag beta x))) →
      generic_format beta fexp1 x → generic_format beta fexp2 x

def lt_cexp_posStatement : Prop :=
  ∀ beta fexp x y, Monotone_exp fexp → Rlt R0 y →
    Zlt (cexp beta fexp x) (cexp beta fexp y) → Rlt x y

def mag_generic_gtStatement : Prop :=
  ∀ beta fexp x, Valid_exp fexp → x ≠ R0 → generic_format beta fexp x →
    Zlt (cexp beta fexp x) (mag beta x)

def mag_round_ZRStatement : Prop :=
  ∀ beta fexp, Valid_exp fexp →
    ∀ x, round beta fexp Ztrunc x ≠ R0 →
      (mag beta (round beta fexp Ztrunc x) : Z) = (mag beta x : Z)

def mag_round_geStatement : Prop :=
  ∀ beta fexp, Valid_exp fexp →
    ∀ rnd, Valid_rnd rnd →
      ∀ x, round beta fexp rnd x ≠ R0 →
        Zle (mag beta x) (mag beta (round beta fexp rnd x))

def mantissa_small_posStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) x ex,
    (Rle (bpow beta (Zsub ex Zone)) x ∧ Rlt x (bpow beta ex)) →
      Zle ex (fexp ex) →
        Rlt R0 (Rmult x (bpow beta (Zopp (fexp ex)))) ∧
          Rlt (Rmult x (bpow beta (Zopp (fexp ex)))) ⟨1⟩

def round_0Statement : Prop :=
  ∀ beta fexp rnd, Valid_rnd rnd → round beta fexp rnd R0 = R0

def round_AW_UPStatement : Prop :=
  ∀ beta fexp x, Rle R0 x →
    round beta fexp Zaway x = round beta fexp Zceil x

def round_AW_absStatement : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ x,
    round beta fexp Zaway (Rabs x) = Rabs (round beta fexp Zaway x)

def round_AW_oppStatement : Prop :=
  ∀ beta fexp x, round beta fexp Zaway (Ropp x) = Ropp (round beta fexp Zaway x)

def round_DN_oppStatement : Prop :=
  ∀ beta fexp x, round beta fexp Zfloor (Ropp x) = Ropp (round beta fexp Zceil x)

def round_DN_or_UPStatement : Prop :=
  ∀ beta fexp rnd, Valid_rnd rnd → ∀ x,
    round beta fexp rnd x = round beta fexp Zfloor x ∨ round beta fexp rnd x = round beta fexp Zceil x

def round_DN_ptStatement : Prop :=
  ∀ beta fexp x, Valid_exp fexp → Rnd_DN_pt (generic_format beta fexp) x (round beta fexp Zfloor x)

def round_UP_oppStatement : Prop :=
  ∀ beta fexp x, round beta fexp Zceil (Ropp x) = Ropp (round beta fexp Zfloor x)

def round_UP_ptStatement : Prop :=
  ∀ beta fexp x, Valid_exp fexp → Rnd_UP_pt (generic_format beta fexp) x (round beta fexp Zceil x)

def round_ZR_DNStatement : Prop :=
  ∀ beta fexp x, Rle R0 x → round beta fexp Ztrunc x = round beta fexp Zfloor x

def round_ZR_absStatement : Prop :=
  ∀ beta fexp x, Valid_exp fexp → round beta fexp Ztrunc (Rabs x) = Rabs (round beta fexp Ztrunc x)

def round_ZR_oppStatement : Prop :=
  ∀ beta fexp x, round beta fexp Ztrunc (Ropp x) = Ropp (round beta fexp Ztrunc x)

def round_ZR_or_AWStatement : Prop :=
  ∀ beta fexp rnd, Valid_rnd rnd → ∀ x,
    round beta fexp rnd x = round beta fexp Ztrunc x ∨ round beta fexp rnd x = round beta fexp Zaway x

def round_bounded_large_posStatement : Prop :=
  ∀ beta fexp rnd, Valid_rnd rnd → ∀ x ex,
    Zlt (fexp ex) ex →
      (Rle (bpow beta (Zsub ex Zone)) x ∧ Rlt x (bpow beta ex)) →
        Rle (bpow beta (Zsub ex Zone)) (round beta fexp rnd x) ∧
          Rle (round beta fexp rnd x) (bpow beta ex)

def round_bounded_small_posStatement : Prop :=
  ∀ beta fexp rnd, Valid_rnd rnd → ∀ x ex,
    Zle ex (fexp ex) →
      (Rle (bpow beta (Zsub ex Zone)) x ∧ Rlt x (bpow beta ex)) →
        round beta fexp rnd x = R0 ∨ round beta fexp rnd x = bpow beta (fexp ex)

def round_ge_genericStatement : Prop :=
  ∀ beta fexp rnd x y, Valid_exp fexp → Valid_rnd rnd →
    generic_format beta fexp x → Rle x y → Rle x (round beta fexp rnd y)

def round_genericStatement : Prop :=
  ∀ beta fexp rnd, Valid_rnd rnd → ∀ x,
    generic_format beta fexp x → round beta fexp rnd x = x

def round_large_pos_ge_bpowStatement : Prop :=
  ∀ beta fexp rnd, Valid_rnd rnd → ∀ x e,
    Rlt R0 (round beta fexp rnd x) → Rle (bpow beta e) x →
      Rle (bpow beta e) (round beta fexp rnd x)

def round_leStatement : Prop :=
  ∀ beta fexp rnd x y, Valid_exp fexp → Valid_rnd rnd →
    Rle x y → Rle (round beta fexp rnd x) (round beta fexp rnd y)

def round_le_genericStatement : Prop :=
  ∀ beta fexp rnd x y, Valid_exp fexp → Valid_rnd rnd →
    generic_format beta fexp y → Rle x y → Rle (round beta fexp rnd x) y

def round_le_posStatement : Prop :=
  ∀ beta fexp rnd x y, Valid_exp fexp → Valid_rnd rnd →
    Rlt R0 x → Rle x y → Rle (round beta fexp rnd x) (round beta fexp rnd y)

def scaled_mantissa_0Statement : Prop :=
  ∀ beta fexp, scaled_mantissa beta fexp R0 = R0

def scaled_mantissa_absStatement : Prop :=
  ∀ beta fexp, ∀ x,
    scaled_mantissa beta fexp (Rabs x) = Rabs (scaled_mantissa beta fexp x)

def scaled_mantissa_genericStatement : Prop :=
  ∀ beta fexp x, generic_format beta fexp x →
    scaled_mantissa beta fexp x = IZR (Ztrunc (scaled_mantissa beta fexp x))

def scaled_mantissa_lt_1Statement : Prop :=
  ∀ beta fexp x ex, Valid_exp fexp →
    Rlt (Rabs x) (bpow beta ex) → Zle ex (fexp ex) →
      Rlt (Rabs (scaled_mantissa beta fexp x)) ⟨1⟩

def scaled_mantissa_mult_bpowStatement : Prop :=
  ∀ beta fexp x,
    Rmult (scaled_mantissa beta fexp x) (bpow beta (cexp beta fexp x)) = x

def scaled_mantissa_oppStatement : Prop :=
  ∀ beta fexp x,
    scaled_mantissa beta fexp (Ropp x) = Ropp (scaled_mantissa beta fexp x)

def valid_exp_large'Statement : Prop :=
  ∀ fexp, Valid_exp fexp → ∀ k l,
    Zlt (fexp k) k → Zle l k → Zlt (fexp l) k

def abs_round_ge_genericStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (rnd : R → Z),
    Valid_exp fexp → Valid_rnd rnd →
      ∀ x y, generic_format beta fexp x →
        Rle x (Rabs y) → Rle x (Rabs (round beta fexp rnd y))

def abs_round_le_genericStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (rnd : R → Z),
    Valid_exp fexp → Valid_rnd rnd →
      ∀ x y, generic_format beta fexp y →
        Rle (Rabs x) y → Rle (Rabs (round beta fexp rnd x)) y

def canonical_0Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z),
    canonical beta fexp (Float beta Z0 (cexp beta fexp R0))

def canonical_absStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (m e : Z),
    canonical beta fexp (Float beta m e) →
      canonical beta fexp (Float beta (Zabs m) e)

def canonical_generic_formatStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), ∀ x,
    generic_format beta fexp x →
      ∃ f : float beta, x = F2R f ∧ canonical beta fexp f

def canonical_oppStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (m e : Z),
    canonical beta fexp (Float beta m e) →
      canonical beta fexp (Float beta (Zopp m) e)

def cexp_DNStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x,
    Rlt R0 (round beta fexp Zfloor x) →
      cexp beta fexp (round beta fexp Zfloor x) = cexp beta fexp x

def exp_small_round_0Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (rnd : R → Z),
    Valid_exp fexp → Valid_rnd rnd → ∀ x ex,
      (Rle (bpow beta (Zsub ex Zone)) (Rabs x) ∧
        Rlt (Rabs x) (bpow beta ex)) →
      round beta fexp rnd x = R0 → Zle ex (fexp ex)

def exp_small_round_0_posStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (rnd : R → Z), Valid_rnd rnd → ∀ x ex,
    (Rle (bpow beta (Zsub ex Zone)) x ∧ Rlt x (bpow beta ex)) →
    round beta fexp rnd x = R0 → Zle ex (fexp ex)

def generic_format_F2R'Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z),
    ∀ (x : R) (f : float beta), F2R f = x →
      (x ≠ R0 → Zle (cexp beta fexp x) (Fexp f)) →
      generic_format beta fexp x

def generic_format_satisfies_anyStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    satisfies_any (generic_format beta fexp)

def mag_DNStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x,
    Rlt R0 (round beta fexp Zfloor x) →
      (mag beta (round beta fexp Zfloor x) : Z) = (mag beta x : Z)

def mantissa_DN_small_posStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (x : R) (ex : Z),
    (Rle (bpow beta (Zsub ex Zone)) x ∧ Rlt x (bpow beta ex)) →
      Zle ex (fexp ex) →
      Zfloor (Rmult x (bpow beta (Zopp (fexp ex)))) = Z0

def mantissa_UP_small_posStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (x : R) (ex : Z),
    (Rle (bpow beta (Zsub ex Zone)) x ∧ Rlt x (bpow beta ex)) →
      Zle ex (fexp ex) →
      Zceil (Rmult x (bpow beta (Zopp (fexp ex)))) = Zone

def round_DN_UP_ltStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x,
    ¬ generic_format beta fexp x →
      Rlt (round beta fexp Zfloor x) x ∧
        Rlt x (round beta fexp Zceil x)

def round_DN_small_posStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (x : R) (ex : Z),
    (Rle (bpow beta (Zsub ex Zone)) x ∧ Rlt x (bpow beta ex)) →
      Zle ex (fexp ex) → round beta fexp Zfloor x = R0

def round_N_oppStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (choice : Z → Bool),
    Valid_exp fexp → ∀ x,
      round beta fexp (Znearest choice) (Ropp x) =
        Ropp (round beta fexp
          (Znearest (fun t => Bool.not (choice (Zopp (Zadd t Zone))))) x)

def round_N_ptStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (choice : Z → Bool) (x : R),
    Rnd_N_pt (generic_format beta fexp) x
      (round beta fexp (Znearest choice) x)

def round_UP_small_posStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (x : R) (ex : Z),
    (Rle (bpow beta (Zsub ex Zone)) x ∧ Rlt x (bpow beta ex)) →
      Zle ex (fexp ex) →
      round beta fexp Zceil x = bpow beta (fexp ex)

def round_abs_absStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (P : R → R → Prop),
    (∀ (rnd : R → Z), Valid_rnd rnd → ∀ x, Rle R0 x →
      P x (round beta fexp rnd x)) →
    ∀ (rnd : R → Z), Valid_rnd rnd → ∀ x,
      P (Rabs x) (Rabs (round beta fexp rnd x))

def round_oppStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (rnd : R → Z),
    ∀ x,
      round beta fexp rnd (Ropp x) =
        Ropp (round beta fexp (Zrnd_opp rnd) x)

end CompCert4Lean.Flocq.Core.Generic_fmt
