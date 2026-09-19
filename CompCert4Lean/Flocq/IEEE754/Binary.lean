import CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

/-!
# IEEE-754 binary floats with payload-carrying NaNs

This is the definition-translation surface for `Flocq.IEEE754.Binary`.
Proof-bearing source declarations in this packet are represented by exact
source-shaped proposition descriptors below.
-/

namespace CompCert4Lean.Flocq.IEEE754.Binary

open CompCert4Lean.Flocq.Core

abbrev R := Raux.R
abbrev Z := Raux.Z
abbrev positive := Raux.positive
abbrev comparison := Raux.comparison
abbrev Lt : comparison := Raux.Lt
abbrev Eq : comparison := Raux.Eq
abbrev Gt : comparison := Raux.Gt
abbrev radix := Raux.radix
abbrev radix2 := Zaux.radix2
abbrev Z0 : Z := Zaux.Z0
abbrev Zone : Z := Zaux.Zone
abbrev Ztwo : Z := Zaux.Ztwo
abbrev Zpos := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
abbrev Zneg := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg
abbrev Zadd := Zaux.Zadd
abbrev Zsub := Zaux.Zsub
abbrev Zmul := Zaux.Zmul
abbrev Zopp := Zaux.Zopp
abbrev Zabs := Zaux.Zabs
abbrev Zeven := Zaux.Zeven
abbrev Zcompare := Zaux.Zcompare
abbrev Zeq_bool := Zaux.Zeq_bool
abbrev Zle := Zaux.Zle
abbrev Zlt := Zaux.Zlt
abbrev Zle_bool := Zaux.Zle_bool
abbrev Zlt_bool := Zaux.Zlt_bool
abbrev Zpower := Zaux.Zpower
abbrev IZR := Raux.IZR
abbrev R0 := Raux.R0
abbrev Rone := Raux.Rone
abbrev Rtwo := Raux.Rtwo
abbrev Rplus := Raux.Rplus
abbrev Rminus := Raux.Rminus
abbrev Rmult := Raux.Rmult
abbrev Rdiv := Raux.Rdiv
abbrev Ropp := Raux.Ropp
abbrev Rabs := Raux.Rabs
abbrev Rlt := Raux.Rlt
abbrev Rle := Raux.Rle
abbrev Rcompare := Raux.Rcompare
abbrev Rlt_bool := Raux.Rlt_bool
abbrev bpow := Raux.bpow
abbrev sqrt := Raux.sqrt
abbrev mag := Raux.mag

abbrev float := Core.Defs.float
abbrev Float (beta : radix) (m e : Z) : float beta := Core.Defs.float.mk m e
abbrev Fnum {beta : radix} (f : float beta) : Z := Core.Defs.Fnum f
abbrev Fexp {beta : radix} (f : float beta) : Z := Core.Defs.Fexp f
abbrev F2R {beta : radix} (f : float beta) : R := Core.Defs.F2R f

abbrev Valid_exp := Core.Generic_fmt.Valid_exp
abbrev generic_format := Core.Generic_fmt.generic_format
abbrev canonical := Core.Generic_fmt.canonical
abbrev cexp := Core.Generic_fmt.cexp
abbrev round := Core.Generic_fmt.round
abbrev spec_float := BinarySingleNaN.spec_float
abbrev S754_zero := BinarySingleNaN.S754_zero
abbrev S754_infinity := BinarySingleNaN.S754_infinity
abbrev S754_nan := BinarySingleNaN.S754_nan
abbrev S754_finite := BinarySingleNaN.S754_finite
abbrev location := BinarySingleNaN.location
abbrev loc_Exact := BinarySingleNaN.loc_Exact
abbrev loc_Inexact := BinarySingleNaN.loc_Inexact
abbrev shr_record := BinarySingleNaN.shr_record
abbrev shr_m := BinarySingleNaN.shr_m
abbrev shr_r := BinarySingleNaN.shr_r
abbrev shr_1 := BinarySingleNaN.shr_1
abbrev shr := BinarySingleNaN.shr
abbrev loc_of_shr_record := BinarySingleNaN.loc_of_shr_record
abbrev shr_record_of_loc := BinarySingleNaN.shr_record_of_loc
abbrev SFcompare := BinarySingleNaN.SFcompare
abbrev bounded0 := BinarySingleNaN.bounded0
abbrev canonical_mantissa0 := BinarySingleNaN.canonical_mantissa0
abbrev emin0 := BinarySingleNaN.emin0
abbrev fexp0 := BinarySingleNaN.fexp0
abbrev cond_Zopp := BinarySingleNaN.cond_Zopp
variable {prec emax : Z} [Core.FLX.Prec_gt_0 prec]
  [BinarySingleNaN.Prec_lt_emax prec emax]

inductive full_float where
  | F754_zero (s : Bool)
  | F754_infinity (s : Bool)
  | F754_nan (s : Bool) (m : positive)
  | F754_finite (s : Bool) (m : positive) (e : Z)

export full_float (F754_zero F754_infinity F754_nan F754_finite)

def FF2SF (x : full_float) : spec_float :=
  match x with
  | .F754_zero s => S754_zero s
  | .F754_infinity s => S754_infinity s
  | .F754_nan _ _ => S754_nan
  | .F754_finite s m e => S754_finite s m e

def SF2FF (x : spec_float) : full_float :=
  match x with
  | .S754_zero s => F754_zero s
  | .S754_infinity s => F754_infinity s
  | .S754_nan => F754_nan false .xH
  | .S754_finite s m e => F754_finite s m e

def is_nan_FF (f : full_float) : Bool :=
  match f with
  | .F754_nan _ _ => true
  | _ => false

abbrev emin : Z := emin0 prec emax
abbrev fexp : Z → Z := fexp0 prec emax

/- The source records this as a global instance.  DMC-003 keeps the exact
   proposition in a mandatory proof-phase certificate; executable definitions
   do not synthesize or carry a proof value. -/
class FexpCorrectCertificate (prec emax : Z)
    [Core.FLX.Prec_gt_0 prec] [BinarySingleNaN.Prec_lt_emax prec emax] : Prop where
  valid : Valid_exp (fexp (prec := prec) (emax := emax))

def fexp_correctStatement : Prop :=
  Valid_exp (fexp (prec := prec) (emax := emax))

instance fexp_correct [certificate : FexpCorrectCertificate prec emax] :
    Valid_exp (fexp (prec := prec) (emax := emax)) :=
  certificate.valid

abbrev bounded : positive → Z → Bool := bounded0 prec emax

def nan_pl (pl : positive) : Bool :=
  Zlt_bool (Zpos (BinarySingleNaN.digits2_pos pl)) prec

def valid_binary (x : full_float) : Bool :=
  match x with
  | .F754_finite _ m e => bounded (prec := prec) (emax := emax) m e
  | .F754_nan _ pl => nan_pl (prec := prec) pl
  | _ => true

def FF2BObligation (x : full_float) : Prop :=
  valid_binary (prec := prec) (emax := emax) x = true

inductive binary_float (prec emax : Z) where
  | B754_zero (s : Bool)
  | B754_infinity (s : Bool)
  | B754_nan (s : Bool) (pl : positive)
  | B754_finite (s : Bool) (m : positive) (e : Z)

export binary_float (B754_zero B754_infinity B754_nan B754_finite)

def B754_nanObligation (pl : positive) : Prop :=
  nan_pl (prec := prec) pl = true

def B754_finiteObligation (m : positive) (e : Z) : Prop :=
  bounded (prec := prec) (emax := emax) m e = true

/-! The executable carrier is intentionally proof-erased, but construction is
    never allowed to cross the certified seam without its source validity
    witness.  The explicitly named raw helper is retained only as a
    compatibility layer; certified consumers use `FF2B` and receive the
    companion certificate together with the value. -/
def FF2B_unchecked (x : full_float) : binary_float prec emax :=
  match x with
  | .F754_finite s m e => .B754_finite s m e
  | .F754_infinity s => B754_infinity s
  | .F754_zero s => B754_zero s
  | .F754_nan s pl => .B754_nan s pl

def B2BSN (x : binary_float prec emax) : BinarySingleNaN.binary_float prec emax :=
  match x with
  | .B754_zero s => BinarySingleNaN.B754_zero s
  | .B754_infinity s => BinarySingleNaN.B754_infinity s
  | .B754_nan _ _ => BinarySingleNaN.B754_nan
  | .B754_finite s m e => BinarySingleNaN.B754_finite s m e

def B2FF (x : binary_float prec emax) : full_float :=
  match x with
  | .B754_finite s m e => F754_finite s m e
  | .B754_infinity s => F754_infinity s
  | .B754_zero s => F754_zero s
  | .B754_nan s pl => F754_nan s pl

def BinaryFloatCertificate (x : binary_float prec emax) : Prop :=
  valid_binary (prec := prec) (emax := emax) (B2FF x) = true

abbrev CertifiedBinaryFloat (prec emax : Z) :=
  { x : binary_float prec emax // BinaryFloatCertificate x }

abbrev CertifiedSingleNaN (prec emax : Z) :=
  BinarySingleNaN.CertifiedBinaryFloat prec emax

def B2BSN_result_obligation : Prop :=
  ∀ (x : CertifiedBinaryFloat prec emax),
    BinarySingleNaN.BinaryFloatCertificate (B2BSN x.1)

def mkB754_nan (s : Bool) (pl : positive)
    (h : B754_nanObligation (prec := prec) pl) :
    CertifiedBinaryFloat prec emax :=
  ⟨.B754_nan s pl, by
    simpa [BinaryFloatCertificate, B2FF, valid_binary, nan_pl,
      B754_nanObligation] using h⟩

def mkB754_finite (s : Bool) (m : positive) (e : Z)
    (h : B754_finiteObligation (prec := prec) (emax := emax) m e) :
    CertifiedBinaryFloat prec emax :=
  ⟨.B754_finite s m e, by
    simpa [BinaryFloatCertificate, B2FF, valid_binary,
      B754_finiteObligation] using h⟩

def FF2B (x : full_float) (Hx : FF2BObligation (prec := prec) (emax := emax) x) :
    CertifiedBinaryFloat prec emax :=
  ⟨FF2B_unchecked x, by
    cases x <;> simpa [FF2B_unchecked, FF2BObligation, valid_binary,
      BinaryFloatCertificate, B2FF] using Hx⟩

def FF2BCertificateStatement : Prop :=
  ∀ (x : full_float),
    ∀ (Hx : FF2BObligation (prec := prec) (emax := emax) x),
      BinaryFloatCertificate
        (FF2B (prec := prec) (emax := emax) x Hx).1

def B2R (f : binary_float prec emax) : R :=
  match f with
  | .B754_finite s m e => F2R (Float radix2 (cond_Zopp s (Zpos m)) e)
  | _ => R0

def B2SF (x : binary_float prec emax) : spec_float :=
  match x with
  | .B754_finite s m e => S754_finite s m e
  | .B754_infinity s => S754_infinity s
  | .B754_zero s => S754_zero s
  | .B754_nan _ _ => S754_nan

def is_finite_strict (f : binary_float prec emax) : Bool :=
  match f with
  | .B754_finite _ _ _ => true
  | _ => false

def Bsign (x : binary_float prec emax) : Bool :=
  match x with
  | .B754_nan s _ => s
  | .B754_zero s => s
  | .B754_infinity s => s
  | .B754_finite s _ _ => s

def is_finite (f : binary_float prec emax) : Bool :=
  match f with
  | .B754_finite _ _ _ | .B754_zero _ => true
  | _ => false

def is_nan (f : binary_float prec emax) : Bool :=
  match f with
  | .B754_nan _ _ => true
  | _ => false

abbrev CertifiedNaNResult (prec emax : Z) :=
  { x : binary_float prec emax //
      is_nan x = true ∧ BinaryFloatCertificate x }

def get_nan_pl (x : binary_float prec emax) : positive :=
  match x with
  | .B754_nan _ pl => pl
  | _ => .xH

def build_nan (x : { x : binary_float prec emax // is_nan x = true }) :
    binary_float prec emax :=
  match x with
  | ⟨.B754_nan s pl, _⟩ => .B754_nan s pl
  | ⟨.B754_zero _, hx⟩ => nomatch hx
  | ⟨.B754_infinity _, hx⟩ => nomatch hx
  | ⟨.B754_finite _ _ _, hx⟩ => nomatch hx

def build_nan_result_obligation : Prop :=
  ∀ (x : CertifiedNaNResult prec emax),
    BinaryFloatCertificate (build_nan ⟨x.1, x.2.1⟩)

def BSN2B (nan : { x : binary_float prec emax // is_nan x = true })
    (x : BinarySingleNaN.binary_float prec emax) : binary_float prec emax :=
  match x with
  | .B754_nan => build_nan nan
  | .B754_zero s => B754_zero s
  | .B754_infinity s => B754_infinity s
  | .B754_finite s m e => .B754_finite s m e

def BSN2B' (x : BinarySingleNaN.binary_float prec emax)
    : BinarySingleNaN.is_nan x = false → binary_float prec emax :=
  match x with
  | .B754_zero s => fun _ => B754_zero s
  | .B754_infinity s => fun _ => B754_infinity s
  | .B754_nan => fun h => nomatch h
  | .B754_finite s m e => fun _ => .B754_finite s m e

def BSN2B_result_obligation : Prop :=
  ∀ (nan : CertifiedNaNResult prec emax)
    (x : CertifiedSingleNaN prec emax),
    BinaryFloatCertificate (BSN2B ⟨nan.1, nan.2.1⟩ x.1)

def BSN2B'_result_obligation : Prop :=
  ∀ (x : CertifiedSingleNaN prec emax)
    (Nx : BinarySingleNaN.is_nan x.1 = false),
    BinaryFloatCertificate (BSN2B' x.1 Nx)

def Bopp (opp_nan : binary_float prec emax → CertifiedNaNResult prec emax)
    (x : binary_float prec emax) : binary_float prec emax :=
  match x with
  | .B754_nan s pl =>
      let r := opp_nan (.B754_nan s pl)
      build_nan ⟨r.1, r.2.1⟩
  | .B754_infinity s => B754_infinity (!s)
  | .B754_finite s m e => .B754_finite (!s) m e
  | .B754_zero s => B754_zero (!s)

def Babs (abs_nan : binary_float prec emax → CertifiedNaNResult prec emax)
    (x : binary_float prec emax) : binary_float prec emax :=
  match x with
  | .B754_nan s pl =>
      let r := abs_nan (.B754_nan s pl)
      build_nan ⟨r.1, r.2.1⟩
  | .B754_infinity _ => B754_infinity false
  | .B754_finite _ m e => .B754_finite false m e
  | .B754_zero _ => B754_zero false

def Bcompare (f1 f2 : binary_float prec emax) : Option comparison :=
  BinarySingleNaN.Bcompare (B2BSN f1) (B2BSN f2)

def binary_overflow (m : BinarySingleNaN.mode) (s : Bool) : full_float :=
  SF2FF (BinarySingleNaN.binary_overflow (prec := prec) (emax := emax) m s)

def Bmult (mult_nan : binary_float prec emax → binary_float prec emax →
      CertifiedNaNResult prec emax)
    (m : BinarySingleNaN.mode) (x y : binary_float prec emax) : binary_float prec emax :=
  BSN2B ⟨(mult_nan x y).1, (mult_nan x y).2.1⟩
    (BinarySingleNaN.Bmult (prec := prec) (emax := emax) m (B2BSN x) (B2BSN y))

/- The source applies `BSN2B'` with the exact non-NaN proof for every
   normalization invocation.  DMC-003 defers construction of that proof while
   keeping the proof-gated conversion boundary mandatory. -/
class BinaryNormalizeCertificate (prec emax : Z)
    [Core.FLX.Prec_gt_0 prec] [BinarySingleNaN.Prec_lt_emax prec emax] : Prop where
  is_nan_binary_normalize :
    ∀ (m : BinarySingleNaN.mode) (x e : Z) (szero : Bool),
      BinarySingleNaN.is_nan
          (BinarySingleNaN.binary_normalize (prec := prec) (emax := emax) m x e szero) = false

def binary_normalize (m : BinarySingleNaN.mode) (x e : Z) (szero : Bool)
    [certificate : BinaryNormalizeCertificate prec emax] : binary_float prec emax :=
  BSN2B' (BinarySingleNaN.binary_normalize (prec := prec) (emax := emax) m x e szero)
    (certificate.is_nan_binary_normalize m x e szero)

def binary_normalize_result_obligation
    [BinaryNormalizeCertificate prec emax] : Prop :=
  ∀ (m : BinarySingleNaN.mode) (x e : Z) (szero : Bool),
    BinaryFloatCertificate
      (binary_normalize (prec := prec) (emax := emax) m x e szero)

def Bplus (plus_nan : binary_float prec emax → binary_float prec emax →
      CertifiedNaNResult prec emax)
    (m : BinarySingleNaN.mode) (x y : binary_float prec emax) : binary_float prec emax :=
  BSN2B ⟨(plus_nan x y).1, (plus_nan x y).2.1⟩
    (BinarySingleNaN.Bplus (prec := prec) (emax := emax) m (B2BSN x) (B2BSN y))

def Bminus (minus_nan : binary_float prec emax → binary_float prec emax →
      CertifiedNaNResult prec emax)
    (m : BinarySingleNaN.mode) (x y : binary_float prec emax) : binary_float prec emax :=
  BSN2B ⟨(minus_nan x y).1, (minus_nan x y).2.1⟩
    (BinarySingleNaN.Bminus (prec := prec) (emax := emax) m (B2BSN x) (B2BSN y))

def Bdiv (div_nan : binary_float prec emax → binary_float prec emax →
      CertifiedNaNResult prec emax)
    (m : BinarySingleNaN.mode) (x y : binary_float prec emax) : binary_float prec emax :=
  BSN2B ⟨(div_nan x y).1, (div_nan x y).2.1⟩
    (BinarySingleNaN.Bdiv (prec := prec) (emax := emax) m (B2BSN x) (B2BSN y))

def Bsqrt (sqrt_nan : binary_float prec emax → CertifiedNaNResult prec emax)
    (m : BinarySingleNaN.mode) (x : binary_float prec emax) : binary_float prec emax :=
  BSN2B ⟨(sqrt_nan x).1, (sqrt_nan x).2.1⟩
    (BinarySingleNaN.Bsqrt (prec := prec) (emax := emax) m (B2BSN x))

def Bopp_result_obligation : Prop :=
  ∀ (opp_nan : binary_float prec emax → CertifiedNaNResult prec emax)
    (x : CertifiedBinaryFloat prec emax),
    BinaryFloatCertificate (Bopp opp_nan x.1)

def Babs_result_obligation : Prop :=
  ∀ (abs_nan : binary_float prec emax → CertifiedNaNResult prec emax)
    (x : CertifiedBinaryFloat prec emax),
    BinaryFloatCertificate (Babs abs_nan x.1)

def Bmult_result_obligation : Prop :=
  ∀ (mult_nan : binary_float prec emax → binary_float prec emax → CertifiedNaNResult prec emax)
    (m : BinarySingleNaN.mode) (x y : CertifiedBinaryFloat prec emax),
      BinaryFloatCertificate (Bmult mult_nan m x.1 y.1)

def Bplus_result_obligation : Prop :=
  ∀ (plus_nan : binary_float prec emax → binary_float prec emax → CertifiedNaNResult prec emax)
    (m : BinarySingleNaN.mode) (x y : CertifiedBinaryFloat prec emax),
      BinaryFloatCertificate (Bplus plus_nan m x.1 y.1)

def Bminus_result_obligation : Prop :=
  ∀ (minus_nan : binary_float prec emax → binary_float prec emax → CertifiedNaNResult prec emax)
    (m : BinarySingleNaN.mode) (x y : CertifiedBinaryFloat prec emax),
      BinaryFloatCertificate (Bminus minus_nan m x.1 y.1)

def Bdiv_result_obligation : Prop :=
  ∀ (div_nan : binary_float prec emax → binary_float prec emax → CertifiedNaNResult prec emax)
    (m : BinarySingleNaN.mode) (x y : CertifiedBinaryFloat prec emax),
      BinaryFloatCertificate (Bdiv div_nan m x.1 y.1)

def Bsqrt_result_obligation : Prop :=
  ∀ (sqrt_nan : binary_float prec emax → CertifiedNaNResult prec emax)
    (m : BinarySingleNaN.mode) (x : CertifiedBinaryFloat prec emax),
    BinaryFloatCertificate (Bsqrt sqrt_nan m x.1)

/-!
Exact theorem-facing interpretation selected by RPR-007.  The executable
definitions above remain on the rational runtime carrier.  This namespace is
only a transparent Binary-specific adapter over `BinarySingleNaN.Exact`.
-/
abbrev ExactRealContext := BinarySingleNaN.Exact.Context

namespace Exact

abbrev Context := ExactRealContext
abbrev Magnitude (ctx : Context) := BinarySingleNaN.Exact.Magnitude ctx
abbrev R (ctx : Context) := BinarySingleNaN.Exact.R ctx
abbrev R0 (ctx : Context) := BinarySingleNaN.Exact.R0 ctx
abbrev Ropp (ctx : Context) := BinarySingleNaN.Exact.Ropp ctx
abbrev Rplus (ctx : Context) := BinarySingleNaN.Exact.Rplus ctx
abbrev Rminus (ctx : Context) := BinarySingleNaN.Exact.Rminus ctx
abbrev Rmult (ctx : Context) := BinarySingleNaN.Exact.Rmult ctx
abbrev Rdiv (ctx : Context) := BinarySingleNaN.Exact.Rdiv ctx
abbrev Rabs (ctx : Context) := BinarySingleNaN.Exact.Rabs ctx
abbrev Rlt (ctx : Context) := BinarySingleNaN.Exact.Rlt ctx
abbrev Rle (ctx : Context) := BinarySingleNaN.Exact.Rle ctx
noncomputable abbrev Rcompare (ctx : Context) := BinarySingleNaN.Exact.Rcompare ctx
noncomputable abbrev Rlt_bool (ctx : Context) := BinarySingleNaN.Exact.Rlt_bool ctx
abbrev bpow (ctx : Context) := BinarySingleNaN.Exact.bpow ctx
abbrev F2R (ctx : Context) {beta : radix} (f : float beta) : R ctx :=
  BinarySingleNaN.Exact.F2R ctx f
abbrev cexp {ctx : Context} (magnitude : Magnitude ctx) :=
  BinarySingleNaN.Exact.cexp magnitude
abbrev canonical {ctx : Context} (magnitude : Magnitude ctx) :=
  BinarySingleNaN.Exact.canonical magnitude
abbrev generic_format {ctx : Context} (magnitude : Magnitude ctx) :=
  BinarySingleNaN.Exact.generic_format magnitude
abbrev round {ctx : Context} (magnitude : Magnitude ctx) :=
  BinarySingleNaN.Exact.round magnitude
noncomputable abbrev round_mode (ctx : Context) := BinarySingleNaN.Exact.round_mode ctx

def B2R (ctx : Context) (f : binary_float prec emax) : R ctx :=
  BinarySingleNaN.Exact.B2R ctx (B2BSN f)

end Exact

def B2BSN_BSN2BStatement : Prop :=
  ∀ (nan : CertifiedNaNResult prec emax)
    (x : CertifiedSingleNaN prec emax),
    B2BSN (BSN2B ⟨nan.1, nan.2.1⟩ x.1) = x.1

def B2BSN_BSN2B'Statement : Prop :=
  ∀ (x : CertifiedSingleNaN prec emax)
    (Nx : BinarySingleNaN.is_nan x.1 = false),
    B2BSN (BSN2B' x.1 Nx) = x.1

def B2FF_FF2BStatement : Prop :=
  ∀ (x : full_float) (Hx : FF2BObligation (prec := prec) (emax := emax) x),
    B2FF (prec := prec) (emax := emax)
      (FF2B (prec := prec) (emax := emax) x Hx).1 = x

def B2FF_injStatement : Prop :=
  ∀ x y : CertifiedBinaryFloat prec emax,
    B2FF x.1 = B2FF y.1 → x.1 = y.1

def B2R_B2BSNStatement (ctx : ExactRealContext) : Prop :=
  ∀ x : CertifiedBinaryFloat prec emax,
      BinarySingleNaN.Exact.B2R ctx (B2BSN x.1) = Exact.B2R ctx x.1

def B2R_Bsign_injStatement (ctx : ExactRealContext) : Prop :=
  ∀ x y : CertifiedBinaryFloat prec emax,
    is_finite x.1 = true → is_finite y.1 = true →
    Exact.B2R ctx x.1 = Exact.B2R ctx y.1 → Bsign x.1 = Bsign y.1 → x.1 = y.1

def B2R_build_nanStatement (ctx : ExactRealContext) : Prop :=
  ∀ x : CertifiedNaNResult prec emax,
    Exact.B2R ctx (build_nan ⟨x.1, x.2.1⟩) = Exact.R0 ctx

def B2R_injStatement (ctx : ExactRealContext) : Prop :=
  ∀ x y : CertifiedBinaryFloat prec emax,
    is_finite_strict x.1 = true → is_finite_strict y.1 = true →
    Exact.B2R ctx x.1 = Exact.B2R ctx y.1 → x.1 = y.1

def B2SF_B2BSNStatement : Prop :=
  ∀ x : CertifiedBinaryFloat prec emax,
    BinarySingleNaN.B2SF (B2BSN x.1) = B2SF x.1

def Bcompare_correctStatement (ctx : ExactRealContext) : Prop :=
  ∀ f1 f2 : CertifiedBinaryFloat prec emax,
    is_finite f1.1 = true → is_finite f2.1 = true →
    Bcompare f1.1 f2.1 = some (Exact.Rcompare ctx (Exact.B2R ctx f1.1) (Exact.B2R ctx f2.1))

def Bcompare_swapStatement : Prop :=
  ∀ x y : CertifiedBinaryFloat prec emax,
    Bcompare y.1 x.1 = match Bcompare x.1 y.1 with
      | some c => some (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp c)
      | none => none

def Bdiv_correctStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (div_nan : binary_float prec emax → binary_float prec emax →
      CertifiedNaNResult prec emax)
    (m : BinarySingleNaN.mode) (x y : CertifiedBinaryFloat prec emax),
    Exact.B2R ctx y.1 ≠ Exact.R0 ctx →
    if Exact.Rlt_bool ctx
      (Exact.Rabs ctx (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
        (Exact.round_mode ctx m) (Exact.Rdiv ctx (Exact.B2R ctx x.1) (Exact.B2R ctx y.1))))
      (Exact.bpow ctx radix2 emax) then
      Exact.B2R ctx (Bdiv (prec := prec) (emax := emax) div_nan m x.1 y.1) =
        Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m) (Exact.Rdiv ctx (Exact.B2R ctx x.1) (Exact.B2R ctx y.1)) ∧
      is_finite (Bdiv (prec := prec) (emax := emax) div_nan m x.1 y.1) = is_finite x.1 ∧
      (is_nan (Bdiv (prec := prec) (emax := emax) div_nan m x.1 y.1) = false →
        Bsign (Bdiv (prec := prec) (emax := emax) div_nan m x.1 y.1) = (Bsign x.1 ^^ Bsign y.1))
    else B2FF (Bdiv (prec := prec) (emax := emax) div_nan m x.1 y.1) =
      binary_overflow (prec := prec) (emax := emax) m (Bsign x.1 ^^ Bsign y.1)

def Bminus_correctStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (minus_nan : binary_float prec emax → binary_float prec emax →
      CertifiedNaNResult prec emax)
    (m : BinarySingleNaN.mode) (x y : CertifiedBinaryFloat prec emax),
    is_finite x.1 = true → is_finite y.1 = true →
    if Exact.Rlt_bool ctx
      (Exact.Rabs ctx (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
        (Exact.round_mode ctx m)
        (Exact.Rminus ctx (Exact.B2R ctx x.1) (Exact.B2R ctx y.1))))
      (Exact.bpow ctx radix2 emax) then
      Exact.B2R ctx (Bminus (prec := prec) (emax := emax) minus_nan m x.1 y.1) =
        Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m)
          (Exact.Rminus ctx (Exact.B2R ctx x.1) (Exact.B2R ctx y.1)) ∧
      is_finite (Bminus (prec := prec) (emax := emax) minus_nan m x.1 y.1) = true ∧
      Bsign (Bminus (prec := prec) (emax := emax) minus_nan m x.1 y.1) =
        (match Exact.Rcompare ctx
          (Exact.Rminus ctx (Exact.B2R ctx x.1) (Exact.B2R ctx y.1)) (Exact.R0 ctx) with
        | .Eq => match m with
          | .mode_DN => Bsign x.1 || (!Bsign y.1)
          | _ => Bsign x.1 && (!Bsign y.1)
        | .Lt => true
        | .Gt => false)
    else B2FF (Bminus (prec := prec) (emax := emax) minus_nan m x.1 y.1) =
      binary_overflow (prec := prec) (emax := emax) m (Bsign x.1) ∧
      Bsign x.1 = !Bsign y.1

def Bmult_correctStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (mult_nan : binary_float prec emax → binary_float prec emax →
      CertifiedNaNResult prec emax)
    (m : BinarySingleNaN.mode) (x y : CertifiedBinaryFloat prec emax),
    if Exact.Rlt_bool ctx
      (Exact.Rabs ctx (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
        (Exact.round_mode ctx m)
        (Exact.Rmult ctx (Exact.B2R ctx x.1) (Exact.B2R ctx y.1))))
      (Exact.bpow ctx radix2 emax) then
      Exact.B2R ctx (Bmult (prec := prec) (emax := emax) mult_nan m x.1 y.1) =
        Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m)
          (Exact.Rmult ctx (Exact.B2R ctx x.1) (Exact.B2R ctx y.1)) ∧
      is_finite (Bmult (prec := prec) (emax := emax) mult_nan m x.1 y.1) = (is_finite x.1 && is_finite y.1) ∧
      (is_nan (Bmult (prec := prec) (emax := emax) mult_nan m x.1 y.1) = false →
        Bsign (Bmult (prec := prec) (emax := emax) mult_nan m x.1 y.1) = (Bsign x.1 ^^ Bsign y.1))
    else B2FF (Bmult (prec := prec) (emax := emax) mult_nan m x.1 y.1) =
      binary_overflow (prec := prec) (emax := emax) m (Bsign x.1 ^^ Bsign y.1)

def Bplus_correctStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (plus_nan : binary_float prec emax → binary_float prec emax →
      CertifiedNaNResult prec emax)
    (m : BinarySingleNaN.mode) (x y : CertifiedBinaryFloat prec emax),
    is_finite x.1 = true → is_finite y.1 = true →
    if Exact.Rlt_bool ctx
      (Exact.Rabs ctx (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
        (Exact.round_mode ctx m)
        (Exact.Rplus ctx (Exact.B2R ctx x.1) (Exact.B2R ctx y.1))))
      (Exact.bpow ctx radix2 emax) then
      Exact.B2R ctx (Bplus (prec := prec) (emax := emax) plus_nan m x.1 y.1) =
        Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m)
          (Exact.Rplus ctx (Exact.B2R ctx x.1) (Exact.B2R ctx y.1)) ∧
      is_finite (Bplus (prec := prec) (emax := emax) plus_nan m x.1 y.1) = true ∧
      Bsign (Bplus (prec := prec) (emax := emax) plus_nan m x.1 y.1) =
        (match Exact.Rcompare ctx
          (Exact.Rplus ctx (Exact.B2R ctx x.1) (Exact.B2R ctx y.1)) (Exact.R0 ctx) with
        | .Eq => match m with
          | .mode_DN => Bsign x.1 || Bsign y.1
          | _ => Bsign x.1 && Bsign y.1
        | .Lt => true
        | .Gt => false)
    else B2FF (Bplus (prec := prec) (emax := emax) plus_nan m x.1 y.1) =
      binary_overflow (prec := prec) (emax := emax) m (Bsign x.1) ∧ Bsign x.1 = Bsign y.1

def Bsign_B2BSNStatement : Prop :=
  ∀ x : CertifiedBinaryFloat prec emax,
    is_nan x.1 = false →
      BinarySingleNaN.Bsign (B2BSN x.1) = Bsign x.1

def FF2SF_B2FFStatement : Prop :=
  ∀ x : CertifiedBinaryFloat prec emax,
    FF2SF (B2FF x.1) = B2SF x.1

def SF2FF_FF2SFStatement : Prop :=
  ∀ x : full_float, is_nan_FF x = false → SF2FF (FF2SF x) = x

def binary_normalize_correctStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx)
    [BinaryNormalizeCertificate prec emax] : Prop :=
  ∀ (m : BinarySingleNaN.mode) (mx ex : Z) (szero : Bool),
    let x := Exact.F2R ctx (Float radix2 mx ex)
    let z := binary_normalize (prec := prec) (emax := emax) m mx ex szero
    if Exact.Rlt_bool ctx
      (Exact.Rabs ctx (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
        (Exact.round_mode ctx m) x))
      (Exact.bpow ctx radix2 emax) then
      Exact.B2R ctx z = Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
        (Exact.round_mode ctx m) x ∧
      is_finite (binary_normalize (prec := prec) (emax := emax) m mx ex szero) = true ∧
      Bsign z =
        (match Exact.Rcompare ctx x (Exact.R0 ctx) with
        | .Eq => szero
        | .Lt => true
        | .Gt => false)
    else B2FF (binary_normalize (prec := prec) (emax := emax) m mx ex szero) =
      binary_overflow (prec := prec) (emax := emax) m
        (Exact.Rlt_bool ctx x (Exact.R0 ctx))

def bounded_canonical_lt_emaxStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (mx : positive) (ex : Z),
    Exact.canonical magnitude radix2 (fexp (prec := prec) (emax := emax))
      (Float radix2 (Zpos mx) ex) →
    Exact.Rlt ctx (Exact.F2R ctx (Float radix2 (Zpos mx) ex))
      (Exact.bpow ctx radix2 emax) →
    bounded (prec := prec) (emax := emax) mx ex = true

def bounded_lt_emaxStatement (ctx : ExactRealContext) : Prop :=
  ∀ (mx : positive) (ex : Z), bounded (prec := prec) (emax := emax) mx ex = true →
    Exact.Rlt ctx (Exact.F2R ctx (Float radix2 (Zpos mx) ex))
      (Exact.bpow ctx radix2 emax)

def eq_binary_overflow_FF2SFStatement : Prop :=
  ∀ (x : full_float) (m : BinarySingleNaN.mode) (s : Bool),
    FF2SF x = BinarySingleNaN.binary_overflow (prec := prec) (emax := emax) m s →
    x = binary_overflow (prec := prec) (emax := emax) m s

def generic_format_B2RStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ x : CertifiedBinaryFloat prec emax,
    Exact.generic_format magnitude radix2 (fexp (prec := prec) (emax := emax))
      (Exact.B2R ctx x.1)

def is_finite_B2BSNStatement : Prop :=
  ∀ x : CertifiedBinaryFloat prec emax,
    BinarySingleNaN.is_finite (B2BSN x.1) = is_finite x.1

def is_finite_build_nanStatement : Prop :=
  ∀ x : CertifiedNaNResult prec emax,
    is_finite (build_nan ⟨x.1, x.2.1⟩) = false

def is_nan_FF2SFStatement : Prop :=
  ∀ x : full_float, BinarySingleNaN.is_nan_SF (FF2SF x) = is_nan_FF x

def is_nan_build_nanStatement : Prop :=
  ∀ x : CertifiedNaNResult prec emax,
    is_nan (build_nan ⟨x.1, x.2.1⟩) = true

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

theorem is_nan_FF2SF : is_nan_FF2SFStatement := by
  intro x
  cases x <;> rfl

theorem SF2FF_FF2SF : SF2FF_FF2SFStatement := by
  intro x hx
  cases x with
  | F754_zero s => rfl
  | F754_infinity s => rfl
  | F754_nan s m => simp [is_nan_FF] at hx
  | F754_finite s m e => rfl

theorem binary64_normalize_certificate_proof :
    ∀ [prec_gt_0 : Core.FLX.Prec_gt_0
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 53)]
      [prec_lt_emax : BinarySingleNaN.Prec_lt_emax
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 53)
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1024)],
      BinaryNormalizeCertificate
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 53)
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1024) := by
  intro prec_gt_0 prec_lt_emax
  constructor
  exact BinarySingleNaN.is_nan_binary_normalize

theorem binary32_normalize_certificate_proof :
    ∀ [prec_gt_0 : Core.FLX.Prec_gt_0
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 24)]
      [prec_lt_emax : BinarySingleNaN.Prec_lt_emax
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 24)
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 128)],
      BinaryNormalizeCertificate
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 24)
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 128) := by
  intro prec_gt_0 prec_lt_emax
  constructor
  exact BinarySingleNaN.is_nan_binary_normalize

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

theorem build_nan_result_obligation_proof :
    ∀ {prec emax : Z}, build_nan_result_obligation (prec := prec) (emax := emax) := by
  intro prec emax x
  rcases x with ⟨x, hx⟩
  cases x with
  | B754_nan s pl =>
      simpa [build_nan, BinaryFloatCertificate, B2FF, valid_binary] using hx.2
  | B754_zero s => simp [is_nan] at hx
  | B754_infinity s => simp [is_nan] at hx
  | B754_finite s m e => simp [is_nan] at hx

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

theorem BSN2B_result_obligation_proof :
    ∀ {prec emax : Z}, BSN2B_result_obligation (prec := prec) (emax := emax) := by
  intro prec emax nan x
  rcases nan with ⟨nan, hnan⟩
  rcases x with ⟨x, hx⟩
  cases x with
  | B754_nan =>
      exact build_nan_result_obligation_proof ⟨nan, hnan⟩
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_finite s m e =>
      change bounded0 prec emax m e = true at hx
      simpa [BSN2B, BinaryFloatCertificate, B2FF, valid_binary, B2SF] using hx

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

theorem Bopp_result_obligation_proof :
    ∀ {prec emax : Z}, Bopp_result_obligation (prec := prec) (emax := emax) := by
  intro prec emax opp_nan x
  rcases x with ⟨x, hx⟩
  cases x with
  | B754_nan s pl =>
      exact build_nan_result_obligation_proof (opp_nan (.B754_nan s pl))
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_finite s m e =>
      change bounded (prec := prec) (emax := emax) m e = true at hx
      simpa [Bopp, BinaryFloatCertificate, B2FF, valid_binary] using hx

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

theorem Babs_result_obligation_proof :
    ∀ {prec emax : Z}, Babs_result_obligation (prec := prec) (emax := emax) := by
  intro prec emax abs_nan x
  rcases x with ⟨x, hx⟩
  cases x with
  | B754_nan s pl =>
      exact build_nan_result_obligation_proof (abs_nan (.B754_nan s pl))
  | B754_infinity s => rfl
  | B754_finite s m e =>
      change bounded (prec := prec) (emax := emax) m e = true at hx
      simpa [Babs, BinaryFloatCertificate, B2FF, valid_binary] using hx
  | B754_zero s => rfl

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

theorem FF2BCertificateStatement_proof :
    ∀ {prec emax : Z}, FF2BCertificateStatement (prec := prec) (emax := emax) := by
  intro prec emax x hx
  exact (FF2B x hx).2

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

theorem BSN2B'_result_obligation_proof :
    ∀ {prec emax : Z}, BSN2B'_result_obligation (prec := prec) (emax := emax) := by
  intro prec emax x Nx
  rcases x with ⟨x, hx⟩
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => simp [BinarySingleNaN.is_nan] at Nx
  | B754_finite s m e =>
      change bounded0 prec emax m e = true at hx
      simpa [BSN2B', BinaryFloatCertificate, B2FF, valid_binary] using hx

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

theorem B2BSN_result_obligation_proof :
    ∀ {prec emax : Z}, B2BSN_result_obligation (prec := prec) (emax := emax) := by
  intro prec emax x
  rcases x with ⟨x, hx⟩
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan s pl => rfl
  | B754_finite s m e =>
      change bounded0 prec emax m e = true at hx
      change bounded0 prec emax m e = true
      exact hx

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

theorem fexp_correct_certificate_proof :
    ∀ (prec emax : Z) [Core.FLX.Prec_gt_0 prec]
      [BinarySingleNaN.Prec_lt_emax prec emax],
      FexpCorrectCertificate prec emax := by
  intro prec emax prec_gt_0 prec_lt_emax
  constructor
  exact CompCert4Lean.Flocq.Core.FLT.FLT_exp_valid
    (BinarySingleNaN.emin0 prec emax) prec (h := prec_gt_0)

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

theorem B2SF_B2BSN :
    ∀ {prec emax : Z}, B2SF_B2BSNStatement (prec := prec) (emax := emax) := by
  intro prec emax x
  rcases x with ⟨x, hx⟩
  cases x <;> rfl

theorem B2R_B2BSN :
    ∀ {prec emax : Z} (ctx : ExactRealContext),
      B2R_B2BSNStatement (prec := prec) (emax := emax) ctx := by
  intro prec emax ctx x
  rcases x with ⟨x, hx⟩
  cases x <;> rfl

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

theorem FF2SF_B2FF :
    ∀ {prec emax : Z}, FF2SF_B2FFStatement (prec := prec) (emax := emax) := by
  intro prec emax x
  rcases x with ⟨x, hx⟩
  cases x <;> rfl

theorem B2FF_FF2B :
    ∀ {prec emax : Z}, B2FF_FF2BStatement (prec := prec) (emax := emax) := by
  intro prec emax x Hx
  cases x <;> rfl

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

theorem B2FF_inj :
    ∀ {prec emax : Z}, B2FF_injStatement (prec := prec) (emax := emax) := by
  intro prec emax x y hxy
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  cases x <;> cases y <;> simp [B2FF] at hxy ⊢ <;> exact hxy

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

theorem is_finite_B2BSN :
    ∀ {prec emax : Z}, is_finite_B2BSNStatement (prec := prec) (emax := emax) := by
  intro prec emax x
  rcases x with ⟨x, hx⟩
  cases x <;> rfl

theorem B2R_build_nan :
    ∀ {prec emax : Z} (ctx : ExactRealContext),
      B2R_build_nanStatement (prec := prec) (emax := emax) ctx := by
  intro prec emax ctx x
  rcases x with ⟨x, hx⟩
  cases x with
  | B754_nan s pl => rfl
  | B754_zero s => simp [is_nan] at hx
  | B754_infinity s => simp [is_nan] at hx
  | B754_finite s m e => simp [is_nan] at hx

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

theorem is_finite_build_nan :
    ∀ {prec emax : Z}, is_finite_build_nanStatement (prec := prec) (emax := emax) := by
  intro prec emax x
  rcases x with ⟨x, hx⟩
  cases x with
  | B754_nan s pl => rfl
  | B754_zero s => simp [is_nan] at hx
  | B754_infinity s => simp [is_nan] at hx
  | B754_finite s m e => simp [is_nan] at hx

theorem is_nan_build_nan :
    ∀ {prec emax : Z}, is_nan_build_nanStatement (prec := prec) (emax := emax) := by
  intro prec emax x
  rcases x with ⟨x, hx⟩
  cases x with
  | B754_nan s pl => rfl
  | B754_zero s => simp [is_nan] at hx
  | B754_infinity s => simp [is_nan] at hx
  | B754_finite s m e => simp [is_nan] at hx

theorem B2BSN_BSN2B :
    ∀ {prec emax : Z}, B2BSN_BSN2BStatement (prec := prec) (emax := emax) := by
  intro prec emax nan x
  rcases nan with ⟨nan, hnan⟩
  rcases x with ⟨x, hx⟩
  cases nan with
  | B754_nan s pl => cases x <;> rfl
  | B754_zero s => simp [is_nan] at hnan
  | B754_infinity s => simp [is_nan] at hnan
  | B754_finite s m e => simp [is_nan] at hnan

theorem Bsign_B2BSN :
    ∀ {prec emax : Z}, Bsign_B2BSNStatement (prec := prec) (emax := emax) := by
  intro prec emax x hn
  rcases x with ⟨x, hx⟩
  cases x with
  | B754_nan s pl => simp [is_nan] at hn
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_finite s m e => rfl

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

theorem B2BSN_BSN2B' :
    ∀ {prec emax : Z}, B2BSN_BSN2B'Statement (prec := prec) (emax := emax) := by
  intro prec emax x Nx
  rcases x with ⟨x, hx⟩
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan => simp [BinarySingleNaN.is_nan] at Nx
  | B754_finite s m e => rfl

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

theorem Bcompare_swap :
    ∀ {prec emax : Z}, Bcompare_swapStatement (prec := prec) (emax := emax) := by
  intro prec emax x y
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  unfold Bcompare
  exact BinarySingleNaN.Bcompare_swap (B2BSN x) (B2BSN y) (by
    change BinarySingleNaN.BinaryFloatCertificate (B2BSN x)
    cases x with
    | B754_zero s => exact hx
    | B754_infinity s => exact hx
    | B754_nan s pl => rfl
    | B754_finite s m e => exact hx) (by
    change BinarySingleNaN.BinaryFloatCertificate (B2BSN y)
    cases y with
    | B754_zero s => exact hy
    | B754_infinity s => exact hy
    | B754_nan s pl => rfl
    | B754_finite s m e => exact hy)

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

theorem bounded_lt_emax :
    ∀ {prec emax : Z} (ctx : ExactRealContext),
      bounded_lt_emaxStatement (prec := prec) (emax := emax) ctx := by
  intro prec emax ctx mx ex Hx
  exact BinarySingleNaN.bounded_lt_emax (prec := prec) (emax := emax) ctx mx ex Hx

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

theorem eq_binary_overflow_FF2SF :
    ∀ {prec emax : Z}, eq_binary_overflow_FF2SFStatement (prec := prec) (emax := emax) := by
  intro prec emax x m s H
  unfold binary_overflow
  rw [← H]
  apply Eq.symm
  apply SF2FF_FF2SF
  rw [← is_nan_FF2SF, H]
  unfold BinarySingleNaN.binary_overflow
  split <;> rfl

end CompCert4Lean.Flocq.IEEE754.Binary


namespace CompCert4Lean.Flocq.IEEE754.Binary

theorem generic_format_B2R :
    ∀ {prec emax : Z} (ctx : ExactRealContext)
      (magnitude : Exact.Magnitude ctx),
      generic_format_B2RStatement (prec := prec) (emax := emax)
        ctx magnitude := by
  intro prec emax ctx magnitude x
  have h := BinarySingleNaN.generic_format_B2R ctx magnitude
    (B2BSN x.1) (B2BSN_result_obligation_proof x)
  rw [B2R_B2BSN ctx x] at h
  exact h

end CompCert4Lean.Flocq.IEEE754.Binary
