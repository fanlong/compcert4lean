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

namespace CompCert4Lean.Flocq.IEEE754.Binary

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem pg_b2r_inj_abs_mantissa (s : Bool) (m : positive) :
    Zabs (cond_Zopp s (Zpos m)) = Zpos m := by
  have ha := Zaux.abs_cond_Zopp s (Zpos m)
  change Zabs (cond_Zopp s (Zpos m)) = Zabs (Zpos m) at ha
  rw [ha]
  apply intOfZ_injective
  change intOfZ (ZArith.BinInt.Z.abs (Zpos m)) = intOfZ (Zpos m)
  unfold ZArith.BinInt.Z.abs
  rw [intOfZ_zOfInt]
  simp [intOfZ]

private theorem pg_b2r_inj_bounds (ctx : ExactRealContext) (m : positive) (e : Z) :
    let d := Zadd (Zpos (BinarySingleNaN.digits2_pos m)) e
    Exact.Rle ctx (Exact.bpow ctx radix2 (Zsub d Zone))
        (Exact.F2R ctx (Float radix2 (Zpos m) e)) ∧
      Exact.Rlt ctx (Exact.F2R ctx (Float radix2 (Zpos m) e))
        (Exact.bpow ctx radix2 d) := by
  let d := Digits.Zdigits radix2 (Zpos m)
  have hd : Zlt Z0 d := Digits.Zdigits_gt_0 radix2 (Zpos m) (by intro h; cases h)
  have hds : Zle Z0 (Zsub d Zone) := by
    change (0 : Int) ≤ intOfZ (Zsub d Zone)
    change (0 : Int) < intOfZ d at hd
    simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    change (0 : Int) ≤ intOfZ d - 1
    omega
  have hdl : Zlt (Zsub d Zone) d := by
    change intOfZ (Zsub d Zone) < intOfZ d
    simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    change intOfZ d - 1 < intOfZ d
    omega
  have hl := Digits.Zpower_le_Zdigits radix2 (Zsub d Zone) (Zpos m) hdl
  have hu := Digits.Zpower_gt_Zdigits radix2 d (Zpos m) (Int.le_refl _)
  have ha : Digits.Zabs (Zpos m) = Zpos m := pg_b2r_inj_abs_mantissa false m
  rw [ha] at hl hu
  have hlow := Float_prop.F2R_le ctx radix2
    (Zpower (radix2 : Z) (Zsub d Zone)) (Zpos m) e hl
  have hupp := Float_prop.F2R_lt ctx radix2 e
    (Zpos m) (Zpower (radix2 : Z) d) hu
  have hp (k : Z) (hk : Zle Z0 k) :
      Float_prop.Exact.F2R ctx (Float radix2 (Zpower (radix2 : Z) k) e) =
        Exact.bpow ctx radix2 (Zadd k e) := by
    have hz := Raux.IZR_Zpower ctx radix2 k hk
    change ctx.spec.ofZ (Zpower (radix2 : Z) k) = Exact.bpow ctx radix2 k at hz
    change ctx.spec.mul (ctx.spec.ofZ (Zpower (radix2 : Z) k))
      (Exact.bpow ctx radix2 e) = _
    rw [hz]
    exact (Raux.bpow_plus ctx radix2 k e).symm
  change Exact.Rle ctx
    (Float_prop.Exact.F2R ctx (Float radix2 (Zpower (radix2 : Z) (Zsub d Zone)) e))
    (Exact.F2R ctx (Float radix2 (Zpos m) e)) at hlow
  change Exact.Rlt ctx (Exact.F2R ctx (Float radix2 (Zpos m) e))
    (Float_prop.Exact.F2R ctx (Float radix2 (Zpower (radix2 : Z) d) e)) at hupp
  rw [hp _ hds] at hlow
  rw [hp _ (Int.le_of_lt hd)] at hupp
  have he : Zadd (Zsub d Zone) e = Zsub (Zadd d e) Zone := by
    apply intOfZ_injective
    simp only [Zadd, Zsub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
      intOfZ_zOfInt]
    omega
  rw [he] at hlow
  have hdigits : Zpos (BinarySingleNaN.digits2_pos m) = d :=
    Digits.Zpos_digits2_pos m
  dsimp only
  rw [hdigits]
  exact ⟨hlow, hupp⟩

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem B2R_inj :
    ∀ {prec emax : Z} (ctx : ExactRealContext),
      B2R_injStatement (prec := prec) (emax := emax) ctx := by
  intro prec emax ctx ⟨x, hx⟩ ⟨y, hy⟩ hfx hfy heq
  cases x <;> cases y <;>
    simp only [is_finite_strict, Bool.false_eq_true] at hfx hfy
  rename_i sx mx ex sy my ey
  change Exact.F2R ctx (Float radix2 (cond_Zopp sx (Zpos mx)) ex) =
    Exact.F2R ctx (Float radix2 (cond_Zopp sy (Zpos my)) ey) at heq
  have habs := congrArg (Exact.Rabs ctx) heq
  have habs_float (s : Bool) (m : positive) (e : Z) :
      Exact.Rabs ctx (Exact.F2R ctx (Float radix2 (cond_Zopp s (Zpos m)) e)) =
        Exact.F2R ctx (Float radix2 (Zpos m) e) := by
    have h := Float_prop.F2R_Zabs ctx radix2 (cond_Zopp s (Zpos m)) e
    change Exact.F2R ctx (Float radix2 (Zabs (cond_Zopp s (Zpos m))) e) =
      Exact.Rabs ctx (Exact.F2R ctx (Float radix2 (cond_Zopp s (Zpos m)) e)) at h
    rw [pg_b2r_inj_abs_mantissa] at h
    exact h.symm
  rw [habs_float, habs_float] at habs
  have hbx := pg_b2r_inj_bounds ctx mx ex
  have hby := pg_b2r_inj_bounds ctx my ey
  rw [← habs] at hby
  have hdigits := Raux.bpow_unique ctx radix2
    (Exact.F2R ctx (Float radix2 (Zpos mx) ex))
    (Zadd (Zpos (BinarySingleNaN.digits2_pos mx)) ex)
    (Zadd (Zpos (BinarySingleNaN.digits2_pos my)) ey) hbx hby
  change bounded0 prec emax mx ex = true at hx
  change bounded0 prec emax my ey = true at hy
  have hcx := (Bool.and_eq_true_iff.mp hx).1
  have hcy := (Bool.and_eq_true_iff.mp hy).1
  have hcx' := ZArith.Zbool.Zeq_bool_eq _ _ hcx
  have hcy' := ZArith.Zbool.Zeq_bool_eq _ _ hcy
  have he : ex = ey := by
    calc
      ex = fexp0 prec emax (Zadd (Zpos (BinarySingleNaN.digits2_pos mx)) ex) := hcx'.symm
      _ = fexp0 prec emax (Zadd (Zpos (BinarySingleNaN.digits2_pos my)) ey) :=
        congrArg (fexp0 prec emax) hdigits
      _ = ey := hcy'
  subst ey
  have hm := Float_prop.eq_F2R ctx radix2 ex
    (cond_Zopp sx (Zpos mx)) (cond_Zopp sy (Zpos my)) heq
  have hmabs := congrArg Zabs hm
  rw [pg_b2r_inj_abs_mantissa, pg_b2r_inj_abs_mantissa] at hmabs
  have hm' : mx = my := by injection hmabs
  subst my
  have hs : sx = sy := by
    cases sx <;> cases sy
    · rfl
    · change Zpos mx = Zopp (Zpos mx) at hm
      have hi := congrArg intOfZ hm
      change (↑(posToNat mx) : Int) = intOfZ (zOfInt (-↑(posToNat mx))) at hi
      rw [intOfZ_zOfInt] at hi
      have hp := posToNat_positive mx
      omega
    · change Zopp (Zpos mx) = Zpos mx at hm
      have hi := congrArg intOfZ hm
      change intOfZ (zOfInt (-↑(posToNat mx))) = (↑(posToNat mx) : Int) at hi
      rw [intOfZ_zOfInt] at hi
      have hp := posToNat_positive mx
      omega
    · rfl
  subst sy
  rfl

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

 theorem B2R_Bsign_inj :
    ∀ {prec emax : Z} (ctx : ExactRealContext),
      B2R_Bsign_injStatement (prec := prec) (emax := emax) ctx := by
  intro prec emax ctx x y hfx hfy heq hsign
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  cases x with
  | B754_nan s pl => simp [is_finite] at hfx
  | B754_infinity s => simp [is_finite] at hfx
  | B754_zero sx =>
      cases y with
      | B754_nan sy pl => simp [is_finite] at hfy
      | B754_infinity sy => simp [is_finite] at hfy
      | B754_zero sy =>
          simp [B2R, Bsign] at heq hsign ⊢
          cases hsign
          rfl
      | B754_finite sy my ey =>
          simp [B2R, Bsign] at heq hsign
          have hnum : cond_Zopp sy (Zpos my) ≠ Z0 := by
            intro h
            have ha := Zaux.abs_cond_Zopp sy (Zpos my)
            change Zaux.cond_Zopp sy (Zpos my) = Z0 at h
            rw [h] at ha
            have hi := congrArg intOfZ ha
            simp only [ZArith.BinInt.Z.abs, intOfZ_zOfInt] at hi
            have hz : intOfZ Z0 = (0 : Int) := rfl
            rw [hz] at hi
            have hp := posToNat_positive my
            have hp' : (0 : Int) < Int.ofNat (posToNat my) := Int.ofNat_lt.mpr hp
            have hzero := hi.symm
            change Int.ofNat (posToNat my) = 0 at hzero
            exact (Int.ne_of_gt hp') hzero
          have hne := Float_prop.F2R_neq_0 ctx radix2
            (Float radix2 (cond_Zopp sy (Zpos my)) ey) hnum
          exact False.elim (hne heq.symm)
  | B754_finite sx mx ex =>
      cases y with
      | B754_nan sy pl => simp [is_finite] at hfy
      | B754_infinity sy => simp [is_finite] at hfy
      | B754_zero sy =>
          simp [B2R, Bsign] at heq hsign
          have hnum : cond_Zopp sx (Zpos mx) ≠ Z0 := by
            intro h
            have ha := Zaux.abs_cond_Zopp sx (Zpos mx)
            change Zaux.cond_Zopp sx (Zpos mx) = Z0 at h
            rw [h] at ha
            have hi := congrArg intOfZ ha
            simp only [ZArith.BinInt.Z.abs, intOfZ_zOfInt] at hi
            have hz : intOfZ Z0 = (0 : Int) := rfl
            rw [hz] at hi
            have hp := posToNat_positive mx
            have hp' : (0 : Int) < Int.ofNat (posToNat mx) := Int.ofNat_lt.mpr hp
            have hzero := hi.symm
            change Int.ofNat (posToNat mx) = 0 at hzero
            exact (Int.ne_of_gt hp') hzero
          have hne := Float_prop.F2R_neq_0 ctx radix2
            (Float radix2 (cond_Zopp sx (Zpos mx)) ex) hnum
          exact False.elim (hne heq)
      | B754_finite sy my ey =>
          apply B2R_inj ctx
          · rfl
          · rfl
          · exact heq

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem binary_compare_exponent_lt (ctx : ExactRealContext)
    {prec emax : Z} (mantissaLeft mantissaRight : positive)
    (exponentLeft exponentRight : Z)
    (validLeft : bounded0 prec emax mantissaLeft exponentLeft = true)
    (validRight : bounded0 prec emax mantissaRight exponentRight = true)
    (exponentOrder : Zlt exponentLeft exponentRight) :
    Exact.Rlt ctx (Exact.F2R ctx (Float radix2 (Zpos mantissaLeft) exponentLeft))
      (Exact.F2R ctx (Float radix2 (Zpos mantissaRight) exponentRight)) := by
  have canonicalLeft := ZArith.Zbool.Zeq_bool_eq _ _
    (Bool.and_eq_true_iff.mp validLeft).1
  have canonicalRight := ZArith.Zbool.Zeq_bool_eq _ _
    (Bool.and_eq_true_iff.mp validRight).1
  have integerLeft := congrArg intOfZ canonicalLeft
  have integerRight := congrArg intOfZ canonicalRight
  change intOfZ (ZArith.BinInt.Z.max
      (Zsub (Zadd (Zpos (BinarySingleNaN.digits2_pos mantissaLeft)) exponentLeft) prec)
      (emin0 prec emax)) = intOfZ exponentLeft at integerLeft
  change intOfZ (ZArith.BinInt.Z.max
      (Zsub (Zadd (Zpos (BinarySingleNaN.digits2_pos mantissaRight)) exponentRight) prec)
      (emin0 prec emax)) = intOfZ exponentRight at integerRight
  simp only [ZArith.BinInt.Z.max, Zsub, Zadd, ZArith.BinInt.Z.sub,
    ZArith.BinInt.Z.add, intOfZ_zOfInt] at integerLeft integerRight
  have magnitudeOrder : Zle
      (Zadd (Zpos (BinarySingleNaN.digits2_pos mantissaLeft)) exponentLeft)
      (Zsub (Zadd (Zpos (BinarySingleNaN.digits2_pos mantissaRight)) exponentRight) Zone) := by
    change intOfZ _ ≤ intOfZ _
    simp only [Zsub, Zadd, ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add, intOfZ_zOfInt]
    change intOfZ exponentLeft < intOfZ exponentRight at exponentOrder
    change intOfZ (Zpos (BinarySingleNaN.digits2_pos mantissaLeft)) + intOfZ exponentLeft ≤
      intOfZ (Zpos (BinarySingleNaN.digits2_pos mantissaRight)) + intOfZ exponentRight - 1
    split at integerLeft <;> split at integerRight <;>
      (try simp only [intOfZ_zOfInt] at integerLeft integerRight) <;> omega
  have boundsLeft := pg_b2r_inj_bounds ctx mantissaLeft exponentLeft
  have boundsRight := pg_b2r_inj_bounds ctx mantissaRight exponentRight
  have powerOrder := Raux.bpow_le ctx radix2 _ _ magnitudeOrder
  exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans ctx _ _ _
    boundsLeft.2 (ctx.certificate.orderedField.le_trans _ _ _ powerOrder boundsRight.1)

private theorem binary_compare_positive (ctx : ExactRealContext)
    {prec emax : Z} (mantissaLeft mantissaRight : positive)
    (exponentLeft exponentRight : Z)
    (validLeft : bounded0 prec emax mantissaLeft exponentLeft = true)
    (validRight : bounded0 prec emax mantissaRight exponentRight = true) :
    (match Zcompare exponentLeft exponentRight with
      | .Eq => PArith.BinPos.Pos.compare_cont .Eq mantissaLeft mantissaRight
      | ordering => ordering) =
    Exact.Rcompare ctx (Exact.F2R ctx (Float radix2 (Zpos mantissaLeft) exponentLeft))
      (Exact.F2R ctx (Float radix2 (Zpos mantissaRight) exponentRight)) := by
  by_cases exponentOrder : intOfZ exponentLeft < intOfZ exponentRight
  · have compared : Zcompare exponentLeft exponentRight = .Lt := by
      change (if intOfZ exponentLeft < intOfZ exponentRight then Lt else
        if intOfZ exponentLeft = intOfZ exponentRight then Eq else Gt) = Lt
      simp [exponentOrder]
    rw [compared]
    exact (Raux.Rcompare_Lt ctx _ _ (binary_compare_exponent_lt ctx
      mantissaLeft mantissaRight exponentLeft exponentRight validLeft validRight exponentOrder)).symm
  · by_cases exponentEqual : intOfZ exponentLeft = intOfZ exponentRight
    · have sameExponent := intOfZ_injective exponentEqual
      subst exponentRight
      have compared : Zcompare exponentLeft exponentLeft = .Eq := by
        change (if intOfZ exponentLeft < intOfZ exponentLeft then Lt else
          if intOfZ exponentLeft = intOfZ exponentLeft then Eq else Gt) = Eq
        simp
      rw [compared]
      have realCompare := Float_prop.Rcompare_F2R ctx radix2 exponentLeft
        (Zpos mantissaLeft) (Zpos mantissaRight)
      change Exact.Rcompare ctx
        (Exact.F2R ctx (Float radix2 (Zpos mantissaLeft) exponentLeft))
        (Exact.F2R ctx (Float radix2 (Zpos mantissaRight) exponentLeft)) = _ at realCompare
      rw [realCompare]
      change (if posToNat mantissaLeft < posToNat mantissaRight then Lt else
        if posToNat mantissaLeft = posToNat mantissaRight then Eq else Gt) =
        (if (posToNat mantissaLeft : Int) < (posToNat mantissaRight : Int) then Lt else
        if (posToNat mantissaLeft : Int) = (posToNat mantissaRight : Int) then Eq else Gt)
      simp only [Int.ofNat_lt, Int.ofNat_inj]
    · have reverseOrder : intOfZ exponentRight < intOfZ exponentLeft := by omega
      have compared : Zcompare exponentLeft exponentRight = .Gt := by
        change (if intOfZ exponentLeft < intOfZ exponentRight then Lt else
          if intOfZ exponentLeft = intOfZ exponentRight then Eq else Gt) = Gt
        simp [exponentOrder, exponentEqual]
      rw [compared]
      exact (Raux.Rcompare_Gt ctx _ _ (binary_compare_exponent_lt ctx
        mantissaRight mantissaLeft exponentRight exponentLeft validRight validLeft reverseOrder)).symm

private theorem binary_compare_positive_value (ctx : ExactRealContext)
    (mantissa : positive) (exponent : Z) :
    Exact.Rlt ctx (Exact.R0 ctx) (Exact.F2R ctx (Float radix2 (Zpos mantissa) exponent)) := by
  apply Float_prop.F2R_gt_0 ctx radix2
  change (0 : Int) < (posToNat mantissa : Int)
  exact Int.ofNat_lt.mpr (posToNat_positive mantissa)

private theorem binary_compare_negative_value (ctx : ExactRealContext)
    (mantissa : positive) (exponent : Z) :
    Exact.Rlt ctx (Exact.F2R ctx (Float radix2 (Zopp (Zpos mantissa)) exponent))
      (Exact.R0 ctx) := by
  apply Float_prop.F2R_lt_0 ctx radix2
  change intOfZ (zOfInt (-(posToNat mantissa : Int))) < 0
  rw [intOfZ_zOfInt]
  have positiveMantissa := posToNat_positive mantissa
  omega

private theorem binary_compare_finite (ctx : ExactRealContext)
    {prec emax : Z} (signLeft signRight : Bool)
    (mantissaLeft mantissaRight : positive) (exponentLeft exponentRight : Z)
    (validLeft : bounded0 prec emax mantissaLeft exponentLeft = true)
    (validRight : bounded0 prec emax mantissaRight exponentRight = true) :
    Bcompare (prec := prec) (emax := emax)
      (.B754_finite signLeft mantissaLeft exponentLeft)
      (.B754_finite signRight mantissaRight exponentRight) =
    some (Exact.Rcompare ctx
      (Exact.F2R ctx (Float radix2 (cond_Zopp signLeft (Zpos mantissaLeft)) exponentLeft))
      (Exact.F2R ctx (Float radix2 (cond_Zopp signRight (Zpos mantissaRight)) exponentRight))) := by
  have positiveCompare := binary_compare_positive ctx mantissaLeft mantissaRight
    exponentLeft exponentRight validLeft validRight
  cases signLeft <;> cases signRight
  · exact congrArg some positiveCompare
  · change some Gt = some (Exact.Rcompare ctx
      (Exact.F2R ctx (Float radix2 (Zpos mantissaLeft) exponentLeft))
      (Exact.F2R ctx (Float radix2 (Zopp (Zpos mantissaRight)) exponentRight)))
    apply congrArg some
    exact (Raux.Rcompare_Gt ctx _ _ (ctx.certificate.orderedField.lt_trans _ _ _
      (binary_compare_negative_value ctx mantissaRight exponentRight)
      (binary_compare_positive_value ctx mantissaLeft exponentLeft))).symm
  · change some Lt = some (Exact.Rcompare ctx
      (Exact.F2R ctx (Float radix2 (Zopp (Zpos mantissaLeft)) exponentLeft))
      (Exact.F2R ctx (Float radix2 (Zpos mantissaRight) exponentRight)))
    apply congrArg some
    exact (Raux.Rcompare_Lt ctx _ _ (ctx.certificate.orderedField.lt_trans _ _ _
      (binary_compare_negative_value ctx mantissaLeft exponentLeft)
      (binary_compare_positive_value ctx mantissaRight exponentRight))).symm
  · have negatedLeft := Float_prop.F2R_Zopp ctx radix2 (Zpos mantissaLeft) exponentLeft
    have negatedRight := Float_prop.F2R_Zopp ctx radix2 (Zpos mantissaRight) exponentRight
    have negativeCompare : Exact.Rcompare ctx
        (Exact.F2R ctx (Float radix2 (Zopp (Zpos mantissaLeft)) exponentLeft))
        (Exact.F2R ctx (Float radix2 (Zopp (Zpos mantissaRight)) exponentRight)) =
        CompOpp (Exact.Rcompare ctx
          (Exact.F2R ctx (Float radix2 (Zpos mantissaLeft) exponentLeft))
          (Exact.F2R ctx (Float radix2 (Zpos mantissaRight) exponentRight))) := by
      change Raux.Exact.Rcompare ctx
        (Float_prop.Exact.F2R ctx (Float radix2 (Zopp (Zpos mantissaLeft)) exponentLeft))
        (Float_prop.Exact.F2R ctx (Float radix2 (Zopp (Zpos mantissaRight)) exponentRight)) = _
      rw [negatedLeft, negatedRight]
      rw [Raux.Rcompare_opp ctx]
      exact Raux.Rcompare_sym ctx _ _
    change Bcompare (prec := prec) (emax := emax)
      (.B754_finite true mantissaLeft exponentLeft)
      (.B754_finite true mantissaRight exponentRight) = some (Exact.Rcompare ctx
        (Exact.F2R ctx (Float radix2 (Zopp (Zpos mantissaLeft)) exponentLeft))
        (Exact.F2R ctx (Float radix2 (Zopp (Zpos mantissaRight)) exponentRight)))
    rw [negativeCompare, ← positiveCompare]
    change some (match Zcompare exponentLeft exponentRight with
      | .Eq => CompOpp (PArith.BinPos.Pos.compare_cont Eq mantissaLeft mantissaRight)
      | .Lt => Gt
      | .Gt => Lt) = _
    cases Zcompare exponentLeft exponentRight <;>
      cases PArith.BinPos.Pos.compare_cont Eq mantissaLeft mantissaRight <;> rfl

theorem Bcompare_correct :
    ∀ {prec emax : Z} (ctx : ExactRealContext),
      Bcompare_correctStatement (prec := prec) (emax := emax) ctx := by
  intro prec emax ctx ⟨left, validLeft⟩ ⟨right, validRight⟩ finiteLeft finiteRight
  cases left with
  | B754_nan sign payload => cases finiteLeft
  | B754_infinity sign => cases finiteLeft
  | B754_zero signLeft =>
      cases right with
      | B754_nan sign payload => cases finiteRight
      | B754_infinity sign => cases finiteRight
      | B754_zero signRight =>
          exact congrArg some (Raux.Rcompare_Eq ctx _ _ rfl).symm
      | B754_finite signRight mantissa exponent =>
          cases signRight
          · exact congrArg some (Raux.Rcompare_Lt ctx _ _
              (binary_compare_positive_value ctx mantissa exponent)).symm
          · exact congrArg some (Raux.Rcompare_Gt ctx _ _
              (binary_compare_negative_value ctx mantissa exponent)).symm
  | B754_finite signLeft mantissaLeft exponentLeft =>
      cases right with
      | B754_nan sign payload => cases finiteRight
      | B754_infinity sign => cases finiteRight
      | B754_zero signRight =>
          cases signLeft
          · exact congrArg some (Raux.Rcompare_Gt ctx _ _
              (binary_compare_positive_value ctx mantissaLeft exponentLeft)).symm
          · exact congrArg some (Raux.Rcompare_Lt ctx _ _
              (binary_compare_negative_value ctx mantissaLeft exponentLeft)).symm
      | B754_finite signRight mantissaRight exponentRight =>
          exact binary_compare_finite ctx signLeft signRight mantissaLeft mantissaRight
            exponentLeft exponentRight validLeft validRight

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private def binary_width : Z → Nat
  | .Z0 => 0
  | .Zpos mantissa | .Zneg mantissa => Digits.digits2_Pnat mantissa + 1

private theorem binary_width_digits (value : Z) :
    intOfZ (Digits.Zdigits2 value) = (binary_width value : Int) := by
  have positiveWidth (mantissa : positive) :
      intOfZ (Zpos (BinarySingleNaN.digits2_pos mantissa)) =
        (Digits.digits2_Pnat mantissa + 1 : Nat) := by
    have digits := congrArg intOfZ ((Digits.Z_of_nat_S_digits2_Pnat mantissa).trans
      (Digits.Zpos_digits2_pos mantissa).symm)
    change intOfZ (zOfInt (Int.ofNat (Digits.digits2_Pnat mantissa + 1))) = _ at digits
    rw [intOfZ_zOfInt] at digits
    exact digits.symm
  cases value with
  | Z0 => rfl
  | Zpos mantissa => exact positiveWidth mantissa
  | Zneg mantissa => exact positiveWidth mantissa

private theorem binary_width_zero (value : Z) : binary_width value = 0 ↔ value = Z0 := by
  cases value <;> simp [binary_width]

private theorem binary_width_shr_one (record : shr_record)
    (nonnegative : Zle Z0 (shr_m record)) :
    binary_width (shr_m (shr_1 record)) = binary_width (shr_m record) - 1 := by
  rcases record with ⟨mantissa, roundBit, stickyBit⟩
  cases mantissa with
  | Z0 => rfl
  | Zpos mantissa =>
      cases mantissa <;> simp [shr_m, shr_1,
        Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shr_1, binary_width, Digits.digits2_Pnat]
  | Zneg mantissa =>
      change (0 : Int) ≤ -(posToNat mantissa : Int) at nonnegative
      have positiveMantissa := posToNat_positive mantissa
      omega

private theorem binary_width_shr_iter (record : shr_record) (count : Nat)
    (nonnegative : Zle Z0 (shr_m record)) :
    Zle Z0 (shr_m (Zaux.iter_nat shr_1 count record)) ∧
      binary_width (shr_m (Zaux.iter_nat shr_1 count record)) =
        binary_width (shr_m record) - count := by
  induction count generalizing record with
  | zero => exact ⟨nonnegative, rfl⟩
  | succ count inductionHypothesis =>
      change Zle Z0 (shr_m (Zaux.iter_nat shr_1 count (shr_1 record))) ∧ _
      have stepNonnegative := (BinarySingleNaN.le_shr1_le record nonnegative).1
      have next := inductionHypothesis (shr_1 record) stepNonnegative
      constructor
      · exact next.1
      · change binary_width (shr_m (Zaux.iter_nat shr_1 count (shr_1 record))) = _
        rw [next.2, binary_width_shr_one record nonnegative]
        omega

private theorem binary_width_monotone (left right : Z)
    (nonnegative : Zle Z0 left) (ordered : Zle left right) :
    binary_width left ≤ binary_width right := by
  apply Classical.byContradiction
  intro reversed
  have digitOrder : Zlt (Digits.Zdigits2 right) (Digits.Zdigits2 left) := by
    change intOfZ _ < intOfZ _
    rw [binary_width_digits, binary_width_digits]
    omega
  rw [Digits.Zdigits2_Zdigits, Digits.Zdigits2_Zdigits] at digitOrder
  have lower := Digits.Zpower_le_Zdigits radix2 (Digits.Zdigits radix2 right) left digitOrder
  have upper := Digits.Zpower_gt_Zdigits radix2 (Digits.Zdigits radix2 right) right
    (by exact Int.le_refl _)
  change intOfZ _ ≤ intOfZ (Zabs left) at lower
  change intOfZ (Zabs right) < intOfZ _ at upper
  change (0 : Int) ≤ intOfZ left at nonnegative
  change intOfZ left ≤ intOfZ right at ordered
  have rightNonnegative : (0 : Int) ≤ intOfZ right := by omega
  have absoluteLeft : intOfZ (Zabs left) = intOfZ left := by
    change intOfZ (zOfInt (intOfZ left).natAbs) = _
    rw [intOfZ_zOfInt]
    exact Int.natAbs_of_nonneg nonnegative
  have absoluteRight : intOfZ (Zabs right) = intOfZ right := by
    change intOfZ (zOfInt (intOfZ right).natAbs) = _
    rw [intOfZ_zOfInt]
    exact Int.natAbs_of_nonneg rightNonnegative
  rw [absoluteLeft] at lower
  rw [absoluteRight] at upper
  omega

private theorem binary_fexp_integer (prec emax exponent : Z) :
    intOfZ (fexp0 prec emax exponent) =
      max (intOfZ exponent - intOfZ prec) (intOfZ (emin0 prec emax)) := by
  change intOfZ (ZArith.BinInt.Z.max (Zsub exponent prec) (emin0 prec emax)) = _
  unfold ZArith.BinInt.Z.max
  split
  · rename_i ordered
    simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] at ordered
    exact (Int.max_eq_right ordered).symm
  · rename_i ordered
    simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] at ordered ⊢
    exact (Int.max_eq_left (by omega)).symm

private theorem binary_shr_fexp_canonical {prec emax : Z} [FLX.Prec_gt_0 prec]
    (mantissa exponent : Z) (position : location)
    (nonnegative : Zle Z0 mantissa)
    (aligned : Zle exponent (fexp0 prec emax (Zadd (Digits.Zdigits2 mantissa) exponent))) :
    let output := BinarySingleNaN.shr_fexp (prec := prec) (emax := emax) mantissa exponent position
    Zle Z0 (shr_m output.1) ∧
      fexp0 prec emax (Zadd (Digits.Zdigits2 (shr_m output.1)) output.2) = output.2 := by
  have positivePrecision := FLX.prec_gt_0 prec
  change (0 : Int) < intOfZ prec at positivePrecision
  have inputDigits := binary_width_digits mantissa
  have inputFormat := binary_fexp_integer prec emax (Zadd (Digits.Zdigits2 mantissa) exponent)
  simp only [Zadd, ZArith.BinInt.Z.add, intOfZ_zOfInt, inputDigits] at inputFormat
  change intOfZ exponent ≤ intOfZ _ at aligned
  have recordMantissa := BinarySingleNaN.shr_m_shr_record_of_loc mantissa position
  change shr_m (shr_record_of_loc mantissa position) = mantissa at recordMantissa
  have recordNonnegative : Zle Z0 (shr_m (shr_record_of_loc mantissa position)) := by
    rw [recordMantissa]
    exact nonnegative
  change
    let output := shr (shr_record_of_loc mantissa position) exponent
      (Zsub (fexp0 prec emax (Zadd (Digits.Zdigits2 mantissa) exponent)) exponent)
    Zle Z0 (shr_m output.1) ∧
      fexp0 prec emax (Zadd (Digits.Zdigits2 (shr_m output.1)) output.2) = output.2
  dsimp only
  cases shiftAmount : Zsub (fexp0 prec emax (Zadd (Digits.Zdigits2 mantissa) exponent)) exponent with
  | Z0 =>
      change Zle Z0 (shr_m (shr_record_of_loc mantissa position)) ∧ _
      constructor
      · exact recordNonnegative
      · change fexp0 prec emax
          (Zadd (Digits.Zdigits2 (shr_m (shr_record_of_loc mantissa position))) exponent) = exponent
        rw [recordMantissa]
        apply intOfZ_injective
        have zeroShift := congrArg intOfZ shiftAmount
        simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] at zeroShift
        change _ - intOfZ exponent = 0 at zeroShift
        omega
  | Zneg count =>
      have negativeShift := congrArg intOfZ shiftAmount
      simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] at negativeShift
      change _ - intOfZ exponent = -(posToNat count : Int) at negativeShift
      have countPositive := posToNat_positive count
      omega
  | Zpos count =>
      have countNonnegative : Zle Z0 (Zpos count) := by
        change (0 : Int) ≤ (posToNat count : Int)
        omega
      have shifted := BinarySingleNaN.shr_nat (shr_record_of_loc mantissa position)
        exponent (Zpos count) countNonnegative
      change shr (shr_record_of_loc mantissa position) exponent (Zpos count) =
        (Zaux.iter_nat shr_1 (posToNat count) (shr_record_of_loc mantissa position),
          Zadd exponent (Zpos count)) at shifted
      rw [shifted]
      have iteration := binary_width_shr_iter (shr_record_of_loc mantissa position)
        (posToNat count) recordNonnegative
      constructor
      · exact iteration.1
      · apply intOfZ_injective
        rw [binary_fexp_integer]
        simp only [Zadd, ZArith.BinInt.Z.add, intOfZ_zOfInt, binary_width_digits]
        have widthOutput := iteration.2
        rw [recordMantissa] at widthOutput
        have positiveShift := congrArg intOfZ shiftAmount
        simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] at positiveShift
        change _ - intOfZ exponent = (posToNat count : Int) at positiveShift
        have outputEquation :
            max ((binary_width mantissa : Int) + intOfZ exponent - intOfZ prec)
                (intOfZ (emin0 prec emax)) - intOfZ exponent = (posToNat count : Int) := by
          rw [← inputFormat]
          simpa only [Zadd, ZArith.BinInt.Z.add, intOfZ_zOfInt, inputDigits] using positiveShift
        change max ((binary_width (shr_m (Zaux.iter_nat shr_1 (posToNat count)
          (shr_record_of_loc mantissa position))) : Int) +
          (intOfZ exponent + (posToNat count : Int)) - intOfZ prec)
          (intOfZ (emin0 prec emax)) = intOfZ exponent + (posToNat count : Int)
        rw [widthOutput]
        simp only [Int.max_def] at outputEquation ⊢
        split at outputEquation <;> split <;> omega

private theorem binary_choice_increases (rounding : BinarySingleNaN.mode)
    (sign : Bool) (mantissa : Z) (position : location) :
    Zle mantissa (BinarySingleNaN.choice_mode rounding sign mantissa position) := by
  have incremented (increment : Bool) :
      Zle mantissa (CompCert4Lean.Flocq.Calc.Round.cond_incr increment mantissa) := by
    cases increment
    · exact Int.le_refl _
    · change intOfZ mantissa ≤ intOfZ (Zadd mantissa Zone)
      simp only [Zadd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
      change intOfZ mantissa ≤ intOfZ mantissa + 1
      omega
  cases rounding with
  | mode_NE => exact incremented _
  | mode_ZR => exact Int.le_refl _
  | mode_DN => exact incremented _
  | mode_UP => exact incremented _
  | mode_NA => exact incremented _

private theorem binary_fexp_mantissa_monotone (prec emax exponent left right : Z)
    (nonnegative : Zle Z0 left) (ordered : Zle left right) :
    Zle (fexp0 prec emax (Zadd (Digits.Zdigits2 left) exponent))
      (fexp0 prec emax (Zadd (Digits.Zdigits2 right) exponent)) := by
  have widthOrder := binary_width_monotone left right nonnegative ordered
  change intOfZ _ ≤ intOfZ _
  rw [binary_fexp_integer, binary_fexp_integer]
  simp only [Zadd, ZArith.BinInt.Z.add, intOfZ_zOfInt, binary_width_digits]
  simp only [Int.max_def]
  split <;> split <;> omega

private theorem binary_round_aux_valid {prec emax : Z}
    [FLX.Prec_gt_0 prec] [BinarySingleNaN.Prec_lt_emax prec emax]
    (rounding : BinarySingleNaN.mode) (sign : Bool) (mantissa exponent : Z)
    (position : location) (nonnegative : Zle Z0 mantissa)
    (aligned : Zle exponent (fexp0 prec emax (Zadd (Digits.Zdigits2 mantissa) exponent))) :
    BinarySingleNaN.valid_binary0 prec emax
      (BinarySingleNaN.binary_round_aux (prec := prec) (emax := emax)
        rounding sign mantissa exponent position) = true := by
  let first := BinarySingleNaN.shr_fexp (prec := prec) (emax := emax) mantissa exponent position
  have firstValid := binary_shr_fexp_canonical (prec := prec) (emax := emax)
    mantissa exponent position nonnegative aligned
  change Zle Z0 (shr_m first.1) ∧
    fexp0 prec emax (Zadd (Digits.Zdigits2 (shr_m first.1)) first.2) = first.2 at firstValid
  let rounded := BinarySingleNaN.choice_mode rounding sign (shr_m first.1) (loc_of_shr_record first.1)
  have increased := binary_choice_increases rounding sign (shr_m first.1) (loc_of_shr_record first.1)
  have roundedNonnegative : Zle Z0 rounded := Int.le_trans firstValid.1 increased
  have roundedAligned : Zle first.2
      (fexp0 prec emax (Zadd (Digits.Zdigits2 rounded) first.2)) := by
    have monotone := binary_fexp_mantissa_monotone prec emax first.2
      (shr_m first.1) rounded firstValid.1 increased
    rw [firstValid.2] at monotone
    exact monotone
  let second := BinarySingleNaN.shr_fexp (prec := prec) (emax := emax) rounded first.2 loc_Exact
  have secondValid := binary_shr_fexp_canonical (prec := prec) (emax := emax)
    rounded first.2 loc_Exact roundedNonnegative roundedAligned
  change Zle Z0 (shr_m second.1) ∧
    fexp0 prec emax (Zadd (Digits.Zdigits2 (shr_m second.1)) second.2) = second.2 at secondValid
  change BinarySingleNaN.valid_binary0 prec emax (match shr_m second.1 with
    | .Z0 => S754_zero sign
    | .Zpos result => BinarySingleNaN.binary_fit_aux (prec := prec) (emax := emax) rounding sign result second.2
    | .Zneg _ => S754_nan) = true
  cases resultMantissa : shr_m second.1 with
  | Z0 => rfl
  | Zneg result => rfl
  | Zpos result =>
      change BinarySingleNaN.valid_binary0 prec emax
        (BinarySingleNaN.binary_fit_aux (prec := prec) (emax := emax)
          rounding sign result second.2) = true
      have canonical := secondValid.2
      rw [resultMantissa] at canonical
      have canonicalBool : canonical_mantissa0 prec emax result second.2 = true := by
        change ZArith.Zbool.Zeq_bool
          (fexp0 prec emax (Zadd (Digits.Zdigits2 (Zpos result)) second.2)) second.2 = true
        rw [canonical]
        simp [ZArith.Zbool.Zeq_bool]
      unfold BinarySingleNaN.binary_fit_aux
      split
      · rename_i exponentBound
        exact Bool.and_eq_true_iff.mpr ⟨canonicalBool, exponentBound⟩
      · exact BinarySingleNaN.binary_overflow_correct rounding sign

private theorem binary_canonical_integer {prec emax : Z}
    (mantissa : positive) (exponent : Z)
    (valid : bounded0 prec emax mantissa exponent = true) :
    max ((binary_width (Zpos mantissa) : Int) + intOfZ exponent - intOfZ prec)
      (intOfZ (emin0 prec emax)) = intOfZ exponent := by
  have canonical := ZArith.Zbool.Zeq_bool_eq _ _ (Bool.and_eq_true_iff.mp valid).1
  have integerCanonical := congrArg intOfZ canonical
  change intOfZ (fexp0 prec emax (Zadd (Digits.Zdigits2 (Zpos mantissa)) exponent)) =
    intOfZ exponent at integerCanonical
  rw [binary_fexp_integer] at integerCanonical
  simpa only [Zadd, ZArith.BinInt.Z.add, intOfZ_zOfInt, binary_width_digits] using integerCanonical

private theorem binary_product_aligned {prec emax : Z}
    [FLX.Prec_gt_0 prec] [BinarySingleNaN.Prec_lt_emax prec emax]
    (mantissaLeft mantissaRight : positive) (exponentLeft exponentRight : Z)
    (validLeft : bounded0 prec emax mantissaLeft exponentLeft = true)
    (validRight : bounded0 prec emax mantissaRight exponentRight = true) :
    Zle (Zadd exponentLeft exponentRight)
      (fexp0 prec emax (Zadd
        (Digits.Zdigits2 (Zpos (PArith.BinPos.Pos.mul mantissaLeft mantissaRight)))
        (Zadd exponentLeft exponentRight))) := by
  have canonicalLeft := binary_canonical_integer mantissaLeft exponentLeft validLeft
  have canonicalRight := binary_canonical_integer mantissaRight exponentRight validRight
  have productIdentity : Zmul (Zpos mantissaLeft) (Zpos mantissaRight) =
      Zpos (PArith.BinPos.Pos.mul mantissaLeft mantissaRight) := by
    apply intOfZ_injective
    change intOfZ (zOfInt ((posToNat mantissaLeft : Int) * (posToNat mantissaRight : Int))) =
      (posToNat (posOfNat (posToNat mantissaLeft * posToNat mantissaRight)) : Int)
    rw [intOfZ_zOfInt, posToNat_posOfNat
      (Nat.mul_pos (posToNat_positive mantissaLeft) (posToNat_positive mantissaRight))]
    simp only [Int.natCast_mul]
  have productDigits := Digits.Zdigits_mult_ge radix2 (Zpos mantissaLeft)
    (Zpos mantissaRight) (by intro impossible; cases impossible) (by intro impossible; cases impossible)
  change Digits.Zmul (Zpos mantissaLeft) (Zpos mantissaRight) =
    Zpos (PArith.BinPos.Pos.mul mantissaLeft mantissaRight) at productIdentity
  rw [productIdentity, ← Digits.Zdigits2_Zdigits, ← Digits.Zdigits2_Zdigits,
    ← Digits.Zdigits2_Zdigits] at productDigits
  change intOfZ _ ≤ intOfZ _ at productDigits
  simp only [Zsub, Zadd, ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add,
    intOfZ_zOfInt, binary_width_digits] at productDigits
  have widthLeftPositive : (0 : Int) < binary_width (Zpos mantissaLeft) := by
    change (0 : Int) < (Digits.digits2_Pnat mantissaLeft + 1 : Nat)
    omega
  have widthRightPositive : (0 : Int) < binary_width (Zpos mantissaRight) := by
    change (0 : Int) < (Digits.digits2_Pnat mantissaRight + 1 : Nat)
    omega
  have minimumNonpositive : intOfZ (emin0 prec emax) ≤ 0 := by
    have positivePrecision := FLX.prec_gt_0 prec
    have precisionBelowMaximum := BinarySingleNaN.prec_lt_emax (prec := prec) (emax := emax)
    change (0 : Int) < intOfZ prec at positivePrecision
    change intOfZ prec < intOfZ emax at precisionBelowMaximum
    change intOfZ (Zsub (Zsub (Zpos (.xI .xH)) emax) prec) ≤ 0
    simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    change (3 : Int) - intOfZ emax - intOfZ prec ≤ 0
    omega
  change intOfZ _ ≤ intOfZ _
  rw [binary_fexp_integer]
  simp only [Zadd, ZArith.BinInt.Z.add, intOfZ_zOfInt, binary_width_digits]
  change (binary_width (Zpos mantissaLeft) : Int) + binary_width (Zpos mantissaRight) - 1 ≤
    binary_width (Zpos (PArith.BinPos.Pos.mul mantissaLeft mantissaRight)) at productDigits
  simp only [Int.max_def] at canonicalLeft canonicalRight ⊢
  split at canonicalLeft <;> split at canonicalRight <;> split <;> omega

theorem Bmult_result_obligation_proof :
    ∀ {prec emax : Z} [FLX.Prec_gt_0 prec] [BinarySingleNaN.Prec_lt_emax prec emax],
      Bmult_result_obligation (prec := prec) (emax := emax) := by
  intro prec emax positivePrecision validFormat nanProvider rounding
    ⟨left, validLeft⟩ ⟨right, validRight⟩
  refine BSN2B_result_obligation_proof (nanProvider left right) ⟨_, ?_⟩
  cases left <;> cases right <;> try rfl
  rename_i signLeft mantissaLeft exponentLeft signRight mantissaRight exponentRight
  apply BinarySingleNaN.SF2BCertificateStatement_proof
  apply binary_round_aux_valid
  · change (0 : Int) ≤ (posToNat (PArith.BinPos.Pos.mul mantissaLeft mantissaRight) : Int)
    omega
  · exact binary_product_aligned mantissaLeft mantissaRight exponentLeft exponentRight validLeft validRight

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem binary_width_shift_nat (mantissa : positive) (count : Nat) :
    binary_width (Zpos (PArith.BinPos.Pos.shiftl_nat mantissa count)) =
      binary_width (Zpos mantissa) + count := by
  induction count with
  | zero => simp [PArith.BinPos.Pos.shiftl_nat, posOfNat_posToNat]
  | succ count inductionHypothesis =>
      have nextShift : PArith.BinPos.Pos.shiftl_nat mantissa (count + 1) =
          .xO (PArith.BinPos.Pos.shiftl_nat mantissa count) := by
        apply posToNat_injective
        change posToNat (posOfNat (posToNat mantissa * 2 ^ (count + 1))) =
          2 * posToNat (posOfNat (posToNat mantissa * 2 ^ count))
        rw [posToNat_posOfNat (Nat.mul_pos (posToNat_positive mantissa) (Nat.two_pow_pos _)),
          posToNat_posOfNat (Nat.mul_pos (posToNat_positive mantissa) (Nat.two_pow_pos _))]
        rw [Nat.pow_succ, ← Nat.mul_assoc]
        omega
      rw [nextShift]
      change binary_width (Zpos (PArith.BinPos.Pos.shiftl_nat mantissa count)) + 1 =
        binary_width (Zpos mantissa) + (count + 1)
      rw [inductionHypothesis]
      omega

private theorem binary_shl_align_aligned (prec emax : Z) (mantissa : positive) (exponent : Z) :
    let output := BinarySingleNaN.shl_align_fexp (prec := prec) (emax := emax) mantissa exponent
    Zle output.2 (fexp0 prec emax (Zadd (Digits.Zdigits2 (Zpos output.1)) output.2)) := by
  let target := fexp0 prec emax (Zadd (Digits.Zdigits2 (Zpos mantissa)) exponent)
  have shape : BinarySingleNaN.shl_align_fexp (prec := prec) (emax := emax) mantissa exponent =
    (match Zsub target exponent with
      | .Zneg count => (ZArith.Zpower.shift_pos count mantissa, target)
      | _ => (mantissa, exponent)) := rfl
  dsimp only
  rw [shape]
  cases shiftAmount : Zsub target exponent with
  | Z0 =>
      change intOfZ exponent ≤ intOfZ target
      have integerShift := congrArg intOfZ shiftAmount
      simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] at integerShift
      change intOfZ target - intOfZ exponent = 0 at integerShift
      omega
  | Zpos count =>
      change intOfZ exponent ≤ intOfZ target
      have integerShift := congrArg intOfZ shiftAmount
      simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] at integerShift
      change intOfZ target - intOfZ exponent = (posToNat count : Int) at integerShift
      omega
  | Zneg count =>
      change Zle target (fexp0 prec emax
        (Zadd (Digits.Zdigits2 (Zpos (ZArith.Zpower.shift_pos count mantissa))) target))
      have preservedMagnitude :
          Zadd (Digits.Zdigits2 (Zpos (ZArith.Zpower.shift_pos count mantissa))) target =
          Zadd (Digits.Zdigits2 (Zpos mantissa)) exponent := by
        apply intOfZ_injective
        simp only [Zadd, ZArith.BinInt.Z.add, intOfZ_zOfInt, binary_width_digits]
        have shiftedWidth := binary_width_shift_nat mantissa (posToNat count)
        change binary_width (Zpos (ZArith.Zpower.shift_pos count mantissa)) =
          binary_width (Zpos mantissa) + posToNat count at shiftedWidth
        rw [shiftedWidth]
        have integerShift := congrArg intOfZ shiftAmount
        simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] at integerShift
        change intOfZ target - intOfZ exponent = -(posToNat count : Int) at integerShift
        omega
      rw [preservedMagnitude]
      exact Int.le_refl _

private theorem binary_round_valid {prec emax : Z}
    [FLX.Prec_gt_0 prec] [BinarySingleNaN.Prec_lt_emax prec emax]
    (rounding : BinarySingleNaN.mode) (sign : Bool) (mantissa : positive) (exponent : Z) :
    BinarySingleNaN.valid_binary0 prec emax
      (BinarySingleNaN.binary_round (prec := prec) (emax := emax) rounding sign mantissa exponent) = true := by
  apply binary_round_aux_valid
  · change (0 : Int) ≤ (posToNat _ : Int)
    omega
  · exact binary_shl_align_aligned prec emax mantissa exponent

private theorem binary_single_normalize_valid {prec emax : Z}
    [FLX.Prec_gt_0 prec] [BinarySingleNaN.Prec_lt_emax prec emax]
    (rounding : BinarySingleNaN.mode) (mantissa exponent : Z) (zeroSign : Bool) :
    BinarySingleNaN.BinaryFloatCertificate
      (BinarySingleNaN.binary_normalize (prec := prec) (emax := emax) rounding mantissa exponent zeroSign) := by
  cases mantissa with
  | Z0 => rfl
  | Zpos mantissa =>
      apply BinarySingleNaN.SF2BCertificateStatement_proof
      exact binary_round_valid rounding false mantissa exponent
  | Zneg mantissa =>
      apply BinarySingleNaN.SF2BCertificateStatement_proof
      exact binary_round_valid rounding true mantissa exponent

theorem binary_normalize_result_obligation_proof :
    ∀ {prec emax : Z} [FLX.Prec_gt_0 prec] [BinarySingleNaN.Prec_lt_emax prec emax]
      [BinaryNormalizeCertificate prec emax],
      binary_normalize_result_obligation (prec := prec) (emax := emax) := by
  intro prec emax positivePrecision validFormat normalizeCertificate rounding mantissa exponent zeroSign
  exact BSN2B'_result_obligation_proof
    ⟨_, binary_single_normalize_valid rounding mantissa exponent zeroSign⟩
    (normalizeCertificate.is_nan_binary_normalize rounding mantissa exponent zeroSign)

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

theorem Bplus_result_obligation_proof :
    ∀ {prec emax : Z} [Core.FLX.Prec_gt_0 prec]
      [BinarySingleNaN.Prec_lt_emax prec emax],
      Bplus_result_obligation (prec := prec) (emax := emax) := by
  intro prec emax positivePrecision validFormat nanProvider rounding
    ⟨left, validLeft⟩ ⟨right, validRight⟩
  refine BSN2B_result_obligation_proof (nanProvider left right) ⟨_, ?_⟩
  cases left <;> cases right <;>
    simp only [B2BSN, BinarySingleNaN.Bplus] <;>
    try rfl
  all_goals try exact validLeft
  all_goals try exact validRight
  all_goals try (split <;> rfl)
  exact binary_single_normalize_valid rounding _ _ _

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

theorem Bminus_result_obligation_proof :
    ∀ {prec emax : Z} [Core.FLX.Prec_gt_0 prec]
      [BinarySingleNaN.Prec_lt_emax prec emax],
      Bminus_result_obligation (prec := prec) (emax := emax) := by
  intro prec emax positivePrecision validFormat nanProvider rounding
    ⟨left, validLeft⟩ ⟨right, validRight⟩
  refine BSN2B_result_obligation_proof (nanProvider left right) ⟨_, ?_⟩
  cases left <;> cases right <;>
    simp only [B2BSN, BinarySingleNaN.Bminus] <;>
    try rfl
  all_goals try exact validLeft
  all_goals try exact validRight
  all_goals try (split <;> rfl)
  exact binary_single_normalize_valid rounding _ _ _

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem binary_positive_width_bounds (mantissa : positive) :
    2 ^ (binary_width (Zpos mantissa) - 1) ≤ posToNat mantissa ∧
      posToNat mantissa < 2 ^ binary_width (Zpos mantissa) := by
  induction mantissa with
  | xH => decide
  | xO mantissa inductionHypothesis =>
      simp only [binary_width, Digits.digits2_Pnat, posToNat, Nat.add_sub_cancel,
        Nat.pow_succ] at inductionHypothesis ⊢
      omega
  | xI mantissa inductionHypothesis =>
      simp only [binary_width, Digits.digits2_Pnat, posToNat, Nat.add_sub_cancel,
        Nat.pow_succ] at inductionHypothesis ⊢
      omega

private theorem binary_width_upper (value : Z) :
    (intOfZ value).natAbs < 2 ^ binary_width value := by
  cases value with
  | Z0 => decide
  | Zpos mantissa => exact (binary_positive_width_bounds mantissa).2
  | Zneg mantissa =>
      change (-(posToNat mantissa : Int)).natAbs < 2 ^ binary_width (Zpos mantissa)
      simpa only [Int.natAbs_neg, Int.natAbs_natCast] using
        (binary_positive_width_bounds mantissa).2

private theorem binary_div_positive (numerator : Z) (denominator : positive) :
    ZArith.BinInt.Z.div numerator (Zpos denominator) =
      zOfInt (intOfZ numerator / (posToNat denominator : Int)) := by
  have positiveDenominator : (0 : Int) < posToNat denominator := by
    exact Int.ofNat_lt.mpr (posToNat_positive denominator)
  change zOfInt (if (posToNat denominator : Int) = 0 then 0
    else if 0 < (posToNat denominator : Int) then
      intOfZ numerator / (posToNat denominator : Int) else _) = _
  simp only [Int.ne_of_gt positiveDenominator, positiveDenominator, if_false, if_true]

private theorem binary_quotient_width (numerator denominator : positive) :
    binary_width (Zpos numerator) ≤ binary_width (Zpos denominator) +
      binary_width (ZArith.BinInt.Z.div (Zpos numerator) (Zpos denominator)) := by
  rw [binary_div_positive]
  change binary_width (Zpos numerator) ≤ binary_width (Zpos denominator) +
    binary_width (zOfInt ((posToNat numerator / posToNat denominator : Nat) : Int))
  let quotient := posToNat numerator / posToNat denominator
  let quotientWidth := binary_width (zOfInt (quotient : Int))
  change binary_width (Zpos numerator) ≤ binary_width (Zpos denominator) + quotientWidth
  have quotientUpper : quotient + 1 ≤ 2 ^ quotientWidth := by
    have bound := binary_width_upper (zOfInt (quotient : Int))
    simp only [intOfZ_zOfInt, Int.natAbs_natCast] at bound
    change quotient < 2 ^ quotientWidth at bound
    exact Nat.succ_le_of_lt bound
  have numeratorLower := (binary_positive_width_bounds numerator).1
  have denominatorUpper := (binary_positive_width_bounds denominator).2
  have numeratorUpper : posToNat numerator <
      2 ^ (binary_width (Zpos denominator) + quotientWidth) := by
    calc
      posToNat numerator < posToNat denominator * (quotient + 1) :=
        Nat.lt_mul_div_succ _ (posToNat_positive denominator)
      _ ≤ posToNat denominator * 2 ^ quotientWidth := Nat.mul_le_mul_left _ quotientUpper
      _ < 2 ^ binary_width (Zpos denominator) * 2 ^ quotientWidth :=
        Nat.mul_lt_mul_of_pos_right denominatorUpper (Nat.two_pow_pos _)
      _ = _ := (Nat.pow_add _ _ _).symm
  apply Classical.byContradiction
  intro tooWide
  have exponentOrder : binary_width (Zpos denominator) + quotientWidth ≤
      binary_width (Zpos numerator) - 1 := by omega
  have powerOrder := Nat.pow_le_pow_right (by decide : 0 < 2) exponentOrder
  omega

private def binary_shift_input (mantissa : positive) (amount : Z) : Z :=
  match amount with
  | .Zpos _ => ZArith.BinInt.Z.shiftl (Zpos mantissa) amount
  | .Z0 => Zpos mantissa
  | .Zneg _ => Z0

private theorem binary_shift_positive (mantissa : positive) (amount : Z)
    (nonnegative : Zle Z0 amount) :
    ∃ shifted : positive,
      binary_shift_input mantissa amount = Zpos shifted ∧
      (binary_width (Zpos shifted) : Int) =
        (binary_width (Zpos mantissa) : Int) + intOfZ amount := by
  cases amount with
  | Z0 => exact ⟨mantissa, rfl, Int.add_zero _ |>.symm⟩
  | Zneg count =>
      change (0 : Int) ≤ -(posToNat count : Int) at nonnegative
      have positiveCount := posToNat_positive count
      omega
  | Zpos count =>
      refine ⟨PArith.BinPos.Pos.shiftl_nat mantissa (posToNat count), ?_, ?_⟩
      · apply intOfZ_injective
        change intOfZ (zOfInt ((posToNat mantissa : Int) * (2 : Int) ^ posToNat count)) =
          (posToNat (posOfNat (posToNat mantissa * 2 ^ posToNat count)) : Int)
        rw [intOfZ_zOfInt]
        rw [posToNat_posOfNat (Nat.mul_pos (posToNat_positive mantissa) (Nat.two_pow_pos _))]
        simp only [Int.natCast_mul, Int.natCast_pow]
        rfl
      · rw [binary_width_shift_nat]
        change ((binary_width (Zpos mantissa) + posToNat count : Nat) : Int) =
          (binary_width (Zpos mantissa) : Int) + (posToNat count : Int)
        omega

private theorem binary_min_integer (left right : Z) :
    intOfZ (ZArith.BinInt.Z.min left right) = min (intOfZ left) (intOfZ right) := by
  unfold ZArith.BinInt.Z.min
  split
  · rename_i ordered
    exact (Int.min_eq_left ordered).symm
  · rename_i ordered
    exact (Int.min_eq_right (by omega)).symm

private theorem binary_div_core_valid (prec emax : Z)
    (mantissaLeft mantissaRight : positive) (exponentLeft exponentRight : Z) :
    let result := BinarySingleNaN.SFdiv_core_binary prec emax
      (Zpos mantissaLeft) exponentLeft (Zpos mantissaRight) exponentRight
    Zle Z0 result.1.1 ∧ Zle result.1.2
      (fexp0 prec emax (Zadd (Digits.Zdigits2 result.1.1) result.1.2)) := by
  let magnitude := Zsub (Zadd (Digits.Zdigits2 (Zpos mantissaLeft)) exponentLeft)
    (Zadd (Digits.Zdigits2 (Zpos mantissaRight)) exponentRight)
  let exponent := ZArith.BinInt.Z.min (fexp0 prec emax magnitude)
    (Zsub exponentLeft exponentRight)
  let amount := Zsub (Zsub exponentLeft exponentRight) exponent
  have exponentValue : intOfZ exponent =
      min (max ((binary_width (Zpos mantissaLeft) : Int) + intOfZ exponentLeft -
        binary_width (Zpos mantissaRight) - intOfZ exponentRight - intOfZ prec)
        (intOfZ (emin0 prec emax))) (intOfZ exponentLeft - intOfZ exponentRight) := by
    dsimp only [exponent]
    rw [binary_min_integer, binary_fexp_integer]
    simp only [magnitude, Zsub, Zadd, ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add,
      intOfZ_zOfInt, binary_width_digits]
    congr 2
    omega
  have amountValue : intOfZ amount = intOfZ exponentLeft - intOfZ exponentRight -
      intOfZ exponent := by
    simp only [amount, Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
  have amountNonnegative : Zle Z0 amount := by
    change (0 : Int) ≤ intOfZ amount
    rw [amountValue, exponentValue]
    have ordered := Int.min_le_right
      (max ((binary_width (Zpos mantissaLeft) : Int) + intOfZ exponentLeft -
        binary_width (Zpos mantissaRight) - intOfZ exponentRight - intOfZ prec)
        (intOfZ (emin0 prec emax))) (intOfZ exponentLeft - intOfZ exponentRight)
    omega
  obtain ⟨shifted, shiftedShape, shiftedWidth⟩ :=
    binary_shift_positive mantissaLeft amount amountNonnegative
  change
    let shiftedMantissa := binary_shift_input mantissaLeft amount
    let quotient := ZArith.BinInt.Z.div shiftedMantissa (Zpos mantissaRight)
    Zle Z0 quotient ∧ Zle exponent
      (fexp0 prec emax (Zadd (Digits.Zdigits2 quotient) exponent))
  dsimp only
  rw [shiftedShape]
  constructor
  · rw [binary_div_positive]
    change (0 : Int) ≤ intOfZ (zOfInt ((posToNat shifted / posToNat mantissaRight : Nat) : Int))
    rw [intOfZ_zOfInt]
    exact Int.natCast_nonneg _
  · have quotientWidth := binary_quotient_width shifted mantissaRight
    change intOfZ exponent ≤ intOfZ _
    rw [binary_fexp_integer]
    simp only [Zadd, ZArith.BinInt.Z.add, intOfZ_zOfInt, binary_width_digits]
    rw [amountValue] at shiftedWidth
    simp only [Int.min_def, Int.max_def] at exponentValue ⊢
    split at exponentValue <;> split at exponentValue <;> split <;> omega

theorem Bdiv_result_obligation_proof :
    ∀ {prec emax : Z} [FLX.Prec_gt_0 prec] [BinarySingleNaN.Prec_lt_emax prec emax],
      Bdiv_result_obligation (prec := prec) (emax := emax) := by
  intro prec emax positivePrecision validFormat nanProvider rounding
    ⟨left, validLeft⟩ ⟨right, validRight⟩
  refine BSN2B_result_obligation_proof (nanProvider left right) ⟨_, ?_⟩
  cases left <;> cases right <;> try rfl
  rename_i signLeft mantissaLeft exponentLeft signRight mantissaRight exponentRight
  apply BinarySingleNaN.SF2BCertificateStatement_proof
  apply binary_round_aux_valid
  · exact (binary_div_core_valid prec emax mantissaLeft mantissaRight exponentLeft exponentRight).1
  · exact (binary_div_core_valid prec emax mantissaLeft mantissaRight exponentLeft exponentRight).2

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem binary_sqrt_width (mantissa : positive) :
    binary_width (Zpos mantissa) ≤
      2 * binary_width (zOfInt (Nat.sqrt (posToNat mantissa) : Int)) := by
  let root := Nat.sqrt (posToNat mantissa)
  let rootWidth := binary_width (zOfInt (root : Int))
  change binary_width (Zpos mantissa) ≤ 2 * rootWidth
  have rootUpper : root + 1 ≤ 2 ^ rootWidth := by
    have bound := binary_width_upper (zOfInt (root : Int))
    simp only [intOfZ_zOfInt, Int.natAbs_natCast] at bound
    change root < 2 ^ rootWidth at bound
    exact Nat.succ_le_of_lt bound
  have mantissaLower := (binary_positive_width_bounds mantissa).1
  have mantissaUpper : posToNat mantissa < 2 ^ (rootWidth + rootWidth) := by
    calc
      posToNat mantissa < (root + 1) * (root + 1) := Nat.lt_succ_sqrt _
      _ ≤ 2 ^ rootWidth * 2 ^ rootWidth := Nat.mul_le_mul rootUpper rootUpper
      _ = _ := (Nat.pow_add _ _ _).symm
  apply Classical.byContradiction
  intro tooWide
  have exponentOrder : rootWidth + rootWidth ≤ binary_width (Zpos mantissa) - 1 := by omega
  have powerOrder := Nat.pow_le_pow_right (by decide : 0 < 2) exponentOrder
  omega

private theorem binary_half_integer (value : Z) :
    intOfZ (ZArith.BinInt.Z.div2 value) = intOfZ value / 2 := by
  change intOfZ (ZArith.BinInt.Z.div value (Zpos (.xO .xH))) = _
  rw [binary_div_positive, intOfZ_zOfInt]
  rfl

private theorem binary_sqrt_core_valid (prec emax : Z)
    (mantissa : positive) (inputExponent : Z) :
    let result := BinarySingleNaN.SFsqrt_core_binary prec emax (Zpos mantissa) inputExponent
    Zle Z0 result.1.1 ∧ Zle result.1.2
      (fexp0 prec emax (Zadd (Digits.Zdigits2 result.1.1) result.1.2)) := by
  let magnitude := ZArith.BinInt.Z.div2
    (Zadd (Zadd (Digits.Zdigits2 (Zpos mantissa)) inputExponent) (Zpos .xH))
  let exponent := ZArith.BinInt.Z.min (fexp0 prec emax magnitude)
    (ZArith.BinInt.Z.div2 inputExponent)
  let amount := Zsub inputExponent (Zmul (Zpos (.xO .xH)) exponent)
  have exponentValue : intOfZ exponent =
      min (max (((binary_width (Zpos mantissa) : Int) + intOfZ inputExponent + 1) / 2 -
        intOfZ prec) (intOfZ (emin0 prec emax))) (intOfZ inputExponent / 2) := by
    simp only [exponent, binary_min_integer, binary_fexp_integer, magnitude,
      binary_half_integer, Zadd, ZArith.BinInt.Z.add, intOfZ_zOfInt, binary_width_digits]
    rfl
  have amountValue : intOfZ amount = intOfZ inputExponent - 2 * intOfZ exponent := by
    simp only [amount, Zsub, Zmul, ZArith.BinInt.Z.sub, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    rfl
  have amountNonnegative : Zle Z0 amount := by
    change (0 : Int) ≤ intOfZ amount
    rw [amountValue, exponentValue]
    have ordered := Int.min_le_right
      (max (((binary_width (Zpos mantissa) : Int) + intOfZ inputExponent + 1) / 2 -
        intOfZ prec) (intOfZ (emin0 prec emax))) (intOfZ inputExponent / 2)
    omega
  obtain ⟨shifted, shiftedShape, shiftedWidth⟩ := binary_shift_positive mantissa amount amountNonnegative
  change
    let root := (ZArith.BinInt.Z.sqrtrem (binary_shift_input mantissa amount)).1
    Zle Z0 root ∧ Zle exponent (fexp0 prec emax (Zadd (Digits.Zdigits2 root) exponent))
  dsimp only
  rw [shiftedShape]
  change
    let root := zOfInt (Nat.sqrt (posToNat shifted) : Int)
    Zle Z0 root ∧ Zle exponent (fexp0 prec emax (Zadd (Digits.Zdigits2 root) exponent))
  dsimp only
  constructor
  · change (0 : Int) ≤ intOfZ (zOfInt (Nat.sqrt (posToNat shifted) : Int))
    rw [intOfZ_zOfInt]
    exact Int.natCast_nonneg _
  · have rootWidth := binary_sqrt_width shifted
    change intOfZ exponent ≤ intOfZ _
    rw [binary_fexp_integer]
    simp only [Zadd, ZArith.BinInt.Z.add, intOfZ_zOfInt, binary_width_digits]
    rw [amountValue] at shiftedWidth
    simp only [Int.min_def, Int.max_def] at exponentValue ⊢
    split at exponentValue <;> split at exponentValue <;> split <;> omega

theorem Bsqrt_result_obligation_proof :
    ∀ {prec emax : Z} [FLX.Prec_gt_0 prec] [BinarySingleNaN.Prec_lt_emax prec emax],
      Bsqrt_result_obligation (prec := prec) (emax := emax) := by
  intro prec emax positivePrecision validFormat nanProvider rounding ⟨value, validValue⟩
  refine BSN2B_result_obligation_proof (nanProvider value) ⟨_, ?_⟩
  cases value with
  | B754_zero sign => rfl
  | B754_nan sign payload => rfl
  | B754_infinity sign => cases sign <;> rfl
  | B754_finite sign mantissa exponent =>
      cases sign with
      | true => rfl
      | false =>
          apply BinarySingleNaN.SF2BCertificateStatement_proof
          apply binary_round_aux_valid
          · exact (binary_sqrt_core_valid prec emax mantissa exponent).1
          · exact (binary_sqrt_core_valid prec emax mantissa exponent).2

end CompCert4Lean.Flocq.IEEE754.Binary

namespace CompCert4Lean.Flocq.IEEE754.Binary

open CompCert4Lean.Flocq.Core

private theorem binary_conversion_fields {prec emax : Z}
    (ctx : ExactRealContext) (value : BinarySingleNaN.binary_float prec emax)
    (notNan : BinarySingleNaN.is_nan value = false) :
    Exact.B2R ctx (BSN2B' value notNan) = BinarySingleNaN.Exact.B2R ctx value ∧
      is_finite (BSN2B' value notNan) = BinarySingleNaN.is_finite value ∧
      Bsign (BSN2B' value notNan) = BinarySingleNaN.Bsign value ∧
      FF2SF (B2FF (BSN2B' value notNan)) = BinarySingleNaN.B2SF value := by
  cases value with
  | B754_zero sign => exact ⟨rfl, rfl, rfl, rfl⟩
  | B754_infinity sign => exact ⟨rfl, rfl, rfl, rfl⟩
  | B754_finite sign mantissa exponent => exact ⟨rfl, rfl, rfl, rfl⟩
  | B754_nan => cases notNan

theorem binary_normalize_correct :
    ∀ {prec emax : Z} [FLX.Prec_gt_0 prec] [BinarySingleNaN.Prec_lt_emax prec emax]
      (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
      [BinaryNormalizeCertificate prec emax],
      binary_normalize_correctStatement (prec := prec) (emax := emax) ctx magnitude := by
  intro prec emax precision exponentLimit ctx magnitude certificate rounding mantissa exponent zeroSign
  have result := BinarySingleNaN.binary_normalize_correct
    (prec := prec) (emax := emax) ctx magnitude rounding mantissa exponent zeroSign
  have fields := binary_conversion_fields ctx
    (BinarySingleNaN.binary_normalize (prec := prec) (emax := emax)
      rounding mantissa exponent zeroSign)
    (certificate.is_nan_binary_normalize rounding mantissa exponent zeroSign)
  dsimp only [binary_normalize_correctStatement] at result ⊢
  split <;> rename_i condition
  · rw [if_pos condition] at result
    exact ⟨fields.1.trans result.1, fields.2.1.trans result.2.1,
      fields.2.2.1.trans result.2.2⟩
  · rw [if_neg condition] at result
    apply eq_binary_overflow_FF2SF
    exact fields.2.2.2.trans result

end CompCert4Lean.Flocq.IEEE754.Binary
