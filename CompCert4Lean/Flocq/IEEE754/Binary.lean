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

def B2BSN (x : binary_float prec emax) : BinarySingleNaN.binary_float prec emax :=
  match x with
  | .B754_zero s => BinarySingleNaN.B754_zero s
  | .B754_infinity s => BinarySingleNaN.B754_infinity s
  | .B754_nan _ _ => BinarySingleNaN.B754_nan
  | .B754_finite s m e => BinarySingleNaN.B754_finite s m e

def FF2B (x : full_float) : binary_float prec emax :=
  match x with
  | .F754_finite s m e => .B754_finite s m e
  | .F754_infinity s => B754_infinity s
  | .F754_zero s => B754_zero s
  | .F754_nan s pl => .B754_nan s pl

def B2FF (x : binary_float prec emax) : full_float :=
  match x with
  | .B754_finite s m e => F754_finite s m e
  | .B754_infinity s => F754_infinity s
  | .B754_zero s => F754_zero s
  | .B754_nan s pl => F754_nan s pl

def BinaryFloatCertificate (x : binary_float prec emax) : Prop :=
  valid_binary (prec := prec) (emax := emax) (B2FF x) = true

abbrev CertifiedBinaryFloat (prec emax : Z)
    [Core.FLX.Prec_gt_0 prec] [BinarySingleNaN.Prec_lt_emax prec emax] :=
  { x : binary_float prec emax // BinaryFloatCertificate x }

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

def Bopp (opp_nan : binary_float prec emax →
      { x : binary_float prec emax // is_nan x = true })
    (x : binary_float prec emax) : binary_float prec emax :=
  match x with
  | .B754_nan s pl => build_nan (opp_nan (.B754_nan s pl))
  | .B754_infinity s => B754_infinity (!s)
  | .B754_finite s m e => .B754_finite (!s) m e
  | .B754_zero s => B754_zero (!s)

def Babs (abs_nan : binary_float prec emax →
      { x : binary_float prec emax // is_nan x = true })
    (x : binary_float prec emax) : binary_float prec emax :=
  match x with
  | .B754_nan s pl => build_nan (abs_nan (.B754_nan s pl))
  | .B754_infinity _ => B754_infinity false
  | .B754_finite _ m e => .B754_finite false m e
  | .B754_zero _ => B754_zero false

def Bcompare (f1 f2 : binary_float prec emax) : Option comparison :=
  BinarySingleNaN.Bcompare (B2BSN f1) (B2BSN f2)

def binary_overflow (m : BinarySingleNaN.mode) (s : Bool) : full_float :=
  SF2FF (BinarySingleNaN.binary_overflow (prec := prec) (emax := emax) m s)

def Bmult (mult_nan : binary_float prec emax → binary_float prec emax →
      { x : binary_float prec emax // is_nan x = true })
    (m : BinarySingleNaN.mode) (x y : binary_float prec emax) : binary_float prec emax :=
  BSN2B (mult_nan x y)
    (BinarySingleNaN.Bmult (prec := prec) (emax := emax) m (B2BSN x) (B2BSN y))

def binary_normalize (m : BinarySingleNaN.mode) (x e : Z) (szero : Bool) :
    binary_float prec emax :=
  match BinarySingleNaN.binary_normalize (prec := prec) (emax := emax) m x e szero with
  | .B754_zero s => B754_zero s
  | .B754_infinity s => B754_infinity s
  | .B754_finite s m e => .B754_finite s m e
  | .B754_nan => B754_zero szero

def Bplus (plus_nan : binary_float prec emax → binary_float prec emax →
      { x : binary_float prec emax // is_nan x = true })
    (m : BinarySingleNaN.mode) (x y : binary_float prec emax) : binary_float prec emax :=
  BSN2B (plus_nan x y)
    (BinarySingleNaN.Bplus (prec := prec) (emax := emax) m (B2BSN x) (B2BSN y))

def Bminus (minus_nan : binary_float prec emax → binary_float prec emax →
      { x : binary_float prec emax // is_nan x = true })
    (m : BinarySingleNaN.mode) (x y : binary_float prec emax) : binary_float prec emax :=
  BSN2B (minus_nan x y)
    (BinarySingleNaN.Bminus (prec := prec) (emax := emax) m (B2BSN x) (B2BSN y))

def Bdiv (div_nan : binary_float prec emax → binary_float prec emax →
      { x : binary_float prec emax // is_nan x = true })
    (m : BinarySingleNaN.mode) (x y : binary_float prec emax) : binary_float prec emax :=
  BSN2B (div_nan x y)
    (BinarySingleNaN.Bdiv (prec := prec) (emax := emax) m (B2BSN x) (B2BSN y))

def Bsqrt (sqrt_nan : binary_float prec emax →
      { x : binary_float prec emax // is_nan x = true })
    (m : BinarySingleNaN.mode) (x : binary_float prec emax) : binary_float prec emax :=
  BSN2B (sqrt_nan x)
    (BinarySingleNaN.Bsqrt (prec := prec) (emax := emax) m (B2BSN x))

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
  ∀ (nan : { x : binary_float prec emax // is_nan x = true })
    (x : BinarySingleNaN.binary_float prec emax),
    BinaryFloatCertificate nan.1 →
    BinarySingleNaN.BinaryFloatCertificate x →
    B2BSN (BSN2B nan x) = x

def B2BSN_BSN2B'Statement : Prop :=
  ∀ (x : BinarySingleNaN.binary_float prec emax)
    (Nx : BinarySingleNaN.is_nan x = false),
    BinarySingleNaN.BinaryFloatCertificate x →
    B2BSN (BSN2B' x Nx) = x

def B2FF_FF2BStatement : Prop :=
  ∀ (x : full_float) (_Hx : FF2BObligation (prec := prec) (emax := emax) x),
    B2FF (prec := prec) (emax := emax)
      (FF2B (prec := prec) (emax := emax) x) = x

def B2FF_injStatement : Prop :=
  ∀ x y : binary_float prec emax,
    BinaryFloatCertificate x → BinaryFloatCertificate y →
      B2FF x = B2FF y → x = y

def B2R_B2BSNStatement (ctx : ExactRealContext) : Prop :=
  ∀ x : binary_float prec emax,
    BinaryFloatCertificate x →
      BinarySingleNaN.Exact.B2R ctx (B2BSN x) = Exact.B2R ctx x

def B2R_Bsign_injStatement (ctx : ExactRealContext) : Prop :=
  ∀ x y : binary_float prec emax,
    BinaryFloatCertificate x → BinaryFloatCertificate y →
    is_finite x = true → is_finite y = true →
    Exact.B2R ctx x = Exact.B2R ctx y → Bsign x = Bsign y → x = y

def B2R_build_nanStatement (ctx : ExactRealContext) : Prop :=
  ∀ x : { x : binary_float prec emax // is_nan x = true },
    BinaryFloatCertificate x.1 → Exact.B2R ctx (build_nan x) = Exact.R0 ctx

def B2R_injStatement (ctx : ExactRealContext) : Prop :=
  ∀ x y : binary_float prec emax,
    BinaryFloatCertificate x → BinaryFloatCertificate y →
    is_finite_strict x = true → is_finite_strict y = true →
    Exact.B2R ctx x = Exact.B2R ctx y → x = y

def B2SF_B2BSNStatement : Prop :=
  ∀ x : binary_float prec emax, BinaryFloatCertificate x →
    BinarySingleNaN.B2SF (B2BSN x) = B2SF x

def Bcompare_correctStatement (ctx : ExactRealContext) : Prop :=
  ∀ f1 f2 : binary_float prec emax,
    BinaryFloatCertificate f1 → BinaryFloatCertificate f2 →
    is_finite f1 = true → is_finite f2 = true →
    Bcompare f1 f2 = some (Exact.Rcompare ctx (Exact.B2R ctx f1) (Exact.B2R ctx f2))

def Bcompare_swapStatement : Prop :=
  ∀ x y : binary_float prec emax,
    BinaryFloatCertificate x → BinaryFloatCertificate y →
    Bcompare y x = match Bcompare x y with
      | some c => some (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp c)
      | none => none

def Bdiv_correctStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (div_nan : binary_float prec emax → binary_float prec emax →
      { x : binary_float prec emax // is_nan x = true })
    (m : BinarySingleNaN.mode) (x y : binary_float prec emax),
    BinaryFloatCertificate x → BinaryFloatCertificate y →
    Exact.B2R ctx y ≠ Exact.R0 ctx →
    if Exact.Rlt_bool ctx
      (Exact.Rabs ctx (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
        (Exact.round_mode ctx m) (Exact.Rdiv ctx (Exact.B2R ctx x) (Exact.B2R ctx y))))
      (Exact.bpow ctx radix2 emax) then
      Exact.B2R ctx (Bdiv (prec := prec) (emax := emax) div_nan m x y) =
        Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m) (Exact.Rdiv ctx (Exact.B2R ctx x) (Exact.B2R ctx y)) ∧
      is_finite (Bdiv (prec := prec) (emax := emax) div_nan m x y) = is_finite x ∧
      (is_nan (Bdiv (prec := prec) (emax := emax) div_nan m x y) = false →
        Bsign (Bdiv (prec := prec) (emax := emax) div_nan m x y) = (Bsign x ^^ Bsign y))
    else B2FF (Bdiv (prec := prec) (emax := emax) div_nan m x y) =
      binary_overflow (prec := prec) (emax := emax) m (Bsign x ^^ Bsign y)

def Bminus_correctStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (minus_nan : binary_float prec emax → binary_float prec emax →
      { x : binary_float prec emax // is_nan x = true })
    (m : BinarySingleNaN.mode) (x y : binary_float prec emax),
    BinaryFloatCertificate x → BinaryFloatCertificate y →
    is_finite x = true → is_finite y = true →
    if Exact.Rlt_bool ctx
      (Exact.Rabs ctx (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
        (Exact.round_mode ctx m)
        (Exact.Rminus ctx (Exact.B2R ctx x) (Exact.B2R ctx y))))
      (Exact.bpow ctx radix2 emax) then
      Exact.B2R ctx (Bminus (prec := prec) (emax := emax) minus_nan m x y) =
        Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m)
          (Exact.Rminus ctx (Exact.B2R ctx x) (Exact.B2R ctx y)) ∧
      is_finite (Bminus (prec := prec) (emax := emax) minus_nan m x y) = true ∧
      Bsign (Bminus (prec := prec) (emax := emax) minus_nan m x y) =
        (match Exact.Rcompare ctx
          (Exact.Rminus ctx (Exact.B2R ctx x) (Exact.B2R ctx y)) (Exact.R0 ctx) with
        | .Eq => match m with
          | .mode_DN => Bsign x || (!Bsign y)
          | _ => Bsign x && (!Bsign y)
        | .Lt => true
        | .Gt => false)
    else B2FF (Bminus (prec := prec) (emax := emax) minus_nan m x y) =
      binary_overflow (prec := prec) (emax := emax) m (Bsign x) ∧
      Bsign x = !Bsign y

def Bmult_correctStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (mult_nan : binary_float prec emax → binary_float prec emax →
      { x : binary_float prec emax // is_nan x = true })
    (m : BinarySingleNaN.mode) (x y : binary_float prec emax),
    BinaryFloatCertificate x → BinaryFloatCertificate y →
    if Exact.Rlt_bool ctx
      (Exact.Rabs ctx (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
        (Exact.round_mode ctx m)
        (Exact.Rmult ctx (Exact.B2R ctx x) (Exact.B2R ctx y))))
      (Exact.bpow ctx radix2 emax) then
      Exact.B2R ctx (Bmult (prec := prec) (emax := emax) mult_nan m x y) =
        Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m)
          (Exact.Rmult ctx (Exact.B2R ctx x) (Exact.B2R ctx y)) ∧
      is_finite (Bmult (prec := prec) (emax := emax) mult_nan m x y) = (is_finite x && is_finite y) ∧
      (is_nan (Bmult (prec := prec) (emax := emax) mult_nan m x y) = false →
        Bsign (Bmult (prec := prec) (emax := emax) mult_nan m x y) = (Bsign x ^^ Bsign y))
    else B2FF (Bmult (prec := prec) (emax := emax) mult_nan m x y) =
      binary_overflow (prec := prec) (emax := emax) m (Bsign x ^^ Bsign y)

def Bplus_correctStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (plus_nan : binary_float prec emax → binary_float prec emax →
      { x : binary_float prec emax // is_nan x = true })
    (m : BinarySingleNaN.mode) (x y : binary_float prec emax),
    BinaryFloatCertificate x → BinaryFloatCertificate y →
    is_finite x = true → is_finite y = true →
    if Exact.Rlt_bool ctx
      (Exact.Rabs ctx (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
        (Exact.round_mode ctx m)
        (Exact.Rplus ctx (Exact.B2R ctx x) (Exact.B2R ctx y))))
      (Exact.bpow ctx radix2 emax) then
      Exact.B2R ctx (Bplus (prec := prec) (emax := emax) plus_nan m x y) =
        Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m)
          (Exact.Rplus ctx (Exact.B2R ctx x) (Exact.B2R ctx y)) ∧
      is_finite (Bplus (prec := prec) (emax := emax) plus_nan m x y) = true ∧
      Bsign (Bplus (prec := prec) (emax := emax) plus_nan m x y) =
        (match Exact.Rcompare ctx
          (Exact.Rplus ctx (Exact.B2R ctx x) (Exact.B2R ctx y)) (Exact.R0 ctx) with
        | .Eq => match m with
          | .mode_DN => Bsign x || Bsign y
          | _ => Bsign x && Bsign y
        | .Lt => true
        | .Gt => false)
    else B2FF (Bplus (prec := prec) (emax := emax) plus_nan m x y) =
      binary_overflow (prec := prec) (emax := emax) m (Bsign x) ∧ Bsign x = Bsign y

def Bsign_B2BSNStatement : Prop :=
  ∀ x : binary_float prec emax,
    BinaryFloatCertificate x →
    is_nan x = false → BinarySingleNaN.Bsign (B2BSN x) = Bsign x

def FF2SF_B2FFStatement : Prop :=
  ∀ x : binary_float prec emax, BinaryFloatCertificate x →
    FF2SF (B2FF x) = B2SF x

def SF2FF_FF2SFStatement : Prop :=
  ∀ x : full_float, is_nan_FF x = false → SF2FF (FF2SF x) = x

def binary_normalize_correctStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) : Prop :=
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
  ∀ x : binary_float prec emax, BinaryFloatCertificate x →
    Exact.generic_format magnitude radix2 (fexp (prec := prec) (emax := emax))
      (Exact.B2R ctx x)

def is_finite_B2BSNStatement : Prop :=
  ∀ x : binary_float prec emax, BinaryFloatCertificate x →
    BinarySingleNaN.is_finite (B2BSN x) = is_finite x

def is_finite_build_nanStatement : Prop :=
  ∀ x : { x : binary_float prec emax // is_nan x = true },
    BinaryFloatCertificate x.1 →
    is_finite (build_nan x) = false

def is_nan_FF2SFStatement : Prop :=
  ∀ x : full_float, BinarySingleNaN.is_nan_SF (FF2SF x) = is_nan_FF x

def is_nan_build_nanStatement : Prop :=
  ∀ x : { x : binary_float prec emax // is_nan x = true },
    BinaryFloatCertificate x.1 → is_nan (build_nan x) = true

end CompCert4Lean.Flocq.IEEE754.Binary
