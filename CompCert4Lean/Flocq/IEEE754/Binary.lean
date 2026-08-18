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

private inductive full_float_carrier where
  | F754_zero (s : Bool)
  | F754_infinity (s : Bool)
  | F754_nan (s : Bool) (m : positive)
  | F754_finite (s : Bool) (m : positive) (e : Z)

abbrev F754_zero (s : Bool) : full_float_carrier := full_float_carrier.F754_zero s
abbrev F754_infinity (s : Bool) : full_float_carrier := full_float_carrier.F754_infinity s
abbrev F754_nan (s : Bool) (m : positive) : full_float_carrier := full_float_carrier.F754_nan s m
abbrev F754_finite (s : Bool) (m : positive) (e : Z) : full_float_carrier := full_float_carrier.F754_finite s m e

def FF2SF (x : full_float_carrier) : spec_float :=
  match x with
  | .F754_zero s => S754_zero s
  | .F754_infinity s => S754_infinity s
  | .F754_nan _ _ => S754_nan
  | .F754_finite s m e => S754_finite s m e

def SF2FF (x : spec_float) : full_float_carrier :=
  match x with
  | .S754_zero s => F754_zero s
  | .S754_infinity s => F754_infinity s
  | .S754_nan => F754_nan false .xH
  | .S754_finite s m e => F754_finite s m e

def is_nan_FF (f : full_float_carrier) : Bool :=
  match f with
  | .F754_nan _ _ => true
  | _ => false

abbrev emin : Z := emin0 prec emax
abbrev fexp : Z → Z := fexp0 prec emax

/- The source records this as an instance.  The facade's arithmetic provider
   already exposes the same format function; retain the named surface here.
   The proposition is consumed by later proof migration rather than by the
   executable wrappers in this packet. -/
def fexp_correct : Prop := Valid_exp (fexp (prec := prec) (emax := emax))

abbrev bounded : positive → Z → Bool := bounded0 prec emax

def nan_pl (pl : positive) : Bool :=
  Zlt_bool (Zpos (BinarySingleNaN.digits2_pos pl)) prec

def valid_binary (x : full_float_carrier) : Bool :=
  match x with
  | .F754_finite _ m e => bounded (prec := prec) (emax := emax) m e
  | .F754_nan _ pl => nan_pl (prec := prec) pl
  | _ => true

inductive binary_float (prec emax : Z) where
  | B754_zero (s : Bool)
  | B754_infinity (s : Bool)
  | B754_nan (s : Bool) (pl : positive) :
      nan_pl (prec := prec) pl = true → binary_float prec emax
  | B754_finite (s : Bool) (m : positive) (e : Z) :
      bounded (prec := prec) (emax := emax) m e = true → binary_float prec emax

abbrev B754_zero {prec emax : Z} (s : Bool) : binary_float prec emax :=
  binary_float.B754_zero s
abbrev B754_infinity {prec emax : Z} (s : Bool) : binary_float prec emax :=
  binary_float.B754_infinity s
abbrev B754_nan {prec emax : Z} (s : Bool) (pl : positive)
    (h : nan_pl (prec := prec) pl = true) : binary_float prec emax :=
  @binary_float.B754_nan prec emax s pl h
abbrev B754_finite {prec emax : Z} (s : Bool) (m : positive) (e : Z)
    (h : bounded (prec := prec) (emax := emax) m e = true) : binary_float prec emax :=
  @binary_float.B754_finite prec emax s m e h

def B2BSN (x : binary_float prec emax) : BinarySingleNaN.binary_float prec emax :=
  match x with
  | .B754_zero s => BinarySingleNaN.B754_zero s
  | .B754_infinity s => BinarySingleNaN.B754_infinity s
  | .B754_nan _ _ _ => BinarySingleNaN.B754_nan
  | .B754_finite s m e h => BinarySingleNaN.B754_finite s m e h

def FF2B (x : full_float_carrier) :
    valid_binary (prec := prec) (emax := emax) x = true → binary_float prec emax :=
  match x with
  | .F754_finite s m e => fun h => B754_finite s m e h
  | .F754_infinity s => fun _ => B754_infinity s
  | .F754_zero s => fun _ => B754_zero s
  | .F754_nan s pl => fun h => B754_nan s pl h

def B2FF (x : binary_float prec emax) : full_float_carrier :=
  match x with
  | .B754_finite s m e _ => F754_finite s m e
  | .B754_infinity s => F754_infinity s
  | .B754_zero s => F754_zero s
  | .B754_nan s pl _ => F754_nan s pl

def B2R (f : binary_float prec emax) : R :=
  match f with
  | .B754_finite s m e _ => F2R (Float radix2 (cond_Zopp s (Zpos m)) e)
  | _ => R0

def B2SF (x : binary_float prec emax) : spec_float :=
  match x with
  | .B754_finite s m e _ => S754_finite s m e
  | .B754_infinity s => S754_infinity s
  | .B754_zero s => S754_zero s
  | .B754_nan _ _ _ => S754_nan

def is_finite_strict (f : binary_float prec emax) : Bool :=
  match f with
  | .B754_finite _ _ _ _ => true
  | _ => false

def Bsign (x : binary_float prec emax) : Bool :=
  match x with
  | .B754_nan s _ _ => s
  | .B754_zero s => s
  | .B754_infinity s => s
  | .B754_finite s _ _ _ => s

def is_finite (f : binary_float prec emax) : Bool :=
  match f with
  | .B754_finite _ _ _ _ | .B754_zero _ => true
  | _ => false

def is_nan (f : binary_float prec emax) : Bool :=
  match f with
  | .B754_nan _ _ _ => true
  | _ => false

def get_nan_pl (x : binary_float prec emax) : positive :=
  match x with
  | .B754_nan _ pl _ => pl
  | _ => .xH

def build_nan (x : { x : binary_float prec emax // is_nan x = true }) :
    binary_float prec emax :=
  match x with
  | ⟨.B754_nan s pl h, _⟩ => B754_nan s pl h
  | ⟨.B754_zero _, hx⟩ => nomatch hx
  | ⟨.B754_infinity _, hx⟩ => nomatch hx
  | ⟨.B754_finite _ _ _ _, hx⟩ => nomatch hx

def BSN2B (nan : { x : binary_float prec emax // is_nan x = true })
    (x : BinarySingleNaN.binary_float prec emax) : binary_float prec emax :=
  match x with
  | .B754_nan => build_nan nan
  | .B754_zero s => B754_zero s
  | .B754_infinity s => B754_infinity s
  | .B754_finite s m e h => B754_finite s m e h

def BSN2B' (x : BinarySingleNaN.binary_float prec emax)
    : BinarySingleNaN.is_nan x = false → binary_float prec emax :=
  match x with
  | .B754_zero s => fun _ => B754_zero s
  | .B754_infinity s => fun _ => B754_infinity s
  | .B754_nan => fun h => nomatch h
  | .B754_finite s m e h => fun _ => B754_finite s m e h

def Bopp (opp_nan : binary_float prec emax →
      { x : binary_float prec emax // is_nan x = true })
    (x : binary_float prec emax) : binary_float prec emax :=
  match x with
  | .B754_nan s pl h => build_nan (opp_nan (.B754_nan s pl h))
  | .B754_infinity s => B754_infinity (!s)
  | .B754_finite s m e h => B754_finite (!s) m e h
  | .B754_zero s => B754_zero (!s)

def Babs (abs_nan : binary_float prec emax →
      { x : binary_float prec emax // is_nan x = true })
    (x : binary_float prec emax) : binary_float prec emax :=
  match x with
  | .B754_nan s pl h => build_nan (abs_nan (.B754_nan s pl h))
  | .B754_infinity _ => B754_infinity false
  | .B754_finite _ m e h => B754_finite false m e h
  | .B754_zero _ => B754_zero false

def Bcompare (f1 f2 : binary_float prec emax) : Option comparison :=
  BinarySingleNaN.Bcompare (B2BSN f1) (B2BSN f2)

def binary_overflow (m : BinarySingleNaN.mode) (s : Bool) : full_float_carrier :=
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
  | .B754_finite s m e h => B754_finite s m e h
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

def B2BSN_BSN2BStatement : Prop :=
  ∀ (nan : { x : binary_float prec emax // is_nan x = true })
    (x : BinarySingleNaN.binary_float prec emax),
    B2BSN (BSN2B nan x) = x

def B2BSN_BSN2B'Statement : Prop :=
  ∀ (x : BinarySingleNaN.binary_float prec emax)
    (Nx : BinarySingleNaN.is_nan x = false),
    B2BSN (BSN2B' x Nx) = x

def B2FF_FF2BStatement : Prop :=
  ∀ (x : full_float_carrier)
    (Hx : valid_binary (prec := prec) (emax := emax) x = true), B2FF (FF2B x Hx) = x

def B2FF_injStatement : Prop :=
  ∀ x y : binary_float prec emax, B2FF x = B2FF y → x = y

def B2R_B2BSNStatement : Prop :=
  ∀ x : binary_float prec emax, BinarySingleNaN.B2R (B2BSN x) = B2R x

def B2R_Bsign_injStatement : Prop :=
  ∀ x y : binary_float prec emax, is_finite x = true → is_finite y = true →
    B2R x = B2R y → Bsign x = Bsign y → x = y

def B2R_build_nanStatement : Prop :=
  ∀ x : { x : binary_float prec emax // is_nan x = true }, B2R (build_nan x) = R0

def B2R_injStatement : Prop :=
  ∀ x y : binary_float prec emax,
    is_finite_strict x = true → is_finite_strict y = true →
    B2R x = B2R y → x = y

def B2SF_B2BSNStatement : Prop :=
  ∀ x : binary_float prec emax, BinarySingleNaN.B2SF (B2BSN x) = B2SF x

def Bcompare_correctStatement : Prop :=
  ∀ f1 f2 : binary_float prec emax, is_finite f1 = true → is_finite f2 = true →
    Bcompare f1 f2 = some (Rcompare (B2R f1) (B2R f2))

def Bcompare_swapStatement : Prop :=
  ∀ x y : binary_float prec emax,
    Bcompare y x = match Bcompare x y with
      | some c => some (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp c)
      | none => none

def Bdiv_correctStatement : Prop :=
  ∀ (div_nan : binary_float prec emax → binary_float prec emax →
      { x : binary_float prec emax // is_nan x = true })
    (m : BinarySingleNaN.mode) (x y : binary_float prec emax), B2R y ≠ R0 →
    if Rlt_bool (Rabs (round radix2 (fexp (prec := prec) (emax := emax))
      (BinarySingleNaN.round_mode m) (B2R x / B2R y))) (bpow radix2 emax) then
      B2R (Bdiv (prec := prec) (emax := emax) div_nan m x y) = round radix2 (fexp (prec := prec) (emax := emax))
        (BinarySingleNaN.round_mode m) (B2R x / B2R y) ∧
      is_finite (Bdiv (prec := prec) (emax := emax) div_nan m x y) = is_finite x ∧
      (is_nan (Bdiv (prec := prec) (emax := emax) div_nan m x y) = false →
        Bsign (Bdiv (prec := prec) (emax := emax) div_nan m x y) = (Bsign x ^^ Bsign y))
    else B2FF (Bdiv (prec := prec) (emax := emax) div_nan m x y) =
      binary_overflow (prec := prec) (emax := emax) m (Bsign x ^^ Bsign y)

def Bminus_correctStatement : Prop :=
  ∀ (minus_nan : binary_float prec emax → binary_float prec emax →
      { x : binary_float prec emax // is_nan x = true })
    (m : BinarySingleNaN.mode) (x y : binary_float prec emax),
    is_finite x = true → is_finite y = true →
    if Rlt_bool (Rabs (round radix2 (fexp (prec := prec) (emax := emax))
      (BinarySingleNaN.round_mode m) (B2R x - B2R y))) (bpow radix2 emax) then
      B2R (Bminus (prec := prec) (emax := emax) minus_nan m x y) = round radix2 (fexp (prec := prec) (emax := emax))
        (BinarySingleNaN.round_mode m) (B2R x - B2R y) ∧
      is_finite (Bminus (prec := prec) (emax := emax) minus_nan m x y) = true ∧
      Bsign (Bminus (prec := prec) (emax := emax) minus_nan m x y) =
        (match Rcompare (B2R x - B2R y) R0 with
        | .Eq => match m with
          | .mode_DN => Bsign x || (!Bsign y)
          | _ => Bsign x && (!Bsign y)
        | .Lt => true
        | .Gt => false)
    else B2FF (Bminus (prec := prec) (emax := emax) minus_nan m x y) =
      binary_overflow (prec := prec) (emax := emax) m (Bsign x) ∧
      Bsign x = !Bsign y

def Bmult_correctStatement : Prop :=
  ∀ (mult_nan : binary_float prec emax → binary_float prec emax →
      { x : binary_float prec emax // is_nan x = true })
    (m : BinarySingleNaN.mode) (x y : binary_float prec emax),
    if Rlt_bool (Rabs (round radix2 (fexp (prec := prec) (emax := emax))
      (BinarySingleNaN.round_mode m) (B2R x * B2R y))) (bpow radix2 emax) then
      B2R (Bmult (prec := prec) (emax := emax) mult_nan m x y) = round radix2 (fexp (prec := prec) (emax := emax))
        (BinarySingleNaN.round_mode m) (B2R x * B2R y) ∧
      is_finite (Bmult (prec := prec) (emax := emax) mult_nan m x y) = (is_finite x && is_finite y) ∧
      (is_nan (Bmult (prec := prec) (emax := emax) mult_nan m x y) = false →
        Bsign (Bmult (prec := prec) (emax := emax) mult_nan m x y) = (Bsign x ^^ Bsign y))
    else B2FF (Bmult (prec := prec) (emax := emax) mult_nan m x y) =
      binary_overflow (prec := prec) (emax := emax) m (Bsign x ^^ Bsign y)

def Bplus_correctStatement : Prop :=
  ∀ (plus_nan : binary_float prec emax → binary_float prec emax →
      { x : binary_float prec emax // is_nan x = true })
    (m : BinarySingleNaN.mode) (x y : binary_float prec emax),
    is_finite x = true → is_finite y = true →
    if Rlt_bool (Rabs (round radix2 (fexp (prec := prec) (emax := emax))
      (BinarySingleNaN.round_mode m) (B2R x + B2R y))) (bpow radix2 emax) then
      B2R (Bplus (prec := prec) (emax := emax) plus_nan m x y) = round radix2 (fexp (prec := prec) (emax := emax))
        (BinarySingleNaN.round_mode m) (B2R x + B2R y) ∧
      is_finite (Bplus (prec := prec) (emax := emax) plus_nan m x y) = true ∧
      Bsign (Bplus (prec := prec) (emax := emax) plus_nan m x y) =
        (match Rcompare (B2R x + B2R y) R0 with
        | .Eq => match m with
          | .mode_DN => Bsign x || Bsign y
          | _ => Bsign x && Bsign y
        | .Lt => true
        | .Gt => false)
    else B2FF (Bplus (prec := prec) (emax := emax) plus_nan m x y) =
      binary_overflow (prec := prec) (emax := emax) m (Bsign x) ∧ Bsign x = Bsign y

def Bsign_B2BSNStatement : Prop :=
  ∀ x : binary_float prec emax,
    is_nan x = false → BinarySingleNaN.Bsign (B2BSN x) = Bsign x

def FF2SF_B2FFStatement : Prop :=
  ∀ x : binary_float prec emax, FF2SF (B2FF x) = B2SF x

def SF2FF_FF2SFStatement : Prop :=
  ∀ x : full_float_carrier, is_nan_FF x = false → SF2FF (FF2SF x) = x

def binary_normalize_correctStatement : Prop :=
  ∀ (m : BinarySingleNaN.mode) (mx ex : Z) (szero : Bool),
    if Rlt_bool (Rabs (round radix2 (fexp (prec := prec) (emax := emax))
      (BinarySingleNaN.round_mode m) (F2R (Float radix2 mx ex)))) (bpow radix2 emax) then
      B2R (binary_normalize (prec := prec) (emax := emax) m mx ex szero) = round radix2 (fexp (prec := prec) (emax := emax))
        (BinarySingleNaN.round_mode m) (F2R (Float radix2 mx ex)) ∧
      is_finite (binary_normalize (prec := prec) (emax := emax) m mx ex szero) = true ∧
      Bsign (binary_normalize (prec := prec) (emax := emax) m mx ex szero) =
        (match Rcompare (F2R (Float radix2 mx ex)) R0 with
        | .Eq => szero
        | .Lt => true
        | .Gt => false)
    else B2FF (binary_normalize (prec := prec) (emax := emax) m mx ex szero) =
      binary_overflow (prec := prec) (emax := emax) m
        (Rlt_bool (F2R (Float radix2 mx ex)) R0)

def bounded_canonical_lt_emaxStatement : Prop :=
  ∀ (mx : positive) (ex : Z),
    canonical radix2 (fexp (prec := prec) (emax := emax)) (Float radix2 (Zpos mx) ex) →
    Rlt (F2R (Float radix2 (Zpos mx) ex)) (bpow radix2 emax) →
    bounded (prec := prec) (emax := emax) mx ex = true

def bounded_lt_emaxStatement : Prop :=
  ∀ (mx : positive) (ex : Z), bounded (prec := prec) (emax := emax) mx ex = true →
    Rlt (F2R (Float radix2 (Zpos mx) ex)) (bpow radix2 emax)

def eq_binary_overflow_FF2SFStatement : Prop :=
  ∀ (x : full_float_carrier) (m : BinarySingleNaN.mode) (s : Bool),
    FF2SF x = BinarySingleNaN.binary_overflow (prec := prec) (emax := emax) m s →
    x = binary_overflow (prec := prec) (emax := emax) m s

def generic_format_B2RStatement : Prop :=
  ∀ x : binary_float prec emax,
    generic_format radix2 (fexp (prec := prec) (emax := emax)) (B2R x)

def is_finite_B2BSNStatement : Prop :=
  ∀ x : binary_float prec emax, BinarySingleNaN.is_finite (B2BSN x) = is_finite x

def is_finite_build_nanStatement : Prop :=
  ∀ x : { x : binary_float prec emax // is_nan x = true },
    is_finite (build_nan x) = false

def is_nan_FF2SFStatement : Prop :=
  ∀ x : full_float_carrier, BinarySingleNaN.is_nan_SF (FF2SF x) = is_nan_FF x

def is_nan_build_nanStatement : Prop :=
  ∀ x : { x : binary_float prec emax // is_nan x = true }, is_nan (build_nan x) = true

end CompCert4Lean.Flocq.IEEE754.Binary
