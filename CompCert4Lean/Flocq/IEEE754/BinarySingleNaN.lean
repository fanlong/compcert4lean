import CompCert4Lean.Flocq.Calc.Round
import CompCert4Lean.Flocq.Calc.Operations
import CompCert4Lean.Flocq.Calc.Div
import CompCert4Lean.Flocq.Calc.Sqrt
import CompCert4Lean.Flocq.Core.FLT
import CompCert4Lean.Lib.Floats.Model

/-!
# Flocq IEEE-754 binary floats with a single NaN value

This is the definition-translation surface for
`Flocq.IEEE754.BinarySingleNaN`.  Proof-bearing source declarations are
represented by exact source-shaped proposition descriptors below.
-/

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

open CompCert4Lean.Flocq.Core

abbrev R := Raux.R
abbrev Z := Zaux.Z
abbrev positive := Zaux.positive
abbrev comparison := Zaux.comparison
abbrev Lt : comparison := Zaux.Lt
abbrev Eq : comparison := Zaux.Eq
abbrev Gt : comparison := Zaux.Gt
abbrev radix := Zaux.radix
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
abbrev Valid_rnd := Core.Generic_fmt.Valid_rnd
abbrev ZnearestA := Core.Generic_fmt.ZnearestA
abbrev ZnearestE := Core.Round_NE.ZnearestE
abbrev Zfloor := Raux.Zfloor
abbrev Zceil := Raux.Zceil
abbrev Ztrunc := Raux.Ztrunc

abbrev spec_float := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.spec_float
abbrev S754_zero := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.S754_zero
abbrev S754_infinity := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.S754_infinity
abbrev S754_nan := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.S754_nan
abbrev S754_finite := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.S754_finite
abbrev location := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.location
abbrev loc_Exact := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.loc_Exact
abbrev loc_Inexact := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.loc_Inexact
abbrev shr_record := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shr_record
abbrev shr_m := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shr_m
abbrev shr_r := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shr_r
abbrev shr_1 := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shr_1
abbrev shr := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shr
abbrev loc_of_shr_record := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.loc_of_shr_record
abbrev shr_record_of_loc := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shr_record_of_loc
abbrev SFcompare := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.SFcompare
abbrev SFdiv_core_binary := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.SFdiv_core_binary
abbrev SFsqrt_core_binary := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.SFsqrt_core_binary
abbrev bounded0 := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.bounded
abbrev valid_binary0 := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.valid_binary
abbrev canonical_mantissa0 := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.canonical_mantissa
abbrev emin0 := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.emin
abbrev fexp0 := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.fexp
abbrev cond_Zopp := Zaux.cond_Zopp
abbrev Falign {beta : radix} (f1 f2 : float beta) : (Z × Z) × Z :=
  Calc.Operations.Falign f1 f2
abbrev Fplus {beta : radix} (f1 f2 : float beta) : float beta :=
  Calc.Operations.Fplus f1 f2
abbrev Fmult {beta : radix} (f1 f2 : float beta) : float beta :=
  Calc.Operations.Fmult f1 f2
abbrev shl_align := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shl_align
abbrev shr_fexp0 := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shr_fexp
abbrev new_location := Calc.Bracket.new_location
abbrev inbetween_float := Calc.Bracket.inbetween_float
abbrev truncate := Calc.Round.truncate
abbrev cond_incr := Calc.Round.cond_incr
abbrev round_sign_DN := Calc.Round.round_sign_DN
abbrev round_sign_UP := Calc.Round.round_sign_UP
abbrev round_N := Calc.Round.round_N
abbrev Zto_pos := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_pos
abbrev Zdigits := Core.Digits.Zdigits
abbrev digits2_pos := Core.Digits.digits2_pos
abbrev Fdiv_core := Calc.Div.Fdiv_core
abbrev Fsqrt_core := Calc.Sqrt.Fsqrt_core

def SF2R (beta : radix) (x : spec_float) : R :=
  match x with
  | .S754_finite s m e => F2R (Float beta (cond_Zopp s (Zpos m)) e)
  | _ => R0

class Prec_lt_emax (prec emax : Z) : Prop where
  prec_lt_emax : Zlt prec emax

abbrev prec_lt_emax (prec emax : Z) [h : Prec_lt_emax prec emax] : Zlt prec emax := h.prec_lt_emax

variable {prec emax : Z} [Core.FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax]

abbrev emin : Z := emin0 prec emax
abbrev fexp : Z → Z := fexp0 prec emax
abbrev canonical_mantissa : positive → Z → Bool := canonical_mantissa0 prec emax
abbrev bounded : positive → Z → Bool := bounded0 prec emax
abbrev valid_binary : spec_float → Bool := valid_binary0 prec emax

inductive binary_float where
  | B754_zero (s : Bool)
  | B754_infinity (s : Bool)
  | B754_nan
  | B754_finite (s : Bool) (m : positive) (e : Z) : bounded m e = true → binary_float

abbrev B754_zero (s : Bool) : binary_float := binary_float.B754_zero s
abbrev B754_infinity (s : Bool) : binary_float := binary_float.B754_infinity s
abbrev B754_nan : binary_float := binary_float.B754_nan
abbrev B754_finite (s : Bool) (m : positive) (e : Z) (h : bounded0 prec emax m e = true) : binary_float :=
  binary_float.B754_finite s m e h

def SF2B (x : spec_float) : valid_binary0 prec emax x = true → binary_float :=
  match x with
  | .S754_finite s m e => fun h => binary_float.B754_finite s m e h
  | .S754_infinity s => fun _ => .B754_infinity s
  | .S754_zero s => fun _ => .B754_zero s
  | .S754_nan => fun _ => .B754_nan

private def sf2bTotal (x : spec_float) : binary_float :=
  match x with
  | .S754_zero s => .B754_zero s
  | .S754_infinity s => .B754_infinity s
  | .S754_nan => .B754_nan
  | .S754_finite s m e =>
      match h : bounded0 prec emax m e with
      | true => .B754_finite s m e h
      | false => .B754_nan

def B2SF (x : binary_float) : spec_float :=
  match x with
  | .B754_finite s m e _ => .S754_finite s m e
  | .B754_infinity s => .S754_infinity s
  | .B754_zero s => .S754_zero s
  | .B754_nan => .S754_nan

def B2R (f : binary_float) : R :=
  match f with
  | .B754_finite s m e _ => F2R (Float radix2 (cond_Zopp s (Zpos m)) e)
  | _ => R0

def Bsign (x : binary_float) : Bool :=
  match x with
  | .B754_nan => false
  | .B754_zero s => s
  | .B754_infinity s => s
  | .B754_finite s _ _ _ => s

def sign_SF (x : spec_float) : Bool :=
  match x with
  | .S754_nan => false
  | .S754_zero s => s
  | .S754_infinity s => s
  | .S754_finite s _ _ => s

def is_finite (x : binary_float) : Bool :=
  match x with
  | .B754_finite _ _ _ _ | .B754_zero _ => true
  | _ => false

def is_finite_SF (x : spec_float) : Bool :=
  match x with
  | .S754_finite _ _ _ | .S754_zero _ => true
  | _ => false

def is_nan (x : binary_float) : Bool :=
  match x with
  | .B754_nan => true
  | _ => false

def is_nan_SF (x : spec_float) : Bool :=
  match x with
  | .S754_nan => true
  | _ => false

def Bopp (x : binary_float) : binary_float :=
  match x with
  | .B754_nan => x
  | .B754_infinity s => .B754_infinity (!s)
  | .B754_finite s m e h => .B754_finite (!s) m e h
  | .B754_zero s => .B754_zero (!s)

def Bcompare (f1 f2 : binary_float) : Option comparison :=
  SFcompare (B2SF f1) (B2SF f2)

inductive mode where
  | mode_NE
  | mode_ZR
  | mode_DN
  | mode_UP
  | mode_NA

abbrev mode_DN : mode := mode.mode_DN
abbrev mode_NA : mode := mode.mode_NA
abbrev mode_NE : mode := mode.mode_NE
abbrev mode_UP : mode := mode.mode_UP
abbrev mode_ZR : mode := mode.mode_ZR

def round_mode (m : mode) : R → Z :=
  match m with
  | mode.mode_NE => ZnearestE
  | mode.mode_ZR => Ztrunc
  | mode.mode_DN => Zfloor
  | mode.mode_UP => Zceil
  | mode.mode_NA => ZnearestA

def choice_mode (m : mode) (sx : Bool) (mx : Z) (lx : location) : Z :=
  match m with
  | mode.mode_NE => cond_incr (round_N (!((match mx with | .Z0 => true | .Zpos _ => false | .Zneg _ => false))) lx) mx
  | mode.mode_ZR => mx
  | mode.mode_DN => cond_incr (round_sign_DN sx lx) mx
  | mode.mode_UP => cond_incr (round_sign_UP sx lx) mx
  | mode.mode_NA => cond_incr (round_N true lx) mx

def overflow_to_inf (m : mode) (s : Bool) : Bool :=
  match m with
  | mode.mode_NE => true
  | mode.mode_NA => true
  | mode.mode_ZR => false
  | mode.mode_UP => !s
  | mode.mode_DN => s

def binary_overflow (m : mode) (s : Bool) : spec_float :=
  if overflow_to_inf m s then
    .S754_infinity s
  else
    .S754_finite s (Zto_pos (Zsub (Zpower (Zpos (.xO .xH)) prec) Zone)) (Zsub emax prec)

def binary_fit_aux (m : mode) (sx : Bool) (mx : positive) (ex : Z) : spec_float :=
  if Zle_bool ex (Zsub emax prec) then .S754_finite sx mx ex else binary_overflow (prec := prec) (emax := emax) m sx

def shr_fexp (m e : Z) (l : location) : shr_record × Z :=
  shr_fexp0 prec emax m e l

def binary_round_aux (m : mode) (sx : Bool) (mx ex : Z) (lx : location) : spec_float :=
  let (mrs', e') := shr_fexp (prec := prec) (emax := emax) mx ex lx
  let (mrs'', e'') := shr_fexp (prec := prec) (emax := emax)
    (choice_mode m sx (shr_m mrs') (loc_of_shr_record mrs')) e' loc_Exact
  match shr_m mrs'' with
  | .Z0 => .S754_zero sx
  | .Zpos p => binary_fit_aux (prec := prec) (emax := emax) m sx p e''
  | .Zneg _ => .S754_nan

def shl_align_fexp (mx : positive) (ex : Z) : positive × Z :=
  shl_align mx ex (fexp0 prec emax (Zadd (Zpos (digits2_pos mx)) ex))

def binary_round (m : mode) (sx : Bool) (mx : positive) (ex : Z) : spec_float :=
  let (mz, ez) := shl_align_fexp (prec := prec) (emax := emax) mx ex
  binary_round_aux (prec := prec) (emax := emax) m sx (Zpos mz) ez loc_Exact

def binary_normalize (m : mode) (x : Z) (e : Z) (szero : Bool) : binary_float :=
  match x with
  | .Z0 => .B754_zero szero
  | .Zpos p => sf2bTotal (prec := prec) (emax := emax) (binary_round (prec := prec) (emax := emax) m false p e)
  | .Zneg p => sf2bTotal (prec := prec) (emax := emax) (binary_round (prec := prec) (emax := emax) m true p e)

def Fplus_naive (sx : Bool) (mx : positive) (ex : Z)
    (sy : Bool) (my : positive) (ey ez : Z) : Z :=
  let m1 := shl_align mx ex ez
  let m2 := shl_align my ey ez
  Zadd (cond_Zopp sx (Zpos m1.1)) (cond_Zopp sy (Zpos m2.1))

def Bmult (m : mode) (x y : binary_float) : binary_float :=
  match x, y with
  | .B754_nan, _ | _, .B754_nan => .B754_nan
  | .B754_infinity sx, .B754_infinity sy => .B754_infinity (sx ^^ sy)
  | .B754_infinity sx, .B754_finite sy _ _ _ => .B754_infinity (sx ^^ sy)
  | .B754_finite sx _ _ _, .B754_infinity sy => .B754_infinity (sx ^^ sy)
  | .B754_infinity _, .B754_zero _ | .B754_zero _, .B754_infinity _ => .B754_nan
  | .B754_finite sx _ _ _, .B754_zero sy => .B754_zero (sx ^^ sy)
  | .B754_zero sx, .B754_finite sy _ _ _ => .B754_zero (sx ^^ sy)
  | .B754_zero sx, .B754_zero sy => .B754_zero (sx ^^ sy)
  | .B754_finite sx mx ex _, .B754_finite sy my ey _ =>
      sf2bTotal (prec := prec) (emax := emax) (binary_round_aux (prec := prec) (emax := emax) m (sx ^^ sy)
        (Zmul (Zpos mx) (Zpos my)) (Zadd ex ey) loc_Exact)

def Bplus (m : mode) (x y : binary_float) : binary_float :=
  match x, y with
  | .B754_nan, _ | _, .B754_nan => .B754_nan
  | .B754_infinity sx, .B754_infinity sy => if sx == sy then x else .B754_nan
  | .B754_infinity _, _ => x
  | _, .B754_infinity _ => y
  | .B754_zero sx, .B754_zero sy =>
      if sx == sy then x else .B754_zero (match m with | .mode_DN => true | _ => false)
  | .B754_zero _, y => y
  | x, .B754_zero _ => x
  | .B754_finite sx mx ex _, .B754_finite sy my ey _ =>
      let ez := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.min ex ey
      binary_normalize (prec := prec) (emax := emax) m (Fplus_naive sx mx ex sy my ey ez) ez
        (match m with | mode.mode_DN => true | _ => false)

def Bminus (m : mode) (x y : binary_float) : binary_float :=
  match x, y with
  | .B754_nan, _ | _, .B754_nan => .B754_nan
  | .B754_infinity sx, .B754_infinity sy => if sx == !sy then x else .B754_nan
  | .B754_infinity _, _ => x
  | _, .B754_infinity sy => .B754_infinity (!sy)
  | .B754_zero sx, .B754_zero sy =>
      if sx == !sy then x else .B754_zero (match m with | .mode_DN => true | _ => false)
  | .B754_zero _, .B754_finite sy my ey h => .B754_finite (!sy) my ey h
  | x, .B754_zero _ => x
  | .B754_finite sx mx ex _, .B754_finite sy my ey _ =>
      let ez := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.min ex ey
      binary_normalize (prec := prec) (emax := emax) m (Fplus_naive sx mx ex (!sy) my ey ez) ez
        (match m with | mode.mode_DN => true | _ => false)

def Bdiv (m : mode) (x y : binary_float) : binary_float :=
  match x, y with
  | .B754_nan, _ | _, .B754_nan => .B754_nan
  | .B754_infinity _, .B754_infinity _ => .B754_nan
  | .B754_infinity sx, .B754_finite sy _ _ _ => .B754_infinity (sx ^^ sy)
  | .B754_finite sx _ _ _, .B754_infinity sy => .B754_zero (sx ^^ sy)
  | .B754_infinity sx, .B754_zero sy => .B754_infinity (sx ^^ sy)
  | .B754_zero sx, .B754_infinity sy => .B754_zero (sx ^^ sy)
  | .B754_finite sx _ _ _, .B754_zero sy => .B754_infinity (sx ^^ sy)
  | .B754_zero sx, .B754_finite sy _ _ _ => .B754_zero (sx ^^ sy)
  | .B754_zero _, .B754_zero _ => .B754_nan
  | .B754_finite sx mx ex _, .B754_finite sy my ey _ =>
      let (pair, lz) := SFdiv_core_binary prec emax (Zpos mx) ex (Zpos my) ey
      sf2bTotal (prec := prec) (emax := emax) (binary_round_aux (prec := prec) (emax := emax) m (sx ^^ sy) pair.1 pair.2 lz)

def Bsqrt (m : mode) (x : binary_float) : binary_float :=
  match x with
  | .B754_nan => .B754_nan
  | .B754_infinity false => x
  | .B754_infinity true => .B754_nan
  | .B754_finite true _ _ _ => .B754_nan
  | .B754_zero _ => x
  | .B754_finite false mx ex h =>
      let (pair, lz) := SFsqrt_core_binary prec emax (Zpos mx) ex
      sf2bTotal (prec := prec) (emax := emax) (binary_round_aux (prec := prec) (emax := emax) m false pair.1 pair.2 lz)

def valid_rnd_round_mode : Prop := ∀ m : mode, Valid_rnd (round_mode m)

def B2R_BoppStatement : Prop :=
  ∀ x : binary_float, B2R (Bopp x) = Ropp (B2R x)

def B2R_SF2BStatement : Prop :=
  ∀ (x : spec_float)
    (Hx : valid_binary (prec := prec) (emax := emax) x = true),
    B2R (SF2B (prec := prec) (emax := emax) x Hx) = SF2R radix2 x

def B2SF_SF2BStatement : Prop :=
  ∀ (x : spec_float)
    (Hx : valid_binary (prec := prec) (emax := emax) x = true),
    B2SF (SF2B (prec := prec) (emax := emax) x Hx) = x

def B2SF_injStatement : Prop :=
  ∀ x y : binary_float, B2SF x = B2SF y → x = y

def Bcompare_correctStatement : Prop :=
  ∀ (f1 f2 : binary_float),
    is_finite f1 = true →
    is_finite f2 = true →
    Bcompare f1 f2 =
      some (Rcompare (B2R f1) (B2R f2))

def Bcompare_swapStatement : Prop :=
  ∀ (x y : binary_float),
    Bcompare y x =
      match Bcompare x y with
      | some c => some (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp c)
      | none => none

def Bdiv_correctStatement : Prop :=
  ∀ (m : mode) (x y : binary_float),
    B2R y ≠ R0 →
    if Rlt_bool (Rabs (round radix2 (fexp (prec := prec) (emax := emax))
      (round_mode m) (B2R x / B2R y)))
        (bpow radix2 emax) then
      B2R (Bdiv (prec := prec) (emax := emax) m x y) =
        round radix2 (fexp (prec := prec) (emax := emax)) (round_mode m) (B2R x / B2R y) ∧
      is_finite (Bdiv (prec := prec) (emax := emax) m x y) = is_finite x ∧
      (is_nan (Bdiv (prec := prec) (emax := emax) m x y) = false →
        Bsign (Bdiv (prec := prec) (emax := emax) m x y) = (Bsign x ^^ Bsign y))
    else
      B2SF (Bdiv (prec := prec) (emax := emax) m x y) =
        binary_overflow (prec := prec) (emax := emax) m (Bsign x ^^ Bsign y)

def Bdiv_correct_auxStatement : Prop :=
  ∀ (m : mode) (sx : Bool) (mx : positive) (ex : Z)
    (sy : Bool) (my : positive) (ey : Z),
    let x := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex)
    let y := F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey)
    let z :=
      let (pair, lz) := SFdiv_core_binary prec emax (Zpos mx) ex (Zpos my) ey
      binary_round_aux (prec := prec) (emax := emax) m (sx ^^ sy) pair.1 pair.2 lz
    valid_binary (prec := prec) (emax := emax) z = true ∧
    if Rlt_bool (Rabs (round radix2 (fexp (prec := prec) (emax := emax))
      (round_mode m) (x / y)))
        (bpow radix2 emax) then
      SF2R radix2 z = round radix2 (fexp (prec := prec) (emax := emax)) (round_mode m) (x / y) ∧
      is_finite_SF z = true ∧ sign_SF z = (sx ^^ sy)
    else
      z = binary_overflow (prec := prec) (emax := emax) m (sx ^^ sy)

def Bminus_correctStatement : Prop :=
  ∀ (m : mode) (x y : binary_float),
    is_finite x = true →
    is_finite y = true →
    if Rlt_bool (Rabs (round radix2 (fexp (prec := prec) (emax := emax))
      (round_mode m) (B2R x - B2R y)))
        (bpow radix2 emax) then
      B2R (Bminus (prec := prec) (emax := emax) m x y) =
        round radix2 (fexp (prec := prec) (emax := emax)) (round_mode m) (B2R x - B2R y) ∧
      is_finite (Bminus (prec := prec) (emax := emax) m x y) = true ∧
      Bsign (Bminus (prec := prec) (emax := emax) m x y) =
        (match Rcompare (B2R x - B2R y) R0 with
        | .Eq =>
            (match m with
            | mode.mode_DN => (Bsign x || (!Bsign y))
            | _ => (Bsign x && (!Bsign y)))
        | .Lt => true
        | .Gt => false)
    else
      B2SF (Bminus (prec := prec) (emax := emax) m x y) =
        binary_overflow (prec := prec) (emax := emax) m (Bsign x) ∧
      Bsign x = !Bsign y

def Bmult_correctStatement : Prop :=
  ∀ (m : mode) (x y : binary_float),
    if Rlt_bool (Rabs (round radix2 (fexp (prec := prec) (emax := emax))
      (round_mode m) (B2R x * B2R y)))
        (bpow radix2 emax) then
      B2R (Bmult (prec := prec) (emax := emax) m x y) =
        round radix2 (fexp (prec := prec) (emax := emax)) (round_mode m) (B2R x * B2R y) ∧
      is_finite (Bmult (prec := prec) (emax := emax) m x y) = (is_finite x && is_finite y) ∧
      (is_nan (Bmult (prec := prec) (emax := emax) m x y) = false →
        Bsign (Bmult (prec := prec) (emax := emax) m x y) = (Bsign x ^^ Bsign y))
    else
      B2SF (Bmult (prec := prec) (emax := emax) m x y) =
        binary_overflow (prec := prec) (emax := emax) m (Bsign x ^^ Bsign y)

def Bmult_correct_auxStatement : Prop :=
  ∀ (m : mode) (sx : Bool) (mx : positive) (ex : Z)
    (_Hx : bounded (prec := prec) (emax := emax) mx ex = true) (sy : Bool)
    (my : positive) (ey : Z) (_Hy : bounded (prec := prec) (emax := emax) my ey = true),
    let x := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex)
    let y := F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey)
    let z := binary_round_aux (prec := prec) (emax := emax) m (sx ^^ sy)
      (Zpos (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.mul mx my))
      (Zadd ex ey) loc_Exact
    valid_binary (prec := prec) (emax := emax) z = true ∧
    if Rlt_bool (Rabs (round radix2 (fexp (prec := prec) (emax := emax))
      (round_mode m) (x * y)))
        (bpow radix2 emax) then
      SF2R radix2 z = round radix2 (fexp (prec := prec) (emax := emax)) (round_mode m) (x * y) ∧
      is_finite_SF z = true ∧ sign_SF z = (sx ^^ sy)
    else
      z = binary_overflow (prec := prec) (emax := emax) m (sx ^^ sy)

def Bplus_correctStatement : Prop :=
  ∀ (m : mode) (x y : binary_float),
    is_finite x = true →
    is_finite y = true →
    if Rlt_bool (Rabs (round radix2 (fexp (prec := prec) (emax := emax))
      (round_mode m) (B2R x + B2R y)))
        (bpow radix2 emax) then
      B2R (Bplus (prec := prec) (emax := emax) m x y) =
        round radix2 (fexp (prec := prec) (emax := emax)) (round_mode m) (B2R x + B2R y) ∧
      is_finite (Bplus (prec := prec) (emax := emax) m x y) = true ∧
      Bsign (Bplus (prec := prec) (emax := emax) m x y) =
        (match Rcompare (B2R x + B2R y) R0 with
        | .Eq =>
            (match m with
            | mode.mode_DN => (Bsign x || Bsign y)
            | _ => (Bsign x && Bsign y))
        | .Lt => true
        | .Gt => false)
    else
      B2SF (Bplus (prec := prec) (emax := emax) m x y) =
        binary_overflow (prec := prec) (emax := emax) m (Bsign x) ∧ Bsign x = Bsign y

def Bsign_BoppStatement : Prop :=
  ∀ x : binary_float, is_nan x = false → Bsign (Bopp x) = !Bsign x

def Bsign_SF2BStatement : Prop :=
  ∀ (x : spec_float)
    (H : valid_binary (prec := prec) (emax := emax) x = true),
    Bsign (SF2B (prec := prec) (emax := emax) x H) = sign_SF x

def Bsqrt_correct_auxStatement : Prop :=
  ∀ (m : mode) (mx : positive) (ex : Z)
    (_Hx : bounded (prec := prec) (emax := emax) mx ex = true),
    let x := F2R (Float radix2 (Zpos mx) ex)
    let z :=
      let (pair, lz) := SFsqrt_core_binary prec emax (Zpos mx) ex
      binary_round_aux (prec := prec) (emax := emax) m false pair.1 pair.2 lz
    valid_binary (prec := prec) (emax := emax) z = true ∧
    SF2R radix2 z = round radix2 (fexp (prec := prec) (emax := emax)) (round_mode m) (sqrt x) ∧
    is_finite_SF z = true ∧ sign_SF z = false

def Fplus_naive_correctStatement : Prop :=
  ∀ (sx : Bool) (mx : positive) (ex : Z)
    (sy : Bool) (my : positive) (ey ez : Z),
    Zle ez ex → Zle ez ey →
    let x := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex)
    let y := F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey)
    F2R (Float radix2 (Fplus_naive sx mx ex sy my ey ez) ez) = x + y

def abs_B2R_lt_emaxStatement : Prop :=
  ∀ x : binary_float, Rlt (Rabs (B2R x)) (bpow radix2 emax)

def binary_fit_aux_correctStatement : Prop :=
  ∀ (m : mode) (sx : Bool) (mx : positive) (ex : Z),
    canonical_mantissa (prec := prec) (emax := emax) mx ex = true →
    let x := SF2R radix2 (S754_finite sx mx ex)
    let z := binary_fit_aux (prec := prec) (emax := emax) m sx mx ex
    valid_binary (prec := prec) (emax := emax) z = true ∧
    if Rlt_bool (Rabs x) (bpow radix2 emax) then
      SF2R radix2 z = x ∧ is_finite_SF z = true ∧ sign_SF z = sx
    else
      z = binary_overflow (prec := prec) (emax := emax) m sx

def binary_normalize_correctStatement : Prop :=
  ∀ (m : mode) (mx ex : Z) (szero : Bool),
    let x := F2R (Float radix2 mx ex)
    let z := binary_normalize (prec := prec) (emax := emax) m mx ex szero
    if Rlt_bool (Rabs (round radix2 (fexp (prec := prec) (emax := emax)) (round_mode m) x))
      (bpow radix2 emax) then
      B2R z = round radix2 (fexp (prec := prec) (emax := emax)) (round_mode m) x ∧
      is_finite z = true ∧
      Bsign z =
        (match Rcompare x R0 with
        | .Eq => szero
        | .Lt => true
        | .Gt => false)
    else
      B2SF z = binary_overflow (prec := prec) (emax := emax) m (Rlt_bool x R0)

def binary_overflow_correctStatement : Prop :=
  ∀ (m : mode) (s : Bool),
    valid_binary (prec := prec) (emax := emax)
      (binary_overflow (prec := prec) (emax := emax) m s) = true

def binary_round_aux_correctStatement : Prop :=
  ∀ (m : mode) (x : R) (mx : positive) (ex : Z) (lx : location),
    inbetween_float radix2 (Zpos mx) ex (Rabs x) lx →
    Zle ex ((fexp (prec := prec) (emax := emax))
      (Zadd (Zdigits radix2 (Zpos mx)) ex)) →
    let z := binary_round_aux (prec := prec) (emax := emax) m (Rlt_bool x R0) (Zpos mx) ex lx
    valid_binary (prec := prec) (emax := emax) z = true ∧
    if Rlt_bool (Rabs (round radix2 (fexp (prec := prec) (emax := emax)) (round_mode m) x))
      (bpow radix2 emax) then
      SF2R radix2 z = round radix2 (fexp (prec := prec) (emax := emax)) (round_mode m) x ∧
      is_finite_SF z = true ∧ sign_SF z = Rlt_bool x R0
    else
      z = binary_overflow (prec := prec) (emax := emax) m (Rlt_bool x R0)

def binary_round_aux_correct'Statement : Prop :=
  ∀ (m : mode) (x : R) (mx ex : Z) (lx : location),
    x ≠ R0 →
    inbetween_float radix2 mx ex (Rabs x) lx →
    Zle ex (cexp radix2 (fexp (prec := prec) (emax := emax)) x) →
    let z := binary_round_aux (prec := prec) (emax := emax) m (Rlt_bool x R0) mx ex lx
    valid_binary (prec := prec) (emax := emax) z = true ∧
    if Rlt_bool (Rabs (round radix2 (fexp (prec := prec) (emax := emax)) (round_mode m) x))
      (bpow radix2 emax) then
      SF2R radix2 z = round radix2 (fexp (prec := prec) (emax := emax)) (round_mode m) x ∧
      is_finite_SF z = true ∧ sign_SF z = Rlt_bool x R0
    else
      z = binary_overflow (prec := prec) (emax := emax) m (Rlt_bool x R0)

def binary_round_correctStatement : Prop :=
  ∀ (m : mode) (sx : Bool) (mx : positive) (ex : Z),
    let z := binary_round (prec := prec) (emax := emax) m sx mx ex
    valid_binary (prec := prec) (emax := emax) z = true ∧
    let x := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex)
    if Rlt_bool (Rabs (round radix2 (fexp (prec := prec) (emax := emax)) (round_mode m) x))
      (bpow radix2 emax) then
      SF2R radix2 z = round radix2 (fexp (prec := prec) (emax := emax)) (round_mode m) x ∧
      is_finite_SF z = true ∧ sign_SF z = sx
    else
      z = binary_overflow (prec := prec) (emax := emax) m sx

def bounded_canonical_lt_emaxStatement : Prop :=
  ∀ (mx : positive) (ex : Z),
    canonical radix2 (fexp (prec := prec) (emax := emax)) (Float radix2 (Zpos mx) ex) →
    Rlt (F2R (Float radix2 (Zpos mx) ex)) (bpow radix2 emax) →
    bounded (prec := prec) (emax := emax) mx ex = true

def bounded_lt_emaxStatement : Prop :=
  ∀ (mx : positive) (ex : Z),
    bounded (prec := prec) (emax := emax) mx ex = true →
    Rlt (F2R (Float radix2 (Zpos mx) ex)) (bpow radix2 emax)

def canonical_boundedStatement : Prop :=
  ∀ (sx : Bool) (mx : positive) (ex : Z),
    bounded (prec := prec) (emax := emax) mx ex = true →
    canonical radix2 (fexp (prec := prec) (emax := emax))
      (Float radix2 (cond_Zopp sx (Zpos mx)) ex)

def canonical_canonical_mantissaStatement : Prop :=
  ∀ (sx : Bool) (mx : positive) (ex : Z),
    canonical_mantissa (prec := prec) (emax := emax) mx ex = true →
    canonical radix2 (fexp (prec := prec) (emax := emax))
      (Float radix2 (cond_Zopp sx (Zpos mx)) ex)

def fexp_emaxStatement : Prop :=
  fexp (prec := prec) (emax := emax) emax = Zsub emax prec

def generic_format_B2RStatement : Prop :=
  ∀ x : binary_float,
    generic_format radix2 (fexp (prec := prec) (emax := emax)) (B2R x)

def inbetween_shrStatement : Prop :=
  ∀ (x : R) (m e : Z) (l : location) (n : Z),
    Zle Z0 m →
    inbetween_float radix2 m e x l →
    let (mrs, e') := shr (shr_record_of_loc m l) e n
    inbetween_float radix2 (shr_m mrs) e' x (loc_of_shr_record mrs)

def inbetween_shr_1Statement : Prop :=
  ∀ (x : R) (mrs : shr_record) (e : Z),
    Zle Z0 (shr_m mrs) →
    inbetween_float radix2 (shr_m mrs) e x (loc_of_shr_record mrs) →
    inbetween_float radix2 (shr_m (shr_1 mrs)) (Zadd e Zone) x
      (loc_of_shr_record (shr_1 mrs))

def is_finite_BoppStatement : Prop :=
  ∀ x : binary_float, is_finite (Bopp x) = is_finite x

def is_finite_SF2BStatement : Prop :=
  ∀ (x : spec_float)
    (Hx : valid_binary (prec := prec) (emax := emax) x = true),
    is_finite (SF2B (prec := prec) (emax := emax) x Hx) = is_finite_SF x

def is_nan_SF_B2SFStatement : Prop :=
  ∀ x : binary_float, is_nan_SF (B2SF x) = is_nan x

def is_nan_binary_normalizeStatement : Prop :=
  ∀ (m : mode) (mx ex : Z) (szero : Bool),
    is_nan (binary_normalize (prec := prec) (emax := emax) m mx ex szero) = false

def is_nan_binary_overflowStatement : Prop :=
  ∀ (m : mode) (s : Bool),
    is_nan_SF (binary_overflow (prec := prec) (emax := emax) m s) = false

def le_shr1_leStatement : Prop :=
  ∀ mrs : shr_record,
    Zle Z0 (shr_m mrs) ∧
    (Zle Z0 (shr_m (shr_1 mrs)) ∧
      Zle (Zmul Ztwo (shr_m (shr_1 mrs))) (shr_m mrs) ∧
      Zlt (shr_m mrs) (Zmul Ztwo (Zadd (shr_m (shr_1 mrs)) Zone)))

def loc_of_shr_record_of_locStatement : Prop :=
  ∀ (m : Z) (l : location), loc_of_shr_record (shr_record_of_loc m l) = l

def shl_align_correctStatement : Prop :=
  ∀ (mx : positive) (ex e : Z),
    let (mx', ex') := shl_align mx ex e
    F2R (Float radix2 (Zpos mx) ex) = F2R (Float radix2 (Zpos mx') ex') ∧
    Zle ex' e

def shl_align_correct'Statement : Prop :=
  ∀ (mx : positive) (ex e : Z),
    Zle e ex →
    let (mx', ex') := shl_align mx ex e
    F2R (Float radix2 (Zpos mx') e) = F2R (Float radix2 (Zpos mx) ex) ∧ ex' = e

def shl_align_fexp_correctStatement : Prop :=
  ∀ (mx : positive) (ex : Z),
    let (mx', ex') := shl_align_fexp (prec := prec) (emax := emax) mx ex
    F2R (Float radix2 (Zpos mx) ex) = F2R (Float radix2 (Zpos mx') ex') ∧
    Zle ex' ((fexp (prec := prec) (emax := emax))
      (Zadd (Zdigits radix2 (Zpos mx')) ex'))

def shr_fexp_truncateStatement : Prop :=
  ∀ (m e : Z) (l : location),
    Zle Z0 m →
    shr_fexp (prec := prec) (emax := emax) m e l =
      let ((m', e'), l') :=
        truncate radix2 (fexp (prec := prec) (emax := emax)) ((m, e), l)
      (shr_record_of_loc m' l', e')

def shr_m_shr_record_of_locStatement : Prop :=
  ∀ (m : Z) (l : location), shr_m (shr_record_of_loc m l) = m

def shr_natStatement : Prop :=
  ∀ (mrs : shr_record) (e n : Z),
    Zle Z0 n →
    shr mrs e n =
      (Zaux.iter_nat shr_1
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat n) mrs,
        Zadd e n)

def sign_plus_overflowStatement : Prop :=
  ∀ (m : mode) (sx : Bool) (mx : positive) (ex : Z)
    (sy : Bool) (my : positive) (ey : Z),
    bounded (prec := prec) (emax := emax) mx ex = true →
    bounded (prec := prec) (emax := emax) my ey = true →
    let z := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) +
      F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey)
    Rle (bpow radix2 emax)
      (Rabs (round radix2 (fexp (prec := prec) (emax := emax)) (round_mode m) z)) →
    sx = Rlt_bool z R0 ∧ sx = sy

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN
