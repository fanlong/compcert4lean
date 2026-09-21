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

export Prec_lt_emax (prec_lt_emax)

variable {prec emax : Z}

abbrev emin : Z := emin0 prec emax
abbrev fexp : Z → Z := fexp0 prec emax
abbrev canonical_mantissa : positive → Z → Bool := canonical_mantissa0 prec emax
abbrev bounded : positive → Z → Bool := bounded0 prec emax
abbrev valid_binary : spec_float → Bool := valid_binary0 prec emax

inductive binary_float (prec emax : Z) where
  | B754_zero (s : Bool)
  | B754_infinity (s : Bool)
  | B754_nan
  | B754_finite (s : Bool) (m : positive) (e : Z)

export binary_float (B754_zero B754_infinity B754_nan B754_finite)

def SF2B (x : spec_float) : binary_float prec emax :=
  match x with
  | .S754_finite s m e => .B754_finite s m e
  | .S754_infinity s => .B754_infinity s
  | .S754_zero s => .B754_zero s
  | .S754_nan => .B754_nan

def B2SF (x : binary_float prec emax) : spec_float :=
  match x with
  | .B754_finite s m e => .S754_finite s m e
  | .B754_infinity s => .S754_infinity s
  | .B754_zero s => .S754_zero s
  | .B754_nan => .S754_nan

/-!
`B754_finiteObligation` is the exact proof-only field detached from the Rocq
`B754_finite` constructor.  `BinaryFloatCertificate` is the certified view of
the proof-erased executable carrier, and `SF2BObligation` records the exact
source premise of `SF2B`.  These propositions are theorem-facing only; runtime
construction never consumes a proof value.
-/
def B754_finiteObligation (m : positive) (e : Z) : Prop :=
  bounded0 prec emax m e = true

def BinaryFloatCertificate (x : binary_float prec emax) : Prop :=
  valid_binary0 prec emax (B2SF x) = true

abbrev CertifiedBinaryFloat (prec emax : Z) :=
  { x : binary_float prec emax // BinaryFloatCertificate x }

def SF2BObligation (x : spec_float) : Prop :=
  valid_binary0 prec emax x = true

def SF2BCertificateStatement : Prop :=
  ∀ x : spec_float,
    SF2BObligation (prec := prec) (emax := emax) x →
      BinaryFloatCertificate (SF2B (prec := prec) (emax := emax) x)

def B2R (f : binary_float prec emax) : R :=
  match f with
  | .B754_finite s m e => F2R (Float radix2 (cond_Zopp s (Zpos m)) e)
  | _ => R0

def Bsign (x : binary_float prec emax) : Bool :=
  match x with
  | .B754_nan => false
  | .B754_zero s => s
  | .B754_infinity s => s
  | .B754_finite s _ _ => s

def sign_SF (x : spec_float) : Bool :=
  match x with
  | .S754_nan => false
  | .S754_zero s => s
  | .S754_infinity s => s
  | .S754_finite s _ _ => s

def is_finite (x : binary_float prec emax) : Bool :=
  match x with
  | .B754_finite _ _ _ | .B754_zero _ => true
  | _ => false

def is_finite_SF (x : spec_float) : Bool :=
  match x with
  | .S754_finite _ _ _ | .S754_zero _ => true
  | _ => false

def is_nan (x : binary_float prec emax) : Bool :=
  match x with
  | .B754_nan => true
  | _ => false

def is_nan_SF (x : spec_float) : Bool :=
  match x with
  | .S754_nan => true
  | _ => false

def Bopp (x : binary_float prec emax) : binary_float prec emax :=
  match x with
  | .B754_nan => x
  | .B754_infinity s => .B754_infinity (!s)
  | .B754_finite s m e => .B754_finite (!s) m e
  | .B754_zero s => .B754_zero (!s)

def Bcompare (f1 f2 : binary_float prec emax) : Option comparison :=
  SFcompare (B2SF f1) (B2SF f2)

inductive mode where
  | mode_NE
  | mode_ZR
  | mode_DN
  | mode_UP
  | mode_NA

export mode (mode_NE mode_ZR mode_DN mode_UP mode_NA)

def round_mode (m : mode) : R → Z :=
  match m with
  | mode.mode_NE => ZnearestE
  | mode.mode_ZR => Ztrunc
  | mode.mode_DN => Zfloor
  | mode.mode_UP => Zceil
  | mode.mode_NA => ZnearestA

def choice_mode (m : mode) (sx : Bool) (mx : Z) (lx : location) : Z :=
  match m with
  | mode.mode_NE => cond_incr (round_N (!Zeven mx) lx) mx
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

/-!
The source constructs the finite results below with `SF2B`, feeding it the
validity component of the corresponding correctness lemma.  DMC-003 detaches
those proof terms from executable construction.  This theorem-facing companion
surface preserves the exact four propositions and their proof ownership; it is
never an argument to a runtime operation.
-/
structure ConstructionObligations (prec emax : Z)
    [Core.FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax] : Prop where
  binary_round_correct_validity :
    ∀ (m : mode) (sx : Bool) (mx : positive) (ex : Z),
      valid_binary0 prec emax (binary_round (prec := prec) (emax := emax) m sx mx ex) = true
  Bmult_correct_aux_validity :
    ∀ (m : mode) (sx : Bool) (mx : positive) (ex : Z)
      (_Hx : bounded0 prec emax mx ex = true) (sy : Bool)
      (my : positive) (ey : Z) (_Hy : bounded0 prec emax my ey = true),
      valid_binary0 prec emax
        (binary_round_aux (prec := prec) (emax := emax) m (sx ^^ sy)
          (Zpos (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.mul mx my))
          (Zadd ex ey) loc_Exact) = true
  Bdiv_correct_aux_validity :
    ∀ (m : mode) (sx : Bool) (mx : positive) (ex : Z)
      (sy : Bool) (my : positive) (ey : Z),
      let (pair, lz) := SFdiv_core_binary prec emax (Zpos mx) ex (Zpos my) ey
      valid_binary0 prec emax
        (binary_round_aux (prec := prec) (emax := emax) m (sx ^^ sy)
          pair.1 pair.2 lz) = true
  Bsqrt_correct_aux_validity :
    ∀ (m : mode) (mx : positive) (ex : Z)
      (_Hx : bounded0 prec emax mx ex = true),
      let (pair, lz) := SFsqrt_core_binary prec emax (Zpos mx) ex
      valid_binary0 prec emax
        (binary_round_aux (prec := prec) (emax := emax) m false
          pair.1 pair.2 lz) = true

def binary_normalize [Core.FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (m : mode) (x : Z) (e : Z) (szero : Bool) : binary_float prec emax :=
  match x with
  | .Z0 => .B754_zero szero
  | .Zpos p => SF2B (prec := prec) (emax := emax)
      (binary_round (prec := prec) (emax := emax) m false p e)
  | .Zneg p => SF2B (prec := prec) (emax := emax)
      (binary_round (prec := prec) (emax := emax) m true p e)

def binary_normalize_result_obligation
    [Core.FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax] : Prop :=
  ∀ (m : mode) (x e : Z) (szero : Bool),
    BinaryFloatCertificate
      (binary_normalize (prec := prec) (emax := emax) m x e szero)

def Fplus_naive (sx : Bool) (mx : positive) (ex : Z)
    (sy : Bool) (my : positive) (ey ez : Z) : Z :=
  let m1 := shl_align mx ex ez
  let m2 := shl_align my ey ez
  Zadd (cond_Zopp sx (Zpos m1.1)) (cond_Zopp sy (Zpos m2.1))

def Bmult [Core.FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (m : mode) (x y : binary_float prec emax) : binary_float prec emax :=
  match x, y with
  | .B754_nan, _ | _, .B754_nan => .B754_nan
  | .B754_infinity sx, .B754_infinity sy => .B754_infinity (sx ^^ sy)
  | .B754_infinity sx, .B754_finite sy _ _ => .B754_infinity (sx ^^ sy)
  | .B754_finite sx _ _, .B754_infinity sy => .B754_infinity (sx ^^ sy)
  | .B754_infinity _, .B754_zero _ | .B754_zero _, .B754_infinity _ => .B754_nan
  | .B754_finite sx _ _, .B754_zero sy => .B754_zero (sx ^^ sy)
  | .B754_zero sx, .B754_finite sy _ _ => .B754_zero (sx ^^ sy)
  | .B754_zero sx, .B754_zero sy => .B754_zero (sx ^^ sy)
  | .B754_finite sx mx ex, .B754_finite sy my ey =>
      SF2B (prec := prec) (emax := emax)
        (binary_round_aux (prec := prec) (emax := emax) m (sx ^^ sy)
          (Zpos (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.mul mx my))
          (Zadd ex ey) loc_Exact)

def Bplus [Core.FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (m : mode) (x y : binary_float prec emax) : binary_float prec emax :=
  match x, y with
  | .B754_nan, _ | _, .B754_nan => .B754_nan
  | .B754_infinity sx, .B754_infinity sy => if sx == sy then x else .B754_nan
  | .B754_infinity _, _ => x
  | _, .B754_infinity _ => y
  | .B754_zero sx, .B754_zero sy =>
      if sx == sy then x else .B754_zero (match m with | .mode_DN => true | _ => false)
  | .B754_zero _, y => y
  | x, .B754_zero _ => x
  | .B754_finite sx mx ex, .B754_finite sy my ey =>
      let ez := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.min ex ey
      binary_normalize (prec := prec) (emax := emax) m
        (Fplus_naive sx mx ex sy my ey ez) ez
        (match m with | mode.mode_DN => true | _ => false)

def Bminus [Core.FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (m : mode) (x y : binary_float prec emax) : binary_float prec emax :=
  match x, y with
  | .B754_nan, _ | _, .B754_nan => .B754_nan
  | .B754_infinity sx, .B754_infinity sy => if sx == !sy then x else .B754_nan
  | .B754_infinity _, _ => x
  | _, .B754_infinity sy => .B754_infinity (!sy)
  | .B754_zero sx, .B754_zero sy =>
      if sx == !sy then x else .B754_zero (match m with | .mode_DN => true | _ => false)
  | .B754_zero _, .B754_finite sy my ey => .B754_finite (!sy) my ey
  | x, .B754_zero _ => x
  | .B754_finite sx mx ex, .B754_finite sy my ey =>
      let ez := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.min ex ey
      binary_normalize (prec := prec) (emax := emax) m
        (Fplus_naive sx mx ex (!sy) my ey ez) ez
        (match m with | mode.mode_DN => true | _ => false)

def Bdiv [Core.FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (m : mode) (x y : binary_float prec emax) : binary_float prec emax :=
  match x, y with
  | .B754_nan, _ | _, .B754_nan => .B754_nan
  | .B754_infinity _, .B754_infinity _ => .B754_nan
  | .B754_infinity sx, .B754_finite sy _ _ => .B754_infinity (sx ^^ sy)
  | .B754_finite sx _ _, .B754_infinity sy => .B754_zero (sx ^^ sy)
  | .B754_infinity sx, .B754_zero sy => .B754_infinity (sx ^^ sy)
  | .B754_zero sx, .B754_infinity sy => .B754_zero (sx ^^ sy)
  | .B754_finite sx _ _, .B754_zero sy => .B754_infinity (sx ^^ sy)
  | .B754_zero sx, .B754_finite sy _ _ => .B754_zero (sx ^^ sy)
  | .B754_zero _, .B754_zero _ => .B754_nan
  | .B754_finite sx mx ex, .B754_finite sy my ey =>
      match SFdiv_core_binary prec emax (Zpos mx) ex (Zpos my) ey with
      | (pair, lz) =>
          SF2B (prec := prec) (emax := emax)
            (binary_round_aux (prec := prec) (emax := emax) m (sx ^^ sy)
              pair.1 pair.2 lz)

def Bsqrt [Core.FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (m : mode) (x : binary_float prec emax) : binary_float prec emax :=
  match x with
  | .B754_nan => .B754_nan
  | .B754_infinity false => x
  | .B754_infinity true => .B754_nan
  | .B754_finite true _ _ => .B754_nan
  | .B754_zero _ => x
  | .B754_finite false mx ex =>
      match SFsqrt_core_binary prec emax (Zpos mx) ex with
      | (pair, lz) =>
          SF2B (prec := prec) (emax := emax)
            (binary_round_aux (prec := prec) (emax := emax) m false pair.1 pair.2 lz)

/-!
Exact theorem-facing interpretation selected by RPR-007.  The executable
definitions above remain on the rational runtime carrier.  Everything below
is parameterized by the canonical exact-real context and, where `mag`/`cexp`
is involved, by an explicit exact magnitude provider.
-/
abbrev ExactRealContext := Raux.ExactRealContext

namespace Exact

abbrev Context := ExactRealContext
abbrev Magnitude (ctx : Context) := Raux.Exact.Magnitude ctx
abbrev R (ctx : Context) := Raux.Exact.R ctx

def IZR (ctx : Context) : Z → R ctx := Raux.Exact.IZR ctx
def R0 (ctx : Context) : R ctx := Raux.Exact.R0 ctx
def Ropp (ctx : Context) : R ctx → R ctx := Raux.Exact.Ropp ctx
def Rplus (ctx : Context) : R ctx → R ctx → R ctx := Raux.Exact.Rplus ctx
def Rminus (ctx : Context) : R ctx → R ctx → R ctx := Raux.Exact.Rminus ctx
def Rmult (ctx : Context) : R ctx → R ctx → R ctx := Raux.Exact.Rmult ctx
def Rdiv (ctx : Context) : R ctx → R ctx → R ctx := Raux.Exact.Rdiv ctx
def Rabs (ctx : Context) : R ctx → R ctx := Raux.Exact.Rabs ctx
def Rlt (ctx : Context) : R ctx → R ctx → Prop := Raux.Exact.Rlt ctx
def Rle (ctx : Context) : R ctx → R ctx → Prop := Raux.Exact.Rle ctx
noncomputable def Rcompare (ctx : Context) : R ctx → R ctx → comparison :=
  Raux.Exact.Rcompare ctx
noncomputable def Rlt_bool (ctx : Context) : R ctx → R ctx → Bool :=
  Raux.Exact.Rlt_bool ctx
def bpow (ctx : Context) : radix → Z → R ctx := Raux.Exact.bpow ctx
def sqrt (ctx : Context) : R ctx → R ctx := Raux.Exact.sqrt ctx
def Zfloor (ctx : Context) : R ctx → Z := Raux.Exact.Zfloor ctx
def Zceil (ctx : Context) : R ctx → Z := Raux.Exact.Zceil ctx
noncomputable def Ztrunc (ctx : Context) : R ctx → Z := Raux.Exact.Ztrunc ctx

def F2R (ctx : Context) {beta : radix} (f : float beta) : R ctx :=
  Rmult ctx (IZR ctx (Fnum f)) (bpow ctx beta (Fexp f))

def SF2R (ctx : Context) (beta : radix) (x : spec_float) : R ctx :=
  match x with
  | .S754_finite s m e => F2R ctx (Float beta (cond_Zopp s (Zpos m)) e)
  | _ => R0 ctx

def B2R (ctx : Context) (f : binary_float prec emax) : R ctx :=
  match f with
  | .B754_finite s m e => F2R ctx (Float radix2 (cond_Zopp s (Zpos m)) e)
  | _ => R0 ctx

def mag (magnitude : Magnitude ctx) (beta : radix) (x : R ctx) : Z :=
  (Raux.Exact.mag magnitude beta x).mag_val

def cexp (magnitude : Magnitude ctx) (beta : radix) (fexp : Z → Z)
    (x : R ctx) : Z :=
  fexp (mag magnitude beta x)

def canonical (magnitude : Magnitude ctx) (beta : radix) (fexp : Z → Z)
    (f : float beta) : Prop :=
  Fexp f = cexp magnitude beta fexp (F2R ctx f)

def scaled_mantissa (magnitude : Magnitude ctx) (beta : radix) (fexp : Z → Z)
    (x : R ctx) : R ctx :=
  Rmult ctx x (bpow ctx beta (Zopp (cexp magnitude beta fexp x)))

def generic_format (magnitude : Magnitude ctx) (beta : radix) (fexp : Z → Z)
    (x : R ctx) : Prop :=
  x = F2R ctx
    (Float beta (Ztrunc ctx (scaled_mantissa magnitude beta fexp x))
      (cexp magnitude beta fexp x))

abbrev round (magnitude : Magnitude ctx) (beta : radix) (fexp : Z → Z)
    (rnd : R ctx → Z) (x : R ctx) : R ctx :=
  Core.Generic_fmt.Exact.round ctx magnitude beta fexp rnd x

noncomputable def Znearest (ctx : Context) (choice : Z → Bool) (x : R ctx) : Z :=
  match Rcompare ctx (Rminus ctx x (IZR ctx (Zfloor ctx x)))
      (Rdiv ctx (Raux.Exact.Rone ctx) (Raux.Exact.Rtwo ctx)) with
  | .Lt => Zfloor ctx x
  | .Eq => if choice (Zfloor ctx x) then Zceil ctx x else Zfloor ctx x
  | .Gt => Zceil ctx x

noncomputable def ZnearestA (ctx : Context) (x : R ctx) : Z :=
  Znearest ctx (fun m => Zle_bool Z0 m) x

noncomputable def ZnearestE (ctx : Context) (x : R ctx) : Z :=
  Znearest ctx (fun m => Bool.not (Zeven m)) x

noncomputable def round_mode (ctx : Context) (m : mode) : R ctx → Z :=
  match m with
  | mode.mode_NE => ZnearestE ctx
  | mode.mode_ZR => Ztrunc ctx
  | mode.mode_DN => Zfloor ctx
  | mode.mode_UP => Zceil ctx
  | mode.mode_NA => ZnearestA ctx

end Exact

def valid_rnd_round_modeStatement (ctx : ExactRealContext) : Prop :=
  ∀ m : mode,
    Core.Generic_fmt.Exact.Valid_rnd ctx (Exact.round_mode ctx m)

class ValidRndRoundModeCertificate (ctx : ExactRealContext) : Prop where
  valid : valid_rnd_round_modeStatement ctx

instance valid_rnd_round_mode (ctx : ExactRealContext)
    [certificate : ValidRndRoundModeCertificate ctx] (m : mode) :
    Core.Generic_fmt.Exact.Valid_rnd ctx (Exact.round_mode ctx m) :=
  certificate.valid m

def B2R_BoppStatement (ctx : ExactRealContext) : Prop :=
  ∀ x : binary_float prec emax,
    BinaryFloatCertificate x →
    Exact.B2R ctx (Bopp x) = Exact.Ropp ctx (Exact.B2R ctx x)

def B2R_SF2BStatement (ctx : ExactRealContext) : Prop :=
  ∀ (x : spec_float)
    (Hx : valid_binary (prec := prec) (emax := emax) x = true),
    Exact.B2R ctx (SF2B (prec := prec) (emax := emax) x) =
      Exact.SF2R ctx radix2 x

def B2SF_SF2BStatement : Prop :=
  ∀ (x : spec_float)
    (Hx : valid_binary (prec := prec) (emax := emax) x = true),
    B2SF (SF2B (prec := prec) (emax := emax) x) = x

def B2SF_injStatement : Prop :=
  ∀ x y : binary_float prec emax,
    BinaryFloatCertificate x → BinaryFloatCertificate y →
      B2SF x = B2SF y → x = y

def Bcompare_correctStatement (ctx : ExactRealContext) : Prop :=
  ∀ (f1 f2 : binary_float prec emax),
    BinaryFloatCertificate f1 →
    BinaryFloatCertificate f2 →
    is_finite f1 = true →
    is_finite f2 = true →
    Bcompare f1 f2 =
      some (Exact.Rcompare ctx (Exact.B2R ctx f1) (Exact.B2R ctx f2))

def Bcompare_swapStatement : Prop :=
  ∀ (x y : binary_float prec emax),
    BinaryFloatCertificate x →
    BinaryFloatCertificate y →
    Bcompare y x =
      match Bcompare x y with
      | some c => some (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp c)
      | none => none

def Bdiv_correctStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    [Core.FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax] : Prop :=
  ∀ (m : mode) (x y : binary_float prec emax),
    BinaryFloatCertificate x →
    BinaryFloatCertificate y →
    Exact.B2R ctx y ≠ Exact.R0 ctx →
    if Exact.Rlt_bool ctx
        (Exact.Rabs ctx
          (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
            (Exact.round_mode ctx m)
            (Exact.Rdiv ctx (Exact.B2R ctx x) (Exact.B2R ctx y))))
        (Exact.bpow ctx radix2 emax) then
      Exact.B2R ctx (Bdiv (prec := prec) (emax := emax) m x y) =
        Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m)
          (Exact.Rdiv ctx (Exact.B2R ctx x) (Exact.B2R ctx y)) ∧
      is_finite (Bdiv (prec := prec) (emax := emax) m x y) = is_finite x ∧
      (is_nan (Bdiv (prec := prec) (emax := emax) m x y) = false →
        Bsign (Bdiv (prec := prec) (emax := emax) m x y) =
          (Bsign x ^^ Bsign y))
    else
      B2SF (Bdiv (prec := prec) (emax := emax) m x y) =
        binary_overflow (prec := prec) (emax := emax) m (Bsign x ^^ Bsign y)

def Bdiv_correct_auxStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    [Core.FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax] : Prop :=
  ∀ (m : mode) (sx : Bool) (mx : positive) (ex : Z)
    (sy : Bool) (my : positive) (ey : Z),
    let x := Exact.F2R ctx (Float radix2 (cond_Zopp sx (Zpos mx)) ex)
    let y := Exact.F2R ctx (Float radix2 (cond_Zopp sy (Zpos my)) ey)
    let z :=
      let (pair, lz) := SFdiv_core_binary prec emax (Zpos mx) ex (Zpos my) ey
      binary_round_aux (prec := prec) (emax := emax) m (sx ^^ sy) pair.1 pair.2 lz
    valid_binary (prec := prec) (emax := emax) z = true ∧
    if Exact.Rlt_bool ctx
        (Exact.Rabs ctx
          (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
            (Exact.round_mode ctx m) (Exact.Rdiv ctx x y)))
        (Exact.bpow ctx radix2 emax) then
      Exact.SF2R ctx radix2 z =
        Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m) (Exact.Rdiv ctx x y) ∧
      is_finite_SF z = true ∧ sign_SF z = (sx ^^ sy)
    else
      z = binary_overflow (prec := prec) (emax := emax) m (sx ^^ sy)

def Bminus_correctStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    [Core.FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax] : Prop :=
  ∀ (m : mode) (x y : binary_float prec emax),
    BinaryFloatCertificate x →
    BinaryFloatCertificate y →
    is_finite x = true →
    is_finite y = true →
    if Exact.Rlt_bool ctx
        (Exact.Rabs ctx
          (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
            (Exact.round_mode ctx m)
            (Exact.Rminus ctx (Exact.B2R ctx x) (Exact.B2R ctx y))))
        (Exact.bpow ctx radix2 emax) then
      Exact.B2R ctx (Bminus (prec := prec) (emax := emax) m x y) =
        Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m)
          (Exact.Rminus ctx (Exact.B2R ctx x) (Exact.B2R ctx y)) ∧
      is_finite (Bminus (prec := prec) (emax := emax) m x y) = true ∧
      Bsign (Bminus (prec := prec) (emax := emax) m x y) =
        (match Exact.Rcompare ctx
          (Exact.Rminus ctx (Exact.B2R ctx x) (Exact.B2R ctx y)) (Exact.R0 ctx) with
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

def Bmult_correctStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    [Core.FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax] : Prop :=
  ∀ (m : mode) (x y : binary_float prec emax),
    BinaryFloatCertificate x →
    BinaryFloatCertificate y →
    if Exact.Rlt_bool ctx
        (Exact.Rabs ctx
          (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
            (Exact.round_mode ctx m)
            (Exact.Rmult ctx (Exact.B2R ctx x) (Exact.B2R ctx y))))
        (Exact.bpow ctx radix2 emax) then
      Exact.B2R ctx (Bmult (prec := prec) (emax := emax) m x y) =
        Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m)
          (Exact.Rmult ctx (Exact.B2R ctx x) (Exact.B2R ctx y)) ∧
      is_finite (Bmult (prec := prec) (emax := emax) m x y) =
        (is_finite x && is_finite y) ∧
      (is_nan (Bmult (prec := prec) (emax := emax) m x y) = false →
        Bsign (Bmult (prec := prec) (emax := emax) m x y) =
          (Bsign x ^^ Bsign y))
    else
      B2SF (Bmult (prec := prec) (emax := emax) m x y) =
        binary_overflow (prec := prec) (emax := emax) m (Bsign x ^^ Bsign y)

def Bmult_correct_auxStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    [Core.FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax] : Prop :=
  ∀ (m : mode) (sx : Bool) (mx : positive) (ex : Z)
    (_Hx : bounded (prec := prec) (emax := emax) mx ex = true) (sy : Bool)
    (my : positive) (ey : Z) (_Hy : bounded (prec := prec) (emax := emax) my ey = true),
    let x := Exact.F2R ctx (Float radix2 (cond_Zopp sx (Zpos mx)) ex)
    let y := Exact.F2R ctx (Float radix2 (cond_Zopp sy (Zpos my)) ey)
    let z := binary_round_aux (prec := prec) (emax := emax) m (sx ^^ sy)
      (Zpos (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.mul mx my))
      (Zadd ex ey) loc_Exact
    valid_binary (prec := prec) (emax := emax) z = true ∧
    if Exact.Rlt_bool ctx
        (Exact.Rabs ctx
          (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
            (Exact.round_mode ctx m) (Exact.Rmult ctx x y)))
        (Exact.bpow ctx radix2 emax) then
      Exact.SF2R ctx radix2 z =
        Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m) (Exact.Rmult ctx x y) ∧
      is_finite_SF z = true ∧ sign_SF z = (sx ^^ sy)
    else
      z = binary_overflow (prec := prec) (emax := emax) m (sx ^^ sy)

def Bplus_correctStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    [Core.FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax] : Prop :=
  ∀ (m : mode) (x y : binary_float prec emax),
    BinaryFloatCertificate x →
    BinaryFloatCertificate y →
    is_finite x = true →
    is_finite y = true →
    if Exact.Rlt_bool ctx
        (Exact.Rabs ctx
          (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
            (Exact.round_mode ctx m)
            (Exact.Rplus ctx (Exact.B2R ctx x) (Exact.B2R ctx y))))
        (Exact.bpow ctx radix2 emax) then
      Exact.B2R ctx (Bplus (prec := prec) (emax := emax) m x y) =
        Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m)
          (Exact.Rplus ctx (Exact.B2R ctx x) (Exact.B2R ctx y)) ∧
      is_finite (Bplus (prec := prec) (emax := emax) m x y) = true ∧
      Bsign (Bplus (prec := prec) (emax := emax) m x y) =
        (match Exact.Rcompare ctx
          (Exact.Rplus ctx (Exact.B2R ctx x) (Exact.B2R ctx y)) (Exact.R0 ctx) with
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
  ∀ x : binary_float prec emax,
    BinaryFloatCertificate x → is_nan x = false → Bsign (Bopp x) = !Bsign x

def Bsign_SF2BStatement : Prop :=
  ∀ (x : spec_float)
    (H : valid_binary (prec := prec) (emax := emax) x = true),
    Bsign (SF2B (prec := prec) (emax := emax) x) = sign_SF x

def Bsqrt_correct_auxStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    [Core.FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax] : Prop :=
  ∀ (m : mode) (mx : positive) (ex : Z)
    (_Hx : bounded (prec := prec) (emax := emax) mx ex = true),
    let x := Exact.F2R ctx (Float radix2 (Zpos mx) ex)
    let z :=
      let (pair, lz) := SFsqrt_core_binary prec emax (Zpos mx) ex
      binary_round_aux (prec := prec) (emax := emax) m false pair.1 pair.2 lz
    valid_binary (prec := prec) (emax := emax) z = true ∧
    Exact.SF2R ctx radix2 z =
      Core.Generic_fmt.Exact.round ctx magnitude radix2
        (fexp (prec := prec) (emax := emax))
        (Exact.round_mode ctx m) (Exact.sqrt ctx x) ∧
    is_finite_SF z = true ∧ sign_SF z = false

def Fplus_naive_correctStatement (ctx : ExactRealContext) : Prop :=
  ∀ (sx : Bool) (mx : positive) (ex : Z)
    (sy : Bool) (my : positive) (ey ez : Z),
    Zle ez ex → Zle ez ey →
    let x := Exact.F2R ctx (Float radix2 (cond_Zopp sx (Zpos mx)) ex)
    let y := Exact.F2R ctx (Float radix2 (cond_Zopp sy (Zpos my)) ey)
    Exact.F2R ctx (Float radix2 (Fplus_naive sx mx ex sy my ey ez) ez) =
      Exact.Rplus ctx x y

def abs_B2R_lt_emaxStatement (ctx : ExactRealContext) : Prop :=
  ∀ x : binary_float prec emax,
    BinaryFloatCertificate x →
    Exact.Rlt ctx (Exact.Rabs ctx (Exact.B2R ctx x)) (Exact.bpow ctx radix2 emax)

def binary_fit_aux_correctStatement (ctx : ExactRealContext)
    [Core.FLX.Prec_gt_0 prec]
    [Prec_lt_emax prec emax] : Prop :=
  ∀ (m : mode) (sx : Bool) (mx : positive) (ex : Z),
    canonical_mantissa (prec := prec) (emax := emax) mx ex = true →
    let x := Exact.SF2R ctx radix2 (S754_finite sx mx ex)
    let z := binary_fit_aux (prec := prec) (emax := emax) m sx mx ex
    valid_binary (prec := prec) (emax := emax) z = true ∧
    if Exact.Rlt_bool ctx (Exact.Rabs ctx x) (Exact.bpow ctx radix2 emax) then
      Exact.SF2R ctx radix2 z = x ∧ is_finite_SF z = true ∧ sign_SF z = sx
    else
      z = binary_overflow (prec := prec) (emax := emax) m sx

def binary_normalize_correctStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) [Core.FLX.Prec_gt_0 prec]
    [Prec_lt_emax prec emax] : Prop :=
  ∀ (m : mode) (mx ex : Z) (szero : Bool),
    let x := Exact.F2R ctx (Float radix2 mx ex)
    let z := binary_normalize (prec := prec) (emax := emax) m mx ex szero
    if Exact.Rlt_bool ctx
      (Exact.Rabs ctx
        (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m) x))
      (Exact.bpow ctx radix2 emax) then
      Exact.B2R ctx z =
        Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m) x ∧
      is_finite z = true ∧
      Bsign z =
        (match Exact.Rcompare ctx x (Exact.R0 ctx) with
        | .Eq => szero
        | .Lt => true
        | .Gt => false)
    else
      B2SF z = binary_overflow (prec := prec) (emax := emax) m
        (Exact.Rlt_bool ctx x (Exact.R0 ctx))

def binary_overflow_correctStatement [Core.FLX.Prec_gt_0 prec]
    [Prec_lt_emax prec emax] : Prop :=
  ∀ (m : mode) (s : Bool),
    valid_binary (prec := prec) (emax := emax)
      (binary_overflow (prec := prec) (emax := emax) m s) = true

def binary_round_aux_correctStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) [Core.FLX.Prec_gt_0 prec]
    [Prec_lt_emax prec emax] : Prop :=
  ∀ (m : mode) (x : Exact.R ctx) (mx : positive) (ex : Z) (lx : location),
    CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx radix2 (Zpos mx) ex
      (Exact.Rabs ctx x) lx →
    Zle ex ((fexp (prec := prec) (emax := emax))
      (Zadd (Zdigits radix2 (Zpos mx)) ex)) →
    let z := binary_round_aux (prec := prec) (emax := emax) m
      (Exact.Rlt_bool ctx x (Exact.R0 ctx)) (Zpos mx) ex lx
    valid_binary (prec := prec) (emax := emax) z = true ∧
    if Exact.Rlt_bool ctx
      (Exact.Rabs ctx
        (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m) x))
      (Exact.bpow ctx radix2 emax) then
      Exact.SF2R ctx radix2 z =
        Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m) x ∧
      is_finite_SF z = true ∧ sign_SF z = Exact.Rlt_bool ctx x (Exact.R0 ctx)
    else
      z = binary_overflow (prec := prec) (emax := emax) m
        (Exact.Rlt_bool ctx x (Exact.R0 ctx))

def binary_round_aux_correct'Statement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) [Core.FLX.Prec_gt_0 prec]
    [Prec_lt_emax prec emax] : Prop :=
  ∀ (m : mode) (x : Exact.R ctx) (mx ex : Z) (lx : location),
    x ≠ Exact.R0 ctx →
    CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx radix2 mx ex
      (Exact.Rabs ctx x) lx →
    Zle ex (Exact.cexp magnitude radix2 (fexp (prec := prec) (emax := emax)) x) →
    let z := binary_round_aux (prec := prec) (emax := emax) m
      (Exact.Rlt_bool ctx x (Exact.R0 ctx)) mx ex lx
    valid_binary (prec := prec) (emax := emax) z = true ∧
    if Exact.Rlt_bool ctx
      (Exact.Rabs ctx
        (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m) x))
      (Exact.bpow ctx radix2 emax) then
      Exact.SF2R ctx radix2 z =
        Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m) x ∧
      is_finite_SF z = true ∧ sign_SF z = Exact.Rlt_bool ctx x (Exact.R0 ctx)
    else
      z = binary_overflow (prec := prec) (emax := emax) m
        (Exact.Rlt_bool ctx x (Exact.R0 ctx))

def binary_round_correctStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) [Core.FLX.Prec_gt_0 prec]
    [Prec_lt_emax prec emax] : Prop :=
  ∀ (m : mode) (sx : Bool) (mx : positive) (ex : Z),
    let z := binary_round (prec := prec) (emax := emax) m sx mx ex
    valid_binary (prec := prec) (emax := emax) z = true ∧
    let x := Exact.F2R ctx (Float radix2 (cond_Zopp sx (Zpos mx)) ex)
    if Exact.Rlt_bool ctx
      (Exact.Rabs ctx
        (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m) x))
      (Exact.bpow ctx radix2 emax) then
      Exact.SF2R ctx radix2 z =
        Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m) x ∧
      is_finite_SF z = true ∧ sign_SF z = sx
    else
      z = binary_overflow (prec := prec) (emax := emax) m sx

def bounded_canonical_lt_emaxStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) [Core.FLX.Prec_gt_0 prec]
    [Prec_lt_emax prec emax] : Prop :=
  ∀ (mx : positive) (ex : Z),
    Exact.canonical magnitude radix2 (fexp (prec := prec) (emax := emax))
      (Float radix2 (Zpos mx) ex) →
    Exact.Rlt ctx (Exact.F2R ctx (Float radix2 (Zpos mx) ex))
      (Exact.bpow ctx radix2 emax) →
    bounded (prec := prec) (emax := emax) mx ex = true

def bounded_lt_emaxStatement (ctx : ExactRealContext) : Prop :=
  ∀ (mx : positive) (ex : Z),
    bounded (prec := prec) (emax := emax) mx ex = true →
    Exact.Rlt ctx (Exact.F2R ctx (Float radix2 (Zpos mx) ex))
      (Exact.bpow ctx radix2 emax)

def canonical_boundedStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (sx : Bool) (mx : positive) (ex : Z),
    bounded (prec := prec) (emax := emax) mx ex = true →
    Exact.canonical magnitude radix2 (fexp (prec := prec) (emax := emax))
      (Float radix2 (cond_Zopp sx (Zpos mx)) ex)

def canonical_canonical_mantissaStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (sx : Bool) (mx : positive) (ex : Z),
    canonical_mantissa (prec := prec) (emax := emax) mx ex = true →
    Exact.canonical magnitude radix2 (fexp (prec := prec) (emax := emax))
      (Float radix2 (cond_Zopp sx (Zpos mx)) ex)

def fexp_emaxStatement [Core.FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax] : Prop :=
  fexp (prec := prec) (emax := emax) emax = Zsub emax prec

def generic_format_B2RStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ x : binary_float prec emax,
    BinaryFloatCertificate x →
    Exact.generic_format magnitude radix2 (fexp (prec := prec) (emax := emax))
      (Exact.B2R ctx x)

def inbetween_shrStatement (ctx : ExactRealContext) : Prop :=
  ∀ (x : Exact.R ctx) (m e : Z) (l : location) (n : Z),
    Zle Z0 m →
    CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx radix2 m e x l →
    let (mrs, e') := shr (shr_record_of_loc m l) e n
    CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx radix2 (shr_m mrs) e' x
      (loc_of_shr_record mrs)

def inbetween_shr_1Statement (ctx : ExactRealContext) : Prop :=
  ∀ (x : Exact.R ctx) (mrs : shr_record) (e : Z),
    Zle Z0 (shr_m mrs) →
    CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx radix2 (shr_m mrs) e x
      (loc_of_shr_record mrs) →
    CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx radix2 (shr_m (shr_1 mrs))
      (Zadd e Zone) x (loc_of_shr_record (shr_1 mrs))

def is_finite_BoppStatement : Prop :=
  ∀ x : binary_float prec emax,
    BinaryFloatCertificate x → is_finite (Bopp x) = is_finite x

def is_finite_SF2BStatement : Prop :=
  ∀ (x : spec_float)
    (Hx : valid_binary (prec := prec) (emax := emax) x = true),
    is_finite (SF2B (prec := prec) (emax := emax) x) = is_finite_SF x

def is_nan_SF_B2SFStatement : Prop :=
  ∀ x : binary_float prec emax,
    BinaryFloatCertificate x → is_nan_SF (B2SF x) = is_nan x

def is_nan_binary_normalizeStatement [Core.FLX.Prec_gt_0 prec]
    [Prec_lt_emax prec emax] : Prop :=
  ∀ (m : mode) (mx ex : Z) (szero : Bool),
    is_nan (binary_normalize (prec := prec) (emax := emax) m mx ex szero) = false

def is_nan_binary_overflowStatement : Prop :=
  ∀ (m : mode) (s : Bool),
    is_nan_SF (binary_overflow (prec := prec) (emax := emax) m s) = false

def le_shr1_leStatement : Prop :=
  ∀ mrs : shr_record,
    Zle Z0 (shr_m mrs) →
    Zle Z0 (shr_m (shr_1 mrs)) ∧
      Zle (Zmul Ztwo (shr_m (shr_1 mrs))) (shr_m mrs) ∧
      Zlt (shr_m mrs) (Zmul Ztwo (Zadd (shr_m (shr_1 mrs)) Zone))

def loc_of_shr_record_of_locStatement : Prop :=
  ∀ (m : Z) (l : location), loc_of_shr_record (shr_record_of_loc m l) = l

def shl_align_correctStatement (ctx : ExactRealContext) : Prop :=
  ∀ (mx : positive) (ex e : Z),
    let (mx', ex') := shl_align mx ex e
    Exact.F2R ctx (Float radix2 (Zpos mx) ex) =
      Exact.F2R ctx (Float radix2 (Zpos mx') ex') ∧
    Zle ex' e

def shl_align_correct'Statement (ctx : ExactRealContext) : Prop :=
  ∀ (mx : positive) (ex e : Z),
    Zle e ex →
    let (mx', ex') := shl_align mx ex e
    Exact.F2R ctx (Float radix2 (Zpos mx') e) =
      Exact.F2R ctx (Float radix2 (Zpos mx) ex) ∧ ex' = e

def shl_align_fexp_correctStatement (ctx : ExactRealContext) : Prop :=
  ∀ (mx : positive) (ex : Z),
    let (mx', ex') := shl_align_fexp (prec := prec) (emax := emax) mx ex
    Exact.F2R ctx (Float radix2 (Zpos mx) ex) =
      Exact.F2R ctx (Float radix2 (Zpos mx') ex') ∧
    Zle ex' ((fexp (prec := prec) (emax := emax))
      (Zadd (Zdigits radix2 (Zpos mx')) ex'))

def shr_fexp_truncateStatement [Core.FLX.Prec_gt_0 prec] : Prop :=
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

def sign_plus_overflowStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) [Core.FLX.Prec_gt_0 prec] : Prop :=
  ∀ (m : mode) (sx : Bool) (mx : positive) (ex : Z)
    (sy : Bool) (my : positive) (ey : Z),
    bounded (prec := prec) (emax := emax) mx ex = true →
    bounded (prec := prec) (emax := emax) my ey = true →
    let z := Exact.Rplus ctx
      (Exact.F2R ctx (Float radix2 (cond_Zopp sx (Zpos mx)) ex))
      (Exact.F2R ctx (Float radix2 (cond_Zopp sy (Zpos my)) ey))
    Exact.Rle ctx (Exact.bpow ctx radix2 emax)
      (Exact.Rabs ctx
        (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx m) z)) →
    sx = Exact.Rlt_bool ctx z (Exact.R0 ctx) ∧ sx = sy

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

theorem SF2BCertificateStatement_proof :
    ∀ {prec emax : Z},
      SF2BCertificateStatement (prec := prec) (emax := emax) := by
  intro prec emax x Hx
  cases x <;> exact Hx

theorem B2SF_SF2B :
    ∀ {prec emax : Z}, B2SF_SF2BStatement (prec := prec) (emax := emax) := by
  intro prec emax x Hx
  cases x <;> rfl

theorem B2R_SF2B :
    ∀ {prec emax : Z} (ctx : ExactRealContext),
      B2R_SF2BStatement (prec := prec) (emax := emax) ctx := by
  intro prec emax ctx x Hx
  cases x <;> rfl

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

open CompCert4Lean.Flocq.Core

private theorem zle_zero_zpos (p : positive) : Zle Z0 (Zpos p) := by
  change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p)
  simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]

private theorem zle_zero_add_one (z : Z) (h : Zle Z0 z) : Zle Z0 (Zadd z Zone) := by
  change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z +
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone))
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z at h
  change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z + 1
  omega

private theorem shr1_nonneg (mrs : shr_record) (h : Zle Z0 (shr_m mrs)) :
    Zle Z0 (shr_m (shr_1 mrs)) := by
  cases mrs with
  | mk m r s =>
    cases m with
    | Z0 => change 0 ≤ (0 : Int); omega
    | Zpos p =>
      cases p with
      | xH => change 0 ≤ (0 : Int); omega
      | xO p =>
        change 0 ≤ Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
        exact Int.ofNat_zero_le _
      | xI p =>
        change 0 ≤ Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
        exact Int.ofNat_zero_le _
    | Zneg p =>
      exfalso
      change 0 ≤ -Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at h
      have hp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have : ¬ (0 ≤ -(Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))) := by
        have hp' : 0 < Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) := by
          simpa using (Int.ofNat_lt.mpr (show 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p from hp))
        omega
      exact (this h).elim

private theorem iter_pos_nonneg {A : Type} (P : A → Prop) (f : A → A)
    (hf : ∀ x, P x → P (f x)) :
    ∀ (p : positive) (x : A), P x → P (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.iter_pos f p x) := by
  intro p
  induction p with
  | xH =>
      intro x hx
      exact hf x hx
  | xO p ih =>
      intro x hx
      exact ih _ (ih x hx)
  | xI p ih =>
      intro x hx
      exact ih _ (ih _ (hf x hx))

private theorem shr_nonneg (mrs : shr_record) (e n : Z)
    (h : Zle Z0 (shr_m mrs)) :
    Zle Z0 (shr_m (shr mrs e n).1) := by
  cases n with
  | Z0 => exact h
  | Zneg p => exact h
  | Zpos p =>
      exact iter_pos_nonneg (fun z : shr_record => Zle Z0 (shr_m z))
        shr_1 (fun x hx => shr1_nonneg x hx) p mrs h

private theorem shr_fexp_nonneg (prec emax m e : Z) (l : location)
    (h : Zle Z0 m) :
    Zle Z0 (shr_m (shr_fexp (prec := prec) (emax := emax) m e l).1) := by
  unfold shr_fexp
  apply shr_nonneg
  have hm : shr_m (shr_record_of_loc m l) = m := by
    cases l with
    | loc_Exact => rfl
    | loc_Inexact c => cases c <;> rfl
  rw [hm]
  exact h

private theorem cond_incr_nonneg (b : Bool) (m : Z) (h : Zle Z0 m) :
    Zle Z0 (cond_incr b m) := by
  unfold cond_incr
  simp only [Calc.Round.cond_incr]
  split
  · exact zle_zero_add_one m h
  · exact h

private theorem choice_mode_nonneg (m : mode) (sx : Bool) (mx : Z) (lx : location)
    (h : Zle Z0 mx) : Zle Z0 (choice_mode m sx mx lx) := by
  cases m with
  | mode_NE => exact cond_incr_nonneg _ _ h
  | mode_ZR => exact h
  | mode_DN => exact cond_incr_nonneg _ _ h
  | mode_UP => exact cond_incr_nonneg _ _ h
  | mode_NA => exact cond_incr_nonneg _ _ h

private theorem binary_overflow_not_nan (m : mode) (s : Bool) :
    is_nan_SF (binary_overflow (prec := prec) (emax := emax) m s) = false := by
  unfold binary_overflow
  split <;> rfl

private theorem binary_fit_aux_not_nan (m : mode) (sx : Bool) (mx : positive) (ex : Z) :
    is_nan_SF (binary_fit_aux (prec := prec) (emax := emax) m sx mx ex) = false := by
  unfold binary_fit_aux
  split
  · rfl
  · exact binary_overflow_not_nan m sx

private theorem binary_round_aux_not_nan [Core.FLX.Prec_gt_0 prec]
    [Prec_lt_emax prec emax] (m : mode) (sx : Bool) (mx ex : Z) (lx : location)
    (hmx : Zle Z0 mx) :
    is_nan_SF (binary_round_aux (prec := prec) (emax := emax) m sx mx ex lx) = false := by
  dsimp [binary_round_aux]
  cases hqv : shr_fexp (prec := prec) (emax := emax) mx ex lx with
    | mk mrs' e' =>
    have hq : Zle Z0 (shr_m mrs') := by
      have ht := shr_fexp_nonneg (prec := prec) (emax := emax) mx ex lx hmx
      simpa [hqv] using ht
    have hc : Zle Z0 (choice_mode m sx (shr_m mrs') (loc_of_shr_record mrs')) :=
      choice_mode_nonneg m sx (shr_m mrs') (loc_of_shr_record mrs') hq
    cases hrv : shr_fexp (prec := prec) (emax := emax)
        (choice_mode m sx (shr_m mrs') (loc_of_shr_record mrs')) e' loc_Exact with
    | mk mrs'' e'' =>
      have hr : Zle Z0 (shr_m mrs'') := by
        have ht := shr_fexp_nonneg (prec := prec) (emax := emax)
          (choice_mode m sx (shr_m mrs') (loc_of_shr_record mrs')) e' loc_Exact hc
        simpa [hrv] using ht
      cases hm : shr_m mrs'' with
      | Z0 => simp [hqv, hrv, hm, is_nan_SF]
      | Zpos p =>
        change is_nan_SF (binary_fit_aux (prec := prec) (emax := emax) m sx p e'') = false
        exact binary_fit_aux_not_nan m sx p e''
      | Zneg p =>
        exfalso
        have hr' := hr
        rw [hm] at hr'
        change 0 ≤ -Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hr'
        have hp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
        have hp' : 0 < Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
          Int.ofNat_lt.mpr hp
        omega

private theorem binary_round_not_nan [Core.FLX.Prec_gt_0 prec]
    [Prec_lt_emax prec emax] (m : mode) (sx : Bool) (mx : positive) (ex : Z) :
    is_nan_SF (binary_round (prec := prec) (emax := emax) m sx mx ex) = false := by
  unfold binary_round
  cases hs : shl_align_fexp (prec := prec) (emax := emax) mx ex with
  | mk mz ez =>
      simpa [binary_round, hs] using
        (binary_round_aux_not_nan (prec := prec) (emax := emax) m sx (Zpos mz) ez loc_Exact
          (zle_zero_zpos mz))

private theorem is_nan_SF2B_eq (prec emax : Z) (x : spec_float) :
    is_nan (prec := prec) (emax := emax) (SF2B x) = is_nan_SF x := by
  cases x <;> rfl

theorem is_nan_binary_normalize :
    ∀ {prec emax : Z}, [Core.FLX.Prec_gt_0 prec] → [Prec_lt_emax prec emax] →
      is_nan_binary_normalizeStatement (prec := prec) (emax := emax) := by
  intro prec emax instp inste m mx ex szero
  cases mx with
  | Z0 => rfl
  | Zpos p =>
      rw [show is_nan (binary_normalize (prec := prec) (emax := emax) m (Zpos p) ex szero) =
        is_nan_SF (binary_round (prec := prec) (emax := emax) m false p ex) by
          simp [binary_normalize, is_nan_SF2B_eq prec emax]]
      exact binary_round_not_nan (prec := prec) (emax := emax) m false p ex
  | Zneg p =>
      rw [show is_nan (binary_normalize (prec := prec) (emax := emax) m (Zneg p) ex szero) =
        is_nan_SF (binary_round (prec := prec) (emax := emax) m true p ex) by
          simp [binary_normalize, is_nan_SF2B_eq prec emax]]
      exact binary_round_not_nan (prec := prec) (emax := emax) m true p ex

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

theorem Bsign_SF2B :
    ∀ {prec emax : Z}, Bsign_SF2BStatement (prec := prec) (emax := emax) := by
  intro prec emax x H
  cases x <;> rfl

theorem B2SF_inj :
    ∀ {prec emax : Z}, B2SF_injStatement (prec := prec) (emax := emax) := by
  intro prec emax x y hx hy hxy
  cases x <;> cases y <;> simp [B2SF] at hxy ⊢ <;> assumption

theorem fexp_emax :
    ∀ {prec emax : Z} [Core.FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax],
      fexp (prec := prec) (emax := emax) emax = Zsub emax prec := by
  intro prec emax hp he
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max (Zsub emax prec)
    (Zsub (Zsub (Zpos (.xI .xH)) emax) prec) = Zsub emax prec
  have zsub_int : ∀ a b : Z,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub a b) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a -
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
    intro a b
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a -
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b)) = _
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  have hp' : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec := by
    exact Core.FLX.prec_gt_0 prec
  have he' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emax := by
    exact he.prec_lt_emax
  have hthree : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos (.xI .xH)) = 3 := by
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
  have hnot : ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub emax prec) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zsub (Zsub (Zpos (.xI .xH)) emax) prec) := by
    rw [zsub_int, zsub_int, zsub_int]
    rw [hthree]
    omega
  simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max, hnot]

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

theorem is_nan_SF_B2SF :
    ∀ {prec emax : Z}, is_nan_SF_B2SFStatement (prec := prec) (emax := emax) := by
  intro prec emax x Hx
  cases x <;> rfl

theorem B2R_Bopp :
    ∀ {prec emax : Z} (ctx : ExactRealContext),
      B2R_BoppStatement (prec := prec) (emax := emax) ctx := by
  intro prec emax ctx x Hx
  have hneg0 : Exact.Ropp ctx (Exact.R0 ctx) = Exact.R0 ctx := by
    change ctx.spec.neg ctx.spec.zero = ctx.spec.zero
    calc
      ctx.spec.neg ctx.spec.zero = ctx.spec.add (ctx.spec.neg ctx.spec.zero) ctx.spec.zero :=
        (ctx.certificate.orderedField.add_zero _).symm
      _ = ctx.spec.zero := ctx.certificate.orderedField.neg_add_cancel _
  cases x with
  | B754_nan => simpa [Bopp, B2R, Exact.B2R] using hneg0.symm
  | B754_infinity s => simpa [Bopp, B2R, Exact.B2R] using hneg0.symm
  | B754_zero s => simpa [Bopp, B2R, Exact.B2R] using hneg0.symm
  | B754_finite s m e =>
      cases s with
      | false =>
          change Exact.F2R ctx (Float radix2 (Zopp (Zpos m)) e) =
            Exact.Ropp ctx (Exact.F2R ctx (Float radix2 (Zpos m) e))
          exact CompCert4Lean.Flocq.Core.Float_prop.F2R_Zopp ctx radix2 (Zpos m) e
      | true =>
          have hnegneg : ∀ y : Exact.R ctx, Exact.Ropp ctx (Exact.Ropp ctx y) = y := by
            intro y
            change ctx.spec.neg (ctx.spec.neg y) = y
            calc
              ctx.spec.neg (ctx.spec.neg y) =
                  ctx.spec.add (ctx.spec.neg (ctx.spec.neg y)) ctx.spec.zero :=
                (ctx.certificate.orderedField.add_zero _).symm
              _ = ctx.spec.add (ctx.spec.neg (ctx.spec.neg y))
                  (ctx.spec.add (ctx.spec.neg y) y) := by
                rw [ctx.certificate.orderedField.neg_add_cancel]
              _ = ctx.spec.add
                  (ctx.spec.add (ctx.spec.neg (ctx.spec.neg y)) (ctx.spec.neg y)) y := by
                rw [ctx.certificate.orderedField.add_assoc]
              _ = ctx.spec.add ctx.spec.zero y := by
                rw [ctx.certificate.orderedField.neg_add_cancel]
              _ = y := ctx.certificate.orderedField.zero_add _
          change Exact.F2R ctx (Float radix2 (Zpos m) e) =
            Exact.Ropp ctx (Exact.F2R ctx (Float radix2 (Zopp (Zpos m)) e))
          have hF :=
            CompCert4Lean.Flocq.Core.Float_prop.F2R_Zopp ctx radix2 (Zpos m) e
          have hF' : Exact.F2R ctx (Float radix2 (Zopp (Zpos m)) e) =
              Exact.Ropp ctx (Exact.F2R ctx (Float radix2 (Zpos m) e)) := by
            exact hF
          rw [hF']
          exact (hnegneg _).symm

theorem is_finite_Bopp :
    ∀ {prec emax : Z}, is_finite_BoppStatement (prec := prec) (emax := emax) := by
  intro prec emax x Hx
  cases x <;> rfl

theorem Bsign_Bopp :
    ∀ {prec emax : Z}, Bsign_BoppStatement (prec := prec) (emax := emax) := by
  intro prec emax x Hx Hnan
  cases x <;> simp [Bopp, Bsign, is_nan] at Hnan ⊢

private theorem pg_zcompare_swap (x y : Z) :
    Zcompare y x =
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp (Zcompare x y) := by
  change
    (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x then Lt else
      if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y =
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x then Eq else Gt) =
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp
        (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y then Lt else
          if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x =
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y then Eq else Gt)
  by_cases hxy : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y
  · have hyx : ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x := by omega
    have hne : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y ≠
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x := by omega
    simp [hxy, hyx, hne,
      _root_.CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.CompOpp]
  · by_cases hxy' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y
    · have hyx : ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x := by omega
      simp [hxy, hxy', hyx,
        _root_.CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.CompOpp]
    · have hyx : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x := by omega
      simp [hxy, hxy', hyx,
        _root_.CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.CompOpp]

private theorem pg_poscompare_swap (x y : positive) :
    Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posCompare Eq y x =
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp
        (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posCompare Eq x y) := by
  change
    (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat y <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat x then Lt else
      if CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat y =
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat x then Eq else Gt) =
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp
        (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat x <
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat y then Lt else
          if CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat x =
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat y then Eq else Gt)
  by_cases hxy : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat x <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat y
  · have hyx : ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat y <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat x := by omega
    have hne : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat y ≠
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat x := by omega
    simp [hxy, hyx, hne,
      _root_.CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.CompOpp]
  · by_cases hxy' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat x =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat y
    · have hyx : ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat y <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat x := by omega
      simp [hxy, hxy', hyx,
        _root_.CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.CompOpp]
    · have hyx : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat y <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat x := by omega
      simp [hxy, hxy', hyx,
        _root_.CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.CompOpp]

private theorem pg_SFcompare_swap (x y : spec_float) :
    Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.SFcompare y x =
      match Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.SFcompare x y with
      | some c => some (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp c)
      | none => none := by
  cases x with
  | S754_zero sx =>
      cases y with
      | S754_zero sy => rfl
      | S754_infinity sy => cases sy <;> rfl
      | S754_nan => rfl
      | S754_finite sy my ey => cases sy <;> rfl
  | S754_infinity sx =>
      cases y with
      | S754_zero sy => cases sx <;> rfl
      | S754_infinity sy => cases sx <;> cases sy <;> rfl
      | S754_nan => rfl
      | S754_finite sy my ey => cases sx <;> rfl
  | S754_nan =>
      cases y <;> rfl
  | S754_finite sx mx ex =>
      cases y with
      | S754_zero sy => cases sx <;> rfl
      | S754_infinity sy => cases sy <;> rfl
      | S754_nan => rfl
      | S754_finite sy my ey =>
          cases sx <;> cases sy
          · change
              some (match Zcompare ey ex with
                | .Eq => Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posCompare Eq my mx
                | c => c) =
                some (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp
                  (match Zcompare ex ey with
                  | .Eq => Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posCompare Eq mx my
                  | c => c))
            rw [pg_zcompare_swap ex ey]
            cases h : Zcompare ex ey with
            | Eq => exact congrArg some (pg_poscompare_swap mx my)
            | Lt => rfl
            | Gt => rfl
          · rfl
          · rfl
          · change
              some (match Zcompare ey ex with
                | .Eq => _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp
                    (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posCompare Eq my mx)
                | .Lt => Gt
                | .Gt => Lt) =
                some (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp
                  (match Zcompare ex ey with
                  | .Eq => _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp
                      (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posCompare Eq mx my)
                  | .Lt => Gt
                  | .Gt => Lt))
            rw [pg_zcompare_swap ex ey]
            cases h : Zcompare ex ey with
            | Eq =>
                rw [pg_poscompare_swap mx my]
                cases hpos : Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posCompare Eq mx my <;> rfl
            | Lt => rfl
            | Gt => rfl

theorem Bcompare_swap :
    ∀ {prec emax : Z}, Bcompare_swapStatement (prec := prec) (emax := emax) := by
  intro prec emax x y Hx Hy
  exact pg_SFcompare_swap (B2SF x) (B2SF y)

theorem bounded_lt_emax :
    ∀ {prec emax : Z} (ctx : ExactRealContext),
      bounded_lt_emaxStatement (prec := prec) (emax := emax) ctx := by
  intro prec emax ctx mx ex Hx
  change (canonical_mantissa0 prec emax mx ex &&
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zle_bool ex
      (Zsub emax prec)) = true at Hx
  have Hparts := Bool.and_eq_true_iff.mp Hx
  have Hcan : canonical_mantissa0 prec emax mx ex = true := Hparts.1
  have Hexp : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zle_bool ex
      (Zsub emax prec) = true := Hparts.2
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool
      (fexp0 prec emax (Zadd (Zpos (digits2_pos mx)) ex)) ex = true at Hcan
  have Hcanon := Hcan
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool] at Hcanon
  have Hcanon' : fexp0 prec emax (Zadd (Zpos (digits2_pos mx)) ex) = ex := by
    simp at Hcanon
    exact Hcanon
  have Hexp' : Zle ex (Zsub emax prec) := by
    change (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub emax prec)
      then true else false) = true at Hexp
    simp at Hexp
    exact Hexp
  have zsub_int : ∀ a b : Z,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub a b) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a -
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
    intro a b
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a -
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b)) = _
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  have zadd_int : ∀ a b : Z,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd a b) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a +
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
    intro a b
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a +
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b)) = _
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  have Hcanon'' := Hcanon'
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max
      (Zsub (Zadd (Zpos (digits2_pos mx)) ex) prec)
      (Zsub (Zsub (Zpos (.xI .xH)) emax) prec) = ex at Hcanon''
  have Hfirst : Zle (Zsub (Zadd (Zpos (digits2_pos mx)) ex) prec) ex := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zsub (Zadd (Zpos (digits2_pos mx)) ex) prec) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex
    rw [zsub_int (Zadd (Zpos (digits2_pos mx)) ex) prec,
      zadd_int]
    by_cases hmax : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zsub (Zadd (Zpos (digits2_pos mx)) ex) prec) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zsub (Zsub (Zpos (.xI .xH)) emax) prec)
    · simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max, hmax] at Hcanon''
      have hmax' := hmax
      have hc' := congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Hcanon''
      simp only [zsub_int, zadd_int] at hmax' hc'
      omega
    · simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max, hmax] at Hcanon''
      have hc' := congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Hcanon''
      simp only [zsub_int, zadd_int] at hc'
      exact Int.le_of_eq hc'
  have Hsum : Zle (Zadd (Zpos (digits2_pos mx)) ex) emax := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zadd (Zpos (digits2_pos mx)) ex) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emax
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zsub (Zadd (Zpos (digits2_pos mx)) ex) prec) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex at Hfirst
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub emax prec) at Hexp'
    simp only [zsub_int, zadd_int] at Hfirst Hexp' ⊢
    omega
  have hd := CompCert4Lean.Flocq.Core.Digits.digits2_Pnat_correct mx
  have hnat :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (digits2_pos mx) =
        Nat.succ (CompCert4Lean.Flocq.Core.Digits.digits2_Pnat mx) := by
    have hnat_aux : ∀ m : positive,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (digits2_pos m) =
          Nat.succ (CompCert4Lean.Flocq.Core.Digits.digits2_Pnat m) := by
      intro m
      induction m with
      | xH => rfl
      | xO p ih =>
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ
                (digits2_pos p)) =
            Nat.succ (Nat.succ (CompCert4Lean.Flocq.Core.Digits.digits2_Pnat p))
          rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.posToNat_succ]
          simp [CompCert4Lean.Flocq.Core.Digits.digits2_Pnat, ih]
      | xI p ih =>
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ
                (digits2_pos p)) =
            Nat.succ (Nat.succ (CompCert4Lean.Flocq.Core.Digits.digits2_Pnat p))
          rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.posToNat_succ]
          simp [CompCert4Lean.Flocq.Core.Digits.digits2_Pnat, ih]
    exact hnat_aux mx
  have Hmant : Zlt (Zpos mx)
      (Zpower (radix2 : Z) (Zpos (digits2_pos mx))) := by
    have hpow := CompCert4Lean.Flocq.Core.Zaux.Zpower_Zpower_nat radix2
      (Zpos (digits2_pos mx)) (by
        change (0 : Int) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zpos (digits2_pos mx))
        simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat])
    have hpow' := congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hpow
    have habs :
        CompCert4Lean.Flocq.Core.Zaux.Zabs_nat (Zpos (digits2_pos mx)) =
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (digits2_pos mx) := by
      unfold CompCert4Lean.Flocq.Core.Zaux.Zabs_nat
      change Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (Int.natAbs (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zpos (digits2_pos mx)))))) = _
      rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      change Int.toNat (Int.natAbs (Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (digits2_pos mx)))) = _
      rw [Int.natAbs_of_nonneg (by simp)]
      exact Int.toNat_natCast _
    have hdhi := hd.2
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos mx) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Flocq.Core.Zaux.Zpower_nat Ztwo
          (Nat.succ (CompCert4Lean.Flocq.Core.Digits.digits2_Pnat mx))) at hdhi
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos mx) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zpower (radix2 : Z) (Zpos (digits2_pos mx)))
    rw [hpow']
    rw [habs]
    rw [hnat]
    exact hdhi
  have hfloat := CompCert4Lean.Flocq.Core.Float_prop.F2R_lt ctx radix2 ex
      (Zpos mx) (Zpower (radix2 : Z) (Zpos (digits2_pos mx))) Hmant
  have hpow_real := CompCert4Lean.Flocq.Core.Raux.IZR_Zpower ctx radix2
      (Zpos (digits2_pos mx)) (by
        change (0 : Int) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zpos (digits2_pos mx))
        simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat])
  have hright : Exact.F2R ctx
      (Float radix2 (Zpower (radix2 : Z) (Zpos (digits2_pos mx))) ex) =
      Exact.bpow ctx radix2 (Zadd (Zpos (digits2_pos mx)) ex) := by
    change ctx.spec.mul
        (ctx.spec.ofZ (Zpower (radix2 : Z) (Zpos (digits2_pos mx))))
        (Exact.bpow ctx radix2 ex) = _
    rw [show ctx.spec.ofZ (Zpower (radix2 : Z) (Zpos (digits2_pos mx))) =
        Exact.bpow ctx radix2 (Zpos (digits2_pos mx)) by exact hpow_real]
    exact (CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx radix2
      (Zpos (digits2_pos mx)) ex).symm
  have hbound : Exact.Rlt ctx
      (Exact.F2R ctx (Float radix2 (Zpos mx) ex))
      (Exact.bpow ctx radix2 (Zadd (Zpos (digits2_pos mx)) ex)) := by
    calc
      Exact.Rlt ctx (Exact.F2R ctx (Float radix2 (Zpos mx) ex))
          (Exact.F2R ctx
            (Float radix2 (Zpower (radix2 : Z) (Zpos (digits2_pos mx))) ex)) :=
        hfloat
      _ = _ := hright
  have hpow_one_le : ∀ d : Z, Zle Z0 d →
      Exact.Rle ctx (Exact.IZR ctx Zone) (Exact.bpow ctx radix2 d) := by
    intro d hd
    cases d with
    | Z0 =>
        change CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle ctx.spec
          (CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR ctx.spec Zone)
          (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx radix2 Z0)
        change ctx.spec.le (ctx.spec.ofZ Zone) (ctx.spec.one)
        rw [ctx.certificate.sourceLaws.ofZ_one]
        exact ctx.certificate.orderedField.le_refl _
    | Zneg p =>
        change (0 : Int) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zneg p) at hd
        simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at hd
        have hp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
        omega
    | Zpos p =>
        change CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle ctx.spec
          (CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR ctx.spec Zone)
          (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx radix2 (Zpos p))
        change ctx.spec.le (ctx.spec.ofZ Zone)
          (ctx.spec.ofZ
            (CompCert4Lean.Flocq.Core.Zaux.Zpower_pos radix2.radix_val p))
        have hpow_nat : ∀ n : Nat, (1 : Int) ≤ (2 : Int) ^ n := by
          intro n
          induction n with
          | zero => simp
          | succ n ih =>
              rw [Int.pow_succ]
              have hmul := Int.mul_le_mul_of_nonneg_right ih (by omega : (0 : Int) ≤ 2)
              omega
        have hp : (1 : Int) ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Flocq.Core.Zaux.Zpower_pos radix2.radix_val p) := by
          simp only [CompCert4Lean.Flocq.Core.Zaux.Zpower_pos,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow_pos,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          exact hpow_nat _
        have hp' := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_le
          ctx Zone (CompCert4Lean.Flocq.Core.Zaux.Zpower_pos radix2.radix_val p) hp
        change ctx.spec.le (ctx.spec.ofZ Zone)
          (ctx.spec.ofZ
            (CompCert4Lean.Flocq.Core.Zaux.Zpower_pos radix2.radix_val p)) at hp'
        exact hp'
  have hbpow_le : ∀ a b : Z, Zle a b →
      CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle ctx.spec
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx radix2 a)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx radix2 b) := by
    intro a b hab
    let d := Zsub b a
    have hd : Zle Z0 d := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d
      simp only [d, zsub_int]
      change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b -
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b at hab
      omega
    have hsum : Zadd a d = b := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp only [d, zadd_int, zsub_int,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a +
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b -
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b
      omega
    have hmul := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
      ctx (Exact.bpow ctx radix2 a) (ctx.spec.one) (Exact.bpow ctx radix2 d)
      (by
        have hnonneg := CompCert4Lean.Flocq.Core.Raux.bpow_ge_0 ctx radix2 a
        have hzero :
            CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR ctx.spec Z0 =
              CompCert4Lean.Foundation.FlocqReal.ExactReal.R0 ctx.spec := by
          exact ctx.certificate.sourceLaws.ofZ_zero
        have hnonneg' : CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle ctx.spec
            (CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR ctx.spec Z0)
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx radix2 a) := by
          rw [hzero]
          exact hnonneg
        exact hnonneg')
      (by
        have hone := hpow_one_le d hd
        change CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle ctx.spec
          (CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR ctx.spec Zone)
          (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx radix2 d) at hone
        change ctx.spec.le (ctx.spec.ofZ Zone)
          (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx radix2 d) at hone
        rw [ctx.certificate.sourceLaws.ofZ_one] at hone
        change CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle ctx.spec
          ctx.spec.one (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx radix2 d)
        exact hone)
    have hdecomp : Exact.bpow ctx radix2 b =
        ctx.spec.mul (Exact.bpow ctx radix2 a) (Exact.bpow ctx radix2 d) := by
      rw [← hsum]
      exact CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx radix2 a d
    have hmul_spec : CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle ctx.spec
      (ctx.spec.mul ctx.spec.one (Exact.bpow ctx radix2 a))
      (ctx.spec.mul (Exact.bpow ctx radix2 d) (Exact.bpow ctx radix2 a)) := by
      change ctx.spec.le
        (ctx.spec.mul ctx.spec.one (Exact.bpow ctx radix2 a))
        (ctx.spec.mul (Exact.bpow ctx radix2 d) (Exact.bpow ctx radix2 a)) at hmul
      exact hmul
    rw [ctx.certificate.orderedField.mul_comm ctx.spec.one _,
      ctx.certificate.orderedField.mul_comm (Exact.bpow ctx radix2 d) _] at hmul_spec
    rw [ctx.certificate.orderedField.mul_one] at hmul_spec
    have hmul_bound : CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle ctx.spec
        (Exact.bpow ctx radix2 a)
        (Exact.bpow ctx radix2 b) := by
      rw [hdecomp]
      exact hmul_spec
    exact hmul_bound
  have hpow_bound := hbpow_le (Zadd (Zpos (digits2_pos mx)) ex) emax Hsum
  exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
    ctx _ _ _ hbound hpow_bound

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

private theorem pg_abs_cond_Zopp_pos (s : Bool) (m : positive) :
    Zabs (cond_Zopp s (Zpos m)) = Zpos m := by
  cases s with
  | false =>
      change Zabs (Zpos m) = Zpos m
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
            (Zpos m)) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos m)
      unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
      rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
  | true =>
      change Zabs (Zopp (Zpos m)) = Zpos m
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
            (Zopp (Zpos m))) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos m)
      have hmopp :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zopp (Zpos m)) =
            -CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos m) := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
              (-CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos m))) = _
        rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
      rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      rw [hmopp]
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
      rw [Int.natAbs_neg]
      rfl

theorem abs_B2R_lt_emax :
    ∀ {prec emax : Z} (ctx : ExactRealContext),
      abs_B2R_lt_emaxStatement (prec := prec) (emax := emax) ctx := by
  intro prec emax ctx x Hx
  have hzero : Exact.Rlt ctx (Exact.Rabs ctx (Exact.R0 ctx))
      (Exact.bpow ctx radix2 emax) := by
    have habs : Exact.Rabs ctx (Exact.R0 ctx) = Exact.R0 ctx := by
      change ctx.spec.abs ctx.spec.zero = ctx.spec.zero
      exact ctx.certificate.sourceLaws.abs_nonnegative ctx.spec.zero
        (ctx.certificate.orderedField.le_refl _)
    rw [habs]
    exact CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx radix2 emax
  cases x with
  | B754_nan => simpa [Exact.B2R] using hzero
  | B754_infinity s => simpa [Exact.B2R] using hzero
  | B754_zero s => simpa [Exact.B2R] using hzero
  | B754_finite s m e =>
      have hb : bounded (prec := prec) (emax := emax) m e = true := by
        change valid_binary0 prec emax (S754_finite s m e) = true at Hx
        change bounded0 prec emax m e = true at Hx
        exact Hx
      have hlt := bounded_lt_emax (prec := prec) (emax := emax) ctx m e hb
      have hz := pg_abs_cond_Zopp_pos s m
      have hF := CompCert4Lean.Flocq.Core.Float_prop.F2R_Zabs ctx radix2
        (cond_Zopp s (Zpos m)) e
      have hrabs : Exact.Rabs ctx
          (Exact.F2R ctx (Float radix2 (cond_Zopp s (Zpos m)) e)) =
          Exact.F2R ctx (Float radix2 (Zabs (cond_Zopp s (Zpos m))) e) := by
        change CompCert4Lean.Flocq.Core.Float_prop.Exact.Rabs ctx
            (CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
              (CompCert4Lean.Flocq.Core.Float_prop.Float radix2
                (cond_Zopp s (Zpos m)) e)) =
          CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
            (CompCert4Lean.Flocq.Core.Float_prop.Float radix2
              (Zabs (cond_Zopp s (Zpos m))) e)
        exact hF.symm
      change Exact.Rlt ctx
        (Exact.Rabs ctx
          (Exact.F2R ctx (Float radix2 (cond_Zopp s (Zpos m)) e)))
        (Exact.bpow ctx radix2 emax)
      rw [hrabs, hz]
      exact hlt

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

theorem shr_m_shr_record_of_loc :
    shr_m_shr_record_of_locStatement := by
  intro m l
  cases l with
  | loc_Exact => rfl
  | loc_Inexact c => cases c <;> rfl

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

private theorem pg_iter_nat_comp {α : Type} (f : α → α) (n : Nat) (x : α) :
    CompCert4Lean.Flocq.Core.Zaux.iter_nat f n (f x) =
      f (CompCert4Lean.Flocq.Core.Zaux.iter_nat f n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      simp [CompCert4Lean.Flocq.Core.Zaux.iter_nat, ih]

private theorem pg_iter_nat_add {α : Type} (f : α → α) (p q : Nat) (x : α) :
    CompCert4Lean.Flocq.Core.Zaux.iter_nat f (p + q) x =
      CompCert4Lean.Flocq.Core.Zaux.iter_nat f p
        (CompCert4Lean.Flocq.Core.Zaux.iter_nat f q x) := by
  induction p with
  | zero => simp [CompCert4Lean.Flocq.Core.Zaux.iter_nat]
  | succ p ih =>
      simp [Nat.succ_add, CompCert4Lean.Flocq.Core.Zaux.iter_nat, ih,
        pg_iter_nat_comp]

private theorem pg_iter_pos_nat {α : Type} (f : α → α) (p : positive) (x : α) :
    Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.iter_pos f p x =
      CompCert4Lean.Flocq.Core.Zaux.iter_nat f
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p) x := by
  induction p generalizing x with
  | xH => rfl
  | xI p ih =>
      simp only [Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.iter_pos,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
      rw [ih, ih]
      have hadd := (pg_iter_nat_add f
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p)
        (f x)).symm
      rw [hadd]
      have hcount :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p +
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p =
            2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p := by
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat]
        omega
      rw [hcount]
      rfl
  | xO p ih =>
      simp only [Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.iter_pos,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
      rw [ih, ih]
      have hadd := (pg_iter_nat_add f
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p)
        x).symm
      rw [hadd]
      have hcount :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p +
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p =
            2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p := by
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat]
        omega
      rw [hcount]

theorem shr_nat :
    shr_natStatement := by
  intro mrs e n hn
  cases n with
  | Z0 =>
      simp [Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shr,
        CompCert4Lean.Flocq.Core.Zaux.iter_nat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat,
        Zadd,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add_0_r]
      constructor
      · rfl
      · exact (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add_0_r e).symm
  | Zpos p =>
      change shr mrs e (Zpos p) =
        (CompCert4Lean.Flocq.Core.Zaux.iter_nat shr_1
          (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat
            (Zpos p)) mrs,
          Zadd e (Zpos p))
      simp only [Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shr]
      have hnat :
          _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat
              (Zpos p) =
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p := by
        rfl
      rw [hnat]
      rw [pg_iter_pos_nat]
  | Zneg p =>
      exfalso
      change 0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zneg p) at hn
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at hn
      have hp :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hp' : 0 < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) := by
        exact Int.natCast_pos.mpr hp
      omega

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

theorem le_shr1_le :
    le_shr1_leStatement := by
  intro mrs hm
  cases mrs with
  | mk m r s =>
      cases m with
      | Z0 =>
          refine ⟨?_, ?_, ?_⟩
          · exact shr1_nonneg _ hm
          · change (0 : Int) ≤ 0
            omega
          · change (0 : Int) < 2
            omega
      | Zneg p =>
          exfalso
          have hp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
          change (0 : Int) ≤ -Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hm
          have hp' : (0 : Int) < Int.ofNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) := by
            exact Int.ofNat_lt.mpr hp
          omega
      | Zpos p =>
          cases p with
          | xH =>
              refine ⟨?_, ?_, ?_⟩
              · exact shr1_nonneg _ hm
              · change (0 : Int) ≤ 1
                omega
              · change (1 : Int) < 2
                omega
          | xO p =>
              refine ⟨?_, ?_, ?_⟩
              · exact shr1_nonneg _ hm
              · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                    (Zmul Ztwo (Zpos p)) ≤
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p.xO)
                simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
                have htwo :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = (2 : Int) := by
                  rfl
                have hpx :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p.xO) =
                      Int.ofNat 2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) := by
                  change Int.ofNat
                      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p.xO) =
                    Int.ofNat 2 * Int.ofNat
                      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
                  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat,
                    Int.ofNat_eq_natCast, Int.natCast_mul]
                have hpx' :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p.xO) =
                      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo *
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) := by
                  calc
                    _ = Int.ofNat 2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) := hpx
                    _ = _ := by
                      rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = Int.ofNat 2 by rfl]
                rw [hpx']
                exact Int.le_refl _
              · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p.xO) <
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                    (Zmul Ztwo (Zadd (Zpos p) Zone))
                simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
                have htwo :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = (2 : Int) := by
                  rfl
                have hzone :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by
                  rfl
                have hpx :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p.xO) =
                      Int.ofNat 2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) := by
                  change Int.ofNat
                      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p.xO) =
                    Int.ofNat 2 * Int.ofNat
                      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
                  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat,
                    Int.ofNat_eq_natCast, Int.natCast_mul]
                have hpx' :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p.xO) =
                      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo *
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) := by
                  calc
                    _ = Int.ofNat 2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) := hpx
                    _ = _ := by
                      rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = Int.ofNat 2 by rfl]
                have hpos : (0 : Int) <
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo := by
                  rw [htwo]
                  exact Int.natCast_pos.mpr (by decide)
                have hstep :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) <
                      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) +
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone := by
                  rw [hzone]
                  exact (Int.add_one_le_iff).mp (Int.le_refl _)
                rw [hpx']
                exact Int.mul_lt_mul_of_pos_left hstep hpos
          | xI p =>
              refine ⟨?_, ?_, ?_⟩
              · exact shr1_nonneg _ hm
              · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                    (Zmul Ztwo (Zpos p)) ≤
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p.xI)
                simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
                have htwo :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = (2 : Int) := by
                  rfl
                have hzone :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by
                  rfl
                have hpx :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p.xI) =
                      Int.ofNat 2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) + Int.ofNat 1 := by
                  change Int.ofNat
                      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p.xI) =
                    Int.ofNat 2 * Int.ofNat
                      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) + Int.ofNat 1
                  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat,
                    Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_add]
                have hpx' :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p.xI) =
                      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo *
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) +
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone := by
                  calc
                    _ = Int.ofNat 2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) + Int.ofNat 1 := hpx
                    _ = _ := by
                      rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = Int.ofNat 2 by rfl,
                        show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = Int.ofNat 1 by rfl]
                have hnonneg :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo *
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) ≤
                      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo *
                          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) +
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone := by
                  rw [hzone]
                  exact Int.le_of_lt ((Int.add_one_le_iff).mp (Int.le_refl _))
                rw [hpx']
                exact hnonneg
              · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p.xI) <
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                    (Zmul Ztwo (Zadd (Zpos p) Zone))
                simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
                have htwo :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = (2 : Int) := by
                  rfl
                have hzone :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by
                  rfl
                have hpx :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p.xI) =
                      Int.ofNat 2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) + Int.ofNat 1 := by
                  change Int.ofNat
                      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p.xI) =
                    Int.ofNat 2 * Int.ofNat
                      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) + Int.ofNat 1
                  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat,
                    Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_add]
                have hpx' :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p.xI) =
                      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo *
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) +
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone := by
                  calc
                    _ = Int.ofNat 2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) + Int.ofNat 1 := hpx
                    _ = _ := by
                      rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = Int.ofNat 2 by rfl,
                        show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = Int.ofNat 1 by rfl]
                have htarget :
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo *
                          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) +
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone <
                      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo *
                        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) +
                          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone) := by
                  rw [htwo, hzone]
                  omega
                rw [hpx']
                exact htarget

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

theorem is_nan_binary_overflow :
    ∀ {prec emax : Z},
      is_nan_binary_overflowStatement (prec := prec) (emax := emax) := by
  intro prec emax m s
  exact binary_overflow_not_nan m s

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

theorem binary_overflow_correct :
    ∀ {prec emax : Z} [Core.FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax],
      binary_overflow_correctStatement (prec := prec) (emax := emax) := by
  intro prec emax hp he m s
  unfold binary_overflow
  split
  · rfl
  · change (canonical_mantissa0 prec emax
        (Zto_pos (Zsub (Zpower (Zpos (.xO .xH)) prec) Zone))
        (Zsub emax prec) &&
      Zle_bool (Zsub emax prec) (Zsub emax prec)) = true
    apply Bool.and_eq_true_iff.mpr
    constructor
    · have hp0 : Zlt Z0 prec := Core.FLX.prec_gt_0 prec
      have hpow_gt : Zlt Zone (Zpower radix2 prec) :=
        Core.Zaux.Zpower_gt_1 radix2 prec hp0
      have hzone :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by
        rfl
      have hxpos : Zlt Z0 (Zsub (Zpower radix2 prec) Zone) := by
        change (0 : Int) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zsub (Zpower radix2 prec) Zone)
        simp only [Zsub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        rw [hzone]
        change (1 : Int) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zpower radix2 prec) at hpow_gt
        omega
      have zto_pos_id (x : Z) (hx : Zlt Z0 x) : Zpos (Zto_pos x) = x := by
        cases x with
        | Z0 =>
            change (0 : Int) < 0 at hx
            omega
        | Zpos p =>
            apply congrArg Zpos
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat
                (Int.toNat (Int.ofNat
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p))) = p
            rw [show Int.toNat (Int.ofNat
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p)) =
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p by
                cases p <;> rfl]
            exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.Pnat.Pos2Nat.id p
        | Zneg p =>
            change (0 : Int) < -Int.ofNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hx
            have hp' := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
            have hp'' : (0 : Int) < Int.ofNat
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
              Int.natCast_pos.mpr hp'
            omega
      have zabs_of_pos (x : Z) (hx : Zlt Z0 x) : Zabs x = x := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs x) =
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x
        unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
        rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        exact Int.natAbs_of_nonneg (Int.le_of_lt hx)
      have hprec_nonneg : Zle Z0 prec := by
        exact Int.le_of_lt hp0
      have hpred_lt : Zlt (Zsub prec Zone) prec := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zsub prec Zone) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec
        simp only [Zsub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        rw [hzone]
        omega
      have hpowers :
          Zlt (Zpower radix2 (Zsub prec Zone)) (Zpower radix2 prec) :=
        Core.Zaux.Zpower_lt radix2 (Zsub prec Zone) prec hprec_nonneg hpred_lt
      have hpow_le :
          Zle (Zpower radix2 (Zsub prec Zone))
            (Zsub (Zpower radix2 prec) Zone) := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zpower radix2 (Zsub prec Zone)) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zsub (Zpower radix2 prec) Zone)
        simp only [Zsub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        rw [hzone]
        exact Int.le_sub_one_of_lt hpowers
      have hdigit_lower0 := Core.Digits.Zdigits_gt_Zpower radix2
        (Zsub prec Zone) (Zsub (Zpower radix2 prec) Zone)
        (by simpa [zabs_of_pos _ hxpos] using hpow_le)
      have hdigit_lower :
          Zle prec (Zdigits radix2 (Zsub (Zpower radix2 prec) Zone)) := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zdigits radix2 (Zsub (Zpower radix2 prec) Zone))
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zsub prec Zone) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zdigits radix2 (Zsub (Zpower radix2 prec) Zone)) at hdigit_lower0
        have hsub_prec :
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub prec Zone) =
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec - 1 := by
          simp only [Zsub,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          rw [hzone]
        rw [hsub_prec] at hdigit_lower0
        omega
      have habs_lt :
          Zlt (Zabs (Zsub (Zpower radix2 prec) Zone)) (Zpower radix2 prec) := by
        rw [zabs_of_pos _ hxpos]
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zsub (Zpower radix2 prec) Zone) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpower radix2 prec)
        simp only [Zsub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        rw [hzone]
        omega
      have hdigit_upper := Core.Digits.Zdigits_le_Zpower radix2 prec
        (Zsub (Zpower radix2 prec) Zone) habs_lt
      have hdigit :
          Zdigits radix2 (Zsub (Zpower radix2 prec) Zone) = prec := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        apply Int.le_antisymm hdigit_upper hdigit_lower
      have hto_pos :
          Zpos (Zto_pos (Zsub (Zpower radix2 prec) Zone)) =
            Zsub (Zpower radix2 prec) Zone :=
        zto_pos_id _ hxpos
      have hdigits_to_pos :
          Zpos (digits2_pos (Zto_pos (Zsub (Zpower radix2 prec) Zone))) = prec := by
        calc
          _ = Zdigits radix2
                (Zpos (Zto_pos (Zsub (Zpower radix2 prec) Zone))) :=
            Core.Digits.Zpos_digits2_pos _
          _ = Zdigits radix2 (Zsub (Zpower radix2 prec) Zone) := by rw [hto_pos]
          _ = prec := hdigit
      have hadd : Zadd prec (Zsub emax prec) = emax := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [Zadd, Zsub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        omega
      change Zeq_bool
        (fexp (prec := prec) (emax := emax)
          (Zadd
            (Zpos (digits2_pos (Zto_pos (Zsub (Zpower radix2 prec) Zone))))
            (Zsub emax prec)))
        (Zsub emax prec) = true
      rw [hdigits_to_pos, hadd, fexp_emax]
      exact Core.Zaux.Zeq_bool_true _ _ rfl
    · exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zle_bool_refl_proof _

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

private theorem pg_fit_zadd_int (a b : Z) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd a b) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a +
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a +
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b)) = _
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]

private theorem pg_fit_zsub_int (a b : Z) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub a b) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a -
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a -
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b)) = _
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]

private theorem pg_fit_bpow_le (ctx : ExactRealContext) (a b : Z)
    (hab : Zle a b) :
    Exact.Rle ctx (Exact.bpow ctx radix2 a) (Exact.bpow ctx radix2 b) := by
  have hpow_one_le : ∀ d : Z, Zle Z0 d →
      Exact.Rle ctx (Exact.IZR ctx Zone) (Exact.bpow ctx radix2 d) := by
    intro d hd
    cases d with
    | Z0 =>
        change ctx.spec.le (ctx.spec.ofZ Zone) ctx.spec.one
        rw [ctx.certificate.sourceLaws.ofZ_one]
        exact ctx.certificate.orderedField.le_refl _
    | Zneg p =>
        change (0 : Int) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zneg p) at hd
        simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at hd
        have hp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
        omega
    | Zpos p =>
        change ctx.spec.le (ctx.spec.ofZ Zone)
          (ctx.spec.ofZ (Core.Zaux.Zpower_pos radix2.radix_val p))
        have hpow_nat : ∀ n : Nat, (1 : Int) ≤ (2 : Int) ^ n := by
          intro n
          induction n with
          | zero => simp
          | succ n ih =>
              rw [Int.pow_succ]
              have hmul := Int.mul_le_mul_of_nonneg_right ih
                (by omega : (0 : Int) ≤ 2)
              omega
        have hp : (1 : Int) ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Core.Zaux.Zpower_pos radix2.radix_val p) := by
          simp only [Core.Zaux.Zpower_pos,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow_pos,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          exact hpow_nat _
        exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_le
          ctx Zone (Core.Zaux.Zpower_pos radix2.radix_val p) hp
  let d := Zsub b a
  have hd : Zle Z0 d := by
    change (0 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d
    simp only [d, pg_fit_zsub_int]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b at hab
    omega
  have hsum : Zadd a d = b := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [d, pg_fit_zadd_int, pg_fit_zsub_int]
    omega
  have hmul :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
      ctx (Exact.bpow ctx radix2 a) ctx.spec.one (Exact.bpow ctx radix2 d)
      (by
        have hnonneg := Core.Raux.bpow_ge_0 ctx radix2 a
        have hzero :
            CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR ctx.spec Z0 =
              CompCert4Lean.Foundation.FlocqReal.ExactReal.R0 ctx.spec :=
          ctx.certificate.sourceLaws.ofZ_zero
        rw [hzero]
        exact hnonneg)
      (by
        have hone := hpow_one_le d hd
        change ctx.spec.le (ctx.spec.ofZ Zone) (Exact.bpow ctx radix2 d) at hone
        rw [ctx.certificate.sourceLaws.ofZ_one] at hone
        exact hone)
  have hdecomp : Exact.bpow ctx radix2 b =
      ctx.spec.mul (Exact.bpow ctx radix2 a) (Exact.bpow ctx radix2 d) := by
    rw [← hsum]
    exact Core.Raux.bpow_plus ctx radix2 a d
  have hmul_spec : ctx.spec.le
      (ctx.spec.mul ctx.spec.one (Exact.bpow ctx radix2 a))
      (ctx.spec.mul (Exact.bpow ctx radix2 d) (Exact.bpow ctx radix2 a)) := by
    exact hmul
  rw [ctx.certificate.orderedField.mul_comm ctx.spec.one _,
    ctx.certificate.orderedField.mul_comm (Exact.bpow ctx radix2 d) _]
      at hmul_spec
  rw [ctx.certificate.orderedField.mul_one] at hmul_spec
  rw [hdecomp]
  exact hmul_spec

theorem binary_fit_aux_correct :
    ∀ {prec emax : Z} (ctx : ExactRealContext)
      [Core.FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax],
      binary_fit_aux_correctStatement (prec := prec) (emax := emax) ctx := by
  intro prec emax ctx _ _
  unfold binary_fit_aux_correctStatement
  intro m sx mx ex hcan
  dsimp only
  unfold binary_fit_aux
  by_cases he : Zle_bool ex (Zsub emax prec) = true
  · rw [he]
    constructor
    · change bounded (prec := prec) (emax := emax) mx ex = true
      exact Bool.and_eq_true_iff.mpr ⟨hcan, he⟩
    · have hb : bounded (prec := prec) (emax := emax) mx ex = true :=
        Bool.and_eq_true_iff.mpr ⟨hcan, he⟩
      have hlt := bounded_lt_emax (prec := prec) (emax := emax) ctx mx ex hb
      have hnonneg : Exact.Rle ctx (Exact.R0 ctx)
          (Exact.F2R ctx (Float radix2 (Zpos mx) ex)) :=
        Core.Float_prop.F2R_ge_0 ctx radix2 (Float radix2 (Zpos mx) ex)
          (by
            change Zle Z0 (Zpos mx)
            exact zle_zero_zpos mx)
      have habs_pos : Exact.Rabs ctx
          (Exact.F2R ctx (Float radix2 (Zpos mx) ex)) =
          Exact.F2R ctx (Float radix2 (Zpos mx) ex) := by
        change ctx.spec.abs _ = _
        apply ctx.certificate.sourceLaws.abs_nonnegative
        change ctx.spec.le ctx.spec.zero _ at hnonneg
        exact hnonneg
      have hcond_abs : Exact.Rabs ctx
          (Exact.F2R ctx (Float radix2 (cond_Zopp sx (Zpos mx)) ex)) =
          Exact.Rabs ctx (Exact.F2R ctx (Float radix2 (Zpos mx) ex)) := by
        calc
          _ = Exact.F2R ctx
              (Float radix2 (Zabs (cond_Zopp sx (Zpos mx))) ex) :=
            (Core.Float_prop.F2R_Zabs ctx radix2
              (cond_Zopp sx (Zpos mx)) ex).symm
          _ = Exact.F2R ctx (Float radix2 (Zpos mx) ex) := by
            rw [pg_abs_cond_Zopp_pos]
          _ = _ := habs_pos.symm
      have htest : Exact.Rlt_bool ctx
          (Exact.F2R ctx (Float radix2 (Zpos mx) ex))
          (Exact.bpow ctx radix2 emax) = true :=
        Core.Raux.Rlt_bool_true ctx _ _ hlt
      simp only [Exact.SF2R, hcond_abs, habs_pos]
      rw [htest]
      exact ⟨rfl, rfl, rfl⟩
  · have hefalse : Zle_bool ex (Zsub emax prec) = false := by
      cases h : Zle_bool ex (Zsub emax prec) <;> simp_all
    rw [hefalse]
    constructor
    · exact binary_overflow_correct (prec := prec) (emax := emax) m sx
    · have hex_not_le : ¬
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Zsub emax prec) := by
        change (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub emax prec)
          then true else false) = false at hefalse
        simpa using hefalse
      have hcan_eq :
          fexp (prec := prec) (emax := emax)
              (Zadd (Zpos (digits2_pos mx)) ex) = ex := by
        have hc := hcan
        change Zeq_bool
          (fexp (prec := prec) (emax := emax)
            (Zadd (Zpos (digits2_pos mx)) ex)) ex = true at hc
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool]
          at hc
        simpa using hc
      have hdigit : Zpos (digits2_pos mx) = prec := by
        have hc := hcan_eq
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max
            (Zsub (Zadd (Zpos (digits2_pos mx)) ex) prec)
            (Zsub (Zsub (Zpos (.xI .xH)) emax) prec) = ex at hc
        have hp0 : (0 : Int) <
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec :=
          Core.FLX.prec_gt_0 prec
        have hpemax :
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emax :=
          prec_lt_emax
        have hthree :
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Zpos (.xI .xH)) = 3 := by
          rfl
        by_cases hmax :
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (Zsub (Zadd (Zpos (digits2_pos mx)) ex) prec) ≤
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (Zsub (Zsub (Zpos (.xI .xH)) emax) prec)
        · simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max,
            hmax] at hc
          have hci := congrArg
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hc
          simp only [pg_fit_zsub_int] at hci
          rw [hthree] at hci
          have hthreshold := hex_not_le
          rw [pg_fit_zsub_int] at hthreshold
          omega
        · simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max,
            hmax] at hc
          apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
          have hci := congrArg
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hc
          simp only [pg_fit_zsub_int, pg_fit_zadd_int] at hci
          omega
      let d := Zsub (Zpos (digits2_pos mx)) Zone
      have hd_nonneg : Zle Z0 d := by
        change (0 : Int) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d
        simp only [d, pg_fit_zsub_int]
        have hp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive
          (digits2_pos mx)
        rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = 1 by rfl]
        have hp' : (0 : Int) <
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Zpos (digits2_pos mx)) := by
          change (0 : Int) < Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (digits2_pos mx))
          exact Int.natCast_pos.mpr hp
        omega
      have hd_lt_digits : Zlt d (Zdigits radix2 (Zpos mx)) := by
        have hz := Core.Digits.Zpos_digits2_pos mx
        change Zpos (digits2_pos mx) = Zdigits radix2 (Zpos mx) at hz
        rw [← hz]
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zpos (digits2_pos mx))
        simp only [d, pg_fit_zsub_int]
        rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = 1 by rfl]
        omega
      have hpower_le := Core.Digits.Zpower_le_Zdigits radix2 d (Zpos mx)
        hd_lt_digits
      have habs_pos_z : Zabs (Zpos mx) = Zpos mx := by
        have hz := pg_abs_cond_Zopp_pos false mx
        change Zabs (Zpos mx) = Zpos mx at hz
        exact hz
      change Zle (Zpower (radix2 : Z) d) (Zabs (Zpos mx)) at hpower_le
      rw [habs_pos_z] at hpower_le
      have hfloat_le := Core.Float_prop.F2R_le ctx radix2
        (Zpower (radix2 : Z) d) (Zpos mx) ex hpower_le
      have hleft : Exact.F2R ctx
          (Float radix2 (Zpower (radix2 : Z) d) ex) =
          Exact.bpow ctx radix2 (Zadd d ex) := by
        change ctx.spec.mul (ctx.spec.ofZ (Zpower (radix2 : Z) d))
            (Exact.bpow ctx radix2 ex) = _
        rw [show ctx.spec.ofZ (Zpower (radix2 : Z) d) =
            Exact.bpow ctx radix2 d by
          exact Core.Raux.IZR_Zpower ctx radix2 d hd_nonneg]
        exact (Core.Raux.bpow_plus ctx radix2 d ex).symm
      change Exact.Rle ctx
          (Exact.F2R ctx (Float radix2 (Zpower (radix2 : Z) d) ex))
          (Exact.F2R ctx (Float radix2 (Zpos mx) ex)) at hfloat_le
      rw [hleft] at hfloat_le
      have hexponents : Zle emax (Zadd d ex) := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emax ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd d ex)
        simp only [d, pg_fit_zadd_int, pg_fit_zsub_int]
        have hdigit_i := congrArg
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hdigit
        have hthreshold := hex_not_le
        rw [pg_fit_zsub_int] at hthreshold
        rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = 1 by rfl]
        omega
      have hpow_le := pg_fit_bpow_le ctx emax (Zadd d ex) hexponents
      have hmantissa_le : Exact.Rle ctx (Exact.bpow ctx radix2 emax)
          (Exact.F2R ctx (Float radix2 (Zpos mx) ex)) :=
        ctx.certificate.orderedField.le_trans _ _ _ hpow_le hfloat_le
      have hnonneg : Exact.Rle ctx (Exact.R0 ctx)
          (Exact.F2R ctx (Float radix2 (Zpos mx) ex)) :=
        Core.Float_prop.F2R_ge_0 ctx radix2 (Float radix2 (Zpos mx) ex)
          (zle_zero_zpos mx)
      have habs_pos : Exact.Rabs ctx
          (Exact.F2R ctx (Float radix2 (Zpos mx) ex)) =
          Exact.F2R ctx (Float radix2 (Zpos mx) ex) := by
        change ctx.spec.abs _ = _
        apply ctx.certificate.sourceLaws.abs_nonnegative
        change ctx.spec.le ctx.spec.zero _ at hnonneg
        exact hnonneg
      have hcond_abs : Exact.Rabs ctx
          (Exact.F2R ctx (Float radix2 (cond_Zopp sx (Zpos mx)) ex)) =
          Exact.Rabs ctx (Exact.F2R ctx (Float radix2 (Zpos mx) ex)) := by
        calc
          _ = Exact.F2R ctx
              (Float radix2 (Zabs (cond_Zopp sx (Zpos mx))) ex) :=
            (Core.Float_prop.F2R_Zabs ctx radix2
              (cond_Zopp sx (Zpos mx)) ex).symm
          _ = Exact.F2R ctx (Float radix2 (Zpos mx) ex) := by
            rw [pg_abs_cond_Zopp_pos]
          _ = _ := habs_pos.symm
      have habs_le : Exact.Rle ctx (Exact.bpow ctx radix2 emax)
          (Exact.Rabs ctx
            (Exact.F2R ctx (Float radix2 (cond_Zopp sx (Zpos mx)) ex))) := by
        rw [hcond_abs, habs_pos]
        exact hmantissa_le
      have htest := Core.Raux.Rlt_bool_false ctx
        (Exact.Rabs ctx
          (Exact.F2R ctx (Float radix2 (cond_Zopp sx (Zpos mx)) ex)))
        (Exact.bpow ctx radix2 emax) habs_le
      have htest' : Exact.Rlt_bool ctx
          (Exact.Rabs ctx (Exact.SF2R ctx radix2 (S754_finite sx mx ex)))
          (Exact.bpow ctx radix2 emax) = false := by
        change Exact.Rlt_bool ctx
          (Exact.Rabs ctx
            (Exact.F2R ctx (Float radix2 (cond_Zopp sx (Zpos mx)) ex)))
          (Exact.bpow ctx radix2 emax) = false
        exact htest
      simp [htest']

private theorem pg_shift_pos (p x : positive) :
    Zpos (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpower.shift_pos p x) =
      Zmul (Zpos x)
        (Zpower (Zpos (.xO .xH)) (Zpos p)) := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpower.shift_pos,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.shiftl_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  have hpos : 0 <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat x *
        2 ^ CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p := by
    exact Nat.mul_pos
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive x)
      (Nat.pow_pos (by decide))
  rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (Zpos (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat x *
          2 ^ CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p))) =
      Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat x *
        2 ^ CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p) by
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ, hpos,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat hpos]]
  have hpcond : ¬
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) < 0 := by
    change ¬ (Int.ofNat
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) < 0)
    exact Int.not_lt_of_ge (Int.natCast_nonneg _)
  rw [if_neg hpcond]
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change Int.ofNat
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat x) *
        2 ^ CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p =
    Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat x) *
      Int.pow 2 (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p)
  rfl

theorem shl_align_correct' :
    ∀ (ctx : ExactRealContext), shl_align_correct'Statement ctx := by
  intro ctx mx ex e hle
  cases hz : Zsub e ex with
  | Z0 =>
      have hsub := congrArg
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hz
      simp only [Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hsub
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e -
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex = 0 at hsub
      have hle' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex := by
        exact hle
      have heq : e = ex := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        omega
      have hshl : shl_align mx ex e = (mx, ex) := by
        change (match Zsub e ex with
          | .Zneg d =>
              (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos d mx, e)
          | _ => (mx, ex)) = (mx, ex)
        rw [hz]
      rw [hshl]
      simp [heq]
  | Zpos p =>
      have hsub := congrArg
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hz
      simp only [Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hsub
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e -
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex =
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) at hsub
      have hp : 0 <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) := by
        change 0 < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
        exact Int.natCast_pos.mpr
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p)
      have hle' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex := by
        exact hle
      omega
  | Zneg p =>
      have hsub := congrArg
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hz
      simp only [Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hsub
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e -
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex =
            -CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) at hsub
      have hdiff : Zsub ex e = Zpos p := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [Zsub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex -
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e =
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p)
        omega
      have hshl : shl_align mx ex e =
          (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos p mx, e) := by
        change (match Zsub e ex with
          | .Zneg d =>
              (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos d mx, e)
          | _ => (mx, ex)) =
            (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos p mx, e)
        rw [hz]
      rw [hshl]
      constructor
      · rw [pg_shift_pos]
        have hchange := CompCert4Lean.Flocq.Core.Float_prop.F2R_change_exp
          ctx radix2 e (Zpos mx) ex hle
        rw [← hdiff]
        exact hchange.symm
      · rfl

theorem shl_align_correct :
    ∀ (ctx : ExactRealContext), shl_align_correctStatement ctx := by
  intro ctx mx ex e
  cases hz : Zsub e ex with
  | Z0 =>
      have hsub := congrArg
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hz
      simp only [Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hsub
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e -
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex = 0 at hsub
      have hle : Zle e ex := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex
        omega
      have hcorrect := shl_align_correct' ctx mx ex e hle
      have hshl : shl_align mx ex e = (mx, ex) := by
        change (match Zsub e ex with
          | .Zneg d =>
              (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos d mx, e)
          | _ => (mx, ex)) = (mx, ex)
        rw [hz]
      rw [hshl] at hcorrect ⊢
      constructor
      · rfl
      · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e
        omega
  | Zpos p =>
      have hsub := congrArg
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hz
      simp only [Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hsub
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e -
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex =
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) at hsub
      have hp : 0 <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) := by
        change 0 < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
        exact Int.natCast_pos.mpr
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p)
      have hshl : shl_align mx ex e = (mx, ex) := by
        change (match Zsub e ex with
          | .Zneg d =>
              (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos d mx, e)
          | _ => (mx, ex)) = (mx, ex)
        rw [hz]
      rw [hshl]
      constructor
      · rfl
      · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e
        omega
  | Zneg p =>
      have hsub := congrArg
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hz
      simp only [Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hsub
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e -
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex =
            -CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) at hsub
      have hp : 0 <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) := by
        change 0 < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
        exact Int.natCast_pos.mpr
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p)
      have hle : Zle e ex := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex
        omega
      have hcorrect := shl_align_correct' ctx mx ex e hle
      have hshl : shl_align mx ex e =
          (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos p mx, e) := by
        change (match Zsub e ex with
          | .Zneg d =>
              (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos d mx, e)
          | _ => (mx, ex)) =
            (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos p mx, e)
        rw [hz]
      rw [hshl] at hcorrect ⊢
      constructor
      · exact hcorrect.1.symm
      · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e
        omega

private theorem pg_shl_fexp_digits2_pos_nat (q : positive) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (digits2_pos q) =
      Nat.log2 (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q) + 1 := by
  have hsucc (r : positive) :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
          (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posSucc r) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat r + 1 := by
    induction r with
    | xH => rfl
    | xI r ih =>
        change 2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
            (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posSucc r) =
          2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat r + 1 + 1
        rw [ih]
        omega
    | xO r ih =>
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (.xI r) =
          2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat r + 1
        rfl
  induction q with
  | xH => decide
  | xO q ih =>
      rw [show digits2_pos (.xO q) =
            Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posSucc
              (digits2_pos q) by rfl,
        hsucc, ih]
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
      have hqne : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q ≠ 0 :=
        Nat.ne_of_gt
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive q)
      rw [Nat.log2_two_mul hqne]
  | xI q ih =>
      rw [show digits2_pos (.xI q) =
            Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posSucc
              (digits2_pos q) by rfl,
        hsucc, ih]
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
      let k := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q
      have hk : 0 < k :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive q
      have hlog : Nat.log2 (2 * k + 1) = Nat.log2 k + 1 := by
        apply (Nat.log2_eq_iff
          (Nat.ne_of_gt (by omega : 0 < 2 * k + 1))).2
        have hlow := Nat.log2_self_le (Nat.ne_of_gt hk)
        have hhigh := (Nat.log2_lt (Nat.ne_of_gt hk)).1
          (Nat.lt_succ_self (Nat.log2 k))
        constructor <;> rw [Nat.pow_succ] <;> omega
      change Nat.log2 k + 1 + 1 = Nat.log2 (2 * k + 1) + 1
      rw [hlog]

private theorem pg_shl_fexp_log2_mul_two_pow (k n : Nat) (hk : 0 < k) :
    Nat.log2 (k * 2 ^ n) = Nat.log2 k + n := by
  apply (Nat.log2_eq_iff
    (Nat.ne_of_gt (Nat.mul_pos hk (Nat.two_pow_pos n)))).2
  have hlow := Nat.log2_self_le (Nat.ne_of_gt hk)
  have hhigh := (Nat.log2_lt (Nat.ne_of_gt hk)).1
    (Nat.lt_succ_self (Nat.log2 k))
  constructor
  · rw [Nat.pow_add]
    exact Nat.mul_le_mul_right (2 ^ n) hlow
  · rw [show Nat.log2 k + n + 1 = (Nat.log2 k + 1) + n by omega,
      Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right hhigh (Nat.two_pow_pos n)

private theorem pg_shl_fexp_shift_digits (p x : positive) :
    Zdigits radix2
        (Zpos (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos p x)) =
      Zadd (Zdigits radix2 (Zpos x)) (Zpos p) := by
  change Core.Digits.Zdigits radix2
      (Zpos (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos p x)) =
    Zadd (Core.Digits.Zdigits radix2 (Zpos x)) (Zpos p)
  rw [← Core.Digits.Zpos_digits2_pos,
    ← Core.Digits.Zpos_digits2_pos]
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [Zadd,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change Int.ofNat
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
        (digits2_pos
          (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos p x))) =
    Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (digits2_pos x)) +
      Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
  rw [pg_shl_fexp_digits2_pos_nat, pg_shl_fexp_digits2_pos_nat]
  unfold Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpower.shift_pos
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.shiftl_nat
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat
    (Nat.mul_pos
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive x)
      (Nat.two_pow_pos _))]
  rw [pg_shl_fexp_log2_mul_two_pow _ _
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive x)]
  simp only [
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat,
    Int.ofNat_eq_coe, Int.natCast_add]
  omega

theorem shl_align_fexp_correct :
    ∀ {prec emax : Z} (ctx : ExactRealContext),
      shl_align_fexp_correctStatement (prec := prec) (emax := emax) ctx := by
  intro prec emax ctx mx ex
  unfold shl_align_fexp
  let e := fexp (prec := prec) (emax := emax)
    (Zadd (Zpos (digits2_pos mx)) ex)
  have hc := shl_align_correct ctx mx ex e
  have hdigit : Zdigits radix2 (Zpos mx) = Zpos (digits2_pos mx) := by
    change Core.Digits.Zdigits radix2 (Zpos mx) = Zpos (digits2_pos mx)
    exact (Core.Digits.Zpos_digits2_pos mx).symm
  cases hz : Zsub e ex with
  | Z0 =>
      have hs : shl_align mx ex e = (mx, ex) := by
        change (match Zsub e ex with
          | .Zneg d =>
              (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos d mx, e)
          | _ => (mx, ex)) = (mx, ex)
        rw [hz]
      rw [hs] at hc ⊢
      refine ⟨hc.1, ?_⟩
      rw [hdigit]
      exact hc.2
  | Zpos p =>
      have hs : shl_align mx ex e = (mx, ex) := by
        change (match Zsub e ex with
          | .Zneg d =>
              (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos d mx, e)
          | _ => (mx, ex)) = (mx, ex)
        rw [hz]
      rw [hs] at hc ⊢
      refine ⟨hc.1, ?_⟩
      rw [hdigit]
      exact hc.2
  | Zneg p =>
      have hs : shl_align mx ex e =
          (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos p mx, e) := by
        change (match Zsub e ex with
          | .Zneg d =>
              (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos d mx, e)
          | _ => (mx, ex)) =
            (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos p mx, e)
        rw [hz]
      rw [hs] at hc ⊢
      refine ⟨hc.1, ?_⟩
      have hsub := congrArg
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hz
      simp only [Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hsub
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e -
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex =
        -CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos p) at hsub
      have harg :
          Zadd
              (Zdigits radix2
                (Zpos
                  (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos p mx))) e =
            Zadd (Zpos (digits2_pos mx)) ex := by
        rw [pg_shl_fexp_shift_digits, hdigit]
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [Zadd,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        omega
      rw [harg]
      exact hc.2

theorem Fplus_naive_correct :
    ∀ (ctx : ExactRealContext), Fplus_naive_correctStatement ctx := by
  intro ctx sx mx ex sy my ey ez Hx Hy
  unfold Fplus_naive
  cases hmy : shl_align my ey ez with
  | mk my' ey' =>
    cases hmx : shl_align mx ex ez with
    | mk mx' ex' =>
      have hy := shl_align_correct' ctx my ey ez Hy
      have hx := shl_align_correct' ctx mx ex ez Hx
      simp only [hmx, hmy] at hy hx ⊢
      have hxs :
          Exact.F2R ctx (Float radix2 (cond_Zopp sx (Zpos mx')) ez) =
            Exact.F2R ctx (Float radix2 (cond_Zopp sx (Zpos mx)) ex) := by
        calc
          Exact.F2R ctx (Float radix2 (cond_Zopp sx (Zpos mx')) ez) =
              CompCert4Lean.Flocq.Core.Raux.Exact.cond_Ropp ctx sx
                (Exact.F2R ctx (Float radix2 (Zpos mx') ez)) :=
            CompCert4Lean.Flocq.Core.Float_prop.F2R_cond_Zopp
              ctx radix2 sx (Zpos mx') ez
          _ = CompCert4Lean.Flocq.Core.Raux.Exact.cond_Ropp ctx sx
                (Exact.F2R ctx (Float radix2 (Zpos mx) ex)) :=
            congrArg (fun t =>
              CompCert4Lean.Flocq.Core.Raux.Exact.cond_Ropp ctx sx t) hx.1
          _ = Exact.F2R ctx (Float radix2 (cond_Zopp sx (Zpos mx)) ex) :=
            (CompCert4Lean.Flocq.Core.Float_prop.F2R_cond_Zopp
              ctx radix2 sx (Zpos mx) ex).symm
      have hys :
          Exact.F2R ctx (Float radix2 (cond_Zopp sy (Zpos my')) ez) =
            Exact.F2R ctx (Float radix2 (cond_Zopp sy (Zpos my)) ey) := by
        calc
          Exact.F2R ctx (Float radix2 (cond_Zopp sy (Zpos my')) ez) =
              CompCert4Lean.Flocq.Core.Raux.Exact.cond_Ropp ctx sy
                (Exact.F2R ctx (Float radix2 (Zpos my') ez)) :=
            CompCert4Lean.Flocq.Core.Float_prop.F2R_cond_Zopp
              ctx radix2 sy (Zpos my') ez
          _ = CompCert4Lean.Flocq.Core.Raux.Exact.cond_Ropp ctx sy
                (Exact.F2R ctx (Float radix2 (Zpos my) ey)) :=
            congrArg (fun t =>
              CompCert4Lean.Flocq.Core.Raux.Exact.cond_Ropp ctx sy t) hy.1
          _ = Exact.F2R ctx (Float radix2 (cond_Zopp sy (Zpos my)) ey) :=
            (CompCert4Lean.Flocq.Core.Float_prop.F2R_cond_Zopp
              ctx radix2 sy (Zpos my) ey).symm
      have hsum (a b : Z) :
          Exact.F2R ctx (Float radix2 (Zadd a b) ez) =
            Exact.Rplus ctx
              (Exact.F2R ctx (Float radix2 a ez))
              (Exact.F2R ctx (Float radix2 b ez)) := by
        change ctx.spec.mul (ctx.spec.ofZ (Zadd a b))
            (Exact.bpow ctx radix2 ez) =
          ctx.spec.add
            (ctx.spec.mul (ctx.spec.ofZ a) (Exact.bpow ctx radix2 ez))
            (ctx.spec.mul (ctx.spec.ofZ b) (Exact.bpow ctx radix2 ez))
        rw [ctx.certificate.sourceLaws.ofZ_add]
        calc
          ctx.spec.mul
              (ctx.spec.add (ctx.spec.ofZ a) (ctx.spec.ofZ b))
              (Exact.bpow ctx radix2 ez) =
            ctx.spec.mul (Exact.bpow ctx radix2 ez)
              (ctx.spec.add (ctx.spec.ofZ a) (ctx.spec.ofZ b)) :=
            ctx.certificate.orderedField.mul_comm _ _
          _ = ctx.spec.add
              (ctx.spec.mul (Exact.bpow ctx radix2 ez) (ctx.spec.ofZ a))
              (ctx.spec.mul (Exact.bpow ctx radix2 ez) (ctx.spec.ofZ b)) :=
            ctx.certificate.orderedField.left_distrib _ _ _
          _ = ctx.spec.add
              (ctx.spec.mul (ctx.spec.ofZ a) (Exact.bpow ctx radix2 ez))
              (ctx.spec.mul (ctx.spec.ofZ b) (Exact.bpow ctx radix2 ez)) := by
            rw [ctx.certificate.orderedField.mul_comm
              (Exact.bpow ctx radix2 ez) (ctx.spec.ofZ a),
              ctx.certificate.orderedField.mul_comm
                (Exact.bpow ctx radix2 ez) (ctx.spec.ofZ b)]
      rw [hsum, hxs, hys]

theorem canonical_canonical_mantissa :
    ∀ {prec emax : Z} (ctx : ExactRealContext)
      (magnitude : Exact.Magnitude ctx),
      canonical_canonical_mantissaStatement (prec := prec) (emax := emax)
        ctx magnitude := by
  intro prec emax ctx magnitude sx mx ex H
  unfold Exact.canonical Exact.cexp Exact.mag
  change ex = (fexp (prec := prec) (emax := emax))
    (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude radix2
      (Exact.F2R ctx (Float radix2 (cond_Zopp sx (Zpos mx)) ex))).mag_val
  have hmant :
      (fexp (prec := prec) (emax := emax))
          (Zadd (Zpos (digits2_pos mx)) ex) = ex := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool
        ((fexp (prec := prec) (emax := emax))
          (Zadd (Zpos (digits2_pos mx)) ex)) ex = true at H
    exact (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool_eq _ _ H)
  have hm : cond_Zopp sx (Zpos mx) ≠ Z0 := by
    intro h
    have hz := pg_abs_cond_Zopp_pos sx mx
    rw [h] at hz
    have hz' := congrArg
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hz
    change (0 : Int) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos mx) at hz'
    have hp : (0 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos mx) := by
      change (0 : Int) < Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat mx)
      exact Int.natCast_pos.mpr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive mx)
    omega
  have hmag := CompCert4Lean.Flocq.Core.Float_prop.mag_F2R_Zdigits
    ctx magnitude radix2 (cond_Zopp sx (Zpos mx)) ex hm
  have habs :
      CompCert4Lean.Flocq.Core.Float_prop.Zdigits radix2
          (cond_Zopp sx (Zpos mx)) = Zpos (digits2_pos mx) := by
    change CompCert4Lean.Flocq.Core.Digits.Zdigits radix2
      (cond_Zopp sx (Zpos mx)) = Zpos (digits2_pos mx)
    rw [← CompCert4Lean.Flocq.Core.Digits.Zdigits_abs radix2
      (cond_Zopp sx (Zpos mx))]
    have hzabs :
        CompCert4Lean.Flocq.Core.Digits.Zabs (cond_Zopp sx (Zpos mx)) = Zpos mx := by
      exact pg_abs_cond_Zopp_pos sx mx
    rw [hzabs]
    exact (CompCert4Lean.Flocq.Core.Digits.Zpos_digits2_pos mx).symm
  change ex = (fexp (prec := prec) (emax := emax))
    ((CompCert4Lean.Flocq.Core.Float_prop.Exact.mag magnitude radix2
      (CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
        (CompCert4Lean.Flocq.Core.Float_prop.Float radix2
          (cond_Zopp sx (Zpos mx)) ex))))
  rw [hmag, habs]
  exact hmant.symm


theorem canonical_bounded :
    ∀ {prec emax : Z} (ctx : ExactRealContext)
      (magnitude : Exact.Magnitude ctx),
      canonical_boundedStatement (prec := prec) (emax := emax)
        ctx magnitude := by
  intro prec emax ctx magnitude sx mx ex h
  apply canonical_canonical_mantissa ctx magnitude sx mx ex
  exact (Bool.and_eq_true_iff.mp h).1

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

open CompCert4Lean.Flocq.Core

theorem generic_format_B2R :
    ∀ {prec emax : Z} (ctx : ExactRealContext)
      (magnitude : Exact.Magnitude ctx),
      generic_format_B2RStatement (prec := prec) (emax := emax)
        ctx magnitude := by
  intro prec emax ctx magnitude x Hx
  cases x with
  | B754_nan =>
      unfold Exact.generic_format
      change CompCert4Lean.Flocq.Core.Generic_fmt.Exact.generic_format
        ctx magnitude radix2 (fexp (prec := prec) (emax := emax))
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R0 ctx)
      exact CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_0
        ctx magnitude radix2 (fexp (prec := prec) (emax := emax))
  | B754_infinity s =>
      unfold Exact.generic_format
      change CompCert4Lean.Flocq.Core.Generic_fmt.Exact.generic_format
        ctx magnitude radix2 (fexp (prec := prec) (emax := emax))
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R0 ctx)
      exact CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_0
        ctx magnitude radix2 (fexp (prec := prec) (emax := emax))
  | B754_zero s =>
      unfold Exact.generic_format
      change CompCert4Lean.Flocq.Core.Generic_fmt.Exact.generic_format
        ctx magnitude radix2 (fexp (prec := prec) (emax := emax))
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R0 ctx)
      exact CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_0
        ctx magnitude radix2 (fexp (prec := prec) (emax := emax))
  | B754_finite s m e =>
      have hb : bounded (prec := prec) (emax := emax) m e = true := by
        change valid_binary0 prec emax (S754_finite s m e) = true at Hx
        change bounded0 prec emax m e = true at Hx
        exact Hx
      have hcanon := canonical_bounded (prec := prec) (emax := emax)
        ctx magnitude s m e hb
      unfold Exact.generic_format
      change CompCert4Lean.Flocq.Core.Generic_fmt.Exact.generic_format
        ctx magnitude radix2 (fexp (prec := prec) (emax := emax))
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx
            (Float radix2 (cond_Zopp s (Zpos m)) e))
      exact CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_canonical
        ctx magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Float radix2 (cond_Zopp s (Zpos m)) e) hcanon

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

theorem is_finite_SF2B :
    ∀ {prec emax : Z}, is_finite_SF2BStatement (prec := prec) (emax := emax) := by
  intro prec emax x Hx
  cases x <;> rfl

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

private theorem pg_int_pow_gt_one_local (a : Int) (ha : (2 : Int) ≤ a) :
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

private theorem pg_bpow_pos_gt_one_local (ctx : ExactRealContext) (r : radix)
    {e : Z} (he : Zlt Z0 e) :
    Exact.Rlt ctx (Exact.IZR ctx Zone) (Exact.bpow ctx r e) := by
  cases e with
  | Z0 =>
      change (0 : Int) < 0 at he
      omega
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
            (CompCert4Lean.Flocq.Core.Zaux.Zpower_pos r.radix_val p) := by
        simp only [CompCert4Lean.Flocq.Core.Zaux.Zpower_pos,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow_pos,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        exact pg_int_pow_gt_one_local _ (by
          have hr := r.radix_prop
          change (if (2 : Int) ≤
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val then true else false) = true at hr
          simpa using hr) _ hp
      have hzlt : Zlt Zone (CompCert4Lean.Flocq.Core.Zaux.Zpower_pos r.radix_val p) := by
        change (1 : Int) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Flocq.Core.Zaux.Zpower_pos r.radix_val p)
        exact hpow
      have h := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt
        ctx Zone (CompCert4Lean.Flocq.Core.Zaux.Zpower_pos r.radix_val p) hzlt
      change ctx.spec.lt (ctx.spec.ofZ Zone)
        (ctx.spec.ofZ (CompCert4Lean.Flocq.Core.Zaux.Zpower_pos r.radix_val p)) at h
      rw [ctx.certificate.sourceLaws.ofZ_one] at h
      change ctx.spec.lt (ctx.spec.ofZ Zone)
        (ctx.spec.ofZ (CompCert4Lean.Flocq.Core.Zaux.Zpower_pos r.radix_val p))
      rw [ctx.certificate.sourceLaws.ofZ_one]
      exact h

private theorem pg_zadd_sub_cancel_local (a b : Z) :
    Zadd a (Zsub b a) = b := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

private theorem pg_bpow_lt_local (ctx : ExactRealContext) (r : radix)
    {e1 e2 : Z} (h : Zlt e1 e2) :
    CompCert4Lean.Flocq.Core.Raux.Exact.Rlt ctx
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1)
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e2) := by
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
  have hsum : Zadd e1 d = e2 := pg_zadd_sub_cancel_local e1 e2
  have hmul : CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e2 =
      ctx.spec.mul
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r d) := by
    rw [← hsum]
    exact CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx r e1 d
  have hpos : CompCert4Lean.Flocq.Core.Raux.Exact.Rlt ctx
      ctx.spec.zero (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1) :=
    CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx r e1
  have hone : CompCert4Lean.Flocq.Core.Raux.Exact.Rlt ctx
      ctx.spec.one (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r d) := by
    have hh := pg_bpow_pos_gt_one_local ctx r hd
    change ctx.spec.lt (ctx.spec.ofZ Zone)
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r d) at hh
    rw [ctx.certificate.sourceLaws.ofZ_one] at hh
    exact hh
  have hpos' : CompCert4Lean.Flocq.Core.Raux.Exact.Rlt ctx
      (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx Z0)
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1) := by
    change ctx.spec.lt (ctx.spec.ofZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0))
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1)
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hpos
  have hmul' :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_compat_r
      ctx (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1)
      (ctx.spec.one) (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r d)
      hpos' hone
  change ctx.spec.lt
    (ctx.spec.mul ctx.spec.one
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1))
    (ctx.spec.mul
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r d)
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1)) at hmul'
  rw [ctx.certificate.orderedField.mul_comm (ctx.spec.one) _,
    ctx.certificate.orderedField.mul_one,
    ctx.certificate.orderedField.mul_comm _
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e1)] at hmul'
  rw [← hmul] at hmul'
  exact hmul'

private theorem pg_bpow_lt_imp_exp_lt_local (ctx : ExactRealContext) (r : radix)
    {a b : Z}
    (h : CompCert4Lean.Flocq.Core.Raux.Exact.Rlt ctx
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r a)
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r b)) :
    Zlt a b := by
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b
  by_cases hablt : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b
  · exact hablt
  · have hle : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a := by omega
    rcases Int.lt_or_eq_of_le hle with hba | heq
    · have hp := pg_bpow_lt_local ctx r (show Zlt b a by exact hba)
      exact (ctx.certificate.orderedField.lt_irrefl _
        (ctx.certificate.orderedField.lt_trans _ _ _ hp h)).elim
    · have hab : a = b := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        exact heq.symm
      subst b
      exact (ctx.certificate.orderedField.lt_irrefl _ h).elim

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

theorem bounded_canonical_lt_emax :
    ∀ {prec emax : Z} (ctx : ExactRealContext)
      (magnitude : Exact.Magnitude ctx) [Core.FLX.Prec_gt_0 prec]
      [Prec_lt_emax prec emax],
      bounded_canonical_lt_emaxStatement (prec := prec) (emax := emax) ctx magnitude := by
  intro prec emax ctx magnitude hp he mx ex Cx Bx
  have hmne : Zpos mx ≠ Z0 := by
    intro hm
    have hm' := congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hm
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos mx) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 at hm'
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at hm'
    have hp' := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive mx
    omega
  have hmxlt : Zlt (Zpos mx) (Zadd (Zpos mx) Zone) := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos mx) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd (Zpos mx) Zone)
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    have hp' := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive mx
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos mx) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos mx) + 1
    omega
  have hmxpos : Zlt Z0 (Zpos mx) := by
    change 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos mx)
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
    exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive mx
  have hupper := CompCert4Lean.Flocq.Core.Float_prop.F2R_lt ctx radix2 ex
    (Zpos mx) (Zadd (Zpos mx) Zone) hmxlt
  have hmag := CompCert4Lean.Flocq.Core.Float_prop.mag_F2R_bounds_Zdigits
    ctx magnitude radix2
    (CompCert4Lean.Flocq.Core.Defs.Exact.F2R ctx
      (CompCert4Lean.Flocq.Core.Defs.Float radix2 (Zpos mx) ex))
    (Zpos mx) ex hmxpos
    ⟨CompCert4Lean.Flocq.Core.Float_prop.F2R_le ctx radix2 (Zpos mx)
        (Zpos mx) ex (by
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos mx) ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos mx)
          omega), hupper⟩
  have hcanon : ex = fexp (prec := prec) (emax := emax)
      (Zadd (Zdigits radix2 (Zpos mx)) ex) := by
    have hc := Cx
    change ex = fexp (Exact.mag magnitude radix2
      (Exact.F2R ctx (Float radix2 (Zpos mx) ex))) at hc
    have hmag_local : Exact.mag magnitude radix2
        (Exact.F2R ctx (Float radix2 (Zpos mx) ex)) =
        Zadd (Zdigits radix2 (Zpos mx)) ex := by
      simpa [Exact.mag, Exact.F2R, Exact.IZR, Exact.Rmult, Exact.bpow,
        CompCert4Lean.Flocq.Core.Float_prop.Exact.mag,
        CompCert4Lean.Flocq.Core.Defs.Exact.F2R] using hmag
    rw [hmag_local] at hc
    exact hc
  have hcanmant : canonical_mantissa (prec := prec) (emax := emax) mx ex = true := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool
      (fexp0 prec emax (Zadd (Zpos (digits2_pos mx)) ex)) ex = true
    have hcanon' : fexp0 prec emax (Zadd (Zpos (digits2_pos mx)) ex) = ex := by
      simpa only [← CompCert4Lean.Flocq.Core.Digits.Zpos_digits2_pos mx] using hcanon.symm
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool, hcanon']
  let xcore := CompCert4Lean.Flocq.Core.Defs.Exact.F2R ctx
    (CompCert4Lean.Flocq.Core.Defs.Float radix2 (Zpos mx) ex)
  let mv := CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude radix2 xcore
  have hpos_core : CompCert4Lean.Flocq.Core.Raux.Exact.Rlt ctx
      ctx.spec.zero xcore := by
    exact CompCert4Lean.Flocq.Core.Float_prop.F2R_gt_0 ctx radix2
      (CompCert4Lean.Flocq.Core.Defs.Float radix2 (Zpos mx) ex) hmxpos
  have hxne : xcore ≠ CompCert4Lean.Flocq.Core.Raux.Exact.R0 ctx := by
    intro hx
    rw [hx] at hpos_core
    exact (ctx.certificate.orderedField.lt_irrefl _ hpos_core).elim
  have hmv := mv.mag_bound hxne
  have hlow_mag : CompCert4Lean.Flocq.Core.Raux.Exact.Rle ctx
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx radix2
        (Zsub mv.mag_val Zone)) xcore := by
    have habs_core : ctx.spec.abs xcore = xcore :=
      ctx.certificate.sourceLaws.abs_nonnegative xcore
        ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hpos_core).1
    have hlow := hmv.1
    change ctx.spec.le
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx radix2
        (Zsub mv.mag_val Zone)) (ctx.spec.abs xcore) at hlow
    rw [habs_core] at hlow
    exact hlow
  have Bx_core : CompCert4Lean.Flocq.Core.Raux.Exact.Rlt ctx xcore
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx radix2 emax) := by
    change ctx.spec.lt
      (ctx.spec.mul (ctx.spec.ofZ (Zpos mx))
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx radix2 ex))
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx radix2 emax)
    exact Bx
  have hpow_lt : CompCert4Lean.Flocq.Core.Raux.Exact.Rlt ctx
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx radix2
        (Zsub mv.mag_val Zone))
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx radix2 emax) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
      ctx _ _ _ hlow_mag Bx_core
  have hmag_exp : mv.mag_val = Zadd (Zdigits radix2 (Zpos mx)) ex := by
    simpa [mv, xcore, CompCert4Lean.Flocq.Core.Float_prop.Exact.mag] using hmag
  have hmag_exp' : mv.mag_val = Zadd (Zpos (digits2_pos mx)) ex := by
    simpa only [← CompCert4Lean.Flocq.Core.Digits.Zpos_digits2_pos mx] using hmag_exp
  have hpow_exp : Zlt (Zsub mv.mag_val Zone) emax :=
    pg_bpow_lt_imp_exp_lt_local ctx radix2 hpow_lt
  have hcanon_mv : ex = fexp (prec := prec) (emax := emax) mv.mag_val := by
    rw [hmag_exp]
    exact hcanon
  have hmax_eq :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max
          (Zsub mv.mag_val prec)
          (Zsub (Zsub (Zpos (.xI .xH)) emax) prec) = ex := by
    have hh := hcanon_mv.symm
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max
        (Zsub mv.mag_val prec)
        (Zsub (Zsub (Zpos (.xI .xH)) emax) prec) = ex at hh
    exact hh
  have hbound_exp : Zle ex (Zsub emax prec) := by
    rw [← hmax_eq]
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max_lub
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Zsub mv.mag_val prec) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub emax prec)
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ mv.mag_val -
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emax -
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec
      have hp' := Core.FLX.prec_gt_0 prec
      change 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec at hp'
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Zsub mv.mag_val Zone) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emax at hpow_exp
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hpow_exp
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ mv.mag_val - 1 <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emax at hpow_exp
      omega
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Zsub (Zsub (Zpos (.xI .xH)) emax) prec) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub emax prec)
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      change (3 : Int) - CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emax -
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emax -
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec
      have hp' := Core.FLX.prec_gt_0 prec
      have he' := he.prec_lt_emax
      change 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec at hp'
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emax at he'
      omega
  have hbound_exp' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub emax prec) := by
    exact hbound_exp
  exact Bool.and_eq_true_iff.mpr ⟨hcanmant, by
    change (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub emax prec) then true else false) = true
    simp [hbound_exp']
    ⟩

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

theorem loc_of_shr_record_of_loc :
    loc_of_shr_record_of_locStatement := by
  intro m l
  cases l with
  | loc_Exact => rfl
  | loc_Inexact c => cases c <;> rfl

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

open CompCert4Lean.Flocq.Core

open CompCert4Lean.Foundation.Numbers.Rocq.Coq in
private theorem pg_shr_one_divmod (mrs : shr_record)
    (hm : Zle Z0 (shr_m mrs)) :
    Raux.Zdiv (shr_m mrs) Ztwo = shr_m (shr_1 mrs) ∧
      ZArith.Zdiv.Zmod (shr_m mrs) Ztwo =
        (if shr_r (shr_1 mrs) then Zone else Z0) := by
  rcases mrs with ⟨m, r, s⟩
  cases m with
  | Z0 => exact ⟨rfl, rfl⟩
  | Zpos p =>
    cases p with
    | xH => exact ⟨rfl, rfl⟩
    | xI p =>
      constructor
      · apply intOfZ_injective
        change intOfZ (zOfInt ((Int.ofNat (2 * posToNat p + 1)) / 2)) =
          Int.ofNat (posToNat p)
        simp only [intOfZ_zOfInt, Int.ofNat_eq_natCast, Int.natCast_add,
          Int.natCast_mul]
        omega
      · apply intOfZ_injective
        change intOfZ (zOfInt ((Int.ofNat (2 * posToNat p + 1)) % 2)) = 1
        simp only [intOfZ_zOfInt, Int.ofNat_eq_natCast, Int.natCast_add,
          Int.natCast_mul]
        omega
    | xO p =>
      constructor
      · apply intOfZ_injective
        change intOfZ (zOfInt ((Int.ofNat (2 * posToNat p)) / 2)) =
          Int.ofNat (posToNat p)
        simp only [intOfZ_zOfInt, Int.ofNat_eq_natCast,
          Int.natCast_mul]
        omega
      · apply intOfZ_injective
        change intOfZ (zOfInt ((Int.ofNat (2 * posToNat p)) % 2)) = 0
        simp only [intOfZ_zOfInt, Int.ofNat_eq_natCast,
          Int.natCast_mul]
        omega
  | Zneg p =>
    change 0 ≤ -(Int.ofNat (posToNat p)) at hm
    have hp := posToNat_positive p
    simp only [Int.ofNat_eq_natCast] at hm
    omega

private theorem pg_shr_one_location (mrs : shr_record) :
    CompCert4Lean.Flocq.Calc.Bracket.new_location Ztwo
        (if shr_r (shr_1 mrs) then Zone else Z0) (loc_of_shr_record mrs) =
      loc_of_shr_record (shr_1 mrs) := by
  rcases mrs with ⟨m, r, s⟩
  cases m with
  | Z0 => cases r <;> cases s <;> rfl
  | Zpos p => cases p <;> cases r <;> cases s <;> rfl
  | Zneg p => cases p <;> cases r <;> cases s <;> rfl

theorem inbetween_shr_1 :
    ∀ (ctx : ExactRealContext), inbetween_shr_1Statement ctx := by
  intro ctx x mrs e hm hx
  have h := CompCert4Lean.Flocq.Calc.Bracket.inbetween_float_new_location
    ctx radix2 x (shr_m mrs) e (loc_of_shr_record mrs) Zone
    (by change (0 : Int) < 1; decide) hx
  change CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx radix2
    (Raux.Zdiv (shr_m mrs) Ztwo) (Zadd e Zone) x
    (CompCert4Lean.Flocq.Calc.Bracket.new_location Ztwo
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Zmod (shr_m mrs) Ztwo)
      (loc_of_shr_record mrs)) at h
  rw [(pg_shr_one_divmod mrs hm).1, (pg_shr_one_divmod mrs hm).2,
    pg_shr_one_location] at h
  exact h

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

theorem inbetween_shr :
    ∀ (ctx : ExactRealContext), inbetween_shrStatement ctx := by
  intro ctx x m e l n hm hx
  rcases CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zorder.Zle_or_lt_proof
      Z0 n with hn | hn
  · have hnonneg : ∀ (k : Nat) (mrs : shr_record),
        Zle Z0 (shr_m mrs) →
          Zle Z0 (shr_m (CompCert4Lean.Flocq.Core.Zaux.iter_nat shr_1 k mrs)) := by
      intro k
      induction k with
      | zero =>
          intro mrs hmrs
          simpa [CompCert4Lean.Flocq.Core.Zaux.iter_nat] using hmrs
      | succ k ih =>
          intro mrs hmrs
          simp only [CompCert4Lean.Flocq.Core.Zaux.iter_nat]
          exact ih (shr_1 mrs) (le_shr1_le mrs hmrs).1
    have haux : ∀ (k : Nat) (mrs : shr_record) (e : Z),
        Zle Z0 (shr_m mrs) →
        CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx radix2
            (shr_m mrs) e x (loc_of_shr_record mrs) →
        CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx radix2
            (shr_m (CompCert4Lean.Flocq.Core.Zaux.iter_nat shr_1 k mrs))
            (Zadd e
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat k)) x
            (loc_of_shr_record
              (CompCert4Lean.Flocq.Core.Zaux.iter_nat shr_1 k mrs)) := by
      intro k
      induction k with
      | zero =>
          intro mrs e hmrs hbetween
          simp only [CompCert4Lean.Flocq.Core.Zaux.iter_nat]
          have hzero : Zadd e
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 0) = e := by
            change Zadd e Z0 = e
            exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add_0_r e
          rw [hzero]
          exact hbetween
      | succ k ih =>
          intro mrs e hmrs hbetween
          simp only [CompCert4Lean.Flocq.Core.Zaux.iter_nat]
          rw [pg_iter_nat_comp]
          have hsucc : Zadd e
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (Nat.succ k)) =
              Zadd (Zadd e
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat k)) Zone := by
            rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Nat2Z.inj_succ]
            unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.succ
            exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add_assoc e
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat k) Zone
          rw [hsucc]
          apply inbetween_shr_1
          · exact hnonneg k mrs hmrs
          · exact ih mrs e hmrs hbetween
    rw [shr_nat (shr_record_of_loc m l) e n hn]
    have hnat := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Z2Nat.id n hn
    have hm' : Zle Z0 (shr_m (shr_record_of_loc m l)) := by
      rw [shr_m_shr_record_of_loc]
      exact hm
    have hx' : CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx radix2
        (shr_m (shr_record_of_loc m l)) e x (loc_of_shr_record (shr_record_of_loc m l)) := by
      rw [shr_m_shr_record_of_loc, loc_of_shr_record_of_loc]
      exact hx
    simpa [hnat] using haux
      (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat n)
      (shr_record_of_loc m l) e hm' hx'
  · cases n with
    | Z0 =>
        exfalso
        change (0 : Int) < 0 at hn
        omega
    | Zpos p =>
        exfalso
        change (Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) : Int) < 0 at hn
        exact (Int.not_lt_of_ge (Int.ofNat_zero_le _)) hn
    | Zneg p =>
        simp [Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shr]
        rw [shr_m_shr_record_of_loc, loc_of_shr_record_of_loc]
        exact hx

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

open CompCert4Lean.Flocq.Core

private theorem pg_round_mode_trunc_valid (ctx : ExactRealContext) :
    Generic_fmt.Exact.Valid_rnd ctx (Raux.Exact.Ztrunc ctx) := by
  constructor
  · intro x y hxy
    have le_total (a b : Raux.Exact.R ctx) :
        Raux.Exact.Rle ctx a b ∨ Raux.Exact.Rle ctx b a := by
      rcases ctx.certificate.total_order a b with (h | h) | h
      · exact Or.inl ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h).1
      · subst b
        exact Or.inl (ctx.certificate.orderedField.le_refl _)
      · exact Or.inr ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h).1
    by_cases hx : Raux.Exact.Rle ctx (Raux.Exact.R0 ctx) x
    · have hy := ctx.certificate.orderedField.le_trans _ _ _ hx hxy
      rw [Raux.Ztrunc_floor ctx x hx, Raux.Ztrunc_floor ctx y hy]
      exact Raux.Zfloor_le ctx x y hxy
    · have hx' := (le_total _ _).resolve_left hx
      by_cases hy : Raux.Exact.Rle ctx (Raux.Exact.R0 ctx) y
      · rw [Raux.Ztrunc_ceil ctx x hx', Raux.Ztrunc_floor ctx y hy]
        have hx0 : Raux.Exact.Rle ctx x (Raux.Exact.IZR ctx Z0) := by
          change ctx.spec.le x (ctx.spec.ofZ Z0)
          rw [ctx.certificate.sourceLaws.ofZ_zero]
          exact hx'
        have hy0 : Raux.Exact.Rle ctx (Raux.Exact.IZR ctx Z0) y := by
          change ctx.spec.le (ctx.spec.ofZ Z0) y
          rw [ctx.certificate.sourceLaws.ofZ_zero]
          exact hy
        exact Int.le_trans (Raux.Zceil_glb ctx Z0 x hx0)
          (Raux.Zfloor_lub ctx Z0 y hy0)
      · have hy' := (le_total _ _).resolve_left hy
        rw [Raux.Ztrunc_ceil ctx x hx', Raux.Ztrunc_ceil ctx y hy']
        exact Raux.Zceil_le ctx x y hxy
  · exact Raux.Ztrunc_IZR ctx

private theorem pg_round_mode_ceil_le_floor (ctx : ExactRealContext)
    (x y : Raux.Exact.R ctx)
    (h : Zlt (Raux.Exact.Zfloor ctx x) (Raux.Exact.Zfloor ctx y)) :
    Zle (Raux.Exact.Zceil ctx x) (Raux.Exact.Zfloor ctx y) := by
  have hgap : Zle (Zadd (Raux.Exact.Zfloor ctx x) Zone)
      (Raux.Exact.Zfloor ctx y) := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zadd (Raux.Exact.Zfloor ctx x) Zone) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Raux.Exact.Zfloor ctx y)
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Raux.Exact.Zfloor ctx x) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Raux.Exact.Zfloor ctx y) at h
    simp only [Zadd, Zaux.Zadd,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change _ + 1 ≤ _
    omega
  have hupper : Raux.Exact.Rle ctx x
      (Raux.Exact.IZR ctx (Zadd (Raux.Exact.Zfloor ctx x) Zone)) := by
    change ctx.spec.le x (ctx.spec.ofZ (Zadd (Raux.Exact.Zfloor ctx x) Zone))
    rw [ctx.certificate.sourceLaws.ofZ_add, ctx.certificate.sourceLaws.ofZ_one]
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
      (Raux.Zfloor_ub ctx x)).1
  exact Raux.Zceil_glb ctx _ x
    (ctx.certificate.orderedField.le_trans _ _ _ hupper
      (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_le ctx _ _ hgap))

private theorem pg_round_mode_nearest_valid (ctx : ExactRealContext)
    (choice : Z → Bool) :
    Generic_fmt.Exact.Valid_rnd ctx (Generic_fmt.Exact.Znearest ctx choice) := by
  constructor
  · intro x y hxy
    have hf := Raux.Zfloor_le ctx x y hxy
    have hc := Raux.Zceil_le ctx x y hxy
    have hfc : Zle (Raux.Exact.Zfloor ctx x) (Raux.Exact.Zceil ctx y) :=
      Int.le_trans hf (Generic_fmt.Znearest_ge_floor ctx choice y |>
        fun h => Int.le_trans h (Generic_fmt.Znearest_le_ceil ctx choice y))
    by_cases heq : Raux.Exact.Zfloor ctx x = Raux.Exact.Zfloor ctx y
    · let a := Raux.Exact.Rminus ctx x
        (Raux.Exact.IZR ctx (Raux.Exact.Zfloor ctx x))
      let b := Raux.Exact.Rminus ctx y
        (Raux.Exact.IZR ctx (Raux.Exact.Zfloor ctx y))
      let c := Raux.Exact.Rdiv ctx (Raux.Exact.Rone ctx) (Raux.Exact.Rtwo ctx)
      have hab : Raux.Exact.Rle ctx a b := by
        dsimp [a, b]
        rw [heq]
        exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_le_compat_r
          ctx (Raux.Exact.Ropp ctx (Raux.Exact.IZR ctx (Raux.Exact.Zfloor ctx y)))
          x y hxy
      change Zle
        (match Raux.Exact.Rcompare ctx a c with
         | .Lt => Raux.Exact.Zfloor ctx x
         | .Eq => if choice (Raux.Exact.Zfloor ctx x) then Raux.Exact.Zceil ctx x
             else Raux.Exact.Zfloor ctx x
         | .Gt => Raux.Exact.Zceil ctx x)
        (match Raux.Exact.Rcompare ctx b c with
         | .Lt => Raux.Exact.Zfloor ctx y
         | .Eq => if choice (Raux.Exact.Zfloor ctx y) then Raux.Exact.Zceil ctx y
             else Raux.Exact.Zfloor ctx y
         | .Gt => Raux.Exact.Zceil ctx y)
      cases ha : Raux.Exact.Rcompare ctx a c with
      | Lt =>
          cases hb : Raux.Exact.Rcompare ctx b c with
          | Lt => exact hf
          | Eq => dsimp only; split <;> assumption
          | Gt => exact hfc
      | Eq =>
          have ha' := Raux.Rcompare_Eq_inv ctx a c ha
          cases hb : Raux.Exact.Rcompare ctx b c with
          | Lt =>
              have hb' := Raux.Rcompare_Lt_inv ctx b c hb
              exact False.elim (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
                hb').2 (ha' ▸ hab))
          | Eq =>
              dsimp only
              rw [heq]
              split
              · exact hc
              · exact Int.le_refl _
          | Gt => dsimp only; split <;> assumption
      | Gt =>
          have ha' := Raux.Rcompare_Gt_inv ctx a c ha
          have hnot : ¬ Raux.Exact.Rle ctx b c := by
            intro hbc
            exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp ha').2
              (ctx.certificate.orderedField.le_trans _ _ _ hab hbc)
          cases hb : Raux.Exact.Rcompare ctx b c with
          | Lt =>
              exact False.elim (hnot
                ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
                  (Raux.Rcompare_Lt_inv ctx b c hb)).1)
          | Eq =>
              have hb' := Raux.Rcompare_Eq_inv ctx b c hb
              exact False.elim (hnot (hb' ▸ ctx.certificate.orderedField.le_refl c))
          | Gt => exact hc
    · have hne : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Raux.Exact.Zfloor ctx x) ≠
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Raux.Exact.Zfloor ctx y) :=
        fun h => heq (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective h)
      have hlt : Zlt (Raux.Exact.Zfloor ctx x) (Raux.Exact.Zfloor ctx y) := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Raux.Exact.Zfloor ctx x) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Raux.Exact.Zfloor ctx y)
        have hf' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Raux.Exact.Zfloor ctx x) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Raux.Exact.Zfloor ctx y) := hf
        omega
      exact Int.le_trans (Generic_fmt.Znearest_le_ceil ctx choice x)
        (Int.le_trans (pg_round_mode_ceil_le_floor ctx x y hlt)
          (Generic_fmt.Znearest_ge_floor ctx choice y))
  · intro n
    rcases Generic_fmt.Znearest_DN_or_UP ctx choice (Raux.Exact.IZR ctx n) with h | h
    · exact h.trans (Raux.Zfloor_IZR ctx n)
    · exact h.trans (Raux.Zceil_IZR ctx n)

theorem valid_rnd_round_mode_proof (ctx : ExactRealContext) :
    valid_rnd_round_modeStatement ctx := by
  intro m
  cases m with
  | mode_NE => exact pg_round_mode_nearest_valid ctx (fun n => Bool.not (Zeven n))
  | mode_ZR => exact pg_round_mode_trunc_valid ctx
  | mode_DN => exact ⟨Raux.Zfloor_le ctx, Raux.Zfloor_IZR ctx⟩
  | mode_UP => exact ⟨Raux.Zceil_le ctx, Raux.Zceil_IZR ctx⟩
  | mode_NA => exact pg_round_mode_nearest_valid ctx (fun n => Zle_bool Z0 n)

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_fexp_mono (prec emax first second : Z)
    (ordered : Zle first second) :
    Zle (fexp0 prec emax first) (fexp0 prec emax second) := by
  change intOfZ first ≤ intOfZ second at ordered
  change intOfZ (ZArith.BinInt.Z.max (Zsub first prec) (emin0 prec emax)) ≤
    intOfZ (ZArith.BinInt.Z.max (Zsub second prec) (emin0 prec emax))
  unfold ZArith.BinInt.Z.max
  split <;> split <;>
    simp_all only [Zsub, Zaux.Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] <;> omega

private theorem manual_bounded_exponent (prec emax : Z)
    (first second : positive) (firstExp secondExp : Z)
    (firstBounded : bounded0 prec emax first firstExp = true)
    (secondBounded : bounded0 prec emax second secondExp = true)
    (ordered : Zlt firstExp secondExp) :
    Zlt (Zadd (Zdigits radix2 (Zpos first)) firstExp)
      (Zadd (Zdigits radix2 (Zpos second)) secondExp) := by
  have firstCanonical := (Bool.and_eq_true_iff.mp firstBounded).1
  have secondCanonical := (Bool.and_eq_true_iff.mp secondBounded).1
  have firstEq := ZArith.Zbool.Zeq_bool_eq _ _ firstCanonical
  have secondEq := ZArith.Zbool.Zeq_bool_eq _ _ secondCanonical
  change fexp0 prec emax (Zadd (Digits.Zpos (Digits.digits2_pos first)) firstExp) = firstExp at firstEq
  change fexp0 prec emax (Zadd (Digits.Zpos (Digits.digits2_pos second)) secondExp) = secondExp at secondEq
  rw [Digits.Zpos_digits2_pos first] at firstEq
  rw [Digits.Zpos_digits2_pos second] at secondEq
  apply Classical.byContradiction
  intro unordered
  have reversed : Zle (Zadd (Zdigits radix2 (Zpos second)) secondExp)
      (Zadd (Zdigits radix2 (Zpos first)) firstExp) := Int.le_of_not_gt unordered
  have monotone := manual_fexp_mono prec emax _ _ reversed
  rw [firstEq, secondEq] at monotone
  exact (Int.not_le.mpr ordered) monotone

private theorem manual_float_power (ctx : ExactRealContext) (exponent power : Z)
    (nonnegative : Zle Z0 power) :
    Exact.F2R ctx (Float radix2 (Zpower (radix2 : Z) power) exponent) =
      Exact.bpow ctx radix2 (Zadd power exponent) := by
  change ctx.spec.mul (ctx.spec.ofZ (Zpower (radix2 : Z) power))
    (Exact.bpow ctx radix2 exponent) = _
  rw [show ctx.spec.ofZ (Zpower (radix2 : Z) power) =
    Exact.bpow ctx radix2 power from Raux.IZR_Zpower ctx radix2 power nonnegative]
  exact (Raux.bpow_plus ctx radix2 power exponent).symm

private theorem manual_float_bounds (ctx : ExactRealContext)
    (mantissa : positive) (exponent : Z) :
    Exact.Rle ctx
        (Exact.bpow ctx radix2 (Zadd (Zsub (Zdigits radix2 (Zpos mantissa)) Zone) exponent))
        (Exact.F2R ctx (Float radix2 (Zpos mantissa) exponent)) ∧
      Exact.Rlt ctx (Exact.F2R ctx (Float radix2 (Zpos mantissa) exponent))
        (Exact.bpow ctx radix2 (Zadd (Zdigits radix2 (Zpos mantissa)) exponent)) := by
  have nonzero : Zpos mantissa ≠ Z0 := by intro impossible; cases impossible
  have digitsPositive := Digits.Zdigits_gt_0 radix2 (Zpos mantissa) nonzero
  have lowerExponent : Zle Z0 (Zsub (Zdigits radix2 (Zpos mantissa)) Zone) := by
    change intOfZ Z0 ≤ intOfZ (Zsub _ Zone)
    simp only [Zsub, Zaux.Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    change (0 : Int) ≤ intOfZ (Zdigits radix2 (Zpos mantissa)) - 1
    exact Int.sub_nonneg.mpr digitsPositive
  have bounds := Digits.Zdigits_correct radix2 (Zpos mantissa)
  have absolute : Digits.Zabs (Zpos mantissa) = Zpos mantissa := by
    apply intOfZ_injective
    change intOfZ (zOfInt (Int.natAbs (intOfZ (Zpos mantissa)))) = intOfZ (Zpos mantissa)
    rw [intOfZ_zOfInt]
    rfl
  rw [absolute] at bounds
  constructor
  · have bound := Float_prop.F2R_le ctx radix2 _ _ exponent bounds.1
    change Exact.Rle ctx
      (Exact.F2R ctx (Float radix2 (Zpower (radix2 : Z)
        (Zsub (Zdigits radix2 (Zpos mantissa)) Zone)) exponent))
      (Exact.F2R ctx (Float radix2 (Zpos mantissa) exponent)) at bound
    rw [manual_float_power ctx exponent _ lowerExponent] at bound
    exact bound
  · have bound := Float_prop.F2R_lt ctx radix2 exponent _ _ bounds.2
    change Exact.Rlt ctx (Exact.F2R ctx (Float radix2 (Zpos mantissa) exponent))
      (Exact.F2R ctx (Float radix2 (Zpower (radix2 : Z)
        (Zdigits radix2 (Zpos mantissa))) exponent)) at bound
    rw [manual_float_power ctx exponent _ (Int.le_of_lt digitsPositive)] at bound
    exact bound

private theorem manual_bounded_lt (prec emax : Z) (ctx : ExactRealContext)
    (first second : positive) (firstExp secondExp : Z)
    (firstBounded : bounded0 prec emax first firstExp = true)
    (secondBounded : bounded0 prec emax second secondExp = true)
    (ordered : Zlt firstExp secondExp) :
    Exact.Rlt ctx (Exact.F2R ctx (Float radix2 (Zpos first) firstExp))
      (Exact.F2R ctx (Float radix2 (Zpos second) secondExp)) := by
  have digitOrder := manual_bounded_exponent prec emax first second firstExp secondExp
    firstBounded secondBounded ordered
  have powerOrder : Zle (Zadd (Zdigits radix2 (Zpos first)) firstExp)
      (Zadd (Zsub (Zdigits radix2 (Zpos second)) Zone) secondExp) := by
    change intOfZ (Zadd _ _) < intOfZ (Zadd _ _) at digitOrder
    change intOfZ (Zadd _ _) ≤ intOfZ (Zadd _ _)
    simp only [Zadd, Zaux.Zadd, ZArith.BinInt.Z.add,
      Zsub, Zaux.Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] at digitOrder ⊢
    change _ ≤ _ - 1 + _
    omega
  have powers := Raux.bpow_le ctx radix2 _ _ powerOrder
  have firstUpper := (manual_float_bounds ctx first firstExp).2
  have secondLower := (manual_float_bounds ctx second secondExp).1
  exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
    ctx _ _ _ firstUpper (ctx.certificate.orderedField.le_trans _ _ _ powers secondLower)

private theorem manual_positive_compare (prec emax : Z) (ctx : ExactRealContext)
    (first second : positive) (firstExp secondExp : Z)
    (firstBounded : bounded0 prec emax first firstExp = true)
    (secondBounded : bounded0 prec emax second secondExp = true) :
    Exact.Rcompare ctx (Exact.F2R ctx (Float radix2 (Zpos first) firstExp))
      (Exact.F2R ctx (Float radix2 (Zpos second) secondExp)) =
      match Zcompare firstExp secondExp with
      | .Eq => Zcompare (Zpos first) (Zpos second)
      | ordering => ordering := by
  by_cases ordered : Zlt firstExp secondExp
  · have comparisonEq : Zcompare firstExp secondExp = Lt := Zaux.Zcompare_Lt _ _ ordered
    rw [comparisonEq]
    exact Raux.Rcompare_Lt ctx _ _
      (manual_bounded_lt prec emax ctx first second firstExp secondExp
        firstBounded secondBounded ordered)
  · by_cases equal : firstExp = secondExp
    · subst secondExp
      have comparisonEq : Zcompare firstExp firstExp = Eq := Zaux.Zcompare_Eq _ _ rfl
      rw [comparisonEq]
      exact Float_prop.Rcompare_F2R ctx radix2 firstExp (Zpos first) (Zpos second)
    · have reversed : Zlt secondExp firstExp := by
        have distinct : intOfZ firstExp ≠ intOfZ secondExp :=
          fun equality => equal (intOfZ_injective equality)
        change ¬ intOfZ firstExp < intOfZ secondExp at ordered
        change intOfZ secondExp < intOfZ firstExp
        omega
      have comparisonEq : Zcompare firstExp secondExp = Gt := Zaux.Zcompare_Gt _ _ reversed
      rw [comparisonEq]
      exact Raux.Rcompare_Gt ctx _ _
        (manual_bounded_lt prec emax ctx second first secondExp firstExp
          secondBounded firstBounded reversed)

private theorem manual_poscompare (first second : positive) :
    Zcompare (Zpos first) (Zpos second) =
      Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posCompare Eq first second := by
  change (if (posToNat first : Int) < (posToNat second : Int) then Lt else
    if (posToNat first : Int) = (posToNat second : Int) then Eq else Gt) =
    (if posToNat first < posToNat second then Lt else
      if posToNat first = posToNat second then Eq else Gt)
  have castLt : (posToNat first : Int) < (posToNat second : Int) ↔
      posToNat first < posToNat second := by omega
  simp only [castLt, Int.natCast_inj]

private theorem manual_positive_value (ctx : ExactRealContext)
    (mantissa : positive) (exponent : Z) :
    Exact.Rlt ctx (Exact.R0 ctx)
      (Exact.F2R ctx (Float radix2 (Zpos mantissa) exponent)) := by
  apply Float_prop.F2R_gt_0 ctx
  exact Int.natCast_pos.mpr (posToNat_positive mantissa)

private theorem manual_negative_value (ctx : ExactRealContext)
    (mantissa : positive) (exponent : Z) :
    Exact.Rlt ctx (Exact.F2R ctx (Float radix2 (Zopp (Zpos mantissa)) exponent))
      (Exact.R0 ctx) := by
  apply Float_prop.F2R_lt_0 ctx
  change intOfZ (Zopp (Zpos mantissa)) < (0 : Int)
  simp only [Zopp, Zaux.Zopp, ZArith.BinInt.Z.opp, intOfZ_zOfInt]
  change -(posToNat mantissa : Int) < 0
  have positive := posToNat_positive mantissa
  omega

theorem Bcompare_correct :
    ∀ {prec emax : Z} (ctx : ExactRealContext),
      Bcompare_correctStatement (prec := prec) (emax := emax) ctx := by
  intro prec emax ctx first second firstCertificate secondCertificate firstFinite secondFinite
  cases first with
  | B754_nan => cases firstFinite
  | B754_infinity sign => cases firstFinite
  | B754_zero firstSign =>
      cases second with
      | B754_nan => cases secondFinite
      | B754_infinity sign => cases secondFinite
      | B754_zero secondSign =>
          exact congrArg some (Raux.Rcompare_Eq ctx _ _ rfl).symm
      | B754_finite secondSign secondMant secondExp =>
          cases secondSign with
          | false =>
              exact congrArg some
                (Raux.Rcompare_Lt ctx _ _ (manual_positive_value ctx secondMant secondExp)).symm
          | true =>
              exact congrArg some
                (Raux.Rcompare_Gt ctx _ _ (manual_negative_value ctx secondMant secondExp)).symm
  | B754_finite firstSign firstMant firstExp =>
      cases second with
      | B754_nan => cases secondFinite
      | B754_infinity sign => cases secondFinite
      | B754_zero secondSign =>
          cases firstSign with
          | false =>
              exact congrArg some
                (Raux.Rcompare_Gt ctx _ _ (manual_positive_value ctx firstMant firstExp)).symm
          | true =>
              exact congrArg some
                (Raux.Rcompare_Lt ctx _ _ (manual_negative_value ctx firstMant firstExp)).symm
      | B754_finite secondSign secondMant secondExp =>
          have positiveCompare := manual_positive_compare prec emax ctx firstMant secondMant
            firstExp secondExp firstCertificate secondCertificate
          rw [manual_poscompare] at positiveCompare
          cases firstSign <;> cases secondSign
          · exact congrArg some positiveCompare.symm
          · exact congrArg some (Raux.Rcompare_Gt ctx _ _
              (ctx.certificate.orderedField.lt_trans _ _ _
                (manual_negative_value ctx secondMant secondExp)
                (manual_positive_value ctx firstMant firstExp))).symm
          · exact congrArg some (Raux.Rcompare_Lt ctx _ _
              (ctx.certificate.orderedField.lt_trans _ _ _
                (manual_negative_value ctx firstMant firstExp)
                (manual_positive_value ctx secondMant secondExp))).symm
          · have reversed := Raux.Rcompare_sym ctx
              (Exact.F2R ctx (Float radix2 (Zpos secondMant) secondExp))
              (Exact.F2R ctx (Float radix2 (Zpos firstMant) firstExp))
            change Exact.Rcompare ctx _ _ = CompOpp
              (Exact.Rcompare ctx (Exact.F2R ctx (Float radix2 (Zpos firstMant) firstExp))
                (Exact.F2R ctx (Float radix2 (Zpos secondMant) secondExp))) at reversed
            rw [positiveCompare] at reversed
            have opposite := Raux.Rcompare_opp ctx
              (Exact.F2R ctx (Float radix2 (Zpos firstMant) firstExp))
              (Exact.F2R ctx (Float radix2 (Zpos secondMant) secondExp))
            have firstNeg := Float_prop.F2R_Zopp ctx radix2 (Zpos firstMant) firstExp
            have secondNeg := Float_prop.F2R_Zopp ctx radix2 (Zpos secondMant) secondExp
            change Exact.Rcompare ctx
              (Exact.Ropp ctx (Exact.F2R ctx (Float radix2 (Zpos firstMant) firstExp)))
              (Exact.Ropp ctx (Exact.F2R ctx (Float radix2 (Zpos secondMant) secondExp))) = _ at opposite
            have negativeComparison := opposite.trans reversed
            change Exact.F2R ctx (Float radix2 (Zopp (Zpos firstMant)) firstExp) =
              Exact.Ropp ctx (Exact.F2R ctx (Float radix2 (Zpos firstMant) firstExp)) at firstNeg
            change Exact.F2R ctx (Float radix2 (Zopp (Zpos secondMant)) secondExp) =
              Exact.Ropp ctx (Exact.F2R ctx (Float radix2 (Zpos secondMant) secondExp)) at secondNeg
            change some _ = some (Exact.Rcompare ctx
              (Exact.F2R ctx (Float radix2 (Zopp (Zpos firstMant)) firstExp))
              (Exact.F2R ctx (Float radix2 (Zopp (Zpos secondMant)) secondExp)))
            rw [firstNeg, secondNeg, negativeComparison]
            change some (match Zcompare firstExp secondExp with
              | .Eq => CompOpp (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posCompare Eq firstMant secondMant)
              | .Lt => Gt
              | .Gt => Lt) = some (CompOpp (match Zcompare firstExp secondExp with
              | .Eq => Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posCompare Eq firstMant secondMant
              | ordering => ordering))
            cases Zcompare firstExp secondExp <;> rfl

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private def manual_shift_encoding (record : shr_record) : Int :=
  2 * intOfZ (shr_m record) + if shr_r record then 1 else 0

private theorem manual_shift_encoding_step (record : shr_record)
    (nonnegative : Zle Z0 (shr_m record)) :
    manual_shift_encoding (shr_1 record) = manual_shift_encoding record / 2 := by
  rcases record with ⟨mantissa, rounding, sticky⟩
  cases mantissa with
  | Z0 => cases rounding <;> rfl
  | Zpos mantissa =>
      cases mantissa <;> cases rounding <;>
        simp [manual_shift_encoding, shr_1, Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shr_1,
          shr_m, shr_r, intOfZ, posToNat] <;> omega
  | Zneg mantissa =>
      change (0 : Int) ≤ -(posToNat mantissa : Int) at nonnegative
      have positive := posToNat_positive mantissa
      omega

private theorem manual_shift_sticky_step (record : shr_record)
    (nonnegative : Zle Z0 (shr_m record)) :
    (shr_1 record).shr_s = false ↔
      manual_shift_encoding record % 2 = 0 ∧ record.shr_s = false := by
  rcases record with ⟨mantissa, rounding, sticky⟩
  cases mantissa with
  | Z0 => cases rounding <;> cases sticky <;> decide
  | Zpos mantissa =>
      cases mantissa <;> cases rounding <;> cases sticky <;>
        simp [manual_shift_encoding, shr_1, Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shr_1,
          shr_m, shr_r, intOfZ, posToNat] <;> omega
  | Zneg mantissa =>
      change (0 : Int) ≤ -(posToNat mantissa : Int) at nonnegative
      have positive := posToNat_positive mantissa
      omega

private theorem manual_mod_product (value divisor : Int) :
    value % (divisor * 2) = 0 ↔ value % divisor = 0 ∧ value / divisor % 2 = 0 := by
  constructor
  · intro divisible
    have productDivides := Int.dvd_of_emod_eq_zero divisible
    exact ⟨Int.emod_eq_zero_of_dvd (Int.dvd_trans (Int.dvd_mul_right divisor 2) productDivides),
      Int.emod_eq_zero_of_dvd (Int.dvd_ediv_of_mul_dvd productDivides)⟩
  · rintro ⟨first, second⟩
    exact Int.emod_eq_zero_of_dvd (Int.mul_dvd_of_dvd_ediv
      (Int.dvd_of_emod_eq_zero first) (Int.dvd_of_emod_eq_zero second))

private theorem manual_iter_encoding (count : Nat) (record : shr_record)
    (nonnegative : Zle Z0 (shr_m record)) :
    Zle Z0 (shr_m (Zaux.iter_nat shr_1 count record)) ∧
      manual_shift_encoding (Zaux.iter_nat shr_1 count record) =
        manual_shift_encoding record / (2 : Int) ^ count ∧
      ((Zaux.iter_nat shr_1 count record).shr_s = false ↔
        manual_shift_encoding record % (2 : Int) ^ count = 0 ∧ record.shr_s = false) := by
  induction count with
  | zero => simpa [Zaux.iter_nat] using nonnegative
  | succ count induction =>
      have iteration : Zaux.iter_nat shr_1 (count + 1) record =
          shr_1 (Zaux.iter_nat shr_1 count record) :=
        Zaux.iter_nat_S shr_1 count record
      rw [iteration]
      refine ⟨(le_shr1_le _ induction.1).1, ?_, ?_⟩
      · rw [manual_shift_encoding_step _ induction.1, induction.2.1]
        rw [Int.ediv_ediv_of_nonneg (Int.pow_nonneg (by decide)), Int.pow_succ]
      · rw [manual_shift_sticky_step _ induction.1, induction.2.1, induction.2.2,
          Int.pow_succ, manual_mod_product]
        simp only [and_assoc, and_left_comm]

private theorem manual_record_ext (first second : shr_record)
    (encoding : manual_shift_encoding first = manual_shift_encoding second)
    (sticky : first.shr_s = false ↔ second.shr_s = false) : first = second := by
  rcases first with ⟨firstMantissa, firstRound, firstSticky⟩
  rcases second with ⟨secondMantissa, secondRound, secondSticky⟩
  have stickyEqual : firstSticky = secondSticky := by
    cases firstSticky <;> cases secondSticky <;> simp_all
  subst secondSticky
  change 2 * intOfZ firstMantissa + (if firstRound then 1 else 0) =
    2 * intOfZ secondMantissa + (if secondRound then 1 else 0) at encoding
  cases firstRound <;> cases secondRound <;> simp only [Bool.false_eq_true, if_false, if_true] at encoding
  · have mantissaEqual : firstMantissa = secondMantissa := intOfZ_injective (by omega)
    subst secondMantissa
    rfl
  · omega
  · omega
  · have mantissaEqual : firstMantissa = secondMantissa := intOfZ_injective (by omega)
    subst secondMantissa
    rfl

private def manual_location (half remainder : Int) (rounding sticky : Bool) : location :=
  if remainder = 0 then
    if rounding || sticky then loc_Inexact Lt else loc_Exact
  else if remainder < half then loc_Inexact Lt
  else if remainder = half then
    if rounding || sticky then loc_Inexact Gt else loc_Inexact Eq
  else loc_Inexact Gt

private theorem manual_location_formula (half remainder : Int)
    (mantissa : Z) (rounding sticky : Bool) :
    new_location (zOfInt (2 * half)) (zOfInt remainder)
      (loc_of_shr_record ⟨mantissa, rounding, sticky⟩) =
      manual_location half remainder rounding sticky := by
  have even : Calc.Bracket.Zeven (zOfInt (2 * half)) = true := by
    change decide (Int.natAbs (intOfZ (zOfInt (2 * half))) % 2 = 0) = true
    simp [intOfZ_zOfInt, Int.natAbs_mul, Nat.mul_mod]
  have zeroEquivalence : zOfInt remainder = (Z0 : Z) ↔ remainder = 0 := by
    constructor
    · intro equal
      have equality := congrArg intOfZ equal
      rw [intOfZ_zOfInt] at equality
      exact equality
    · intro equal
      subst remainder
      rfl
  have comparisonValue : Calc.Bracket.Zcompare
      (Calc.Bracket.Zmul Calc.Bracket.Ztwo (zOfInt remainder)) (zOfInt (2 * half)) =
      if remainder < half then Lt else if remainder = half then Eq else Gt := by
    change (if intOfZ (zOfInt (2 * intOfZ (zOfInt remainder))) < intOfZ (zOfInt (2 * half)) then Lt
      else if intOfZ (zOfInt (2 * intOfZ (zOfInt remainder))) = intOfZ (zOfInt (2 * half)) then Eq else Gt) = _
    simp only [intOfZ_zOfInt]
    have less : 2 * remainder < 2 * half ↔ remainder < half := by omega
    have equal : 2 * remainder = 2 * half ↔ remainder = half := by omega
    simp only [less, equal]
  unfold new_location Calc.Bracket.new_location
  rw [even]
  simp only [if_true]
  unfold Calc.Bracket.new_location_even
  rw [comparisonValue]
  simp only [Calc.Bracket.Zeq_bool, Zaux.Zeq_bool, ZArith.Zbool.Zeq_bool,
    zeroEquivalence, decide_eq_true_eq]
  by_cases zero : remainder = 0 <;> by_cases less : remainder < half <;>
    by_cases equal : remainder = half <;> cases rounding <;> cases sticky <;>
    simp [manual_location, zero, less, equal, loc_of_shr_record,
      Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.loc_of_shr_record]

private theorem manual_encoded_division (mantissa divisor bit : Int)
    (nonzero : divisor ≠ 0) :
    (2 * mantissa + bit) / divisor =
        2 * (mantissa / divisor) + (2 * (mantissa % divisor) + bit) / divisor ∧
      (2 * mantissa + bit) % divisor = (2 * (mantissa % divisor) + bit) % divisor := by
  have decomposition : 2 * mantissa + bit =
      (2 * (mantissa % divisor) + bit) + divisor * (2 * (mantissa / divisor)) := by
    calc
      2 * mantissa + bit = 2 * (mantissa % divisor + divisor * (mantissa / divisor)) + bit :=
        congrArg (fun value => 2 * value + bit) (Int.emod_add_mul_ediv mantissa divisor).symm
      _ = _ := by
        simp only [Int.mul_add, Int.mul_left_comm 2 divisor]
        omega
  rw [decomposition, Int.add_mul_ediv_left _ _ nonzero, Int.add_mul_emod_self_left]
  exact ⟨Int.add_comm _ _, rfl⟩

private theorem manual_result_encoding (mantissa half : Int) (positive : 0 < half)
    (rounding sticky : Bool) :
    let result := shr_record_of_loc (zOfInt (mantissa / (2 * half)))
      (manual_location half (mantissa % (2 * half)) rounding sticky)
    manual_shift_encoding result =
        (2 * mantissa + if rounding then 1 else 0) / (2 * half) ∧
      (result.shr_s = false ↔
        (2 * mantissa + if rounding then 1 else 0) % (2 * half) = 0 ∧ sticky = false) := by
  let remainder := mantissa % (2 * half)
  let bit : Int := if rounding then 1 else 0
  have bitBounds : 0 ≤ bit ∧ bit ≤ 1 := by cases rounding <;> decide
  have divisorPositive : 0 < 2 * half := by omega
  have divisorNonzero : 2 * half ≠ 0 := by omega
  have halfNonzero : half ≠ 0 := by omega
  have lower : 0 ≤ remainder := Int.emod_nonneg _ divisorNonzero
  have upper : remainder < 2 * half := Int.emod_lt_of_pos _ divisorPositive
  have division := manual_encoded_division mantissa (2 * half) bit divisorNonzero
  have residual :
      ((2 * remainder + bit) / (2 * half) = if remainder < half then 0 else 1) ∧
      ((2 * remainder + bit) % (2 * half) =
        if remainder < half then 2 * remainder + bit else 2 * remainder + bit - 2 * half) := by
    by_cases less : remainder < half
    · simp only [less, if_true]
      exact (Int.ediv_emod_unique divisorPositive).mpr ⟨by omega, by omega, by omega⟩
    · simp only [less, if_false]
      exact (Int.ediv_emod_unique divisorPositive).mpr ⟨by omega, by omega, by omega⟩
  have quotientValue := division.1.trans (congrArg (fun value => 2 * (mantissa / (2 * half)) + value) residual.1)
  have remainderValue := division.2.trans residual.2
  dsimp only
  change manual_shift_encoding (shr_record_of_loc (zOfInt (mantissa / (2 * half)))
      (manual_location half remainder rounding sticky)) = (2 * mantissa + bit) / (2 * half) ∧
    ((shr_record_of_loc (zOfInt (mantissa / (2 * half)))
      (manual_location half remainder rounding sticky)).shr_s = false ↔
      (2 * mantissa + bit) % (2 * half) = 0 ∧ sticky = false)
  rw [quotientValue, remainderValue]
  by_cases zero : remainder = 0 <;> by_cases less : remainder < half <;>
    by_cases equal : remainder = half <;>
    cases rounding <;> cases sticky <;>
    simp [manual_location, zero, less, equal, halfNonzero, manual_shift_encoding, shr_record_of_loc,
      Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shr_record_of_loc,
      shr_m, shr_r, intOfZ_zOfInt, bit] <;> omega

private theorem manual_source_div (mantissa : Z) (divisor : Int) (positive : 0 < divisor) :
    Raux.Zdiv mantissa (zOfInt divisor) = zOfInt (intOfZ mantissa / divisor) := by
  change zOfInt (if intOfZ (zOfInt divisor) = 0 then 0
    else if 0 < intOfZ (zOfInt divisor) then intOfZ mantissa / intOfZ (zOfInt divisor)
    else _) = _
  simp only [intOfZ_zOfInt, positive, Int.ne_of_gt positive, if_false, if_true]

private theorem manual_source_mod (mantissa : Z) (divisor : Int) (positive : 0 < divisor) :
    ZArith.Zdiv.Zmod mantissa (zOfInt divisor) = zOfInt (intOfZ mantissa % divisor) := by
  change zOfInt (if intOfZ (zOfInt divisor) = 0 then intOfZ mantissa
    else if 0 < intOfZ (zOfInt divisor) then intOfZ mantissa % intOfZ (zOfInt divisor)
    else _) = _
  simp only [intOfZ_zOfInt, positive, Int.ne_of_gt positive, if_false, if_true]

private theorem manual_iter_record (count : Nat) (positiveCount : 0 < count)
    (record : shr_record) (nonnegative : Zle Z0 (shr_m record)) :
    Zaux.iter_nat shr_1 count record =
      shr_record_of_loc (Raux.Zdiv (shr_m record) (zOfInt ((2 : Int) ^ count)))
        (new_location (zOfInt ((2 : Int) ^ count))
          (ZArith.Zdiv.Zmod (shr_m record) (zOfInt ((2 : Int) ^ count)))
          (loc_of_shr_record record)) := by
  cases count with
  | zero => omega
  | succ count =>
      have invariant := manual_iter_encoding (count + 1) record nonnegative
      rcases record with ⟨mantissa, rounding, sticky⟩
      have powerPositive : 0 < (2 : Int) ^ count := Int.pow_pos (by decide)
      have powerRewrite : (2 : Int) ^ (count + 1) = 2 * 2 ^ count := by
        rw [Int.pow_succ, Int.mul_comm]
      have result := manual_result_encoding (intOfZ mantissa) (2 ^ count) powerPositive rounding sticky
      simp only [powerRewrite] at invariant ⊢
      change Zaux.iter_nat shr_1 (count + 1) ⟨mantissa, rounding, sticky⟩ =
        shr_record_of_loc (Raux.Zdiv mantissa (zOfInt (2 * 2 ^ count)))
          (new_location (zOfInt (2 * 2 ^ count))
            (ZArith.Zdiv.Zmod mantissa (zOfInt (2 * 2 ^ count)))
            (loc_of_shr_record ⟨mantissa, rounding, sticky⟩))
      rw [manual_source_div _ _ (by omega), manual_source_mod _ _ (by omega), manual_location_formula]
      apply manual_record_ext
      · exact invariant.2.1.trans result.1.symm
      · exact invariant.2.2.trans result.2.symm

private theorem manual_shr_truncate (mantissa exponent count : Z) (place : location)
    (nonnegative : Zle Z0 mantissa) :
    shr (shr_record_of_loc mantissa place) exponent count =
      if Zlt_bool Z0 count then
        (shr_record_of_loc (Raux.Zdiv mantissa (Zpower (radix2 : Z) count))
          (new_location (Zpower (radix2 : Z) count)
            (ZArith.Zdiv.Zmod mantissa (Zpower (radix2 : Z) count)) place), Zadd exponent count)
      else (shr_record_of_loc mantissa place, exponent) := by
  cases count with
  | Z0 => rfl
  | Zneg count =>
      have positive := posToNat_positive count
      have comparison : Zlt_bool Z0 (Zneg count) = false := by
        change (if (0 : Int) < -(posToNat count : Int) then true else false) = false
        simp [show ¬ (0 : Int) < -(posToNat count : Int) by omega]
      rw [comparison]
      rfl
  | Zpos count =>
      have positive := posToNat_positive count
      have comparison : Zlt_bool Z0 (Zpos count) = true := by
        change (if (0 : Int) < (posToNat count : Int) then true else false) = true
        simp [positive]
      rw [comparison]
      have countNonnegative : Zle Z0 (Zpos count) := by
        change (0 : Int) ≤ (posToNat count : Int)
        omega
      rw [shr_nat _ _ _ countNonnegative]
      change (Zaux.iter_nat shr_1 (posToNat count) (shr_record_of_loc mantissa place),
        Zadd exponent (Zpos count)) = _
      have recordNonnegative : Zle Z0 (shr_m (shr_record_of_loc mantissa place)) := by
        rw [shr_m_shr_record_of_loc]
        exact nonnegative
      rw [manual_iter_record _ positive _ recordNonnegative, shr_m_shr_record_of_loc,
        loc_of_shr_record_of_loc]
      have powerValue : Zpower (radix2 : Z) (Zpos count) = zOfInt ((2 : Int) ^ posToNat count) := by
        change (if (posToNat count : Int) < 0 then Z0
          else zOfInt ((2 : Int) ^ Int.toNat (posToNat count : Int))) = _
        rw [if_neg (by omega)]
        rfl
      rw [powerValue]
      rfl

theorem shr_fexp_truncate :
    ∀ {prec emax : Z} [Core.FLX.Prec_gt_0 prec],
      shr_fexp_truncateStatement (prec := prec) (emax := emax) := by
  intro prec emax precision mantissa exponent place nonnegative
  change shr (shr_record_of_loc mantissa place) exponent
      (Zsub (fexp0 prec emax (Zadd (Digits.Zdigits2 mantissa) exponent)) exponent) = _
  rw [Digits.Zdigits2_Zdigits]
  rw [manual_shr_truncate _ _ _ _ nonnegative]
  unfold truncate Calc.Round.truncate
  dsimp only
  simp only [Calc.Round.Zsub, Zsub, Calc.Round.Zadd, Zadd,
    Calc.Round.Zdigits, Zdigits, Calc.Round.Zlt_bool, Zlt_bool,
    Calc.Round.Z0, Z0, fexp, Digits.radix2, radix2]
  split <;> rename_i condition <;>
    simp only [condition, if_true, if_false, Calc.Round.truncate_aux]

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals

private theorem manual_mixed_sum_bounded {prec emax : Z}
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    [precision : FLX.Prec_gt_0 prec] (rounding : mode)
    (first second : positive) (firstExp secondExp : Z)
    (firstBounded : bounded (prec := prec) (emax := emax) first firstExp = true)
    (secondBounded : bounded (prec := prec) (emax := emax) second secondExp = true) :
    Exact.Rlt ctx
      (Exact.Rabs ctx (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
        (Exact.round_mode ctx rounding)
        (Exact.Rplus ctx
          (Exact.F2R ctx (Float radix2 (Zopp (Zpos first)) firstExp))
          (Exact.F2R ctx (Float radix2 (Zpos second) secondExp)))))
      (Exact.bpow ctx radix2 emax) := by
  have validExp : Valid_exp (fexp (prec := prec) (emax := emax)) :=
    FLT.FLT_exp_valid (emin (prec := prec) (emax := emax)) prec (h := precision)
  have validRound := valid_rnd_round_mode_proof ctx rounding
  have firstGeneric := Generic_fmt.generic_format_canonical ctx magnitude radix2
    (fexp (prec := prec) (emax := emax)) _
    (canonical_bounded (prec := prec) (emax := emax) ctx magnitude true
      first firstExp firstBounded)
  have secondGeneric := Generic_fmt.generic_format_canonical ctx magnitude radix2
    (fexp (prec := prec) (emax := emax)) _
    (canonical_bounded (prec := prec) (emax := emax) ctx magnitude false
      second secondExp secondBounded)
  have negative := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
    (manual_negative_value ctx first firstExp) |>.1
  have positive := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
    (manual_positive_value ctx second secondExp) |>.1
  have lower := RIneq.Rplus_le_compat_l ctx
    (Exact.F2R ctx (Float radix2 (Zopp (Zpos first)) firstExp)) _ _ positive
  change ctx.spec.le (ctx.spec.add _ ctx.spec.zero) _ at lower
  rw [ctx.certificate.orderedField.add_zero] at lower
  have upper := RIneq.Rplus_le_compat_r ctx
    (Exact.F2R ctx (Float radix2 (Zpos second) secondExp)) _ _ negative
  change ctx.spec.le _ (ctx.spec.add ctx.spec.zero _) at upper
  rw [ctx.certificate.orderedField.zero_add] at upper
  have roundedLower := Generic_fmt.round_ge_generic ctx magnitude radix2
    (fexp (prec := prec) (emax := emax)) validExp (Exact.round_mode ctx rounding)
    validRound _ _ firstGeneric lower
  have roundedUpper := Generic_fmt.round_le_generic ctx magnitude radix2
    (fexp (prec := prec) (emax := emax)) validExp (Exact.round_mode ctx rounding)
    validRound _ _ secondGeneric upper
  apply Raux.Rabs_lt ctx
  constructor
  · have strict := RIneq.Ropp_lt_contravar ctx _ _
      (bounded_lt_emax (prec := prec) (emax := emax) ctx first firstExp firstBounded)
    change Exact.Rlt ctx (Exact.Ropp ctx (Exact.bpow ctx radix2 emax))
      (Exact.Ropp ctx (Exact.F2R ctx (Float radix2 (Zpos first) firstExp))) at strict
    have opposite : Exact.F2R ctx (Float radix2 (Zopp (Zpos first)) firstExp) =
        Exact.Ropp ctx (Exact.F2R ctx (Float radix2 (Zpos first) firstExp)) :=
      Float_prop.F2R_Zopp ctx radix2 (Zpos first) firstExp
    rw [← opposite] at strict
    exact RIneq.Rlt_le_trans ctx _ _ _ strict roundedLower
  · exact RIneq.Rle_lt_trans ctx _ _ _ roundedUpper
      (bounded_lt_emax (prec := prec) (emax := emax) ctx second secondExp secondBounded)

theorem sign_plus_overflow :
    ∀ {prec emax : Z} (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
      [FLX.Prec_gt_0 prec],
      sign_plus_overflowStatement (prec := prec) (emax := emax) ctx magnitude := by
  intro prec emax ctx magnitude precision rounding firstSign first firstExp
    secondSign second secondExp firstBounded secondBounded
  dsimp only
  intro overflow
  cases firstSign <;> cases secondSign
  · refine ⟨?_, rfl⟩
    symm
    apply Raux.Rlt_bool_false ctx
    have strict := RIneq.Rplus_lt_compat ctx _ _ _ _
      (manual_positive_value ctx first firstExp) (manual_positive_value ctx second secondExp)
    change ctx.spec.lt (ctx.spec.add ctx.spec.zero ctx.spec.zero) _ at strict
    rw [ctx.certificate.orderedField.add_zero] at strict
    exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp strict |>.1
  · have strict := manual_mixed_sum_bounded ctx magnitude rounding second first
      secondExp firstExp secondBounded firstBounded
    change ctx.spec.le _ (ctx.spec.abs (Exact.round magnitude radix2
      (fexp (prec := prec) (emax := emax)) (Exact.round_mode ctx rounding)
        (ctx.spec.add _ _))) at overflow
    rw [ctx.certificate.orderedField.add_comm] at overflow
    exact False.elim (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp strict).2 overflow)
  · have strict := manual_mixed_sum_bounded ctx magnitude rounding first second
      firstExp secondExp firstBounded secondBounded
    exact False.elim (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp strict).2 overflow)
  · refine ⟨?_, rfl⟩
    symm
    apply Raux.Rlt_bool_true ctx
    have strict := RIneq.Rplus_lt_compat ctx _ _ _ _
      (manual_negative_value ctx first firstExp) (manual_negative_value ctx second secondExp)
    change ctx.spec.lt _ (ctx.spec.add ctx.spec.zero ctx.spec.zero) at strict
    rw [ctx.certificate.orderedField.add_zero] at strict
    exact strict

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals

private theorem manual_choice_correct (ctx : ExactRealContext) (rounding : mode)
    (value : Exact.R ctx) (mantissa : Z) (place : location)
    (bracket : Calc.Bracket.inbetween_int ctx mantissa (Exact.Rabs ctx value) place) :
    Exact.round_mode ctx rounding value =
      cond_Zopp (Exact.Rlt_bool ctx value (Exact.R0 ctx))
        (choice_mode rounding (Exact.Rlt_bool ctx value (Exact.R0 ctx)) mantissa place) := by
  cases rounding
  · have nearest := Calc.Round.inbetween_int_N_sign ctx
      (fun integer => !Zeven integer) value mantissa place bracket
    have parity : Zeven (Zopp (Zadd mantissa Zone)) = !Zeven mantissa := by
      change ZArith.BinInt.Z.even (ZArith.BinInt.Z.opp
        (ZArith.BinInt.Z.add mantissa Zone)) = _
      rw [ZArith.BinInt.Z.even_opp, ZArith.BinInt.Z.even_add]
      change CompCert4Lean.Foundation.Logic.Rocq.Coq.Bool.Bool.eqb (Zeven mantissa) false = _
      cases Zeven mantissa <;> rfl
    change Exact.round_mode ctx mode_NE value =
      cond_Zopp (Exact.Rlt_bool ctx value (Exact.R0 ctx))
        (cond_incr (round_N
          (if Exact.Rlt_bool ctx value (Exact.R0 ctx) then
            !(!(Zeven (Zopp (Zadd mantissa Zone)))) else !Zeven mantissa) place) mantissa)
      at nearest
    rw [parity] at nearest
    simpa only [Bool.not_not, ite_self, choice_mode] using nearest
  · exact Calc.Round.inbetween_int_ZR_sign ctx value mantissa place bracket
  · exact Calc.Round.inbetween_int_DN_sign ctx value mantissa place bracket
  · exact Calc.Round.inbetween_int_UP_sign ctx value mantissa place bracket
  · exact Calc.Round.inbetween_int_NA_sign ctx value mantissa place bracket

private theorem manual_choice_ge (rounding : mode) (sign : Bool)
    (mantissa : Z) (place : location) :
    Zle mantissa (choice_mode rounding sign mantissa place) := by
  have increased : Zle mantissa (Zadd mantissa Zone) := by
    change intOfZ mantissa ≤ intOfZ (ZArith.BinInt.Z.add mantissa Zone)
    simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
    change intOfZ mantissa ≤ intOfZ mantissa + 1
    omega
  cases rounding <;> simp only [choice_mode, cond_incr, Calc.Round.cond_incr]
  all_goals first | exact Int.le_refl _ | split <;> first | exact increased | exact Int.le_refl _

private theorem manual_bracket_nonnegative (ctx : ExactRealContext)
    (value : Exact.R ctx) (mantissa exponent : Z) (place : location)
    (nonnegative : Exact.Rle ctx (Exact.R0 ctx) value)
    (bracket : Calc.Bracket.inbetween_float ctx radix2 mantissa exponent value place) :
    Zle Z0 mantissa := by
  have bound := (Calc.Bracket.inbetween_float_bounds ctx radix2 value
    mantissa exponent place bracket).2
  have positive := RIneq.Rle_lt_trans ctx _ _ _ nonnegative bound
  have integerPositive := Float_prop.gt_0_F2R ctx radix2 (Zadd mantissa Zone) exponent positive
  change (0 : Int) < intOfZ (ZArith.BinInt.Z.add mantissa Zone) at integerPositive
  simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt] at integerPositive
  change (0 : Int) ≤ intOfZ mantissa
  change (0 : Int) < intOfZ mantissa + 1 at integerPositive
  omega

private theorem manual_abs_positive (ctx : ExactRealContext) (value : Exact.R ctx)
    (nonzero : value ≠ Exact.R0 ctx) :
    Exact.Rlt ctx (Exact.R0 ctx) (Exact.Rabs ctx value) := by
  have nonzero' : value ≠ ctx.spec.ofZ Z0 := by
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact nonzero
  have positive := Rbasic_fun.Rabs_pos_lt ctx value nonzero'
  change ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.abs value) at positive
  rw [ctx.certificate.sourceLaws.ofZ_zero] at positive
  exact positive

private theorem manual_signed_absolute (ctx : ExactRealContext) (sign : Bool)
    (mantissa exponent : Z) (nonnegative : Zle Z0 mantissa) :
    Exact.Rabs ctx (Exact.F2R ctx (Float radix2 (cond_Zopp sign mantissa) exponent)) =
      Exact.F2R ctx (Float radix2 mantissa exponent) := by
  have absolute : Zabs mantissa = mantissa := by
    apply intOfZ_injective
    change intOfZ (zOfInt (intOfZ mantissa).natAbs) = intOfZ mantissa
    rw [intOfZ_zOfInt]
    exact Int.natAbs_of_nonneg nonnegative
  have signed : Zabs (cond_Zopp sign mantissa) = mantissa :=
    (Zaux.abs_cond_Zopp sign mantissa).trans absolute
  have identity : Exact.F2R ctx (Float radix2 (Zabs (cond_Zopp sign mantissa)) exponent) =
      Exact.Rabs ctx (Exact.F2R ctx (Float radix2 (cond_Zopp sign mantissa) exponent)) :=
    Float_prop.F2R_Zabs ctx radix2 (cond_Zopp sign mantissa) exponent
  rw [signed] at identity
  exact identity.symm

private theorem manual_cexp_float (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (exponentFunction : Z → Z) (mantissa exponent : Z) (nonzero : mantissa ≠ Z0) :
    Exact.cexp magnitude radix2 exponentFunction
      (Exact.F2R ctx (Float radix2 mantissa exponent)) =
      exponentFunction (Zadd (Zdigits radix2 mantissa) exponent) := by
  change exponentFunction (Float_prop.Exact.mag magnitude radix2
    (Float_prop.Exact.F2R ctx (Float radix2 mantissa exponent))) = _
  rw [Float_prop.mag_F2R_Zdigits ctx magnitude radix2 mantissa exponent nonzero]

private theorem manual_canonical_mantissa {prec emax : Z}
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (mantissa : positive) (exponent : Z)
    (canonical : exponent = Exact.cexp magnitude radix2 (fexp (prec := prec) (emax := emax))
      (Exact.F2R ctx (Float radix2 (Zpos mantissa) exponent))) :
    canonical_mantissa (prec := prec) (emax := emax) mantissa exponent = true := by
  rw [manual_cexp_float ctx magnitude _ _ _ (by intro impossible; cases impossible)] at canonical
  change Zeq_bool (fexp0 prec emax
    (Zadd (Digits.Zpos (Digits.digits2_pos mantissa)) exponent)) exponent = true
  rw [Digits.Zpos_digits2_pos]
  apply Zaux.Zeq_bool_true
  exact canonical.symm

private theorem manual_signed_float_eq (ctx : ExactRealContext) (sign : Bool)
    (first firstExp second secondExp : Z)
    (same : Exact.F2R ctx (Float radix2 first firstExp) =
      Exact.F2R ctx (Float radix2 second secondExp)) :
    Exact.F2R ctx (Float radix2 (cond_Zopp sign first) firstExp) =
      Exact.F2R ctx (Float radix2 (cond_Zopp sign second) secondExp) := by
  change Float_prop.Exact.F2R ctx (Float radix2 (cond_Zopp sign first) firstExp) =
    Float_prop.Exact.F2R ctx (Float radix2 (cond_Zopp sign second) secondExp)
  rw [Float_prop.F2R_cond_Zopp, Float_prop.F2R_cond_Zopp]
  exact congrArg (Raux.Exact.cond_Ropp ctx sign) same

theorem binary_round_aux_correct' :
    ∀ {prec emax : Z} (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
      [FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax],
      binary_round_aux_correct'Statement (prec := prec) (emax := emax) ctx magnitude := by
  intro prec emax ctx magnitude precision exponentLimit rounding value mantissa exponent place
    nonzero bracket exponentBound
  have validExp : Valid_exp (fexp (prec := prec) (emax := emax)) :=
    FLT.FLT_exp_valid (emin (prec := prec) (emax := emax)) prec (h := precision)
  have validRound := valid_rnd_round_mode_proof ctx rounding
  have absPositive := manual_abs_positive ctx value nonzero
  have absNonnegative := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp absPositive |>.1
  have mantissaNonnegative := manual_bracket_nonnegative ctx _ _ _ _ absNonnegative bracket
  have absExponent : Exact.cexp magnitude radix2 (fexp (prec := prec) (emax := emax))
      (Exact.Rabs ctx value) = Exact.cexp magnitude radix2 (fexp (prec := prec) (emax := emax)) value :=
    Generic_fmt.cexp_abs ctx magnitude radix2 _ value
  have absExponentBound : Zle exponent
      (Exact.cexp magnitude radix2 (fexp (prec := prec) (emax := emax)) (Exact.Rabs ctx value)) := by
    rw [absExponent]
    exact exponentBound
  have firstData := Calc.Round.truncate_correct_partial' ctx magnitude radix2
    (fexp (prec := prec) (emax := emax)) validExp (Exact.Rabs ctx value)
    mantissa exponent place absPositive bracket absExponentBound
  have firstRound := Calc.Round.round_trunc_sign_any_correct' ctx magnitude radix2
    (fexp (prec := prec) (emax := emax)) validExp (Exact.round_mode ctx rounding)
    validRound (choice_mode rounding) (manual_choice_correct ctx rounding)
    value mantissa exponent place bracket (Or.inl exponentBound)
  have firstShift := shr_fexp_truncate (prec := prec) (emax := emax)
    mantissa exponent place mantissaNonnegative
  dsimp only at firstShift
  rcases firstTrunc : Calc.Round.truncate radix2 (fexp (prec := prec) (emax := emax))
      ((mantissa, exponent), place) with ⟨⟨firstMantissa, firstExp⟩, firstPlace⟩
  rw [firstTrunc] at firstData firstRound firstShift
  dsimp only at firstData firstRound firstShift
  have firstExponent : firstExp = Exact.cexp magnitude radix2
      (fexp (prec := prec) (emax := emax)) value := firstData.2.trans absExponent
  have firstNonnegative := manual_bracket_nonnegative ctx _ _ _ _ absNonnegative firstData.1
  let selected := choice_mode rounding (Exact.Rlt_bool ctx value (Exact.R0 ctx)) firstMantissa firstPlace
  have selectedNonnegative : Zle Z0 selected :=
    Int.le_trans firstNonnegative (manual_choice_ge rounding _ firstMantissa firstPlace)
  have roundedValue : Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
      (Exact.round_mode ctx rounding) value =
      Exact.F2R ctx (Float radix2 (cond_Zopp (Exact.Rlt_bool ctx value (Exact.R0 ctx)) selected) firstExp) :=
    firstRound
  have absoluteValue : Exact.Rabs ctx
      (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
        (Exact.round_mode ctx rounding) value) = Exact.F2R ctx (Float radix2 selected firstExp) := by
    rw [roundedValue]
    exact manual_signed_absolute ctx _ _ _ selectedNonnegative
  have secondShift := shr_fexp_truncate (prec := prec) (emax := emax)
    selected firstExp loc_Exact selectedNonnegative
  dsimp only at secondShift
  unfold binary_round_aux
  rw [firstShift]
  dsimp only
  rw [shr_m_shr_record_of_loc, loc_of_shr_record_of_loc]
  change valid_binary (prec := prec) (emax := emax)
      (let result := shr_fexp (prec := prec) (emax := emax) selected firstExp loc_Exact
       match shr_m result.1 with
       | .Z0 => S754_zero (Exact.Rlt_bool ctx value (Exact.R0 ctx))
       | .Zpos positiveMantissa => binary_fit_aux (prec := prec) (emax := emax)
           rounding (Exact.Rlt_bool ctx value (Exact.R0 ctx)) positiveMantissa result.2
       | .Zneg _ => S754_nan) = true ∧ _
  rw [secondShift]
  have absoluteZero : Exact.Rabs ctx (Exact.R0 ctx) = Exact.R0 ctx :=
    ctx.certificate.sourceLaws.abs_nonnegative _ (ctx.certificate.orderedField.le_refl _)
  cases selectedEq : selected with
  | Z0 =>
      rw [selectedEq] at secondShift roundedValue absoluteValue
      have zeroTrunc := Calc.Round.truncate_0 radix2 (fexp (prec := prec) (emax := emax)) firstExp loc_Exact
      rcases secondTrunc : Calc.Round.truncate radix2 (fexp (prec := prec) (emax := emax))
          ((Z0, firstExp), loc_Exact) with ⟨⟨secondMantissa, secondExp⟩, secondPlace⟩
      rw [secondTrunc] at zeroTrunc
      dsimp only at zeroTrunc
      rw [zeroTrunc]
      dsimp only
      rw [shr_m_shr_record_of_loc Z0 secondPlace]
      have signedZero : cond_Zopp (Exact.Rlt_bool ctx value (Exact.R0 ctx)) Z0 = Z0 := by
        cases Exact.Rlt_bool ctx value (Exact.R0 ctx) <;> rfl
      rw [signedZero] at roundedValue
      have zeroValue : Exact.F2R ctx (Float radix2 Z0 firstExp) = Exact.R0 ctx :=
        Float_prop.F2R_0 ctx radix2 firstExp
      rw [zeroValue] at roundedValue
      rw [roundedValue, absoluteZero]
      have small : Exact.Rlt_bool ctx (Exact.R0 ctx) (Exact.bpow ctx radix2 emax) = true :=
        Raux.Rlt_bool_true ctx _ _ (Raux.bpow_gt_0 ctx radix2 emax)
      simp only [small, if_true]
      exact ⟨rfl, rfl, rfl, rfl⟩
  | Zpos selectedMantissa =>
      rw [selectedEq] at roundedValue absoluteValue secondShift
      have selectedNotZero : Zpos selectedMantissa ≠ Z0 := by intro impossible; cases impossible
      have signedNotZero : cond_Zopp (Exact.Rlt_bool ctx value (Exact.R0 ctx))
          (Zpos selectedMantissa) ≠ Z0 := by
        intro impossible
        have absolute := Zaux.abs_cond_Zopp (Exact.Rlt_bool ctx value (Exact.R0 ctx))
          (Zpos selectedMantissa)
        change Zabs (cond_Zopp _ (Zpos selectedMantissa)) = Zabs (Zpos selectedMantissa) at absolute
        rw [impossible] at absolute
        have integerEq := congrArg intOfZ absolute
        change intOfZ (zOfInt (intOfZ Z0).natAbs) =
          intOfZ (zOfInt (intOfZ (Zpos selectedMantissa)).natAbs) at integerEq
        simp only [intOfZ_zOfInt] at integerEq
        change (0 : Int) = (posToNat selectedMantissa : Int) at integerEq
        have positive := posToNat_positive selectedMantissa
        omega
      have roundedNonzero : Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx rounding) value ≠ Exact.R0 ctx := by
        rw [roundedValue]
        exact Float_prop.F2R_neq_0 ctx radix2 _ signedNotZero
      have roundedExponent : Exact.cexp magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.Rabs ctx (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
            (Exact.round_mode ctx rounding) value)) =
          Exact.cexp magnitude radix2 (fexp (prec := prec) (emax := emax))
            (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
              (Exact.round_mode ctx rounding) value) :=
        Generic_fmt.cexp_abs ctx magnitude radix2 _ _
      have selectedExponent : Zle firstExp (fexp (prec := prec) (emax := emax)
          (Zadd (Zdigits radix2 (Zpos selectedMantissa)) firstExp)) := by
        rw [← manual_cexp_float ctx magnitude (fexp (prec := prec) (emax := emax))
          (Zpos selectedMantissa) firstExp selectedNotZero,
          ← absoluteValue, roundedExponent, firstExponent]
        exact Generic_fmt.cexp_round_ge ctx magnitude radix2 _ validExp
          (FLT.FLT_exp_monotone (emin (prec := prec) (emax := emax)) prec)
          _ validRound value roundedNonzero
      have formatted : Exact.generic_format magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.F2R ctx (Float radix2 (Zpos selectedMantissa) firstExp)) := by
        rw [← absoluteValue]
        exact Generic_fmt.generic_format_abs ctx magnitude radix2 _ _
          (Generic_fmt.generic_format_round ctx magnitude radix2 _ validExp _ validRound value)
      have secondData := Calc.Round.truncate_correct_format ctx magnitude radix2
        (fexp (prec := prec) (emax := emax)) (Zpos selectedMantissa) firstExp
        selectedNotZero formatted selectedExponent
      rcases secondTrunc : Calc.Round.truncate radix2 (fexp (prec := prec) (emax := emax))
          ((Zpos selectedMantissa, firstExp), loc_Exact) with ⟨⟨secondMantissa, secondExp⟩, secondPlace⟩
      rw [secondTrunc] at secondData
      dsimp only at secondData
      have secondValue : Exact.F2R ctx (Float radix2 (Zpos selectedMantissa) firstExp) =
          Exact.F2R ctx (Float radix2 secondMantissa secondExp) := secondData.1
      have secondPositive : Zlt Z0 secondMantissa := by
        apply Float_prop.gt_0_F2R ctx radix2 secondMantissa secondExp
        change Exact.Rlt ctx (Exact.R0 ctx) (Exact.F2R ctx (Float radix2 secondMantissa secondExp))
        rw [← secondValue]
        exact Float_prop.F2R_gt_0 ctx radix2 _
          (Int.natCast_pos.mpr (posToNat_positive selectedMantissa))
      cases secondMantissa with
      | Z0 => exact False.elim (Int.lt_irrefl 0 secondPositive)
      | Zneg negativeMantissa =>
          change (0 : Int) < -(posToNat negativeMantissa : Int) at secondPositive
          omega
      | Zpos positiveMantissa =>
          dsimp only
          rw [shr_m_shr_record_of_loc (Zpos positiveMantissa) secondPlace]
          have canonical : secondExp = Exact.cexp magnitude radix2
              (fexp (prec := prec) (emax := emax))
              (Exact.F2R ctx (Float radix2 (Zpos positiveMantissa) secondExp)) :=
            secondData.2.trans (congrArg (Exact.cexp magnitude radix2
              (fexp (prec := prec) (emax := emax))) secondData.1)
          have resultValue := roundedValue.trans (manual_signed_float_eq ctx _ _ _ _ _ secondData.1)
          have fitted := binary_fit_aux_correct (prec := prec) (emax := emax) ctx rounding
            (Exact.Rlt_bool ctx value (Exact.R0 ctx)) positiveMantissa secondExp
            (manual_canonical_mantissa ctx magnitude positiveMantissa secondExp canonical)
          dsimp only [Exact.SF2R] at fitted
          rw [← resultValue] at fitted
          exact fitted
  | Zneg negativeMantissa =>
      rw [selectedEq] at selectedNonnegative
      change (0 : Int) ≤ -(posToNat negativeMantissa : Int) at selectedNonnegative
      have positive := posToNat_positive negativeMantissa
      omega

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals

theorem binary_round_aux_correct :
    ∀ {prec emax : Z} (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
      [FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax],
      binary_round_aux_correctStatement (prec := prec) (emax := emax) ctx magnitude := by
  intro prec emax ctx magnitude precision exponentLimit rounding value mantissa exponent place
    bracket exponentBound
  have validExp : Valid_exp (fexp (prec := prec) (emax := emax)) :=
    FLT.FLT_exp_valid (emin (prec := prec) (emax := emax)) prec (h := precision)
  have absPositive : Exact.Rlt ctx (Exact.R0 ctx) (Exact.Rabs ctx value) :=
    RIneq.Rlt_le_trans ctx _ _ _ (manual_positive_value ctx mantissa exponent)
      (Calc.Bracket.inbetween_float_bounds ctx radix2 _ _ _ _ bracket).1
  have nonzero : value ≠ Exact.R0 ctx := by
    intro zero
    have absZero : Exact.Rabs ctx (Exact.R0 ctx) = Exact.R0 ctx :=
      ctx.certificate.sourceLaws.abs_nonnegative _ (ctx.certificate.orderedField.le_refl _)
    rw [zero, absZero] at absPositive
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp absPositive).2
      (ctx.certificate.orderedField.le_refl _)
  apply binary_round_aux_correct' ctx magnitude rounding value (Zpos mantissa) exponent place
    nonzero bracket
  have exactExponent : Exact.cexp magnitude radix2 (fexp (prec := prec) (emax := emax))
      (Exact.Rabs ctx value) = fexp (prec := prec) (emax := emax)
        (Zadd (Zdigits radix2 (Zpos mantissa)) exponent) :=
    Calc.Round.cexp_inbetween_float ctx magnitude radix2 _ validExp _ _ _ _
      absPositive bracket (Or.inr exponentBound)
  have absExponent : Exact.cexp magnitude radix2 (fexp (prec := prec) (emax := emax))
      (Exact.Rabs ctx value) = Exact.cexp magnitude radix2 (fexp (prec := prec) (emax := emax)) value :=
    Generic_fmt.cexp_abs ctx magnitude radix2 _ value
  rw [← absExponent, exactExponent]
  exact exponentBound

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_float_sign (ctx : ExactRealContext) (sign : Bool)
    (mantissa : positive) (exponent : Z) :
    Exact.Rlt_bool ctx (Exact.F2R ctx (Float radix2 (cond_Zopp sign (Zpos mantissa)) exponent))
      (Exact.R0 ctx) = sign := by
  cases sign
  · exact Raux.Rlt_bool_false ctx _ _
      ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
        (manual_positive_value ctx mantissa exponent)).1
  · exact Raux.Rlt_bool_true ctx _ _ (manual_negative_value ctx mantissa exponent)

theorem binary_round_correct :
    ∀ {prec emax : Z} (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
      [FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax],
      binary_round_correctStatement (prec := prec) (emax := emax) ctx magnitude := by
  intro prec emax ctx magnitude precision exponentLimit rounding sign mantissa exponent
  have alignment := shl_align_fexp_correct (prec := prec) (emax := emax) ctx mantissa exponent
  unfold binary_round
  rcases aligned : shl_align_fexp (prec := prec) (emax := emax) mantissa exponent with
    ⟨alignedMantissa, alignedExp⟩
  rw [aligned] at alignment
  dsimp only at alignment ⊢
  have bracket : Calc.Bracket.inbetween_float ctx radix2 (Zpos alignedMantissa) alignedExp
      (Exact.Rabs ctx (Exact.F2R ctx (Float radix2 (cond_Zopp sign (Zpos mantissa)) exponent)))
      loc_Exact := by
    apply Calc.Bracket.inbetween_Exact
    exact (manual_signed_absolute ctx sign (Zpos mantissa) exponent
      (Int.le_of_lt (Int.natCast_pos.mpr (posToNat_positive mantissa)))).trans alignment.1
  have rounded := binary_round_aux_correct (prec := prec) (emax := emax) ctx magnitude rounding
    (Exact.F2R ctx (Float radix2 (cond_Zopp sign (Zpos mantissa)) exponent))
    alignedMantissa alignedExp loc_Exact bracket alignment.2
  dsimp only at rounded
  rw [manual_float_sign ctx sign mantissa exponent] at rounded
  exact rounded

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_round_zero {prec emax : Z}
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) (rounding : mode) :
    Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
      (Exact.round_mode ctx rounding) (Exact.R0 ctx) = Exact.R0 ctx :=
  Generic_fmt.round_0 ctx magnitude radix2 _ _ (valid_rnd_round_mode_proof ctx rounding)

private theorem manual_zero_small (ctx : ExactRealContext) (exponent : Z) :
    Exact.Rlt_bool ctx (Exact.Rabs ctx (Exact.R0 ctx)) (Exact.bpow ctx radix2 exponent) = true := by
  have absoluteZero : Exact.Rabs ctx (Exact.R0 ctx) = Exact.R0 ctx :=
    ctx.certificate.sourceLaws.abs_nonnegative _ (ctx.certificate.orderedField.le_refl _)
  rw [absoluteZero]
  exact Raux.Rlt_bool_true ctx _ _ (Raux.bpow_gt_0 ctx radix2 exponent)

private theorem manual_round_as_binary {prec emax : Z}
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    [FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (rounding : mode) (sign : Bool) (mantissa : positive) (exponent : Z) :
    let value := Exact.F2R ctx (Float radix2 (cond_Zopp sign (Zpos mantissa)) exponent)
    let result := SF2B (prec := prec) (emax := emax)
      (binary_round (prec := prec) (emax := emax) rounding sign mantissa exponent)
    if Exact.Rlt_bool ctx
      (Exact.Rabs ctx (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
        (Exact.round_mode ctx rounding) value)) (Exact.bpow ctx radix2 emax) then
      Exact.B2R ctx result = Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
        (Exact.round_mode ctx rounding) value ∧ is_finite result = true ∧ Bsign result = sign
    else B2SF result = binary_overflow (prec := prec) (emax := emax) rounding sign := by
  have rounded := binary_round_correct (prec := prec) (emax := emax) ctx magnitude rounding sign mantissa exponent
  dsimp only at rounded ⊢
  have fields := rounded.2
  split <;> rename_i condition
  · rw [if_pos condition] at fields
    exact ⟨(B2R_SF2B ctx _ rounded.1).trans fields.1,
      (is_finite_SF2B _ rounded.1).trans fields.2.1,
      (Bsign_SF2B _ rounded.1).trans fields.2.2⟩
  · rw [if_neg condition] at fields
    exact (B2SF_SF2B _ rounded.1).trans fields

theorem binary_normalize_correct :
    ∀ {prec emax : Z} (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
      [FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax],
      binary_normalize_correctStatement (prec := prec) (emax := emax) ctx magnitude := by
  intro prec emax ctx magnitude precision exponentLimit rounding mantissa exponent zeroSign
  dsimp only
  cases mantissa with
  | Z0 =>
      have zeroValue : Exact.F2R ctx (Float radix2 Z0 exponent) = Exact.R0 ctx :=
        Float_prop.F2R_0 ctx radix2 exponent
      rw [zeroValue, manual_round_zero ctx magnitude rounding, manual_zero_small ctx emax]
      have compared : Exact.Rcompare ctx (Exact.R0 ctx) (Exact.R0 ctx) = Eq :=
        Raux.Rcompare_Eq ctx _ _ rfl
      rw [compared]
      exact ⟨rfl, rfl, rfl⟩
  | Zpos positiveMantissa =>
      have rounded := manual_round_as_binary (prec := prec) (emax := emax)
        ctx magnitude rounding false positiveMantissa exponent
      have compared : Exact.Rcompare ctx (Exact.F2R ctx (Float radix2 (Zpos positiveMantissa) exponent))
          (Exact.R0 ctx) = Gt :=
        Raux.Rcompare_Gt ctx _ _ (manual_positive_value ctx positiveMantissa exponent)
      have signed : Exact.Rlt_bool ctx (Exact.F2R ctx (Float radix2 (Zpos positiveMantissa) exponent))
          (Exact.R0 ctx) = false := manual_float_sign ctx false positiveMantissa exponent
      rw [compared, signed]
      exact rounded
  | Zneg negativeMantissa =>
      have opposite : cond_Zopp true (Zpos negativeMantissa) = Zneg negativeMantissa := by
        apply intOfZ_injective
        change intOfZ (zOfInt (-(posToNat negativeMantissa : Int))) = -(posToNat negativeMantissa : Int)
        exact intOfZ_zOfInt _
      have rounded := manual_round_as_binary (prec := prec) (emax := emax)
        ctx magnitude rounding true negativeMantissa exponent
      dsimp only at rounded
      rw [opposite] at rounded
      have compared : Exact.Rcompare ctx (Exact.F2R ctx (Float radix2 (Zneg negativeMantissa) exponent))
          (Exact.R0 ctx) = Lt := by
        rw [← opposite]
        exact Raux.Rcompare_Lt ctx _ _ (manual_negative_value ctx negativeMantissa exponent)
      have signed : Exact.Rlt_bool ctx (Exact.F2R ctx (Float radix2 (Zneg negativeMantissa) exponent))
          (Exact.R0 ctx) = true := by
        rw [← opposite]
        exact manual_float_sign ctx true negativeMantissa exponent
      rw [compared, signed]
      exact rounded

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN

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
  have increased := manual_choice_ge rounding sign (shr_m first.1) (loc_of_shr_record first.1)
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
    ∀ {prec emax : Z} [FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax],
      binary_normalize_result_obligation (prec := prec) (emax := emax) := by
  intro prec emax precision exponentLimit rounding mantissa exponent zeroSign
  exact binary_single_normalize_valid rounding mantissa exponent zeroSign

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN
