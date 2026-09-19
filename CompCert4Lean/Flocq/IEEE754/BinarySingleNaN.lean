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
