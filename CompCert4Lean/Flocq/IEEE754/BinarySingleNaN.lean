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
    [Core.FLX.Prec_gt_0Class prec] [Prec_lt_emax prec emax] : Prop where
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

def binary_normalize [Core.FLX.Prec_gt_0Class prec] [Prec_lt_emax prec emax]
    (m : mode) (x : Z) (e : Z) (szero : Bool) : binary_float prec emax :=
  match x with
  | .Z0 => .B754_zero szero
  | .Zpos p => SF2B (prec := prec) (emax := emax)
      (binary_round (prec := prec) (emax := emax) m false p e)
  | .Zneg p => SF2B (prec := prec) (emax := emax)
      (binary_round (prec := prec) (emax := emax) m true p e)

def binary_normalize_result_obligation
    [Core.FLX.Prec_gt_0Class prec] [Prec_lt_emax prec emax] : Prop :=
  ∀ (m : mode) (x e : Z) (szero : Bool),
    BinaryFloatCertificate
      (binary_normalize (prec := prec) (emax := emax) m x e szero)

def Fplus_naive (sx : Bool) (mx : positive) (ex : Z)
    (sy : Bool) (my : positive) (ey ez : Z) : Z :=
  let m1 := shl_align mx ex ez
  let m2 := shl_align my ey ez
  Zadd (cond_Zopp sx (Zpos m1.1)) (cond_Zopp sy (Zpos m2.1))

def Bmult [Core.FLX.Prec_gt_0Class prec] [Prec_lt_emax prec emax]
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

def Bplus [Core.FLX.Prec_gt_0Class prec] [Prec_lt_emax prec emax]
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

def Bminus [Core.FLX.Prec_gt_0Class prec] [Prec_lt_emax prec emax]
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

def Bdiv [Core.FLX.Prec_gt_0Class prec] [Prec_lt_emax prec emax]
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

def Bsqrt [Core.FLX.Prec_gt_0Class prec] [Prec_lt_emax prec emax]
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

def round (magnitude : Magnitude ctx) (beta : radix) (fexp : Z → Z)
    (rnd : R ctx → Z) (x : R ctx) : R ctx :=
  F2R ctx
    (Float beta (rnd (scaled_mantissa magnitude beta fexp x))
      (cexp magnitude beta fexp x))

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

structure Valid_rnd (ctx : Context) (rnd : R ctx → Z) : Prop where
  Zrnd_le : ∀ x y : R ctx, Rle ctx x y → Zle (rnd x) (rnd y)
  Zrnd_IZR : ∀ n : Z, rnd (IZR ctx n) = n

end Exact

def valid_rnd_round_mode (ctx : ExactRealContext) : Prop :=
  ∀ m : mode, Exact.Valid_rnd ctx (Exact.round_mode ctx m)

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
    [Core.FLX.Prec_gt_0Class prec] [Prec_lt_emax prec emax] : Prop :=
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
    [Core.FLX.Prec_gt_0Class prec] [Prec_lt_emax prec emax] : Prop :=
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
    [Core.FLX.Prec_gt_0Class prec] [Prec_lt_emax prec emax] : Prop :=
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
    [Core.FLX.Prec_gt_0Class prec] [Prec_lt_emax prec emax] : Prop :=
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
    [Core.FLX.Prec_gt_0Class prec] [Prec_lt_emax prec emax] : Prop :=
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
    [Core.FLX.Prec_gt_0Class prec] [Prec_lt_emax prec emax] : Prop :=
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
    [Core.FLX.Prec_gt_0Class prec] [Prec_lt_emax prec emax] : Prop :=
  ∀ (m : mode) (mx : positive) (ex : Z)
    (_Hx : bounded (prec := prec) (emax := emax) mx ex = true),
    let x := Exact.F2R ctx (Float radix2 (Zpos mx) ex)
    let z :=
      let (pair, lz) := SFsqrt_core_binary prec emax (Zpos mx) ex
      binary_round_aux (prec := prec) (emax := emax) m false pair.1 pair.2 lz
    valid_binary (prec := prec) (emax := emax) z = true ∧
    Exact.SF2R ctx radix2 z =
      Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
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
    [Core.FLX.Prec_gt_0Class prec]
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
    (magnitude : Exact.Magnitude ctx) [Core.FLX.Prec_gt_0Class prec]
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

def binary_overflow_correctStatement [Core.FLX.Prec_gt_0Class prec]
    [Prec_lt_emax prec emax] : Prop :=
  ∀ (m : mode) (s : Bool),
    valid_binary (prec := prec) (emax := emax)
      (binary_overflow (prec := prec) (emax := emax) m s) = true

def binary_round_aux_correctStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) [Core.FLX.Prec_gt_0Class prec]
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
    (magnitude : Exact.Magnitude ctx) [Core.FLX.Prec_gt_0Class prec]
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
    (magnitude : Exact.Magnitude ctx) [Core.FLX.Prec_gt_0Class prec]
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
    (magnitude : Exact.Magnitude ctx) [Core.FLX.Prec_gt_0Class prec]
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

def fexp_emaxStatement [Core.FLX.Prec_gt_0Class prec] [Prec_lt_emax prec emax] : Prop :=
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

def is_nan_binary_normalizeStatement [Core.FLX.Prec_gt_0Class prec]
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

def shr_fexp_truncateStatement [Core.FLX.Prec_gt_0Class prec] : Prop :=
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
    (magnitude : Exact.Magnitude ctx) [Core.FLX.Prec_gt_0Class prec] : Prop :=
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
