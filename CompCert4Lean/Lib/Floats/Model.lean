import Std
import Init.Data.Float.Model.Format.Basic
import Init.Data.Float.Model.Unpacked.Basic
import Init.Data.Float.Model.Unpacked.Pack.Basic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.FlocqReal

/- Pinned Lean 4.33 sources authenticated against the Gate 2 bundle:
   Format.Basic       1e0dbd99de769af969ded5aa41c34ef30de090a2e06292a5c7a17da6f9340f34
   Unpacked.Basic     ff0736240d209840ed078bb8b64df6110aa9250712ba37565cca85fcb9af5881
   Unpacked.Pack.Basic ac7989ba723dc7fc93337db82a0819ceee01a4f4a8ed0bd88ce9baaeedbef44a -/

/-!
# CompCert floating-point specification model

This is the source-shaped adapter for the declarations exported by
`Coq.Floats.SpecFloat`.  The executable carrier used by the checked float
model remains Lean's pinned `Float.Model` carrier; this module supplies the
Rocq names and arithmetic facade consumed by the translated Flocq modules.
-/

namespace CompCert4Lean.Lib.Floats.Model

open CompCert4Lean.Foundation
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

namespace Rocq.Coq.Floats.SpecFloat

abbrev positive := CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive
abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
abbrev comparison := CompCert4Lean.Foundation.Numbers.Rocq.Coq.comparison

abbrev Lt : comparison := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Lt
abbrev Eq : comparison := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Eq
abbrev Gt : comparison := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Gt

abbrev z0 : Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0
abbrev zpos : positive → Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
abbrev zneg : positive → Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg

abbrev zadd := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
abbrev zsub := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub
abbrev zmul := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
abbrev zopp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
abbrev zcompare := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.compare
abbrev zleBool := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.leb
abbrev zeven := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
abbrev zmin := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.min
abbrev zmax := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max
abbrev zdiv2 := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div2
abbrev zdivEucl := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl
abbrev zsqrtrem := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sqrtrem
abbrev zshiftl := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftl
abbrev shiftPos := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpower.shift_pos
abbrev posSucc := CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ
abbrev posCompare := CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.compare_cont
abbrev posToNat := CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat

private def compOpp : comparison → comparison
  | .Lt => .Gt
  | .Eq => .Eq
  | .Gt => .Lt

private abbrev zThree : Z := zpos (.xI .xH)
private abbrev zTwo : Z := zpos (.xO .xH)

/- The source `spec_float` has no NaN payload.  Raw-word payload and quieting
   are handled by the public Float facade; this type is the exact Rocq
   specification carrier. -/
inductive spec_float where
  | S754_zero (s : Bool)
  | S754_infinity (s : Bool)
  | S754_nan
  | S754_finite (s : Bool) (m : positive) (e : Z)
deriving DecidableEq

inductive location where
  | loc_Exact
  | loc_Inexact (c : comparison)
deriving DecidableEq

@[match_pattern] abbrev loc_Exact : location := location.loc_Exact
@[match_pattern] abbrev loc_Inexact (c : comparison) : location := location.loc_Inexact c

structure shr_record where
  shr_m : Z
  shr_r : Bool
  shr_s : Bool
deriving DecidableEq

abbrev shr_m (mrs : shr_record) : Z := mrs.shr_m
abbrev shr_r (mrs : shr_record) : Bool := mrs.shr_r

@[match_pattern] abbrev S754_zero (s : Bool) : spec_float := spec_float.S754_zero s
@[match_pattern] abbrev S754_infinity (s : Bool) : spec_float := spec_float.S754_infinity s
@[match_pattern] abbrev S754_nan : spec_float := spec_float.S754_nan
@[match_pattern] abbrev S754_finite (s : Bool) (m : positive) (e : Z) : spec_float :=
  spec_float.S754_finite s m e

/-! Pinned Float.Model entry points used by the executable provider. -/
abbrev Format := Float.Model.Format
abbrev UnpackedFloat := Float.Model.UnpackedFloat
abbrev Sign := Float.Model.UnpackedFloat.Sign

def unpack (spec : Format) (bits : BitVec spec.numBits) : UnpackedFloat :=
  Float.Model.UnpackedFloat.unpack spec bits

def pack (spec : Format) (value : UnpackedFloat) : BitVec spec.numBits :=
  Float.Model.UnpackedFloat.pack spec value

private def digits2_pos_impl : positive → positive
  | .xH => .xH
  | .xO p => posSucc (digits2_pos_impl p)
  | .xI p => posSucc (digits2_pos_impl p)

def digits2_pos (n : positive) : positive :=
  digits2_pos_impl n

def Zdigits2 (n : Z) : Z :=
  match n with
  | .Z0 => .Z0
  | .Zpos p => .Zpos (digits2_pos p)
  | .Zneg p => .Zpos (digits2_pos p)

def emin (prec emax : Z) : Z :=
  zsub (zsub zThree emax) prec

def fexp (prec emax e : Z) : Z :=
  zmax (zsub e prec) (emin prec emax)

def canonical_mantissa (prec emax : Z) (m : positive) (e : Z) : Bool :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool
    (fexp prec emax (zadd (zpos (digits2_pos m)) e)) e

def bounded (prec emax : Z) (m : positive) (e : Z) : Bool :=
  canonical_mantissa prec emax m e &&
    zleBool e (zsub emax prec)

def valid_binary (prec emax : Z) (x : spec_float) : Bool :=
  match x with
  | .S754_finite _ m e => bounded prec emax m e
  | _ => true

def cond_Zopp (b : Bool) (m : Z) : Z :=
  if b then zopp m else m

private def natIter {A : Type} (f : A → A) : Nat → A → A
  | 0, x => x
  | n + 1, x => natIter f n (f x)

def iter_pos {A : Type} (f : A → A) (n : positive) (x : A) : A :=
  natIter f (posToNat n) x

def shr_1 (mrs : shr_record) : shr_record :=
  let s := mrs.shr_r || mrs.shr_s
  match mrs.shr_m with
  | .Z0 => ⟨.Z0, false, s⟩
  | .Zpos .xH => ⟨.Z0, true, s⟩
  | .Zpos (.xO p) => ⟨.Zpos p, false, s⟩
  | .Zpos (.xI p) => ⟨.Zpos p, true, s⟩
  | .Zneg .xH => ⟨.Z0, true, s⟩
  | .Zneg (.xO p) => ⟨.Zneg p, false, s⟩
  | .Zneg (.xI p) => ⟨.Zneg p, true, s⟩

def loc_of_shr_record (mrs : shr_record) : location :=
  match mrs.shr_r, mrs.shr_s with
  | false, false => .loc_Exact
  | false, true => .loc_Inexact .Lt
  | true, false => .loc_Inexact .Eq
  | true, true => .loc_Inexact .Gt

def shr_record_of_loc (m : Z) : location → shr_record
  | .loc_Exact => ⟨m, false, false⟩
  | .loc_Inexact .Lt => ⟨m, false, true⟩
  | .loc_Inexact .Eq => ⟨m, true, false⟩
  | .loc_Inexact .Gt => ⟨m, true, true⟩

def shr (mrs : shr_record) (e n : Z) : shr_record × Z :=
  match n with
  | .Zpos p => (iter_pos shr_1 p mrs, zadd e n)
  | _ => (mrs, e)

def shr_fexp (prec emax m e : Z) (l : location) : shr_record × Z :=
  shr (shr_record_of_loc m l) e
    (zsub (fexp prec emax (zadd (Zdigits2 m) e)) e)

def shl_align (mx : positive) (ex ex' : Z) : positive × Z :=
  match zsub ex' ex with
  | .Zneg d => (shiftPos d mx, ex')
  | _ => (mx, ex)

private def new_location_even_impl (nb_steps k : Z) : location :=
  if CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool k .Z0 then
    .loc_Exact
  else
    .loc_Inexact (zcompare (zmul zTwo k) nb_steps)

private def new_location_odd_impl (nb_steps k : Z) : location :=
  if CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool k .Z0 then
    .loc_Exact
  else
    .loc_Inexact (match zcompare (zadd (zmul zTwo k) (zpos .xH)) nb_steps with
      | .Eq => .Lt
      | c => c)

def new_location_even (nb_steps k : Z) : location :=
  new_location_even_impl nb_steps k

def new_location (nb_steps k : Z) : location :=
  if zeven nb_steps then
    new_location_even nb_steps k
  else
    new_location_odd_impl nb_steps k

def SFcompare (f1 f2 : spec_float) : Option comparison :=
  match f1, f2 with
  | .S754_nan, _ | _, .S754_nan => none
  | .S754_infinity s1, .S754_infinity s2 =>
      some (if s1 then if s2 then .Eq else .Lt else if s2 then .Gt else .Eq)
  | .S754_infinity s, _ => some (if s then .Lt else .Gt)
  | _, .S754_infinity s => some (if s then .Gt else .Lt)
  | .S754_finite s _ _, .S754_zero _ => some (if s then .Lt else .Gt)
  | .S754_zero _, .S754_finite s _ _ => some (if s then .Gt else .Lt)
  | .S754_zero _, .S754_zero _ => some .Eq
  | .S754_finite s1 m1 e1, .S754_finite s2 m2 e2 =>
      some <| if s1 then
        if s2 then
          match zcompare e1 e2 with
          | .Eq => compOpp (posCompare .Eq m1 m2)
          | .Lt => .Gt
          | .Gt => .Lt
        else .Lt
      else if s2 then .Gt
      else
        match zcompare e1 e2 with
        | .Eq => posCompare .Eq m1 m2
        | c => c

def SFdiv_core_binary (prec emax m1 e1 m2 e2 : Z) : (Z × Z) × location :=
  let d1 := Zdigits2 m1
  let d2 := Zdigits2 m2
  let e' := zmin (fexp prec emax (zsub (zadd d1 e1) (zadd d2 e2))) (zsub e1 e2)
  let s := zsub (zsub e1 e2) e'
  let m' := match s with
    | .Zpos _ => zshiftl m1 s
    | .Z0 => m1
    | .Zneg _ => .Z0
  let qr := zdivEucl m' m2
  ((qr.1, e'), new_location m2 qr.2)

def SFsqrt_core_binary (prec emax m e : Z) : (Z × Z) × location :=
  let d := Zdigits2 m
  let e' := zmin (fexp prec emax (zdiv2 (zadd (zadd d e) (zpos .xH)))) (zdiv2 e)
  let s := zsub e (zmul zTwo e')
  let m' := match s with
    | .Zpos _ => zshiftl m s
    | .Z0 => m
    | .Zneg _ => .Z0
  let qr := zsqrtrem m'
  let l := if CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool qr.2 .Z0 then
    .loc_Exact
  else
    .loc_Inexact (if zleBool qr.2 qr.1 then .Lt else .Gt)
  ((qr.1, e'), l)

end Rocq.Coq.Floats.SpecFloat

end CompCert4Lean.Lib.Floats.Model
