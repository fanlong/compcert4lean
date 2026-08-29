import CompCert4Lean.Flocq.IEEE754.Bits
import CompCert4Lean.Lib.IEEE754_extra
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Floats.Sqrt
import CompCert4Lean.X86_64.Archi

/-!
# CompCert floating-point facade

The public carriers are the accepted exact raw-word representations.  Numeric
operations use Lean's checked floating-point model behind an explicit x86-64
NaN-policy layer; source-shaped Flocq adapters provide exact integer
conversion and inverse-recognition behavior.
-/

namespace CompCert4Lean.Lib.Floats

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Lib
open CompCert4Lean.X86_64

private abbrev RCmp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.comparison
private abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
private abbrev positive := CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive
private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool

private abbrev z0 : Z := .Z0
private abbrev z1 : Z := ZArith.BinInt.Z.of_nat 1
private abbrev z24 : Z := ZArith.BinInt.Z.of_nat 24
private abbrev z53 : Z := ZArith.BinInt.Z.of_nat 53
private abbrev z128 : Z := ZArith.BinInt.Z.of_nat 128
private abbrev z1024 : Z := ZArith.BinInt.Z.of_nat 1024

private instance : CompCert4Lean.Flocq.Core.FLX.Prec_gt_0Class z24 :=
  CompCert4Lean.Flocq.Core.FLX.Prec_gt_0Class.of (by change (0 : Int) < 24; decide)

private instance : CompCert4Lean.Flocq.Core.FLX.Prec_gt_0Class z53 :=
  CompCert4Lean.Flocq.Core.FLX.Prec_gt_0Class.of (by change (0 : Int) < 53; decide)

private instance : CompCert4Lean.Flocq.IEEE754.BinarySingleNaN.Prec_lt_emax z24 z128 :=
  ⟨by change (24 : Int) < 128; decide⟩

private instance : CompCert4Lean.Flocq.IEEE754.BinarySingleNaN.Prec_lt_emax z53 z1024 :=
  ⟨by change (53 : Int) < 1024; decide⟩

@[ext] structure float where
  bits : BitVec 64
deriving DecidableEq

@[ext] structure float32 where
  bits : BitVec 32
deriving DecidableEq

/- Raw-word decoding remains a runtime compatibility boundary; theorem-facing
   certified consumers use the corresponding result obligations. -/
private def decode64 (x : float) : Bits.binary64 :=
  Bits.b64_of_bits_unchecked (ZArith.BinInt.Z.of_nat x.bits.toNat)

private def encode64 (x : Bits.binary64) : float :=
  ⟨BitVec.ofNat 64 (ZArith.BinInt.Z.to_nat (Bits.bits_of_b64 x))⟩

private def decode32 (x : float32) : Bits.binary32 :=
  Bits.b32_of_bits_unchecked (ZArith.BinInt.Z.of_nat x.bits.toNat)

private def encode32 (x : Bits.binary32) : float32 :=
  ⟨BitVec.ofNat 32 (ZArith.BinInt.Z.to_nat (Bits.bits_of_b32 x))⟩

private def sign64 (x : float) : Bool :=
  x.bits.toNat / (2 ^ 63) % 2 == 1

private def exponent64 (x : float) : Nat :=
  x.bits.toNat / (2 ^ 52) % (2 ^ 11)

private def fraction64 (x : float) : Nat :=
  x.bits.toNat % (2 ^ 52)

private def isNaN64 (x : float) : Bool :=
  exponent64 x == (2 ^ 11 - 1) && fraction64 x != 0

private def sign32 (x : float32) : Bool :=
  x.bits.toNat / (2 ^ 31) % 2 == 1

private def exponent32 (x : float32) : Nat :=
  x.bits.toNat / (2 ^ 23) % (2 ^ 8)

private def fraction32 (x : float32) : Nat :=
  x.bits.toNat % (2 ^ 23)

private def isNaN32 (x : float32) : Bool :=
  exponent32 x == (2 ^ 8 - 1) && fraction32 x != 0

private def mkNaN64 (s : Bool) (payload : positive) : float :=
  let signPart := if s then 2 ^ 63 else 0
  let exponentPart := (2 ^ 11 - 1) * 2 ^ 52
  let payloadPart := PArith.BinPos.Pos.to_nat payload % (2 ^ 52)
  ⟨BitVec.ofNat 64 (signPart + exponentPart + payloadPart)⟩

private def mkNaN32 (s : Bool) (payload : positive) : float32 :=
  let signPart := if s then 2 ^ 31 else 0
  let exponentPart := (2 ^ 8 - 1) * 2 ^ 23
  let payloadPart := PArith.BinPos.Pos.to_nat payload % (2 ^ 23)
  ⟨BitVec.ofNat 32 (signPart + exponentPart + payloadPart)⟩

private def payload64 (x : float) : positive :=
  PArith.BinPos.Pos.of_nat (fraction64 x)

private def payload32 (x : float32) : positive :=
  PArith.BinPos.Pos.of_nat (fraction32 x)

def integer_representable_nStatement : Prop :=
  IEEE754_extra.integer_representable_nStatement (prec := z53) (emax := z1024)

def cmp_of_comparison (c : Integers.comparison) (x : Option RCmp) : Bool :=
  match c with
  | .Ceq => match x with | some .Eq => true | _ => false
  | .Cne => match x with | some .Eq => false | _ => true
  | .Clt => match x with | some .Lt => true | _ => false
  | .Cle => match x with | some .Lt | some .Eq => true | _ => false
  | .Cgt => match x with | some .Gt => true | _ => false
  | .Cge => match x with | some .Gt | some .Eq => true | _ => false

def ordered_of_comparison (x : Option RCmp) : Bool :=
  x.isSome

def cmp_of_comparison_swapStatement : Prop :=
  ∀ (c : Integers.comparison) (x : Option RCmp),
    cmp_of_comparison (Integers.swap_comparison c) x =
      cmp_of_comparison c (x.map CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp)

def cmp_of_comparison_ne_eqStatement : Prop :=
  ∀ x : Option RCmp,
    cmp_of_comparison .Cne x = !(cmp_of_comparison .Ceq x)

def normalized_nanStatement : Prop :=
  ∀ (prec : Z) (n : Nat) (p : positive),
    ZArith.BinInt.Z.of_nat n = ZArith.BinInt.Z.sub prec z1 →
    ZArith.BinInt.Z.lt z1 prec →
    Binary.nan_pl (prec := prec)
      (ZArith.BinInt.Z.to_pos (CompCert4Lean.Lib.Zbits.P_mod_two_p p n)) = true

def quiet_nan_64_payload (p : positive) : positive :=
  PArith.BinPos.Pos.of_nat
    ((Nat.lor (PArith.BinPos.Pos.to_nat p) (2 ^ 51)) % (2 ^ 52))

def quiet_nan_64_proofStatement : Prop :=
  ∀ p : positive, Binary.nan_pl (prec := z53) (quiet_nan_64_payload p) = true

def quiet_nan_64 (sp : Bool × positive) : float :=
  mkNaN64 sp.1 (quiet_nan_64_payload sp.2)

def quiet_nan_64_result_obligation : Prop :=
  ∀ sp : Bool × positive,
    Binary.is_nan (decode64 (quiet_nan_64 sp)) = true ∧
      Binary.BinaryFloatCertificate (decode64 (quiet_nan_64 sp))

def default_nan_64 : float :=
  quiet_nan_64 Archi.default_nan_64

def default_nan_64_result_obligation : Prop :=
  Binary.is_nan (decode64 default_nan_64) = true ∧
    Binary.BinaryFloatCertificate (decode64 default_nan_64)

def quiet_nan_32_payload (p : positive) : positive :=
  PArith.BinPos.Pos.of_nat
    ((Nat.lor (PArith.BinPos.Pos.to_nat p) (2 ^ 22)) % (2 ^ 23))

def quiet_nan_32_proofStatement : Prop :=
  ∀ p : positive, Binary.nan_pl (prec := z24) (quiet_nan_32_payload p) = true

def quiet_nan_32 (sp : Bool × positive) : float32 :=
  mkNaN32 sp.1 (quiet_nan_32_payload sp.2)

def quiet_nan_32_result_obligation : Prop :=
  ∀ sp : Bool × positive,
    Binary.is_nan (decode32 (quiet_nan_32 sp)) = true ∧
      Binary.BinaryFloatCertificate (decode32 (quiet_nan_32 sp))

def default_nan_32 : float32 :=
  quiet_nan_32 Archi.default_nan_32

def default_nan_32_result_obligation : Prop :=
  Binary.is_nan (decode32 default_nan_32) = true ∧
    Binary.BinaryFloatCertificate (decode32 default_nan_32)

abbrev __ :
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Lt =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Lt) := rfl

private def modelBinary64
    (op : _root_.Float.Model.UnpackedFloat → _root_.Float.Model.UnpackedFloat →
      _root_.Float.Model.UnpackedFloat)
    (x y : float) : float :=
  ⟨_root_.Float.Model.UnpackedFloat.pack _root_.Float.Model.Format.binary64
    (op
      (_root_.Float.Model.UnpackedFloat.unpack _root_.Float.Model.Format.binary64 x.bits)
      (_root_.Float.Model.UnpackedFloat.unpack _root_.Float.Model.Format.binary64 y.bits))⟩

private def modelBinary32
    (op : _root_.Float.Model.UnpackedFloat → _root_.Float.Model.UnpackedFloat →
      _root_.Float.Model.UnpackedFloat)
    (x y : float32) : float32 :=
  ⟨_root_.Float.Model.UnpackedFloat.pack _root_.Float.Model.Format.binary32
    (op
      (_root_.Float.Model.UnpackedFloat.unpack _root_.Float.Model.Format.binary32 x.bits)
      (_root_.Float.Model.UnpackedFloat.unpack _root_.Float.Model.Format.binary32 y.bits))⟩

namespace Float

def expand_nan_payload (p : positive) : positive :=
  PArith.BinPos.Pos.shiftl_nat p 29

def expand_nan_proofStatement : Prop :=
  ∀ p : positive,
    Binary.nan_pl (prec := z24) p = true →
    Binary.nan_pl (prec := z53) (expand_nan_payload p) = true

def expand_nan (s : Bool) (p : positive) (_h : Binary.nan_pl (prec := z24) p = true) : float :=
  mkNaN64 s (expand_nan_payload p)

def expand_nan_result_obligation : Prop :=
  ∀ (s : Bool) (p : positive) (h : Binary.nan_pl (prec := z24) p = true),
    Binary.is_nan (decode64 (expand_nan s p h)) = true ∧
      Binary.BinaryFloatCertificate (decode64 (expand_nan s p h))

def of_single_nan (f : float32) : float :=
  if isNaN32 f then
    if Archi.float_conversion_default_nan then default_nan_64
    else if Archi.float_of_single_preserves_sNaN then
      mkNaN64 (sign32 f) (expand_nan_payload (payload32 f))
    else quiet_nan_64 (sign32 f, expand_nan_payload (payload32 f))
  else default_nan_64

def of_single_nan_result_obligation : Prop :=
  ∀ f : float32,
    Binary.BinaryFloatCertificate (decode32 f) →
      Binary.is_nan (decode64 (of_single_nan f)) = true ∧
        Binary.BinaryFloatCertificate (decode64 (of_single_nan f))

def reduce_nan_payload (p : positive) : positive :=
  PArith.BinPos.Pos.shiftr_nat (quiet_nan_64_payload p) 29

def to_single_nan (f : float) : float32 :=
  if isNaN64 f then
    if Archi.float_conversion_default_nan then default_nan_32
    else quiet_nan_32 (sign64 f, reduce_nan_payload (payload64 f))
  else default_nan_32

def to_single_nan_result_obligation : Prop :=
  ∀ f : float,
    Binary.BinaryFloatCertificate (decode64 f) →
      Binary.is_nan (decode32 (to_single_nan f)) = true ∧
        Binary.BinaryFloatCertificate (decode32 (to_single_nan f))

def neg_nan (f : float) : float :=
  if isNaN64 f then
    mkNaN64 (!sign64 f) (payload64 f)
  else default_nan_64

def neg_nan_result_obligation : Prop :=
  ∀ f : float,
    Binary.BinaryFloatCertificate (decode64 f) →
      Binary.is_nan (decode64 (neg_nan f)) = true ∧
        Binary.BinaryFloatCertificate (decode64 (neg_nan f))

def abs_nan (f : float) : float :=
  if isNaN64 f then mkNaN64 false (payload64 f) else default_nan_64

def abs_nan_result_obligation : Prop :=
  ∀ f : float,
    Binary.BinaryFloatCertificate (decode64 f) →
      Binary.is_nan (decode64 (abs_nan f)) = true ∧
        Binary.BinaryFloatCertificate (decode64 (abs_nan f))

def cons_pl (x : float) (l : List (Bool × positive)) : List (Bool × positive) :=
  if isNaN64 x then (sign64 x, payload64 x) :: l else l

def unop_nan (x : float) : float :=
  quiet_nan_64 (Archi.choose_nan_64 (cons_pl x []))

def unop_nan_result_obligation : Prop :=
  ∀ x : float,
    Binary.BinaryFloatCertificate (decode64 x) →
      Binary.is_nan (decode64 (unop_nan x)) = true ∧
        Binary.BinaryFloatCertificate (decode64 (unop_nan x))

def binop_nan (x y : float) : float :=
  quiet_nan_64 (Archi.choose_nan_64 (cons_pl x (cons_pl y [])))

def binop_nan_result_obligation : Prop :=
  ∀ (x y : float),
    Binary.BinaryFloatCertificate (decode64 x) →
      Binary.BinaryFloatCertificate (decode64 y) →
        Binary.is_nan (decode64 (binop_nan x y)) = true ∧
          Binary.BinaryFloatCertificate (decode64 (binop_nan x y))

def zero : float := ⟨0#64⟩

def eq_dec (f1 f2 : float) : Sumbool (f1 = f2) (f1 ≠ f2) := by
  by_cases h : f1 = f2
  · exact .left h
  · exact .right h

def neg (x : float) : float :=
  ⟨x.bits.xor (BitVec.ofNat 64 (2 ^ 63))⟩

def abs (x : float) : float :=
  ⟨x.bits.and (BitVec.ofNat 64 (2 ^ 63 - 1))⟩

def sqrt (x : float) : float :=
  if isNaN64 x then unop_nan x
  else
    let r : float := ⟨Sqrt.rawSqrt _root_.Float.Model.Format.binary64 x.bits⟩
    if isNaN64 r then default_nan_64 else r

private def finishBinary (x y r : float) : float :=
  if isNaN64 x || isNaN64 y then binop_nan x y
  else if isNaN64 r then default_nan_64 else r

def add (x y : float) : float :=
  finishBinary x y
    (modelBinary64 (_root_.Float.Model.UnpackedFloat.add _root_.Float.Model.Format.binary64) x y)

def sub (x y : float) : float :=
  finishBinary x y
    (modelBinary64 (_root_.Float.Model.UnpackedFloat.sub _root_.Float.Model.Format.binary64) x y)

def mul (x y : float) : float :=
  finishBinary x y
    (modelBinary64 (_root_.Float.Model.UnpackedFloat.mul _root_.Float.Model.Format.binary64) x y)

def div (x y : float) : float :=
  finishBinary x y
    (modelBinary64 (_root_.Float.Model.UnpackedFloat.div _root_.Float.Model.Format.binary64) x y)

def compare (f1 f2 : float) : Option RCmp :=
  match Binary.Bcompare (decode64 f1) (decode64 f2) with
  | none => none
  | some .Lt => some .Lt
  | some .Eq => some .Eq
  | some .Gt => some .Gt

def cmp (c : Integers.comparison) (f1 f2 : float) : Bool :=
  cmp_of_comparison c (compare f1 f2)

def ordered (f1 f2 : float) : Bool :=
  ordered_of_comparison (compare f1 f2)

def of_single (f : float32) : float :=
  if isNaN32 f then of_single_nan f
  else
    ⟨_root_.Float.Model.UnpackedFloat.pack _root_.Float.Model.Format.binary64
      (_root_.Float.Model.UnpackedFloat.unpack _root_.Float.Model.Format.binary32 f.bits)⟩

def to_single (f : float) : float32 :=
  if isNaN64 f then to_single_nan f
  else
    ⟨_root_.Float.Model.UnpackedFloat.pack _root_.Float.Model.Format.binary32
      (_root_.Float.Model.UnpackedFloat.unpack _root_.Float.Model.Format.binary64 f.bits)⟩

def to_int (f : float) : Option Integers.Int.int :=
  (IEEE754_extra.ZofB_range (decode64 f) Integers.Int.min_signed Integers.Int.max_signed).map
    Integers.Int.repr

def to_intu (f : float) : Option Integers.Int.int :=
  (IEEE754_extra.ZofB_range (decode64 f) z0 Integers.Int.max_unsigned).map Integers.Int.repr

def to_long (f : float) : Option Integers.Int64.int :=
  (IEEE754_extra.ZofB_range (decode64 f) Integers.Int64.min_signed Integers.Int64.max_signed).map
    Integers.Int64.repr

def to_longu (f : float) : Option Integers.Int64.int :=
  (IEEE754_extra.ZofB_range (decode64 f) z0 Integers.Int64.max_unsigned).map Integers.Int64.repr

def of_int (n : Integers.Int.int)
    [certificate : Binary.BinaryNormalizeCertificate z53 z1024] : float :=
  encode64 (IEEE754_extra.BofZ (prec := z53) (emax := z1024) (Integers.Int.signed n))

def of_intu (n : Integers.Int.int)
    [certificate : Binary.BinaryNormalizeCertificate z53 z1024] : float :=
  encode64 (IEEE754_extra.BofZ (prec := z53) (emax := z1024) (Integers.Int.unsigned n))

def of_long (n : Integers.Int64.int)
    [certificate : Binary.BinaryNormalizeCertificate z53 z1024] : float :=
  encode64 (IEEE754_extra.BofZ (prec := z53) (emax := z1024) (Integers.Int64.signed n))

def of_longu (n : Integers.Int64.int)
    [certificate : Binary.BinaryNormalizeCertificate z53 z1024] : float :=
  encode64 (IEEE754_extra.BofZ (prec := z53) (emax := z1024) (Integers.Int64.unsigned n))

def to_bits (f : float) : Integers.Int64.int :=
  Integers.Int64.ofFin f.bits.toFin

def of_bits (b : Integers.Int64.int) : float :=
  ⟨BitVec.ofFin (Integers.Int64.toFin b)⟩

def exact_inverse (f : float)
    [certificate : IEEE754_extra.Bexact_inverse_certificate z53 z1024] : Option float :=
  (IEEE754_extra.Bexact_inverse (prec := z53) (emax := z1024) (decode64 f)).map encode64

def mul_commutStatement : Prop :=
  ∀ x y : float, isNaN64 x = false ∨ isNaN64 y = false → mul x y = mul y x

def mul2_addStatement
    [certificate : Binary.BinaryNormalizeCertificate z53 z1024] : Prop :=
  ∀ f : float,
    add f f = mul f (of_int (Integers.Int.repr (ZArith.BinInt.Z.of_nat 2)))

def div_mul_inverseStatement
    [certificate : IEEE754_extra.Bexact_inverse_certificate z53 z1024] : Prop :=
  ∀ x y z : float, exact_inverse y = some z → div x y = mul x z

def cmp_swapStatement : Prop :=
  ∀ (c : Integers.comparison) (x y : float),
    cmp (Integers.swap_comparison c) x y = cmp c y x

def cmp_ne_eqStatement : Prop :=
  ∀ f1 f2 : float, cmp .Cne f1 f2 = !(cmp .Ceq f1 f2)

def of_to_bitsStatement : Prop :=
  ∀ f : float, of_bits (to_bits f) = f

def ox8000_0000 : Integers.Int.int :=
  Integers.Int.repr Integers.Int.half_modulus

def of_intu_of_int_1Statement
    [certificate : Binary.BinaryNormalizeCertificate z53 z1024] : Prop :=
  ∀ x : Integers.Int.int,
    Integers.Int.ltu x ox8000_0000 = true → of_intu x = of_int x

def of_intu_of_int_2Statement
    [certificate : Binary.BinaryNormalizeCertificate z53 z1024] : Prop :=
  ∀ x : Integers.Int.int, Integers.Int.ltu x ox8000_0000 = false →
    of_intu x =
      add (of_int (Integers.Int.sub x ox8000_0000)) (of_intu ox8000_0000)

def to_intu_to_int_1Statement
    [certificate : Binary.BinaryNormalizeCertificate z53 z1024] : Prop :=
  ∀ (x : float) (n : Integers.Int.int),
    cmp .Clt x (of_intu ox8000_0000) = true →
    to_intu x = some n → to_int x = some n

def to_intu_to_int_2Statement
    [certificate : Binary.BinaryNormalizeCertificate z53 z1024] : Prop :=
  ∀ (x : float) (n : Integers.Int.int),
    cmp .Clt x (of_intu ox8000_0000) = false →
    to_intu x = some n →
    to_int (sub x (of_intu ox8000_0000)) = some (Integers.Int.sub n ox8000_0000)

def ZofB_range_widenStatement : Prop :=
  ∀ (f : float) (n min1 max1 min2 max2 : Z),
    IEEE754_extra.ZofB_range (decode64 f) min1 max1 = some n →
    ZArith.BinInt.Z.le min2 min1 → ZArith.BinInt.Z.le max1 max2 →
    IEEE754_extra.ZofB_range (decode64 f) min2 max2 = some n

def to_intu_to_longStatement : Prop :=
  ∀ (f : float) (n : Integers.Int.int),
    to_intu f = some n →
    to_long f = some (Integers.Int64.repr (Integers.Int.unsigned n))

def of_intu_of_longStatement
    [certificate : Binary.BinaryNormalizeCertificate z53 z1024] : Prop :=
  ∀ n : Integers.Int.int,
    of_intu n = of_long (Integers.Int64.repr (Integers.Int.unsigned n))

end Float

namespace Float32

def neg_nan (f : float32) : float32 :=
  if isNaN32 f then mkNaN32 (!sign32 f) (payload32 f) else default_nan_32

def neg_nan_result_obligation : Prop :=
  ∀ f : float32,
    Binary.BinaryFloatCertificate (decode32 f) →
      Binary.is_nan (decode32 (neg_nan f)) = true ∧
        Binary.BinaryFloatCertificate (decode32 (neg_nan f))

def abs_nan (f : float32) : float32 :=
  if isNaN32 f then mkNaN32 false (payload32 f) else default_nan_32

def abs_nan_result_obligation : Prop :=
  ∀ f : float32,
    Binary.BinaryFloatCertificate (decode32 f) →
      Binary.is_nan (decode32 (abs_nan f)) = true ∧
        Binary.BinaryFloatCertificate (decode32 (abs_nan f))

def cons_pl (x : float32) (l : List (Bool × positive)) : List (Bool × positive) :=
  if isNaN32 x then (sign32 x, payload32 x) :: l else l

def unop_nan (x : float32) : float32 :=
  quiet_nan_32 (Archi.choose_nan_32 (cons_pl x []))

def unop_nan_result_obligation : Prop :=
  ∀ x : float32,
    Binary.BinaryFloatCertificate (decode32 x) →
      Binary.is_nan (decode32 (unop_nan x)) = true ∧
        Binary.BinaryFloatCertificate (decode32 (unop_nan x))

def binop_nan (x y : float32) : float32 :=
  quiet_nan_32 (Archi.choose_nan_32 (cons_pl x (cons_pl y [])))

def binop_nan_result_obligation : Prop :=
  ∀ (x y : float32),
    Binary.BinaryFloatCertificate (decode32 x) →
      Binary.BinaryFloatCertificate (decode32 y) →
        Binary.is_nan (decode32 (binop_nan x y)) = true ∧
          Binary.BinaryFloatCertificate (decode32 (binop_nan x y))

def zero : float32 := ⟨0#32⟩

def eq_dec (f1 f2 : float32) : Sumbool (f1 = f2) (f1 ≠ f2) := by
  by_cases h : f1 = f2
  · exact .left h
  · exact .right h

def neg (x : float32) : float32 :=
  ⟨x.bits.xor (BitVec.ofNat 32 (2 ^ 31))⟩

def abs (x : float32) : float32 :=
  ⟨x.bits.and (BitVec.ofNat 32 (2 ^ 31 - 1))⟩

def sqrt (x : float32) : float32 :=
  if isNaN32 x then
    unop_nan x
  else
    let r : float32 :=
      ⟨Sqrt.rawSqrt _root_.Float.Model.Format.binary32 x.bits⟩
    if isNaN32 r then default_nan_32 else r

private def finishBinary (x y r : float32) : float32 :=
  if isNaN32 x || isNaN32 y then binop_nan x y
  else if isNaN32 r then default_nan_32 else r

def add (x y : float32) : float32 :=
  finishBinary x y
    (modelBinary32 (_root_.Float.Model.UnpackedFloat.add _root_.Float.Model.Format.binary32) x y)

def sub (x y : float32) : float32 :=
  finishBinary x y
    (modelBinary32 (_root_.Float.Model.UnpackedFloat.sub _root_.Float.Model.Format.binary32) x y)

def mul (x y : float32) : float32 :=
  finishBinary x y
    (modelBinary32 (_root_.Float.Model.UnpackedFloat.mul _root_.Float.Model.Format.binary32) x y)

def div (x y : float32) : float32 :=
  finishBinary x y
    (modelBinary32 (_root_.Float.Model.UnpackedFloat.div _root_.Float.Model.Format.binary32) x y)

def compare (f1 f2 : float32) : Option RCmp :=
  match Binary.Bcompare (decode32 f1) (decode32 f2) with
  | none => none
  | some .Lt => some .Lt
  | some .Eq => some .Eq
  | some .Gt => some .Gt

def cmp (c : Integers.comparison) (f1 f2 : float32) : Bool :=
  cmp_of_comparison c (compare f1 f2)

def ordered (f1 f2 : float32) : Bool :=
  ordered_of_comparison (compare f1 f2)

def of_double : float → float32 :=
  Float.to_single

def to_double : float32 → float :=
  Float.of_single

def to_int (f : float32) : Option Integers.Int.int :=
  (IEEE754_extra.ZofB_range (decode32 f) Integers.Int.min_signed Integers.Int.max_signed).map
    Integers.Int.repr

def to_intu (f : float32) : Option Integers.Int.int :=
  (IEEE754_extra.ZofB_range (decode32 f) z0 Integers.Int.max_unsigned).map Integers.Int.repr

def to_long (f : float32) : Option Integers.Int64.int :=
  (IEEE754_extra.ZofB_range (decode32 f) Integers.Int64.min_signed Integers.Int64.max_signed).map
    Integers.Int64.repr

def to_longu (f : float32) : Option Integers.Int64.int :=
  (IEEE754_extra.ZofB_range (decode32 f) z0 Integers.Int64.max_unsigned).map Integers.Int64.repr

def of_int (n : Integers.Int.int)
    [certificate : Binary.BinaryNormalizeCertificate z24 z128] : float32 :=
  encode32 (IEEE754_extra.BofZ (prec := z24) (emax := z128) (Integers.Int.signed n))

def of_intu (n : Integers.Int.int)
    [certificate : Binary.BinaryNormalizeCertificate z24 z128] : float32 :=
  encode32 (IEEE754_extra.BofZ (prec := z24) (emax := z128) (Integers.Int.unsigned n))

def of_long (n : Integers.Int64.int)
    [certificate : Binary.BinaryNormalizeCertificate z24 z128] : float32 :=
  encode32 (IEEE754_extra.BofZ (prec := z24) (emax := z128) (Integers.Int64.signed n))

def of_longu (n : Integers.Int64.int)
    [certificate : Binary.BinaryNormalizeCertificate z24 z128] : float32 :=
  encode32 (IEEE754_extra.BofZ (prec := z24) (emax := z128) (Integers.Int64.unsigned n))

def to_bits (f : float32) : Integers.Int.int :=
  Integers.Int.ofFin f.bits.toFin

def of_bits (b : Integers.Int.int) : float32 :=
  ⟨BitVec.ofFin (Integers.Int.toFin b)⟩

def exact_inverse (f : float32)
    [certificate : IEEE754_extra.Bexact_inverse_certificate z24 z128] : Option float32 :=
  (IEEE754_extra.Bexact_inverse (prec := z24) (emax := z128) (decode32 f)).map encode32

def mul_commutStatement : Prop :=
  ∀ x y : float32, isNaN32 x = false ∨ isNaN32 y = false → mul x y = mul y x

def mul2_addStatement
    [certificate : Binary.BinaryNormalizeCertificate z24 z128] : Prop :=
  ∀ f : float32,
    add f f = mul f (of_int (Integers.Int.repr (ZArith.BinInt.Z.of_nat 2)))

def div_mul_inverseStatement
    [certificate : IEEE754_extra.Bexact_inverse_certificate z24 z128] : Prop :=
  ∀ x y z : float32, exact_inverse y = some z → div x y = mul x z

def cmp_swapStatement : Prop :=
  ∀ (c : Integers.comparison) (x y : float32),
    cmp (Integers.swap_comparison c) x y = cmp c y x

def cmp_ne_eqStatement : Prop :=
  ∀ f1 f2 : float32, cmp .Cne f1 f2 = !(cmp .Ceq f1 f2)

def of_to_bitsStatement : Prop :=
  ∀ f : float32, of_bits (to_bits f) = f

def of_intu_doubleStatement
    [binary32_certificate : Binary.BinaryNormalizeCertificate z24 z128]
    [binary64_certificate : Binary.BinaryNormalizeCertificate z53 z1024] : Prop :=
  ∀ n : Integers.Int.int, of_intu n = of_double (Float.of_intu n)

def to_intu_doubleStatement : Prop :=
  ∀ (f : float32) (n : Integers.Int.int),
    to_intu f = some n → Float.to_intu (to_double f) = some n

def to_long_doubleStatement : Prop :=
  ∀ (f : float32) (n : Integers.Int64.int),
    to_long f = some n → Float.to_long (to_double f) = some n

def to_longu_doubleStatement : Prop :=
  ∀ (f : float32) (n : Integers.Int64.int),
    to_longu f = some n → Float.to_longu (to_double f) = some n

end Float32

namespace Sqrt

/-! The selected fixed-width correspondence obligations deliberately name the
actual public facades.  Their right-hand sides therefore retain both observable
parts of CompCert's unary square-root policy: input NaNs are handled by
`Float.unop_nan` / `Float32.unop_nan`, and NaNs produced by the model result are
normalized to `default_nan_64` / `default_nan_32`. -/

def float32_sqrt_correctStatement : Prop :=
  ∀ x : UInt32,
    float32_sqrt x =
      UInt32.ofBitVec
        (Float32.sqrt (⟨x.toBitVec⟩ : float32)).bits

abbrev float32_sqrt_correct : Prop := float32_sqrt_correctStatement

def float64_sqrt_correctStatement : Prop :=
  ∀ x : UInt64,
    float64_sqrt x =
      UInt64.ofBitVec
        (Float.sqrt (⟨x.toBitVec⟩ : float)).bits

abbrev float64_sqrt_correct : Prop := float64_sqrt_correctStatement

end Sqrt

end CompCert4Lean.Lib.Floats
