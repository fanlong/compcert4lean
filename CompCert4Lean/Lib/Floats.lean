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

private instance : CompCert4Lean.Flocq.Core.FLX.Prec_gt_0 z24 := by
  change (0 : Int) < 24
  decide

private instance : CompCert4Lean.Flocq.Core.FLX.Prec_gt_0 z53 := by
  change (0 : Int) < 53
  decide

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

namespace CompCert4Lean.Lib.Floats

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Lib

theorem cmp_of_comparison_swap : cmp_of_comparison_swapStatement := by
  intro c x
  cases c <;> cases x with
  | none => rfl
  | some v => cases v <;> simp [Integers.swap_comparison, cmp_of_comparison,
      CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.CompOpp]

theorem cmp_of_comparison_ne_eq : cmp_of_comparison_ne_eqStatement := by
  intro x
  cases x with
  | none => rfl
  | some v => cases v <;> simp [cmp_of_comparison]

theorem normalized_nan : normalized_nanStatement := by
  have hdouble (x : Z) :
      intOfZ (ZArith.BinInt.Z.double x) = 2 * intOfZ x := by
    unfold ZArith.BinInt.Z.double ZArith.BinInt.Z.mul
    simp only [intOfZ_zOfInt]
    have h2 : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
    rw [h2]
  have hsucc (x : Z) :
      intOfZ (ZArith.BinInt.Z.succ_double x) = 2 * intOfZ x + 1 := by
    unfold ZArith.BinInt.Z.succ_double ZArith.BinInt.Z.succ
    unfold ZArith.BinInt.Z.double ZArith.BinInt.Z.mul ZArith.BinInt.Z.add
    simp only [intOfZ_zOfInt]
    have h2 : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
    have h1 : intOfZ (Zpos .xH) = (1 : Int) := by decide
    rw [h2, h1]
  have hpow_succ : ∀ n : Nat,
      two_power_nat (Nat.succ n) = ZArith.BinInt.Z.double (two_power_nat n) := by
    intro n
    have hpow (m : Nat) :
        ZArith.BinInt.Z.pow (Zpos (.xO .xH))
            (ZArith.BinInt.Z.of_nat m) = zOfInt (2 ^ m) := by
      unfold ZArith.BinInt.Z.pow ZArith.BinInt.Z.of_nat
      simp only [intOfZ_zOfInt]
      have h2 : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
      rw [h2]
      change (if (Int.ofNat m) < 0 then Z0 else
        zOfInt ((2 : Int) ^ (Int.ofNat m).toNat)) = zOfInt (2 ^ m)
      split
      · next h => exact (Int.not_lt_of_ge (Int.natCast_nonneg _) h).elim
      · next h => simp
    unfold two_power_nat ZArith.Zpower.two_power_nat
    rw [hpow, hpow]
    apply intOfZ_injective
    simp [ZArith.BinInt.Z.double, ZArith.BinInt.Z.mul,
      intOfZ_zOfInt, Int.pow_succ]
    have h2 : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
    rw [h2]
    exact Int.mul_comm _ _
  have hp0 : two_power_nat 0 = Zpos .xH := by decide
  have hpos : ∀ n : Nat, 0 < intOfZ (two_power_nat n) := by
    intro n
    induction n with
    | zero => rw [hp0]; decide
    | succ n ih =>
        rw [hpow_succ, hdouble]
        omega
  have hrange : ∀ (n : Nat) (p : positive),
      ZArith.BinInt.Z.le Z0 (CompCert4Lean.Lib.Zbits.P_mod_two_p p n) ∧
      ZArith.BinInt.Z.lt (CompCert4Lean.Lib.Zbits.P_mod_two_p p n)
        (two_power_nat n) := by
    intro n
    induction n with
    | zero =>
        intro p
        simp only [CompCert4Lean.Lib.Zbits.P_mod_two_p]
        change (0 ≤ intOfZ Z0 ∧ intOfZ Z0 < intOfZ (two_power_nat 0))
        rw [hp0]
        decide
    | succ n ih =>
        intro p
        have hpow := hpow_succ n
        cases p with
        | xH =>
            have hm : CompCert4Lean.Lib.Zbits.P_mod_two_p (.xH) (Nat.succ n) = Zpos .xH := by rfl
            rw [hm]
            change (0 ≤ intOfZ (Zpos .xH) ∧
              intOfZ (Zpos .xH) < intOfZ (two_power_nat (Nat.succ n)))
            rw [hpow]
            have h2 := hdouble (two_power_nat n)
            rw [h2]
            have hone : intOfZ (Zpos .xH) = (1 : Int) := by decide
            rw [hone]
            have hpn := hpos n
            omega
        | xO q =>
            have h := ih q
            have hm : CompCert4Lean.Lib.Zbits.P_mod_two_p (.xO q) (Nat.succ n) =
                ZArith.BinInt.Z.double (CompCert4Lean.Lib.Zbits.P_mod_two_p q n) := by rfl
            rw [hm]
            change (0 ≤ intOfZ (ZArith.BinInt.Z.double
                (CompCert4Lean.Lib.Zbits.P_mod_two_p q n)) ∧
              intOfZ (ZArith.BinInt.Z.double
                (CompCert4Lean.Lib.Zbits.P_mod_two_p q n)) <
                intOfZ (two_power_nat (Nat.succ n)))
            rw [hpow]
            have hq := hdouble (CompCert4Lean.Lib.Zbits.P_mod_two_p q n)
            have h2 := hdouble (two_power_nat n)
            rw [hq, h2]
            change (0 ≤ 2 * intOfZ (CompCert4Lean.Lib.Zbits.P_mod_two_p q n) ∧
              2 * intOfZ (CompCert4Lean.Lib.Zbits.P_mod_two_p q n) <
                2 * intOfZ (two_power_nat n))
            change (0 ≤ intOfZ (CompCert4Lean.Lib.Zbits.P_mod_two_p q n) ∧
              intOfZ (CompCert4Lean.Lib.Zbits.P_mod_two_p q n) <
                intOfZ (two_power_nat n)) at h
            omega
        | xI q =>
            have h := ih q
            have hm : CompCert4Lean.Lib.Zbits.P_mod_two_p (.xI q) (Nat.succ n) =
                ZArith.BinInt.Z.succ_double (CompCert4Lean.Lib.Zbits.P_mod_two_p q n) := by rfl
            rw [hm]
            change (0 ≤ intOfZ (ZArith.BinInt.Z.succ_double
                (CompCert4Lean.Lib.Zbits.P_mod_two_p q n)) ∧
              intOfZ (ZArith.BinInt.Z.succ_double
                (CompCert4Lean.Lib.Zbits.P_mod_two_p q n)) <
                intOfZ (two_power_nat (Nat.succ n)))
            rw [hpow]
            have hq := hsucc (CompCert4Lean.Lib.Zbits.P_mod_two_p q n)
            have h2 := hdouble (two_power_nat n)
            rw [hq, h2]
            change (0 ≤ 2 * intOfZ (CompCert4Lean.Lib.Zbits.P_mod_two_p q n) + 1 ∧
              2 * intOfZ (CompCert4Lean.Lib.Zbits.P_mod_two_p q n) + 1 <
                2 * intOfZ (two_power_nat n))
            change (0 ≤ intOfZ (CompCert4Lean.Lib.Zbits.P_mod_two_p q n) ∧
              intOfZ (CompCert4Lean.Lib.Zbits.P_mod_two_p q n) <
                intOfZ (two_power_nat n)) at h
            omega
  have h_digits : ∀ q : positive,
      PArith.BinPos.Pos.to_nat
          (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos q) =
        Nat.log2 (PArith.BinPos.Pos.to_nat q) + 1 := by
    have hsucc (q : positive) :
        PArith.BinPos.Pos.to_nat
            (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posSucc q) =
          PArith.BinPos.Pos.to_nat q + 1 := by
      induction q with
      | xH => rfl
      | xI q ih =>
          change 2 * PArith.BinPos.Pos.to_nat
              (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posSucc q) =
            2 * PArith.BinPos.Pos.to_nat q + 1 + 1
          rw [ih]
          omega
      | xO q ih =>
          change PArith.BinPos.Pos.to_nat (.xI q) =
            2 * PArith.BinPos.Pos.to_nat q + 1
          rfl
    intro q
    induction q with
    | xH => decide
    | xO q ih =>
        rw [show CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos
              (.xO q) =
              CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posSucc
                (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos q) by rfl,
          hsucc, ih]
        simp only [PArith.BinPos.Pos.to_nat,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
        have hqne : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q ≠ 0 :=
          Nat.ne_of_gt (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive q)
        rw [Nat.log2_two_mul hqne]
    | xI q ih =>
        rw [show CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos
              (.xI q) =
              CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posSucc
                (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos q) by rfl,
          hsucc, ih]
        simp only [PArith.BinPos.Pos.to_nat,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
        let k : Nat := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q
        have hk : 0 < k := by exact
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive q
        have hlog : Nat.log2 (2 * k + 1) = Nat.log2 k + 1 := by
          apply (Nat.log2_eq_iff (Nat.ne_of_gt (by omega : 0 < 2 * k + 1))).2
          have hlow := Nat.log2_self_le (Nat.ne_of_gt hk)
          have hhigh := (Nat.log2_lt (Nat.ne_of_gt hk)).1
            (Nat.lt_succ_self (Nat.log2 k))
          constructor <;> rw [Nat.pow_succ] <;> omega
        change Nat.log2 k + 1 + 1 = Nat.log2 (2 * k + 1) + 1
        rw [hlog]
  have hpNat : ∀ k : Nat, intOfZ (two_power_nat k) = (2 : Int) ^ k := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
        rw [hpow_succ, hdouble, ih]
        change 2 * (2 : Int) ^ k = (2 : Int) ^ Nat.succ k
        calc
          2 * (2 : Int) ^ k = (2 : Int) ^ k * 2 := Int.mul_comm _ _
          _ = (2 : Int) ^ Nat.succ k := (Int.pow_succ 2 k).symm
  have hpowInt : ∀ k : Nat, (2 : Int) ^ k = Int.ofNat (2 ^ k) := by
    intro k
    have htwo : (2 : Int) = (↑(2 : Nat) : Int) := by decide
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Int.pow_succ, ih, Nat.pow_succ]
        simp only [Int.ofNat_eq_natCast]
        rw [Int.natCast_mul]
        rw [htwo]
  intro prec n p hn hprec
  unfold Binary.nan_pl
  have hm := hrange n p
  cases hval : CompCert4Lean.Lib.Zbits.P_mod_two_p p n with
  | Z0 =>
      change ZArith.BinInt.Z.ltb
        (ZArith.BinInt.Z.Zpos
          (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos
            (ZArith.BinInt.Z.to_pos ZArith.BinInt.Z.Z0))) prec = true
      change (if intOfZ (Zpos
          (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos
            (ZArith.BinInt.Z.to_pos ZArith.BinInt.Z.Z0))) < intOfZ prec then true else false) = true
      have hp : intOfZ (Zpos
          (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos
            (ZArith.BinInt.Z.to_pos ZArith.BinInt.Z.Z0))) = (1 : Int) := by decide
      rw [hp]
      change 1 < intOfZ prec at hprec
      simp [hprec]
  | Zpos q =>
      have hlt := hm.2
      rw [hval] at hlt
      change intOfZ (Zpos q) < intOfZ (two_power_nat n) at hlt
      rw [hpNat n] at hlt
      change Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q) <
        (2 : Int) ^ n at hlt
      have hltNat : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q < 2 ^ n := by
        apply Int.ofNat_lt.mp
        have hlt' := hlt
        rw [hpowInt n] at hlt'
        simp only [Int.ofNat_eq_natCast] at hlt'
        exact hlt'
      have hlog := (Nat.log2_lt (Nat.ne_of_gt
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive q))).2 hltNat
      have hd := h_digits q
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
          (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos q) =
        Nat.log2 (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q) + 1 at hd
      have hdNat : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
          (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos q) ≤ n := by
        omega
      have hnInt := congrArg intOfZ hn
      have hprecInt := hprec
      have hn_of : intOfZ (ZArith.BinInt.Z.of_nat n) = Int.ofNat n := by
        change intOfZ (zOfInt (Int.ofNat n)) = Int.ofNat n
        exact intOfZ_zOfInt _
      rw [hn_of] at hnInt
      have hsub : intOfZ (ZArith.BinInt.Z.sub prec z1) = intOfZ prec - 1 := by
        unfold ZArith.BinInt.Z.sub
        simp only [intOfZ_zOfInt]
        have h1 : intOfZ z1 = (1 : Int) := by decide
        rw [h1]
      rw [hsub] at hnInt
      change 1 < intOfZ prec at hprecInt
      have hto_pos : ZArith.BinInt.Z.to_pos (Zpos q) = q := by
        change PArith.BinPos.Pos.of_nat
          (Int.toNat (Int.ofNat (PArith.BinPos.Pos.to_nat q))) = q
        rw [show Int.toNat (Int.ofNat (PArith.BinPos.Pos.to_nat q)) =
            PArith.BinPos.Pos.to_nat q by cases q <;> rfl]
        exact PArith.Pnat.Pos2Nat.id q
      rw [hto_pos]
      change (if intOfZ (Zpos
          (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos q)) <
          intOfZ prec then true else false) = true
      have htarget : intOfZ (Zpos
          (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos q)) <
          intOfZ prec := by
        change Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
            (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos q)) <
          intOfZ prec
        have hprecEq0 : intOfZ prec = Int.ofNat n + 1 := by omega
        have hprecEq : intOfZ prec = Int.ofNat (n + 1) := by
          calc
            intOfZ prec = Int.ofNat n + 1 := hprecEq0
            _ = Int.ofNat (n + 1) := by
              rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast]
              rw [Int.natCast_add, Int.natCast_one]
        rw [hprecEq]
        rw [Int.ofNat_eq_natCast]
        apply Int.ofNat_lt.mpr
        omega
      simp [htarget]
  | Zneg q =>
      have hnonneg := hm.1
      rw [hval] at hnonneg
      change 0 ≤ -Int.ofNat (PArith.BinPos.Pos.to_nat q) at hnonneg
      have hqpos : 0 < PArith.BinPos.Pos.to_nat q := by
        change 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q
        exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive q
      have hqposInt : (0 : Int) < Int.ofNat (PArith.BinPos.Pos.to_nat q) := by
        change (0 : Int) < (PArith.BinPos.Pos.to_nat q : Int)
        exact Int.ofNat_lt.mpr hqpos
      omega

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Lib

private theorem quiet_nan_digits2_pos_nat (q : positive) :
    PArith.BinPos.Pos.to_nat
        (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos q) =
      Nat.log2 (PArith.BinPos.Pos.to_nat q) + 1 := by
  have hsucc (q : positive) :
      PArith.BinPos.Pos.to_nat
          (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posSucc q) =
        PArith.BinPos.Pos.to_nat q + 1 := by
    induction q with
    | xH => rfl
    | xI q ih =>
        change 2 * PArith.BinPos.Pos.to_nat
            (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posSucc q) =
          2 * PArith.BinPos.Pos.to_nat q + 1 + 1
        rw [ih]
        omega
    | xO q ih =>
        change PArith.BinPos.Pos.to_nat (.xI q) =
          2 * PArith.BinPos.Pos.to_nat q + 1
        rfl
  induction q with
  | xH => decide
  | xO q ih =>
      rw [show CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos
            (.xO q) =
            CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posSucc
              (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos q) by rfl,
        hsucc, ih]
      simp only [PArith.BinPos.Pos.to_nat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
      have hqne : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q ≠ 0 :=
        Nat.ne_of_gt (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive q)
      rw [Nat.log2_two_mul hqne]
  | xI q ih =>
      rw [show CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos
            (.xI q) =
            CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posSucc
              (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos q) by rfl,
        hsucc, ih]
      simp only [PArith.BinPos.Pos.to_nat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
      let k : Nat := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q
      have hk : 0 < k := by exact
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive q
      have hlog : Nat.log2 (2 * k + 1) = Nat.log2 k + 1 := by
        apply (Nat.log2_eq_iff (Nat.ne_of_gt (by omega : 0 < 2 * k + 1))).2
        have hlow := Nat.log2_self_le (Nat.ne_of_gt hk)
        have hhigh := (Nat.log2_lt (Nat.ne_of_gt hk)).1
          (Nat.lt_succ_self (Nat.log2 k))
        constructor <;> rw [Nat.pow_succ] <;> omega
      change Nat.log2 k + 1 + 1 = Nat.log2 (2 * k + 1) + 1
      rw [hlog]

theorem quiet_nan_64_proof : quiet_nan_64_proofStatement := by
  intro p
  unfold Binary.nan_pl quiet_nan_64_payload
  change (if intOfZ (Zpos
      (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos
        (PArith.BinPos.Pos.of_nat
          ((Nat.lor (PArith.BinPos.Pos.to_nat p) (2 ^ 51)) % (2 ^ 52))))) <
      intOfZ z53 then true else false) = true
  let q : Nat := (Nat.lor (PArith.BinPos.Pos.to_nat p) (2 ^ 51)) % (2 ^ 52)
  have hq_lt : q < 2 ^ 52 := by
    dsimp [q]
    exact Nat.mod_lt _ (Nat.two_pow_pos 52)
  have hq_pos : 0 < q := by
    have hbit : q.testBit 51 = true := by
      simp only [q]
      rw [Nat.testBit_mod_two_pow]
      change (true && (Nat.lor (PArith.BinPos.Pos.to_nat p) (2 ^ 51)).testBit 51) = true
      rw [Nat.lor_eq, Nat.testBit_or]
      rw [Nat.testBit_two_pow_self]
      exact Bool.or_true _
    have hh := Nat.ge_two_pow_of_testBit hbit
    have hpow : 0 < 2 ^ 51 := Nat.two_pow_pos 51
    omega
  have hq_log : Nat.log2 q < 52 :=
    (Nat.log2_lt (Nat.ne_of_gt hq_pos)).2 hq_lt
  have hdigits_q :
      PArith.BinPos.Pos.to_nat
          (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos
            (PArith.BinPos.Pos.of_nat q)) = Nat.log2 q + 1 := by
    rw [quiet_nan_digits2_pos_nat]
    change Nat.log2 (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat q)) + 1 = Nat.log2 q + 1
    rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat hq_pos]
  have hdigits_lt : Nat.log2 q + 1 < 53 := by omega
  change (if intOfZ (Zpos
      (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos
        (PArith.BinPos.Pos.of_nat q))) < intOfZ z53 then true else false) = true
  have hdigits_int :
      intOfZ (Zpos
        (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos
          (PArith.BinPos.Pos.of_nat q))) = Int.ofNat (Nat.log2 q + 1) := by
    exact congrArg Int.ofNat hdigits_q
  rw [hdigits_int]
  have hz53 : intOfZ z53 = (53 : Int) := by decide
  rw [hz53]
  have hltInt : Int.ofNat (Nat.log2 q + 1) < (53 : Int) := by
    change (Nat.log2 q : Int) + 1 < (53 : Int)
    exact_mod_cast hdigits_lt
  rw [if_pos hltInt]

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

private theorem test_nan_aux (q : Nat) (hq : 0 < q) (hqlt : q < 2 ^ 23) :
    CompCert4Lean.Flocq.IEEE754.Bits.binary_float_of_bits_aux
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 23)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 8)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
          (2139095040 + q)) =
      CompCert4Lean.Flocq.IEEE754.Binary.F754_nan false
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat q) := by
  unfold CompCert4Lean.Flocq.IEEE754.Bits.binary_float_of_bits_aux
  unfold CompCert4Lean.Flocq.IEEE754.Bits.split_bits
  have zmod_nat (a b : Nat) (hb : 0 < b) :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat a)
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat b) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (a % b) := by
    have hdecomp :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat a =
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (a % b))
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (a / b))
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat b)) := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      calc
        Int.ofNat a = Int.ofNat (a % b + b * (a / b)) := by
          congr 1
          exact (Nat.mod_add_div a b).symm
        _ = Int.ofNat (a % b + (a / b) * b) := by rw [Nat.mul_comm]
    rw [hdecomp,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo_add_mul]
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mod_small
    constructor
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (a % b))
      rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 = 0 by rfl]
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      exact Int.natCast_nonneg _
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (a % b)) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat b)
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      exact (Int.ofNat_lt).2 (Nat.mod_lt a hb)
  have zdiv_nat (a b : Nat) (hb : 0 < b) :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat a)
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat b) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (a / b) := by
    have hiden :=
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Z_div_mod_eq_full
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat a)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat b)
    rw [zmod_nat a b hb] at hiden
    have hiden' := congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hiden
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hiden'
    have hcast : Int.ofNat a = Int.ofNat b * Int.ofNat (a / b) + Int.ofNat (a % b) := by
      have hn : a = b * (a / b) + a % b := by
        calc
          a = a % b + b * (a / b) := (Nat.mod_add_div a b).symm
          _ = b * (a / b) + a % b := by rw [Nat.add_comm]
      have hi := congrArg (fun n : Nat => (n : Int)) hn
      simp only [Int.natCast_mul, Int.natCast_add] at hi
      exact hi
    have hsum : Int.ofNat b *
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat a)
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat b)) +
          Int.ofNat (a % b) =
        Int.ofNat b * Int.ofNat (a / b) + Int.ofNat (a % b) := hiden'.symm.trans hcast
    have hprod : Int.ofNat b *
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat a)
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat b)) =
        Int.ofNat b * Int.ofNat (a / b) := by
      apply Int.add_left_cancel (a := Int.ofNat (a % b))
      simpa [Int.add_comm] using hsum
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    have hbI : Int.ofNat b ≠ 0 := (Int.ofNat_ne_zero).2 (Nat.ne_of_gt hb)
    have hqcast :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (a / b)) =
          Int.ofNat (a / b) := by
      exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt _
    exact Int.eq_of_mul_eq_mul_left hbI (hprod.trans (by rw [hqcast]))
  have h23 : CompCert4Lean.Flocq.IEEE754.Bits.Zpower
      CompCert4Lean.Flocq.IEEE754.Bits.Ztwo
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 23) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 8388608 := by decide
  have h8 : CompCert4Lean.Flocq.IEEE754.Bits.Zpower
      CompCert4Lean.Flocq.IEEE754.Bits.Ztwo
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 8) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 256 := by decide
  rw [h23, h8]
  dsimp only
  change (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool _ _ then _ else _) = _
  change (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div _ _) _) _ then _ else _) = _
  rw [zdiv_nat (2139095040 + q) 8388608 (by omega)]
  rw [zmod_nat ((2139095040 + q) / 8388608) 256 (by omega)]
  change (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool _ _ then
      match CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo _ _ with
      | .Z0 => _ | .Zpos px => _ | .Zneg px => _
    else _) = _
  rw [zmod_nat (2139095040 + q) 8388608 (by omega)]
  have hqmod : (2139095040 + q) % 8388608 = q := by
    have hbase : 2139095040 = 255 * 8388608 := by decide
    rw [hbase, Nat.add_comm, Nat.mul_comm 255 8388608,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hqlt]
  have hqdiv : (2139095040 + q) / 8388608 = 255 := by
    have hbase : 2139095040 = 255 * 8388608 := by decide
    rw [hbase, Nat.add_comm, Nat.mul_comm 255 8388608,
      Nat.add_mul_div_left q 255 (by omega),
      Nat.div_eq_of_lt hqlt]
  rw [hqmod, hqdiv]
  simp only [Nat.mod_eq_of_lt (by omega : 255 < 256)]
  have hz255 :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 255 =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 256)
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos .xH) := by decide
  have hqz :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat q =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat q) := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    exact congrArg Int.ofNat
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat hq).symm
  rw [hz255, hqz]
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool]
  simp
  have hsign : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.leb
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 8388608)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 256))
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (2139095040 + q)) = false := by
    unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.leb
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    rw [if_neg]
    have hfull : 2139095040 + q < 2147483648 := by omega
    have hfullInt := (Int.ofNat_lt).2 hfull
    rw [show Int.ofNat 8388608 * Int.ofNat 256 = Int.ofNat 2147483648 by decide]
    exact Int.not_le_of_gt hfullInt
  simp only [CompCert4Lean.Flocq.IEEE754.Bits.Zle_bool,
    CompCert4Lean.Flocq.IEEE754.Bits.Zmul, hsign]
  simp only [CompCert4Lean.Flocq.IEEE754.Bits.Zmod,
    CompCert4Lean.Flocq.IEEE754.Bits.Zdiv,
    CompCert4Lean.Flocq.IEEE754.Bits.Zsub,
    CompCert4Lean.Flocq.IEEE754.Bits.Zone,
    CompCert4Lean.Flocq.IEEE754.Bits.Z0,
    CompCert4Lean.Flocq.IEEE754.Bits.Zadd]
  rw [← hz255]
  rw [zdiv_nat (2139095040 + q) 8388608 (by omega)]
  rw [zmod_nat ((2139095040 + q) / 8388608) 256 (by omega)]
  rw [hqdiv, Nat.mod_eq_of_lt (by omega : 255 < 256)]
  rw [zmod_nat (2139095040 + q) 8388608 (by omega), hqmod, hqz]
  have h255ne : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 255 ≠
      CompCert4Lean.Flocq.Core.Zaux.Z0 := by decide
  rw [if_neg h255ne]
  have h255eq : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 255 =
      CompCert4Lean.Flocq.Core.Zaux.Zsub
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 256)
        CompCert4Lean.Flocq.Core.Zaux.Zone := by decide
  rw [if_pos h255eq]

private theorem decode32_mkNaN_false (q : Nat) (hq : 0 < q) (hqlt : q < 2 ^ 23) :
    decode32
        (mkNaN32 false
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat q)) =
      (CompCert4Lean.Flocq.IEEE754.Binary.B754_nan false
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat q) :
        CompCert4Lean.Flocq.IEEE754.Bits.binary32) := by
  unfold decode32 mkNaN32
  dsimp only
  have hpayload :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat q) = q := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat q) = q
    exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat hq
  rw [hpayload]
  rw [Nat.mod_eq_of_lt hqlt]
  simp only [Bool.false_eq_true, if_false, Nat.zero_add]
  rw [show (2 ^ 8 - 1) * 2 ^ 23 = 2139095040 by decide]
  rw [BitVec.toNat_ofNat]
  have hsum : 2139095040 + q < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt hsum]
  unfold CompCert4Lean.Flocq.IEEE754.Bits.b32_of_bits_unchecked
  unfold CompCert4Lean.Flocq.IEEE754.Bits.binary_float_of_bits_unchecked
  unfold CompCert4Lean.Flocq.IEEE754.Binary.FF2B_unchecked
  rw [test_nan_aux q hq hqlt]

private theorem nan_pl_posOfNat_lt_23 (q : Nat) (hq : 0 < q) (hqlt : q < 2 ^ 23) :
    CompCert4Lean.Flocq.IEEE754.Binary.nan_pl (prec := z24)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat q) = true := by
  unfold CompCert4Lean.Flocq.IEEE754.Binary.nan_pl
  change (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
        (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat q))) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z24 then true else false) = true
  have hqlog : Nat.log2 q < 23 :=
    (Nat.log2_lt (Nat.ne_of_gt hq)).2 hqlt
  have hdigits :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat
          (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat q)) =
        Nat.log2 q + 1 := by
    rw [quiet_nan_digits2_pos_nat]
    change Nat.log2
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat q)) + 1 =
      Nat.log2 q + 1
    rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat hq]
  have hdigitsInt : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
        (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat q))) =
      Int.ofNat (Nat.log2 q + 1) := by
    exact congrArg Int.ofNat hdigits
  rw [hdigitsInt]
  have hz24 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z24 = (24 : Int) := by
    decide
  rw [hz24]
  apply if_pos
  exact (Int.ofNat_lt).2 (by omega : Nat.log2 q + 1 < 24)

theorem Float32.abs_nan_result_obligation_proof : Float32.abs_nan_result_obligation := by
  intro f hf
  unfold Float32.abs_nan
  split
  · rename_i hnan
    have hparts : (exponent32 f == (2 ^ 8 - 1)) = true ∧
        (fraction32 f != 0) = true := by
      simpa only [isNaN32, Bool.and_eq_true] using hnan
    have hq : 0 < fraction32 f := by
      have hne : fraction32 f ≠ 0 := by simpa using hparts.2
      omega
    have hqlt : fraction32 f < 2 ^ 23 := by
      unfold fraction32
      exact Nat.mod_lt _ (Nat.two_pow_pos 23)
    unfold payload32
    rw [decode32_mkNaN_false (fraction32 f) hq hqlt]
    constructor
    · rfl
    · unfold CompCert4Lean.Flocq.IEEE754.Binary.BinaryFloatCertificate
      unfold CompCert4Lean.Flocq.IEEE754.Binary.B2FF
      unfold CompCert4Lean.Flocq.IEEE754.Binary.valid_binary
      change CompCert4Lean.Flocq.IEEE754.Binary.nan_pl (prec := z24)
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat
            (fraction32 f)) = true
      exact nan_pl_posOfNat_lt_23 (fraction32 f) hq hqlt
  · unfold default_nan_32 quiet_nan_32 quiet_nan_32_payload
    unfold CompCert4Lean.X86_64.Archi.default_nan_32
    dsimp only
    constructor <;> rfl

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

theorem default_nan_64_result_obligation_proof : default_nan_64_result_obligation := by
  unfold default_nan_64_result_obligation
  unfold default_nan_64 quiet_nan_64 quiet_nan_64_payload
  unfold CompCert4Lean.X86_64.Archi.default_nan_64 mkNaN64 decode64
  constructor
  · rfl
  · unfold CompCert4Lean.Flocq.IEEE754.Binary.BinaryFloatCertificate
    unfold CompCert4Lean.Flocq.IEEE754.Binary.valid_binary
    decide

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

theorem default_nan_32_result_obligation_proof : default_nan_32_result_obligation := by
  unfold default_nan_32_result_obligation
  unfold default_nan_32 quiet_nan_32 quiet_nan_32_payload
  unfold CompCert4Lean.X86_64.Archi.default_nan_32 mkNaN32 decode32
  constructor
  · rfl
  · unfold CompCert4Lean.Flocq.IEEE754.Binary.BinaryFloatCertificate
    unfold CompCert4Lean.Flocq.IEEE754.Binary.valid_binary
    decide

end CompCert4Lean.Lib.Floats
