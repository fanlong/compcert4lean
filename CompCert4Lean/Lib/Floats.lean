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

namespace CompCert4Lean.Lib.Floats
private theorem test_nan_aux_true (q : Nat) (hq : 0 < q) (hqlt : q < 2 ^ 23) :
    CompCert4Lean.Flocq.IEEE754.Bits.binary_float_of_bits_aux
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 23)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 8)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
          (4286578688 + q)) =
      CompCert4Lean.Flocq.IEEE754.Binary.F754_nan true
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
  rw [zdiv_nat (4286578688 + q) 8388608 (by omega)]
  rw [zmod_nat ((4286578688 + q) / 8388608) 256 (by omega)]
  change (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool _ _ then
      match CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo _ _ with
      | .Z0 => _ | .Zpos px => _ | .Zneg px => _
    else _) = _
  rw [zmod_nat (4286578688 + q) 8388608 (by omega)]
  have hqmod : (4286578688 + q) % 8388608 = q := by
    have hbase : 4286578688 = 511 * 8388608 := by decide
    rw [hbase, Nat.add_comm, Nat.mul_comm 511 8388608,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hqlt]
  have hqdiv : (4286578688 + q) / 8388608 = 511 := by
    have hbase : 4286578688 = 511 * 8388608 := by decide
    rw [hbase, Nat.add_comm, Nat.mul_comm 511 8388608,
      Nat.add_mul_div_left q 511 (by omega),
      Nat.div_eq_of_lt hqlt]
  rw [hqmod, hqdiv]
  simp only [show 511 % 256 = 255 by decide]
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
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (4286578688 + q)) = true := by
    unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.leb
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    rw [if_pos]
    have hfull : 2147483648 ≤ 4286578688 + q := by omega
    have hfullInt := (Int.ofNat_le).2 hfull
    rw [show Int.ofNat 8388608 * Int.ofNat 256 = Int.ofNat 2147483648 by decide]
    exact hfullInt
  simp only [CompCert4Lean.Flocq.IEEE754.Bits.Zle_bool,
    CompCert4Lean.Flocq.IEEE754.Bits.Zmul, hsign]
  simp only [CompCert4Lean.Flocq.IEEE754.Bits.Zmod,
    CompCert4Lean.Flocq.IEEE754.Bits.Zdiv,
    CompCert4Lean.Flocq.IEEE754.Bits.Zsub,
    CompCert4Lean.Flocq.IEEE754.Bits.Zone,
    CompCert4Lean.Flocq.IEEE754.Bits.Z0,
    CompCert4Lean.Flocq.IEEE754.Bits.Zadd]
  rw [← hz255]
  rw [zdiv_nat (4286578688 + q) 8388608 (by omega)]
  rw [zmod_nat ((4286578688 + q) / 8388608) 256 (by omega)]
  rw [hqdiv, show 511 % 256 = 255 by decide]
  rw [zmod_nat (4286578688 + q) 8388608 (by omega), hqmod, hqz]
  have h255ne : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 255 ≠
      CompCert4Lean.Flocq.Core.Zaux.Z0 := by decide
  rw [if_neg h255ne]
  have h255eq : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 255 =
      CompCert4Lean.Flocq.Core.Zaux.Zsub
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 256)
        CompCert4Lean.Flocq.Core.Zaux.Zone := by decide
  rw [if_pos h255eq]

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Lib

private theorem decode32_mkNaN_true (q : Nat) (hq : 0 < q) (hqlt : q < 2 ^ 23) :
    decode32
        (mkNaN32 true
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat q)) =
      (CompCert4Lean.Flocq.IEEE754.Binary.B754_nan true
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat q) :
        CompCert4Lean.Flocq.IEEE754.Bits.binary32) := by
  unfold decode32 mkNaN32
  dsimp only
  have hpayload :
      PArith.BinPos.Pos.to_nat
          (PArith.BinPos.Pos.of_nat q) = q := by
    change posToNat (posOfNat q) = q
    exact posToNat_posOfNat hq
  rw [hpayload, Nat.mod_eq_of_lt hqlt]
  simp only [if_true]
  rw [show (2 ^ 8 - 1) * 2 ^ 23 = 2139095040 by decide]
  have hbase : 2 ^ 31 + 2139095040 = 4286578688 := by decide
  rw [hbase, BitVec.toNat_ofNat]
  have hsum : 4286578688 + q < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt hsum]
  unfold CompCert4Lean.Flocq.IEEE754.Bits.b32_of_bits_unchecked
  unfold CompCert4Lean.Flocq.IEEE754.Bits.binary_float_of_bits_unchecked
  unfold CompCert4Lean.Flocq.IEEE754.Binary.FF2B_unchecked
  rw [test_nan_aux_true q hq hqlt]

theorem Float32.neg_nan_result_obligation_proof : Float32.neg_nan_result_obligation := by
  intro f hf
  unfold Float32.neg_nan
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
    cases hs : sign32 f with
    | false =>
        simp only [Bool.not_false]
        rw [decode32_mkNaN_true (fraction32 f) hq hqlt]
        constructor
        · rfl
        · unfold CompCert4Lean.Flocq.IEEE754.Binary.BinaryFloatCertificate
          unfold CompCert4Lean.Flocq.IEEE754.Binary.B2FF
          unfold CompCert4Lean.Flocq.IEEE754.Binary.valid_binary
          change CompCert4Lean.Flocq.IEEE754.Binary.nan_pl (prec := z24)
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat
                (fraction32 f)) = true
          exact nan_pl_posOfNat_lt_23 (fraction32 f) hq hqlt
    | true =>
        simp only [Bool.not_true]
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

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Lib

private theorem quiet_nan_32_payload_bounds (p : positive) :
    0 < PArith.BinPos.Pos.to_nat (quiet_nan_32_payload p) ∧
      PArith.BinPos.Pos.to_nat (quiet_nan_32_payload p) < 2 ^ 23 := by
  unfold quiet_nan_32_payload
  have hmod : (Nat.lor (PArith.BinPos.Pos.to_nat p) (2 ^ 22)) % (2 ^ 23) < 2 ^ 23 :=
    Nat.mod_lt _ (Nat.two_pow_pos 23)
  have hbit : ((Nat.lor (PArith.BinPos.Pos.to_nat p) (2 ^ 22)) % (2 ^ 23)).testBit 22 = true := by
    rw [Nat.testBit_mod_two_pow]
    simp only [Nat.lor_eq, Nat.testBit_or, Nat.testBit_two_pow_self, Bool.or_true]
    decide
  have hge := Nat.ge_two_pow_of_testBit hbit
  have hpow : 0 < 2 ^ 22 := Nat.two_pow_pos 22
  have hrpos : 0 < (Nat.lor (PArith.BinPos.Pos.to_nat p) (2 ^ 22)) % (2 ^ 23) := by
    omega
  change 0 < posToNat (posOfNat ((Nat.lor (PArith.BinPos.Pos.to_nat p) (2 ^ 22)) % (2 ^ 23))) ∧
    posToNat (posOfNat ((Nat.lor (PArith.BinPos.Pos.to_nat p) (2 ^ 22)) % (2 ^ 23))) < 2 ^ 23
  rw [posToNat_posOfNat hrpos]
  exact ⟨hrpos, hmod⟩

private theorem decode32_quiet_nan (s : Bool) (p : positive) :
    decode32 (quiet_nan_32 (s, p)) =
      (CompCert4Lean.Flocq.IEEE754.Binary.B754_nan s
        (quiet_nan_32_payload p) : CompCert4Lean.Flocq.IEEE754.Bits.binary32) := by
  have hbounds := quiet_nan_32_payload_bounds p
  have hpayload :
      PArith.BinPos.Pos.of_nat (PArith.BinPos.Pos.to_nat (quiet_nan_32_payload p)) =
        quiet_nan_32_payload p :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat_posToNat
      (quiet_nan_32_payload p)
  cases s with
  | false =>
      unfold quiet_nan_32
      rw [← hpayload]
      exact decode32_mkNaN_false
        (PArith.BinPos.Pos.to_nat (quiet_nan_32_payload p)) hbounds.1 hbounds.2
  | true =>
      unfold quiet_nan_32
      rw [← hpayload]
      exact decode32_mkNaN_true
        (PArith.BinPos.Pos.to_nat (quiet_nan_32_payload p)) hbounds.1 hbounds.2

private theorem quiet_nan_32_result_obligation_proof_local : quiet_nan_32_result_obligation := by
  intro sp
  rw [decode32_quiet_nan sp.1 sp.2]
  constructor
  · rfl
  · unfold CompCert4Lean.Flocq.IEEE754.Binary.BinaryFloatCertificate
    unfold CompCert4Lean.Flocq.IEEE754.Binary.B2FF
    unfold CompCert4Lean.Flocq.IEEE754.Binary.valid_binary
    have hpayload :
        PArith.BinPos.Pos.of_nat (PArith.BinPos.Pos.to_nat (quiet_nan_32_payload sp.2)) =
          quiet_nan_32_payload sp.2 :=
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat_posToNat
        (quiet_nan_32_payload sp.2)
    change CompCert4Lean.Flocq.IEEE754.Binary.nan_pl (prec := z24)
      (quiet_nan_32_payload sp.2) = true
    rw [← hpayload]
    exact nan_pl_posOfNat_lt_23
      (PArith.BinPos.Pos.to_nat (quiet_nan_32_payload sp.2))
      (quiet_nan_32_payload_bounds sp.2).1
      (quiet_nan_32_payload_bounds sp.2).2

theorem Float.to_single_nan_result_obligation_proof : Float.to_single_nan_result_obligation := by
  intro f hf
  unfold Float.to_single_nan
  split
  · rename_i hnan
    simp only [CompCert4Lean.X86_64.Archi.float_conversion_default_nan, Bool.false_eq_true,
      ↓reduceIte]
    exact quiet_nan_32_result_obligation_proof_local (sign64 f, reduce_nan_payload (payload64 f))
  · exact default_nan_32_result_obligation_proof

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

theorem Float32.binop_nan_result_obligation_proof : Float32.binop_nan_result_obligation := by
  intro x y _hx _hy
  exact quiet_nan_32_result_obligation_proof_local
    (CompCert4Lean.X86_64.Archi.choose_nan_32
      (Float32.cons_pl x (Float32.cons_pl y [])))

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Lib

private theorem zmod_nat_f64 (a b : Nat) (hb : 0 < b) :
    ZArith.BinInt.Z.modulo (ZArith.BinInt.Z.of_nat a)
        (ZArith.BinInt.Z.of_nat b) = ZArith.BinInt.Z.of_nat (a % b) := by
  have hdecomp :
      ZArith.BinInt.Z.of_nat a =
        ZArith.BinInt.Z.add (ZArith.BinInt.Z.of_nat (a % b))
          (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.of_nat (a / b))
            (ZArith.BinInt.Z.of_nat b)) := by
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.add,
      ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    calc
      Int.ofNat a = Int.ofNat (a % b + b * (a / b)) := by
        congr 1
        exact (Nat.mod_add_div a b).symm
      _ = Int.ofNat (a % b + (a / b) * b) := by rw [Nat.mul_comm]
  rw [hdecomp, ZArith.BinInt.Z.modulo_add_mul]
  apply ZArith.BinInt.Z.mod_small
  constructor
  · change intOfZ ZArith.BinInt.Z.Z0 ≤ intOfZ (ZArith.BinInt.Z.of_nat (a % b))
    simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
    change (0 : Int) ≤ Int.ofNat (a % b)
    exact Int.ofNat_nonneg _
  · change intOfZ (ZArith.BinInt.Z.of_nat (a % b)) <
      intOfZ (ZArith.BinInt.Z.of_nat b)
    simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
    exact (Int.ofNat_lt).2 (Nat.mod_lt a hb)

private theorem zdiv_nat_f64 (a b : Nat) (hb : 0 < b) :
    ZArith.BinInt.Z.div (ZArith.BinInt.Z.of_nat a)
        (ZArith.BinInt.Z.of_nat b) = ZArith.BinInt.Z.of_nat (a / b) := by
  have hiden :=
    ZArith.Zdiv.Z_div_mod_eq_full
      (ZArith.BinInt.Z.of_nat a) (ZArith.BinInt.Z.of_nat b)
  rw [zmod_nat_f64 a b hb] at hiden
  have hiden' := congrArg intOfZ hiden
  simp only [ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.add,
    ZArith.BinInt.Z.mul, intOfZ_zOfInt] at hiden'
  have hcast : Int.ofNat a = Int.ofNat b * Int.ofNat (a / b) + Int.ofNat (a % b) := by
    calc
      Int.ofNat a = Int.ofNat (a % b + b * (a / b)) := by
        congr 1
        exact (Nat.mod_add_div a b).symm
      _ = Int.ofNat (b * (a / b) + a % b) := by rw [Nat.add_comm]
      _ = Int.ofNat b * Int.ofNat (a / b) + Int.ofNat (a % b) := by
        simp
  have hsum : Int.ofNat b * intOfZ
        (ZArith.BinInt.Z.div (ZArith.BinInt.Z.of_nat a)
          (ZArith.BinInt.Z.of_nat b)) + Int.ofNat (a % b) =
      Int.ofNat b * Int.ofNat (a / b) + Int.ofNat (a % b) := hiden'.symm.trans hcast
  have hprod : Int.ofNat b * intOfZ
        (ZArith.BinInt.Z.div (ZArith.BinInt.Z.of_nat a)
          (ZArith.BinInt.Z.of_nat b)) = Int.ofNat b * Int.ofNat (a / b) := by
    apply Int.add_left_cancel (a := Int.ofNat (a % b))
    simpa [Int.add_comm] using hsum
  apply intOfZ_injective
  have hbI : Int.ofNat b ≠ 0 := (Int.ofNat_ne_zero).2 (Nat.ne_of_gt hb)
  have hqcast : intOfZ
        (ZArith.BinInt.Z.of_nat (a / b)) = Int.ofNat (a / b) := by
    exact intOfZ_zOfInt _
  exact Int.eq_of_mul_eq_mul_left hbI (hprod.trans (by rw [hqcast]))

private theorem expand_nan_pos_bounds (p : positive)
    (h : Binary.nan_pl (prec := z24) p = true) :
    0 < PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.shiftl_nat p 29) ∧
      PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.shiftl_nat p 29) < 2 ^ 52 := by
  have hp : 0 < PArith.BinPos.Pos.to_nat p :=
    posToNat_positive p
  have hdigits := quiet_nan_digits2_pos_nat p
  unfold Binary.nan_pl at h
  change (if intOfZ (Zpos
      (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos p)) <
      intOfZ z24 then true else false) = true at h
  simp at h
  change Int.ofNat (PArith.BinPos.Pos.to_nat
      (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos p)) <
    24 at h
  rw [hdigits] at h
  have hlog : Nat.log2 (PArith.BinPos.Pos.to_nat p) < 23 := by
    change Int.ofNat (Nat.log2 (PArith.BinPos.Pos.to_nat p) + 1) < 24 at h
    have hnat : Nat.log2 (PArith.BinPos.Pos.to_nat p) + 1 < 24 :=
      (Int.ofNat_lt).mp h
    omega
  have hp_lt : PArith.BinPos.Pos.to_nat p < 2 ^ 23 := by
    exact (Nat.log2_lt (Nat.ne_of_gt hp)).1 (by omega)
  unfold PArith.BinPos.Pos.shiftl_nat
  have hshiftpos : 0 < PArith.BinPos.Pos.to_nat p * 2 ^ 29 :=
    Nat.mul_pos hp (Nat.two_pow_pos 29)
  change 0 < posToNat (posOfNat (posToNat p * 2 ^ 29)) ∧
    posToNat (posOfNat (posToNat p * 2 ^ 29)) < 2 ^ 52
  have hshiftpos' : 0 < posToNat p * 2 ^ 29 := by exact hshiftpos
  rw [posToNat_posOfNat hshiftpos']
  constructor
  · exact hshiftpos
  · have hmul := Nat.mul_lt_mul_of_pos_right hp_lt (Nat.two_pow_pos 29)
    rw [show (2 ^ 23 : Nat) * 2 ^ 29 = 2 ^ 52 by
      rw [← Nat.pow_add]] at hmul
    exact hmul

private theorem test_nan_aux64_false (q : Nat) (hq : 0 < q) (hqlt : q < 2 ^ 52) :
    CompCert4Lean.Flocq.IEEE754.Bits.binary_float_of_bits_aux
        (ZArith.BinInt.Z.of_nat 52)
        (ZArith.BinInt.Z.of_nat 11)
        (ZArith.BinInt.Z.of_nat (9218868437227405312 + q)) =
      CompCert4Lean.Flocq.IEEE754.Binary.F754_nan false
        (PArith.BinPos.Pos.of_nat q) := by
  unfold CompCert4Lean.Flocq.IEEE754.Bits.binary_float_of_bits_aux
  unfold CompCert4Lean.Flocq.IEEE754.Bits.split_bits
  dsimp only
  have h52 : CompCert4Lean.Flocq.IEEE754.Bits.Zpower
      CompCert4Lean.Flocq.IEEE754.Bits.Ztwo (ZArith.BinInt.Z.of_nat 52) =
      ZArith.BinInt.Z.of_nat 4503599627370496 := by decide
  have h11 : CompCert4Lean.Flocq.IEEE754.Bits.Zpower
      CompCert4Lean.Flocq.IEEE754.Bits.Ztwo (ZArith.BinInt.Z.of_nat 11) =
      ZArith.BinInt.Z.of_nat 2048 := by decide
  rw [h52, h11]
  have hdiv : (9218868437227405312 + q) / 4503599627370496 = 2047 := by
    have hbase : 9218868437227405312 = 2047 * 4503599627370496 := by decide
    rw [hbase, Nat.add_comm, Nat.mul_comm 2047 4503599627370496,
      Nat.add_mul_div_left q 2047 (by omega), Nat.div_eq_of_lt hqlt]
  have hmod : (9218868437227405312 + q) % 4503599627370496 = q := by
    have hbase : 9218868437227405312 = 2047 * 4503599627370496 := by decide
    rw [hbase, Nat.add_comm, Nat.mul_comm 2047 4503599627370496,
      Nat.add_mul_mod_self_left q 4503599627370496 2047, Nat.mod_eq_of_lt hqlt]
  have hzdiv : CompCert4Lean.Flocq.IEEE754.Bits.Zdiv
      (ZArith.BinInt.Z.of_nat (9218868437227405312 + q))
      (ZArith.BinInt.Z.of_nat 4503599627370496) =
      ZArith.BinInt.Z.of_nat 2047 := by
    change ZArith.BinInt.Z.div
      (ZArith.BinInt.Z.of_nat (9218868437227405312 + q))
      (ZArith.BinInt.Z.of_nat 4503599627370496) = _
    rw [zdiv_nat_f64 (9218868437227405312 + q) 4503599627370496 (by decide), hdiv]
  rw [hzdiv]
  have hzmod2047 : CompCert4Lean.Flocq.IEEE754.Bits.Zmod
      (ZArith.BinInt.Z.of_nat 2047) (ZArith.BinInt.Z.of_nat 2048) =
      ZArith.BinInt.Z.of_nat 2047 := by
    change ZArith.BinInt.Z.modulo
      (ZArith.BinInt.Z.of_nat 2047) (ZArith.BinInt.Z.of_nat 2048) = _
    exact zmod_nat_f64 2047 2048 (by decide)
  rw [hzmod2047]
  have hz : CompCert4Lean.Flocq.IEEE754.Bits.Zeq_bool
      (ZArith.BinInt.Z.of_nat 2047)
      CompCert4Lean.Flocq.IEEE754.Bits.Z0 = false := by decide
  rw [hz]
  have hsub : ZArith.BinInt.Z.sub (ZArith.BinInt.Z.of_nat 2048)
      CompCert4Lean.Flocq.IEEE754.Bits.Zone =
      ZArith.BinInt.Z.of_nat 2047 := by decide
  have heq : CompCert4Lean.Flocq.IEEE754.Bits.Zeq_bool
      (ZArith.BinInt.Z.of_nat 2047)
      (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.of_nat 2048)
        CompCert4Lean.Flocq.IEEE754.Bits.Zone) = true := by
    rw [hsub]
    decide
  have hzmod : CompCert4Lean.Flocq.IEEE754.Bits.Zmod
      (ZArith.BinInt.Z.of_nat (9218868437227405312 + q))
      (ZArith.BinInt.Z.of_nat 4503599627370496) =
      ZArith.BinInt.Z.of_nat q := by
    change ZArith.BinInt.Z.modulo
      (ZArith.BinInt.Z.of_nat (9218868437227405312 + q))
      (ZArith.BinInt.Z.of_nat 4503599627370496) = _
    rw [zmod_nat_f64 (9218868437227405312 + q) 4503599627370496 (by decide), hmod]
  rw [heq, hzmod]
  have hqz : ZArith.BinInt.Z.of_nat q = Zpos (PArith.BinPos.Pos.of_nat q) := by
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
    exact congrArg Int.ofNat (posToNat_posOfNat hq).symm
  rw [hqz]
  have hsign : CompCert4Lean.Flocq.IEEE754.Bits.Zle_bool
      (CompCert4Lean.Flocq.IEEE754.Bits.Zmul
        (ZArith.BinInt.Z.of_nat 4503599627370496)
        (ZArith.BinInt.Z.of_nat 2048))
      (ZArith.BinInt.Z.of_nat (9218868437227405312 + q)) = false := by
    apply CompCert4Lean.Flocq.Core.Zaux.Zle_bool_false
    change intOfZ (ZArith.BinInt.Z.of_nat (9218868437227405312 + q)) <
      intOfZ (ZArith.BinInt.Z.mul
        (ZArith.BinInt.Z.of_nat 4503599627370496)
        (ZArith.BinInt.Z.of_nat 2048))
    simp only [ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    rw [show Int.ofNat 4503599627370496 * Int.ofNat 2048 =
      Int.ofNat 9223372036854775808 by decide]
    have hfull : 9218868437227405312 + q < 9223372036854775808 := by omega
    have hfullInt := (Int.ofNat_lt).2 hfull
    exact hfullInt
  rw [hsign]
  simp

private theorem test_nan_aux64_true (q : Nat) (hq : 0 < q) (hqlt : q < 2 ^ 52) :
    CompCert4Lean.Flocq.IEEE754.Bits.binary_float_of_bits_aux
        (ZArith.BinInt.Z.of_nat 52)
        (ZArith.BinInt.Z.of_nat 11)
        (ZArith.BinInt.Z.of_nat (18442240474082181120 + q)) =
      CompCert4Lean.Flocq.IEEE754.Binary.F754_nan true
        (PArith.BinPos.Pos.of_nat q) := by
  unfold CompCert4Lean.Flocq.IEEE754.Bits.binary_float_of_bits_aux
  unfold CompCert4Lean.Flocq.IEEE754.Bits.split_bits
  dsimp only
  have h52 : CompCert4Lean.Flocq.IEEE754.Bits.Zpower
      CompCert4Lean.Flocq.IEEE754.Bits.Ztwo (ZArith.BinInt.Z.of_nat 52) =
      ZArith.BinInt.Z.of_nat 4503599627370496 := by decide
  have h11 : CompCert4Lean.Flocq.IEEE754.Bits.Zpower
      CompCert4Lean.Flocq.IEEE754.Bits.Ztwo (ZArith.BinInt.Z.of_nat 11) =
      ZArith.BinInt.Z.of_nat 2048 := by decide
  rw [h52, h11]
  have hdiv : (18442240474082181120 + q) / 4503599627370496 = 4095 := by
    have hbase : 18442240474082181120 = 4095 * 4503599627370496 := by decide
    rw [hbase, Nat.add_comm, Nat.mul_comm 4095 4503599627370496,
      Nat.add_mul_div_left q 4095 (by omega), Nat.div_eq_of_lt hqlt]
  have hmod : (18442240474082181120 + q) % 4503599627370496 = q := by
    have hbase : 18442240474082181120 = 4095 * 4503599627370496 := by decide
    rw [hbase, Nat.add_comm, Nat.mul_comm 4095 4503599627370496,
      Nat.add_mul_mod_self_left q 4503599627370496 4095, Nat.mod_eq_of_lt hqlt]
  have hzdiv : CompCert4Lean.Flocq.IEEE754.Bits.Zdiv
      (ZArith.BinInt.Z.of_nat (18442240474082181120 + q))
      (ZArith.BinInt.Z.of_nat 4503599627370496) =
      ZArith.BinInt.Z.of_nat 4095 := by
    change ZArith.BinInt.Z.div
      (ZArith.BinInt.Z.of_nat (18442240474082181120 + q))
      (ZArith.BinInt.Z.of_nat 4503599627370496) = _
    rw [zdiv_nat_f64 (18442240474082181120 + q) 4503599627370496 (by decide), hdiv]
  rw [hzdiv]
  have hzmod4095 : CompCert4Lean.Flocq.IEEE754.Bits.Zmod
      (ZArith.BinInt.Z.of_nat 4095) (ZArith.BinInt.Z.of_nat 2048) =
      ZArith.BinInt.Z.of_nat 2047 := by
    change ZArith.BinInt.Z.modulo
      (ZArith.BinInt.Z.of_nat 4095) (ZArith.BinInt.Z.of_nat 2048) = _
    exact zmod_nat_f64 4095 2048 (by decide)
  rw [hzmod4095]
  have hz : CompCert4Lean.Flocq.IEEE754.Bits.Zeq_bool
      (ZArith.BinInt.Z.of_nat 2047)
      CompCert4Lean.Flocq.IEEE754.Bits.Z0 = false := by decide
  rw [hz]
  have hsub : ZArith.BinInt.Z.sub (ZArith.BinInt.Z.of_nat 2048)
      CompCert4Lean.Flocq.IEEE754.Bits.Zone =
      ZArith.BinInt.Z.of_nat 2047 := by decide
  have heq : CompCert4Lean.Flocq.IEEE754.Bits.Zeq_bool
      (ZArith.BinInt.Z.of_nat 2047)
      (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.of_nat 2048)
        CompCert4Lean.Flocq.IEEE754.Bits.Zone) = true := by
    rw [hsub]
    decide
  have hzmod : CompCert4Lean.Flocq.IEEE754.Bits.Zmod
      (ZArith.BinInt.Z.of_nat (18442240474082181120 + q))
      (ZArith.BinInt.Z.of_nat 4503599627370496) =
      ZArith.BinInt.Z.of_nat q := by
    change ZArith.BinInt.Z.modulo
      (ZArith.BinInt.Z.of_nat (18442240474082181120 + q))
      (ZArith.BinInt.Z.of_nat 4503599627370496) = _
    rw [zmod_nat_f64 (18442240474082181120 + q) 4503599627370496 (by decide), hmod]
  rw [heq, hzmod]
  have hqz : ZArith.BinInt.Z.of_nat q = Zpos (PArith.BinPos.Pos.of_nat q) := by
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
    exact congrArg Int.ofNat (posToNat_posOfNat hq).symm
  rw [hqz]
  have hsign : CompCert4Lean.Flocq.IEEE754.Bits.Zle_bool
      (CompCert4Lean.Flocq.IEEE754.Bits.Zmul
        (ZArith.BinInt.Z.of_nat 4503599627370496)
        (ZArith.BinInt.Z.of_nat 2048))
      (ZArith.BinInt.Z.of_nat (18442240474082181120 + q)) = true := by
    apply CompCert4Lean.Flocq.Core.Zaux.Zle_bool_true
    change intOfZ (ZArith.BinInt.Z.mul
        (ZArith.BinInt.Z.of_nat 4503599627370496)
        (ZArith.BinInt.Z.of_nat 2048)) ≤
      intOfZ (ZArith.BinInt.Z.of_nat (18442240474082181120 + q))
    simp only [ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    rw [show Int.ofNat 4503599627370496 * Int.ofNat 2048 =
      Int.ofNat 9223372036854775808 by decide]
    exact (Int.ofNat_le).2 (by omega)
  rw [hsign]
  simp

private theorem decode64_mkNaN (s : Bool) (q : Nat) (hq : 0 < q) (hqlt : q < 2 ^ 52) :
    decode64 (mkNaN64 s (PArith.BinPos.Pos.of_nat q)) =
      (CompCert4Lean.Flocq.IEEE754.Binary.B754_nan s
        (PArith.BinPos.Pos.of_nat q) : CompCert4Lean.Flocq.IEEE754.Bits.binary64) := by
  cases s with
  | false =>
      unfold decode64 mkNaN64
      dsimp only
      have hpayload : PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.of_nat q) = q := by
        change posToNat (posOfNat q) = q
        exact posToNat_posOfNat hq
      rw [hpayload, Nat.mod_eq_of_lt hqlt]
      have hexp : (2 ^ 11 - 1) * 2 ^ 52 = 9218868437227405312 := by decide
      rw [hexp]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [BitVec.toNat_ofNat]
      have hsum : 9218868437227405312 + q < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hsum]
      unfold CompCert4Lean.Flocq.IEEE754.Bits.b64_of_bits_unchecked
      unfold CompCert4Lean.Flocq.IEEE754.Bits.binary_float_of_bits_unchecked
      unfold CompCert4Lean.Flocq.IEEE754.Binary.FF2B_unchecked
      rw [test_nan_aux64_false q hq hqlt]
  | true =>
      unfold decode64 mkNaN64
      dsimp only
      have hpayload : PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.of_nat q) = q := by
        change posToNat (posOfNat q) = q
        exact posToNat_posOfNat hq
      rw [hpayload, Nat.mod_eq_of_lt hqlt]
      have hexp : (2 ^ 11 - 1) * 2 ^ 52 = 9218868437227405312 := by decide
      rw [hexp]
      have hbase : 2 ^ 63 + 9218868437227405312 = 18442240474082181120 := by decide
      simp
      have hsum : 18442240474082181120 + q < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hsum]
      unfold CompCert4Lean.Flocq.IEEE754.Bits.b64_of_bits_unchecked
      unfold CompCert4Lean.Flocq.IEEE754.Bits.binary_float_of_bits_unchecked
      unfold CompCert4Lean.Flocq.IEEE754.Binary.FF2B_unchecked
      rw [test_nan_aux64_true q hq hqlt]

private theorem nan_pl_posOfNat_lt_52 (q : Nat) (hq : 0 < q) (hqlt : q < 2 ^ 52) :
    CompCert4Lean.Flocq.IEEE754.Binary.nan_pl (prec := z53)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat q) = true := by
  unfold CompCert4Lean.Flocq.IEEE754.Binary.nan_pl
  change (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
        (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat q))) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z53 then true else false) = true
  have hqlog : Nat.log2 q < 52 :=
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
  have hz53 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z53 = (53 : Int) := by
    decide
  rw [hz53]
  apply if_pos
  exact (Int.ofNat_lt).2 (by omega : Nat.log2 q + 1 < 53)

theorem Float.expand_nan_result_obligation_proof : Float.expand_nan_result_obligation := by
  intro s p h
  have hq := expand_nan_pos_bounds p h
  unfold Float.expand_nan
  have hpayload : PArith.BinPos.Pos.of_nat
      (PArith.BinPos.Pos.to_nat (Float.expand_nan_payload p)) =
      Float.expand_nan_payload p :=
    posOfNat_posToNat (Float.expand_nan_payload p)
  rw [← hpayload]
  have hdecode := decode64_mkNaN s
      (PArith.BinPos.Pos.to_nat (Float.expand_nan_payload p))
      hq.1 hq.2
  rw [hdecode]
  constructor
  · rfl
  · unfold CompCert4Lean.Flocq.IEEE754.Binary.BinaryFloatCertificate
    unfold CompCert4Lean.Flocq.IEEE754.Binary.B2FF
    unfold CompCert4Lean.Flocq.IEEE754.Binary.valid_binary
    change CompCert4Lean.Flocq.IEEE754.Binary.nan_pl (prec := z53)
      (PArith.BinPos.Pos.of_nat
        (PArith.BinPos.Pos.to_nat (Float.expand_nan_payload p))) = true
    exact nan_pl_posOfNat_lt_52
      (PArith.BinPos.Pos.to_nat (Float.expand_nan_payload p)) hq.1 hq.2

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Lib

private theorem quiet_nan_64_payload_bounds (p : positive) :
    0 < PArith.BinPos.Pos.to_nat (quiet_nan_64_payload p) ∧
      PArith.BinPos.Pos.to_nat (quiet_nan_64_payload p) < 2 ^ 52 := by
  unfold quiet_nan_64_payload
  have hmod : (Nat.lor (PArith.BinPos.Pos.to_nat p) (2 ^ 51)) % (2 ^ 52) < 2 ^ 52 :=
    Nat.mod_lt _ (Nat.two_pow_pos 52)
  have hbit : ((Nat.lor (PArith.BinPos.Pos.to_nat p) (2 ^ 51)) % (2 ^ 52)).testBit 51 = true := by
    rw [Nat.testBit_mod_two_pow]
    simp only [Nat.lor_eq, Nat.testBit_or, Nat.testBit_two_pow_self, Bool.or_true]
    decide
  have hge := Nat.ge_two_pow_of_testBit hbit
  have hpow : 0 < 2 ^ 51 := Nat.two_pow_pos 51
  have hrpos : 0 < (Nat.lor (PArith.BinPos.Pos.to_nat p) (2 ^ 51)) % (2 ^ 52) := by
    omega
  change 0 < posToNat (posOfNat ((Nat.lor (PArith.BinPos.Pos.to_nat p) (2 ^ 51)) % (2 ^ 52))) ∧
    posToNat (posOfNat ((Nat.lor (PArith.BinPos.Pos.to_nat p) (2 ^ 51)) % (2 ^ 52))) < 2 ^ 52
  rw [posToNat_posOfNat hrpos]
  exact ⟨hrpos, hmod⟩

private theorem decode64_quiet_nan (s : Bool) (p : positive) :
    decode64 (quiet_nan_64 (s, p)) =
      (CompCert4Lean.Flocq.IEEE754.Binary.B754_nan s
        (quiet_nan_64_payload p) : CompCert4Lean.Flocq.IEEE754.Bits.binary64) := by
  have hbounds := quiet_nan_64_payload_bounds p
  have hpayload :
      PArith.BinPos.Pos.of_nat (PArith.BinPos.Pos.to_nat (quiet_nan_64_payload p)) =
        quiet_nan_64_payload p :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat_posToNat
      (quiet_nan_64_payload p)
  cases s with
  | false =>
      unfold quiet_nan_64
      rw [← hpayload]
      exact decode64_mkNaN false
        (PArith.BinPos.Pos.to_nat (quiet_nan_64_payload p)) hbounds.1 hbounds.2
  | true =>
      unfold quiet_nan_64
      rw [← hpayload]
      exact decode64_mkNaN true
        (PArith.BinPos.Pos.to_nat (quiet_nan_64_payload p)) hbounds.1 hbounds.2

private theorem quiet_nan_64_result_obligation_proof_local : quiet_nan_64_result_obligation := by
  intro sp
  rw [decode64_quiet_nan sp.1 sp.2]
  constructor
  · rfl
  · unfold CompCert4Lean.Flocq.IEEE754.Binary.BinaryFloatCertificate
    unfold CompCert4Lean.Flocq.IEEE754.Binary.B2FF
    unfold CompCert4Lean.Flocq.IEEE754.Binary.valid_binary
    have hpayload :
        PArith.BinPos.Pos.of_nat (PArith.BinPos.Pos.to_nat (quiet_nan_64_payload sp.2)) =
          quiet_nan_64_payload sp.2 :=
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat_posToNat
        (quiet_nan_64_payload sp.2)
    change CompCert4Lean.Flocq.IEEE754.Binary.nan_pl (prec := z53)
      (quiet_nan_64_payload sp.2) = true
    rw [← hpayload]
    exact nan_pl_posOfNat_lt_52
      (PArith.BinPos.Pos.to_nat (quiet_nan_64_payload sp.2))
      (quiet_nan_64_payload_bounds sp.2).1
      (quiet_nan_64_payload_bounds sp.2).2

theorem quiet_nan_64_result_obligation_proof : quiet_nan_64_result_obligation :=
  quiet_nan_64_result_obligation_proof_local

theorem Float.neg_nan_result_obligation_proof : Float.neg_nan_result_obligation := by
  intro f hf
  unfold Float.neg_nan
  split
  · rename_i hnan
    have hparts : (exponent64 f == (2 ^ 11 - 1)) = true ∧
        (fraction64 f != 0) = true := by
      simpa only [isNaN64, Bool.and_eq_true] using hnan
    have hq : 0 < fraction64 f := by
      have hne : fraction64 f ≠ 0 := by simpa using hparts.2
      omega
    have hqlt : fraction64 f < 2 ^ 52 := by
      unfold fraction64
      exact Nat.mod_lt _ (Nat.two_pow_pos 52)
    unfold payload64
    cases hs : sign64 f with
    | false =>
        simp only [Bool.not_false]
        rw [decode64_mkNaN true (fraction64 f) hq hqlt]
        constructor
        · rfl
        · unfold CompCert4Lean.Flocq.IEEE754.Binary.BinaryFloatCertificate
          unfold CompCert4Lean.Flocq.IEEE754.Binary.B2FF
          unfold CompCert4Lean.Flocq.IEEE754.Binary.valid_binary
          change CompCert4Lean.Flocq.IEEE754.Binary.nan_pl (prec := z53)
              (PArith.BinPos.Pos.of_nat (fraction64 f)) = true
          exact nan_pl_posOfNat_lt_52 (fraction64 f) hq hqlt
    | true =>
        simp only [Bool.not_true]
        rw [decode64_mkNaN false (fraction64 f) hq hqlt]
        constructor
        · rfl
        · unfold CompCert4Lean.Flocq.IEEE754.Binary.BinaryFloatCertificate
          unfold CompCert4Lean.Flocq.IEEE754.Binary.B2FF
          unfold CompCert4Lean.Flocq.IEEE754.Binary.valid_binary
          change CompCert4Lean.Flocq.IEEE754.Binary.nan_pl (prec := z53)
              (PArith.BinPos.Pos.of_nat (fraction64 f)) = true
          exact nan_pl_posOfNat_lt_52 (fraction64 f) hq hqlt
  · exact default_nan_64_result_obligation_proof

theorem Float.of_single_nan_result_obligation_proof : Float.of_single_nan_result_obligation := by
  intro f hf
  unfold Float.of_single_nan
  split
  · rename_i hnan
    simp only [CompCert4Lean.X86_64.Archi.float_conversion_default_nan, Bool.false_eq_true,
      ↓reduceIte]
    exact quiet_nan_64_result_obligation_proof_local
      (sign32 f, Float.expand_nan_payload (payload32 f))
  · exact default_nan_64_result_obligation_proof

theorem Float.unop_nan_result_obligation_proof : Float.unop_nan_result_obligation := by
  intro x hx
  unfold Float.unop_nan
  exact quiet_nan_64_result_obligation_proof_local
    (CompCert4Lean.X86_64.Archi.choose_nan_64 (Float.cons_pl x []))

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Flocq.IEEE754

theorem Float.expand_nan_proof : Float.expand_nan_proofStatement := by
  intro p h
  have hq := expand_nan_pos_bounds p h
  have hpayload :
      PArith.BinPos.Pos.of_nat (PArith.BinPos.Pos.to_nat (Float.expand_nan_payload p)) =
        Float.expand_nan_payload p :=
    posOfNat_posToNat (Float.expand_nan_payload p)
  rw [← hpayload]
  exact nan_pl_posOfNat_lt_52
    (PArith.BinPos.Pos.to_nat (Float.expand_nan_payload p)) hq.1 hq.2

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

namespace Float

private theorem unpacked_mul_comm_worker (a b : _root_.Float.Model.UnpackedFloat) :
    _root_.Float.Model.UnpackedFloat.mul _root_.Float.Model.Format.binary64 a b =
      _root_.Float.Model.UnpackedFloat.mul _root_.Float.Model.Format.binary64 b a := by
  cases a with
  | notANumber => cases b <;> rfl
  | infinity sa =>
      cases b with
      | notANumber => rfl
      | infinity sb => cases sa <;> cases sb <;> rfl
      | zero sb => cases sa <;> cases sb <;> rfl
      | finite sb mb eb hb => cases sa <;> cases sb <;> rfl
  | zero sa =>
      cases b with
      | notANumber => rfl
      | infinity sb => cases sa <;> cases sb <;> rfl
      | zero sb => cases sa <;> cases sb <;> rfl
      | finite sb mb eb hb => cases sa <;> cases sb <;> rfl
  | finite sa ma ea ha =>
      cases b with
      | notANumber => rfl
      | infinity sb => cases sa <;> cases sb <;> rfl
      | zero sb => cases sa <;> cases sb <;> rfl
      | finite sb mb eb hb =>
          cases sa <;> cases sb <;>
            simp [_root_.Float.Model.UnpackedFloat.mul, Nat.mul_comm, Int.add_comm]
          all_goals rfl

private theorem model_mul_comm_worker (x y : float) :
    modelBinary64
      (_root_.Float.Model.UnpackedFloat.mul _root_.Float.Model.Format.binary64) x y =
      modelBinary64
      (_root_.Float.Model.UnpackedFloat.mul _root_.Float.Model.Format.binary64) y x := by
  unfold modelBinary64
  rw [unpacked_mul_comm_worker]

theorem mul_commut : Float.mul_commutStatement := by
  intro x y h
  unfold Float.mul
  rw [model_mul_comm_worker]
  by_cases hx : isNaN64 x = true
  · by_cases hy : isNaN64 y = true
    · exfalso
      rcases h with h | h <;> simp_all
    · simp [finishBinary, binop_nan, cons_pl, hx, hy]
  · by_cases hy : isNaN64 y = true
    · simp [finishBinary, binop_nan, cons_pl, hx, hy]
    · simp [finishBinary, hx, hy]

end Float

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Lib

namespace Float

private theorem raw_zcompare_swap (x y : Z) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.compare y x =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.compare x y) := by
  change
    (if intOfZ y < intOfZ x then Lt else
      if intOfZ y = intOfZ x then Eq else Gt) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp
        (if intOfZ x < intOfZ y then Lt else
          if intOfZ x = intOfZ y then Eq else Gt)
  by_cases hxy : intOfZ x < intOfZ y
  · have hyx : ¬ intOfZ y < intOfZ x := by omega
    have hne : intOfZ y ≠ intOfZ x := by omega
    simp [hxy, hyx, hne,
      CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.CompOpp]
  · by_cases hxy' : intOfZ x = intOfZ y
    · have hyx : ¬ intOfZ y < intOfZ x := by omega
      simp [hxy, hxy', hyx,
        CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.CompOpp]
    · have hyx : intOfZ y < intOfZ x := by omega
      simp [hxy, hxy', hyx,
        CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.CompOpp]

private theorem raw_poscompare_swap (x y : positive) :
    CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posCompare Eq y x =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp
        (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posCompare Eq x y) := by
  change
    (if posToNat y < posToNat x then Lt else
      if posToNat y = posToNat x then Eq else Gt) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp
        (if posToNat x < posToNat y then Lt else
          if posToNat x = posToNat y then Eq else Gt)
  by_cases hxy : posToNat x < posToNat y
  · have hyx : ¬ posToNat y < posToNat x := by omega
    have hne : posToNat y ≠ posToNat x := by omega
    simp [hxy, hyx, hne,
      CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.CompOpp]
  · by_cases hxy' : posToNat x = posToNat y
    · have hyx : ¬ posToNat y < posToNat x := by omega
      simp [hxy, hxy', hyx,
        CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.CompOpp]
    · have hyx : posToNat y < posToNat x := by omega
      simp [hxy, hxy', hyx,
        CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.CompOpp]

private theorem raw_sfcompare_swap
    (x y : CompCert4Lean.Flocq.IEEE754.BinarySingleNaN.spec_float) :
    CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.SFcompare y x =
      match CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.SFcompare x y with
      | some c => some (CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp c)
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
  | S754_nan => cases y <;> rfl
  | S754_finite sx mx ex =>
      cases y with
      | S754_zero sy => cases sx <;> rfl
      | S754_infinity sy => cases sy <;> rfl
      | S754_nan => rfl
      | S754_finite sy my ey =>
          cases sx <;> cases sy
          · change
              some (match CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.compare ey ex with
                | .Eq =>
                    CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posCompare
                      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Eq my mx
                | c => c) =
                some (CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp
                  (match CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.compare ex ey with
                  | .Eq =>
                      CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posCompare
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.Eq mx my
                  | c => c))
            rw [raw_zcompare_swap ex ey]
            cases h : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.compare ex ey with
            | Eq => exact congrArg some (raw_poscompare_swap mx my)
            | Lt => rfl
            | Gt => rfl
          · rfl
          · rfl
          · change
              some (match CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.compare ey ex with
                | .Eq => CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp
                    (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posCompare
                      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Eq my mx)
                | .Lt => Gt
                | .Gt => Lt) =
                some (CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp
                  (match CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.compare ex ey with
                  | .Eq => CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp
                      (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posCompare
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.Eq mx my)
                  | .Lt => Gt
                  | .Gt => Lt))
            rw [raw_zcompare_swap ex ey]
            cases h : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.compare ex ey with
            | Eq =>
                rw [raw_poscompare_swap mx my]
                cases hpos :
                    CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posCompare
                      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Eq mx my <;>
                  rfl
            | Lt => rfl
            | Gt => rfl

private theorem raw_bcompare_swap
    {prec emax : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z}
    (x y : CompCert4Lean.Flocq.IEEE754.Binary.binary_float prec emax) :
    CompCert4Lean.Flocq.IEEE754.Binary.Bcompare y x =
      match CompCert4Lean.Flocq.IEEE754.Binary.Bcompare x y with
      | some c => some (CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp c)
      | none => none := by
  unfold CompCert4Lean.Flocq.IEEE754.Binary.Bcompare
  exact raw_sfcompare_swap
    (CompCert4Lean.Flocq.IEEE754.BinarySingleNaN.B2SF
      (CompCert4Lean.Flocq.IEEE754.Binary.B2BSN x))
    (CompCert4Lean.Flocq.IEEE754.BinarySingleNaN.B2SF
      (CompCert4Lean.Flocq.IEEE754.Binary.B2BSN y))

theorem cmp_swap : Float.cmp_swapStatement := by
  intro c x y
  unfold Float.cmp Float.compare
  have hraw := raw_bcompare_swap (x := decode64 x) (y := decode64 y)
  rw [hraw]
  cases h : CompCert4Lean.Flocq.IEEE754.Binary.Bcompare (decode64 x) (decode64 y) with
  | none => exact cmp_of_comparison_swap c none
  | some v => cases v <;> exact cmp_of_comparison_swap c (some _)

end Float

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

namespace Float

theorem cmp_ne_eq : Float.cmp_ne_eqStatement := by
  intro f1 f2
  unfold Float.cmp
  exact cmp_of_comparison_ne_eq (Float.compare f1 f2)

end Float

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib
open Lean Elab Tactic Meta

namespace Float

private def floatPrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem floatValReprOfNat (bits n : Nat) :
    (CompCert4Lean.Lib.Integers.WordCore.repr bits
      (ZArith.BinInt.Z.of_nat n)).val = n % (2 ^ bits) := by
  run_tac
    let lctx ← getLCtx
    let bitsF := (lctx.findFromUserName? `bits).get!
    let nF := (lctx.findFromUserName? `n).get!
    let bitsE := mkFVar bitsF.fvarId
    let nE := mkFVar nF.fvarId
    let z := mkApp
      (mkConst ``CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat)
      nE
    let e1 := mkApp2
      (mkConst (floatPrivateName
        "CompCert4Lean.Lib.Integers.WordCore.val_repr_residue")) bitsE z
    let e2 := mkApp2
      (mkConst (floatPrivateName
        "CompCert4Lean.Lib.Integers.WordCore.residue_zOfNat")) bitsE nE
    let t1 ← inferType e1
    let t2 ← inferType e2
    let (α, lhs, mid) := match_expr t1 with
      | _root_.Eq α lhs mid => (α, lhs, mid)
      | _ => panic! "unexpected first equality"
    let (_, _, rhs) := match_expr t2 with
      | _root_.Eq _ middle rhs => (α, middle, rhs)
      | _ => panic! "unexpected second equality"
    let eqtrans := mkConst ``Eq.trans [.succ .zero]
    let e := mkAppN eqtrans #[α, lhs, mid, rhs, e1, e2]
    closeMainGoal Name.anonymous e

theorem of_to_bits : Float.of_to_bitsStatement := by
  intro f
  apply congrArg (fun b : BitVec 64 => (⟨b⟩ : float))
  rw [← BitVec.ofFin_toFin f.bits]
  congr 1
  apply Fin.ext
  change (Integers.Int64.ofFin f.bits.toFin).val = f.bits.toNat
  unfold Integers.Int64.ofFin
  change (CompCert4Lean.Lib.Integers.WordCore.repr 64
    (ZArith.BinInt.Z.of_nat f.bits.toFin.val)).val = f.bits.toNat
  rw [floatValReprOfNat]
  exact Nat.mod_eq_of_lt f.bits.isLt

end Float

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

namespace Float

theorem ZofB_range_widen : Float.ZofB_range_widenStatement := by
  intro f n min1 max1 min2 max2 h hmin hmax
  unfold CompCert4Lean.Lib.IEEE754_extra.ZofB_range at h ⊢
  cases hz : CompCert4Lean.Lib.IEEE754_extra.ZofB (decode64 f) with
  | none => simp [hz] at h
  | some z =>
    simp [hz] at h ⊢
    rcases h with ⟨⟨hmin1, hmax1⟩, rfl⟩
    have hmin1' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le min1 z := by
      have hs : CompCert4Lean.Flocq.Core.Zaux.Zle_bool_prop min1 z true := by
        simpa [hmin1] using (CompCert4Lean.Flocq.Core.Zaux.Zle_bool_spec min1 z)
      cases hs with
      | Zle_bool_true_ hle => exact hle
    have hmax1' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le z max1 := by
      have hs : CompCert4Lean.Flocq.Core.Zaux.Zle_bool_prop z max1 true := by
        simpa [hmax1] using (CompCert4Lean.Flocq.Core.Zaux.Zle_bool_spec z max1)
      cases hs with
      | Zle_bool_true_ hle => exact hle
    have hmin2' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le min2 z :=
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le_trans min2 min1 z hmin hmin1'
    have hmax2' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le z max2 :=
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le_trans z max1 max2 hmax1' hmax
    have hbmin : CompCert4Lean.Lib.IEEE754_extra.Zle_bool min2 z = true :=
      CompCert4Lean.Flocq.Core.Zaux.Zle_bool_true min2 z hmin2'
    have hbmax : CompCert4Lean.Lib.IEEE754_extra.Zle_bool z max2 = true :=
      CompCert4Lean.Flocq.Core.Zaux.Zle_bool_true z max2 hmax2'
    exact ⟨⟨hbmin, hbmax⟩, rfl⟩

end Float

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

namespace Float

theorem to_intu_to_long : Float.to_intu_to_longStatement := by
  intro f n h
  unfold to_intu at h
  unfold to_long
  cases hz : CompCert4Lean.Lib.IEEE754_extra.ZofB_range (decode64 f) z0 Integers.Int.max_unsigned with
  | none => simp [hz] at h
  | some z =>
    simp [hz] at h
    subst n
    have hbound :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le z0 z ∧
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
            z Integers.Int.max_unsigned := by
      unfold CompCert4Lean.Lib.IEEE754_extra.ZofB_range at hz
      cases hzb : CompCert4Lean.Lib.IEEE754_extra.ZofB (decode64 f) with
      | none => simp [hzb] at hz
      | some z' =>
        simp [hzb] at hz
        rcases hz with ⟨⟨hminb, hmaxb⟩, rfl⟩
        constructor
        · have hs : CompCert4Lean.Flocq.Core.Zaux.Zle_bool_prop z0 z' true := by
            simpa [hminb] using
              (CompCert4Lean.Flocq.Core.Zaux.Zle_bool_spec z0 z')
          cases hs with
          | Zle_bool_true_ hle => exact hle
        · have hs : CompCert4Lean.Flocq.Core.Zaux.Zle_bool_prop z' Integers.Int.max_unsigned true := by
            simpa [hmaxb] using
              (CompCert4Lean.Flocq.Core.Zaux.Zle_bool_spec z' Integers.Int.max_unsigned)
          cases hs with
          | Zle_bool_true_ hle => exact hle
    have hmin :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
          Integers.Int64.min_signed z0 := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Integers.Int64.min_signed ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z0
      decide
    have hmax :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
          Integers.Int.max_unsigned Integers.Int64.max_signed := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Integers.Int.max_unsigned ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Integers.Int64.max_signed
      decide
    have hdst := ZofB_range_widen f z z0 Integers.Int.max_unsigned
      Integers.Int64.min_signed Integers.Int64.max_signed hz hmin hmax
    rw [hdst]
    have hu : Integers.Int.unsigned (Integers.Int.repr z) = z :=
      CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api z hbound
    rw [hu]
    rfl

end Float

end CompCert4Lean.Lib.Floats
namespace CompCert4Lean.Lib.Floats
namespace Float

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open Lean Elab Tactic Meta

private def ofLongPrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem ofLongValReprOfNat (bits n : Nat) :
    (CompCert4Lean.Lib.Integers.WordCore.repr bits
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)).val = n % (2 ^ bits) := by
  run_tac
    let lctx ← getLCtx
    let bitsF := (lctx.findFromUserName? `bits).get!
    let nF := (lctx.findFromUserName? `n).get!
    let bitsE := mkFVar bitsF.fvarId
    let nE := mkFVar nF.fvarId
    let z := mkApp
      (mkConst ``CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat)
      nE
    let e1 := mkApp2
      (mkConst (ofLongPrivateName
        "CompCert4Lean.Lib.Integers.WordCore.val_repr_residue")) bitsE z
    let e2 := mkApp2
      (mkConst (ofLongPrivateName
        "CompCert4Lean.Lib.Integers.WordCore.residue_zOfNat")) bitsE nE
    let t1 ← inferType e1
    let t2 ← inferType e2
    let (α, lhs, mid) := match_expr t1 with
      | _root_.Eq α lhs mid => (α, lhs, mid)
      | _ => panic! "unexpected first equality"
    let (_, _, rhs) := match_expr t2 with
      | _root_.Eq _ middle rhs => (α, middle, rhs)
      | _ => panic! "unexpected second equality"
    let eqtrans := mkConst ``Eq.trans [.succ .zero]
    let e := mkAppN eqtrans #[α, lhs, mid, rhs, e1, e2]
    closeMainGoal Name.anonymous e

theorem of_intu_of_long
    [certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate z53 z1024] :
    Float.of_intu_of_longStatement := by
  intro n
  unfold of_intu of_long
  congr 1

  have hn_nonneg :
      0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n.intval := by
    have h := n.intrange.1
    change (-1 : Int) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n.intval at h
    omega
  have hn_unsigned :
      Integers.Int.unsigned n =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n.val := by
    have h := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Z2Nat.id
      n.intval (by
        change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n.intval
        exact hn_nonneg)
    symm
    simpa [Integers.Int.unsigned, Integers.WordCore.unsigned,
      Integers.WordCore.Word.val] using h
  rw [hn_unsigned]
  have hnval_lt : n.val < 2 ^ 32 := by
    have h := n.intrange.2
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n.intval <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 2)
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 32)) at h
    have hpow :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 2)
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 32)) =
          (2 ^ 32 : Int) := by decide
    rw [hpow] at h
    have hval :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n.intval =
          Int.ofNat n.val := by
      rw [show n.intval =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n.val by
          symm
          simpa [Integers.WordCore.Word.val] using
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Z2Nat.id n.intval
              (by
                change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n.intval
                exact hn_nonneg))]
      simpa only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    rw [hval] at h
    exact Int.ofNat_lt.mp h
  have hval_repr :
      (Integers.Int64.repr
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n.val)).val = n.val := by
    change (CompCert4Lean.Lib.Integers.WordCore.repr 64
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n.val)).val = n.val
    rw [ofLongValReprOfNat]
    exact Nat.mod_eq_of_lt (by
      have hp : 2 ^ 32 ≤ 2 ^ 64 := Nat.pow_le_pow_right Nat.zero_lt_two (by decide)
      exact Nat.lt_of_lt_of_le hnval_lt hp)
  have hrepr_unsigned :
      Integers.WordCore.unsigned
          (Integers.Int64.repr
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n.val)) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n.val := by
    have hx_nonneg :
        0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Integers.Int64.repr
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n.val)).intval := by
      have h := (Integers.Int64.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n.val)).intrange.1
      change (-1 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Integers.Int64.repr
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n.val)).intval at h
      omega
    have h := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Z2Nat.id
      (Integers.Int64.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n.val)).intval
      (by
        change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Integers.Int64.repr
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n.val)).intval
        exact hx_nonneg)
    have h' :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
            (Integers.Int64.repr
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n.val)).val =
          (Integers.Int64.repr
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n.val)).intval := by
      simpa only [Integers.WordCore.Word.val] using h
    rw [hval_repr] at h'
    change (Integers.Int64.repr
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n.val)).intval =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n.val
    exact h'.symm
  rw [show Integers.Int64.signed
      (Integers.Int64.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n.val)) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n.val by
    unfold Integers.Int64.signed Integers.WordCore.signed
    dsimp only
    rw [hrepr_unsigned]
    cases hdec : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.ZArith_dec.Z_lt_dec
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n.val)
      Integers.Int64.half_modulus with
    | left h =>
        run_tac
          let g ← getMainGoal
          let zltName := ofLongPrivateName "CompCert4Lean.Lib.Integers.zltSelect"
          let sbName := ofLongPrivateName "CompCert4Lean.Lib.Integers.sumboolSelect"
          let t ← g.getType
          let t' ← withTransparency .all <|
            transform t
              (pre := fun e => do
                match e with
                | .const n lvls =>
                    if n == zltName || n == sbName then
                      let ci ← Lean.getConstInfo n
                      match ci.value? true with
                      | some v => pure (.visit (v.instantiateLevelParams ci.levelParams lvls))
                      | none => pure (.continue)
                    else
                      pure (.continue)
                | _ => pure (.continue))

          let g' ← g.change t' false
          replaceMainGoal [g']
        have hdec' := hdec
        simp only [Integers.Int64.half_modulus] at hdec'
        simp [hdec', CompCert4Lean.Lib.Coqlib.zlt]
    | right h =>
        exfalso
        apply h
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n.val) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Integers.Int64.half_modulus
        have hhalf :
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Integers.Int64.half_modulus =
              (2 ^ 63 : Int) := by decide
        have hz :
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n.val) =
              Int.ofNat n.val := by
          simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        rw [hz, hhalf]
        have hnval_lt' : Int.ofNat n.val < (2 ^ 32 : Int) := Int.ofNat_lt.mpr hnval_lt
        omega]

end Float
end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

namespace Float32

private theorem unpacked_mul_comm_worker32 (a b : _root_.Float.Model.UnpackedFloat) :
    _root_.Float.Model.UnpackedFloat.mul _root_.Float.Model.Format.binary32 a b =
      _root_.Float.Model.UnpackedFloat.mul _root_.Float.Model.Format.binary32 b a := by
  cases a with
  | notANumber => cases b <;> rfl
  | infinity sa =>
      cases b with
      | notANumber => rfl
      | infinity sb => cases sa <;> cases sb <;> rfl
      | zero sb => cases sa <;> cases sb <;> rfl
      | finite sb mb eb hb => cases sa <;> cases sb <;> rfl
  | zero sa =>
      cases b with
      | notANumber => rfl
      | infinity sb => cases sa <;> cases sb <;> rfl
      | zero sb => cases sa <;> cases sb <;> rfl
      | finite sb mb eb hb => cases sa <;> cases sb <;> rfl
  | finite sa ma ea ha =>
      cases b with
      | notANumber => rfl
      | infinity sb => cases sa <;> cases sb <;> rfl
      | zero sb => cases sa <;> cases sb <;> rfl
      | finite sb mb eb hb =>
          cases sa <;> cases sb <;>
            simp [_root_.Float.Model.UnpackedFloat.mul, Nat.mul_comm, Int.add_comm]
          all_goals rfl

private theorem model_mul_comm_worker32 (x y : float32) :
    modelBinary32
      (_root_.Float.Model.UnpackedFloat.mul _root_.Float.Model.Format.binary32) x y =
      modelBinary32
      (_root_.Float.Model.UnpackedFloat.mul _root_.Float.Model.Format.binary32) y x := by
  unfold modelBinary32
  rw [unpacked_mul_comm_worker32]

theorem mul_commut : Float32.mul_commutStatement := by
  intro x y h
  unfold Float32.mul
  rw [model_mul_comm_worker32]
  by_cases hx : isNaN32 x = true
  · by_cases hy : isNaN32 y = true
    · exfalso
      rcases h with h | h <;> simp_all
    · simp [finishBinary, binop_nan, cons_pl, hx, hy]
  · by_cases hy : isNaN32 y = true
    · simp [finishBinary, binop_nan, cons_pl, hx, hy]
    · simp [finishBinary, hx, hy]

end Float32

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

namespace Float32

theorem cmp_swap : Float32.cmp_swapStatement := by
  intro c x y
  unfold Float32.cmp Float32.compare
  have hraw := Float.raw_bcompare_swap (x := decode32 x) (y := decode32 y)
  rw [hraw]
  cases h : CompCert4Lean.Flocq.IEEE754.Binary.Bcompare (decode32 x) (decode32 y) with
  | none => exact cmp_of_comparison_swap c none
  | some v => cases v <;> exact cmp_of_comparison_swap c (some _)

theorem cmp_ne_eq : Float32.cmp_ne_eqStatement := by
  intro f1 f2
  unfold Float32.cmp
  exact cmp_of_comparison_ne_eq (Float32.compare f1 f2)

end Float32

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem float32_of_int_two_bits
    [certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate z24 z128] :
    Float32.of_int (Integers.Int.repr (ZArith.BinInt.Z.of_nat 2)) =
      ⟨BitVec.ofNat 32 1073741824⟩ := by
  rfl

private theorem float32_unpack_two_bits :
    _root_.Float.Model.UnpackedFloat.unpack _root_.Float.Model.Format.binary32
        (BitVec.ofNat 32 1073741824) =
      .finite .positive 8388608 (-22) (by decide) := by
  rfl

private theorem extendedMantissa_shift_pow (m k : Nat) :
    (_root_.Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
        (m * 2 ^ k) _root_.Float.Model.UnpackedFloat.Accuracy.exact >>> k) =
      _root_.Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
        m _root_.Float.Model.UnpackedFloat.Accuracy.exact := by
  change Nat.repeat
      _root_.Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne k
        (_root_.Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
          (m * 2 ^ k) _root_.Float.Model.UnpackedFloat.Accuracy.exact) = _
  induction k generalizing m with
  | zero => simp [Nat.repeat]
  | succ k ih =>
      rw [show m * 2 ^ (k + 1) = (m * 2) * 2 ^ k by
        simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]]
      simp only [Nat.repeat]
      rw [ih]
      simp [_root_.Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne,
        _root_.Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy]

private theorem extendedMantissa_shift_zero
    (x : _root_.Float.Model.UnpackedFloat.ExtendedMantissa) : x >>> 0 = x := by
  change Nat.repeat
    _root_.Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne 0 x = x
  unfold Nat.repeat
  rfl

private theorem extendedMantissa_shift_pow_add (m k q : Nat) :
    (_root_.Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
        (m * 2 ^ k) _root_.Float.Model.UnpackedFloat.Accuracy.exact >>> (k + q)) =
      (_root_.Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
        m _root_.Float.Model.UnpackedFloat.Accuracy.exact >>> q) := by
  induction q with
  | zero =>
      rw [extendedMantissa_shift_zero]
      exact extendedMantissa_shift_pow m k
  | succ q ih =>
      change
        _root_.Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne
            ((_root_.Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
              (m * 2 ^ k) _root_.Float.Model.UnpackedFloat.Accuracy.exact) >>> (k + q)) =
          _root_.Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne
            ((_root_.Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
              m _root_.Float.Model.UnpackedFloat.Accuracy.exact) >>> q)
      exact congrArg _ ih

private theorem log2_mul_pow (m k : Nat) (hm : m ≠ 0) :
    (m * 2 ^ k).log2 = m.log2 + k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.pow_succ]
      rw [show m * (2 ^ k * 2) = 2 * (m * 2 ^ k) by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]]
      rw [Nat.log2_two_mul
        (Nat.mul_ne_zero hm (Nat.ne_of_gt (Nat.two_pow_pos k))), ih]
      omega

private theorem shiftToTargetExponent_scale32
    (m k : Nat) (e : Int) (hm : m ≠ 0)
    (hle : e ≤ _root_.Float.Model.Format.binary32.targetExponent
      (_root_.Float.Model.totalExponent m e)) :
    _root_.Float.Model.UnpackedFloat.shiftToTargetExponent
        _root_.Float.Model.Format.binary32 (m * 2 ^ k) (e - (k : Int))
        _root_.Float.Model.UnpackedFloat.Accuracy.exact =
      _root_.Float.Model.UnpackedFloat.shiftToTargetExponent
        _root_.Float.Model.Format.binary32 m e
        _root_.Float.Model.UnpackedFloat.Accuracy.exact := by
  have htotal :
      _root_.Float.Model.totalExponent (m * 2 ^ k) (e - (k : Int)) =
        _root_.Float.Model.totalExponent m e := by
    unfold _root_.Float.Model.totalExponent
    rw [log2_mul_pow m k hm]
    omega
  unfold _root_.Float.Model.UnpackedFloat.shiftToTargetExponent
  rw [htotal]
  unfold _root_.Float.Model.UnpackedFloat.shiftToExponent
  let t := _root_.Float.Model.Format.binary32.targetExponent
    (_root_.Float.Model.totalExponent m e)
  have hnonneg : 0 ≤ t - e := by omega
  have hdiff : t - (e - (k : Int)) = (k : Int) + (t - e) := by omega
  change
    ((_root_.Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
        (m * 2 ^ k) _root_.Float.Model.UnpackedFloat.Accuracy.exact >>>
          (t - (e - (k : Int))).toNat),
        e - (k : Int) + (t - (e - (k : Int))).toNat) =
      ((_root_.Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
        m _root_.Float.Model.UnpackedFloat.Accuracy.exact >>> (t - e).toNat),
        e + (t - e).toNat)
  rw [hdiff, Int.toNat_add (Int.ofNat_nonneg k) hnonneg]
  apply Prod.ext
  · exact extendedMantissa_shift_pow_add m k (t - e).toNat
  · simp only [Int.toNat_natCast]
    have hcast : ((t - e).toNat : Int) = t - e := Int.toNat_of_nonneg hnonneg
    omega

private theorem round_double_worker32
    (s : _root_.Float.Model.UnpackedFloat.Sign) (m : Nat) (e : Int)
    (hm : 0 < m) :
    _root_.Float.Model.UnpackedFloat.round _root_.Float.Model.Format.binary32
        s (m + m) e =
      _root_.Float.Model.UnpackedFloat.roundWithAccuracy
        _root_.Float.Model.Format.binary32 s (m * 8388608) (e - 22)
        _root_.Float.Model.UnpackedFloat.Accuracy.exact := by
  let a := m + m
  let t := _root_.Float.Model.Format.binary32.targetExponent
    (_root_.Float.Model.totalExponent a e)
  let d := (e - t).toNat
  have ha : a ≠ 0 := by simp [a, Nat.ne_of_gt hm]
  have hloga : a.log2 = m.log2 + 1 := by
    rw [show a = 2 * m by omega, Nat.log2_two_mul (Nat.ne_of_gt hm)]
  have ht_lower : e - 22 ≤ t := by
    dsimp [t]
    change e - 22 ≤ max ((a.log2 : Int) + 1 + e - 24) (-149)
    rw [hloga]
    omega
  have hdle : d ≤ 22 := by
    dsimp [d]
    omega
  let c := a * 2 ^ d
  let ec := e - (d : Int)
  have hc : c ≠ 0 :=
    Nat.mul_ne_zero ha (Nat.ne_of_gt (Nat.two_pow_pos d))
  have htotalc :
      _root_.Float.Model.totalExponent c ec =
        _root_.Float.Model.totalExponent a e := by
    dsimp [c, ec]
    unfold _root_.Float.Model.totalExponent
    rw [log2_mul_pow a d ha]
    omega
  have hlec : ec ≤ _root_.Float.Model.Format.binary32.targetExponent
      (_root_.Float.Model.totalExponent c ec) := by
    rw [htotalc]
    change e - (d : Int) ≤ t
    dsimp [d]
    omega
  have hscale := shiftToTargetExponent_scale32 c (22 - d) ec hc hlec
  have hmant : c * 2 ^ (22 - d) = m * 8388608 := by
    dsimp [c, a]
    rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le hdle]
    change (m + m) * 4194304 = m * 8388608
    omega
  have hexp : ec - ((22 - d : Nat) : Int) = e - 22 := by
    dsimp [ec]
    omega
  rw [hmant, hexp] at hscale
  unfold _root_.Float.Model.UnpackedFloat.round
    _root_.Float.Model.UnpackedFloat.decreaseExponent
  dsimp only
  change
    _root_.Float.Model.UnpackedFloat.roundWithAccuracy
        _root_.Float.Model.Format.binary32 s (a <<< d) ec
        _root_.Float.Model.UnpackedFloat.Accuracy.exact = _
  rw [Nat.shiftLeft_eq]
  change
    _root_.Float.Model.UnpackedFloat.roundWithAccuracy
        _root_.Float.Model.Format.binary32 s c ec
        _root_.Float.Model.UnpackedFloat.Accuracy.exact = _
  unfold _root_.Float.Model.UnpackedFloat.roundWithAccuracy
  rw [← hscale]

private theorem unpacked_add_self_mul_two_worker32
    (a : _root_.Float.Model.UnpackedFloat) :
    _root_.Float.Model.UnpackedFloat.add _root_.Float.Model.Format.binary32 a a =
      _root_.Float.Model.UnpackedFloat.mul _root_.Float.Model.Format.binary32 a
        (.finite .positive 8388608 (-22) (by decide)) := by
  cases a with
  | notANumber => rfl
  | infinity s => cases s <;> rfl
  | zero s => cases s <;> rfl
  | finite s m e hm =>
      have hmI : (0 : Int) < (m : Int) := by omega
      cases s with
      | negative =>
        simp only [_root_.Float.Model.UnpackedFloat.add,
          _root_.Float.Model.UnpackedFloat.mul,
          _root_.Float.Model.UnpackedFloat.decreaseExponent,
          _root_.Float.Model.UnpackedFloat.Sign.apply,
          _root_.Float.Model.UnpackedFloat.normalize, Int.min_self, Int.sub_self,
          Int.toNat_zero, Nat.shiftLeft_zero]
        have hc : compare (-(m : Int) + -(m : Int)) 0 = .lt :=
          Int.compare_eq_lt.mpr (by omega)
        rw [hc]
        have hnat : (-(-(m : Int) + -(m : Int))).toNat = m + m := by omega
        rw [hnat]
        change
          _root_.Float.Model.UnpackedFloat.round _root_.Float.Model.Format.binary32
              .negative (m + m) e =
            _root_.Float.Model.UnpackedFloat.roundWithAccuracy
              _root_.Float.Model.Format.binary32 .negative (m * 8388608) (e - 22)
              _root_.Float.Model.UnpackedFloat.Accuracy.exact
        exact round_double_worker32 .negative m e hm
      | positive =>
        simp only [_root_.Float.Model.UnpackedFloat.add,
          _root_.Float.Model.UnpackedFloat.mul,
          _root_.Float.Model.UnpackedFloat.decreaseExponent,
          _root_.Float.Model.UnpackedFloat.Sign.apply,
          _root_.Float.Model.UnpackedFloat.normalize, Int.min_self, Int.sub_self,
          Int.toNat_zero, Nat.shiftLeft_zero]
        have hc : compare ((m : Int) + (m : Int)) 0 = .gt :=
          Int.compare_eq_gt.mpr (by omega)
        rw [hc]
        have hnat : ((m : Int) + (m : Int)).toNat = m + m := by omega
        rw [hnat]
        change
          _root_.Float.Model.UnpackedFloat.round _root_.Float.Model.Format.binary32
              .positive (m + m) e =
            _root_.Float.Model.UnpackedFloat.roundWithAccuracy
              _root_.Float.Model.Format.binary32 .positive (m * 8388608) (e - 22)
              _root_.Float.Model.UnpackedFloat.Accuracy.exact
        exact round_double_worker32 .positive m e hm

private theorem model_add_self_mul_two_worker32
    [certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate z24 z128]
    (f : float32) :
    modelBinary32
        (_root_.Float.Model.UnpackedFloat.add _root_.Float.Model.Format.binary32) f f =
      modelBinary32
        (_root_.Float.Model.UnpackedFloat.mul _root_.Float.Model.Format.binary32) f
          (Float32.of_int (Integers.Int.repr (ZArith.BinInt.Z.of_nat 2))) := by
  rw [float32_of_int_two_bits]
  unfold modelBinary32
  rw [float32_unpack_two_bits, unpacked_add_self_mul_two_worker32]

private theorem isNaN_of_int_two_worker32
    [certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate z24 z128] :
    isNaN32 (Float32.of_int (Integers.Int.repr (ZArith.BinInt.Z.of_nat 2))) = false := by
  rw [float32_of_int_two_bits]
  rfl

namespace Float32

theorem mul2_add
    [certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate z24 z128] :
    Float32.mul2_addStatement := by
  intro f
  unfold Float32.add Float32.mul
  rw [model_add_self_mul_two_worker32]
  have htwo := isNaN_of_int_two_worker32
  by_cases hf : isNaN32 f = true
  · simp only [finishBinary, binop_nan, cons_pl, hf, htwo, Bool.true_or,
      Bool.false_eq_true, ↓reduceIte]
    rw [CompCert4Lean.X86_64.Archi.choose_nan_32_idem]
  · simp [finishBinary, hf, htwo]

end Float32

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib
open Lean Elab Tactic Meta

namespace Float32

private def float32PrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem float32ValReprOfNat (bits n : Nat) :
    (CompCert4Lean.Lib.Integers.WordCore.repr bits
      (ZArith.BinInt.Z.of_nat n)).val = n % (2 ^ bits) := by
  run_tac
    let lctx ← getLCtx
    let bitsF := (lctx.findFromUserName? `bits).get!
    let nF := (lctx.findFromUserName? `n).get!
    let bitsE := mkFVar bitsF.fvarId
    let nE := mkFVar nF.fvarId
    let z := mkApp
      (mkConst ``CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat)
      nE
    let e1 := mkApp2
      (mkConst (float32PrivateName
        "CompCert4Lean.Lib.Integers.WordCore.val_repr_residue")) bitsE z
    let e2 := mkApp2
      (mkConst (float32PrivateName
        "CompCert4Lean.Lib.Integers.WordCore.residue_zOfNat")) bitsE nE
    let t1 ← inferType e1
    let t2 ← inferType e2
    let (α, lhs, mid) := match_expr t1 with
      | _root_.Eq α lhs mid => (α, lhs, mid)
      | _ => panic! "unexpected first equality"
    let (_, _, rhs) := match_expr t2 with
      | _root_.Eq _ middle rhs => (α, middle, rhs)
      | _ => panic! "unexpected second equality"
    let eqtrans := mkConst ``Eq.trans [.succ .zero]
    let e := mkAppN eqtrans #[α, lhs, mid, rhs, e1, e2]
    closeMainGoal Name.anonymous e

theorem of_to_bits : Float32.of_to_bitsStatement := by
  intro f
  apply congrArg (fun b : BitVec 32 => (⟨b⟩ : float32))
  rw [← BitVec.ofFin_toFin f.bits]
  congr 1
  apply Fin.ext
  change (Integers.Int.ofFin f.bits.toFin).val = f.bits.toNat
  unfold Integers.Int.ofFin
  change (CompCert4Lean.Lib.Integers.WordCore.repr 32
    (ZArith.BinInt.Z.of_nat f.bits.toFin.val)).val = f.bits.toNat
  rw [float32ValReprOfNat]
  exact Nat.mod_eq_of_lt f.bits.isLt

end Float32

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats.Sqrt

open Lean Elab Tactic Meta

private def sqrtPrivateName (suffix : String) : Name :=
  let p := Name.str
    (Name.str
      (Name.str
        (Name.str
          (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Floats") "Sqrt"
  let p := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str p

private def sqrtUnfoldPrivate (suffixes : List String) : TacticM Unit := do
  for suffix in suffixes do
    let n := sqrtPrivateName suffix
    evalTactic (← `(tactic| unfold $(Lean.mkIdent n) at *))

private theorem quiet_nan64_bits_worker (y : BitVec 64)
    (he : y.toNat / 2 ^ 52 % 2 ^ 11 = 2047)
    (hm : y.toNat % 2 ^ 52 ≠ 0) :
    y ||| (1#64 <<< 51) =
      (quiet_nan_64 (sign64 (⟨y⟩ : float), payload64 (⟨y⟩ : float))).bits := by
  unfold quiet_nan_64 quiet_nan_64_payload mkNaN64 sign64 payload64 fraction64
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by decide : 2 ^ 51 < 2 ^ 64)]
  let k := y.toNat / 2 ^ 52
  let f := y.toNat % 2 ^ 52
  have hf : f < 2 ^ 52 := Nat.mod_lt _ (by omega)
  have hfpos : 0 < f := Nat.pos_of_ne_zero hm
  have hy : 2 ^ 52 * k + f = y.toNat := by
    dsimp [k, f]
    rw [Nat.div_add_mod]
  have hk : k < 2 ^ 12 := by
    dsimp [k]
    apply Nat.div_lt_of_lt_mul
    simpa [Nat.pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using y.isLt
  have hkmod : k % 2 ^ 11 = 2047 := by
    dsimp [k]
    exact he
  have hk_cases : k = 2047 ∨ k = 4095 := by omega
  have horlt : Nat.lor f (2 ^ 51) < 2 ^ 52 := Nat.or_lt_two_pow hf (by omega)
  have hqeq : Nat.lor f (2 ^ 51) % 2 ^ 52 = Nat.lor f (2 ^ 51) :=
    Nat.mod_eq_of_lt horlt
  have hqpos : 0 < Nat.lor f (2 ^ 51) % 2 ^ 52 := by
    rw [hqeq]
    have hb : 2 ^ 51 ≤ Nat.lor f (2 ^ 51) := Nat.right_le_or
    omega
  have hpayload :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat f) = f := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat f) = _
    exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat hfpos
  have hpayloadQuiet :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat
            (Nat.lor f (2 ^ 51) % 2 ^ 52)) = Nat.lor f (2 ^ 51) % 2 ^ 52 := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat
          (Nat.lor f (2 ^ 51) % 2 ^ 52)) = _
    exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat hqpos
  rw [show y.toNat % 2 ^ 52 = f by rfl, hpayload,
    hpayloadQuiet, hqeq]
  have hmask : (1 % 2 ^ 64) <<< 51 % 2 ^ 64 = 2 ^ 51 := by decide
  rw [hmask]
  have horassoc (a b c : Nat) :
      Nat.lor (Nat.lor a b) c = Nat.lor a (Nat.lor b c) := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp [Nat.testBit_or, Bool.or_assoc]
  have hpow (a b : Nat) (hb : b < 2 ^ 52) :
      Nat.lor (2 ^ 52 * a) b = 2 ^ 52 * a + b := by
    have hh := Nat.two_pow_add_eq_or_of_lt hb a
    simpa using hh.symm
  have hor_split (a b : Nat) (hb : b < 2 ^ 52) :
      Nat.lor (2 ^ 52 * a + b) (2 ^ 51) = 2 ^ 52 * a + Nat.lor b (2 ^ 51) := by
    rw [← hpow a b hb, horassoc]
    have hbq : Nat.lor b (2 ^ 51) < 2 ^ 52 := Nat.or_lt_two_pow hb (by decide)
    rw [hpow a _ hbq]
  have hor_def : (2 ^ 52 * k + f) ||| (2 ^ 51) =
      Nat.lor (2 ^ 52 * k + f) (2 ^ 51) := by rfl
  rw [← hy, hor_def, hor_split k f hf]
  rcases hk_cases with hkval | hkval
  · have hs : (2 ^ 52 * 2047 + f) / 2 ^ 63 % 2 = 0 := by omega
    simp [hkval, hs, hqeq]
    rw [show (f ||| 2251799813685248) = Nat.lor f 2251799813685248 by rfl]
    have hqeqNum : Nat.lor f 2251799813685248 % 4503599627370496 =
        Nat.lor f 2251799813685248 := by simpa using hqeq
    rw [hqeqNum]
    have hqbound : Nat.lor f 2251799813685248 < 2 ^ 52 := by simpa using horlt
    have hsum : 9218868437227405312 + Nat.lor f 2251799813685248 <
        18446744073709551616 := by omega
    rw [Nat.mod_eq_of_lt hsum]
  · have hs : (2 ^ 52 * 4095 + f) / 2 ^ 63 % 2 = 1 := by omega
    simp [hkval, hs, hqeq]
    rw [show (f ||| 2251799813685248) = Nat.lor f 2251799813685248 by rfl]
    have hqeqNum : Nat.lor f 2251799813685248 % 4503599627370496 =
        Nat.lor f 2251799813685248 := by simpa using hqeq
    rw [hqeqNum]
    have hqbound : Nat.lor f 2251799813685248 < 2 ^ 52 := by simpa using horlt
    have hsum : 18442240474082181120 + Nat.lor f 2251799813685248 <
        18446744073709551616 := by omega
    rw [Nat.mod_eq_of_lt hsum]

theorem float64_sqrt_correct_proof : float64_sqrt_correctStatement := by
  intro x
  have rawNaN_iff (y : BitVec 64) :
      (BitVec.extractLsb 62 52 y = 2047#11 ∧
        ¬BitVec.extractLsb 51 0 y = 0#52) ↔
      isNaN64 (⟨y⟩ : float) = true := by
    have he_iff :
        BitVec.extractLsb 62 52 y = 2047#11 ↔
          y.toNat / 2 ^ 52 % 2 ^ 11 = 2047 := by
      constructor
      · intro he
        have ht := congrArg BitVec.toNat he
        simpa [BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow] using ht
      · intro he
        apply BitVec.eq_of_toNat_eq
        simpa [BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow] using he
    have hm_iff :
        BitVec.extractLsb 51 0 y = 0#52 ↔
          y.toNat % 2 ^ 52 = 0 := by
      constructor
      · intro hm
        have ht := congrArg BitVec.toNat hm
        simpa [BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow] using ht
      · intro hm
        apply BitVec.eq_of_toNat_eq
        simpa [BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow] using hm
    constructor
    · intro hparts
      have he := he_iff.1 hparts.1
      have hm : y.toNat % 2 ^ 52 ≠ 0 := fun hm => hparts.2 (hm_iff.2 hm)
      simp [isNaN64, exponent64, fraction64, he, hm]
    · intro hnan
      have hparts :
          y.toNat / 2 ^ 52 % 2 ^ 11 = 2047 ∧ y.toNat % 2 ^ 52 ≠ 0 := by
        simpa [isNaN64, exponent64, fraction64] using hnan
      exact ⟨he_iff.2 hparts.1, fun hm => hparts.2 (hm_iff.1 hm)⟩
  have raw_iff (y : BitVec 64) :
      (Float.Model.UnpackedFloat.unpackExponent
          (spec := Float.Model.Format.binary64) y == -1#11 &&
        Float.Model.UnpackedFloat.unpackMantissa
          (spec := Float.Model.Format.binary64) y != 0#52) = true ↔
      isNaN64 (⟨y⟩ : float) = true := by
    have hp := rawNaN_iff y
    simpa [Float.Model.UnpackedFloat.unpackExponent,
      Float.Model.UnpackedFloat.unpackMantissa,
      BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow] using hp
  have rawProp_iff (y : BitVec 64) :
      (Float.Model.UnpackedFloat.unpackExponent
          (spec := Float.Model.Format.binary64) y = -1#11 ∧
        Float.Model.UnpackedFloat.unpackMantissa
          (spec := Float.Model.Format.binary64) y ≠ 0#52) ↔
      isNaN64 (⟨y⟩ : float) = true := by
    simpa [Bool.and_eq_true] using (raw_iff y)
  have rawProp2047_iff (y : BitVec 64) :
      (Float.Model.UnpackedFloat.unpackExponent
          (spec := Float.Model.Format.binary64) y = 2047#11 ∧
        Float.Model.UnpackedFloat.unpackMantissa
          (spec := Float.Model.Format.binary64) y ≠ 0#52) ↔
      isNaN64 (⟨y⟩ : float) = true := by
    simpa using (rawProp_iff y)
  dsimp [float64_sqrt, Float.sqrt, Sqrt.rawSqrt]
  run_tac sqrtUnfoldPrivate ["CompCert4Lean.Lib.Floats.Sqrt.rawIsNaN",
    "CompCert4Lean.Lib.Floats.Sqrt.quietNaN",
    "CompCert4Lean.Lib.Floats.Sqrt.defaultNaN"]
  by_cases h : isNaN64 (⟨x.toBitVec⟩ : float) = true
  · have hparts : x.toNat / 2 ^ 52 % 2 ^ 11 = 2047 ∧
        x.toNat % 2 ^ 52 ≠ 0 := by
      simpa [isNaN64, exponent64, fraction64] using h
    simp only [h, ↓reduceIte]
    split
    · rename_i hraw
      apply UInt64.toBitVec_inj.mp
      change (x.toBitVec ||| (1#64 <<< 51)) = _
      simpa [h, hraw, Float.unop_nan, Float.cons_pl,
        CompCert4Lean.X86_64.Archi.choose_nan_64, quiet_nan_64,
        quiet_nan_64_payload, mkNaN64, sign64, payload64] using
        (quiet_nan64_bits_worker x.toBitVec hparts.1 hparts.2)
    · simp_all! [Float.unop_nan, Float.cons_pl, quiet_nan_64,
        quiet_nan_64_payload, mkNaN64, sign64, payload64,
        Float.Model.UnpackedFloat.unpackExponent,
        Float.Model.UnpackedFloat.unpackMantissa, rawNaN_iff]
  · split
    · rename_i hraw
      have hbad : isNaN64 (⟨x.toBitVec⟩ : float) = true :=
        (raw_iff x.toBitVec).1 hraw
      exact (h hbad).elim
    · rename_i hraw
      by_cases hr : isNaN64
          ({ bits :=
              Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
                (unpackedSqrt Float.Model.Format.binary64
                  (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 x.toBitVec)) } : float) = true
      · have hp :
            Float.Model.UnpackedFloat.unpackExponent
                  (Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
                    (unpackedSqrt Float.Model.Format.binary64
                      (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 x.toBitVec))) = 2047#11 ∧
              Float.Model.UnpackedFloat.unpackMantissa
                  (Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
                    (unpackedSqrt Float.Model.Format.binary64
                      (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 x.toBitVec))) ≠ 0#52 :=
          (rawProp2047_iff _).2 hr
        have hbeq : (2047#11 == -1#11) = true := by decide
        have hpe :
            Float.Model.UnpackedFloat.unpackExponent
                (Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
                  (unpackedSqrt Float.Model.Format.binary64
                    (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 x.toBitVec))) = -1#11 := by
          have heq : (2047#11 : BitVec 11) = -1#11 := by decide
          exact heq ▸ hp.1
        have hc :
            (Float.Model.UnpackedFloat.unpackExponent
                (Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
                  (unpackedSqrt Float.Model.Format.binary64
                    (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 x.toBitVec))) == -1#11 &&
              Float.Model.UnpackedFloat.unpackMantissa
                (Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
                  (unpackedSqrt Float.Model.Format.binary64
                    (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 x.toBitVec))) != 0#52) = true := by
          simp [hpe, hp]
        simp only [hc, hr, ↓reduceIte]
        have hd : isNaN64 default_nan_64 = true := by decide
        have hdraw : isNaN64
            ({ bits :=
                Float.Model.UnpackedFloat.packedNaN Float.Model.Format.binary64 |||
                  (1#Float.Model.Format.binary64.numBits <<<
                    (Float.Model.Format.binary64.numBits - 1)) } : float) = true := by decide
        have hdef : default_nan_64.bits =
            Float.Model.UnpackedFloat.packedNaN Float.Model.Format.binary64 |||
              (1#Float.Model.Format.binary64.numBits <<<
                (Float.Model.Format.binary64.numBits - 1)) := by
          unfold default_nan_64 quiet_nan_64 quiet_nan_64_payload
          unfold CompCert4Lean.X86_64.Archi.default_nan_64 mkNaN64
          decide
        simp only [hdraw, ↓reduceIte]
        apply UInt64.toBitVec_inj.mp
        simpa using hdef.symm
      · have hp : ¬(
            Float.Model.UnpackedFloat.unpackExponent
                  (Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
                    (unpackedSqrt Float.Model.Format.binary64
                      (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 x.toBitVec))) = 2047#11 ∧
              Float.Model.UnpackedFloat.unpackMantissa
                  (Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
                    (unpackedSqrt Float.Model.Format.binary64
                      (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 x.toBitVec))) ≠ 0#52) := by
          intro hp
          exact hr ((rawProp2047_iff _).1 hp)
        have hc :
            (Float.Model.UnpackedFloat.unpackExponent
                    (Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
                      (unpackedSqrt Float.Model.Format.binary64
                        (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 x.toBitVec))) == -1#11 &&
                Float.Model.UnpackedFloat.unpackMantissa
                    (Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
                      (unpackedSqrt Float.Model.Format.binary64
                        (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 x.toBitVec))) != 0#52) ≠ true := by
          intro hc
          exact hr ((raw_iff _).1 hc)
        simp only [hc, hr, Bool.false_eq_true, ↓reduceIte]

end CompCert4Lean.Lib.Floats.Sqrt

namespace CompCert4Lean.Lib.Floats

theorem Float32.unop_nan_result_obligation_proof : Float32.unop_nan_result_obligation := by
  intro x hx
  unfold Float32.unop_nan
  exact quiet_nan_32_result_obligation_proof_local
    (CompCert4Lean.X86_64.Archi.choose_nan_32 (Float32.cons_pl x []))

end CompCert4Lean.Lib.Floats
