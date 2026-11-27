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
    match decode32 f with
    | .B754_finite sign mantissa exponent =>
      encode64 (Binary.binary_normalize (prec := z53) (emax := z1024)
        (certificate := Binary.binary64_normalize_certificate_proof)
        BinarySingleNaN.mode_NE
        (CompCert4Lean.Flocq.Core.Zaux.cond_Zopp sign (.Zpos mantissa)) exponent sign)
    | _ =>
      ⟨_root_.Float.Model.UnpackedFloat.pack _root_.Float.Model.Format.binary64
        (_root_.Float.Model.UnpackedFloat.unpack _root_.Float.Model.Format.binary32 f.bits)⟩

def to_single (f : float) : float32 :=
  if isNaN64 f then to_single_nan f
  else
    match decode64 f with
    | .B754_finite sign mantissa exponent =>
      encode32 (Binary.binary_normalize (prec := z24) (emax := z128)
        (certificate := Binary.binary32_normalize_certificate_proof)
        BinarySingleNaN.mode_NE
        (CompCert4Lean.Flocq.Core.Zaux.cond_Zopp sign (.Zpos mantissa)) exponent sign)
    | _ =>
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
      (BitVec.extractLsb' 52 11 y = 2047#11 ∧
        ¬BitVec.extractLsb' 0 52 y = 0#52) ↔
      isNaN64 (⟨y⟩ : float) = true := by
    have he_iff :
        BitVec.extractLsb' 52 11 y = 2047#11 ↔
          y.toNat / 2 ^ 52 % 2 ^ 11 = 2047 := by
      constructor
      · intro he
        have ht := congrArg BitVec.toNat he
        simpa [BitVec.extractLsb_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] using ht
      · intro he
        apply BitVec.eq_of_toNat_eq
        simpa [BitVec.extractLsb_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] using he
    have hm_iff :
        BitVec.extractLsb' 0 52 y = 0#52 ↔
          y.toNat % 2 ^ 52 = 0 := by
      constructor
      · intro hm
        have ht := congrArg BitVec.toNat hm
        simpa [BitVec.extractLsb_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] using ht
      · intro hm
        apply BitVec.eq_of_toNat_eq
        simpa [BitVec.extractLsb_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] using hm
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
      BitVec.extractLsb_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] using hp
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

namespace CompCert4Lean.Lib.Floats

theorem quiet_nan_32_result_obligation_proof : quiet_nan_32_result_obligation :=
  quiet_nan_32_result_obligation_proof_local

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

theorem Float.binop_nan_result_obligation_proof : Float.binop_nan_result_obligation := by
  intro x y _hx _hy
  exact quiet_nan_64_result_obligation_proof_local
    (CompCert4Lean.X86_64.Archi.choose_nan_64
      (Float.cons_pl x (Float.cons_pl y [])))

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

theorem Float.abs_nan_result_obligation_proof : Float.abs_nan_result_obligation := by
  intro f hf
  unfold Float.abs_nan
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
    rw [decode64_mkNaN false (fraction64 f) hq hqlt]
    constructor
    · rfl
    · unfold CompCert4Lean.Flocq.IEEE754.Binary.BinaryFloatCertificate
      unfold CompCert4Lean.Flocq.IEEE754.Binary.B2FF
      unfold CompCert4Lean.Flocq.IEEE754.Binary.valid_binary
      change CompCert4Lean.Flocq.IEEE754.Binary.nan_pl (prec := z53)
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat
            (fraction64 f)) = true
      exact nan_pl_posOfNat_lt_52 (fraction64 f) hq hqlt
  · exact default_nan_64_result_obligation_proof

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

theorem quiet_nan_32_proof : quiet_nan_32_proofStatement := by
  intro p
  have hpayload :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat
            (quiet_nan_32_payload p)) =
        quiet_nan_32_payload p :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat_posToNat
      (quiet_nan_32_payload p)
  rw [← hpayload]
  exact nan_pl_posOfNat_lt_23
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat
      (quiet_nan_32_payload p))
    (quiet_nan_32_payload_bounds p).1
    (quiet_nan_32_payload_bounds p).2

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem float64_of_int_two_bits
    [certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate z53 z1024] :
    Float.of_int (Integers.Int.repr (ZArith.BinInt.Z.of_nat 2)) =
      ⟨BitVec.ofNat 64 4611686018427387904⟩ := by
  rfl

private theorem float64_unpack_two_bits :
    _root_.Float.Model.UnpackedFloat.unpack _root_.Float.Model.Format.binary64
        (BitVec.ofNat 64 4611686018427387904) =
      .finite .positive 4503599627370496 (-51) (by decide) := by
  rfl

private theorem shiftToTargetExponent_scale64
    (m k : Nat) (e : Int) (hm : m ≠ 0)
    (hle : e ≤ _root_.Float.Model.Format.binary64.targetExponent
      (_root_.Float.Model.totalExponent m e)) :
    _root_.Float.Model.UnpackedFloat.shiftToTargetExponent
        _root_.Float.Model.Format.binary64 (m * 2 ^ k) (e - (k : Int))
        _root_.Float.Model.UnpackedFloat.Accuracy.exact =
      _root_.Float.Model.UnpackedFloat.shiftToTargetExponent
        _root_.Float.Model.Format.binary64 m e
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
  let t := _root_.Float.Model.Format.binary64.targetExponent
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

private theorem round_double_worker64
    (s : _root_.Float.Model.UnpackedFloat.Sign) (m : Nat) (e : Int)
    (hm : 0 < m) :
    _root_.Float.Model.UnpackedFloat.round _root_.Float.Model.Format.binary64
        s (m + m) e =
      _root_.Float.Model.UnpackedFloat.roundWithAccuracy
        _root_.Float.Model.Format.binary64 s (m * 4503599627370496) (e - 51)
        _root_.Float.Model.UnpackedFloat.Accuracy.exact := by
  let a := m + m
  let t := _root_.Float.Model.Format.binary64.targetExponent
    (_root_.Float.Model.totalExponent a e)
  let d := (e - t).toNat
  have ha : a ≠ 0 := by simp [a, Nat.ne_of_gt hm]
  have hloga : a.log2 = m.log2 + 1 := by
    rw [show a = 2 * m by omega, Nat.log2_two_mul (Nat.ne_of_gt hm)]
  have ht_lower : e - 51 ≤ t := by
    dsimp [t]
    change e - 51 ≤ max ((a.log2 : Int) + 1 + e - 53) (-1074)
    rw [hloga]
    omega
  have hdle : d ≤ 51 := by
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
  have hlec : ec ≤ _root_.Float.Model.Format.binary64.targetExponent
      (_root_.Float.Model.totalExponent c ec) := by
    rw [htotalc]
    change e - (d : Int) ≤ t
    dsimp [d]
    omega
  have hscale := shiftToTargetExponent_scale64 c (51 - d) ec hc hlec
  have hmant : c * 2 ^ (51 - d) = m * 4503599627370496 := by
    dsimp [c, a]
    rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le hdle]
    change (m + m) * 2251799813685248 = m * 4503599627370496
    omega
  have hexp : ec - ((51 - d : Nat) : Int) = e - 51 := by
    dsimp [ec]
    omega
  rw [hmant, hexp] at hscale
  unfold _root_.Float.Model.UnpackedFloat.round
    _root_.Float.Model.UnpackedFloat.decreaseExponent
  dsimp only
  change
    _root_.Float.Model.UnpackedFloat.roundWithAccuracy
        _root_.Float.Model.Format.binary64 s (a <<< d) ec
        _root_.Float.Model.UnpackedFloat.Accuracy.exact = _
  rw [Nat.shiftLeft_eq]
  change
    _root_.Float.Model.UnpackedFloat.roundWithAccuracy
        _root_.Float.Model.Format.binary64 s c ec
        _root_.Float.Model.UnpackedFloat.Accuracy.exact = _
  unfold _root_.Float.Model.UnpackedFloat.roundWithAccuracy
  rw [← hscale]

private theorem unpacked_add_self_mul_two_worker64
    (a : _root_.Float.Model.UnpackedFloat) :
    _root_.Float.Model.UnpackedFloat.add _root_.Float.Model.Format.binary64 a a =
      _root_.Float.Model.UnpackedFloat.mul _root_.Float.Model.Format.binary64 a
        (.finite .positive 4503599627370496 (-51) (by decide)) := by
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
          _root_.Float.Model.UnpackedFloat.round _root_.Float.Model.Format.binary64
              .negative (m + m) e =
            _root_.Float.Model.UnpackedFloat.roundWithAccuracy
              _root_.Float.Model.Format.binary64 .negative (m * 4503599627370496) (e - 51)
              _root_.Float.Model.UnpackedFloat.Accuracy.exact
        exact round_double_worker64 .negative m e hm
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
          _root_.Float.Model.UnpackedFloat.round _root_.Float.Model.Format.binary64
              .positive (m + m) e =
            _root_.Float.Model.UnpackedFloat.roundWithAccuracy
              _root_.Float.Model.Format.binary64 .positive (m * 4503599627370496) (e - 51)
              _root_.Float.Model.UnpackedFloat.Accuracy.exact
        exact round_double_worker64 .positive m e hm

private theorem model_add_self_mul_two_worker64
    [certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate z53 z1024]
    (f : float) :
    modelBinary64
        (_root_.Float.Model.UnpackedFloat.add _root_.Float.Model.Format.binary64) f f =
      modelBinary64
        (_root_.Float.Model.UnpackedFloat.mul _root_.Float.Model.Format.binary64) f
          (Float.of_int (Integers.Int.repr (ZArith.BinInt.Z.of_nat 2))) := by
  rw [float64_of_int_two_bits]
  unfold modelBinary64
  rw [float64_unpack_two_bits, unpacked_add_self_mul_two_worker64]

private theorem isNaN_of_int_two_worker64
    [certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate z53 z1024] :
    isNaN64 (Float.of_int (Integers.Int.repr (ZArith.BinInt.Z.of_nat 2))) = false := by
  rw [float64_of_int_two_bits]
  rfl

namespace Float

theorem mul2_add
    [certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate z53 z1024] :
    Float.mul2_addStatement := by
  intro f
  unfold Float.add Float.mul
  rw [model_add_self_mul_two_worker64]
  have htwo := isNaN_of_int_two_worker64
  by_cases hf : isNaN64 f = true
  · simp only [finishBinary, binop_nan, cons_pl, hf, htwo, Bool.true_or,
      Bool.false_eq_true, ↓reduceIte]
    rw [CompCert4Lean.X86_64.Archi.choose_nan_64_idem]
  · simp [finishBinary, hf, htwo]

end Float

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats.Float

theorem of_intu_of_int_1
    [certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate z53 z1024] :
    of_intu_of_int_1Statement := by
  intro x hx
  suffices hs : Integers.Int.signed x = Integers.Int.unsigned x by
    simp only [of_intu, of_int, hs]
  have hbound : Integers.Int.unsigned ox8000_0000 = Integers.Int.half_modulus := by
    decide
  have hlt := (Integers.Int.ltu_inv_proof x ox8000_0000 hx).2
  rw [hbound] at hlt
  exact Coqlib.zlt_true _ _ _ _ _ hlt

end CompCert4Lean.Lib.Floats.Float

namespace CompCert4Lean.Lib.Floats.Sqrt

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private def sqrtRawIsNaN (spec : Float.Model.Format)
    (x : BitVec spec.numBits) : Bool :=
  Float.Model.UnpackedFloat.unpackExponent x == (-1#_) &&
    Float.Model.UnpackedFloat.unpackMantissa x != (0#_)

private def sqrtDefaultNaN (spec : Float.Model.Format) : BitVec spec.numBits :=
  let signMask : BitVec spec.numBits :=
    1#_ <<< (spec.numBits - 1)
  Float.Model.UnpackedFloat.packedNaN spec ||| signMask

private def sqrtQuietNaN (spec : Float.Model.Format)
    (x : BitVec spec.numBits) : BitVec spec.numBits :=
  let quietMask : BitVec spec.numBits :=
    1#_ <<< (spec.mantissaBitsWithoutImplicit - 1)
  x ||| quietMask

private theorem sqrt_nan_equiv (b : BitVec 32) :
    isNaN32 (⟨b⟩ : float32) = sqrtRawIsNaN Float.Model.Format.binary32 b := by
  unfold isNaN32 exponent32 fraction32 sqrtRawIsNaN
  simp only [Float.Model.UnpackedFloat.unpackExponent,
    Float.Model.UnpackedFloat.unpackMantissa]
  have hexp : (b.toNat / 8388608 % 256 == 255) =
      (BitVec.extractLsb' 23 8 b == 255#8) := by
    apply Bool.eq_iff_iff.mpr
    simp [BitVec.toNat_eq, BitVec.extractLsb'_toNat,
      Nat.shiftRight_eq_div_pow]
  have hmant : (b.toNat % 8388608 != 0) =
      (BitVec.extractLsb' 0 23 b != 0#23) := by
    apply Bool.eq_iff_iff.mpr
    simp [BitVec.toNat_eq, BitVec.extractLsb'_toNat]
  rw [hexp, hmant]
  rfl

end CompCert4Lean.Lib.Floats.Sqrt

namespace CompCert4Lean.Lib.Floats.Sqrt

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

set_option maxRecDepth 100000 in
private theorem test_quiet (b : BitVec 32)
    (h : isNaN32 (⟨b⟩ : float32) = true) :
    (b ||| (1#32 <<< 22)) = (Float32.unop_nan (⟨b⟩ : float32)).bits := by
  have hparts : (exponent32 (⟨b⟩ : float32) == (2 ^ 8 - 1)) = true ∧
      (fraction32 (⟨b⟩ : float32) != 0) = true := by
    simpa only [isNaN32, Bool.and_eq_true] using h
  have hq : 0 < b.toNat % 8388608 := by
    have hne : b.toNat % 8388608 ≠ 0 := by simpa [fraction32] using hparts.2
    omega
  have hqlt : b.toNat % 8388608 < 8388608 :=
    Nat.mod_lt _ (by decide)
  have hsign : b.toNat / 2147483648 % 2 = 1 ∨
      b.toNat / 2147483648 % 2 = 0 := by omega
  have hqorlt : b.toNat % 8388608 ||| 4194304 < 8388608 := by
    have h := Nat.or_lt_two_pow (x := b.toNat % 8388608) (y := 4194304)
      (n := 23) hqlt (by decide)
    simpa using h
  have hqorpos : 0 < (b.toNat % 8388608 ||| 4194304) % 8388608 := by
    rw [Nat.mod_eq_of_lt hqorlt]
    exact Nat.lt_of_lt_of_le (by decide) (Nat.right_le_or)
  have hqpos :
      PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.of_nat (b.toNat % 8388608)) =
        b.toNat % 8388608 := by
    change posToNat (posOfNat (b.toNat % 8388608)) = b.toNat % 8388608
    exact posToNat_posOfNat hq
  have hpos :
      PArith.BinPos.Pos.to_nat
          (PArith.BinPos.Pos.of_nat
            ((PArith.BinPos.Pos.to_nat
                (PArith.BinPos.Pos.of_nat (b.toNat % 8388608)) ||| 4194304) % 8388608)) =
        (b.toNat % 8388608 ||| 4194304) % 8388608 := by
    rw [hqpos]
    exact posToNat_posOfNat hqorpos
  have hpos2 :
      PArith.BinPos.Pos.to_nat
          (PArith.BinPos.Pos.of_nat
            ((b.toNat % 8388608 ||| 4194304) % 8388608)) =
        (b.toNat % 8388608 ||| 4194304) % 8388608 := by
    exact posToNat_posOfNat hqorpos
  unfold Float32.unop_nan Float32.cons_pl quiet_nan_32 quiet_nan_32_payload
  simp [h, CompCert4Lean.X86_64.Archi.choose_nan_32, mkNaN32,
    payload32, sign32, fraction32, hq, hqlt,
    hqpos, hpos]
  rw [hpos2]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat]
  have hklt : b.toNat / 8388608 < 512 := by
    have hb := b.isLt
    omega
  have hkmod : b.toNat / 8388608 % 256 = 255 := by
    have hh := hparts.1
    simp only [exponent32] at hh
    simpa [Nat.pow_succ, Nat.mul_comm] using hh
  have hkdecomp : b.toNat / 8388608 =
      (b.toNat / 2147483648 % 2) * 256 + 255 := by
    omega
  have hbdecomp : b.toNat =
      ((b.toNat / 2147483648 % 2) * 256 + 255) * 8388608 +
        (b.toNat % 8388608) := by
    have hm := Nat.mod_add_div b.toNat 8388608
    omega
  have hlow :
      (b.toNat ||| 4194304) % 8388608 =
        (b.toNat % 8388608 ||| 4194304) % 8388608 := by
    have hh := Nat.or_mod_two_pow (a := b.toNat) (b := 4194304) (n := 23)
    rw [Nat.mod_eq_of_lt hqorlt]
    simpa [show (2 ^ 23 : Nat) = 8388608 by decide] using hh
  have hhigh :
      (b.toNat ||| 4194304) / 8388608 = b.toNat / 8388608 := by
    have hh := Nat.or_div_two_pow (a := b.toNat) (b := 4194304) (n := 23)
    simpa [show (2 ^ 23 : Nat) = 8388608 by decide] using hh
  have hor : b.toNat ||| 4194304 =
      ((b.toNat / 2147483648 % 2) * 256 + 255) * 8388608 +
        ((b.toNat % 8388608 ||| 4194304) % 8388608) := by
    rw [← Nat.mod_add_div (b.toNat ||| 4194304) 8388608]
    rw [hlow, hhigh, hkdecomp]
    omega
  rw [Nat.mod_eq_of_lt hqorlt]
  have hfull :
      ((if b.toNat / 2147483648 % 2 = 1 then 2147483648 else 0) +
        2139095040 + ((b.toNat % 8388608 ||| 4194304) % 8388608)) <
        4294967296 := by
    split <;> omega
  rw [Nat.mod_eq_of_lt hfull]
  rw [show (4194304 % (2 ^ 32 : Nat)) = 4194304 by decide]
  have hbase :
      (b.toNat / 2147483648 % 2 * 256 + 255) * 8388608 =
        (if b.toNat / 2147483648 % 2 = 1 then 2147483648 else 0) +
          2139095040 := by
    split <;> omega
  rw [← hbase]
  simpa only using hor

private theorem test_default :
    sqrtDefaultNaN Float.Model.Format.binary32 =
      (default_nan_32 : float32).bits := by
  unfold sqrtDefaultNaN default_nan_32 quiet_nan_32 quiet_nan_32_payload
  unfold CompCert4Lean.X86_64.Archi.default_nan_32
  rfl

theorem float32_sqrt_correct_proof : float32_sqrt_correctStatement := by
  intro x
  have hraw (b : BitVec 32) :
      Sqrt.rawSqrt Float.Model.Format.binary32 b =
        (if sqrtRawIsNaN Float.Model.Format.binary32 b then
          sqrtQuietNaN Float.Model.Format.binary32 b
        else
          let r := Float.Model.UnpackedFloat.pack Float.Model.Format.binary32
            (Sqrt.unpackedSqrt Float.Model.Format.binary32
              (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary32 b))
          if sqrtRawIsNaN Float.Model.Format.binary32 r then
            sqrtDefaultNaN Float.Model.Format.binary32
          else r) := by
    rfl
  apply UInt32.toBitVec_inj.1
  change Sqrt.rawSqrt Float.Model.Format.binary32 x.toBitVec =
    (Float32.sqrt (⟨x.toBitVec⟩ : float32)).bits
  unfold Float32.sqrt
  rw [hraw]
  by_cases h : sqrtRawIsNaN Float.Model.Format.binary32 x.toBitVec = true
  · have hxe := congrArg (fun q : Bool => q = true)
      (sqrt_nan_equiv x.toBitVec)
    have hx : isNaN32 (⟨x.toBitVec⟩ : float32) = true := hxe.mpr h
    simp only [h, hx, Bool.false_eq_true, ↓reduceIte]
    exact test_quiet x.toBitVec hx
  · have hx : isNaN32 (⟨x.toBitVec⟩ : float32) ≠ true := by
      intro hx
      exact h ((congrArg (fun q : Bool => q = true)
        (sqrt_nan_equiv x.toBitVec)).mp hx)
    simp only [h, hx, Bool.false_eq_true, ↓reduceIte]
    by_cases hr : sqrtRawIsNaN Float.Model.Format.binary32
        (Float.Model.UnpackedFloat.pack Float.Model.Format.binary32
          (Sqrt.unpackedSqrt Float.Model.Format.binary32
            (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary32 x.toBitVec))) = true
    · have hrx := congrArg (fun q : Bool => q = true)
          (sqrt_nan_equiv
            (Float.Model.UnpackedFloat.pack Float.Model.Format.binary32
              (Sqrt.unpackedSqrt Float.Model.Format.binary32
                (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary32 x.toBitVec))))
      simp only [hr, hrx.mpr hr, Bool.false_eq_true, ↓reduceIte]
      exact test_default
    · have hrx : isNaN32
          (⟨Float.Model.UnpackedFloat.pack Float.Model.Format.binary32
            (Sqrt.unpackedSqrt Float.Model.Format.binary32
              (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary32 x.toBitVec))⟩ : float32) ≠ true := by
        intro hh
        exact hr ((congrArg (fun q : Bool => q = true)
          (sqrt_nan_equiv
            (Float.Model.UnpackedFloat.pack Float.Model.Format.binary32
              (Sqrt.unpackedSqrt Float.Model.Format.binary32
                (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary32 x.toBitVec))))).mp hh)
      simp only [hr, hrx, Bool.false_eq_true, ↓reduceIte]

end CompCert4Lean.Lib.Floats.Sqrt

namespace CompCert4Lean.Lib.Floats

theorem integer_representable_n :
    integer_representable_nStatement :=
  CompCert4Lean.Lib.IEEE754_extra.integer_representable_n
    (prec := z53) (emax := z1024)

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Flocq.Core

private theorem manual_decode64_certificate (value : float) :
    Binary.BinaryFloatCertificate (decode64 value) := by
  have valid := Bits.binary_float_of_bits_aux_correct
    (ZArith.BinInt.Z.of_nat 52) (ZArith.BinInt.Z.of_nat 11)
    (by change (0 : Int) < 52; decide)
    (by change (0 : Int) < 11; decide)
    (by change (53 : Int) < 1024; decide)
    (ZArith.BinInt.Z.of_nat value.bits.toNat)
  exact (Binary.FF2B _ valid).property

set_option maxRecDepth 10000 in
private theorem manual_mantissa_bound64 (mantissa : positive) (exponent : Z)
    (bounded : Binary.bounded (prec := z53) (emax := z1024) mantissa exponent = true) :
    (posToNat mantissa : Int) < 9007199254740992 := by
  have canonical := (Bool.and_eq_true_iff.mp bounded).1
  change ZArith.Zbool.Zeq_bool
    (ZArith.BinInt.Z.max
      (ZArith.BinInt.Z.sub
        (ZArith.BinInt.Z.add (.Zpos (BinarySingleNaN.digits2_pos mantissa)) exponent) z53)
      (BinarySingleNaN.emin0 z53 z1024)) exponent = true at canonical
  simp only [ZArith.Zbool.Zeq_bool, decide_eq_true_eq] at canonical
  have lower := ZArith.BinInt.Z.le_max_l
    (ZArith.BinInt.Z.sub
      (ZArith.BinInt.Z.add (.Zpos (BinarySingleNaN.digits2_pos mantissa)) exponent) z53)
    (BinarySingleNaN.emin0 z53 z1024)
  rw [canonical] at lower
  have digits : ZArith.BinInt.Z.le (Digits.Zdigits Digits.radix2 (.Zpos mantissa)) z53 := by
    rw [← Digits.Zpos_digits2_pos]
    change intOfZ (.Zpos (BinarySingleNaN.digits2_pos mantissa)) ≤ 53
    change intOfZ (ZArith.BinInt.Z.sub
      (ZArith.BinInt.Z.add (.Zpos (BinarySingleNaN.digits2_pos mantissa)) exponent) z53) ≤
        intOfZ exponent at lower
    simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add, intOfZ_zOfInt] at lower
    change intOfZ (.Zpos (BinarySingleNaN.digits2_pos mantissa)) + intOfZ exponent - 53 ≤
      intOfZ exponent at lower
    omega
  have bound := Digits.Zpower_gt_Zdigits Digits.radix2 z53 (.Zpos mantissa) digits
  change intOfZ (ZArith.BinInt.Z.abs (.Zpos mantissa)) < 9007199254740992 at bound
  rw [ZArith.BinInt.Z.abs, intOfZ_zOfInt] at bound
  change (((posToNat mantissa : Int).natAbs : Int)) < 9007199254740992 at bound
  simpa only [Int.natAbs_natCast] using bound

private theorem manual_positive_compare_bound64 (mantissa : positive) (exponent : Z)
    (less : Binary.Bcompare (prec := z53) (emax := z1024)
      (.B754_finite false mantissa exponent)
      (.B754_finite false (posOfNat 4503599627370496) (.Zneg (posOfNat 21))) = some .Lt) :
    intOfZ exponent < -21 ∨
      (intOfZ exponent = -21 ∧ posToNat mantissa < 4503599627370496) := by
  change some (match ZArith.BinInt.Z.compare exponent (.Zneg (posOfNat 21)) with
    | .Eq => PArith.BinPos.Pos.compare_cont .Eq mantissa (posOfNat 4503599627370496)
    | other => other) = some .Lt at less
  have compared := Option.some.inj less
  change (match (if intOfZ exponent < -21 then (.Lt : RCmp)
    else if intOfZ exponent = -21 then .Eq else .Gt) with
    | .Eq => PArith.BinPos.Pos.compare_cont .Eq mantissa (posOfNat 4503599627370496)
    | other => other) = .Lt at compared
  by_cases lower : intOfZ exponent < -21
  · exact Or.inl lower
  · right
    have equal : intOfZ exponent = -21 := by
      by_cases equal : intOfZ exponent = -21
      · exact equal
      · simp [lower, equal] at compared
    refine ⟨equal, ?_⟩
    have mantissa_less :
        PArith.BinPos.Pos.compare_cont .Eq mantissa (posOfNat 4503599627370496) = .Lt := by
      rw [if_neg lower, if_pos equal] at compared
      exact compared
    exact PArith.Pnat.nat_of_P_lt_Lt_compare_morphism _ _ mantissa_less

private theorem manual_div_pow_int (mantissa exponent : positive) :
    intOfZ (ZArith.BinInt.Z.div (.Zpos mantissa)
      (ZArith.BinInt.Z.pow_pos (.Zpos (.xO .xH)) exponent)) =
        (posToNat mantissa : Int) / (2 : Int) ^ posToNat exponent := by
  have nonnegative : ZArith.BinInt.Z.le .Z0 (.Zpos mantissa) := by
    change (0 : Int) ≤ posToNat mantissa
    omega
  have denominator : ZArith.BinInt.Z.le .Z0
      (ZArith.BinInt.Z.pow_pos (.Zpos (.xO .xH)) exponent) := by
    change (0 : Int) ≤ intOfZ (zOfInt ((2 : Int) ^ posToNat exponent))
    rw [intOfZ_zOfInt]
    exact Int.le_of_lt (Int.pow_pos (by decide))
  rw [← ZArith.Zquot.Zquot_Zdiv_pos _ _ nonnegative denominator]
  simp only [ZArith.BinInt.Z.quot, ZArith.BinInt.Z.pow_pos, intOfZ_zOfInt]
  change Int.tdiv (posToNat mantissa) ((2 : Int) ^ posToNat exponent) = _
  exact Int.tdiv_eq_ediv_of_nonneg (Int.natCast_nonneg _)

private theorem manual_negative_trunc_nonpositive
    (mantissa : positive) (exponent result : Z)
    (converted : IEEE754_extra.ZofB (prec := z53) (emax := z1024)
      (.B754_finite true mantissa exponent) = some result) :
    intOfZ result ≤ 0 := by
  cases exponent with
  | Z0 =>
    have equal := congrArg intOfZ (Option.some.inj converted)
    change intOfZ (ZArith.BinInt.Z.opp (.Zpos mantissa)) = intOfZ result at equal
    rw [ZArith.BinInt.Z.opp, intOfZ_zOfInt] at equal
    change -(posToNat mantissa : Int) = intOfZ result at equal
    omega
  | Zpos shift =>
    have equal := congrArg intOfZ (Option.some.inj converted)
    change intOfZ (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.opp (.Zpos mantissa))
      (ZArith.BinInt.Z.pow_pos (.Zpos (.xO .xH)) shift)) = intOfZ result at equal
    simp only [ZArith.BinInt.Z.mul, ZArith.BinInt.Z.opp,
      ZArith.BinInt.Z.pow_pos, intOfZ_zOfInt] at equal
    rw [← equal]
    apply Int.mul_nonpos_of_nonpos_of_nonneg
    · change -(posToNat mantissa : Int) ≤ 0
      omega
    · exact Int.le_of_lt (Int.pow_pos (by decide))
  | Zneg shift =>
    have equal := congrArg intOfZ (Option.some.inj converted)
    change intOfZ (ZArith.BinInt.Z.opp
      (ZArith.BinInt.Z.div (.Zpos mantissa)
        (ZArith.BinInt.Z.pow_pos (.Zpos (.xO .xH)) shift))) = intOfZ result at equal
    rw [ZArith.BinInt.Z.opp, intOfZ_zOfInt, manual_div_pow_int] at equal
    have nonnegative : 0 ≤ (posToNat mantissa : Int) / (2 : Int) ^ posToNat shift :=
      Int.ediv_nonneg (Int.natCast_nonneg _) (Int.le_of_lt (Int.pow_pos (by decide)))
    omega

private theorem manual_positive_trunc_bound
    (mantissa : positive) (exponent result : Z)
    (mantissa_bound : (posToNat mantissa : Int) < 9007199254740992)
    (compared : intOfZ exponent < -21 ∨
      (intOfZ exponent = -21 ∧ posToNat mantissa < 4503599627370496))
    (converted : IEEE754_extra.ZofB (prec := z53) (emax := z1024)
      (.B754_finite false mantissa exponent) = some result) :
    intOfZ result < 2147483648 := by
  have exponent_bound : intOfZ exponent ≤ -21 := by omega
  cases exponent with
  | Z0 => change (0 : Int) ≤ -21 at exponent_bound; omega
  | Zpos shift =>
    change (posToNat shift : Int) ≤ -21 at exponent_bound
    omega
  | Zneg shift =>
    have equal := congrArg intOfZ (Option.some.inj converted)
    change intOfZ (ZArith.BinInt.Z.div (.Zpos mantissa)
      (ZArith.BinInt.Z.pow_pos (.Zpos (.xO .xH)) shift)) = intOfZ result at equal
    rw [manual_div_pow_int] at equal
    rw [← equal]
    apply (Int.ediv_lt_iff_lt_mul (Int.pow_pos (by decide))).mpr
    rcases compared with smaller | ⟨same, mantissa_small⟩
    · have shift_bound : 22 ≤ posToNat shift := by change -(posToNat shift : Int) < -21 at smaller; omega
      have power_bound := Nat.pow_le_pow_right (by decide : 0 < 2) shift_bound
      have power_bound_int : (4194304 : Int) ≤ (2 : Int) ^ posToNat shift := by
        exact Int.ofNat_le.mpr power_bound
      have product_bound := Int.mul_le_mul_of_nonneg_left power_bound_int
        (by decide : (0 : Int) ≤ 2147483648)
      omega
    · have shift_equal : posToNat shift = 21 := by change -(posToNat shift : Int) = -21 at same; omega
      rw [shift_equal]
      change (posToNat mantissa : Int) < 4503599627370496
      omega

theorem Float.to_intu_to_int_1
    [certificate : Binary.BinaryNormalizeCertificate z53 z1024] :
    Float.to_intu_to_int_1Statement := by
  intro value word less converted
  have threshold : decode64 (Float.of_intu Float.ox8000_0000) =
      Binary.B754_finite false (posOfNat 4503599627370496) (.Zneg (posOfNat 21)) := by
    rfl
  have compared : Binary.Bcompare (decode64 value)
      (.B754_finite false (posOfNat 4503599627370496) (.Zneg (posOfNat 21))) = some .Lt := by
    unfold Float.cmp Float.compare at less
    rw [threshold] at less
    cases comparison_result : Binary.Bcompare (decode64 value)
        (.B754_finite false (posOfNat 4503599627370496) (.Zneg (posOfNat 21))) with
    | none => simp [comparison_result, cmp_of_comparison] at less
    | some ordering =>
      cases ordering <;> simp_all [cmp_of_comparison]
  unfold Float.to_intu at converted
  unfold Float.to_int
  cases range_result : IEEE754_extra.ZofB_range (decode64 value) z0 Integers.Int.max_unsigned with
  | none => simp [range_result] at converted
  | some result =>
    have in_range := IEEE754_extra.ZofB_range_inversion
      ⟨decode64 value, manual_decode64_certificate value⟩ z0 Integers.Int.max_unsigned result range_result
    rcases in_range with ⟨nonnegative, _, truncated⟩
    change IEEE754_extra.ZofB (decode64 value) = some result at truncated
    have upper : intOfZ result < 2147483648 := by
      have valid := manual_decode64_certificate value
      cases decoded : decode64 value with
      | B754_zero sign =>
        rw [decoded] at truncated
        have result_zero : z0 = result := Option.some.inj truncated
        rw [← result_zero]
        decide
      | B754_infinity sign => simp [decoded, IEEE754_extra.ZofB] at truncated
      | B754_nan sign payload => simp [decoded, IEEE754_extra.ZofB] at truncated
      | B754_finite sign mantissa exponent =>
        rw [decoded] at truncated compared valid
        cases sign with
        | false =>
          exact manual_positive_trunc_bound mantissa exponent result
            (manual_mantissa_bound64 mantissa exponent valid)
            (manual_positive_compare_bound64 mantissa exponent compared) truncated
        | true =>
          have upper_zero := manual_negative_trunc_nonpositive mantissa exponent result truncated
          omega
    have minimum : ZArith.Zbool.Zle_bool Integers.Int.min_signed result = true := by
      change (if -2147483648 ≤ intOfZ result then true else false) = true
      have positive : (0 : Int) ≤ intOfZ result := nonnegative
      simp only [show -2147483648 ≤ intOfZ result by omega, ↓reduceIte]
    have maximum : ZArith.Zbool.Zle_bool result Integers.Int.max_signed = true := by
      change (if intOfZ result ≤ 2147483647 then true else false) = true
      simp only [show intOfZ result ≤ 2147483647 by omega, ↓reduceIte]
    simpa only [IEEE754_extra.ZofB_range, truncated, minimum, maximum,
      Bool.true_and, ↓reduceIte] using (show (some result).map Integers.Int.repr = some word from by
        simpa only [range_result] using converted)

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754

private theorem conversion_decode_valid (mantissaWidth exponentWidth : Z)
    (positiveMantissa : Zaux.Zlt .Z0 mantissaWidth)
    (positiveExponent : Zaux.Zlt .Z0 exponentWidth)
    (validFormat : Zaux.Zlt (Bits.prec mantissaWidth) (Bits.emax exponentWidth))
    (word : Z) :
    Binary.BinaryFloatCertificate
      (Bits.binary_float_of_bits_unchecked mantissaWidth exponentWidth
        positiveMantissa positiveExponent validFormat word) := by
  have valid := Bits.binary_float_of_bits_aux_correct mantissaWidth exponentWidth
    positiveMantissa positiveExponent validFormat word
  unfold Bits.binary_float_of_bits_unchecked
  generalize Bits.binary_float_of_bits_aux mantissaWidth exponentWidth word = decoded at *
  cases decoded <;>
    simpa [Binary.BinaryFloatCertificate, Binary.FF2B_unchecked, Binary.B2FF] using valid

private theorem conversion_decode32_valid (value : float32) :
    Binary.BinaryFloatCertificate (decode32 value) :=
  by
    have valid := Bits.binary_float_of_bits_aux_correct
      (ZArith.BinInt.Z.of_nat 23) (ZArith.BinInt.Z.of_nat 8)
      (by change (0 : Int) < 23; decide)
      (by change (0 : Int) < 8; decide)
      (by change (24 : Int) < 128; decide)
      (ZArith.BinInt.Z.of_nat value.bits.toNat)
    exact (Binary.FF2B _ valid).property

private theorem conversion_decode64_valid (value : float) :
    Binary.BinaryFloatCertificate (decode64 value) :=
  by
    have valid := Bits.binary_float_of_bits_aux_correct
      (ZArith.BinInt.Z.of_nat 52) (ZArith.BinInt.Z.of_nat 11)
      (by change (0 : Int) < 52; decide)
      (by change (0 : Int) < 11; decide)
      (by change (53 : Int) < 1024; decide)
      (ZArith.BinInt.Z.of_nat value.bits.toNat)
    exact (Binary.FF2B _ valid).property

private theorem conversion_binary_of_bits_roundtrip
    (value : Binary.CertifiedBinaryFloat z53 z1024) :
    Bits.binary_float_of_bits_unchecked
      (ZArith.BinInt.Z.of_nat 52) (ZArith.BinInt.Z.of_nat 11)
      (by change (0 : Int) < 52; decide)
      (by change (0 : Int) < 11; decide)
      (by change (53 : Int) < 1024; decide)
      (Bits.bits_of_binary_float (ZArith.BinInt.Z.of_nat 52)
        (ZArith.BinInt.Z.of_nat 11) value.1) = value.1 := by
  rcases value with ⟨value, hvalue⟩
  have hsplit := Bits.split_bits_of_binary_float_correct
    (ZArith.BinInt.Z.of_nat 52) (ZArith.BinInt.Z.of_nat 11)
    (by change (0 : Int) < 52; decide)
    (by change (0 : Int) < 11; decide) ⟨value, hvalue⟩
  unfold Bits.binary_float_of_bits_unchecked Bits.binary_float_of_bits_aux
  cases value with
  | B754_zero sign =>
    simp [Bits.split_bits_of_binary_float] at hsplit ⊢
    rw [hsplit]
    rfl
  | B754_infinity sign =>
    simp [Bits.split_bits_of_binary_float] at hsplit ⊢
    rw [hsplit]
    rfl
  | B754_nan sign payload =>
    simp [Bits.split_bits_of_binary_float] at hsplit ⊢
    rw [hsplit]
    have hEq : Bits.Zeq_bool
        (Bits.Zsub (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 11)) Bits.Zone)
        (Bits.Zsub (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 11)) Bits.Zone) = true :=
      CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_true _ _ rfl
    rw [hEq]
    have hzero : Bits.Zeq_bool
        (Bits.Zsub (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 11)) Bits.Zone)
        Bits.Z0 = false :=
      CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false _ _ (by decide)
    rw [hzero]
    simp [Binary.FF2B_unchecked]
    rfl
  | B754_finite sign mantissa exponent =>
    simp [Bits.split_bits_of_binary_float] at hsplit ⊢
    have hparts :
        BinarySingleNaN.canonical_mantissa0 z53 z1024 mantissa exponent = true ∧
          ZArith.Zbool.Zle_bool exponent (ZArith.BinInt.Z.sub z1024 z53) = true := by
      change (BinarySingleNaN.canonical_mantissa0 z53 z1024 mantissa exponent &&
        ZArith.Zbool.Zle_bool exponent (ZArith.BinInt.Z.sub z1024 z53)) = true at hvalue
      exact Bool.and_eq_true_iff.mp hvalue
    have hcan := hparts.1
    have hbound := hparts.2
    by_cases hb : Bits.Zle_bool Bits.Z0
        (Bits.Zsub (Bits.Zpos mantissa) (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 52))) = true
    · simp [hb] at hsplit ⊢
      rw [hsplit]
      have hcanEq := ZArith.Zbool.Zeq_bool_eq _ _ hcan
      change ZArith.BinInt.Z.max
          (ZArith.BinInt.Z.sub
            (ZArith.BinInt.Z.add
              (ZArith.BinInt.Z.pos (BinarySingleNaN.digits2_pos mantissa)) exponent) z53)
          (BinarySingleNaN.emin0 z53 z1024) = exponent at hcanEq
      have hlowZ := ZArith.BinInt.Z.le_max_r
        (ZArith.BinInt.Z.sub
          (ZArith.BinInt.Z.add
            (ZArith.BinInt.Z.pos (BinarySingleNaN.digits2_pos mantissa)) exponent) z53)
        (BinarySingleNaN.emin0 z53 z1024)
      rw [hcanEq] at hlowZ
      have hboundZ := ZArith.Zbool.Zle_bool_imp_le exponent
        (ZArith.BinInt.Z.sub z1024 z53) hbound
      have hzadd : ∀ a b : Z,
          intOfZ (ZArith.BinInt.Z.add a b) = intOfZ a + intOfZ b := by
        intro a b
        change intOfZ (zOfInt (intOfZ a + intOfZ b)) = _
        exact intOfZ_zOfInt _
      have hzsub : ∀ a b : Z,
          intOfZ (ZArith.BinInt.Z.sub a b) = intOfZ a - intOfZ b := by
        intro a b
        change intOfZ (zOfInt (intOfZ a - intOfZ b)) = _
        exact intOfZ_zOfInt _
      have hem : intOfZ (Bits.emin (ZArith.BinInt.Z.of_nat 52)
          (ZArith.BinInt.Z.of_nat 11)) = -1074 := by decide
      have hemin64 : intOfZ (BinarySingleNaN.emin0 z53 z1024) = -1074 := by decide
      have hone : intOfZ Bits.Zone = 1 := by decide
      have hshift_formula : intOfZ (Bits.Zadd (Bits.Zsub exponent
          (Bits.emin (ZArith.BinInt.Z.of_nat 52) (ZArith.BinInt.Z.of_nat 11))) Bits.Zone) =
          intOfZ exponent + 1075 := by
        rw [hzadd, hzsub, hem, hone]
        omega
      have hshift_pos : 0 <
          intOfZ (Bits.Zadd (Bits.Zsub exponent (Bits.emin (ZArith.BinInt.Z.of_nat 52)
            (ZArith.BinInt.Z.of_nat 11))) Bits.Zone) := by
        rw [hshift_formula]
        change intOfZ (BinarySingleNaN.emin0 z53 z1024) ≤ intOfZ exponent at hlowZ
        rw [hemin64] at hlowZ
        change intOfZ exponent ≤ 971 at hboundZ
        omega
      have hshift_lt : intOfZ (Bits.Zadd (Bits.Zsub exponent
          (Bits.emin (ZArith.BinInt.Z.of_nat 52) (ZArith.BinInt.Z.of_nat 11))) Bits.Zone) < 2047 := by
        rw [hshift_formula]
        change intOfZ exponent ≤ 971 at hboundZ
        omega
      have hshift_ne_zero : Bits.Zadd (Bits.Zsub exponent
          (Bits.emin (ZArith.BinInt.Z.of_nat 52) (ZArith.BinInt.Z.of_nat 11))) Bits.Zone ≠ Bits.Z0 := by
        intro hz
        have hz' := congrArg intOfZ hz
        rw [hshift_formula] at hz'
        have hzero' : intOfZ Bits.Z0 = 0 := by decide
        rw [hzero'] at hz'
        omega
      have hshift_ne_max : Bits.Zadd (Bits.Zsub exponent
          (Bits.emin (ZArith.BinInt.Z.of_nat 52) (ZArith.BinInt.Z.of_nat 11))) Bits.Zone ≠
          Bits.Zsub (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 11)) Bits.Zone := by
        intro hz
        have hz' := congrArg intOfZ hz
        rw [hshift_formula] at hz'
        have hmax' : intOfZ (Bits.Zsub (Bits.Zpower Bits.Ztwo
            (ZArith.BinInt.Z.of_nat 11)) Bits.Zone) = 2047 := by decide
        rw [hmax'] at hz'
        omega
      have hzero : Bits.Zeq_bool
          (Bits.Zadd (Bits.Zsub exponent (Bits.emin (ZArith.BinInt.Z.of_nat 52)
            (ZArith.BinInt.Z.of_nat 11))) Bits.Zone) Bits.Z0 = false :=
        CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false _ _ hshift_ne_zero
      have hmax : Bits.Zeq_bool
          (Bits.Zadd (Bits.Zsub exponent (Bits.emin (ZArith.BinInt.Z.of_nat 52)
            (ZArith.BinInt.Z.of_nat 11))) Bits.Zone)
          (Bits.Zsub (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 11)) Bits.Zone) = false :=
        CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false _ _ hshift_ne_max
      rw [hzero, hmax]
      have hsum : Bits.Zadd (Bits.Zsub (Bits.Zpos mantissa)
          (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 52)))
          (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 52)) = Bits.Zpos mantissa := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        rw [hzadd, hzsub]
        have hpow : intOfZ (Bits.Zpower Bits.Ztwo
            (ZArith.BinInt.Z.of_nat 52)) = 2 ^ 52 := by decide
        rw [hpow]
        omega
      have hexp : Bits.Zsub
          (Bits.Zadd (Bits.Zadd (Bits.Zsub exponent
            (Bits.emin (ZArith.BinInt.Z.of_nat 52) (ZArith.BinInt.Z.of_nat 11))) Bits.Zone)
            (Bits.emin (ZArith.BinInt.Z.of_nat 52) (ZArith.BinInt.Z.of_nat 11))) Bits.Zone = exponent := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        rw [hzsub, hzadd, hzadd, hzsub]
        rw [hem, hone]
        omega
      rw [hsum, hexp]
      rfl
    · simp [hb] at hsplit ⊢
      rw [hsplit]
      have hzeroEq : Bits.Zeq_bool Bits.Z0 Bits.Z0 = true :=
        CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_true _ _ rfl
      rw [hzeroEq]
      have hzsub : ∀ a b : Z,
          intOfZ (ZArith.BinInt.Z.sub a b) = intOfZ a - intOfZ b := by
        intro a b
        change intOfZ (zOfInt (intOfZ a - intOfZ b)) = _
        exact intOfZ_zOfInt _
      have hltbranch : Bits.Zlt (Bits.Zsub (Bits.Zpos mantissa)
          (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 52))) Bits.Z0 := by
        have hs := CompCert4Lean.Flocq.Core.Zaux.Zle_bool_spec Bits.Z0
          (Bits.Zsub (Bits.Zpos mantissa)
            (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 52)))
        have hs' : CompCert4Lean.Flocq.Core.Zaux.Zle_bool_prop Bits.Z0
            (Bits.Zsub (Bits.Zpos mantissa)
              (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 52))) false := by
          simpa [hb] using hs
        cases hs' with
        | Zle_bool_false_ h => exact h
      have hmlt : Bits.Zlt (Bits.Zpos mantissa)
          (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 52)) := by
        change intOfZ (Bits.Zpos mantissa) < intOfZ
          (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 52))
        change intOfZ (Bits.Zsub (Bits.Zpos mantissa)
          (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 52))) < intOfZ Bits.Z0 at hltbranch
        rw [hzsub] at hltbranch
        have hz0 : intOfZ Bits.Z0 = 0 := by decide
        rw [hz0] at hltbranch
        omega
      have hdigit_le : ZArith.BinInt.Z.le (ZArith.BinInt.Z.pos
          (BinarySingleNaN.digits2_pos mantissa))
          (ZArith.BinInt.Z.of_nat 52) := by
        have habs : CompCert4Lean.Flocq.Core.Digits.Zabs (Bits.Zpos mantissa) =
            Bits.Zpos mantissa := by
          apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
          change intOfZ (zOfInt (Int.natAbs (Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat mantissa)))) = _
          rw [intOfZ_zOfInt]
          exact Int.natAbs_of_nonneg (Int.natCast_nonneg _)
        have hstrict : CompCert4Lean.Flocq.Core.Digits.Zlt
            (CompCert4Lean.Flocq.Core.Digits.Zabs (Bits.Zpos mantissa))
            (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 52)) := by
          rw [habs]
          exact hmlt
        have hdigits := CompCert4Lean.Flocq.Core.Digits.Zdigits_le_Zpower
          CompCert4Lean.Flocq.Core.Digits.radix2
          (ZArith.BinInt.Z.of_nat 52) (Bits.Zpos mantissa) hstrict
        have hdigit_eq : ZArith.BinInt.Z.pos (BinarySingleNaN.digits2_pos mantissa) =
            CompCert4Lean.Flocq.Core.Digits.Zdigits
              CompCert4Lean.Flocq.Core.Digits.radix2 (Bits.Zpos mantissa) := by
          exact CompCert4Lean.Flocq.Core.Digits.Zpos_digits2_pos mantissa
        rw [hdigit_eq]
        exact hdigits
      have hcanEq := ZArith.Zbool.Zeq_bool_eq _ _ hcan
      change ZArith.BinInt.Z.max
          (ZArith.BinInt.Z.sub
            (ZArith.BinInt.Z.add
              (ZArith.BinInt.Z.pos (BinarySingleNaN.digits2_pos mantissa)) exponent) z53)
          (BinarySingleNaN.emin0 z53 z1024) = exponent at hcanEq
      let first : Z := ZArith.BinInt.Z.sub
        (ZArith.BinInt.Z.add
          (ZArith.BinInt.Z.pos (BinarySingleNaN.digits2_pos mantissa)) exponent) z53
      have hexpEmin : exponent = BinarySingleNaN.emin0 z53 z1024 := by
        have hzadd : ∀ a b : Z,
            intOfZ (ZArith.BinInt.Z.add a b) = intOfZ a + intOfZ b := by
          intro a b
          change intOfZ (zOfInt (intOfZ a + intOfZ b)) = _
          exact intOfZ_zOfInt _
        have hzsub : ∀ a b : Z,
            intOfZ (ZArith.BinInt.Z.sub a b) = intOfZ a - intOfZ b := by
          intro a b
          change intOfZ (zOfInt (intOfZ a - intOfZ b)) = _
          exact intOfZ_zOfInt _
        by_cases hfirst : ZArith.BinInt.Z.le
            (BinarySingleNaN.emin0 z53 z1024) first
        · have hmax := ZArith.BinInt.Z.max_l first
              (BinarySingleNaN.emin0 z53 z1024) hfirst
          have hfirstEq : first = exponent := by
            exact hmax.symm.trans hcanEq
          have hfirstInt := congrArg intOfZ hfirstEq
          change intOfZ (ZArith.BinInt.Z.pos
              (BinarySingleNaN.digits2_pos mantissa)) ≤
            intOfZ (ZArith.BinInt.Z.of_nat 52) at hdigit_le
          have h52 : intOfZ (ZArith.BinInt.Z.of_nat 52) = 52 := by decide
          rw [h52] at hdigit_le
          change intOfZ (ZArith.BinInt.Z.sub
              (ZArith.BinInt.Z.add
                (ZArith.BinInt.Z.pos (BinarySingleNaN.digits2_pos mantissa)) exponent) z53) =
            intOfZ exponent at hfirstInt
          rw [hzsub, hzadd] at hfirstInt
          have hz53 : intOfZ z53 = 53 := by decide
          rw [hz53] at hfirstInt
          omega
        · have hfirst_le : ZArith.BinInt.Z.le first
              (BinarySingleNaN.emin0 z53 z1024) := by
            change intOfZ first ≤ intOfZ (BinarySingleNaN.emin0 z53 z1024)
            change ¬ intOfZ (BinarySingleNaN.emin0 z53 z1024) ≤ intOfZ first at hfirst
            omega
          have hmax := ZArith.BinInt.Z.max_r first
              (BinarySingleNaN.emin0 z53 z1024) hfirst_le
          exact (hmax.symm.trans hcanEq).symm
      have hzeroEmin : Bits.emin (ZArith.BinInt.Z.of_nat 52)
          (ZArith.BinInt.Z.of_nat 11) = exponent := by
        change BinarySingleNaN.emin0 z53 z1024 = exponent
        exact hexpEmin.symm
      rw [hzeroEmin]
      simp [Binary.FF2B_unchecked]
      rfl

private theorem conversion_encode64_decode (value : Binary.CertifiedBinaryFloat z53 z1024) :
    decode64 (encode64 value.1) = value.1 := by
  unfold decode64 encode64
  simp only [BitVec.toNat_ofNat]
  have hround := conversion_binary_of_bits_roundtrip value
  have hrange := Bits.bits_of_binary_float_range
    (ZArith.BinInt.Z.of_nat 52) (ZArith.BinInt.Z.of_nat 11)
    (by change (0 : Int) < 52; decide)
    (by change (0 : Int) < 11; decide) value
  have hnonneg : Bits.Zle Bits.Z0 (Bits.bits_of_b64 value.1) := by
    exact hrange.1
  have hlt : Bits.Zlt (Bits.bits_of_b64 value.1)
      (Bits.Zpower Bits.Ztwo
        (Bits.Zadd (Bits.Zadd (ZArith.BinInt.Z.of_nat 52)
          (ZArith.BinInt.Z.of_nat 11)) Bits.Zone)) := by
    exact hrange.2
  have hnonnegInt : 0 ≤ intOfZ (Bits.bits_of_b64 value.1) := by
    exact hnonneg
  have hltInt : intOfZ (Bits.bits_of_b64 value.1) < 2 ^ 64 := by
    change intOfZ (Bits.bits_of_b64 value.1) <
      intOfZ (Bits.Zpower Bits.Ztwo
        (Bits.Zadd (Bits.Zadd (ZArith.BinInt.Z.of_nat 52)
          (ZArith.BinInt.Z.of_nat 11)) Bits.Zone)) at hlt
    have hpow : intOfZ (Bits.Zpower Bits.Ztwo
        (Bits.Zadd (Bits.Zadd (ZArith.BinInt.Z.of_nat 52)
          (ZArith.BinInt.Z.of_nat 11)) Bits.Zone)) = 2 ^ 64 := by decide
    rw [hpow] at hlt
    exact hlt
  have hnatlt : ZArith.BinInt.Z.to_nat (Bits.bits_of_b64 value.1) < 2 ^ 64 := by
    change Int.toNat (intOfZ (Bits.bits_of_b64 value.1)) < 2 ^ 64
    exact (Int.toNat_lt hnonnegInt).mpr hltInt
  rw [Nat.mod_eq_of_lt hnatlt]
  rw [ZArith.Znat.Z2Nat.id (Bits.bits_of_b64 value.1) hnonneg]
  simpa [Bits.b64_of_bits_unchecked, Bits.binary_float_of_bits_unchecked,
    Bits.bits_of_b64, Bits.binary64] using hround

private theorem conversion_zadd_positive (n : Nat) (hn : 0 < n) :
    ∃ p : positive,
      Bits.Zadd (ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat n))
          (ZArith.BinInt.Z.of_nat 8388608) = ZArith.BinInt.Z.pos p := by
  have hpos : 0 < intOfZ
      (Bits.Zadd (ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat n))
        (ZArith.BinInt.Z.of_nat 8388608)) := by
    change 0 < intOfZ (ZArith.BinInt.Z.add
      (ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat n))
      (ZArith.BinInt.Z.of_nat 8388608))
    simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.pos,
      ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
    change 0 < (posToNat (PArith.BinPos.Pos.of_nat n) : Int) + 8388608
    have hnat : posToNat (PArith.BinPos.Pos.of_nat n) = n := by
      change posToNat (posOfNat n) = n
      exact posToNat_posOfNat hn
    rw [hnat]
    omega
  cases h : Bits.Zadd
      (ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat n))
      (ZArith.BinInt.Z.of_nat 8388608) with
  | Z0 =>
      rw [h] at hpos
      change (0 : Int) < 0 at hpos
      omega
  | Zpos p => exact ⟨p, by simpa only using h⟩
  | Zneg p =>
      rw [h] at hpos
      change 0 < -(posToNat p : Int) at hpos
      omega

private theorem conversion_isNaN32_decode (value : float32) :
    Binary.is_nan (decode32 value) = isNaN32 value := by
  unfold decode32 isNaN32 Binary.is_nan
  change Binary.is_nan
    (Bits.binary_float_of_bits_unchecked
      (ZArith.BinInt.Z.of_nat 23) (ZArith.BinInt.Z.of_nat 8) _ _ _
      (ZArith.BinInt.Z.of_nat value.bits.toNat)) = _
  have hdiv :
      Bits.Zdiv (ZArith.BinInt.Z.of_nat value.bits.toNat)
          (ZArith.BinInt.Z.of_nat (2 ^ 23)) =
        ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 23) :=
    zdiv_nat_f64 _ _ (by decide)
  have hmod :
      Bits.Zmod (ZArith.BinInt.Z.of_nat value.bits.toNat)
          (ZArith.BinInt.Z.of_nat (2 ^ 23)) =
        ZArith.BinInt.Z.of_nat (value.bits.toNat % 2 ^ 23) :=
    zmod_nat_f64 _ _ (by decide)
  have hmodexp :
      Bits.Zmod
          (ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 23))
          (ZArith.BinInt.Z.of_nat (2 ^ 8)) =
        ZArith.BinInt.Z.of_nat ((value.bits.toNat / 2 ^ 23) % 2 ^ 8) :=
    zmod_nat_f64 _ _ (by decide)
  unfold Bits.binary_float_of_bits_unchecked Bits.binary_float_of_bits_aux
  unfold Bits.split_bits
  simp only []
  rw [show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 23) =
      ZArith.BinInt.Z.of_nat (2 ^ 23) by decide,
    show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 8) =
      ZArith.BinInt.Z.of_nat (2 ^ 8) by decide,
    hdiv, hmod, hmodexp]
  simp only [exponent32, fraction32]
  let exponent : Nat := value.bits.toNat / 8388608 % 256
  let mantissa : Nat := value.bits.toNat % 8388608
  dsimp [exponent, mantissa] at *
  have hzeroEq : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat 0) Bits.Z0 = true := by decide
  have hzeroMax : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat 0)
      (Bits.Zsub (ZArith.BinInt.Z.of_nat 256) Bits.Zone) = false := by decide
  have h255Zero : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat 255) Bits.Z0 = false := by decide
  have h255Max : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat 255)
      (Bits.Zsub (ZArith.BinInt.Z.of_nat 256) Bits.Zone) = true := by decide
  have hsum0 : Bits.Zadd (ZArith.BinInt.Z.of_nat 0)
      (ZArith.BinInt.Z.of_nat 8388608) =
      ZArith.BinInt.Z.of_nat 8388608 := by decide
  have hsum0' : Bits.Zadd Bits.Z0
      (ZArith.BinInt.Z.of_nat 8388608) =
      ZArith.BinInt.Z.of_nat 8388608 := by decide
  have h8388608 : ZArith.BinInt.Z.of_nat 8388608 =
      ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat 8388608) := by decide
  have hsum0pos : Bits.Zadd Bits.Z0
      (ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat 8388608)) =
      ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat 8388608) := by decide
  have hzero : ZArith.BinInt.Z.of_nat 0 = Bits.Z0 := by decide
  have h00 : Bits.Zeq_bool Bits.Z0 Bits.Z0 = true := by decide
  have h0Max : Bits.Zeq_bool Bits.Z0
      (Bits.Zsub (ZArith.BinInt.Z.of_nat 256) Bits.Zone) = false := by decide
  by_cases he0 : exponent = 0
  · have hexp0 : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent) Bits.Z0 = true := by
      apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_true
      rw [he0]
      decide
    have hexp255 : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent)
        (Bits.Zsub (ZArith.BinInt.Z.of_nat 256) Bits.Zone) = false := by
      apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false
      intro h
      have hi := congrArg intOfZ h
      have hleft : intOfZ (ZArith.BinInt.Z.of_nat exponent) = (exponent : Int) := by
        change intOfZ (zOfInt (Int.ofNat exponent)) = Int.ofNat exponent
        exact intOfZ_zOfInt _
      have hright : intOfZ (Bits.Zsub (ZArith.BinInt.Z.of_nat 256) Bits.Zone) = 255 := by decide
      rw [hleft, hright] at hi
      omega
    by_cases hm0 : mantissa = 0
    · have hmant : ZArith.BinInt.Z.of_nat mantissa = Bits.Z0 := by
        rw [hm0]
        decide
      have hexp0' : Bits.Zeq_bool
          (ZArith.BinInt.Z.of_nat (value.bits.toNat / 8388608 % 256)) Bits.Z0 = true := by
        simpa [exponent, hzero] using hexp0
      have hexp255' : Bits.Zeq_bool
          (ZArith.BinInt.Z.of_nat (value.bits.toNat / 8388608 % 256))
          (Bits.Zsub (ZArith.BinInt.Z.of_nat 256) Bits.Zone) = false := by
        simpa [exponent] using hexp255
      have hmant' : ZArith.BinInt.Z.of_nat (value.bits.toNat % 8388608) = Bits.Z0 := by
        simpa [mantissa] using hmant
      simp [Binary.is_nan, Binary.FF2B_unchecked, exponent, mantissa, hzero,
        h00, h0Max, hzeroEq, hzeroMax, hexp0', hexp255', hmant', he0, hm0]
    · have hmpos : 0 < mantissa := Nat.pos_of_ne_zero hm0
      have hmz : ZArith.BinInt.Z.of_nat mantissa =
          ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat mantissa) := by
        apply intOfZ_injective
        simp only [ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.pos,
          intOfZ_zOfInt]
        exact congrArg Int.ofNat (posToNat_posOfNat hmpos).symm
      have hexp0' : Bits.Zeq_bool
          (ZArith.BinInt.Z.of_nat (value.bits.toNat / 8388608 % 256)) Bits.Z0 = true := by
        simpa [exponent] using hexp0
      have hexp255' : Bits.Zeq_bool
          (ZArith.BinInt.Z.of_nat (value.bits.toNat / 8388608 % 256))
          (Bits.Zsub (ZArith.BinInt.Z.of_nat 256) Bits.Zone) = false := by
        simpa [exponent] using hexp255
      have hmz' : ZArith.BinInt.Z.of_nat (value.bits.toNat % 8388608) =
          ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat (value.bits.toNat % 8388608)) := by
        simpa [mantissa] using hmz
      simp [Binary.is_nan, Binary.FF2B_unchecked, exponent, mantissa, hzero,
        h00, h0Max, hzeroEq, hzeroMax, hexp0', hexp255', hmz', he0, hm0]
  · by_cases he255 : exponent = 255
    · have hexp0 : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent) Bits.Z0 = false := by
        apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false
        intro h
        have hi := congrArg intOfZ h
        have hleft : intOfZ (ZArith.BinInt.Z.of_nat exponent) = (exponent : Int) := by
          change intOfZ (zOfInt (Int.ofNat exponent)) = Int.ofNat exponent
          exact intOfZ_zOfInt _
        have hright : intOfZ Bits.Z0 = 0 := by decide
        rw [hleft, hright] at hi
        omega
      have hexp255 : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent)
          (Bits.Zsub (ZArith.BinInt.Z.of_nat 256) Bits.Zone) = true := by
        apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_true
        apply intOfZ_injective
        have hright : intOfZ (Bits.Zsub (ZArith.BinInt.Z.of_nat 256) Bits.Zone) = 255 := by decide
        rw [hright]
        rw [he255]
        change intOfZ (zOfInt (Int.ofNat 255)) = (255 : Int)
        exact intOfZ_zOfInt _
      by_cases hm0 : mantissa = 0
      · have hmant : ZArith.BinInt.Z.of_nat mantissa = Bits.Z0 := by
          rw [hm0]
          decide
        simp [Binary.is_nan, Binary.FF2B_unchecked, exponent, mantissa, hzero,
          h255Zero, h255Max, hexp0, hexp255, hmant, he255, hm0]
      · have hmpos : 0 < mantissa := Nat.pos_of_ne_zero hm0
        have hmz : ZArith.BinInt.Z.of_nat mantissa =
            ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat mantissa) := by
          apply intOfZ_injective
          simp only [ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.pos,
            intOfZ_zOfInt]
          exact congrArg Int.ofNat (posToNat_posOfNat hmpos).symm
        have hmraw : value.bits.toNat % 8388608 ≠ 0 := by
          simpa [mantissa] using hm0
        simp [Binary.is_nan, Binary.FF2B_unchecked, exponent, mantissa, hzero,
          h255Zero, h255Max, hexp0, hexp255, hmz, he255, hm0, hmraw]
    · have hexp0 : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent) Bits.Z0 = false := by
        apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false
        intro h
        have hi := congrArg intOfZ h
        have hleft : intOfZ (ZArith.BinInt.Z.of_nat exponent) = (exponent : Int) := by
          change intOfZ (zOfInt (Int.ofNat exponent)) = Int.ofNat exponent
          exact intOfZ_zOfInt _
        have hright : intOfZ Bits.Z0 = 0 := by decide
        rw [hleft, hright] at hi
        omega
      have hexp255 : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent)
          (Bits.Zsub (ZArith.BinInt.Z.of_nat 256) Bits.Zone) = false := by
        apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false
        intro h
        have hi := congrArg intOfZ h
        have hleft : intOfZ (ZArith.BinInt.Z.of_nat exponent) = (exponent : Int) := by
          change intOfZ (zOfInt (Int.ofNat exponent)) = Int.ofNat exponent
          exact intOfZ_zOfInt _
        have hright : intOfZ (Bits.Zsub (ZArith.BinInt.Z.of_nat 256) Bits.Zone) = 255 := by decide
        rw [hleft, hright] at hi
        omega
      by_cases hm0 : mantissa = 0
      · have hmant : ZArith.BinInt.Z.of_nat mantissa = Bits.Z0 := by
          rw [hm0]
          decide
        simp [Binary.is_nan, Binary.FF2B_unchecked, exponent, mantissa, hzero,
          h00, h0Max, hsum0, hsum0', h8388608, hsum0pos, h255Zero, h255Max,
          hexp0, hexp255, hmant, he255, hm0]
      · have hmpos : 0 < mantissa := Nat.pos_of_ne_zero hm0
        have hmz : ZArith.BinInt.Z.of_nat mantissa =
            ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat mantissa) := by
          apply intOfZ_injective
          simp only [ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.pos,
            intOfZ_zOfInt]
          exact congrArg Int.ofNat (posToNat_posOfNat hmpos).symm
        obtain ⟨p, hp⟩ := conversion_zadd_positive mantissa hmpos
        simp [Binary.is_nan, Binary.FF2B_unchecked, exponent, mantissa, hzero,
          h00, h0Max, hp, h255Zero, h255Max, hexp0, hexp255, hmz, he255, hm0]

local instance conversion_binary32_certificate :
    Binary.BinaryNormalizeCertificate z24 z128 :=
  Binary.binary32_normalize_certificate_proof

local instance conversion_binary64_certificate :
    Binary.BinaryNormalizeCertificate z53 z1024 :=
  Binary.binary64_normalize_certificate_proof

private theorem conversion_model_zero (value : float32)
    (hfields : exponent32 value = 0 ∧ fraction32 value = 0)
    (hbit : BitVec.extractLsb 31 31 value.bits = 0#1) :
    decode64 (⟨
      Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
        (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary32 value.bits)⟩ : float) =
      Binary.B754_zero (sign32 value) := by
  have hexponent : BitVec.extractLsb 30 23 value.bits = 0#8 := by
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow,
      exponent32] using hfields.1
  have hmantissa : BitVec.extractLsb 22 0 value.bits = 0#23 := by
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.extractLsb_toNat, fraction32] using hfields.2
  have hsign32_eq : sign32 value =
      ((BitVec.extractLsb 31 31 value.bits).toNat == (1 : Nat)) := by
    simp [sign32, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]
  have hsign' : sign32 value = false := by
    rw [hsign32_eq, hbit]
    decide
  have hunpack : Float.Model.UnpackedFloat.unpack Float.Model.Format.binary32 value.bits =
      Float.Model.UnpackedFloat.zero
        (Float.Model.UnpackedFloat.Sign.ofBitVec (BitVec.extractLsb 31 31 value.bits)) := by
    simp only [BitVec.extractLsb] at hexponent hmantissa hbit ⊢
    simp [Float.Model.UnpackedFloat.unpack,
    Float.Model.UnpackedFloat.unpackExponent,
    Float.Model.UnpackedFloat.unpackMantissa,
    Float.Model.UnpackedFloat.unpackSign,
    hexponent, hmantissa, hbit]
  have hcert : Binary.BinaryFloatCertificate (prec := z53) (emax := z1024)
      (Binary.B754_zero (sign32 value)) := by
    simp [Binary.BinaryFloatCertificate, Binary.B2FF, Binary.valid_binary]
  have hround := conversion_encode64_decode
    (⟨Binary.B754_zero (sign32 value), hcert⟩ : Binary.CertifiedBinaryFloat z53 z1024)
  have hbits : (⟨Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
      (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary32 value.bits)⟩ : float) =
      encode64 (Binary.B754_zero (sign32 value)) := by
    rw [hunpack]
    apply float.ext
    apply BitVec.eq_of_toNat_eq
    simp [encode64, Float.Model.UnpackedFloat.pack,
    Float.Model.UnpackedFloat.packedZero,
    Float.Model.UnpackedFloat.packComponents,
    Float.Model.UnpackedFloat.Sign.ofBitVec,
    Float.Model.UnpackedFloat.Sign.toBitVec, hbit,
    Bits.bits_of_b64, Bits.bits_of_binary_float, Bits.join_bits, hsign']
    decide
  rw [hbits]
  exact hround

private theorem conversion_model_zero_neg (value : float32)
    (hfields : exponent32 value = 0 ∧ fraction32 value = 0)
    (hbit : BitVec.extractLsb 31 31 value.bits = 1#1) :
    decode64 (⟨
      Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
        (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary32 value.bits)⟩ : float) =
      Binary.B754_zero (sign32 value) := by
  have hexponent : BitVec.extractLsb 30 23 value.bits = 0#8 := by
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow,
      exponent32] using hfields.1
  have hmantissa : BitVec.extractLsb 22 0 value.bits = 0#23 := by
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.extractLsb_toNat, fraction32] using hfields.2
  have hsign32_eq : sign32 value =
      ((BitVec.extractLsb 31 31 value.bits).toNat == (1 : Nat)) := by
    simp [sign32, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]
  have hsign' : sign32 value = true := by
    rw [hsign32_eq, hbit]
    decide
  have hunpack : Float.Model.UnpackedFloat.unpack Float.Model.Format.binary32 value.bits =
      Float.Model.UnpackedFloat.zero
        (Float.Model.UnpackedFloat.Sign.ofBitVec (BitVec.extractLsb 31 31 value.bits)) := by
    simp only [BitVec.extractLsb] at hexponent hmantissa hbit ⊢
    simp [Float.Model.UnpackedFloat.unpack,
      Float.Model.UnpackedFloat.unpackExponent,
      Float.Model.UnpackedFloat.unpackMantissa,
      Float.Model.UnpackedFloat.unpackSign,
      hexponent, hmantissa, hbit]
  have hcert : Binary.BinaryFloatCertificate (prec := z53) (emax := z1024)
      (Binary.B754_zero (sign32 value)) := by
    simp [Binary.BinaryFloatCertificate, Binary.B2FF, Binary.valid_binary]
  have hround := conversion_encode64_decode
    (⟨Binary.B754_zero (sign32 value), hcert⟩ : Binary.CertifiedBinaryFloat z53 z1024)
  have hbits : (⟨Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
      (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary32 value.bits)⟩ : float) =
      encode64 (Binary.B754_zero (sign32 value)) := by
    rw [hunpack]
    apply float.ext
    apply BitVec.eq_of_toNat_eq
    simp [encode64, Float.Model.UnpackedFloat.pack,
      Float.Model.UnpackedFloat.packedZero,
      Float.Model.UnpackedFloat.packComponents,
      Float.Model.UnpackedFloat.Sign.ofBitVec,
      Float.Model.UnpackedFloat.Sign.toBitVec, hbit,
      Bits.bits_of_b64, Bits.bits_of_binary_float, Bits.join_bits, hsign']
    decide
  rw [hbits]
  exact hround

set_option maxRecDepth 100000 in
private theorem conversion_decode32_zero_sign (value : float32)
    (hfields : exponent32 value = 0 ∧ fraction32 value = 0) :
    Binary.Bsign (decode32 value) = sign32 value := by
  have hdiv :
      Bits.Zdiv (ZArith.BinInt.Z.of_nat value.bits.toNat)
          (ZArith.BinInt.Z.of_nat (2 ^ 23)) =
        ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 23) :=
    zdiv_nat_f64 _ _ (by decide)
  have hmod :
      Bits.Zmod (ZArith.BinInt.Z.of_nat value.bits.toNat)
          (ZArith.BinInt.Z.of_nat (2 ^ 23)) =
        ZArith.BinInt.Z.of_nat (value.bits.toNat % 2 ^ 23) :=
    zmod_nat_f64 _ _ (by decide)
  have hmodexp :
      Bits.Zmod
          (ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 23))
          (ZArith.BinInt.Z.of_nat (2 ^ 8)) =
        ZArith.BinInt.Z.of_nat ((value.bits.toNat / 2 ^ 23) % 2 ^ 8) :=
    zmod_nat_f64 _ _ (by decide)
  have hexpNat : value.bits.toNat / 2 ^ 23 % 2 ^ 8 = 0 := by
    simpa [exponent32] using hfields.1
  have hmantNat : value.bits.toNat % 2 ^ 23 = 0 := by
    simpa [fraction32] using hfields.2
  have hexp0 : Bits.Zeq_bool
      (ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 23 % 2 ^ 8)) Bits.Z0 = true := by
    rw [hexpNat]
    decide
  have hmant0 : ZArith.BinInt.Z.of_nat (value.bits.toNat % 2 ^ 23) = Bits.Z0 := by
    rw [hmantNat]
    decide
  have hsign32_eq : sign32 value =
      ((BitVec.extractLsb 31 31 value.bits).toNat == (1 : Nat)) := by
    simp [sign32, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]
  have hthreshold :
      Bits.Zle_bool
        (Bits.Zmul (ZArith.BinInt.Z.of_nat (2 ^ 23))
          (ZArith.BinInt.Z.of_nat (2 ^ 8)))
        (ZArith.BinInt.Z.of_nat value.bits.toNat) = sign32 value := by
    have hlt : value.bits.toNat < 2 ^ 32 := value.bits.isLt
    rcases BitVec.eq_zero_or_eq_one (BitVec.extractLsb 31 31 value.bits) with hbit | hbit
    · have hq : value.bits.toNat / 2 ^ 31 % 2 = 0 := by
        have hh := congrArg BitVec.toNat hbit
        simpa [BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow] using hh
      have hn : value.bits.toNat < 2 ^ 31 := by omega
      have hfalse : Bits.Zle_bool
          (Bits.Zmul (ZArith.BinInt.Z.of_nat (2 ^ 23))
            (ZArith.BinInt.Z.of_nat (2 ^ 8)))
          (ZArith.BinInt.Z.of_nat value.bits.toNat) = false := by
        have hprod : Bits.Zmul (ZArith.BinInt.Z.of_nat (2 ^ 23))
            (ZArith.BinInt.Z.of_nat (2 ^ 8)) =
            ZArith.BinInt.Z.of_nat (2 ^ 31) := by decide
        rw [hprod]
        apply CompCert4Lean.Flocq.Core.Zaux.Zle_bool_false
        change intOfZ (ZArith.BinInt.Z.of_nat value.bits.toNat) <
          intOfZ (ZArith.BinInt.Z.of_nat (2 ^ 31))
        simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
        exact Int.ofNat_lt.mpr hn
      rw [hfalse]
      rw [hsign32_eq, hbit]
      decide
    · have hq : value.bits.toNat / 2 ^ 31 % 2 = 1 := by
        have hh := congrArg BitVec.toNat hbit
        simpa [BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow] using hh
      have hn : 2 ^ 31 ≤ value.bits.toNat := by omega
      have htrue : Bits.Zle_bool
          (Bits.Zmul (ZArith.BinInt.Z.of_nat (2 ^ 23))
            (ZArith.BinInt.Z.of_nat (2 ^ 8)))
          (ZArith.BinInt.Z.of_nat value.bits.toNat) = true := by
        have hprod : Bits.Zmul (ZArith.BinInt.Z.of_nat (2 ^ 23))
            (ZArith.BinInt.Z.of_nat (2 ^ 8)) =
            ZArith.BinInt.Z.of_nat (2 ^ 31) := by decide
        rw [hprod]
        apply CompCert4Lean.Flocq.Core.Zaux.Zle_bool_true
        change intOfZ (ZArith.BinInt.Z.of_nat (2 ^ 31)) ≤
          intOfZ (ZArith.BinInt.Z.of_nat value.bits.toNat)
        simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
        exact Int.ofNat_le.mpr hn
      rw [htrue]
      rw [hsign32_eq, hbit]
      decide
  unfold Binary.Bsign decode32
  unfold Bits.b32_of_bits_unchecked Bits.binary_float_of_bits_unchecked
    Bits.binary_float_of_bits_aux Bits.split_bits
  simp only []
  rw [show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 23) =
        ZArith.BinInt.Z.of_nat (2 ^ 23) by decide,
    show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 8) =
        ZArith.BinInt.Z.of_nat (2 ^ 8) by decide,
    hdiv, hmod, hmodexp]
  simp [Binary.FF2B_unchecked, hexp0, hmant0, hthreshold,
    Binary.Bsign]

set_option maxRecDepth 100000 in
private theorem conversion_decode32_infinity_sign (value : float32)
    (hfields : exponent32 value = 2 ^ 8 - 1 ∧ fraction32 value = 0) :
    Binary.Bsign (decode32 value) = sign32 value := by
  have hdiv :
      Bits.Zdiv (ZArith.BinInt.Z.of_nat value.bits.toNat)
          (ZArith.BinInt.Z.of_nat (2 ^ 23)) =
        ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 23) :=
    zdiv_nat_f64 _ _ (by decide)
  have hmod :
      Bits.Zmod (ZArith.BinInt.Z.of_nat value.bits.toNat)
          (ZArith.BinInt.Z.of_nat (2 ^ 23)) =
        ZArith.BinInt.Z.of_nat (value.bits.toNat % 2 ^ 23) :=
    zmod_nat_f64 _ _ (by decide)
  have hmodexp :
      Bits.Zmod
          (ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 23))
          (ZArith.BinInt.Z.of_nat (2 ^ 8)) =
        ZArith.BinInt.Z.of_nat ((value.bits.toNat / 2 ^ 23) % 2 ^ 8) :=
    zmod_nat_f64 _ _ (by decide)
  have hexpNat : value.bits.toNat / 2 ^ 23 % 2 ^ 8 = 2 ^ 8 - 1 := by
    simpa [exponent32] using hfields.1
  have hmantNat : value.bits.toNat % 2 ^ 23 = 0 := by
    simpa [fraction32] using hfields.2
  have hexp0 : Bits.Zeq_bool
      (ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 23 % 2 ^ 8)) Bits.Z0 = false := by
    rw [hexpNat]
    decide
  have hmax : Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 8)) Bits.Zone =
      ZArith.BinInt.Z.of_nat (2 ^ 8 - 1) := by decide
  have hexpmax : Bits.Zeq_bool
      (ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 23 % 2 ^ 8))
      (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 8)) Bits.Zone) = true := by
    rw [hexpNat, hmax]
    decide
  have hmant0 : ZArith.BinInt.Z.of_nat (value.bits.toNat % 2 ^ 23) = Bits.Z0 := by
    rw [hmantNat]
    decide
  have hsign32_eq : sign32 value =
      ((BitVec.extractLsb 31 31 value.bits).toNat == (1 : Nat)) := by
    simp [sign32, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]
  have hthreshold :
      Bits.Zle_bool
        (Bits.Zmul (ZArith.BinInt.Z.of_nat (2 ^ 23))
          (ZArith.BinInt.Z.of_nat (2 ^ 8)))
        (ZArith.BinInt.Z.of_nat value.bits.toNat) = sign32 value := by
    have hlt : value.bits.toNat < 2 ^ 32 := value.bits.isLt
    rcases BitVec.eq_zero_or_eq_one (BitVec.extractLsb 31 31 value.bits) with hbit | hbit
    · have hq : value.bits.toNat / 2 ^ 31 % 2 = 0 := by
        have hh := congrArg BitVec.toNat hbit
        simpa [BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow] using hh
      have hn : value.bits.toNat < 2 ^ 31 := by omega
      have hfalse : Bits.Zle_bool
          (Bits.Zmul (ZArith.BinInt.Z.of_nat (2 ^ 23))
            (ZArith.BinInt.Z.of_nat (2 ^ 8)))
          (ZArith.BinInt.Z.of_nat value.bits.toNat) = false := by
        have hprod : Bits.Zmul (ZArith.BinInt.Z.of_nat (2 ^ 23))
            (ZArith.BinInt.Z.of_nat (2 ^ 8)) =
            ZArith.BinInt.Z.of_nat (2 ^ 31) := by decide
        rw [hprod]
        apply CompCert4Lean.Flocq.Core.Zaux.Zle_bool_false
        change intOfZ (ZArith.BinInt.Z.of_nat value.bits.toNat) <
          intOfZ (ZArith.BinInt.Z.of_nat (2 ^ 31))
        simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
        exact Int.ofNat_lt.mpr hn
      rw [hfalse, hsign32_eq, hbit]
      decide
    · have hq : value.bits.toNat / 2 ^ 31 % 2 = 1 := by
        have hh := congrArg BitVec.toNat hbit
        simpa [BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow] using hh
      have hn : 2 ^ 31 ≤ value.bits.toNat := by omega
      have htrue : Bits.Zle_bool
          (Bits.Zmul (ZArith.BinInt.Z.of_nat (2 ^ 23))
            (ZArith.BinInt.Z.of_nat (2 ^ 8)))
          (ZArith.BinInt.Z.of_nat value.bits.toNat) = true := by
        have hprod : Bits.Zmul (ZArith.BinInt.Z.of_nat (2 ^ 23))
            (ZArith.BinInt.Z.of_nat (2 ^ 8)) =
            ZArith.BinInt.Z.of_nat (2 ^ 31) := by decide
        rw [hprod]
        apply CompCert4Lean.Flocq.Core.Zaux.Zle_bool_true
        change intOfZ (ZArith.BinInt.Z.of_nat (2 ^ 31)) ≤
          intOfZ (ZArith.BinInt.Z.of_nat value.bits.toNat)
        simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
        exact Int.ofNat_le.mpr hn
      rw [htrue, hsign32_eq, hbit]
      decide
  unfold Binary.Bsign decode32
  unfold Bits.b32_of_bits_unchecked Bits.binary_float_of_bits_unchecked
    Bits.binary_float_of_bits_aux Bits.split_bits
  simp only []
  rw [show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 23) =
        ZArith.BinInt.Z.of_nat (2 ^ 23) by decide,
    show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 8) =
        ZArith.BinInt.Z.of_nat (2 ^ 8) by decide,
    hdiv, hmod, hmodexp]
  simp [Binary.FF2B_unchecked, hexp0, hexpmax, hmant0, hthreshold,
    Binary.Bsign]

private theorem conversion_model_infinity (value : float32)
    (hfields : exponent32 value = 2 ^ 8 - 1 ∧ fraction32 value = 0)
    (hbit : BitVec.extractLsb 31 31 value.bits = 0#1 ∨
      BitVec.extractLsb 31 31 value.bits = 1#1) :
    decode64 (⟨
      Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
        (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary32 value.bits)⟩ : float) =
      Binary.B754_infinity (sign32 value) := by
  have hexponent : BitVec.extractLsb 30 23 value.bits = (255#8) := by
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow,
      exponent32] using hfields.1
  have hmantissa : BitVec.extractLsb 22 0 value.bits = 0#23 := by
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.extractLsb_toNat, fraction32] using hfields.2
  have hsign32_eq : sign32 value =
      ((BitVec.extractLsb 31 31 value.bits).toNat == (1 : Nat)) := by
    simp [sign32, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]
  have hunpack : Float.Model.UnpackedFloat.unpack Float.Model.Format.binary32 value.bits =
      Float.Model.UnpackedFloat.infinity
        (Float.Model.UnpackedFloat.Sign.ofBitVec (BitVec.extractLsb 31 31 value.bits)) := by
    simp only [BitVec.extractLsb] at hexponent hmantissa hbit ⊢
    simp [Float.Model.UnpackedFloat.unpack,
      Float.Model.UnpackedFloat.unpackExponent,
      Float.Model.UnpackedFloat.unpackMantissa,
      Float.Model.UnpackedFloat.unpackSign,
      hexponent, hmantissa, hbit]
  have hcert : Binary.BinaryFloatCertificate (prec := z53) (emax := z1024)
      (Binary.B754_infinity (sign32 value)) := by
    simp [Binary.BinaryFloatCertificate, Binary.B2FF, Binary.valid_binary]
  have hround := conversion_encode64_decode
    (⟨Binary.B754_infinity (sign32 value), hcert⟩ : Binary.CertifiedBinaryFloat z53 z1024)
  have hbits : (⟨Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
      (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary32 value.bits)⟩ : float) =
      encode64 (Binary.B754_infinity (sign32 value)) := by
    rw [hunpack]
    apply float.ext
    apply BitVec.eq_of_toNat_eq
    rcases hbit with hbit | hbit
    · simp [encode64, Float.Model.UnpackedFloat.pack,
        Float.Model.UnpackedFloat.packedInfinity,
        Float.Model.UnpackedFloat.packComponents,
        Float.Model.UnpackedFloat.Sign.ofBitVec,
        Float.Model.UnpackedFloat.Sign.toBitVec, hbit,
        Bits.bits_of_b64, Bits.bits_of_binary_float, Bits.join_bits, hsign32_eq]
      decide
    · simp [encode64, Float.Model.UnpackedFloat.pack,
        Float.Model.UnpackedFloat.packedInfinity,
        Float.Model.UnpackedFloat.packComponents,
        Float.Model.UnpackedFloat.Sign.ofBitVec,
        Float.Model.UnpackedFloat.Sign.toBitVec, hbit,
        Bits.bits_of_b64, Bits.bits_of_binary_float, Bits.join_bits, hsign32_eq]
      decide
  rw [hbits]
  exact hround
set_option maxRecDepth 100000 in
private theorem conversion_of_single_bconv
    (value : float32)
    (conv_nan : Bits.binary32 →
      IEEE754_extra.NaNResult z53 z1024)
    (hnotnan : Binary.is_nan (decode32 value) = false) :
    decode64 (Float.of_single value) =
      IEEE754_extra.Bconv conv_nan BinarySingleNaN.mode_NE (decode32 value) := by
  have hnan : isNaN32 value = false := by
    rw [← conversion_isNaN32_decode value]
    exact hnotnan
  cases hvalue : decode32 value with
  | B754_zero sign =>
      have hvalue0 := hvalue
      have hfields : exponent32 value = 0 ∧ fraction32 value = 0 := by
        have hdiv :
            Bits.Zdiv (ZArith.BinInt.Z.of_nat value.bits.toNat)
                (ZArith.BinInt.Z.of_nat (2 ^ 23)) =
              ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 23) :=
          zdiv_nat_f64 _ _ (by decide)
        have hmod :
            Bits.Zmod (ZArith.BinInt.Z.of_nat value.bits.toNat)
                (ZArith.BinInt.Z.of_nat (2 ^ 23)) =
              ZArith.BinInt.Z.of_nat (value.bits.toNat % 2 ^ 23) :=
          zmod_nat_f64 _ _ (by decide)
        have hmodexp :
            Bits.Zmod
                (ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 23))
                (ZArith.BinInt.Z.of_nat (2 ^ 8)) =
              ZArith.BinInt.Z.of_nat ((value.bits.toNat / 2 ^ 23) % 2 ^ 8) :=
          zmod_nat_f64 _ _ (by decide)
        have hraw := hvalue
        unfold decode32 at hraw
        unfold Bits.b32_of_bits_unchecked Bits.binary_float_of_bits_unchecked
          Bits.binary_float_of_bits_aux Bits.split_bits at hraw
        simp only [] at hraw
        rw [show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 23) =
              ZArith.BinInt.Z.of_nat (2 ^ 23) by decide,
          show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 8) =
              ZArith.BinInt.Z.of_nat (2 ^ 8) by decide,
          hdiv, hmod, hmodexp] at hraw
        let exponent := value.bits.toNat / 8388608 % 256
        let mantissa := value.bits.toNat % 8388608
        have hzero : ZArith.BinInt.Z.of_nat 0 = Bits.Z0 := by decide
        have zeq_true {a b : Nat} (h : a = b) :
            Bits.Zeq_bool (ZArith.BinInt.Z.of_nat a)
              (ZArith.BinInt.Z.of_nat b) = true := by
          apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_true
          simpa [h]
        have zeq_false {a b : Nat} (h : a ≠ b) :
            Bits.Zeq_bool (ZArith.BinInt.Z.of_nat a)
              (ZArith.BinInt.Z.of_nat b) = false := by
          apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false
          intro hab
          have hi := congrArg intOfZ hab
          simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hi
          exact h (Int.ofNat_inj.mp hi)
        by_cases he0 : exponent = 0
        · by_cases hm0 : mantissa = 0
          · exact ⟨he0, hm0⟩
          · have hmpos : 0 < mantissa := Nat.pos_of_ne_zero hm0
            have hmz : ZArith.BinInt.Z.of_nat mantissa =
                ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat mantissa) := by
              apply intOfZ_injective
              simp only [ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.pos,
                intOfZ_zOfInt]
              exact congrArg Int.ofNat (posToNat_posOfNat hmpos).symm
            have hexp0 : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent) Bits.Z0 = true :=
              zeq_true he0
            have hexpMax : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent)
                (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 8)) Bits.Zone) = false := by
              apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false
              intro h
              have hi := congrArg intOfZ h
              have hleft : intOfZ (ZArith.BinInt.Z.of_nat exponent) =
                  (exponent : Int) := by
                simp [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
              have hright : intOfZ
                  (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 8)) Bits.Zone) = 255 := by decide
              rw [hleft, hright] at hi
              omega
            simp [Binary.FF2B_unchecked, exponent, mantissa, hexp0, hexpMax, hmz, he0, hm0] at hraw
            cases hraw
        · have hexp0 : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent) Bits.Z0 = false :=
              zeq_false he0
          by_cases heMax : exponent = 2 ^ 8 - 1
          · by_cases hm0 : mantissa = 0
            · have hmz : ZArith.BinInt.Z.of_nat mantissa = Bits.Z0 := by
                rw [hm0]
                decide
              have hexpMax : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent)
                  (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 8)) Bits.Zone) = true := by
                apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_true
                simpa [heMax] using (show ZArith.BinInt.Z.of_nat (2 ^ 8 - 1) =
                  Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 8)) Bits.Zone by decide)
              simp [Binary.FF2B_unchecked, exponent, mantissa, hexp0, hexpMax, hmz, heMax, hm0] at hraw
              cases hraw
            · have hmpos : 0 < mantissa := Nat.pos_of_ne_zero hm0
              have hmz : ZArith.BinInt.Z.of_nat mantissa =
                  ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat mantissa) := by
                apply intOfZ_injective
                simp only [ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.pos,
                  intOfZ_zOfInt]
                exact congrArg Int.ofNat (posToNat_posOfNat hmpos).symm
              have hexpMax : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent)
                  (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 8)) Bits.Zone) = true := by
                apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_true
                simpa [heMax] using (show ZArith.BinInt.Z.of_nat (2 ^ 8 - 1) =
                  Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 8)) Bits.Zone by decide)
              simp [Binary.FF2B_unchecked, exponent, mantissa, hexp0, hexpMax, hmz, heMax, hm0] at hraw
              cases hraw
          · have hexpMax : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent)
                (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 8)) Bits.Zone) = false := by
              apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false
              intro h
              have hi := congrArg intOfZ h
              have hleft : intOfZ (ZArith.BinInt.Z.of_nat exponent) =
                  (exponent : Int) := by
                simp [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
              have hright : intOfZ
                  (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 8)) Bits.Zone) = 255 := by decide
              rw [hleft, hright] at hi
              omega
            simp [Binary.FF2B_unchecked, exponent, mantissa, hexp0, hexpMax, heMax] at hraw
            cases hsum : Bits.Zadd
                (ZArith.BinInt.Z.of_nat (value.bits.toNat % 8388608))
                (ZArith.BinInt.Z.of_nat 8388608) <;>
              simp [hsum] at hraw
      have hsign32_eq : sign32 value =
          ((BitVec.extractLsb 31 31 value.bits).toNat == (1 : Nat)) := by
        simp [sign32, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]
      rcases BitVec.eq_zero_or_eq_one (BitVec.extractLsb 31 31 value.bits) with hbit | hbit
      · have hz := conversion_model_zero value hfields hbit
        have hsignraw := congrArg Binary.Bsign hvalue0
        have hdecode_sign := conversion_decode32_zero_sign value hfields
        have hsignraw' : Binary.Bsign (decode32 value) = sign := by
          simpa [Binary.Bsign] using hsignraw
        have hsign : sign32 value = sign := by
          exact hdecode_sign.symm.trans hsignraw'
        simp only [Float.of_single, hnan, hvalue0, Bool.false_eq_true, ↓reduceIte]
        simp only [IEEE754_extra.Bconv]
        rw [hsign] at hz
        exact hz
      · have hz := conversion_model_zero_neg value hfields hbit
        have hsignraw := congrArg Binary.Bsign hvalue0
        have hdecode_sign := conversion_decode32_zero_sign value hfields
        have hsignraw' : Binary.Bsign (decode32 value) = sign := by
          simpa [Binary.Bsign] using hsignraw
        have hsign : sign32 value = sign := by
          exact hdecode_sign.symm.trans hsignraw'
        simp only [Float.of_single, hnan, hvalue0, Bool.false_eq_true, ↓reduceIte]
        simp only [IEEE754_extra.Bconv]
        rw [hsign] at hz
        exact hz
  | B754_infinity sign =>
      have hvalue0 := hvalue
      have hfields : exponent32 value = 2 ^ 8 - 1 ∧ fraction32 value = 0 := by
        have hdiv :
            Bits.Zdiv (ZArith.BinInt.Z.of_nat value.bits.toNat)
                (ZArith.BinInt.Z.of_nat (2 ^ 23)) =
              ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 23) :=
          zdiv_nat_f64 _ _ (by decide)
        have hmod :
            Bits.Zmod (ZArith.BinInt.Z.of_nat value.bits.toNat)
                (ZArith.BinInt.Z.of_nat (2 ^ 23)) =
              ZArith.BinInt.Z.of_nat (value.bits.toNat % 2 ^ 23) :=
          zmod_nat_f64 _ _ (by decide)
        have hmodexp :
            Bits.Zmod
                (ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 23))
                (ZArith.BinInt.Z.of_nat (2 ^ 8)) =
              ZArith.BinInt.Z.of_nat ((value.bits.toNat / 2 ^ 23) % 2 ^ 8) :=
          zmod_nat_f64 _ _ (by decide)
        have hraw := hvalue
        unfold decode32 at hraw
        unfold Bits.b32_of_bits_unchecked Bits.binary_float_of_bits_unchecked
          Bits.binary_float_of_bits_aux Bits.split_bits at hraw
        simp only [] at hraw
        rw [show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 23) =
              ZArith.BinInt.Z.of_nat (2 ^ 23) by decide,
          show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 8) =
              ZArith.BinInt.Z.of_nat (2 ^ 8) by decide,
          hdiv, hmod, hmodexp] at hraw
        have hzero : ZArith.BinInt.Z.of_nat 0 = Bits.Z0 := by decide
        have hmax : Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 8)) Bits.Zone =
            ZArith.BinInt.Z.of_nat (2 ^ 8 - 1) := by decide
        let exponent := value.bits.toNat / 8388608 % 256
        let mantissa := value.bits.toNat % 8388608
        have zeq_true {a b : Nat} (h : a = b) :
            Bits.Zeq_bool (ZArith.BinInt.Z.of_nat a)
              (ZArith.BinInt.Z.of_nat b) = true := by
          apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_true
          simpa [h]
        have zeq_false {a b : Nat} (h : a ≠ b) :
            Bits.Zeq_bool (ZArith.BinInt.Z.of_nat a)
              (ZArith.BinInt.Z.of_nat b) = false := by
          apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false
          intro hab
          have hi := congrArg intOfZ hab
          simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hi
          exact h (Int.ofNat_inj.mp hi)
        have hmax_nat : 255 = 2 ^ 8 - 1 := by decide
        by_cases he0 : exponent = 0
        · have hexp0 := zeq_true he0
          have hexpmax : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent)
              (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 8)) Bits.Zone) = false := by
            rw [hmax]
            exact zeq_false (by omega)
          have hexpmaxraw : Bits.Zeq_bool
              (ZArith.BinInt.Z.of_nat (value.bits.toNat / 8388608 % 256))
              (ZArith.BinInt.Z.of_nat 255) = false := by
            simpa [exponent] using (show Bits.Zeq_bool
              (ZArith.BinInt.Z.of_nat exponent) (ZArith.BinInt.Z.of_nat 255) = false by
              exact zeq_false (by omega))
          by_cases hm0 : mantissa = 0
          · have hmant := zeq_true hm0
            simp [Binary.FF2B_unchecked, exponent, mantissa, hzero, hmax,
              hexp0, hexpmax, hexpmaxraw, hmant, he0, hm0] at hraw
            cases hraw
          · have hmpos : 0 < mantissa := Nat.pos_of_ne_zero hm0
            have hmz : ZArith.BinInt.Z.of_nat mantissa =
                ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat mantissa) := by
              apply intOfZ_injective
              simp only [ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.pos, intOfZ_zOfInt]
              exact congrArg Int.ofNat (posToNat_posOfNat hmpos).symm
            have hmant := zeq_false hm0
            simp [Binary.FF2B_unchecked, exponent, mantissa, hzero, hmax,
              hexp0, hexpmax, hmant, hmz, he0, hm0] at hraw
            cases hraw
        · have hexp0 := zeq_false he0
          by_cases hemax : exponent = 2 ^ 8 - 1
          · have hexpmax : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent)
                (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 8)) Bits.Zone) = true := by
              apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_true
              simpa [hemax] using (show ZArith.BinInt.Z.of_nat (2 ^ 8 - 1) =
                Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 8)) Bits.Zone by decide)
            have hexpmaxraw : Bits.Zeq_bool
                (ZArith.BinInt.Z.of_nat (value.bits.toNat / 8388608 % 256))
                (ZArith.BinInt.Z.of_nat 255) = true := by
              simpa [exponent] using (show Bits.Zeq_bool
                (ZArith.BinInt.Z.of_nat exponent) (ZArith.BinInt.Z.of_nat 255) = true by
                exact zeq_true hemax)
            by_cases hm0 : mantissa = 0
            · constructor
              · simpa [exponent32, exponent] using hemax
              · simpa [fraction32, mantissa] using hm0
            · have hmpos : 0 < mantissa := Nat.pos_of_ne_zero hm0
              have hmz : ZArith.BinInt.Z.of_nat mantissa =
                  ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat mantissa) := by
                apply intOfZ_injective
                simp only [ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.pos, intOfZ_zOfInt]
                exact congrArg Int.ofNat (posToNat_posOfNat hmpos).symm
              have hmant := zeq_false hm0
              simp [Binary.FF2B_unchecked, exponent, mantissa, hzero, hmax,
                hexp0, hexpmax, hexpmaxraw, hmz, hemax, hm0, hmant] at hraw
              cases hraw
          · have hexpmax : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent)
                (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 8)) Bits.Zone) = false := by
              apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false
              intro h
              have hi := congrArg intOfZ h
              have hleft : intOfZ (ZArith.BinInt.Z.of_nat exponent) =
                  (exponent : Int) := by
                simp [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
              have hright : intOfZ
                  (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 8)) Bits.Zone) = 255 := by decide
              rw [hleft, hright] at hi
              omega
            by_cases hm0 : mantissa = 0
            · have hmz : ZArith.BinInt.Z.of_nat mantissa = Bits.Z0 := by
                rw [hm0]
                decide
              have hexp0raw : Bits.Zeq_bool
                  (ZArith.BinInt.Z.of_nat (value.bits.toNat / 8388608 % 256)) Bits.Z0 = false := by
                simpa [exponent, hzero] using hexp0
              have hexpmaxraw : Bits.Zeq_bool
                  (ZArith.BinInt.Z.of_nat (value.bits.toNat / 8388608 % 256))
                  (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 8)) Bits.Zone) = false := by
                simpa [exponent, hmax] using hexpmax
              have hexpmaxraw255 : Bits.Zeq_bool
                  (ZArith.BinInt.Z.of_nat (value.bits.toNat / 8388608 % 256))
                  (ZArith.BinInt.Z.of_nat 255) = false := by
                simpa [exponent] using (show Bits.Zeq_bool
                  (ZArith.BinInt.Z.of_nat exponent) (ZArith.BinInt.Z.of_nat 255) = false by
                  exact zeq_false (by omega))
              have hsum0 : Bits.Zadd Bits.Z0 (ZArith.BinInt.Z.of_nat 8388608) =
                  ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat 8388608) := by decide
              simp [Binary.FF2B_unchecked, mantissa, hm0, hzero, hmax, hexp0raw, hexpmaxraw,
                hexpmaxraw255,
                hmz, hsum0] at hraw
            · have hmpos : 0 < mantissa := Nat.pos_of_ne_zero hm0
              have hmz : ZArith.BinInt.Z.of_nat mantissa =
                  ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat mantissa) := by
                apply intOfZ_injective
                simp only [ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.pos, intOfZ_zOfInt]
                exact congrArg Int.ofNat (posToNat_posOfNat hmpos).symm
              have hexp0raw : Bits.Zeq_bool
                  (ZArith.BinInt.Z.of_nat (value.bits.toNat / 8388608 % 256)) Bits.Z0 = false := by
                simpa [exponent, hzero] using hexp0
              have hexpmaxraw : Bits.Zeq_bool
                  (ZArith.BinInt.Z.of_nat (value.bits.toNat / 8388608 % 256))
                  (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 8)) Bits.Zone) = false := by
                simpa [exponent, hmax] using hexpmax
              have hexpmaxraw255 : Bits.Zeq_bool
                  (ZArith.BinInt.Z.of_nat (value.bits.toNat / 8388608 % 256))
                  (ZArith.BinInt.Z.of_nat 255) = false := by
                simpa [exponent] using (show Bits.Zeq_bool
                  (ZArith.BinInt.Z.of_nat exponent) (ZArith.BinInt.Z.of_nat 255) = false by
                  exact zeq_false (by omega))
              cases hsum : Bits.Zadd
                  (ZArith.BinInt.Z.of_nat (value.bits.toNat % 8388608))
                  (ZArith.BinInt.Z.of_nat 8388608) <;>
                simp [Binary.FF2B_unchecked, hzero, hmax,
                  hexp0raw, hexpmaxraw, hexpmaxraw255, hmz, hsum] at hraw <;>
                cases hraw
      have hbit : BitVec.extractLsb 31 31 value.bits = 0#1 ∨
          BitVec.extractLsb 31 31 value.bits = 1#1 :=
        BitVec.eq_zero_or_eq_one _
      have hz := conversion_model_infinity value hfields hbit
      have hsignraw := congrArg Binary.Bsign hvalue0
      have hdecode_sign := conversion_decode32_infinity_sign value hfields
      have hsignraw' : Binary.Bsign (decode32 value) = sign := by
        simpa [Binary.Bsign] using hsignraw
      have hsign : sign32 value = sign := by
        exact hdecode_sign.symm.trans hsignraw'
      simp only [Float.of_single, hnan, hvalue0, Bool.false_eq_true, ↓reduceIte]
      simp only [IEEE754_extra.Bconv]
      rw [hsign] at hz
      exact hz
  | B754_nan sign payload =>
      rw [hvalue] at hnotnan
      simp [Binary.is_nan] at hnotnan
  | B754_finite sign mantissa exponent =>
      simp only [Float.of_single, hnan, hvalue, Bool.false_eq_true, ↓reduceIte]
      have hnorm := Binary.binary_normalize_result_obligation_proof
        (prec := z53) (emax := z1024) BinarySingleNaN.mode_NE
        (CompCert4Lean.Flocq.Core.Zaux.cond_Zopp sign (.Zpos mantissa)) exponent sign
      have hround := conversion_encode64_decode
        (⟨Binary.binary_normalize BinarySingleNaN.mode_NE
          (CompCert4Lean.Flocq.Core.Zaux.cond_Zopp sign (.Zpos mantissa)) exponent sign,
          hnorm⟩ : Binary.CertifiedBinaryFloat z53 z1024)
      simpa [IEEE754_extra.Bconv] using hround

private theorem conversion_zeq_nat_true {a b : Nat} (h : a = b) :
    Bits.Zeq_bool (ZArith.BinInt.Z.of_nat a)
      (ZArith.BinInt.Z.of_nat b) = true := by
  rw [h]
  exact CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_true _ _ rfl

private theorem conversion_zeq_nat_false {a b : Nat} (h : a ≠ b) :
    Bits.Zeq_bool (ZArith.BinInt.Z.of_nat a)
      (ZArith.BinInt.Z.of_nat b) = false := by
  apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false
  intro hab
  have hi := congrArg intOfZ hab
  simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hi
  exact h (Int.ofNat_inj.mp hi)

private theorem conversion_zadd64_positive (n : Nat) (hn : 0 < n) :
    ∃ p : positive,
      Bits.Zadd (ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat n))
          (ZArith.BinInt.Z.of_nat 4503599627370496) = ZArith.BinInt.Z.pos p := by
  have hpos : 0 < intOfZ
      (Bits.Zadd (ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat n))
        (ZArith.BinInt.Z.of_nat 4503599627370496)) := by
    change 0 < intOfZ (ZArith.BinInt.Z.add
      (ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat n))
      (ZArith.BinInt.Z.of_nat 4503599627370496))
    simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.pos,
      ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
    change 0 < (posToNat (PArith.BinPos.Pos.of_nat n) : Int) + 4503599627370496
    have hnat : posToNat (PArith.BinPos.Pos.of_nat n) = n := by
      change posToNat (posOfNat n) = n
      exact posToNat_posOfNat hn
    rw [hnat]
    omega
  cases h : Bits.Zadd
      (ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat n))
      (ZArith.BinInt.Z.of_nat 4503599627370496) with
  | Z0 =>
      rw [h] at hpos
      change (0 : Int) < 0 at hpos
      omega
  | Zpos p => exact ⟨p, by simpa only using h⟩
  | Zneg p =>
      rw [h] at hpos
      change 0 < -(posToNat p : Int) at hpos
      omega

private theorem conversion_isNaN64_decode (value : float) :
    Binary.is_nan (decode64 value) = isNaN64 value := by
  unfold decode64 isNaN64 Binary.is_nan
  change Binary.is_nan
    (Bits.binary_float_of_bits_unchecked
      (ZArith.BinInt.Z.of_nat 52) (ZArith.BinInt.Z.of_nat 11) _ _ _
      (ZArith.BinInt.Z.of_nat value.bits.toNat)) = _
  have hdiv :
      Bits.Zdiv (ZArith.BinInt.Z.of_nat value.bits.toNat)
          (ZArith.BinInt.Z.of_nat (2 ^ 52)) =
        ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 52) :=
    zdiv_nat_f64 _ _ (by decide)
  have hmod :
      Bits.Zmod (ZArith.BinInt.Z.of_nat value.bits.toNat)
          (ZArith.BinInt.Z.of_nat (2 ^ 52)) =
        ZArith.BinInt.Z.of_nat (value.bits.toNat % 2 ^ 52) :=
    zmod_nat_f64 _ _ (by decide)
  have hmodexp :
      Bits.Zmod
          (ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 52))
          (ZArith.BinInt.Z.of_nat (2 ^ 11)) =
        ZArith.BinInt.Z.of_nat ((value.bits.toNat / 2 ^ 52) % 2 ^ 11) :=
    zmod_nat_f64 _ _ (by decide)
  unfold Bits.binary_float_of_bits_unchecked Bits.binary_float_of_bits_aux
  unfold Bits.split_bits
  simp only []
  rw [show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 52) =
      ZArith.BinInt.Z.of_nat (2 ^ 52) by decide,
    show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 11) =
      ZArith.BinInt.Z.of_nat (2 ^ 11) by decide,
    hdiv, hmod, hmodexp]
  simp only [exponent64, fraction64]
  let exponent : Nat := value.bits.toNat / 4503599627370496 % 2048
  let mantissa : Nat := value.bits.toNat % 4503599627370496
  dsimp [exponent, mantissa] at *
  have hmaxz : Bits.Zsub (ZArith.BinInt.Z.of_nat 2048) Bits.Zone =
      ZArith.BinInt.Z.of_nat 2047 := by decide
  have hpowz : Bits.Zadd Bits.Z0
      (ZArith.BinInt.Z.of_nat 4503599627370496) =
      ZArith.BinInt.Z.of_nat 4503599627370496 := by decide
  have hpowpos : Bits.Zadd Bits.Z0
      (ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat 4503599627370496)) =
      ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat 4503599627370496) := by decide
  have h450 : ZArith.BinInt.Z.of_nat 4503599627370496 =
      ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat 4503599627370496) := by decide
  have hzero : ZArith.BinInt.Z.of_nat 0 = Bits.Z0 := by decide
  have h00 : Bits.Zeq_bool Bits.Z0 Bits.Z0 = true := by decide
  have h0max : Bits.Zeq_bool Bits.Z0 (ZArith.BinInt.Z.of_nat 2047) = false := by decide
  have h2047zero : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat 2047) Bits.Z0 = false := by decide
  have h2047eq : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat 2047)
      (ZArith.BinInt.Z.of_nat 2047) = true := by decide
  by_cases he0 : exponent = 0
  · have hexp0 := conversion_zeq_nat_true he0
    have hexpmax : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent)
        (Bits.Zsub (ZArith.BinInt.Z.of_nat 2048) Bits.Zone) = false := by
      rw [hmaxz]
      exact conversion_zeq_nat_false (by omega)
    have hexp0' : Bits.Zeq_bool
        (ZArith.BinInt.Z.of_nat (value.bits.toNat / 4503599627370496 % 2048)) Bits.Z0 = true := by
      simpa [exponent, hzero] using hexp0
    have hexpmax' : Bits.Zeq_bool
        (ZArith.BinInt.Z.of_nat (value.bits.toNat / 4503599627370496 % 2048))
        (Bits.Zsub (ZArith.BinInt.Z.of_nat 2048) Bits.Zone) = false := by
      simpa [exponent] using hexpmax
    by_cases hm0 : mantissa = 0
    · have hmant := conversion_zeq_nat_true hm0
      have hmant' : Bits.Zeq_bool
          (ZArith.BinInt.Z.of_nat (value.bits.toNat % 4503599627370496)) Bits.Z0 = true := by
        simpa [mantissa, hzero] using hmant
      simp [Binary.is_nan, Binary.FF2B_unchecked, exponent, mantissa, hzero,
        hmaxz, h00, h0max, hexp0, hexpmax, hexp0', hexpmax', hmant, hmant', he0, hm0]
    · have hmpos : 0 < mantissa := Nat.pos_of_ne_zero hm0
      have hmz : ZArith.BinInt.Z.of_nat mantissa =
          ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat mantissa) := by
        apply intOfZ_injective
        simp only [ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.pos,
          intOfZ_zOfInt]
        exact congrArg Int.ofNat (posToNat_posOfNat hmpos).symm
      have hmraw : ZArith.BinInt.Z.of_nat (value.bits.toNat % 4503599627370496) =
          ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat (value.bits.toNat % 4503599627370496)) := by
        simpa [mantissa] using hmz
      have hmneq : value.bits.toNat % 4503599627370496 ≠ 0 := by
        simpa [mantissa] using hm0
      simp [Binary.is_nan, Binary.FF2B_unchecked, exponent, mantissa, hzero,
        hmaxz, h00, h0max, hexp0, hexpmax, hexp0', hexpmax', hmraw, he0, hm0, hmneq]
  · by_cases hemax : exponent = 2047
    · have hexp0 := conversion_zeq_nat_false (show exponent ≠ 0 by omega)
      have hexpmax : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent)
          (Bits.Zsub (ZArith.BinInt.Z.of_nat 2048) Bits.Zone) = true := by
        rw [hmaxz]
        exact conversion_zeq_nat_true hemax
      have hexp0' : Bits.Zeq_bool
          (ZArith.BinInt.Z.of_nat (value.bits.toNat / 4503599627370496 % 2048)) Bits.Z0 = false := by
        simpa [exponent, hzero] using hexp0
      have hexpmax' : Bits.Zeq_bool
          (ZArith.BinInt.Z.of_nat (value.bits.toNat / 4503599627370496 % 2048))
          (Bits.Zsub (ZArith.BinInt.Z.of_nat 2048) Bits.Zone) = true := by
        simpa [exponent] using hexpmax
      have hexp2047' : Bits.Zeq_bool
          (ZArith.BinInt.Z.of_nat (value.bits.toNat / 4503599627370496 % 2048))
          (ZArith.BinInt.Z.of_nat 2047) = true := by
        simpa [hmaxz] using hexpmax'
      by_cases hm0 : mantissa = 0
      · have hmant := conversion_zeq_nat_true hm0
        have hmant' : Bits.Zeq_bool
            (ZArith.BinInt.Z.of_nat (value.bits.toNat % 4503599627370496)) Bits.Z0 = true := by
          simpa [mantissa, hzero] using hmant
        simp [Binary.is_nan, Binary.FF2B_unchecked, exponent, mantissa, hzero,
          hmaxz, h2047zero, h2047eq, hexp0, hexpmax, hexp0', hexpmax', hexp2047', hmant, hmant', hemax, hm0]
      · have hmpos : 0 < mantissa := Nat.pos_of_ne_zero hm0
        have hmz : ZArith.BinInt.Z.of_nat mantissa =
            ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat mantissa) := by
          apply intOfZ_injective
          simp only [ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.pos,
            intOfZ_zOfInt]
          exact congrArg Int.ofNat (posToNat_posOfNat hmpos).symm
        have hmraw : ZArith.BinInt.Z.of_nat (value.bits.toNat % 4503599627370496) =
            ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat (value.bits.toNat % 4503599627370496)) := by
          simpa [mantissa] using hmz
        have hmneq : value.bits.toNat % 4503599627370496 ≠ 0 := by
          simpa [mantissa] using hm0
        simp [Binary.is_nan, Binary.FF2B_unchecked, exponent, mantissa, hzero,
          hmaxz, h2047zero, h2047eq, hexp0, hexpmax, hexp0', hexpmax', hexp2047', hmraw, hemax, hm0, hmneq]
    · have hexp0 := conversion_zeq_nat_false (show exponent ≠ 0 by omega)
      have hexpmax : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent)
          (Bits.Zsub (ZArith.BinInt.Z.of_nat 2048) Bits.Zone) = false := by
        rw [hmaxz]
        exact conversion_zeq_nat_false (by omega)
      have hexp0' : Bits.Zeq_bool
          (ZArith.BinInt.Z.of_nat (value.bits.toNat / 4503599627370496 % 2048)) Bits.Z0 = false := by
        simpa [exponent, hzero] using hexp0
      have hexpmax' : Bits.Zeq_bool
          (ZArith.BinInt.Z.of_nat (value.bits.toNat / 4503599627370496 % 2048))
          (Bits.Zsub (ZArith.BinInt.Z.of_nat 2048) Bits.Zone) = false := by
        simpa [exponent] using hexpmax
      have hexp2047' : Bits.Zeq_bool
          (ZArith.BinInt.Z.of_nat (value.bits.toNat / 4503599627370496 % 2048))
          (ZArith.BinInt.Z.of_nat 2047) = false := by
        simpa [hmaxz] using hexpmax'
      by_cases hm0 : mantissa = 0
      · have hmant := conversion_zeq_nat_true hm0
        have hmant' : Bits.Zeq_bool
            (ZArith.BinInt.Z.of_nat (value.bits.toNat % 4503599627370496)) Bits.Z0 = true := by
          simpa [mantissa, hzero] using hmant
        simp [Binary.is_nan, Binary.FF2B_unchecked, exponent, mantissa, hzero,
          hpowz, hpowpos, h450, hmaxz, h00, h0max, hexp0, hexpmax, hexp0', hexpmax', hexp2047', hmant, hmant', hemax, hm0]
      · have hmpos : 0 < mantissa := Nat.pos_of_ne_zero hm0
        have hmz : ZArith.BinInt.Z.of_nat mantissa =
            ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat mantissa) := by
          apply intOfZ_injective
          simp only [ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.pos,
            intOfZ_zOfInt]
          exact congrArg Int.ofNat (posToNat_posOfNat hmpos).symm
        obtain ⟨p, hp⟩ := conversion_zadd64_positive mantissa hmpos
        have hmraw : ZArith.BinInt.Z.of_nat (value.bits.toNat % 4503599627370496) =
            ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat (value.bits.toNat % 4503599627370496)) := by
          simpa [mantissa] using hmz
        have hmneq : value.bits.toNat % 4503599627370496 ≠ 0 := by
          simpa [mantissa] using hm0
        simp [Binary.is_nan, Binary.FF2B_unchecked, exponent, mantissa, hzero,
          hpowz, hpowpos, hmaxz, h00, h0max, hp, hexp0, hexpmax, hexp0', hexpmax', hexp2047', hmraw, hemax, hm0, hmneq]

private theorem conversion_range32_to64
    (value : float32) (minimum1 maximum1 minimum2 maximum2 : Z)
    (hminimum : ZArith.Zbool.Zle_bool minimum2 minimum1 = true)
    (hmaximum : ZArith.Zbool.Zle_bool maximum1 maximum2 = true)
    (conv_nan : Bits.binary32 → IEEE754_extra.NaNResult z53 z1024)
    (rounding : IEEE754_extra.mode) (n : Z)
    (hvalue : IEEE754_extra.ZofB_range (decode32 value) minimum1 maximum1 = some n) :
    IEEE754_extra.ZofB_range
      (IEEE754_extra.Bconv conv_nan rounding (decode32 value)) minimum2 maximum2 = some n := by
  have hnotnan : Binary.is_nan (decode32 value) = false := by
    unfold IEEE754_extra.ZofB_range at hvalue
    cases hdecoded : decode32 value <;>
      simp [hdecoded, IEEE754_extra.ZofB, Binary.is_nan] at hvalue ⊢
  have hminimum' : IEEE754_extra.Zle minimum2 minimum1 := by
    have hs := CompCert4Lean.Flocq.Core.Zaux.Zle_bool_spec minimum2 minimum1
    have hs' : CompCert4Lean.Flocq.Core.Zaux.Zle_bool_prop minimum2 minimum1 true := by
      simpa [hminimum] using hs
    cases hs' with
    | Zle_bool_true_ h => exact h
  have hmaximum' : IEEE754_extra.Zle maximum1 maximum2 := by
    have hs := CompCert4Lean.Flocq.Core.Zaux.Zle_bool_spec maximum1 maximum2
    have hs' : CompCert4Lean.Flocq.Core.Zaux.Zle_bool_prop maximum1 maximum2 true := by
      simpa [hmaximum] using hs
    cases hs' with
    | Zle_bool_true_ h => exact h
  have hconversion := conversion_of_single_bconv value conv_nan hnotnan
  have hrange := IEEE754_extra.ZofB_range_Bconv
    (prec1 := z24) (emax1 := z128) (prec2 := z53) (emax2 := z1024)
    minimum1 maximum1 minimum2 maximum2
    (by change (24 : Int) ≤ 53; decide) (by change (128 : Int) ≤ 1024; decide)
    hminimum' hmaximum' conv_nan rounding
    ⟨decode32 value, conversion_decode32_valid value⟩ n hvalue
  exact hrange

theorem Float32.to_intu_double : Float32.to_intu_doubleStatement := by
  intro value result hresult
  unfold Float32.to_intu at hresult
  cases hsource : IEEE754_extra.ZofB_range (decode32 value) z0 Integers.Int.max_unsigned with
  | none => simp [hsource] at hresult
  | some source =>
      have hrepr : Integers.Int.repr source = result := by
        simpa [hsource] using hresult
      have hinversion := IEEE754_extra.ZofB_range_inversion
        ⟨decode32 value, conversion_decode32_valid value⟩
        z0 Integers.Int.max_unsigned source hsource
      have hsource_eq : source = Integers.Int.unsigned result := by
        have hu := congrArg Integers.Int.unsigned hrepr
        rw [Integers.Int.unsigned_repr_proof_api source ⟨hinversion.1, hinversion.2.1⟩] at hu
        simpa using hu
      have htransport := conversion_range32_to64 value z0 Integers.Int.max_unsigned
        z0 Integers.Int.max_unsigned (by decide) (by decide)
        (fun _ => ⟨Binary.B754_nan false .xH, by
          simp only [Binary.BinaryFloatCertificate, Binary.B2FF, Binary.valid_binary,
            Binary.nan_pl]
          constructor
          · rfl
          · apply CompCert4Lean.Flocq.Core.Zaux.Zlt_bool_true
            change (1 : Int) < 53
            decide
          ⟩)
        BinarySingleNaN.mode_NE source hsource
      have hnotnan : Binary.is_nan (decode32 value) = false := by
        unfold IEEE754_extra.ZofB_range at hsource
        cases hdecoded : decode32 value <;>
          simp [hdecoded, IEEE754_extra.ZofB, Binary.is_nan] at hsource ⊢
      have hconversion := conversion_of_single_bconv value
        (fun _ => ⟨Binary.B754_nan false .xH, by
          simp only [Binary.BinaryFloatCertificate, Binary.B2FF, Binary.valid_binary,
            Binary.nan_pl]
          constructor
          · rfl
          · apply CompCert4Lean.Flocq.Core.Zaux.Zlt_bool_true
            change (1 : Int) < 53
            decide
          ⟩) hnotnan
      have htarget : IEEE754_extra.ZofB_range
          (decode64 (Float.of_single value)) z0 Integers.Int.max_unsigned = some source := by
        rw [hconversion]
        exact htransport
      unfold Float.to_intu
      change Option.map Integers.Int.repr
        (IEEE754_extra.ZofB_range (decode64 (Float.of_single value)) z0 Integers.Int.max_unsigned) = some result
      rw [htarget]
      simpa [hrepr]

theorem Float32.to_long_double : Float32.to_long_doubleStatement := by
  intro value result hresult
  unfold Float32.to_long at hresult
  cases hsource : IEEE754_extra.ZofB_range (decode32 value)
      Integers.Int64.min_signed Integers.Int64.max_signed with
  | none => simp [hsource] at hresult
  | some source =>
      have hrepr : Integers.Int64.repr source = result := by
        simpa [hsource] using hresult
      have hinversion := IEEE754_extra.ZofB_range_inversion
        ⟨decode32 value, conversion_decode32_valid value⟩
        Integers.Int64.min_signed Integers.Int64.max_signed source hsource
      have hsource_eq : source = Integers.Int64.signed result := by
        have hs := congrArg Integers.Int64.signed hrepr
        rw [Integers.Int64.signed_repr_proof source ⟨hinversion.1, hinversion.2.1⟩] at hs
        simpa using hs
      have htransport := conversion_range32_to64 value
        Integers.Int64.min_signed Integers.Int64.max_signed
        Integers.Int64.min_signed Integers.Int64.max_signed (by decide) (by decide)
        (fun _ => ⟨Binary.B754_nan false .xH, by
          simp only [Binary.BinaryFloatCertificate, Binary.B2FF, Binary.valid_binary,
            Binary.nan_pl]
          constructor
          · rfl
          · apply CompCert4Lean.Flocq.Core.Zaux.Zlt_bool_true
            change (1 : Int) < 53
            decide
          ⟩)
        BinarySingleNaN.mode_NE source hsource
      have hnotnan : Binary.is_nan (decode32 value) = false := by
        unfold IEEE754_extra.ZofB_range at hsource
        cases hdecoded : decode32 value <;>
          simp [hdecoded, IEEE754_extra.ZofB, Binary.is_nan] at hsource ⊢
      have hconversion := conversion_of_single_bconv value
        (fun _ => ⟨Binary.B754_nan false .xH, by
          simp only [Binary.BinaryFloatCertificate, Binary.B2FF, Binary.valid_binary,
            Binary.nan_pl]
          constructor
          · rfl
          · apply CompCert4Lean.Flocq.Core.Zaux.Zlt_bool_true
            change (1 : Int) < 53
            decide
          ⟩) hnotnan
      have htarget : IEEE754_extra.ZofB_range
          (decode64 (Float.of_single value)) Integers.Int64.min_signed
            Integers.Int64.max_signed = some source := by
        rw [hconversion]
        exact htransport
      unfold Float.to_long
      change Option.map Integers.Int64.repr
        (IEEE754_extra.ZofB_range (decode64 (Float.of_single value))
          Integers.Int64.min_signed Integers.Int64.max_signed) = some result
      rw [htarget]
      simpa [hrepr]

theorem Float32.to_longu_double : Float32.to_longu_doubleStatement := by
  intro value result hresult
  unfold Float32.to_longu at hresult
  cases hsource : IEEE754_extra.ZofB_range (decode32 value) z0 Integers.Int64.max_unsigned with
  | none => simp [hsource] at hresult
  | some source =>
      have hrepr : Integers.Int64.repr source = result := by
        simpa [hsource] using hresult
      have hinversion := IEEE754_extra.ZofB_range_inversion
        ⟨decode32 value, conversion_decode32_valid value⟩
        z0 Integers.Int64.max_unsigned source hsource
      have hsource_eq : source = Integers.Int64.unsigned result := by
        have hu := congrArg Integers.Int64.unsigned hrepr
        rw [Integers.Int64.unsigned_repr_proof source ⟨hinversion.1, hinversion.2.1⟩] at hu
        simpa using hu
      have htransport := conversion_range32_to64 value z0 Integers.Int64.max_unsigned
        z0 Integers.Int64.max_unsigned (by decide) (by decide)
        (fun _ => ⟨Binary.B754_nan false .xH, by
          simp only [Binary.BinaryFloatCertificate, Binary.B2FF, Binary.valid_binary,
            Binary.nan_pl]
          constructor
          · rfl
          · apply CompCert4Lean.Flocq.Core.Zaux.Zlt_bool_true
            change (1 : Int) < 53
            decide
          ⟩)
        BinarySingleNaN.mode_NE source hsource
      have hnotnan : Binary.is_nan (decode32 value) = false := by
        unfold IEEE754_extra.ZofB_range at hsource
        cases hdecoded : decode32 value <;>
          simp [hdecoded, IEEE754_extra.ZofB, Binary.is_nan] at hsource ⊢
      have hconversion := conversion_of_single_bconv value
        (fun _ => ⟨Binary.B754_nan false .xH, by
          simp only [Binary.BinaryFloatCertificate, Binary.B2FF, Binary.valid_binary,
            Binary.nan_pl]
          constructor
          · rfl
          · apply CompCert4Lean.Flocq.Core.Zaux.Zlt_bool_true
            change (1 : Int) < 53
            decide
          ⟩) hnotnan
      have htarget : IEEE754_extra.ZofB_range
          (decode64 (Float.of_single value)) z0 Integers.Int64.max_unsigned = some source := by
        rw [hconversion]
        exact htransport
      unfold Float.to_longu
      change Option.map Integers.Int64.repr
        (IEEE754_extra.ZofB_range (decode64 (Float.of_single value)) z0
          Integers.Int64.max_unsigned) = some result
      rw [htarget]
      simpa [hrepr]

private theorem manual_fexp_canonical64 (mantissa : positive) (exponent : Z)
    (digits : posToNat (BinarySingleNaN.digits2_pos mantissa) = 53)
    (minimum : -1074 ≤ intOfZ exponent) :
    BinarySingleNaN.fexp0 z53 z1024
      (ZArith.BinInt.Z.add (.Zpos (BinarySingleNaN.digits2_pos mantissa)) exponent) = exponent := by
  have digits_value : (.Zpos (BinarySingleNaN.digits2_pos mantissa) : Z) = z53 := by
    apply intOfZ_injective
    change (posToNat (BinarySingleNaN.digits2_pos mantissa) : Int) = 53
    rw [digits]
    rfl
  have cancel : ZArith.BinInt.Z.sub (ZArith.BinInt.Z.add z53 exponent) z53 = exponent := by
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add, intOfZ_zOfInt]
    omega
  change ZArith.BinInt.Z.max
    (ZArith.BinInt.Z.sub
      (ZArith.BinInt.Z.add (.Zpos (BinarySingleNaN.digits2_pos mantissa)) exponent) z53)
    (BinarySingleNaN.emin0 z53 z1024) = exponent
  rw [digits_value, cancel]
  exact ZArith.BinInt.Z.max_l _ _ minimum

private theorem manual_round_aux_canonical64 (sign : Bool) (mantissa : positive) (exponent : Z)
    (digits : posToNat (BinarySingleNaN.digits2_pos mantissa) = 53)
    (minimum : -1074 ≤ intOfZ exponent) (maximum : intOfZ exponent ≤ 971) :
    BinarySingleNaN.binary_round_aux (prec := z53) (emax := z1024)
      .mode_NE sign (.Zpos mantissa) exponent .loc_Exact =
        .S754_finite sign mantissa exponent := by
  have target := manual_fexp_canonical64 mantissa exponent digits minimum
  have subtract : ZArith.BinInt.Z.sub exponent exponent = .Z0 := by
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt, Int.sub_self]
    rfl
  have shifted : BinarySingleNaN.shr_fexp (prec := z53) (emax := z1024)
      (.Zpos mantissa) exponent .loc_Exact =
        (BinarySingleNaN.shr_record_of_loc (.Zpos mantissa) .loc_Exact, exponent) := by
    change BinarySingleNaN.shr
      (BinarySingleNaN.shr_record_of_loc (.Zpos mantissa) .loc_Exact) exponent
      (ZArith.BinInt.Z.sub (BinarySingleNaN.fexp0 z53 z1024
        (ZArith.BinInt.Z.add (.Zpos (BinarySingleNaN.digits2_pos mantissa)) exponent)) exponent) = _
    rw [target, subtract]
    rfl
  unfold BinarySingleNaN.binary_round_aux
  rw [shifted]
  change (match (BinarySingleNaN.shr_fexp (prec := z53) (emax := z1024)
      (.Zpos mantissa) exponent .loc_Exact).1.shr_m with
    | .Z0 => BinarySingleNaN.S754_zero sign
    | .Zpos result => BinarySingleNaN.binary_fit_aux (prec := z53) (emax := z1024)
        .mode_NE sign result (BinarySingleNaN.shr_fexp (prec := z53) (emax := z1024)
          (.Zpos mantissa) exponent .loc_Exact).2
    | .Zneg _ => BinarySingleNaN.S754_nan) = _
  rw [shifted]
  change (if ZArith.Zbool.Zle_bool exponent
    (ZArith.BinInt.Z.sub z1024 z53) then _ else _) = _
  have fits : ZArith.Zbool.Zle_bool exponent (ZArith.BinInt.Z.sub z1024 z53) = true := by
    change (if intOfZ exponent ≤ 971 then true else false) = true
    simp only [maximum, ↓reduceIte]
  rw [fits]
  rfl

private theorem manual_normalized_mantissa_digits64 (mantissa : positive)
    (small : (posToNat mantissa).log2 ≤ 31) :
    posToNat (BinarySingleNaN.digits2_pos
      (posOfNat (posToNat mantissa * 2 ^ (52 - (posToNat mantissa).log2)))) = 53 := by
  have natural_digits := quiet_nan_digits2_pos_nat
    (posOfNat (posToNat mantissa * 2 ^ (52 - (posToNat mantissa).log2)))
  change posToNat (BinarySingleNaN.digits2_pos
    (posOfNat (posToNat mantissa * 2 ^ (52 - (posToNat mantissa).log2)))) =
      (posToNat (posOfNat (posToNat mantissa * 2 ^ (52 - (posToNat mantissa).log2)))).log2 + 1 at natural_digits
  rw [natural_digits]
  have positive := Nat.mul_pos (posToNat_positive mantissa)
    (Nat.two_pow_pos (52 - (posToNat mantissa).log2))
  change (posToNat (posOfNat
    (posToNat mantissa * 2 ^ (52 - (posToNat mantissa).log2)))).log2 + 1 = 53
  rw [posToNat_posOfNat positive, log2_mul_pow _ _ (Nat.ne_of_gt (posToNat_positive mantissa))]
  omega

private theorem manual_lift_finite {prec emax : Z}
    (value : BinarySingleNaN.binary_float prec emax)
    (hnan : BinarySingleNaN.is_nan value = false)
    (sign : Bool) (mantissa : positive) (exponent : Z)
    (hequal : value = BinarySingleNaN.B754_finite sign mantissa exponent) :
    Binary.BSN2B' value hnan = Binary.B754_finite sign mantissa exponent := by
  cases hequal
  rfl

private theorem manual_fexp_canonical32 (mantissa : positive) (exponent : Z)
    (digits : posToNat (BinarySingleNaN.digits2_pos mantissa) = 24)
    (minimum : -149 ≤ intOfZ exponent) :
    BinarySingleNaN.fexp0 z24 z128
      (ZArith.BinInt.Z.add (.Zpos (BinarySingleNaN.digits2_pos mantissa)) exponent) = exponent := by
  have digits_value : (.Zpos (BinarySingleNaN.digits2_pos mantissa) : Z) = z24 := by
    apply intOfZ_injective
    change (posToNat (BinarySingleNaN.digits2_pos mantissa) : Int) = 24
    rw [digits]
    rfl
  have cancel : ZArith.BinInt.Z.sub (ZArith.BinInt.Z.add z24 exponent) z24 = exponent := by
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add, intOfZ_zOfInt]
    omega
  change ZArith.BinInt.Z.max
    (ZArith.BinInt.Z.sub
      (ZArith.BinInt.Z.add (.Zpos (BinarySingleNaN.digits2_pos mantissa)) exponent) z24)
    (BinarySingleNaN.emin0 z24 z128) = exponent
  rw [digits_value, cancel]
  exact ZArith.BinInt.Z.max_l _ _ minimum

private theorem manual_round_aux_canonical32 (sign : Bool) (mantissa : positive) (exponent : Z)
    (digits : posToNat (BinarySingleNaN.digits2_pos mantissa) = 24)
    (minimum : -149 ≤ intOfZ exponent) (maximum : intOfZ exponent ≤ 104) :
    BinarySingleNaN.binary_round_aux (prec := z24) (emax := z128)
      .mode_NE sign (.Zpos mantissa) exponent .loc_Exact =
        .S754_finite sign mantissa exponent := by
  have target := manual_fexp_canonical32 mantissa exponent digits minimum
  have subtract : ZArith.BinInt.Z.sub exponent exponent = .Z0 := by
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt, Int.sub_self]
    rfl
  have shifted : BinarySingleNaN.shr_fexp (prec := z24) (emax := z128)
      (.Zpos mantissa) exponent .loc_Exact =
        (BinarySingleNaN.shr_record_of_loc (.Zpos mantissa) .loc_Exact, exponent) := by
    change BinarySingleNaN.shr
      (BinarySingleNaN.shr_record_of_loc (.Zpos mantissa) .loc_Exact) exponent
      (ZArith.BinInt.Z.sub (BinarySingleNaN.fexp0 z24 z128
        (ZArith.BinInt.Z.add (.Zpos (BinarySingleNaN.digits2_pos mantissa)) exponent)) exponent) = _
    rw [target, subtract]
    rfl
  unfold BinarySingleNaN.binary_round_aux
  rw [shifted]
  change (match (BinarySingleNaN.shr_fexp (prec := z24) (emax := z128)
      (.Zpos mantissa) exponent .loc_Exact).1.shr_m with
    | .Z0 => BinarySingleNaN.S754_zero sign
    | .Zpos result => BinarySingleNaN.binary_fit_aux (prec := z24) (emax := z128)
        .mode_NE sign result (BinarySingleNaN.shr_fexp (prec := z24) (emax := z128)
          (.Zpos mantissa) exponent .loc_Exact).2
    | .Zneg _ => BinarySingleNaN.S754_nan) = _
  rw [shifted]
  change (if ZArith.Zbool.Zle_bool exponent
    (ZArith.BinInt.Z.sub z128 z24) then _ else _) = _
  have fits : ZArith.Zbool.Zle_bool exponent (ZArith.BinInt.Z.sub z128 z24) = true := by
    change (if intOfZ exponent ≤ 104 then true else false) = true
    simp only [maximum, ↓reduceIte]
  rw [fits]
  rfl

private theorem manual_normalized_mantissa_digits32 (mantissa : positive)
    (small : (posToNat mantissa).log2 ≤ 23) :
    posToNat (BinarySingleNaN.digits2_pos
      (posOfNat (posToNat mantissa * 2 ^ (23 - (posToNat mantissa).log2)))) = 24 := by
  have natural_digits := quiet_nan_digits2_pos_nat
    (posOfNat (posToNat mantissa * 2 ^ (23 - (posToNat mantissa).log2)))
  change posToNat (BinarySingleNaN.digits2_pos
    (posOfNat (posToNat mantissa * 2 ^ (23 - (posToNat mantissa).log2)))) =
      (posToNat (posOfNat (posToNat mantissa * 2 ^ (23 - (posToNat mantissa).log2)))).log2 + 1 at natural_digits
  rw [natural_digits]
  have positive := Nat.mul_pos (posToNat_positive mantissa)
    (Nat.two_pow_pos (23 - (posToNat mantissa).log2))
  change (posToNat (posOfNat
    (posToNat mantissa * 2 ^ (23 - (posToNat mantissa).log2)))).log2 + 1 = 24
  rw [posToNat_posOfNat positive, log2_mul_pow _ _ (Nat.ne_of_gt (posToNat_positive mantissa))]
  omega

private theorem manual_BofZ_positive_small32
    [certificate : Binary.BinaryNormalizeCertificate z24 z128]
    (mantissa : positive) (small : (posToNat mantissa).log2 < 23) :
    IEEE754_extra.BofZ (prec := z24) (emax := z128) (.Zpos mantissa) =
      .B754_finite false
        (posOfNat (posToNat mantissa * 2 ^ (23 - (posToNat mantissa).log2)) )
        (zOfInt ((posToNat mantissa).log2 - 23)) := by
  have target : BinarySingleNaN.fexp0 z24 z128
      (ZArith.BinInt.Z.add (.Zpos (BinarySingleNaN.digits2_pos mantissa)) .Z0) =
        zOfInt ((posToNat mantissa).log2 - 23) := by
    have digits := quiet_nan_digits2_pos_nat mantissa
    change ZArith.BinInt.Z.max
      (ZArith.BinInt.Z.sub
        (ZArith.BinInt.Z.add (.Zpos (BinarySingleNaN.digits2_pos mantissa)) .Z0) z24)
      (BinarySingleNaN.emin0 z24 z128) = _
    have difference : ZArith.BinInt.Z.sub
        (ZArith.BinInt.Z.add (.Zpos (BinarySingleNaN.digits2_pos mantissa)) .Z0) z24 =
          zOfInt ((posToNat mantissa).log2 - 23) := by
      apply intOfZ_injective
      simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add, intOfZ_zOfInt]
      change (posToNat (BinarySingleNaN.digits2_pos mantissa) : Int) + 0 - 24 = _
      change posToNat (BinarySingleNaN.digits2_pos mantissa) =
        (posToNat mantissa).log2 + 1 at digits
      rw [digits]
      omega
    rw [difference]
    apply ZArith.BinInt.Z.max_l
    change -149 ≤ intOfZ (zOfInt ((posToNat mantissa).log2 - 23))
    rw [intOfZ_zOfInt]
    omega
  have shift_positive : 0 < 23 - (posToNat mantissa).log2 := by omega
  have shift_target : ZArith.BinInt.Z.sub
      (zOfInt ((posToNat mantissa).log2 - 23)) .Z0 =
        .Zneg (posOfNat (23 - (posToNat mantissa).log2)) := by
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    change (posToNat mantissa).log2 - 23 - (0 : Int) =
      -(posToNat (posOfNat (23 - (posToNat mantissa).log2)) : Int)
    rw [posToNat_posOfNat shift_positive]
    omega
  have aligned : BinarySingleNaN.shl_align_fexp (prec := z24) (emax := z128) mantissa .Z0 =
      (posOfNat (posToNat mantissa * 2 ^ (23 - (posToNat mantissa).log2)),
        zOfInt ((posToNat mantissa).log2 - 23)) := by
    unfold BinarySingleNaN.shl_align_fexp
    rw [target]
    unfold BinarySingleNaN.shl_align Model.Rocq.Coq.Floats.SpecFloat.shl_align
    simp only [Model.Rocq.Coq.Floats.SpecFloat.zsub]
    rw [shift_target]
    change (posOfNat (posToNat mantissa * 2 ^
      posToNat (posOfNat (23 - (posToNat mantissa).log2))), _) = _
    rw [posToNat_posOfNat shift_positive]
  have rounded := manual_round_aux_canonical32 false
    (posOfNat (posToNat mantissa * 2 ^ (23 - (posToNat mantissa).log2)))
    (zOfInt ((posToNat mantissa).log2 - 23))
    (manual_normalized_mantissa_digits32 mantissa (Nat.le_of_lt small))
    (by rw [intOfZ_zOfInt]; omega) (by rw [intOfZ_zOfInt]; omega)
  have round_result : BinarySingleNaN.binary_round (prec := z24) (emax := z128)
      .mode_NE false mantissa .Z0 =
        .S754_finite false
          (posOfNat (posToNat mantissa * 2 ^ (23 - (posToNat mantissa).log2)))
          (zOfInt ((posToNat mantissa).log2 - 23)) := by
    unfold BinarySingleNaN.binary_round
    rw [aligned]
    exact rounded
  have normalized : BinarySingleNaN.binary_normalize (prec := z24) (emax := z128)
      .mode_NE (.Zpos mantissa) .Z0 false =
        .B754_finite false
          (posOfNat (posToNat mantissa * 2 ^ (23 - (posToNat mantissa).log2)))
          (zOfInt ((posToNat mantissa).log2 - 23)) := by
    change BinarySingleNaN.SF2B
      (BinarySingleNaN.binary_round (prec := z24) (emax := z128) .mode_NE false mantissa .Z0) = _
    rw [round_result]
    rfl
  change Binary.BSN2B'
    (BinarySingleNaN.binary_normalize (prec := z24) (emax := z128)
      .mode_NE (.Zpos mantissa) .Z0 false) _ = _
  exact manual_lift_finite
    (BinarySingleNaN.binary_normalize (prec := z24) (emax := z128)
      .mode_NE (.Zpos mantissa) .Z0 false)
    ((inferInstance : Binary.BinaryNormalizeCertificate z24 z128).is_nan_binary_normalize
      BinarySingleNaN.mode_NE (.Zpos mantissa) .Z0 false)
    false
    (posOfNat (posToNat mantissa * 2 ^ (23 - (posToNat mantissa).log2)))
    (zOfInt ((posToNat mantissa).log2 - 23))
    normalized

private theorem manual_BofZ_positive_log23
    [certificate : Binary.BinaryNormalizeCertificate z24 z128]
    (mantissa : positive) (hlog : (posToNat mantissa).log2 = 23) :
    IEEE754_extra.BofZ (prec := z24) (emax := z128) (.Zpos mantissa) =
      .B754_finite false mantissa .Z0 := by
  have digits : posToNat (BinarySingleNaN.digits2_pos mantissa) = 24 := by
    have natural_digits := quiet_nan_digits2_pos_nat mantissa
    change posToNat (BinarySingleNaN.digits2_pos mantissa) =
      (posToNat mantissa).log2 + 1 at natural_digits
    rw [natural_digits, hlog]
  have target : BinarySingleNaN.fexp0 z24 z128
      (ZArith.BinInt.Z.add (.Zpos (BinarySingleNaN.digits2_pos mantissa)) .Z0) = .Z0 := by
    have h := manual_fexp_canonical32 mantissa .Z0 digits (by decide)
    simpa using h
  have aligned : BinarySingleNaN.shl_align_fexp (prec := z24) (emax := z128) mantissa .Z0 =
      (mantissa, .Z0) := by
    unfold BinarySingleNaN.shl_align_fexp
    rw [target]
    unfold BinarySingleNaN.shl_align Model.Rocq.Coq.Floats.SpecFloat.shl_align
    simp only [Model.Rocq.Coq.Floats.SpecFloat.zsub]
    rfl
  have rounded := manual_round_aux_canonical32 false mantissa .Z0 digits (by decide) (by decide)
  have round_result : BinarySingleNaN.binary_round (prec := z24) (emax := z128)
      .mode_NE false mantissa .Z0 = .S754_finite false mantissa .Z0 := by
    unfold BinarySingleNaN.binary_round
    rw [aligned]
    exact rounded
  have normalized : BinarySingleNaN.binary_normalize (prec := z24) (emax := z128)
      .mode_NE (.Zpos mantissa) .Z0 false = .B754_finite false mantissa .Z0 := by
    change BinarySingleNaN.SF2B
      (BinarySingleNaN.binary_round (prec := z24) (emax := z128) .mode_NE false mantissa .Z0) = _
    rw [round_result]
    rfl
  change Binary.BSN2B'
    (BinarySingleNaN.binary_normalize (prec := z24) (emax := z128)
      .mode_NE (.Zpos mantissa) .Z0 false) _ = _
  exact manual_lift_finite
    (BinarySingleNaN.binary_normalize (prec := z24) (emax := z128)
      .mode_NE (.Zpos mantissa) .Z0 false)
    ((inferInstance : Binary.BinaryNormalizeCertificate z24 z128).is_nan_binary_normalize
      BinarySingleNaN.mode_NE (.Zpos mantissa) .Z0 false)
    false mantissa .Z0 normalized

private theorem manual_BofZ_positive_small64
    [certificate : Binary.BinaryNormalizeCertificate z53 z1024]
    (mantissa : positive) (small : (posToNat mantissa).log2 ≤ 31) :
    IEEE754_extra.BofZ (prec := z53) (emax := z1024) (.Zpos mantissa) =
      .B754_finite false
        (posOfNat (posToNat mantissa * 2 ^ (52 - (posToNat mantissa).log2)))
        (zOfInt ((posToNat mantissa).log2 - 52)) := by
  have target : BinarySingleNaN.fexp0 z53 z1024
      (ZArith.BinInt.Z.add (.Zpos (BinarySingleNaN.digits2_pos mantissa)) .Z0) =
        zOfInt ((posToNat mantissa).log2 - 52) := by
    have digits := quiet_nan_digits2_pos_nat mantissa
    change ZArith.BinInt.Z.max
      (ZArith.BinInt.Z.sub
        (ZArith.BinInt.Z.add (.Zpos (BinarySingleNaN.digits2_pos mantissa)) .Z0) z53)
      (BinarySingleNaN.emin0 z53 z1024) = _
    have difference : ZArith.BinInt.Z.sub
        (ZArith.BinInt.Z.add (.Zpos (BinarySingleNaN.digits2_pos mantissa)) .Z0) z53 =
          zOfInt ((posToNat mantissa).log2 - 52) := by
      apply intOfZ_injective
      simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add, intOfZ_zOfInt]
      change (posToNat (BinarySingleNaN.digits2_pos mantissa) : Int) + 0 - 53 = _
      change posToNat (BinarySingleNaN.digits2_pos mantissa) =
        (posToNat mantissa).log2 + 1 at digits
      rw [digits]
      omega
    rw [difference]
    apply ZArith.BinInt.Z.max_l
    change -1074 ≤ intOfZ (zOfInt ((posToNat mantissa).log2 - 52))
    rw [intOfZ_zOfInt]
    omega
  have shift_positive : 0 < 52 - (posToNat mantissa).log2 := by omega
  have shift_target : ZArith.BinInt.Z.sub
      (zOfInt ((posToNat mantissa).log2 - 52)) .Z0 =
        .Zneg (posOfNat (52 - (posToNat mantissa).log2)) := by
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    change (posToNat mantissa).log2 - 52 - (0 : Int) =
      -(posToNat (posOfNat (52 - (posToNat mantissa).log2)) : Int)
    rw [posToNat_posOfNat shift_positive]
    omega
  have aligned : BinarySingleNaN.shl_align_fexp (prec := z53) (emax := z1024) mantissa .Z0 =
      (posOfNat (posToNat mantissa * 2 ^ (52 - (posToNat mantissa).log2)),
        zOfInt ((posToNat mantissa).log2 - 52)) := by
    unfold BinarySingleNaN.shl_align_fexp
    rw [target]
    unfold BinarySingleNaN.shl_align Model.Rocq.Coq.Floats.SpecFloat.shl_align
    simp only [Model.Rocq.Coq.Floats.SpecFloat.zsub]
    rw [shift_target]
    change (posOfNat (posToNat mantissa * 2 ^
      posToNat (posOfNat (52 - (posToNat mantissa).log2))), _) = _
    rw [posToNat_posOfNat shift_positive]
  have rounded := manual_round_aux_canonical64 false
    (posOfNat (posToNat mantissa * 2 ^ (52 - (posToNat mantissa).log2)))
    (zOfInt ((posToNat mantissa).log2 - 52))
    (manual_normalized_mantissa_digits64 mantissa small)
    (by rw [intOfZ_zOfInt]; omega) (by rw [intOfZ_zOfInt]; omega)
  have round_result : BinarySingleNaN.binary_round (prec := z53) (emax := z1024)
      .mode_NE false mantissa .Z0 =
        .S754_finite false
          (posOfNat (posToNat mantissa * 2 ^ (52 - (posToNat mantissa).log2)))
          (zOfInt ((posToNat mantissa).log2 - 52)) := by
    unfold BinarySingleNaN.binary_round
    rw [aligned]
    exact rounded
  have normalized : BinarySingleNaN.binary_normalize (prec := z53) (emax := z1024)
      .mode_NE (.Zpos mantissa) .Z0 false =
        .B754_finite false
          (posOfNat (posToNat mantissa * 2 ^ (52 - (posToNat mantissa).log2)))
          (zOfInt ((posToNat mantissa).log2 - 52)) := by
    change BinarySingleNaN.SF2B
      (BinarySingleNaN.binary_round (prec := z53) (emax := z1024) .mode_NE false mantissa .Z0) = _
    rw [round_result]
    rfl
  change Binary.BSN2B'
    (BinarySingleNaN.binary_normalize (prec := z53) (emax := z1024)
      .mode_NE (.Zpos mantissa) .Z0 false) _ = _
  exact manual_lift_finite
    (BinarySingleNaN.binary_normalize (prec := z53) (emax := z1024)
      .mode_NE (.Zpos mantissa) .Z0 false)
    ((inferInstance : Binary.BinaryNormalizeCertificate z53 z1024).is_nan_binary_normalize
      BinarySingleNaN.mode_NE (.Zpos mantissa) .Z0 false)
    false
    (posOfNat (posToNat mantissa * 2 ^ (52 - (posToNat mantissa).log2)))
    (zOfInt ((posToNat mantissa).log2 - 52))
    normalized

private theorem conversion_iter_add {α : Type} (operation : α → α)
    (first second : Nat) (value : α) :
    CompCert4Lean.Flocq.Core.Zaux.iter_nat operation (first + second) value =
      CompCert4Lean.Flocq.Core.Zaux.iter_nat operation first
        (CompCert4Lean.Flocq.Core.Zaux.iter_nat operation second value) := by
  induction second generalizing value with
  | zero => rfl
  | succ second induction =>
      change CompCert4Lean.Flocq.Core.Zaux.iter_nat operation (first + second)
        (operation value) = _
      exact induction (operation value)

private theorem conversion_shift_succ (mantissa : positive) (count : Nat) :
    posOfNat (posToNat mantissa * 2 ^ (count + 1)) =
      .xO (posOfNat (posToNat mantissa * 2 ^ count)) := by
  apply posToNat_injective
  rw [posToNat_posOfNat (Nat.mul_pos (posToNat_positive _) (Nat.two_pow_pos _))]
  change _ = 2 * posToNat (posOfNat (posToNat mantissa * 2 ^ count))
  rw [posToNat_posOfNat (Nat.mul_pos (posToNat_positive _) (Nat.two_pow_pos _)),
    Nat.pow_succ]
  ac_rfl

private theorem conversion_shift_exact (mantissa : positive) (count : Nat) :
    CompCert4Lean.Flocq.Core.Zaux.iter_nat BinarySingleNaN.shr_1 count
        (BinarySingleNaN.shr_record_of_loc
          (.Zpos (posOfNat (posToNat mantissa * 2 ^ count))) .loc_Exact) =
      BinarySingleNaN.shr_record_of_loc (.Zpos mantissa) .loc_Exact := by
  induction count with
  | zero => simp only [Nat.pow_zero, Nat.mul_one, posOfNat_posToNat]; rfl
  | succ count induction =>
      rw [conversion_shift_succ]
      exact induction

private theorem conversion_shr_count (mantissa : positive) (exponent : Int) (count : Nat) :
    BinarySingleNaN.shr (BinarySingleNaN.shr_record_of_loc (.Zpos mantissa) .loc_Exact)
        (zOfInt exponent) (zOfInt count) =
      (CompCert4Lean.Flocq.Core.Zaux.iter_nat BinarySingleNaN.shr_1 count
        (BinarySingleNaN.shr_record_of_loc (.Zpos mantissa) .loc_Exact),
        zOfInt (exponent + count)) := by
  rw [BinarySingleNaN.shr_nat _ _ _ (by
    change (0 : Int) ≤ intOfZ (zOfInt count)
    rw [intOfZ_zOfInt]
    omega)]
  simp only [ZArith.BinInt.Z.to_nat, intOfZ_zOfInt, Int.toNat_natCast,
    ZArith.BinInt.Z.add]

private theorem conversion_fexp32 (mantissa : positive) (exponent : Int)
    (minimum : -126 ≤ (posToNat mantissa).log2 + exponent) :
    BinarySingleNaN.fexp0 z24 z128
        (ZArith.BinInt.Z.add (.Zpos (BinarySingleNaN.digits2_pos mantissa))
          (zOfInt exponent)) =
      zOfInt ((posToNat mantissa).log2 + exponent - 23) := by
  have digits := quiet_nan_digits2_pos_nat mantissa
  change posToNat (BinarySingleNaN.digits2_pos mantissa) =
    (posToNat mantissa).log2 + 1 at digits
  have difference : ZArith.BinInt.Z.sub
      (ZArith.BinInt.Z.add (.Zpos (BinarySingleNaN.digits2_pos mantissa))
        (zOfInt exponent)) z24 =
      zOfInt ((posToNat mantissa).log2 + exponent - 23) := by
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add, intOfZ_zOfInt]
    change (posToNat (BinarySingleNaN.digits2_pos mantissa) : Int) + exponent - 24 = _
    rw [digits]
    omega
  change ZArith.BinInt.Z.max
    (ZArith.BinInt.Z.sub
      (ZArith.BinInt.Z.add (.Zpos (BinarySingleNaN.digits2_pos mantissa))
        (zOfInt exponent)) z24) (BinarySingleNaN.emin0 z24 z128) = _
  rw [difference]
  apply ZArith.BinInt.Z.max_l
  change -149 ≤ intOfZ (zOfInt ((posToNat mantissa).log2 + exponent - 23))
  rw [intOfZ_zOfInt]
  omega

private theorem conversion_align_ge (mantissa : positive) (exponent target : Int)
    (ordered : exponent ≤ target) :
    BinarySingleNaN.shl_align mantissa (zOfInt exponent) (zOfInt target) =
      (mantissa, zOfInt exponent) := by
  change (match ZArith.BinInt.Z.sub (zOfInt target) (zOfInt exponent) with
    | .Zneg count => _
    | _ => _) = _
  cases difference : ZArith.BinInt.Z.sub (zOfInt target) (zOfInt exponent) with
  | Z0 => rfl
  | Zpos count => rfl
  | Zneg count =>
      have numeric := congrArg intOfZ difference
      simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt] at numeric
      change target - exponent = -(posToNat count : Int) at numeric
      have positive := posToNat_positive count
      omega

private theorem conversion_round_scaled32 (mantissa : positive) (exponent : Int) (count : Nat)
    (digits : 23 ≤ (posToNat mantissa).log2)
    (minimum : -126 ≤ (posToNat mantissa).log2 + exponent) :
    BinarySingleNaN.binary_round (prec := z24) (emax := z128) .mode_NE false
        (posOfNat (posToNat mantissa * 2 ^ count)) (zOfInt (exponent - count)) =
      BinarySingleNaN.binary_round (prec := z24) (emax := z128) .mode_NE false
        mantissa (zOfInt exponent) := by
  have positive := Nat.mul_pos (posToNat_positive mantissa) (Nat.two_pow_pos count)
  have logScaled :
      (posToNat (posOfNat (posToNat mantissa * 2 ^ count))).log2 =
        (posToNat mantissa).log2 + count := by
    rw [posToNat_posOfNat positive, log2_mul_pow _ _ (Nat.ne_of_gt (posToNat_positive _))]
  have sourceTarget := conversion_fexp32 mantissa exponent minimum
  have scaledTarget := conversion_fexp32
    (posOfNat (posToNat mantissa * 2 ^ count)) (exponent - count)
    (by rw [logScaled]; omega)
  have targetEqual :
      ((posToNat (posOfNat (posToNat mantissa * 2 ^ count))).log2 : Int) +
          (exponent - count) - 23 =
        (posToNat mantissa).log2 + exponent - 23 := by rw [logScaled]; omega
  rw [targetEqual] at scaledTarget
  unfold BinarySingleNaN.binary_round BinarySingleNaN.shl_align_fexp
  rw [sourceTarget, scaledTarget,
    conversion_align_ge _ _ _ (by omega),
    conversion_align_ge _ _ _ (by omega)]
  simp only
  have firstEqual :
      BinarySingleNaN.shr_fexp (prec := z24) (emax := z128)
        (.Zpos (posOfNat (posToNat mantissa * 2 ^ count)))
        (zOfInt (exponent - count)) .loc_Exact =
      BinarySingleNaN.shr_fexp (prec := z24) (emax := z128)
        (.Zpos mantissa) (zOfInt exponent) .loc_Exact := by
    change BinarySingleNaN.shr
      (BinarySingleNaN.shr_record_of_loc
        (.Zpos (posOfNat (posToNat mantissa * 2 ^ count))) .loc_Exact)
      (zOfInt (exponent - count))
      (ZArith.BinInt.Z.sub (BinarySingleNaN.fexp0 z24 z128
        (ZArith.BinInt.Z.add
          (.Zpos (BinarySingleNaN.digits2_pos (posOfNat (posToNat mantissa * 2 ^ count))))
          (zOfInt (exponent - count)))) (zOfInt (exponent - count))) =
      BinarySingleNaN.shr
      (BinarySingleNaN.shr_record_of_loc (.Zpos mantissa) .loc_Exact)
      (zOfInt exponent)
      (ZArith.BinInt.Z.sub (BinarySingleNaN.fexp0 z24 z128
        (ZArith.BinInt.Z.add (.Zpos (BinarySingleNaN.digits2_pos mantissa))
          (zOfInt exponent))) (zOfInt exponent))
    rw [sourceTarget, scaledTarget]
    have sourceCount : ZArith.BinInt.Z.sub
        (zOfInt ((posToNat mantissa).log2 + exponent - 23)) (zOfInt exponent) =
        zOfInt (((posToNat mantissa).log2 - 23 : Nat) : Int) := by
      apply intOfZ_injective
      simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      omega
    have scaledCount : ZArith.BinInt.Z.sub
        (zOfInt ((posToNat mantissa).log2 + exponent - 23)) (zOfInt (exponent - count)) =
        zOfInt ((((posToNat mantissa).log2 - 23) + count : Nat) : Int) := by
      apply intOfZ_injective
      simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      omega
    rw [sourceCount, scaledCount, conversion_shr_count, conversion_shr_count,
      conversion_iter_add, conversion_shift_exact]
    congr 2
    omega
  unfold BinarySingleNaN.binary_round_aux
  rw [firstEqual]

private theorem conversion_lift_equal {prec emax : Z}
    (first second : BinarySingleNaN.binary_float prec emax)
    (firstNotNaN : BinarySingleNaN.is_nan first = false)
    (secondNotNaN : BinarySingleNaN.is_nan second = false)
    (equal : first = second) :
    Binary.BSN2B' first firstNotNaN = Binary.BSN2B' second secondNotNaN := by
  cases equal
  rfl

private theorem conversion_round_canonical32 (mantissa : positive) (exponent : Int)
    (digits : posToNat (BinarySingleNaN.digits2_pos mantissa) = 24)
    (minimum : -149 ≤ exponent) (maximum : exponent ≤ 104) :
    BinarySingleNaN.binary_round (prec := z24) (emax := z128)
      .mode_NE false mantissa (zOfInt exponent) =
        .S754_finite false mantissa (zOfInt exponent) := by
  have target := manual_fexp_canonical32 mantissa (zOfInt exponent) digits
    (by simpa only [intOfZ_zOfInt] using minimum)
  unfold BinarySingleNaN.binary_round BinarySingleNaN.shl_align_fexp
  rw [target, conversion_align_ge _ _ _ (by omega)]
  exact manual_round_aux_canonical32 false mantissa (zOfInt exponent) digits
    (by simpa only [intOfZ_zOfInt] using minimum)
    (by simpa only [intOfZ_zOfInt] using maximum)

set_option maxHeartbeats 1000000 in
private theorem conversion_uint32_normalize
    [certificate : Binary.BinaryNormalizeCertificate z24 z128]
    (mantissa : positive) (bound : (posToNat mantissa).log2 ≤ 31) :
    IEEE754_extra.BofZ (prec := z24) (emax := z128) (.Zpos mantissa) =
      Binary.binary_normalize (prec := z24) (emax := z128)
        (certificate := Binary.binary32_normalize_certificate_proof)
        .mode_NE (.Zpos (posOfNat (posToNat mantissa * 2 ^ (52 - (posToNat mantissa).log2))))
        (zOfInt ((posToNat mantissa).log2 - 52)) false := by
  by_cases small : (posToNat mantissa).log2 < 23
  · rw [manual_BofZ_positive_small32 mantissa small]
    have positive := Nat.mul_pos (posToNat_positive mantissa)
      (Nat.two_pow_pos (23 - (posToNat mantissa).log2))
    have logAligned :
        (posToNat (posOfNat (posToNat mantissa * 2 ^ (23 - (posToNat mantissa).log2)))).log2 = 23 := by
      rw [posToNat_posOfNat positive, log2_mul_pow _ _ (Nat.ne_of_gt (posToNat_positive _))]
      omega
    have scaled := conversion_round_scaled32
      (posOfNat (posToNat mantissa * 2 ^ (23 - (posToNat mantissa).log2)))
      ((posToNat mantissa).log2 - 23) 29 (by rw [logAligned]; omega)
      (by rw [logAligned]; omega)
    have mantissaEqual :
        posOfNat (posToNat (posOfNat
          (posToNat mantissa * 2 ^ (23 - (posToNat mantissa).log2))) * 2 ^ 29) =
        posOfNat (posToNat mantissa * 2 ^ (52 - (posToNat mantissa).log2)) := by
      apply congrArg posOfNat
      rw [posToNat_posOfNat positive, Nat.mul_assoc, ← Nat.pow_add]
      have counts : 23 - (posToNat mantissa).log2 + 29 =
          52 - (posToNat mantissa).log2 := by omega
      rw [counts]
    have exponentEqual : ((posToNat mantissa).log2 : Int) - 23 - (29 : Nat) =
        (posToNat mantissa).log2 - 52 := by omega
    rw [mantissaEqual, exponentEqual, conversion_round_canonical32 _ _
      (manual_normalized_mantissa_digits32 mantissa (by omega)) (by omega) (by omega)] at scaled
    symm
    apply manual_lift_finite
    change BinarySingleNaN.SF2B
      (BinarySingleNaN.binary_round (prec := z24) (emax := z128) .mode_NE false
        (posOfNat (posToNat mantissa * 2 ^ (52 - (posToNat mantissa).log2)))
        (zOfInt ((posToNat mantissa).log2 - 52))) = _
    rw [scaled]
    rfl
  · have rounded := conversion_round_scaled32 mantissa 0
      (52 - (posToNat mantissa).log2) (by omega) (by omega)
    have exponentEqual : (0 : Int) - (52 - (posToNat mantissa).log2 : Nat) =
        (posToNat mantissa).log2 - 52 := by omega
    rw [exponentEqual] at rounded
    change BinarySingleNaN.binary_round (prec := z24) (emax := z128) .mode_NE false
      (posOfNat (posToNat mantissa * 2 ^ (52 - (posToNat mantissa).log2)))
      (zOfInt ((posToNat mantissa).log2 - 52)) =
      BinarySingleNaN.binary_round .mode_NE false mantissa .Z0 at rounded
    unfold IEEE754_extra.BofZ Binary.binary_normalize
    apply conversion_lift_equal
    change BinarySingleNaN.SF2B
      (BinarySingleNaN.binary_round (prec := z24) (emax := z128) .mode_NE false mantissa .Z0) = _
    rw [← rounded]
    rfl

set_option maxRecDepth 100000 in
theorem Float32.of_intu_double
    [binary32_certificate : Binary.BinaryNormalizeCertificate z24 z128]
    [binary64_certificate : Binary.BinaryNormalizeCertificate z53 z1024] :
    Float32.of_intu_doubleStatement := by
  intro n
  unfold Float32.of_intu Float.of_intu Float32.of_double Float.to_single
  cases h : Integers.Int.unsigned n with
  | Z0 =>
      have hzero64 : Binary.BinaryFloatCertificate
          (Binary.binary_normalize (prec := z53) (emax := z1024)
            BinarySingleNaN.mode_NE .Z0 .Z0 false) :=
        Binary.binary_normalize_result_obligation_proof
          BinarySingleNaN.mode_NE .Z0 .Z0 false
      have hzero64decode := conversion_encode64_decode
        (⟨Binary.binary_normalize (prec := z53) (emax := z1024)
          BinarySingleNaN.mode_NE .Z0 .Z0 false, hzero64⟩ :
          Binary.CertifiedBinaryFloat z53 z1024)
      have hzero64nan : isNaN64 (encode64
          (Binary.binary_normalize (prec := z53) (emax := z1024)
            BinarySingleNaN.mode_NE .Z0 .Z0 false)) = false := by
        rw [← conversion_isNaN64_decode]
        rw [hzero64decode]
        rfl
      unfold IEEE754_extra.BofZ
      rw [hzero64decode, hzero64nan]
      simp [Binary.binary_normalize, Binary.BSN2B', BinarySingleNaN.binary_normalize]
      rfl
  | Zpos p =>
      have hu := Integers.Int.unsigned_range_proof n
      rw [h] at hu
      have hp_lt : posToNat p < 2 ^ 32 := by
        have hpz := hu.2
        have hp_pos := posToNat_positive p
        change (posToNat p : Int) < intOfZ Integers.Int.modulus at hpz
        have hmod : intOfZ Integers.Int.modulus = (2 : Int) ^ 32 := by decide
        rw [hmod] at hpz
        have hpz_nat : posToNat p < 2 ^ 32 := by
          exact Int.ofNat_lt.mp hpz
        exact hpz_nat
      have hlog_lt : (posToNat p).log2 < 32 := by
        apply (Nat.log2_lt (Nat.ne_of_gt (posToNat_positive p))).mpr
        exact hp_lt
      have hlog : (posToNat p).log2 ≤ 31 := by omega
      have h64 := manual_BofZ_positive_small64 (certificate := binary64_certificate) p hlog
      rw [h64]
      have hcert : Binary.BinaryFloatCertificate (prec := z53) (emax := z1024)
          (.B754_finite false
            (posOfNat (posToNat p * 2 ^ (52 - (posToNat p).log2)))
            (zOfInt ((posToNat p).log2 - 52))) := by
        change Binary.bounded (prec := z53) (emax := z1024)
          (posOfNat (posToNat p * 2 ^ (52 - (posToNat p).log2)))
          (zOfInt ((posToNat p).log2 - 52)) = true
        apply Bool.and_eq_true_iff.mpr
        constructor
        · change ZArith.Zbool.Zeq_bool _ _ = true
          apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_true
          exact manual_fexp_canonical64
            (posOfNat (posToNat p * 2 ^ (52 - (posToNat p).log2)))
            (zOfInt ((posToNat p).log2 - 52))
            (manual_normalized_mantissa_digits64 p hlog)
            (by rw [intOfZ_zOfInt]; omega)
        · change (if intOfZ (zOfInt ((posToNat p).log2 - 52)) ≤
            intOfZ (ZArith.BinInt.Z.sub z1024 z53) then true else false) = true
          rw [intOfZ_zOfInt]
          have hemax : intOfZ (ZArith.BinInt.Z.sub z1024 z53) = 971 := by decide
          rw [hemax]
          have hbound : ((posToNat p).log2 : Int) - 52 ≤ 971 := by
            have hlog_int : (posToNat p).log2 ≤ (31 : Int) := by
              exact_mod_cast hlog
            omega
          simp [hbound]
      have hdec := conversion_encode64_decode
        (⟨.B754_finite false
          (posOfNat (posToNat p * 2 ^ (52 - (posToNat p).log2)))
          (zOfInt ((posToNat p).log2 - 52)), hcert⟩ :
          Binary.CertifiedBinaryFloat z53 z1024)
      have hnan64 : isNaN64 (encode64
          (⟨.B754_finite false
            (posOfNat (posToNat p * 2 ^ (52 - (posToNat p).log2)))
            (zOfInt ((posToNat p).log2 - 52)), hcert⟩ :
            Binary.CertifiedBinaryFloat z53 z1024).val) = false := by
        rw [← conversion_isNaN64_decode, hdec]
        rfl
      rw [hnan64]
      simp only [Bool.false_eq_true, ↓reduceIte, hdec]
      exact congrArg encode32 (conversion_uint32_normalize p hlog)
  | Zneg p =>
      have hu := Integers.Int.unsigned_range_proof n
      rw [h] at hu
      change 0 ≤ -(posToNat p : Int) ∧ _ at hu
      have hp_pos := posToNat_positive p
      omega

private theorem conversion_binary32_of_bits_roundtrip
    (value : Binary.CertifiedBinaryFloat z24 z128) :
    Bits.binary_float_of_bits_unchecked
      (ZArith.BinInt.Z.of_nat 23) (ZArith.BinInt.Z.of_nat 8)
      (by change (0 : Int) < 23; decide)
      (by change (0 : Int) < 8; decide)
      (by change (24 : Int) < 128; decide)
      (Bits.bits_of_binary_float (ZArith.BinInt.Z.of_nat 23)
        (ZArith.BinInt.Z.of_nat 8) value.1) = value.1 := by
  rcases value with ⟨value, hvalue⟩
  have hsplit := Bits.split_bits_of_binary_float_correct
    (ZArith.BinInt.Z.of_nat 23) (ZArith.BinInt.Z.of_nat 8)
    (by change (0 : Int) < 23; decide)
    (by change (0 : Int) < 8; decide) ⟨value, hvalue⟩
  unfold Bits.binary_float_of_bits_unchecked Bits.binary_float_of_bits_aux
  cases value with
  | B754_zero sign =>
    simp [Bits.split_bits_of_binary_float] at hsplit ⊢
    rw [hsplit]
    rfl
  | B754_infinity sign =>
    simp [Bits.split_bits_of_binary_float] at hsplit ⊢
    rw [hsplit]
    rfl
  | B754_nan sign payload =>
    simp [Bits.split_bits_of_binary_float] at hsplit ⊢
    rw [hsplit]
    have hEq : Bits.Zeq_bool
        (Bits.Zsub (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 8)) Bits.Zone)
        (Bits.Zsub (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 8)) Bits.Zone) = true :=
      CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_true _ _ rfl
    rw [hEq]
    have hzero : Bits.Zeq_bool
        (Bits.Zsub (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 8)) Bits.Zone)
        Bits.Z0 = false :=
      CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false _ _ (by decide)
    rw [hzero]
    simp [Binary.FF2B_unchecked]
    rfl
  | B754_finite sign mantissa exponent =>
    simp [Bits.split_bits_of_binary_float] at hsplit ⊢
    have hparts :
        BinarySingleNaN.canonical_mantissa0 z24 z128 mantissa exponent = true ∧
          ZArith.Zbool.Zle_bool exponent (ZArith.BinInt.Z.sub z128 z24) = true := by
      change (BinarySingleNaN.canonical_mantissa0 z24 z128 mantissa exponent &&
        ZArith.Zbool.Zle_bool exponent (ZArith.BinInt.Z.sub z128 z24)) = true at hvalue
      exact Bool.and_eq_true_iff.mp hvalue
    have hcan := hparts.1
    have hbound := hparts.2
    by_cases hb : Bits.Zle_bool Bits.Z0
        (Bits.Zsub (Bits.Zpos mantissa) (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 23))) = true
    · simp [hb] at hsplit ⊢
      rw [hsplit]
      have hcanEq := ZArith.Zbool.Zeq_bool_eq _ _ hcan
      change ZArith.BinInt.Z.max
          (ZArith.BinInt.Z.sub
            (ZArith.BinInt.Z.add
              (ZArith.BinInt.Z.pos (BinarySingleNaN.digits2_pos mantissa)) exponent) z24)
          (BinarySingleNaN.emin0 z24 z128) = exponent at hcanEq
      have hlowZ := ZArith.BinInt.Z.le_max_r
        (ZArith.BinInt.Z.sub
          (ZArith.BinInt.Z.add
            (ZArith.BinInt.Z.pos (BinarySingleNaN.digits2_pos mantissa)) exponent) z24)
        (BinarySingleNaN.emin0 z24 z128)
      rw [hcanEq] at hlowZ
      have hboundZ := ZArith.Zbool.Zle_bool_imp_le exponent
        (ZArith.BinInt.Z.sub z128 z24) hbound
      have hzadd : ∀ a b : Z,
          intOfZ (ZArith.BinInt.Z.add a b) = intOfZ a + intOfZ b := by
        intro a b
        change intOfZ (zOfInt (intOfZ a + intOfZ b)) = _
        exact intOfZ_zOfInt _
      have hzsub : ∀ a b : Z,
          intOfZ (ZArith.BinInt.Z.sub a b) = intOfZ a - intOfZ b := by
        intro a b
        change intOfZ (zOfInt (intOfZ a - intOfZ b)) = _
        exact intOfZ_zOfInt _
      have hem : intOfZ (Bits.emin (ZArith.BinInt.Z.of_nat 23)
          (ZArith.BinInt.Z.of_nat 8)) = -149 := by decide
      have hemin64 : intOfZ (BinarySingleNaN.emin0 z24 z128) = -149 := by decide
      have hone : intOfZ Bits.Zone = 1 := by decide
      have hshift_formula : intOfZ (Bits.Zadd (Bits.Zsub exponent
          (Bits.emin (ZArith.BinInt.Z.of_nat 23) (ZArith.BinInt.Z.of_nat 8))) Bits.Zone) =
          intOfZ exponent + 150 := by
        rw [hzadd, hzsub, hem, hone]
        omega
      have hshift_pos : 0 <
          intOfZ (Bits.Zadd (Bits.Zsub exponent (Bits.emin (ZArith.BinInt.Z.of_nat 23)
            (ZArith.BinInt.Z.of_nat 8))) Bits.Zone) := by
        rw [hshift_formula]
        change intOfZ (BinarySingleNaN.emin0 z24 z128) ≤ intOfZ exponent at hlowZ
        rw [hemin64] at hlowZ
        change intOfZ exponent ≤ 104 at hboundZ
        omega
      have hshift_lt : intOfZ (Bits.Zadd (Bits.Zsub exponent
          (Bits.emin (ZArith.BinInt.Z.of_nat 23) (ZArith.BinInt.Z.of_nat 8))) Bits.Zone) < 255 := by
        rw [hshift_formula]
        change intOfZ exponent ≤ 104 at hboundZ
        omega
      have hshift_ne_zero : Bits.Zadd (Bits.Zsub exponent
          (Bits.emin (ZArith.BinInt.Z.of_nat 23) (ZArith.BinInt.Z.of_nat 8))) Bits.Zone ≠ Bits.Z0 := by
        intro hz
        have hz' := congrArg intOfZ hz
        rw [hshift_formula] at hz'
        have hzero' : intOfZ Bits.Z0 = 0 := by decide
        rw [hzero'] at hz'
        omega
      have hshift_ne_max : Bits.Zadd (Bits.Zsub exponent
          (Bits.emin (ZArith.BinInt.Z.of_nat 23) (ZArith.BinInt.Z.of_nat 8))) Bits.Zone ≠
          Bits.Zsub (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 8)) Bits.Zone := by
        intro hz
        have hz' := congrArg intOfZ hz
        rw [hshift_formula] at hz'
        have hmax' : intOfZ (Bits.Zsub (Bits.Zpower Bits.Ztwo
            (ZArith.BinInt.Z.of_nat 8)) Bits.Zone) = 255 := by decide
        rw [hmax'] at hz'
        omega
      have hzero : Bits.Zeq_bool
          (Bits.Zadd (Bits.Zsub exponent (Bits.emin (ZArith.BinInt.Z.of_nat 23)
            (ZArith.BinInt.Z.of_nat 8))) Bits.Zone) Bits.Z0 = false :=
        CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false _ _ hshift_ne_zero
      have hmax : Bits.Zeq_bool
          (Bits.Zadd (Bits.Zsub exponent (Bits.emin (ZArith.BinInt.Z.of_nat 23)
            (ZArith.BinInt.Z.of_nat 8))) Bits.Zone)
          (Bits.Zsub (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 8)) Bits.Zone) = false :=
        CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false _ _ hshift_ne_max
      rw [hzero, hmax]
      have hsum : Bits.Zadd (Bits.Zsub (Bits.Zpos mantissa)
          (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 23)))
          (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 23)) = Bits.Zpos mantissa := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        rw [hzadd, hzsub]
        have hpow : intOfZ (Bits.Zpower Bits.Ztwo
            (ZArith.BinInt.Z.of_nat 23)) = 2 ^ 23 := by decide
        rw [hpow]
        omega
      have hexp : Bits.Zsub
          (Bits.Zadd (Bits.Zadd (Bits.Zsub exponent
            (Bits.emin (ZArith.BinInt.Z.of_nat 23) (ZArith.BinInt.Z.of_nat 8))) Bits.Zone)
            (Bits.emin (ZArith.BinInt.Z.of_nat 23) (ZArith.BinInt.Z.of_nat 8))) Bits.Zone = exponent := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        rw [hzsub, hzadd, hzadd, hzsub]
        rw [hem, hone]
        omega
      rw [hsum, hexp]
      rfl
    · simp [hb] at hsplit ⊢
      rw [hsplit]
      have hzeroEq : Bits.Zeq_bool Bits.Z0 Bits.Z0 = true :=
        CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_true _ _ rfl
      rw [hzeroEq]
      have hzsub : ∀ a b : Z,
          intOfZ (ZArith.BinInt.Z.sub a b) = intOfZ a - intOfZ b := by
        intro a b
        change intOfZ (zOfInt (intOfZ a - intOfZ b)) = _
        exact intOfZ_zOfInt _
      have hltbranch : Bits.Zlt (Bits.Zsub (Bits.Zpos mantissa)
          (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 23))) Bits.Z0 := by
        have hs := CompCert4Lean.Flocq.Core.Zaux.Zle_bool_spec Bits.Z0
          (Bits.Zsub (Bits.Zpos mantissa)
            (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 23)))
        have hs' : CompCert4Lean.Flocq.Core.Zaux.Zle_bool_prop Bits.Z0
            (Bits.Zsub (Bits.Zpos mantissa)
              (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 23))) false := by
          simpa [hb] using hs
        cases hs' with
        | Zle_bool_false_ h => exact h
      have hmlt : Bits.Zlt (Bits.Zpos mantissa)
          (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 23)) := by
        change intOfZ (Bits.Zpos mantissa) < intOfZ
          (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 23))
        change intOfZ (Bits.Zsub (Bits.Zpos mantissa)
          (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 23))) < intOfZ Bits.Z0 at hltbranch
        rw [hzsub] at hltbranch
        have hz0 : intOfZ Bits.Z0 = 0 := by decide
        rw [hz0] at hltbranch
        omega
      have hdigit_le : ZArith.BinInt.Z.le (ZArith.BinInt.Z.pos
          (BinarySingleNaN.digits2_pos mantissa))
          (ZArith.BinInt.Z.of_nat 23) := by
        have habs : CompCert4Lean.Flocq.Core.Digits.Zabs (Bits.Zpos mantissa) =
            Bits.Zpos mantissa := by
          apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
          change intOfZ (zOfInt (Int.natAbs (Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat mantissa)))) = _
          rw [intOfZ_zOfInt]
          exact Int.natAbs_of_nonneg (Int.natCast_nonneg _)
        have hstrict : CompCert4Lean.Flocq.Core.Digits.Zlt
            (CompCert4Lean.Flocq.Core.Digits.Zabs (Bits.Zpos mantissa))
            (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 23)) := by
          rw [habs]
          exact hmlt
        have hdigits := CompCert4Lean.Flocq.Core.Digits.Zdigits_le_Zpower
          CompCert4Lean.Flocq.Core.Digits.radix2
          (ZArith.BinInt.Z.of_nat 23) (Bits.Zpos mantissa) hstrict
        have hdigit_eq : ZArith.BinInt.Z.pos (BinarySingleNaN.digits2_pos mantissa) =
            CompCert4Lean.Flocq.Core.Digits.Zdigits
              CompCert4Lean.Flocq.Core.Digits.radix2 (Bits.Zpos mantissa) := by
          exact CompCert4Lean.Flocq.Core.Digits.Zpos_digits2_pos mantissa
        rw [hdigit_eq]
        exact hdigits
      have hcanEq := ZArith.Zbool.Zeq_bool_eq _ _ hcan
      change ZArith.BinInt.Z.max
          (ZArith.BinInt.Z.sub
            (ZArith.BinInt.Z.add
              (ZArith.BinInt.Z.pos (BinarySingleNaN.digits2_pos mantissa)) exponent) z24)
          (BinarySingleNaN.emin0 z24 z128) = exponent at hcanEq
      let first : Z := ZArith.BinInt.Z.sub
        (ZArith.BinInt.Z.add
          (ZArith.BinInt.Z.pos (BinarySingleNaN.digits2_pos mantissa)) exponent) z24
      have hexpEmin : exponent = BinarySingleNaN.emin0 z24 z128 := by
        have hzadd : ∀ a b : Z,
            intOfZ (ZArith.BinInt.Z.add a b) = intOfZ a + intOfZ b := by
          intro a b
          change intOfZ (zOfInt (intOfZ a + intOfZ b)) = _
          exact intOfZ_zOfInt _
        have hzsub : ∀ a b : Z,
            intOfZ (ZArith.BinInt.Z.sub a b) = intOfZ a - intOfZ b := by
          intro a b
          change intOfZ (zOfInt (intOfZ a - intOfZ b)) = _
          exact intOfZ_zOfInt _
        by_cases hfirst : ZArith.BinInt.Z.le
            (BinarySingleNaN.emin0 z24 z128) first
        · have hmax := ZArith.BinInt.Z.max_l first
              (BinarySingleNaN.emin0 z24 z128) hfirst
          have hfirstEq : first = exponent := by
            exact hmax.symm.trans hcanEq
          have hfirstInt := congrArg intOfZ hfirstEq
          change intOfZ (ZArith.BinInt.Z.pos
              (BinarySingleNaN.digits2_pos mantissa)) ≤
            intOfZ (ZArith.BinInt.Z.of_nat 23) at hdigit_le
          have h52 : intOfZ (ZArith.BinInt.Z.of_nat 23) = 23 := by decide
          rw [h52] at hdigit_le
          change intOfZ (ZArith.BinInt.Z.sub
              (ZArith.BinInt.Z.add
                (ZArith.BinInt.Z.pos (BinarySingleNaN.digits2_pos mantissa)) exponent) z24) =
            intOfZ exponent at hfirstInt
          rw [hzsub, hzadd] at hfirstInt
          have hz53 : intOfZ z24 = 24 := by decide
          rw [hz53] at hfirstInt
          omega
        · have hfirst_le : ZArith.BinInt.Z.le first
              (BinarySingleNaN.emin0 z24 z128) := by
            change intOfZ first ≤ intOfZ (BinarySingleNaN.emin0 z24 z128)
            change ¬ intOfZ (BinarySingleNaN.emin0 z24 z128) ≤ intOfZ first at hfirst
            omega
          have hmax := ZArith.BinInt.Z.max_r first
              (BinarySingleNaN.emin0 z24 z128) hfirst_le
          exact (hmax.symm.trans hcanEq).symm
      have hzeroEmin : Bits.emin (ZArith.BinInt.Z.of_nat 23)
          (ZArith.BinInt.Z.of_nat 8) = exponent := by
        change BinarySingleNaN.emin0 z24 z128 = exponent
        exact hexpEmin.symm
      rw [hzeroEmin]
      simp [Binary.FF2B_unchecked]
      rfl

private theorem conversion_encode32_decode (value : Binary.CertifiedBinaryFloat z24 z128) :
    decode32 (encode32 value.1) = value.1 := by
  unfold decode32 encode32
  simp only [BitVec.toNat_ofNat]
  have hround := conversion_binary32_of_bits_roundtrip value
  have hrange := Bits.bits_of_binary_float_range
    (ZArith.BinInt.Z.of_nat 23) (ZArith.BinInt.Z.of_nat 8)
    (by change (0 : Int) < 23; decide)
    (by change (0 : Int) < 8; decide) value
  have hnonneg : Bits.Zle Bits.Z0 (Bits.bits_of_b32 value.1) := by
    exact hrange.1
  have hlt : Bits.Zlt (Bits.bits_of_b32 value.1)
      (Bits.Zpower Bits.Ztwo
        (Bits.Zadd (Bits.Zadd (ZArith.BinInt.Z.of_nat 23)
          (ZArith.BinInt.Z.of_nat 8)) Bits.Zone)) := by
    exact hrange.2
  have hnonnegInt : 0 ≤ intOfZ (Bits.bits_of_b32 value.1) := by
    exact hnonneg
  have hltInt : intOfZ (Bits.bits_of_b32 value.1) < 2 ^ 32 := by
    change intOfZ (Bits.bits_of_b32 value.1) <
      intOfZ (Bits.Zpower Bits.Ztwo
        (Bits.Zadd (Bits.Zadd (ZArith.BinInt.Z.of_nat 23)
          (ZArith.BinInt.Z.of_nat 8)) Bits.Zone)) at hlt
    have hpow : intOfZ (Bits.Zpower Bits.Ztwo
        (Bits.Zadd (Bits.Zadd (ZArith.BinInt.Z.of_nat 23)
          (ZArith.BinInt.Z.of_nat 8)) Bits.Zone)) = 2 ^ 32 := by decide
    rw [hpow] at hlt
    exact hlt
  have hnatlt : ZArith.BinInt.Z.to_nat (Bits.bits_of_b32 value.1) < 2 ^ 32 := by
    change Int.toNat (intOfZ (Bits.bits_of_b32 value.1)) < 2 ^ 32
    exact (Int.toNat_lt hnonnegInt).mpr hltInt
  rw [Nat.mod_eq_of_lt hnatlt]
  rw [ZArith.Znat.Z2Nat.id (Bits.bits_of_b32 value.1) hnonneg]
  simpa [Bits.b32_of_bits_unchecked, Bits.binary_float_of_bits_unchecked,
    Bits.bits_of_b32, Bits.binary32] using hround

private theorem conversion_narrow_model_zero (value : float)
    (hfields : exponent64 value = 0 ∧ fraction64 value = 0)
    (hbit : BitVec.extractLsb 63 63 value.bits = 0#1) :
    decode32 (⟨
      Float.Model.UnpackedFloat.pack Float.Model.Format.binary32
        (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 value.bits)⟩ : float32) =
      Binary.B754_zero (sign64 value) := by
  have hexponent : BitVec.extractLsb 62 52 value.bits = 0#11 := by
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow,
      exponent64] using hfields.1
  have hmantissa : BitVec.extractLsb 51 0 value.bits = 0#52 := by
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.extractLsb_toNat, fraction64] using hfields.2
  have hsign32_eq : sign64 value =
      ((BitVec.extractLsb 63 63 value.bits).toNat == (1 : Nat)) := by
    simp [sign64, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]
  have hsign' : sign64 value = false := by
    rw [hsign32_eq, hbit]
    decide
  have hunpack : Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 value.bits =
      Float.Model.UnpackedFloat.zero
        (Float.Model.UnpackedFloat.Sign.ofBitVec (BitVec.extractLsb 63 63 value.bits)) := by
    simp only [BitVec.extractLsb] at hexponent hmantissa hbit ⊢
    simp [Float.Model.UnpackedFloat.unpack,
    Float.Model.UnpackedFloat.unpackExponent,
    Float.Model.UnpackedFloat.unpackMantissa,
    Float.Model.UnpackedFloat.unpackSign,
    hexponent, hmantissa, hbit]
  have hcert : Binary.BinaryFloatCertificate (prec := z24) (emax := z128)
      (Binary.B754_zero (sign64 value)) := by
    simp [Binary.BinaryFloatCertificate, Binary.B2FF, Binary.valid_binary]
  have hround := conversion_encode32_decode
    (⟨Binary.B754_zero (sign64 value), hcert⟩ : Binary.CertifiedBinaryFloat z24 z128)
  have hbits : (⟨Float.Model.UnpackedFloat.pack Float.Model.Format.binary32
      (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 value.bits)⟩ : float32) =
      encode32 (Binary.B754_zero (sign64 value)) := by
    rw [hunpack]
    apply float32.ext
    apply BitVec.eq_of_toNat_eq
    simp [encode32, Float.Model.UnpackedFloat.pack,
    Float.Model.UnpackedFloat.packedZero,
    Float.Model.UnpackedFloat.packComponents,
    Float.Model.UnpackedFloat.Sign.ofBitVec,
    Float.Model.UnpackedFloat.Sign.toBitVec, hbit,
    Bits.bits_of_b32, Bits.bits_of_binary_float, Bits.join_bits, hsign']
    decide
  rw [hbits]
  exact hround

private theorem conversion_narrow_model_zero_neg (value : float)
    (hfields : exponent64 value = 0 ∧ fraction64 value = 0)
    (hbit : BitVec.extractLsb 63 63 value.bits = 1#1) :
    decode32 (⟨
      Float.Model.UnpackedFloat.pack Float.Model.Format.binary32
        (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 value.bits)⟩ : float32) =
      Binary.B754_zero (sign64 value) := by
  have hexponent : BitVec.extractLsb 62 52 value.bits = 0#11 := by
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow,
      exponent64] using hfields.1
  have hmantissa : BitVec.extractLsb 51 0 value.bits = 0#52 := by
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.extractLsb_toNat, fraction64] using hfields.2
  have hsign32_eq : sign64 value =
      ((BitVec.extractLsb 63 63 value.bits).toNat == (1 : Nat)) := by
    simp [sign64, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]
  have hsign' : sign64 value = true := by
    rw [hsign32_eq, hbit]
    decide
  have hunpack : Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 value.bits =
      Float.Model.UnpackedFloat.zero
        (Float.Model.UnpackedFloat.Sign.ofBitVec (BitVec.extractLsb 63 63 value.bits)) := by
    simp only [BitVec.extractLsb] at hexponent hmantissa hbit ⊢
    simp [Float.Model.UnpackedFloat.unpack,
      Float.Model.UnpackedFloat.unpackExponent,
      Float.Model.UnpackedFloat.unpackMantissa,
      Float.Model.UnpackedFloat.unpackSign,
      hexponent, hmantissa, hbit]
  have hcert : Binary.BinaryFloatCertificate (prec := z24) (emax := z128)
      (Binary.B754_zero (sign64 value)) := by
    simp [Binary.BinaryFloatCertificate, Binary.B2FF, Binary.valid_binary]
  have hround := conversion_encode32_decode
    (⟨Binary.B754_zero (sign64 value), hcert⟩ : Binary.CertifiedBinaryFloat z24 z128)
  have hbits : (⟨Float.Model.UnpackedFloat.pack Float.Model.Format.binary32
      (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 value.bits)⟩ : float32) =
      encode32 (Binary.B754_zero (sign64 value)) := by
    rw [hunpack]
    apply float32.ext
    apply BitVec.eq_of_toNat_eq
    simp [encode32, Float.Model.UnpackedFloat.pack,
      Float.Model.UnpackedFloat.packedZero,
      Float.Model.UnpackedFloat.packComponents,
      Float.Model.UnpackedFloat.Sign.ofBitVec,
      Float.Model.UnpackedFloat.Sign.toBitVec, hbit,
      Bits.bits_of_b32, Bits.bits_of_binary_float, Bits.join_bits, hsign']
    decide
  rw [hbits]
  exact hround

set_option maxRecDepth 100000 in
private theorem conversion_decode64_zero_sign (value : float)
    (hfields : exponent64 value = 0 ∧ fraction64 value = 0) :
    Binary.Bsign (decode64 value) = sign64 value := by
  have hdiv :
      Bits.Zdiv (ZArith.BinInt.Z.of_nat value.bits.toNat)
          (ZArith.BinInt.Z.of_nat (2 ^ 52)) =
        ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 52) :=
    zdiv_nat_f64 _ _ (by decide)
  have hmod :
      Bits.Zmod (ZArith.BinInt.Z.of_nat value.bits.toNat)
          (ZArith.BinInt.Z.of_nat (2 ^ 52)) =
        ZArith.BinInt.Z.of_nat (value.bits.toNat % 2 ^ 52) :=
    zmod_nat_f64 _ _ (by decide)
  have hmodexp :
      Bits.Zmod
          (ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 52))
          (ZArith.BinInt.Z.of_nat (2 ^ 11)) =
        ZArith.BinInt.Z.of_nat ((value.bits.toNat / 2 ^ 52) % 2 ^ 11) :=
    zmod_nat_f64 _ _ (by decide)
  have hexpNat : value.bits.toNat / 2 ^ 52 % 2 ^ 11 = 0 := by
    simpa [exponent64] using hfields.1
  have hmantNat : value.bits.toNat % 2 ^ 52 = 0 := by
    simpa [fraction64] using hfields.2
  have hexp0 : Bits.Zeq_bool
      (ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 52 % 2 ^ 11)) Bits.Z0 = true := by
    rw [hexpNat]
    decide
  have hmant0 : ZArith.BinInt.Z.of_nat (value.bits.toNat % 2 ^ 52) = Bits.Z0 := by
    rw [hmantNat]
    decide
  have hsign32_eq : sign64 value =
      ((BitVec.extractLsb 63 63 value.bits).toNat == (1 : Nat)) := by
    simp [sign64, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]
  have hthreshold :
      Bits.Zle_bool
        (Bits.Zmul (ZArith.BinInt.Z.of_nat (2 ^ 52))
          (ZArith.BinInt.Z.of_nat (2 ^ 11)))
        (ZArith.BinInt.Z.of_nat value.bits.toNat) = sign64 value := by
    have hlt : value.bits.toNat < 2 ^ 64 := value.bits.isLt
    rcases BitVec.eq_zero_or_eq_one (BitVec.extractLsb 63 63 value.bits) with hbit | hbit
    · have hq : value.bits.toNat / 2 ^ 63 % 2 = 0 := by
        have hh := congrArg BitVec.toNat hbit
        simpa [BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow] using hh
      have hn : value.bits.toNat < 2 ^ 63 := by omega
      have hfalse : Bits.Zle_bool
          (Bits.Zmul (ZArith.BinInt.Z.of_nat (2 ^ 52))
            (ZArith.BinInt.Z.of_nat (2 ^ 11)))
          (ZArith.BinInt.Z.of_nat value.bits.toNat) = false := by
        have hprod : Bits.Zmul (ZArith.BinInt.Z.of_nat (2 ^ 52))
            (ZArith.BinInt.Z.of_nat (2 ^ 11)) =
            ZArith.BinInt.Z.of_nat (2 ^ 63) := by decide
        rw [hprod]
        apply CompCert4Lean.Flocq.Core.Zaux.Zle_bool_false
        change intOfZ (ZArith.BinInt.Z.of_nat value.bits.toNat) <
          intOfZ (ZArith.BinInt.Z.of_nat (2 ^ 63))
        simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
        exact Int.ofNat_lt.mpr hn
      rw [hfalse]
      rw [hsign32_eq, hbit]
      decide
    · have hq : value.bits.toNat / 2 ^ 63 % 2 = 1 := by
        have hh := congrArg BitVec.toNat hbit
        simpa [BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow] using hh
      have hn : 2 ^ 63 ≤ value.bits.toNat := by omega
      have htrue : Bits.Zle_bool
          (Bits.Zmul (ZArith.BinInt.Z.of_nat (2 ^ 52))
            (ZArith.BinInt.Z.of_nat (2 ^ 11)))
          (ZArith.BinInt.Z.of_nat value.bits.toNat) = true := by
        have hprod : Bits.Zmul (ZArith.BinInt.Z.of_nat (2 ^ 52))
            (ZArith.BinInt.Z.of_nat (2 ^ 11)) =
            ZArith.BinInt.Z.of_nat (2 ^ 63) := by decide
        rw [hprod]
        apply CompCert4Lean.Flocq.Core.Zaux.Zle_bool_true
        change intOfZ (ZArith.BinInt.Z.of_nat (2 ^ 63)) ≤
          intOfZ (ZArith.BinInt.Z.of_nat value.bits.toNat)
        simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
        exact Int.ofNat_le.mpr hn
      rw [htrue]
      rw [hsign32_eq, hbit]
      decide
  unfold Binary.Bsign decode64
  unfold Bits.b64_of_bits_unchecked Bits.binary_float_of_bits_unchecked
    Bits.binary_float_of_bits_aux Bits.split_bits
  simp only []
  rw [show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 52) =
        ZArith.BinInt.Z.of_nat (2 ^ 52) by decide,
    show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 11) =
        ZArith.BinInt.Z.of_nat (2 ^ 11) by decide,
    hdiv, hmod, hmodexp]
  simp [Binary.FF2B_unchecked, hexp0, hmant0, hthreshold,
    Binary.Bsign]

set_option maxRecDepth 100000 in
private theorem conversion_decode64_infinity_sign (value : float)
    (hfields : exponent64 value = 2 ^ 11 - 1 ∧ fraction64 value = 0) :
    Binary.Bsign (decode64 value) = sign64 value := by
  have hdiv :
      Bits.Zdiv (ZArith.BinInt.Z.of_nat value.bits.toNat)
          (ZArith.BinInt.Z.of_nat (2 ^ 52)) =
        ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 52) :=
    zdiv_nat_f64 _ _ (by decide)
  have hmod :
      Bits.Zmod (ZArith.BinInt.Z.of_nat value.bits.toNat)
          (ZArith.BinInt.Z.of_nat (2 ^ 52)) =
        ZArith.BinInt.Z.of_nat (value.bits.toNat % 2 ^ 52) :=
    zmod_nat_f64 _ _ (by decide)
  have hmodexp :
      Bits.Zmod
          (ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 52))
          (ZArith.BinInt.Z.of_nat (2 ^ 11)) =
        ZArith.BinInt.Z.of_nat ((value.bits.toNat / 2 ^ 52) % 2 ^ 11) :=
    zmod_nat_f64 _ _ (by decide)
  have hexpNat : value.bits.toNat / 2 ^ 52 % 2 ^ 11 = 2 ^ 11 - 1 := by
    simpa [exponent64] using hfields.1
  have hmantNat : value.bits.toNat % 2 ^ 52 = 0 := by
    simpa [fraction64] using hfields.2
  have hexp0 : Bits.Zeq_bool
      (ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 52 % 2 ^ 11)) Bits.Z0 = false := by
    rw [hexpNat]
    decide
  have hmax : Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 11)) Bits.Zone =
      ZArith.BinInt.Z.of_nat (2 ^ 11 - 1) := by decide
  have hexpmax : Bits.Zeq_bool
      (ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 52 % 2 ^ 11))
      (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 11)) Bits.Zone) = true := by
    rw [hexpNat, hmax]
    decide
  have hmant0 : ZArith.BinInt.Z.of_nat (value.bits.toNat % 2 ^ 52) = Bits.Z0 := by
    rw [hmantNat]
    decide
  have hsign32_eq : sign64 value =
      ((BitVec.extractLsb 63 63 value.bits).toNat == (1 : Nat)) := by
    simp [sign64, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]
  have hthreshold :
      Bits.Zle_bool
        (Bits.Zmul (ZArith.BinInt.Z.of_nat (2 ^ 52))
          (ZArith.BinInt.Z.of_nat (2 ^ 11)))
        (ZArith.BinInt.Z.of_nat value.bits.toNat) = sign64 value := by
    have hlt : value.bits.toNat < 2 ^ 64 := value.bits.isLt
    rcases BitVec.eq_zero_or_eq_one (BitVec.extractLsb 63 63 value.bits) with hbit | hbit
    · have hq : value.bits.toNat / 2 ^ 63 % 2 = 0 := by
        have hh := congrArg BitVec.toNat hbit
        simpa [BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow] using hh
      have hn : value.bits.toNat < 2 ^ 63 := by omega
      have hfalse : Bits.Zle_bool
          (Bits.Zmul (ZArith.BinInt.Z.of_nat (2 ^ 52))
            (ZArith.BinInt.Z.of_nat (2 ^ 11)))
          (ZArith.BinInt.Z.of_nat value.bits.toNat) = false := by
        have hprod : Bits.Zmul (ZArith.BinInt.Z.of_nat (2 ^ 52))
            (ZArith.BinInt.Z.of_nat (2 ^ 11)) =
            ZArith.BinInt.Z.of_nat (2 ^ 63) := by decide
        rw [hprod]
        apply CompCert4Lean.Flocq.Core.Zaux.Zle_bool_false
        change intOfZ (ZArith.BinInt.Z.of_nat value.bits.toNat) <
          intOfZ (ZArith.BinInt.Z.of_nat (2 ^ 63))
        simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
        exact Int.ofNat_lt.mpr hn
      rw [hfalse, hsign32_eq, hbit]
      decide
    · have hq : value.bits.toNat / 2 ^ 63 % 2 = 1 := by
        have hh := congrArg BitVec.toNat hbit
        simpa [BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow] using hh
      have hn : 2 ^ 63 ≤ value.bits.toNat := by omega
      have htrue : Bits.Zle_bool
          (Bits.Zmul (ZArith.BinInt.Z.of_nat (2 ^ 52))
            (ZArith.BinInt.Z.of_nat (2 ^ 11)))
          (ZArith.BinInt.Z.of_nat value.bits.toNat) = true := by
        have hprod : Bits.Zmul (ZArith.BinInt.Z.of_nat (2 ^ 52))
            (ZArith.BinInt.Z.of_nat (2 ^ 11)) =
            ZArith.BinInt.Z.of_nat (2 ^ 63) := by decide
        rw [hprod]
        apply CompCert4Lean.Flocq.Core.Zaux.Zle_bool_true
        change intOfZ (ZArith.BinInt.Z.of_nat (2 ^ 63)) ≤
          intOfZ (ZArith.BinInt.Z.of_nat value.bits.toNat)
        simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
        exact Int.ofNat_le.mpr hn
      rw [htrue, hsign32_eq, hbit]
      decide
  unfold Binary.Bsign decode64
  unfold Bits.b64_of_bits_unchecked Bits.binary_float_of_bits_unchecked
    Bits.binary_float_of_bits_aux Bits.split_bits
  simp only []
  rw [show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 52) =
        ZArith.BinInt.Z.of_nat (2 ^ 52) by decide,
    show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 11) =
        ZArith.BinInt.Z.of_nat (2 ^ 11) by decide,
    hdiv, hmod, hmodexp]
  simp [Binary.FF2B_unchecked, hexp0, hexpmax, hmant0, hthreshold,
    Binary.Bsign]

private theorem conversion_narrow_model_infinity (value : float)
    (hfields : exponent64 value = 2 ^ 11 - 1 ∧ fraction64 value = 0)
    (hbit : BitVec.extractLsb 63 63 value.bits = 0#1 ∨
      BitVec.extractLsb 63 63 value.bits = 1#1) :
    decode32 (⟨
      Float.Model.UnpackedFloat.pack Float.Model.Format.binary32
        (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 value.bits)⟩ : float32) =
      Binary.B754_infinity (sign64 value) := by
  have hexponent : BitVec.extractLsb 62 52 value.bits = (2047#11) := by
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow,
      exponent64] using hfields.1
  have hmantissa : BitVec.extractLsb 51 0 value.bits = 0#52 := by
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.extractLsb_toNat, fraction64] using hfields.2
  have hsign32_eq : sign64 value =
      ((BitVec.extractLsb 63 63 value.bits).toNat == (1 : Nat)) := by
    simp [sign64, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]
  have hunpack : Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 value.bits =
      Float.Model.UnpackedFloat.infinity
        (Float.Model.UnpackedFloat.Sign.ofBitVec (BitVec.extractLsb 63 63 value.bits)) := by
    simp only [BitVec.extractLsb] at hexponent hmantissa hbit ⊢
    simp [Float.Model.UnpackedFloat.unpack,
      Float.Model.UnpackedFloat.unpackExponent,
      Float.Model.UnpackedFloat.unpackMantissa,
      Float.Model.UnpackedFloat.unpackSign,
      hexponent, hmantissa, hbit]
  have hcert : Binary.BinaryFloatCertificate (prec := z24) (emax := z128)
      (Binary.B754_infinity (sign64 value)) := by
    simp [Binary.BinaryFloatCertificate, Binary.B2FF, Binary.valid_binary]
  have hround := conversion_encode32_decode
    (⟨Binary.B754_infinity (sign64 value), hcert⟩ : Binary.CertifiedBinaryFloat z24 z128)
  have hbits : (⟨Float.Model.UnpackedFloat.pack Float.Model.Format.binary32
      (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 value.bits)⟩ : float32) =
      encode32 (Binary.B754_infinity (sign64 value)) := by
    rw [hunpack]
    apply float32.ext
    apply BitVec.eq_of_toNat_eq
    rcases hbit with hbit | hbit
    · simp [encode32, Float.Model.UnpackedFloat.pack,
        Float.Model.UnpackedFloat.packedInfinity,
        Float.Model.UnpackedFloat.packComponents,
        Float.Model.UnpackedFloat.Sign.ofBitVec,
        Float.Model.UnpackedFloat.Sign.toBitVec, hbit,
        Bits.bits_of_b32, Bits.bits_of_binary_float, Bits.join_bits, hsign32_eq]
      decide
    · simp [encode32, Float.Model.UnpackedFloat.pack,
        Float.Model.UnpackedFloat.packedInfinity,
        Float.Model.UnpackedFloat.packComponents,
        Float.Model.UnpackedFloat.Sign.ofBitVec,
        Float.Model.UnpackedFloat.Sign.toBitVec, hbit,
        Bits.bits_of_b32, Bits.bits_of_binary_float, Bits.join_bits, hsign32_eq]
      decide
  rw [hbits]
  exact hround
set_option maxRecDepth 100000 in
private theorem conversion_to_single_bconv
    (value : float)
    (conv_nan : Bits.binary64 →
      IEEE754_extra.NaNResult z24 z128)
    (hnotnan : Binary.is_nan (decode64 value) = false) :
    decode32 (Float.to_single value) =
      IEEE754_extra.Bconv conv_nan BinarySingleNaN.mode_NE (decode64 value) := by
  have hnan : isNaN64 value = false := by
    rw [← conversion_isNaN64_decode value]
    exact hnotnan
  cases hvalue : decode64 value with
  | B754_zero sign =>
      have hvalue0 := hvalue
      have hfields : exponent64 value = 0 ∧ fraction64 value = 0 := by
        have hdiv :
            Bits.Zdiv (ZArith.BinInt.Z.of_nat value.bits.toNat)
                (ZArith.BinInt.Z.of_nat (2 ^ 52)) =
              ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 52) :=
          zdiv_nat_f64 _ _ (by decide)
        have hmod :
            Bits.Zmod (ZArith.BinInt.Z.of_nat value.bits.toNat)
                (ZArith.BinInt.Z.of_nat (2 ^ 52)) =
              ZArith.BinInt.Z.of_nat (value.bits.toNat % 2 ^ 52) :=
          zmod_nat_f64 _ _ (by decide)
        have hmodexp :
            Bits.Zmod
                (ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 52))
                (ZArith.BinInt.Z.of_nat (2 ^ 11)) =
              ZArith.BinInt.Z.of_nat ((value.bits.toNat / 2 ^ 52) % 2 ^ 11) :=
          zmod_nat_f64 _ _ (by decide)
        have hraw := hvalue
        unfold decode64 at hraw
        unfold Bits.b64_of_bits_unchecked Bits.binary_float_of_bits_unchecked
          Bits.binary_float_of_bits_aux Bits.split_bits at hraw
        simp only [] at hraw
        rw [show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 52) =
              ZArith.BinInt.Z.of_nat (2 ^ 52) by decide,
          show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 11) =
              ZArith.BinInt.Z.of_nat (2 ^ 11) by decide,
          hdiv, hmod, hmodexp] at hraw
        let exponent := value.bits.toNat / 4503599627370496 % 2048
        let mantissa := value.bits.toNat % 4503599627370496
        have hzero : ZArith.BinInt.Z.of_nat 0 = Bits.Z0 := by decide
        have zeq_true {a b : Nat} (h : a = b) :
            Bits.Zeq_bool (ZArith.BinInt.Z.of_nat a)
              (ZArith.BinInt.Z.of_nat b) = true := by
          apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_true
          simpa [h]
        have zeq_false {a b : Nat} (h : a ≠ b) :
            Bits.Zeq_bool (ZArith.BinInt.Z.of_nat a)
              (ZArith.BinInt.Z.of_nat b) = false := by
          apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false
          intro hab
          have hi := congrArg intOfZ hab
          simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hi
          exact h (Int.ofNat_inj.mp hi)
        by_cases he0 : exponent = 0
        · by_cases hm0 : mantissa = 0
          · exact ⟨he0, hm0⟩
          · have hmpos : 0 < mantissa := Nat.pos_of_ne_zero hm0
            have hmz : ZArith.BinInt.Z.of_nat mantissa =
                ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat mantissa) := by
              apply intOfZ_injective
              simp only [ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.pos,
                intOfZ_zOfInt]
              exact congrArg Int.ofNat (posToNat_posOfNat hmpos).symm
            have hexp0 : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent) Bits.Z0 = true :=
              zeq_true he0
            have hexpMax : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent)
                (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 11)) Bits.Zone) = false := by
              apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false
              intro h
              have hi := congrArg intOfZ h
              have hleft : intOfZ (ZArith.BinInt.Z.of_nat exponent) =
                  (exponent : Int) := by
                simp [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
              have hright : intOfZ
                  (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 11)) Bits.Zone) = 2047 := by decide
              rw [hleft, hright] at hi
              omega
            simp [Binary.FF2B_unchecked, exponent, mantissa, hexp0, hexpMax, hmz, he0, hm0] at hraw
            cases hraw
        · have hexp0 : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent) Bits.Z0 = false :=
              zeq_false he0
          by_cases heMax : exponent = 2 ^ 11 - 1
          · by_cases hm0 : mantissa = 0
            · have hmz : ZArith.BinInt.Z.of_nat mantissa = Bits.Z0 := by
                rw [hm0]
                decide
              have hexpMax : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent)
                  (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 11)) Bits.Zone) = true := by
                apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_true
                simpa [heMax] using (show ZArith.BinInt.Z.of_nat (2 ^ 11 - 1) =
                  Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 11)) Bits.Zone by decide)
              simp [Binary.FF2B_unchecked, exponent, mantissa, hexp0, hexpMax, hmz, heMax, hm0] at hraw
              cases hraw
            · have hmpos : 0 < mantissa := Nat.pos_of_ne_zero hm0
              have hmz : ZArith.BinInt.Z.of_nat mantissa =
                  ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat mantissa) := by
                apply intOfZ_injective
                simp only [ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.pos,
                  intOfZ_zOfInt]
                exact congrArg Int.ofNat (posToNat_posOfNat hmpos).symm
              have hexpMax : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent)
                  (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 11)) Bits.Zone) = true := by
                apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_true
                simpa [heMax] using (show ZArith.BinInt.Z.of_nat (2 ^ 11 - 1) =
                  Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 11)) Bits.Zone by decide)
              simp [Binary.FF2B_unchecked, exponent, mantissa, hexp0, hexpMax, hmz, heMax, hm0] at hraw
              cases hraw
          · have hexpMax : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent)
                (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 11)) Bits.Zone) = false := by
              apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false
              intro h
              have hi := congrArg intOfZ h
              have hleft : intOfZ (ZArith.BinInt.Z.of_nat exponent) =
                  (exponent : Int) := by
                simp [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
              have hright : intOfZ
                  (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 11)) Bits.Zone) = 2047 := by decide
              rw [hleft, hright] at hi
              omega
            simp [Binary.FF2B_unchecked, exponent, mantissa, hexp0, hexpMax, heMax] at hraw
            cases hsum : Bits.Zadd
                (ZArith.BinInt.Z.of_nat (value.bits.toNat % 4503599627370496))
                (ZArith.BinInt.Z.of_nat 4503599627370496) <;>
              simp [hsum] at hraw
      have hsign32_eq : sign64 value =
          ((BitVec.extractLsb 63 63 value.bits).toNat == (1 : Nat)) := by
        simp [sign64, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]
      rcases BitVec.eq_zero_or_eq_one (BitVec.extractLsb 63 63 value.bits) with hbit | hbit
      · have hz := conversion_narrow_model_zero value hfields hbit
        have hsignraw := congrArg Binary.Bsign hvalue0
        have hdecode_sign := conversion_decode64_zero_sign value hfields
        have hsignraw' : Binary.Bsign (decode64 value) = sign := by
          simpa [Binary.Bsign] using hsignraw
        have hsign : sign64 value = sign := by
          exact hdecode_sign.symm.trans hsignraw'
        simp only [Float.to_single, hnan, hvalue0, Bool.false_eq_true, ↓reduceIte]
        simp only [IEEE754_extra.Bconv]
        rw [hsign] at hz
        exact hz
      · have hz := conversion_narrow_model_zero_neg value hfields hbit
        have hsignraw := congrArg Binary.Bsign hvalue0
        have hdecode_sign := conversion_decode64_zero_sign value hfields
        have hsignraw' : Binary.Bsign (decode64 value) = sign := by
          simpa [Binary.Bsign] using hsignraw
        have hsign : sign64 value = sign := by
          exact hdecode_sign.symm.trans hsignraw'
        simp only [Float.to_single, hnan, hvalue0, Bool.false_eq_true, ↓reduceIte]
        simp only [IEEE754_extra.Bconv]
        rw [hsign] at hz
        exact hz
  | B754_infinity sign =>
      have hvalue0 := hvalue
      have hfields : exponent64 value = 2 ^ 11 - 1 ∧ fraction64 value = 0 := by
        have hdiv :
            Bits.Zdiv (ZArith.BinInt.Z.of_nat value.bits.toNat)
                (ZArith.BinInt.Z.of_nat (2 ^ 52)) =
              ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 52) :=
          zdiv_nat_f64 _ _ (by decide)
        have hmod :
            Bits.Zmod (ZArith.BinInt.Z.of_nat value.bits.toNat)
                (ZArith.BinInt.Z.of_nat (2 ^ 52)) =
              ZArith.BinInt.Z.of_nat (value.bits.toNat % 2 ^ 52) :=
          zmod_nat_f64 _ _ (by decide)
        have hmodexp :
            Bits.Zmod
                (ZArith.BinInt.Z.of_nat (value.bits.toNat / 2 ^ 52))
                (ZArith.BinInt.Z.of_nat (2 ^ 11)) =
              ZArith.BinInt.Z.of_nat ((value.bits.toNat / 2 ^ 52) % 2 ^ 11) :=
          zmod_nat_f64 _ _ (by decide)
        have hraw := hvalue
        unfold decode64 at hraw
        unfold Bits.b64_of_bits_unchecked Bits.binary_float_of_bits_unchecked
          Bits.binary_float_of_bits_aux Bits.split_bits at hraw
        simp only [] at hraw
        rw [show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 52) =
              ZArith.BinInt.Z.of_nat (2 ^ 52) by decide,
          show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 11) =
              ZArith.BinInt.Z.of_nat (2 ^ 11) by decide,
          hdiv, hmod, hmodexp] at hraw
        have hzero : ZArith.BinInt.Z.of_nat 0 = Bits.Z0 := by decide
        have hmax : Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 11)) Bits.Zone =
            ZArith.BinInt.Z.of_nat (2 ^ 11 - 1) := by decide
        let exponent := value.bits.toNat / 4503599627370496 % 2048
        let mantissa := value.bits.toNat % 4503599627370496
        have zeq_true {a b : Nat} (h : a = b) :
            Bits.Zeq_bool (ZArith.BinInt.Z.of_nat a)
              (ZArith.BinInt.Z.of_nat b) = true := by
          apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_true
          simpa [h]
        have zeq_false {a b : Nat} (h : a ≠ b) :
            Bits.Zeq_bool (ZArith.BinInt.Z.of_nat a)
              (ZArith.BinInt.Z.of_nat b) = false := by
          apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false
          intro hab
          have hi := congrArg intOfZ hab
          simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hi
          exact h (Int.ofNat_inj.mp hi)
        have hmax_nat : 2047 = 2 ^ 11 - 1 := by decide
        by_cases he0 : exponent = 0
        · have hexp0 := zeq_true he0
          have hexpmax : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent)
              (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 11)) Bits.Zone) = false := by
            rw [hmax]
            exact zeq_false (by omega)
          have hexpmaxraw : Bits.Zeq_bool
              (ZArith.BinInt.Z.of_nat (value.bits.toNat / 4503599627370496 % 2048))
              (ZArith.BinInt.Z.of_nat 2047) = false := by
            simpa [exponent] using (show Bits.Zeq_bool
              (ZArith.BinInt.Z.of_nat exponent) (ZArith.BinInt.Z.of_nat 2047) = false by
              exact zeq_false (by omega))
          by_cases hm0 : mantissa = 0
          · have hmant := zeq_true hm0
            simp [Binary.FF2B_unchecked, exponent, mantissa, hzero, hmax,
              hexp0, hexpmax, hexpmaxraw, hmant, he0, hm0] at hraw
            cases hraw
          · have hmpos : 0 < mantissa := Nat.pos_of_ne_zero hm0
            have hmz : ZArith.BinInt.Z.of_nat mantissa =
                ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat mantissa) := by
              apply intOfZ_injective
              simp only [ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.pos, intOfZ_zOfInt]
              exact congrArg Int.ofNat (posToNat_posOfNat hmpos).symm
            have hmant := zeq_false hm0
            simp [Binary.FF2B_unchecked, exponent, mantissa, hzero, hmax,
              hexp0, hexpmax, hmant, hmz, he0, hm0] at hraw
            cases hraw
        · have hexp0 := zeq_false he0
          by_cases hemax : exponent = 2 ^ 11 - 1
          · have hexpmax : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent)
                (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 11)) Bits.Zone) = true := by
              apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_true
              simpa [hemax] using (show ZArith.BinInt.Z.of_nat (2 ^ 11 - 1) =
                Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 11)) Bits.Zone by decide)
            have hexpmaxraw : Bits.Zeq_bool
                (ZArith.BinInt.Z.of_nat (value.bits.toNat / 4503599627370496 % 2048))
                (ZArith.BinInt.Z.of_nat 2047) = true := by
              simpa [exponent] using (show Bits.Zeq_bool
                (ZArith.BinInt.Z.of_nat exponent) (ZArith.BinInt.Z.of_nat 2047) = true by
                exact zeq_true hemax)
            by_cases hm0 : mantissa = 0
            · constructor
              · simpa [exponent64, exponent] using hemax
              · simpa [fraction64, mantissa] using hm0
            · have hmpos : 0 < mantissa := Nat.pos_of_ne_zero hm0
              have hmz : ZArith.BinInt.Z.of_nat mantissa =
                  ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat mantissa) := by
                apply intOfZ_injective
                simp only [ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.pos, intOfZ_zOfInt]
                exact congrArg Int.ofNat (posToNat_posOfNat hmpos).symm
              have hmant := zeq_false hm0
              simp [Binary.FF2B_unchecked, exponent, mantissa, hzero, hmax,
                hexp0, hexpmax, hexpmaxraw, hmz, hemax, hm0, hmant] at hraw
              cases hraw
          · have hexpmax : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat exponent)
                (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 11)) Bits.Zone) = false := by
              apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_false
              intro h
              have hi := congrArg intOfZ h
              have hleft : intOfZ (ZArith.BinInt.Z.of_nat exponent) =
                  (exponent : Int) := by
                simp [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
              have hright : intOfZ
                  (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 11)) Bits.Zone) = 2047 := by decide
              rw [hleft, hright] at hi
              omega
            by_cases hm0 : mantissa = 0
            · have hmz : ZArith.BinInt.Z.of_nat mantissa = Bits.Z0 := by
                rw [hm0]
                decide
              have hexp0raw : Bits.Zeq_bool
                  (ZArith.BinInt.Z.of_nat (value.bits.toNat / 4503599627370496 % 2048)) Bits.Z0 = false := by
                simpa [exponent, hzero] using hexp0
              have hexpmaxraw : Bits.Zeq_bool
                  (ZArith.BinInt.Z.of_nat (value.bits.toNat / 4503599627370496 % 2048))
                  (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 11)) Bits.Zone) = false := by
                simpa [exponent, hmax] using hexpmax
              have hexpmaxraw255 : Bits.Zeq_bool
                  (ZArith.BinInt.Z.of_nat (value.bits.toNat / 4503599627370496 % 2048))
                  (ZArith.BinInt.Z.of_nat 2047) = false := by
                simpa [exponent] using (show Bits.Zeq_bool
                  (ZArith.BinInt.Z.of_nat exponent) (ZArith.BinInt.Z.of_nat 2047) = false by
                  exact zeq_false (by omega))
              have hsum0 : Bits.Zadd Bits.Z0 (ZArith.BinInt.Z.of_nat 4503599627370496) =
                  ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat 4503599627370496) := by decide
              simp [Binary.FF2B_unchecked, mantissa, hm0, hzero, hmax, hexp0raw, hexpmaxraw,
                hexpmaxraw255,
                hmz, hsum0] at hraw
            · have hmpos : 0 < mantissa := Nat.pos_of_ne_zero hm0
              have hmz : ZArith.BinInt.Z.of_nat mantissa =
                  ZArith.BinInt.Z.pos (PArith.BinPos.Pos.of_nat mantissa) := by
                apply intOfZ_injective
                simp only [ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.pos, intOfZ_zOfInt]
                exact congrArg Int.ofNat (posToNat_posOfNat hmpos).symm
              have hexp0raw : Bits.Zeq_bool
                  (ZArith.BinInt.Z.of_nat (value.bits.toNat / 4503599627370496 % 2048)) Bits.Z0 = false := by
                simpa [exponent, hzero] using hexp0
              have hexpmaxraw : Bits.Zeq_bool
                  (ZArith.BinInt.Z.of_nat (value.bits.toNat / 4503599627370496 % 2048))
                  (Bits.Zsub (ZArith.BinInt.Z.of_nat (2 ^ 11)) Bits.Zone) = false := by
                simpa [exponent, hmax] using hexpmax
              have hexpmaxraw255 : Bits.Zeq_bool
                  (ZArith.BinInt.Z.of_nat (value.bits.toNat / 4503599627370496 % 2048))
                  (ZArith.BinInt.Z.of_nat 2047) = false := by
                simpa [exponent] using (show Bits.Zeq_bool
                  (ZArith.BinInt.Z.of_nat exponent) (ZArith.BinInt.Z.of_nat 2047) = false by
                  exact zeq_false (by omega))
              cases hsum : Bits.Zadd
                  (ZArith.BinInt.Z.of_nat (value.bits.toNat % 4503599627370496))
                  (ZArith.BinInt.Z.of_nat 4503599627370496) <;>
                simp [Binary.FF2B_unchecked, hzero, hmax,
                  hexp0raw, hexpmaxraw, hexpmaxraw255, hmz, hsum] at hraw <;>
                cases hraw
      have hbit : BitVec.extractLsb 63 63 value.bits = 0#1 ∨
          BitVec.extractLsb 63 63 value.bits = 1#1 :=
        BitVec.eq_zero_or_eq_one _
      have hz := conversion_narrow_model_infinity value hfields hbit
      have hsignraw := congrArg Binary.Bsign hvalue0
      have hdecode_sign := conversion_decode64_infinity_sign value hfields
      have hsignraw' : Binary.Bsign (decode64 value) = sign := by
        simpa [Binary.Bsign] using hsignraw
      have hsign : sign64 value = sign := by
        exact hdecode_sign.symm.trans hsignraw'
      simp only [Float.to_single, hnan, hvalue0, Bool.false_eq_true, ↓reduceIte]
      simp only [IEEE754_extra.Bconv]
      rw [hsign] at hz
      exact hz
  | B754_nan sign payload =>
      rw [hvalue] at hnotnan
      simp [Binary.is_nan] at hnotnan
  | B754_finite sign mantissa exponent =>
      simp only [Float.to_single, hnan, hvalue, Bool.false_eq_true, ↓reduceIte]
      have hnorm := Binary.binary_normalize_result_obligation_proof
        (prec := z24) (emax := z128) BinarySingleNaN.mode_NE
        (CompCert4Lean.Flocq.Core.Zaux.cond_Zopp sign (.Zpos mantissa)) exponent sign
      have hround := conversion_encode32_decode
        (⟨Binary.binary_normalize BinarySingleNaN.mode_NE
          (CompCert4Lean.Flocq.Core.Zaux.cond_Zopp sign (.Zpos mantissa)) exponent sign,
          hnorm⟩ : Binary.CertifiedBinaryFloat z24 z128)
      simpa [IEEE754_extra.Bconv] using hround

private theorem conversion_build_nan_eq {precision maximum : Z}
    (value : Binary.binary_float precision maximum) (isNaN : Binary.is_nan value = true) :
    Binary.build_nan ⟨value, isNaN⟩ = value := by
  cases value <;> first | rfl | contradiction

private theorem conversion_of_single_correspondence (value : float32) :
    decode64 (Float.of_single value) =
      IEEE754_extra.Bconv (prec1 := z24) (emax1 := z128) (prec2 := z53) (emax2 := z1024)
        (fun _ => ⟨decode64 (Float.of_single_nan value),
          Float.of_single_nan_result_obligation_proof value (conversion_decode32_valid value)⟩)
        BinarySingleNaN.mode_NE (decode32 value) := by
  cases isNaN : Binary.is_nan (decode32 value) with
  | false => exact conversion_of_single_bconv value _ isNaN
  | true =>
      have rawNaN : isNaN32 value = true := by
        rw [← conversion_isNaN32_decode, isNaN]
      rw [Float.of_single, rawNaN]
      simp only [↓reduceIte]
      cases decoded : decode32 value <;>
        simp only [decoded, Binary.is_nan] at isNaN
      all_goals first | contradiction | skip
      change _ = Binary.build_nan _
      exact (conversion_build_nan_eq _ _).symm

private theorem conversion_to_single_correspondence (value : float) :
    decode32 (Float.to_single value) =
      IEEE754_extra.Bconv (prec1 := z53) (emax1 := z1024) (prec2 := z24) (emax2 := z128)
        (fun _ => ⟨decode32 (Float.to_single_nan value),
          Float.to_single_nan_result_obligation_proof value (conversion_decode64_valid value)⟩)
        BinarySingleNaN.mode_NE (decode64 value) := by
  cases isNaN : Binary.is_nan (decode64 value) with
  | false => exact conversion_to_single_bconv value _ isNaN
  | true =>
      have rawNaN : isNaN64 value = true := by
        rw [← conversion_isNaN64_decode, isNaN]
      rw [Float.to_single, rawNaN]
      simp only [↓reduceIte]
      cases decoded : decode64 value <;>
        simp only [decoded, Binary.is_nan] at isNaN
      all_goals first | contradiction | skip
      change _ = Binary.build_nan _
      exact (conversion_build_nan_eq _ _).symm

private theorem conversion_widen_exact
    (ctx : CompCert4Lean.Foundation.FlocqReal.ExactRealContext)
    (value : float32) (finite : Binary.is_finite (decode32 value) = true) :
    Binary.Exact.B2R ctx (decode64 (Float.of_single value)) = Binary.Exact.B2R ctx (decode32 value) ∧
      Binary.is_finite (decode64 (Float.of_single value)) = true ∧
      Binary.Bsign (decode64 (Float.of_single value)) = Binary.Bsign (decode32 value) := by
  rw [conversion_of_single_correspondence]
  exact IEEE754_extra.Bconv_widen_exact (prec1 := z24) (emax1 := z128)
    (prec2 := z53) (emax2 := z1024) ctx
    (by change (24 : Int) ≤ 53; decide) (by change (128 : Int) ≤ 1024; decide) _
    BinarySingleNaN.mode_NE ⟨decode32 value, conversion_decode32_valid value⟩ finite

private theorem conversion_lift_projections {precision maximum : Z}
    (ctx : CompCert4Lean.Foundation.FlocqReal.ExactRealContext)
    (value : BinarySingleNaN.binary_float precision maximum)
    (notNaN : BinarySingleNaN.is_nan value = false) :
    Binary.Exact.B2R ctx (Binary.BSN2B' value notNaN) = BinarySingleNaN.Exact.B2R ctx value ∧
      Binary.is_finite (Binary.BSN2B' value notNaN) = BinarySingleNaN.is_finite value ∧
      Binary.Bsign (Binary.BSN2B' value notNaN) = BinarySingleNaN.Bsign value ∧
      Binary.B2FF (Binary.BSN2B' value notNaN) = Binary.SF2FF (BinarySingleNaN.B2SF value) := by
  cases value <;> first | exact ⟨rfl, rfl, rfl, rfl⟩ | contradiction

private theorem conversion_normalize32_correct
    (ctx : CompCert4Lean.Foundation.FlocqReal.ExactRealContext)
    (magnitude : Binary.Exact.Magnitude ctx) :
    Binary.binary_normalize_correctStatement (prec := z24) (emax := z128) ctx magnitude := by
  intro rounding mantissa exponent zeroSign
  have correct := BinarySingleNaN.binary_normalize_correct (prec := z24) (emax := z128)
    ctx magnitude rounding mantissa exponent zeroSign
  have projections := conversion_lift_projections ctx
    (BinarySingleNaN.binary_normalize (prec := z24) (emax := z128) rounding mantissa exponent zeroSign)
    (Binary.binary32_normalize_certificate_proof.is_nan_binary_normalize rounding mantissa exponent zeroSign)
  dsimp only at correct ⊢
  simp only [Binary.binary_normalize, projections.1, projections.2.1,
    projections.2.2.1, projections.2.2.2]
  split <;> rename_i condition
  · rw [if_pos condition] at correct
    exact correct
  · rw [if_neg condition] at correct
    exact congrArg Binary.SF2FF correct

private theorem conversion_to_single_finite (value : float)
    (sign : Bool) (mantissa : positive) (exponent : Z)
    (decoded : decode64 value = .B754_finite sign mantissa exponent) :
    Float.to_single value = encode32
      (Binary.binary_normalize (prec := z24) (emax := z128) BinarySingleNaN.mode_NE
        (CompCert4Lean.Flocq.Core.Zaux.cond_Zopp sign (.Zpos mantissa)) exponent sign) := by
  have notNaN : isNaN64 value = false := by
    rw [← conversion_isNaN64_decode, decoded]
    rfl
  simp only [Float.to_single, notNaN, Bool.false_eq_true, ↓reduceIte, decoded]

private theorem conversion_narrow_normalization (value : float)
    (sign : Bool) (mantissa : positive) (exponent : Z)
    (decoded : decode64 value = .B754_finite sign mantissa exponent) :
    decode32 (Float.to_single value) =
      Binary.binary_normalize (prec := z24) (emax := z128) BinarySingleNaN.mode_NE
        (CompCert4Lean.Flocq.Core.Zaux.cond_Zopp sign (.Zpos mantissa)) exponent sign := by
  rw [conversion_to_single_finite value sign mantissa exponent decoded]
  exact conversion_encode32_decode ⟨_, Binary.binary_normalize_result_obligation_proof _ _ _ _⟩

private theorem conversion_strict_of_nonzero {precision maximum : Z}
    (ctx : CompCert4Lean.Foundation.FlocqReal.ExactRealContext)
    (value : Binary.binary_float precision maximum)
    (finite : Binary.is_finite value = true)
    (nonzero : Binary.Exact.B2R ctx value ≠ Binary.Exact.R0 ctx) :
    Binary.is_finite_strict value = true := by
  cases value <;> first | rfl | contradiction | exact False.elim (nonzero rfl)

private theorem conversion_narrow_representable
    (ctx : CompCert4Lean.Foundation.FlocqReal.ExactRealContext)
    (magnitude : Binary.Exact.Magnitude ctx)
    (original : Binary.CertifiedBinaryFloat z24 z128)
    (strict : Binary.is_finite_strict original.val = true)
    (nonzero : Binary.Exact.B2R ctx original.val ≠ Binary.Exact.R0 ctx)
    (sign : Bool) (mantissa : positive) (exponent : Z)
    (sameValue : Binary.Exact.F2R ctx
      (CompCert4Lean.Flocq.Core.Defs.Float CompCert4Lean.Flocq.Core.Zaux.radix2
        (CompCert4Lean.Flocq.Core.Zaux.cond_Zopp sign (.Zpos mantissa)) exponent) =
      Binary.Exact.B2R ctx original.val) :
    Binary.binary_normalize (prec := z24) (emax := z128) BinarySingleNaN.mode_NE
      (CompCert4Lean.Flocq.Core.Zaux.cond_Zopp sign (.Zpos mantissa)) exponent sign = original.val := by
  have correct := conversion_normalize32_correct ctx magnitude BinarySingleNaN.mode_NE
    (CompCert4Lean.Flocq.Core.Zaux.cond_Zopp sign (.Zpos mantissa)) exponent sign
  dsimp only at correct
  rw [sameValue] at correct
  have fixed := CompCert4Lean.Flocq.Core.Generic_fmt.round_generic ctx magnitude
    CompCert4Lean.Flocq.Core.Zaux.radix2 (Binary.fexp (prec := z24) (emax := z128))
    (Binary.Exact.round_mode ctx BinarySingleNaN.mode_NE)
    (BinarySingleNaN.valid_rnd_round_mode_proof ctx BinarySingleNaN.mode_NE)
    (Binary.Exact.B2R ctx original.val) (Binary.generic_format_B2R ctx magnitude original)
  change Binary.Exact.round magnitude Binary.radix2 (Binary.fexp (prec := z24) (emax := z128))
    (Binary.Exact.round_mode ctx BinarySingleNaN.mode_NE) (Binary.Exact.B2R ctx original.val) =
    Binary.Exact.B2R ctx original.val at fixed
  rw [fixed] at correct
  have bounded := BinarySingleNaN.abs_B2R_lt_emax ctx (Binary.B2BSN original.val)
    (Binary.B2BSN_result_obligation_proof original)
  rw [Binary.B2R_B2BSN ctx original] at bounded
  have inRange := CompCert4Lean.Flocq.Core.Raux.Rlt_bool_true ctx _ _ bounded
  change Binary.Exact.Rlt_bool ctx (Binary.Exact.Rabs ctx (Binary.Exact.B2R ctx original.val))
    (Binary.Exact.bpow ctx Binary.radix2 z128) = true at inRange
  rw [inRange, if_pos rfl] at correct
  apply Binary.B2R_inj ctx
    ⟨_, Binary.binary_normalize_result_obligation_proof _ _ _ _⟩ original
    (conversion_strict_of_nonzero ctx _ correct.2.1 (by rw [correct.1]; exact nonzero)) strict
  exact correct.1

set_option backward.isDefEq.respectTransparency false in
private theorem conversion_finite32_roundtrip
    (ctx : CompCert4Lean.Foundation.FlocqReal.ExactRealContext)
    (magnitude : Binary.Exact.Magnitude ctx)
    (value : Binary.CertifiedBinaryFloat z24 z128)
    (finite : Binary.is_finite value.val = true) :
    Float.to_single (Float.of_single (encode32 value.val)) = encode32 value.val := by
  rcases value with ⟨value, valid⟩
  cases value with
  | B754_zero sign => dsimp only; cases sign <;> decide
  | B754_infinity sign => contradiction
  | B754_nan sign payload => contradiction
  | B754_finite sign mantissa exponent =>
      have decoded := conversion_encode32_decode
        (⟨.B754_finite sign mantissa exponent, valid⟩ : Binary.CertifiedBinaryFloat z24 z128)
      dsimp only at decoded
      have exactValue := conversion_widen_exact ctx
        (encode32 (.B754_finite sign mantissa exponent)) (by rw [decoded]; rfl)
      rw [decoded] at exactValue
      have nonzero : Binary.Exact.B2R ctx
          (Binary.B754_finite (prec := z24) (emax := z128) sign mantissa exponent) ≠
            Binary.Exact.R0 ctx := by
        apply CompCert4Lean.Flocq.Core.Float_prop.F2R_neq_0 ctx
          CompCert4Lean.Flocq.Core.Zaux.radix2
        change CompCert4Lean.Flocq.Core.Zaux.cond_Zopp sign (.Zpos mantissa) ≠ .Z0
        cases sign
        · intro impossible
          cases impossible
        · intro impossible
          have numeric := congrArg intOfZ impossible
          change intOfZ (zOfInt (-(posToNat mantissa : Int))) = 0 at numeric
          rw [intOfZ_zOfInt] at numeric
          have positive := posToNat_positive mantissa
          omega
      cases wide : decode64 (Float.of_single (encode32
          (Binary.B754_finite sign mantissa exponent))) with
      | B754_zero wideSign =>
          rw [wide] at exactValue
          exact False.elim (nonzero exactValue.1.symm)
      | B754_infinity wideSign => simp [wide, Binary.is_finite] at exactValue
      | B754_nan wideSign payload => simp [wide, Binary.is_finite] at exactValue
      | B754_finite wideSign wideMantissa wideExponent =>
          rw [conversion_to_single_finite _ _ _ _ wide]
          apply congrArg encode32
          apply conversion_narrow_representable ctx magnitude
            ⟨.B754_finite sign mantissa exponent, valid⟩ rfl nonzero
          have equality := exactValue.1
          rw [wide] at equality
          exact equality

end CompCert4Lean.Lib.Floats

set_option maxRecDepth 4096
namespace CompCert4Lean.Lib.Floats
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Flocq.IEEE754

open _root_.Float.Model
open _root_.Float.Model.UnpackedFloat

private theorem remaining_round_canonical64
    (sign : Sign) (mantissa : Nat) (exponent : Int)
    (positive : 0 < mantissa) (digits : mantissa.log2 = 52)
    (minimum : -1074 ≤ exponent) :
    roundWithAccuracy Format.binary64 sign mantissa exponent .exact =
      .finite sign mantissa exponent positive := by
  have target : Format.binary64.targetExponent (totalExponent mantissa exponent) = exponent := by
    change max ((mantissa.log2 : Int) + 1 + exponent - 53) (-1074) = exponent
    rw [digits]
    omega
  have shifted : shiftToTargetExponent Format.binary64 mantissa exponent .exact =
      (⟨mantissa, false, false⟩, exponent) := by
    unfold shiftToTargetExponent
    rw [target]
    simp [shiftToExponent, ExtendedMantissa.ofMantissaAndAccuracy]
    rfl
  unfold roundWithAccuracy
  rw [shifted]
  dsimp only
  change (match shiftToTargetExponent Format.binary64 mantissa exponent .exact with
    | (final, finalExponent) =>
      if proof : final.mantissa = 0 then UnpackedFloat.zero sign
      else UnpackedFloat.finite sign final.mantissa finalExponent (Nat.pos_of_ne_zero proof)) = _
  rw [shifted]
  simp [Nat.ne_of_gt positive]

private theorem remaining_round_small64 (mantissa : Nat)
    (positive : 0 < mantissa) (small : mantissa.log2 ≤ 31) :
    round Format.binary64 .positive mantissa 0 =
      .finite .positive (mantissa * 2 ^ (52 - mantissa.log2))
        ((mantissa.log2 : Int) - 52)
        (Nat.mul_pos positive (Nat.two_pow_pos _)) := by
  have target : Format.binary64.targetExponent (totalExponent mantissa 0) =
      (mantissa.log2 : Int) - 52 := by
    change max ((mantissa.log2 : Int) + 1 + 0 - 53) (-1074) = _
    omega
  have shift : (0 - ((mantissa.log2 : Int) - 52)).toNat = 52 - mantissa.log2 := by omega
  have exponent : (0 : Int) - ((52 - mantissa.log2 : Nat) : Int) =
      (mantissa.log2 : Int) - 52 := by omega
  unfold round
  rw [target]
  simp only [decreaseExponent, shift, Nat.shiftLeft_eq, exponent]
  apply remaining_round_canonical64
  · rw [log2_mul_pow _ _ (Nat.ne_of_gt positive)]
    omega
  · omega

private theorem remaining_encode64_normal (mantissa : positive) (exponent : Int)
    (lower : 2 ^ 52 ≤ posToNat mantissa) (upper : posToNat mantissa < 2 ^ 53)
    (emin : -1074 ≤ exponent) (emax : exponent ≤ 971) :
    (encode64 (.B754_finite false mantissa (zOfInt exponent))).bits =
      packComponents Format.binary64 .positive
        (BitVec.ofNat 11 (exponent + 1075).toNat)
        (BitVec.ofNat 52 (posToNat mantissa)) := by
  have fraction : 0 ≤ (posToNat mantissa : Int) - 4503599627370496 := by omega
  have fractionTest : Bits.Zle_bool Bits.Z0
      (Bits.Zsub (.Zpos mantissa) (Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 52))) = true := by
    change (if 0 ≤ intOfZ (zOfInt ((posToNat mantissa : Int) - 4503599627370496)) then true else false) = true
    rw [intOfZ_zOfInt]
    exact if_pos fraction
  unfold encode64 Bits.bits_of_b64 Bits.bits_of_binary_float
  dsimp only
  rw [fractionTest]
  simp only [↓reduceIte]
  change (BitVec.ofNat 64 (ZArith.BinInt.Z.to_nat
    (Bits.join_bits _ _ false (zOfInt ((posToNat mantissa : Int) - 4503599627370496))
        (Bits.Zadd (Bits.Zsub (zOfInt exponent) (Bits.emin _ _)) Bits.Zone)))) = _
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, packComponents, BitVec.toNat_append,
    Sign.toBitVec, BitVec.toNat_ofNat]
  have eminValue : intOfZ (Bits.emin (ZArith.BinInt.Z.of_nat 52)
      (ZArith.BinInt.Z.of_nat 11)) = -1074 := by decide
  simp only [Bits.join_bits, Bits.Zadd, Bits.Zshiftl, Bits.Zsub, Bits.Zone,
    ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub, ZArith.BinInt.Z.shiftl,
    ZArith.BinInt.Z.to_nat, intOfZ_zOfInt]
  simp only [eminValue, show intOfZ (ZArith.BinInt.Z.of_nat 52) = 52 from rfl,
    show intOfZ Flocq.Core.Zaux.Zone = 1 from rfl]
  simp only [show (0 : Int) ≤ 52 from by decide, show (false = true) = False from by decide,
    ↓reduceIte, intOfZ_zOfInt, show intOfZ Bits.Z0 = 0 from rfl, Int.zero_add]
  rw [show exponent - (-1074) + 1 = exponent + 1075 by omega]
  change (Int.toNat (((exponent + 1075) * 4503599627370496) +
    ((posToNat mantissa : Int) - 4503599627370496))) % 18446744073709551616 = _
  have exponentNat : ((exponent + 1075).toNat : Int) = exponent + 1075 := by omega
  have fractionNat : ((posToNat mantissa - 4503599627370496 : Nat) : Int) =
      (posToNat mantissa : Int) - 4503599627370496 := by omega
  have natural : Int.toNat (((exponent + 1075) * 4503599627370496) +
      ((posToNat mantissa : Int) - 4503599627370496)) =
      (exponent + 1075).toNat * 4503599627370496 +
        (posToNat mantissa - 4503599627370496) := by
    rw [← exponentNat, ← fractionNat]
    omega
  rw [natural]
  have exponentBound : (exponent + 1075).toNat < 2048 := by omega
  have mantissaMod : posToNat mantissa % 4503599627370496 =
      posToNat mantissa - 4503599627370496 := by omega
  simp only [Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or, Nat.mod_eq_of_lt exponentBound]
  rw [Nat.shiftLeft_eq, Nat.mul_comm _ (2 ^ 52),
    ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos 52))]
  rw [mantissaMod]
  omega

private theorem remaining_sign_components64 (exponent : BitVec 11) (mantissa : BitVec 52) :
    unpackSign (spec := Format.binary64)
      (packComponents Format.binary64 .positive exponent mantissa) = 0#1 := by
  change BitVec.extractLsb 63 63 (0#1 ++ exponent ++ mantissa) = 0#1
  bv_decide

private theorem remaining_unpack_components64 (mantissa exponent : Nat)
    (lower : 2 ^ 52 ≤ mantissa) (upper : mantissa < 2 ^ 53)
    (emin : 0 < exponent) (emax : exponent < 2047) :
    UnpackedFloat.unpack Format.binary64
      (packComponents Format.binary64 .positive
        (BitVec.ofNat 11 exponent) (BitVec.ofNat 52 mantissa)) =
      .finite .positive mantissa ((exponent : Int) - 1075) (by omega) := by
  have exponentNonzero : (BitVec.ofNat 11 exponent) ≠ 0#11 := by
    intro equality
    have := congrArg BitVec.toNat equality
    simp only [BitVec.toNat_ofNat] at this
    omega
  have exponentFinite : (BitVec.ofNat 11 exponent) ≠ -1#11 := by
    intro equality
    have := congrArg BitVec.toNat equality
    change exponent % 2048 = 2047 at this
    omega
  unfold UnpackedFloat.unpack
  dsimp only
  simp only [unpackMantissa_packComponents (spec := Format.binary64),
    unpackExponent_packComponents (spec := Format.binary64), remaining_sign_components64]
  simp only [exponentNonzero, exponentFinite, ↓reduceIte, Sign.ofBitVec]
  have combined : (1#1 ++ BitVec.ofNat 52 mantissa).toNat = mantissa := by
    rw [BitVec.toNat_append, Nat.shiftLeft_eq]
    change 4503599627370496 ||| mantissa % 4503599627370496 = mantissa
    rw [show 4503599627370496 = 2 ^ 52 * 1 by rfl,
      ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos 52))]
    omega
  simp only [combined, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show exponent < 2 ^ 11 by omega)]
  rfl

private theorem remaining_scaled_bounds (mantissa : Nat) (positive : 0 < mantissa)
    (small : mantissa.log2 ≤ 31) :
    2 ^ 52 ≤ mantissa * 2 ^ (52 - mantissa.log2) ∧
      mantissa * 2 ^ (52 - mantissa.log2) < 2 ^ 53 := by
  have digits : (mantissa * 2 ^ (52 - mantissa.log2)).log2 = 52 := by
    rw [log2_mul_pow _ _ (Nat.ne_of_gt positive)]
    omega
  have nonzero := Nat.ne_of_gt (Nat.mul_pos positive (Nat.two_pow_pos (52 - mantissa.log2)))
  constructor
  · exact (Nat.le_log2 nonzero).mp (by omega)
  · exact (Nat.log2_lt nonzero).mp (by omega)

private theorem remaining_BofZ_bits64
    [certificate : Binary.BinaryNormalizeCertificate z53 z1024]
    (mantissa : Nat) (positive : 0 < mantissa) (small : mantissa.log2 ≤ 31) :
    (encode64 (IEEE754_extra.BofZ (prec := z53) (emax := z1024)
      (ZArith.BinInt.Z.of_nat mantissa))).bits =
      packComponents Format.binary64 .positive
        (BitVec.ofNat 11 (mantissa.log2 + 1023))
        (BitVec.ofNat 52 (mantissa * 2 ^ (52 - mantissa.log2))) := by
  have naturalZ : ZArith.BinInt.Z.of_nat mantissa = .Zpos (posOfNat mantissa) := by
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
    change (mantissa : Int) = (posToNat (posOfNat mantissa) : Int)
    rw [posToNat_posOfNat positive]
  rw [naturalZ, manual_BofZ_positive_small64 (posOfNat mantissa)
    (by simpa only [posToNat_posOfNat positive] using small)]
  simp only [posToNat_posOfNat positive]
  have scaledPositive := Nat.mul_pos positive (Nat.two_pow_pos (52 - mantissa.log2))
  have bounds := remaining_scaled_bounds mantissa positive small
  erw [remaining_encode64_normal _ _
    (by simpa only [posToNat_posOfNat scaledPositive] using bounds.1)
    (by simpa only [posToNat_posOfNat scaledPositive] using bounds.2)
    (by omega) (by omega)]
  rw [posToNat_posOfNat scaledPositive]
  have exponent : ((mantissa.log2 : Int) - 52 + 1075).toNat = mantissa.log2 + 1023 := by omega
  rw [exponent]

private theorem remaining_BofZ_unpack64
    [certificate : Binary.BinaryNormalizeCertificate z53 z1024]
    (mantissa : Nat) (positive : 0 < mantissa) (small : mantissa.log2 ≤ 31) :
    UnpackedFloat.unpack Format.binary64
      (encode64 (IEEE754_extra.BofZ (prec := z53) (emax := z1024)
        (ZArith.BinInt.Z.of_nat mantissa))).bits =
      .finite .positive (mantissa * 2 ^ (52 - mantissa.log2))
        ((mantissa.log2 : Int) - 52)
        (Nat.mul_pos positive (Nat.two_pow_pos _)) := by
  rw [remaining_BofZ_bits64 mantissa positive small]
  have bounds := remaining_scaled_bounds mantissa positive small
  rw [remaining_unpack_components64 (mantissa * 2 ^ (52 - mantissa.log2))
    (mantissa.log2 + 1023) bounds.1 bounds.2 (by omega) (by omega)]
  have exponent : ((mantissa.log2 + 1023 : Nat) : Int) - 1075 =
      (mantissa.log2 : Int) - 52 := by omega
  simp only [exponent]

private theorem remaining_round_scaled_uint64 (mantissa shift : Nat)
    (digits : mantissa.log2 = 31) (positive : 0 < mantissa)
    (shiftLower : 21 ≤ shift) (shiftUpper : shift ≤ 52) :
    round Format.binary64 .positive (mantissa * 2 ^ shift) (-(shift : Int)) =
      .finite .positive (mantissa * 2 ^ 21) (-21)
        (Nat.mul_pos positive (Nat.two_pow_pos 21)) := by
  have scaledNonzero : mantissa * 2 ^ shift ≠ 0 :=
    Nat.ne_of_gt (Nat.mul_pos positive (Nat.two_pow_pos shift))
  have total : totalExponent (mantissa * 2 ^ shift) (-(shift : Int)) = 32 := by
    unfold totalExponent
    rw [log2_mul_pow _ _ (Nat.ne_of_gt positive), digits]
    omega
  have target : Format.binary64.targetExponent
      (totalExponent (mantissa * 2 ^ shift) (-(shift : Int))) = -21 := by
    rw [total]
    rfl
  unfold round
  rw [target]
  have noDecrease : (-(shift : Int) - (-21)).toNat = 0 := by omega
  simp only [decreaseExponent, noDecrease, Nat.shiftLeft_zero, Int.ofNat_zero, Int.sub_zero]
  have canonicalDigits : (mantissa * 2 ^ 21).log2 = 52 := by
    rw [log2_mul_pow _ _ (Nat.ne_of_gt positive), digits]
  have canonicalTarget : Format.binary64.targetExponent
      (totalExponent (mantissa * 2 ^ 21) (-21)) = -21 := by
    change max (((mantissa * 2 ^ 21).log2 : Int) + 1 - 21 - 53) (-1074) = -21
    rw [canonicalDigits]
    rfl
  have scale := shiftToTargetExponent_scale64 (mantissa * 2 ^ 21) (shift - 21) (-21)
    (Nat.ne_of_gt (Nat.mul_pos positive (Nat.two_pow_pos 21)))
    (by rw [canonicalTarget]; omega)
  have scaledMantissa : mantissa * 2 ^ 21 * 2 ^ (shift - 21) = mantissa * 2 ^ shift := by
    rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le shiftLower]
  have scaledExponent : (-21 : Int) - ((shift - 21 : Nat) : Int) = -(shift : Int) := by omega
  rw [scaledMantissa, scaledExponent] at scale
  have canonical := remaining_round_canonical64 .positive (mantissa * 2 ^ 21) (-21)
    (Nat.mul_pos positive (Nat.two_pow_pos 21)) canonicalDigits (by decide)
  unfold roundWithAccuracy at canonical ⊢
  rw [scale]
  exact canonical

private theorem remaining_BofZ_pack64
    [certificate : Binary.BinaryNormalizeCertificate z53 z1024]
    (mantissa : Nat) (positive : 0 < mantissa) (small : mantissa.log2 ≤ 31) :
    (encode64 (IEEE754_extra.BofZ (prec := z53) (emax := z1024)
      (ZArith.BinInt.Z.of_nat mantissa))).bits =
      UnpackedFloat.pack Format.binary64
        (.finite .positive (mantissa * 2 ^ (52 - mantissa.log2))
          ((mantissa.log2 : Int) - 52)
          (Nat.mul_pos positive (Nat.two_pow_pos _))) := by
  rw [remaining_BofZ_bits64 mantissa positive small]
  have digits : (mantissa * 2 ^ (52 - mantissa.log2)).log2 = 52 := by
    rw [log2_mul_pow _ _ (Nat.ne_of_gt positive)]
    omega
  unfold UnpackedFloat.pack
  dsimp only
  rw [digits]
  have exponent : ((mantissa.log2 : Int) - 52 + 1023 + 52).toNat = mantissa.log2 + 1023 := by omega
  change _ = if 2048 ≤ ((mantissa.log2 : Int) - 52 + 1023 + 52).toNat + 1 then _ else _
  simp only [exponent]
  simp only [show ¬ 2048 ≤ mantissa.log2 + 1023 + 1 by omega, ↓reduceIte]
  simp only [show 52 + 1 = Format.binary64.mantissaBits from rfl, ↓reduceIte]
  simp only [show Format.binary64.exponentBias = 1023 from rfl,
    show ((1023 : Nat) : Int) = 1023 from rfl,
    show ((52 : Nat) : Int) = 52 from rfl, exponent]

private theorem remaining_components_notNaN64 (mantissa exponent : Nat)
    (bound : exponent < 2047) :
    isNaN64 ⟨packComponents Format.binary64 .positive
      (BitVec.ofNat 11 exponent) (BitVec.ofNat 52 mantissa)⟩ = false := by
  have extracted := congrArg BitVec.toNat
    (unpackExponent_packComponents (spec := Format.binary64)
      (sign := .positive) (exponent := BitVec.ofNat 11 exponent)
      (mantissa := BitVec.ofNat 52 mantissa))
  simp only [unpackExponent, BitVec.toNat_cast, BitVec.extractLsb_toNat,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat] at extracted
  have exponentValue : exponent64 ⟨packComponents Format.binary64 .positive
      (BitVec.ofNat 11 exponent) (BitVec.ofNat 52 mantissa)⟩ = exponent := by
    change (packComponents Format.binary64 .positive
      (BitVec.ofNat 11 exponent) (BitVec.ofNat 52 mantissa)).toNat / 2 ^ 52 % 2 ^ 11 = exponent
    rw [extracted, Nat.mod_eq_of_lt (by omega)]
  unfold isNaN64
  rw [exponentValue]
  simp only [show (2 ^ 11 - 1 : Nat) = 2047 by decide,
    show (exponent == 2047) = false by simp; omega, Bool.false_and]

private theorem remaining_BofZ_notNaN64
    [certificate : Binary.BinaryNormalizeCertificate z53 z1024]
    (mantissa : Nat) (positive : 0 < mantissa) (small : mantissa.log2 ≤ 31) :
    isNaN64 (encode64 (IEEE754_extra.BofZ (prec := z53) (emax := z1024)
      (ZArith.BinInt.Z.of_nat mantissa))) = false := by
  have value : encode64 (IEEE754_extra.BofZ (prec := z53) (emax := z1024)
      (ZArith.BinInt.Z.of_nat mantissa)) =
      ⟨packComponents Format.binary64 .positive
        (BitVec.ofNat 11 (mantissa.log2 + 1023))
        (BitVec.ofNat 52 (mantissa * 2 ^ (52 - mantissa.log2)))⟩ := by
    apply float.ext
    exact remaining_BofZ_bits64 mantissa positive small
  rw [value]
  exact remaining_components_notNaN64 _ _ (by omega)

private theorem remaining_add_uint64 (mantissa : Nat)
    (positive : 0 < mantissa) (bound : mantissa < 2 ^ 31) :
    UnpackedFloat.add Format.binary64
      (.finite .positive (mantissa * 2 ^ (52 - mantissa.log2))
        ((mantissa.log2 : Int) - 52)
        (Nat.mul_pos positive (Nat.two_pow_pos _)))
      (.finite .positive 4503599627370496 (-21) (by decide)) =
      .finite .positive ((mantissa + 2 ^ 31) * 2 ^ 21) (-21)
        (Nat.mul_pos (by omega) (Nat.two_pow_pos _)) := by
  have small : mantissa.log2 < 31 := (Nat.log2_lt (Nat.ne_of_gt positive)).mpr bound
  have minimum : min ((mantissa.log2 : Int) - 52) (-21) =
      (mantissa.log2 : Int) - 52 := by omega
  have noShift : ((mantissa.log2 : Int) - 52 - ((mantissa.log2 : Int) - 52)).toNat = 0 := by omega
  have thresholdShift : ((-21 : Int) - ((mantissa.log2 : Int) - 52)).toNat =
      31 - mantissa.log2 := by omega
  have shiftedThreshold : 4503599627370496 * 2 ^ (31 - mantissa.log2) =
      2 ^ 31 * 2 ^ (52 - mantissa.log2) := by
    change 2 ^ 52 * 2 ^ (31 - mantissa.log2) = _
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  have totalPositive : 0 < mantissa * 2 ^ (52 - mantissa.log2) +
      4503599627370496 * 2 ^ (31 - mantissa.log2) := by
    have := Nat.mul_pos positive (Nat.two_pow_pos (52 - mantissa.log2))
    omega
  unfold UnpackedFloat.add
  dsimp only
  rw [minimum]
  simp only [decreaseExponent, noShift, thresholdShift,
    Nat.shiftLeft_eq, Sign.apply, Nat.pow_zero, Nat.mul_one]
  unfold normalize
  have comparison : compare
      ((mantissa * 2 ^ (52 - mantissa.log2) : Nat) +
        (4503599627370496 * 2 ^ (31 - mantissa.log2) : Nat) : Int) 0 = .gt := by
    apply Int.compare_eq_gt.mpr
    omega
  rw [comparison]
  simp only [← Int.natCast_add, Int.toNat_natCast, shiftedThreshold, ← Nat.add_mul]
  have totalDigits : (mantissa + 2 ^ 31).log2 = 31 := by
    have totalNonzero : mantissa + 2 ^ 31 ≠ 0 := by omega
    have low := (Nat.le_log2 totalNonzero).mpr (show 2 ^ 31 ≤ mantissa + 2 ^ 31 by omega)
    have high := (Nat.log2_lt totalNonzero).mpr (show mantissa + 2 ^ 31 < 2 ^ 32 by omega)
    omega
  have exponent : (mantissa.log2 : Int) - 52 = -((52 - mantissa.log2 : Nat) : Int) := by omega
  rw [exponent]
  exact remaining_round_scaled_uint64 (mantissa + 2 ^ 31) (52 - mantissa.log2)
    totalDigits (by omega) (by omega) (by omega)

private theorem remaining_BofZ_add64
    [certificate : Binary.BinaryNormalizeCertificate z53 z1024]
    (mantissa : Nat) (positive : 0 < mantissa) (bound : mantissa < 2 ^ 31) :
    Float.add
      (encode64 (IEEE754_extra.BofZ (prec := z53) (emax := z1024) (ZArith.BinInt.Z.of_nat mantissa)))
      (encode64 (IEEE754_extra.BofZ (prec := z53) (emax := z1024) (ZArith.BinInt.Z.of_nat (2 ^ 31)))) =
      encode64 (IEEE754_extra.BofZ (prec := z53) (emax := z1024)
        (ZArith.BinInt.Z.of_nat (mantissa + 2 ^ 31))) := by
  have small : mantissa.log2 ≤ 31 := by
    have := (Nat.log2_lt (Nat.ne_of_gt positive)).mpr bound
    omega
  have totalPositive : 0 < mantissa + 2 ^ 31 := by omega
  have totalDigits : (mantissa + 2 ^ 31).log2 = 31 := by
    have nonzero := Nat.ne_of_gt totalPositive
    have low := (Nat.le_log2 nonzero).mpr (show 2 ^ 31 ≤ mantissa + 2 ^ 31 by omega)
    have high := (Nat.log2_lt nonzero).mpr (show mantissa + 2 ^ 31 < 2 ^ 32 by omega)
    omega
  have raw : modelBinary64 (UnpackedFloat.add Format.binary64)
      (encode64 (IEEE754_extra.BofZ (prec := z53) (emax := z1024) (ZArith.BinInt.Z.of_nat mantissa)))
      (encode64 (IEEE754_extra.BofZ (prec := z53) (emax := z1024) (ZArith.BinInt.Z.of_nat (2 ^ 31)))) =
      encode64 (IEEE754_extra.BofZ (prec := z53) (emax := z1024)
        (ZArith.BinInt.Z.of_nat (mantissa + 2 ^ 31))) := by
    apply float.ext
    unfold modelBinary64
    simp only
    rw [remaining_BofZ_unpack64 mantissa positive small,
      remaining_BofZ_unpack64 (2 ^ 31) (by decide) (by decide)]
    change UnpackedFloat.pack Format.binary64
      (UnpackedFloat.add Format.binary64
        (.finite .positive (mantissa * 2 ^ (52 - mantissa.log2))
          ((mantissa.log2 : Int) - 52) _)
        (.finite .positive 4503599627370496 (-21) _)) = _
    rw [remaining_add_uint64 mantissa positive bound,
      remaining_BofZ_pack64 (mantissa + 2 ^ 31) totalPositive (by omega)]
    simp only [totalDigits, show (52 - 31 : Nat) = 21 from rfl,
      show ((31 : Nat) : Int) - 52 = -21 from rfl]
  unfold Float.add
  rw [raw]
  simp only [Float.finishBinary, remaining_BofZ_notNaN64 mantissa positive small,
    remaining_BofZ_notNaN64 (2 ^ 31) (by decide) (by decide),
    remaining_BofZ_notNaN64 (mantissa + 2 ^ 31) totalPositive (by omega),
    Bool.false_or, Bool.false_eq_true, ↓reduceIte]

private theorem remaining_unsigned_split (word : Integers.Int.int)
    (large : Integers.Int.ltu word Float.ox8000_0000 = false) :
    ∃ mantissa : Nat, mantissa < 2 ^ 31 ∧
      Integers.Int.unsigned word = ZArith.BinInt.Z.of_nat (mantissa + 2 ^ 31) ∧
      Integers.Int.signed (Integers.Int.sub word Float.ox8000_0000) =
        ZArith.BinInt.Z.of_nat mantissa := by
  have range := Integers.Int.unsigned_range_proof word
  have half : Integers.Int.unsigned Float.ox8000_0000 = ZArith.BinInt.Z.of_nat (2 ^ 31) := by decide
  have lower : (2147483648 : Int) ≤ intOfZ (Integers.Int.unsigned word) := by
    apply Int.le_of_not_gt
    intro contradiction
    have less : ZArith.BinInt.Z.lt (Integers.Int.unsigned word)
        (Integers.Int.unsigned Float.ox8000_0000) := by
      rw [half]
      change intOfZ (Integers.Int.unsigned word) < 2147483648
      omega
    have comparison : Integers.Int.ltu word Float.ox8000_0000 = true :=
      Coqlib.zlt_true _ _ _ _ _ less
    rw [large] at comparison
    contradiction
  have upper : intOfZ (Integers.Int.unsigned word) < 4294967296 := range.2
  let mantissa := (intOfZ (Integers.Int.unsigned word) - 2147483648).toNat
  have cast : (mantissa : Int) = intOfZ (Integers.Int.unsigned word) - 2147483648 := by
    dsimp [mantissa]
    omega
  have bound : mantissa < 2 ^ 31 := by omega
  refine ⟨mantissa, bound, ?_, ?_⟩
  · apply intOfZ_injective
    simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt, Int.ofNat_eq_natCast, Int.natCast_add]
    omega
  · have difference : Integers.Int.sub word Float.ox8000_0000 =
        Integers.Int.repr (ZArith.BinInt.Z.of_nat mantissa) := by
      unfold Integers.Int.sub Integers.WordCore.sub
      change Integers.Int.repr (ZArith.BinInt.Z.sub (Integers.Int.unsigned word)
        (Integers.Int.unsigned Float.ox8000_0000)) = _
      rw [half]
      congr 1
      apply intOfZ_injective
      simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
      exact cast.symm
    rw [difference]
    apply Integers.Int.signed_repr_proof
    constructor
    · change -2147483648 ≤ intOfZ (ZArith.BinInt.Z.of_nat mantissa)
      simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt, Int.ofNat_eq_natCast]
      omega
    · change intOfZ (ZArith.BinInt.Z.of_nat mantissa) ≤ 2147483647
      simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt, Int.ofNat_eq_natCast]
      omega

theorem Float.of_intu_of_int_2
    [certificate : Binary.BinaryNormalizeCertificate z53 z1024] :
    Float.of_intu_of_int_2Statement := by
  intro word large
  obtain ⟨mantissa, bound, unsigned, signed⟩ := remaining_unsigned_split word large
  have half : Integers.Int.unsigned Float.ox8000_0000 = ZArith.BinInt.Z.of_nat (2 ^ 31) := by decide
  unfold Float.of_intu Float.of_int
  rw [unsigned, signed, half]
  by_cases positive : 0 < mantissa
  · exact (remaining_BofZ_add64 mantissa positive bound).symm
  · have zero : mantissa = 0 := by omega
    subst mantissa
    simp only [Nat.zero_add]
    have encodedZero : encode64 (IEEE754_extra.BofZ (prec := z53) (emax := z1024)
        (ZArith.BinInt.Z.of_nat 0)) = ⟨0#64⟩ := by
      rfl
    rw [encodedZero]
    have raw : modelBinary64 (UnpackedFloat.add Format.binary64) ⟨0#64⟩
        (encode64 (IEEE754_extra.BofZ (prec := z53) (emax := z1024)
          (ZArith.BinInt.Z.of_nat (2 ^ 31)))) =
        encode64 (IEEE754_extra.BofZ (prec := z53) (emax := z1024)
          (ZArith.BinInt.Z.of_nat (2 ^ 31))) := by
      apply float.ext
      unfold modelBinary64
      simp only
      rw [remaining_BofZ_unpack64 (2 ^ 31) (by decide) (by decide),
        remaining_BofZ_pack64 (2 ^ 31) (by decide) (by decide)]
      rfl
    unfold Float.add
    rw [raw]
    simp only [Float.finishBinary, remaining_BofZ_notNaN64 (2 ^ 31) (by decide) (by decide),
      show isNaN64 ⟨0#64⟩ = false from rfl, Bool.false_or, Bool.false_eq_true, ↓reduceIte]

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Flocq.IEEE754
open _root_.Float.Model
open _root_.Float.Model.UnpackedFloat

private theorem remaining_zofnat_positive (value : Nat) (positive : 0 < value) :
    ZArith.BinInt.Z.of_nat value = .Zpos (posOfNat value) := by
  apply intOfZ_injective
  change intOfZ (zOfInt value) = (posToNat (posOfNat value) : Int)
  rw [intOfZ_zOfInt, posToNat_posOfNat positive]

private theorem remaining_decode64_fields (value : float) (sign : Bool)
    (mantissa : positive) (exponent : Z)
    (decoded : decode64 value = .B754_finite sign mantissa exponent) :
    sign = decide (2 ^ 63 ≤ value.bits.toNat) ∧
    ((intOfZ exponent = -1074 ∧ posToNat mantissa = value.bits.toNat % 2 ^ 52 ∧
      value.bits.toNat / 2 ^ 52 % 2048 = 0) ∨
      (intOfZ exponent = ((value.bits.toNat / 2 ^ 52 % 2048 : Nat) : Int) - 1075 ∧
       posToNat mantissa = value.bits.toNat % 2 ^ 52 + 2 ^ 52 ∧
       0 < value.bits.toNat / 2 ^ 52 % 2048 ∧
       value.bits.toNat / 2 ^ 52 % 2048 < 2047)) := by
  let rawExponent := value.bits.toNat / 2 ^ 52 % 2048
  let rawMantissa := value.bits.toNat % 2 ^ 52
  have rawBound : rawExponent < 2048 := Nat.mod_lt _ (by decide)
  have division := zdiv_nat_f64 value.bits.toNat (2 ^ 52) (by decide)
  have remainder := zmod_nat_f64 value.bits.toNat (2 ^ 52) (by decide)
  have exponentRemainder := zmod_nat_f64 (value.bits.toNat / 2 ^ 52) 2048 (by decide)
  change @Eq (Binary.binary_float z53 z1024) (decode64 value)
    (.B754_finite sign mantissa exponent) at decoded
  unfold decode64 Bits.b64_of_bits_unchecked Bits.binary_float_of_bits_unchecked
    Bits.binary_float_of_bits_aux Bits.split_bits at decoded
  dsimp only at decoded
  simp only [show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 52) =
      ZArith.BinInt.Z.of_nat (2 ^ 52) by decide,
    show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 11) =
      ZArith.BinInt.Z.of_nat 2048 by decide,
    division, remainder, exponentRemainder] at decoded
  have signTest : Bits.Zle_bool
      (Bits.Zmul (ZArith.BinInt.Z.of_nat (2 ^ 52)) (ZArith.BinInt.Z.of_nat 2048))
      (ZArith.BinInt.Z.of_nat value.bits.toNat) = decide (2 ^ 63 ≤ value.bits.toNat) := by
    change (if (9223372036854775808 : Int) ≤ intOfZ (zOfInt value.bits.toNat) then true else false) = _
    rw [intOfZ_zOfInt]
    split
    · symm
      apply decide_eq_true
      omega
    · symm
      apply decide_eq_false
      omega
  rw [signTest] at decoded
  by_cases zeroExponent : rawExponent = 0
  · have zeroTest : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat rawExponent) Bits.Z0 = true := by
      rw [zeroExponent]
      rfl
    rw [zeroTest] at decoded
    simp only [↓reduceIte] at decoded
    by_cases zeroMantissa : rawMantissa = 0
    · have mantissaZero : ZArith.BinInt.Z.of_nat (value.bits.toNat % 2 ^ 52) = .Z0 := by
        rw [show value.bits.toNat % 2 ^ 52 = 0 from zeroMantissa]
        rfl
      simp only [mantissaZero, Binary.FF2B_unchecked] at decoded
      contradiction
    · have positive := Nat.pos_of_ne_zero zeroMantissa
      rw [remaining_zofnat_positive rawMantissa positive] at decoded
      change Binary.B754_finite (decide (2 ^ 63 ≤ value.bits.toNat))
        (posOfNat rawMantissa) (Bits.emin _ _) = _ at decoded
      injection decoded with signEq mantissaEq exponentEq
      refine ⟨signEq.symm, Or.inl ⟨?_, ?_, zeroExponent⟩⟩
      · rw [← exponentEq]
        rfl
      · rw [← mantissaEq, posToNat_posOfNat positive]
  · have zeroTest : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat rawExponent) Bits.Z0 = false :=
      conversion_zeq_nat_false zeroExponent
    rw [zeroTest] at decoded
    simp only [Bool.false_eq_true, ↓reduceIte] at decoded
    have maxValue : Bits.Zsub (ZArith.BinInt.Z.of_nat 2048) Bits.Zone =
        ZArith.BinInt.Z.of_nat 2047 := by decide
    rw [maxValue] at decoded
    by_cases maxExponent : rawExponent = 2047
    · rw [conversion_zeq_nat_true maxExponent] at decoded
      simp only [↓reduceIte] at decoded
      cases mantissaValue : ZArith.BinInt.Z.of_nat (value.bits.toNat % 2 ^ 52) <;>
        simp only [mantissaValue, Binary.FF2B_unchecked] at decoded <;> contradiction
    · rw [conversion_zeq_nat_false maxExponent] at decoded
      simp only [Bool.false_eq_true, ↓reduceIte] at decoded
      have sum : Bits.Zadd (ZArith.BinInt.Z.of_nat rawMantissa)
          (ZArith.BinInt.Z.of_nat (2 ^ 52)) =
          ZArith.BinInt.Z.of_nat (rawMantissa + 2 ^ 52) := by
        apply intOfZ_injective
        simp only [Bits.Zadd, ZArith.BinInt.Z.add, ZArith.BinInt.Z.of_nat,
          intOfZ_zOfInt, Int.ofNat_eq_natCast, Int.natCast_add]
      rw [sum, remaining_zofnat_positive (rawMantissa + 2 ^ 52) (by omega)] at decoded
      change Binary.B754_finite (decide (2 ^ 63 ≤ value.bits.toNat))
        (posOfNat (rawMantissa + 2 ^ 52))
        (Bits.Zsub (Bits.Zadd (ZArith.BinInt.Z.of_nat rawExponent) (Bits.emin _ _)) Bits.Zone) = _ at decoded
      injection decoded with signEq mantissaEq exponentEq
      refine ⟨signEq.symm, Or.inr ⟨?_, ?_, by omega, by omega⟩⟩
      · rw [← exponentEq]
        simp only [Bits.Zsub, Bits.Zadd, ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add,
          ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
        change (rawExponent : Int) + (-1074) - 1 = (rawExponent : Int) - 1075
        omega
      · rw [← mantissaEq, posToNat_posOfNat (by omega)]

private theorem remaining_positive_uint_exponent (mantissa : positive) (exponent result : Z)
    (lower : 4503599627370496 ≤ posToNat mantissa)
    (large : -21 ≤ intOfZ exponent)
    (upper : intOfZ result < 4294967296)
    (converted : IEEE754_extra.ZofB (prec := z53) (emax := z1024)
      (.B754_finite false mantissa exponent) = some result) :
    exponent = .Zneg (posOfNat 21) := by
  cases exponent with
  | Z0 =>
      have equal := congrArg intOfZ (Option.some.inj converted)
      change (posToNat mantissa : Int) = intOfZ result at equal
      omega
  | Zpos shift =>
      have equal := congrArg intOfZ (Option.some.inj converted)
      change intOfZ (ZArith.BinInt.Z.mul (.Zpos mantissa)
        (ZArith.BinInt.Z.pow_pos (.Zpos (.xO .xH)) shift)) = intOfZ result at equal
      simp only [ZArith.BinInt.Z.mul, ZArith.BinInt.Z.pow_pos, intOfZ_zOfInt] at equal
      change (posToNat mantissa : Int) * (2 : Int) ^ posToNat shift = intOfZ result at equal
      have factor : (1 : Int) ≤ (2 : Int) ^ posToNat shift := Int.pow_pos (by decide)
      have bound := Int.mul_le_mul_of_nonneg_left factor (Int.natCast_nonneg (posToNat mantissa))
      omega
  | Zneg shift =>
      have equal := congrArg intOfZ (Option.some.inj converted)
      change intOfZ (ZArith.BinInt.Z.div (.Zpos mantissa)
        (ZArith.BinInt.Z.pow_pos (.Zpos (.xO .xH)) shift)) = intOfZ result at equal
      rw [manual_div_pow_int] at equal
      have shiftUpper : posToNat shift ≤ 21 := by
        change -21 ≤ -(posToNat shift : Int) at large
        omega
      have shiftLower : 21 ≤ posToNat shift := by
        by_cases small : posToNat shift ≤ 20
        · have power := Nat.pow_le_pow_right (by decide : 0 < 2) small
          have powerInt : (2 : Int) ^ posToNat shift ≤ 1048576 := Int.ofNat_le.mpr power
          have scaled := Int.mul_le_mul_of_nonneg_left powerInt (by decide : (0 : Int) ≤ 4294967296)
          have quotient : 4294967296 ≤ (posToNat mantissa : Int) / (2 : Int) ^ posToNat shift := by
            apply (Int.le_ediv_iff_mul_le (Int.pow_pos (by decide))).mpr
            omega
          omega
        · omega
      congr 1
      apply posToNat_injective
      change posToNat shift = 21
      omega

private theorem remaining_uint_input
    [certificate : Binary.BinaryNormalizeCertificate z53 z1024]
    (value : float) (word : Integers.Int.int)
    (compared : Float.cmp .Clt value (Float.of_intu Float.ox8000_0000) = false)
    (converted : Float.to_intu value = some word) :
    ∃ mantissa : positive,
      decode64 value = .B754_finite false mantissa (.Zneg (posOfNat 21)) ∧
      2 ^ 52 ≤ posToNat mantissa ∧ posToNat mantissa < 2 ^ 53 := by
  have threshold : decode64 (Float.of_intu Float.ox8000_0000) =
      Binary.B754_finite false (posOfNat 4503599627370496) (.Zneg (posOfNat 21)) := by rfl
  unfold Float.cmp Float.compare at compared
  rw [threshold] at compared
  have notLess : Binary.Bcompare (decode64 value)
      (.B754_finite false (posOfNat 4503599627370496) (.Zneg (posOfNat 21))) ≠ some .Lt := by
    intro equality
    simp only [equality, cmp_of_comparison] at compared
    contradiction
  unfold Float.to_intu at converted
  cases rangeResult : IEEE754_extra.ZofB_range (decode64 value) z0 Integers.Int.max_unsigned with
  | none => simp [rangeResult] at converted
  | some result =>
    have inRange := IEEE754_extra.ZofB_range_inversion
      ⟨decode64 value, manual_decode64_certificate value⟩ z0 Integers.Int.max_unsigned result rangeResult
    have truncated : IEEE754_extra.ZofB (decode64 value) = some result := inRange.2.2
    have upper : intOfZ result < 4294967296 := by
      have limit : intOfZ result ≤ 4294967295 := inRange.2.1
      omega
    have valid := manual_decode64_certificate value
    cases decoded : decode64 value with
    | B754_zero sign => simp [decoded, Binary.Bcompare, Binary.B2BSN, BinarySingleNaN.Bcompare,
        BinarySingleNaN.SFcompare, Model.Rocq.Coq.Floats.SpecFloat.SFcompare,
        BinarySingleNaN.B2SF, cmp_of_comparison] at compared
    | B754_infinity sign => simp [decoded, IEEE754_extra.ZofB] at truncated
    | B754_nan sign payload => simp [decoded, IEEE754_extra.ZofB] at truncated
    | B754_finite sign mantissa exponent =>
      rw [decoded] at compared truncated valid notLess
      cases sign with
      | true =>
        simp [Binary.Bcompare, Binary.B2BSN, BinarySingleNaN.Bcompare,
          BinarySingleNaN.SFcompare, Model.Rocq.Coq.Floats.SpecFloat.SFcompare,
          BinarySingleNaN.B2SF, cmp_of_comparison] at compared
      | false =>
        have large : -21 ≤ intOfZ exponent := by
          apply Int.le_of_not_gt
          intro less
          have lessComparison : Binary.Bcompare (prec := z53) (emax := z1024)
              (.B754_finite false mantissa exponent)
              (.B754_finite false (posOfNat 4503599627370496) (.Zneg (posOfNat 21))) = some .Lt := by
            change some (match ZArith.BinInt.Z.compare exponent (.Zneg (posOfNat 21)) with
              | .Eq => PArith.BinPos.Pos.compare_cont .Eq mantissa (posOfNat 4503599627370496)
              | other => other) = some .Lt
            have comparison : ZArith.BinInt.Z.compare exponent (.Zneg (posOfNat 21)) = .Lt := by
              change (if intOfZ exponent < -21 then (.Lt : RCmp) else if intOfZ exponent = -21 then .Eq else .Gt) = .Lt
              rw [if_pos less]
            rw [comparison]
          exact notLess lessComparison
        have fields := remaining_decode64_fields value false mantissa exponent decoded
        have lower : 4503599627370496 ≤ posToNat mantissa := by
          rcases fields.2 with subnormal | normal
          · omega
          · omega
        have exponentExact := remaining_positive_uint_exponent mantissa exponent result lower large upper truncated
        refine ⟨mantissa, ?_, lower, ?_⟩
        · subst exponent
          rfl
        · have bound := manual_mantissa_bound64 mantissa exponent valid
          omega

private theorem remaining_positive_normal_bits64 (value : float)
    (mantissa : positive) (exponent : Z)
    (decoded : decode64 value = .B754_finite false mantissa exponent)
    (lower : 2 ^ 52 ≤ posToNat mantissa) :
    value.bits = packComponents Format.binary64 .positive
      (BitVec.ofNat 11 (intOfZ exponent + 1075).toNat)
      (BitVec.ofNat 52 (posToNat mantissa)) := by
  have fields := remaining_decode64_fields value false mantissa exponent decoded
  have rawSmall : value.bits.toNat < 2 ^ 63 := by
    have signFalse := fields.1.symm
    simp only [decide_eq_false_iff_not] at signFalse
    omega
  have fractionBound : value.bits.toNat % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (by decide)
  rcases fields.2 with subnormal | ⟨exponentEq, mantissaEq, exponentPositive, exponentBound⟩
  · omega
  · have quotientBound : value.bits.toNat / 2 ^ 52 < 2048 := by omega
    have quotientMod : value.bits.toNat / 2 ^ 52 % 2048 = value.bits.toNat / 2 ^ 52 := Nat.mod_eq_of_lt quotientBound
    rw [quotientMod] at exponentEq exponentPositive exponentBound
    have exponentNat : (intOfZ exponent + 1075).toNat = value.bits.toNat / 2 ^ 52 := by omega
    apply BitVec.eq_of_toNat_eq
    simp only [packComponents, BitVec.toNat_append, Sign.toBitVec, BitVec.toNat_ofNat,
      Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or, exponentNat,
      Nat.mod_eq_of_lt quotientBound]
    rw [Nat.shiftLeft_eq, Nat.mul_comm _ (2 ^ 52),
      ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos 52))]
    omega

private theorem remaining_positive_normal_unpack64 (value : float)
    (mantissa : positive) (exponent : Z)
    (decoded : decode64 value = .B754_finite false mantissa exponent)
    (lower : 2 ^ 52 ≤ posToNat mantissa) :
    UnpackedFloat.unpack Format.binary64 value.bits =
      .finite .positive (posToNat mantissa) (intOfZ exponent) (posToNat_positive mantissa) := by
  have fields := remaining_decode64_fields value false mantissa exponent decoded
  have fractionBound : value.bits.toNat % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have exponentBounds : 0 < (intOfZ exponent + 1075).toNat ∧
      (intOfZ exponent + 1075).toNat < 2047 := by
    rcases fields.2 with subnormal | normal <;> omega
  have mantissaUpper : posToNat mantissa < 2 ^ 53 := by
    rcases fields.2 with subnormal | normal <;> omega
  rw [remaining_positive_normal_bits64 value mantissa exponent decoded lower]
  rw [remaining_unpack_components64 (posToNat mantissa) _ lower mantissaUpper
    exponentBounds.1 exponentBounds.2]
  have exponentEq : ((intOfZ exponent + 1075).toNat : Int) - 1075 = intOfZ exponent := by
    rcases fields.2 with subnormal | normal <;> omega
  simp only [exponentEq]

private theorem remaining_fraction_round64 (mantissa : Nat)
    (positive : 0 < mantissa) (small : mantissa.log2 ≤ 51) :
    round Format.binary64 .positive mantissa (-21) =
      .finite .positive (mantissa * 2 ^ (52 - mantissa.log2))
        ((mantissa.log2 : Int) - 73)
        (Nat.mul_pos positive (Nat.two_pow_pos _)) := by
  have target : Format.binary64.targetExponent (totalExponent mantissa (-21)) =
      (mantissa.log2 : Int) - 73 := by
    change max ((mantissa.log2 : Int) + 1 - 21 - 53) (-1074) = _
    omega
  have shift : (-21 - ((mantissa.log2 : Int) - 73)).toNat = 52 - mantissa.log2 := by omega
  have exponent : (-21 : Int) - ((52 - mantissa.log2 : Nat) : Int) =
      (mantissa.log2 : Int) - 73 := by omega
  unfold round
  rw [target]
  simp only [decreaseExponent, shift, Nat.shiftLeft_eq, exponent]
  apply remaining_round_canonical64
  · rw [log2_mul_pow _ _ (Nat.ne_of_gt positive)]
    omega
  · omega

private theorem remaining_fraction_certificate64 (mantissa : Nat)
    (positive : 0 < mantissa) (small : mantissa.log2 ≤ 51) :
    Binary.BinaryFloatCertificate (prec := z53) (emax := z1024)
      (.B754_finite false (posOfNat (mantissa * 2 ^ (52 - mantissa.log2)))
        (zOfInt ((mantissa.log2 : Int) - 73))) := by
  have scaledPositive := Nat.mul_pos positive (Nat.two_pow_pos (52 - mantissa.log2))
  have digits : posToNat (BinarySingleNaN.digits2_pos
      (posOfNat (mantissa * 2 ^ (52 - mantissa.log2)))) = 53 := by
    have equation := quiet_nan_digits2_pos_nat (posOfNat (mantissa * 2 ^ (52 - mantissa.log2)))
    change posToNat (BinarySingleNaN.digits2_pos _) =
      (posToNat (posOfNat (mantissa * 2 ^ (52 - mantissa.log2)))).log2 + 1 at equation
    rw [equation, posToNat_posOfNat scaledPositive, log2_mul_pow _ _ (Nat.ne_of_gt positive)]
    omega
  change (BinarySingleNaN.canonical_mantissa0 z53 z1024 _ _ &&
    ZArith.Zbool.Zle_bool _ (ZArith.BinInt.Z.sub z1024 z53)) = true
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply CompCert4Lean.Flocq.Core.Zaux.Zeq_bool_true
    exact manual_fexp_canonical64 _ _ digits (by rw [intOfZ_zOfInt]; omega)
  · change (if intOfZ (zOfInt ((mantissa.log2 : Int) - 73)) ≤ 971 then true else false) = true
    rw [intOfZ_zOfInt]
    exact if_pos (by omega)

private theorem remaining_fraction_pack64 (mantissa : Nat)
    (positive : 0 < mantissa) (small : mantissa.log2 ≤ 51) :
    UnpackedFloat.pack Format.binary64 (round Format.binary64 .positive mantissa (-21)) =
      (encode64 (.B754_finite false (posOfNat (mantissa * 2 ^ (52 - mantissa.log2)))
        (zOfInt ((mantissa.log2 : Int) - 73)))).bits := by
  have scaledPositive := Nat.mul_pos positive (Nat.two_pow_pos (52 - mantissa.log2))
  have digits : (mantissa * 2 ^ (52 - mantissa.log2)).log2 = 52 := by
    rw [log2_mul_pow _ _ (Nat.ne_of_gt positive)]
    omega
  have lower : 2 ^ 52 ≤ mantissa * 2 ^ (52 - mantissa.log2) :=
    (Nat.le_log2 (Nat.ne_of_gt scaledPositive)).mp (by omega)
  have upper : mantissa * 2 ^ (52 - mantissa.log2) < 2 ^ 53 :=
    (Nat.log2_lt (Nat.ne_of_gt scaledPositive)).mp (by omega)
  rw [remaining_fraction_round64 mantissa positive small]
  rw [remaining_encode64_normal _ _
    (by simpa only [posToNat_posOfNat scaledPositive] using lower)
    (by simpa only [posToNat_posOfNat scaledPositive] using upper)
    (by omega) (by omega), posToNat_posOfNat scaledPositive]
  unfold UnpackedFloat.pack
  dsimp only
  rw [digits]
  have exponent : ((mantissa.log2 : Int) - 73 + 1023 + 52).toNat = mantissa.log2 + 1002 := by omega
  have exponent' : ((mantissa.log2 : Int) - 73 + 1075).toNat = mantissa.log2 + 1002 := by omega
  simp only [show Format.binary64.exponentBits = 11 from rfl,
    show Format.binary64.exponentBias = 1023 from rfl,
    show Format.binary64.mantissaBitsWithoutImplicit = 52 from rfl,
    show Format.binary64.mantissaBits = 53 from rfl,
    show ((1023 : Nat) : Int) = 1023 from rfl,
    show ((52 : Nat) : Int) = 52 from rfl, exponent, exponent',
    show ¬ 2 ^ 11 ≤ mantissa.log2 + 1002 + 1 by omega, ↓reduceIte]

private theorem remaining_fraction_trunc64 (mantissa : Nat)
    (positive : 0 < mantissa) (small : mantissa.log2 ≤ 51) :
    IEEE754_extra.ZofB (prec := z53) (emax := z1024)
      (.B754_finite false (posOfNat (mantissa * 2 ^ (52 - mantissa.log2)))
        (zOfInt ((mantissa.log2 : Int) - 73))) =
      some (ZArith.BinInt.Z.of_nat (mantissa / 2 ^ 21)) := by
  have exponent : zOfInt ((mantissa.log2 : Int) - 73) = .Zneg (posOfNat (73 - mantissa.log2)) := by
    apply intOfZ_injective
    rw [intOfZ_zOfInt]
    change (mantissa.log2 : Int) - 73 = -(posToNat (posOfNat (73 - mantissa.log2)) : Int)
    rw [posToNat_posOfNat (by omega)]
    omega
  rw [exponent]
  apply congrArg some
  apply intOfZ_injective
  simp only [Flocq.Core.Zaux.cond_Zopp, Model.Rocq.Coq.Floats.SpecFloat.cond_Zopp,
    Bool.false_eq_true, ↓reduceIte]
  rw [manual_div_pow_int]
  rw [posToNat_posOfNat (Nat.mul_pos positive (Nat.two_pow_pos _)),
    posToNat_posOfNat (by omega)]
  have denominator : 2 ^ (73 - mantissa.log2) = 2 ^ 21 * 2 ^ (52 - mantissa.log2) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have natural : (mantissa * 2 ^ (52 - mantissa.log2)) / 2 ^ (73 - mantissa.log2) =
      mantissa / 2 ^ 21 := by
    rw [denominator]
    exact Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)
  change ((mantissa * 2 ^ (52 - mantissa.log2) : Nat) : Int) /
    (2 : Int) ^ (73 - mantissa.log2) = intOfZ (zOfInt ((mantissa / 2 ^ 21 : Nat) : Int))
  rw [intOfZ_zOfInt]
  exact (Int.natCast_ediv _ _).symm.trans (congrArg Int.ofNat natural)

private theorem remaining_fraction_properties64 (mantissa : Nat) (small : mantissa < 2 ^ 52) :
    let value : float := ⟨UnpackedFloat.pack Format.binary64
      (normalize Format.binary64 (mantissa : Int) (-21) .positive)⟩
    isNaN64 value = false ∧
      Float.to_int value = some (Integers.Int.repr (ZArith.BinInt.Z.of_nat (mantissa / 2 ^ 21))) := by
  by_cases positive : 0 < mantissa
  · have logarithm : mantissa.log2 ≤ 51 := by
      have := (Nat.log2_lt (Nat.ne_of_gt positive)).mpr small
      omega
    have comparison : compare (mantissa : Int) 0 = .gt := Int.compare_eq_gt.mpr (by omega)
    simp only [normalize, comparison, Int.toNat_natCast]
    have bits := remaining_fraction_pack64 mantissa positive logarithm
    have valueEq : (⟨UnpackedFloat.pack Format.binary64 (round Format.binary64 .positive mantissa (-21))⟩ : float) =
        encode64 (.B754_finite false (posOfNat (mantissa * 2 ^ (52 - mantissa.log2)))
          (zOfInt ((mantissa.log2 : Int) - 73))) := float.ext bits
    rw [valueEq]
    have decoded := conversion_encode64_decode
      (⟨.B754_finite false (posOfNat (mantissa * 2 ^ (52 - mantissa.log2)))
        (zOfInt ((mantissa.log2 : Int) - 73)),
        remaining_fraction_certificate64 mantissa positive logarithm⟩ : Binary.CertifiedBinaryFloat z53 z1024)
    constructor
    · rw [← conversion_isNaN64_decode]
      erw [decoded]
      rfl
    · unfold Float.to_int
      erw [decoded]
      have truncated := remaining_fraction_trunc64 mantissa positive logarithm
      have lower : ZArith.Zbool.Zle_bool Integers.Int.min_signed
          (ZArith.BinInt.Z.of_nat (mantissa / 2 ^ 21)) = true := by
        change (if -2147483648 ≤ intOfZ (zOfInt (mantissa / 2 ^ 21)) then true else false) = true
        rw [intOfZ_zOfInt]
        exact if_pos (by omega)
      have upper : ZArith.Zbool.Zle_bool (ZArith.BinInt.Z.of_nat (mantissa / 2 ^ 21))
          Integers.Int.max_signed = true := by
        change (if intOfZ (zOfInt (mantissa / 2 ^ 21)) ≤ 2147483647 then true else false) = true
        rw [intOfZ_zOfInt]
        exact if_pos (by omega)
      unfold IEEE754_extra.ZofB_range
      erw [truncated]
      simp only [lower, upper, Bool.true_and, ↓reduceIte]
      rfl
  · have zero : mantissa = 0 := by omega
    subst mantissa
    decide

private theorem remaining_sub_uint64
    [certificate : Binary.BinaryNormalizeCertificate z53 z1024]
    (value : float) (mantissa : positive)
    (decoded : decode64 value = .B754_finite false mantissa (.Zneg (posOfNat 21)))
    (lower : 2 ^ 52 ≤ posToNat mantissa) (upper : posToNat mantissa < 2 ^ 53) :
    Float.to_int (Float.sub value (Float.of_intu Float.ox8000_0000)) =
      some (Integers.Int.repr (ZArith.BinInt.Z.of_nat ((posToNat mantissa - 2 ^ 52) / 2 ^ 21))) := by
  let remainder := posToNat mantissa - 2 ^ 52
  have remainderSmall : remainder < 2 ^ 52 := by dsimp [remainder]; omega
  have difference : (posToNat mantissa : Int) - 4503599627370496 = (remainder : Int) := by
    dsimp [remainder]
    omega
  have unpacked := remaining_positive_normal_unpack64 value mantissa (.Zneg (posOfNat 21)) decoded lower
  have half : Float.of_intu Float.ox8000_0000 =
      encode64 (IEEE754_extra.BofZ (prec := z53) (emax := z1024)
        (ZArith.BinInt.Z.of_nat (2 ^ 31))) := by rfl
  have raw : modelBinary64 (UnpackedFloat.sub Format.binary64) value (Float.of_intu Float.ox8000_0000) =
      ⟨UnpackedFloat.pack Format.binary64 (normalize Format.binary64 (remainder : Int) (-21) .positive)⟩ := by
    apply float.ext
    unfold modelBinary64
    simp only
    rw [unpacked, half, remaining_BofZ_unpack64 (2 ^ 31) (by decide) (by decide)]
    change UnpackedFloat.pack Format.binary64
      (UnpackedFloat.sub Format.binary64 (.finite .positive (posToNat mantissa) (-21) _)
        (.finite .positive 4503599627370496 (-21) _)) = _
    simp only [UnpackedFloat.sub, decreaseExponent, Int.min_self, Int.sub_self,
      Int.toNat_zero, Nat.shiftLeft_zero, Sign.apply,
      show ((4503599627370496 : Nat) : Int) = 4503599627370496 from rfl, difference]
  have properties := remaining_fraction_properties64 remainder remainderSmall
  have valueNan : isNaN64 value = false := by
    rw [← conversion_isNaN64_decode, decoded]
    rfl
  have halfNan : isNaN64 (Float.of_intu Float.ox8000_0000) = false := by
    rw [half]
    exact remaining_BofZ_notNaN64 (2 ^ 31) (by decide) (by decide)
  unfold Float.sub
  rw [raw]
  simp only [Float.finishBinary, valueNan, halfNan, properties.1, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte]
  exact properties.2

theorem Float.to_intu_to_int_2
    [certificate : Binary.BinaryNormalizeCertificate z53 z1024] :
    Float.to_intu_to_int_2Statement := by
  intro value word compared converted
  obtain ⟨mantissa, decoded, lower, upper⟩ := remaining_uint_input value word compared converted
  have subtraction := remaining_sub_uint64 value mantissa decoded lower upper
  rw [subtraction]
  have truncated : IEEE754_extra.ZofB (decode64 value) =
      some (ZArith.BinInt.Z.of_nat (posToNat mantissa / 2 ^ 21)) := by
    rw [decoded]
    apply congrArg some
    apply intOfZ_injective
    change intOfZ (ZArith.BinInt.Z.div (.Zpos mantissa)
      (ZArith.BinInt.Z.pow_pos (.Zpos (.xO .xH)) (posOfNat 21))) = _
    rw [manual_div_pow_int]
    change (posToNat mantissa : Int) / (2 : Int) ^ 21 =
      intOfZ (zOfInt (posToNat mantissa / 2 ^ 21))
    rw [intOfZ_zOfInt]
  unfold Float.to_intu IEEE754_extra.ZofB_range at converted
  rw [truncated] at converted
  dsimp only at converted
  split at converted
  · simp only [Option.map_some, Option.some.injEq] at converted
    rw [← converted]
    apply congrArg some
    unfold Integers.Int.sub Integers.WordCore.sub
    change _ = Integers.Int.repr
      (ZArith.BinInt.Z.sub
        (Integers.Int.unsigned (Integers.Int.repr (ZArith.BinInt.Z.of_nat (posToNat mantissa / 2 ^ 21))))
        (Integers.Int.unsigned Float.ox8000_0000))
    have quotientRange : ZArith.BinInt.Z.le .Z0 (ZArith.BinInt.Z.of_nat (posToNat mantissa / 2 ^ 21)) ∧
        ZArith.BinInt.Z.le (ZArith.BinInt.Z.of_nat (posToNat mantissa / 2 ^ 21)) Integers.Int.max_unsigned := by
      constructor
      · change 0 ≤ intOfZ (zOfInt (posToNat mantissa / 2 ^ 21))
        rw [intOfZ_zOfInt]
        omega
      · change intOfZ (zOfInt (posToNat mantissa / 2 ^ 21)) ≤ 4294967295
        rw [intOfZ_zOfInt]
        omega
    rw [Integers.Int.unsigned_repr_proof_api _ quotientRange,
      show Integers.Int.unsigned Float.ox8000_0000 = ZArith.BinInt.Z.of_nat (2 ^ 31) by decide]
    congr 1
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.of_nat,
      intOfZ_zOfInt, Int.ofNat_eq_natCast]
    omega
  · simp only [Option.map_none, reduceCtorEq] at converted

end CompCert4Lean.Lib.Floats

namespace CompCert4Lean.Lib.Floats
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Flocq.IEEE754
open _root_.Float.Model
open _root_.Float.Model.UnpackedFloat

private theorem inverse_extended_add (value : ExtendedMantissa) (first second : Nat) :
    (value >>> first) >>> second = value >>> (first + second) := by
  induction second with
  | zero => rfl
  | succ second inductionHypothesis =>
      change ExtendedMantissa.shiftRightOne ((value >>> first) >>> second) =
        ExtendedMantissa.shiftRightOne (value >>> (first + second))
      rw [inductionHypothesis]

private theorem inverse_extended_fields (mantissa count : Nat) :
    (ExtendedMantissa.ofMantissaAndAccuracy mantissa .exact >>> (count + 1)) =
      ⟨mantissa / 2 ^ (count + 1), mantissa / 2 ^ count % 2 != 0,
        mantissa % 2 ^ count != 0⟩ := by
  induction count with
  | zero =>
      simp only [Nat.zero_add, Nat.pow_zero, Nat.div_one, Nat.mod_one, bne_self_eq_false]
      rfl
  | succ count inductionHypothesis =>
      change ExtendedMantissa.shiftRightOne
        (ExtendedMantissa.ofMantissaAndAccuracy mantissa .exact >>> (count + 1)) = _
      rw [inductionHypothesis]
      unfold ExtendedMantissa.shiftRightOne
      have quotient : mantissa / 2 ^ (count + 1) / 2 = mantissa / 2 ^ (count + 1 + 1) := by
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
      have sticky : (mantissa / 2 ^ count % 2 != 0 || mantissa % 2 ^ count != 0) =
          (mantissa % 2 ^ (count + 1) != 0) := by
        have modulo : mantissa % 2 ^ (count + 1) =
            mantissa % 2 ^ count + 2 ^ count * (mantissa / 2 ^ count % 2) := by
          rw [Nat.pow_succ, Nat.mod_mul]
        rw [modulo]
        have power := Nat.two_pow_pos count
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq]
        constructor
        · intro nonzero
          rcases nonzero with high | low
          · have product := Nat.mul_pos power (Nat.pos_of_ne_zero high)
            omega
          · omega
        · intro nonzero
          by_cases high : mantissa / 2 ^ count % 2 = 0
          · right
            rw [high, Nat.mul_zero, Nat.add_zero] at nonzero
            exact nonzero
          · exact Or.inl high
      simp only [quotient, sticky]

private theorem inverse_fraction_extended (mantissa count : Nat) :
    ExtendedMantissa.ofMantissaAndAccuracy (mantissa / 2 ^ count)
      (accuracyOfFraction (mantissa % 2 ^ count) (2 ^ count)) =
      ExtendedMantissa.ofMantissaAndAccuracy mantissa .exact >>> count := by
  cases count with
  | zero => simp [accuracyOfFraction, extendedMantissa_shift_zero, Nat.mod_one]
  | succ count =>
      rw [inverse_extended_fields]
      let half := 2 ^ count
      have halfPositive : 0 < half := Nat.two_pow_pos count
      have remainderBound : mantissa % (half * 2) < half * 2 := Nat.mod_lt _ (by omega)
      have high : mantissa % (half * 2) / half = mantissa / half % 2 := Nat.mod_mul_right_div_self _ _ _
      have low : mantissa % (half * 2) % half = mantissa % half := Nat.mod_mul_right_mod _ _ _
      have splitRemainder := Nat.mod_add_div (mantissa % (half * 2)) half
      rw [high, low] at splitRemainder
      have digitBound : mantissa / half % 2 < 2 := Nat.mod_lt _ (by decide)
      change ExtendedMantissa.ofMantissaAndAccuracy (mantissa / (half * 2))
        (accuracyOfFraction (mantissa % (half * 2)) (half * 2)) =
          ⟨mantissa / (half * 2), mantissa / half % 2 != 0, mantissa % half != 0⟩
      unfold accuracyOfFraction
      by_cases exactRemainder : mantissa % (half * 2) = 0
      · rw [if_pos exactRemainder]
        have highZero : mantissa / half % 2 = 0 := by
          rw [exactRemainder, Nat.zero_div] at high
          exact high.symm
        have lowZero : mantissa % half = 0 := by
          rw [exactRemainder, Nat.zero_mod] at low
          exact low.symm
        simp [ExtendedMantissa.ofMantissaAndAccuracy, highZero, lowZero]
      · rw [if_neg exactRemainder]
        by_cases roundZero : mantissa / half % 2 = 0
        · rw [roundZero, Nat.mul_zero, Nat.add_zero] at splitRemainder
          have less : 2 * (mantissa % (half * 2)) < half * 2 := by
            have remainderLow := Nat.mod_lt mantissa halfPositive
            omega
          have compared : compare (2 * (mantissa % (half * 2))) (half * 2) = .lt := Nat.compare_eq_lt.mpr less
          have lowNonzero : mantissa % half ≠ 0 := by omega
          simp [compared, ExtendedMantissa.ofMantissaAndAccuracy, roundZero, lowNonzero]
        · have highOne : mantissa / half % 2 = 1 := by omega
          rw [highOne, Nat.mul_one] at splitRemainder
          by_cases stickyZero : mantissa % half = 0
          · have equal : 2 * (mantissa % (half * 2)) = half * 2 := by omega
            have compared : compare (2 * (mantissa % (half * 2))) (half * 2) = .eq := Nat.compare_eq_eq.mpr equal
            simp [compared, ExtendedMantissa.ofMantissaAndAccuracy, highOne, stickyZero]
          · have greater : half * 2 < 2 * (mantissa % (half * 2)) := by omega
            have compared : compare (2 * (mantissa % (half * 2))) (half * 2) = .gt := Nat.compare_eq_gt.mpr greater
            simp [compared, ExtendedMantissa.ofMantissaAndAccuracy, highOne, stickyZero]

private theorem inverse_extended_scales (mantissa firstScale secondScale firstShift secondShift : Nat)
    (equal : firstScale + secondShift = secondScale + firstShift) :
    (ExtendedMantissa.ofMantissaAndAccuracy (mantissa * 2 ^ firstScale) .exact >>> firstShift) =
      (ExtendedMantissa.ofMantissaAndAccuracy (mantissa * 2 ^ secondScale) .exact >>> secondShift) := by
  by_cases scales : firstScale ≤ secondScale
  · have shift : secondShift = (secondScale - firstScale) + firstShift := by omega
    have scaled : mantissa * 2 ^ secondScale =
        (mantissa * 2 ^ firstScale) * 2 ^ (secondScale - firstScale) := by
      rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le scales]
    rw [scaled, shift, extendedMantissa_shift_pow_add]
  · have shift : firstShift = (firstScale - secondScale) + secondShift := by omega
    have scaled : mantissa * 2 ^ firstScale =
        (mantissa * 2 ^ secondScale) * 2 ^ (firstScale - secondScale) := by
      rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le (by omega)]
    rw [scaled, shift, extendedMantissa_shift_pow_add]

private theorem inverse_log2_quotient (mantissa count : Nat)
    (positive : 0 < mantissa / 2 ^ count) :
    (mantissa / 2 ^ count).log2 + count = mantissa.log2 := by
  have mantissaPositive : 0 < mantissa := by
    have bound := Nat.div_le_self mantissa (2 ^ count)
    omega
  have bounds := (Nat.log2_eq_iff (Nat.ne_of_gt positive)).mp rfl
  have lower := Nat.mul_le_mul_right (2 ^ count) bounds.1
  have product := Nat.div_mul_le_self mantissa (2 ^ count)
  have lowerCombined : 2 ^ ((mantissa / 2 ^ count).log2 + count) ≤ mantissa := by
    rw [Nat.pow_add]
    omega
  have upperCombined : mantissa < 2 ^ ((mantissa / 2 ^ count).log2 + count + 1) := by
    have bound := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos count)).mp bounds.2
    rw [← Nat.pow_add] at bound
    simpa only [Nat.add_right_comm] using bound
  exact ((Nat.log2_eq_iff (Nat.ne_of_gt mantissaPositive)).mpr
    ⟨lowerCombined, upperCombined⟩).symm

private theorem inverse_division_shift (spec : Format) (precision mantissa : Nat)
    (specPrecision : spec.mantissaBits = precision + 1)
    (precisionPositive : 0 < precision) (positive : 0 < mantissa)
    (numeratorExponent denominatorExponent : Int) :
    let divided := divCore spec mantissa numeratorExponent (2 ^ precision) denominatorExponent
    shiftToTargetExponent spec divided.1 divided.2.1 divided.2.2 =
      shiftToTargetExponent spec (mantissa * 2 ^ precision)
        (numeratorExponent - denominatorExponent - 2 * (precision : Int)) .exact := by
  let difference := numeratorExponent - denominatorExponent
  let target := min difference
    (max ((mantissa.log2 : Int) + difference - 2 * (precision : Int) - 1) spec.minExponent)
  let shift := (difference - target).toNat
  let numerator := mantissa * 2 ^ shift
  let quotient := numerator / 2 ^ precision
  let finalTarget := max ((mantissa.log2 : Int) + difference - 2 * (precision : Int)) spec.minExponent
  have targetLower : target ≤ difference := by dsimp [target]; omega
  have shiftCast : (shift : Int) = difference - target := by dsimp [shift]; omega
  have numeratorPositive : 0 < numerator := Nat.mul_pos positive (Nat.two_pow_pos shift)
  have numeratorDigits : numerator.log2 = mantissa.log2 + shift :=
    log2_mul_pow mantissa shift (Nat.ne_of_gt positive)
  have targetFinal : target ≤ finalTarget := by dsimp [target, finalTarget]; omega
  have productLower : difference - 2 * (precision : Int) ≤ finalTarget := by
    dsimp [finalTarget]
    omega
  have divShape : divCore spec mantissa numeratorExponent (2 ^ precision) denominatorExponent =
      (quotient, target, accuracyOfFraction (numerator % 2 ^ precision) (2 ^ precision)) := by
    unfold divCore totalExponent Format.targetExponent
    rw [Nat.log2_two_pow, specPrecision]
    have targetEq : min (numeratorExponent - denominatorExponent)
        (max (((mantissa.log2 : Int) + 1 + numeratorExponent -
          ((precision : Int) + 1 + denominatorExponent)) - ((precision + 1 : Nat) : Int)) spec.minExponent) = target := by
      dsimp [target, difference]
      congr 2
      omega
    simp only [targetEq, Nat.shiftLeft_eq]
    rfl
  have quotientTarget : spec.targetExponent (totalExponent quotient target) = finalTarget := by
    by_cases quotientPositive : 0 < quotient
    · have digits := inverse_log2_quotient numerator precision quotientPositive
      rw [numeratorDigits] at digits
      change quotient.log2 + precision = mantissa.log2 + shift at digits
      unfold Format.targetExponent totalExponent
      rw [specPrecision]
      change max ((quotient.log2 : Int) + 1 + target - ((precision + 1 : Nat) : Int)) spec.minExponent =
        max ((mantissa.log2 : Int) + difference - 2 * (precision : Int)) spec.minExponent
      apply congrArg (fun exponent : Int => max exponent spec.minExponent)
      omega
    · have quotientZero : quotient = 0 := Nat.eq_zero_of_not_pos quotientPositive
      have numeratorSmall : numerator < 2 ^ precision := by
        rcases Nat.div_eq_zero_iff.mp quotientZero with zero | small
        · have := Nat.two_pow_pos precision
          omega
        · exact small
      have digitsSmall := (Nat.log2_lt (Nat.ne_of_gt numeratorPositive)).mpr numeratorSmall
      rw [numeratorDigits] at digitsSmall
      have targetMinimum : target ≤ spec.minExponent := by
        change min difference (max ((mantissa.log2 : Int) + difference - 2 * (precision : Int) - 1)
          spec.minExponent) ≤ spec.minExponent
        omega
      have finalMinimum : finalTarget = spec.minExponent := by dsimp [finalTarget]; omega
      rw [quotientZero, finalMinimum]
      unfold Format.targetExponent totalExponent
      rw [specPrecision]
      change max ((0 : Int) + 1 + target - ((precision + 1 : Nat) : Int)) spec.minExponent = spec.minExponent
      omega
  have productTarget : spec.targetExponent
      (totalExponent (mantissa * 2 ^ precision) (difference - 2 * (precision : Int))) = finalTarget := by
    unfold Format.targetExponent totalExponent
    rw [log2_mul_pow _ _ (Nat.ne_of_gt positive), specPrecision]
    dsimp [finalTarget]
    congr 1
    omega
  rw [divShape]
  change shiftToTargetExponent spec quotient target
    (accuracyOfFraction (numerator % 2 ^ precision) (2 ^ precision)) = _
  unfold shiftToTargetExponent
  rw [quotientTarget, productTarget]
  unfold shiftToExponent
  apply Prod.ext
  · dsimp only
    rw [inverse_fraction_extended numerator precision, inverse_extended_add]
    apply inverse_extended_scales
    have firstCast : ((finalTarget - target).toNat : Int) = finalTarget - target := by omega
    have secondCast : ((finalTarget - (difference - 2 * (precision : Int))).toNat : Int) =
        finalTarget - (difference - 2 * (precision : Int)) := by omega
    omega
  · dsimp only
    have firstCast : ((finalTarget - target).toNat : Int) = finalTarget - target := by omega
    have secondCast : ((finalTarget - (difference - 2 * (precision : Int))).toNat : Int) =
        finalTarget - (difference - 2 * (precision : Int)) := by omega
    omega

private theorem inverse_unpacked_div_mul (spec : Format) (precision : Nat)
    (specPrecision : spec.mantissaBits = precision + 1) (precisionPositive : 0 < precision)
    (value : UnpackedFloat) (sign : Sign) (exponent : Int) :
    UnpackedFloat.div spec value (.finite sign (2 ^ precision) exponent (Nat.two_pow_pos precision)) =
      UnpackedFloat.mul spec value
        (.finite sign (2 ^ precision) (-exponent - 2 * (precision : Int)) (Nat.two_pow_pos precision)) := by
  have signDivision (other : Sign) : other / sign = other * sign := by
    cases other <;> cases sign <;> rfl
  cases value with
  | notANumber => rfl
  | infinity other => simp only [UnpackedFloat.div, UnpackedFloat.mul, signDivision]
  | zero other => simp only [UnpackedFloat.div, UnpackedFloat.mul, signDivision]
  | finite other mantissa numeratorExponent positive =>
      have aligned := inverse_division_shift spec precision mantissa specPrecision precisionPositive positive
        numeratorExponent exponent
      cases result : divCore spec mantissa numeratorExponent (2 ^ precision) exponent with
      | mk quotient rest =>
        cases rest with
        | mk quotientExponent accuracy =>
          rw [result] at aligned
          dsimp only at aligned
          simp only [UnpackedFloat.div, UnpackedFloat.mul, result, signDivision]
          have exponentEq : numeratorExponent + (-exponent - 2 * (precision : Int)) =
              numeratorExponent - exponent - 2 * (precision : Int) := by omega
          rw [exponentEq]
          unfold roundWithAccuracy
          rw [aligned]

private theorem inverse_normal_bits64 (value : float) (sign : Bool)
    (mantissa : positive) (exponent : Z)
    (decoded : decode64 value = .B754_finite sign mantissa exponent)
    (lower : 2 ^ 52 ≤ posToNat mantissa) :
    value.bits = packComponents Format.binary64 (if sign then .negative else .positive)
      (BitVec.ofNat 11 (intOfZ exponent + 1075).toNat)
      (BitVec.ofNat 52 (posToNat mantissa)) := by
  cases sign with
  | false => exact remaining_positive_normal_bits64 value mantissa exponent decoded lower
  | true =>
    have fields := remaining_decode64_fields value true mantissa exponent decoded
    have rawLower : 2 ^ 63 ≤ value.bits.toNat := by
      have signTrue := fields.1.symm
      exact of_decide_eq_true signTrue
    have rawUpper : value.bits.toNat < 2 ^ 64 := value.bits.isLt
    have fractionBound : value.bits.toNat % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (by decide)
    rcases fields.2 with subnormal | ⟨exponentEq, mantissaEq, exponentPositive, exponentBound⟩
    · omega
    · have quotientBound : value.bits.toNat / 2 ^ 52 < 4096 := by omega
      have quotientMod : value.bits.toNat / 2 ^ 52 % 2048 = value.bits.toNat / 2 ^ 52 - 2048 := by omega
      have exponentNat : (intOfZ exponent + 1075).toNat = value.bits.toNat / 2 ^ 52 % 2048 := by omega
      have exponentSmall : value.bits.toNat / 2 ^ 52 % 2048 < 2048 := Nat.mod_lt _ (by decide)
      apply BitVec.eq_of_toNat_eq
      simp only [↓reduceIte, packComponents, BitVec.toNat_append, Sign.toBitVec, BitVec.toNat_ofNat,
        exponentNat, Nat.mod_eq_of_lt exponentSmall]
      change value.bits.toNat = (1 <<< 11 ||| value.bits.toNat / 2 ^ 52 % 2048) <<< 52 ||| posToNat mantissa % 2 ^ 52
      simp only [Nat.shiftLeft_eq]
      rw [show (1 : Nat) * 2 ^ 11 = 2 ^ 11 * 1 by rfl,
        ← Nat.two_pow_add_eq_or_of_lt exponentSmall]
      rw [Nat.mul_comm _ (2 ^ 52),
        ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos 52))]
      omega

private theorem inverse_unpack_components64 (sign : Sign) (mantissa exponent : Nat)
    (lower : 2 ^ 52 ≤ mantissa) (upper : mantissa < 2 ^ 53)
    (emin : 0 < exponent) (emax : exponent < 2047) :
    UnpackedFloat.unpack Format.binary64
      (packComponents Format.binary64 sign (BitVec.ofNat 11 exponent) (BitVec.ofNat 52 mantissa)) =
      .finite sign mantissa ((exponent : Int) - 1075) (by omega) := by
  have signPart (exponentBits : BitVec 11) (mantissaBits : BitVec 52) :
      unpackSign (spec := Format.binary64) (packComponents Format.binary64 sign exponentBits mantissaBits) =
        sign.toBitVec := by
    cases sign <;> change BitVec.extractLsb 63 63 (_ ++ exponentBits ++ mantissaBits) = _ <;> bv_decide
  have exponentNonzero : BitVec.ofNat 11 exponent ≠ 0#11 := by
    intro equality
    have := congrArg BitVec.toNat equality
    change exponent % 2048 = 0 at this
    omega
  have exponentFinite : BitVec.ofNat 11 exponent ≠ -1#11 := by
    intro equality
    have := congrArg BitVec.toNat equality
    change exponent % 2048 = 2047 at this
    omega
  have combined : (1#1 ++ BitVec.ofNat 52 mantissa).toNat = mantissa := by
    rw [BitVec.toNat_append, Nat.shiftLeft_eq]
    change 4503599627370496 ||| mantissa % 4503599627370496 = mantissa
    rw [show 4503599627370496 = 2 ^ 52 * 1 by rfl,
      ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos 52))]
    omega
  unfold UnpackedFloat.unpack
  dsimp only
  simp only [unpackMantissa_packComponents (spec := Format.binary64),
    unpackExponent_packComponents (spec := Format.binary64), signPart,
    exponentNonzero, exponentFinite, ↓reduceIte, combined,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show exponent < 2 ^ 11 by omega)]
  cases sign <;> rfl

private theorem inverse_normal_unpack64 (value : float) (sign : Bool)
    (mantissa : positive) (exponent : Z)
    (decoded : decode64 value = .B754_finite sign mantissa exponent)
    (lower : 2 ^ 52 ≤ posToNat mantissa) :
    UnpackedFloat.unpack Format.binary64 value.bits =
      .finite (if sign then .negative else .positive) (posToNat mantissa) (intOfZ exponent)
        (posToNat_positive mantissa) := by
  have fields := remaining_decode64_fields value sign mantissa exponent decoded
  have fractionBound : value.bits.toNat % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have exponentBounds : 0 < (intOfZ exponent + 1075).toNat ∧
      (intOfZ exponent + 1075).toNat < 2047 := by
    rcases fields.2 with subnormal | normal <;> omega
  have mantissaUpper : posToNat mantissa < 2 ^ 53 := by
    rcases fields.2 with subnormal | normal <;> omega
  rw [inverse_normal_bits64 value sign mantissa exponent decoded lower]
  rw [inverse_unpack_components64 _ (posToNat mantissa) _ lower mantissaUpper
    exponentBounds.1 exponentBounds.2]
  have exponentEq : ((intOfZ exponent + 1075).toNat : Int) - 1075 = intOfZ exponent := by
    rcases fields.2 with subnormal | normal <;> omega
  simp only [exponentEq]

private theorem inverse_result_shape {precision maximum : Z}
    [IEEE754_extra.Prec_gt_0 precision] [IEEE754_extra.Prec_lt_emax precision maximum]
    [IEEE754_extra.Bexact_inverse_certificate precision maximum]
    (value result : Binary.binary_float precision maximum)
    (returned : IEEE754_extra.Bexact_inverse value = some result) :
    ∃ sign exponent,
      value = .B754_finite sign (IEEE754_extra.Bexact_inverse_mantissa (prec := precision)) exponent ∧
      result = .B754_finite sign (IEEE754_extra.Bexact_inverse_mantissa (prec := precision))
        (IEEE754_extra.Zsub (IEEE754_extra.Zopp exponent)
          (IEEE754_extra.Zmul (IEEE754_extra.Zsub precision IEEE754_extra.Zone) IEEE754_extra.Ztwo)) := by
  cases value with
  | B754_zero sign => simp [IEEE754_extra.Bexact_inverse] at returned
  | B754_infinity sign => simp [IEEE754_extra.Bexact_inverse] at returned
  | B754_nan sign payload => simp [IEEE754_extra.Bexact_inverse] at returned
  | B754_finite sign mantissa exponent =>
      by_cases recognized : mantissa = IEEE754_extra.Bexact_inverse_mantissa (prec := precision)
      · subst mantissa
        simp only [IEEE754_extra.Bexact_inverse, ↓reduceDIte] at returned
        split at returned
        · split at returned
          · exact ⟨sign, exponent, rfl, (Option.some.inj returned).symm⟩
          · contradiction
        · contradiction
      · simp [IEEE754_extra.Bexact_inverse, recognized] at returned

theorem Float.div_mul_inverse
    [certificate : IEEE754_extra.Bexact_inverse_certificate z53 z1024] :
    Float.div_mul_inverseStatement := by
  intro numerator divisor reciprocal inverse
  unfold Float.exact_inverse at inverse
  cases returned : IEEE754_extra.Bexact_inverse (prec := z53) (emax := z1024) (decode64 divisor) with
  | none =>
      rw [returned] at inverse
      change (none : Option float) = some reciprocal at inverse
      contradiction
  | some result =>
      have encoded : encode64 result = reciprocal := by
        rw [returned] at inverse
        change some (encode64 result) = some reciprocal at inverse
        exact Option.some.inj inverse
      subst reciprocal
      rcases inverse_result_shape (precision := z53) (maximum := z1024) (decode64 divisor) result returned with
        ⟨sign, exponent, decoded, resultShape⟩
      have valid := IEEE754_extra.Bexact_inverse_result_obligation_proof (prec := z53) (emax := z1024)
        ⟨decode64 divisor, manual_decode64_certificate divisor⟩ result returned
      have reciprocalDecoded : decode64 (encode64 result) = result := conversion_encode64_decode ⟨result, valid⟩
      have mantissaValue : posToNat (IEEE754_extra.Bexact_inverse_mantissa (prec := z53)) = 2 ^ 52 := by decide
      have divisorUnpacked := inverse_normal_unpack64 divisor sign _ exponent decoded (by rw [mantissaValue]; omega)
      have reciprocalUnpacked := inverse_normal_unpack64 (encode64 result) sign _ _
        (reciprocalDecoded.trans resultShape) (by rw [mantissaValue]; omega)
      have exponentValue : intOfZ (IEEE754_extra.Zsub (IEEE754_extra.Zopp exponent)
          (IEEE754_extra.Zmul (IEEE754_extra.Zsub z53 IEEE754_extra.Zone) IEEE754_extra.Ztwo)) =
          -intOfZ exponent - 2 * (52 : Int) := by
        change intOfZ (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.opp exponent)
          (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.sub z53 IEEE754_extra.Zone) IEEE754_extra.Ztwo)) = _
        simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.opp, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
        rfl
      have modelEqual : modelBinary64 (UnpackedFloat.div Format.binary64) numerator divisor =
          modelBinary64 (UnpackedFloat.mul Format.binary64) numerator (encode64 result) := by
        unfold modelBinary64
        rw [divisorUnpacked, reciprocalUnpacked]
        simp only [mantissaValue, exponentValue]
        rw [inverse_unpacked_div_mul Format.binary64 52 (by rfl) (by decide)]
        rfl
      have divisorNan : isNaN64 divisor = false := by
        rw [← conversion_isNaN64_decode, decoded]
        rfl
      have reciprocalNan : isNaN64 (encode64 result) = false := by
        rw [← conversion_isNaN64_decode, reciprocalDecoded, resultShape]
        rfl
      simp only [Float.div, Float.mul, modelEqual, Float.finishBinary, divisorNan, reciprocalNan,
        Float.binop_nan, Float.cons_pl, Bool.false_eq_true, ↓reduceIte]

private theorem inverse_decode32_fields (value : float32) (sign : Bool)
    (mantissa : positive) (exponent : Z)
    (decoded : decode32 value = .B754_finite sign mantissa exponent) :
    sign = decide (2 ^ 31 ≤ value.bits.toNat) ∧
    ((intOfZ exponent = -149 ∧ posToNat mantissa = value.bits.toNat % 2 ^ 23 ∧
      value.bits.toNat / 2 ^ 23 % 256 = 0) ∨
      (intOfZ exponent = ((value.bits.toNat / 2 ^ 23 % 256 : Nat) : Int) - 150 ∧
       posToNat mantissa = value.bits.toNat % 2 ^ 23 + 2 ^ 23 ∧
       0 < value.bits.toNat / 2 ^ 23 % 256 ∧
       value.bits.toNat / 2 ^ 23 % 256 < 255)) := by
  let rawExponent := value.bits.toNat / 2 ^ 23 % 256
  let rawMantissa := value.bits.toNat % 2 ^ 23
  have rawBound : rawExponent < 256 := Nat.mod_lt _ (by decide)
  have division := zdiv_nat_f64 value.bits.toNat (2 ^ 23) (by decide)
  have remainder := zmod_nat_f64 value.bits.toNat (2 ^ 23) (by decide)
  have exponentRemainder := zmod_nat_f64 (value.bits.toNat / 2 ^ 23) 256 (by decide)
  change @Eq (Binary.binary_float z24 z128) (decode32 value)
    (.B754_finite sign mantissa exponent) at decoded
  unfold decode32 Bits.b32_of_bits_unchecked Bits.binary_float_of_bits_unchecked
    Bits.binary_float_of_bits_aux Bits.split_bits at decoded
  dsimp only at decoded
  simp only [show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 23) =
      ZArith.BinInt.Z.of_nat (2 ^ 23) by decide,
    show Bits.Zpower Bits.Ztwo (ZArith.BinInt.Z.of_nat 8) =
      ZArith.BinInt.Z.of_nat 256 by decide,
    division, remainder, exponentRemainder] at decoded
  have signTest : Bits.Zle_bool
      (Bits.Zmul (ZArith.BinInt.Z.of_nat (2 ^ 23)) (ZArith.BinInt.Z.of_nat 256))
      (ZArith.BinInt.Z.of_nat value.bits.toNat) = decide (2 ^ 31 ≤ value.bits.toNat) := by
    change (if (2147483648 : Int) ≤ intOfZ (zOfInt value.bits.toNat) then true else false) = _
    rw [intOfZ_zOfInt]
    split
    · symm
      apply decide_eq_true
      omega
    · symm
      apply decide_eq_false
      omega
  rw [signTest] at decoded
  by_cases zeroExponent : rawExponent = 0
  · have zeroTest : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat rawExponent) Bits.Z0 = true := by
      rw [zeroExponent]
      rfl
    rw [zeroTest] at decoded
    simp only [↓reduceIte] at decoded
    by_cases zeroMantissa : rawMantissa = 0
    · have mantissaZero : ZArith.BinInt.Z.of_nat (value.bits.toNat % 2 ^ 23) = .Z0 := by
        rw [show value.bits.toNat % 2 ^ 23 = 0 from zeroMantissa]
        rfl
      simp only [mantissaZero, Binary.FF2B_unchecked] at decoded
      contradiction
    · have positive := Nat.pos_of_ne_zero zeroMantissa
      rw [remaining_zofnat_positive rawMantissa positive] at decoded
      change Binary.B754_finite (decide (2 ^ 31 ≤ value.bits.toNat))
        (posOfNat rawMantissa) (Bits.emin _ _) = _ at decoded
      injection decoded with signEq mantissaEq exponentEq
      refine ⟨signEq.symm, Or.inl ⟨?_, ?_, zeroExponent⟩⟩
      · rw [← exponentEq]
        rfl
      · rw [← mantissaEq, posToNat_posOfNat positive]
  · have zeroTest : Bits.Zeq_bool (ZArith.BinInt.Z.of_nat rawExponent) Bits.Z0 = false :=
      conversion_zeq_nat_false zeroExponent
    rw [zeroTest] at decoded
    simp only [Bool.false_eq_true, ↓reduceIte] at decoded
    have maxValue : Bits.Zsub (ZArith.BinInt.Z.of_nat 256) Bits.Zone =
        ZArith.BinInt.Z.of_nat 255 := by decide
    rw [maxValue] at decoded
    by_cases maxExponent : rawExponent = 255
    · rw [conversion_zeq_nat_true maxExponent] at decoded
      simp only [↓reduceIte] at decoded
      cases mantissaValue : ZArith.BinInt.Z.of_nat (value.bits.toNat % 2 ^ 23) <;>
        simp only [mantissaValue, Binary.FF2B_unchecked] at decoded <;> contradiction
    · rw [conversion_zeq_nat_false maxExponent] at decoded
      simp only [Bool.false_eq_true, ↓reduceIte] at decoded
      have sum : Bits.Zadd (ZArith.BinInt.Z.of_nat rawMantissa)
          (ZArith.BinInt.Z.of_nat (2 ^ 23)) =
          ZArith.BinInt.Z.of_nat (rawMantissa + 2 ^ 23) := by
        apply intOfZ_injective
        simp only [Bits.Zadd, ZArith.BinInt.Z.add, ZArith.BinInt.Z.of_nat,
          intOfZ_zOfInt, Int.ofNat_eq_natCast, Int.natCast_add]
      rw [sum, remaining_zofnat_positive (rawMantissa + 2 ^ 23) (by omega)] at decoded
      change Binary.B754_finite (decide (2 ^ 31 ≤ value.bits.toNat))
        (posOfNat (rawMantissa + 2 ^ 23))
        (Bits.Zsub (Bits.Zadd (ZArith.BinInt.Z.of_nat rawExponent) (Bits.emin _ _)) Bits.Zone) = _ at decoded
      injection decoded with signEq mantissaEq exponentEq
      refine ⟨signEq.symm, Or.inr ⟨?_, ?_, by omega, by omega⟩⟩
      · rw [← exponentEq]
        simp only [Bits.Zsub, Bits.Zadd, ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add,
          ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
        change (rawExponent : Int) + (-149) - 1 = (rawExponent : Int) - 150
        omega
      · rw [← mantissaEq, posToNat_posOfNat (by omega)]

private theorem inverse_positive_normal_bits32 (value : float32)
    (mantissa : positive) (exponent : Z)
    (decoded : decode32 value = .B754_finite false mantissa exponent)
    (lower : 2 ^ 23 ≤ posToNat mantissa) :
    value.bits = packComponents Format.binary32 .positive
      (BitVec.ofNat 8 (intOfZ exponent + 150).toNat)
      (BitVec.ofNat 23 (posToNat mantissa)) := by
  have fields := inverse_decode32_fields value false mantissa exponent decoded
  have rawSmall : value.bits.toNat < 2 ^ 31 := by
    have signFalse := fields.1.symm
    simp only [decide_eq_false_iff_not] at signFalse
    omega
  have fractionBound : value.bits.toNat % 2 ^ 23 < 2 ^ 23 := Nat.mod_lt _ (by decide)
  rcases fields.2 with subnormal | ⟨exponentEq, mantissaEq, exponentPositive, exponentBound⟩
  · omega
  · have quotientBound : value.bits.toNat / 2 ^ 23 < 256 := by omega
    have quotientMod : value.bits.toNat / 2 ^ 23 % 256 = value.bits.toNat / 2 ^ 23 := Nat.mod_eq_of_lt quotientBound
    rw [quotientMod] at exponentEq exponentPositive exponentBound
    have exponentNat : (intOfZ exponent + 150).toNat = value.bits.toNat / 2 ^ 23 := by omega
    apply BitVec.eq_of_toNat_eq
    simp only [packComponents, BitVec.toNat_append, Sign.toBitVec, BitVec.toNat_ofNat,
      Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or, exponentNat,
      Nat.mod_eq_of_lt quotientBound]
    rw [Nat.shiftLeft_eq, Nat.mul_comm _ (2 ^ 23),
      ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos 23))]
    omega

private theorem inverse_normal_bits32 (value : float32) (sign : Bool)
    (mantissa : positive) (exponent : Z)
    (decoded : decode32 value = .B754_finite sign mantissa exponent)
    (lower : 2 ^ 23 ≤ posToNat mantissa) :
    value.bits = packComponents Format.binary32 (if sign then .negative else .positive)
      (BitVec.ofNat 8 (intOfZ exponent + 150).toNat)
      (BitVec.ofNat 23 (posToNat mantissa)) := by
  cases sign with
  | false => exact inverse_positive_normal_bits32 value mantissa exponent decoded lower
  | true =>
    have fields := inverse_decode32_fields value true mantissa exponent decoded
    have rawLower : 2 ^ 31 ≤ value.bits.toNat := by
      have signTrue := fields.1.symm
      exact of_decide_eq_true signTrue
    have rawUpper : value.bits.toNat < 2 ^ 32 := value.bits.isLt
    have fractionBound : value.bits.toNat % 2 ^ 23 < 2 ^ 23 := Nat.mod_lt _ (by decide)
    rcases fields.2 with subnormal | ⟨exponentEq, mantissaEq, exponentPositive, exponentBound⟩
    · omega
    · have quotientBound : value.bits.toNat / 2 ^ 23 < 512 := by omega
      have quotientMod : value.bits.toNat / 2 ^ 23 % 256 = value.bits.toNat / 2 ^ 23 - 256 := by omega
      have exponentNat : (intOfZ exponent + 150).toNat = value.bits.toNat / 2 ^ 23 % 256 := by omega
      have exponentSmall : value.bits.toNat / 2 ^ 23 % 256 < 256 := Nat.mod_lt _ (by decide)
      apply BitVec.eq_of_toNat_eq
      simp only [↓reduceIte, packComponents, BitVec.toNat_append, Sign.toBitVec, BitVec.toNat_ofNat,
        exponentNat, Nat.mod_eq_of_lt exponentSmall]
      change value.bits.toNat = (1 <<< 8 ||| value.bits.toNat / 2 ^ 23 % 256) <<< 23 ||| posToNat mantissa % 2 ^ 23
      simp only [Nat.shiftLeft_eq]
      rw [show (1 : Nat) * 2 ^ 8 = 2 ^ 8 * 1 by rfl,
        ← Nat.two_pow_add_eq_or_of_lt exponentSmall]
      rw [Nat.mul_comm _ (2 ^ 23),
        ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos 23))]
      omega

private theorem inverse_unpack_components32 (sign : Sign) (mantissa exponent : Nat)
    (lower : 2 ^ 23 ≤ mantissa) (upper : mantissa < 2 ^ 24)
    (emin : 0 < exponent) (emax : exponent < 255) :
    UnpackedFloat.unpack Format.binary32
      (packComponents Format.binary32 sign (BitVec.ofNat 8 exponent) (BitVec.ofNat 23 mantissa)) =
      .finite sign mantissa ((exponent : Int) - 150) (by omega) := by
  have signPart (exponentBits : BitVec 8) (mantissaBits : BitVec 23) :
      unpackSign (spec := Format.binary32) (packComponents Format.binary32 sign exponentBits mantissaBits) =
        sign.toBitVec := by
    cases sign <;> change BitVec.extractLsb 31 31 (_ ++ exponentBits ++ mantissaBits) = _ <;> bv_decide
  have exponentNonzero : BitVec.ofNat 8 exponent ≠ 0#8 := by
    intro equality
    have := congrArg BitVec.toNat equality
    change exponent % 256 = 0 at this
    omega
  have exponentFinite : BitVec.ofNat 8 exponent ≠ -1#8 := by
    intro equality
    have := congrArg BitVec.toNat equality
    change exponent % 256 = 255 at this
    omega
  have combined : (1#1 ++ BitVec.ofNat 23 mantissa).toNat = mantissa := by
    rw [BitVec.toNat_append, Nat.shiftLeft_eq]
    change 8388608 ||| mantissa % 8388608 = mantissa
    rw [show 8388608 = 2 ^ 23 * 1 by rfl,
      ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos 23))]
    omega
  unfold UnpackedFloat.unpack
  dsimp only
  simp only [unpackMantissa_packComponents (spec := Format.binary32),
    unpackExponent_packComponents (spec := Format.binary32), signPart,
    exponentNonzero, exponentFinite, ↓reduceIte, combined,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show exponent < 2 ^ 8 by omega)]
  cases sign <;> rfl

private theorem inverse_normal_unpack32 (value : float32) (sign : Bool)
    (mantissa : positive) (exponent : Z)
    (decoded : decode32 value = .B754_finite sign mantissa exponent)
    (lower : 2 ^ 23 ≤ posToNat mantissa) :
    UnpackedFloat.unpack Format.binary32 value.bits =
      .finite (if sign then .negative else .positive) (posToNat mantissa) (intOfZ exponent)
        (posToNat_positive mantissa) := by
  have fields := inverse_decode32_fields value sign mantissa exponent decoded
  have fractionBound : value.bits.toNat % 2 ^ 23 < 2 ^ 23 := Nat.mod_lt _ (by decide)
  have exponentBounds : 0 < (intOfZ exponent + 150).toNat ∧
      (intOfZ exponent + 150).toNat < 255 := by
    rcases fields.2 with subnormal | normal <;> omega
  have mantissaUpper : posToNat mantissa < 2 ^ 24 := by
    rcases fields.2 with subnormal | normal <;> omega
  rw [inverse_normal_bits32 value sign mantissa exponent decoded lower]
  rw [inverse_unpack_components32 _ (posToNat mantissa) _ lower mantissaUpper
    exponentBounds.1 exponentBounds.2]
  have exponentEq : ((intOfZ exponent + 150).toNat : Int) - 150 = intOfZ exponent := by
    rcases fields.2 with subnormal | normal <;> omega
  simp only [exponentEq]

theorem Float32.div_mul_inverse
    [certificate : IEEE754_extra.Bexact_inverse_certificate z24 z128] :
    Float32.div_mul_inverseStatement := by
  intro numerator divisor reciprocal inverse
  unfold Float32.exact_inverse at inverse
  cases returned : IEEE754_extra.Bexact_inverse (prec := z24) (emax := z128) (decode32 divisor) with
  | none =>
      rw [returned] at inverse
      change (none : Option float32) = some reciprocal at inverse
      contradiction
  | some result =>
      have encoded : encode32 result = reciprocal := by
        rw [returned] at inverse
        change some (encode32 result) = some reciprocal at inverse
        exact Option.some.inj inverse
      subst reciprocal
      rcases inverse_result_shape (precision := z24) (maximum := z128) (decode32 divisor) result returned with
        ⟨sign, exponent, decoded, resultShape⟩
      have valid := IEEE754_extra.Bexact_inverse_result_obligation_proof (prec := z24) (emax := z128)
        ⟨decode32 divisor, conversion_decode32_valid divisor⟩ result returned
      have reciprocalDecoded : decode32 (encode32 result) = result := conversion_encode32_decode ⟨result, valid⟩
      have mantissaValue : posToNat (IEEE754_extra.Bexact_inverse_mantissa (prec := z24)) = 2 ^ 23 := by decide
      have divisorUnpacked := inverse_normal_unpack32 divisor sign _ exponent decoded (by rw [mantissaValue]; omega)
      have reciprocalUnpacked := inverse_normal_unpack32 (encode32 result) sign _ _
        (reciprocalDecoded.trans resultShape) (by rw [mantissaValue]; omega)
      have exponentValue : intOfZ (IEEE754_extra.Zsub (IEEE754_extra.Zopp exponent)
          (IEEE754_extra.Zmul (IEEE754_extra.Zsub z24 IEEE754_extra.Zone) IEEE754_extra.Ztwo)) =
          -intOfZ exponent - 2 * (23 : Int) := by
        change intOfZ (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.opp exponent)
          (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.sub z24 IEEE754_extra.Zone) IEEE754_extra.Ztwo)) = _
        simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.opp, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
        rfl
      have modelEqual : modelBinary32 (UnpackedFloat.div Format.binary32) numerator divisor =
          modelBinary32 (UnpackedFloat.mul Format.binary32) numerator (encode32 result) := by
        unfold modelBinary32
        rw [divisorUnpacked, reciprocalUnpacked]
        simp only [mantissaValue, exponentValue]
        rw [inverse_unpacked_div_mul Format.binary32 23 (by rfl) (by decide)]
        rfl
      have divisorNan : isNaN32 divisor = false := by
        rw [← conversion_isNaN32_decode, decoded]
        rfl
      have reciprocalNan : isNaN32 (encode32 result) = false := by
        rw [← conversion_isNaN32_decode, reciprocalDecoded, resultShape]
        rfl
      simp only [Float32.div, Float32.mul, modelEqual, Float32.finishBinary, divisorNan, reciprocalNan,
        Float32.binop_nan, Float32.cons_pl, Bool.false_eq_true, ↓reduceIte]

end CompCert4Lean.Lib.Floats
