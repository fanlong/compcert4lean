import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Values
import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Floats
import CompCert4Lean.Lib.Zbits
import CompCert4Lean.X86_64.Archi

/-!
# In-memory representation of values

This module translates the definition-bearing surface of CompCert's
`common/Memdata.v`. Proofs assigned to later proof migration are represented
by transparent proposition descriptors.
-/

namespace CompCert4Lean.Common.Memdata

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Floats

private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
private abbrev byte := CompCert4Lean.Lib.Integers.byte
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev meminj := CompCert4Lean.Common.Values.Val.meminj
private abbrev list_forall2 {A B : Type} (P : A → B → Prop) :=
  CompCert4Lean.Lib.Coqlib.list_forall2 P

namespace CCInt
private abbrev int := CompCert4Lean.Lib.Integers.Int.int
private abbrev repr := CompCert4Lean.Lib.Integers.Int.repr
private abbrev unsigned := CompCert4Lean.Lib.Integers.Int.unsigned
end CCInt

namespace CCInt64
private abbrev repr := CompCert4Lean.Lib.Integers.Int64.repr
private abbrev unsigned := CompCert4Lean.Lib.Integers.Int64.unsigned
private abbrev loword := CompCert4Lean.Lib.Integers.Int64.loword
private abbrev hiword := CompCert4Lean.Lib.Integers.Int64.hiword
end CCInt64

namespace CCByte
private abbrev repr := CompCert4Lean.Lib.Integers.Byte.repr
private abbrev unsigned (x : byte) : Z :=
  CompCert4Lean.Lib.Integers.WordCore.unsigned x
end CCByte

namespace CCFloat
private abbrev to_bits := CompCert4Lean.Lib.Floats.Float.to_bits
private abbrev of_bits := CompCert4Lean.Lib.Floats.Float.of_bits
end CCFloat

namespace CCFloat32
private abbrev to_bits := CompCert4Lean.Lib.Floats.Float32.to_bits
private abbrev of_bits := CompCert4Lean.Lib.Floats.Float32.of_bits
end CCFloat32

private abbrev z0 : Z := .Z0
private abbrev z1 : Z := ZArith.BinInt.Z.of_nat 1
private abbrev z2 : Z := ZArith.BinInt.Z.of_nat 2
private abbrev z4 : Z := ZArith.BinInt.Z.of_nat 4
private abbrev z8 : Z := ZArith.BinInt.Z.of_nat 8
private abbrev z16 : Z := ZArith.BinInt.Z.of_nat 16
private abbrev z256 : Z := ZArith.BinInt.Z.of_nat 256
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zMul := ZArith.BinInt.Z.mul
private abbrev zDiv := ZArith.BinInt.Z.div
private abbrev zMod := ZArith.BinInt.Z.modulo
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev zToNat := ZArith.BinInt.Z.to_nat
private abbrev zDivide := ZArith.BinInt.Z.divide
private abbrev zTwoP := two_p

private theorem intOfZ_two_p_zOfNat (n : Nat) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (zTwoP (zOfNat n)) = (2 : _root_.Int) ^ n := by
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (ZArith.BinInt.Z.pow (Zpos (.xO .xH)) (ZArith.BinInt.Z.of_nat n)) = _
  unfold ZArith.BinInt.Z.pow
  rw [show ZArith.BinInt.Z.of_nat n =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (_root_.Int.ofNat n) by rfl,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  have hn : ¬ _root_.Int.ofNat n < 0 :=
    _root_.Int.not_lt.mpr (_root_.Int.natCast_nonneg n)
  rw [if_neg hn]
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  rfl
private abbrev eqmod := CompCert4Lean.Lib.Zbits.eqmod

private def sumboolBool {P Q : Prop} (d : Sumbool P Q) : Bool :=
  match d with
  | .left _ => true
  | .right _ => false

private abbrev intZeroExt := CompCert4Lean.Lib.Integers.Int.zero_ext

private abbrev intSignExt := CompCert4Lean.Lib.Integers.Int.sign_ext

/-! ## Memory chunks -/

def size_chunk : memory_chunk → Z
  | Mbool | Mint8signed | Mint8unsigned => z1
  | Mint16signed | Mint16unsigned => z2
  | Mint32 | Mfloat32 | Many32 => z4
  | Mint64 | Mfloat64 | Many64 => z8

def size_chunk_posStatement : Prop :=
  ∀ chunk, zLt z0 (size_chunk chunk)

def size_chunk_nat (chunk : memory_chunk) : Nat :=
  zToNat (size_chunk chunk)

def size_chunk_convStatement : Prop :=
  ∀ chunk, size_chunk chunk = zOfNat (size_chunk_nat chunk)

def size_chunk_nat_posStatement : Prop :=
  ∀ chunk, ∃ n, size_chunk_nat chunk = Nat.succ n

def size_chunk_MptrStatement : Prop :=
  size_chunk Mptr = if CompCert4Lean.X86_64.Archi.ptr64 then z8 else z4

def align_chunk : memory_chunk → Z
  | Mbool | Mint8signed | Mint8unsigned => z1
  | Mint16signed | Mint16unsigned => z2
  | Mint32 | Mfloat32 | Mfloat64 | Many32 | Many64 => z4
  | Mint64 => z8

def align_chunk_posStatement : Prop :=
  ∀ chunk, zLt z0 (align_chunk chunk)

def align_chunk_MptrStatement : Prop :=
  align_chunk Mptr = if CompCert4Lean.X86_64.Archi.ptr64 then z8 else z4

def align_size_chunk_dividesStatement : Prop :=
  ∀ chunk, zDivide (align_chunk chunk) (size_chunk chunk)

def align_le_dividesStatement : Prop :=
  ∀ chunk1 chunk2,
    zLe (align_chunk chunk1) (align_chunk chunk2) →
      zDivide (align_chunk chunk1) (align_chunk chunk2)

inductive quantity : Type where
  | Q32
  | Q64
deriving DecidableEq

export quantity (Q32 Q64)

def quantity_eq (q1 q2 : quantity) : Sumbool (q1 = q2) (q1 ≠ q2) := by
  by_cases h : q1 = q2
  · exact .left h
  · exact .right h

def size_quantity_nat : quantity → Nat
  | Q32 => 4
  | Q64 => 8

def size_quantity_nat_posStatement : Prop :=
  ∀ q, ∃ n, size_quantity_nat q = Nat.succ n

/-! ## Memory values and integer encodings -/

inductive memval : Type where
  | Undef
  | Byte (value : byte)
  | Fragment (value : val) (quantity : quantity) (index : Nat)

export memval (Undef Byte Fragment)

def bytes_of_int : Nat → Z → List byte
  | 0, _ => []
  | n + 1, x => CCByte.repr x :: bytes_of_int n (zDiv x z256)

def int_of_bytes : List byte → Z
  | [] => z0
  | b :: rest => zAdd (CCByte.unsigned b) (zMul (int_of_bytes rest) z256)

def rev_if_be (l : List byte) : List byte :=
  if CompCert4Lean.X86_64.Archi.big_endian then l.reverse else l

def encode_int (sz : Nat) (x : Z) : List byte :=
  rev_if_be (bytes_of_int sz x)

def decode_int (b : List byte) : Z :=
  int_of_bytes (rev_if_be b)

def length_bytes_of_intStatement : Prop :=
  ∀ n x, (bytes_of_int n x).length = n

def rev_if_be_lengthStatement : Prop :=
  ∀ l, (rev_if_be l).length = l.length

def encode_int_lengthStatement : Prop :=
  ∀ sz x, (encode_int sz x).length = sz

theorem length_bytes_of_int_proof_api (n : Nat) (x : Z) :
    (bytes_of_int n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [bytes_of_int, List.length_cons, ih]

theorem rev_if_be_length_proof_api (l : List byte) :
    (rev_if_be l).length = l.length := by
  unfold rev_if_be
  split <;> simp

theorem encode_int_length_proof_api (sz : Nat) (x : Z) :
    (encode_int sz x).length = sz := by
  rw [encode_int, rev_if_be_length_proof_api,
    length_bytes_of_int_proof_api]

def bytes_of_int_modStatement : Prop :=
  ∀ n x y,
    eqmod (zTwoP (zMul (zOfNat n) z8)) x y →
      bytes_of_int n x = bytes_of_int n y

def encode_int_8_modStatement : Prop :=
  ∀ x y, eqmod (zTwoP z8) x y → encode_int 1 x = encode_int 1 y

def encode_int_16_modStatement : Prop :=
  ∀ x y, eqmod (zTwoP z16) x y → encode_int 2 x = encode_int 2 y

/-! ## Encoding and decoding values -/

def inj_bytes (bl : List byte) : List memval :=
  bl.map memval.Byte

def proj_bytes : List memval → Option (List byte)
  | [] => some []
  | Byte b :: rest =>
      match proj_bytes rest with
      | none => none
      | some bl => some (b :: bl)
  | _ => none

def length_inj_bytesStatement : Prop :=
  ∀ bl, (inj_bytes bl).length = bl.length

def inj_value_rec : Nat → val → quantity → List memval
  | 0, _, _ => []
  | n + 1, v, q => Fragment v q n :: inj_value_rec n v q

def inj_value (q : quantity) (v : val) : List memval :=
  inj_value_rec (size_quantity_nat q) v q

def check_value : Nat → val → quantity → List memval → Bool
  | 0, _, _, [] => true
  | n + 1, v, q, Fragment v' q' n' :: rest =>
      sumboolBool (Val.eq v v') &&
      sumboolBool (quantity_eq q q') &&
      decide (n = n') &&
      check_value n v q rest
  | _, _, _, _ => false

def proj_value (q : quantity) (vl : List memval) : val :=
  match vl with
  | Fragment v _ _ :: _ =>
      if check_value (size_quantity_nat q) v q vl then v else Vundef
  | _ => Vundef

def encode_val (chunk : memory_chunk) (v : val) : List memval :=
  match v with
  | Vundef =>
      match chunk with
      | Many32 => inj_value Q32 v
      | Many64 => inj_value Q64 v
      | _ => List.replicate (size_chunk_nat chunk) Undef
  | Vint n =>
      match chunk with
      | Mbool | Mint8signed | Mint8unsigned =>
          inj_bytes (encode_int 1 (CCInt.unsigned n))
      | Mint16signed | Mint16unsigned =>
          inj_bytes (encode_int 2 (CCInt.unsigned n))
      | Mint32 => inj_bytes (encode_int 4 (CCInt.unsigned n))
      | Many32 => inj_value Q32 v
      | Many64 => inj_value Q64 v
      | _ => List.replicate (size_chunk_nat chunk) Undef
  | Vptr _ _ =>
      match chunk with
      | Mint32 =>
          if CompCert4Lean.X86_64.Archi.ptr64 then List.replicate 4 Undef
          else inj_value Q32 v
      | Mint64 =>
          if CompCert4Lean.X86_64.Archi.ptr64 then inj_value Q64 v
          else List.replicate 8 Undef
      | Many32 => inj_value Q32 v
      | Many64 => inj_value Q64 v
      | _ => List.replicate (size_chunk_nat chunk) Undef
  | Vlong n =>
      match chunk with
      | Mint64 => inj_bytes (encode_int 8 (CCInt64.unsigned n))
      | Many32 => inj_value Q32 v
      | Many64 => inj_value Q64 v
      | _ => List.replicate (size_chunk_nat chunk) Undef
  | Vsingle n =>
      match chunk with
      | Mfloat32 => inj_bytes (encode_int 4 (CCInt.unsigned (CCFloat32.to_bits n)))
      | Many32 => inj_value Q32 v
      | Many64 => inj_value Q64 v
      | _ => List.replicate (size_chunk_nat chunk) Undef
  | Vfloat n =>
      match chunk with
      | Mfloat64 => inj_bytes (encode_int 8 (CCInt64.unsigned (CCFloat.to_bits n)))
      | Many32 => inj_value Q32 v
      | Many64 => inj_value Q64 v
      | _ => List.replicate (size_chunk_nat chunk) Undef

def decode_val (chunk : memory_chunk) (vl : List memval) : val :=
  match proj_bytes vl with
  | some bl =>
      match chunk with
      | Mbool => Val.norm_bool (Vint (intZeroExt z8 (CCInt.repr (decode_int bl))))
      | Mint8signed => Vint (intSignExt z8 (CCInt.repr (decode_int bl)))
      | Mint8unsigned => Vint (intZeroExt z8 (CCInt.repr (decode_int bl)))
      | Mint16signed => Vint (intSignExt z16 (CCInt.repr (decode_int bl)))
      | Mint16unsigned => Vint (intZeroExt z16 (CCInt.repr (decode_int bl)))
      | Mint32 => Vint (CCInt.repr (decode_int bl))
      | Mint64 => Vlong (CCInt64.repr (decode_int bl))
      | Mfloat32 => Vsingle (CCFloat32.of_bits (CCInt.repr (decode_int bl)))
      | Mfloat64 => Vfloat (CCFloat.of_bits (CCInt64.repr (decode_int bl)))
      | Many32 | Many64 => Vundef
  | none =>
      match chunk with
      | Mint32 =>
          if CompCert4Lean.X86_64.Archi.ptr64 then Vundef
          else Val.load_result chunk (proj_value Q32 vl)
      | Many32 => Val.load_result chunk (proj_value Q32 vl)
      | Mint64 =>
          if CompCert4Lean.X86_64.Archi.ptr64 then Val.load_result chunk (proj_value Q64 vl)
          else Vundef
      | Many64 => Val.load_result chunk (proj_value Q64 vl)
      | _ => Vundef

def encode_val_lengthStatement : Prop :=
  ∀ chunk v, (encode_val chunk v).length = size_chunk_nat chunk

def decode_encode_val (v1 : val) (chunk1 chunk2 : memory_chunk) (v2 : val) : Prop :=
  match v1 with
  | Vundef => v2 = Vundef
  | Vint n =>
      match chunk1 with
      | Mbool | Mint8signed | Mint8unsigned =>
          match chunk2 with
          | Mint8signed => v2 = Vint (intSignExt z8 n)
          | Mint8unsigned => v2 = Vint (intZeroExt z8 n)
          | Mbool => v2 = Val.norm_bool (Vint (intZeroExt z8 n))
          | _ => True
      | Mint16signed | Mint16unsigned =>
          match chunk2 with
          | Mint16signed => v2 = Vint (intSignExt z16 n)
          | Mint16unsigned => v2 = Vint (intZeroExt z16 n)
          | _ => True
      | Mint32 =>
          match chunk2 with
          | Mint32 => v2 = Vint n
          | Mfloat32 => v2 = Vsingle (CCFloat32.of_bits n)
          | _ => True
      | Many32 =>
          match chunk2 with
          | Many32 => v2 = Vint n
          | _ => True
      | Many64 =>
          match chunk2 with
          | Many64 => v2 = Vint n
          | _ => v2 = Vundef
      | Mint64 | Mfloat32 | Mfloat64 => v2 = Vundef
  | Vptr b ofs =>
      match chunk1 with
      | Mint32 | Many32 =>
          match chunk2 with
          | Mint32 | Many32 =>
              v2 = if CompCert4Lean.X86_64.Archi.ptr64 then Vundef else Vptr b ofs
          | _ => v2 = Vundef
      | Mint64 =>
          match chunk2 with
          | Mint64 | Many64 =>
              v2 = if CompCert4Lean.X86_64.Archi.ptr64 then Vptr b ofs else Vundef
          | _ => v2 = Vundef
      | Many64 =>
          match chunk2 with
          | Many64 => v2 = Vptr b ofs
          | Mint64 =>
              v2 = if CompCert4Lean.X86_64.Archi.ptr64 then Vptr b ofs else Vundef
          | _ => v2 = Vundef
      | _ => v2 = Vundef
  | Vlong n =>
      match chunk1 with
      | Mint64 =>
          match chunk2 with
          | Mint64 => v2 = Vlong n
          | Mfloat64 => v2 = Vfloat (CCFloat.of_bits n)
          | _ => True
      | Many64 =>
          match chunk2 with
          | Many64 => v2 = Vlong n
          | _ => True
      | _ => v2 = Vundef
  | Vfloat f =>
      match chunk1 with
      | Mfloat64 =>
          match chunk2 with
          | Mfloat64 => v2 = Vfloat f
          | Mint64 => v2 = Vlong (CCFloat.to_bits f)
          | _ => True
      | Many64 =>
          match chunk2 with
          | Many64 => v2 = Vfloat f
          | _ => True
      | _ => v2 = Vundef
  | Vsingle f =>
      match chunk1 with
      | Mfloat32 =>
          match chunk2 with
          | Mfloat32 => v2 = Vsingle f
          | Mint32 => v2 = Vint (CCFloat32.to_bits f)
          | _ => True
      | Many32 =>
          match chunk2 with
          | Many32 => v2 = Vsingle f
          | _ => True
      | Many64 =>
          match chunk2 with
          | Many64 => v2 = Vsingle f
          | _ => v2 = Vundef
      | _ => v2 = Vundef

def decode_val_undefStatement : Prop :=
  ∀ bl chunk, decode_val chunk (Undef :: bl) = Vundef

def decode_encode_val_generalStatement : Prop :=
  ∀ v chunk1 chunk2,
    decode_encode_val v chunk1 chunk2 (decode_val chunk2 (encode_val chunk1 v))

def decode_encode_val_similarStatement : Prop :=
  ∀ v1 chunk1 chunk2 v2,
    type_of_chunk chunk1 = type_of_chunk chunk2 →
    size_chunk chunk1 = size_chunk chunk2 →
    decode_encode_val v1 chunk1 chunk2 v2 →
    v2 = Val.load_result chunk2 v1

def decode_val_xtypeStatement : Prop :=
  ∀ chunk cl, Val.has_rettype (decode_val chunk cl) (xtype_of_chunk chunk)

def decode_val_typeStatement : Prop :=
  ∀ chunk cl, Val.has_type (decode_val chunk cl) (type_of_chunk chunk)

def encode_val_int8_signed_unsignedStatement : Prop :=
  ∀ v, encode_val Mint8signed v = encode_val Mint8unsigned v

def encode_val_int16_signed_unsignedStatement : Prop :=
  ∀ v, encode_val Mint16signed v = encode_val Mint16unsigned v

def decode_val_castStatement : Prop :=
  ∀ chunk l,
    let v := decode_val chunk l
    match chunk with
    | Mbool => v = Val.norm_bool v
    | Mint8signed => v = Val.sign_ext z8 v
    | Mint8unsigned => v = Val.zero_ext z8 v
    | Mint16signed => v = Val.sign_ext z16 v
    | Mint16unsigned => v = Val.zero_ext z16 v
    | _ => True

/-! ## Shapes of memory encodings -/

def quantity_chunk : memory_chunk → quantity
  | Mint64 | Mfloat64 | Many64 => Q64
  | _ => Q32

inductive shape_encoding : memory_chunk → val → List memval → Prop where
  | fragment (chunk : memory_chunk) (v : val) (q : quantity) (i : Nat) (mvl : List memval) :
      (chunk = Mint32 ∨ chunk = Many32 ∨ chunk = Mint64 ∨ chunk = Many64) →
      q = quantity_chunk chunk →
      Nat.succ i = size_quantity_nat q →
      (∀ mv, mv ∈ mvl →
        ∃ j, mv = Fragment v q j ∧ Nat.succ j ≠ size_quantity_nat q) →
      shape_encoding chunk v (Fragment v q i :: mvl)
  | bytes (chunk : memory_chunk) (v : val) (b : byte) (mvl : List memval) :
      (match v with
       | Vint _ | Vlong _ | Vfloat _ | Vsingle _ => True
       | _ => False) →
      (∀ mv, mv ∈ mvl → ∃ b', mv = Byte b') →
      shape_encoding chunk v (Byte b :: mvl)
  | undef (chunk : memory_chunk) (v : val) (mvl : List memval) :
      (∀ mv, mv ∈ mvl → mv = Undef) →
      shape_encoding chunk v (Undef :: mvl)

def encode_val_shapeStatement : Prop :=
  ∀ chunk v, shape_encoding chunk v (encode_val chunk v)

inductive shape_decoding : memory_chunk → List memval → val → Prop where
  | fragment (chunk : memory_chunk) (v : val) (q : quantity) (i : Nat) (mvl : List memval) :
      (chunk = Mint32 ∨ chunk = Many32 ∨ chunk = Mint64 ∨ chunk = Many64) →
      q = quantity_chunk chunk →
      Nat.succ i = size_quantity_nat q →
      (∀ mv, mv ∈ mvl →
        ∃ j, mv = Fragment v q j ∧ Nat.succ j ≠ size_quantity_nat q) →
      shape_decoding chunk (Fragment v q i :: mvl) (Val.load_result chunk v)
  | shape_decoding_b (chunk : memory_chunk) (b : byte) (mvl : List memval) (v : val) :
      (match v with | Vptr _ _ => False | _ => True) →
      (∀ mv, mv ∈ mvl → ∃ b', mv = Byte b') →
      shape_decoding chunk (Byte b :: mvl) v
  | shape_decoding_u (chunk : memory_chunk) (mvl : List memval) :
      shape_decoding chunk mvl Vundef

export shape_decoding (shape_decoding_b shape_decoding_u)

def decode_val_shapeStatement : Prop :=
  ∀ chunk mv1 mvl,
    shape_decoding chunk (mv1 :: mvl) (decode_val chunk (mv1 :: mvl))

/-! ## Compatibility with memory injections -/

inductive memval_inject : meminj → memval → memval → Prop where
  | byte (f : meminj) (n : byte) : memval_inject f (Byte n) (Byte n)
  | fragment (f : meminj) (v1 v2 : val) (q : quantity) (n : Nat) :
      Val.inject f v1 v2 →
      memval_inject f (Fragment v1 q n) (Fragment v2 q n)
  | undef (f : meminj) (mv : memval) : memval_inject f Undef mv

def memval_inject_incrStatement : Prop :=
  ∀ f f' v1 v2,
    memval_inject f v1 v2 → inject_incr f f' → memval_inject f' v1 v2

def proj_bytes_injectStatement : Prop :=
  ∀ f vl vl',
    list_forall2 (memval_inject f) vl vl' →
    ∀ bl, proj_bytes vl = some bl → proj_bytes vl' = some bl

def check_value_injectStatement : Prop :=
  ∀ f vl vl',
    list_forall2 (memval_inject f) vl vl' →
    ∀ v v' q n,
      check_value n v q vl = true →
      Val.inject f v v' →
      v ≠ Vundef →
      check_value n v' q vl' = true

def proj_value_injectStatement : Prop :=
  ∀ f q vl1 vl2,
    list_forall2 (memval_inject f) vl1 vl2 →
      Val.inject f (proj_value q vl1) (proj_value q vl2)

def proj_bytes_not_injectStatement : Prop :=
  ∀ f vl vl',
    list_forall2 (memval_inject f) vl vl' →
    proj_bytes vl = none →
    proj_bytes vl' ≠ none →
    Undef ∈ vl

def check_value_undefStatement : Prop :=
  ∀ n q v vl, Undef ∈ vl → check_value n v q vl = false

def proj_value_undefStatement : Prop :=
  ∀ q vl, Undef ∈ vl → proj_value q vl = Vundef

def decode_val_injectStatement : Prop :=
  ∀ f vl1 vl2 chunk,
    list_forall2 (memval_inject f) vl1 vl2 →
      Val.inject f (decode_val chunk vl1) (decode_val chunk vl2)

def inj_bytes_injectStatement : Prop :=
  ∀ f bl, list_forall2 (memval_inject f) (inj_bytes bl) (inj_bytes bl)

def repeat_Undef_inject_anyStatement : Prop :=
  ∀ f vl,
    list_forall2 (memval_inject f) (List.replicate vl.length Undef) vl

def repeat_Undef_inject_encode_valStatement : Prop :=
  ∀ f chunk v,
    list_forall2 (memval_inject f)
      (List.replicate (size_chunk_nat chunk) Undef) (encode_val chunk v)

def repeat_Undef_inject_selfStatement : Prop :=
  ∀ f n,
    list_forall2 (memval_inject f)
      (List.replicate n Undef) (List.replicate n Undef)

def inj_value_injectStatement : Prop :=
  ∀ f v1 v2 q,
    Val.inject f v1 v2 →
      list_forall2 (memval_inject f) (inj_value q v1) (inj_value q v2)

def encode_val_injectStatement : Prop :=
  ∀ f v1 v2 chunk,
    Val.inject f v1 v2 →
      list_forall2 (memval_inject f) (encode_val chunk v1) (encode_val chunk v2)

def memval_lessdef : memval → memval → Prop :=
  memval_inject inject_id

def memval_lessdef_reflStatement : Prop :=
  ∀ mv, memval_lessdef mv mv

/-! ## Splitting 64-bit memory accesses -/

def int_of_bytes_appendStatement : Prop :=
  ∀ l2 l1,
    int_of_bytes (l1 ++ l2) =
      zAdd (int_of_bytes l1)
        (zMul (int_of_bytes l2) (zTwoP (zMul (zOfNat l1.length) z8)))

def int_of_bytes_rangeStatement : Prop :=
  ∀ l,
    zLe z0 (int_of_bytes l) ∧
      zLt (int_of_bytes l) (zTwoP (zMul (zOfNat l.length) z8))

theorem int_of_bytes_range_proof_api (l : List byte) :
    zLe z0 (int_of_bytes l) ∧
      zLt (int_of_bytes l) (zTwoP (zMul (zOfNat l.length) z8)) := by
  induction l with
  | nil =>
      change (0 : _root_.Int) ≤ 0 ∧ (0 : _root_.Int) < 1
      omega
  | cons b rest ih =>
      have hb := CompCert4Lean.Lib.Integers.Byte.unsigned_range_proof_api b
      have hpow :
          (2 : _root_.Int) ^ ((rest.length + 1) * 8) =
            (2 : _root_.Int) ^ (rest.length * 8) * 256 := by
        rw [show (rest.length + 1) * 8 = rest.length * 8 + 8 by omega,
          _root_.Int.pow_add]
        rfl
      change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (int_of_bytes (b :: rest)) ∧
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (int_of_bytes (b :: rest)) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (zTwoP (zMul (zOfNat (b :: rest).length) z8))
      have hexp :
          zMul (zOfNat (rest.length + 1)) z8 =
            zOfNat ((rest.length + 1) * 8) := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [zMul, zOfNat, z8, ZArith.BinInt.Z.mul,
          ZArith.BinInt.Z.of_nat,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        rfl
      simp only [List.length_cons]
      rw [hexp, intOfZ_two_p_zOfNat]
      simp only [int_of_bytes, zAdd, zMul, z256,
        ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, ZArith.BinInt.Z.of_nat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
        _root_.Int.ofNat_eq_natCast]
      change
        0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (CCByte.unsigned b) +
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (int_of_bytes rest) * 256 ∧
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (CCByte.unsigned b) +
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (int_of_bytes rest) * 256 <
            (2 : _root_.Int) ^ ((rest.length + 1) * 8)
      change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CCByte.unsigned b) ∧
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (CCByte.unsigned b) < 256 at hb
      change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (int_of_bytes rest) ∧
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (int_of_bytes rest) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (zTwoP (zMul (zOfNat rest.length) z8)) at ih
      have hexpRest :
          zMul (zOfNat rest.length) z8 = zOfNat (rest.length * 8) := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [zMul, zOfNat, z8, ZArith.BinInt.Z.mul,
          ZArith.BinInt.Z.of_nat,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        rfl
      rw [hexpRest, intOfZ_two_p_zOfNat] at ih
      rw [hpow]
      constructor <;> omega

def length_proj_bytesStatement : Prop :=
  ∀ l b, proj_bytes l = some b → b.length = l.length

def proj_bytes_appendStatement : Prop :=
  ∀ l2 l1,
    proj_bytes (l1 ++ l2) =
      match proj_bytes l1, proj_bytes l2 with
      | some b1, some b2 => some (b1 ++ b2)
      | _, _ => none

def decode_val_int64Statement : Prop :=
  ∀ l1 l2,
    l1.length = 4 →
    l2.length = 4 →
    CompCert4Lean.X86_64.Archi.ptr64 = false →
    Val.lessdef
      (decode_val Mint64 (l1 ++ l2))
      (Val.longofwords
        (decode_val Mint32
          (if CompCert4Lean.X86_64.Archi.big_endian then l1 else l2))
        (decode_val Mint32
          (if CompCert4Lean.X86_64.Archi.big_endian then l2 else l1)))

def bytes_of_int_appendStatement : Prop :=
  ∀ n2 x2 n1 x1,
    zLe z0 x1 ∧ zLt x1 (zTwoP (zMul (zOfNat n1) z8)) →
    bytes_of_int (n1 + n2)
      (zAdd x1 (zMul x2 (zTwoP (zMul (zOfNat n1) z8)))) =
      bytes_of_int n1 x1 ++ bytes_of_int n2 x2

def bytes_of_int64Statement : Prop :=
  ∀ i,
    bytes_of_int 8 (CCInt64.unsigned i) =
      bytes_of_int 4 (CCInt.unsigned (CCInt64.loword i)) ++
      bytes_of_int 4 (CCInt.unsigned (CCInt64.hiword i))

def encode_val_int64Statement : Prop :=
  ∀ v,
    CompCert4Lean.X86_64.Archi.ptr64 = false →
    encode_val Mint64 v =
      encode_val Mint32
        (if CompCert4Lean.X86_64.Archi.big_endian then Val.hiword v else Val.loword v) ++
      encode_val Mint32
        (if CompCert4Lean.X86_64.Archi.big_endian then Val.loword v else Val.hiword v)

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

theorem size_chunk_pos : size_chunk_posStatement := by
  intro chunk
  cases chunk <;> simp [size_chunk, zLt, z0, z1, z2, z4, z8,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt]
  all_goals exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive _

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

theorem size_chunk_conv : size_chunk_convStatement := by
  intro chunk
  cases chunk <;> rfl

theorem size_chunk_nat_pos : size_chunk_nat_posStatement := by
  intro chunk
  cases chunk <;> simp [size_chunk_nat, zToNat, size_chunk, z1, z2, z4, z8]

theorem size_chunk_Mptr : size_chunk_MptrStatement := by
  rfl

theorem align_chunk_pos : align_chunk_posStatement := by
  intro chunk
  cases chunk <;> simp [align_chunk, zLt, z0, z1, z2, z4, z8,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt]
  all_goals exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive _

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

theorem align_chunk_Mptr : align_chunk_MptrStatement := by
  rfl

theorem size_quantity_nat_pos : size_quantity_nat_posStatement := by
  intro q
  cases q with
  | Q32 => exact ⟨3, rfl⟩
  | Q64 => exact ⟨7, rfl⟩

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

theorem align_size_chunk_divides : align_size_chunk_dividesStatement := by
  intro chunk
  cases chunk <;> simp [align_chunk, size_chunk, zDivide, z1, z2, z4, z8]
  all_goals first
    | exact ⟨z1, by rfl⟩
    | exact ⟨z2, by rfl⟩

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

theorem align_le_divides : align_le_dividesStatement := by
  intro chunk1 chunk2 h
  have hp1 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat 1) = 1 :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat (by omega)
  have hp2 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat 2) = 2 :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat (by omega)
  have hp4 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat 4) = 4 :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat (by omega)
  have hp8 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat 8) = 8 :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat (by omega)
  cases chunk1 <;> cases chunk2 <;>
    simp [align_chunk, zLe, zDivide, z1, z2, z4, z8,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt, hp1, hp2, hp4, hp8] at h ⊢
  all_goals first
    | exact ⟨z1, by rfl⟩
    | exact ⟨z2, by rfl⟩
    | exact ⟨z4, by rfl⟩
    | exact ⟨z8, by rfl⟩

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

theorem length_bytes_of_int : length_bytes_of_intStatement := by
  exact fun n x => length_bytes_of_int_proof_api n x

theorem rev_if_be_length : rev_if_be_lengthStatement := by
  exact fun l => rev_if_be_length_proof_api l

theorem encode_int_length : encode_int_lengthStatement := by
  exact fun sz x => encode_int_length_proof_api sz x

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

theorem length_inj_bytes : length_inj_bytesStatement := by
  intro bl
  simp [inj_bytes]

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

theorem encode_val_length : encode_val_lengthStatement := by
  have hinj : ∀ (n : Nat) (v : val) (q : quantity),
      (inj_value_rec n v q).length = n := by
    intro n v q
    induction n with
    | zero => rfl
    | succ n ih => simp [inj_value_rec, ih]
  have hbytes : ∀ (bl : List byte), (inj_bytes bl).length = bl.length := by
    intro bl
    simp [inj_bytes]
  intro chunk v
  cases v <;> cases chunk <;>
    simp [encode_val, inj_value, inj_value_rec, size_chunk_nat, size_chunk,
      zToNat, z1, z2, z4, z8, size_quantity_nat, hinj, hbytes,
      encode_int_length_proof_api]
  all_goals by_cases h : CompCert4Lean.X86_64.Archi.ptr64 = true <;> simp [h]

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

theorem decode_val_undef : decode_val_undefStatement := by
  intro bl chunk
  cases chunk <;>
    simp [decode_val, proj_bytes, proj_value,
      CompCert4Lean.Common.Values.Val.load_result]

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

theorem decode_encode_val_similar : decode_encode_val_similarStatement := by
  intro v1 chunk1 chunk2 v2 hty hsz hde
  cases chunk1 <;> cases chunk2 <;> cases v1 <;>
    simp [CompCert4Lean.Common.AST.type_of_chunk, size_chunk,
      decode_encode_val, CompCert4Lean.Common.Values.Val.load_result,
      z1, z2, z4, z8] at hty hsz hde ⊢ <;>
    first | exact hde | contradiction

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

theorem encode_val_int8_signed_unsigned : encode_val_int8_signed_unsignedStatement := by
  intro v
  cases v <;> rfl

theorem encode_val_int16_signed_unsigned : encode_val_int16_signed_unsignedStatement := by
  intro v
  cases v <;> rfl

theorem decode_val_type : decode_val_typeStatement := by
  intro chunk cl
  cases h : proj_bytes cl with
  | none =>
      cases chunk with
      | Mbool => simp [decode_val, h, CompCert4Lean.Common.Values.Val.has_type,
          CompCert4Lean.Common.AST.type_of_chunk]
      | Mint8signed => simp [decode_val, h, CompCert4Lean.Common.Values.Val.has_type,
          CompCert4Lean.Common.AST.type_of_chunk]
      | Mint8unsigned => simp [decode_val, h, CompCert4Lean.Common.Values.Val.has_type,
          CompCert4Lean.Common.AST.type_of_chunk]
      | Mint16signed => simp [decode_val, h, CompCert4Lean.Common.Values.Val.has_type,
          CompCert4Lean.Common.AST.type_of_chunk]
      | Mint16unsigned => simp [decode_val, h, CompCert4Lean.Common.Values.Val.has_type,
          CompCert4Lean.Common.AST.type_of_chunk]
      | Mint32 =>
          by_cases hp : CompCert4Lean.X86_64.Archi.ptr64
          · simp [decode_val, h, hp, CompCert4Lean.Common.Values.Val.has_type,
              CompCert4Lean.Common.AST.type_of_chunk]
          · simpa [decode_val, h, hp] using
              (CompCert4Lean.Common.Values.Val.load_result_type
                CompCert4Lean.Common.AST.Mint32 (proj_value Q32 cl))
      | Mint64 =>
          by_cases hp : CompCert4Lean.X86_64.Archi.ptr64
          · simpa [decode_val, h, hp] using
              (CompCert4Lean.Common.Values.Val.load_result_type
                CompCert4Lean.Common.AST.Mint64 (proj_value Q64 cl))
          · simp [decode_val, h, hp, CompCert4Lean.Common.Values.Val.has_type,
              CompCert4Lean.Common.AST.type_of_chunk]
      | Mfloat32 => simp [decode_val, h, CompCert4Lean.Common.Values.Val.has_type,
          CompCert4Lean.Common.AST.type_of_chunk]
      | Mfloat64 => simp [decode_val, h, CompCert4Lean.Common.Values.Val.has_type,
          CompCert4Lean.Common.AST.type_of_chunk]
      | Many32 =>
          simpa [decode_val, h] using
            (CompCert4Lean.Common.Values.Val.load_result_type
              CompCert4Lean.Common.AST.Many32 (proj_value Q32 cl))
      | Many64 =>
          simpa [decode_val, h] using
            (CompCert4Lean.Common.Values.Val.load_result_type
              CompCert4Lean.Common.AST.Many64 (proj_value Q64 cl))
  | some bl =>
      cases chunk with
      | Mbool =>
          by_cases hb : Values.Val.is_bool
              (Values.Vint (intZeroExt z8 (CCInt.repr (decode_int bl)))) = true <;>
            simp [decode_val, h, Values.Val.norm_bool,
              Values.Val.has_type, AST.type_of_chunk, hb]
      | Mint8signed =>
          simp [decode_val, h, Values.Val.has_type, AST.type_of_chunk,
            Values.Val.sign_ext]
      | Mint8unsigned =>
          simp [decode_val, h, Values.Val.has_type, AST.type_of_chunk,
            Values.Val.zero_ext]
      | Mint16signed =>
          simp [decode_val, h, Values.Val.has_type, AST.type_of_chunk,
            Values.Val.sign_ext]
      | Mint16unsigned =>
          simp [decode_val, h, Values.Val.has_type, AST.type_of_chunk,
            Values.Val.zero_ext]
      | Mint32 => simp [decode_val, h, Values.Val.has_type, AST.type_of_chunk]
      | Mint64 => simp [decode_val, h, Values.Val.has_type, AST.type_of_chunk]
      | Mfloat32 => simp [decode_val, h, Values.Val.has_type, AST.type_of_chunk]
      | Mfloat64 => simp [decode_val, h, Values.Val.has_type, AST.type_of_chunk]
      | Many32 => simp [decode_val, h, Values.Val.has_type, AST.type_of_chunk]
      | Many64 => simp [decode_val, h, Values.Val.has_type, AST.type_of_chunk]

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

open CompCert4Lean.Common.Values

private theorem val_inject_incr_local :
    ∀ (f f' : meminj) (v v' : val),
      inject_incr f f' → Val.inject f v v' → Val.inject f' v v' := by
  intro f f' v v' hinc hinj
  cases hinj with
  | inject_int i => exact Val.inject.inject_int i
  | inject_long i => exact Val.inject.inject_long i
  | inject_float x => exact Val.inject.inject_float x
  | inject_single x => exact Val.inject.inject_single x
  | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
      exact Val.inject.inject_ptr b1 ofs1 b2 ofs2 delta (hinc b1 b2 delta hmap) hofs
  | val_inject_undef _ => exact Val.inject.val_inject_undef _

theorem memval_inject_incr : memval_inject_incrStatement := by
  intro f f' v1 v2 hrel hinc
  cases hrel with
  | byte n => exact memval_inject.byte f' n
  | fragment v1 v2 q n hv =>
      exact memval_inject.fragment f' v1 v2 q n
        (val_inject_incr_local f f' v1 v2 hinc hv)
  | undef => exact memval_inject.undef f' _

theorem proj_bytes_inject : proj_bytes_injectStatement := by
  intro f vl vl' hrel
  induction hrel with
  | nil =>
      intro bl h
      simpa [proj_bytes] using h
  | @cons a al b bl hab htail ih =>
      intro out h
      cases hab with
      | byte n =>
          cases hp : proj_bytes al with
          | none => simp [proj_bytes, hp] at h
          | some tail =>
              have htail' := ih tail hp
              have hout : out = n :: tail := by
                simpa [proj_bytes, hp] using h.symm
              subst out
              simp [proj_bytes, htail']
      | fragment v1 v2 q n hv => simp [proj_bytes] at h
      | undef mv => simp [proj_bytes] at h

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

open CompCert4Lean.Common.Values
open CompCert4Lean.Common.AST

theorem encode_val_shape : encode_val_shapeStatement := by
  intro chunk v
  have hA : ∀ (v : val) (mv : memval) (q : quantity) (n : Nat),
      n < size_quantity_nat q → mv ∈ inj_value_rec n v q →
      ∃ j, mv = Fragment v q j ∧ Nat.succ j ≠ size_quantity_nat q := by
    intro v mv q n hn hmem
    induction n with
    | zero => simp [inj_value_rec] at hmem
    | succ n ih =>
        simp only [inj_value_rec, List.mem_cons] at hmem
        rcases hmem with hmem | hmem
        · subst mv
          exact ⟨n, rfl, by omega⟩
        · exact ih (by omega) hmem
  have hB : ∀ (v : val) (chunk : memory_chunk) (q : quantity),
      q = quantity_chunk chunk →
      (chunk = Mint32 ∨ chunk = Many32 ∨ chunk = Mint64 ∨ chunk = Many64) →
      shape_encoding chunk v (inj_value q v) := by
    intro v chunk q hq hchunk
    unfold inj_value
    obtain ⟨n, hn⟩ := size_quantity_nat_pos q
    rw [hn]
    simp only [inj_value_rec]
    apply shape_encoding.fragment
    · exact hchunk
    · exact hq
    · exact hn.symm
    · intro mv hmem
      exact hA v mv q n (by omega) hmem
  have hC : ∀ (v : val) (chunk : memory_chunk) (bl : List byte),
      (match v with
       | Vint _ | Vlong _ | Vfloat _ | Vsingle _ => True
       | _ => False) →
      (inj_bytes bl).length = size_chunk_nat chunk →
      shape_encoding chunk v (inj_bytes bl) := by
    intro v chunk bl hv hlen
    cases bl with
    | nil =>
        have hp := size_chunk_nat_pos chunk
        simp [inj_bytes] at hlen
        rcases hp with ⟨k, hk⟩
        omega
    | cons b bl =>
        apply shape_encoding.bytes
        · exact hv
        · intro mv hmem
          have hm : mv ∈ List.map memval.Byte bl := by
            simpa [inj_bytes] using hmem
          obtain ⟨b', _, hb'⟩ := List.mem_map.mp hm
          exact ⟨b', hb'.symm⟩
  have hD : ∀ (v : val) (chunk : memory_chunk),
      shape_encoding chunk v (List.replicate (size_chunk_nat chunk) Undef) := by
    intro v chunk
    obtain ⟨n, hn⟩ := size_chunk_nat_pos chunk
    rw [hn]
    simp only [List.replicate_succ]
    apply shape_encoding.undef
    intro mv hmem
    exact (List.mem_replicate.mp hmem).2
  have hlen := encode_val_length chunk v
  cases v <;> cases chunk <;>
    simp only [encode_val] at hlen ⊢ <;>
    first
    | exact hB _ _ _ rfl (by simp)
    | exact hC _ _ _ trivial hlen
    | exact hD _ _

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

open CompCert4Lean.Common.Values
open CompCert4Lean.Common.AST

theorem decode_val_shape : decode_val_shapeStatement := by
  intro chunk mv1 mvl
  have hA : ∀ (mv : memval) (mvs : List memval) (bs : List byte),
      proj_bytes mvs = some bs → mv ∈ mvs → ∃ b, mv = Byte b := by
    intro mv mvs
    induction mvs generalizing mv with
    | nil =>
        intro bs hp hm
        simp at hm
    | cons a mvs ih =>
        intro bs hp hm
        cases a with
        | Undef => simp [proj_bytes] at hp
        | Fragment v q i => simp [proj_bytes] at hp
        | Byte b =>
            cases ht : proj_bytes mvs with
            | none => simp [proj_bytes, ht] at hp
            | some bs' =>
                have hm' : mv = Byte b ∨ mv ∈ mvs := by
                  simpa using (List.mem_cons.mp hm)
                rcases hm' with rfl | hm'
                · exact ⟨b, rfl⟩
                · exact ih mv bs' ht hm'
  have hB : ∀ (v : val) (q : quantity) (mv : memval) (n : Nat)
      (mvs : List memval),
      check_value n v q mvs = true → mv ∈ mvs →
      n < size_quantity_nat q →
      ∃ j, mv = Fragment v q j ∧ Nat.succ j ≠ size_quantity_nat q := by
    intro v q mv n mvs
    induction n generalizing mvs mv with
    | zero =>
        intro hc hm hn
        cases mvs with
        | nil => simp at hm
        | cons m mvs => simp [check_value] at hc
    | succ n ih =>
        intro hc hm hn
        cases mvs with
        | nil => simp [check_value] at hc
        | cons m mvs =>
            cases m with
            | Undef => simp [check_value] at hc
            | Byte b => simp [check_value] at hc
            | Fragment v' q' n' =>
                simp only [check_value] at hc
                simp only [Bool.and_eq_true] at hc
                rcases hc with ⟨⟨⟨hv, hq⟩, hn'⟩, htail⟩
                cases heq : Val.eq v v' with
                | left hveq =>
                    cases hqeq : quantity_eq q q' with
                    | left hqq =>
                        have hneq : n = n' := by simpa using hn'
                        subst v'
                        subst q'
                        subst n'
                        have hm' : mv = Fragment v q n ∨ mv ∈ mvs := by
                          simpa using (List.mem_cons.mp hm)
                        rcases hm' with rfl | hm'
                        · exact ⟨n, rfl, by omega⟩
                        · exact ih mv mvs htail hm' (by omega)
                    | right _ => simp [sumboolBool, hqeq] at hq
                | right _ => simp [sumboolBool, heq] at hv
  have hU : ∀ (mvs : List memval),
      shape_decoding chunk mvs (Val.load_result chunk Vundef) := by
    intro mvs
    have hu : Val.load_result chunk Vundef = Vundef := by
      cases chunk <;> rfl
    rw [hu]
    exact shape_decoding.shape_decoding_u chunk mvs
  have hU0 : ∀ (c : memory_chunk) (mvs : List memval),
      shape_decoding c mvs Vundef := by
    intro c mvs
    exact shape_decoding.shape_decoding_u c mvs
  have hNormNoPtr : ∀ (x : val),
      (match Val.norm_bool x with | Vptr _ _ => False | _ => True) := by
    intro x
    cases x with
    | Vundef => simp [Val.norm_bool]
    | Vint n =>
        unfold Val.norm_bool
        split
        · cases h : Val.is_bool (Vint n) <;> simp [h] at *
        · trivial
    | Vlong n =>
        unfold Val.norm_bool
        split
        · cases h : Val.is_bool (Vlong n) <;> simp [h] at *
        · trivial
    | Vfloat f =>
        unfold Val.norm_bool
        split
        · cases h : Val.is_bool (Vfloat f) <;> simp [h] at *
        · trivial
    | Vsingle f =>
        unfold Val.norm_bool
        split
        · cases h : Val.is_bool (Vsingle f) <;> simp [h] at *
        · trivial
    | Vptr b ofs =>
        have hb : Val.is_bool (Vptr b ofs) = false := by
          rfl
        simp [Val.norm_bool, hb]
  have hC : ∀ (q : quantity), size_quantity_nat q = size_chunk_nat chunk →
      (chunk = Mint32 ∨ chunk = Many32 ∨ chunk = Mint64 ∨ chunk = Many64) →
      shape_decoding chunk (mv1 :: mvl)
        (Val.load_result chunk (proj_value q (mv1 :: mvl))) := by
    intro q hsz hchunk
    obtain ⟨k, hk⟩ := size_quantity_nat_pos q
    unfold proj_value
    cases mv1 with
    | Undef => exact hU (Undef :: mvl)
    | Byte b => exact hU (Byte b :: mvl)
    | Fragment v q' n =>
        rw [hk]
        cases hc : check_value (Nat.succ k) v q (Fragment v q' n :: mvl) with
        | false =>
            have hcn : ¬ check_value (Nat.succ k) v q
                (Fragment v q' n :: mvl) = true := by simp [hc]
            simpa [hc] using hU (Fragment v q' n :: mvl)
        | true =>
            simp [hc]
            simp only [check_value] at hc
            simp only [Bool.and_eq_true] at hc
            rcases hc with ⟨⟨⟨hv, hq⟩, hn⟩, htail⟩
            cases hqeq : quantity_eq q q' with
            | left hqq =>
                subst q'
                have hn' : k = n := by simpa using hn
                have hqc : q = quantity_chunk chunk := by
                  rcases hchunk with rfl | rfl | rfl | rfl <;>
                    cases q <;>
                    simp [quantity_chunk, size_quantity_nat, size_chunk_nat, size_chunk,
                      zToNat, z1, z2, z4, z8] at hsz ⊢
                  all_goals omega
                have htail' : ∀ mv, mv ∈ mvl →
                    ∃ j, mv = Fragment v q j ∧ Nat.succ j ≠ size_quantity_nat q := by
                  intro mv hm
                  exact hB v q mv k mvl htail hm (by omega)
                apply shape_decoding.fragment
                · exact hchunk
                · exact hqc
                · omega
                · exact htail'
            | right _ => simp [sumboolBool, hqeq] at hq
  cases hp : proj_bytes (mv1 :: mvl) with
  | some bl =>
      obtain ⟨b, hb⟩ := hA mv1 (mv1 :: mvl) bl hp (by simp)
      subst mv1
      cases ht : proj_bytes mvl with
      | none => simp [proj_bytes, ht] at hp
      | some bl' =>
          cases chunk <;> simp only [decode_val, hp]
          all_goals apply shape_decoding.shape_decoding_b
          all_goals
            first
            | exact hNormNoPtr _
            | (change True; trivial)
            | (intro mv hm; exact hA mv mvl bl' ht hm)
  | none =>
      cases chunk with
      | Mbool | Mint8signed | Mint8unsigned | Mint16signed | Mint16unsigned |
        Mfloat32 | Mfloat64 =>
          simpa [decode_val, hp] using hU0 _ _
      | Mint32 =>
          by_cases hptr : CompCert4Lean.X86_64.Archi.ptr64 = true
          · simpa [decode_val, hp, hptr] using hU0 _ _
          · simpa [decode_val, hp, hptr] using
              hC Q32 (by simp [size_quantity_nat, size_chunk_nat, size_chunk, zToNat,
                z1, z2, z4, z8]) (by simp)
      | Mint64 =>
          by_cases hptr : CompCert4Lean.X86_64.Archi.ptr64 = true
          · simpa [decode_val, hp, hptr] using
              hC Q64 (by simp [size_quantity_nat, size_chunk_nat, size_chunk, zToNat,
                z1, z2, z4, z8]) (by simp)
          · simpa [decode_val, hp, hptr] using hU0 _ _
      | Many32 =>
          simpa [decode_val, hp] using
            hC Q32 (by simp [size_quantity_nat, size_chunk_nat, size_chunk, zToNat,
              z1, z2, z4, z8]) (by simp)
      | Many64 =>
          simpa [decode_val, hp] using
            hC Q64 (by simp [size_quantity_nat, size_chunk_nat, size_chunk, zToNat,
              z1, z2, z4, z8]) (by simp)

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

theorem check_value_undef : check_value_undefStatement := by
  intro n q v vl huv
  induction vl generalizing n with
  | nil => simp at huv
  | cons mv rest ih =>
      cases mv with
      | Undef =>
          cases n <;> rfl
      | Byte b =>
          cases n <;> rfl
      | Fragment v' q' i =>
          simp only [List.mem_cons] at huv
          rcases huv with hhead | htail
          · cases hhead
          · cases n with
            | zero => rfl
            | succ n =>
                simp only [check_value]
                rw [ih n htail]
                simp

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

theorem proj_bytes_not_inject : proj_bytes_not_injectStatement := by
  intro f vl vl' hrel
  induction hrel with
  | nil =>
      intro hnone hsome
      simp [proj_bytes] at hnone
  | @cons a al b bl hab htail ih =>
      intro hnone hsome
      cases hab with
      | byte n =>
          have hnone_tail : proj_bytes al = none := by
            cases hp : proj_bytes al with
            | none => rfl
            | some bs => simp [proj_bytes, hp] at hnone
          have hsome_tail : proj_bytes bl ≠ none := by
            intro hp
            apply hsome
            simp [proj_bytes, hp]
          have hu : Undef ∈ al := ih hnone_tail hsome_tail
          simp [hu]
      | fragment v1 v2 q n hv =>
          simp [proj_bytes] at hsome
      | undef mv =>
          simp

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

open CompCert4Lean.Common.Values

private theorem val_inject_deterministic_local {f : meminj} {v v1 v2 : val}
    (h1 : Val.inject f v v1) (h2 : Val.inject f v v2) (hv : v ≠ Vundef) :
    v1 = v2 := by
  cases h1 <;> cases h2 <;> simp_all

theorem check_value_inject : check_value_injectStatement := by
  intro f vl vl' hrel
  induction hrel with
  | nil =>
      intro v v' q n hc hinj hv
      cases n <;> simp [check_value] at hc ⊢
  | @cons a al b bl hab htail ih =>
      intro v v' q n hc hinj hv
      cases n with
      | zero => simp [check_value] at hc
      | succ n =>
          cases hab with
          | byte nb => simp [check_value] at hc
          | undef mv => simp [check_value] at hc
          | fragment v1 v2 q' i hval =>
              simp only [check_value] at hc
              simp only [Bool.and_eq_true] at hc
              rcases hc with ⟨⟨⟨hv_eq, hq_eq⟩, hi_eq⟩, htailc⟩
              cases heq : Val.eq v v1 with
              | right hne => simp [sumboolBool, heq] at hv_eq
              | left hveq =>
                  cases hqeq : quantity_eq q q' with
                  | right hnq => simp [sumboolBool, hqeq] at hq_eq
                  | left hqq =>
                      have hi : n = i := by simpa using hi_eq
                      subst v1
                      subst q'
                      subst i
                      have hv2 : v2 = v' :=
                        val_inject_deterministic_local hval hinj hv
                      subst v2
                      simp only [check_value]
                      have heqtrue : sumboolBool (Val.eq v' v') = true := by
                        cases heq' : Val.eq v' v' with
                        | left h => simp [sumboolBool, heq']
                        | right h => exact (h rfl).elim
                      have hqtrue : sumboolBool (quantity_eq q q) = true := by
                        cases hq' : quantity_eq q q with
                        | left h => simp [sumboolBool, hq']
                        | right h => exact (h rfl).elim
                      simp only [Bool.and_eq_true]
                      exact ⟨⟨⟨heqtrue, hqtrue⟩, rfl⟩,
                        ih _ _ _ _ htailc hinj hv⟩

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

open CompCert4Lean.Common.Values

theorem proj_value_inject : proj_value_injectStatement := by
  intro f q vl1 vl2 hrel
  induction hrel with
  | nil =>
      exact Val.inject.val_inject_undef _
  | @cons a al b bl hab htail ih =>
      cases hab with
      | byte n =>
          exact Val.inject.val_inject_undef _
      | undef mv =>
          exact Val.inject.val_inject_undef _
      | fragment v1 v2 q' n hval =>
          simp only [proj_value]
          obtain ⟨k, hk⟩ := size_quantity_nat_pos q
          cases hleft : check_value (size_quantity_nat q) v1 q
              (Fragment v1 q' n :: al) with
          | false =>
              exact Val.inject.val_inject_undef _
          | true =>
              rw [hk] at hleft ⊢
              cases hvundef : Val.eq v1 Vundef with
              | left hv =>
                  have hv' : v1 = Vundef := hv
                  subst v1
                  exact Val.inject.val_inject_undef _
              | right hvn =>
                  have hleft' := hleft
                  simp only [check_value] at hleft'
                  simp only [Bool.and_eq_true] at hleft'
                  rcases hleft' with ⟨⟨⟨_, hq_eq⟩, hi_eq⟩, htailc⟩
                  cases hqeq : quantity_eq q q' with
                  | right hnq => simp [sumboolBool, hqeq] at hq_eq
                  | left hqq =>
                      have hi : k = n := by simpa using hi_eq
                      subst q'
                      subst n
                      have htail' : check_value k v2 q bl = true :=
                        check_value_inject f al bl htail v1 v2 q k htailc hval hvn
                      have heqtrue : sumboolBool (Val.eq v2 v2) = true := by
                        cases heq' : Val.eq v2 v2 with
                        | left h => simp [sumboolBool, heq']
                        | right h => exact (h rfl).elim
                      have hqtrue : sumboolBool (quantity_eq q q) = true := by
                        cases hq' : quantity_eq q q with
                        | left h => simp [sumboolBool, hq']
                        | right h => exact (h rfl).elim
                      have hright :
                          check_value (Nat.succ k) v2 q
                            (Fragment v2 q k :: bl) = true := by
                        simp only [check_value, Bool.and_eq_true]
                        exact ⟨⟨⟨heqtrue, hqtrue⟩, rfl⟩, htail'⟩
                      cases hright' : check_value (Nat.succ k) v2 q
                          (Fragment v2 q k :: bl) with
                      | false => simp [hright'] at hright
                      | true =>
                          simp [hleft, hright']
                          exact hval

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

theorem inj_bytes_inject : inj_bytes_injectStatement := by
  intro f bl
  induction bl with
  | nil => constructor
  | cons b bl ih =>
      simp only [inj_bytes, List.map_cons]
      constructor
      · exact memval_inject.byte f b
      · exact ih

theorem repeat_Undef_inject_any : repeat_Undef_inject_anyStatement := by
  intro f vl
  induction vl with
  | nil => constructor
  | cons v vl ih =>
      simp only [List.length_cons, List.replicate_succ]
      constructor
      · exact memval_inject.undef f v
      · exact ih

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

open CompCert4Lean.Common.Values

theorem proj_value_undef : proj_value_undefStatement := by
  intro q vl huv
  cases vl with
  | nil => rfl
  | cons mv rest =>
      cases mv with
      | Undef => rfl
      | Byte b => rfl
      | Fragment v q' n =>
          change (if check_value (size_quantity_nat q) v q
              (Fragment v q' n :: rest) = true then v else Vundef) = Vundef
          simp [check_value_undef (size_quantity_nat q) q v _ huv]

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

open CompCert4Lean.Common.Values

private theorem memdata_load_result_inject_local :
    ∀ (f : meminj) chunk v1 v2,
      Val.inject f v1 v2 →
        Val.inject f (Val.load_result chunk v1) (Val.load_result chunk v2) := by
  intro f chunk v1 v2 h
  cases h with
  | inject_int i =>
      cases chunk with
      | Mbool =>
          by_cases hb : Val.is_bool (Vint (intZeroExt z8 i)) = true
          · simp [Val.load_result, Val.norm_bool, hb]
            exact Val.inject.inject_int _
          · simp [Val.load_result, Val.norm_bool, hb]
            exact Val.inject.val_inject_undef _
      | Mint8signed =>
          simp [Val.load_result]
          exact Val.inject.inject_int _
      | Mint8unsigned =>
          simp [Val.load_result]
          exact Val.inject.inject_int _
      | Mint16signed =>
          simp [Val.load_result]
          exact Val.inject.inject_int _
      | Mint16unsigned =>
          simp [Val.load_result]
          exact Val.inject.inject_int _
      | Mint32 =>
          exact Val.inject.inject_int _
      | Mint64 =>
          simp [Val.load_result]
          exact Val.inject.val_inject_undef _
      | Mfloat32 =>
          simp [Val.load_result]
          exact Val.inject.val_inject_undef _
      | Mfloat64 =>
          simp [Val.load_result]
          exact Val.inject.val_inject_undef _
      | Many32 =>
          exact Val.inject.inject_int _
      | Many64 =>
          exact Val.inject.inject_int _
  | inject_long i =>
      cases chunk <;>
        simp [Val.load_result] <;>
        first | exact Val.inject.inject_long _ | exact Val.inject.val_inject_undef _
  | inject_float x =>
      cases chunk <;>
        simp [Val.load_result] <;>
        first | exact Val.inject.inject_float _ | exact Val.inject.val_inject_undef _
  | inject_single x =>
      cases chunk <;>
        simp [Val.load_result] <;>
        first | exact Val.inject.inject_single _ | exact Val.inject.val_inject_undef _
  | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
      cases chunk with
      | Mbool =>
          simp [Val.load_result, CompCert4Lean.X86_64.Archi.ptr64]
          exact Val.inject.val_inject_undef _
      | Mint8signed =>
          simp [Val.load_result, CompCert4Lean.X86_64.Archi.ptr64]
          exact Val.inject.val_inject_undef _
      | Mint8unsigned =>
          simp [Val.load_result, CompCert4Lean.X86_64.Archi.ptr64]
          exact Val.inject.val_inject_undef _
      | Mint16signed =>
          simp [Val.load_result, CompCert4Lean.X86_64.Archi.ptr64]
          exact Val.inject.val_inject_undef _
      | Mint16unsigned =>
          simp [Val.load_result, CompCert4Lean.X86_64.Archi.ptr64]
          exact Val.inject.val_inject_undef _
      | Mint32 =>
          simp [Val.load_result, CompCert4Lean.X86_64.Archi.ptr64]
          exact Val.inject.val_inject_undef _
      | Mint64 =>
          exact Val.inject.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs
      | Mfloat32 =>
          simp [Val.load_result, CompCert4Lean.X86_64.Archi.ptr64]
          exact Val.inject.val_inject_undef _
      | Mfloat64 =>
          simp [Val.load_result, CompCert4Lean.X86_64.Archi.ptr64]
          exact Val.inject.val_inject_undef _
      | Many32 =>
          simp [Val.load_result, CompCert4Lean.X86_64.Archi.ptr64]
          exact Val.inject.val_inject_undef _
      | Many64 =>
          exact Val.inject.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs
  | val_inject_undef v =>
      cases chunk <;> exact Val.inject.val_inject_undef _

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

open CompCert4Lean.Common.Values
open CompCert4Lean.Common.AST

theorem decode_val_inject : decode_val_injectStatement := by
  intro f vl1 vl2 chunk hrel
  cases hp1 : proj_bytes vl1 with
  | some bl1 =>
      have hp2' := proj_bytes_inject f vl1 vl2 hrel bl1 hp1
      cases hp2 : proj_bytes vl2 with
      | none => simp [hp2] at hp2'
      | some bl2 =>
          have hbl : bl2 = bl1 := Option.some.inj (hp2.symm.trans hp2')
          subst bl2
          cases chunk with
          | Mbool =>
              by_cases hb : Val.is_bool
                  (Vint (intZeroExt z8 (CCInt.repr (decode_int bl1)))) = true
              · simp [decode_val, hp1, hp2, Val.norm_bool, hb]
                exact Val.inject.inject_int _
              · simp [decode_val, hp1, hp2, Val.norm_bool, hb]
                exact Val.inject.val_inject_undef _
          | Mint8signed =>
              simp [decode_val, hp1, hp2]
              exact Val.inject.inject_int _
          | Mint8unsigned =>
              simp [decode_val, hp1, hp2]
              exact Val.inject.inject_int _
          | Mint16signed =>
              simp [decode_val, hp1, hp2]
              exact Val.inject.inject_int _
          | Mint16unsigned =>
              simp [decode_val, hp1, hp2]
              exact Val.inject.inject_int _
          | Mint32 =>
              simp [decode_val, hp1, hp2]
              exact Val.inject.inject_int _
          | Mint64 =>
              simp [decode_val, hp1, hp2]
              exact Val.inject.inject_long _
          | Mfloat32 =>
              simp [decode_val, hp1, hp2]
              exact Val.inject.inject_single _
          | Mfloat64 =>
              simp [decode_val, hp1, hp2]
              exact Val.inject.inject_float _
          | Many32 =>
              simp [decode_val, hp1, hp2]
              exact Val.inject.val_inject_undef _
          | Many64 =>
              simp [decode_val, hp1, hp2]
              exact Val.inject.val_inject_undef _
  | none =>
      cases hp2 : proj_bytes vl2 with
      | none =>
          cases chunk with
          | Mbool =>
              simp [decode_val, hp1, hp2, CompCert4Lean.X86_64.Archi.ptr64]
              exact Val.inject.val_inject_undef _
          | Mint8signed =>
              simp [decode_val, hp1, hp2, CompCert4Lean.X86_64.Archi.ptr64]
              exact Val.inject.val_inject_undef _
          | Mint8unsigned =>
              simp [decode_val, hp1, hp2, CompCert4Lean.X86_64.Archi.ptr64]
              exact Val.inject.val_inject_undef _
          | Mint16signed =>
              simp [decode_val, hp1, hp2, CompCert4Lean.X86_64.Archi.ptr64]
              exact Val.inject.val_inject_undef _
          | Mint16unsigned =>
              simp [decode_val, hp1, hp2, CompCert4Lean.X86_64.Archi.ptr64]
              exact Val.inject.val_inject_undef _
          | Mint32 =>
              simp [decode_val, hp1, hp2, CompCert4Lean.X86_64.Archi.ptr64]
              exact Val.inject.val_inject_undef _
          | Mint64 =>
              simpa [decode_val, hp1, hp2, CompCert4Lean.X86_64.Archi.ptr64] using
                (memdata_load_result_inject_local f Mint64
                  (proj_value Q64 vl1) (proj_value Q64 vl2)
                  (proj_value_inject f Q64 vl1 vl2 hrel))
          | Mfloat32 =>
              simp [decode_val, hp1, hp2, CompCert4Lean.X86_64.Archi.ptr64]
              exact Val.inject.val_inject_undef _
          | Mfloat64 =>
              simp [decode_val, hp1, hp2, CompCert4Lean.X86_64.Archi.ptr64]
              exact Val.inject.val_inject_undef _
          | Many32 =>
              simpa [decode_val, hp1, hp2] using
                (memdata_load_result_inject_local f Many32
                  (proj_value Q32 vl1) (proj_value Q32 vl2)
                  (proj_value_inject f Q32 vl1 vl2 hrel))
          | Many64 =>
              simpa [decode_val, hp1, hp2] using
                (memdata_load_result_inject_local f Many64
                  (proj_value Q64 vl1) (proj_value Q64 vl2)
                  (proj_value_inject f Q64 vl1 vl2 hrel))
      | some bl2 =>
          have hp2ne : proj_bytes vl2 ≠ none := by simp [hp2]
          have hu : Undef ∈ vl1 := proj_bytes_not_inject f vl1 vl2 hrel hp1 hp2ne
          have hq32 : proj_value Q32 vl1 = Vundef := proj_value_undef Q32 vl1 hu
          have hq64 : proj_value Q64 vl1 = Vundef := proj_value_undef Q64 vl1 hu
          cases chunk with
          | Mbool =>
              simp [decode_val, hp1, hp2, CompCert4Lean.X86_64.Archi.ptr64]
              exact Val.inject.val_inject_undef _
          | Mint8signed =>
              simp [decode_val, hp1, hp2, CompCert4Lean.X86_64.Archi.ptr64]
              exact Val.inject.val_inject_undef _
          | Mint8unsigned =>
              simp [decode_val, hp1, hp2, CompCert4Lean.X86_64.Archi.ptr64]
              exact Val.inject.val_inject_undef _
          | Mint16signed =>
              simp [decode_val, hp1, hp2, CompCert4Lean.X86_64.Archi.ptr64]
              exact Val.inject.val_inject_undef _
          | Mint16unsigned =>
              simp [decode_val, hp1, hp2, CompCert4Lean.X86_64.Archi.ptr64]
              exact Val.inject.val_inject_undef _
          | Mint32 =>
              simp [decode_val, hp1, hp2, CompCert4Lean.X86_64.Archi.ptr64]
              exact Val.inject.val_inject_undef _
          | Mint64 =>
              simpa [decode_val, Val.load_result, hp1, hp2,
                CompCert4Lean.X86_64.Archi.ptr64, hq64] using
                (Val.inject.val_inject_undef (decode_val Mint64 vl2))
          | Mfloat32 =>
              simp [decode_val, hp1, hp2, CompCert4Lean.X86_64.Archi.ptr64]
              exact Val.inject.val_inject_undef _
          | Mfloat64 =>
              simp [decode_val, hp1, hp2, CompCert4Lean.X86_64.Archi.ptr64]
              exact Val.inject.val_inject_undef _
          | Many32 =>
              simpa [decode_val, Val.load_result, hp1, hp2, hq32] using
                (Val.inject.val_inject_undef (decode_val Many32 vl2))
          | Many64 =>
              simpa [decode_val, Val.load_result, hp1, hp2, hq64] using
                (Val.inject.val_inject_undef (decode_val Many64 vl2))

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

theorem repeat_Undef_inject_self : repeat_Undef_inject_selfStatement := by
  intro f n
  induction n with
  | zero => constructor
  | succ n ih =>
      simp only [List.replicate_succ]
      constructor
      · exact memval_inject.undef f Undef
      · exact ih

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

theorem repeat_Undef_inject_encode_val : repeat_Undef_inject_encode_valStatement := by
  intro f chunk v
  have h := repeat_Undef_inject_any f (encode_val chunk v)
  have hlen := encode_val_length chunk v
  rw [hlen] at h
  exact h

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

open CompCert4Lean.Common.Values

theorem inj_value_inject : inj_value_injectStatement := by
  intro f v1 v2 q hval
  have hrec : ∀ (n : Nat) (v1 v2 : val) (q : quantity),
      Val.inject f v1 v2 →
        list_forall2 (memval_inject f)
          (inj_value_rec n v1 q) (inj_value_rec n v2 q) := by
    intro n
    induction n with
    | zero =>
        intro v1 v2 q h
        constructor
    | succ n ih =>
        intro v1 v2 q h
        simp only [inj_value_rec]
        constructor
        · exact memval_inject.fragment f v1 v2 q n h
        · exact ih v1 v2 q h
  exact hrec (size_quantity_nat q) v1 v2 q hval

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

open CompCert4Lean.Common.Values
open CompCert4Lean.Common.AST

theorem encode_val_inject : encode_val_injectStatement := by
  intro f v1 v2 chunk h
  cases h with
  | inject_int i =>
      cases chunk with
      | Mbool => exact inj_bytes_inject f _
      | Mint8signed => exact inj_bytes_inject f _
      | Mint8unsigned => exact inj_bytes_inject f _
      | Mint16signed => exact inj_bytes_inject f _
      | Mint16unsigned => exact inj_bytes_inject f _
      | Mint32 => exact inj_bytes_inject f _
      | Mint64 => exact repeat_Undef_inject_self f _
      | Mfloat32 => exact repeat_Undef_inject_self f _
      | Mfloat64 => exact repeat_Undef_inject_self f _
      | Many32 => exact inj_value_inject f (Vint i) (Vint i) Q32 (Val.inject.inject_int i)
      | Many64 => exact inj_value_inject f (Vint i) (Vint i) Q64 (Val.inject.inject_int i)
  | inject_long i =>
      cases chunk with
      | Mbool => exact repeat_Undef_inject_self f _
      | Mint8signed => exact repeat_Undef_inject_self f _
      | Mint8unsigned => exact repeat_Undef_inject_self f _
      | Mint16signed => exact repeat_Undef_inject_self f _
      | Mint16unsigned => exact repeat_Undef_inject_self f _
      | Mint32 => exact repeat_Undef_inject_self f _
      | Mint64 => exact inj_bytes_inject f _
      | Mfloat32 => exact repeat_Undef_inject_self f _
      | Mfloat64 => exact repeat_Undef_inject_self f _
      | Many32 => exact inj_value_inject f (Vlong i) (Vlong i) Q32 (Val.inject.inject_long i)
      | Many64 => exact inj_value_inject f (Vlong i) (Vlong i) Q64 (Val.inject.inject_long i)
  | inject_float x =>
      cases chunk with
      | Mbool => exact repeat_Undef_inject_self f _
      | Mint8signed => exact repeat_Undef_inject_self f _
      | Mint8unsigned => exact repeat_Undef_inject_self f _
      | Mint16signed => exact repeat_Undef_inject_self f _
      | Mint16unsigned => exact repeat_Undef_inject_self f _
      | Mint32 => exact repeat_Undef_inject_self f _
      | Mint64 => exact repeat_Undef_inject_self f _
      | Mfloat32 => exact repeat_Undef_inject_self f _
      | Mfloat64 => exact inj_bytes_inject f _
      | Many32 => exact inj_value_inject f (Vfloat x) (Vfloat x) Q32 (Val.inject.inject_float x)
      | Many64 => exact inj_value_inject f (Vfloat x) (Vfloat x) Q64 (Val.inject.inject_float x)
  | inject_single x =>
      cases chunk with
      | Mbool => exact repeat_Undef_inject_self f _
      | Mint8signed => exact repeat_Undef_inject_self f _
      | Mint8unsigned => exact repeat_Undef_inject_self f _
      | Mint16signed => exact repeat_Undef_inject_self f _
      | Mint16unsigned => exact repeat_Undef_inject_self f _
      | Mint32 => exact repeat_Undef_inject_self f _
      | Mint64 => exact repeat_Undef_inject_self f _
      | Mfloat32 => exact inj_bytes_inject f _
      | Mfloat64 => exact repeat_Undef_inject_self f _
      | Many32 => exact inj_value_inject f (Vsingle x) (Vsingle x) Q32 (Val.inject.inject_single x)
      | Many64 => exact inj_value_inject f (Vsingle x) (Vsingle x) Q64 (Val.inject.inject_single x)
  | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
      cases chunk with
      | Mbool => exact repeat_Undef_inject_self f _
      | Mint8signed => exact repeat_Undef_inject_self f _
      | Mint8unsigned => exact repeat_Undef_inject_self f _
      | Mint16signed => exact repeat_Undef_inject_self f _
      | Mint16unsigned => exact repeat_Undef_inject_self f _
      | Mint32 =>
          by_cases hp : CompCert4Lean.X86_64.Archi.ptr64 = true
          · exact repeat_Undef_inject_self f _
          · simpa [encode_val, hp] using
              (inj_value_inject f (Vptr b1 ofs1) (Vptr b2 ofs2) Q32
                (Val.inject.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs))
      | Mint64 =>
          by_cases hp : CompCert4Lean.X86_64.Archi.ptr64 = true
          · simpa [encode_val, hp] using
              (inj_value_inject f (Vptr b1 ofs1) (Vptr b2 ofs2) Q64
                (Val.inject.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs))
          · simpa [encode_val, hp] using (repeat_Undef_inject_self f 8)
      | Mfloat32 => exact repeat_Undef_inject_self f _
      | Mfloat64 => exact repeat_Undef_inject_self f _
      | Many32 =>
          exact inj_value_inject f (Vptr b1 ofs1) (Vptr b2 ofs2) Q32
            (Val.inject.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs)
      | Many64 =>
          exact inj_value_inject f (Vptr b1 ofs1) (Vptr b2 ofs2) Q64
            (Val.inject.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs)
  | val_inject_undef v =>
      cases chunk with
      | Mbool => exact repeat_Undef_inject_encode_val f Mbool _
      | Mint8signed => exact repeat_Undef_inject_encode_val f Mint8signed _
      | Mint8unsigned => exact repeat_Undef_inject_encode_val f Mint8unsigned _
      | Mint16signed => exact repeat_Undef_inject_encode_val f Mint16signed _
      | Mint16unsigned => exact repeat_Undef_inject_encode_val f Mint16unsigned _
      | Mint32 => exact repeat_Undef_inject_encode_val f Mint32 _
      | Mint64 => exact repeat_Undef_inject_encode_val f Mint64 _
      | Mfloat32 => exact repeat_Undef_inject_encode_val f Mfloat32 _
      | Mfloat64 => exact repeat_Undef_inject_encode_val f Mfloat64 _
      | Many32 =>
          cases v2 <;>
            simpa [encode_val] using
              (inj_value_inject f Vundef _ Q32 (Val.inject.val_inject_undef _))
      | Many64 =>
          cases v2 <;>
            simpa [encode_val] using
              (inj_value_inject f Vundef _ Q64 (Val.inject.val_inject_undef _))

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

open Lean Elab Tactic Meta

private def memdataPrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem memdata_wordcore_add_val {bits : Nat}
    (x y : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    (CompCert4Lean.Lib.Integers.WordCore.add x y).val =
      (x.val + y.val) % (2 ^ bits) := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let yF := (lctx.findFromUserName? `y).get!
    let e ← mkAppM
      (memdataPrivateName "CompCert4Lean.Lib.Integers.WordCore.add_val")
      #[mkFVar xF.fvarId, mkFVar yF.fvarId]
    closeMainGoal Name.anonymous e

private theorem memdata_wordcore_zero_val (bits : Nat) :
    (CompCert4Lean.Lib.Integers.WordCore.zero bits).val = 0 := by
  unfold CompCert4Lean.Lib.Integers.WordCore.zero
  run_tac
    let lctx ← getLCtx
    let bF := (lctx.findFromUserName? `bits).get!
    let e ← mkAppM
      (memdataPrivateName "CompCert4Lean.Lib.Integers.WordCore.val_repr_residue")
      #[mkFVar bF.fvarId,
        mkConst ``CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0]
    closeMainGoal Name.anonymous e

private theorem memdata_wordcore_val_lt
    (x : CompCert4Lean.Lib.Integers.WordCore.Word
      CompCert4Lean.Lib.Integers.Ptrofs.wordsize) :
    x.val < 2 ^ CompCert4Lean.Lib.Integers.Ptrofs.wordsize := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let e ← mkAppM
      (memdataPrivateName "CompCert4Lean.Lib.Integers.WordCore.val_lt")
      #[mkFVar xF.fvarId]
    closeMainGoal Name.anonymous e

private theorem memdata_ptrofs_add_zero
    (ofs : CompCert4Lean.Lib.Integers.Ptrofs.int) :
    CompCert4Lean.Lib.Integers.Ptrofs.add ofs
      (CompCert4Lean.Lib.Integers.Ptrofs.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0)) = ofs := by
  change CompCert4Lean.Lib.Integers.WordCore.add ofs
    (CompCert4Lean.Lib.Integers.WordCore.zero
      CompCert4Lean.Lib.Integers.Ptrofs.wordsize) = ofs
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [memdata_wordcore_add_val, memdata_wordcore_zero_val, Nat.add_zero]
  exact Nat.mod_eq_of_lt (memdata_wordcore_val_lt ofs)

theorem memval_lessdef_refl : memval_lessdef_reflStatement := by
  intro mv
  cases mv with
  | Undef =>
      exact memval_inject.undef CompCert4Lean.Common.Values.inject_id Undef
  | Byte b =>
      exact memval_inject.byte CompCert4Lean.Common.Values.inject_id b
  | Fragment v q i =>
      apply memval_inject.fragment
      cases v with
      | Vundef => exact CompCert4Lean.Common.Values.Val.inject.val_inject_undef _
      | Vint n => exact CompCert4Lean.Common.Values.Val.inject.inject_int _
      | Vlong n => exact CompCert4Lean.Common.Values.Val.inject.inject_long _
      | Vfloat f => exact CompCert4Lean.Common.Values.Val.inject.inject_float _
      | Vsingle f => exact CompCert4Lean.Common.Values.Val.inject.inject_single _
      | Vptr b ofs =>
          apply CompCert4Lean.Common.Values.Val.inject.inject_ptr
          · rfl
          · symm
            exact memdata_ptrofs_add_zero ofs

theorem int_of_bytes_range : int_of_bytes_rangeStatement := by
  intro l
  exact int_of_bytes_range_proof_api l

theorem int_of_bytes_append : int_of_bytes_appendStatement := by
  have hadd0 (x : Z) : zAdd z0 x = x := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [zAdd, ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
  have hmul0 (x : Z) : zMul x z0 = z0 := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [zMul, ZArith.BinInt.Z.mul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
  have hmul1 (x : Z) : zMul x (zOfNat 1) = x := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [zMul, zOfNat, ZArith.BinInt.Z.mul,
      ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    simp
  have hmulZeroNat : zMul (zOfNat 0) z8 = zOfNat 0 := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [zMul, zOfNat, z8, ZArith.BinInt.Z.mul,
      ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    simp
  have hpow0 : zTwoP (zMul (zOfNat 0) z8) = zOfNat 1 := by
    rw [hmulZeroNat]
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    have hz1 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zOfNat 1) =
        Int.ofNat 1 := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat 1)) = Int.ofNat 1
      rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    rw [hz1]
    simpa [zTwoP] using (intOfZ_two_p_zOfNat 0)
  intro l2 l1
  induction l1 with
  | nil =>
      simp only [List.nil_append, List.length_nil]
      simp only [int_of_bytes]
      rw [hpow0, hmul1, hadd0]
  | cons b l ih =>
      simp only [List.cons_append, int_of_bytes, List.length_cons]
      rw [ih]
      have hpow : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (zTwoP (zMul (zOfNat (l.length + 1)) z8)) =
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (zTwoP (zMul (zOfNat l.length) z8)) * 256 := by
        rw [show zMul (zOfNat (l.length + 1)) z8 =
          zOfNat (l.length * 8 + 8) by
            apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
            simp only [zMul, zOfNat, z8,
              ZArith.BinInt.Z.mul,
              ZArith.BinInt.Z.of_nat,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
            change ((l.length + 1 : Nat) : Int) * 8 =
              ((l.length * 8 + 8 : Nat) : Int)
            omega]
        rw [intOfZ_two_p_zOfNat]
        have hrest : zMul (zOfNat l.length) z8 = zOfNat (l.length * 8) := by
          apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
          simp only [zMul, zOfNat, z8,
            ZArith.BinInt.Z.mul,
            ZArith.BinInt.Z.of_nat,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          change ((l.length : Nat) : Int) * 8 =
            ((l.length * 8 : Nat) : Int)
          omega
        rw [hrest, intOfZ_two_p_zOfNat]
        rw [_root_.Int.pow_add]
        simp
      have hpowZ : zTwoP (zMul (zOfNat (l.length + 1)) z8) =
          zMul (zTwoP (zMul (zOfNat l.length) z8)) z256 := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        rw [hpow]
        simp [zMul, z256, ZArith.BinInt.Z.mul,
          ZArith.BinInt.Z.of_nat,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      rw [hpowZ]
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp only [zAdd, zMul, z256, ZArith.BinInt.Z.add,
        ZArith.BinInt.Z.mul, ZArith.BinInt.Z.of_nat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      rw [Int.add_mul, Int.mul_assoc]
      simp [Int.add_assoc]

theorem length_proj_bytes : length_proj_bytesStatement := by
  intro l
  induction l with
  | nil =>
      intro b h
      cases h
      simp
  | cons a l ih =>
      intro b h
      cases a with
      | Undef => simp [proj_bytes] at h
      | Fragment v q i => simp [proj_bytes] at h
      | Byte b =>
          cases hp : proj_bytes l with
          | none => simp [proj_bytes, hp] at h
          | some bl =>
              simp [proj_bytes, hp] at h
              cases h
              have hlen := ih bl hp
              simp [hlen]

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

theorem proj_bytes_append : proj_bytes_appendStatement := by
  intro l2 l1
  induction l1 with
  | nil =>
      cases h : proj_bytes l2 <;> simp [proj_bytes, h]
  | cons a l ih =>
      cases a with
      | Undef => simp [proj_bytes]
      | Fragment v q i => simp [proj_bytes]
      | Byte b =>
          simp only [List.cons_append, proj_bytes]
          cases hl : proj_bytes l with
          | none =>
              rw [ih]
              simp [hl]
          | some bl =>
              rw [ih]
              cases h2 : proj_bytes l2 <;> simp [hl, h2]

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

theorem encode_val_int64 : encode_val_int64Statement := by
  intro v hptr64
  simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr64

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

private abbrev pgZ := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
private abbrev pgAdd : pgZ → pgZ → pgZ :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
private abbrev pgMul : pgZ → pgZ → pgZ :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
private abbrev pgDiv : pgZ → pgZ → pgZ :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div
private abbrev pgOfNat : Nat → pgZ :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
private abbrev pgTwoP : pgZ → pgZ :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.two_p
private abbrev pg8 : pgZ := pgOfNat 8
private abbrev pg256 : pgZ := pgOfNat 256

private theorem pg_bytes_of_int_mod_pow_succ (n : Nat) :
    pgTwoP (pgMul (pgOfNat (Nat.succ n)) pg8) =
      pgMul (pgTwoP (pgMul (pgOfNat n) pg8)) pg256 := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  rw [show pgMul (pgOfNat (Nat.succ n)) pg8 =
      pgOfNat ((Nat.succ n) * 8) by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [pgMul, pgOfNat, pg8,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        rfl]
  rw [show pgMul (pgOfNat n) pg8 = pgOfNat (n * 8) by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [pgMul, pgOfNat, pg8,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        rfl]
  simp only [pgMul, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  rw [intOfZ_two_p_zOfNat, intOfZ_two_p_zOfNat]
  simp only [pg256, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  rw [show (Nat.succ n) * 8 = n * 8 + 8 by omega, _root_.Int.pow_add]
  rfl

private theorem pg_bytes_of_int_mod_head (n : Nat)
    (x y : pgZ)
    (h : CompCert4Lean.Lib.Zbits.eqmod
      (pgTwoP (pgMul (pgOfNat (Nat.succ n)) pg8)) x y) :
    CompCert4Lean.Lib.Integers.Byte.repr x =
      CompCert4Lean.Lib.Integers.Byte.repr y := by
  apply CompCert4Lean.Lib.Integers.Byte.eqm_samerepr_proof
  apply CompCert4Lean.Lib.Zbits.eqmod_divides
      (pgTwoP (pgMul (pgOfNat (Nat.succ n)) pg8)) (pgTwoP pg8) x y h
  rw [pg_bytes_of_int_mod_pow_succ]
  exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.divide_factor_r _ _

theorem bytes_of_int_mod : bytes_of_int_modStatement := by
  intro n
  induction n with
  | zero =>
      intro x y h
      rfl
  | succ n ih =>
      intro x y h
      simp only [bytes_of_int]
      congr 1
      · apply pg_bytes_of_int_mod_head n x y
        exact h
      · apply ih
        rcases h with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        rw [hk]
        change pgDiv (pgAdd (pgMul k (pgTwoP (pgMul (pgOfNat (Nat.succ n)) pg8))) y) pg256 =
          pgAdd (pgMul k (pgTwoP (pgMul (pgOfNat n) pg8))) (pgDiv y pg256)
        rw [pg_bytes_of_int_mod_pow_succ]
        have hassoc : pgMul k
            (pgMul (pgTwoP (pgMul (pgOfNat n) pg8)) pg256) =
            pgMul (pgMul k (pgTwoP (pgMul (pgOfNat n) pg8))) pg256 :=
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul_assoc _ _ _
        rw [hassoc]
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Z_div_plus_full_l
        intro hz
        have hz' := congrArg
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hz
        change (256 : _root_.Int) = 0 at hz'
        omega

end CompCert4Lean.Common.Memdata

namespace CompCert4Lean.Common.Memdata

theorem encode_int_8_mod : encode_int_8_modStatement := by
  intro x y h
  unfold encode_int
  congr 1
  apply bytes_of_int_mod
  exact h

end CompCert4Lean.Common.Memdata
