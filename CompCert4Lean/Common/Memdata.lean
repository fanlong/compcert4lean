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
