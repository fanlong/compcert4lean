import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.RocqString
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Errors
import CompCert4Lean.Common.Linking
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Maps
import CompCert4Lean.X86_64.Archi

/-!
# C types

Definition-bearing translation of CompCert's `cfrontend/Ctypes.v`.  Theorems
assigned to the later proof phase are represented by exact proposition or
type descriptors.  Composite values retain the source proof-carrying fields.
-/

namespace CompCert4Lean.Cfrontend.Ctypes

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common
open CompCert4Lean.Lib.Maps

private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string
private abbrev ident := CompCert4Lean.Common.AST.ident
private abbrev calling_convention := CompCert4Lean.Common.AST.calling_convention
private abbrev external_function := CompCert4Lean.Common.AST.external_function
private abbrev memory_chunk := CompCert4Lean.Common.AST.memory_chunk
private abbrev xtype := CompCert4Lean.Common.AST.xtype
private abbrev signature := CompCert4Lean.Common.AST.signature

private abbrev z0 : Z := .Z0
private abbrev z1 : Z := .Zpos .xH
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev zOfN := ZArith.BinInt.Z.of_N
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zMul := ZArith.BinInt.Z.mul
private abbrev zDiv := ZArith.BinInt.Z.div
private abbrev zMax := ZArith.BinInt.Z.max
private abbrev zMin := ZArith.BinInt.Z.min
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev zGt := ZArith.BinInt.Z.gt
private abbrev zDivide := ZArith.BinInt.Z.divide
private abbrev align := CompCert4Lean.Lib.Coqlib.align
private abbrev floor := CompCert4Lean.Lib.Coqlib.floor
private abbrev two_p := ZArith.Zpower.two_p
private abbrev two_power_nat := ZArith.Zpower.two_power_nat

private def rocqStringOfBytes : List UInt8 -> RocqString
  | [] => .EmptyString
  | b :: bs => .String b (rocqStringOfBytes bs)

private def zeroWidthBitfieldText : RocqString :=
  rocqStringOfBytes [97, 99, 99, 101, 115, 115, 105, 110, 103, 32, 122, 101,
    114, 111, 45, 119, 105, 100, 116, 104, 32, 98, 105, 116, 102, 105, 101,
    108, 100]

private def bitfieldTooWideText : RocqString :=
  rocqStringOfBytes [98, 105, 116, 102, 105, 101, 108, 100, 32, 116, 111, 111,
    32, 119, 105, 100, 101]

private def unknownFieldText : RocqString :=
  rocqStringOfBytes [85, 110, 107, 110, 111, 119, 110, 32, 102, 105, 101, 108,
    100, 32]

private def duplicateCompositeText : RocqString :=
  rocqStringOfBytes [77, 117, 108, 116, 105, 112, 108, 101, 32, 100, 101, 102,
    105, 110, 105, 116, 105, 111, 110, 115, 32, 111, 102, 32, 115, 116, 114,
    117, 99, 116, 32, 111, 114, 32, 117, 110, 105, 111, 110, 32]

private def incompleteCompositeText : RocqString :=
  rocqStringOfBytes [73, 110, 99, 111, 109, 112, 108, 101, 116, 101, 32, 115,
    116, 114, 117, 99, 116, 32, 111, 114, 32, 117, 110, 105, 111, 110, 32]

/-! ## Type syntax -/

inductive signedness : Type where
  | Signed
  | Unsigned
deriving DecidableEq

export signedness (Signed Unsigned)

inductive intsize : Type where
  | I8
  | I16
  | I32
  | IBool
deriving DecidableEq

export intsize (I8 I16 I32 IBool)

inductive floatsize : Type where
  | F32
  | F64
deriving DecidableEq

export floatsize (F32 F64)

structure attr : Type where
  attr_volatile : Bool
  attr_alignas : Option N
deriving DecidableEq

export attr (attr_volatile attr_alignas)

def noattr : attr :=
  { attr_volatile := false, attr_alignas := none }

inductive type : Type where
  | Tvoid
  | Tint (size : intsize) (signed : signedness) (attributes : attr)
  | Tlong (signed : signedness) (attributes : attr)
  | Tfloat (size : floatsize) (attributes : attr)
  | Tpointer (element : type) (attributes : attr)
  | Tarray (element : type) (length : Z) (attributes : attr)
  | Tfunction (args : List type) (result : type) (cc : calling_convention)
  | Tstruct (id : ident) (attributes : attr)
  | Tunion (id : ident) (attributes : attr)

export type (Tvoid Tint Tlong Tfloat Tpointer Tarray Tfunction Tstruct Tunion)

def intsize_eqStatement :=
  forall s1 s2 : intsize, Sumbool (s1 = s2) (s1 ≠ s2)

def signedness_eqStatement :=
  forall s1 s2 : signedness, Sumbool (s1 = s2) (s1 ≠ s2)

def floatsize_eqStatement :=
  forall s1 s2 : floatsize, Sumbool (s1 = s2) (s1 ≠ s2)

def attr_eqStatement :=
  forall a1 a2 : attr, Sumbool (a1 = a2) (a1 ≠ a2)

def type_eqStatement :=
  forall t1 t2 : type, Sumbool (t1 = t2) (t1 ≠ t2)

def attr_of_type : type -> attr
  | .Tvoid => noattr
  | .Tint _ _ a => a
  | .Tlong _ a => a
  | .Tfloat _ a => a
  | .Tpointer _ a => a
  | .Tarray _ _ a => a
  | .Tfunction _ _ _ => noattr
  | .Tstruct _ a => a
  | .Tunion _ a => a

def change_attributes (f : attr -> attr) : type -> type
  | .Tvoid => .Tvoid
  | .Tint sz sg a => .Tint sz sg (f a)
  | .Tlong sg a => .Tlong sg (f a)
  | .Tfloat sz a => .Tfloat sz (f a)
  | .Tpointer t a => .Tpointer t (f a)
  | .Tarray t n a => .Tarray t n (f a)
  | .Tfunction args res cc => .Tfunction args res cc
  | .Tstruct id a => .Tstruct id (f a)
  | .Tunion id a => .Tunion id (f a)

def remove_attributes (t : type) : type :=
  change_attributes (fun _ => noattr) t

def bitsize_intsize : intsize -> Z
  | .I8 => zOfNat 8
  | .I16 => zOfNat 16
  | .I32 => zOfNat 32
  | .IBool => zOfNat 1

inductive struct_or_union : Type where
  | Struct
  | Union
deriving DecidableEq

export struct_or_union (Struct Union)

inductive member : Type where
  | Member_plain (id : ident) (t : type)
  | Member_bitfield (id : ident) (size : intsize) (signed : signedness)
      (attributes : attr) (width : Z) (padding : Bool)

export member (Member_plain Member_bitfield)

def members : Type := List member

inductive composite_definition : Type where
  | Composite (id : ident) (su : struct_or_union) (members : members) (attributes : attr)

export composite_definition (Composite)

def name_member : member -> ident
  | .Member_plain id _ => id
  | .Member_bitfield id _ _ _ _ _ => id

def type_member : member -> type
  | .Member_plain _ t => t
  | .Member_bitfield _ sz sg a width _ =>
      match CompCert4Lean.Lib.Coqlib.zlt width (bitsize_intsize sz) with
      | .left _ => .Tint sz .Signed a
      | .right _ => .Tint sz sg a

def member_is_padding : member -> Bool
  | .Member_plain _ _ => false
  | .Member_bitfield _ _ _ _ _ padding => padding

structure composite : Type where
  co_su : struct_or_union
  co_members : members
  co_attr : attr
  co_sizeof : Z
  co_alignof : Z
  co_rank : Nat
  co_sizeof_pos : zLe z0 co_sizeof
  co_alignof_two_p : Exists fun n : Nat => co_alignof = two_power_nat n
  co_sizeof_alignof : zDivide co_alignof co_sizeof

export composite (co_su co_members co_attr co_sizeof co_alignof co_rank
  co_sizeof_pos co_alignof_two_p co_sizeof_alignof)

def composite_env : Type := PTree.t composite

inductive bitfield : Type where
  | Full
  | Bits (size : intsize) (signed : signedness) (pos : Z) (width : Z)
deriving DecidableEq

export bitfield (Full Bits)

def type_int32s : type := .Tint .I32 .Signed noattr
def type_bool : type := .Tint .IBool .Signed noattr

def typeconv : type -> type
  | .Tint .I8 _ _ => type_int32s
  | .Tint .I16 _ _ => type_int32s
  | .Tint .IBool _ _ => type_int32s
  | .Tarray t _ _ => .Tpointer t noattr
  | t@(.Tfunction _ _ _) => .Tpointer t noattr
  | t => remove_attributes t

def default_argument_conversion : type -> type
  | .Tint .I8 _ _ => type_int32s
  | .Tint .I16 _ _ => type_int32s
  | .Tint .IBool _ _ => type_int32s
  | .Tfloat _ _ => .Tfloat .F64 noattr
  | .Tarray t _ _ => .Tpointer t noattr
  | t@(.Tfunction _ _ _) => .Tpointer t noattr
  | t => remove_attributes t

/-! ## Completeness, alignment, and size -/

def complete_type (env : composite_env) : type -> Bool
  | .Tvoid => false
  | .Tint _ _ _ => true
  | .Tlong _ _ => true
  | .Tfloat _ _ => true
  | .Tpointer _ _ => true
  | .Tarray t _ _ => complete_type env t
  | .Tfunction _ _ _ => false
  | .Tstruct id _ | .Tunion id _ => (PTree.get id env).isSome

def align_attr (a : attr) (al : Z) : Z :=
  match a.attr_alignas with
  | some l => two_power_nat (NArith.BinNat.N.to_nat l)
  | none => al

def alignof (env : composite_env) : type -> Z
  | .Tvoid => align_attr noattr (zOfNat 1)
  | .Tint .I8 _ a => align_attr a (zOfNat 1)
  | .Tint .I16 _ a => align_attr a (zOfNat 2)
  | .Tint .I32 _ a => align_attr a (zOfNat 4)
  | .Tint .IBool _ a => align_attr a (zOfNat 1)
  | .Tlong _ a => align_attr a CompCert4Lean.X86_64.Archi.align_int64
  | .Tfloat .F32 a => align_attr a (zOfNat 4)
  | .Tfloat .F64 a => align_attr a CompCert4Lean.X86_64.Archi.align_float64
  | .Tpointer _ a =>
      align_attr a (if CompCert4Lean.X86_64.Archi.ptr64 then zOfNat 8 else zOfNat 4)
  | .Tarray t _ a => align_attr a (alignof env t)
  | .Tfunction _ _ _ => align_attr noattr (zOfNat 1)
  | .Tstruct id a | .Tunion id a =>
      align_attr a (match PTree.get id env with | some co => co.co_alignof | none => zOfNat 1)

def sizeof (env : composite_env) : type -> Z
  | .Tvoid => zOfNat 1
  | .Tint .I8 _ _ => zOfNat 1
  | .Tint .I16 _ _ => zOfNat 2
  | .Tint .I32 _ _ => zOfNat 4
  | .Tint .IBool _ _ => zOfNat 1
  | .Tlong _ _ => zOfNat 8
  | .Tfloat .F32 _ => zOfNat 4
  | .Tfloat .F64 _ => zOfNat 8
  | .Tpointer _ _ => if CompCert4Lean.X86_64.Archi.ptr64 then zOfNat 8 else zOfNat 4
  | .Tarray t n _ => zMul (sizeof env t) (zMax z0 n)
  | .Tfunction _ _ _ => zOfNat 1
  | .Tstruct id _ | .Tunion id _ =>
      match PTree.get id env with | some co => co.co_sizeof | none => z0

def align_attr_two_pStatement : Prop :=
  forall al a, (Exists fun n : Nat => al = two_power_nat n) ->
    Exists fun n : Nat => align_attr a al = two_power_nat n

def alignof_two_pStatement : Prop :=
  forall env t, Exists fun n : Nat => alignof env t = two_power_nat n

def alignof_posStatement : Prop :=
  forall env t, zGt (alignof env t) z0

def sizeof_posStatement : Prop :=
  forall env t, zLe z0 (sizeof env t)

/-! ## Layout -/

def bitalignof (env : composite_env) (t : type) : Z :=
  zMul (alignof env t) (zOfNat 8)

def bitsizeof (env : composite_env) (t : type) : Z :=
  zMul (sizeof env t) (zOfNat 8)

def bitalignof_intsize : intsize -> Z
  | .I8 | .IBool => zOfNat 8
  | .I16 => zOfNat 16
  | .I32 => zOfNat 32

def next_field (env : composite_env) (pos : Z) : member -> Z
  | .Member_plain _ t => zAdd (align pos (bitalignof env t)) (bitsizeof env t)
  | .Member_bitfield _ sz _ _ width _ =>
      let s := bitalignof_intsize sz
      match CompCert4Lean.Lib.Coqlib.zle width z0 with
      | .left _ => align pos s
      | .right _ =>
          let current := floor pos s
          let next := zAdd current s
          match CompCert4Lean.Lib.Coqlib.zle (zAdd pos width) next with
          | .left _ => zAdd pos width
          | .right _ => zAdd next width

def layout_field (env : composite_env) (pos : Z) : member -> Errors.res (Z × bitfield)
  | .Member_plain _ t =>
      .OK (zDiv (align pos (bitalignof env t)) (zOfNat 8), Full)
  | .Member_bitfield _ sz sg _ width _ =>
      match CompCert4Lean.Lib.Coqlib.zle width z0 with
      | .left _ => .Error (Errors.msg zeroWidthBitfieldText)
      | .right _ =>
          match CompCert4Lean.Lib.Coqlib.zlt (bitsize_intsize sz) width with
          | .left _ => .Error (Errors.msg bitfieldTooWideText)
          | .right _ =>
              let s := bitalignof_intsize sz
              let start := floor pos s
              let next := zAdd start s
              match CompCert4Lean.Lib.Coqlib.zle (zAdd pos width) next with
              | .left _ => .OK (zDiv start (zOfNat 8), Bits sz sg (zSub pos start) width)
              | .right _ => .OK (zDiv next (zOfNat 8), Bits sz sg z0 width)

def bitalignof_intsize_posStatement : Prop :=
  forall sz, zGt (bitalignof_intsize sz) z0

def next_field_incrStatement : Prop :=
  forall env pos m, zLe pos (next_field env pos m)

def alignof_composite (env : composite_env) : members -> Z
  | [] => zOfNat 1
  | m :: ms =>
      if member_is_padding m then alignof_composite env ms
      else zMax (alignof env (type_member m)) (alignof_composite env ms)

def bitsizeof_struct (env : composite_env) : Z -> members -> Z
  | current, [] => current
  | current, m :: ms => bitsizeof_struct env (next_field env current m) ms

def bytes_of_bits (n : Z) : Z :=
  zDiv (zAdd n (zOfNat 7)) (zOfNat 8)

def sizeof_struct (env : composite_env) (ms : members) : Z :=
  bytes_of_bits (bitsizeof_struct env z0 ms)

def sizeof_union (env : composite_env) : members -> Z
  | [] => z0
  | m :: ms => zMax (sizeof env (type_member m)) (sizeof_union env ms)

def alignof_composite_two_pStatement : Prop :=
  forall env m, Exists fun n : Nat => alignof_composite env m = two_power_nat n

def alignof_composite_posStatement : Prop :=
  forall env m a, zGt (align_attr a (alignof_composite env m)) z0

def bitsizeof_struct_incrStatement : Prop :=
  forall env m current, zLe current (bitsizeof_struct env current m)

def sizeof_union_posStatement : Prop :=
  forall env m, zLe z0 (sizeof_union env m)

def field_offset_rec (env : composite_env) (id : ident) : members -> Z -> Errors.res (Z × bitfield)
  | [], _ => .Error (Errors.MSG unknownFieldText :: Errors.CTX id :: [])
  | m :: ms, pos =>
      match AST.ident_eq id (name_member m) with
      | .left _ => layout_field env pos m
      | .right _ => field_offset_rec env id ms (next_field env pos m)

def field_offset (env : composite_env) (id : ident) (ms : members) : Errors.res (Z × bitfield) :=
  field_offset_rec env id ms z0

def union_field_offset (env : composite_env) (id : ident) : members -> Errors.res (Z × bitfield)
  | [] => .Error (Errors.MSG unknownFieldText :: Errors.CTX id :: [])
  | m :: ms =>
      match AST.ident_eq id (name_member m) with
      | .left _ => layout_field env z0 m
      | .right _ => union_field_offset env id ms

/-! ## Access modes and back-end types -/

inductive mode : Type where
  | By_value (chunk : memory_chunk)
  | By_reference
  | By_copy
  | By_nothing
deriving DecidableEq

export mode (By_value By_reference By_copy By_nothing)

def access_mode : type -> mode
  | .Tint .I8 .Signed _ => .By_value .Mint8signed
  | .Tint .I8 .Unsigned _ => .By_value .Mint8unsigned
  | .Tint .I16 .Signed _ => .By_value .Mint16signed
  | .Tint .I16 .Unsigned _ => .By_value .Mint16unsigned
  | .Tint .I32 _ _ => .By_value .Mint32
  | .Tint .IBool _ _ => .By_value .Mbool
  | .Tlong _ _ => .By_value .Mint64
  | .Tfloat .F32 _ => .By_value .Mfloat32
  | .Tfloat .F64 _ => .By_value .Mfloat64
  | .Tvoid => .By_nothing
  | .Tpointer _ _ => .By_value AST.Mptr
  | .Tarray _ _ _ => .By_reference
  | .Tfunction _ _ _ => .By_reference
  | .Tstruct _ _ => .By_copy
  | .Tunion _ _ => .By_copy

def type_is_volatile (t : type) : Bool :=
  match access_mode t with
  | .By_value _ => (attr_of_type t).attr_volatile
  | _ => false

def alignof_blockcopy (env : composite_env) : type -> Z
  | .Tvoid => zOfNat 1
  | .Tint .I8 _ _ => zOfNat 1
  | .Tint .I16 _ _ => zOfNat 2
  | .Tint .I32 _ _ => zOfNat 4
  | .Tint .IBool _ _ => zOfNat 1
  | .Tlong _ _ => zOfNat 8
  | .Tfloat .F32 _ => zOfNat 4
  | .Tfloat .F64 _ => zOfNat 8
  | .Tpointer _ _ => if CompCert4Lean.X86_64.Archi.ptr64 then zOfNat 8 else zOfNat 4
  | .Tarray t _ _ => alignof_blockcopy env t
  | .Tfunction _ _ _ => zOfNat 1
  | .Tstruct id _ | .Tunion id _ =>
      match PTree.get id env with
      | some co => zMin (zOfNat 8) co.co_alignof
      | none => zOfNat 1

def alignof_blockcopy_1248Statement : Prop :=
  forall env t,
    let a := alignof_blockcopy env t
    a = zOfNat 1 ∨ a = zOfNat 2 ∨ a = zOfNat 4 ∨ a = zOfNat 8

def sizeof_alignof_blockcopy_compatStatement : Prop :=
  forall env t, zDivide (alignof_blockcopy env t) (sizeof env t)

def rank_type (env : composite_env) : type -> Nat
  | .Tarray t _ _ => Nat.succ (rank_type env t)
  | .Tstruct id _ | .Tunion id _ =>
      match PTree.get id env with
      | none => 0
      | some co => Nat.succ co.co_rank
  | _ => 0

def rank_members (env : composite_env) : members -> Nat
  | [] => 0
  | .Member_plain _ t :: ms => Nat.max (rank_type env t) (rank_members env ms)
  | .Member_bitfield _ _ _ _ _ _ :: ms => rank_members env ms

def type_of_params (params : List (ident × type)) : List type :=
  params.map Prod.snd

def typ_of_type : type -> AST.typ
  | .Tvoid => .Tint
  | .Tint _ _ _ => .Tint
  | .Tlong _ _ => .Tlong
  | .Tfloat .F32 _ => .Tsingle
  | .Tfloat .F64 _ => .Tfloat
  | .Tpointer _ _ | .Tarray _ _ _ | .Tfunction _ _ _ | .Tstruct _ _ | .Tunion _ _ => AST.Tptr

def argtype_of_type : type -> xtype
  | .Tvoid => .Xvoid
  | .Tint .I32 _ _ => .Xint
  | .Tint .I8 .Signed _ => .Xint8signed
  | .Tint .I8 .Unsigned _ => .Xint8unsigned
  | .Tint .I16 .Signed _ => .Xint16signed
  | .Tint .I16 .Unsigned _ => .Xint16unsigned
  | .Tint .IBool _ _ => .Xbool
  | .Tlong _ _ => .Xlong
  | .Tfloat .F32 _ => .Xsingle
  | .Tfloat .F64 _ => .Xfloat
  | .Tpointer _ _ | .Tarray _ _ _ | .Tfunction _ _ _ | .Tstruct _ _ | .Tunion _ _ => .Xptr

def rettype_of_type : type -> xtype
  | .Tvoid => .Xvoid
  | .Tint .I32 _ _ => .Xint
  | .Tint .I8 .Signed _ => .Xint8signed
  | .Tint .I8 .Unsigned _ => .Xint8unsigned
  | .Tint .I16 .Signed _ => .Xint16signed
  | .Tint .I16 .Unsigned _ => .Xint16unsigned
  | .Tint .IBool _ _ => .Xbool
  | .Tlong _ _ => .Xlong
  | .Tfloat .F32 _ => .Xsingle
  | .Tfloat .F64 _ => .Xfloat
  | .Tpointer _ _ => .Xptr
  | .Tarray _ _ _ | .Tfunction _ _ _ | .Tstruct _ _ | .Tunion _ _ => .Xvoid

def signature_of_type (args : List type) (result : type) (cc : calling_convention) : signature :=
  { sig_args := args.map argtype_of_type, sig_res := rettype_of_type result, sig_cc := cc }

/-! ## Composite environments -/

def sizeof_composite (env : composite_env) (su : struct_or_union) (ms : members) : Z :=
  match su with
  | .Struct => sizeof_struct env ms
  | .Union => sizeof_union env ms

def sizeof_composite_posStatement : Prop :=
  forall env su ms, zLe z0 (sizeof_composite env su ms)

def complete_members (env : composite_env) : members -> Bool
  | [] => true
  | m :: ms => complete_type env (type_member m) && complete_members env ms

private theorem posToNat_positive (p : positive) : 0 < PArith.BinPos.Pos.to_nat p := by
  induction p with
  | xH => decide
  | xI p ih =>
      change 0 < 2 * PArith.BinPos.Pos.to_nat p + 1
      omega
  | xO p ih =>
      change 0 < 2 * PArith.BinPos.Pos.to_nat p
      omega

private theorem zPos_positive (p : positive) : zGt (.Zpos p) z0 := by
  change (0 : Int) < Int.ofNat (PArith.BinPos.Pos.to_nat p)
  exact Int.natCast_pos.mpr (posToNat_positive p)

private theorem zNeg_not_nonneg (p : positive) : Not (zLe z0 (.Zneg p)) := by
  change Not ((0 : Int) <= -Int.ofNat (PArith.BinPos.Pos.to_nat p))
  have hp : (0 : Int) < Int.ofNat (PArith.BinPos.Pos.to_nat p) :=
    Int.natCast_pos.mpr (posToNat_positive p)
  omega

private def zInt : Z -> Int
  | .Z0 => 0
  | .Zpos p => Int.ofNat (PArith.BinPos.Pos.to_nat p)
  | .Zneg p => -Int.ofNat (PArith.BinPos.Pos.to_nat p)

private def zFromInt : Int -> Z
  | .ofNat 0 => .Z0
  | .ofNat (n + 1) => .Zpos (PArith.BinPos.Pos.of_nat (n + 1))
  | .negSucc n => .Zneg (PArith.BinPos.Pos.of_nat (n + 1))

private theorem zLe_iff_zInt (x y : Z) : zLe x y <-> zInt x <= zInt y := by
  cases x <;> cases y <;> rfl

private theorem zLt_iff_zInt (x y : Z) : zLt x y <-> zInt x < zInt y := by
  cases x <;> cases y <;> rfl

private theorem zFromInt_nonneg (i : Int) (h : 0 <= i) : zLe z0 (zFromInt i) := by
  cases i with
  | ofNat n =>
      cases n with
      | zero =>
          change (0 : Int) <= 0
          omega
      | succ n => exact Int.le_of_lt (zPos_positive _)
  | negSucc n => omega

private theorem zFromInt_positive (i : Int) (h : 0 < i) : zGt (zFromInt i) z0 := by
  cases i with
  | ofNat n =>
      cases n with
      | zero =>
          change (0 : Int) < 0 at h
          omega
      | succ n => exact zPos_positive _
  | negSucc n =>
      change (0 : Int) < -Int.ofNat (n + 1) at h
      have hn : (0 : Int) < Int.ofNat (n + 1) :=
        Int.natCast_pos.mpr (Nat.zero_lt_succ n)
      omega

private theorem zAdd_fromInt (x y : Z) :
    zAdd x y = zFromInt (zInt x + zInt y) := by
  cases x <;> cases y <;> rfl

private theorem zSub_fromInt (x y : Z) :
    zSub x y = zFromInt (zInt x - zInt y) := by
  cases x <;> cases y <;> rfl

private theorem zMul_fromInt (x y : Z) :
    zMul x y = zFromInt (zInt x * zInt y) := by
  cases x <;> cases y <;> rfl

private def intDivEucl (a b : Int) : Int :=
  if b = 0 then 0
  else if 0 < b then Int.ediv a b
  else
    let d := -b
    let q := Int.ediv a d
    let r := Int.emod a d
    if r = 0 then -q else -(q + 1)

private theorem zDiv_fromInt (x y : Z) :
    zDiv x y = zFromInt (intDivEucl (zInt x) (zInt y)) := by
  cases x <;> cases y <;> rfl

private theorem intDivEucl_nonneg (a b : Int) (ha : 0 <= a) (hb : 0 < b) :
    0 <= intDivEucl a b := by
  unfold intDivEucl
  rw [if_neg (Int.ne_of_gt hb), if_pos hb]
  exact Int.ediv_nonneg ha (Int.le_of_lt hb)

private theorem zDiv_nonneg (x y : Z) (hx : zLe z0 x) (hy : zGt y z0) :
    zLe z0 (zDiv x y) := by
  rw [zDiv_fromInt]
  exact zFromInt_nonneg _ (intDivEucl_nonneg _ _
    ((zLe_iff_zInt _ _).mp hx) ((zLt_iff_zInt _ _).mp hy))

private theorem zSub_nonneg (x y : Z) (h : zLe y x) : zLe z0 (zSub x y) := by
  rw [zSub_fromInt]
  exact zFromInt_nonneg _ (Int.sub_nonneg.mpr ((zLe_iff_zInt _ _).mp h))

private theorem zAdd_positive (x y : Z) (hx : zLe z0 x) (hy : zGt y z0) :
    zGt (zAdd x y) z0 := by
  rw [zAdd_fromInt]
  exact zFromInt_positive _ (Int.add_pos_of_nonneg_of_pos
    ((zLe_iff_zInt _ _).mp hx) ((zLt_iff_zInt _ _).mp hy))

private theorem zPositive_ge_one (x : Z) (h : zGt x z0) : zLe z1 x := by
  apply (zLe_iff_zInt _ _).mpr
  have hx := (zLt_iff_zInt _ _).mp h
  have hz0 : zInt z0 = 0 := rfl
  have hz1 : zInt z1 = 1 := rfl
  rw [hz0] at hx
  rw [hz1]
  cases x with
  | Z0 => omega
  | Zpos p =>
      have hp : (0 : Int) < Int.ofNat (PArith.BinPos.Pos.to_nat p) :=
        Int.natCast_pos.mpr (posToNat_positive p)
      change (1 : Int) <= Int.ofNat (PArith.BinPos.Pos.to_nat p)
      omega
  | Zneg p =>
      have hp : (0 : Int) < Int.ofNat (PArith.BinPos.Pos.to_nat p) :=
        Int.natCast_pos.mpr (posToNat_positive p)
      omega

private def zPowInt (x y : Int) : Z :=
  if y < 0 then .Z0 else zFromInt (Int.pow x y.toNat)

private theorem zPow_fromInt (x y : Z) :
    ZArith.BinInt.Z.pow x y = zPowInt (zInt x) (zInt y) := by
  cases x <;> cases y <;> rfl

private theorem zOfNat_nonneg (n : Nat) : zLe z0 (zOfNat n) := by
  cases n with
  | zero =>
      change (0 : Int) <= 0
      omega
  | succ n =>
      change zLe z0 (.Zpos (PArith.BinPos.Pos.of_nat (n + 1)))
      exact Int.le_of_lt (zPos_positive _)

private theorem zOfNat_positive (n : Nat) (h : 0 < n) : zGt (zOfNat n) z0 := by
  cases n with
  | zero => omega
  | succ n =>
      change zGt (.Zpos (PArith.BinPos.Pos.of_nat (n + 1))) z0
      exact zPos_positive _

private theorem twoPowerNat_positive (n : Nat) : zGt (two_power_nat n) z0 := by
  unfold two_power_nat ZArith.Zpower.two_power_nat
  rw [zPow_fromInt]
  unfold zPowInt
  have hn : 0 <= zInt (zOfNat n) :=
    (zLe_iff_zInt _ _).mp (zOfNat_nonneg n)
  have hnot : Not (zInt (ZArith.BinInt.Z.of_nat n) < 0) := by
    change Not (zInt (zOfNat n) < 0)
    omega
  rw [if_neg hnot]
  apply zFromInt_positive
  apply Int.pow_pos
  change (0 : Int) < 2
  omega

private theorem alignAttrPositive (a : attr) (al : Z) (hal : zGt al z0) :
    zGt (align_attr a al) z0 := by
  cases a with
  | mk volatile alignas =>
      cases alignas with
      | none => exact hal
      | some n => exact twoPowerNat_positive _

private theorem alignof_positive (env : composite_env) :
    forall t : type, zGt (alignof env t) z0
  | .Tvoid => alignAttrPositive noattr _ (zOfNat_positive 1 (by omega))
  | .Tint sz _ a => by
      cases sz with
      | I8 | IBool => exact alignAttrPositive a _ (zOfNat_positive 1 (by omega))
      | I16 => exact alignAttrPositive a _ (zOfNat_positive 2 (by omega))
      | I32 => exact alignAttrPositive a _ (zOfNat_positive 4 (by omega))
  | .Tlong _ a => alignAttrPositive a _ (zPos_positive _)
  | .Tfloat sz a => by
      cases sz with
      | F32 => exact alignAttrPositive a _ (zOfNat_positive 4 (by omega))
      | F64 => exact alignAttrPositive a _ (zPos_positive _)
  | .Tpointer _ a => by
      apply alignAttrPositive
      simp only [CompCert4Lean.X86_64.Archi.ptr64, if_true]
      exact zOfNat_positive 8 (by omega)
  | .Tarray t _ a => alignAttrPositive a _ (alignof_positive env t)
  | .Tfunction _ _ _ => alignAttrPositive noattr _ (zOfNat_positive 1 (by omega))
  | .Tstruct id a => by
      simp only [alignof]
      cases h : PTree.get id env with
      | none => exact alignAttrPositive a _ (zOfNat_positive 1 (by omega))
      | some co =>
          apply alignAttrPositive
          simp only
          rcases co.co_alignof_two_p with ⟨n, hn⟩
          rw [hn]
          exact twoPowerNat_positive n
  | .Tunion id a => by
      simp only [alignof]
      cases h : PTree.get id env with
      | none => exact alignAttrPositive a _ (zOfNat_positive 1 (by omega))
      | some co =>
          apply alignAttrPositive
          simp only
          rcases co.co_alignof_two_p with ⟨n, hn⟩
          rw [hn]
          exact twoPowerNat_positive n

private theorem zMul_nonneg (x y : Z) (hx : zLe z0 x) (hy : zLe z0 y) :
    zLe z0 (zMul x y) := by
  rw [zMul_fromInt]
  exact zFromInt_nonneg _ (Int.mul_nonneg
    ((zLe_iff_zInt _ _).mp hx) ((zLe_iff_zInt _ _).mp hy))

private theorem zAdd_nonneg (x y : Z) (hx : zLe z0 x) (hy : zLe z0 y) :
    zLe z0 (zAdd x y) := by
  rw [zAdd_fromInt]
  exact zFromInt_nonneg _ (Int.add_nonneg
    ((zLe_iff_zInt _ _).mp hx) ((zLe_iff_zInt _ _).mp hy))

private theorem zMul_positive (x y : Z) (hx : zGt x z0) (hy : zGt y z0) :
    zGt (zMul x y) z0 := by
  rw [zMul_fromInt]
  exact zFromInt_positive _ (Int.mul_pos
    ((zLt_iff_zInt _ _).mp hx) ((zLt_iff_zInt _ _).mp hy))

private theorem alignNonnegative (n amount : Z) (hn : zLe z0 n)
    (ha : zGt amount z0) : zLe z0 (align n amount) := by
  simp only [align, CompCert4Lean.Lib.Coqlib.align]
  apply zMul_nonneg
  · apply zDiv_nonneg
    · apply zSub_nonneg
      exact zPositive_ge_one _ (zAdd_positive _ _ hn ha)
    · exact ha
  · exact Int.le_of_lt ha

private theorem floorNonnegative (n amount : Z) (hn : zLe z0 n)
    (ha : zGt amount z0) : zLe z0 (floor n amount) := by
  simp only [floor, CompCert4Lean.Lib.Coqlib.floor]
  exact zMul_nonneg _ _ (zDiv_nonneg _ _ hn ha) (Int.le_of_lt ha)

private theorem zMax_nonneg_right (x y : Z) (hy : zLe z0 y) : zLe z0 (zMax x y) := by
  unfold zLe zMax ZArith.BinInt.Z.le ZArith.BinInt.Z.max at *
  split <;> omega

private theorem zMax_nonneg_left (x y : Z) (hx : zLe z0 x) : zLe z0 (zMax x y) := by
  unfold zLe zMax ZArith.BinInt.Z.le ZArith.BinInt.Z.max at *
  split <;> omega

private theorem sizeof_nonneg (env : composite_env) :
    forall t : type, zLe z0 (sizeof env t)
  | .Tvoid => zOfNat_nonneg 1
  | .Tint sz _ _ => by cases sz <;> exact zOfNat_nonneg _
  | .Tlong _ _ => zOfNat_nonneg 8
  | .Tfloat sz _ => by cases sz <;> exact zOfNat_nonneg _
  | .Tpointer _ _ => by
      simp only [sizeof]
      split <;> exact zOfNat_nonneg _
  | .Tarray t n _ => by
      have ih := sizeof_nonneg env t
      simp only [sizeof]
      apply zMul_nonneg _ _ ih
      exact zMax_nonneg_left _ _ (zOfNat_nonneg 0)
  | .Tfunction _ _ _ => zOfNat_nonneg 1
  | .Tstruct id _ => by
      simp only [sizeof]
      cases h : PTree.get id env with
      | none => exact zOfNat_nonneg 0
      | some co => exact co.co_sizeof_pos
  | .Tunion id _ => by
      simp only [sizeof]
      cases h : PTree.get id env with
      | none => exact zOfNat_nonneg 0
      | some co => exact co.co_sizeof_pos

private theorem sizeof_union_nonneg (env : composite_env) (ms : members) :
    zLe z0 (sizeof_union env ms) := by
  induction ms with
  | nil => exact zOfNat_nonneg 0
  | cons m ms ih =>
      simp only [sizeof_union]
      exact zMax_nonneg_right _ _ ih

private theorem bitsizeof_nonneg (env : composite_env) (t : type) :
    zLe z0 (bitsizeof env t) := by
  simp only [bitsizeof]
  exact zMul_nonneg _ _ (sizeof_nonneg env t) (zOfNat_nonneg 8)

private theorem bitalignof_positive (env : composite_env) (t : type) :
    zGt (bitalignof env t) z0 := by
  simp only [bitalignof]
  exact zMul_positive _ _ (alignof_positive env t) (zOfNat_positive 8 (by omega))

private theorem bitalignof_intsize_positive (sz : intsize) :
    zGt (bitalignof_intsize sz) z0 := by
  cases sz <;> exact zOfNat_positive _ (by omega)

private theorem nextFieldNonnegative (env : composite_env) (pos : Z) (m : member)
    (hpos : zLe z0 pos) : zLe z0 (next_field env pos m) := by
  cases m with
  | Member_plain id t =>
      simp only [next_field]
      exact zAdd_nonneg _ _
        (alignNonnegative _ _ hpos (bitalignof_positive env t))
        (bitsizeof_nonneg env t)
  | Member_bitfield id sz sg a width padding =>
      simp only [next_field]
      cases hwidth : CompCert4Lean.Lib.Coqlib.zle width z0 with
      | left hw =>
          simp only [hwidth]
          exact alignNonnegative _ _ hpos (bitalignof_intsize_positive sz)
      | right hw =>
          simp only [hwidth]
          let s := bitalignof_intsize sz
          let current := floor pos s
          let next := zAdd current s
          have hs : zGt s z0 := bitalignof_intsize_positive sz
          have hwidth_nonneg : zLe z0 width := Int.le_of_lt hw
          have hcurrent : zLe z0 current := floorNonnegative _ _ hpos hs
          have hnext : zLe z0 next := zAdd_nonneg _ _ hcurrent (Int.le_of_lt hs)
          cases hfit : CompCert4Lean.Lib.Coqlib.zle (zAdd pos width) next with
          | left hle =>
              simp only [hfit]
              exact zAdd_nonneg _ _ hpos hwidth_nonneg
          | right hgt =>
              simp only [hfit]
              exact zAdd_nonneg _ _ hnext hwidth_nonneg

private theorem bitsizeofStructNonnegative (env : composite_env) :
    forall (ms : members) (current : Z), zLe z0 current ->
      zLe z0 (bitsizeof_struct env current ms)
  | [], current, hcurrent => hcurrent
  | m :: ms, current, hcurrent => by
      simp only [bitsizeof_struct]
      exact bitsizeofStructNonnegative env ms (next_field env current m)
        (nextFieldNonnegative env current m hcurrent)

private theorem sizeof_struct_nonneg (env : composite_env) (ms : members) :
    zLe z0 (sizeof_struct env ms) := by
  simp only [sizeof_struct, bytes_of_bits]
  apply zDiv_nonneg
  · exact zAdd_nonneg _ _
      (bitsizeofStructNonnegative env ms z0 (zOfNat_nonneg 0))
      (zOfNat_nonneg 7)
  · exact zOfNat_positive 8 (by omega)

private theorem sizeof_composite_nonneg (env : composite_env) (su : struct_or_union)
    (ms : members) : zLe z0 (sizeof_composite env su ms) := by
  cases su with
  | Struct => exact sizeof_struct_nonneg env ms
  | Union => exact sizeof_union_nonneg env ms

private theorem zMax_positive_right (x y : Z) (hy : zGt y z0) :
    zGt (zMax x y) z0 := by
  unfold zMax ZArith.BinInt.Z.max
  split
  · exact hy
  · exact Int.lt_trans hy (Int.lt_of_not_ge (by assumption))

private theorem alignof_composite_positive (env : composite_env) :
    forall ms : members, zGt (alignof_composite env ms) z0
  | [] => by
      simp only [alignof_composite]
      change zGt (.Zpos (PArith.BinPos.Pos.of_nat 1)) z0
      exact zPos_positive _
  | m :: ms => by
      have ih := alignof_composite_positive env ms
      simp only [alignof_composite]
      split
      · exact ih
      · exact zMax_positive_right _ _ ih

private theorem alignAttrTwoPower (a : attr) (al : Z)
    (h : Exists fun n : Nat => al = two_power_nat n) :
    Exists fun n : Nat => align_attr a al = two_power_nat n := by
  cases a with
  | mk volatile alignas =>
      cases alignas with
      | none => exact h
      | some n => exact Exists.intro (NArith.BinNat.N.to_nat n) rfl

private theorem alignofTwoPower (env : composite_env) :
    forall t : type, Exists fun n : Nat => alignof env t = two_power_nat n
  | .Tvoid => alignAttrTwoPower noattr _ (Exists.intro 0 rfl)
  | .Tint sz _ a => by
      cases sz with
      | I8 | IBool => exact alignAttrTwoPower a _ (Exists.intro 0 rfl)
      | I16 => exact alignAttrTwoPower a _ (Exists.intro 1 rfl)
      | I32 => exact alignAttrTwoPower a _ (Exists.intro 2 rfl)
  | .Tlong _ a => alignAttrTwoPower a _ (Exists.intro 3 rfl)
  | .Tfloat sz a => by
      cases sz with
      | F32 => exact alignAttrTwoPower a _ (Exists.intro 2 rfl)
      | F64 => exact alignAttrTwoPower a _ (Exists.intro 3 rfl)
  | .Tpointer _ a => alignAttrTwoPower a _ (Exists.intro 3 rfl)
  | .Tarray t _ a => alignAttrTwoPower a _ (alignofTwoPower env t)
  | .Tfunction _ _ _ => alignAttrTwoPower noattr _ (Exists.intro 0 rfl)
  | .Tstruct id a => by
      cases h : PTree.get id env with
      | none =>
          simp only [alignof, h]
          exact alignAttrTwoPower a _ (Exists.intro 0 rfl)
      | some co =>
          simp only [alignof, h]
          exact alignAttrTwoPower a _ co.co_alignof_two_p
  | .Tunion id a => by
      cases h : PTree.get id env with
      | none =>
          simp only [alignof, h]
          exact alignAttrTwoPower a _ (Exists.intro 0 rfl)
      | some co =>
          simp only [alignof, h]
          exact alignAttrTwoPower a _ co.co_alignof_two_p

private theorem alignofCompositeTwoPower (env : composite_env) :
    forall ms : members, Exists fun n : Nat => alignof_composite env ms = two_power_nat n
  | [] => Exists.intro 0 rfl
  | m :: ms => by
      simp only [alignof_composite]
      split
      · exact alignofCompositeTwoPower env ms
      · rcases alignofCompositeTwoPower env ms with ⟨n, hn⟩
        rcases alignofTwoPower env (type_member m) with ⟨k, hk⟩
        rw [hk, hn]
        unfold zMax ZArith.BinInt.Z.max
        split
        · exact Exists.intro n rfl
        · exact Exists.intro k rfl

private theorem align_nonneg (n amount : Z) (hn : zLe z0 n) (ha : zGt amount z0) :
    zLe z0 (align n amount) := by
  exact alignNonnegative n amount hn ha

private theorem align_divisible (n amount : Z) : zDivide amount (align n amount) := by
  unfold zDivide align CompCert4Lean.Lib.Coqlib.align ZArith.BinInt.Z.divide
  refine Exists.intro (zDiv (zSub (zAdd n amount) z1) amount) ?_
  simp [ZArith.BinInt.Z.mul, Int.mul_comm]

def composite_of_def (env : composite_env) (id : ident) (su : struct_or_union)
    (ms : members) (a : attr) : Errors.res composite :=
  match hget : PTree.get id env with
  | some _ => .Error (Errors.MSG duplicateCompositeText :: Errors.CTX id :: [])
  | none =>
      match hcomplete : complete_members env ms with
      | false => .Error (Errors.MSG incompleteCompositeText :: Errors.CTX id :: [])
      | true =>
          let al := align_attr a (alignof_composite env ms)
          let sz := align (sizeof_composite env su ms) al
          .OK
            { co_su := su
              co_members := ms
              co_attr := a
              co_sizeof := sz
              co_alignof := al
              co_rank := rank_members env ms
              co_sizeof_pos := align_nonneg _ _ (sizeof_composite_nonneg env su ms)
                (alignAttrPositive a _ (alignof_composite_positive env ms))
              co_alignof_two_p := alignAttrTwoPower a _ (alignofCompositeTwoPower env ms)
              co_sizeof_alignof := align_divisible _ _ }

def add_composite_definitions (env : composite_env) :
    List composite_definition -> Errors.res composite_env
  | [] => .OK env
  | .Composite id su ms a :: defs =>
      match composite_of_def env id su ms a with
      | .Error msg => .Error msg
      | .OK co => add_composite_definitions (PTree.set id co env) defs

def build_composite_env (defs : List composite_definition) : Errors.res composite_env :=
  add_composite_definitions (PTree.empty composite) defs

/-! ## Stability and consistency statement surface -/

def alignof_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall t, complete_type env t = true -> alignof env' t = alignof env t

def sizeof_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall t, complete_type env t = true -> sizeof env' t = sizeof env t

def complete_type_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall t, complete_type env t = true -> complete_type env' t = true

def rank_type_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall t, complete_type env t = true -> rank_type env' t = rank_type env t

def alignof_composite_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall ms, complete_members env ms = true ->
      alignof_composite env' ms = alignof_composite env ms

def next_field_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall pos m, complete_type env (type_member m) = true ->
      next_field env' pos m = next_field env pos m

def bitsizeof_struct_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall ms pos, complete_members env ms = true ->
      bitsizeof_struct env' pos ms = bitsizeof_struct env pos ms

def sizeof_union_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall ms, complete_members env ms = true -> sizeof_union env' ms = sizeof_union env ms

def sizeof_composite_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall su ms, complete_members env ms = true ->
      sizeof_composite env' su ms = sizeof_composite env su ms

def complete_members_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall ms, complete_members env ms = true -> complete_members env' ms = true

def rank_members_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall ms, complete_members env ms = true -> rank_members env' ms = rank_members env ms

def layout_field_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall pos m, complete_type env (type_member m) = true ->
      layout_field env' pos m = layout_field env pos m

def field_offset_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall f ms, complete_members env ms = true ->
      field_offset env' f ms = field_offset env f ms

def union_field_offset_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall f ms, complete_members env ms = true ->
      union_field_offset env' f ms = union_field_offset env f ms

structure composite_consistent (env : composite_env) (co : composite) : Prop where
  co_consistent_complete : complete_members env co.co_members = true
  co_consistent_alignof :
    co.co_alignof = align_attr co.co_attr (alignof_composite env co.co_members)
  co_consistent_sizeof :
    co.co_sizeof = align (sizeof_composite env co.co_su co.co_members) co.co_alignof
  co_consistent_rank : co.co_rank = rank_members env co.co_members

def Build_composite_consistent (env : composite_env) (co : composite)
    (h_complete : complete_members env co.co_members = true)
    (h_alignof : co.co_alignof = align_attr co.co_attr (alignof_composite env co.co_members))
    (h_sizeof : co.co_sizeof = align (sizeof_composite env co.co_su co.co_members) co.co_alignof)
    (h_rank : co.co_rank = rank_members env co.co_members) : composite_consistent env co :=
  { co_consistent_complete := h_complete
    co_consistent_alignof := h_alignof
    co_consistent_sizeof := h_sizeof
    co_consistent_rank := h_rank }

def co_consistent_complete (env : composite_env) (co : composite)
    (h : composite_consistent env co) : complete_members env co.co_members = true :=
  h.co_consistent_complete

def co_consistent_alignof (env : composite_env) (co : composite)
    (h : composite_consistent env co) :
    co.co_alignof = align_attr co.co_attr (alignof_composite env co.co_members) :=
  h.co_consistent_alignof

def co_consistent_sizeof (env : composite_env) (co : composite)
    (h : composite_consistent env co) :
    co.co_sizeof = align (sizeof_composite env co.co_su co.co_members) co.co_alignof :=
  h.co_consistent_sizeof

def co_consistent_rank (env : composite_env) (co : composite)
    (h : composite_consistent env co) :
    co.co_rank = rank_members env co.co_members := h.co_consistent_rank

def composite_env_consistent (env : composite_env) : Prop :=
  forall id co, PTree.get id env = some co -> composite_consistent env co

def composite_consistent_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall co, composite_consistent env co -> composite_consistent env' co

def composite_of_def_consistentStatement : Prop :=
  forall env id su ms a co,
    composite_of_def env id su ms a = .OK co -> composite_consistent env co

def build_composite_env_consistentStatement : Prop :=
  forall defs env,
    build_composite_env defs = .OK env -> composite_env_consistent env

/-! ## Programs and compilation units -/

inductive fundef (F : Type) : Type where
  | Internal (f : F)
  | External (ef : external_function) (args : List type) (result : type)
      (cc : calling_convention)

export fundef (Internal External)

structure program (F : Type) : Type where
  prog_defs : List (ident × AST.globdef (fundef F) type)
  prog_public : List ident
  prog_main : ident
  prog_types : List composite_definition
  prog_comp_env : composite_env
  prog_comp_env_eq : build_composite_env prog_types = .OK prog_comp_env

export program (prog_defs prog_public prog_main prog_types prog_comp_env prog_comp_env_eq)

def program_of_program {F : Type} (p : program F) : AST.program (fundef F) type :=
  { prog_defs := p.prog_defs, prog_public := p.prog_public, prog_main := p.prog_main }

/-! ## Separate compilation and linking -/

private noncomputable instance typeDecidableEq : DecidableEq type :=
  Classical.typeDecidableEq type

noncomputable instance Linker_types : CompCert4Lean.Common.Linking.Linker type where
  link := fun t1 t2 => if t1 = t2 then some t1 else none
  linkorder := Eq
  linkorder_refl := fun _ => rfl
  linkorder_trans := by
    intro x y z hxy hyz
    exact hxy.trans hyz
  link_linkorder := by
    intro x y z h
    by_cases hxy : x = y
    · subst y
      simp only [↓reduceIte] at h
      cases h
      exact ⟨rfl, rfl⟩
    · simp only [hxy, ↓reduceIte] at h
      cases h

noncomputable def link_fundef {F : Type} (fd1 fd2 : fundef F) : Option (fundef F) :=
  match fd1, fd2 with
  | .Internal _, .Internal _ => none
  | .External ef1 args1 result1 cc1, .External ef2 args2 result2 cc2 =>
      if ef1 = ef2 ∧ args1 = args2 ∧ result1 = result2 ∧ cc1 = cc2 then
        some (.External ef1 args1 result1 cc1)
      else
        none
  | .Internal f, .External (.EF_external _ _) _ _ _ => some (.Internal f)
  | .External (.EF_external _ _) _ _ _, .Internal f => some (.Internal f)
  | _, _ => none

inductive linkorder_fundef {F : Type} : fundef F → fundef F → Prop where
  | linkorder_fundef_refl (fd : fundef F) : linkorder_fundef fd fd
  | linkorder_fundef_ext_int (f : F) (id : RocqString) (sg : signature)
      (args : List type) (result : type) (cc : calling_convention) :
      linkorder_fundef (.External (.EF_external id sg) args result cc) (.Internal f)

export linkorder_fundef (linkorder_fundef_refl linkorder_fundef_ext_int)

noncomputable instance Linker_fundef (F : Type) :
    CompCert4Lean.Common.Linking.Linker (fundef F) where
  link := link_fundef
  linkorder := linkorder_fundef
  linkorder_refl := linkorder_fundef.linkorder_fundef_refl
  linkorder_trans := by
    intro x y z hxy hyz
    cases hxy <;> cases hyz <;> constructor
  link_linkorder := by
    intro x y z h
    cases x with
    | Internal f1 =>
        cases y with
        | Internal f2 => simp [link_fundef] at h
        | External ef args result cc =>
            cases ef <;> simp [link_fundef] at h
            case EF_external id sg =>
              subst z
              exact ⟨linkorder_fundef.linkorder_fundef_refl _,
                linkorder_fundef.linkorder_fundef_ext_int f1 id sg args result cc⟩
    | External ef1 args1 result1 cc1 =>
        cases y with
        | Internal f2 =>
            cases ef1 <;> simp [link_fundef] at h
            case EF_external id sg =>
              subst z
              exact ⟨linkorder_fundef.linkorder_fundef_ext_int f2 id sg args1 result1 cc1,
                linkorder_fundef.linkorder_fundef_refl _⟩
        | External ef2 args2 result2 cc2 =>
            by_cases heq : ef1 = ef2 ∧ args1 = args2 ∧ result1 = result2 ∧ cc1 = cc2
            · rcases heq with ⟨hef, hargs, hresult, hcc⟩
              subst ef2
              subst args2
              subst result2
              subst cc2
              simp only [link_fundef, and_self, if_true] at h
              cases Option.some.inj h
              exact ⟨linkorder_fundef.linkorder_fundef_refl _,
                linkorder_fundef.linkorder_fundef_refl _⟩
            · simp only [link_fundef, heq, ↓reduceIte] at h
              cases h

def linkorder_program {F : Type} (p1 p2 : program F) : Prop :=
  CompCert4Lean.Common.Linking.linkorder
      (program_of_program p1) (program_of_program p2) ∧
    ∀ id co, PTree.get id p1.prog_comp_env = some co →
      PTree.get id p2.prog_comp_env = some co

end CompCert4Lean.Cfrontend.Ctypes
