import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Values
import CompCert4Lean.Common.Memory
import CompCert4Lean.Cfrontend.Ctypes
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Floats
import CompCert4Lean.X86_64.Archi

/-!
# Arithmetic and logical operators

Definition-bearing translation of CompCert's `cfrontend/Cop.v`.  Later proof
obligations are represented by exact proposition descriptors.
-/

namespace CompCert4Lean.Cfrontend.Cop

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Floats

private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev CCInt64 := CompCert4Lean.Lib.Integers.int64
private abbrev Ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev CCFloat := CompCert4Lean.Lib.Floats.float
private abbrev CCFloat32 := CompCert4Lean.Lib.Floats.float32
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev block := CompCert4Lean.Common.Values.block
private abbrev mem := CompCert4Lean.Common.Memory.Mem.mem
private abbrev meminj := CompCert4Lean.Common.Values.Val.meminj
private abbrev ident := CompCert4Lean.Common.AST.ident

private abbrev z0 : Z := .Z0
private abbrev z1 : Z := .Zpos .xH
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zMul := ZArith.BinInt.Z.mul
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zGt := ZArith.BinInt.Z.gt
private abbrev comparison := CompCert4Lean.Lib.Integers.comparison
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate

private def zltBool (x y : Z) : Bool :=
  match zlt x y with
  | .left _ => true
  | .right _ => false

private def zleBool (x y : Z) : Bool :=
  match zle x y with
  | .left _ => true
  | .right _ => false

namespace Int
private abbrev repr := CompCert4Lean.Lib.Integers.Int.repr
private abbrev unsigned := CompCert4Lean.Lib.Integers.Int.unsigned
private abbrev signed := CompCert4Lean.Lib.Integers.Int.signed
private abbrev zero := CompCert4Lean.Lib.Integers.Int.zero
private abbrev one := CompCert4Lean.Lib.Integers.Int.one
private abbrev mone := CompCert4Lean.Lib.Integers.Int.mone
private abbrev min_signed := CompCert4Lean.Lib.Integers.Int.min_signed
private abbrev iwordsize := CompCert4Lean.Lib.Integers.Int.iwordsize
private abbrev eq := CompCert4Lean.Lib.Integers.Int.eq
private abbrev lt := CompCert4Lean.Lib.Integers.Int.lt
private abbrev ltu := CompCert4Lean.Lib.Integers.Int.ltu
private abbrev neg := CompCert4Lean.Lib.Integers.Int.neg
private abbrev add := CompCert4Lean.Lib.Integers.Int.add
private abbrev sub := CompCert4Lean.Lib.Integers.Int.sub
private abbrev mul := CompCert4Lean.Lib.Integers.Int.mul
private abbrev divs := CompCert4Lean.Lib.Integers.Int.divs
private abbrev divu := CompCert4Lean.Lib.Integers.Int.divu
private abbrev and := CompCert4Lean.Lib.Integers.Int.and
private abbrev or := CompCert4Lean.Lib.Integers.Int.or
private abbrev xor := CompCert4Lean.Lib.Integers.Int.xor
private abbrev not := CompCert4Lean.Lib.Integers.Int.not
private abbrev shl := CompCert4Lean.Lib.Integers.Int.shl
private abbrev shru := CompCert4Lean.Lib.Integers.Int.shru
private abbrev shr := CompCert4Lean.Lib.Integers.Int.shr
private abbrev zero_ext := CompCert4Lean.Lib.Integers.Int.zero_ext
private abbrev sign_ext := CompCert4Lean.Lib.Integers.Int.sign_ext
end Int

namespace Int64
private abbrev repr := CompCert4Lean.Lib.Integers.Int64.repr
private abbrev unsigned := CompCert4Lean.Lib.Integers.Int64.unsigned
private abbrev zero := CompCert4Lean.Lib.Integers.Int64.zero
private abbrev one := CompCert4Lean.Lib.Integers.Int64.one
private abbrev mone := CompCert4Lean.Lib.Integers.Int64.mone
private abbrev min_signed := CompCert4Lean.Lib.Integers.Int64.min_signed
private abbrev iwordsize := CompCert4Lean.Lib.Integers.Int64.iwordsize
private abbrev iwordsize' := CompCert4Lean.Lib.Integers.Int64.iwordsize'
private abbrev eq := CompCert4Lean.Lib.Integers.Int64.eq
private abbrev lt := CompCert4Lean.Lib.Integers.Int64.lt
private abbrev ltu := CompCert4Lean.Lib.Integers.Int64.ltu
private abbrev neg := CompCert4Lean.Lib.Integers.Int64.neg
private abbrev add := CompCert4Lean.Lib.Integers.Int64.add
private abbrev sub := CompCert4Lean.Lib.Integers.Int64.sub
private abbrev mul := CompCert4Lean.Lib.Integers.Int64.mul
private abbrev divs := CompCert4Lean.Lib.Integers.Int64.divs
private abbrev divu := CompCert4Lean.Lib.Integers.Int64.divu
private abbrev and := CompCert4Lean.Lib.Integers.Int64.and
private abbrev or := CompCert4Lean.Lib.Integers.Int64.or
private abbrev xor := CompCert4Lean.Lib.Integers.Int64.xor
private abbrev not := CompCert4Lean.Lib.Integers.Int64.not
private abbrev shl := CompCert4Lean.Lib.Integers.Int64.shl
private abbrev shru := CompCert4Lean.Lib.Integers.Int64.shru
private abbrev shr := CompCert4Lean.Lib.Integers.Int64.shr
private abbrev loword := CompCert4Lean.Lib.Integers.Int64.loword
end Int64

namespace Float
private abbrev zero := CompCert4Lean.Lib.Floats.Float.zero
private abbrev neg := CompCert4Lean.Lib.Floats.Float.neg
private abbrev abs := CompCert4Lean.Lib.Floats.Float.abs
private abbrev add := CompCert4Lean.Lib.Floats.Float.add
private abbrev sub := CompCert4Lean.Lib.Floats.Float.sub
private abbrev mul := CompCert4Lean.Lib.Floats.Float.mul
private abbrev div := CompCert4Lean.Lib.Floats.Float.div
private abbrev cmp := CompCert4Lean.Lib.Floats.Float.cmp
private abbrev of_int := CompCert4Lean.Lib.Floats.Float.of_int
private abbrev of_intu := CompCert4Lean.Lib.Floats.Float.of_intu
private abbrev of_long := CompCert4Lean.Lib.Floats.Float.of_long
private abbrev of_longu := CompCert4Lean.Lib.Floats.Float.of_longu
private abbrev to_int := CompCert4Lean.Lib.Floats.Float.to_int
private abbrev to_intu := CompCert4Lean.Lib.Floats.Float.to_intu
private abbrev to_long := CompCert4Lean.Lib.Floats.Float.to_long
private abbrev to_longu := CompCert4Lean.Lib.Floats.Float.to_longu
private abbrev of_single := CompCert4Lean.Lib.Floats.Float.of_single
private abbrev to_single := CompCert4Lean.Lib.Floats.Float.to_single
end Float

namespace Float32
private abbrev zero := CompCert4Lean.Lib.Floats.Float32.zero
private abbrev neg := CompCert4Lean.Lib.Floats.Float32.neg
private abbrev abs := CompCert4Lean.Lib.Floats.Float32.abs
private abbrev add := CompCert4Lean.Lib.Floats.Float32.add
private abbrev sub := CompCert4Lean.Lib.Floats.Float32.sub
private abbrev mul := CompCert4Lean.Lib.Floats.Float32.mul
private abbrev div := CompCert4Lean.Lib.Floats.Float32.div
private abbrev cmp := CompCert4Lean.Lib.Floats.Float32.cmp
private abbrev of_int := CompCert4Lean.Lib.Floats.Float32.of_int
private abbrev of_intu := CompCert4Lean.Lib.Floats.Float32.of_intu
private abbrev of_long := CompCert4Lean.Lib.Floats.Float32.of_long
private abbrev of_longu := CompCert4Lean.Lib.Floats.Float32.of_longu
private abbrev to_int := CompCert4Lean.Lib.Floats.Float32.to_int
private abbrev to_intu := CompCert4Lean.Lib.Floats.Float32.to_intu
private abbrev to_long := CompCert4Lean.Lib.Floats.Float32.to_long
private abbrev to_longu := CompCert4Lean.Lib.Floats.Float32.to_longu
end Float32

private abbrev boolEqInt : CCInt → CCInt → Bool := Int.eq
private abbrev boolEqInt64 : CCInt64 → CCInt64 → Bool := Int64.eq
private abbrev intsizeEq (x y : intsize) : Bool := decide (x = y)
private abbrev signednessEq (x y : signedness) : Bool := decide (x = y)
private abbrev identEq (x y : ident) : Bool := decide (x = y)

/-! ## Syntax of operators -/

inductive unary_operation : Type where
  | Onotbool
  | Onotint
  | Oneg
  | Oabsfloat

export unary_operation (Onotbool Onotint Oneg Oabsfloat)

inductive binary_operation : Type where
  | Oadd
  | Osub
  | Omul
  | Odiv
  | Omod
  | Oand
  | Oor
  | Oxor
  | Oshl
  | Oshr
  | Oeq
  | One
  | Olt
  | Ogt
  | Ole
  | Oge

export binary_operation (Oadd Osub Omul Odiv Omod Oand Oor Oxor Oshl Oshr Oeq One Olt Ogt Ole Oge)

inductive incr_or_decr : Type where
  | Incr
  | Decr

export incr_or_decr (Incr Decr)

/-! ## Casts and truth values -/

inductive classify_cast_cases : Type where
  | cast_case_pointer
  | cast_case_i2i (sz2 : intsize) (si2 : signedness)
  | cast_case_f2f
  | cast_case_s2s
  | cast_case_f2s
  | cast_case_s2f
  | cast_case_i2f (si1 : signedness)
  | cast_case_i2s (si1 : signedness)
  | cast_case_f2i (sz2 : intsize) (si2 : signedness)
  | cast_case_s2i (sz2 : intsize) (si2 : signedness)
  | cast_case_l2l
  | cast_case_i2l (si1 : signedness)
  | cast_case_l2i (sz2 : intsize) (si2 : signedness)
  | cast_case_l2f (si1 : signedness)
  | cast_case_l2s (si1 : signedness)
  | cast_case_f2l (si2 : signedness)
  | cast_case_s2l (si2 : signedness)
  | cast_case_i2bool
  | cast_case_l2bool
  | cast_case_f2bool
  | cast_case_s2bool
  | cast_case_struct (id1 id2 : ident)
  | cast_case_union (id1 id2 : ident)
  | cast_case_void
  | cast_case_default

export classify_cast_cases (cast_case_pointer cast_case_i2i cast_case_f2f cast_case_s2s
  cast_case_f2s cast_case_s2f cast_case_i2f cast_case_i2s cast_case_f2i cast_case_s2i
  cast_case_l2l cast_case_i2l cast_case_l2i cast_case_l2f cast_case_l2s cast_case_f2l
  cast_case_s2l cast_case_i2bool cast_case_l2bool cast_case_f2bool cast_case_s2bool
  cast_case_struct cast_case_union cast_case_void cast_case_default)

def classify_cast (tfrom tto : type) : classify_cast_cases :=
  match tto, tfrom with
  | .Tvoid, _ => .cast_case_void
  | .Tint sz2 si2 _, .Tint _ _ _ =>
      match sz2 with
      | .IBool => .cast_case_i2bool
      | .I32 => if CompCert4Lean.X86_64.Archi.ptr64 then .cast_case_i2i sz2 si2 else .cast_case_pointer
      | _ => .cast_case_i2i sz2 si2
  | .Tint sz2 si2 _, .Tlong _ _ =>
      if intsizeEq sz2 .IBool then .cast_case_l2bool else .cast_case_l2i sz2 si2
  | .Tint sz2 si2 _, .Tfloat .F64 _ =>
      if intsizeEq sz2 .IBool then .cast_case_f2bool else .cast_case_f2i sz2 si2
  | .Tint sz2 si2 _, .Tfloat .F32 _ =>
      if intsizeEq sz2 .IBool then .cast_case_s2bool else .cast_case_s2i sz2 si2
  | .Tint sz2 si2 _, .Tpointer _ _
  | .Tint sz2 si2 _, .Tarray _ _ _
  | .Tint sz2 si2 _, .Tfunction _ _ _ =>
      if CompCert4Lean.X86_64.Archi.ptr64 then
        if intsizeEq sz2 .IBool then .cast_case_l2bool else .cast_case_l2i sz2 si2
      else
        match sz2 with
        | .IBool => .cast_case_i2bool
        | .I32 => .cast_case_pointer
        | _ => .cast_case_i2i sz2 si2
  | .Tlong _ _, .Tlong _ _ =>
      if CompCert4Lean.X86_64.Archi.ptr64 then .cast_case_pointer else .cast_case_l2l
  | .Tlong _ _, .Tint _ si1 _ => .cast_case_i2l si1
  | .Tlong si2 _, .Tfloat .F64 _ => .cast_case_f2l si2
  | .Tlong si2 _, .Tfloat .F32 _ => .cast_case_s2l si2
  | .Tlong si2 _, .Tpointer _ _
  | .Tlong si2 _, .Tarray _ _ _
  | .Tlong si2 _, .Tfunction _ _ _ =>
      if CompCert4Lean.X86_64.Archi.ptr64 then .cast_case_pointer else .cast_case_i2l si2
  | .Tfloat .F64 _, .Tint _ si1 _ => .cast_case_i2f si1
  | .Tfloat .F32 _, .Tint _ si1 _ => .cast_case_i2s si1
  | .Tfloat .F64 _, .Tlong si1 _ => .cast_case_l2f si1
  | .Tfloat .F32 _, .Tlong si1 _ => .cast_case_l2s si1
  | .Tfloat .F64 _, .Tfloat .F64 _ => .cast_case_f2f
  | .Tfloat .F32 _, .Tfloat .F32 _ => .cast_case_s2s
  | .Tfloat .F64 _, .Tfloat .F32 _ => .cast_case_s2f
  | .Tfloat .F32 _, .Tfloat .F64 _ => .cast_case_f2s
  | .Tpointer _ _, .Tint _ si _ =>
      if CompCert4Lean.X86_64.Archi.ptr64 then .cast_case_i2l si else .cast_case_pointer
  | .Tpointer _ _, .Tlong _ _ =>
      if CompCert4Lean.X86_64.Archi.ptr64 then .cast_case_pointer else .cast_case_l2i .I32 .Unsigned
  | .Tpointer _ _, .Tpointer _ _
  | .Tpointer _ _, .Tarray _ _ _
  | .Tpointer _ _, .Tfunction _ _ _ => .cast_case_pointer
  | .Tstruct id2 _, .Tstruct id1 _ => .cast_case_struct id1 id2
  | .Tunion id2 _, .Tunion id1 _ => .cast_case_union id1 id2
  | _, _ => .cast_case_default

def cast_int_int (sz : intsize) (sg : signedness) (i : CCInt) : CCInt :=
  match sz, sg with
  | .I8, .Signed => Int.sign_ext (zOfNat 8) i
  | .I8, .Unsigned => Int.zero_ext (zOfNat 8) i
  | .I16, .Signed => Int.sign_ext (zOfNat 16) i
  | .I16, .Unsigned => Int.zero_ext (zOfNat 16) i
  | .I32, _ => i
  | .IBool, _ => if boolEqInt i Int.zero then Int.zero else Int.one

def cast_int_float
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    (si : signedness) (i : CCInt) : CCFloat :=
  match si with
  | .Signed => Float.of_int (certificate := binary64_certificate) i
  | .Unsigned => Float.of_intu (certificate := binary64_certificate) i

def cast_float_int (si : signedness) (f : CCFloat) : Option CCInt :=
  match si with
  | .Signed => Float.to_int f
  | .Unsigned => Float.to_intu f

def cast_int_single
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (si : signedness) (i : CCInt) : CCFloat32 :=
  match si with
  | .Signed => Float32.of_int (certificate := binary32_certificate) i
  | .Unsigned => Float32.of_intu (certificate := binary32_certificate) i

def cast_single_int (si : signedness) (f : CCFloat32) : Option CCInt :=
  match si with
  | .Signed => Float32.to_int f
  | .Unsigned => Float32.to_intu f

def cast_int_long (si : signedness) (i : CCInt) : CCInt64 :=
  match si with
  | .Signed => Int64.repr (Int.signed i)
  | .Unsigned => Int64.repr (Int.unsigned i)

def cast_long_float
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    (si : signedness) (i : CCInt64) : CCFloat :=
  match si with
  | .Signed => Float.of_long (certificate := binary64_certificate) i
  | .Unsigned => Float.of_longu (certificate := binary64_certificate) i

def cast_long_single
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (si : signedness) (i : CCInt64) : CCFloat32 :=
  match si with
  | .Signed => Float32.of_long (certificate := binary32_certificate) i
  | .Unsigned => Float32.of_longu (certificate := binary32_certificate) i

def cast_float_long (si : signedness) (f : CCFloat) : Option CCInt64 :=
  match si with
  | .Signed => Float.to_long f
  | .Unsigned => Float.to_longu f

def cast_single_long (si : signedness) (f : CCFloat32) : Option CCInt64 :=
  match si with
  | .Signed => Float32.to_long f
  | .Unsigned => Float32.to_longu f

def sem_cast
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (v : val) (t1 t2 : type) (m : mem) : Option val :=
  match classify_cast t1 t2 with
  | .cast_case_pointer =>
      match v with
      | .Vptr _ _ => some v
      | .Vint _ => if CompCert4Lean.X86_64.Archi.ptr64 then none else some v
      | .Vlong _ => if CompCert4Lean.X86_64.Archi.ptr64 then some v else none
      | _ => none
  | .cast_case_i2i sz2 si2 =>
      match v with | .Vint i => some (.Vint (cast_int_int sz2 si2 i)) | _ => none
  | .cast_case_f2f => match v with | .Vfloat f => some (.Vfloat f) | _ => none
  | .cast_case_s2s => match v with | .Vsingle f => some (.Vsingle f) | _ => none
  | .cast_case_s2f => match v with | .Vsingle f => some (.Vfloat (Float.of_single f)) | _ => none
  | .cast_case_f2s => match v with | .Vfloat f => some (.Vsingle (Float.to_single f)) | _ => none
  | .cast_case_i2f si1 => match v with | .Vint i => some (.Vfloat (cast_int_float (binary64_certificate := binary64_certificate) si1 i)) | _ => none
  | .cast_case_i2s si1 => match v with | .Vint i => some (.Vsingle (cast_int_single (binary32_certificate := binary32_certificate) si1 i)) | _ => none
  | .cast_case_f2i sz2 si2 =>
      match v with
      | .Vfloat f => (cast_float_int si2 f).map (fun i => .Vint (cast_int_int sz2 si2 i))
      | _ => none
  | .cast_case_s2i sz2 si2 =>
      match v with
      | .Vsingle f => (cast_single_int si2 f).map (fun i => .Vint (cast_int_int sz2 si2 i))
      | _ => none
  | .cast_case_i2bool =>
      match v with
      | .Vint n => some (.Vint (if boolEqInt n Int.zero then Int.zero else Int.one))
      | .Vptr b ofs => if CompCert4Lean.X86_64.Archi.ptr64 then none else if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then some Vone else none
      | _ => none
  | .cast_case_l2bool =>
      match v with
      | .Vlong n => some (.Vint (if boolEqInt64 n Int64.zero then Int.zero else Int.one))
      | .Vptr b ofs => if !CompCert4Lean.X86_64.Archi.ptr64 then none else if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then some Vone else none
      | _ => none
  | .cast_case_f2bool =>
      match v with
      | .Vfloat f => some (.Vint (if Float.cmp Ceq f Float.zero then Int.zero else Int.one))
      | _ => none
  | .cast_case_s2bool =>
      match v with
      | .Vsingle f => some (.Vint (if Float32.cmp Ceq f Float32.zero then Int.zero else Int.one))
      | _ => none
  | .cast_case_l2l => match v with | .Vlong n => some (.Vlong n) | _ => none
  | .cast_case_i2l si => match v with | .Vint n => some (.Vlong (cast_int_long si n)) | _ => none
  | .cast_case_l2i sz si => match v with | .Vlong n => some (.Vint (cast_int_int sz si (Int.repr (Int64.unsigned n)))) | _ => none
  | .cast_case_l2f si1 => match v with | .Vlong i => some (.Vfloat (cast_long_float (binary64_certificate := binary64_certificate) si1 i)) | _ => none
  | .cast_case_l2s si1 => match v with | .Vlong i => some (.Vsingle (cast_long_single (binary32_certificate := binary32_certificate) si1 i)) | _ => none
  | .cast_case_f2l si2 => match v with | .Vfloat f => (cast_float_long si2 f).map .Vlong | _ => none
  | .cast_case_s2l si2 => match v with | .Vsingle f => (cast_single_long si2 f).map .Vlong | _ => none
  | .cast_case_struct id1 id2 => match v with | .Vptr _ _ => if identEq id1 id2 then some v else none | _ => none
  | .cast_case_union id1 id2 => match v with | .Vptr _ _ => if identEq id1 id2 then some v else none | _ => none
  | .cast_case_void => some v
  | .cast_case_default => none

inductive classify_bool_cases : Type where
  | bool_case_i
  | bool_case_l
  | bool_case_f
  | bool_case_s
  | bool_default

export classify_bool_cases (bool_case_i bool_case_l bool_case_f bool_case_s bool_default)

def classify_bool (ty : type) : classify_bool_cases :=
  match typeconv ty with
  | .Tint _ _ _ => .bool_case_i
  | .Tpointer _ _ => if CompCert4Lean.X86_64.Archi.ptr64 then .bool_case_l else .bool_case_i
  | .Tfloat .F64 _ => .bool_case_f
  | .Tfloat .F32 _ => .bool_case_s
  | .Tlong _ _ => .bool_case_l
  | _ => .bool_default

def bool_val (v : val) (t : type) (m : mem) : Option Bool :=
  match classify_bool t with
  | .bool_case_i =>
      match v with
      | .Vint n => some (!(boolEqInt n Int.zero))
      | .Vptr b ofs => if CompCert4Lean.X86_64.Archi.ptr64 then none else if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then some true else none
      | _ => none
  | .bool_case_l =>
      match v with
      | .Vlong n => some (!(boolEqInt64 n Int64.zero))
      | .Vptr b ofs => if !CompCert4Lean.X86_64.Archi.ptr64 then none else if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then some true else none
      | _ => none
  | .bool_case_f => match v with | .Vfloat f => some (!(Float.cmp Ceq f Float.zero)) | _ => none
  | .bool_case_s => match v with | .Vsingle f => some (!(Float32.cmp Ceq f Float32.zero)) | _ => none
  | .bool_default => none

def sem_notbool (v : val) (ty : type) (m : mem) : Option val :=
  (bool_val v ty m).map (fun b => Values.Val.of_bool (!b))

inductive classify_neg_cases : Type where
  | neg_case_i (s : signedness)
  | neg_case_f
  | neg_case_s
  | neg_case_l (s : signedness)
  | neg_default

export classify_neg_cases (neg_case_i neg_case_f neg_case_s neg_case_l neg_default)

def classify_neg (ty : type) : classify_neg_cases :=
  match ty with
  | .Tint .I32 .Unsigned _ => .neg_case_i .Unsigned
  | .Tint _ _ _ => .neg_case_i .Signed
  | .Tfloat .F64 _ => .neg_case_f
  | .Tfloat .F32 _ => .neg_case_s
  | .Tlong si _ => .neg_case_l si
  | _ => .neg_default

def sem_neg (v : val) (ty : type) : Option val :=
  match classify_neg ty with
  | .neg_case_i _ => match v with | .Vint n => some (.Vint (Int.neg n)) | _ => none
  | .neg_case_f => match v with | .Vfloat f => some (.Vfloat (Float.neg f)) | _ => none
  | .neg_case_s => match v with | .Vsingle f => some (.Vsingle (Float32.neg f)) | _ => none
  | .neg_case_l _ => match v with | .Vlong n => some (.Vlong (Int64.neg n)) | _ => none
  | .neg_default => none

def sem_absfloat
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    (v : val) (ty : type) : Option val :=
  match classify_neg ty with
  | .neg_case_i sg => match v with | .Vint n => some (.Vfloat (Float.abs (cast_int_float (binary64_certificate := binary64_certificate) sg n))) | _ => none
  | .neg_case_f => match v with | .Vfloat f => some (.Vfloat (Float.abs f)) | _ => none
  | .neg_case_s => match v with | .Vsingle f => some (.Vfloat (Float.abs (Float.of_single f))) | _ => none
  | .neg_case_l sg => match v with | .Vlong n => some (.Vfloat (Float.abs (cast_long_float (binary64_certificate := binary64_certificate) sg n))) | _ => none
  | .neg_default => none

inductive classify_notint_cases : Type where
  | notint_case_i (s : signedness)
  | notint_case_l (s : signedness)
  | notint_default

export classify_notint_cases (notint_case_i notint_case_l notint_default)

def classify_notint (ty : type) : classify_notint_cases :=
  match ty with
  | .Tint .I32 .Unsigned _ => .notint_case_i .Unsigned
  | .Tint _ _ _ => .notint_case_i .Signed
  | .Tlong si _ => .notint_case_l si
  | _ => .notint_default

def sem_notint (v : val) (ty : type) : Option val :=
  match classify_notint ty with
  | .notint_case_i _ => match v with | .Vint n => some (.Vint (Int.not n)) | _ => none
  | .notint_case_l _ => match v with | .Vlong n => some (.Vlong (Int64.not n)) | _ => none
  | .notint_default => none

/-! ## Binary operators -/

inductive binarith_cases : Type where
  | bin_case_i (s : signedness)
  | bin_case_l (s : signedness)
  | bin_case_f
  | bin_case_s
  | bin_default

export binarith_cases (bin_case_i bin_case_l bin_case_f bin_case_s bin_default)

def classify_binarith (ty1 ty2 : type) : binarith_cases :=
  match ty1, ty2 with
  | .Tint .I32 .Unsigned _, .Tint _ _ _ => .bin_case_i .Unsigned
  | .Tint _ _ _, .Tint .I32 .Unsigned _ => .bin_case_i .Unsigned
  | .Tint _ _ _, .Tint _ _ _ => .bin_case_i .Signed
  | .Tlong .Signed _, .Tlong .Signed _ => .bin_case_l .Signed
  | .Tlong _ _, .Tlong _ _ => .bin_case_l .Unsigned
  | .Tlong sg _, .Tint _ _ _ => .bin_case_l sg
  | .Tint _ _ _, .Tlong sg _ => .bin_case_l sg
  | .Tfloat .F32 _, .Tfloat .F32 _ => .bin_case_s
  | .Tfloat _ _, .Tfloat _ _ => .bin_case_f
  | .Tfloat .F64 _, .Tint _ _ _
  | .Tfloat .F64 _, .Tlong _ _ => .bin_case_f
  | .Tint _ _ _, .Tfloat .F64 _
  | .Tlong _ _, .Tfloat .F64 _ => .bin_case_f
  | .Tfloat .F32 _, .Tint _ _ _
  | .Tfloat .F32 _, .Tlong _ _ => .bin_case_s
  | .Tint _ _ _, .Tfloat .F32 _
  | .Tlong _ _, .Tfloat .F32 _ => .bin_case_s
  | _, _ => .bin_default

def binarith_type (c : binarith_cases) : type :=
  match c with
  | .bin_case_i sg => .Tint .I32 sg noattr
  | .bin_case_l sg => .Tlong sg noattr
  | .bin_case_f => .Tfloat .F64 noattr
  | .bin_case_s => .Tfloat .F32 noattr
  | .bin_default => .Tvoid

def sem_binarith
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (sem_int : signedness → CCInt → CCInt → Option val)
    (sem_long : signedness → CCInt64 → CCInt64 → Option val)
    (sem_float : CCFloat → CCFloat → Option val)
    (sem_single : CCFloat32 → CCFloat32 → Option val)
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  let c := classify_binarith t1 t2
  let t := binarith_type c
  match sem_cast (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) v1 t1 t m with
  | none => none
  | some v1' =>
      match sem_cast (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) v2 t2 t m with
      | none => none
      | some v2' =>
          match c with
          | .bin_case_i sg => match v1', v2' with | .Vint n1, .Vint n2 => sem_int sg n1 n2 | _, _ => none
          | .bin_case_f => match v1', v2' with | .Vfloat n1, .Vfloat n2 => sem_float n1 n2 | _, _ => none
          | .bin_case_s => match v1', v2' with | .Vsingle n1, .Vsingle n2 => sem_single n1 n2 | _, _ => none
          | .bin_case_l sg => match v1', v2' with | .Vlong n1, .Vlong n2 => sem_long sg n1 n2 | _, _ => none
          | .bin_default => none

inductive classify_add_cases : Type where
  | add_case_pi (ty : type) (si : signedness)
  | add_case_pl (ty : type)
  | add_case_ip (si : signedness) (ty : type)
  | add_case_lp (ty : type)
  | add_default

export classify_add_cases (add_case_pi add_case_pl add_case_ip add_case_lp add_default)

def classify_add (ty1 ty2 : type) : classify_add_cases :=
  match typeconv ty1, typeconv ty2 with
  | .Tpointer ty _, .Tint _ si _ => .add_case_pi ty si
  | .Tpointer ty _, .Tlong _ _ => .add_case_pl ty
  | .Tint _ si _, .Tpointer ty _ => .add_case_ip si ty
  | .Tlong _ _, .Tpointer ty _ => .add_case_lp ty
  | _, _ => .add_default

def ptrofs_of_int (si : signedness) (n : CCInt) : Ptrofs :=
  match si with
  | .Signed => Ptrofs.of_ints n
  | .Unsigned => Ptrofs.of_intu n

def sem_add_ptr_int (cenv : composite_env) (ty : type) (si : signedness) (v1 v2 : val) : Option val :=
  match v1, v2 with
  | .Vptr b1 ofs1, .Vint n2 =>
      let n2 := ptrofs_of_int si n2
      some (.Vptr b1 (Ptrofs.add ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
  | .Vint n1, .Vint n2 =>
      if CompCert4Lean.X86_64.Archi.ptr64 then none else some (.Vint (Int.add n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
  | .Vlong n1, .Vint n2 =>
      let n2 := cast_int_long si n2
      if CompCert4Lean.X86_64.Archi.ptr64 then some (.Vlong (Int64.add n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2))) else none
  | _, _ => none

def sem_add_ptr_long (cenv : composite_env) (ty : type) (v1 v2 : val) : Option val :=
  match v1, v2 with
  | .Vptr b1 ofs1, .Vlong n2 =>
      let n2 := Ptrofs.of_int64 n2
      some (.Vptr b1 (Ptrofs.add ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
  | .Vint n1, .Vlong n2 =>
      let n2 := Int.repr (Int64.unsigned n2)
      if CompCert4Lean.X86_64.Archi.ptr64 then none else some (.Vint (Int.add n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
  | .Vlong n1, .Vlong n2 =>
      if CompCert4Lean.X86_64.Archi.ptr64 then some (.Vlong (Int64.add n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2))) else none
  | _, _ => none

def sem_add
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cenv : composite_env) (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  match classify_add t1 t2 with
  | .add_case_pi ty si => sem_add_ptr_int cenv ty si v1 v2
  | .add_case_pl ty => sem_add_ptr_long cenv ty v1 v2
  | .add_case_ip si ty => sem_add_ptr_int cenv ty si v2 v1
  | .add_case_lp ty => sem_add_ptr_long cenv ty v2 v1
  | .add_default =>
      sem_binarith (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (fun _ n1 n2 => some (.Vint (Int.add n1 n2)))
        (fun _ n1 n2 => some (.Vlong (Int64.add n1 n2)))
        (fun n1 n2 => some (.Vfloat (Float.add n1 n2)))
        (fun n1 n2 => some (.Vsingle (Float32.add n1 n2)))
        v1 t1 v2 t2 m

inductive classify_sub_cases : Type where
  | sub_case_pi (ty : type) (si : signedness)
  | sub_case_pp (ty : type)
  | sub_case_pl (ty : type)
  | sub_default

export classify_sub_cases (sub_case_pi sub_case_pp sub_case_pl sub_default)

def classify_sub (ty1 ty2 : type) : classify_sub_cases :=
  match typeconv ty1, typeconv ty2 with
  | .Tpointer ty _, .Tint _ si _ => .sub_case_pi ty si
  | .Tpointer ty _, .Tpointer _ _ => .sub_case_pp ty
  | .Tpointer ty _, .Tlong _ _ => .sub_case_pl ty
  | _, _ => .sub_default

def sem_sub
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cenv : composite_env) (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  match classify_sub t1 t2 with
  | .sub_case_pi ty si =>
      match v1, v2 with
      | .Vptr b1 ofs1, .Vint n2 =>
          let n2 := ptrofs_of_int si n2
          some (.Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
      | .Vint n1, .Vint n2 =>
          if CompCert4Lean.X86_64.Archi.ptr64 then none else some (.Vint (Int.sub n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
      | .Vlong n1, .Vint n2 =>
          let n2 := cast_int_long si n2
          if CompCert4Lean.X86_64.Archi.ptr64 then some (.Vlong (Int64.sub n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2))) else none
      | _, _ => none
  | .sub_case_pl ty =>
      match v1, v2 with
      | .Vptr b1 ofs1, .Vlong n2 =>
          let n2 := Ptrofs.of_int64 n2
          some (.Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
      | .Vint n1, .Vlong n2 =>
          let n2 := Int.repr (Int64.unsigned n2)
          if CompCert4Lean.X86_64.Archi.ptr64 then none else some (.Vint (Int.sub n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
      | .Vlong n1, .Vlong n2 =>
          if CompCert4Lean.X86_64.Archi.ptr64 then some (.Vlong (Int64.sub n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2))) else none
      | _, _ => none
  | .sub_case_pp ty =>
      match v1, v2 with
      | .Vptr b1 ofs1, .Vptr b2 ofs2 =>
          if identEq b1 b2 then
            let sz := sizeof cenv ty
            if zltBool z0 sz && zleBool sz Ptrofs.max_signed then
              some (Vptrofs (Ptrofs.divs (Ptrofs.sub ofs1 ofs2) (Ptrofs.repr sz)))
            else none
          else none
      | _, _ => none
  | .sub_default =>
      sem_binarith (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (fun _ n1 n2 => some (.Vint (Int.sub n1 n2)))
        (fun _ n1 n2 => some (.Vlong (Int64.sub n1 n2)))
        (fun n1 n2 => some (.Vfloat (Float.sub n1 n2)))
        (fun n1 n2 => some (.Vsingle (Float32.sub n1 n2)))
        v1 t1 v2 t2 m

def sem_mul
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    (fun _ n1 n2 => some (.Vint (Int.mul n1 n2)))
    (fun _ n1 n2 => some (.Vlong (Int64.mul n1 n2)))
    (fun n1 n2 => some (.Vfloat (Float.mul n1 n2)))
    (fun n1 n2 => some (.Vsingle (Float32.mul n1 n2))) v1 t1 v2 t2 m

def sem_div
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    (fun sg n1 n2 => match sg with
      | .Signed => if boolEqInt n2 Int.zero || (boolEqInt n1 (Int.repr Int.min_signed) && boolEqInt n2 Int.mone) then none else some (.Vint (Int.divs n1 n2))
      | .Unsigned => if boolEqInt n2 Int.zero then none else some (.Vint (Int.divu n1 n2)))
    (fun sg n1 n2 => match sg with
      | .Signed => if boolEqInt64 n2 Int64.zero || (boolEqInt64 n1 (Int64.repr Int64.min_signed) && boolEqInt64 n2 Int64.mone) then none else some (.Vlong (Int64.divs n1 n2))
      | .Unsigned => if boolEqInt64 n2 Int64.zero then none else some (.Vlong (Int64.divu n1 n2)))
    (fun n1 n2 => some (.Vfloat (Float.div n1 n2)))
    (fun n1 n2 => some (.Vsingle (Float32.div n1 n2))) v1 t1 v2 t2 m

def sem_mod
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    (fun sg n1 n2 => match sg with
      | .Signed => if boolEqInt n2 Int.zero || (boolEqInt n1 (Int.repr Int.min_signed) && boolEqInt n2 Int.mone) then none else some (.Vint (CompCert4Lean.Lib.Integers.Int.mods n1 n2))
      | .Unsigned => if boolEqInt n2 Int.zero then none else some (.Vint (CompCert4Lean.Lib.Integers.Int.modu n1 n2)))
    (fun sg n1 n2 => match sg with
      | .Signed => if boolEqInt64 n2 Int64.zero || (boolEqInt64 n1 (Int64.repr Int64.min_signed) && boolEqInt64 n2 Int64.mone) then none else some (.Vlong (CompCert4Lean.Lib.Integers.Int64.mods n1 n2))
      | .Unsigned => if boolEqInt64 n2 Int64.zero then none else some (.Vlong (CompCert4Lean.Lib.Integers.Int64.modu n1 n2)))
    (fun _ _ => none) (fun _ _ => none) v1 t1 v2 t2 m

def sem_and
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) (fun _ n1 n2 => some (.Vint (Int.and n1 n2))) (fun _ n1 n2 => some (.Vlong (Int64.and n1 n2))) (fun _ _ => none) (fun _ _ => none) v1 t1 v2 t2 m

def sem_or
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) (fun _ n1 n2 => some (.Vint (Int.or n1 n2))) (fun _ n1 n2 => some (.Vlong (Int64.or n1 n2))) (fun _ _ => none) (fun _ _ => none) v1 t1 v2 t2 m

def sem_xor
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) (fun _ n1 n2 => some (.Vint (Int.xor n1 n2))) (fun _ n1 n2 => some (.Vlong (Int64.xor n1 n2))) (fun _ _ => none) (fun _ _ => none) v1 t1 v2 t2 m

inductive classify_shift_cases : Type where
  | shift_case_ii (s : signedness)
  | shift_case_ll (s : signedness)
  | shift_case_il (s : signedness)
  | shift_case_li (s : signedness)
  | shift_default

export classify_shift_cases (shift_case_ii shift_case_ll shift_case_il shift_case_li shift_default)

def classify_shift (ty1 ty2 : type) : classify_shift_cases :=
  match typeconv ty1, typeconv ty2 with
  | .Tint .I32 .Unsigned _, .Tint _ _ _ => .shift_case_ii .Unsigned
  | .Tint _ _ _, .Tint _ _ _ => .shift_case_ii .Signed
  | .Tint .I32 .Unsigned _, .Tlong _ _ => .shift_case_il .Unsigned
  | .Tint _ _ _, .Tlong _ _ => .shift_case_il .Signed
  | .Tlong s _, .Tint _ _ _ => .shift_case_li s
  | .Tlong s _, .Tlong _ _ => .shift_case_ll s
  | _, _ => .shift_default

def sem_shift
    (sem_int : signedness → CCInt → CCInt → CCInt)
    (sem_long : signedness → CCInt64 → CCInt64 → CCInt64)
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) : Option val :=
  match classify_shift t1 t2 with
  | .shift_case_ii sg => match v1, v2 with
      | .Vint n1, .Vint n2 => if Int.ltu n2 Int.iwordsize then some (.Vint (sem_int sg n1 n2)) else none
      | _, _ => none
  | .shift_case_il sg => match v1, v2 with
      | .Vint n1, .Vlong n2 => if Int64.ltu n2 (Int64.repr (zOfNat 32)) then some (.Vint (sem_int sg n1 (Int64.loword n2))) else none
      | _, _ => none
  | .shift_case_li sg => match v1, v2 with
      | .Vlong n1, .Vint n2 => if Int.ltu n2 Int64.iwordsize' then some (.Vlong (sem_long sg n1 (Int64.repr (Int.unsigned n2)))) else none
      | _, _ => none
  | .shift_case_ll sg => match v1, v2 with
      | .Vlong n1, .Vlong n2 => if Int64.ltu n2 Int64.iwordsize then some (.Vlong (sem_long sg n1 n2)) else none
      | _, _ => none
  | .shift_default => none

def sem_shl (v1 : val) (t1 : type) (v2 : val) (t2 : type) : Option val :=
  sem_shift (fun _ n1 n2 => Int.shl n1 n2) (fun _ n1 n2 => Int64.shl n1 n2) v1 t1 v2 t2

def sem_shr (v1 : val) (t1 : type) (v2 : val) (t2 : type) : Option val :=
  sem_shift
    (fun sg n1 n2 => match sg with | .Signed => Int.shr n1 n2 | .Unsigned => Int.shru n1 n2)
    (fun sg n1 n2 => match sg with | .Signed => Int64.shr n1 n2 | .Unsigned => Int64.shru n1 n2)
    v1 t1 v2 t2

inductive classify_cmp_cases : Type where
  | cmp_case_pp
  | cmp_case_pi (si : signedness)
  | cmp_case_ip (si : signedness)
  | cmp_case_pl
  | cmp_case_lp
  | cmp_default

export classify_cmp_cases (cmp_case_pp cmp_case_pi cmp_case_ip cmp_case_pl cmp_case_lp cmp_default)

def classify_cmp (ty1 ty2 : type) : classify_cmp_cases :=
  match typeconv ty1, typeconv ty2 with
  | .Tpointer _ _, .Tpointer _ _ => .cmp_case_pp
  | .Tpointer _ _, .Tint _ si _ => .cmp_case_pi si
  | .Tint _ si _, .Tpointer _ _ => .cmp_case_ip si
  | .Tpointer _ _, .Tlong _ _ => .cmp_case_pl
  | .Tlong _ _, .Tpointer _ _ => .cmp_case_lp
  | _, _ => .cmp_default

def cmp_ptr (m : mem) (c : comparison) (v1 v2 : val) : Option val :=
  ((if CompCert4Lean.X86_64.Archi.ptr64 then Val.cmplu_bool (Mem.valid_pointer m) c v1 v2 else Val.cmpu_bool (Mem.valid_pointer m) c v1 v2).map Val.of_bool)

def sem_cmp
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (c : comparison) (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  match classify_cmp t1 t2 with
  | .cmp_case_pp => cmp_ptr m c v1 v2
  | .cmp_case_pi si =>
      match v2 with
      | .Vint n2 => cmp_ptr m c v1 (Vptrofs (ptrofs_of_int si n2))
      | .Vptr _ _ => if CompCert4Lean.X86_64.Archi.ptr64 then none else cmp_ptr m c v1 v2
      | _ => none
  | .cmp_case_ip si =>
      match v1 with
      | .Vint n1 => cmp_ptr m c (Vptrofs (ptrofs_of_int si n1)) v2
      | .Vptr _ _ => if CompCert4Lean.X86_64.Archi.ptr64 then none else cmp_ptr m c v1 v2
      | _ => none
  | .cmp_case_pl =>
      match v2 with
      | .Vlong n2 => cmp_ptr m c v1 (Vptrofs (Ptrofs.of_int64 n2))
      | .Vptr _ _ => if CompCert4Lean.X86_64.Archi.ptr64 then cmp_ptr m c v1 v2 else none
      | _ => none
  | .cmp_case_lp =>
      match v1 with
      | .Vlong n1 => cmp_ptr m c (Vptrofs (Ptrofs.of_int64 n1)) v2
      | .Vptr _ _ => if CompCert4Lean.X86_64.Archi.ptr64 then cmp_ptr m c v1 v2 else none
      | _ => none
  | .cmp_default =>
      sem_binarith (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (fun sg n1 n2 => some (Val.of_bool (match sg with | .Signed => CompCert4Lean.Lib.Integers.Int.cmp c n1 n2 | .Unsigned => CompCert4Lean.Lib.Integers.Int.cmpu c n1 n2)))
        (fun sg n1 n2 => some (Val.of_bool (match sg with | .Signed => CompCert4Lean.Lib.Integers.Int64.cmp c n1 n2 | .Unsigned => CompCert4Lean.Lib.Integers.Int64.cmpu c n1 n2)))
        (fun n1 n2 => some (Val.of_bool (Float.cmp c n1 n2)))
        (fun n1 n2 => some (Val.of_bool (Float32.cmp c n1 n2))) v1 t1 v2 t2 m

inductive classify_fun_cases : Type where
  | fun_case_f (targs : List type) (tres : type) (cc : calling_convention)
  | fun_default

export classify_fun_cases (fun_case_f fun_default)

def classify_fun (ty : type) : classify_fun_cases :=
  match ty with
  | .Tfunction args res cc => .fun_case_f args res cc
  | .Tpointer (.Tfunction args res cc) _ => .fun_case_f args res cc
  | _ => .fun_default

inductive classify_switch_cases : Type where
  | switch_case_i
  | switch_case_l
  | switch_default

export classify_switch_cases (switch_case_i switch_case_l switch_default)

def classify_switch (ty : type) : classify_switch_cases :=
  match ty with
  | .Tint _ _ _ => .switch_case_i
  | .Tlong _ _ => .switch_case_l
  | _ => .switch_default

def sem_switch_arg (v : val) (ty : type) : Option Z :=
  match classify_switch ty with
  | .switch_case_i => match v with | .Vint n => some (Int.unsigned n) | _ => none
  | .switch_case_l => match v with | .Vlong n => some (Int64.unsigned n) | _ => none
  | .switch_default => none

def sem_unary_operation
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    (op : unary_operation) (v : val) (ty : type) (m : mem) : Option val :=
  match op with
  | .Onotbool => sem_notbool v ty m
  | .Onotint => sem_notint v ty
  | .Oneg => sem_neg v ty
  | .Oabsfloat => sem_absfloat (binary64_certificate := binary64_certificate) v ty

def sem_binary_operation
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cenv : composite_env) (op : binary_operation)
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  match op with
  | .Oadd => sem_add (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cenv v1 t1 v2 t2 m
  | .Osub => sem_sub (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cenv v1 t1 v2 t2 m
  | .Omul => sem_mul (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) v1 t1 v2 t2 m
  | .Odiv => sem_div (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) v1 t1 v2 t2 m
  | .Omod => sem_mod (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) v1 t1 v2 t2 m
  | .Oand => sem_and (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) v1 t1 v2 t2 m
  | .Oor => sem_or (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) v1 t1 v2 t2 m
  | .Oxor => sem_xor (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) v1 t1 v2 t2 m
  | .Oshl => sem_shl v1 t1 v2 t2
  | .Oshr => sem_shr v1 t1 v2 t2
  | .Oeq => sem_cmp (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) Ceq v1 t1 v2 t2 m
  | .One => sem_cmp (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) Cne v1 t1 v2 t2 m
  | .Olt => sem_cmp (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) Clt v1 t1 v2 t2 m
  | .Ogt => sem_cmp (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) Cgt v1 t1 v2 t2 m
  | .Ole => sem_cmp (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) Cle v1 t1 v2 t2 m
  | .Oge => sem_cmp (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) Cge v1 t1 v2 t2 m

def sem_incrdecr
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cenv : composite_env) (id : incr_or_decr) (v : val) (ty : type) (m : mem) : Option val :=
  match id with
  | .Incr => sem_add (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cenv v ty (.Vint Int.one) type_int32s m
  | .Decr => sem_sub (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cenv v ty (.Vint Int.one) type_int32s m

def incrdecr_type (ty : type) : type :=
  match typeconv ty with
  | .Tpointer ty a => .Tpointer ty a
  | .Tint sz sg _ => .Tint sz sg noattr
  | .Tlong sg _ => .Tlong sg noattr
  | .Tfloat sz _ => .Tfloat sz noattr
  | _ => .Tvoid

def chunk_for_carrier (sz : intsize) : memory_chunk :=
  match sz with
  | .I8 | .IBool => .Mint8unsigned
  | .I16 => .Mint16unsigned
  | .I32 => .Mint32

def bitsize_carrier (sz : intsize) : Z :=
  match sz with
  | .I8 | .IBool => zOfNat 8
  | .I16 => zOfNat 16
  | .I32 => zOfNat 32

def first_bit (sz : intsize) (pos width : Z) : Z :=
  if CompCert4Lean.X86_64.Archi.big_endian then zSub (zSub (bitsize_carrier sz) pos) width else pos

def bitfield_extract (sz : intsize) (sg : signedness) (pos width : Z) (c : CCInt) : CCInt :=
  if intsizeEq sz .IBool || signednessEq sg .Unsigned then
    CompCert4Lean.Lib.Integers.Int.unsigned_bitfield_extract (first_bit sz pos width) width c
  else CompCert4Lean.Lib.Integers.Int.signed_bitfield_extract (first_bit sz pos width) width c

def bitfield_normalize (sz : intsize) (sg : signedness) (width : Z) (n : CCInt) : CCInt :=
  if intsizeEq sz .IBool || signednessEq sg .Unsigned then Int.zero_ext width n else Int.sign_ext width n

inductive load_bitfield : type → intsize → signedness → Z → Z → mem → val → val → Prop where
  | load_bitfield_intro
      (sz : intsize) (sg1 : signedness) (attr : attr) (sg : signedness)
      (pos width : Z) (m : mem) (addr : val) (c : CCInt)
      (hpos : zLe z0 pos)
      (hwidth : zLt z0 width ∧ zLe width (bitsize_intsize sz))
      (hcarrier : zLe (zAdd pos width) (bitsize_carrier sz))
      (hsg : sg1 = (if zltBool width (bitsize_intsize sz) then .Signed else sg))
      (hload : Mem.loadv (chunk_for_carrier sz) m addr = some (.Vint c)) :
      load_bitfield (.Tint sz sg1 attr) sz sg pos width m addr
        (.Vint (bitfield_extract sz sg pos width c))

export load_bitfield (load_bitfield_intro)

inductive store_bitfield : type → intsize → signedness → Z → Z → mem → val → val → mem → val → Prop where
  | store_bitfield_intro
      (sz : intsize) (sg1 : signedness) (attr : attr) (sg : signedness)
      (pos width : Z) (m : mem) (addr : val) (c n : CCInt) (m' : mem)
      (hpos : zLe z0 pos)
      (hwidth : zLt z0 width ∧ zLe width (bitsize_intsize sz))
      (hcarrier : zLe (zAdd pos width) (bitsize_carrier sz))
      (hsg : sg1 = (if zltBool width (bitsize_intsize sz) then .Signed else sg))
      (hload : Mem.loadv (chunk_for_carrier sz) m addr = some (.Vint c))
      (hstore : Mem.storev (chunk_for_carrier sz) m addr
        (.Vint (CompCert4Lean.Lib.Integers.Int.bitfield_insert (first_bit sz pos width) width c n)) = some m') :
      store_bitfield (.Tint sz sg1 attr) sz sg pos width m addr (.Vint n)
        m' (.Vint (bitfield_normalize sz sg width n))

export store_bitfield (store_bitfield_intro)

/-! ## Compatibility with extensions and injections -/

def optval_self_injects (ov : Option val) : Prop :=
  match ov with
  | some (.Vptr _ _) => False
  | _ => True

/-! ## Properties of casted values -/

inductive val_casted : val → type → Prop where
  | val_casted_int
      (sz : intsize) (si : signedness) (attr : attr) (n : CCInt)
      (hcast : cast_int_int sz si n = n) :
      val_casted (.Vint n) (.Tint sz si attr)
  | val_casted_float
      (attr : attr) (n : CCFloat) :
      val_casted (.Vfloat n) (.Tfloat .F64 attr)
  | val_casted_single
      (attr : attr) (n : CCFloat32) :
      val_casted (.Vsingle n) (.Tfloat .F32 attr)
  | val_casted_long
      (si : signedness) (attr : attr) (n : CCInt64) :
      val_casted (.Vlong n) (.Tlong si attr)
  | val_casted_ptr_ptr
      (b : block) (ofs : Ptrofs) (ty : type) (attr : attr) :
      val_casted (.Vptr b ofs) (.Tpointer ty attr)
  | val_casted_int_ptr
      (n : CCInt) (ty : type) (attr : attr)
      (hptr64 : CompCert4Lean.X86_64.Archi.ptr64 = false) :
      val_casted (.Vint n) (.Tpointer ty attr)
  | val_casted_ptr_int
      (b : block) (ofs : Ptrofs) (si : signedness) (attr : attr)
      (hptr64 : CompCert4Lean.X86_64.Archi.ptr64 = false) :
      val_casted (.Vptr b ofs) (.Tint .I32 si attr)
  | val_casted_long_ptr
      (n : CCInt64) (ty : type) (attr : attr)
      (hptr64 : CompCert4Lean.X86_64.Archi.ptr64 = true) :
      val_casted (.Vlong n) (.Tpointer ty attr)
  | val_casted_ptr_long
      (b : block) (ofs : Ptrofs) (si : signedness) (attr : attr)
      (hptr64 : CompCert4Lean.X86_64.Archi.ptr64 = true) :
      val_casted (.Vptr b ofs) (.Tlong si attr)
  | val_casted_struct
      (id : ident) (attr : attr) (b : block) (ofs : Ptrofs) :
      val_casted (.Vptr b ofs) (.Tstruct id attr)
  | val_casted_union
      (id : ident) (attr : attr) (b : block) (ofs : Ptrofs) :
      val_casted (.Vptr b ofs) (.Tunion id attr)
  | val_casted_void
      (v : val) :
      val_casted v .Tvoid

export val_casted (val_casted_int val_casted_float val_casted_single val_casted_long
  val_casted_ptr_ptr val_casted_int_ptr val_casted_ptr_int val_casted_long_ptr
  val_casted_ptr_long val_casted_struct val_casted_union val_casted_void)

/-! Later-proof exact statement descriptors. -/

def sem_cast_injStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (f : meminj) (m m' : mem),
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    ∀ v1 ty1 ty v tv1,
      sem_cast v1 ty1 ty m = some v →
      Val.inject f v1 tv1 →
      ∃ tv, sem_cast tv1 ty1 ty m' = some tv ∧ Val.inject f v tv

def bool_val_injStatement : Prop :=
  ∀ (f : meminj) (m m' : mem),
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    ∀ v ty b tv,
      bool_val v ty m = some b →
      Val.inject f v tv →
      bool_val tv ty m' = some b

def sem_unary_operation_injStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)] : Prop :=
  ∀ (f : meminj) (m m' : mem),
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    ∀ op v1 ty v tv1,
      sem_unary_operation op v1 ty m = some v →
      Val.inject f v1 tv1 →
      ∃ tv, sem_unary_operation op tv1 ty m' = some tv ∧ Val.inject f v tv

def sem_binarith_injectStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (f : meminj) (m m' : mem),
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    ∀ (sem_int : signedness → CCInt → CCInt → Option val)
      (sem_long : signedness → CCInt64 → CCInt64 → Option val)
      (sem_float : CCFloat → CCFloat → Option val)
      (sem_single : CCFloat32 → CCFloat32 → Option val)
      v1 t1 v2 t2 v v1' v2',
      sem_binarith sem_int sem_long sem_float sem_single v1 t1 v2 t2 m = some v →
      Val.inject f v1 v1' → Val.inject f v2 v2' →
      (∀ sg n1 n2, optval_self_injects (sem_int sg n1 n2)) →
      (∀ sg n1 n2, optval_self_injects (sem_long sg n1 n2)) →
      (∀ n1 n2, optval_self_injects (sem_float n1 n2)) →
      (∀ n1 n2, optval_self_injects (sem_single n1 n2)) →
      ∃ v', sem_binarith sem_int sem_long sem_float sem_single v1' t1 v2' t2 m' = some v' ∧ Val.inject f v v'

def sem_shift_injectStatement : Prop :=
  ∀ (f : meminj)
    (sem_int : signedness → CCInt → CCInt → CCInt)
    (sem_long : signedness → CCInt64 → CCInt64 → CCInt64)
    v1 t1 v2 t2 v v1' v2',
    sem_shift sem_int sem_long v1 t1 v2 t2 = some v →
    Val.inject f v1 v1' → Val.inject f v2 v2' →
    ∃ v', sem_shift sem_int sem_long v1' t1 v2' t2 = some v' ∧ Val.inject f v v'

def sem_cmp_ptr_injStatement : Prop :=
  ∀ (f : meminj) (m m' : mem),
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Mem.valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      zLe z0 (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta))) ∧
      zLe (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta))) Ptrofs.max_unsigned) →
    (∀ (b1 : block) (ofs1 : Ptrofs) (b2 : block) (ofs2 : Ptrofs)
      (b1' : block) (delta1 : Z) (b2' : block) (delta2 : Z),
      b1 ≠ b2 →
      Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true →
      Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true →
      f b1 = some (b1', delta1) → f b2 = some (b2', delta2) →
      b1' ≠ b2' ∨
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
        Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2))) →
    ∀ c v1 v2 v tv1 tv2,
    cmp_ptr m c v1 v2 = some v →
    Val.inject f v1 tv1 → Val.inject f v2 tv2 →
    ∃ tv, cmp_ptr m' c tv1 tv2 = some tv ∧ Val.inject f v tv

def sem_cmp_injStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (f : meminj) (m m'),
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Mem.valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      zLe z0 (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta))) ∧
      zLe (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta))) Ptrofs.max_unsigned) →
    (∀ (b1 : block) (ofs1 : Ptrofs) (b2 : block) (ofs2 : Ptrofs)
      (b1' : block) (delta1 : Z) (b2' : block) (delta2 : Z),
      b1 ≠ b2 →
      Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true →
      Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true →
      f b1 = some (b1', delta1) → f b2 = some (b2', delta2) →
      b1' ≠ b2' ∨
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
        Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2))) →
    ∀ cmp v1 tv1 ty1 v2 tv2 ty2 v,
    sem_cmp cmp v1 ty1 v2 ty2 m = some v →
    Val.inject f v1 tv1 → Val.inject f v2 tv2 →
    ∃ tv, sem_cmp cmp tv1 ty1 tv2 ty2 m' = some tv ∧ Val.inject f v tv

def sem_binary_operation_injStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (f : meminj) (m m'),
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Mem.valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      zLe z0 (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta))) ∧
      zLe (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta))) Ptrofs.max_unsigned) →
    (∀ (b1 : block) (ofs1 : Ptrofs) (b2 : block) (ofs2 : Ptrofs)
      (b1' : block) (delta1 : Z) (b2' : block) (delta2 : Z),
      b1 ≠ b2 →
      Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true →
      Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true →
      f b1 = some (b1', delta1) → f b2 = some (b2', delta2) →
      b1' ≠ b2' ∨
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
        Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2))) →
    ∀ cenv op v1 ty1 v2 ty2 v tv1 tv2,
    sem_binary_operation cenv op v1 ty1 v2 ty2 m = some v →
    Val.inject f v1 tv1 → Val.inject f v2 tv2 →
    ∃ tv, sem_binary_operation cenv op tv1 ty1 tv2 ty2 m' = some tv ∧ Val.inject f v tv

def sem_cast_injectStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (f : meminj) (v1 : val) (ty1 ty : type) (m : mem)
    (v tv1 : val) (tm : mem),
    sem_cast v1 ty1 ty m = some v →
    Val.inject f v1 tv1 →
    Mem.inject f m tm →
    ∃ tv, sem_cast tv1 ty1 ty tm = some tv ∧ Val.inject f v tv

def sem_unary_operation_injectStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)] : Prop :=
  ∀ (f : meminj) (m m' : mem) op v1 ty1 v tv1,
    sem_unary_operation op v1 ty1 m = some v →
    Val.inject f v1 tv1 →
    Mem.inject f m m' →
    ∃ tv, sem_unary_operation op tv1 ty1 m' = some tv ∧ Val.inject f v tv

def sem_binary_operation_injectStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (f : meminj) (m m' : mem) cenv op v1 ty1 v2 ty2 v tv1 tv2,
    sem_binary_operation cenv op v1 ty1 v2 ty2 m = some v →
    Val.inject f v1 tv1 → Val.inject f v2 tv2 →
    Mem.inject f m m' →
    ∃ tv, sem_binary_operation cenv op tv1 ty1 tv2 ty2 m' = some tv ∧ Val.inject f v tv

def bool_val_injectStatement : Prop :=
  ∀ (f : meminj) (m m' : mem) v ty b tv,
    bool_val v ty m = some b → Val.inject f v tv → Mem.inject f m m' → bool_val tv ty m' = some b

def cast_val_is_castedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ v ty ty' v' m, sem_cast v ty ty' m = some v' → val_casted v' ty'

def cast_val_castedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ v ty m, val_casted v ty → sem_cast v ty ty m = some v

def cast_idempotentStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ v ty ty' v' m, sem_cast v ty ty' m = some v' → sem_cast v' ty' ty' m = some v'

def val_casted_has_argtypeStatement : Prop :=
  ∀ v ty, val_casted v ty → Val.has_argtype v (argtype_of_type ty)

end CompCert4Lean.Cfrontend.Cop


namespace CompCert4Lean.Cfrontend.Cop

private theorem bool_val_inj_aux : bool_val_injStatement := by
  intro f m m' hweak v ty b tv hval hinj
  cases hinj with
  | inject_int n =>
      cases hclass : classify_bool ty <;>
        simp [bool_val, hclass, CompCert4Lean.X86_64.Archi.ptr64] at hval ⊢ <;>
        exact hval
  | inject_long n =>
      cases hclass : classify_bool ty <;>
        simp [bool_val, hclass, CompCert4Lean.X86_64.Archi.ptr64] at hval ⊢ <;>
        exact hval
  | inject_float x =>
      cases hclass : classify_bool ty <;> simp [bool_val, hclass] at hval ⊢ <;>
        exact hval
  | inject_single x =>
      cases hclass : classify_bool ty <;> simp [bool_val, hclass] at hval ⊢ <;>
        exact hval
  | val_inject_undef x =>
      cases hclass : classify_bool ty <;> simp [bool_val, hclass] at hval
  | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
      cases hclass : classify_bool ty with
      | bool_case_i =>
          simp [bool_val, hclass, CompCert4Lean.X86_64.Archi.ptr64] at hval ⊢
      | bool_case_l =>
          simp [bool_val, hclass, CompCert4Lean.X86_64.Archi.ptr64] at hval ⊢
          have hp' := hweak b1 ofs1 b2 delta hmap hval.1
          rw [hval.2]
          simpa [hofs] using hp'
      | _ => simp [bool_val, hclass] at hval

theorem sem_unary_operation_inj :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)],
      sem_unary_operation_injStatement := by
  intro _binary64_certificate f m m' hweak op v1 ty v tv1 hsem hinj
  cases op with
  | Onotbool =>
      unfold sem_unary_operation sem_notbool at hsem ⊢
      cases hb : bool_val v1 ty m with
      | none => simp [hb] at hsem
      | some b =>
          simp [hb] at hsem ⊢
          have hb' := bool_val_inj_aux f m m' hweak v1 ty b tv1 hb hinj
          cases b <;> simp [hb']
          · rw [← hsem]
            exact Common.Values.Val.inject.inject_int _
          · rw [← hsem]
            exact Common.Values.Val.inject.inject_int _
  | Onotint =>
      unfold sem_unary_operation sem_notint at hsem ⊢
      cases hc : classify_notint ty <;> simp [hc] at hsem ⊢ <;>
        cases hinj <;> simp_all <;> try { subst v; constructor }
  | Oneg =>
      unfold sem_unary_operation sem_neg at hsem ⊢
      cases hc : classify_neg ty <;> simp [hc] at hsem ⊢ <;>
        cases hinj <;> simp_all <;> try { subst v; constructor }
  | Oabsfloat =>
      unfold sem_unary_operation sem_absfloat at hsem ⊢
      cases hc : classify_neg ty <;> simp [hc] at hsem ⊢ <;>
        cases hinj <;> simp_all <;> try { subst v; constructor }

end CompCert4Lean.Cfrontend.Cop



namespace CompCert4Lean.Cfrontend.Cop

theorem bool_val_inj : bool_val_injStatement := bool_val_inj_aux

end CompCert4Lean.Cfrontend.Cop

namespace CompCert4Lean.Cfrontend.Cop

theorem sem_cast_inj :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      sem_cast_injStatement := by
  intro _binary64_certificate _binary32_certificate f m m' hweak v1 ty1 ty v tv1 hsem hinj
  unfold sem_cast at hsem ⊢
  cases hclass : classify_cast ty1 ty <;>
    rw [hclass] at hsem <;>
    cases hinj <;>
    simp_all [cast_int_int, cast_int_float, cast_int_single, cast_int_long,
      cast_float_int, cast_single_int, cast_long_float, cast_long_single,
      cast_float_long, cast_single_long] <;>
    try { subst v; constructor }
  case cast_case_pointer.inject_int =>
    rcases hsem with ⟨_, hv⟩
    subst v
    exact Common.Values.Val.inject.inject_int _
  case cast_case_pointer.inject_long =>
    rcases hsem with ⟨_, hv⟩
    subst v
    exact Common.Values.Val.inject.inject_long _
  case cast_case_pointer.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
    subst v
    have hp : Common.Values.Val.inject f (Common.Values.Vptr b1 ofs1)
        (Common.Values.Vptr b2 ofs2) :=
      Common.Values.Val.inject.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs
    simpa [hofs] using hp
  case cast_case_f2i.inject_float sz2 si f0 =>
    rcases hsem with ⟨i, hi, hv⟩
    subst v
    refine ⟨Common.Values.Vint (cast_int_int sz2 si i), ?_, ?_⟩
    · exact ⟨i, hi, rfl⟩
    · exact Common.Values.Val.inject.inject_int _
  case cast_case_s2i.inject_single sz2 si f0 =>
    rcases hsem with ⟨i, hi, hv⟩
    subst v
    refine ⟨Common.Values.Vint (cast_int_int sz2 si i), ?_, ?_⟩
    · exact ⟨i, hi, rfl⟩
    · exact Common.Values.Val.inject.inject_int _
  case cast_case_f2l.inject_float si f0 =>
    rcases hsem with ⟨i, hi, hv⟩
    subst v
    refine ⟨Common.Values.Vlong i, ?_, ?_⟩
    · exact ⟨i, hi, rfl⟩
    · exact Common.Values.Val.inject.inject_long _
  case cast_case_s2l.inject_single si f0 =>
    rcases hsem with ⟨i, hi, hv⟩
    subst v
    refine ⟨Common.Values.Vlong i, ?_, ?_⟩
    · exact ⟨i, hi, rfl⟩
    · exact Common.Values.Val.inject.inject_long _
  case cast_case_i2bool.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
    rcases hsem with ⟨hptr, hvalid, hv⟩
    have hvalid' := hweak b1 ofs1 b2 delta hmap hvalid
    subst v
    refine ⟨Common.Values.Vone, ?_, ?_⟩
    · exact ⟨by simpa [hofs] using hvalid', rfl⟩
    · exact Common.Values.Val.inject.inject_int _
  case cast_case_l2bool.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
    rcases hsem with ⟨hptr, hvalid, hv⟩
    have hvalid' := hweak b1 ofs1 b2 delta hmap hvalid
    subst v
    refine ⟨Common.Values.Vone, ?_, ?_⟩
    · exact ⟨by simpa [hofs] using hvalid', rfl⟩
    · exact Common.Values.Val.inject.inject_int _
  case cast_case_struct.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
    rcases hsem with ⟨hid, hv⟩
    subst v
    have hp : Common.Values.Val.inject f (Common.Values.Vptr b1 ofs1)
        (Common.Values.Vptr b2 ofs2) :=
      Common.Values.Val.inject.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs
    simpa [hofs] using hp
  case cast_case_union.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
    rcases hsem with ⟨hid, hv⟩
    subst v
    have hp : Common.Values.Val.inject f (Common.Values.Vptr b1 ofs1)
        (Common.Values.Vptr b2 ofs2) :=
      Common.Values.Val.inject.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs
    simpa [hofs] using hp
  case cast_case_void.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
    subst v
    have hp : Common.Values.Val.inject f (Common.Values.Vptr b1 ofs1)
        (Common.Values.Vptr b2 ofs2) :=
      Common.Values.Val.inject.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs
    simpa [hofs] using hp

end CompCert4Lean.Cfrontend.Cop

namespace CompCert4Lean.Cfrontend.Cop

theorem sem_shift_inject : sem_shift_injectStatement := by
  intro f sem_int sem_long v1 t1 v2 t2 v v1' v2' hsem hinj1 hinj2
  cases hclass : classify_shift t1 t2 <;> simp [sem_shift, hclass] at hsem ⊢
  all_goals
    cases hinj1 <;> cases hinj2 <;> simp_all <;> rcases hsem with ⟨_, rfl⟩ <;> constructor

end CompCert4Lean.Cfrontend.Cop

namespace CompCert4Lean.Cfrontend.Cop

theorem cast_val_casted :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      cast_val_castedStatement := by
  intro _binary64_certificate _binary32_certificate v ty m h
  cases h with
  | val_casted_int sz si attr n hcast =>
      cases sz with
      | I8 =>
          cases si <;>
            simpa [sem_cast, classify_cast, cast_int_int,
              CompCert4Lean.X86_64.Archi.ptr64] using hcast
      | I16 =>
          cases si <;>
            simpa [sem_cast, classify_cast, cast_int_int,
              CompCert4Lean.X86_64.Archi.ptr64] using hcast
      | I32 =>
          simp [sem_cast, classify_cast, cast_int_int,
            CompCert4Lean.X86_64.Archi.ptr64]
      | IBool =>
          cases si <;>
            cases hb : boolEqInt n Int.zero <;>
              simpa [sem_cast, classify_cast, cast_int_int,
                CompCert4Lean.X86_64.Archi.ptr64, hb] using hcast
  | val_casted_float attr n =>
      simp [sem_cast, classify_cast, CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_single attr n =>
      simp [sem_cast, classify_cast, CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_long si attr n =>
      simp [sem_cast, classify_cast, CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_ptr_ptr b ofs ty attr =>
      simp [sem_cast, classify_cast, CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_int_ptr n ty attr hptr64 =>
      simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr64
  | val_casted_ptr_int b ofs si attr hptr64 =>
      simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr64
  | val_casted_long_ptr n ty attr hptr64 =>
      simp [sem_cast, classify_cast, CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_ptr_long b ofs si attr hptr64 =>
      simp [sem_cast, classify_cast, CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_struct id attr b ofs =>
      simp [sem_cast, classify_cast, CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_union id attr b ofs =>
      simp [sem_cast, classify_cast, CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_void v =>
      simp [sem_cast, classify_cast, CompCert4Lean.X86_64.Archi.ptr64]

theorem val_casted_has_argtype : val_casted_has_argtypeStatement := by
  intro v ty h
  cases h with
  | val_casted_int sz si attr n hcast =>
      cases sz with
      | I8 =>
          cases si with
          | Signed =>
              change n = Int.sign_ext (zOfNat 8) n
              exact hcast.symm
          | Unsigned =>
              change n = Int.zero_ext (zOfNat 8) n
              exact hcast.symm
      | I16 =>
          cases si with
          | Signed =>
              change n = Int.sign_ext (zOfNat 16) n
              exact hcast.symm
          | Unsigned =>
              change n = Int.zero_ext (zOfNat 16) n
              exact hcast.symm
      | I32 =>
          simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
            CompCert4Lean.Common.Values.Val.has_argtype]
      | IBool =>
          cases hb : boolEqInt n Int.zero with
          | false =>
              right
              simpa [hb, cast_int_int] using hcast.symm
          | true =>
              left
              simpa [hb, cast_int_int] using hcast.symm
  | val_casted_float attr n =>
      simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
        CompCert4Lean.Common.Values.Val.has_argtype]
  | val_casted_single attr n =>
      simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
        CompCert4Lean.Common.Values.Val.has_argtype]
  | val_casted_long si attr n =>
      simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
        CompCert4Lean.Common.Values.Val.has_argtype]
  | val_casted_ptr_ptr b ofs ty attr =>
      simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
        CompCert4Lean.Common.Values.Val.has_argtype]
  | val_casted_int_ptr n ty attr hptr64 =>
      simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
        CompCert4Lean.Common.Values.Val.has_argtype, hptr64]
  | val_casted_ptr_int b ofs si attr hptr64 =>
      simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
        CompCert4Lean.Common.Values.Val.has_argtype, hptr64]
  | val_casted_long_ptr n ty attr hptr64 =>
      simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
        CompCert4Lean.Common.Values.Val.has_argtype, hptr64]
  | val_casted_ptr_long b ofs si attr hptr64 =>
      simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
        CompCert4Lean.Common.Values.Val.has_argtype, hptr64]
  | val_casted_struct id attr b ofs =>
      simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
        CompCert4Lean.Common.Values.Val.has_argtype]
  | val_casted_union id attr b ofs =>
      simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
        CompCert4Lean.Common.Values.Val.has_argtype]
  | val_casted_void v =>
      simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
        CompCert4Lean.Common.Values.Val.has_argtype]

end CompCert4Lean.Cfrontend.Cop
