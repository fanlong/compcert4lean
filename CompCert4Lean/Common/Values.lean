import CompCert4Lean.Common.AST
import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Floats
import CompCert4Lean.X86_64.Archi

/-!
  Definition-bearing translation of `common/Values.v`.

  The computational definitions below preserve the source-visible shape.  The
  proof declarations selected for later migration are represented by named
  proposition descriptors at the end of each relevant section.
-/

namespace CompCert4Lean.Common.Values

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Floats

private abbrev comparison := CompCert4Lean.Lib.Integers.comparison

namespace Archi
private abbrev ptr64 := CompCert4Lean.X86_64.Archi.ptr64
end Archi

namespace Int
private abbrev repr := CompCert4Lean.Lib.Integers.Int.repr
private abbrev unsigned := CompCert4Lean.Lib.Integers.Int.unsigned
private abbrev signed := CompCert4Lean.Lib.Integers.Int.signed
private abbrev zero := CompCert4Lean.Lib.Integers.Int.zero
private abbrev one := CompCert4Lean.Lib.Integers.Int.one
private abbrev mone := CompCert4Lean.Lib.Integers.Int.mone
private abbrev iwordsize := CompCert4Lean.Lib.Integers.Int.iwordsize
private abbrev eq := CompCert4Lean.Lib.Integers.Int.eq
private abbrev lt := CompCert4Lean.Lib.Integers.Int.lt
private abbrev ltu := CompCert4Lean.Lib.Integers.Int.ltu
private abbrev neg := CompCert4Lean.Lib.Integers.Int.neg
private abbrev add := CompCert4Lean.Lib.Integers.Int.add
private abbrev sub := CompCert4Lean.Lib.Integers.Int.sub
private abbrev mul := CompCert4Lean.Lib.Integers.Int.mul
private abbrev divs := CompCert4Lean.Lib.Integers.Int.divs
private abbrev mods := CompCert4Lean.Lib.Integers.Int.mods
private abbrev divu := CompCert4Lean.Lib.Integers.Int.divu
private abbrev modu := CompCert4Lean.Lib.Integers.Int.modu
private abbrev negative := CompCert4Lean.Lib.Integers.Int.negative
private abbrev add_carry := CompCert4Lean.Lib.Integers.Int.add_carry
private abbrev sub_overflow := CompCert4Lean.Lib.Integers.Int.sub_overflow
private abbrev mulhs := CompCert4Lean.Lib.Integers.Int.mulhs
private abbrev mulhu := CompCert4Lean.Lib.Integers.Int.mulhu
private abbrev min_signed := CompCert4Lean.Lib.Integers.Int.min_signed
private abbrev and := CompCert4Lean.Lib.Integers.Int.and
private abbrev or := CompCert4Lean.Lib.Integers.Int.or
private abbrev xor := CompCert4Lean.Lib.Integers.Int.xor
private abbrev not := CompCert4Lean.Lib.Integers.Int.not
private abbrev shl := CompCert4Lean.Lib.Integers.Int.shl
private abbrev shru := CompCert4Lean.Lib.Integers.Int.shru
private abbrev shr := CompCert4Lean.Lib.Integers.Int.shr
private abbrev rol := CompCert4Lean.Lib.Integers.Int.rol
private abbrev ror := CompCert4Lean.Lib.Integers.Int.ror
private abbrev shrx := CompCert4Lean.Lib.Integers.Int.shrx
end Int

namespace Int64
private abbrev repr := CompCert4Lean.Lib.Integers.Int64.repr
private abbrev unsigned := CompCert4Lean.Lib.Integers.Int64.unsigned
private abbrev signed := CompCert4Lean.Lib.Integers.Int64.signed
private abbrev zero := CompCert4Lean.Lib.Integers.Int64.zero
private abbrev one := CompCert4Lean.Lib.Integers.Int64.one
private abbrev mone := CompCert4Lean.Lib.Integers.Int64.mone
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
private abbrev mods := CompCert4Lean.Lib.Integers.Int64.mods
private abbrev divu := CompCert4Lean.Lib.Integers.Int64.divu
private abbrev modu := CompCert4Lean.Lib.Integers.Int64.modu
private abbrev negative := CompCert4Lean.Lib.Integers.Int64.negative
private abbrev add_carry := CompCert4Lean.Lib.Integers.Int64.add_carry
private abbrev sub_overflow := CompCert4Lean.Lib.Integers.Int64.sub_overflow
private abbrev mulhs := CompCert4Lean.Lib.Integers.Int64.mulhs
private abbrev mulhu := CompCert4Lean.Lib.Integers.Int64.mulhu
private abbrev min_signed := CompCert4Lean.Lib.Integers.Int64.min_signed
private abbrev and := CompCert4Lean.Lib.Integers.Int64.and
private abbrev or := CompCert4Lean.Lib.Integers.Int64.or
private abbrev xor := CompCert4Lean.Lib.Integers.Int64.xor
private abbrev not := CompCert4Lean.Lib.Integers.Int64.not
private abbrev shl' := CompCert4Lean.Lib.Integers.Int64.shl'
private abbrev shru' := CompCert4Lean.Lib.Integers.Int64.shru'
private abbrev shr' := CompCert4Lean.Lib.Integers.Int64.shr'
private abbrev rol := CompCert4Lean.Lib.Integers.Int64.rol
private abbrev ror := CompCert4Lean.Lib.Integers.Int64.ror
private abbrev shrx' := CompCert4Lean.Lib.Integers.Int64.shrx'
private abbrev loword := CompCert4Lean.Lib.Integers.Int64.loword
private abbrev hiword := CompCert4Lean.Lib.Integers.Int64.hiword
private abbrev ofwords := CompCert4Lean.Lib.Integers.Int64.ofwords
private abbrev mul' := CompCert4Lean.Lib.Integers.Int64.mul'
end Int64

namespace Float
private abbrev neg := CompCert4Lean.Lib.Floats.Float.neg
private abbrev abs := CompCert4Lean.Lib.Floats.Float.abs
private abbrev add := CompCert4Lean.Lib.Floats.Float.add
private abbrev sub := CompCert4Lean.Lib.Floats.Float.sub
private abbrev mul := CompCert4Lean.Lib.Floats.Float.mul
private abbrev div := CompCert4Lean.Lib.Floats.Float.div
private abbrev cmp := CompCert4Lean.Lib.Floats.Float.cmp
private abbrev to_int := CompCert4Lean.Lib.Floats.Float.to_int
private abbrev to_intu := CompCert4Lean.Lib.Floats.Float.to_intu
private abbrev to_long := CompCert4Lean.Lib.Floats.Float.to_long
private abbrev to_longu := CompCert4Lean.Lib.Floats.Float.to_longu
private abbrev of_int := CompCert4Lean.Lib.Floats.Float.of_int
private abbrev of_intu := CompCert4Lean.Lib.Floats.Float.of_intu
private abbrev of_long := CompCert4Lean.Lib.Floats.Float.of_long
private abbrev of_longu := CompCert4Lean.Lib.Floats.Float.of_longu
private abbrev to_single := CompCert4Lean.Lib.Floats.Float.to_single
private abbrev of_single := CompCert4Lean.Lib.Floats.Float.of_single
end Float

namespace Float32
private abbrev neg := CompCert4Lean.Lib.Floats.Float32.neg
private abbrev abs := CompCert4Lean.Lib.Floats.Float32.abs
private abbrev add := CompCert4Lean.Lib.Floats.Float32.add
private abbrev sub := CompCert4Lean.Lib.Floats.Float32.sub
private abbrev mul := CompCert4Lean.Lib.Floats.Float32.mul
private abbrev div := CompCert4Lean.Lib.Floats.Float32.div
private abbrev cmp := CompCert4Lean.Lib.Floats.Float32.cmp
private abbrev to_int := CompCert4Lean.Lib.Floats.Float32.to_int
private abbrev to_intu := CompCert4Lean.Lib.Floats.Float32.to_intu
private abbrev to_long := CompCert4Lean.Lib.Floats.Float32.to_long
private abbrev to_longu := CompCert4Lean.Lib.Floats.Float32.to_longu
private abbrev of_int := CompCert4Lean.Lib.Floats.Float32.of_int
private abbrev of_intu := CompCert4Lean.Lib.Floats.Float32.of_intu
private abbrev of_long := CompCert4Lean.Lib.Floats.Float32.of_long
private abbrev of_longu := CompCert4Lean.Lib.Floats.Float32.of_longu
end Float32

private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev CCInt64 := CompCert4Lean.Lib.Integers.int64
private abbrev Ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev CCFloat := CompCert4Lean.Lib.Floats.float
private abbrev CCFloat32 := CompCert4Lean.Lib.Floats.float32

private abbrev z0 : Z := ZArith.BinInt.Z.Z0
private abbrev z1 : Z := ZArith.BinInt.Z.Zpos xH
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zMul := ZArith.BinInt.Z.mul
private abbrev zOpp := ZArith.BinInt.Z.opp
private abbrev zDiv := ZArith.BinInt.Z.div
private abbrev zQuot := ZArith.BinInt.Z.quot
private abbrev zMod := ZArith.BinInt.Z.modulo
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLtb := ZArith.BinInt.Z.ltb
private abbrev zTwoP := two_p
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

private def boolOfSumbool {P Q : Prop} (d : Sumbool P Q) : Bool :=
  match d with
  | .left _ => true
  | .right _ => false

private abbrev intZeroExt := CompCert4Lean.Lib.Integers.Int.zero_ext

private abbrev intSignExt := CompCert4Lean.Lib.Integers.Int.sign_ext

private abbrev int64SignExt := CompCert4Lean.Lib.Integers.Int64.sign_ext

private def intMulhs (x y : CCInt) : CCInt := Int.mulhs x y
private def intMulhu (x y : CCInt) : CCInt := Int.mulhu x y
private def int64Mulhs (x y : CCInt64) : CCInt64 := Int64.mulhs x y
private def int64Mulhu (x y : CCInt64) : CCInt64 := Int64.mulhu x y
private def intShrCarry (x y : CCInt) : CCInt := Int.shr x y
private def int64ShrCarry (x : CCInt64) (y : CCInt) : CCInt64 := Int64.shr' x y
private def intRolm (x amount mask : CCInt) : CCInt := Int.or (Int.rol x amount) mask
private def int64Rolm (x amount : CCInt) (mask : CCInt64) : CCInt64 :=
  Int64.or (Int64.rol (Int64.repr (Int.unsigned x)) (Int64.repr (Int.unsigned amount))) mask

def block : Type := positive

instance : DecidableEq block := by
  change DecidableEq positive
  exact inferInstance

def eq_block (x y : block) : Sumbool (x = y) (x ≠ y) :=
  CompCert4Lean.Lib.Coqlib.peq x y

inductive val : Type where
  | Vundef : val
  | Vint : CCInt → val
  | Vlong : CCInt64 → val
  | Vfloat : CCFloat → val
  | Vsingle : CCFloat32 → val
  | Vptr : block → Ptrofs → val
deriving DecidableEq

export val (Vundef Vint Vlong Vfloat Vsingle Vptr)

def Vzero : val := Vint Int.zero
def Vone : val := Vint Int.one
def Vtrue : val := Vint Int.one
def Vfalse : val := Vint Int.zero

def Vnullptr : val := if CompCert4Lean.X86_64.Archi.ptr64 then Vlong Int64.zero else Vint Int.zero

def Vptrofs (n : Ptrofs) : val :=
  if CompCert4Lean.X86_64.Archi.ptr64 then Vlong (Ptrofs.to_int64 n) else Vint (Ptrofs.to_int n)

namespace Val

def eq (x y : val) : Sumbool (x = y) (x ≠ y) := by
  by_cases h : x = y
  · exact .left h
  · exact .right h

def has_type (v : val) (t : typ) : Prop :=
  match v, t with
  | Vundef, _ => True
  | Vint _, Tint => True
  | Vlong _, Tlong => True
  | Vfloat _, Tfloat => True
  | Vsingle _, Tsingle => True
  | Vptr _ _, Tint => CompCert4Lean.X86_64.Archi.ptr64 = false
  | Vptr _ _, Tlong => CompCert4Lean.X86_64.Archi.ptr64 = true
  | Vint _, Tany32 | Vsingle _, Tany32 => True
  | Vptr _ _, Tany32 => CompCert4Lean.X86_64.Archi.ptr64 = false
  | _, Tany64 => True
  | _, _ => False

def has_type_list : List val → List typ → Prop
  | [], [] => True
  | v :: vs, t :: ts => has_type v t ∧ has_type_list vs ts
  | _, _ => False

def Vptr_has_typeStatement : Prop := ∀ b ofs, has_type (Vptr b ofs) Tptr
def Vnullptr_has_typeStatement : Prop := has_type Vnullptr Tptr

def has_argtype (v : val) (x : xtype) : Prop :=
  match x, v with
  | Xbool, Vint n => n = Int.zero ∨ n = Int.one
  | Xint8signed, Vint n => n = intSignExt (zOfNat 8) n
  | Xint8unsigned, Vint n => n = intZeroExt (zOfNat 8) n
  | Xint16signed, Vint n => n = intSignExt (zOfNat 16) n
  | Xint16unsigned, Vint n => n = intZeroExt (zOfNat 16) n
  | Xint, Vint _ => True
  | Xint, Vptr _ _ => CompCert4Lean.X86_64.Archi.ptr64 = false
  | Xlong, Vlong _ => True
  | Xlong, Vptr _ _ => CompCert4Lean.X86_64.Archi.ptr64 = true
  | Xfloat, Vfloat _ => True
  | Xsingle, Vsingle _ => True
  | Xptr, Vptr _ _ => True
  | Xptr, Vint _ => CompCert4Lean.X86_64.Archi.ptr64 = false
  | Xptr, Vlong _ => CompCert4Lean.X86_64.Archi.ptr64 = true
  | Xany32, Vint _ | Xany32, Vsingle _ => True
  | Xany32, Vptr _ _ => CompCert4Lean.X86_64.Archi.ptr64 = false
  | Xany64, Vint _ | Xany64, Vlong _ | Xany64, Vptr _ _
  | Xany64, Vsingle _ | Xany64, Vfloat _ => True
  | Xvoid, _ => True
  | _, _ => False

def has_argtype_list (vl : List val) (xl : List xtype) : Prop :=
  CompCert4Lean.Lib.Coqlib.list_forall2 has_argtype vl xl

def has_rettype (v : val) (r : xtype) : Prop :=
  match r, v with
  | Xbool, Vint n => n = Int.zero ∨ n = Int.one
  | Xint8signed, Vint n => n = intSignExt (zOfNat 8) n
  | Xint8unsigned, Vint n => n = intZeroExt (zOfNat 8) n
  | Xint16signed, Vint n => n = intSignExt (zOfNat 16) n
  | Xint16unsigned, Vint n => n = intZeroExt (zOfNat 16) n
  | Xint, Vint _ => True
  | Xint, Vptr _ _ => CompCert4Lean.X86_64.Archi.ptr64 = false
  | Xlong, Vlong _ => True
  | Xlong, Vptr _ _ => CompCert4Lean.X86_64.Archi.ptr64 = true
  | Xfloat, Vfloat _ => True
  | Xsingle, Vsingle _ => True
  | Xptr, Vptr _ _ => True
  | Xptr, Vint _ => CompCert4Lean.X86_64.Archi.ptr64 = false
  | Xptr, Vlong _ => CompCert4Lean.X86_64.Archi.ptr64 = true
  | Xany32, Vint _ | Xany32, Vsingle _ => True
  | Xany32, Vptr _ _ => CompCert4Lean.X86_64.Archi.ptr64 = false
  | Xany64, _ => True
  | _, Vundef => True
  | _, _ => False

def has_subtypeStatement : Prop :=
  ∀ ty1 ty2 v,
    subtype ty1 ty2 = true → has_type v ty1 → has_type v ty2

def has_proj_xtypeStatement : Prop :=
  ∀ v t, has_rettype v t → has_type v (proj_xtype t)

def has_inj_typeStatement : Prop :=
  ∀ v t, has_type v t → has_rettype v (inj_type t)

inductive bool_of_val : val → Bool → Prop where
  | bool_of_val_int (n : CCInt) : bool_of_val (Vint n) (!(Int.eq n Int.zero))

abbrev bool_of_val_int (n : CCInt) : bool_of_val (Vint n) (!(Int.eq n Int.zero)) :=
  @bool_of_val.bool_of_val_int n

def neg (v : val) : val := match v with | Vint n => Vint (Int.neg n) | _ => Vundef
def negf (v : val) : val := match v with | Vfloat f => Vfloat (Float.neg f) | _ => Vundef
def absf (v : val) : val := match v with | Vfloat f => Vfloat (Float.abs f) | _ => Vundef
def negfs (v : val) : val := match v with | Vsingle f => Vsingle (Float32.neg f) | _ => Vundef
def absfs (v : val) : val := match v with | Vsingle f => Vsingle (Float32.abs f) | _ => Vundef
def maketotal (ov : Option val) : val := match ov with | some v => v | none => Vundef
def intoffloat (v : val) : Option val := match v with | Vfloat f => (Float.to_int f).map Vint | _ => none
def intuoffloat (v : val) : Option val := match v with | Vfloat f => (Float.to_intu f).map Vint | _ => none
def floatofint (v : val)
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (zOfNat 53) (zOfNat 1024)] : Option val :=
  match v with | Vint n => some (Vfloat (Float.of_int n)) | _ => none
def floatofintu (v : val)
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (zOfNat 53) (zOfNat 1024)] : Option val :=
  match v with | Vint n => some (Vfloat (Float.of_intu n)) | _ => none
def intofsingle (v : val) : Option val := match v with | Vsingle f => (Float32.to_int f).map Vint | _ => none
def intuofsingle (v : val) : Option val := match v with | Vsingle f => (Float32.to_intu f).map Vint | _ => none
def singleofint (v : val)
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (zOfNat 24) (zOfNat 128)] : Option val :=
  match v with | Vint n => some (Vsingle (Float32.of_int n)) | _ => none
def singleofintu (v : val)
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (zOfNat 24) (zOfNat 128)] : Option val :=
  match v with | Vint n => some (Vsingle (Float32.of_intu n)) | _ => none
def negint (v : val) : val := match v with | Vint n => Vint (Int.neg n) | _ => Vundef
def notint (v : val) : val := match v with | Vint n => Vint (Int.not n) | _ => Vundef
def of_bool (b : Bool) : val := if b then Vtrue else Vfalse
def is_bool (v : val) : Bool := boolOfSumbool (eq v Vtrue) || boolOfSumbool (eq v Vfalse)
def norm_bool (v : val) : val := if is_bool v then v else Vundef
def zero_ext (nbits : Z) (v : val) : val := match v with | Vint n => Vint (intZeroExt nbits n) | _ => Vundef
def sign_ext (nbits : Z) (v : val) : val := match v with | Vint n => Vint (intSignExt nbits n) | _ => Vundef
def singleoffloat (v : val) : val := match v with | Vfloat f => Vsingle (Float.to_single f) | _ => Vundef
def floatofsingle (v : val) : val := match v with | Vsingle f => Vfloat (Float.of_single f) | _ => Vundef

def add (v1 v2 : val) : val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint (Int.add n1 n2)
  | Vptr b ofs, Vint n => if Archi.ptr64 then Vundef else Vptr b (Ptrofs.add ofs (Ptrofs.of_int n))
  | Vint n, Vptr b ofs => if Archi.ptr64 then Vundef else Vptr b (Ptrofs.add ofs (Ptrofs.of_int n))
  | _, _ => Vundef

def sub (v1 v2 : val) : val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint (Int.sub n1 n2)
  | Vptr b ofs, Vint n => if Archi.ptr64 then Vundef else Vptr b (Ptrofs.sub ofs (Ptrofs.of_int n))
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if Archi.ptr64 then Vundef else
        if boolOfSumbool (eq_block b1 b2) then
          Vint (Ptrofs.to_int (Ptrofs.sub ofs1 ofs2))
        else Vundef
  | _, _ => Vundef

def mul (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => Vint (Int.mul n1 n2) | _, _ => Vundef
def mulhs (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => Vint (intMulhs n1 n2) | _, _ => Vundef
def mulhu (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => Vint (intMulhu n1 n2) | _, _ => Vundef

def divs (v1 v2 : val) : Option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero ||
          (Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone)
      then none
      else some (Vint (Int.divs n1 n2))
  | _, _ => none
def mods (v1 v2 : val) : Option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero ||
          (Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone)
      then none
      else some (Vint (Int.mods n1 n2))
  | _, _ => none
def divu (v1 v2 : val) : Option val :=
  match v1, v2 with
  | Vint n1, Vint n2 => if Int.eq n2 Int.zero then none else some (Vint (Int.divu n1 n2))
  | _, _ => none
def modu (v1 v2 : val) : Option val :=
  match v1, v2 with
  | Vint n1, Vint n2 => if Int.eq n2 Int.zero then none else some (Vint (Int.modu n1 n2))
  | _, _ => none

def sub_overflow (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => Vint (Int.sub_overflow n1 n2 Int.zero) | _, _ => Vundef
def negative (v : val) : val := match v with | Vint n => Vint (Int.negative n) | _ => Vundef
def and (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => Vint (Int.and n1 n2) | _, _ => Vundef
def or (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => Vint (Int.or n1 n2) | _, _ => Vundef
def xor (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => Vint (Int.xor n1 n2) | _, _ => Vundef
def shl (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => if Int.ltu n2 Int.iwordsize then Vint (Int.shl n1 n2) else Vundef | _, _ => Vundef
def shr (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => if Int.ltu n2 Int.iwordsize then Vint (Int.shr n1 n2) else Vundef | _, _ => Vundef
def shru (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => if Int.ltu n2 Int.iwordsize then Vint (Int.shru n1 n2) else Vundef | _, _ => Vundef
def shrx (v1 v2 : val) : Option val := match v1, v2 with | Vint n1, Vint n2 => if Int.ltu n2 (Int.repr (zOfNat 31)) then some (Vint (Int.shrx n1 n2)) else none | _, _ => none
def ror (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => Vint (Int.ror n1 n2) | _, _ => Vundef

def addf (v1 v2 : val) : val := match v1, v2 with | Vfloat f1, Vfloat f2 => Vfloat (Float.add f1 f2) | _, _ => Vundef
def subf (v1 v2 : val) : val := match v1, v2 with | Vfloat f1, Vfloat f2 => Vfloat (Float.sub f1 f2) | _, _ => Vundef
def mulf (v1 v2 : val) : val := match v1, v2 with | Vfloat f1, Vfloat f2 => Vfloat (Float.mul f1 f2) | _, _ => Vundef
def divf (v1 v2 : val) : val := match v1, v2 with | Vfloat f1, Vfloat f2 => Vfloat (Float.div f1 f2) | _, _ => Vundef
def addfs (v1 v2 : val) : val := match v1, v2 with | Vsingle f1, Vsingle f2 => Vsingle (Float32.add f1 f2) | _, _ => Vundef
def subfs (v1 v2 : val) : val := match v1, v2 with | Vsingle f1, Vsingle f2 => Vsingle (Float32.sub f1 f2) | _, _ => Vundef
def mulfs (v1 v2 : val) : val := match v1, v2 with | Vsingle f1, Vsingle f2 => Vsingle (Float32.mul f1 f2) | _, _ => Vundef
def divfs (v1 v2 : val) : val := match v1, v2 with | Vsingle f1, Vsingle f2 => Vsingle (Float32.div f1 f2) | _, _ => Vundef

def longofwords (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => Vlong (Int64.ofwords n1 n2) | _, _ => Vundef
def loword (v : val) : val := match v with | Vlong n => Vint (Int64.loword n) | _ => Vundef
def hiword (v : val) : val := match v with | Vlong n => Vint (Int64.hiword n) | _ => Vundef
def negl (v : val) : val := match v with | Vlong n => Vlong (Int64.neg n) | _ => Vundef
def notl (v : val) : val := match v with | Vlong n => Vlong (Int64.not n) | _ => Vundef
def longofint (v : val) : val := match v with | Vint n => Vlong (Int64.repr (Int.signed n)) | _ => Vundef
def longofintu (v : val) : val := match v with | Vint n => Vlong (Int64.repr (Int.unsigned n)) | _ => Vundef
def longoffloat (v : val) : Option val := match v with | Vfloat f => (Float.to_long f).map Vlong | _ => none
def longuoffloat (v : val) : Option val := match v with | Vfloat f => (Float.to_longu f).map Vlong | _ => none
def longofsingle (v : val) : Option val := match v with | Vsingle f => (Float32.to_long f).map Vlong | _ => none
def longuofsingle (v : val) : Option val := match v with | Vsingle f => (Float32.to_longu f).map Vlong | _ => none
def floatoflong (v : val)
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (zOfNat 53) (zOfNat 1024)] : Option val :=
  match v with | Vlong n => some (Vfloat (Float.of_long n)) | _ => none
def floatoflongu (v : val)
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (zOfNat 53) (zOfNat 1024)] : Option val :=
  match v with | Vlong n => some (Vfloat (Float.of_longu n)) | _ => none
def singleoflong (v : val)
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (zOfNat 24) (zOfNat 128)] : Option val :=
  match v with | Vlong n => some (Vsingle (Float32.of_long n)) | _ => none
def singleoflongu (v : val)
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (zOfNat 24) (zOfNat 128)] : Option val :=
  match v with | Vlong n => some (Vsingle (Float32.of_longu n)) | _ => none

def addl (v1 v2 : val) : val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong (Int64.add n1 n2)
  | Vptr b ofs, Vlong n => if Archi.ptr64 then Vptr b (Ptrofs.add ofs (Ptrofs.of_int64 n)) else Vundef
  | Vlong n, Vptr b ofs => if Archi.ptr64 then Vptr b (Ptrofs.add ofs (Ptrofs.of_int64 n)) else Vundef
  | _, _ => Vundef
def subl (v1 v2 : val) : val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong (Int64.sub n1 n2)
  | Vptr b ofs, Vlong n => if Archi.ptr64 then Vptr b (Ptrofs.sub ofs (Ptrofs.of_int64 n)) else Vundef
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if !Archi.ptr64 then Vundef
      else if boolOfSumbool (eq_block b1 b2) then
        Vlong (Ptrofs.to_int64 (Ptrofs.sub ofs1 ofs2))
      else Vundef
  | _, _ => Vundef
def mull (v1 v2 : val) : val := match v1, v2 with | Vlong n1, Vlong n2 => Vlong (Int64.mul n1 n2) | _, _ => Vundef
def mull' (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => Vlong (Int64.mul' n1 n2) | _, _ => Vundef
def mullhs (v1 v2 : val) : val := match v1, v2 with | Vlong n1, Vlong n2 => Vlong (int64Mulhs n1 n2) | _, _ => Vundef
def mullhu (v1 v2 : val) : val := match v1, v2 with | Vlong n1, Vlong n2 => Vlong (int64Mulhu n1 n2) | _, _ => Vundef
def divls (v1 v2 : val) : Option val := match v1, v2 with | Vlong n1, Vlong n2 => if Int64.eq n2 Int64.zero || (Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone) then none else some (Vlong (Int64.divs n1 n2)) | _, _ => none
def modls (v1 v2 : val) : Option val := match v1, v2 with | Vlong n1, Vlong n2 => if Int64.eq n2 Int64.zero || (Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone) then none else some (Vlong (Int64.mods n1 n2)) | _, _ => none
def divlu (v1 v2 : val) : Option val := match v1, v2 with | Vlong n1, Vlong n2 => if Int64.eq n2 Int64.zero then none else some (Vlong (Int64.divu n1 n2)) | _, _ => none
def modlu (v1 v2 : val) : Option val := match v1, v2 with | Vlong n1, Vlong n2 => if Int64.eq n2 Int64.zero then none else some (Vlong (Int64.modu n1 n2)) | _, _ => none
def subl_overflow (v1 v2 : val) : val := match v1, v2 with | Vlong n1, Vlong n2 => Vint (Int.repr (Int64.unsigned (Int64.sub_overflow n1 n2 Int64.zero))) | _, _ => Vundef
def negativel (v : val) : val := match v with | Vlong n => Vint (Int.repr (Int64.unsigned (Int64.negative n))) | _ => Vundef
def andl (v1 v2 : val) : val := match v1, v2 with | Vlong n1, Vlong n2 => Vlong (Int64.and n1 n2) | _, _ => Vundef
def orl (v1 v2 : val) : val := match v1, v2 with | Vlong n1, Vlong n2 => Vlong (Int64.or n1 n2) | _, _ => Vundef
def xorl (v1 v2 : val) : val := match v1, v2 with | Vlong n1, Vlong n2 => Vlong (Int64.xor n1 n2) | _, _ => Vundef
def shll (v1 v2 : val) : val := match v1, v2 with | Vlong n1, Vint n2 => if Int.ltu n2 Int64.iwordsize' then Vlong (Int64.shl' n1 n2) else Vundef | _, _ => Vundef
def shrl (v1 v2 : val) : val := match v1, v2 with | Vlong n1, Vint n2 => if Int.ltu n2 Int64.iwordsize' then Vlong (Int64.shr' n1 n2) else Vundef | _, _ => Vundef
def shrlu (v1 v2 : val) : val := match v1, v2 with | Vlong n1, Vint n2 => if Int.ltu n2 Int64.iwordsize' then Vlong (Int64.shru' n1 n2) else Vundef | _, _ => Vundef
def shrxl (v1 v2 : val) : Option val := match v1, v2 with | Vlong n1, Vint n2 => if Int.ltu n2 (Int.repr (zOfNat 63)) then some (Vlong (Int64.shrx' n1 n2)) else none | _, _ => none
def rorl (v1 v2 : val) : val := match v1, v2 with | Vlong n1, Vint n2 => Vlong (Int64.ror n1 (Int64.repr (Int.unsigned n2))) | _, _ => Vundef

def cmp_bool (c : comparison) (v1 v2 : val) : Option Bool :=
  match v1, v2 with
  | Vint n1, Vint n2 => some (CompCert4Lean.Lib.Integers.Int.cmp c n1 n2)
  | _, _ => none
def cmp_different_blocks (c : comparison) : Option Bool := match c with | .Ceq => some false | .Cne => some true | _ => none
def cmpu_bool (valid_ptr : block → Z → Bool) (c : comparison) (v1 v2 : val) : Option Bool :=
  match v1, v2 with
  | Vint n1, Vint n2 => some (CompCert4Lean.Lib.Integers.Int.cmpu c n1 n2)
  | Vint n, Vptr b ofs => if !Archi.ptr64 && Int.eq n Int.zero && (valid_ptr b (Ptrofs.unsigned ofs) || valid_ptr b (zSub (Ptrofs.unsigned ofs) z1)) then cmp_different_blocks c else none
  | Vptr b ofs, Vint n => if !Archi.ptr64 && Int.eq n Int.zero && (valid_ptr b (Ptrofs.unsigned ofs) || valid_ptr b (zSub (Ptrofs.unsigned ofs) z1)) then cmp_different_blocks c else none
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if !Archi.ptr64 then
        if boolOfSumbool (eq_block b1 b2) then
          if (valid_ptr b1 (Ptrofs.unsigned ofs1) || valid_ptr b1 (zSub (Ptrofs.unsigned ofs1) z1)) &&
             (valid_ptr b2 (Ptrofs.unsigned ofs2) || valid_ptr b2 (zSub (Ptrofs.unsigned ofs2) z1))
          then some (CompCert4Lean.Lib.Integers.Ptrofs.cmpu c ofs1 ofs2) else none
        else if valid_ptr b1 (Ptrofs.unsigned ofs1) && valid_ptr b2 (Ptrofs.unsigned ofs2) then cmp_different_blocks c else none
      else none
  | _, _ => none
def cmpf_bool (c : comparison) (v1 v2 : val) : Option Bool := match v1, v2 with | Vfloat f1, Vfloat f2 => some (Float.cmp c f1 f2) | _, _ => none
def cmpfs_bool (c : comparison) (v1 v2 : val) : Option Bool := match v1, v2 with | Vsingle f1, Vsingle f2 => some (Float32.cmp c f1 f2) | _, _ => none
def cmpl_bool (c : comparison) (v1 v2 : val) : Option Bool :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => some (CompCert4Lean.Lib.Integers.Int64.cmp c n1 n2)
  | _, _ => none
def cmplu_bool (valid_ptr : block → Z → Bool) (c : comparison) (v1 v2 : val) : Option Bool :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => some (CompCert4Lean.Lib.Integers.Int64.cmpu c n1 n2)
  | Vlong n, Vptr b ofs =>
      if Archi.ptr64 && Int64.eq n Int64.zero &&
        (valid_ptr b (Ptrofs.unsigned ofs) || valid_ptr b (zSub (Ptrofs.unsigned ofs) z1))
      then cmp_different_blocks c else none
  | Vptr b ofs, Vlong n =>
      if Archi.ptr64 && Int64.eq n Int64.zero &&
        (valid_ptr b (Ptrofs.unsigned ofs) || valid_ptr b (zSub (Ptrofs.unsigned ofs) z1))
      then cmp_different_blocks c else none
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if Archi.ptr64 then
        if boolOfSumbool (eq_block b1 b2) then
          if (valid_ptr b1 (Ptrofs.unsigned ofs1) || valid_ptr b1 (zSub (Ptrofs.unsigned ofs1) z1)) &&
             (valid_ptr b2 (Ptrofs.unsigned ofs2) || valid_ptr b2 (zSub (Ptrofs.unsigned ofs2) z1))
          then some (CompCert4Lean.Lib.Integers.Ptrofs.cmpu c ofs1 ofs2) else none
        else if valid_ptr b1 (Ptrofs.unsigned ofs1) && valid_ptr b2 (Ptrofs.unsigned ofs2)
        then cmp_different_blocks c else none
      else none
  | _, _ => none
def of_optbool (ob : Option Bool) : val := match ob with | some true => Vtrue | some false => Vfalse | none => Vundef
def cmp (c : comparison) (v1 v2 : val) : val := of_optbool (cmp_bool c v1 v2)
def cmpu (valid_ptr : block → Z → Bool) (c : comparison) (v1 v2 : val) : val := of_optbool (cmpu_bool valid_ptr c v1 v2)
def cmpf (c : comparison) (v1 v2 : val) : val := of_optbool (cmpf_bool c v1 v2)
def cmpfs (c : comparison) (v1 v2 : val) : val := of_optbool (cmpfs_bool c v1 v2)
def cmpl (c : comparison) (v1 v2 : val) : Option val := (cmpl_bool c v1 v2).map of_bool
def cmplu (valid_ptr : block → Z → Bool) (c : comparison) (v1 v2 : val) : Option val := (cmplu_bool valid_ptr c v1 v2).map of_bool
def maskzero_bool (v : val) (mask : CCInt) : Option Bool := match v with | Vint n => some (Int.eq (Int.and n mask) Int.zero) | _ => none

def offset_ptr (v : val) (delta : Ptrofs) : val := match v with | Vptr b ofs => Vptr b (Ptrofs.add ofs delta) | _ => Vundef
def normalize (v : val) (ty : typ) : val :=
  match v, ty with
  | Vundef, _ => Vundef
  | Vint _, Tint | Vlong _, Tlong | Vfloat _, Tfloat | Vsingle _, Tsingle => v
  | Vptr _ _, Tint | Vptr _ _, Tany32 => if Archi.ptr64 then Vundef else v
  | Vptr _ _, Tlong => if Archi.ptr64 then v else Vundef
  | Vint _, Tany32 | Vsingle _, Tany32 => v
  | _, Tany64 => v
  | _, _ => Vundef
def select (cmp : Option Bool) (v1 v2 : val) (ty : typ) : val := match cmp with | some b => normalize (if b then v1 else v2) ty | none => Vundef
def load_result (chunk : memory_chunk) (v : val) : val :=
  match chunk, v with
  | Mbool, Vint n => norm_bool (Vint (intZeroExt (zOfNat 8) n))
  | Mint8signed, Vint n => Vint (intSignExt (zOfNat 8) n)
  | Mint8unsigned, Vint n => Vint (intZeroExt (zOfNat 8) n)
  | Mint16signed, Vint n => Vint (intSignExt (zOfNat 16) n)
  | Mint16unsigned, Vint n => Vint (intZeroExt (zOfNat 16) n)
  | Mint32, Vint n => Vint n
  | Mint32, Vptr b ofs => if Archi.ptr64 then Vundef else Vptr b ofs
  | Mint64, Vlong n => Vlong n
  | Mint64, Vptr b ofs => if Archi.ptr64 then Vptr b ofs else Vundef
  | Mfloat32, Vsingle f => Vsingle f
  | Mfloat64, Vfloat f => Vfloat f
  | Many32, Vint _ | Many32, Vsingle _ => v
  | Many32, Vptr _ _ => if Archi.ptr64 then Vundef else v
  | Many64, _ => v
  | _, _ => Vundef

inductive lessdef : val → val → Prop where
  | lessdef_refl (v : val) : lessdef v v
  | lessdef_undef (v : val) : lessdef Vundef v

abbrev lessdef_refl (v : val) : lessdef v v :=
  @lessdef.lessdef_refl v

abbrev lessdef_undef (v : val) : lessdef Vundef v :=
  @lessdef.lessdef_undef v

inductive lessdef_list : List val → List val → Prop where
  | lessdef_list_nil : lessdef_list [] []
  | lessdef_list_cons (v1 v2 : val) (vl1 vl2 : List val) : lessdef v1 v2 → lessdef_list vl1 vl2 → lessdef_list (v1 :: vl1) (v2 :: vl2)

abbrev lessdef_list_nil : lessdef_list [] [] :=
  @lessdef_list.lessdef_list_nil

abbrev lessdef_list_cons (v1 v2 : val) (vl1 vl2 : List val)
    (hhead : lessdef v1 v2) (htail : lessdef_list vl1 vl2) :
    lessdef_list (v1 :: vl1) (v2 :: vl2) :=
  @lessdef_list.lessdef_list_cons v1 v2 vl1 vl2 hhead htail

def meminj : Type := block → Option (block × Z)

inductive inject (mi : meminj) : val → val → Prop where
  | inject_int (i : CCInt) : inject mi (Vint i) (Vint i)
  | inject_long (i : CCInt64) : inject mi (Vlong i) (Vlong i)
  | inject_float (f : CCFloat) : inject mi (Vfloat f) (Vfloat f)
  | inject_single (f : CCFloat32) : inject mi (Vsingle f) (Vsingle f)
  | inject_ptr (b1 : block) (ofs1 : Ptrofs) (b2 : block) (ofs2 : Ptrofs) (delta : Z) :
      mi b1 = some (b2, delta) →
      ofs2 = Ptrofs.add ofs1 (Ptrofs.repr delta) →
      inject mi (Vptr b1 ofs1) (Vptr b2 ofs2)
  | val_inject_undef (v : val) : inject mi Vundef v

abbrev inject_int (mi : meminj) (i : CCInt) : inject mi (Vint i) (Vint i) :=
  @inject.inject_int mi i

abbrev inject_long (mi : meminj) (i : CCInt64) : inject mi (Vlong i) (Vlong i) :=
  @inject.inject_long mi i

abbrev inject_float (mi : meminj) (f : CCFloat) : inject mi (Vfloat f) (Vfloat f) :=
  @inject.inject_float mi f

abbrev inject_single (mi : meminj) (f : CCFloat32) : inject mi (Vsingle f) (Vsingle f) :=
  @inject.inject_single mi f

abbrev inject_ptr (mi : meminj) (b1 : block) (ofs1 : Ptrofs) (b2 : block)
    (ofs2 : Ptrofs) (delta : Z) (hmap : mi b1 = some (b2, delta))
    (hofs : ofs2 = Ptrofs.add ofs1 (Ptrofs.repr delta)) :
    inject mi (Vptr b1 ofs1) (Vptr b2 ofs2) :=
  @inject.inject_ptr mi b1 ofs1 b2 ofs2 delta hmap hofs

abbrev val_inject_undef (mi : meminj) (v : val) : inject mi Vundef v :=
  @inject.val_inject_undef mi v

def addl_injectStatement : Prop :=
  ∀ (f : meminj) v1 v1' v2 v2',
    inject f v1 v1' →
    inject f v2 v2' →
    inject f (addl v1 v2) (addl v1' v2')

theorem addl_inject : addl_injectStatement := by
  intro f v1 v1' v2 v2' h1 h2
  cases h1 <;> cases h2 <;>
    simp [addl, Archi.ptr64, CompCert4Lean.X86_64.Archi.ptr64] <;>
    constructor <;>
    try assumption
  all_goals
    subst_vars
    rw [Ptrofs.add_assoc_proof_api, Ptrofs.add_assoc_proof_api]
    congr 1
    exact Ptrofs.add_commut_proof_api _ _

def subl_injectStatement : Prop :=
  ∀ (f : meminj) v1 v1' v2 v2',
    inject f v1 v1' →
    inject f v2 v2' →
    inject f (subl v1 v2) (subl v1' v2')

theorem subl_inject : subl_injectStatement := by
  intro f v1 v1' v2 v2' h1 h2
  cases h1 <;> cases h2 <;>
    simp [subl, Archi.ptr64, CompCert4Lean.X86_64.Archi.ptr64] <;>
    try constructor <;>
    try assumption
  case inject_ptr.inject_long.a =>
    subst_vars
    exact Ptrofs.sub_add_l_proof_api _ _ _
  case inject_ptr.inject_ptr =>
    rename_i srcB1 srcOfs1 dstB1 dstOfs1 delta1 map1 ofsEq1
      srcB2 srcOfs2 dstB2 dstOfs2 delta2 map2 ofsEq2
    by_cases hsrc : srcB1 = srcB2
    · subst srcB2
      have hpair : (dstB1, delta1) = (dstB2, delta2) :=
        Option.some.inj (map1.symm.trans map2)
      have hdst : dstB1 = dstB2 := congrArg Prod.fst hpair
      have hdelta : delta1 = delta2 := congrArg Prod.snd hpair
      subst dstB2
      subst delta2
      have hsrcEq : boolOfSumbool (eq_block srcB1 srcB1) = true := by
        cases h : eq_block srcB1 srcB1 with
        | left _ => rfl
        | right hne => exact (hne rfl).elim
      have hdstEq : boolOfSumbool (eq_block dstB1 dstB1) = true := by
        cases h : eq_block dstB1 dstB1 with
        | left _ => rfl
        | right hne => exact (hne rfl).elim
      rw [hsrcEq, hdstEq]
      simp
      rw [ofsEq1, ofsEq2, Ptrofs.sub_shifted_proof_api]
      exact inject.inject_long _
    · have hsrcEq : boolOfSumbool (eq_block srcB1 srcB2) = false := by
        cases h : eq_block srcB1 srcB2 with
        | left heq => exact (hsrc heq).elim
        | right _ => rfl
      rw [hsrcEq]
      exact inject.val_inject_undef _

inductive inject_list (mi : meminj) : List val → List val → Prop where
  | inject_list_nil : inject_list mi [] []
  | inject_list_cons (v1 v2 : val) (vl1 vl2 : List val) :
      inject mi v1 v2 →
      inject_list mi vl1 vl2 →
      inject_list mi (v1 :: vl1) (v2 :: vl2)

abbrev inject_list_nil (mi : meminj) : inject_list mi [] [] :=
  @inject_list.inject_list_nil mi

abbrev inject_list_cons (mi : meminj) (v1 v2 : val) (vl1 vl2 : List val)
    (hhead : inject mi v1 v2) (htail : inject_list mi vl1 vl2) :
    inject_list mi (v1 :: vl1) (v2 :: vl2) :=
  @inject_list.inject_list_cons mi v1 v2 vl1 vl2 hhead htail

def bool_of_val_of_optboolStatement : Prop :=
  ∀ ob b, bool_of_val (of_optbool ob) b → ob = some b

def norm_bool_casesStatement : Prop :=
  ∀ v, norm_bool v = Vundef ∨ norm_bool v = Vfalse ∨ norm_bool v = Vtrue

def norm_bool_idemStatement : Prop :=
  ∀ v, norm_bool (norm_bool v) = norm_bool v

def norm_bool_is_lessdefStatement : Prop :=
  ∀ v, lessdef (norm_bool v) v

def norm_bool_lessdefStatement : Prop :=
  ∀ v1 v2, lessdef v1 v2 → lessdef (norm_bool v1) (norm_bool v2)

def load_result_xtypeStatement : Prop :=
  ∀ chunk v, has_rettype (load_result chunk v) (xtype_of_chunk chunk)

def load_result_typeStatement : Prop :=
  ∀ chunk v, has_type (load_result chunk v) (type_of_chunk chunk)

def load_result_sameStatement : Prop :=
  ∀ v ty, has_type v ty → load_result (chunk_of_type ty) v = v

def load_result_lessdefStatement : Prop :=
  ∀ chunk v1 v2,
    lessdef v1 v2 → lessdef (load_result chunk v1) (load_result chunk v2)

def load_result_injectStatement : Prop :=
  ∀ (f : meminj) chunk v1 v2,
    inject f v1 v2 → inject f (load_result chunk v1) (load_result chunk v2)

def add_commutStatement : Prop :=
  ∀ x y, add x y = add y x

def add_assocStatement : Prop :=
  ∀ x y z, add (add x y) z = add x (add y z)

def add_permutStatement : Prop :=
  ∀ x y z, add x (add y z) = add y (add x z)

def add_permut_4Statement : Prop :=
  ∀ x y z t, add (add x y) (add z t) = add (add x z) (add y t)

def add_lessdefStatement : Prop :=
  ∀ v1 v1' v2 v2',
    lessdef v1 v1' → lessdef v2 v2' → lessdef (add v1 v2) (add v1' v2')

def add_injectStatement : Prop :=
  ∀ (f : meminj) v1 v1' v2 v2',
    inject f v1 v1' →
    inject f v2 v2' →
    inject f (add v1 v2) (add v1' v2')

def sub_add_oppStatement : Prop :=
  ∀ x y, sub x (Vint y) = add x (Vint (Int.neg y))

def sub_add_lStatement : Prop :=
  ∀ v1 v2 i, sub (add v1 (Vint i)) v2 = add (sub v1 v2) (Vint i)

def sub_add_rStatement : Prop :=
  ∀ v1 v2 i,
    sub v1 (add v2 (Vint i)) = add (sub v1 v2) (Vint (Int.neg i))

def sub_injectStatement : Prop :=
  ∀ (f : meminj) v1 v1' v2 v2',
    inject f v1 v1' →
    inject f v2 v2' →
    inject f (sub v1 v2) (sub v1' v2')

def mul_commutStatement : Prop :=
  ∀ x y, mul x y = mul y x

def mul_add_distr_lStatement : Prop :=
  ∀ x y z, mul (add x y) z = add (mul x z) (mul y z)

def mul_add_distr_rStatement : Prop :=
  ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)

def mul_pow2Statement : Prop :=
  ∀ x n logn,
    Int.is_power2 n = some logn →
    mul x (Vint n) = shl x (Vint logn)

def and_commutStatement : Prop :=
  ∀ x y, and x y = and y x

def and_assocStatement : Prop :=
  ∀ x y z, and (and x y) z = and x (and y z)

def or_commutStatement : Prop :=
  ∀ x y, or x y = or y x

def or_assocStatement : Prop :=
  ∀ x y z, or (or x y) z = or x (or y z)

def xor_commutStatement : Prop :=
  ∀ x y, xor x y = xor y x

def xor_assocStatement : Prop :=
  ∀ x y z, xor (xor x y) z = xor x (xor y z)

def not_xorStatement : Prop :=
  ∀ x, notint x = xor x (Vint Int.mone)

def shl_mulStatement : Prop :=
  ∀ x y, mul x (shl Vone y) = shl x y

def addl_commutStatement : Prop :=
  ∀ x y, addl x y = addl y x

def addl_assocStatement : Prop :=
  ∀ x y z, addl (addl x y) z = addl x (addl y z)

def addl_permutStatement : Prop :=
  ∀ x y z, addl x (addl y z) = addl y (addl x z)

def addl_permut_4Statement : Prop :=
  ∀ x y z t, addl (addl x y) (addl z t) = addl (addl x z) (addl y t)

def addl_lessdefStatement : Prop :=
  ∀ v1 v1' v2 v2',
    lessdef v1 v1' → lessdef v2 v2' → lessdef (addl v1 v2) (addl v1' v2')

def andl_commutStatement : Prop :=
  ∀ x y, andl x y = andl y x

def andl_assocStatement : Prop :=
  ∀ x y z, andl (andl x y) z = andl x (andl y z)

def orl_commutStatement : Prop :=
  ∀ x y, orl x y = orl y x

def orl_assocStatement : Prop :=
  ∀ x y z, orl (orl x y) z = orl x (orl y z)

def xorl_commutStatement : Prop :=
  ∀ x y, xorl x y = xorl y x

def xorl_assocStatement : Prop :=
  ∀ x y z, xorl (xorl x y) z = xorl x (xorl y z)

def notl_xorlStatement : Prop :=
  ∀ x, notl x = xorl x (Vlong Int64.mone)

def divs_pow2Statement : Prop :=
  ∀ x n logn y,
    Int.is_power2 n = some logn →
    Int.ltu logn (Int.repr (zOfNat 31)) = true →
    divs x (Vint n) = some y →
    shrx x (Vint logn) = some y

def divs_oneStatement : Prop :=
  ∀ s, divs (Vint s) (Vint Int.one) = some (Vint s)

def divu_pow2Statement : Prop :=
  ∀ x n logn y,
    Int.is_power2 n = some logn →
    divu x (Vint n) = some y →
    shru x (Vint logn) = y

def divu_oneStatement : Prop :=
  ∀ s, divu (Vint s) (Vint Int.one) = some (Vint s)

def divls_pow2Statement : Prop :=
  ∀ x n logn y,
    Int64.is_power2' n = some logn →
    Int.ltu logn (Int.repr (zOfNat 63)) = true →
    divls x (Vlong n) = some y →
    shrxl x (Vint logn) = some y

def divlu_pow2Statement : Prop :=
  ∀ x n logn y,
    Int64.is_power2' n = some logn →
    divlu x (Vlong n) = some y →
    shrlu x (Vint logn) = y

def modlu_pow2Statement : Prop :=
  ∀ x n logn y,
    Int64.is_power2 n = some logn →
    modlu x (Vlong n) = some y →
    andl x (Vlong (Int64.sub n Int64.one)) = y

def mods_divsStatement : Prop :=
  ∀ x y z,
    mods x y = some z → ∃ v, divs x y = some v ∧ z = sub x (mul v y)

def modu_pow2Statement : Prop :=
  ∀ x n logn y,
    Int.is_power2 n = some logn →
    modu x (Vint n) = some y →
    and x (Vint (Int.sub n Int.one)) = y

def negate_cmp_boolStatement : Prop :=
  ∀ c x y,
    cmp_bool (negate_comparison c) x y =
      CompCert4Lean.Lib.Coqlib.option_map Bool.not (cmp_bool c x y)

def negate_cmpu_boolStatement : Prop :=
  ∀ valid_ptr c x y,
    cmpu_bool valid_ptr (negate_comparison c) x y =
      CompCert4Lean.Lib.Coqlib.option_map Bool.not (cmpu_bool valid_ptr c x y)

def negate_cmpl_boolStatement : Prop :=
  ∀ c x y,
    cmpl_bool (negate_comparison c) x y =
      CompCert4Lean.Lib.Coqlib.option_map Bool.not (cmpl_bool c x y)

def negate_cmplu_boolStatement : Prop :=
  ∀ valid_ptr c x y,
    cmplu_bool valid_ptr (negate_comparison c) x y =
      CompCert4Lean.Lib.Coqlib.option_map Bool.not (cmplu_bool valid_ptr c x y)

def swap_cmp_boolStatement : Prop :=
  ∀ c x y, cmp_bool (swap_comparison c) x y = cmp_bool c y x

def swap_cmpu_boolStatement : Prop :=
  ∀ valid_ptr c x y,
    cmpu_bool valid_ptr (swap_comparison c) x y = cmpu_bool valid_ptr c y x

def swap_cmpl_boolStatement : Prop :=
  ∀ c x y, cmpl_bool (swap_comparison c) x y = cmpl_bool c y x

def swap_cmplu_boolStatement : Prop :=
  ∀ valid_ptr c x y,
    cmplu_bool valid_ptr (swap_comparison c) x y = cmplu_bool valid_ptr c y x

def cmpu_bool_lessdefStatement : Prop :=
  ∀ (valid_ptr valid_ptr' : block → Z → Bool) c v1 v1' v2 v2' b,
    (∀ b ofs, valid_ptr b ofs = true → valid_ptr' b ofs = true) →
    lessdef v1 v1' →
    lessdef v2 v2' →
    cmpu_bool valid_ptr c v1 v2 = some b →
    cmpu_bool valid_ptr' c v1' v2' = some b

def cmplu_bool_lessdefStatement : Prop :=
  ∀ (valid_ptr valid_ptr' : block → Z → Bool) c v1 v1' v2 v2' b,
    (∀ b ofs, valid_ptr b ofs = true → valid_ptr' b ofs = true) →
    lessdef v1 v1' →
    lessdef v2 v2' →
    cmplu_bool valid_ptr c v1 v2 = some b →
    cmplu_bool valid_ptr' c v1' v2' = some b

def cmpu_bool_injectStatement : Prop :=
  ∀ (f : meminj) (valid_ptr1 valid_ptr2 : block → Z → Bool),
    let weak_valid_ptr1 := fun (b : block) (ofs : Z) =>
      valid_ptr1 b ofs || valid_ptr1 b (zSub ofs z1)
    let weak_valid_ptr2 := fun (b : block) (ofs : Z) =>
      valid_ptr2 b ofs || valid_ptr2 b (zSub ofs z1)
    (∀ (b1 : block) (ofs : Ptrofs) (b2 : block) (delta : Z),
      f b1 = some (b2, delta) →
      valid_ptr1 b1 (Ptrofs.unsigned ofs) = true →
      valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ (b1 : block) (ofs : Ptrofs) (b2 : block) (delta : Z),
      f b1 = some (b2, delta) →
      weak_valid_ptr1 b1 (Ptrofs.unsigned ofs) = true →
      weak_valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ (b1 : block) (ofs : Ptrofs) (b2 : block) (delta : Z),
      f b1 = some (b2, delta) →
      weak_valid_ptr1 b1 (Ptrofs.unsigned ofs) = true →
      zLe z0 (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta))) ∧
      zLe (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta)))
        Ptrofs.max_unsigned) →
    (∀ (b1 : block) (ofs1 : Ptrofs) (b2 : block) (ofs2 : Ptrofs)
        (b1' : block) (delta1 : Z) (b2' : block) (delta2 : Z),
      b1 ≠ b2 →
      valid_ptr1 b1 (Ptrofs.unsigned ofs1) = true →
      valid_ptr1 b2 (Ptrofs.unsigned ofs2) = true →
      f b1 = some (b1', delta1) →
      f b2 = some (b2', delta2) →
      b1' ≠ b2' ∨
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
        Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2))) →
    ∀ c v1 v2 v1' v2' b,
      inject f v1 v1' →
      inject f v2 v2' →
      cmpu_bool valid_ptr1 c v1 v2 = some b →
      cmpu_bool valid_ptr2 c v1' v2' = some b

def cmplu_bool_injectStatement : Prop :=
  ∀ (f : meminj) (valid_ptr1 valid_ptr2 : block → Z → Bool),
    let weak_valid_ptr1 := fun (b : block) (ofs : Z) =>
      valid_ptr1 b ofs || valid_ptr1 b (zSub ofs z1)
    let weak_valid_ptr2 := fun (b : block) (ofs : Z) =>
      valid_ptr2 b ofs || valid_ptr2 b (zSub ofs z1)
    (∀ (b1 : block) (ofs : Ptrofs) (b2 : block) (delta : Z),
      f b1 = some (b2, delta) →
      valid_ptr1 b1 (Ptrofs.unsigned ofs) = true →
      valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ (b1 : block) (ofs : Ptrofs) (b2 : block) (delta : Z),
      f b1 = some (b2, delta) →
      weak_valid_ptr1 b1 (Ptrofs.unsigned ofs) = true →
      weak_valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ (b1 : block) (ofs : Ptrofs) (b2 : block) (delta : Z),
      f b1 = some (b2, delta) →
      weak_valid_ptr1 b1 (Ptrofs.unsigned ofs) = true →
      zLe z0 (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta))) ∧
      zLe (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta)))
        Ptrofs.max_unsigned) →
    (∀ (b1 : block) (ofs1 : Ptrofs) (b2 : block) (ofs2 : Ptrofs)
        (b1' : block) (delta1 : Z) (b2' : block) (delta2 : Z),
      b1 ≠ b2 →
      valid_ptr1 b1 (Ptrofs.unsigned ofs1) = true →
      valid_ptr1 b2 (Ptrofs.unsigned ofs2) = true →
      f b1 = some (b1', delta1) →
      f b2 = some (b2', delta2) →
      b1' ≠ b2' ∨
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
        Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2))) →
    ∀ c v1 v2 v1' v2' b,
      inject f v1 v1' →
      inject f v2 v2' →
      cmplu_bool valid_ptr1 c v1 v2 = some b →
      cmplu_bool valid_ptr2 c v1' v2' = some b

def offset_ptr_injectStatement : Prop :=
  ∀ (f : meminj) v v' ofs,
    inject f v v' → inject f (offset_ptr v ofs) (offset_ptr v' ofs)

def normalize_typeStatement : Prop :=
  ∀ v ty, has_type (normalize v ty) ty

def normalize_idemStatement : Prop :=
  ∀ v ty, has_type v ty → normalize v ty = v

def normalize_lessdefStatement : Prop :=
  ∀ v v' ty, lessdef v v' → lessdef (normalize v ty) (normalize v' ty)

def normalize_injectStatement : Prop :=
  ∀ (f : meminj) v v' ty,
    inject f v v' → inject f (normalize v ty) (normalize v' ty)

def lessdef_normalizeStatement : Prop :=
  ∀ v ty, lessdef (normalize v ty) v

def select_injectStatement : Prop :=
  ∀ (f : meminj) (ob ob' : Option Bool) v1 v1' v2 v2' ty,
    (ob = none ∨ ob = ob') →
    inject f v1 v1' →
    inject f v2 v2' →
    inject f (select ob v1 v2 ty) (select ob' v1' v2' ty)

def of_optbool_lessdefStatement : Prop :=
  ∀ (ob ob' : Option Bool),
    (∀ b, ob = some b → ob' = some b) →
    lessdef (of_optbool ob) (of_optbool ob')

def longofwords_lessdefStatement : Prop :=
  ∀ v1 v2 v1' v2',
    lessdef v1 v1' →
    lessdef v2 v2' →
    lessdef (longofwords v1 v2) (longofwords v1' v2')

def longofwords_injectStatement : Prop :=
  ∀ (f : meminj) v1 v2 v1' v2',
    inject f v1 v1' →
    inject f v2 v2' →
    inject f (longofwords v1 v2) (longofwords v1' v2')

def loword_lessdefStatement : Prop :=
  ∀ v v', lessdef v v' → lessdef (loword v) (loword v')

def loword_injectStatement : Prop :=
  ∀ (f : meminj) v v', inject f v v' → inject f (loword v) (loword v')

def hiword_lessdefStatement : Prop :=
  ∀ v v', lessdef v v' → lessdef (hiword v) (hiword v')

def hiword_injectStatement : Prop :=
  ∀ (f : meminj) v v', inject f v v' → inject f (hiword v) (hiword v')

def has_argtype_lessdefStatement : Prop :=
  ∀ v r v', has_argtype v r → lessdef v v' → has_argtype v' r

def has_argtype_injectStatement : Prop :=
  ∀ (f : meminj) v r v', has_argtype v r → inject f v v' → has_argtype v' r

def has_argtype_list_lessdefStatement : Prop :=
  ∀ vl rl vl',
    has_argtype_list vl rl → lessdef_list vl vl' → has_argtype_list vl' rl

def has_argtype_list_injectStatement : Prop :=
  ∀ (f : meminj) vl rl vl',
    has_argtype_list vl rl → inject_list f vl vl' → has_argtype_list vl' rl

def lessdef_sameStatement : Prop :=
  ∀ v1 v2, v1 = v2 → lessdef v1 v2

def lessdef_transStatement : Prop :=
  ∀ v1 v2 v3, lessdef v1 v2 → lessdef v2 v3 → lessdef v1 v3

def lessdef_list_transStatement : Prop :=
  ∀ vl1 vl2,
    lessdef_list vl1 vl2 → ∀ vl3, lessdef_list vl2 vl3 → lessdef_list vl1 vl3

def mull_commutStatement : Prop :=
  ∀ x y, mull x y = mull y x

def shrx_shrStatement : Prop :=
  ∀ x y z,
    shrx x y = some z →
    ∃ p q,
      x = Vint p ∧
      y = Vint q ∧
      z = shr
        (if Int.lt p Int.zero then
          add x (Vint (Int.sub (Int.shl Int.one q) Int.one))
        else x)
        (Vint q)

def shrxl_shrl_2Statement : Prop :=
  ∀ n x z,
    shrxl x (Vint n) = some z →
    z = if Int.eq n Int.zero then x else
      shrl
        (addl x
          (shrlu (shrl x (Vint (Int.repr (zOfNat 63))))
            (Vint (Int.sub (Int.repr (zOfNat 64)) n))))
        (Vint n)

def subl_addl_lStatement : Prop :=
  ∀ v1 v2 i, subl (addl v1 (Vlong i)) v2 = addl (subl v1 v2) (Vlong i)

def subl_addl_oppStatement : Prop :=
  ∀ x y, subl x (Vlong y) = addl x (Vlong (Int64.neg y))

def subl_addl_rStatement : Prop :=
  ∀ v1 v2 i,
    subl v1 (addl v2 (Vlong i)) = addl (subl v1 v2) (Vlong (Int64.neg i))

def zero_ext_andStatement : Prop :=
  ∀ n v,
    zLe z0 n → zero_ext n v = and v (Vint (Int.repr (zSub (zTwoP n) z1)))

end Val

abbrev meminj := Val.meminj

def inject_incr (f1 f2 : meminj) : Prop :=
  ∀ b b' delta, f1 b = some (b', delta) → f2 b = some (b', delta)

def inject_id : meminj := fun b => some (b, z0)

def inject_incr_reflStatement : Prop :=
  ∀ f : meminj, inject_incr f f

def inject_incr_transStatement : Prop :=
  ∀ f1 f2 f3,
    inject_incr f1 f2 → inject_incr f2 f3 → inject_incr f1 f3

def val_inject_incrStatement : Prop :=
  ∀ f1 f2 v v',
    inject_incr f1 f2 → Val.inject f1 v v' → Val.inject f2 v v'

def val_inject_list_incrStatement : Prop :=
  ∀ f1 f2 vl vl',
    inject_incr f1 f2 → Val.inject_list f1 vl vl' → Val.inject_list f2 vl vl'

def val_inject_lessdefStatement : Prop :=
  ∀ v1 v2,
    Val.lessdef v1 v2 ↔ Val.inject (fun b => some (b, z0)) v1 v2

def val_inject_list_lessdefStatement : Prop :=
  ∀ vl1 vl2,
    Val.lessdef_list vl1 vl2 ↔ Val.inject_list (fun b => some (b, z0)) vl1 vl2

def val_inject_idStatement : Prop :=
  ∀ v1 v2, Val.inject inject_id v1 v2 ↔ Val.lessdef v1 v2

end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values

theorem inject_incr_refl : inject_incr_reflStatement := by
  intro f b b' delta h
  exact h

namespace Val

theorem Vptr_has_type : Vptr_has_typeStatement := by
  intro b ofs
  rfl

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values

namespace Val

private theorem repr_val_of_lt (n : Nat) (hn : n < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize) :
    (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)).val = n := by
  have hn0 : (0 : Int) ≤ n := Int.natCast_nonneg n
  have hnmax : (n : Int) ≤ (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize : Nat) - 1 := by omega
  have hnat : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n) =
      (n : Int) := by
    simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat] using
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt (Int.ofNat n))
  have hmax : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      CompCert4Lean.Lib.Integers.Int.max_unsigned =
      (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize : Int) - 1 := by rfl
  have hu : CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n := by
    apply CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api
    constructor
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)
      rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0 = 0 by rfl, hnat]
      exact hn0
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          CompCert4Lean.Lib.Integers.Int.max_unsigned
      rw [hnat, hmax]
      exact hnmax
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat
    ((CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)).intval) = n
  change CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)) = _ at hu
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat
    (CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n))) = n
  rw [hu]
  exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Nat2Z.id n

theorem and_assoc : and_assocStatement := by
  intro x y z
  cases x <;> cases y <;> cases z <;> simp [and]
  rename_i a b c
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  change (CompCert4Lean.Lib.Integers.WordCore.and
      (CompCert4Lean.Lib.Integers.WordCore.and _ _) _).val =
    (CompCert4Lean.Lib.Integers.WordCore.and _
      (CompCert4Lean.Lib.Integers.WordCore.and _ _)).val
  simp only [CompCert4Lean.Lib.Integers.WordCore.and]
  have ha : a.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := a.toFin.isLt
  have hb : b.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := b.toFin.isLt
  have hc : c.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := c.toFin.isLt
  change
    (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (Nat.land
          (CompCert4Lean.Lib.Integers.WordCore.Word.val
            (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
                (Nat.land a.val b.val)))) c.val))).val =
      (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
          (Nat.land a.val
            (CompCert4Lean.Lib.Integers.WordCore.Word.val
              (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
                  (Nat.land b.val c.val))))))).val
  simp only [repr_val_of_lt (Nat.land a.val b.val) (Nat.and_lt_two_pow a.val hb),
    repr_val_of_lt (Nat.land b.val c.val) (Nat.and_lt_two_pow b.val hc),
    repr_val_of_lt (Nat.land (Nat.land a.val b.val) c.val)
      (Nat.and_lt_two_pow (Nat.land a.val b.val) hc),
    repr_val_of_lt (Nat.land a.val (Nat.land b.val c.val))
      (Nat.and_lt_two_pow a.val (Nat.and_lt_two_pow b.val hc))]
  exact Nat.and_assoc _ _ _

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values

namespace Val

private theorem or_assoc_repr_val_of_lt (n : Nat)
    (hn : n < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize) :
    (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)).val = n := by
  have hn0 : (0 : Int) ≤ n := Int.natCast_nonneg n
  have hnmax : (n : Int) ≤ (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize : Nat) - 1 := by omega
  have hnat : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n) =
      (n : Int) := by
    simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat] using
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt (Int.ofNat n))
  have hmax : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      CompCert4Lean.Lib.Integers.Int.max_unsigned =
      (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize : Int) - 1 := by rfl
  have hu : CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n := by
    apply CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api
    constructor
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)
      rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0 = 0 by rfl, hnat]
      exact hn0
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          CompCert4Lean.Lib.Integers.Int.max_unsigned
      rw [hnat, hmax]
      exact hnmax
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat
    ((CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)).intval) = n
  change CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)) = _ at hu
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat
    (CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n))) = n
  rw [hu]
  exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Nat2Z.id n

theorem or_assoc : or_assocStatement := by
  intro x y z
  cases x <;> cases y <;> cases z <;> simp [or]
  rename_i a b c
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  change (CompCert4Lean.Lib.Integers.WordCore.or
      (CompCert4Lean.Lib.Integers.WordCore.or _ _) _).val =
    (CompCert4Lean.Lib.Integers.WordCore.or _
      (CompCert4Lean.Lib.Integers.WordCore.or _ _)).val
  simp only [CompCert4Lean.Lib.Integers.WordCore.or]
  have ha : a.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := a.toFin.isLt
  have hb : b.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := b.toFin.isLt
  have hc : c.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := c.toFin.isLt
  change
    (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (Nat.lor
          (CompCert4Lean.Lib.Integers.WordCore.Word.val
            (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
                (Nat.lor a.val b.val)))) c.val))).val =
      (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
          (Nat.lor a.val
            (CompCert4Lean.Lib.Integers.WordCore.Word.val
              (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
                  (Nat.lor b.val c.val))))))).val
  simp only [or_assoc_repr_val_of_lt (Nat.lor a.val b.val) (Nat.or_lt_two_pow ha hb),
    or_assoc_repr_val_of_lt (Nat.lor b.val c.val) (Nat.or_lt_two_pow hb hc),
    or_assoc_repr_val_of_lt (Nat.lor (Nat.lor a.val b.val) c.val)
      (Nat.or_lt_two_pow (Nat.or_lt_two_pow ha hb) hc),
    or_assoc_repr_val_of_lt (Nat.lor a.val (Nat.lor b.val c.val))
      (Nat.or_lt_two_pow ha (Nat.or_lt_two_pow hb hc))]
  exact Nat.or_assoc _ _ _

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

private theorem xor_assoc_repr_val_of_lt' (n : Nat)
    (hn : n < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize) :
    (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)).val = n := by
  have hn0 : (0 : Int) ≤ n := Int.natCast_nonneg n
  have hnmax : (n : Int) ≤ (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize : Nat) - 1 := by omega
  have hnat : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n) = (n : Int) := by
    simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat] using
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt (Int.ofNat n))
  have hmax : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      CompCert4Lean.Lib.Integers.Int.max_unsigned =
      (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize : Int) - 1 := by rfl
  have hu : CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n := by
    apply CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api
    constructor
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0 ≤ _
      rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0 = 0 by rfl, hnat]
      exact hn0
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n) ≤ _
      rw [hnat, hmax]
      exact hnmax
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat
    ((CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)).intval) = n
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat
    (CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n))) = n
  rw [hu]
  exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Nat2Z.id n

theorem xor_assoc : xor_assocStatement := by
  intro x y z
  cases x <;> cases y <;> cases z <;> simp [xor]
  rename_i a b c
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  change (CompCert4Lean.Lib.Integers.WordCore.xor
      (CompCert4Lean.Lib.Integers.WordCore.xor _ _) _).val =
    (CompCert4Lean.Lib.Integers.WordCore.xor _
      (CompCert4Lean.Lib.Integers.WordCore.xor _ _)).val
  simp only [CompCert4Lean.Lib.Integers.WordCore.xor]
  have ha : a.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := a.toFin.isLt
  have hb : b.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := b.toFin.isLt
  have hc : c.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := c.toFin.isLt
  change
    (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (Nat.xor
          (CompCert4Lean.Lib.Integers.WordCore.Word.val
            (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
                (Nat.xor a.val b.val)))) c.val))).val =
      (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
          (Nat.xor a.val
            (CompCert4Lean.Lib.Integers.WordCore.Word.val
              (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
                  (Nat.xor b.val c.val))))))).val
  simp only [xor_assoc_repr_val_of_lt' (Nat.xor a.val b.val) (Nat.xor_lt_two_pow ha hb),
    xor_assoc_repr_val_of_lt' (Nat.xor b.val c.val) (Nat.xor_lt_two_pow hb hc),
    xor_assoc_repr_val_of_lt' (Nat.xor (Nat.xor a.val b.val) c.val)
      (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ha hb) hc),
    xor_assoc_repr_val_of_lt' (Nat.xor a.val (Nat.xor b.val c.val))
      (Nat.xor_lt_two_pow ha (Nat.xor_lt_two_pow hb hc))]
  exact Nat.xor_assoc _ _ _

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values

open CompCert4Lean.Common.AST

namespace Val

theorem Vnullptr_has_type : Vnullptr_has_typeStatement := by
  change Val.has_type Vnullptr CompCert4Lean.Common.AST.Tptr
  cases hptr : CompCert4Lean.X86_64.Archi.ptr64 <;>
    simp [Vnullptr, CompCert4Lean.Common.AST.Tptr, Val.has_type, hptr]

private theorem has_subtype_local (ty1 ty2 : CompCert4Lean.Common.AST.typ) (v : val) :
    CompCert4Lean.Common.AST.subtype ty1 ty2 = true → Val.has_type v ty1 → Val.has_type v ty2 := by
  intro hsub hv
  cases ty1 <;> cases ty2 <;> cases v <;>
    simp [CompCert4Lean.Common.AST.subtype, Val.has_type] at hsub hv ⊢
  all_goals exact hv

theorem has_subtype : has_subtypeStatement := by
  intro ty1 ty2 v hsub hv
  exact has_subtype_local ty1 ty2 v hsub hv

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values

namespace Val

theorem has_proj_xtype : has_proj_xtypeStatement := by
  intro v t h
  cases t <;> cases v <;>
    simp [has_rettype, has_type, CompCert4Lean.Common.AST.proj_xtype,
      CompCert4Lean.Common.AST.Tptr,
      CompCert4Lean.X86_64.Archi.ptr64] at h ⊢

theorem has_inj_type : has_inj_typeStatement := by
  intro v t h
  cases v <;> cases t <;>
    simp [has_type, has_rettype, CompCert4Lean.Common.AST.inj_type,
      CompCert4Lean.X86_64.Archi.ptr64] at h ⊢

theorem normalize_type : normalize_typeStatement := by
  intro v ty
  cases v <;> cases ty <;>
    simp [normalize, has_type, CompCert4Lean.X86_64.Archi.ptr64]

theorem normalize_idem : normalize_idemStatement := by
  intro v ty h
  cases v <;> cases ty <;>
    simp [normalize, has_type, CompCert4Lean.X86_64.Archi.ptr64] at h ⊢

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem norm_bool_cases : norm_bool_casesStatement := by
  intro v
  unfold norm_bool
  unfold is_bool
  by_cases h₁ : v = Vtrue
  · simp [eq, h₁, boolOfSumbool]
  · by_cases h₂ : v = Vfalse
    · simp [eq, h₁, h₂, boolOfSumbool]
    · simp [eq, h₁, h₂, boolOfSumbool]

theorem load_result_type : load_result_typeStatement := by
  intro chunk v
  cases chunk <;> cases v <;>
    simp [load_result, has_type, CompCert4Lean.Common.AST.type_of_chunk,
      CompCert4Lean.X86_64.Archi.ptr64]
  case Mbool.Vint n =>
    rcases norm_bool_cases (Vint (intZeroExt (zOfNat 8) n)) with h | h | h <;>
      simp [h, has_type, Vfalse, Vtrue]

theorem load_result_same : load_result_sameStatement := by
  intro v ty h
  cases v <;> cases ty <;>
    simp [has_type, load_result, CompCert4Lean.Common.AST.chunk_of_type,
      CompCert4Lean.X86_64.Archi.ptr64] at h ⊢

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem bool_of_val_of_optbool : bool_of_val_of_optboolStatement := by
  intro ob b h
  cases ob with
  | none => cases h
  | some x => cases x <;> cases h <;> rfl

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem norm_bool_idem : norm_bool_idemStatement := by
  intro v
  unfold norm_bool
  by_cases h : is_bool v
  · simp [h]
  · simp [h]

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem add_commut : add_commutStatement := by
  intro x y
  cases x <;> cases y <;>
    simp [add, CompCert4Lean.X86_64.Archi.ptr64]
  case Vint.Vint a b =>
    change CompCert4Lean.Lib.Integers.WordCore.repr 32
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add a.intval b.intval) =
      CompCert4Lean.Lib.Integers.WordCore.repr 32
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add b.intval a.intval)
    apply congrArg (CompCert4Lean.Lib.Integers.WordCore.repr 32)
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    exact Int.add_comm _ _

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem add_assoc : add_assocStatement := by
  intro x y z
  cases x <;> cases y <;> cases z <;>
    simp [add, CompCert4Lean.X86_64.Archi.ptr64]
  case Vint.Vint.Vint a b c =>
    exact CompCert4Lean.Lib.Integers.Int.add_assoc_proof a b c

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem add_permut : add_permutStatement := by
  intro x y z
  cases x <;> cases y <;> cases z <;>
    simp [add, CompCert4Lean.X86_64.Archi.ptr64]
  case Vint.Vint.Vint a b c =>
    change Int.add a (Int.add b c) = Int.add b (Int.add a c)
    calc
      Int.add a (Int.add b c) = Int.add (Int.add a b) c :=
        (CompCert4Lean.Lib.Integers.Int.add_assoc_proof a b c).symm
      _ = Int.add (Int.add b a) c := by
        have h := add_commut (Vint a) (Vint b)
        have h' : Int.add a b = Int.add b a := by
          injection h
        exact congrArg (fun q => Int.add q c) h'
      _ = Int.add b (Int.add a c) :=
        CompCert4Lean.Lib.Integers.Int.add_assoc_proof b a c

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem add_permut_4 : add_permut_4Statement := by
  intro x y z t
  calc
    add (add x y) (add z t) = add x (add y (add z t)) :=
      add_assoc x y (add z t)
    _ = add x (add z (add y t)) := by
      exact congrArg (fun q => add x q) (add_permut y z t)
    _ = add (add x z) (add y t) :=
      (add_assoc x z (add y t)).symm

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem sub_add_opp : sub_add_oppStatement := by
  intro x y
  cases x <;> simp [sub, add, CompCert4Lean.X86_64.Archi.ptr64]
  case Vint a =>
    exact CompCert4Lean.Lib.Integers.Int.sub_add_opp_proof a y

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

private theorem int_add_commut_local (a b : CompCert4Lean.Lib.Integers.int) :
    Int.add a b = Int.add b a := by
  have h := add_commut (Vint a) (Vint b)
  injection h

private theorem int_sub_add_l_local
    (x y z : CompCert4Lean.Lib.Integers.int) :
    Int.sub (Int.add x y) z = Int.add (Int.sub x z) y := by
  calc
    Int.sub (Int.add x y) z = Int.add (Int.add x y) (Int.neg z) :=
      CompCert4Lean.Lib.Integers.Int.sub_add_opp_proof (Int.add x y) z
    _ = Int.add x (Int.add y (Int.neg z)) :=
      CompCert4Lean.Lib.Integers.Int.add_assoc_proof x y (Int.neg z)
    _ = Int.add x (Int.add (Int.neg z) y) := by
      exact congrArg (fun q => Int.add x q) (int_add_commut_local y (Int.neg z))
    _ = Int.add (Int.add x (Int.neg z)) y :=
      (CompCert4Lean.Lib.Integers.Int.add_assoc_proof x (Int.neg z) y).symm
    _ = Int.add (Int.sub x z) y := by
      exact congrArg (fun q => Int.add q y)
        (CompCert4Lean.Lib.Integers.Int.sub_add_opp_proof x z).symm

theorem sub_add_l : sub_add_lStatement := by
  intro v1 v2 i
  cases v1 <;> cases v2 <;>
    simp [sub, add, CompCert4Lean.X86_64.Archi.ptr64]
  case Vint.Vint a b =>
    exact int_sub_add_l_local a i b

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem mul_commut : mul_commutStatement := by
  intro x y
  cases x <;> cases y <;>
    simp [mul]
  case Vint.Vint a b =>
    change CompCert4Lean.Lib.Integers.WordCore.repr 32
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul a.intval b.intval) =
      CompCert4Lean.Lib.Integers.WordCore.repr 32
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul b.intval a.intval)
    apply congrArg (CompCert4Lean.Lib.Integers.WordCore.repr 32)
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    exact Int.mul_comm _ _

theorem mul_add_distr_r : mul_add_distr_rStatement := by
  intro x y z
  cases x <;> cases y <;> cases z <;>
    simp [mul, add, CompCert4Lean.X86_64.Archi.ptr64]
  case Vint.Vint.Vint a b c =>
    exact CompCert4Lean.Lib.Integers.Int.mul_add_distr_r_proof a b c

theorem mul_add_distr_l : mul_add_distr_lStatement := by
  intro x y z
  calc
    mul (add x y) z = mul z (add x y) := mul_commut _ _
    _ = add (mul z x) (mul z y) := mul_add_distr_r _ _ _
    _ = add (mul x z) (mul y z) := by
      rw [mul_commut z x, mul_commut z y]

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

private theorem int_sub_self_local (x : CompCert4Lean.Lib.Integers.int) :
    Int.sub x x = Int.zero := by
  change CompCert4Lean.Lib.Integers.WordCore.repr 32
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub x.intval x.intval) =
    CompCert4Lean.Lib.Integers.WordCore.repr 32
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0
  apply congrArg (CompCert4Lean.Lib.Integers.WordCore.repr 32)
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  exact Int.sub_self _

private theorem int_add_zero_l_local (x : CompCert4Lean.Lib.Integers.int) :
    Int.add Int.zero x = x := by
  calc
    Int.add Int.zero x = Int.add x Int.zero := int_add_commut_local _ _
    _ = x := CompCert4Lean.Lib.Integers.Int.add_zero_proof x

private theorem int_add_neg_self_local (x : CompCert4Lean.Lib.Integers.int) :
    Int.add x (Int.neg x) = Int.zero := by
  calc
    Int.add x (Int.neg x) = Int.sub x x :=
      (CompCert4Lean.Lib.Integers.Int.sub_add_opp_proof x x).symm
    _ = Int.zero := int_sub_self_local x

private theorem int_add_neg_self_left_local (x : CompCert4Lean.Lib.Integers.int) :
    Int.add (Int.neg x) x = Int.zero := by
  calc
    Int.add (Int.neg x) x = Int.add x (Int.neg x) := int_add_commut_local _ _
    _ = Int.zero := int_add_neg_self_local x

private theorem int_add_permut_local
    (x y z : CompCert4Lean.Lib.Integers.int) :
    Int.add x (Int.add y z) = Int.add y (Int.add x z) := by
  calc
    Int.add x (Int.add y z) = Int.add (Int.add x y) z :=
      (CompCert4Lean.Lib.Integers.Int.add_assoc_proof x y z).symm
    _ = Int.add (Int.add y x) z := by rw [int_add_commut_local x y]
    _ = Int.add y (Int.add x z) :=
      CompCert4Lean.Lib.Integers.Int.add_assoc_proof y x z

private theorem int_neg_unique_local
    (a b : CompCert4Lean.Lib.Integers.int) (h : Int.add a b = Int.zero) :
    b = Int.neg a := by
  calc
    b = Int.add Int.zero b := (int_add_zero_l_local b).symm
    _ = Int.add (Int.add (Int.neg a) a) b := by
      rw [int_add_neg_self_left_local a]
    _ = Int.add (Int.neg a) (Int.add a b) :=
      CompCert4Lean.Lib.Integers.Int.add_assoc_proof (Int.neg a) a b
    _ = Int.add (Int.neg a) Int.zero := by rw [h]
    _ = Int.neg a := CompCert4Lean.Lib.Integers.Int.add_zero_proof (Int.neg a)

private theorem int_neg_add_distr_local
    (y z : CompCert4Lean.Lib.Integers.int) :
    Int.neg (Int.add y z) = Int.add (Int.neg y) (Int.neg z) := by
  apply Eq.symm
  apply int_neg_unique_local
  calc
    Int.add (Int.add y z) (Int.add (Int.neg y) (Int.neg z)) =
        Int.add y (Int.add z (Int.add (Int.neg y) (Int.neg z))) :=
      CompCert4Lean.Lib.Integers.Int.add_assoc_proof y z _
    _ = Int.add y (Int.add (Int.neg y) (Int.add z (Int.neg z))) := by
      exact congrArg (fun q => Int.add y q)
        (int_add_permut_local z (Int.neg y) (Int.neg z))
    _ = Int.add (Int.add y (Int.neg y)) (Int.add z (Int.neg z)) :=
      (CompCert4Lean.Lib.Integers.Int.add_assoc_proof y (Int.neg y) _).symm
    _ = Int.add Int.zero Int.zero := by
      rw [int_add_neg_self_local y, int_add_neg_self_local z]
    _ = Int.zero := CompCert4Lean.Lib.Integers.Int.add_zero_proof Int.zero

private theorem int_sub_add_r_local
    (x y z : CompCert4Lean.Lib.Integers.int) :
    Int.sub x (Int.add y z) = Int.add (Int.sub x y) (Int.neg z) := by
  calc
    Int.sub x (Int.add y z) = Int.add x (Int.neg (Int.add y z)) :=
      CompCert4Lean.Lib.Integers.Int.sub_add_opp_proof x (Int.add y z)
    _ = Int.add x (Int.add (Int.neg y) (Int.neg z)) := by
      rw [int_neg_add_distr_local]
    _ = Int.add (Int.add x (Int.neg y)) (Int.neg z) :=
      (CompCert4Lean.Lib.Integers.Int.add_assoc_proof x (Int.neg y) (Int.neg z)).symm
    _ = Int.add (Int.sub x y) (Int.neg z) := by
      exact congrArg (fun q => Int.add q (Int.neg z))
        (CompCert4Lean.Lib.Integers.Int.sub_add_opp_proof x y).symm

theorem sub_add_r : sub_add_rStatement := by
  intro v1 v2 i
  cases v1 <;> cases v2 <;>
    simp [sub, add, CompCert4Lean.X86_64.Archi.ptr64]
  case Vint.Vint a b =>
    exact int_sub_add_r_local a b i

end Val
end CompCert4Lean.Common.Values
