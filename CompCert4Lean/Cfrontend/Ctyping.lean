import CompCert4Lean.Cfrontend.Cop

/-!
# CompCert C typing predicates

Definition-bearing translation of the selected declarations from
`cfrontend/Ctyping.v`.  Proofs assigned to the later proof phase are recorded
as exact proposition descriptors.
-/

namespace CompCert4Lean.Cfrontend.Ctyping

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Common.Values

private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

def wt_int (n : CCInt) (sz : intsize) (sg : signedness) : Prop :=
  match sz, sg with
  | .IBool, _ =>
      n = CompCert4Lean.Lib.Integers.Int.zero ∨
        n = CompCert4Lean.Lib.Integers.Int.one
  | .I8, .Unsigned =>
      CompCert4Lean.Lib.Integers.Int.zero_ext (zOfNat 8) n = n
  | .I8, .Signed =>
      cast_int_int .I8 .Signed n = n
  | .I16, .Unsigned =>
      CompCert4Lean.Lib.Integers.Int.zero_ext (zOfNat 16) n = n
  | .I16, .Signed =>
      cast_int_int .I16 .Signed n = n
  | .I32, _ => True

inductive wt_val : val → type → Prop where
  | wt_val_int (n : CCInt) (sz : intsize) (sg : signedness) (a : attr)
      (hwt : wt_int n sz sg) :
      wt_val (.Vint n) (.Tint sz sg a)
  | wt_val_ptr_int (b : block) (ofs : CompCert4Lean.Lib.Integers.Ptrofs.int)
      (sg : signedness) (a : attr)
      (hptr64 : CompCert4Lean.X86_64.Archi.ptr64 = false) :
      wt_val (.Vptr b ofs) (.Tint .I32 sg a)
  | wt_val_long (n : CompCert4Lean.Lib.Integers.int64) (sg : signedness) (a : attr) :
      wt_val (.Vlong n) (.Tlong sg a)
  | wt_val_ptr_long (b : block) (ofs : CompCert4Lean.Lib.Integers.Ptrofs.int)
      (sg : signedness) (a : attr)
      (hptr64 : CompCert4Lean.X86_64.Archi.ptr64 = true) :
      wt_val (.Vptr b ofs) (.Tlong sg a)
  | wt_val_float (f : CompCert4Lean.Lib.Floats.float) (a : attr) :
      wt_val (.Vfloat f) (.Tfloat .F64 a)
  | wt_val_single (f : CompCert4Lean.Lib.Floats.float32) (a : attr) :
      wt_val (.Vsingle f) (.Tfloat .F32 a)
  | wt_val_pointer (b : block) (ofs : CompCert4Lean.Lib.Integers.Ptrofs.int)
      (ty : type) (a : attr) :
      wt_val (.Vptr b ofs) (.Tpointer ty a)
  | wt_val_int_pointer (n : CCInt) (ty : type) (a : attr)
      (hptr64 : CompCert4Lean.X86_64.Archi.ptr64 = false) :
      wt_val (.Vint n) (.Tpointer ty a)
  | wt_val_long_pointer (n : CompCert4Lean.Lib.Integers.int64) (ty : type) (a : attr)
      (hptr64 : CompCert4Lean.X86_64.Archi.ptr64 = true) :
      wt_val (.Vlong n) (.Tpointer ty a)
  | wt_val_array (b : block) (ofs : CompCert4Lean.Lib.Integers.Ptrofs.int)
      (ty : type) (sz : Z) (a : attr) :
      wt_val (.Vptr b ofs) (.Tarray ty sz a)
  | wt_val_function (b : block) (ofs : CompCert4Lean.Lib.Integers.Ptrofs.int)
      (tyargs : List type) (tyres : type)
      (cc : CompCert4Lean.Common.AST.calling_convention) :
      wt_val (.Vptr b ofs) (.Tfunction tyargs tyres cc)
  | wt_val_struct (b : block) (ofs : CompCert4Lean.Lib.Integers.Ptrofs.int)
      (id : CompCert4Lean.Common.AST.ident) (a : attr) :
      wt_val (.Vptr b ofs) (.Tstruct id a)
  | wt_val_union (b : block) (ofs : CompCert4Lean.Lib.Integers.Ptrofs.int)
      (id : CompCert4Lean.Common.AST.ident) (a : attr) :
      wt_val (.Vptr b ofs) (.Tunion id a)
  | wt_val_undef (ty : type) :
      wt_val .Vundef ty
  | wt_val_void (v : val) :
      wt_val v .Tvoid

def pres_cast_int_intStatement : Prop :=
  ∀ (sz : intsize) (sg : signedness) (n : CCInt),
    wt_int (cast_int_int sz sg n) sz sg

def wt_val_castedStatement : Prop :=
  ∀ (v : val) (ty : type), val_casted v ty → wt_val v ty

def has_rettype_wt_valStatement : Prop :=
  ∀ (v : val) (ty : type),
    CompCert4Lean.Common.Values.Val.has_rettype v (rettype_of_type ty) → wt_val v ty

end CompCert4Lean.Cfrontend.Ctyping
