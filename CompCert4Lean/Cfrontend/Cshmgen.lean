import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.RocqString
import CompCert4Lean.Backend.Cminor
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Errors
import CompCert4Lean.Cfrontend.Clight
import CompCert4Lean.Cfrontend.Cop
import CompCert4Lean.Cfrontend.Csharpminor
import CompCert4Lean.Cfrontend.Ctypes
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Floats
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Maps
import CompCert4Lean.X86.Conventions1
import CompCert4Lean.X86_64.Archi

/-!
# Translation from Clight to Csharpminor

Definition-bearing translation of CompCert's `cfrontend/Cshmgen.v`.
-/

namespace CompCert4Lean.Cfrontend.Cshmgen

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private abbrev ident := CompCert4Lean.Common.AST.ident
private abbrev CType := CompCert4Lean.Cfrontend.Ctypes.type
private abbrev composite_env := CompCert4Lean.Cfrontend.Ctypes.composite_env
private abbrev intsize := CompCert4Lean.Cfrontend.Ctypes.intsize
private abbrev signedness := CompCert4Lean.Cfrontend.Ctypes.signedness
private abbrev bitfield := CompCert4Lean.Cfrontend.Ctypes.bitfield
private abbrev CExpr := CompCert4Lean.Cfrontend.Csharpminor.expr
private abbrev CStmt := CompCert4Lean.Cfrontend.Csharpminor.stmt
private abbrev CLblStmt := CompCert4Lean.Cfrontend.Csharpminor.lbl_stmt
private abbrev CFunction := CompCert4Lean.Cfrontend.Csharpminor.function
private abbrev CFundef := CompCert4Lean.Cfrontend.Csharpminor.fundef
private abbrev CProgram := CompCert4Lean.Cfrontend.Csharpminor.program
private abbrev LExpr := CompCert4Lean.Cfrontend.Clight.expr
private abbrev LStmt := CompCert4Lean.Cfrontend.Clight.statement
private abbrev LLblStmt := CompCert4Lean.Cfrontend.Clight.labeled_statements
private abbrev LFunction := CompCert4Lean.Cfrontend.Clight.function
private abbrev LFundef := CompCert4Lean.Cfrontend.Clight.fundef
private abbrev LProgram := CompCert4Lean.Cfrontend.Clight.program
private abbrev Res := CompCert4Lean.Common.Errors.res
private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev CCInt64 := CompCert4Lean.Lib.Integers.int64
private abbrev CCFloat := CompCert4Lean.Lib.Floats.float
private abbrev CCFloat32 := CompCert4Lean.Lib.Floats.float32
private abbrev BinOp := CompCert4Lean.Backend.Cminor.binary_operation
private abbrev Comparison := CompCert4Lean.Lib.Integers.comparison
private abbrev Signature := CompCert4Lean.Common.AST.signature
private abbrev Xtype := CompCert4Lean.Common.AST.xtype
private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string

private abbrev z0 : Z := .Z0
private abbrev z1 : Z := .Zpos .xH
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev twoP := ZArith.Zpower.two_p

private def zleBool (x y : Z) : Bool :=
  match CompCert4Lean.Lib.Coqlib.zle x y with
  | .left _ => true
  | .right _ => false

private def zltBool (x y : Z) : Bool :=
  match CompCert4Lean.Lib.Coqlib.zlt x y with
  | .left _ => true
  | .right _ => false

private def ofString (s : String) : RocqString :=
  (String.toUTF8 s).toList.foldr
    (fun b tail =>
      CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.String b tail)
    CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.EmptyString

private def error {A : Type} (s : String) : Res A :=
  .Error (CompCert4Lean.Common.Errors.msg (ofString s))

/-! ## Csharpminor constructors -/

def make_intconst (n : CCInt) : CExpr :=
  .Econst (.Ointconst n)

def make_longconst (n : CCInt64) : CExpr :=
  .Econst (.Olongconst n)

def make_floatconst (n : CCFloat) : CExpr :=
  .Econst (.Ofloatconst n)

def make_singleconst (n : CCFloat32) : CExpr :=
  .Econst (.Osingleconst n)

def make_ptrofsconst (n : Z) : CExpr :=
  if CompCert4Lean.X86_64.Archi.ptr64 then
    make_longconst (CompCert4Lean.Lib.Integers.Int64.repr n)
  else
    make_intconst (CompCert4Lean.Lib.Integers.Int.repr n)

def make_singleoffloat (e : CExpr) : CExpr := .Eunop .Osingleoffloat e

def make_floatofsingle (e : CExpr) : CExpr := .Eunop .Ofloatofsingle e

def make_floatofint (e : CExpr) (sg : signedness) : CExpr :=
  match sg with
  | .Signed => .Eunop .Ofloatofint e
  | .Unsigned => .Eunop .Ofloatofintu e

def make_singleofint (e : CExpr) (sg : signedness) : CExpr :=
  match sg with
  | .Signed => .Eunop .Osingleofint e
  | .Unsigned => .Eunop .Osingleofintu e

def make_intoffloat (e : CExpr) (sg : signedness) : CExpr :=
  match sg with
  | .Signed => .Eunop .Ointoffloat e
  | .Unsigned => .Eunop .Ointuoffloat e

def make_intofsingle (e : CExpr) (sg : signedness) : CExpr :=
  match sg with
  | .Signed => .Eunop .Ointofsingle e
  | .Unsigned => .Eunop .Ointuofsingle e

def make_longofint (e : CExpr) (sg : signedness) : CExpr :=
  match sg with
  | .Signed => .Eunop .Olongofint e
  | .Unsigned => .Eunop .Olongofintu e

def make_floatoflong (e : CExpr) (sg : signedness) : CExpr :=
  match sg with
  | .Signed => .Eunop .Ofloatoflong e
  | .Unsigned => .Eunop .Ofloatoflongu e

def make_singleoflong (e : CExpr) (sg : signedness) : CExpr :=
  match sg with
  | .Signed => .Eunop .Osingleoflong e
  | .Unsigned => .Eunop .Osingleoflongu e

def make_longoffloat (e : CExpr) (sg : signedness) : CExpr :=
  match sg with
  | .Signed => .Eunop .Olongoffloat e
  | .Unsigned => .Eunop .Olonguoffloat e

def make_longofsingle (e : CExpr) (sg : signedness) : CExpr :=
  match sg with
  | .Signed => .Eunop .Olongofsingle e
  | .Unsigned => .Eunop .Olonguofsingle e

def make_cmpu_ne_zero (e : CExpr) : CExpr :=
  match e with
  | .Ebinop (.Ocmp _) _ _
  | .Ebinop (.Ocmpu _) _ _
  | .Ebinop (.Ocmpf _) _ _
  | .Ebinop (.Ocmpfs _) _ _
  | .Ebinop (.Ocmpl _) _ _
  | .Ebinop (.Ocmplu _) _ _ => e
  | _ =>
      .Ebinop (.Ocmpu .Cne) e
        (make_intconst CompCert4Lean.Lib.Integers.Int.zero)

def sizeof (ce : composite_env) (t : CType) : Res Z :=
  if CompCert4Lean.Cfrontend.Ctypes.complete_type ce t then
    .OK (CompCert4Lean.Cfrontend.Ctypes.sizeof ce t)
  else
    error "incomplete type"

def alignof (ce : composite_env) (t : CType) : Res Z :=
  if CompCert4Lean.Cfrontend.Ctypes.complete_type ce t then
    .OK (CompCert4Lean.Cfrontend.Ctypes.alignof ce t)
  else
    error "incomplete type"

def make_cast_int (e : CExpr) (sz : intsize) (si : signedness) : CExpr :=
  match sz, si with
  | .I8, .Signed => .Eunop .Ocast8signed e
  | .I8, .Unsigned => .Eunop .Ocast8unsigned e
  | .I16, .Signed => .Eunop .Ocast16signed e
  | .I16, .Unsigned => .Eunop .Ocast16unsigned e
  | .I32, _ => e
  | .IBool, _ => make_cmpu_ne_zero e

def make_cast (fromTy toTy : CType) (e : CExpr) : Res CExpr :=
  match CompCert4Lean.Cfrontend.Cop.classify_cast fromTy toTy with
  | .cast_case_pointer => .OK e
  | .cast_case_i2i sz2 si2 => .OK (make_cast_int e sz2 si2)
  | .cast_case_f2f => .OK e
  | .cast_case_s2s => .OK e
  | .cast_case_f2s => .OK (make_singleoffloat e)
  | .cast_case_s2f => .OK (make_floatofsingle e)
  | .cast_case_i2f si1 => .OK (make_floatofint e si1)
  | .cast_case_i2s si1 => .OK (make_singleofint e si1)
  | .cast_case_f2i sz2 si2 => .OK (make_cast_int (make_intoffloat e si2) sz2 si2)
  | .cast_case_s2i sz2 si2 => .OK (make_cast_int (make_intofsingle e si2) sz2 si2)
  | .cast_case_l2l => .OK e
  | .cast_case_i2l si1 => .OK (make_longofint e si1)
  | .cast_case_l2i sz2 si2 => .OK (make_cast_int (.Eunop .Ointoflong e) sz2 si2)
  | .cast_case_l2f si1 => .OK (make_floatoflong e si1)
  | .cast_case_l2s si1 => .OK (make_singleoflong e si1)
  | .cast_case_f2l si2 => .OK (make_longoffloat e si2)
  | .cast_case_s2l si2 => .OK (make_longofsingle e si2)
  | .cast_case_i2bool => .OK (make_cmpu_ne_zero e)
  | .cast_case_f2bool =>
      .OK (.Ebinop (.Ocmpf .Cne) e
        (make_floatconst CompCert4Lean.Lib.Floats.Float.zero))
  | .cast_case_s2bool =>
      .OK (.Ebinop (.Ocmpfs .Cne) e
        (make_singleconst CompCert4Lean.Lib.Floats.Float32.zero))
  | .cast_case_l2bool =>
      .OK (.Ebinop (.Ocmplu .Cne) e
        (make_longconst CompCert4Lean.Lib.Integers.Int64.zero))
  | .cast_case_struct _ _ => .OK e
  | .cast_case_union _ _ => .OK e
  | .cast_case_void => .OK e
  | .cast_case_default => error "Cshmgen.make_cast"

def make_boolean (e : CExpr) (ty : CType) : CExpr :=
  match CompCert4Lean.Cfrontend.Cop.classify_bool ty with
  | .bool_case_i => make_cmpu_ne_zero e
  | .bool_case_f =>
      .Ebinop (.Ocmpf .Cne) e
        (make_floatconst CompCert4Lean.Lib.Floats.Float.zero)
  | .bool_case_s =>
      .Ebinop (.Ocmpfs .Cne) e
        (make_singleconst CompCert4Lean.Lib.Floats.Float32.zero)
  | .bool_case_l =>
      .Ebinop (.Ocmplu .Cne) e
        (make_longconst CompCert4Lean.Lib.Integers.Int64.zero)
  | .bool_default => e

/-! ## Unary operators -/

def make_notbool (e : CExpr) (ty : CType) : Res CExpr :=
  match CompCert4Lean.Cfrontend.Cop.classify_bool ty with
  | .bool_case_i =>
      .OK (.Ebinop (.Ocmpu .Ceq) e
        (make_intconst CompCert4Lean.Lib.Integers.Int.zero))
  | .bool_case_f =>
      .OK (.Ebinop (.Ocmpf .Ceq) e
        (make_floatconst CompCert4Lean.Lib.Floats.Float.zero))
  | .bool_case_s =>
      .OK (.Ebinop (.Ocmpfs .Ceq) e
        (make_singleconst CompCert4Lean.Lib.Floats.Float32.zero))
  | .bool_case_l =>
      .OK (.Ebinop (.Ocmplu .Ceq) e
        (make_longconst CompCert4Lean.Lib.Integers.Int64.zero))
  | .bool_default => error "Cshmgen.make_notbool"

def make_neg (e : CExpr) (ty : CType) : Res CExpr :=
  match CompCert4Lean.Cfrontend.Cop.classify_neg ty with
  | .neg_case_i _ => .OK (.Eunop .Onegint e)
  | .neg_case_f => .OK (.Eunop .Onegf e)
  | .neg_case_s => .OK (.Eunop .Onegfs e)
  | .neg_case_l _ => .OK (.Eunop .Onegl e)
  | .neg_default => error "Cshmgen.make_neg"

def make_absfloat (e : CExpr) (ty : CType) : Res CExpr :=
  match CompCert4Lean.Cfrontend.Cop.classify_neg ty with
  | .neg_case_i sg => .OK (.Eunop .Oabsf (make_floatofint e sg))
  | .neg_case_f => .OK (.Eunop .Oabsf e)
  | .neg_case_s => .OK (.Eunop .Oabsf (make_floatofsingle e))
  | .neg_case_l sg => .OK (.Eunop .Oabsf (make_floatoflong e sg))
  | .neg_default => error "Cshmgen.make_absfloat"

def make_notint (e : CExpr) (ty : CType) : Res CExpr :=
  match CompCert4Lean.Cfrontend.Cop.classify_notint ty with
  | .notint_case_i _ => .OK (.Eunop .Onotint e)
  | .notint_case_l _ => .OK (.Eunop .Onotl e)
  | .notint_default => error "Cshmgen.make_notint"

/-! ## Binary operators -/

def make_binarith
    (iop iopu fop sop lop lopu : BinOp)
    (e1 : CExpr) (ty1 : CType) (e2 : CExpr) (ty2 : CType) : Res CExpr :=
  let c := CompCert4Lean.Cfrontend.Cop.classify_binarith ty1 ty2
  let ty := CompCert4Lean.Cfrontend.Cop.binarith_type c
  match make_cast ty1 ty e1 with
  | .Error message => .Error message
  | .OK e1' =>
      match make_cast ty2 ty e2 with
      | .Error message => .Error message
      | .OK e2' =>
          match c with
          | .bin_case_i .Signed => .OK (.Ebinop iop e1' e2')
          | .bin_case_i .Unsigned => .OK (.Ebinop iopu e1' e2')
          | .bin_case_f => .OK (.Ebinop fop e1' e2')
          | .bin_case_s => .OK (.Ebinop sop e1' e2')
          | .bin_case_l .Signed => .OK (.Ebinop lop e1' e2')
          | .bin_case_l .Unsigned => .OK (.Ebinop lopu e1' e2')
          | .bin_default => error "Cshmgen.make_binarith"

def make_add_ptr_int
    (ce : composite_env) (ty : CType) (si : signedness)
    (e1 e2 : CExpr) : Res CExpr :=
  match sizeof ce ty with
  | .Error message => .Error message
  | .OK sz =>
      if CompCert4Lean.X86_64.Archi.ptr64 then
        let n := make_longconst (CompCert4Lean.Lib.Integers.Int64.repr sz)
        .OK (.Ebinop .Oaddl e1 (.Ebinop .Omull n (make_longofint e2 si)))
      else
        let n := make_intconst (CompCert4Lean.Lib.Integers.Int.repr sz)
        .OK (.Ebinop .Oadd e1 (.Ebinop .Omul n e2))

def make_add_ptr_long
    (ce : composite_env) (ty : CType) (e1 e2 : CExpr) : Res CExpr :=
  match sizeof ce ty with
  | .Error message => .Error message
  | .OK sz =>
      if CompCert4Lean.X86_64.Archi.ptr64 then
        let n := make_longconst (CompCert4Lean.Lib.Integers.Int64.repr sz)
        .OK (.Ebinop .Oaddl e1 (.Ebinop .Omull n e2))
      else
        let n := make_intconst (CompCert4Lean.Lib.Integers.Int.repr sz)
        .OK (.Ebinop .Oadd e1 (.Ebinop .Omul n (.Eunop .Ointoflong e2)))

def make_add
    (ce : composite_env) (e1 : CExpr) (ty1 : CType)
    (e2 : CExpr) (ty2 : CType) : Res CExpr :=
  match CompCert4Lean.Cfrontend.Ctypes.typeconv ty1,
      CompCert4Lean.Cfrontend.Ctypes.typeconv ty2 with
  | .Tpointer ty _, .Tint _ si _ => make_add_ptr_int ce ty si e1 e2
  | .Tpointer ty _, .Tlong _ _ => make_add_ptr_long ce ty e1 e2
  | .Tint _ si _, .Tpointer ty _ => make_add_ptr_int ce ty si e2 e1
  | .Tlong _ _, .Tpointer ty _ => make_add_ptr_long ce ty e2 e1
  | _, _ =>
      make_binarith .Oadd .Oadd .Oaddf .Oaddfs .Oaddl .Oaddl e1 ty1 e2 ty2

def make_sub
    (ce : composite_env) (e1 : CExpr) (ty1 : CType)
    (e2 : CExpr) (ty2 : CType) : Res CExpr :=
  match CompCert4Lean.Cfrontend.Ctypes.typeconv ty1,
      CompCert4Lean.Cfrontend.Ctypes.typeconv ty2 with
  | .Tpointer ty _, .Tint _ si _ =>
      match sizeof ce ty with
      | .Error message => .Error message
      | .OK sz =>
          if CompCert4Lean.X86_64.Archi.ptr64 then
            let n := make_longconst (CompCert4Lean.Lib.Integers.Int64.repr sz)
            .OK (.Ebinop .Osubl e1 (.Ebinop .Omull n (make_longofint e2 si)))
          else
            let n := make_intconst (CompCert4Lean.Lib.Integers.Int.repr sz)
            .OK (.Ebinop .Osub e1 (.Ebinop .Omul n e2))
  | .Tpointer ty _, .Tpointer _ _ =>
      match sizeof ce ty with
      | .Error message => .Error message
      | .OK sz =>
          if CompCert4Lean.X86_64.Archi.ptr64 then
            let n := make_longconst (CompCert4Lean.Lib.Integers.Int64.repr sz)
            .OK (.Ebinop .Odivl (.Ebinop .Osubl e1 e2) n)
          else
            let n := make_intconst (CompCert4Lean.Lib.Integers.Int.repr sz)
            .OK (.Ebinop .Odiv (.Ebinop .Osub e1 e2) n)
  | .Tpointer ty _, .Tlong _ _ =>
      match sizeof ce ty with
      | .Error message => .Error message
      | .OK sz =>
          if CompCert4Lean.X86_64.Archi.ptr64 then
            let n := make_longconst (CompCert4Lean.Lib.Integers.Int64.repr sz)
            .OK (.Ebinop .Osubl e1 (.Ebinop .Omull n e2))
          else
            let n := make_intconst (CompCert4Lean.Lib.Integers.Int.repr sz)
            .OK (.Ebinop .Osub e1 (.Ebinop .Omul n (.Eunop .Ointoflong e2)))
  | _, _ =>
      make_binarith .Osub .Osub .Osubf .Osubfs .Osubl .Osubl e1 ty1 e2 ty2

def make_mul (e1 : CExpr) (ty1 : CType) (e2 : CExpr) (ty2 : CType) : Res CExpr :=
  make_binarith .Omul .Omul .Omulf .Omulfs .Omull .Omull e1 ty1 e2 ty2

def make_div (e1 : CExpr) (ty1 : CType) (e2 : CExpr) (ty2 : CType) : Res CExpr :=
  make_binarith .Odiv .Odivu .Odivf .Odivfs .Odivl .Odivlu e1 ty1 e2 ty2

def make_binarith_int
    (iop iopu lop lopu : BinOp)
    (e1 : CExpr) (ty1 : CType) (e2 : CExpr) (ty2 : CType) : Res CExpr :=
  let c := CompCert4Lean.Cfrontend.Cop.classify_binarith ty1 ty2
  let ty := CompCert4Lean.Cfrontend.Cop.binarith_type c
  match make_cast ty1 ty e1 with
  | .Error message => .Error message
  | .OK e1' =>
      match make_cast ty2 ty e2 with
      | .Error message => .Error message
      | .OK e2' =>
          match c with
          | .bin_case_i .Signed => .OK (.Ebinop iop e1' e2')
          | .bin_case_i .Unsigned => .OK (.Ebinop iopu e1' e2')
          | .bin_case_l .Signed => .OK (.Ebinop lop e1' e2')
          | .bin_case_l .Unsigned => .OK (.Ebinop lopu e1' e2')
          | .bin_case_f | .bin_case_s | .bin_default =>
              error "Cshmgen.make_binarith_int"

def make_mod (e1 : CExpr) (ty1 : CType) (e2 : CExpr) (ty2 : CType) : Res CExpr :=
  make_binarith_int .Omod .Omodu .Omodl .Omodlu e1 ty1 e2 ty2

def make_and (e1 : CExpr) (ty1 : CType) (e2 : CExpr) (ty2 : CType) : Res CExpr :=
  make_binarith_int .Oand .Oand .Oandl .Oandl e1 ty1 e2 ty2

def make_or (e1 : CExpr) (ty1 : CType) (e2 : CExpr) (ty2 : CType) : Res CExpr :=
  make_binarith_int .Oor .Oor .Oorl .Oorl e1 ty1 e2 ty2

def make_xor (e1 : CExpr) (ty1 : CType) (e2 : CExpr) (ty2 : CType) : Res CExpr :=
  make_binarith_int .Oxor .Oxor .Oxorl .Oxorl e1 ty1 e2 ty2

def make_shl (e1 : CExpr) (ty1 : CType) (e2 : CExpr) (ty2 : CType) : Res CExpr :=
  match CompCert4Lean.Cfrontend.Ctypes.typeconv ty1,
      CompCert4Lean.Cfrontend.Ctypes.typeconv ty2 with
  | .Tint _ _ _, .Tint _ _ _ => .OK (.Ebinop .Oshl e1 e2)
  | .Tlong _ _, .Tint _ _ _ => .OK (.Ebinop .Oshll e1 e2)
  | .Tint _ _ _, .Tlong _ _ => .OK (.Ebinop .Oshl e1 (.Eunop .Ointoflong e2))
  | .Tlong _ _, .Tlong _ _ => .OK (.Ebinop .Oshll e1 (.Eunop .Ointoflong e2))
  | _, _ => error "Cshmgen.make_shl"

def make_shr (e1 : CExpr) (ty1 : CType) (e2 : CExpr) (ty2 : CType) : Res CExpr :=
  match CompCert4Lean.Cfrontend.Ctypes.typeconv ty1,
      CompCert4Lean.Cfrontend.Ctypes.typeconv ty2 with
  | .Tint .I32 .Unsigned _, .Tint _ _ _ => .OK (.Ebinop .Oshru e1 e2)
  | .Tint _ _ _, .Tint _ _ _ => .OK (.Ebinop .Oshr e1 e2)
  | .Tlong .Signed _, .Tint _ _ _ => .OK (.Ebinop .Oshrl e1 e2)
  | .Tlong .Unsigned _, .Tint _ _ _ => .OK (.Ebinop .Oshrlu e1 e2)
  | .Tint .I32 .Unsigned _, .Tlong _ _ =>
      .OK (.Ebinop .Oshru e1 (.Eunop .Ointoflong e2))
  | .Tint _ _ _, .Tlong _ _ => .OK (.Ebinop .Oshr e1 (.Eunop .Ointoflong e2))
  | .Tlong .Signed _, .Tlong _ _ =>
      .OK (.Ebinop .Oshrl e1 (.Eunop .Ointoflong e2))
  | .Tlong .Unsigned _, .Tlong _ _ =>
      .OK (.Ebinop .Oshrlu e1 (.Eunop .Ointoflong e2))
  | _, _ => error "Cshmgen.make_shr"

def make_cmp_ptr (c : Comparison) (e1 e2 : CExpr) : CExpr :=
  .Ebinop
    (if CompCert4Lean.X86_64.Archi.ptr64 then .Ocmplu c else .Ocmpu c)
    e1 e2

def make_cmp
    (c : Comparison) (e1 : CExpr) (ty1 : CType)
    (e2 : CExpr) (ty2 : CType) : Res CExpr :=
  match CompCert4Lean.Cfrontend.Ctypes.typeconv ty1,
      CompCert4Lean.Cfrontend.Ctypes.typeconv ty2 with
  | .Tpointer _ _, .Tpointer _ _ => .OK (make_cmp_ptr c e1 e2)
  | .Tpointer _ _, .Tint _ si _ =>
      .OK (make_cmp_ptr c e1
        (if CompCert4Lean.X86_64.Archi.ptr64 then make_longofint e2 si else e2))
  | .Tint _ si _, .Tpointer _ _ =>
      .OK (make_cmp_ptr c
        (if CompCert4Lean.X86_64.Archi.ptr64 then make_longofint e1 si else e1) e2)
  | .Tpointer _ _, .Tlong _ _ =>
      .OK (make_cmp_ptr c e1
        (if CompCert4Lean.X86_64.Archi.ptr64 then e2 else .Eunop .Ointoflong e2))
  | .Tlong _ _, .Tpointer _ _ =>
      .OK (make_cmp_ptr c
        (if CompCert4Lean.X86_64.Archi.ptr64 then e1 else .Eunop .Ointoflong e1) e2)
  | _, _ =>
      make_binarith (.Ocmp c) (.Ocmpu c) (.Ocmpf c) (.Ocmpfs c)
        (.Ocmpl c) (.Ocmplu c) e1 ty1 e2 ty2

/-! ## Bitfields and memory access -/

def make_extract_bitfield
    (sz : intsize) (sg : signedness) (pos width : Z)
    (addr : CExpr) : Res CExpr :=
  if zleBool z0 pos && zltBool z0 width &&
      zleBool (zAdd pos width) (CompCert4Lean.Cfrontend.Cop.bitsize_carrier sz) then
    let amount1 := CompCert4Lean.Lib.Integers.Int.repr
      (zSub
        (zSub CompCert4Lean.Lib.Integers.Int.zwordsize
          (CompCert4Lean.Cfrontend.Cop.first_bit sz pos width))
        width)
    let amount2 := CompCert4Lean.Lib.Integers.Int.repr
      (zSub CompCert4Lean.Lib.Integers.Int.zwordsize width)
    let e1 : CExpr := .Eload (CompCert4Lean.Cfrontend.Cop.chunk_for_carrier sz) addr
    let e2 : CExpr := .Ebinop .Oshl e1 (make_intconst amount1)
    let op : BinOp :=
      if decide (sz = .IBool) || decide (sg = .Unsigned) then .Oshru else .Oshr
    .OK (.Ebinop op e2 (make_intconst amount2))
  else
    error "Cshmgen.extract_bitfield"

def make_load (addr : CExpr) (tyRes : CType) (bf : bitfield) : Res CExpr :=
  match bf with
  | .Full =>
      match CompCert4Lean.Cfrontend.Ctypes.access_mode tyRes with
      | .By_value chunk => .OK (.Eload chunk addr)
      | .By_reference => .OK addr
      | .By_copy => .OK addr
      | .By_nothing => error "Cshmgen.make_load"
  | .Bits sz sg pos width => make_extract_bitfield sz sg pos width addr

def make_store_bitfield
    (sz : intsize) (_sg : signedness) (pos width : Z)
    (addr val : CExpr) : Res CStmt :=
  if zleBool z0 pos && zltBool z0 width &&
      zleBool (zAdd pos width) (CompCert4Lean.Cfrontend.Cop.bitsize_carrier sz) then
    let amount := CompCert4Lean.Cfrontend.Cop.first_bit sz pos width
    let mask := CompCert4Lean.Lib.Integers.Int.shl
      (CompCert4Lean.Lib.Integers.Int.repr (zSub (twoP width) z1))
      (CompCert4Lean.Lib.Integers.Int.repr amount)
    let e1 : CExpr := .Eload (CompCert4Lean.Cfrontend.Cop.chunk_for_carrier sz) addr
    let e2 : CExpr := .Ebinop .Oshl val
      (make_intconst (CompCert4Lean.Lib.Integers.Int.repr amount))
    let e3 : CExpr := .Ebinop .Oor
      (.Ebinop .Oand e2 (make_intconst mask))
      (.Ebinop .Oand e1
        (make_intconst (CompCert4Lean.Lib.Integers.Int.not mask)))
    .OK (.Sstore (CompCert4Lean.Cfrontend.Cop.chunk_for_carrier sz) addr e3)
  else
    error "Cshmgen.make_store_bitfield"

def make_memcpy
    (ce : composite_env) (dst src : CExpr) (ty : CType) : Res CStmt :=
  match sizeof ce ty with
  | .Error message => .Error message
  | .OK sz =>
      .OK (.Sbuiltin none
        (.EF_memcpy sz (CompCert4Lean.Cfrontend.Ctypes.alignof_blockcopy ce ty))
        [dst, src])

def make_store
    (ce : composite_env) (addr : CExpr) (ty : CType)
    (bf : bitfield) (rhs : CExpr) : Res CStmt :=
  match bf with
  | .Full =>
      match CompCert4Lean.Cfrontend.Ctypes.access_mode ty with
      | .By_value chunk => .OK (.Sstore chunk addr rhs)
      | .By_copy => make_memcpy ce addr rhs ty
      | _ => error "Cshmgen.make_store"
  | .Bits sz sg pos width => make_store_bitfield sz sg pos width addr rhs

/-! ## Translation of operators -/

def transl_unop
    (op : CompCert4Lean.Cfrontend.Cop.unary_operation)
    (a : CExpr) (ta : CType) : Res CExpr :=
  match op with
  | .Onotbool => make_notbool a ta
  | .Onotint => make_notint a ta
  | .Oneg => make_neg a ta
  | .Oabsfloat => make_absfloat a ta

def transl_binop
    (ce : composite_env) (op : CompCert4Lean.Cfrontend.Cop.binary_operation)
    (a : CExpr) (ta : CType) (b : CExpr) (tb : CType) : Res CExpr :=
  match op with
  | .Oadd => make_add ce a ta b tb
  | .Osub => make_sub ce a ta b tb
  | .Omul => make_mul a ta b tb
  | .Odiv => make_div a ta b tb
  | .Omod => make_mod a ta b tb
  | .Oand => make_and a ta b tb
  | .Oor => make_or a ta b tb
  | .Oxor => make_xor a ta b tb
  | .Oshl => make_shl a ta b tb
  | .Oshr => make_shr a ta b tb
  | .Oeq => make_cmp .Ceq a ta b tb
  | .One => make_cmp .Cne a ta b tb
  | .Olt => make_cmp .Clt a ta b tb
  | .Ogt => make_cmp .Cgt a ta b tb
  | .Ole => make_cmp .Cle a ta b tb
  | .Oge => make_cmp .Cge a ta b tb

/-! ## Translation of field accesses -/

def make_field_access
    (ce : composite_env) (ty : CType) (f : ident)
    (a : CExpr) : Res (CExpr × bitfield) :=
  let offsetResult : Res (Z × bitfield) :=
    match ty with
    | .Tstruct id _ =>
        match CompCert4Lean.Lib.Maps.PTree.get id ce with
        | none =>
            .Error
              [CompCert4Lean.Common.Errors.MSG (ofString "Undefined struct "),
               CompCert4Lean.Common.Errors.CTX id]
        | some co => CompCert4Lean.Cfrontend.Ctypes.field_offset ce f co.co_members
    | .Tunion id _ =>
        match CompCert4Lean.Lib.Maps.PTree.get id ce with
        | none =>
            .Error
              [CompCert4Lean.Common.Errors.MSG (ofString "Undefined union "),
               CompCert4Lean.Common.Errors.CTX id]
        | some co => CompCert4Lean.Cfrontend.Ctypes.union_field_offset ce f co.co_members
    | _ => error "Cshmgen.make_field_access"
  match offsetResult with
  | .Error message => .Error message
  | .OK (ofs, bf) =>
      let a' : CExpr :=
        if CompCert4Lean.X86_64.Archi.ptr64 then
          .Ebinop .Oaddl a
            (make_longconst (CompCert4Lean.Lib.Integers.Int64.repr ofs))
        else
          .Ebinop .Oadd a
            (make_intconst (CompCert4Lean.Lib.Integers.Int.repr ofs))
      .OK (a', bf)

/-! ## Translation of expressions -/

mutual
  def transl_expr (ce : composite_env) : LExpr → Res CExpr
    | .Econst_int n _ => .OK (make_intconst n)
    | .Econst_float n _ => .OK (make_floatconst n)
    | .Econst_single n _ => .OK (make_singleconst n)
    | .Econst_long n _ => .OK (make_longconst n)
    | .Evar id ty => make_load (.Eaddrof id) ty .Full
    | .Etempvar id _ => .OK (.Evar id)
    | .Ederef b ty =>
        match transl_expr ce b with
        | .Error message => .Error message
        | .OK tb => make_load tb ty .Full
    | .Eaddrof b _ =>
        match transl_lvalue ce b with
        | .Error message => .Error message
        | .OK (tb, .Full) => .OK tb
        | .OK (_, .Bits _ _ _ _) => error "Cshmgen.transl_expr: addrof bitfield"
    | .Eunop op b _ =>
        match transl_expr ce b with
        | .Error message => .Error message
        | .OK tb => transl_unop op tb (CompCert4Lean.Cfrontend.Clight.typeof b)
    | .Ebinop op b c _ =>
        match transl_expr ce b with
        | .Error message => .Error message
        | .OK tb =>
            match transl_expr ce c with
            | .Error message => .Error message
            | .OK tc =>
                transl_binop ce op tb (CompCert4Lean.Cfrontend.Clight.typeof b)
                  tc (CompCert4Lean.Cfrontend.Clight.typeof c)
    | .Ecast b ty =>
        match transl_expr ce b with
        | .Error message => .Error message
        | .OK tb => make_cast (CompCert4Lean.Cfrontend.Clight.typeof b) ty tb
    | .Efield b i ty =>
        match transl_expr ce b with
        | .Error message => .Error message
        | .OK tb =>
            match make_field_access ce (CompCert4Lean.Cfrontend.Clight.typeof b) i tb with
            | .Error message => .Error message
            | .OK (addr, bf) => make_load addr ty bf
    | .Esizeof ty' _ =>
        match sizeof ce ty' with
        | .Error message => .Error message
        | .OK sz => .OK (make_ptrofsconst sz)
    | .Ealignof ty' _ =>
        match alignof ce ty' with
        | .Error message => .Error message
        | .OK al => .OK (make_ptrofsconst al)

  def transl_lvalue (ce : composite_env) : LExpr → Res (CExpr × bitfield)
    | .Evar id _ => .OK (.Eaddrof id, .Full)
    | .Ederef b _ =>
        match transl_expr ce b with
        | .Error message => .Error message
        | .OK tb => .OK (tb, .Full)
    | .Efield b i _ =>
        match transl_expr ce b with
        | .Error message => .Error message
        | .OK tb =>
            make_field_access ce (CompCert4Lean.Cfrontend.Clight.typeof b) i tb
    | _ => error "Cshmgen.transl_lvalue"
end

def transl_arglist
    (ce : composite_env) : List LExpr → List CType → Res (List CExpr)
  | [], [] => .OK []
  | [], _ :: _ => error "Cshmgen.transl_arglist: arity mismatch"
  | a1 :: a2, ty1 :: ty2 =>
      match transl_expr ce a1 with
      | .Error message => .Error message
      | .OK ta1 =>
          match make_cast (CompCert4Lean.Cfrontend.Clight.typeof a1) ty1 ta1 with
          | .Error message => .Error message
          | .OK ta1' =>
              match transl_arglist ce a2 ty2 with
              | .Error message => .Error message
              | .OK ta2 => .OK (ta1' :: ta2)
  | a1 :: a2, [] =>
      match transl_expr ce a1 with
      | .Error message => .Error message
      | .OK ta1 =>
          let targetTy := CompCert4Lean.Cfrontend.Ctypes.default_argument_conversion
            (CompCert4Lean.Cfrontend.Clight.typeof a1)
          match make_cast (CompCert4Lean.Cfrontend.Clight.typeof a1) targetTy ta1 with
          | .Error message => .Error message
          | .OK ta1' =>
              match transl_arglist ce a2 [] with
              | .Error message => .Error message
              | .OK ta2 => .OK (ta1' :: ta2)

def typlist_of_arglist : List LExpr → List CType → List Xtype
  | [], _ => []
  | _a1 :: a2, ty1 :: ty2 =>
      CompCert4Lean.Cfrontend.Ctypes.argtype_of_type ty1 ::
        typlist_of_arglist a2 ty2
  | a1 :: a2, [] =>
      CompCert4Lean.Cfrontend.Ctypes.argtype_of_type
        (CompCert4Lean.Cfrontend.Ctypes.default_argument_conversion
          (CompCert4Lean.Cfrontend.Clight.typeof a1)) ::
        typlist_of_arglist a2 []

def make_normalization (t : CType) (a : CExpr) : CExpr :=
  match t with
  | .Tint .IBool _ _ => .Eunop .Ocast8unsigned a
  | .Tint .I8 .Signed _ => .Eunop .Ocast8signed a
  | .Tint .I8 .Unsigned _ => .Eunop .Ocast8unsigned a
  | .Tint .I16 .Signed _ => .Eunop .Ocast16signed a
  | .Tint .I16 .Unsigned _ => .Eunop .Ocast16unsigned a
  | _ => a

def make_funcall
    (x : Option ident) (tres : CType) (sg : Signature)
    (fn : CExpr) (args : List CExpr) : CStmt :=
  match x, CompCert4Lean.X86.Conventions1.return_value_needs_normalization sg.sig_res with
  | some id, true =>
      .Sseq (.Scall x sg fn args)
        (.Sset id (make_normalization tres (.Evar id)))
  | _, _ => .Scall x sg fn args

/-! ## Translation of statements -/

mutual
  def transl_statement
      (ce : composite_env) (tyret : CType) (nbrk ncnt : Nat) : LStmt → Res CStmt
    | .Sskip => .OK .Sskip
    | .Sassign b c =>
        match transl_lvalue ce b with
        | .Error message => .Error message
        | .OK (tb, bf) =>
            match transl_expr ce c with
            | .Error message => .Error message
            | .OK tc =>
                match make_cast (CompCert4Lean.Cfrontend.Clight.typeof c)
                    (CompCert4Lean.Cfrontend.Clight.typeof b) tc with
                | .Error message => .Error message
                | .OK tc' =>
                    make_store ce tb (CompCert4Lean.Cfrontend.Clight.typeof b) bf tc'
    | .Sset x b =>
        match transl_expr ce b with
        | .Error message => .Error message
        | .OK tb => .OK (.Sset x tb)
    | .Scall x b cl =>
        match CompCert4Lean.Cfrontend.Clight.typeof b with
        | .Tfunction args res cconv
        | .Tpointer (.Tfunction args res cconv) _ =>
            match transl_expr ce b with
            | .Error message => .Error message
            | .OK tb =>
                match transl_arglist ce cl args with
                | .Error message => .Error message
                | .OK tcl =>
                    let sg : Signature :=
                      { sig_args := typlist_of_arglist cl args
                        sig_res := CompCert4Lean.Cfrontend.Ctypes.rettype_of_type res
                        sig_cc := cconv }
                    .OK (make_funcall x res sg tb tcl)
        | _ => error "Cshmgen.transl_stmt(call)"
    | .Sbuiltin x ef tyargs bl =>
        match transl_arglist ce bl tyargs with
        | .Error message => .Error message
        | .OK tbl => .OK (.Sbuiltin x ef tbl)
    | .Ssequence s1 s2 =>
        match transl_statement ce tyret nbrk ncnt s1 with
        | .Error message => .Error message
        | .OK ts1 =>
            match transl_statement ce tyret nbrk ncnt s2 with
            | .Error message => .Error message
            | .OK ts2 => .OK (.Sseq ts1 ts2)
    | .Sifthenelse e s1 s2 =>
        match transl_expr ce e with
        | .Error message => .Error message
        | .OK te =>
            match transl_statement ce tyret nbrk ncnt s1 with
            | .Error message => .Error message
            | .OK ts1 =>
                match transl_statement ce tyret nbrk ncnt s2 with
                | .Error message => .Error message
                | .OK ts2 =>
                    .OK (.Sifthenelse
                      (make_boolean te (CompCert4Lean.Cfrontend.Clight.typeof e))
                      ts1 ts2)
    | .Sloop s1 s2 =>
        match transl_statement ce tyret 1 0 s1 with
        | .Error message => .Error message
        | .OK ts1 =>
            match transl_statement ce tyret 0 (Nat.succ ncnt) s2 with
            | .Error message => .Error message
            | .OK ts2 => .OK (.Sblock (.Sloop (.Sseq (.Sblock ts1) ts2)))
    | .Sbreak => .OK (.Sexit nbrk)
    | .Scontinue => .OK (.Sexit ncnt)
    | .Sreturn (some e) =>
        match transl_expr ce e with
        | .Error message => .Error message
        | .OK te =>
            match make_cast (CompCert4Lean.Cfrontend.Clight.typeof e) tyret te with
            | .Error message => .Error message
            | .OK te' => .OK (.Sreturn (some te'))
    | .Sreturn none => .OK (.Sreturn none)
    | .Sswitch a sl =>
        match transl_expr ce a with
        | .Error message => .Error message
        | .OK ta =>
            match transl_lbl_stmt ce tyret 0 (Nat.succ ncnt) sl with
            | .Error message => .Error message
            | .OK tsl =>
                match CompCert4Lean.Cfrontend.Clight.typeof a with
                | .Tint _ _ _ => .OK (.Sblock (.Sswitch false ta tsl))
                | .Tlong _ _ => .OK (.Sblock (.Sswitch true ta tsl))
                | _ => error "Cshmgen.transl_stmt(switch)"
    | .Slabel lbl s =>
        match transl_statement ce tyret nbrk ncnt s with
        | .Error message => .Error message
        | .OK ts => .OK (.Slabel lbl ts)
    | .Sgoto lbl => .OK (.Sgoto lbl)

  def transl_lbl_stmt
      (ce : composite_env) (tyret : CType) (nbrk ncnt : Nat) : LLblStmt → Res CLblStmt
    | .LSnil => .OK .LSnil
    | .LScons n s sl =>
        match transl_statement ce tyret nbrk ncnt s with
        | .Error message => .Error message
        | .OK ts =>
            match transl_lbl_stmt ce tyret nbrk ncnt sl with
            | .Error message => .Error message
            | .OK tsl => .OK (.LScons n ts tsl)
end

/-! ## Translation of functions and programs -/

def transl_var (ce : composite_env) (v : ident × CType) : Res (ident × Z) :=
  match sizeof ce v.2 with
  | .Error message => .Error message
  | .OK sz => .OK (v.1, sz)

def signature_of_function (f : LFunction) : Signature :=
  { sig_args := f.fn_params.map (fun p =>
      CompCert4Lean.Cfrontend.Ctypes.argtype_of_type p.2)
    sig_res := CompCert4Lean.Cfrontend.Ctypes.rettype_of_type f.fn_return
    sig_cc := f.fn_callconv }

def transl_function (ce : composite_env) (f : LFunction) : Res CFunction :=
  match transl_statement ce f.fn_return 1 0 f.fn_body with
  | .Error message => .Error message
  | .OK tbody =>
      match CompCert4Lean.Common.Errors.mmap (transl_var ce) f.fn_vars with
      | .Error message => .Error message
      | .OK tvars =>
          .OK
            { fn_sig := signature_of_function f
              fn_params := f.fn_params.map Prod.fst
              fn_vars := tvars
              fn_temps := f.fn_temps.map Prod.fst
              fn_body := tbody }

def transl_fundef (ce : composite_env) (_id : ident) (f : LFundef) : Res CFundef :=
  match f with
  | .Internal g =>
      match transl_function ce g with
      | .Error message => .Error message
      | .OK tg => .OK (.Internal tg)
  | .External ef args res cconv =>
      match CompCert4Lean.Common.AST.signature_eq
          (CompCert4Lean.Common.AST.ef_sig ef)
          (CompCert4Lean.Cfrontend.Ctypes.signature_of_type args res cconv) with
      | .left _ => .OK (.External ef)
      | .right _ => error "Cshmgen.transl_fundef: wrong external signature"

def transl_globvar (_id : ident) (_ty : CType) : Res Unit := .OK ()

def transl_program (p : LProgram) : Res CProgram :=
  CompCert4Lean.Common.AST.transform_partial_program2
    (transl_fundef p.prog_comp_env)
    transl_globvar
    (CompCert4Lean.Cfrontend.Ctypes.program_of_program p)

end CompCert4Lean.Cfrontend.Cshmgen
