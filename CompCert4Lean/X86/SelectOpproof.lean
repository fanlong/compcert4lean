import CompCert4Lean.X86.SelectOp

/-!
# Correctness surface for x86 instruction-selection smart constructors

The two constructor-soundness predicates are executable definitions from
`x86/SelectOpproof.v`.  The remaining declarations are exact proposition
descriptors for the proofs assigned to the later proof-migration phase.
-/

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev Ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev comparison := CompCert4Lean.Lib.Integers.comparison
private abbrev env := CompCert4Lean.Backend.Cminor.env
private abbrev op_addressing := CompCert4Lean.X86.Op.addressing
private abbrev z8 : Z := ZArith.BinInt.Z.of_nat 8
private abbrev z16 : Z := ZArith.BinInt.Z.of_nat 16
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

def unary_constructor_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val)
    (e : env) (m : mem) (cstr : expr → expr) (sem : val → val) : Prop :=
  ∀ (le : letenv) (a : expr) (x : val),
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a x →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le (cstr a) v ∧ Val.lessdef (sem x) v

def binary_constructor_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val)
    (e : env) (m : mem) (cstr : expr → expr → expr)
    (sem : val → val → val) : Prop :=
  ∀ (le : letenv) (a : expr) (x : val) (b : expr) (y : val),
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a x →
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le b y →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le (cstr a b) v ∧ Val.lessdef (sem x y) v

/-! ## Exact statement descriptors for later proof migration -/

def eval_Olea_ptrStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : val) (a : op_addressing) (el : List val) (m : mem),
    eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge sp (Olea_ptr a) el m = eval_addressing ge sp a el

def eval_addrsymbolStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (ctx : RelocationContext) (le : letenv) (id : ident) (ofs : Ptrofs),
    ∃ v,
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le (addrsymbol ctx id ofs) v ∧
      Val.lessdef (Genv.symbol_address ge id ofs) v

def eval_addrstackStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (le : letenv) (ofs : Ptrofs),
    ∃ v,
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le (addrstack ofs) v ∧
      Val.lessdef (Val.offset_ptr sp ofs) v

def eval_notintStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m notint Val.notint

def eval_addimmStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (n : CCInt),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m (addimm n)
      (fun x => Val.add x (.Vint n))

def eval_addStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m SelectOp.add Val.add

def eval_subStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m SelectOp.sub Val.sub

def eval_negintStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m negint Val.neg

def eval_shlimmStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (n : CCInt),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m (fun a => shlimm a n)
      (fun x => Val.shl x (.Vint n))

def eval_shruimmStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (n : CCInt),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m (fun a => shruimm a n)
      (fun x => Val.shru x (.Vint n))

def eval_shrimmStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (n : CCInt),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m (fun a => shrimm a n)
      (fun x => Val.shr x (.Vint n))

def eval_mulimm_baseStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (n : CCInt),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m (mulimm_base n)
      (fun x => Val.mul x (.Vint n))

def eval_mulimmStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (n : CCInt),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m (mulimm n)
      (fun x => Val.mul x (.Vint n))

def eval_mulStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m SelectOp.mul Val.mul

def eval_mulhsStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m mulhs Val.mulhs

def eval_mulhuStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m mulhu Val.mulhu

def eval_andimmStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (n : CCInt),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m (andimm n)
      (fun x => Val.and x (.Vint n))

def eval_andStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m SelectOp.and Val.and

def eval_orimmStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (n : CCInt),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m (orimm n)
      (fun x => Val.or x (.Vint n))

def eval_same_exprStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (a1 a2 : expr) (le : letenv) (v1 v2 : val),
    same_expr_pure a1 a2 = true →
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a1 v1 →
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a2 v2 →
      a1 = a2 ∧ v1 = v2

def int_add_sub_eqStatement : Prop :=
  ∀ (x y z : CCInt),
    CompCert4Lean.Lib.Integers.Int.add x y = z →
      CompCert4Lean.Lib.Integers.Int.sub z x = y

def eval_orStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m SelectOp.or Val.or

def eval_xorimmStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (n : CCInt),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m (xorimm n)
      (fun x => Val.xor x (.Vint n))

def eval_xorStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m SelectOp.xor Val.xor

def eval_divs_baseStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (le : letenv) (a b : expr) (x y z : val),
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a x →
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le b y →
    Val.divs x y = some z →
      ∃ v,
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le (divs_base a b) v ∧
        Val.lessdef z v

def eval_divu_baseStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (le : letenv) (a b : expr) (x y z : val),
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a x →
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le b y →
    Val.divu x y = some z →
      ∃ v,
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le (divu_base a b) v ∧
        Val.lessdef z v

def eval_mods_baseStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (le : letenv) (a b : expr) (x y z : val),
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a x →
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le b y →
    Val.mods x y = some z →
      ∃ v,
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le (mods_base a b) v ∧
        Val.lessdef z v

def eval_modu_baseStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (le : letenv) (a b : expr) (x y z : val),
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a x →
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le b y →
    Val.modu x y = some z →
      ∃ v,
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le (modu_base a b) v ∧
        Val.lessdef z v

def eval_shrximmStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (le : letenv) (a : expr) (n : CCInt) (x z : val),
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a x →
    Val.shrx x (.Vint n) = some z →
      ∃ v,
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le (shrximm a n) v ∧
        Val.lessdef z v

def eval_shlStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m shl Val.shl

def eval_shrStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m shr Val.shr

def eval_shruStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m shru Val.shru

def eval_negfStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m negf Val.negf

def eval_absfStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m absf Val.absf

def eval_addfStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m addf Val.addf

def eval_subfStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m subf Val.subf

def eval_mulfStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m mulf Val.mulf

def eval_negfsStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m negfs Val.negfs

def eval_absfsStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m absfs Val.absfs

def eval_addfsStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m addfs Val.addfs

def eval_subfsStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m subfs Val.subfs

def eval_mulfsStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m mulfs Val.mulfs

def eval_compimmStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (default : comparison → CCInt → condition)
      (intsem : comparison → CCInt → CCInt → Bool)
      (sem : comparison → val → val → val),
    (∀ c x y, sem c (.Vint x) (.Vint y) = Val.of_bool (intsem c x y)) →
    (∀ c v, sem c .Vundef v = .Vundef) →
    (∀ x y, sem .Ceq (.Vint x) (.Vint y) = Val.of_bool (Int.eq x y)) →
    (∀ x y, sem .Cne (.Vint x) (.Vint y) = Val.of_bool (!(Int.eq x y))) →
    (∀ c v n,
      sem c v (.Vint n) =
        Val.of_optbool (eval_condition (default c n) [v] m)) →
    ∀ (le : letenv) (c : comparison) (a : expr) (n2 : CCInt) (x : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a x →
        ∃ v,
          eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le (compimm default intsem c a n2) v ∧
          Val.lessdef (sem c x (.Vint n2)) v

def eval_compimm_swapStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (default : comparison → CCInt → condition)
      (intsem : comparison → CCInt → CCInt → Bool)
      (sem : comparison → val → val → val),
    (∀ c x y, sem c (.Vint x) (.Vint y) = Val.of_bool (intsem c x y)) →
    (∀ c v, sem c .Vundef v = .Vundef) →
    (∀ x y, sem .Ceq (.Vint x) (.Vint y) = Val.of_bool (Int.eq x y)) →
    (∀ x y, sem .Cne (.Vint x) (.Vint y) = Val.of_bool (!(Int.eq x y))) →
    (∀ c v n,
      sem c v (.Vint n) =
        Val.of_optbool (eval_condition (default c n) [v] m)) →
    (∀ c x y, sem (swap_comparison c) x y = sem c y x) →
    ∀ (le : letenv) (c : comparison) (a : expr) (n2 : CCInt) (x : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a x →
        ∃ v,
          eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le
            (compimm default intsem (swap_comparison c) a n2) v ∧
          Val.lessdef (sem c (.Vint n2) x) v

def eval_compStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (c : comparison),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m (comp c) (Val.cmp c)

def eval_compuStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (c : comparison),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m (compu c)
      (Val.cmpu (Mem.valid_pointer m) c)

def eval_compfStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (c : comparison),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m (compf c) (Val.cmpf c)

def eval_compfsStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (c : comparison),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m (compfs c) (Val.cmpfs c)

def eval_cast8signedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m cast8signed (Val.sign_ext z8)

def eval_cast8unsignedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m cast8unsigned (Val.zero_ext z8)

def eval_cast16signedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m cast16signed (Val.sign_ext z16)

def eval_cast16unsignedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m cast16unsigned (Val.zero_ext z16)

def eval_selectStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (le : letenv) (ty : typ) (cond : condition) (al : exprlist)
      (vl : List val) (a1 : expr) (v1 : val) (a2 : expr) (v2 : val),
    select_supported ty = true →
    eval_exprlist (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le al vl →
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a1 v1 →
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a2 v2 →
      ∃ v,
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le (SelectOp.select ty cond al a1 a2) v ∧
        Val.lessdef (Val.select (eval_condition cond vl m) v1 v2 ty) v

def eval_singleoffloatStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m singleoffloat Val.singleoffloat

def eval_floatofsingleStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m floatofsingle Val.floatofsingle

def eval_intoffloatStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (le : letenv) (a : expr) (x y : val),
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a x →
    Val.intoffloat x = some y →
      ∃ v,
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le (SelectOp.intoffloat a) v ∧
        Val.lessdef y v

def eval_floatofintStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (le : letenv) (a : expr) (x y : val),
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a x →
    Val.floatofint (binary64_certificate := binary64_certificate) x = some y →
      ∃ v,
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le (SelectOp.floatofint (binary64_certificate := binary64_certificate) a) v ∧
        Val.lessdef y v

def eval_intuoffloatStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (le : letenv) (a : expr) (x y : val),
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a x →
    Val.intuoffloat x = some y →
      ∃ v,
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le (SelectOp.intuoffloat (binary64_certificate := binary64_certificate) a) v ∧
        Val.lessdef y v

def eval_floatofintuStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (le : letenv) (a : expr) (x y : val),
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a x →
    Val.floatofintu (binary64_certificate := binary64_certificate) x = some y →
      ∃ v,
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le (SelectOp.floatofintu (binary64_certificate := binary64_certificate) a) v ∧
        Val.lessdef y v

def eval_intofsingleStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (le : letenv) (a : expr) (x y : val),
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a x →
    Val.intofsingle x = some y →
      ∃ v,
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le (SelectOp.intofsingle a) v ∧
        Val.lessdef y v

def eval_singleofintStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (le : letenv) (a : expr) (x y : val),
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a x →
    Val.singleofint (binary32_certificate := binary32_certificate) x = some y →
      ∃ v,
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le (SelectOp.singleofint (binary32_certificate := binary32_certificate) a) v ∧
        Val.lessdef y v

def eval_intuofsingleStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (le : letenv) (a : expr) (x y : val),
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a x →
    Val.intuofsingle x = some y →
      ∃ v,
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le (SelectOp.intuofsingle (binary64_certificate := binary64_certificate) a) v ∧
        Val.lessdef y v

def eval_singleofintuStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (le : letenv) (a : expr) (x y : val),
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a x →
    Val.singleofintu (binary32_certificate := binary32_certificate) x = some y →
      ∃ v,
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le (SelectOp.singleofintu (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) a) v ∧
        Val.lessdef y v

def eval_addressingStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (le : letenv) (chunk : memory_chunk) (a : expr) (v : val)
      (b : block) (ofs : Ptrofs),
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a v →
    v = .Vptr b ofs →
      match SelectOp.addressing chunk a with
      | (mode, args) =>
          ∃ vl,
            eval_exprlist (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le args vl ∧
            eval_addressing ge sp mode vl = some v

def eval_builtin_arg_addrStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (addr : op_addressing) (al : exprlist) (vl : List val) (v : val),
    eval_exprlist (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m [] al vl →
    eval_addressing ge sp addr vl = some v →
      CompCert4Lean.Backend.CminorSel.eval_builtin_arg (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m
        (builtin_arg_addr addr al) v

def eval_builtin_argStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (a : expr) (v : val),
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m [] a v →
      CompCert4Lean.Backend.CminorSel.eval_builtin_arg (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m
        (SelectOp.builtin_arg a) v

def eval_platform_builtinStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
      (bf : CompCert4Lean.X86.Builtins1.platform_builtin) (al : exprlist)
      (a : expr) (vl : List val) (v : val) (le : letenv),
    platform_builtin bf al = some a →
    eval_exprlist (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le al vl →
    CompCert4Lean.X86.Builtins1.platform_builtin_sem bf vl = some v →
      ∃ v', eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi ge sp e m le a v' ∧ Val.lessdef v v'

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

theorem eval_Olea_ptr
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_Olea_ptrStatement := by
  intro ge sp a el m
  rfl

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

theorem eval_addrstack
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_addrstackStatement := by
  intro xi ge sp e m le ofs
  refine ⟨Val.offset_ptr sp ofs, ?_, Val.lessdef_refl _⟩
  apply CompCert4Lean.Backend.CminorSel.eval_expr.eval_Eop le
    (Olea_ptr (Ainstack ofs)) Enil [] (Val.offset_ptr sp ofs)
  · exact CompCert4Lean.Backend.CminorSel.eval_exprlist.nil le
  · change eval_addressing64 ge sp (.Ainstack ofs) [] =
      some (Val.offset_ptr sp ofs)
    simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64]

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

private theorem not_xor_word_local (n : CompCert4Lean.Lib.Integers.int) :
    CompCert4Lean.Lib.Integers.Int.not n =
      CompCert4Lean.Lib.Integers.Int.xor n CompCert4Lean.Lib.Integers.Int.mone := by
  have hmone :
      (CompCert4Lean.Lib.Integers.WordCore.mone
        CompCert4Lean.Lib.Integers.Int.wordsize).val =
        2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1 := by
    rfl
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  simp [CompCert4Lean.Lib.Integers.Int.not,
    CompCert4Lean.Lib.Integers.Int.xor,
    CompCert4Lean.Lib.Integers.Int.mone,
    CompCert4Lean.Lib.Integers.WordCore.not,
    CompCert4Lean.Lib.Integers.WordCore.xor,
    CompCert4Lean.Lib.Integers.WordCore.repr,
    CompCert4Lean.Lib.Integers.WordCore.Word.val]
  simp only [CompCert4Lean.Lib.Integers.WordCore.Word.val] at hmone
  rw [hmone]

private theorem not_xor_val_local (v : val) :
    Val.notint v = Val.xor v (.Vint CompCert4Lean.Lib.Integers.Int.mone) := by
  cases v with
  | Vundef => rfl
  | Vint n =>
      simp only [Val.notint, Val.xor]
      exact congrArg Vint (not_xor_word_local n)
  | Vlong _ => rfl
  | Vfloat _ => rfl
  | Vsingle _ => rfl
  | Vptr _ _ => rfl

theorem eval_notint
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_notintStatement := by
  intro xi ge sp e m le a x h
  cases hcase : notint_match a with
  | notint_case1 n =>
      cases h with
      | eval_Eop le op al vl v hargs hop =>
          cases hargs with
          | nil _ =>
              change some (.Vint n) = some x at hop
              cases hop
              refine ⟨.Vint (CompCert4Lean.Lib.Integers.Int.not n), ?_, ?_⟩
              · apply eval_Eop le (Ointconst (CompCert4Lean.Lib.Integers.Int.not n)) Enil []
                · exact eval_exprlist.nil le
                · rfl
              · exact Val.lessdef_refl _
  | notint_case2 n e1 =>
      cases h with
      | eval_Eop le' op al vl v hargs hop =>
          cases hargs with
          | cons _ a' al' v1 vl' hhead htail =>
              cases htail with
              | nil _ =>
                  change some (Val.xor v1 (.Vint n)) = some x at hop
                  cases hop
                  refine ⟨Val.xor v1 (.Vint (CompCert4Lean.Lib.Integers.Int.not n)), ?_, ?_⟩
                  · apply eval_Eop le (Oxorimm (CompCert4Lean.Lib.Integers.Int.not n))
                      (Econs e1 Enil) [v1] (Val.xor v1 (.Vint (CompCert4Lean.Lib.Integers.Int.not n)))
                    · apply eval_exprlist.cons le e1 Enil v1 [] hhead
                      exact eval_exprlist.nil le
                    · rfl
                  · have hid :
                        Val.notint (Val.xor v1 (.Vint n)) =
                          Val.xor v1 (.Vint (CompCert4Lean.Lib.Integers.Int.not n)) := by
                      rw [not_xor_val_local, Val.xor_assoc]
                      rw [← not_xor_val_local (.Vint n)]
                      rfl
                    exact hid ▸ Val.lessdef_refl _
  | notint_default e1 =>
      refine ⟨Val.notint x, ?_, Val.lessdef_refl _⟩
      simp only [notint, hcase]
      apply eval_Eop le Onot (Econs a Enil) [x] (Val.notint x)
      · exact eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)
      · rfl

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

theorem eval_negint
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_negintStatement := by
  intro xi ge sp e m le a x h
  cases hcase : negint_match a with
  | negint_case1 n =>
      cases h with
      | eval_Eop le' op al vl v hargs hop =>
          cases hargs with
          | nil _ =>
              change some (.Vint n) = some x at hop
              cases hop
              refine ⟨.Vint (CompCert4Lean.Lib.Integers.Int.neg n), ?_, ?_⟩
              · apply eval_Eop le (Ointconst (CompCert4Lean.Lib.Integers.Int.neg n)) Enil []
                · exact eval_exprlist.nil le
                · rfl
              · exact Val.lessdef_refl _
  | negint_default e1 =>
      refine ⟨Val.neg x, ?_, Val.lessdef_refl _⟩
      simp only [negint, hcase]
      apply eval_Eop le Oneg (Econs a Enil) [x] (Val.neg x)
      · exact eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)
      · rfl

end CompCert4Lean.X86.SelectOpproof
