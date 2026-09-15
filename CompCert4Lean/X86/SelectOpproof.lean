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

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

theorem eval_mulhs
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_mulhsStatement := by
  intro xi ge sp e m le a x b y hxa hxb
  refine ⟨Val.mulhs x y, ?_, Val.lessdef_refl _⟩
  apply eval_Eop le Omulhs (Econs a (Econs b Enil)) [x, y] (Val.mulhs x y)
  · apply eval_exprlist.cons le a (Econs b Enil) x [y] hxa
    exact eval_exprlist.cons le b Enil y [] hxb (eval_exprlist.nil le)
  · rfl

theorem eval_mulhu
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_mulhuStatement := by
  intro xi ge sp e m le a x b y hxa hxb
  refine ⟨Val.mulhu x y, ?_, Val.lessdef_refl _⟩
  apply eval_Eop le Omulhu (Econs a (Econs b Enil)) [x, y] (Val.mulhu x y)
  · apply eval_exprlist.cons le a (Econs b Enil) x [y] hxa
    exact eval_exprlist.cons le b Enil y [] hxb (eval_exprlist.nil le)
  · rfl

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Memory
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

private theorem eval_intconst_value_local
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (le : letenv) (n : CCInt) (x : val)
    (h : eval_expr (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge sp e m le
      (Eop (Ointconst n) Enil) x) :
    x = .Vint n := by
  cases h with
  | eval_Eop _ _ _ _ _ hargs hop =>
      cases hargs
      change some (.Vint n) = some x at hop
      cases hop
      rfl

private theorem int_eq_true_zero_local (n : CCInt)
    (h : CompCert4Lean.Lib.Integers.Int.eq n
      CompCert4Lean.Lib.Integers.Int.zero = true) :
    n = CompCert4Lean.Lib.Integers.Int.zero := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext
  have hd : decide (n.intval =
      CompCert4Lean.Lib.Integers.Int.zero.intval) = true := by
    simpa [CompCert4Lean.Lib.Integers.Int.eq,
      CompCert4Lean.Lib.Integers.WordCore.eq] using h
  exact of_decide_eq_true hd

private theorem int_eq_true_mone_local (n : CCInt)
    (h : CompCert4Lean.Lib.Integers.Int.eq n
      CompCert4Lean.Lib.Integers.Int.mone = true) :
    n = CompCert4Lean.Lib.Integers.Int.mone := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext
  have hd : decide (n.intval =
      CompCert4Lean.Lib.Integers.Int.mone.intval) = true := by
    simpa [CompCert4Lean.Lib.Integers.Int.eq,
      CompCert4Lean.Lib.Integers.WordCore.eq] using h
  exact of_decide_eq_true hd

private theorem val_and_zero_local (x : val) :
    Val.lessdef (Val.and x (.Vint CompCert4Lean.Lib.Integers.Int.zero))
      (.Vint CompCert4Lean.Lib.Integers.Int.zero) := by
  cases x with
  | Vint n =>
      have hi : CompCert4Lean.Lib.Integers.Int.and n
          CompCert4Lean.Lib.Integers.Int.zero =
          CompCert4Lean.Lib.Integers.Int.zero := by
        apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
        change (CompCert4Lean.Lib.Integers.WordCore.repr
          CompCert4Lean.Lib.Integers.Int.wordsize
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
            (Nat.land n.val
              CompCert4Lean.Lib.Integers.Int.zero.val))).val =
          CompCert4Lean.Lib.Integers.Int.zero.val
        have hz : CompCert4Lean.Lib.Integers.Int.zero.val = 0 := by rfl
        rw [hz]
        simp only [Nat.land_eq, Nat.and_zero]
        rfl
      change Val.lessdef
        (.Vint (CompCert4Lean.Lib.Integers.Int.and n
          CompCert4Lean.Lib.Integers.Int.zero))
        (.Vint CompCert4Lean.Lib.Integers.Int.zero)
      rw [hi]
      exact Val.lessdef_refl _
  | _ => exact Val.lessdef_undef _

private theorem val_and_mone_local (x : val) :
    Val.lessdef (Val.and x (.Vint CompCert4Lean.Lib.Integers.Int.mone)) x := by
  cases x with
  | Vint n =>
      change Val.lessdef
        (.Vint (CompCert4Lean.Lib.Integers.Int.and n
          CompCert4Lean.Lib.Integers.Int.mone)) (.Vint n)
      rw [CompCert4Lean.Lib.Integers.Int.and_mone_proof]
      exact Val.lessdef_refl _
  | _ => exact Val.lessdef_undef _

private theorem val_and_zero_ext8_local (v : val) (n : CCInt) :
    Val.and (Val.zero_ext (zOfNat 8) v) (.Vint n) =
      Val.and v (.Vint (CompCert4Lean.Lib.Integers.Int.and n
        (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 255)))) := by
  cases v with
  | Vundef => rfl
  | Vfloat _ => rfl
  | Vsingle _ => rfl
  | Vlong _ => rfl
  | Vptr _ _ => rfl
  | Vint v =>
      have hext : Val.zero_ext (zOfNat 8)
          (CompCert4Lean.Common.Values.val.Vint v) =
          Val.and (CompCert4Lean.Common.Values.val.Vint v)
            (CompCert4Lean.Common.Values.val.Vint
              (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 255))) := by
        change CompCert4Lean.Common.Values.val.Vint
            (CompCert4Lean.Lib.Integers.Int.zero_ext (zOfNat 8) v) =
          CompCert4Lean.Common.Values.val.Vint
            (CompCert4Lean.Lib.Integers.Int.and v
            (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 255)))
        rw [CompCert4Lean.Lib.Integers.Int.zero_ext_and_proof (zOfNat 8) v
          (by change (0 : Int) ≤ 8; omega)]
        congr 1
      rw [hext]
      have ha := CompCert4Lean.Common.Values.Val.and_assoc
        (.Vint v)
        (.Vint (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 255)))
        (.Vint n)
      have hc := CompCert4Lean.Common.Values.Val.and_commut
        (.Vint (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 255))) (.Vint n)
      rw [ha, hc]
      rfl

private theorem val_and_zero_ext16_local (v : val) (n : CCInt) :
    Val.and (Val.zero_ext (zOfNat 16) v) (.Vint n) =
      Val.and v (.Vint (CompCert4Lean.Lib.Integers.Int.and n
        (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 65535)))) := by
  cases v with
  | Vundef => rfl
  | Vfloat _ => rfl
  | Vsingle _ => rfl
  | Vlong _ => rfl
  | Vptr _ _ => rfl
  | Vint v =>
      have hext : Val.zero_ext (zOfNat 16)
          (CompCert4Lean.Common.Values.val.Vint v) =
          Val.and (CompCert4Lean.Common.Values.val.Vint v)
            (CompCert4Lean.Common.Values.val.Vint
              (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 65535))) := by
        change CompCert4Lean.Common.Values.val.Vint
            (CompCert4Lean.Lib.Integers.Int.zero_ext (zOfNat 16) v) =
          CompCert4Lean.Common.Values.val.Vint
            (CompCert4Lean.Lib.Integers.Int.and v
            (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 65535)))
        rw [CompCert4Lean.Lib.Integers.Int.zero_ext_and_proof (zOfNat 16) v
          (by change (0 : Int) ≤ 16; omega)]
        congr 1
      rw [hext]
      have ha := CompCert4Lean.Common.Values.Val.and_assoc
        (.Vint v)
        (.Vint (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 65535)))
        (.Vint n)
      have hc := CompCert4Lean.Common.Values.Val.and_commut
        (.Vint (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 65535))) (.Vint n)
      rw [ha, hc]
      rfl

theorem eval_andimm
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_andimmStatement := by
  intro xi ge sp e m n le a x h
  unfold andimm
  by_cases hz : CompCert4Lean.Lib.Integers.Int.eq n
      CompCert4Lean.Lib.Integers.Int.zero = true
  · have hn := int_eq_true_zero_local n hz
    rw [if_pos hz]
    refine ⟨.Vint CompCert4Lean.Lib.Integers.Int.zero, ?_, ?_⟩
    · exact eval_expr.eval_Eop le (Ointconst CompCert4Lean.Lib.Integers.Int.zero)
        Enil [] (.Vint CompCert4Lean.Lib.Integers.Int.zero)
        (eval_exprlist.nil le) rfl
    · subst n
      exact val_and_zero_local x
  · by_cases hm : CompCert4Lean.Lib.Integers.Int.eq n
        CompCert4Lean.Lib.Integers.Int.mone = true
    · have hn := int_eq_true_mone_local n hm
      rw [if_neg hz, if_pos hm]
      subst n
      exact ⟨x, h, val_and_mone_local x⟩
    · rw [if_neg hz, if_neg hm]
      cases hmatch : andimm_match a with
      | andimm_case1 n2 =>
          have hx : x = .Vint n2 := eval_intconst_value_local xi ge sp e m le n2 x
            (by simpa [hmatch] using h)
          subst x
          refine ⟨.Vint (CompCert4Lean.Lib.Integers.Int.and n n2), ?_, ?_⟩
          · exact eval_expr.eval_Eop le
              (Ointconst (CompCert4Lean.Lib.Integers.Int.and n n2)) Enil [] _
              (eval_exprlist.nil le) rfl
          · change Val.lessdef
              (.Vint (CompCert4Lean.Lib.Integers.Int.and n2 n))
              (.Vint (CompCert4Lean.Lib.Integers.Int.and n n2))
            rw [CompCert4Lean.Lib.Integers.Int.and_commut_proof]
            exact Val.lessdef_refl _
      | andimm_case2 n2 t2 =>
          cases h with
          | eval_Eop le' op al vl v hargs hop =>
              cases hargs with
              | cons _ a' al' v1 vl' hhead htail =>
                  cases htail with
                  | nil _ =>
                      change some (Val.and v1 (.Vint n2)) = some x at hop
                      cases hop
                      refine ⟨Val.and v1
                        (.Vint (CompCert4Lean.Lib.Integers.Int.and n n2)), ?_, ?_⟩
                      · apply eval_expr.eval_Eop le
                          (Oandimm (CompCert4Lean.Lib.Integers.Int.and n n2))
                          (Econs t2 Enil) [v1] _
                        · exact eval_exprlist.cons le t2 Enil v1 []
                            (by simpa [hmatch] using hhead)
                            (eval_exprlist.nil le)
                        · rfl
                      · change Val.lessdef
                          (Val.and (Val.and v1 (.Vint n2)) (.Vint n))
                          (Val.and v1
                            (.Vint (CompCert4Lean.Lib.Integers.Int.and n n2)))
                        rw [CompCert4Lean.Common.Values.Val.and_assoc]
                        cases v1 with
                        | Vundef => exact Val.lessdef_refl _
                        | Vfloat _ => exact Val.lessdef_refl _
                        | Vsingle _ => exact Val.lessdef_refl _
                        | Vlong _ => exact Val.lessdef_refl _
                        | Vptr _ _ => exact Val.lessdef_refl _
                        | Vint v1 =>
                            have hc := CompCert4Lean.Common.Values.Val.and_commut
                              (.Vint n2) (.Vint n)
                            rw [hc]
                            exact Val.lessdef_refl _
      | andimm_case3 t2 =>
          cases h with
          | eval_Eop le' op al vl v hargs hop =>
              cases hargs with
              | cons _ a' al' v1 vl' hhead htail =>
                  cases htail with
                  | nil _ =>
                      change some (Val.zero_ext (zOfNat 8) v1) = some x at hop
                      cases hop
                      let mask := CompCert4Lean.Lib.Integers.Int.and n
                        (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 255))
                      refine ⟨Val.and v1 (.Vint mask), ?_, ?_⟩
                      · apply eval_expr.eval_Eop le (Oandimm mask)
                          (Econs t2 Enil) [v1] _
                        · exact eval_exprlist.cons le t2 Enil v1 []
                            (by simpa [hmatch] using hhead)
                            (eval_exprlist.nil le)
                        · rfl
                      · change Val.lessdef
                          (Val.and (Val.zero_ext (zOfNat 8) v1) (.Vint n))
                          (Val.and v1 (.Vint mask))
                        rw [val_and_zero_ext8_local v1 n]
                        exact Val.lessdef_refl _
      | andimm_case4 t2 =>
          cases h with
          | eval_Eop le' op al vl v hargs hop =>
              cases hargs with
              | cons _ a' al' v1 vl' hhead htail =>
                  cases htail with
                  | nil _ =>
                      change some (Val.zero_ext (zOfNat 16) v1) = some x at hop
                      cases hop
                      let mask := CompCert4Lean.Lib.Integers.Int.and n
                        (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 65535))
                      refine ⟨Val.and v1 (.Vint mask), ?_, ?_⟩
                      · apply eval_expr.eval_Eop le (Oandimm mask)
                          (Econs t2 Enil) [v1] _
                        · exact eval_exprlist.cons le t2 Enil v1 []
                            (by simpa [hmatch] using hhead)
                            (eval_exprlist.nil le)
                        · rfl
                      · change Val.lessdef
                          (Val.and (Val.zero_ext (zOfNat 16) v1) (.Vint n))
                          (Val.and v1 (.Vint mask))
                        rw [val_and_zero_ext16_local v1 n]
                        exact Val.lessdef_refl _
      | andimm_default e2 =>
          refine ⟨Val.and x (.Vint n), ?_, Val.lessdef_refl _⟩
          apply eval_expr.eval_Eop le (Oandimm n) (Econs a Enil) [x]
            (Val.and x (.Vint n))
          · exact eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)
          · rfl

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Memory
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

theorem eval_and
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_andStatement := by
  unfold eval_andStatement binary_constructor_sound
  intro xi ge sp e m le a x b y ha hb
  cases hmatch : and_match a b with
  | and_case1 n1 _t2 =>
      have hx : x = .Vint n1 := eval_intconst_value_local xi ge sp e m le n1 x
        (by simpa [hmatch] using ha)
      subst x
      obtain ⟨v, hv, hd⟩ := eval_andimm xi ge sp e m n1 le b y hb
      refine ⟨v, ?_, ?_⟩
      · simpa [CompCert4Lean.X86.SelectOp.and, hmatch] using hv
      · rw [CompCert4Lean.Common.Values.Val.and_commut]
        exact hd
  | and_case2 _t1 n2 =>
      have hy : y = .Vint n2 := eval_intconst_value_local xi ge sp e m le n2 y
        (by simpa [hmatch] using hb)
      subst y
      obtain ⟨v, hv, hd⟩ := eval_andimm xi ge sp e m n2 le a x ha
      refine ⟨v, ?_, ?_⟩
      · simpa [CompCert4Lean.X86.SelectOp.and, hmatch] using hv
      · exact hd
  | and_default e1 e2 =>
      refine ⟨Val.and x y, ?_, Val.lessdef_refl _⟩
      simp only [CompCert4Lean.X86.SelectOp.and, hmatch]
      apply eval_expr.eval_Eop le Oand (Econs a (Econs b Enil)) [x, y]
        (Val.and x y)
      · exact eval_exprlist.cons le a (Econs b Enil) x [y] ha
          (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))
      · rfl

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

theorem eval_same_expr
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_same_exprStatement := by
  intro xi ge sp e m a1 a2 le v1 v2 hsame h1 h2
  cases a1 <;> cases a2 <;>
    simp [CompCert4Lean.X86.SelectOp.same_expr_pure] at hsame
  subst_vars
  cases h1 with
  | var _ _ _ hget1 =>
      cases h2 with
      | var _ _ _ hget2 =>
          exact ⟨rfl, Option.some.inj (hget1.symm.trans hget2)⟩

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

theorem int_add_sub_eq : int_add_sub_eqStatement := by
  intro x y z h
  subst z
  have hs := CompCert4Lean.Common.Values.Val.sub_add_l
    (.Vint x) (.Vint x) y
  change CompCert4Lean.Common.Values.val.Vint (CompCert4Lean.Lib.Integers.Int.sub
      (CompCert4Lean.Lib.Integers.Int.add x y) x) =
    CompCert4Lean.Common.Values.val.Vint (CompCert4Lean.Lib.Integers.Int.add
      (CompCert4Lean.Lib.Integers.Int.sub x x) y) at hs
  have hs' := CompCert4Lean.Common.Values.val.Vint.inj hs
  rw [hs', CompCert4Lean.Lib.Integers.Int.sub_idem_proof]
  have hc := CompCert4Lean.Common.Values.Val.add_commut
    (.Vint CompCert4Lean.Lib.Integers.Int.zero) (.Vint y)
  change CompCert4Lean.Common.Values.val.Vint (CompCert4Lean.Lib.Integers.Int.add
      CompCert4Lean.Lib.Integers.Int.zero y) =
    CompCert4Lean.Common.Values.val.Vint (CompCert4Lean.Lib.Integers.Int.add y
      CompCert4Lean.Lib.Integers.Int.zero) at hc
  exact (CompCert4Lean.Common.Values.val.Vint.inj hc).trans
    (CompCert4Lean.Lib.Integers.Int.add_zero_proof y)

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

private theorem int_zOfNat_val_local (x : CCInt) :
    zOfNat x.val = x.intval := by
  have hx : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0 x.intval := by
    have h := x.intrange.1
    change (-1 : Int) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval at h
    change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval
    omega
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat
        x.intval) = x.intval
  exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Z2Nat.id
    x.intval hx

private theorem int_xor_zero_local (x : CCInt) :
    CompCert4Lean.Lib.Integers.Int.xor x
      CompCert4Lean.Lib.Integers.Int.zero = x := by
  unfold CompCert4Lean.Lib.Integers.Int.xor
    CompCert4Lean.Lib.Integers.WordCore.xor
  change CompCert4Lean.Lib.Integers.WordCore.repr
      CompCert4Lean.Lib.Integers.Int.wordsize
      (zOfNat (Nat.xor x.val CompCert4Lean.Lib.Integers.Int.zero.val)) = x
  have hz : CompCert4Lean.Lib.Integers.Int.zero.val = 0 := rfl
  rw [hz]
  have hx0 : Nat.xor x.val 0 = x.val := by
    simpa only [Nat.xor_eq] using (Nat.xor_zero x.val)
  rw [hx0]
  change CompCert4Lean.Lib.Integers.Int.repr (zOfNat x.val) = x
  rw [int_zOfNat_val_local x]
  exact CompCert4Lean.Lib.Integers.Int.repr_unsigned_proof x

private theorem val_xor_zero_local (x : val) :
    Val.lessdef (Val.xor x
      (.Vint CompCert4Lean.Lib.Integers.Int.zero)) x := by
  cases x with
  | Vint n =>
      change Val.lessdef
        (.Vint (CompCert4Lean.Lib.Integers.Int.xor n
          CompCert4Lean.Lib.Integers.Int.zero)) (.Vint n)
      rw [int_xor_zero_local]
      exact Val.lessdef_refl _
  | _ => exact Val.lessdef_undef _

theorem eval_xorimm
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_xorimmStatement := by
  intro xi ge sp e m n le a x h
  unfold xorimm
  by_cases hz : CompCert4Lean.Lib.Integers.Int.eq n
      CompCert4Lean.Lib.Integers.Int.zero = true
  · have hn := int_eq_true_zero_local n hz
    rw [if_pos hz]
    subst n
    exact ⟨x, h, val_xor_zero_local x⟩
  · rw [if_neg hz]
    cases hmatch : xorimm_match a with
    | xorimm_case1 n2 =>
        have hx : x = .Vint n2 := eval_intconst_value_local xi ge sp e m le n2 x
          (by simpa [hmatch] using h)
        subst x
        refine ⟨.Vint (CompCert4Lean.Lib.Integers.Int.xor n n2), ?_, ?_⟩
        · exact eval_expr.eval_Eop le
            (Ointconst (CompCert4Lean.Lib.Integers.Int.xor n n2)) Enil [] _
            (eval_exprlist.nil le) rfl
        · change Val.lessdef
            (Val.xor (.Vint n2) (.Vint n))
            (.Vint (CompCert4Lean.Lib.Integers.Int.xor n n2))
          rw [CompCert4Lean.Common.Values.Val.xor_commut]
          exact Val.lessdef_refl _
    | xorimm_case2 n2 t2 =>
        cases h with
        | eval_Eop le' op al vl v hargs hop =>
            cases hargs with
            | cons _ a' al' v1 vl' hhead htail =>
                cases htail with
                | nil _ =>
                    change some (Val.xor v1 (.Vint n2)) = some x at hop
                    cases hop
                    refine ⟨Val.xor v1
                      (.Vint (CompCert4Lean.Lib.Integers.Int.xor n n2)), ?_, ?_⟩
                    · apply eval_expr.eval_Eop le
                        (Oxorimm (CompCert4Lean.Lib.Integers.Int.xor n n2))
                        (Econs t2 Enil) [v1] _
                      · exact eval_exprlist.cons le t2 Enil v1 []
                          (by simpa [hmatch] using hhead)
                          (eval_exprlist.nil le)
                      · rfl
                    · change Val.lessdef
                        (Val.xor (Val.xor v1 (.Vint n2)) (.Vint n))
                        (Val.xor v1
                          (.Vint (CompCert4Lean.Lib.Integers.Int.xor n n2)))
                      rw [CompCert4Lean.Common.Values.Val.xor_assoc]
                      have hc := CompCert4Lean.Common.Values.Val.xor_commut
                        (.Vint n2) (.Vint n)
                      rw [hc]
                      exact Val.lessdef_refl _
    | xorimm_case3 t2 =>
        cases h with
        | eval_Eop le' op al vl v hargs hop =>
            cases hargs with
            | cons _ a' al' v1 vl' hhead htail =>
                cases htail with
                | nil _ =>
                    change some (Val.notint v1) = some x at hop
                    cases hop
                    refine ⟨Val.xor v1
                      (.Vint (CompCert4Lean.Lib.Integers.Int.not n)), ?_, ?_⟩
                    · apply eval_expr.eval_Eop le
                        (Oxorimm (CompCert4Lean.Lib.Integers.Int.not n))
                        (Econs t2 Enil) [v1] _
                      · exact eval_exprlist.cons le t2 Enil v1 []
                          (by simpa [hmatch] using hhead)
                          (eval_exprlist.nil le)
                      · rfl
                    · have hsem :
                          Val.xor (Val.notint v1) (.Vint n) =
                            Val.xor v1
                              (.Vint (CompCert4Lean.Lib.Integers.Int.not n)) := by
                        calc
                          Val.xor (Val.notint v1) (.Vint n) =
                              Val.xor (Val.xor v1
                                (.Vint CompCert4Lean.Lib.Integers.Int.mone))
                                (.Vint n) := by
                                  rw [CompCert4Lean.Common.Values.Val.not_xor]
                          _ = Val.xor v1 (Val.xor
                                (.Vint CompCert4Lean.Lib.Integers.Int.mone)
                                (.Vint n)) :=
                              CompCert4Lean.Common.Values.Val.xor_assoc _ _ _
                          _ = Val.xor v1 (Val.xor (.Vint n)
                                (.Vint CompCert4Lean.Lib.Integers.Int.mone)) := by
                              rw [CompCert4Lean.Common.Values.Val.xor_commut
                                (.Vint CompCert4Lean.Lib.Integers.Int.mone)]
                          _ = Val.xor v1 (Val.notint (.Vint n)) := by
                              rw [CompCert4Lean.Common.Values.Val.not_xor]
                          _ = Val.xor v1
                                (.Vint (CompCert4Lean.Lib.Integers.Int.not n)) := rfl
                      change Val.lessdef
                        (Val.xor (Val.notint v1) (.Vint n))
                        (Val.xor v1
                          (.Vint (CompCert4Lean.Lib.Integers.Int.not n)))
                      rw [hsem]
                      exact Val.lessdef_refl _
    | xorimm_default e2 =>
        refine ⟨Val.xor x (.Vint n), ?_, Val.lessdef_refl _⟩
        apply eval_expr.eval_Eop le (Oxorimm n) (Econs a Enil) [x]
          (Val.xor x (.Vint n))
        · exact eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)
        · rfl

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

theorem eval_xor
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_xorStatement := by
  unfold eval_xorStatement binary_constructor_sound
  intro xi ge sp e m le a x b y ha hb
  cases hmatch : xor_match a b with
  | xor_case1 n1 _t2 =>
      have hx : x = .Vint n1 := eval_intconst_value_local xi ge sp e m le n1 x
        (by simpa [hmatch] using ha)
      subst x
      obtain ⟨v, hv, hd⟩ := eval_xorimm xi ge sp e m n1 le b y hb
      refine ⟨v, ?_, ?_⟩
      · simpa [CompCert4Lean.X86.SelectOp.xor, hmatch] using hv
      · rw [CompCert4Lean.Common.Values.Val.xor_commut]
        exact hd
  | xor_case2 _t1 n2 =>
      have hy : y = .Vint n2 := eval_intconst_value_local xi ge sp e m le n2 y
        (by simpa [hmatch] using hb)
      subst y
      obtain ⟨v, hv, hd⟩ := eval_xorimm xi ge sp e m n2 le a x ha
      refine ⟨v, ?_, ?_⟩
      · simpa [CompCert4Lean.X86.SelectOp.xor, hmatch] using hv
      · exact hd
  | xor_default e1 e2 =>
      refine ⟨Val.xor x y, ?_, Val.lessdef_refl _⟩
      simp only [CompCert4Lean.X86.SelectOp.xor, hmatch]
      apply eval_expr.eval_Eop le Oxor (Econs a (Econs b Enil)) [x, y]
        (Val.xor x y)
      · exact eval_exprlist.cons le a (Econs b Enil) x [y] ha
          (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))
      · rfl

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

private theorem int_or_zero_local (x : CCInt) :
    CompCert4Lean.Lib.Integers.Int.or x
      CompCert4Lean.Lib.Integers.Int.zero = x := by
  unfold CompCert4Lean.Lib.Integers.Int.or
    CompCert4Lean.Lib.Integers.WordCore.or
  change CompCert4Lean.Lib.Integers.Int.repr
      (zOfNat (Nat.lor x.val CompCert4Lean.Lib.Integers.Int.zero.val)) = x
  have hz : CompCert4Lean.Lib.Integers.Int.zero.val = 0 := rfl
  rw [hz]
  have hx0 : Nat.lor x.val 0 = x.val := by
    simpa only [Nat.lor_eq] using (Nat.or_zero x.val)
  rw [hx0, int_zOfNat_val_local x]
  exact CompCert4Lean.Lib.Integers.Int.repr_unsigned_proof x

private theorem int_or_mone_local (x : CCInt) :
    CompCert4Lean.Lib.Integers.Int.or x
      CompCert4Lean.Lib.Integers.Int.mone =
        CompCert4Lean.Lib.Integers.Int.mone := by
  unfold CompCert4Lean.Lib.Integers.Int.or
    CompCert4Lean.Lib.Integers.WordCore.or
  change CompCert4Lean.Lib.Integers.Int.repr
      (zOfNat (Nat.lor x.val CompCert4Lean.Lib.Integers.Int.mone.val)) =
    CompCert4Lean.Lib.Integers.Int.mone
  have hm : CompCert4Lean.Lib.Integers.Int.mone.val =
      2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1 := rfl
  rw [hm]
  have hor : Nat.lor x.val
      (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1) =
      2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1 := by
    have hlt : Nat.lor x.val
        (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1) <
        2 ^ CompCert4Lean.Lib.Integers.Int.wordsize :=
      Nat.or_lt_two_pow x.toFin.isLt (by
        change 2 ^ (32 : Nat) - 1 < 2 ^ (32 : Nat)
        omega)
    have hle : 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1 ≤
        Nat.lor x.val
          (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1) :=
      Nat.right_le_or
    omega
  rw [hor, ← hm, int_zOfNat_val_local
    CompCert4Lean.Lib.Integers.Int.mone]
  exact CompCert4Lean.Lib.Integers.Int.repr_unsigned_proof
    CompCert4Lean.Lib.Integers.Int.mone

private theorem val_or_zero_local (x : val) :
    Val.lessdef (Val.or x
      (.Vint CompCert4Lean.Lib.Integers.Int.zero)) x := by
  cases x with
  | Vint n =>
      change Val.lessdef
        (.Vint (CompCert4Lean.Lib.Integers.Int.or n
          CompCert4Lean.Lib.Integers.Int.zero)) (.Vint n)
      rw [int_or_zero_local]
      exact Val.lessdef_refl _
  | _ => exact Val.lessdef_undef _

private theorem val_or_mone_local (x : val) :
    Val.lessdef (Val.or x
      (.Vint CompCert4Lean.Lib.Integers.Int.mone))
      (.Vint CompCert4Lean.Lib.Integers.Int.mone) := by
  cases x with
  | Vint n =>
      change Val.lessdef
        (.Vint (CompCert4Lean.Lib.Integers.Int.or n
          CompCert4Lean.Lib.Integers.Int.mone))
        (.Vint CompCert4Lean.Lib.Integers.Int.mone)
      rw [int_or_mone_local]
      exact Val.lessdef_refl _
  | _ => exact Val.lessdef_undef _

private theorem eval_orimm_local
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (ge : CompCert4Lean.Backend.CminorSel.genv) (sp : val) (e : env)
    (m : CompCert4Lean.Common.Memory.mem)
    (n : CCInt) :
    unary_constructor_sound xi ge sp e m (orimm n)
      (fun x => Val.or x (.Vint n)) := by
  intro le a x h
  unfold orimm
  by_cases hz : CompCert4Lean.Lib.Integers.Int.eq n
      CompCert4Lean.Lib.Integers.Int.zero = true
  · have hn := int_eq_true_zero_local n hz
    rw [if_pos hz]
    subst n
    exact ⟨x, h, val_or_zero_local x⟩
  · by_cases hm : CompCert4Lean.Lib.Integers.Int.eq n
        CompCert4Lean.Lib.Integers.Int.mone = true
    · have hn := int_eq_true_mone_local n hm
      rw [if_neg hz, if_pos hm]
      refine ⟨.Vint CompCert4Lean.Lib.Integers.Int.mone, ?_, ?_⟩
      · exact eval_expr.eval_Eop le
          (Ointconst CompCert4Lean.Lib.Integers.Int.mone) Enil [] _
          (eval_exprlist.nil le) rfl
      · subst n
        exact val_or_mone_local x
    · rw [if_neg hz, if_neg hm]
      cases hmatch : orimm_match a with
      | orimm_case1 n2 =>
          have hx : x = .Vint n2 := eval_intconst_value_local xi ge sp e m le n2 x
            (by simpa [hmatch] using h)
          subst x
          refine ⟨.Vint (CompCert4Lean.Lib.Integers.Int.or n n2), ?_, ?_⟩
          · exact eval_expr.eval_Eop le
              (Ointconst (CompCert4Lean.Lib.Integers.Int.or n n2)) Enil [] _
              (eval_exprlist.nil le) rfl
          · change Val.lessdef (Val.or (.Vint n2) (.Vint n))
              (.Vint (CompCert4Lean.Lib.Integers.Int.or n n2))
            rw [CompCert4Lean.Common.Values.Val.or_commut]
            exact Val.lessdef_refl _
      | orimm_case2 n2 t2 =>
          cases h with
          | eval_Eop le' op al vl v hargs hop =>
              cases hargs with
              | cons _ a' al' v1 vl' hhead htail =>
                  cases htail with
                  | nil _ =>
                      change some (Val.or v1 (.Vint n2)) = some x at hop
                      cases hop
                      refine ⟨Val.or v1
                        (.Vint (CompCert4Lean.Lib.Integers.Int.or n n2)), ?_, ?_⟩
                      · apply eval_expr.eval_Eop le
                          (Oorimm (CompCert4Lean.Lib.Integers.Int.or n n2))
                          (Econs t2 Enil) [v1] _
                        · exact eval_exprlist.cons le t2 Enil v1 []
                            (by simpa [hmatch] using hhead)
                            (eval_exprlist.nil le)
                        · rfl
                      · change Val.lessdef
                          (Val.or (Val.or v1 (.Vint n2)) (.Vint n))
                          (Val.or v1
                            (.Vint (CompCert4Lean.Lib.Integers.Int.or n n2)))
                        rw [CompCert4Lean.Common.Values.Val.or_assoc]
                        have hc := CompCert4Lean.Common.Values.Val.or_commut
                          (.Vint n2) (.Vint n)
                        rw [hc]
                        exact Val.lessdef_refl _
      | orimm_default e2 =>
          refine ⟨Val.or x (.Vint n), ?_, Val.lessdef_refl _⟩
          apply eval_expr.eval_Eop le (Oorimm n) (Econs a Enil) [x]
            (Val.or x (.Vint n))
          · exact eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)
          · rfl

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers
open Lean Elab Tactic Meta

private def selectOpproofPrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private")
    "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem word_val_repr_local (bits : Nat) (i : Int) :
    (WordCore.repr bits (zOfInt i)).val =
      Int.toNat (i % ((2 ^ bits : Nat) : Int)) := by
  run_tac
    let lctx ← getLCtx
    let bitsF := (lctx.findFromUserName? `bits).get!
    let iF := (lctx.findFromUserName? `i).get!
    let bitsE := mkFVar bitsF.fvarId
    let iE := mkFVar iF.fvarId
    let proof ← mkAppM
      (selectOpproofPrivateName
        "CompCert4Lean.Lib.Integers.WordCore.val_repr")
      #[bitsE, iE]
    closeMainGoal Name.anonymous proof

private theorem repr_val_mod_local (bits n : Nat) :
    (WordCore.repr bits (ZArith.BinInt.Z.of_nat n)).val =
      n % (2 ^ bits) := by
  rw [show ZArith.BinInt.Z.of_nat n = zOfInt (Int.ofNat n) by rfl,
    word_val_repr_local]
  apply Int.ofNat.inj
  simp only [Int.ofNat_eq_natCast]
  have hmpos : (0 : Int) < ((2 ^ bits : Nat) : Int) :=
    Int.natCast_pos.mpr (Nat.two_pow_pos bits)
  have hnonneg : 0 ≤ Int.ofNat n % Int.ofNat (2 ^ bits) :=
    Int.emod_nonneg _ (Int.ne_of_gt hmpos)
  calc
    Int.ofNat ((Int.ofNat n % Int.ofNat (2 ^ bits)).toNat) =
        Int.ofNat n % Int.ofNat (2 ^ bits) :=
      Int.toNat_of_nonneg hnonneg
    _ = Int.ofNat (n % 2 ^ bits) := by
      simpa only [Int.ofNat_eq_natCast] using
        (Int.natCast_emod n (2 ^ bits)).symm

private theorem int_or_val_local' (x y : CCInt) :
    (CompCert4Lean.Lib.Integers.Int.or x y).val = Nat.lor x.val y.val := by
  unfold CompCert4Lean.Lib.Integers.Int.or WordCore.or
  rw [repr_val_mod_local]
  apply Nat.mod_eq_of_lt
  exact Nat.or_lt_two_pow x.toFin.isLt y.toFin.isLt

private theorem int_shl_val_local (x y : CCInt) :
    (CompCert4Lean.Lib.Integers.Int.shl x y).val =
      (x.val * 2 ^ y.val) %
        (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize) := by
  unfold CompCert4Lean.Lib.Integers.Int.shl WordCore.shl
  change (WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (ZArith.BinInt.Z.shiftl x.intval y.intval)).val = _
  rw [← int_zOfNat_val_local x, ← int_zOfNat_val_local y]
  have hshift : ZArith.BinInt.Z.shiftl (zOfNat x.val) (zOfNat y.val) =
      zOfNat (x.val * 2 ^ y.val) := by
    unfold ZArith.BinInt.Z.shiftl
    simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
      Int.ofNat_eq_natCast, Int.natCast_nonneg, ↓reduceIte,
      Int.toNat_natCast, Int.natCast_mul, Int.natCast_pow]
    rfl
  rw [hshift, repr_val_mod_local]

private theorem int_shru_val_local (x y : CCInt) :
    (CompCert4Lean.Lib.Integers.Int.shru x y).val =
      x.val / 2 ^ y.val := by
  unfold CompCert4Lean.Lib.Integers.Int.shru WordCore.shru
  change (WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (ZArith.BinInt.Z.shiftr x.intval y.intval)).val = _
  rw [← int_zOfNat_val_local x, ← int_zOfNat_val_local y]
  have hshift : ZArith.BinInt.Z.shiftr (zOfNat x.val) (zOfNat y.val) =
      zOfNat (x.val / 2 ^ y.val) := by
    unfold ZArith.BinInt.Z.shiftr
    simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
      Int.ofNat_eq_natCast, Int.natCast_nonneg, ↓reduceIte,
      Int.toNat_natCast, Int.natCast_pow]
    exact congrArg zOfInt Int.ofNat_ediv_ofNat
  rw [hshift, repr_val_mod_local]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt (Nat.div_le_self x.val _) x.toFin.isLt

private theorem int_ror_val_local (x y : CCInt) :
    (CompCert4Lean.Lib.Integers.Int.ror x y).val =
      Nat.lor (Nat.shiftRight x.val
        (y.val % CompCert4Lean.Lib.Integers.Int.wordsize))
        (Nat.shiftLeft x.val
          (CompCert4Lean.Lib.Integers.Int.wordsize -
            y.val % CompCert4Lean.Lib.Integers.Int.wordsize)) %
      (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize) := by
  unfold CompCert4Lean.Lib.Integers.Int.ror WordCore.ror
  simp only [CompCert4Lean.Lib.Integers.Int.wordsize, if_false]
  exact repr_val_mod_local _ _

private theorem int_ltu_iwordsize_val_local (n : CCInt)
    (h : CompCert4Lean.Lib.Integers.Int.ltu n
      CompCert4Lean.Lib.Integers.Int.iwordsize = true) :
    n.val < CompCert4Lean.Lib.Integers.Int.wordsize := by
  have hlt := (CompCert4Lean.Lib.Integers.Int.ltu_inv_proof n
    CompCert4Lean.Lib.Integers.Int.iwordsize h).2
  change ZArith.BinInt.Z.lt n.intval
    CompCert4Lean.Lib.Integers.Int.iwordsize.intval at hlt
  rw [← int_zOfNat_val_local n,
    ← int_zOfNat_val_local CompCert4Lean.Lib.Integers.Int.iwordsize] at hlt
  have hi : CompCert4Lean.Lib.Integers.Int.iwordsize.val =
      CompCert4Lean.Lib.Integers.Int.wordsize := rfl
  rw [hi] at hlt
  change intOfZ (ZArith.BinInt.Z.of_nat n.val) <
    intOfZ (ZArith.BinInt.Z.of_nat
      CompCert4Lean.Lib.Integers.Int.wordsize) at hlt
  rw [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
    ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hlt
  exact Int.ofNat_lt.mp hlt

private theorem int_add_val_local' (x y : CCInt) :
    (CompCert4Lean.Lib.Integers.Int.add x y).val =
      (x.val + y.val) %
        (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize) := by
  unfold CompCert4Lean.Lib.Integers.Int.add WordCore.add
  change (WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (ZArith.BinInt.Z.add x.intval y.intval)).val = _
  rw [← int_zOfNat_val_local x, ← int_zOfNat_val_local y]
  have hadd : ZArith.BinInt.Z.add (zOfNat x.val) (zOfNat y.val) =
      zOfNat (x.val + y.val) := by
    unfold ZArith.BinInt.Z.add
    simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
      Int.ofNat_eq_natCast, Int.natCast_add]
  rw [hadd, repr_val_mod_local]

private theorem nat_or_mod_left_local (a b w : Nat)
    (hb : b < 2 ^ w) :
    Nat.lor (a % 2 ^ w) b = Nat.lor b a % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.lor_eq]
  rw [Nat.testBit_or, Nat.testBit_mod_two_pow,
    Nat.testBit_mod_two_pow, Nat.testBit_or]
  by_cases hk : k < w
  · have hkd : decide (k < w) = true := decide_eq_true hk
    rw [hkd, Bool.true_and]
    exact Bool.or_comm _ _
  · have hkw : w ≤ k := Nat.le_of_not_gt hk
    have hpow : 2 ^ w ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by decide) hkw
    have hb' : b < 2 ^ k := Nat.lt_of_lt_of_le hb hpow
    have hfb : b.testBit k = false := Nat.testBit_lt_two_pow hb'
    have hkd : decide (k < w) = false := decide_eq_false hk
    rw [hkd, Bool.false_and, hfb, Bool.false_or]
    simp

private theorem int_or_shl_shru_eq_ror_local
    (x n1 n2 : CCInt)
    (h1 : CompCert4Lean.Lib.Integers.Int.ltu n1
      CompCert4Lean.Lib.Integers.Int.iwordsize = true)
    (h2 : CompCert4Lean.Lib.Integers.Int.ltu n2
      CompCert4Lean.Lib.Integers.Int.iwordsize = true)
    (hadd : CompCert4Lean.Lib.Integers.Int.add n1 n2 =
      CompCert4Lean.Lib.Integers.Int.iwordsize) :
    CompCert4Lean.Lib.Integers.Int.or
        (CompCert4Lean.Lib.Integers.Int.shl x n1)
        (CompCert4Lean.Lib.Integers.Int.shru x n2) =
      CompCert4Lean.Lib.Integers.Int.ror x n2 := by
  have hn1 := int_ltu_iwordsize_val_local n1 h1
  have hn2 := int_ltu_iwordsize_val_local n2 h2
  have hn2mod : n2.val % CompCert4Lean.Lib.Integers.Int.wordsize =
      n2.val := Nat.mod_eq_of_lt hn2
  change n1.val < 32 at hn1
  change n2.val < 32 at hn2
  have hsum := congrArg (fun q : CCInt => q.val) hadd
  rw [int_add_val_local', Nat.mod_eq_of_lt (by
      change n1.val + n2.val < 2 ^ (32 : Nat)
      omega)] at hsum
  have hi : CompCert4Lean.Lib.Integers.Int.iwordsize.val =
      CompCert4Lean.Lib.Integers.Int.wordsize := rfl
  rw [hi] at hsum
  change n1.val + n2.val = 32 at hsum
  have hdiff : 32 - n2.val = n1.val := by omega
  have hdiffw : CompCert4Lean.Lib.Integers.Int.wordsize - n2.val =
      n1.val := by
    change 32 - n2.val = n1.val
    exact hdiff
  apply WordCore.ext_of_val_eq
  rw [int_or_val_local', int_shl_val_local, int_shru_val_local,
    int_ror_val_local]
  rw [hn2mod]
  rw [hdiffw]
  rw [← Nat.shiftLeft_eq x.val n1.val,
    ← Nat.shiftRight_eq_div_pow x.val n2.val]
  simp only [Nat.shiftRight_eq', Nat.shiftLeft_eq']
  apply nat_or_mod_left_local
  exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) x.toFin.isLt

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

private theorem int_eq_true_local (x y : CCInt)
    (h : CompCert4Lean.Lib.Integers.Int.eq x y = true) : x = y := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext
  have hd : decide (x.intval = y.intval) = true := by
    simpa [CompCert4Lean.Lib.Integers.Int.eq,
      CompCert4Lean.Lib.Integers.WordCore.eq] using h
  exact of_decide_eq_true hd

private theorem val_or_shl_shru_ror_local
    (v : val) (n1 n2 : CCInt)
    (hadd : CompCert4Lean.Lib.Integers.Int.add n1 n2 =
      CompCert4Lean.Lib.Integers.Int.iwordsize) :
    Val.lessdef
      (Val.or (Val.shl v (.Vint n1)) (Val.shru v (.Vint n2)))
      (Val.ror v (.Vint n2)) := by
  cases v with
  | Vint x =>
      by_cases h1 : CompCert4Lean.Lib.Integers.Int.ltu n1
          CompCert4Lean.Lib.Integers.Int.iwordsize = true
      · by_cases h2 : CompCert4Lean.Lib.Integers.Int.ltu n2
            CompCert4Lean.Lib.Integers.Int.iwordsize = true
        · change Val.lessdef
            (Val.or (Val.shl (.Vint x) (.Vint n1))
              (Val.shru (.Vint x) (.Vint n2)))
            (Val.ror (.Vint x) (.Vint n2))
          simp [Val.shl, h1, Val.shru, h2, Val.or, Val.ror]
          change Val.lessdef
            (.Vint (CompCert4Lean.Lib.Integers.Int.or
              (CompCert4Lean.Lib.Integers.Int.shl x n1)
              (CompCert4Lean.Lib.Integers.Int.shru x n2)))
            (.Vint (CompCert4Lean.Lib.Integers.Int.ror x n2))
          rw [int_or_shl_shru_eq_ror_local x n1 n2 h1 h2 hadd]
          exact Val.lessdef_refl _
        · simp [Val.shl, Val.shru, h1, h2, Val.or, Val.ror]
          exact Val.lessdef_undef _
      · simp [Val.shl, h1, Val.or, Val.ror]
        exact Val.lessdef_undef _
  | _ => exact Val.lessdef_undef _

private theorem eval_shlimm_inv_local
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (ge : CompCert4Lean.Backend.CminorSel.genv) (sp : val) (e : env)
    (m : CompCert4Lean.Common.Memory.mem)
    (le : letenv) (t : expr) (n : CCInt) (x : val)
    (h : eval_expr xi ge sp e m le
      (Eop (Oshlimm n) (Econs t Enil)) x) :
    ∃ v, eval_expr xi ge sp e m le t v ∧
      x = Val.shl v (.Vint n) := by
  cases h with
  | eval_Eop _ _ _ _ _ hargs hop =>
      cases hargs with
      | cons _ _ _ v _ hhead htail =>
          cases htail with
          | nil _ =>
              change some (Val.shl v (.Vint n)) = some x at hop
              cases hop
              exact ⟨v, hhead, rfl⟩

private theorem eval_shruimm_inv_local
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (ge : CompCert4Lean.Backend.CminorSel.genv) (sp : val) (e : env)
    (m : CompCert4Lean.Common.Memory.mem)
    (le : letenv) (t : expr) (n : CCInt) (x : val)
    (h : eval_expr xi ge sp e m le
      (Eop (Oshruimm n) (Econs t Enil)) x) :
    ∃ v, eval_expr xi ge sp e m le t v ∧
      x = Val.shru v (.Vint n) := by
  cases h with
  | eval_Eop _ _ _ _ _ hargs hop =>
      cases hargs with
      | cons _ _ _ v _ hhead htail =>
          cases htail with
          | nil _ =>
              change some (Val.shru v (.Vint n)) = some x at hop
              cases hop
              exact ⟨v, hhead, rfl⟩

theorem eval_or
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_orStatement := by
  unfold eval_orStatement binary_constructor_sound
  intro xi ge sp e m le a x b y ha hb
  cases hmatch : or_match a b with
  | or_case1 n1 _t2 =>
      have hx : x = .Vint n1 := eval_intconst_value_local xi ge sp e m le n1 x
        (by simpa [hmatch] using ha)
      subst x
      obtain ⟨v, hv, hd⟩ := eval_orimm_local xi ge sp e m n1 le b y hb
      refine ⟨v, ?_, ?_⟩
      · simpa [CompCert4Lean.X86.SelectOp.or, hmatch] using hv
      · rw [CompCert4Lean.Common.Values.Val.or_commut]
        exact hd
  | or_case2 _t1 n2 =>
      have hy : y = .Vint n2 := eval_intconst_value_local xi ge sp e m le n2 y
        (by simpa [hmatch] using hb)
      subst y
      obtain ⟨v, hv, hd⟩ := eval_orimm_local xi ge sp e m n2 le a x ha
      refine ⟨v, ?_, hd⟩
      simpa [CompCert4Lean.X86.SelectOp.or, hmatch] using hv
  | or_case3 n1 t1 n2 t2 =>
      obtain ⟨vx, htx, hx⟩ := eval_shlimm_inv_local
        xi ge sp e m le t1 n1 x ha
      obtain ⟨vy, hty, hy⟩ := eval_shruimm_inv_local
        xi ge sp e m le t2 n2 y hb
      subst x
      subst y
      by_cases heq : CompCert4Lean.Lib.Integers.Int.eq
          (CompCert4Lean.Lib.Integers.Int.add n1 n2)
          CompCert4Lean.Lib.Integers.Int.iwordsize = true
      · have hadd := int_eq_true_local _ _ heq
        by_cases hsame : same_expr_pure t1 t2 = true
        · obtain ⟨ht, hv⟩ := eval_same_expr xi ge sp e m
            t1 t2 le vx vy hsame htx hty
          subst t2
          subst vy
          refine ⟨Val.ror vx (.Vint n2), ?_, ?_⟩
          · simp only [CompCert4Lean.X86.SelectOp.or, hmatch,
              if_pos heq, if_pos hsame]
            apply eval_expr.eval_Eop le (Ororimm n2) (Econs t1 Enil) [vx]
              (Val.ror vx (.Vint n2))
            · exact eval_exprlist.cons le t1 Enil vx [] htx
                (eval_exprlist.nil le)
            · rfl
          · exact val_or_shl_shru_ror_local vx n1 n2 hadd
        · have hsub : CompCert4Lean.Lib.Integers.Int.sub
              CompCert4Lean.Lib.Integers.Int.iwordsize n1 = n2 :=
            int_add_sub_eq n1 n2
              CompCert4Lean.Lib.Integers.Int.iwordsize hadd
          refine ⟨Val.or (Val.shl vx (.Vint n1))
              (Val.shru vy (.Vint
                (CompCert4Lean.Lib.Integers.Int.sub
                  CompCert4Lean.Lib.Integers.Int.iwordsize n1))), ?_, ?_⟩
          · simp only [CompCert4Lean.X86.SelectOp.or, hmatch,
              if_pos heq, if_neg hsame]
            apply eval_expr.eval_Eop le (Oshldimm n1)
              (Econs t1 (Econs t2 Enil)) [vx, vy] _
            · exact eval_exprlist.cons le t1 (Econs t2 Enil) vx [vy] htx
                (eval_exprlist.cons le t2 Enil vy [] hty
                  (eval_exprlist.nil le))
            · rfl
          · rw [hsub]
            exact Val.lessdef_refl _
      · refine ⟨Val.or (Val.shl vx (.Vint n1))
            (Val.shru vy (.Vint n2)), ?_, Val.lessdef_refl _⟩
        simp only [CompCert4Lean.X86.SelectOp.or, hmatch, if_neg heq]
        apply eval_expr.eval_Eop le Oor
          (Econs (Eop (Oshlimm n1) (Econs t1 Enil))
            (Econs (Eop (Oshruimm n2) (Econs t2 Enil)) Enil))
          [Val.shl vx (.Vint n1), Val.shru vy (.Vint n2)] _
        · exact eval_exprlist.cons le _ _ _ _ ha
            (eval_exprlist.cons le _ _ _ _ hb (eval_exprlist.nil le))
        · rfl
  | or_case4 n2 t2 n1 t1 =>
      obtain ⟨vx, htx, hx⟩ := eval_shruimm_inv_local
        xi ge sp e m le t2 n2 x ha
      obtain ⟨vy, hty, hy⟩ := eval_shlimm_inv_local
        xi ge sp e m le t1 n1 y hb
      subst x
      subst y
      by_cases heq : CompCert4Lean.Lib.Integers.Int.eq
          (CompCert4Lean.Lib.Integers.Int.add n1 n2)
          CompCert4Lean.Lib.Integers.Int.iwordsize = true
      · have hadd := int_eq_true_local _ _ heq
        by_cases hsame : same_expr_pure t1 t2 = true
        · obtain ⟨ht, hv⟩ := eval_same_expr xi ge sp e m
            t1 t2 le vy vx hsame hty htx
          subst t2
          subst vx
          refine ⟨Val.ror vy (.Vint n2), ?_, ?_⟩
          · simp only [CompCert4Lean.X86.SelectOp.or, hmatch,
              if_pos heq, if_pos hsame]
            apply eval_expr.eval_Eop le (Ororimm n2) (Econs t1 Enil) [vy]
              (Val.ror vy (.Vint n2))
            · exact eval_exprlist.cons le t1 Enil vy [] hty
                (eval_exprlist.nil le)
            · rfl
          · rw [CompCert4Lean.Common.Values.Val.or_commut]
            exact val_or_shl_shru_ror_local vy n1 n2 hadd
        · have hsub : CompCert4Lean.Lib.Integers.Int.sub
              CompCert4Lean.Lib.Integers.Int.iwordsize n1 = n2 :=
            int_add_sub_eq n1 n2
              CompCert4Lean.Lib.Integers.Int.iwordsize hadd
          refine ⟨Val.or (Val.shl vy (.Vint n1))
              (Val.shru vx (.Vint
                (CompCert4Lean.Lib.Integers.Int.sub
                  CompCert4Lean.Lib.Integers.Int.iwordsize n1))), ?_, ?_⟩
          · simp only [CompCert4Lean.X86.SelectOp.or, hmatch,
              if_pos heq, if_neg hsame]
            apply eval_expr.eval_Eop le (Oshldimm n1)
              (Econs t1 (Econs t2 Enil)) [vy, vx] _
            · exact eval_exprlist.cons le t1 (Econs t2 Enil) vy [vx] hty
                (eval_exprlist.cons le t2 Enil vx [] htx
                  (eval_exprlist.nil le))
            · rfl
          · rw [hsub, CompCert4Lean.Common.Values.Val.or_commut]
            exact Val.lessdef_refl _
      · refine ⟨Val.or (Val.shru vx (.Vint n2))
            (Val.shl vy (.Vint n1)), ?_, Val.lessdef_refl _⟩
        simp only [CompCert4Lean.X86.SelectOp.or, hmatch, if_neg heq]
        apply eval_expr.eval_Eop le Oor
          (Econs (Eop (Oshruimm n2) (Econs t2 Enil))
            (Econs (Eop (Oshlimm n1) (Econs t1 Enil)) Enil))
          [Val.shru vx (.Vint n2), Val.shl vy (.Vint n1)] _
        · exact eval_exprlist.cons le _ _ _ _ ha
            (eval_exprlist.cons le _ _ _ _ hb (eval_exprlist.nil le))
        · rfl
  | or_default e1 e2 =>
      refine ⟨Val.or x y, ?_, Val.lessdef_refl _⟩
      simp only [CompCert4Lean.X86.SelectOp.or, hmatch]
      apply eval_expr.eval_Eop le Oor (Econs a (Econs b Enil)) [x, y]
        (Val.or x y)
      · exact eval_exprlist.cons le a (Econs b Enil) x [y] ha
          (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))
      · rfl

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

theorem eval_divs_base
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_divs_baseStatement := by
  intro xi ge sp e m le a b x y z ha hb hdiv
  refine ⟨z, ?_, Val.lessdef_refl _⟩
  unfold divs_base
  apply eval_expr.eval_Eop le Odiv (Econs a (Econs b Enil)) [x, y] z
  · exact eval_exprlist.cons le a (Econs b Enil) x [y] ha
      (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))
  · exact hdiv

theorem eval_divu_base
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_divu_baseStatement := by
  intro xi ge sp e m le a b x y z ha hb hdiv
  refine ⟨z, ?_, Val.lessdef_refl _⟩
  unfold divu_base
  apply eval_expr.eval_Eop le Odivu (Econs a (Econs b Enil)) [x, y] z
  · exact eval_exprlist.cons le a (Econs b Enil) x [y] ha
      (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))
  · exact hdiv

theorem eval_mods_base
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_mods_baseStatement := by
  intro xi ge sp e m le a b x y z ha hb hmod
  refine ⟨z, ?_, Val.lessdef_refl _⟩
  unfold mods_base
  apply eval_expr.eval_Eop le Omod (Econs a (Econs b Enil)) [x, y] z
  · exact eval_exprlist.cons le a (Econs b Enil) x [y] ha
      (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))
  · exact hmod

theorem eval_modu_base
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_modu_baseStatement := by
  intro xi ge sp e m le a b x y z ha hb hmod
  refine ⟨z, ?_, Val.lessdef_refl _⟩
  unfold modu_base
  apply eval_expr.eval_Eop le Omodu (Econs a (Econs b Enil)) [x, y] z
  · exact eval_exprlist.cons le a (Econs b Enil) x [y] ha
      (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))
  · exact hmod

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp
open Lean Elab Tactic Meta

private theorem int_shrx_zero_local (x : CCInt) :
    CompCert4Lean.Lib.Integers.Int.shrx x
      CompCert4Lean.Lib.Integers.Int.zero = x := by
  change CompCert4Lean.Lib.Integers.Int.divs x
      (CompCert4Lean.Lib.Integers.Int.shl
        CompCert4Lean.Lib.Integers.Int.one
        CompCert4Lean.Lib.Integers.Int.zero) = x
  rw [CompCert4Lean.Lib.Integers.Int.shl_zero_proof]
  unfold CompCert4Lean.Lib.Integers.Int.divs
    CompCert4Lean.Lib.Integers.WordCore.divs
  have hone : CompCert4Lean.Lib.Integers.WordCore.signed
      CompCert4Lean.Lib.Integers.Int.one =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1 := by rfl
  rw [hone]
  have hquot : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.quot
      (CompCert4Lean.Lib.Integers.WordCore.signed x)
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1) =
      CompCert4Lean.Lib.Integers.WordCore.signed x := by
    have honez : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1 =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH := by rfl
    rw [honez]
    exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.quot_1_r _
  change CompCert4Lean.Lib.Integers.WordCore.repr
      CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.quot
        (CompCert4Lean.Lib.Integers.WordCore.signed x)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1)) = x
  rw [hquot]
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  change (CompCert4Lean.Lib.Integers.WordCore.repr
      CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Lib.Integers.WordCore.signed x)).val = x.val
  rw [show CompCert4Lean.Lib.Integers.WordCore.signed x =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.WordCore.signed x)) by
    exact (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt_intOfZ _).symm]
  rw [word_val_repr_local]
  simp only [CompCert4Lean.Lib.Integers.WordCore.signed,
    CompCert4Lean.Lib.Integers.WordCore.unsigned,
    CompCert4Lean.Lib.Integers.Int.wordsize]
  run_tac
    let zltName := Lean.mkIdent
      (selectOpproofPrivateName "CompCert4Lean.Lib.Integers.zltSelect")
    let selectName := Lean.mkIdent
      (selectOpproofPrivateName "CompCert4Lean.Lib.Integers.sumboolSelect")
    let subName := Lean.mkIdent
      (selectOpproofPrivateName "CompCert4Lean.Lib.Integers.zSub")
    let powerName := Lean.mkIdent
      (selectOpproofPrivateName "CompCert4Lean.Lib.Integers.zTwoPowerNat")
    evalTactic (← `(tactic|
      unfold $zltName $selectName $subName $powerName))
  have hxrepr : x.intval = zOfNat x.val :=
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Z2Nat.id x.intval (by
      have h := x.intrange.1
      change (-1 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval at h
      change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval
      omega)).symm
  rw [hxrepr]
  split
  · rw [show zOfNat x.val =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat x.val) by rfl,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change Int.toNat ((Int.ofNat x.val) % (2 ^ 32 : Int)) = x.val
    have hvalLt : Int.ofNat x.val < (2 ^ 32 : Int) := by
      change Int.ofNat x.val < Int.ofNat (2 ^ 32)
      exact Int.ofNat_lt.mpr x.toFin.isLt
    have hmod := Int.emod_eq_of_lt (Int.natCast_nonneg _) hvalLt
    simpa using congrArg Int.toNat hmod
  · have hp : CompCert4Lean.Foundation.Numbers.Rocq.Coq.two_power_nat 32 =
        zOfNat (2 ^ 32) := by rfl
    rw [hp]
    rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub
          (zOfNat x.val) (zOfNat (2 ^ 32)) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (Int.ofNat x.val - (2 ^ 32 : Int)) by
          apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
          simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          rfl,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change Int.toNat
      (((Int.ofNat x.val) - (2 ^ 32 : Int)) % (2 ^ 32 : Int)) = x.val
    rw [Int.sub_emod]
    rw [Int.emod_self, Int.sub_zero]
    have hvalLt : Int.ofNat x.val < (2 ^ 32 : Int) := by
      change Int.ofNat x.val < Int.ofNat (2 ^ 32)
      exact Int.ofNat_lt.mpr x.toFin.isLt
    have hmod := Int.emod_eq_of_lt (Int.natCast_nonneg _) hvalLt
    simpa using congrArg Int.toNat hmod

theorem eval_shrximm
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_shrximmStatement := by
  intro xi ge sp e m le a n x z ha hz
  rw [CompCert4Lean.X86.SelectOp.shrximm]
  split
  · rename_i hn
    have hn' := int_eq_true_local n
      CompCert4Lean.Lib.Integers.Int.zero hn
    subst n
    refine ⟨x, ha, ?_⟩
    cases x with
    | Vint nx =>
        simp only [CompCert4Lean.Common.Values.Val.shrx] at hz
        split at hz
        · cases hz
          change Val.lessdef
            (.Vint (CompCert4Lean.Lib.Integers.Int.shrx nx
              CompCert4Lean.Lib.Integers.Int.zero)) (.Vint nx)
          rw [int_shrx_zero_local nx]
          exact Val.lessdef_refl _
        · cases hz
    | Vundef => cases hz
    | Vlong _ => cases hz
    | Vfloat _ => cases hz
    | Vsingle _ => cases hz
    | Vptr _ _ => cases hz
  · rename_i hn
    cases x with
    | Vint nx =>
        simp only [CompCert4Lean.Common.Values.Val.shrx] at hz
        split at hz
        · cases hz
          refine ⟨.Vint (CompCert4Lean.Lib.Integers.Int.shrx nx n), ?_, ?_⟩
          · apply eval_expr.eval_Eop le (Oshrximm n) (Econs a Enil)
                [.Vint nx] _
            · exact eval_exprlist.cons le a Enil _ [] ha
                (eval_exprlist.nil le)
            · change CompCert4Lean.Common.Values.Val.shrx
                (.Vint nx) (.Vint n) =
                some (.Vint (CompCert4Lean.Lib.Integers.Int.shrx nx n))
              simp only [CompCert4Lean.Common.Values.Val.shrx]
              split
              · rfl
              · contradiction
          · change Val.lessdef
              (.Vint (CompCert4Lean.Lib.Integers.Int.shrx nx n))
              (.Vint (CompCert4Lean.Lib.Integers.Int.shrx nx n))
            exact Val.lessdef_refl _
        · cases hz
    | Vundef => cases hz
    | Vlong _ => cases hz
    | Vfloat _ => cases hz
    | Vsingle _ => cases hz
    | Vptr _ _ => cases hz

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

private theorem int_mul_val_eval_shl_local (x y : CCInt) :
    (CompCert4Lean.Lib.Integers.Int.mul x y).val =
      (x.val * y.val) %
        (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize) := by
  unfold CompCert4Lean.Lib.Integers.Int.mul WordCore.mul
  change (WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
        x.intval y.intval)).val = _
  rw [← int_zOfNat_val_local x, ← int_zOfNat_val_local y]
  have hmul : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
      (zOfNat x.val) (zOfNat y.val) =
      zOfNat (x.val * y.val) := by
    unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
      Int.ofNat_eq_natCast, Int.natCast_mul]
  rw [hmul, repr_val_mod_local]

private theorem int_shl_mul_eval_shl_local (x n : CCInt) :
    CompCert4Lean.Lib.Integers.Int.shl x n =
      CompCert4Lean.Lib.Integers.Int.mul x
        (CompCert4Lean.Lib.Integers.Int.shl
          CompCert4Lean.Lib.Integers.Int.one n) := by
  apply WordCore.ext_of_val_eq
  rw [int_shl_val_local, int_mul_val_eval_shl_local,
    int_shl_val_local]
  change (x.val * 2 ^ n.val) % (2 ^ 32) =
    (x.val * ((1 * 2 ^ n.val) % (2 ^ 32))) % (2 ^ 32)
  simp only [Nat.one_mul, Nat.mul_mod_mod]

private theorem val_shl_mul_eval_shl_local (x : val) (n : CCInt)
    (hn : CompCert4Lean.Lib.Integers.Int.ltu n
      CompCert4Lean.Lib.Integers.Int.iwordsize = true) :
    Val.mul x
        (.Vint (CompCert4Lean.Lib.Integers.Int.shl
          CompCert4Lean.Lib.Integers.Int.one n)) =
      Val.shl x (.Vint n) := by
  cases x with
  | Vint x =>
      simp only [Val.mul, Val.shl, hn, if_true]
      change CompCert4Lean.Common.Values.val.Vint
          (CompCert4Lean.Lib.Integers.Int.mul x
          (CompCert4Lean.Lib.Integers.Int.shl
            CompCert4Lean.Lib.Integers.Int.one n)) =
        CompCert4Lean.Common.Values.val.Vint
          (CompCert4Lean.Lib.Integers.Int.shl x n)
      exact congrArg (fun q : CCInt =>
        CompCert4Lean.Common.Values.val.Vint q)
        (int_shl_mul_eval_shl_local x n).symm
  | Vundef => rfl
  | Vlong _ => rfl
  | Vfloat _ => rfl
  | Vsingle _ => rfl
  | Vptr _ _ => rfl

private theorem val_mul_add_zero_eval_shl_local (x : val) (k : CCInt) :
    Val.add (Val.mul x (.Vint k))
        (.Vint CompCert4Lean.Lib.Integers.Int.zero) =
      Val.mul x (.Vint k) := by
  cases x with
  | Vint x =>
      simp only [Val.mul, Val.add]
      change CompCert4Lean.Common.Values.val.Vint
          (CompCert4Lean.Lib.Integers.Int.add
          (CompCert4Lean.Lib.Integers.Int.mul x k)
          CompCert4Lean.Lib.Integers.Int.zero) =
        CompCert4Lean.Common.Values.val.Vint
          (CompCert4Lean.Lib.Integers.Int.mul x k)
      exact congrArg (fun q : CCInt =>
        CompCert4Lean.Common.Values.val.Vint q)
        (CompCert4Lean.Lib.Integers.Int.add_zero_proof _)
  | Vundef => rfl
  | Vlong _ => rfl
  | Vfloat _ => rfl
  | Vsingle _ => rfl
  | Vptr _ _ => rfl

private theorem val_shl_add_eval_shl_local (x y : val) (n : CCInt)
    (hn : CompCert4Lean.Lib.Integers.Int.ltu n
      CompCert4Lean.Lib.Integers.Int.iwordsize = true) :
    Val.shl (Val.add x y) (.Vint n) =
      Val.add
        (Val.mul x (.Vint (CompCert4Lean.Lib.Integers.Int.shl
          CompCert4Lean.Lib.Integers.Int.one n)))
        (Val.shl y (.Vint n)) := by
  calc
    Val.shl (Val.add x y) (.Vint n) =
        Val.mul (Val.add x y)
          (.Vint (CompCert4Lean.Lib.Integers.Int.shl
            CompCert4Lean.Lib.Integers.Int.one n)) :=
      (val_shl_mul_eval_shl_local (Val.add x y) n hn).symm
    _ = Val.add
        (Val.mul x (.Vint (CompCert4Lean.Lib.Integers.Int.shl
          CompCert4Lean.Lib.Integers.Int.one n)))
        (Val.mul y (.Vint (CompCert4Lean.Lib.Integers.Int.shl
          CompCert4Lean.Lib.Integers.Int.one n))) :=
      Val.mul_add_distr_l x y _
    _ = Val.add
        (Val.mul x (.Vint (CompCert4Lean.Lib.Integers.Int.shl
          CompCert4Lean.Lib.Integers.Int.one n)))
        (Val.shl y (.Vint n)) := by
      rw [val_shl_mul_eval_shl_local y n hn]

private theorem int_shl_shl_eval_shl_local (x n1 n : CCInt)
    (hn1 : CompCert4Lean.Lib.Integers.Int.ltu n1
      CompCert4Lean.Lib.Integers.Int.iwordsize = true)
    (hn : CompCert4Lean.Lib.Integers.Int.ltu n
      CompCert4Lean.Lib.Integers.Int.iwordsize = true) :
    CompCert4Lean.Lib.Integers.Int.shl
        (CompCert4Lean.Lib.Integers.Int.shl x n1) n =
      CompCert4Lean.Lib.Integers.Int.shl x
        (CompCert4Lean.Lib.Integers.Int.add n n1) := by
  have hn1v := int_ltu_iwordsize_val_local n1 hn1
  have hnv := int_ltu_iwordsize_val_local n hn
  change n1.val < 32 at hn1v
  change n.val < 32 at hnv
  have hsum : n.val + n1.val <
      2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := by
    change n.val + n1.val < 2 ^ 32
    omega
  apply WordCore.ext_of_val_eq
  rw [int_shl_val_local, int_shl_val_local, int_shl_val_local,
    int_add_val_local', Nat.mod_eq_of_lt hsum]
  rw [Nat.pow_add]
  calc
    (((x.val * 2 ^ n1.val) % (2 ^ 32)) * 2 ^ n.val) % (2 ^ 32) =
        (x.val * 2 ^ n1.val * 2 ^ n.val) % (2 ^ 32) := by
      rw [Nat.mul_comm ((x.val * 2 ^ n1.val) % (2 ^ 32)) (2 ^ n.val),
        Nat.mul_mod_mod,
        Nat.mul_comm (2 ^ n.val) (x.val * 2 ^ n1.val)]
    _ = (x.val * (2 ^ n.val * 2 ^ n1.val)) % (2 ^ 32) := by
      congr 1
      ac_rfl

private theorem val_shl_shl_eval_shl_local (x : val) (n1 n : CCInt)
    (hn : CompCert4Lean.Lib.Integers.Int.ltu n
      CompCert4Lean.Lib.Integers.Int.iwordsize = true)
    (hadd : CompCert4Lean.Lib.Integers.Int.ltu
      (CompCert4Lean.Lib.Integers.Int.add n n1)
      CompCert4Lean.Lib.Integers.Int.iwordsize = true) :
    Val.lessdef
      (Val.shl (Val.shl x (.Vint n1)) (.Vint n))
      (Val.shl x
        (.Vint (CompCert4Lean.Lib.Integers.Int.add n n1))) := by
  cases x with
  | Vint x =>
      by_cases hn1 : CompCert4Lean.Lib.Integers.Int.ltu n1
          CompCert4Lean.Lib.Integers.Int.iwordsize = true
      · simp only [Val.shl, hn1, hn, hadd, if_true]
        change Val.lessdef
          (.Vint (CompCert4Lean.Lib.Integers.Int.shl
            (CompCert4Lean.Lib.Integers.Int.shl x n1) n))
          (.Vint (CompCert4Lean.Lib.Integers.Int.shl x
            (CompCert4Lean.Lib.Integers.Int.add n n1)))
        rw [int_shl_shl_eval_shl_local x n1 n hn1 hn]
        exact Val.lessdef_refl _
      · have hn1f : CompCert4Lean.Lib.Integers.Int.ltu n1
            CompCert4Lean.Lib.Integers.Int.iwordsize = false :=
          Bool.eq_false_iff.mpr hn1
        simp only [Val.shl, hn1f, Bool.false_eq_true, if_false]
        exact Val.lessdef_undef _
  | Vundef => exact Val.lessdef_undef _
  | Vlong _ => exact Val.lessdef_undef _
  | Vfloat _ => exact Val.lessdef_undef _
  | Vsingle _ => exact Val.lessdef_undef _
  | Vptr _ _ => exact Val.lessdef_undef _

private theorem eval_lea_indexed_inv_eval_shl_local
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (le : letenv) (t : expr)
    (ofs : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (x : val)
    (h : eval_expr xi ge sp e m le
      (Eop (Olea (Aindexed ofs)) (Econs t Enil)) x) :
    ∃ v, eval_expr xi ge sp e m le t v ∧
      x = Val.add v
        (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs)) := by
  cases h with
  | eval_Eop _ _ _ _ _ hargs hop =>
      cases hargs with
      | cons _ _ _ v _ hhead htail =>
          cases htail with
          | nil _ =>
              change some (Val.add v
                (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs))) = some x at hop
              cases hop
              exact ⟨v, hhead, rfl⟩

private theorem eval_shlimm_for_eval_shl_local
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (n : CCInt) :
    unary_constructor_sound xi ge sp e m (fun a => shlimm a n)
      (fun x => Val.shl x (.Vint n)) := by
  intro le a x ha
  change ∃ v, eval_expr xi ge sp e m le (shlimm a n) v ∧
    Val.lessdef (Val.shl x (.Vint n)) v
  unfold shlimm
  by_cases hz : CompCert4Lean.Lib.Integers.Int.eq n
      CompCert4Lean.Lib.Integers.Int.zero = true
  · rw [if_pos hz]
    have hn := int_eq_true_zero_local n hz
    subst n
    refine ⟨x, ha, ?_⟩
    cases x with
    | Vint x =>
        simp only [Val.shl]
        change Val.lessdef
          (if CompCert4Lean.Lib.Integers.Int.ltu
              CompCert4Lean.Lib.Integers.Int.zero
              CompCert4Lean.Lib.Integers.Int.iwordsize = true then
            .Vint (CompCert4Lean.Lib.Integers.Int.shl x
              CompCert4Lean.Lib.Integers.Int.zero)
          else .Vundef) (.Vint x)
        simp only [show CompCert4Lean.Lib.Integers.Int.ltu
            CompCert4Lean.Lib.Integers.Int.zero
            CompCert4Lean.Lib.Integers.Int.iwordsize = true by rfl,
          ]
        have hi : True := trivial
        rw [if_pos hi]
        rw [CompCert4Lean.Lib.Integers.Int.shl_zero_proof]
        exact Val.lessdef_refl _
    | _ => exact Val.lessdef_undef _
  · rw [if_neg hz]
    by_cases hn : CompCert4Lean.Lib.Integers.Int.ltu n
        CompCert4Lean.Lib.Integers.Int.iwordsize = true
    · simp only [hn, Bool.not_true, Bool.false_eq_true, if_false]
      cases hmatch : shlimm_match a with
      | shlimm_case1 n1 =>
          have hx : x = .Vint n1 := eval_intconst_value_local
            xi ge sp e m le n1 x (by simpa [hmatch] using ha)
          subst x
          refine ⟨.Vint (CompCert4Lean.Lib.Integers.Int.shl n1 n), ?_, ?_⟩
          · exact eval_expr.eval_Eop le
              (Ointconst (CompCert4Lean.Lib.Integers.Int.shl n1 n))
              Enil [] _ (eval_exprlist.nil le) rfl
          · simp only [Val.shl, hn, if_true]
            exact Val.lessdef_refl _
      | shlimm_case2 n1 t1 =>
          obtain ⟨v1, ht1, hx⟩ := eval_shlimm_inv_local
            xi ge sp e m le t1 n1 x (by simpa [hmatch] using ha)
          subst x
          by_cases hadd : CompCert4Lean.Lib.Integers.Int.ltu
              (CompCert4Lean.Lib.Integers.Int.add n n1)
              CompCert4Lean.Lib.Integers.Int.iwordsize = true
          · refine ⟨Val.shl v1
                (.Vint (CompCert4Lean.Lib.Integers.Int.add n n1)), ?_, ?_⟩
            · simp only [hadd, if_true]
              exact eval_expr.eval_Eop le
                (Oshlimm (CompCert4Lean.Lib.Integers.Int.add n n1))
                (Econs t1 Enil) [v1] _
                (eval_exprlist.cons le t1 Enil v1 [] ht1
                  (eval_exprlist.nil le)) rfl
            · exact val_shl_shl_eval_shl_local v1 n1 n hn hadd
          · have haddf : CompCert4Lean.Lib.Integers.Int.ltu
                (CompCert4Lean.Lib.Integers.Int.add n n1)
                CompCert4Lean.Lib.Integers.Int.iwordsize = false :=
              Bool.eq_false_iff.mpr hadd
            refine ⟨Val.shl (Val.shl v1 (.Vint n1)) (.Vint n), ?_,
              Val.lessdef_refl _⟩
            simp only [haddf, Bool.false_eq_true, if_false]
            exact eval_expr.eval_Eop le (Oshlimm n)
              (Econs (Eop (Oshlimm n1) (Econs t1 Enil)) Enil)
              [Val.shl v1 (.Vint n1)] _
              (eval_exprlist.cons le _ Enil _ [] ha
                (eval_exprlist.nil le)) rfl
      | shlimm_case3 ofs t1 =>
          obtain ⟨v1, ht1, hx⟩ := eval_lea_indexed_inv_eval_shl_local
            xi ge sp e m le t1 ofs x (by simpa [hmatch] using ha)
          subst x
          by_cases hscale : shift_is_scale n = true
          · refine ⟨Val.add
                (Val.mul v1 (.Vint (CompCert4Lean.Lib.Integers.Int.repr
                  (CompCert4Lean.Lib.Integers.Int.unsigned
                    (CompCert4Lean.Lib.Integers.Int.shl
                      CompCert4Lean.Lib.Integers.Int.one n)))))
                (.Vint (CompCert4Lean.Lib.Integers.Int.repr
                  (CompCert4Lean.Lib.Integers.Int.unsigned
                    (CompCert4Lean.Lib.Integers.Int.shl
                      (CompCert4Lean.Lib.Integers.Int.repr ofs) n)))), ?_, ?_⟩
            · simp only [hscale, if_true]
              exact eval_expr.eval_Eop le
                (Olea (Ascaled
                  (CompCert4Lean.Lib.Integers.Int.unsigned
                    (CompCert4Lean.Lib.Integers.Int.shl
                      CompCert4Lean.Lib.Integers.Int.one n))
                  (CompCert4Lean.Lib.Integers.Int.unsigned
                    (CompCert4Lean.Lib.Integers.Int.shl
                      (CompCert4Lean.Lib.Integers.Int.repr ofs) n))))
                (Econs t1 Enil) [v1] _
                (eval_exprlist.cons le t1 Enil v1 [] ht1
                  (eval_exprlist.nil le)) rfl
            · rw [CompCert4Lean.Lib.Integers.Int.repr_unsigned_proof,
                CompCert4Lean.Lib.Integers.Int.repr_unsigned_proof]
              rw [val_shl_add_eval_shl_local v1
                (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs)) n hn]
              simp only [Val.shl, hn, if_true]
              exact Val.lessdef_refl _
          · have hscalef : shift_is_scale n = false :=
              Bool.eq_false_iff.mpr hscale
            refine ⟨Val.shl
                (Val.add v1 (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs)))
                (.Vint n), ?_, Val.lessdef_refl _⟩
            simp only [hscalef, Bool.false_eq_true, if_false]
            exact eval_expr.eval_Eop le (Oshlimm n)
              (Econs (Eop (Olea (Aindexed ofs)) (Econs t1 Enil)) Enil)
              [Val.add v1 (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs))] _
              (eval_exprlist.cons le _ Enil _ [] ha
                (eval_exprlist.nil le)) rfl
      | shlimm_default e1 =>
          by_cases hscale : shift_is_scale n = true
          · refine ⟨Val.add
                (Val.mul x (.Vint (CompCert4Lean.Lib.Integers.Int.repr
                  (CompCert4Lean.Lib.Integers.Int.unsigned
                    (CompCert4Lean.Lib.Integers.Int.shl
                      CompCert4Lean.Lib.Integers.Int.one n)))))
                (.Vint (CompCert4Lean.Lib.Integers.Int.repr
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0))), ?_, ?_⟩
            · simp only [hscale, if_true]
              exact eval_expr.eval_Eop le
                (Olea (Ascaled
                  (CompCert4Lean.Lib.Integers.Int.unsigned
                    (CompCert4Lean.Lib.Integers.Int.shl
                      CompCert4Lean.Lib.Integers.Int.one n))
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0)))
                (Econs a Enil) [x] _
                (eval_exprlist.cons le a Enil x [] ha
                  (eval_exprlist.nil le)) rfl
            · rw [CompCert4Lean.Lib.Integers.Int.repr_unsigned_proof]
              change Val.lessdef (Val.shl x (.Vint n))
                (Val.add
                  (Val.mul x (.Vint
                    (CompCert4Lean.Lib.Integers.Int.shl
                      CompCert4Lean.Lib.Integers.Int.one n)))
                  (.Vint CompCert4Lean.Lib.Integers.Int.zero))
              rw [val_mul_add_zero_eval_shl_local,
                val_shl_mul_eval_shl_local x n hn]
              exact Val.lessdef_refl _
          · have hscalef : shift_is_scale n = false :=
              Bool.eq_false_iff.mpr hscale
            refine ⟨Val.shl x (.Vint n), ?_, Val.lessdef_refl _⟩
            simp only [hscalef, Bool.false_eq_true, if_false]
            exact eval_expr.eval_Eop le (Oshlimm n) (Econs a Enil)
              [x] _ (eval_exprlist.cons le a Enil x [] ha
                (eval_exprlist.nil le)) rfl
    · have hnf : CompCert4Lean.Lib.Integers.Int.ltu n
          CompCert4Lean.Lib.Integers.Int.iwordsize = false :=
        Bool.eq_false_iff.mpr hn
      simp only [hnf, Bool.not_false, if_true]
      refine ⟨Val.shl x (.Vint n), ?_, Val.lessdef_refl _⟩
      exact eval_expr.eval_Eop le Oshl
        (Econs a (Econs (Eop (Ointconst n) Enil) Enil))
        [x, .Vint n] _
        (eval_exprlist.cons le a _ x [.Vint n] ha
          (eval_exprlist.cons le (Eop (Ointconst n) Enil) Enil
            (.Vint n) []
            (eval_expr.eval_Eop le (Ointconst n) Enil [] (.Vint n)
              (eval_exprlist.nil le) rfl)
            (eval_exprlist.nil le))) rfl

theorem eval_shl
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_shlStatement := by
  unfold eval_shlStatement binary_constructor_sound
  intro xi ge sp e m le a x b y ha hb
  cases hmatch : shl_match b with
  | shl_case1 n =>
      have hy : y = .Vint n := eval_intconst_value_local
        xi ge sp e m le n y (by simpa [hmatch] using hb)
      subst y
      obtain ⟨v, hv, hd⟩ := eval_shlimm_for_eval_shl_local
        xi ge sp e m n le a x ha
      refine ⟨v, ?_, hd⟩
      simpa [CompCert4Lean.X86.SelectOp.shl, hmatch] using hv
  | shl_default e2 =>
      refine ⟨Val.shl x y, ?_, Val.lessdef_refl _⟩
      simp only [CompCert4Lean.X86.SelectOp.shl, hmatch]
      exact eval_expr.eval_Eop le Oshl (Econs a (Econs b Enil))
        [x, y] _
        (eval_exprlist.cons le a (Econs b Enil) x [y] ha
          (eval_exprlist.cons le b Enil y [] hb
            (eval_exprlist.nil le))) rfl

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

private theorem val_shru_shru_local (x : val)
    (n1 n : CompCert4Lean.Lib.Integers.int)
    (hn : CompCert4Lean.Lib.Integers.Int.ltu n
      CompCert4Lean.Lib.Integers.Int.iwordsize = true)
    (hadd : CompCert4Lean.Lib.Integers.Int.ltu
      (CompCert4Lean.Lib.Integers.Int.add n n1)
      CompCert4Lean.Lib.Integers.Int.iwordsize = true) :
    Val.lessdef
      (Val.shru (Val.shru x (.Vint n1)) (.Vint n))
      (Val.shru x
        (.Vint (CompCert4Lean.Lib.Integers.Int.add n n1))) := by
  cases x with
  | Vint x =>
      by_cases hn1' : CompCert4Lean.Lib.Integers.Int.ltu n1
          CompCert4Lean.Lib.Integers.Int.iwordsize = true
      · have hadd' : CompCert4Lean.Lib.Integers.Int.ltu
            (CompCert4Lean.Lib.Integers.Int.add n1 n)
            CompCert4Lean.Lib.Integers.Int.iwordsize = true := by
          rw [CompCert4Lean.Lib.Integers.Int.add_commut_proof]
          exact hadd
        simp only [Val.shru, hn1', hn, hadd, if_true]
        change Val.lessdef
          (.Vint (CompCert4Lean.Lib.Integers.Int.shru
            (CompCert4Lean.Lib.Integers.Int.shru x n1) n))
          (.Vint (CompCert4Lean.Lib.Integers.Int.shru x
            (CompCert4Lean.Lib.Integers.Int.add n n1)))
        rw [CompCert4Lean.Lib.Integers.Int.shru_shru_proof
          x n1 n hn1' hn hadd',
          CompCert4Lean.Lib.Integers.Int.add_commut_proof]
        exact Val.lessdef_refl _
      · have hn1f : CompCert4Lean.Lib.Integers.Int.ltu n1
            CompCert4Lean.Lib.Integers.Int.iwordsize = false :=
          Bool.eq_false_iff.mpr hn1'
        simp only [Val.shru, hn1f, Bool.false_eq_true, if_false]
        exact Val.lessdef_undef _
  | Vundef => exact Val.lessdef_undef _
  | Vlong _ => exact Val.lessdef_undef _
  | Vfloat _ => exact Val.lessdef_undef _
  | Vsingle _ => exact Val.lessdef_undef _
  | Vptr _ _ => exact Val.lessdef_undef _

private theorem eval_shruimm_for_eval_shru_local
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (n : CompCert4Lean.Lib.Integers.int) :
    unary_constructor_sound xi ge sp e m (fun a => shruimm a n)
      (fun x => Val.shru x (.Vint n)) := by
  intro le a x ha
  change ∃ v, eval_expr xi ge sp e m le (shruimm a n) v ∧
    Val.lessdef (Val.shru x (.Vint n)) v
  unfold shruimm
  by_cases hz : CompCert4Lean.Lib.Integers.Int.eq n
      CompCert4Lean.Lib.Integers.Int.zero = true
  · rw [if_pos hz]
    have hn := int_eq_true_zero_local n hz
    subst n
    refine ⟨x, ha, ?_⟩
    cases x with
    | Vint x =>
        simp only [Val.shru]
        change Val.lessdef
          (if CompCert4Lean.Lib.Integers.Int.ltu
              CompCert4Lean.Lib.Integers.Int.zero
              CompCert4Lean.Lib.Integers.Int.iwordsize = true then
            .Vint (CompCert4Lean.Lib.Integers.Int.shru x
              CompCert4Lean.Lib.Integers.Int.zero)
          else .Vundef) (.Vint x)
        simp only [show CompCert4Lean.Lib.Integers.Int.ltu
            CompCert4Lean.Lib.Integers.Int.zero
            CompCert4Lean.Lib.Integers.Int.iwordsize = true by rfl]
        rw [CompCert4Lean.Lib.Integers.Int.shru_zero_proof]
        exact Val.lessdef_refl _
    | _ => exact Val.lessdef_undef _
  · rw [if_neg hz]
    by_cases hn : CompCert4Lean.Lib.Integers.Int.ltu n
        CompCert4Lean.Lib.Integers.Int.iwordsize = true
    · simp only [hn, Bool.not_true, Bool.false_eq_true, if_false]
      cases hmatch : shruimm_match a with
      | shruimm_case1 n1 =>
          have hx : x = .Vint n1 := eval_intconst_value_local
            xi ge sp e m le n1 x (by simpa [hmatch] using ha)
          subst x
          refine ⟨.Vint (CompCert4Lean.Lib.Integers.Int.shru n1 n), ?_, ?_⟩
          · exact eval_expr.eval_Eop le
              (Ointconst (CompCert4Lean.Lib.Integers.Int.shru n1 n))
              Enil [] _ (eval_exprlist.nil le) rfl
          · simp only [Val.shru, hn, if_true]
            exact Val.lessdef_refl _
      | shruimm_case2 n1 t1 =>
          obtain ⟨v1, ht1, hx⟩ := eval_shruimm_inv_local
            xi ge sp e m le t1 n1 x (by simpa [hmatch] using ha)
          subst x
          by_cases hadd : CompCert4Lean.Lib.Integers.Int.ltu
              (CompCert4Lean.Lib.Integers.Int.add n n1)
              CompCert4Lean.Lib.Integers.Int.iwordsize = true
          · refine ⟨Val.shru v1
                (.Vint (CompCert4Lean.Lib.Integers.Int.add n n1)), ?_, ?_⟩
            · simp only [hadd, if_true]
              exact eval_expr.eval_Eop le
                (Oshruimm (CompCert4Lean.Lib.Integers.Int.add n n1))
                (Econs t1 Enil) [v1] _
                (eval_exprlist.cons le t1 Enil v1 [] ht1
                  (eval_exprlist.nil le)) rfl
            · exact val_shru_shru_local v1 n1 n hn hadd
          · have haddf : CompCert4Lean.Lib.Integers.Int.ltu
                (CompCert4Lean.Lib.Integers.Int.add n n1)
                CompCert4Lean.Lib.Integers.Int.iwordsize = false :=
              Bool.eq_false_iff.mpr hadd
            refine ⟨Val.shru (Val.shru v1 (.Vint n1)) (.Vint n), ?_,
              Val.lessdef_refl _⟩
            simp only [haddf, Bool.false_eq_true, if_false]
            exact eval_expr.eval_Eop le (Oshruimm n)
              (Econs (Eop (Oshruimm n1) (Econs t1 Enil)) Enil)
              [Val.shru v1 (.Vint n1)] _
              (eval_exprlist.cons le _ Enil _ [] ha
                (eval_exprlist.nil le)) rfl
      | shruimm_default e1 =>
          refine ⟨Val.shru x (.Vint n), ?_, Val.lessdef_refl _⟩
          exact eval_expr.eval_Eop le (Oshruimm n) (Econs a Enil)
            [x] _ (eval_exprlist.cons le a Enil x [] ha
              (eval_exprlist.nil le)) rfl
    · have hnf : CompCert4Lean.Lib.Integers.Int.ltu n
          CompCert4Lean.Lib.Integers.Int.iwordsize = false :=
        Bool.eq_false_iff.mpr hn
      simp only [hnf, Bool.not_false, if_true]
      refine ⟨Val.shru x (.Vint n), ?_, Val.lessdef_refl _⟩
      exact eval_expr.eval_Eop le Oshru
        (Econs a (Econs (Eop (Ointconst n) Enil) Enil))
        [x, .Vint n] _
        (eval_exprlist.cons le a _ x [.Vint n] ha
          (eval_exprlist.cons le (Eop (Ointconst n) Enil) Enil
            (.Vint n) []
            (eval_expr.eval_Eop le (Ointconst n) Enil [] (.Vint n)
              (eval_exprlist.nil le) rfl)
            (eval_exprlist.nil le))) rfl

theorem eval_shru
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_shruStatement := by
  unfold eval_shruStatement binary_constructor_sound
  intro xi ge sp e m le a x b y ha hb
  cases hmatch : shru_match b with
  | shru_case1 n =>
      have hy : y = .Vint n := eval_intconst_value_local
        xi ge sp e m le n y (by simpa [hmatch] using hb)
      subst y
      obtain ⟨v, hv, hd⟩ := eval_shruimm_for_eval_shru_local
        xi ge sp e m n le a x ha
      refine ⟨v, ?_, hd⟩
      simpa [CompCert4Lean.X86.SelectOp.shru, hmatch] using hv
  | shru_default e2 =>
      refine ⟨Val.shru x y, ?_, Val.lessdef_refl _⟩
      simp only [CompCert4Lean.X86.SelectOp.shru, hmatch]
      exact eval_expr.eval_Eop le Oshru (Econs a (Econs b Enil))
        [x, y] _
        (eval_exprlist.cons le a (Econs b Enil) x [y] ha
          (eval_exprlist.cons le b Enil y [] hb
            (eval_exprlist.nil le))) rfl

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Op

theorem eval_negf
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_negfStatement := by
  intro xi ge sp e m le a x h
  refine ⟨Val.negf x, ?_, Val.lessdef_refl _⟩
  exact eval_expr.eval_Eop le Onegf (Econs a Enil) [x] (Val.negf x)
    (eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)) rfl

theorem eval_absf
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_absfStatement := by
  intro xi ge sp e m le a x h
  refine ⟨Val.absf x, ?_, Val.lessdef_refl _⟩
  exact eval_expr.eval_Eop le Oabsf (Econs a Enil) [x] (Val.absf x)
    (eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)) rfl

theorem eval_addf
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_addfStatement := by
  intro xi ge sp e m le a x b y ha hb
  refine ⟨Val.addf x y, ?_, Val.lessdef_refl _⟩
  exact eval_expr.eval_Eop le Oaddf (Econs a (Econs b Enil)) [x, y]
    (Val.addf x y)
    (eval_exprlist.cons le a (Econs b Enil) x [y] ha
      (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))) rfl

theorem eval_subf
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_subfStatement := by
  intro xi ge sp e m le a x b y ha hb
  refine ⟨Val.subf x y, ?_, Val.lessdef_refl _⟩
  exact eval_expr.eval_Eop le Osubf (Econs a (Econs b Enil)) [x, y]
    (Val.subf x y)
    (eval_exprlist.cons le a (Econs b Enil) x [y] ha
      (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))) rfl

end CompCert4Lean.X86.SelectOpproof
