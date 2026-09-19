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

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Op

theorem eval_mulf
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_mulfStatement := by
  intro xi ge sp e m le a x b y ha hb
  refine ⟨Val.mulf x y, ?_, Val.lessdef_refl _⟩
  exact eval_expr.eval_Eop le Omulf (Econs a (Econs b Enil)) [x, y]
    (Val.mulf x y)
    (eval_exprlist.cons le a (Econs b Enil) x [y] ha
      (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))) rfl

theorem eval_negfs
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_negfsStatement := by
  intro xi ge sp e m le a x h
  refine ⟨Val.negfs x, ?_, Val.lessdef_refl _⟩
  exact eval_expr.eval_Eop le Onegfs (Econs a Enil) [x] (Val.negfs x)
    (eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)) rfl

theorem eval_absfs
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_absfsStatement := by
  intro xi ge sp e m le a x h
  refine ⟨Val.absfs x, ?_, Val.lessdef_refl _⟩
  exact eval_expr.eval_Eop le Oabsfs (Econs a Enil) [x] (Val.absfs x)
    (eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)) rfl

theorem eval_addfs
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_addfsStatement := by
  intro xi ge sp e m le a x b y ha hb
  refine ⟨Val.addfs x y, ?_, Val.lessdef_refl _⟩
  exact eval_expr.eval_Eop le Oaddfs (Econs a (Econs b Enil)) [x, y]
    (Val.addfs x y)
    (eval_exprlist.cons le a (Econs b Enil) x [y] ha
      (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))) rfl

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

/-
set_option maxHeartbeats 1000000 in
private theorem eval_compimm_case1_local
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (default : comparison → CCInt → condition)
    (intsem : comparison → CCInt → CCInt → Bool)
    (sem : comparison → val → val → val)
    (hsem_int : ∀ c x y, sem c (.Vint x) (.Vint y) = Val.of_bool (intsem c x y))
    (le : letenv) (c : comparison) (n1 n2 : CCInt) :
    ∀ (x : val),
      eval_expr xi ge sp e m le (Eop (Ointconst n1) Enil) x →
      ∃ v,
        eval_expr xi ge sp e m le (compimm default intsem c
          (Eop (Ointconst n1) Enil) n2) v ∧
        Val.lessdef (sem c x (.Vint n2)) v := by
  intro x hx
  have hx' := eval_intconst_value_local xi ge sp e m le n1 x hx
  subst x
  refine ⟨Val.of_bool (intsem c n1 n2), ?_, ?_⟩
  · simp [CompCert4Lean.X86.SelectOp.compimm]
    apply eval_expr.eval_Eop le
      (Ointconst _) Enil [] _
    · exact eval_exprlist.nil le
    · cases h : intsem c n1 n2 <;> rfl
  · rw [hsem_int]
    exact Val.lessdef_refl _

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

set_option maxHeartbeats 1000000 in
private theorem eval_compimm_case2_local
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (default : comparison → CCInt → condition)
    (intsem : comparison → CCInt → CCInt → Bool)
    (sem : comparison → val → val → val)
    (hsem_undef : ∀ c v, sem c .Vundef v = .Vundef)
    (hsem_eq : ∀ x y, sem .Ceq (.Vint x) (.Vint y) =
      Val.of_bool (CompCert4Lean.Lib.Integers.Int.eq x y))
    (le : letenv) (cond : condition) (el : exprlist) (n2 : CCInt) (x : val) :
    eval_expr xi ge sp e m le (Eop (Ocmp cond) el) x →
      ∃ v,
        eval_expr xi ge sp e m le
          (compimm default intsem .Ceq (Eop (Ocmp cond) el) n2) v ∧
        Val.lessdef (sem .Ceq x (.Vint n2)) v := by
  have h00 : CompCert4Lean.Lib.Integers.Int.eq
      CompCert4Lean.Lib.Integers.Int.zero CompCert4Lean.Lib.Integers.Int.zero = true := by
    rfl
  have h01 : CompCert4Lean.Lib.Integers.Int.eq
      CompCert4Lean.Lib.Integers.Int.zero CompCert4Lean.Lib.Integers.Int.one = false := by
    rfl
  have h10 : CompCert4Lean.Lib.Integers.Int.eq
      CompCert4Lean.Lib.Integers.Int.one CompCert4Lean.Lib.Integers.Int.zero = false := by
    rfl
  have h11 : CompCert4Lean.Lib.Integers.Int.eq
      CompCert4Lean.Lib.Integers.Int.one CompCert4Lean.Lib.Integers.Int.one = true := by
    rfl
  intro hx
  cases hx with
  | eval_Eop le' op al vl v hargs hop =>
      change some (Val.of_optbool (eval_condition cond vl m)) = some x at hop
      have hx' : Val.of_optbool (eval_condition cond vl m) = x :=
        Option.some.inj hop
      subst x
      by_cases hz : n2 = CompCert4Lean.Lib.Integers.Int.zero
      · subst n2
        refine ⟨Val.of_optbool (eval_condition (negate_condition cond) vl m), ?_, ?_⟩
        · simp [CompCert4Lean.X86.SelectOp.compimm]
          apply eval_expr.eval_Eop le (Ocmp (negate_condition cond)) el vl _
          · exact hargs
          · rfl
        · have hneg := eval_negate_condition cond vl m
          rw [hneg]
          cases hc : eval_condition cond vl m with
          | none =>
              change Val.lessdef (sem .Ceq .Vundef _) .Vundef
              rw [hsem_undef]
              exact Val.lessdef_undef _
          | some b =>
              cases b <;>
                simp [Val.of_optbool, Vtrue, Vfalse, hsem_eq, h00, h01, h10, h11,
                  CompCert4Lean.Lib.Integers.Int.eq,
                    CompCert4Lean.Lib.Integers.WordCore.eq] <;>
                  try exact Val.lessdef_refl _
      · by_cases ho : n2 = CompCert4Lean.Lib.Integers.Int.one
        · subst n2
          refine ⟨Val.of_optbool (eval_condition cond vl m), ?_, ?_⟩
          · simp [CompCert4Lean.X86.SelectOp.compimm]
            apply eval_expr.eval_Eop le (Ocmp cond) el vl _
            · exact hargs
            · rfl
          · cases hc : eval_condition cond vl m with
            | none =>
                change Val.lessdef (sem .Ceq .Vundef _) .Vundef
                rw [hsem_undef]
                exact Val.lessdef_undef _
            | some b =>
                cases b <;>
                  simp [Val.of_optbool, Vtrue, Vfalse, hsem_eq, h00, h01, h10, h11,
                    CompCert4Lean.Lib.Integers.Int.eq,
                    CompCert4Lean.Lib.Integers.WordCore.eq] <;>
                  try exact Val.lessdef_refl _
        · have hzero : CompCert4Lean.Lib.Integers.Int.eq_dec n2
              CompCert4Lean.Lib.Integers.Int.zero = .right hz := by
            unfold CompCert4Lean.Lib.Integers.Int.eq_dec
            split
            · next h => exact (hz h).elim
            · rfl
          have hone : CompCert4Lean.Lib.Integers.Int.eq_dec n2
              CompCert4Lean.Lib.Integers.Int.one = .right ho := by
            unfold CompCert4Lean.Lib.Integers.Int.eq_dec
            split
            · next h => exact (ho h).elim
            · rfl
          refine ⟨.Vint CompCert4Lean.Lib.Integers.Int.zero, ?_, ?_⟩
          · have hcm : CompCert4Lean.X86.SelectOp.compimm_match .Ceq
                (Eop (Ocmp cond) el) = .compimm_case2 cond el := by
              rfl
            simp only [CompCert4Lean.X86.SelectOp.compimm, hcm]
            change eval_expr xi ge sp e m le
              (if (match CompCert4Lean.Lib.Integers.Int.eq_dec n2
                  CompCert4Lean.Lib.Integers.Int.zero with
                | .left _ => true
                | .right _ => false) = true then
                Eop (Ocmp (negate_condition cond)) el
              else if (match CompCert4Lean.Lib.Integers.Int.eq_dec n2
                  CompCert4Lean.Lib.Integers.Int.one with
                | .left _ => true
                | .right _ => false) = true then
                Eop (Ocmp cond) el
              else Eop (Ointconst CompCert4Lean.Lib.Integers.Int.zero) Enil)
              (Vint CompCert4Lean.Lib.Integers.Int.zero)
            simp [hzero, hone]
            apply eval_expr.eval_Eop le
              (Ointconst CompCert4Lean.Lib.Integers.Int.zero) Enil [] _
            · exact eval_exprlist.nil le
            · rfl
          · cases hc : eval_condition cond vl m with
            | none =>
                change Val.lessdef (sem .Ceq .Vundef _) _
                rw [hsem_undef]
                exact Val.lessdef_undef _
            | some b =>
                cases b <;>
                  simp [Val.of_optbool, Vtrue, Vfalse, hsem_eq, h00, h01, h10, h11,
                    CompCert4Lean.Lib.Integers.Int.eq,
                    CompCert4Lean.Lib.Integers.WordCore.eq] <;>
                  try exact Val.lessdef_refl _

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Op

-/
theorem eval_subfs
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_subfsStatement := by
  intro xi ge sp e m le a x b y ha hb
  refine ⟨Val.subfs x y, ?_, Val.lessdef_refl _⟩
  exact eval_expr.eval_Eop le Osubfs (Econs a (Econs b Enil)) [x, y]
    (Val.subfs x y)
    (eval_exprlist.cons le a (Econs b Enil) x [y] ha
      (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))) rfl

theorem eval_mulfs
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_mulfsStatement := by
  intro xi ge sp e m le a x b y ha hb
  refine ⟨Val.mulfs x y, ?_, Val.lessdef_refl _⟩
  exact eval_expr.eval_Eop le Omulfs (Econs a (Econs b Enil)) [x, y]
    (Val.mulfs x y)
    (eval_exprlist.cons le a (Econs b Enil) x [y] ha
      (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))) rfl

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

private theorem int_eq_false_of_ne_for_compimm (x y : CCInt) (h : x ≠ y) :
    CompCert4Lean.Lib.Integers.Int.eq x y = false := by
  unfold CompCert4Lean.Lib.Integers.Int.eq
  unfold CompCert4Lean.Lib.Integers.WordCore.eq
  apply decide_eq_false
  intro hxy
  exact h (CompCert4Lean.Lib.Integers.WordCore.ext hxy)

private theorem eval_compimm_for_swap_local
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (default : comparison → CCInt → condition)
    (intsem : comparison → CCInt → CCInt → Bool)
    (sem : comparison → val → val → val)
    (hsem_int : ∀ c x y, sem c (.Vint x) (.Vint y) = Val.of_bool (intsem c x y))
    (hsem_undef : ∀ c v, sem c .Vundef v = .Vundef)
    (hsem_eq : ∀ x y, sem .Ceq (.Vint x) (.Vint y) =
      Val.of_bool (CompCert4Lean.Lib.Integers.Int.eq x y))
    (hsem_ne : ∀ x y, sem .Cne (.Vint x) (.Vint y) =
      Val.of_bool (!(CompCert4Lean.Lib.Integers.Int.eq x y)))
    (hsem_default : ∀ c v n, sem c v (.Vint n) =
      Val.of_optbool (eval_condition (default c n) [v] m))
    (le : letenv) (c : comparison) (a : expr) (n2 : CCInt) (x : val)
    (h : eval_expr xi ge sp e m le a x) :
    ∃ v,
      eval_expr xi ge sp e m le (compimm default intsem c a n2) v ∧
      Val.lessdef (sem c x (.Vint n2)) v := by
  have h00 : CompCert4Lean.Lib.Integers.Int.eq
      CompCert4Lean.Lib.Integers.Int.zero
      CompCert4Lean.Lib.Integers.Int.zero = true := by rfl
  have h01 : CompCert4Lean.Lib.Integers.Int.eq
      CompCert4Lean.Lib.Integers.Int.zero
      CompCert4Lean.Lib.Integers.Int.one = false := by rfl
  have h10 : CompCert4Lean.Lib.Integers.Int.eq
      CompCert4Lean.Lib.Integers.Int.one
      CompCert4Lean.Lib.Integers.Int.zero = false := by rfl
  have h11 : CompCert4Lean.Lib.Integers.Int.eq
      CompCert4Lean.Lib.Integers.Int.one
      CompCert4Lean.Lib.Integers.Int.one = true := by rfl
  cases hcase : compimm_match c a with
  | compimm_case1 c n1 =>
      have hx := eval_intconst_value_local xi ge sp e m le n1 x h
      subst x
      refine ⟨Val.of_bool (intsem c n1 n2), ?_, ?_⟩
      · simp only [compimm, hcase]
        apply eval_expr.eval_Eop le
          (Ointconst (if intsem c n1 n2 then
            CompCert4Lean.Lib.Integers.Int.one
          else CompCert4Lean.Lib.Integers.Int.zero)) Enil [] _
        · exact eval_exprlist.nil le
        · cases intsem c n1 n2 <;> rfl
      · rw [hsem_int]
        exact Val.lessdef_refl _
  | compimm_case2 cond el =>
      cases h with
      | eval_Eop le' op al vl v hargs hop =>
          change some (Val.of_optbool (eval_condition cond vl m)) = some x at hop
          have hx : Val.of_optbool (eval_condition cond vl m) = x :=
            Option.some.inj hop
          subst x
          by_cases hz : n2 = CompCert4Lean.Lib.Integers.Int.zero
          · subst n2
            refine ⟨Val.of_optbool (eval_condition (negate_condition cond) vl m), ?_, ?_⟩
            · simp only [compimm, hcase]
              apply eval_expr.eval_Eop le (Ocmp (negate_condition cond)) el vl _
              · exact hargs
              · rfl
            · rw [eval_negate_condition]
              cases hc : eval_condition cond vl m with
              | none =>
                  change Val.lessdef (sem .Ceq .Vundef _) .Vundef
                  rw [hsem_undef]
                  exact Val.lessdef_undef _
              | some b =>
                  cases b <;>
                    simp [Val.of_optbool, Val.of_bool, Vtrue, Vfalse, hsem_eq,
                      h00, h01, h10, h11] <;>
                    exact Val.lessdef_refl _
          · by_cases ho : n2 = CompCert4Lean.Lib.Integers.Int.one
            · subst n2
              refine ⟨Val.of_optbool (eval_condition cond vl m), ?_, ?_⟩
              · simp only [compimm, hcase]
                apply eval_expr.eval_Eop le (Ocmp cond) el vl _
                · exact hargs
                · rfl
              · cases hc : eval_condition cond vl m with
                | none =>
                    change Val.lessdef (sem .Ceq .Vundef _) .Vundef
                    rw [hsem_undef]
                    exact Val.lessdef_undef _
                | some b =>
                    cases b <;>
                      simp [Val.of_optbool, Val.of_bool, Vtrue, Vfalse, hsem_eq,
                        h00, h01, h10, h11] <;>
                      exact Val.lessdef_refl _
            · have hzero : CompCert4Lean.Lib.Integers.Int.eq_dec n2
                  CompCert4Lean.Lib.Integers.Int.zero = .right hz := by
                unfold CompCert4Lean.Lib.Integers.Int.eq_dec
                split
                · next heq => exact (hz heq).elim
                · rfl
              have hone : CompCert4Lean.Lib.Integers.Int.eq_dec n2
                  CompCert4Lean.Lib.Integers.Int.one = .right ho := by
                unfold CompCert4Lean.Lib.Integers.Int.eq_dec
                split
                · next heq => exact (ho heq).elim
                · rfl
              have heq0 : CompCert4Lean.Lib.Integers.Int.eq
                  CompCert4Lean.Lib.Integers.Int.zero n2 = false :=
                int_eq_false_of_ne_for_compimm _ _ (fun heq => hz heq.symm)
              have heq1 : CompCert4Lean.Lib.Integers.Int.eq
                  CompCert4Lean.Lib.Integers.Int.one n2 = false :=
                int_eq_false_of_ne_for_compimm _ _ (fun heq => ho heq.symm)
              refine ⟨.Vint CompCert4Lean.Lib.Integers.Int.zero, ?_, ?_⟩
              · simp only [compimm, hcase]
                run_tac
                  let goal ← Lean.Elab.Tactic.getMainGoal
                  let target ← goal.getType
                  let some e := target.find? fun e =>
                    e.isConst && e.constName!.getString! == "intEqDecBool"
                    | throwError "private equality decider not found"
                  let .defnInfo info ← Lean.getConstInfo e.constName!
                    | throwError "private equality decider is not a definition"
                  let target' := target.replace fun e =>
                    if e.isConstOf info.name then some info.value else none
                  let goal' ← Lean.Meta.withTransparency .all <|
                    goal.replaceTargetDefEq target'
                  Lean.Elab.Tactic.replaceMainGoal [goal']
                simp [hzero, hone]
                exact eval_expr.eval_Eop le
                  (Ointconst CompCert4Lean.Lib.Integers.Int.zero) Enil [] _
                  (eval_exprlist.nil le) rfl
              · cases hc : eval_condition cond vl m with
                | none =>
                    change Val.lessdef (sem .Ceq .Vundef _) _
                    rw [hsem_undef]
                    exact Val.lessdef_undef _
                | some b =>
                    cases b <;>
                      simp [Val.of_optbool, Val.of_bool, Vtrue, Vfalse, hsem_eq,
                        heq0, heq1] <;>
                      exact Val.lessdef_refl _
  | compimm_case3 cond el =>
      cases h with
      | eval_Eop le' op al vl v hargs hop =>
          change some (Val.of_optbool (eval_condition cond vl m)) = some x at hop
          have hx : Val.of_optbool (eval_condition cond vl m) = x :=
            Option.some.inj hop
          subst x
          by_cases hz : n2 = CompCert4Lean.Lib.Integers.Int.zero
          · subst n2
            refine ⟨Val.of_optbool (eval_condition cond vl m), ?_, ?_⟩
            · simp only [compimm, hcase]
              apply eval_expr.eval_Eop le (Ocmp cond) el vl _
              · exact hargs
              · rfl
            · cases hc : eval_condition cond vl m with
              | none =>
                  change Val.lessdef (sem .Cne .Vundef _) .Vundef
                  rw [hsem_undef]
                  exact Val.lessdef_undef _
              | some b =>
                  cases b <;>
                    simp [Val.of_optbool, Val.of_bool, Vtrue, Vfalse, hsem_ne,
                      h00, h01, h10, h11] <;>
                    exact Val.lessdef_refl _
          · by_cases ho : n2 = CompCert4Lean.Lib.Integers.Int.one
            · subst n2
              refine ⟨Val.of_optbool (eval_condition (negate_condition cond) vl m), ?_, ?_⟩
              · simp only [compimm, hcase]
                apply eval_expr.eval_Eop le (Ocmp (negate_condition cond)) el vl _
                · exact hargs
                · rfl
              · rw [eval_negate_condition]
                cases hc : eval_condition cond vl m with
                | none =>
                    change Val.lessdef (sem .Cne .Vundef _) .Vundef
                    rw [hsem_undef]
                    exact Val.lessdef_undef _
                | some b =>
                    cases b <;>
                      simp [Val.of_optbool, Val.of_bool, Vtrue, Vfalse, hsem_ne,
                        h00, h01, h10, h11] <;>
                      exact Val.lessdef_refl _
            · have hzero : CompCert4Lean.Lib.Integers.Int.eq_dec n2
                  CompCert4Lean.Lib.Integers.Int.zero = .right hz := by
                unfold CompCert4Lean.Lib.Integers.Int.eq_dec
                split
                · next heq => exact (hz heq).elim
                · rfl
              have hone : CompCert4Lean.Lib.Integers.Int.eq_dec n2
                  CompCert4Lean.Lib.Integers.Int.one = .right ho := by
                unfold CompCert4Lean.Lib.Integers.Int.eq_dec
                split
                · next heq => exact (ho heq).elim
                · rfl
              have heq0 : CompCert4Lean.Lib.Integers.Int.eq
                  CompCert4Lean.Lib.Integers.Int.zero n2 = false :=
                int_eq_false_of_ne_for_compimm _ _ (fun heq => hz heq.symm)
              have heq1 : CompCert4Lean.Lib.Integers.Int.eq
                  CompCert4Lean.Lib.Integers.Int.one n2 = false :=
                int_eq_false_of_ne_for_compimm _ _ (fun heq => ho heq.symm)
              refine ⟨.Vint CompCert4Lean.Lib.Integers.Int.one, ?_, ?_⟩
              · simp only [compimm, hcase]
                run_tac
                  let goal ← Lean.Elab.Tactic.getMainGoal
                  let target ← goal.getType
                  let some e := target.find? fun e =>
                    e.isConst && e.constName!.getString! == "intEqDecBool"
                    | throwError "private equality decider not found"
                  let .defnInfo info ← Lean.getConstInfo e.constName!
                    | throwError "private equality decider is not a definition"
                  let target' := target.replace fun e =>
                    if e.isConstOf info.name then some info.value else none
                  let goal' ← Lean.Meta.withTransparency .all <|
                    goal.replaceTargetDefEq target'
                  Lean.Elab.Tactic.replaceMainGoal [goal']
                simp [hzero, hone]
                exact eval_expr.eval_Eop le
                  (Ointconst CompCert4Lean.Lib.Integers.Int.one) Enil [] _
                  (eval_exprlist.nil le) rfl
              · cases hc : eval_condition cond vl m with
                | none =>
                    change Val.lessdef (sem .Cne .Vundef _) _
                    rw [hsem_undef]
                    exact Val.lessdef_undef _
                | some b =>
                    cases b <;>
                      simp [Val.of_optbool, Val.of_bool, Vtrue, Vfalse, hsem_ne,
                        heq0, heq1] <;>
                      exact Val.lessdef_refl _
  | compimm_case4 n1 t1 =>
      cases h with
      | eval_Eop le' op al vl v hargs hop =>
          cases hargs with
          | cons _ a' al' v1 vl' hhead htail =>
              cases htail with
              | nil _ =>
                  change some (Val.and v1 (.Vint n1)) = some x at hop
                  have hx : Val.and v1 (.Vint n1) = x := Option.some.inj hop
                  subst x
                  by_cases hz : n2 = CompCert4Lean.Lib.Integers.Int.zero
                  · subst n2
                    refine ⟨Val.of_optbool (eval_condition (.Cmaskzero n1) [v1] m), ?_, ?_⟩
                    · simp only [compimm, hcase]
                      apply eval_expr.eval_Eop le (Ocmp (.Cmaskzero n1))
                        (Econs t1 Enil) [v1] _
                      · exact eval_exprlist.cons le t1 Enil v1 [] hhead
                          (eval_exprlist.nil le)
                      · rfl
                    · cases v1 with
                      | Vint i =>
                          change Val.lessdef
                            (sem .Ceq (.Vint (CompCert4Lean.Lib.Integers.Int.and i n1))
                              (.Vint CompCert4Lean.Lib.Integers.Int.zero)) _
                          rw [hsem_eq]
                          cases hb : CompCert4Lean.Lib.Integers.Int.eq
                              (CompCert4Lean.Lib.Integers.Int.and i n1)
                              CompCert4Lean.Lib.Integers.Int.zero <;>
                            simp [eval_condition, Val.maskzero_bool, hb,
                              Val.of_optbool, Val.of_bool, Vtrue, Vfalse] <;>
                            exact Val.lessdef_refl _
                      | _ =>
                          change Val.lessdef (sem .Ceq .Vundef _) .Vundef
                          rw [hsem_undef]
                          exact Val.lessdef_undef _
                  · have hzero : CompCert4Lean.Lib.Integers.Int.eq_dec n2
                        CompCert4Lean.Lib.Integers.Int.zero = .right hz := by
                      unfold CompCert4Lean.Lib.Integers.Int.eq_dec
                      split
                      · next heq => exact (hz heq).elim
                      · rfl
                    refine ⟨Val.of_optbool
                      (eval_condition (default .Ceq n2)
                        [Val.and v1 (.Vint n1)] m), ?_, ?_⟩
                    · simp only [compimm, hcase]
                      run_tac
                        let goal ← Lean.Elab.Tactic.getMainGoal
                        let target ← goal.getType
                        let some e := target.find? fun e =>
                          e.isConst && e.constName!.getString! == "intEqDecBool"
                          | throwError "private equality decider not found"
                        let .defnInfo info ← Lean.getConstInfo e.constName!
                          | throwError "private equality decider is not a definition"
                        let target' := target.replace fun e =>
                          if e.isConstOf info.name then some info.value else none
                        let goal' ← Lean.Meta.withTransparency .all <|
                          goal.replaceTargetDefEq target'
                        Lean.Elab.Tactic.replaceMainGoal [goal']
                      simp [hzero]
                      apply eval_expr.eval_Eop le (Ocmp (default .Ceq n2))
                        (Econs (Eop (Oandimm n1) (Econs t1 Enil)) Enil)
                        [Val.and v1 (.Vint n1)] _
                      · apply eval_exprlist.cons le _ Enil _ []
                        · apply eval_expr.eval_Eop le (Oandimm n1)
                            (Econs t1 Enil) [v1] _
                          · exact eval_exprlist.cons le t1 Enil v1 [] hhead
                              (eval_exprlist.nil le)
                          · rfl
                        · exact eval_exprlist.nil le
                      · rfl
                    · rw [hsem_default]
                      exact Val.lessdef_refl _
  | compimm_case5 n1 t1 =>
      cases h with
      | eval_Eop le' op al vl v hargs hop =>
          cases hargs with
          | cons _ a' al' v1 vl' hhead htail =>
              cases htail with
              | nil _ =>
                  change some (Val.and v1 (.Vint n1)) = some x at hop
                  have hx : Val.and v1 (.Vint n1) = x := Option.some.inj hop
                  subst x
                  by_cases hz : n2 = CompCert4Lean.Lib.Integers.Int.zero
                  · subst n2
                    refine ⟨Val.of_optbool (eval_condition (.Cmasknotzero n1) [v1] m), ?_, ?_⟩
                    · simp only [compimm, hcase]
                      apply eval_expr.eval_Eop le (Ocmp (.Cmasknotzero n1))
                        (Econs t1 Enil) [v1] _
                      · exact eval_exprlist.cons le t1 Enil v1 [] hhead
                          (eval_exprlist.nil le)
                      · rfl
                    · cases v1 with
                      | Vint i =>
                          change Val.lessdef
                            (sem .Cne (.Vint (CompCert4Lean.Lib.Integers.Int.and i n1))
                              (.Vint CompCert4Lean.Lib.Integers.Int.zero)) _
                          rw [hsem_ne]
                          cases hb : CompCert4Lean.Lib.Integers.Int.eq
                              (CompCert4Lean.Lib.Integers.Int.and i n1)
                              CompCert4Lean.Lib.Integers.Int.zero <;>
                            simp [eval_condition, Val.maskzero_bool, hb,
                              Val.of_optbool, Val.of_bool, Vtrue, Vfalse] <;>
                            exact Val.lessdef_refl _
                      | _ =>
                          change Val.lessdef (sem .Cne .Vundef _) .Vundef
                          rw [hsem_undef]
                          exact Val.lessdef_undef _
                  · have hzero : CompCert4Lean.Lib.Integers.Int.eq_dec n2
                        CompCert4Lean.Lib.Integers.Int.zero = .right hz := by
                      unfold CompCert4Lean.Lib.Integers.Int.eq_dec
                      split
                      · next heq => exact (hz heq).elim
                      · rfl
                    refine ⟨Val.of_optbool
                      (eval_condition (default .Cne n2)
                        [Val.and v1 (.Vint n1)] m), ?_, ?_⟩
                    · simp only [compimm, hcase]
                      run_tac
                        let goal ← Lean.Elab.Tactic.getMainGoal
                        let target ← goal.getType
                        let some e := target.find? fun e =>
                          e.isConst && e.constName!.getString! == "intEqDecBool"
                          | throwError "private equality decider not found"
                        let .defnInfo info ← Lean.getConstInfo e.constName!
                          | throwError "private equality decider is not a definition"
                        let target' := target.replace fun e =>
                          if e.isConstOf info.name then some info.value else none
                        let goal' ← Lean.Meta.withTransparency .all <|
                          goal.replaceTargetDefEq target'
                        Lean.Elab.Tactic.replaceMainGoal [goal']
                      simp [hzero]
                      apply eval_expr.eval_Eop le (Ocmp (default .Cne n2))
                        (Econs (Eop (Oandimm n1) (Econs t1 Enil)) Enil)
                        [Val.and v1 (.Vint n1)] _
                      · apply eval_exprlist.cons le _ Enil _ []
                        · apply eval_expr.eval_Eop le (Oandimm n1)
                            (Econs t1 Enil) [v1] _
                          · exact eval_exprlist.cons le t1 Enil v1 [] hhead
                              (eval_exprlist.nil le)
                          · rfl
                        · exact eval_exprlist.nil le
                      · rfl
                    · rw [hsem_default]
                      exact Val.lessdef_refl _
  | compimm_default c a =>
      refine ⟨Val.of_optbool (eval_condition (default c n2) [x] m), ?_, ?_⟩
      · simp only [compimm, hcase]
        apply eval_expr.eval_Eop le (Ocmp (default c n2)) (Econs a Enil) [x] _
        · exact eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)
        · rfl
      · rw [hsem_default]
        exact Val.lessdef_refl _

theorem eval_compimm_swap
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_compimm_swapStatement := by
  intro xi ge sp e m default intsem sem hsem_int hsem_undef hsem_eq hsem_ne
    hsem_default hsem_swap le c a n2 x h
  have hresult := eval_compimm_for_swap_local xi ge sp e m default intsem sem
    hsem_int hsem_undef hsem_eq hsem_ne hsem_default le
      (CompCert4Lean.Lib.Integers.swap_comparison c) a n2 x h
  rcases hresult with ⟨v, hev, hless⟩
  refine ⟨v, hev, ?_⟩
  rw [hsem_swap] at hless
  exact hless

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

private theorem eval_comp_swap_cmp_bool (c : comparison) (x y : val) :
    Val.cmp_bool (swap_comparison c) x y = Val.cmp_bool c y x := by
  cases c <;> cases x <;> cases y <;>
    simp [Val.cmp_bool, swap_comparison, Int.cmp, WordCore.cmp,
      WordCore.eq, eq_comm]

theorem eval_comp
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_compStatement := by
  unfold eval_compStatement binary_constructor_sound
  intro xi ge sp e m c le a x b y ha hb
  cases hmatch : comp_match a b with
  | comp_case1 n1 t2 =>
      have hx : x = .Vint n1 := eval_intconst_value_local xi ge sp e m le n1 x
        (by simpa [hmatch] using ha)
      subst x
      have hsem_int : ∀ c x y, Val.cmp c (.Vint x) (.Vint y) =
          Val.of_bool (CompCert4Lean.Lib.Integers.Int.cmp c x y) := by
        intro c x y
        cases h : CompCert4Lean.Lib.Integers.Int.cmp c x y <;>
          simp [Val.cmp, Val.cmp_bool, Val.of_optbool, Val.of_bool,
            Vtrue, Vfalse, h]
      have hsem_undef : ∀ c v, Val.cmp c .Vundef v = .Vundef := by
        intro c v
        simp [Val.cmp, Val.cmp_bool, Val.of_optbool]
      have hsem_eq : ∀ x y, Val.cmp .Ceq (.Vint x) (.Vint y) =
          Val.of_bool (Int.eq x y) := by
        intro x y
        simpa [CompCert4Lean.Lib.Integers.Int.cmp, WordCore.cmp,
          CompCert4Lean.Lib.Integers.Int.eq, WordCore.eq] using
          (hsem_int .Ceq x y)
      have hsem_ne : ∀ x y, Val.cmp .Cne (.Vint x) (.Vint y) =
          Val.of_bool (!(Int.eq x y)) := by
        intro x y
        simpa [CompCert4Lean.Lib.Integers.Int.cmp, WordCore.cmp,
          CompCert4Lean.Lib.Integers.Int.eq, WordCore.eq] using
          (hsem_int .Cne x y)
      have hsem_default : ∀ c v n, Val.cmp c v (.Vint n) =
          Val.of_optbool (eval_condition (Ccompimm c n) [v] m) := by
        intro c v n
        simp [Val.cmp, Val.cmp_bool, Val.of_optbool, eval_condition]
      have hsem_swap : ∀ c x y, Val.cmp (swap_comparison c) x y =
          Val.cmp c y x := by
        intro c x y
        simp [Val.cmp, eval_comp_swap_cmp_bool]
      obtain ⟨v, hv, hd⟩ := eval_compimm_swap xi ge sp e m Ccompimm
        CompCert4Lean.Lib.Integers.Int.cmp Val.cmp hsem_int hsem_undef
        hsem_eq hsem_ne hsem_default hsem_swap le c b n1 y hb
      refine ⟨v, ?_, ?_⟩
      · simpa [comp, hmatch] using hv
      · exact hd
  | comp_case2 t1 n2 =>
      have hy : y = .Vint n2 := eval_intconst_value_local xi ge sp e m le n2 y
        (by simpa [hmatch] using hb)
      subst y
      have hsem_int : ∀ c x y, Val.cmp c (.Vint x) (.Vint y) =
          Val.of_bool (CompCert4Lean.Lib.Integers.Int.cmp c x y) := by
        intro c x y
        cases h : CompCert4Lean.Lib.Integers.Int.cmp c x y <;>
          simp [Val.cmp, Val.cmp_bool, Val.of_optbool, Val.of_bool,
            Vtrue, Vfalse, h]
      have hsem_undef : ∀ c v, Val.cmp c .Vundef v = .Vundef := by
        intro c v
        simp [Val.cmp, Val.cmp_bool, Val.of_optbool]
      have hsem_eq : ∀ x y, Val.cmp .Ceq (.Vint x) (.Vint y) =
          Val.of_bool (Int.eq x y) := by
        intro x y
        simpa [CompCert4Lean.Lib.Integers.Int.cmp, WordCore.cmp,
          CompCert4Lean.Lib.Integers.Int.eq, WordCore.eq] using
          (hsem_int .Ceq x y)
      have hsem_ne : ∀ x y, Val.cmp .Cne (.Vint x) (.Vint y) =
          Val.of_bool (!(Int.eq x y)) := by
        intro x y
        simpa [CompCert4Lean.Lib.Integers.Int.cmp, WordCore.cmp,
          CompCert4Lean.Lib.Integers.Int.eq, WordCore.eq] using
          (hsem_int .Cne x y)
      have hsem_default : ∀ c v n, Val.cmp c v (.Vint n) =
          Val.of_optbool (eval_condition (Ccompimm c n) [v] m) := by
        intro c v n
        simp [Val.cmp, Val.cmp_bool, Val.of_optbool, eval_condition]
      obtain ⟨v, hv, hd⟩ := eval_compimm_for_swap_local xi ge sp e m
        Ccompimm CompCert4Lean.Lib.Integers.Int.cmp Val.cmp hsem_int hsem_undef
        hsem_eq hsem_ne hsem_default le c a n2 x ha
      refine ⟨v, ?_, ?_⟩
      · simpa [comp, hmatch] using hv
      · exact hd
  | comp_default e1 e2 =>
      refine ⟨Val.cmp c x y, ?_, Val.lessdef_refl _⟩
      simp only [comp, hmatch]
      apply eval_expr.eval_Eop le (Ocmp (Ccomp c))
        (Econs a (Econs b Enil)) [x, y] (Val.cmp c x y)
      · exact eval_exprlist.cons le a (Econs b Enil) x [y] ha
          (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))
      · rfl

end CompCert4Lean.X86.SelectOpproof
namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

private theorem eval_compu_swap_cmpu
    (valid_ptr : block → CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z → Bool)
    (c : comparison) (x y : val) :
    Val.cmpu valid_ptr (swap_comparison c) x y =
      Val.cmpu valid_ptr c y x := by
  cases c <;> cases x <;> cases y <;>
    simp [Val.cmpu, Val.cmpu_bool, Val.cmp_different_blocks,
      swap_comparison, CompCert4Lean.Lib.Integers.Int.cmpu,
      CompCert4Lean.Lib.Integers.Int64.cmpu,
      CompCert4Lean.Lib.Integers.Ptrofs.cmpu,
      CompCert4Lean.Lib.Integers.WordCore.cmpu,
      CompCert4Lean.Lib.Integers.WordCore.eq, eq_comm,
      CompCert4Lean.X86_64.Archi.ptr64]

theorem eval_compu
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_compuStatement := by
  unfold eval_compuStatement binary_constructor_sound
  intro xi ge sp e m c le a x b y ha hb
  cases hmatch : compu_match a b with
  | compu_case1 n1 t2 =>
      have hx : x = .Vint n1 := eval_intconst_value_local xi ge sp e m le n1 x
        (by simpa [hmatch] using ha)
      subst x
      have hsem_int : ∀ c x y, Val.cmpu (Mem.valid_pointer m) c (.Vint x) (.Vint y) =
          Val.of_bool (CompCert4Lean.Lib.Integers.Int.cmpu c x y) := by
        intro c x y
        cases h : CompCert4Lean.Lib.Integers.Int.cmpu c x y <;>
          simp [Val.cmpu, Val.cmpu_bool, Val.of_optbool, Val.of_bool,
            Vtrue, Vfalse, h]
      have hsem_undef : ∀ c v, Val.cmpu (Mem.valid_pointer m) c .Vundef v = .Vundef := by
        intro c v
        simp [Val.cmpu, Val.cmpu_bool, Val.of_optbool]
      have hsem_eq : ∀ x y, Val.cmpu (Mem.valid_pointer m) .Ceq (.Vint x) (.Vint y) =
          Val.of_bool (Int.eq x y) := by
        intro x y
        simpa [CompCert4Lean.Lib.Integers.Int.cmpu, WordCore.cmpu,
          CompCert4Lean.Lib.Integers.Int.eq, WordCore.eq] using
          (hsem_int .Ceq x y)
      have hsem_ne : ∀ x y, Val.cmpu (Mem.valid_pointer m) .Cne (.Vint x) (.Vint y) =
          Val.of_bool (!(Int.eq x y)) := by
        intro x y
        simpa [CompCert4Lean.Lib.Integers.Int.cmpu, WordCore.cmpu,
          CompCert4Lean.Lib.Integers.Int.eq, WordCore.eq] using
          (hsem_int .Cne x y)
      have hsem_default : ∀ c v n,
          Val.cmpu (Mem.valid_pointer m) c v (.Vint n) =
            Val.of_optbool (eval_condition (Ccompuimm c n) [v] m) := by
        intro c v n
        simp [Val.cmpu, Val.cmpu_bool, Val.of_optbool, eval_condition]
      have hsem_swap : ∀ c x y,
          Val.cmpu (Mem.valid_pointer m) (swap_comparison c) x y =
            Val.cmpu (Mem.valid_pointer m) c y x := by
        intro c x y
        exact eval_compu_swap_cmpu (Mem.valid_pointer m) c x y
      obtain ⟨v, hv, hd⟩ := eval_compimm_swap xi ge sp e m Ccompuimm
        CompCert4Lean.Lib.Integers.Int.cmpu (Val.cmpu (Mem.valid_pointer m))
        hsem_int hsem_undef hsem_eq hsem_ne hsem_default hsem_swap le c b n1 y hb
      refine ⟨v, ?_, ?_⟩
      · simpa [compu, hmatch] using hv
      · exact hd
  | compu_case2 t1 n2 =>
      have hy : y = .Vint n2 := eval_intconst_value_local xi ge sp e m le n2 y
        (by simpa [hmatch] using hb)
      subst y
      have hsem_int : ∀ c x y, Val.cmpu (Mem.valid_pointer m) c (.Vint x) (.Vint y) =
          Val.of_bool (CompCert4Lean.Lib.Integers.Int.cmpu c x y) := by
        intro c x y
        cases h : CompCert4Lean.Lib.Integers.Int.cmpu c x y <;>
          simp [Val.cmpu, Val.cmpu_bool, Val.of_optbool, Val.of_bool,
            Vtrue, Vfalse, h]
      have hsem_undef : ∀ c v, Val.cmpu (Mem.valid_pointer m) c .Vundef v = .Vundef := by
        intro c v
        simp [Val.cmpu, Val.cmpu_bool, Val.of_optbool]
      have hsem_eq : ∀ x y, Val.cmpu (Mem.valid_pointer m) .Ceq (.Vint x) (.Vint y) =
          Val.of_bool (Int.eq x y) := by
        intro x y
        simpa [CompCert4Lean.Lib.Integers.Int.cmpu, WordCore.cmpu,
          CompCert4Lean.Lib.Integers.Int.eq, WordCore.eq] using
          (hsem_int .Ceq x y)
      have hsem_ne : ∀ x y, Val.cmpu (Mem.valid_pointer m) .Cne (.Vint x) (.Vint y) =
          Val.of_bool (!(Int.eq x y)) := by
        intro x y
        simpa [CompCert4Lean.Lib.Integers.Int.cmpu, WordCore.cmpu,
          CompCert4Lean.Lib.Integers.Int.eq, WordCore.eq] using
          (hsem_int .Cne x y)
      have hsem_default : ∀ c v n,
          Val.cmpu (Mem.valid_pointer m) c v (.Vint n) =
            Val.of_optbool (eval_condition (Ccompuimm c n) [v] m) := by
        intro c v n
        simp [Val.cmpu, Val.cmpu_bool, Val.of_optbool, eval_condition]
      obtain ⟨v, hv, hd⟩ := eval_compimm_for_swap_local xi ge sp e m
        Ccompuimm CompCert4Lean.Lib.Integers.Int.cmpu
        (Val.cmpu (Mem.valid_pointer m)) hsem_int hsem_undef hsem_eq hsem_ne
        hsem_default le c a n2 x ha
      refine ⟨v, ?_, ?_⟩
      · simpa [compu, hmatch] using hv
      · exact hd
  | compu_default e1 e2 =>
      refine ⟨Val.cmpu (Mem.valid_pointer m) c x y, ?_, Val.lessdef_refl _⟩
      simp only [compu, hmatch]
      apply eval_expr.eval_Eop le (Ocmp (Ccompu c))
        (Econs a (Econs b Enil)) [x, y] (Val.cmpu (Mem.valid_pointer m) c x y)
      · exact eval_exprlist.cons le a (Econs b Enil) x [y] ha
          (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))
      · rfl

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

theorem eval_compf
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_compfStatement := by
  intro xi ge sp e m c le a x b y ha hb
  refine ⟨Val.cmpf c x y, ?_, Val.lessdef_refl _⟩
  exact eval_expr.eval_Eop le (Ocmp (Ccompf c)) (Econs a (Econs b Enil)) [x, y]
    (Val.cmpf c x y)
    (eval_exprlist.cons le a (Econs b Enil) x [y] ha
      (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))) rfl

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Memory
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

theorem eval_cast8signed
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_cast8signedStatement := by
  intro xi ge sp e m le a x h
  cases hcase : cast8signed_match a with
  | cast8signed_case1 n =>
      have hx : x = .Vint n := eval_intconst_value_local xi ge sp e m le n x
        (by simpa [hcase] using h)
      subst x
      refine ⟨.Vint (CompCert4Lean.Lib.Integers.Int.sign_ext z8 n), ?_, ?_⟩
      · exact eval_expr.eval_Eop le
          (Ointconst (CompCert4Lean.Lib.Integers.Int.sign_ext z8 n)) Enil [] _
          (eval_exprlist.nil le) rfl
      · exact Val.lessdef_refl _
  | cast8signed_default e1 =>
      refine ⟨Val.sign_ext z8 x, ?_, Val.lessdef_refl _⟩
      simp only [cast8signed, hcase]
      apply eval_expr.eval_Eop le Ocast8signed (Econs a Enil) [x]
        (Val.sign_ext z8 x)
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

private theorem val_zero_ext_and_mask8_local (v : val)
    (n : CompCert4Lean.Lib.Integers.int) :
    Val.zero_ext z8 (Val.and v (.Vint n)) =
      Val.and v (.Vint (CompCert4Lean.Lib.Integers.Int.and
        (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 255)) n)) := by
  cases v with
  | Vundef => rfl
  | Vfloat _ => rfl
  | Vsingle _ => rfl
  | Vlong _ => rfl
  | Vptr _ _ => rfl
  | Vint p =>
      change CompCert4Lean.Common.Values.val.Vint
          (CompCert4Lean.Lib.Integers.Int.zero_ext z8
            (CompCert4Lean.Lib.Integers.Int.and p n)) =
        CompCert4Lean.Common.Values.val.Vint
          (CompCert4Lean.Lib.Integers.Int.and p
            (CompCert4Lean.Lib.Integers.Int.and
              (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 255)) n))
      congr 1
      rw [CompCert4Lean.Lib.Integers.Int.zero_ext_and_proof
        z8 (CompCert4Lean.Lib.Integers.Int.and p n)
        (by change (0 : Int) ≤ 8; omega)]
      calc
        CompCert4Lean.Lib.Integers.Int.and
              (CompCert4Lean.Lib.Integers.Int.and p n)
              (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 255)) =
            CompCert4Lean.Lib.Integers.Int.and p
              (CompCert4Lean.Lib.Integers.Int.and n
                (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 255))) := by
                  exact CompCert4Lean.Lib.Integers.Int.and_assoc_proof p n
                    (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 255))
        _ = CompCert4Lean.Lib.Integers.Int.and p
              (CompCert4Lean.Lib.Integers.Int.and
                (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 255)) n) := by
                  exact congrArg (CompCert4Lean.Lib.Integers.Int.and p)
                    (CompCert4Lean.Lib.Integers.Int.and_commut_proof n
                      (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 255)))

theorem eval_cast8unsigned
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_cast8unsignedStatement := by
  intro xi ge sp e m le a x h
  cases hcase : cast8unsigned_match a with
  | cast8unsigned_case1 n =>
      have hx : x = .Vint n := eval_intconst_value_local xi ge sp e m le n x
        (by simpa [hcase] using h)
      subst x
      refine ⟨.Vint (CompCert4Lean.Lib.Integers.Int.zero_ext z8 n), ?_, ?_⟩
      · exact eval_expr.eval_Eop le
          (Ointconst (CompCert4Lean.Lib.Integers.Int.zero_ext z8 n)) Enil [] _
          (eval_exprlist.nil le) rfl
      · exact Val.lessdef_refl _
  | cast8unsigned_case2 n t =>
      cases h with
      | eval_Eop le' op al vl v hargs hop =>
          cases hargs with
          | cons _ a' al' v1 vl' hhead htail =>
              cases htail with
              | nil _ =>
                  change some (Val.and v1 (.Vint n)) = some x at hop
                  cases hop
                  let mask := CompCert4Lean.Lib.Integers.Int.and
                    (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 255)) n
                  obtain ⟨v, hv, hd⟩ := eval_andimm xi ge sp e m mask le t v1
                    (by simpa [hcase] using hhead)
                  refine ⟨v, ?_, ?_⟩
                  · simpa [cast8unsigned, hcase, mask] using hv
                  · rw [val_zero_ext_and_mask8_local v1 n]
                    exact hd
  | cast8unsigned_default e1 =>
      refine ⟨Val.zero_ext z8 x, ?_, Val.lessdef_refl _⟩
      simp only [cast8unsigned, hcase]
      apply eval_expr.eval_Eop le Ocast8unsigned (Econs a Enil) [x]
        (Val.zero_ext z8 x)
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

theorem eval_cast16signed
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_cast16signedStatement := by
  intro xi ge sp e m le a x h
  cases hcase : cast16signed_match a with
  | cast16signed_case1 n =>
      have hx : x = .Vint n := eval_intconst_value_local xi ge sp e m le n x
        (by simpa [hcase] using h)
      subst x
      refine ⟨.Vint (CompCert4Lean.Lib.Integers.Int.sign_ext z16 n), ?_, ?_⟩
      · exact eval_expr.eval_Eop le
          (Ointconst (CompCert4Lean.Lib.Integers.Int.sign_ext z16 n)) Enil [] _
          (eval_exprlist.nil le) rfl
      · exact Val.lessdef_refl _
  | cast16signed_default e1 =>
      refine ⟨Val.sign_ext z16 x, ?_, Val.lessdef_refl _⟩
      simp only [cast16signed, hcase]
      apply eval_expr.eval_Eop le Ocast16signed (Econs a Enil) [x]
        (Val.sign_ext z16 x)
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

private theorem val_zero_ext_and_mask16_local (v : val)
    (n : CompCert4Lean.Lib.Integers.int) :
    Val.zero_ext z16 (Val.and v (.Vint n)) =
      Val.and v (.Vint (CompCert4Lean.Lib.Integers.Int.and
        (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 65535)) n)) := by
  cases v with
  | Vundef => rfl
  | Vfloat _ => rfl
  | Vsingle _ => rfl
  | Vlong _ => rfl
  | Vptr _ _ => rfl
  | Vint p =>
      change CompCert4Lean.Common.Values.val.Vint
          (CompCert4Lean.Lib.Integers.Int.zero_ext z16
            (CompCert4Lean.Lib.Integers.Int.and p n)) =
        CompCert4Lean.Common.Values.val.Vint
          (CompCert4Lean.Lib.Integers.Int.and p
            (CompCert4Lean.Lib.Integers.Int.and
              (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 65535)) n))
      congr 1
      rw [CompCert4Lean.Lib.Integers.Int.zero_ext_and_proof
        z16 (CompCert4Lean.Lib.Integers.Int.and p n)
        (by change (0 : Int) ≤ 16; omega)]
      calc
        CompCert4Lean.Lib.Integers.Int.and
              (CompCert4Lean.Lib.Integers.Int.and p n)
              (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 65535)) =
            CompCert4Lean.Lib.Integers.Int.and p
              (CompCert4Lean.Lib.Integers.Int.and n
                (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 65535))) := by
                  exact CompCert4Lean.Lib.Integers.Int.and_assoc_proof p n
                    (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 65535))
        _ = CompCert4Lean.Lib.Integers.Int.and p
              (CompCert4Lean.Lib.Integers.Int.and
                (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 65535)) n) := by
                  exact congrArg (CompCert4Lean.Lib.Integers.Int.and p)
                    (CompCert4Lean.Lib.Integers.Int.and_commut_proof n
                      (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 65535)))

theorem eval_cast16unsigned
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_cast16unsignedStatement := by
  intro xi ge sp e m le a x h
  cases hcase : cast16unsigned_match a with
  | cast16unsigned_case1 n =>
      have hx : x = .Vint n := eval_intconst_value_local xi ge sp e m le n x
        (by simpa [hcase] using h)
      subst x
      refine ⟨.Vint (CompCert4Lean.Lib.Integers.Int.zero_ext z16 n), ?_, ?_⟩
      · exact eval_expr.eval_Eop le
          (Ointconst (CompCert4Lean.Lib.Integers.Int.zero_ext z16 n)) Enil [] _
          (eval_exprlist.nil le) rfl
      · exact Val.lessdef_refl _
  | cast16unsigned_case2 n t =>
      cases h with
      | eval_Eop le' op al vl v hargs hop =>
          cases hargs with
          | cons _ a' al' v1 vl' hhead htail =>
              cases htail with
              | nil _ =>
                  change some (Val.and v1 (.Vint n)) = some x at hop
                  cases hop
                  let mask := CompCert4Lean.Lib.Integers.Int.and
                    (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 65535)) n
                  obtain ⟨v, hv, hd⟩ := eval_andimm xi ge sp e m mask le t v1
                    (by simpa [hcase] using hhead)
                  refine ⟨v, ?_, ?_⟩
                  · simpa [cast16unsigned, hcase, mask] using hv
                  · rw [val_zero_ext_and_mask16_local v1 n]
                    exact hd
  | cast16unsigned_default e1 =>
      refine ⟨Val.zero_ext z16 x, ?_, Val.lessdef_refl _⟩
      simp only [cast16unsigned, hcase]
      apply eval_expr.eval_Eop le Ocast16unsigned (Econs a Enil) [x]
        (Val.zero_ext z16 x)
      · exact eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)
      · rfl

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Memory
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

theorem eval_singleoffloat
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_singleoffloatStatement := by
  intro xi ge sp e m le a x h
  refine ⟨Val.singleoffloat x, ?_, Val.lessdef_refl _⟩
  apply eval_expr.eval_Eop le Osingleoffloat (Econs a Enil) [x]
    (Val.singleoffloat x)
  · exact eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)
  · rfl

theorem eval_floatofsingle
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_floatofsingleStatement := by
  intro xi ge sp e m le a x h
  refine ⟨Val.floatofsingle x, ?_, Val.lessdef_refl _⟩
  apply eval_expr.eval_Eop le Ofloatofsingle (Econs a Enil) [x]
    (Val.floatofsingle x)
  · exact eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)
  · rfl

theorem eval_intoffloat
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_intoffloatStatement := by
  intro xi ge sp e m le a x y h hxy
  refine ⟨y, ?_, Val.lessdef_refl _⟩
  apply eval_expr.eval_Eop le Ointoffloat (Econs a Enil) [x] y
  · exact eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)
  · exact hxy

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Memory
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

theorem eval_select
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_selectStatement := by
  intro xi ge sp e m le ty cond al vl a1 v1 a2 v2 hs hAl h1 h2
  by_cases hswap : select_swap cond = true
  · refine ⟨Val.select (eval_condition (negate_condition cond) vl m) v2 v1 ty, ?_, ?_⟩
    · simp only [SelectOp.select, hswap, ↓reduceIte]
      apply eval_expr.eval_Eop le (Osel (negate_condition cond) ty)
        (Econs a2 (Econs a1 al)) (v2 :: v1 :: vl) _
      · exact eval_exprlist.cons le a2 (Econs a1 al) v2 (v1 :: vl) h2
          (eval_exprlist.cons le a1 al v1 vl h1 hAl)
      · rfl
    · rw [eval_negate_condition]
      cases hc : eval_condition cond vl m with
      | none => exact Val.lessdef_refl _
      | some b => cases b <;> exact Val.lessdef_refl _
  · refine ⟨Val.select (eval_condition cond vl m) v1 v2 ty, ?_, Val.lessdef_refl _⟩
    · simp only [SelectOp.select, hswap, ↓reduceIte]
      apply eval_expr.eval_Eop le (Osel cond ty)
        (Econs a1 (Econs a2 al)) (v1 :: v2 :: vl) _
      · exact eval_exprlist.cons le a1 (Econs a2 al) v1 (v2 :: vl) h1
          (eval_exprlist.cons le a2 al v2 vl h2 hAl)
      · rfl

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Memory
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

theorem eval_floatofint
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_floatofintStatement := by
  intro xi ge sp e m le a x y h hx
  cases hmatch : floatofint_match a with
  | floatofint_case1 n =>
      have hx' : x = .Vint n := eval_intconst_value_local
        xi ge sp e m le n x (by simpa [hmatch] using h)
      subst x
      simp [Val.floatofint] at hx
      subst y
      refine ⟨.Vfloat (CompCert4Lean.Lib.Floats.Float.of_int
          (certificate := binary64_certificate) n), ?_,
        Val.lessdef_refl _⟩
      simp only [CompCert4Lean.X86.SelectOp.floatofint, hmatch]
      exact eval_expr.eval_Eop le
        (Ofloatconst (CompCert4Lean.Lib.Floats.Float.of_int
          (certificate := binary64_certificate) n)) Enil [] _
        (eval_exprlist.nil le) rfl
  | floatofint_default e1 =>
      refine ⟨y, ?_, Val.lessdef_refl _⟩
      simp only [CompCert4Lean.X86.SelectOp.floatofint, hmatch]
      apply eval_expr.eval_Eop le Ofloatofint (Econs a Enil) [x] y
      · exact eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)
      · exact hx

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Memory
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

private theorem eval_intconst_suffix
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (le : letenv) (n : CCInt) (x : val)
    (h : eval_expr (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge sp e m le
      (Eop (Ointconst n) Enil) x) : x = .Vint n := by
  cases h with
  | eval_Eop _ _ _ _ _ hargs hop =>
      cases hargs
      change some (.Vint n) = some x at hop
      cases hop
      rfl

theorem eval_floatofintu
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_floatofintuStatement := by
  intro xi ge sp e m le a x y h hx
  cases hmatch : floatofintu_match a with
  | floatofintu_case1 n =>
      have hn := eval_intconst_suffix xi ge sp e m le n x (by simpa [hmatch] using h)
      subst x
      simp [Val.floatofintu] at hx
      subst y
      refine ⟨Vfloat (CompCert4Lean.Lib.Floats.Float.of_intu
          (certificate := binary64_certificate) n), ?_, Val.lessdef_refl _⟩
      simp only [CompCert4Lean.X86.SelectOp.floatofintu, hmatch]
      exact eval_expr.eval_Eop le
        (Ofloatconst (CompCert4Lean.Lib.Floats.Float.of_intu
          (certificate := binary64_certificate) n)) Enil [] _
        (eval_exprlist.nil le) rfl
  | floatofintu_default a =>
      cases x with
      | Vint n =>
          simp [Val.floatofintu] at hx
          subst y
          refine ⟨.Vfloat (CompCert4Lean.Lib.Floats.Float.of_intu
              (certificate := binary64_certificate) n), ?_, Val.lessdef_refl _⟩
          simp only [CompCert4Lean.X86.SelectOp.floatofintu, hmatch,
            CompCert4Lean.X86_64.Archi.splitlong,
            CompCert4Lean.X86_64.Archi.ptr64]
          apply eval_expr.eval_Eop le Ofloatoflong
            (Econs (Eop Ocast32unsigned (Econs a Enil)) Enil)
            [Val.longofintu (.Vint n)] _
          · exact eval_exprlist.cons le _ _ _ _
              (eval_expr.eval_Eop le Ocast32unsigned (Econs a Enil) [.Vint n]
                _ (eval_exprlist.cons le a Enil (.Vint n) [] h (eval_exprlist.nil le)) rfl)
              (eval_exprlist.nil le)
          · change some (Vfloat (CompCert4Lean.Lib.Floats.Float.of_long
              (CompCert4Lean.Lib.Integers.Int64.repr
                (CompCert4Lean.Lib.Integers.Int.unsigned n)))) = _
            rw [← CompCert4Lean.Lib.Floats.Float.of_intu_of_long]
      | _ => simp [Val.floatofintu] at hx
end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Memory
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

theorem eval_intofsingle
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_intofsingleStatement := by
  intro xi ge sp e m le a x y h hxy
  refine ⟨y, ?_, Val.lessdef_refl _⟩
  apply eval_expr.eval_Eop le Ointofsingle (Econs a Enil) [x] y
  · exact eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)
  · exact hxy

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Memory
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

theorem eval_singleofint
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_singleofintStatement := by
  intro xi ge sp e m le a x y h hx
  cases hmatch : singleofint_match a with
  | singleofint_case1 n =>
      have hx' : x = .Vint n := eval_intconst_suffix xi ge sp e m le n x
        (by simpa [hmatch] using h)
      subst x
      simp [Val.singleofint] at hx
      subst y
      refine ⟨.Vsingle (CompCert4Lean.Lib.Floats.Float32.of_int
          (certificate := binary32_certificate) n), ?_, Val.lessdef_refl _⟩
      simp only [CompCert4Lean.X86.SelectOp.singleofint, hmatch]
      exact eval_expr.eval_Eop le
        (Osingleconst (CompCert4Lean.Lib.Floats.Float32.of_int
          (certificate := binary32_certificate) n)) Enil [] _
        (eval_exprlist.nil le) rfl
  | singleofint_default e1 =>
      refine ⟨y, ?_, Val.lessdef_refl _⟩
      simp only [CompCert4Lean.X86.SelectOp.singleofint, hmatch]
      apply eval_expr.eval_Eop le Osingleofint (Econs a Enil) [x] y
      · exact eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)
      · exact hx

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Memory
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

theorem eval_builtin_arg_addr
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_builtin_arg_addrStatement := by
  intro xi ge sp e m addr al vl v hargs haddr
  cases hmatch : builtin_arg_addr_match addr al with
  | builtin_arg_addr_case1 n e1 =>
      cases hargs with
      | cons _ _ _ v1 _ h1 hnil =>
          cases hnil
          have hv : v = Val.addl v1 (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr n)) := by
            simpa [eval_addressing, eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] using haddr.symm
          subst v
          simp only [builtin_arg_addr, hmatch]
          simpa [CompCert4Lean.X86_64.Archi.ptr64] using
            (eval_builtin_arg.addPointer (.BA e1) (.BA_long (CompCert4Lean.Lib.Integers.Int64.repr n)) v1
              (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr n))
              (eval_builtin_arg.argument e1 v1 h1) (eval_builtin_arg.longValue _))
  | builtin_arg_addr_case2 id ofs =>
      cases hargs
      simp only [builtin_arg_addr, hmatch]
      simp [eval_addressing, eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at haddr
      cases haddr
      exact eval_builtin_arg.addressGlobal id ofs
  | builtin_arg_addr_case3 ofs =>
      cases hargs
      simp only [builtin_arg_addr, hmatch]
      simp [eval_addressing, eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at haddr
      cases haddr
      exact eval_builtin_arg.addressStack ofs
  | builtin_arg_addr_default addr al =>
      simp only [builtin_arg_addr, hmatch]
      apply eval_builtin_arg.argument (Eop (Olea_ptr addr) al) v
      apply eval_expr.eval_Eop [] (Olea_ptr addr) al vl v
      · exact hargs
      · exact (eval_Olea_ptr (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge sp addr vl m) ▸ haddr

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Memory
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

 theorem eval_addimm
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_addimmStatement := by
  unfold eval_addimmStatement unary_constructor_sound
  intro xi ge sp e mem0 n le a x h
  by_cases hz : CompCert4Lean.Lib.Integers.Int.eq n
      CompCert4Lean.Lib.Integers.Int.zero = true
  · have hn : n = CompCert4Lean.Lib.Integers.Int.zero :=
      int_eq_true_zero_local n hz
    subst n
    refine ⟨x, ?_, ?_⟩
    · simpa [CompCert4Lean.X86.SelectOp.addimm, hz] using h
    · cases x with
      | Vint q =>
          change Val.lessdef (.Vint (CompCert4Lean.Lib.Integers.Int.add q
            CompCert4Lean.Lib.Integers.Int.zero)) (.Vint q)
          rw [CompCert4Lean.Lib.Integers.Int.add_zero_proof]
          exact Val.lessdef_refl _
      | Vundef => exact Val.lessdef_refl _
      | Vlong q => exact Val.lessdef_undef _
      | Vfloat q => exact Val.lessdef_undef _
      | Vsingle q => exact Val.lessdef_undef _
      | Vptr b ofs => exact Val.lessdef_undef _
  · unfold CompCert4Lean.X86.SelectOp.addimm
    rw [if_neg hz]
    cases hcase : addimm_match a with
    | addimm_case1 m =>
        have hx : x = .Vint m := eval_intconst_value_local xi ge sp e mem0 le m x
          (by simpa [hcase] using h)
        subst x
        refine ⟨.Vint (CompCert4Lean.Lib.Integers.Int.add n m), ?_, ?_⟩
        · exact eval_expr.eval_Eop le
            (Ointconst (CompCert4Lean.Lib.Integers.Int.add n m)) Enil [] _
            (eval_exprlist.nil le) rfl
        · change Val.lessdef
            (.Vint (CompCert4Lean.Lib.Integers.Int.add m n))
            (.Vint (CompCert4Lean.Lib.Integers.Int.add n m))
          rw [CompCert4Lean.Lib.Integers.Int.add_commut_proof]
          exact Val.lessdef_refl _
    | addimm_case2 addr args =>
        cases h with
        | eval_Eop le' op al vl v hargs hop =>
            change eval_addressing32 ge sp addr vl = some x at hop
            have hnew := CompCert4Lean.X86.Op.eval_offset_addressing_total_32
              (F := CompCert4Lean.Backend.CminorSel.fundef) (V := Unit) ge sp addr vl
              (CompCert4Lean.Lib.Integers.Int.signed n) x hop
            refine ⟨Val.add x (.Vint n), ?_, Val.lessdef_refl _⟩
            simp only [hcase]
            apply eval_expr.eval_Eop le
              (Olea (offset_addressing_total addr
                (CompCert4Lean.Lib.Integers.Int.signed n)))
              args vl (Val.add x (.Vint n))
            · exact hargs
            · change CompCert4Lean.X86.Op.eval_addressing32
                (F := CompCert4Lean.Backend.CminorSel.fundef) (V := Unit) ge sp
                (offset_addressing_total addr
                  (CompCert4Lean.Lib.Integers.Int.signed n)) vl =
                some (Val.add x (.Vint n))
              have hrepr := CompCert4Lean.Lib.Integers.Int.repr_signed_proof n
              simpa only [hrepr] using hnew
    | addimm_default e1 =>
        refine ⟨Val.add x (.Vint n), ?_, Val.lessdef_refl _⟩
        simp only [hcase]
        apply eval_expr.eval_Eop le
          (Olea (Aindexed (CompCert4Lean.Lib.Integers.Int.signed n)))
          (Econs a Enil) [x] (Val.add x (.Vint n))
        · exact eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)
        · change eval_addressing32 ge sp
            (Aindexed (CompCert4Lean.Lib.Integers.Int.signed n)) [x] =
            some (Val.add x (.Vint n))
          simp [eval_addressing32]
          rw [CompCert4Lean.Lib.Integers.Int.repr_signed_proof n]

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Memory
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

private theorem eval_add_repr_sum_local (x y : Z) :
    CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.add x y) =
      CompCert4Lean.Lib.Integers.Int.add
        (CompCert4Lean.Lib.Integers.Int.repr x)
        (CompCert4Lean.Lib.Integers.Int.repr y) := by
  have hx := CompCert4Lean.Lib.Integers.Int.eqm_unsigned_repr_r_proof x x
    (CompCert4Lean.Lib.Integers.Int.eqm_refl_proof x)
  have hy := CompCert4Lean.Lib.Integers.Int.eqm_unsigned_repr_r_proof y y
    (CompCert4Lean.Lib.Integers.Int.eqm_refl_proof y)
  have hxy := CompCert4Lean.Lib.Integers.Int.eqm_add_proof _ _ _ _ hx hy
  rw [CompCert4Lean.Lib.Integers.Int.eqm_samerepr_proof _ _ hxy]
  exact (CompCert4Lean.Lib.Integers.Int.add_unsigned_proof _ _).symm

private theorem eval_add_scaled_inv_local
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (le : letenv) (t : expr) (sc ofs : Z) (x : val)
    (h : eval_expr xi ge sp e m le
      (Eop (Olea (Ascaled sc ofs)) (Econs t Enil)) x) :
    ∃ v, eval_expr xi ge sp e m le t v ∧
      x = Val.add
        (Val.mul v (.Vint (CompCert4Lean.Lib.Integers.Int.repr sc)))
        (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs)) := by
  cases h with
  | eval_Eop _ _ _ _ _ hargs hop =>
      cases hargs with
      | cons _ _ _ v _ hhead htail =>
          cases htail
          change some (Val.add
            (Val.mul v (.Vint (CompCert4Lean.Lib.Integers.Int.repr sc)))
            (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs))) = some x at hop
          cases hop
          exact ⟨v, hhead, rfl⟩

private theorem eval_add_global_impossible_local
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (le : letenv) (id : CompCert4Lean.Common.AST.ident) (ofs : Ptrofs) (x : val)
    (h : eval_expr xi ge sp e m le (Eop (Olea (Aglobal id ofs)) Enil) x) :
    False := by
  cases h with
  | eval_Eop _ _ _ _ _ hargs hop =>
      cases hargs
      change none = some x at hop
      cases hop

private theorem eval_add_lea_pair_local
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (le : letenv) (addr : op_addressing) (t1 t2 : expr) (x y v : val)
    (hx : eval_expr xi ge sp e m le t1 x)
    (hy : eval_expr xi ge sp e m le t2 y)
    (hv : eval_addressing32 ge sp addr [x, y] = some v) :
    eval_expr xi ge sp e m le (Eop (Olea addr) (Econs t1 (Econs t2 Enil))) v := by
  exact eval_expr.eval_Eop le _ _ [x, y] v
    (eval_exprlist.cons le t1 _ x [y] hx
      (eval_exprlist.cons le t2 Enil y [] hy (eval_exprlist.nil le))) hv

private theorem eval_add_zero_local (x y : val) :
    Val.add (Val.add x y) (.Vint CompCert4Lean.Lib.Integers.Int.zero) =
      Val.add x y := by
  cases x <;> cases y <;>
    simp [Val.add, CompCert4Lean.X86_64.Archi.ptr64]
  case Vint.Vint a b =>
    exact CompCert4Lean.Lib.Integers.Int.add_zero_proof _

theorem eval_add
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_addStatement := by
  intro xi ge sp e m le a x b y ha hb
  have hadd_assoc : ∀ u v w : val,
      Val.add (Val.add u v) w = Val.add u (Val.add v w) := Val.add_assoc
  have hadd_comm : ∀ u v : val, Val.add u v = Val.add v u := Val.add_commut
  have hadd_permut : ∀ u v w : val,
      Val.add u (Val.add v w) = Val.add v (Val.add u w) := Val.add_permut
  have hconst : ∀ n1 n2 : Z,
      val.Vint (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.add n1 n2)) =
        Val.add (.Vint (CompCert4Lean.Lib.Integers.Int.repr n1))
          (.Vint (CompCert4Lean.Lib.Integers.Int.repr n2)) := by
    intro n1 n2
    exact congrArg val.Vint (eval_add_repr_sum_local n1 n2)
  unfold CompCert4Lean.X86.SelectOp.add
  cases hcase : add_match a b with
  | add_case1 n t =>
      have hx := eval_intconst_value_local xi ge sp e m le n x ha
      subst x
      simpa only [hadd_comm] using (eval_addimm xi ge sp e m n le b y hb)
  | add_case2 t n =>
      have hy := eval_intconst_value_local xi ge sp e m le n y hb
      subst y
      exact eval_addimm xi ge sp e m n le a x ha
  | add_case3 n1 t1 n2 t2 =>
      obtain ⟨u, hu, rfl⟩ := eval_lea_indexed_inv_eval_shl_local
        xi ge sp e m le t1 n1 x ha
      obtain ⟨v, hv, rfl⟩ := eval_lea_indexed_inv_eval_shl_local
        xi ge sp e m le t2 n2 y hb
      refine ⟨_, eval_add_lea_pair_local xi ge sp e m le _ _ _ u v _ hu hv rfl, ?_⟩
      rw [hconst]
      rw [Val.add_permut_4 u]
      exact Val.lessdef_refl _
  | add_case4 n1 t1 sc n2 t2 =>
      obtain ⟨u, hu, rfl⟩ := eval_lea_indexed_inv_eval_shl_local
        xi ge sp e m le t1 n1 x ha
      obtain ⟨v, hv, rfl⟩ := eval_add_scaled_inv_local
        xi ge sp e m le t2 sc n2 y hb
      refine ⟨_, eval_add_lea_pair_local xi ge sp e m le _ _ _ u v _ hu hv rfl, ?_⟩
      rw [hconst]
      simp only [hadd_assoc, hadd_comm, hadd_permut]
      exact Val.lessdef_refl _
  | add_case5 sc n1 t1 n2 t2 =>
      obtain ⟨u, hu, rfl⟩ := eval_add_scaled_inv_local
        xi ge sp e m le t1 sc n1 x ha
      obtain ⟨v, hv, rfl⟩ := eval_lea_indexed_inv_eval_shl_local
        xi ge sp e m le t2 n2 y hb
      refine ⟨_, eval_add_lea_pair_local xi ge sp e m le _ _ _ v u _ hv hu rfl, ?_⟩
      rw [hconst]
      simp only [hadd_assoc, hadd_comm, hadd_permut]
      exact Val.lessdef_refl _
  | add_case6 n t id ofs =>
      exact False.elim (eval_add_global_impossible_local xi ge sp e m le id ofs y hb)
  | add_case7 id ofs n t =>
      exact False.elim (eval_add_global_impossible_local xi ge sp e m le id ofs x ha)
  | add_case8 sc n t id ofs =>
      exact False.elim (eval_add_global_impossible_local xi ge sp e m le id ofs y hb)
  | add_case9 id ofs sc n t =>
      exact False.elim (eval_add_global_impossible_local xi ge sp e m le id ofs x ha)
  | add_case10 sc n t1 t2 =>
      obtain ⟨u, hu, rfl⟩ := eval_add_scaled_inv_local
        xi ge sp e m le t1 sc n x ha
      refine ⟨_, eval_add_lea_pair_local xi ge sp e m le _ _ _ y u _ hb hu rfl, ?_⟩
      rw [Val.add_commut]
      exact Val.lessdef_refl _
  | add_case11 t1 sc n t2 =>
      obtain ⟨v, hv, rfl⟩ := eval_add_scaled_inv_local
        xi ge sp e m le t2 sc n y hb
      exact ⟨_, eval_add_lea_pair_local xi ge sp e m le _ _ _ x v _ ha hv rfl,
        Val.lessdef_refl _⟩
  | add_case12 n t1 t2 =>
      obtain ⟨u, hu, rfl⟩ := eval_lea_indexed_inv_eval_shl_local
        xi ge sp e m le t1 n x ha
      refine ⟨_, eval_add_lea_pair_local xi ge sp e m le _ _ _ u y _ hu hb rfl, ?_⟩
      simp only [hadd_assoc, hadd_comm, hadd_permut]
      exact Val.lessdef_refl _
  | add_case13 t1 n t2 =>
      obtain ⟨v, hv, rfl⟩ := eval_lea_indexed_inv_eval_shl_local
        xi ge sp e m le t2 n y hb
      refine ⟨_, eval_add_lea_pair_local xi ge sp e m le _ _ _ x v _ ha hv rfl, ?_⟩
      rw [Val.add_assoc]
      exact Val.lessdef_refl _
  | add_default t1 t2 =>
      refine ⟨_, eval_add_lea_pair_local xi ge sp e m le _ _ _ x y _ ha hb rfl, ?_⟩
      change Val.lessdef (Val.add x y)
        (Val.add (Val.add x y) (.Vint CompCert4Lean.Lib.Integers.Int.zero))
      rw [eval_add_zero_local]
      exact Val.lessdef_refl _

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Memory
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

private theorem eval_sub_repr_neg_local (n : Z) :
    CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.opp n) =
      CompCert4Lean.Lib.Integers.Int.neg
        (CompCert4Lean.Lib.Integers.Int.repr n) := by
  apply CompCert4Lean.Lib.Integers.Int.eqm_samerepr_proof
  apply CompCert4Lean.Lib.Zbits.eqmod_neg
  exact CompCert4Lean.Lib.Integers.Int.eqm_unsigned_repr_r_proof n n
    (CompCert4Lean.Lib.Integers.Int.eqm_refl_proof n)

private theorem eval_sub_repr_diff_local (n1 n2 : Z) :
    CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.sub n1 n2) =
      CompCert4Lean.Lib.Integers.Int.sub
        (CompCert4Lean.Lib.Integers.Int.repr n1)
        (CompCert4Lean.Lib.Integers.Int.repr n2) := by
  have hsub : ZArith.BinInt.Z.sub n1 n2 =
      ZArith.BinInt.Z.add n1 (ZArith.BinInt.Z.opp n2) := by
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add,
      ZArith.BinInt.Z.opp, intOfZ_zOfInt, Int.sub_eq_add_neg]
  rw [hsub, eval_add_repr_sum_local, eval_sub_repr_neg_local,
    CompCert4Lean.Lib.Integers.Int.sub_add_opp_proof]

private theorem eval_sub_pair_local
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (le : letenv) (a b : expr) (x y : val)
    (ha : eval_expr xi ge sp e m le a x)
    (hb : eval_expr xi ge sp e m le b y) :
    eval_expr xi ge sp e m le (Eop Osub (Econs a (Econs b Enil)))
      (Val.sub x y) := by
  exact eval_expr.eval_Eop le Osub _ [x, y] _
    (eval_exprlist.cons le a _ x [y] ha
      (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))) rfl

theorem eval_sub
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_subStatement := by
  intro xi ge sp e m le a x b y ha hb
  unfold CompCert4Lean.X86.SelectOp.sub
  cases hcase : sub_match a b with
  | sub_case1 t n =>
      have hy := eval_intconst_value_local xi ge sp e m le n y hb
      subst y
      rw [Val.sub_add_opp]
      exact eval_addimm xi ge sp e m _ le a x ha
  | sub_case2 n1 t1 n2 t2 =>
      obtain ⟨u, hu, rfl⟩ := eval_lea_indexed_inv_eval_shl_local
        xi ge sp e m le t1 n1 x ha
      obtain ⟨v, hv, rfl⟩ := eval_lea_indexed_inv_eval_shl_local
        xi ge sp e m le t2 n2 y hb
      rw [Val.sub_add_l, Val.sub_add_r, Val.add_assoc]
      change ∃ w, eval_expr xi ge sp e m le _ w ∧
        Val.lessdef (Val.add (Val.sub u v)
          (.Vint (CompCert4Lean.Lib.Integers.Int.add
            (CompCert4Lean.Lib.Integers.Int.neg (CompCert4Lean.Lib.Integers.Int.repr n2))
            (CompCert4Lean.Lib.Integers.Int.repr n1)))) w
      rw [CompCert4Lean.Lib.Integers.Int.add_commut_proof,
        ← CompCert4Lean.Lib.Integers.Int.sub_add_opp_proof,
        ← eval_sub_repr_diff_local]
      exact eval_addimm xi ge sp e m _ le _ _
        (eval_sub_pair_local xi ge sp e m le t1 t2 u v hu hv)
  | sub_case3 n t1 t2 =>
      obtain ⟨u, hu, rfl⟩ := eval_lea_indexed_inv_eval_shl_local
        xi ge sp e m le t1 n x ha
      rw [Val.sub_add_l]
      exact eval_addimm xi ge sp e m _ le _ _
        (eval_sub_pair_local xi ge sp e m le t1 b u y hu hb)
  | sub_case4 t1 n t2 =>
      obtain ⟨v, hv, rfl⟩ := eval_lea_indexed_inv_eval_shl_local
        xi ge sp e m le t2 n y hb
      rw [Val.sub_add_r]
      change ∃ w, eval_expr xi ge sp e m le
        (addimm (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.opp n))
          (Eop Osub (Econs a (Econs t2 Enil)))) w ∧
        Val.lessdef (Val.add (Val.sub x v)
          (.Vint (CompCert4Lean.Lib.Integers.Int.neg
            (CompCert4Lean.Lib.Integers.Int.repr n)))) w
      rw [eval_sub_repr_neg_local n]
      exact eval_addimm xi ge sp e m _ le _ _
        (eval_sub_pair_local xi ge sp e m le a t2 x v ha hv)
  | sub_default t1 t2 =>
      exact ⟨Val.sub x y, eval_sub_pair_local xi ge sp e m le a b x y ha hb,
        Val.lessdef_refl _⟩

end CompCert4Lean.X86.SelectOpproof

namespace CompCert4Lean.X86.SelectOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Memory
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

theorem eval_shlimm
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_shlimmStatement := by
  intro xi ge sp e m n
  exact eval_shlimm_for_eval_shl_local xi ge sp e m n

end CompCert4Lean.X86.SelectOpproof
