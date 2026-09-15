import CompCert4Lean.X86.ConstpropOp
import CompCert4Lean.Backend.RTL
import CompCert4Lean.Backend.ValueDomain
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Values
import CompCert4Lean.Lib.Floats
import CompCert4Lean.Lib.Integers

/-!
# Correctness surface for x86 constant-propagation strength reduction

The source proofs in `x86/ConstpropOpproof.v` are migrated in a later proof
phase.  This module records their exact proposition statements without proof
stubs.
-/

namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Floats
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp
open CompCert4Lean.X86.ConstpropOp

private abbrev reg := CompCert4Lean.Backend.Registers.reg
private abbrev regset := CompCert4Lean.Backend.RTL.regset
private abbrev genv := CompCert4Lean.Backend.RTL.genv
private abbrev block := CompCert4Lean.Common.Values.block
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev operation := CompCert4Lean.X86.Op.operation
private abbrev addressing := CompCert4Lean.X86.Op.addressing
private abbrev condition := CompCert4Lean.X86.Op.condition
private abbrev typ := CompCert4Lean.Common.AST.typ
private abbrev ident := CompCert4Lean.Common.AST.ident
private abbrev aval := CompCert4Lean.Backend.ValueDomain.aval
private abbrev block_classification := CompCert4Lean.Backend.ValueDomain.block_classification
private abbrev int := CompCert4Lean.Lib.Integers.int
private abbrev int64 := CompCert4Lean.Lib.Integers.int64
private abbrev ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev float := CompCert4Lean.Lib.Floats.float
private abbrev float32 := CompCert4Lean.Lib.Floats.float32
private abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev RelocationContext := CompCert4Lean.X86.SelectOp.RelocationContext

private def reg_values (e : regset) (args : List reg) : List val :=
  args.map (fun r => Regmap.get r e)

def eval_Olea_ptrStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (m : mem) (a : addressing) (el : List val),
    eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) (ConstpropOp.Olea_ptr a) el m =
      eval_addressing ge (.Vptr sp Ptrofs.zero) a el

def const_for_result_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (bc : block_classification) (ge : genv),
    genv_match bc ge →
    ∀ (sp : block), bc sp = BCstack →
    ∀ (m : mem) (ctx : RelocationContext) (a : aval) (op : operation) (v : val),
      const_for_result cfg ctx a = some op →
      vmatch bc v a →
      ∃ v',
        eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op [] m = some v' ∧
        Val.lessdef v v'

def cond_strength_reduction_correctStatement : Prop :=
  ∀ (bc : block_classification) (ae : AE.t) (e : regset) (m : mem),
    ematch bc e ae →
    ∀ (cond : condition) (args : List reg) (vl : List aval),
      vl = args.map (fun r => AE.get r ae) →
      let (cond', args') := cond_strength_reduction cond args vl
      eval_condition cond' (reg_values e args') m =
        eval_condition cond (reg_values e args) m

def addr_strength_reduction_32_generic_correctStatement : Prop :=
  ∀ (bc : block_classification) (ge : genv) (sp : block) (ae : AE.t)
    (e : regset),
    ematch bc e ae →
    ∀ (addr : addressing) (args : List reg) (vl : List aval) (res : val),
      vl = args.map (fun r => AE.get r ae) →
      eval_addressing32 ge (.Vptr sp Ptrofs.zero) addr (reg_values e args) = some res →
      let (addr', args') := addr_strength_reduction_32_generic addr args vl
      ∃ res',
        eval_addressing32 ge (.Vptr sp Ptrofs.zero) addr' (reg_values e args') = some res' ∧
        Val.lessdef res res'

def addr_strength_reduction_32_correctStatement : Prop :=
  ∀ (bc : block_classification) (ge : genv),
    genv_match bc ge →
    ∀ (sp : block), bc sp = BCstack →
    ∀ (ae : AE.t) (e : regset),
    ematch bc e ae →
    ∀ (addr : addressing) (args : List reg) (vl : List aval) (res : val),
      vl = args.map (fun r => AE.get r ae) →
      eval_addressing32 ge (.Vptr sp Ptrofs.zero) addr (reg_values e args) = some res →
      let (addr', args') := addr_strength_reduction_32 addr args vl
      ∃ res',
        eval_addressing32 ge (.Vptr sp Ptrofs.zero) addr' (reg_values e args') = some res' ∧
        Val.lessdef res res'

def addr_strength_reduction_64_generic_correctStatement : Prop :=
  ∀ (bc : block_classification) (ge : genv) (sp : block) (ae : AE.t)
    (e : regset),
    ematch bc e ae →
    ∀ (addr : addressing) (args : List reg) (vl : List aval) (res : val),
      vl = args.map (fun r => AE.get r ae) →
      eval_addressing64 ge (.Vptr sp Ptrofs.zero) addr (reg_values e args) = some res →
      let (addr', args') := addr_strength_reduction_64_generic addr args vl
      ∃ res',
        eval_addressing64 ge (.Vptr sp Ptrofs.zero) addr' (reg_values e args') = some res' ∧
        Val.lessdef res res'

def addr_strength_reduction_64_correctStatement : Prop :=
  ∀ (bc : block_classification) (ge : genv),
    genv_match bc ge →
    ∀ (sp : block), bc sp = BCstack →
    ∀ (ae : AE.t) (e : regset),
    ematch bc e ae →
    ∀ (addr : addressing) (args : List reg) (vl : List aval) (res : val),
      vl = args.map (fun r => AE.get r ae) →
      eval_addressing64 ge (.Vptr sp Ptrofs.zero) addr (reg_values e args) = some res →
      let (addr', args') := addr_strength_reduction_64 addr args vl
      ∃ res',
        eval_addressing64 ge (.Vptr sp Ptrofs.zero) addr' (reg_values e args') = some res' ∧
        Val.lessdef res res'

def addr_strength_reduction_correctStatement : Prop :=
  ∀ (bc : block_classification) (ge : genv),
    genv_match bc ge →
    ∀ (sp : block), bc sp = BCstack →
    ∀ (ae : AE.t) (e : regset),
    ematch bc e ae →
    ∀ (addr : addressing) (args : List reg) (vl : List aval) (res : val),
      vl = args.map (fun r => AE.get r ae) →
      eval_addressing ge (.Vptr sp Ptrofs.zero) addr (reg_values e args) = some res →
      let (addr', args') := addr_strength_reduction addr args vl
      ∃ res',
        eval_addressing ge (.Vptr sp Ptrofs.zero) addr' (reg_values e args') = some res' ∧
        Val.lessdef res res'

def make_cmp_base_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (bc : block_classification) (ge : genv) (sp : block) (ae : AE.t)
    (e : regset) (m : mem),
    ematch bc e ae →
    ∀ (c : condition) (args : List reg) (vl : List aval),
      vl = args.map (fun r => AE.get r ae) →
      let (op', args') := make_cmp_base c args vl
      ∃ v,
        eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op' (reg_values e args') m = some v ∧
        Val.lessdef (Val.of_optbool (eval_condition c (reg_values e args) m)) v

def make_cmp_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (bc : block_classification) (ge : genv) (sp : block) (ae : AE.t)
    (e : regset) (m : mem),
    ematch bc e ae →
    ∀ (c : condition) (args : List reg) (vl : List aval),
      vl = args.map (fun r => AE.get r ae) →
      let (op', args') := make_cmp c args vl
      ∃ v,
        eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op' (reg_values e args') m = some v ∧
        Val.lessdef (Val.of_optbool (eval_condition c (reg_values e args) m)) v

def make_select_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (bc : block_classification) (ge : genv)
    (sp : block) (ae : AE.t)
    (e : regset) (m : mem),
    ematch bc e ae →
    ∀ (c : condition) (ty : typ) (r1 r2 : reg) (args : List reg) (vl : List aval),
      vl = args.map (fun r => AE.get r ae) →
      let (op', args') := make_select cfg c ty r1 r2 args vl
      ∃ v,
        eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op' (reg_values e args') m = some v ∧
        Val.lessdef (Val.select (eval_condition c (reg_values e args) m)
          (Regmap.get r1 e) (Regmap.get r2 e) ty) v

def make_addimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : int) (r : reg),
    let (op, args) := make_addimm n r
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.add (Regmap.get r e) (.Vint n)) v

def make_shlimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : int)
    (r1 r2 : reg),
    Regmap.get r2 e = .Vint n →
    let (op, args) := make_shlimm n r1 r2
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.shl (Regmap.get r1 e) (.Vint n)) v

def make_shrimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : int)
    (r1 r2 : reg),
    Regmap.get r2 e = .Vint n →
    let (op, args) := make_shrimm n r1 r2
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.shr (Regmap.get r1 e) (.Vint n)) v

def make_shruimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : int)
    (r1 r2 : reg),
    Regmap.get r2 e = .Vint n →
    let (op, args) := make_shruimm n r1 r2
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.shru (Regmap.get r1 e) (.Vint n)) v

def make_mulimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : int) (r1 : reg),
    let (op, args) := make_mulimm n r1
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.mul (Regmap.get r1 e) (.Vint n)) v

def make_divimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : int)
    (r1 r2 : reg) (v : val),
    Val.divs (Regmap.get r1 e) (Regmap.get r2 e) = some v →
    Regmap.get r2 e = .Vint n →
    let (op, args) := make_divimm n r1 r2
    ∃ w,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some w ∧
      Val.lessdef v w

def make_divuimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : int)
    (r1 r2 : reg) (v : val),
    Val.divu (Regmap.get r1 e) (Regmap.get r2 e) = some v →
    Regmap.get r2 e = .Vint n →
    let (op, args) := make_divuimm n r1 r2
    ∃ w,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some w ∧
      Val.lessdef v w

def make_moduimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : int)
    (r1 r2 : reg) (v : val),
    Val.modu (Regmap.get r1 e) (Regmap.get r2 e) = some v →
    Regmap.get r2 e = .Vint n →
    let (op, args) := make_moduimm n r1 r2
    ∃ w,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some w ∧
      Val.lessdef v w

def make_andimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (bc : block_classification) (ge : genv) (sp : block) (e : regset)
    (m : mem) (n : int) (r : reg) (x : aval),
    vmatch bc (Regmap.get r e) x →
    let (op, args) := make_andimm n r x
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.and (Regmap.get r e) (.Vint n)) v

def make_orimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : int) (r : reg),
    let (op, args) := make_orimm n r
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.or (Regmap.get r e) (.Vint n)) v

def make_xorimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : int) (r : reg),
    let (op, args) := make_xorimm n r
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.xor (Regmap.get r e) (.Vint n)) v

def make_addlimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : int64) (r : reg),
    let (op, args) := make_addlimm n r
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.addl (Regmap.get r e) (.Vlong n)) v

def make_shllimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : int)
    (r1 r2 : reg),
    Regmap.get r2 e = .Vint n →
    let (op, args) := make_shllimm n r1 r2
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.shll (Regmap.get r1 e) (.Vint n)) v

def make_shrlimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : int)
    (r1 r2 : reg),
    Regmap.get r2 e = .Vint n →
    let (op, args) := make_shrlimm n r1 r2
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.shrl (Regmap.get r1 e) (.Vint n)) v

def make_shrluimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : int)
    (r1 r2 : reg),
    Regmap.get r2 e = .Vint n →
    let (op, args) := make_shrluimm n r1 r2
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.shrlu (Regmap.get r1 e) (.Vint n)) v

def make_mullimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : int64) (r1 : reg),
    let (op, args) := make_mullimm n r1
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.mull (Regmap.get r1 e) (.Vlong n)) v

def make_divlimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : int64)
    (r1 r2 : reg) (v : val),
    Val.divls (Regmap.get r1 e) (Regmap.get r2 e) = some v →
    Regmap.get r2 e = .Vlong n →
    let (op, args) := make_divlimm n r1 r2
    ∃ w,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some w ∧
      Val.lessdef v w

def make_divluimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : int64)
    (r1 r2 : reg) (v : val),
    Val.divlu (Regmap.get r1 e) (Regmap.get r2 e) = some v →
    Regmap.get r2 e = .Vlong n →
    let (op, args) := make_divluimm n r1 r2
    ∃ w,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some w ∧
      Val.lessdef v w

def make_modluimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : int64)
    (r1 r2 : reg) (v : val),
    Val.modlu (Regmap.get r1 e) (Regmap.get r2 e) = some v →
    Regmap.get r2 e = .Vlong n →
    let (op, args) := make_modluimm n r1 r2
    ∃ w,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some w ∧
      Val.lessdef v w

def make_andlimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : int64)
    (r : reg) (x : aval),
    let (op, args) := make_andlimm n r x
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.andl (Regmap.get r e) (.Vlong n)) v

def make_orlimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : int64) (r : reg),
    let (op, args) := make_orlimm n r
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.orl (Regmap.get r e) (.Vlong n)) v

def make_xorlimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : int64) (r : reg),
    let (op, args) := make_xorlimm n r
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.xorl (Regmap.get r e) (.Vlong n)) v

def make_mulfimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : float)
    (r1 r2 : reg),
    Regmap.get r2 e = .Vfloat n →
    let (op, args) := make_mulfimm n r1 r1 r2
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.mulf (Regmap.get r1 e) (Regmap.get r2 e)) v

def make_mulfimm_correct_2Statement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : float)
    (r1 : reg) (r2 : reg),
    Regmap.get r1 e = .Vfloat n →
    let (op, args) := make_mulfimm n r2 r1 r2
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.mulf (Regmap.get r1 e) (Regmap.get r2 e)) v

def make_mulfsimm_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : float32)
    (r1 r2 : reg),
    Regmap.get r2 e = .Vsingle n →
    let (op, args) := make_mulfsimm n r1 r1 r2
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.mulfs (Regmap.get r1 e) (Regmap.get r2 e)) v

def make_mulfsimm_correct_2Statement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (e : regset) (m : mem) (n : float32)
    (r1 : reg) (r2 : reg),
    Regmap.get r1 e = .Vsingle n →
    let (op, args) := make_mulfsimm n r2 r1 r2
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.mulfs (Regmap.get r1 e) (Regmap.get r2 e)) v

def make_cast8signed_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (bc : block_classification) (ge : genv) (sp : block) (e : regset)
    (m : mem) (r : reg) (x : aval),
    vmatch bc (Regmap.get r e) x →
    let (op, args) := make_cast8signed r x
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.sign_ext (ZArith.BinInt.Z.of_nat 8) (Regmap.get r e)) v

def make_cast8unsigned_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (bc : block_classification) (ge : genv) (sp : block) (e : regset)
    (m : mem) (r : reg) (x : aval),
    vmatch bc (Regmap.get r e) x →
    let (op, args) := make_cast8unsigned r x
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.zero_ext (ZArith.BinInt.Z.of_nat 8) (Regmap.get r e)) v

def make_cast16signed_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (bc : block_classification) (ge : genv) (sp : block) (e : regset)
    (m : mem) (r : reg) (x : aval),
    vmatch bc (Regmap.get r e) x →
    let (op, args) := make_cast16signed r x
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.sign_ext (ZArith.BinInt.Z.of_nat 16) (Regmap.get r e)) v

def make_cast16unsigned_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (bc : block_classification) (ge : genv) (sp : block) (e : regset)
    (m : mem) (r : reg) (x : aval),
    vmatch bc (Regmap.get r e) x →
    let (op, args) := make_cast16unsigned r x
    ∃ v,
      eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v ∧
      Val.lessdef (Val.zero_ext (ZArith.BinInt.Z.of_nat 16) (Regmap.get r e)) v

def op_strength_reduction_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (bc : block_classification) (ge : genv),
    genv_match bc ge →
    ∀ (sp : block), bc sp = BCstack →
    ∀ (ae : AE.t) (e : regset) (m : mem),
      ematch bc e ae →
      ∀ (op : operation) (args : List reg) (vl : List aval) (v : val),
        vl = args.map (fun r => AE.get r ae) →
        eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op (reg_values e args) m = some v →
        let (op', args') := op_strength_reduction cfg op args vl
        ∃ w,
          eval_operation (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) ge (.Vptr sp Ptrofs.zero) op' (reg_values e args') m = some w ∧
          Val.lessdef v w

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

theorem eval_Olea_ptr
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_Olea_ptrStatement binary64_certificate binary32_certificate := by
  intro ge sp m a el
  rfl

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.X86.ConstpropOp
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem cp_eq_true (x y : CompCert4Lean.Lib.Integers.int)
    (h : CompCert4Lean.Lib.Integers.Int.eq x y = true) : x = y := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext
  have hd : decide (x.intval = y.intval) = true := by
    simpa [CompCert4Lean.Lib.Integers.Int.eq,
      CompCert4Lean.Lib.Integers.WordCore.eq] using h
  exact of_decide_eq_true hd

private theorem cp_zofnat (x : CompCert4Lean.Lib.Integers.int) :
    zOfNat x.val = x.intval := by
  have hx : ZArith.BinInt.Z.le Z0 x.intval := by
    have h := x.intrange.1
    change (-1 : Int) < intOfZ x.intval at h
    change 0 ≤ intOfZ x.intval
    omega
  exact ZArith.Znat.Z2Nat.id x.intval hx

private theorem cp_or_zero (x : CompCert4Lean.Lib.Integers.int) :
    CompCert4Lean.Lib.Integers.Int.or x CompCert4Lean.Lib.Integers.Int.zero = x := by
  unfold CompCert4Lean.Lib.Integers.Int.or CompCert4Lean.Lib.Integers.WordCore.or
  change CompCert4Lean.Lib.Integers.Int.repr
    (zOfNat (Nat.lor x.val CompCert4Lean.Lib.Integers.Int.zero.val)) = x
  rw [show CompCert4Lean.Lib.Integers.Int.zero.val = 0 by rfl]
  rw [show Nat.lor x.val 0 = x.val by simpa only [Nat.lor_eq] using Nat.or_zero x.val]
  rw [cp_zofnat]
  exact CompCert4Lean.Lib.Integers.Int.repr_unsigned_proof x

private theorem cp_or_mone (x : CompCert4Lean.Lib.Integers.int) :
    CompCert4Lean.Lib.Integers.Int.or x CompCert4Lean.Lib.Integers.Int.mone =
      CompCert4Lean.Lib.Integers.Int.mone := by
  unfold CompCert4Lean.Lib.Integers.Int.or CompCert4Lean.Lib.Integers.WordCore.or
  change CompCert4Lean.Lib.Integers.Int.repr
    (zOfNat (Nat.lor x.val CompCert4Lean.Lib.Integers.Int.mone.val)) =
      CompCert4Lean.Lib.Integers.Int.mone
  have hm : CompCert4Lean.Lib.Integers.Int.mone.val =
      2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1 := by rfl
  rw [hm]
  have hor : Nat.lor x.val (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1) =
      2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1 := by
    have hlt : Nat.lor x.val (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1) <
        2 ^ CompCert4Lean.Lib.Integers.Int.wordsize :=
      Nat.or_lt_two_pow x.toFin.isLt (by change 2 ^ (32 : Nat) - 1 < 2 ^ (32 : Nat); omega)
    have hle : 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1 ≤
        Nat.lor x.val (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1) := Nat.right_le_or
    omega
  rw [hor, ← hm, cp_zofnat]
  exact CompCert4Lean.Lib.Integers.Int.repr_unsigned_proof _

private theorem cp_xor_zero (x : CompCert4Lean.Lib.Integers.int) :
    CompCert4Lean.Lib.Integers.Int.xor x CompCert4Lean.Lib.Integers.Int.zero = x := by
  unfold CompCert4Lean.Lib.Integers.Int.xor CompCert4Lean.Lib.Integers.WordCore.xor
  change CompCert4Lean.Lib.Integers.Int.repr
    (zOfNat (Nat.xor x.val CompCert4Lean.Lib.Integers.Int.zero.val)) = x
  rw [show CompCert4Lean.Lib.Integers.Int.zero.val = 0 by rfl]
  rw [show Nat.xor x.val 0 = x.val by simpa only [Nat.xor_eq] using Nat.xor_zero x.val]
  rw [cp_zofnat]
  exact CompCert4Lean.Lib.Integers.Int.repr_unsigned_proof x

private theorem cp_not_xor (x : CompCert4Lean.Lib.Integers.int) :
    CompCert4Lean.Lib.Integers.Int.not x =
      CompCert4Lean.Lib.Integers.Int.xor x CompCert4Lean.Lib.Integers.Int.mone := by
  have hm : (CompCert4Lean.Lib.Integers.WordCore.mone
      CompCert4Lean.Lib.Integers.Int.wordsize).val =
      2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1 := by rfl
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  simp [CompCert4Lean.Lib.Integers.Int.not,
    CompCert4Lean.Lib.Integers.Int.xor,
    CompCert4Lean.Lib.Integers.Int.mone,
    CompCert4Lean.Lib.Integers.WordCore.not,
    CompCert4Lean.Lib.Integers.WordCore.xor,
    CompCert4Lean.Lib.Integers.WordCore.repr,
    CompCert4Lean.Lib.Integers.WordCore.Word.val]
  simp only [CompCert4Lean.Lib.Integers.WordCore.Word.val] at hm
  rw [hm]

private theorem cp_val_or_zero (x : CompCert4Lean.Common.Values.val) :
    CompCert4Lean.Common.Values.Val.lessdef
      (CompCert4Lean.Common.Values.Val.or x (.Vint CompCert4Lean.Lib.Integers.Int.zero)) x := by
  cases x with
  | Vint n =>
      change CompCert4Lean.Common.Values.Val.lessdef
        (.Vint (CompCert4Lean.Lib.Integers.Int.or n CompCert4Lean.Lib.Integers.Int.zero)) (.Vint n)
      rw [cp_or_zero]
      exact CompCert4Lean.Common.Values.Val.lessdef_refl _
  | _ => exact CompCert4Lean.Common.Values.Val.lessdef_undef _

private theorem cp_val_or_mone (x : CompCert4Lean.Common.Values.val) :
    CompCert4Lean.Common.Values.Val.lessdef
      (CompCert4Lean.Common.Values.Val.or x (.Vint CompCert4Lean.Lib.Integers.Int.mone))
      (.Vint CompCert4Lean.Lib.Integers.Int.mone) := by
  cases x with
  | Vint n =>
      change CompCert4Lean.Common.Values.Val.lessdef
        (.Vint (CompCert4Lean.Lib.Integers.Int.or n CompCert4Lean.Lib.Integers.Int.mone))
        (.Vint CompCert4Lean.Lib.Integers.Int.mone)
      rw [cp_or_mone]
      exact CompCert4Lean.Common.Values.Val.lessdef_refl _
  | _ => exact CompCert4Lean.Common.Values.Val.lessdef_undef _

private theorem cp_val_xor_zero (x : CompCert4Lean.Common.Values.val) :
    CompCert4Lean.Common.Values.Val.lessdef
      (CompCert4Lean.Common.Values.Val.xor x (.Vint CompCert4Lean.Lib.Integers.Int.zero)) x := by
  cases x with
  | Vint n =>
      change CompCert4Lean.Common.Values.Val.lessdef
        (.Vint (CompCert4Lean.Lib.Integers.Int.xor n CompCert4Lean.Lib.Integers.Int.zero)) (.Vint n)
      rw [cp_xor_zero]
      exact CompCert4Lean.Common.Values.Val.lessdef_refl _
  | _ => exact CompCert4Lean.Common.Values.Val.lessdef_undef _

private theorem cp_val_not_xor (x : CompCert4Lean.Common.Values.val) :
    CompCert4Lean.Common.Values.Val.notint x =
      CompCert4Lean.Common.Values.Val.xor x (.Vint CompCert4Lean.Lib.Integers.Int.mone) := by
  cases x with
  | Vundef => rfl
  | Vint n =>
      simp only [CompCert4Lean.Common.Values.Val.notint, CompCert4Lean.Common.Values.Val.xor]
      exact congrArg CompCert4Lean.Common.Values.val.Vint (cp_not_xor n).symm
  | Vlong _ => rfl
  | Vfloat _ => rfl
  | Vsingle _ => rfl
  | Vptr _ _ => rfl

theorem make_orimm_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @make_orimm_correctStatement binary64_certificate binary32_certificate := by
  intro ge sp e m n r
  dsimp [make_orimm]
  split <;> rename_i h
  · have hn := cp_eq_true n CompCert4Lean.Lib.Integers.Int.zero h
    subst n
    refine ⟨CompCert4Lean.Backend.Registers.Regmap.get r e, ?_, cp_val_or_zero _⟩
    rfl
  · split <;> rename_i h'
    · have hn := cp_eq_true n CompCert4Lean.Lib.Integers.Int.mone h'
      subst n
      refine ⟨.Vint CompCert4Lean.Lib.Integers.Int.mone, ?_, cp_val_or_mone _⟩
      rfl
    · refine ⟨CompCert4Lean.Common.Values.Val.or
          (CompCert4Lean.Backend.Registers.Regmap.get r e) (.Vint n), ?_,
          CompCert4Lean.Common.Values.Val.lessdef_refl _⟩
      rfl

theorem make_xorimm_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @make_xorimm_correctStatement binary64_certificate binary32_certificate := by
  intro ge sp e m n r
  dsimp [make_xorimm]
  split <;> rename_i h
  · have hn := cp_eq_true n CompCert4Lean.Lib.Integers.Int.zero h
    subst n
    refine ⟨CompCert4Lean.Backend.Registers.Regmap.get r e, ?_, cp_val_xor_zero _⟩
    rfl
  · split <;> rename_i h'
    · have hn := cp_eq_true n CompCert4Lean.Lib.Integers.Int.mone h'
      subst n
      let x := CompCert4Lean.Backend.Registers.Regmap.get r e
      refine ⟨CompCert4Lean.Common.Values.Val.notint x, ?_, ?_⟩
      · rfl
      · rw [cp_val_not_xor]
        exact CompCert4Lean.Common.Values.Val.lessdef_refl _
    · refine ⟨CompCert4Lean.Common.Values.Val.xor
          (CompCert4Lean.Backend.Registers.Regmap.get r e) (.Vint n), ?_,
          CompCert4Lean.Common.Values.Val.lessdef_refl _⟩
      rfl

end CompCert4Lean.X86.ConstpropOpproof
