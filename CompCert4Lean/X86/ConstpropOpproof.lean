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

namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.ConstpropOp
open Lean Elab Tactic Meta

private def cp_suffixPrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem cp_suffixWordValRepr64 (bits : Nat) (i : Int) :
    (CompCert4Lean.Lib.Integers.WordCore.repr bits
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt i)).val =
      Int.toNat (i % ((2 ^ bits : Nat) : Int)) := by
  run_tac
    let lctx ← getLCtx
    let bitsF := (lctx.findFromUserName? `bits).get!
    let iF := (lctx.findFromUserName? `i).get!
    let bitsE := mkFVar bitsF.fvarId
    let iE := mkFVar iF.fvarId
    let e ← mkAppM
      (cp_suffixPrivateName "CompCert4Lean.Lib.Integers.WordCore.val_repr")
      #[bitsE, iE]
    closeMainGoal Name.anonymous e

private theorem cp_word_add_val {bits : Nat}
    (x y : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    (CompCert4Lean.Lib.Integers.WordCore.add x y).val =
      (x.val + y.val) % (2 ^ bits) := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let yF := (lctx.findFromUserName? `y).get!
    let e ← mkAppM
      (cp_suffixPrivateName "CompCert4Lean.Lib.Integers.WordCore.add_val")
      #[mkFVar xF.fvarId, mkFVar yF.fvarId]
    closeMainGoal Name.anonymous e

private theorem cp_word_add_zero {bits : Nat}
    (x : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    CompCert4Lean.Lib.Integers.WordCore.add x
        (CompCert4Lean.Lib.Integers.WordCore.zero bits) = x := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  change (CompCert4Lean.Lib.Integers.WordCore.add x
      (CompCert4Lean.Lib.Integers.WordCore.zero bits)).val = x.val
  rw [cp_word_add_val]
  change (x.val + 0) % (2 ^ bits) = x.val
  rw [Nat.add_zero, Nat.mod_eq_of_lt]
  exact x.toFin.isLt

private theorem cp_ptrofs_add_zero
    (x : CompCert4Lean.Lib.Integers.Ptrofs.int) :
    CompCert4Lean.Lib.Integers.Ptrofs.add x
        CompCert4Lean.Lib.Integers.Ptrofs.zero = x := by
  change CompCert4Lean.Lib.Integers.WordCore.add x
      (CompCert4Lean.Lib.Integers.WordCore.zero
        CompCert4Lean.Lib.Integers.Ptrofs.wordsize) = x
  exact cp_word_add_zero x

private theorem cp_int64_repr_signed (x : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.repr
        (CompCert4Lean.Lib.Integers.Int64.signed x) = x := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  have hx0 : ZArith.BinInt.Z.le .Z0 x.intval := by
    have h := x.intrange.1
    change (-1 : Int) < intOfZ x.intval at h
    change 0 ≤ intOfZ x.intval
    omega
  have hxrepr : x.intval = zOfNat x.val :=
    (ZArith.Znat.Z2Nat.id x.intval hx0).symm
  have hxlt : x.val < 2 ^ 64 := x.toFin.isLt
  rw [show CompCert4Lean.Lib.Integers.Int64.signed x =
      zOfInt (intOfZ (CompCert4Lean.Lib.Integers.Int64.signed x)) by
    exact (zOfInt_intOfZ _).symm]
  unfold CompCert4Lean.Lib.Integers.Int64.repr
  rw [cp_suffixWordValRepr64]
  simp only [CompCert4Lean.Lib.Integers.Int64.signed,
    CompCert4Lean.Lib.Integers.WordCore.signed,
    CompCert4Lean.Lib.Integers.WordCore.unsigned,
    CompCert4Lean.Lib.Integers.Int64.wordsize]
  run_tac
    let zltName := Lean.mkIdent
      (cp_suffixPrivateName "CompCert4Lean.Lib.Integers.zltSelect")
    let selectName := Lean.mkIdent
      (cp_suffixPrivateName "CompCert4Lean.Lib.Integers.sumboolSelect")
    let subName := Lean.mkIdent
      (cp_suffixPrivateName "CompCert4Lean.Lib.Integers.zSub")
    let powerName := Lean.mkIdent
      (cp_suffixPrivateName "CompCert4Lean.Lib.Integers.zTwoPowerNat")
    evalTactic (← `(tactic|
      unfold $zltName $selectName $subName $powerName))
  simp only [CompCert4Lean.Lib.Integers.Int64.wordsize, Nat.reduceSub]
  rw [hxrepr]
  unfold zOfNat
  split
  · rw [show ZArith.BinInt.Z.of_nat x.val = zOfInt (Int.ofNat x.val) by rfl,
      intOfZ_zOfInt]
    change Int.toNat ((Int.ofNat x.val) % (2 ^ 64 : Int)) = x.val
    have hvalLt : Int.ofNat x.val < (2 ^ 64 : Int) := by
      change Int.ofNat x.val < Int.ofNat (2 ^ 64)
      exact Int.ofNat_lt.mpr hxlt
    have hmod := Int.emod_eq_of_lt (Int.natCast_nonneg _) hvalLt
    exact (congrArg Int.toNat hmod).trans (by simp)
  · rw [show ZArith.BinInt.Z.of_nat x.val = zOfInt (Int.ofNat x.val) by rfl]
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    change Int.toNat
      (((Int.ofNat x.val) - (2 ^ 64 : Int)) % (2 ^ 64 : Int)) = x.val
    rw [Int.sub_emod]
    rw [Int.emod_self, Int.sub_zero]
    have hvalLt : Int.ofNat x.val < (2 ^ 64 : Int) := by
      change Int.ofNat x.val < Int.ofNat (2 ^ 64)
      exact Int.ofNat_lt.mpr hxlt
    have hmod := Int.emod_eq_of_lt (Int.natCast_nonneg _) hvalLt
    calc
      Int.toNat ((Int.ofNat x.val % (2 ^ 64 : Int)) % (2 ^ 64 : Int)) =
          Int.toNat (Int.ofNat x.val % (2 ^ 64 : Int)) := by
        exact congrArg Int.toNat (Int.emod_emod _ _)
      _ = Int.toNat (Int.ofNat x.val) := congrArg Int.toNat hmod
      _ = x.val := by simp

set_option maxHeartbeats 1000000 in
theorem make_addlimm_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @make_addlimm_correctStatement binary64_certificate binary32_certificate := by
  intro ge sp e m n r
  dsimp [make_addlimm]
  split <;> rename_i h
  · have hn : n = CompCert4Lean.Lib.Integers.Int64.zero := by
      apply CompCert4Lean.Lib.Integers.WordCore.ext
      have hd : decide (n.intval =
          CompCert4Lean.Lib.Integers.Int64.zero.intval) = true := by
        simpa [CompCert4Lean.Lib.Integers.Int64.eq,
          CompCert4Lean.Lib.Integers.WordCore.eq] using h
      exact of_decide_eq_true hd
    subst n
    refine ⟨CompCert4Lean.Backend.Registers.Regmap.get r e, ?_, ?_⟩
    · rfl
    · cases hr : CompCert4Lean.Backend.Registers.Regmap.get r e with
      | Vundef =>
          simp [CompCert4Lean.Common.Values.Val.addl]
          exact CompCert4Lean.Common.Values.Val.lessdef_refl _
      | Vint i =>
          simp [CompCert4Lean.Common.Values.Val.addl]
          exact CompCert4Lean.Common.Values.Val.lessdef_undef _
      | Vlong i =>
          change CompCert4Lean.Common.Values.Val.lessdef
            (.Vlong (CompCert4Lean.Lib.Integers.Int64.add i
              CompCert4Lean.Lib.Integers.Int64.zero)) (.Vlong i)
          rw [show CompCert4Lean.Lib.Integers.Int64.add i
              CompCert4Lean.Lib.Integers.Int64.zero = i by
            exact cp_word_add_zero i]
          exact CompCert4Lean.Common.Values.Val.lessdef_refl _
      | Vfloat f =>
          simp [CompCert4Lean.Common.Values.Val.addl]
          exact CompCert4Lean.Common.Values.Val.lessdef_undef _
      | Vsingle f =>
          simp [CompCert4Lean.Common.Values.Val.addl]
          exact CompCert4Lean.Common.Values.Val.lessdef_undef _
      | Vptr b ofs =>
          by_cases hp : CompCert4Lean.X86_64.Archi.ptr64 = true
          · simp only [CompCert4Lean.Common.Values.Val.addl, hp, ↓reduceIte]
            have hz : CompCert4Lean.Lib.Integers.Ptrofs.of_int64
                CompCert4Lean.Lib.Integers.Int64.zero =
                CompCert4Lean.Lib.Integers.Ptrofs.zero := by rfl
            rw [hz, cp_ptrofs_add_zero]
            exact CompCert4Lean.Common.Values.Val.lessdef_refl _
          · simp only [CompCert4Lean.Common.Values.Val.addl, hp, ↓reduceIte]
            exact CompCert4Lean.Common.Values.Val.lessdef_undef _
  · refine ⟨CompCert4Lean.Common.Values.Val.addl
      (CompCert4Lean.Backend.Registers.Regmap.get r e) (.Vlong n), ?_⟩
    constructor
    · change some (CompCert4Lean.Common.Values.Val.addl
          (CompCert4Lean.Backend.Registers.Regmap.get r e)
          (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr
            (CompCert4Lean.Lib.Integers.Int64.signed n)))) =
        some (CompCert4Lean.Common.Values.Val.addl
          (CompCert4Lean.Backend.Registers.Regmap.get r e) (.Vlong n))
      rw [cp_int64_repr_signed]
    · exact CompCert4Lean.Common.Values.Val.lessdef_refl _

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.ConstpropOp

private theorem cp_int64_shl'_zero
    (x : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.shl' x
        CompCert4Lean.Lib.Integers.Int.zero = x := by
  unfold CompCert4Lean.Lib.Integers.Int64.shl'
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  change (CompCert4Lean.Lib.Integers.WordCore.repr
      CompCert4Lean.Lib.Integers.Int64.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftl
        (CompCert4Lean.Lib.Integers.Int64.unsigned x)
        (CompCert4Lean.Lib.Integers.Int.unsigned
          CompCert4Lean.Lib.Integers.Int.zero))).val = x.val
  have hz : CompCert4Lean.Lib.Integers.Int.unsigned
      CompCert4Lean.Lib.Integers.Int.zero =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0 := by
    rfl
  rw [hz]
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftl_0_r]
  have hx0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0 x.intval := by
    have h := x.intrange.1
    change (-1 : Int) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval at h
    change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval
    omega
  have hunsigned : CompCert4Lean.Lib.Integers.Int64.unsigned x =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat x.val := by
    unfold CompCert4Lean.Lib.Integers.Int64.unsigned
      CompCert4Lean.Lib.Integers.WordCore.unsigned
      CompCert4Lean.Lib.Integers.WordCore.Word.val
    exact (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Z2Nat.id
      x.intval hx0).symm
  rw [hunsigned]
  rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat x.val =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat x.val) by rfl]
  rw [cp_suffixWordValRepr64]
  have hxlt : x.val < 2 ^ 64 := x.toFin.isLt
  have hmod : Int.ofNat x.val % (2 ^ 64 : Int) = Int.ofNat x.val := by
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by
      change Int.ofNat x.val < Int.ofNat (2 ^ 64)
      exact Int.ofNat_lt.mpr hxlt)
  change Int.toNat (Int.ofNat x.val % (2 ^ 64 : Int)) = x.val
  rw [hmod]
  simp

set_option maxHeartbeats 1000000 in
theorem make_shllimm_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @make_shllimm_correctStatement binary64_certificate binary32_certificate := by
  intro ge sp e m n r1 r2 h
  dsimp [CompCert4Lean.X86.ConstpropOp.make_shllimm]
  split <;> rename_i hzero
  · have hn : n = CompCert4Lean.Lib.Integers.Int.zero := by
      apply CompCert4Lean.Lib.Integers.WordCore.ext
      have hd : decide (n.intval =
          CompCert4Lean.Lib.Integers.Int.zero.intval) = true := by
        simpa [CompCert4Lean.Lib.Integers.Int.eq,
          CompCert4Lean.Lib.Integers.WordCore.eq] using hzero
      exact of_decide_eq_true hd
    subst n
    refine ⟨CompCert4Lean.Backend.Registers.Regmap.get r1 e, ?_, ?_⟩
    · rfl
    · cases hr : CompCert4Lean.Backend.Registers.Regmap.get r1 e with
      | Vundef =>
          simp [CompCert4Lean.Common.Values.Val.shll]
          exact CompCert4Lean.Common.Values.Val.lessdef_refl _
      | Vint i =>
          simp [CompCert4Lean.Common.Values.Val.shll]
          exact CompCert4Lean.Common.Values.Val.lessdef_undef _
      | Vlong i =>
          change CompCert4Lean.Common.Values.Val.lessdef
            (.Vlong (CompCert4Lean.Lib.Integers.Int64.shl' i
              CompCert4Lean.Lib.Integers.Int.zero)) (.Vlong i)
          rw [cp_int64_shl'_zero]
          exact CompCert4Lean.Common.Values.Val.lessdef_refl _
      | Vfloat f =>
          simp [CompCert4Lean.Common.Values.Val.shll]
          exact CompCert4Lean.Common.Values.Val.lessdef_undef _
      | Vsingle f =>
          simp [CompCert4Lean.Common.Values.Val.shll]
          exact CompCert4Lean.Common.Values.Val.lessdef_undef _
      | Vptr b ofs =>
          simp [CompCert4Lean.Common.Values.Val.shll]
          exact CompCert4Lean.Common.Values.Val.lessdef_undef _
  · split <;> rename_i hlt
    · refine ⟨CompCert4Lean.Common.Values.Val.shll
        (CompCert4Lean.Backend.Registers.Regmap.get r1 e) (.Vint n), ?_⟩
      constructor
      · rfl
      · exact CompCert4Lean.Common.Values.Val.lessdef_refl _
    · refine ⟨CompCert4Lean.Common.Values.Val.shll
        (CompCert4Lean.Backend.Registers.Regmap.get r1 e)
        (CompCert4Lean.Backend.Registers.Regmap.get r2 e), ?_⟩
      constructor
      · rfl
      · rw [h]
        exact CompCert4Lean.Common.Values.Val.lessdef_refl _

end CompCert4Lean.X86.ConstpropOpproof


namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.ConstpropOp

private theorem cp_int64_shr'_zero
    (x : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.shr' x
        CompCert4Lean.Lib.Integers.Int.zero = x := by
  unfold CompCert4Lean.Lib.Integers.Int64.shr'
  change CompCert4Lean.Lib.Integers.Int64.repr
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftr
        (CompCert4Lean.Lib.Integers.Int64.signed x)
        (CompCert4Lean.Lib.Integers.Int.unsigned
          CompCert4Lean.Lib.Integers.Int.zero)) = x
  have hz : CompCert4Lean.Lib.Integers.Int.unsigned
      CompCert4Lean.Lib.Integers.Int.zero =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0 := by
    rfl
  rw [hz]
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftr
  rw [if_pos (show (0 : Int) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0 by
    change (0 : Int) ≤ 0
    exact Int.le_refl _)]
  rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0 = 0 by rfl]
  change CompCert4Lean.Lib.Integers.Int64.repr
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (Int.ediv (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int64.signed x)) 1)) = x
  have hdiv : Int.ediv
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Lib.Integers.Int64.signed x)) 1 =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Lib.Integers.Int64.signed x) := by
    exact Int.ediv_one _
  rw [hdiv]
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt_intOfZ]
  exact cp_int64_repr_signed x

set_option maxHeartbeats 1000000 in
theorem make_shrlimm_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @make_shrlimm_correctStatement binary64_certificate binary32_certificate := by
  intro ge sp e m n r1 r2 h
  dsimp [CompCert4Lean.X86.ConstpropOp.make_shrlimm]
  split <;> rename_i hzero
  · have hn : n = CompCert4Lean.Lib.Integers.Int.zero := by
      apply CompCert4Lean.Lib.Integers.WordCore.ext
      have hd : decide (n.intval =
          CompCert4Lean.Lib.Integers.Int.zero.intval) = true := by
        simpa [CompCert4Lean.Lib.Integers.Int.eq,
          CompCert4Lean.Lib.Integers.WordCore.eq] using hzero
      exact of_decide_eq_true hd
    subst n
    refine ⟨CompCert4Lean.Backend.Registers.Regmap.get r1 e, ?_, ?_⟩
    · rfl
    · cases hr : CompCert4Lean.Backend.Registers.Regmap.get r1 e with
      | Vundef =>
          simp [CompCert4Lean.Common.Values.Val.shrl]
          exact CompCert4Lean.Common.Values.Val.lessdef_refl _
      | Vint i =>
          simp [CompCert4Lean.Common.Values.Val.shrl]
          exact CompCert4Lean.Common.Values.Val.lessdef_undef _
      | Vlong i =>
          change CompCert4Lean.Common.Values.Val.lessdef
            (.Vlong (CompCert4Lean.Lib.Integers.Int64.shr' i
              CompCert4Lean.Lib.Integers.Int.zero)) (.Vlong i)
          rw [cp_int64_shr'_zero]
          exact CompCert4Lean.Common.Values.Val.lessdef_refl _
      | Vfloat f =>
          simp [CompCert4Lean.Common.Values.Val.shrl]
          exact CompCert4Lean.Common.Values.Val.lessdef_undef _
      | Vsingle f =>
          simp [CompCert4Lean.Common.Values.Val.shrl]
          exact CompCert4Lean.Common.Values.Val.lessdef_undef _
      | Vptr b ofs =>
          simp [CompCert4Lean.Common.Values.Val.shrl]
          exact CompCert4Lean.Common.Values.Val.lessdef_undef _
  · split <;> rename_i hlt
    · refine ⟨CompCert4Lean.Common.Values.Val.shrl
        (CompCert4Lean.Backend.Registers.Regmap.get r1 e) (.Vint n), ?_⟩
      constructor
      · rfl
      · exact CompCert4Lean.Common.Values.Val.lessdef_refl _
    · refine ⟨CompCert4Lean.Common.Values.Val.shrl
        (CompCert4Lean.Backend.Registers.Regmap.get r1 e)
        (CompCert4Lean.Backend.Registers.Regmap.get r2 e), ?_⟩
      constructor
      · rfl
      · rw [h]
        exact CompCert4Lean.Common.Values.Val.lessdef_refl _

end CompCert4Lean.X86.ConstpropOpproof
namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.ConstpropOp
open Lean Elab Tactic Meta

private def worker_suffixPrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem worker_word_val_repr (bits : Nat) (i : Int) :
    (CompCert4Lean.Lib.Integers.WordCore.repr bits
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt i)).val =
      Int.toNat (i % ((2 ^ bits : Nat) : Int)) := by
  run_tac
    let lctx ← getLCtx
    let bitsF := (lctx.findFromUserName? `bits).get!
    let iF := (lctx.findFromUserName? `i).get!
    let e ← mkAppM
      (worker_suffixPrivateName "CompCert4Lean.Lib.Integers.WordCore.val_repr")
      #[mkFVar bitsF.fvarId, mkFVar iF.fvarId]
    closeMainGoal Name.anonymous e

private theorem worker_int64_repr_unsigned (x : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.repr
        (CompCert4Lean.Lib.Integers.Int64.unsigned x) = x := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  have hx0 : ZArith.BinInt.Z.le .Z0
      (CompCert4Lean.Lib.Integers.Int64.unsigned x) := by
    have h := x.intrange.1
    change (-1 : Int) < intOfZ x.intval at h
    change 0 ≤ intOfZ x.intval
    omega
  have hxlt : ZArith.BinInt.Z.lt
      (CompCert4Lean.Lib.Integers.Int64.unsigned x)
      CompCert4Lean.Lib.Integers.Int64.modulus := x.intrange.2
  have hxmax : ZArith.BinInt.Z.le
      (CompCert4Lean.Lib.Integers.Int64.unsigned x)
      CompCert4Lean.Lib.Integers.Int64.max_unsigned := by
    change intOfZ (CompCert4Lean.Lib.Integers.Int64.unsigned x) ≤
      intOfZ CompCert4Lean.Lib.Integers.Int64.modulus - 1
    change intOfZ (CompCert4Lean.Lib.Integers.Int64.unsigned x) <
      intOfZ CompCert4Lean.Lib.Integers.Int64.modulus at hxlt
    omega
  have hxrepr : x.intval = ZArith.BinInt.Z.of_nat x.val :=
    (ZArith.Znat.Z2Nat.id x.intval hx0).symm
  unfold CompCert4Lean.Lib.Integers.Int64.repr
  rw [show CompCert4Lean.Lib.Integers.Int64.unsigned x =
      ZArith.BinInt.Z.of_nat x.val by exact hxrepr]
  rw [show ZArith.BinInt.Z.of_nat x.val = zOfInt (Int.ofNat x.val) by rfl,
    worker_word_val_repr]
  have hvalLt : Int.ofNat x.val < (2 ^ 64 : Int) := by
    change Int.ofNat x.val < Int.ofNat (2 ^ 64)
    exact Int.ofNat_lt.mpr x.toFin.isLt
  have hmod := Int.emod_eq_of_lt (Int.natCast_nonneg _) hvalLt
  exact (congrArg Int.toNat hmod).trans (by simp)

private theorem worker_int64_shru_zero
    (x : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.shru' x
        CompCert4Lean.Lib.Integers.Int.zero = x := by
  unfold CompCert4Lean.Lib.Integers.Int64.shru'
  change CompCert4Lean.Lib.Integers.Int64.repr
      (ZArith.BinInt.Z.shiftr
        (CompCert4Lean.Lib.Integers.Int64.unsigned x)
        (CompCert4Lean.Lib.Integers.Int.unsigned
          CompCert4Lean.Lib.Integers.Int.zero)) = x
  have hz : CompCert4Lean.Lib.Integers.Int.unsigned
      CompCert4Lean.Lib.Integers.Int.zero = Numbers.BinNums.Z.Z0 := by rfl
  rw [hz]
  unfold ZArith.BinInt.Z.shiftr
  rw [if_pos (show (0 : Int) ≤ intOfZ Numbers.BinNums.Z.Z0 by
    change (0 : Int) ≤ 0
    exact Int.le_refl _)]
  rw [show intOfZ Numbers.BinNums.Z.Z0 = 0 by rfl]
  change CompCert4Lean.Lib.Integers.Int64.repr
      (zOfInt (Int.ediv (intOfZ
        (CompCert4Lean.Lib.Integers.Int64.unsigned x)) 1)) = x
  rw [show Int.ediv (intOfZ
      (CompCert4Lean.Lib.Integers.Int64.unsigned x)) 1 =
      intOfZ (CompCert4Lean.Lib.Integers.Int64.unsigned x) by
    exact Int.ediv_one _]
  rw [zOfInt_intOfZ]
  exact worker_int64_repr_unsigned x

set_option maxHeartbeats 1000000 in
theorem make_shrluimm_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @make_shrluimm_correctStatement binary64_certificate binary32_certificate := by
  intro ge sp e m n r1 r2 h
  dsimp [CompCert4Lean.X86.ConstpropOp.make_shrluimm]
  split <;> rename_i hzero
  · have hn : n = CompCert4Lean.Lib.Integers.Int.zero := by
      apply CompCert4Lean.Lib.Integers.WordCore.ext
      have hd : decide (n.intval =
          CompCert4Lean.Lib.Integers.Int.zero.intval) = true := by
        simpa [CompCert4Lean.Lib.Integers.Int.eq,
          CompCert4Lean.Lib.Integers.WordCore.eq] using hzero
      exact of_decide_eq_true hd
    subst n
    refine ⟨CompCert4Lean.Backend.Registers.Regmap.get r1 e, ?_, ?_⟩
    · rfl
    · cases hr : CompCert4Lean.Backend.Registers.Regmap.get r1 e with
      | Vundef =>
          simp [CompCert4Lean.Common.Values.Val.shrlu]
          exact CompCert4Lean.Common.Values.Val.lessdef_refl _
      | Vint i =>
          simp [CompCert4Lean.Common.Values.Val.shrlu]
          exact CompCert4Lean.Common.Values.Val.lessdef_undef _
      | Vlong i =>
          change CompCert4Lean.Common.Values.Val.lessdef
            (.Vlong (CompCert4Lean.Lib.Integers.Int64.shru' i
              CompCert4Lean.Lib.Integers.Int.zero)) (.Vlong i)
          rw [worker_int64_shru_zero]
          exact CompCert4Lean.Common.Values.Val.lessdef_refl _
      | Vfloat f =>
          simp [CompCert4Lean.Common.Values.Val.shrlu]
          exact CompCert4Lean.Common.Values.Val.lessdef_undef _
      | Vsingle f =>
          simp [CompCert4Lean.Common.Values.Val.shrlu]
          exact CompCert4Lean.Common.Values.Val.lessdef_undef _
      | Vptr b ofs =>
          simp [CompCert4Lean.Common.Values.Val.shrlu]
          exact CompCert4Lean.Common.Values.Val.lessdef_undef _
  · split <;> rename_i hlt
    · refine ⟨CompCert4Lean.Common.Values.Val.shrlu
        (CompCert4Lean.Backend.Registers.Regmap.get r1 e) (.Vint n), ?_⟩
      constructor
      · rfl
      · exact CompCert4Lean.Common.Values.Val.lessdef_refl _
    · refine ⟨CompCert4Lean.Common.Values.Val.shrlu
        (CompCert4Lean.Backend.Registers.Regmap.get r1 e)
        (CompCert4Lean.Backend.Registers.Regmap.get r2 e), ?_⟩
      constructor
      · rfl
      · rw [h]
        exact CompCert4Lean.Common.Values.Val.lessdef_refl _

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.ConstpropOp

private theorem worker_int64_eq_true (x y : CompCert4Lean.Lib.Integers.Int64.int)
    (h : CompCert4Lean.Lib.Integers.Int64.eq x y = true) : x = y := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext
  have hd : decide (x.intval = y.intval) = true := by
    simpa [CompCert4Lean.Lib.Integers.Int64.eq,
      CompCert4Lean.Lib.Integers.WordCore.eq] using h
  exact of_decide_eq_true hd

private theorem worker_int_ltu_repr_64 (p : Z)
    (hp : ZArith.BinInt.Z.le Z0 p ∧ ZArith.BinInt.Z.lt p (zOfNat 64)) :
    CompCert4Lean.Lib.Integers.Int.ltu (CompCert4Lean.Lib.Integers.Int.repr p)
      CompCert4Lean.Lib.Integers.Int64.iwordsize' = true := by
  have hpmax : ZArith.BinInt.Z.le p CompCert4Lean.Lib.Integers.Int.max_unsigned := by
    change intOfZ p ≤ 2 ^ 32 - 1
    have h := hp.2
    change intOfZ p < 64 at h
    omega
  have hu : CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int.repr p) = p :=
    CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api p ⟨hp.1, hpmax⟩
  have hi : CompCert4Lean.Lib.Integers.Int.unsigned
      CompCert4Lean.Lib.Integers.Int64.iwordsize' = zOfNat 64 := by
    unfold CompCert4Lean.Lib.Integers.Int64.iwordsize'
    apply CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api
    constructor
    · change (0 : Int) ≤ 64
      omega
    · change (64 : Int) ≤ 2 ^ 32 - 1
      omega
  have hrev : CompCert4Lean.Lib.Integers.Int.ltu
      CompCert4Lean.Lib.Integers.Int64.iwordsize'
      (CompCert4Lean.Lib.Integers.Int.repr p) = false := by
    cases hval : CompCert4Lean.Lib.Integers.Int.ltu
        CompCert4Lean.Lib.Integers.Int64.iwordsize'
        (CompCert4Lean.Lib.Integers.Int.repr p) with
    | false => rfl
    | true =>
        have hr := CompCert4Lean.Lib.Integers.Int.ltu_inv_proof
          CompCert4Lean.Lib.Integers.Int64.iwordsize'
          (CompCert4Lean.Lib.Integers.Int.repr p) hval
        rw [hi, hu] at hr
        have hge := hr.2
        have hlt := hp.2
        change intOfZ (zOfNat 64) < intOfZ p at hge
        change intOfZ p < intOfZ (zOfNat 64) at hlt
        omega
  have hneq : CompCert4Lean.Lib.Integers.Int.repr p ≠
      CompCert4Lean.Lib.Integers.Int64.iwordsize' := by
    intro h
    have he := congrArg CompCert4Lean.Lib.Integers.Int.unsigned h
    rw [hu, hi] at he
    have hlt := hp.2
    change intOfZ p < intOfZ (zOfNat 64) at hlt
    rw [he] at hlt
    exact (Int.lt_irrefl _ hlt).elim
  have hvalneq : (CompCert4Lean.Lib.Integers.Int.repr p).intval ≠
      CompCert4Lean.Lib.Integers.Int64.iwordsize'.intval := by
    intro h
    exact hneq (CompCert4Lean.Lib.Integers.WordCore.ext h)
  have heq : CompCert4Lean.Lib.Integers.Int.eq
      (CompCert4Lean.Lib.Integers.Int.repr p)
      CompCert4Lean.Lib.Integers.Int64.iwordsize' = false := by
    unfold CompCert4Lean.Lib.Integers.Int.eq CompCert4Lean.Lib.Integers.WordCore.eq
    simp [hvalneq]
  have hnot := CompCert4Lean.Lib.Integers.Int.not_ltu_proof
    (CompCert4Lean.Lib.Integers.Int.repr p)
    CompCert4Lean.Lib.Integers.Int64.iwordsize'
  rw [hrev, heq] at hnot
  simpa using hnot.symm

private theorem worker_int64_is_power2'_correct
    (n : CompCert4Lean.Lib.Integers.Int64.int)
    (logn : CompCert4Lean.Lib.Integers.Int.int)
    (hpow : CompCert4Lean.Lib.Integers.Int64.is_power2' n = some logn) :
    CompCert4Lean.Lib.Integers.Int64.unsigned n =
      two_p (CompCert4Lean.Lib.Integers.Int.unsigned logn) := by
  unfold CompCert4Lean.Lib.Integers.Int64.is_power2' at hpow
  generalize hbits : CompCert4Lean.Lib.Zbits.Z_one_bits
      CompCert4Lean.Lib.Integers.Int64.wordsize
      (CompCert4Lean.Lib.Integers.Int64.unsigned n) Z0 = bits at hpow
  cases bits with
  | nil => simp at hpow
  | cons i rest =>
      cases rest with
      | nil =>
          simp only at hpow
          cases hpow
          have hirange := CompCert4Lean.Lib.Zbits.Z_one_bits_range
            CompCert4Lean.Lib.Integers.Int64.wordsize
            (CompCert4Lean.Lib.Integers.Int64.unsigned n) i
            (by rw [hbits]; simp)
          have himax : ZArith.BinInt.Z.le i
              CompCert4Lean.Lib.Integers.Int.max_unsigned := by
            have hlt := hirange.2
            change intOfZ i < 64 at hlt
            change intOfZ i ≤ 2 ^ 32 - 1
            omega
          have hi : CompCert4Lean.Lib.Integers.Int.unsigned
              (CompCert4Lean.Lib.Integers.Int.repr i) = i :=
            CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api i
              ⟨hirange.1, himax⟩
          rw [hi]
          have hn0 : ZArith.BinInt.Z.le Z0
              (CompCert4Lean.Lib.Integers.Int64.unsigned n) := by
            have h := n.intrange.1
            change (-1 : Int) < intOfZ n.intval at h
            change 0 ≤ intOfZ n.intval
            omega
          have hnrange : ZArith.BinInt.Z.le Z0
                (CompCert4Lean.Lib.Integers.Int64.unsigned n) ∧
              ZArith.BinInt.Z.lt (CompCert4Lean.Lib.Integers.Int64.unsigned n)
                CompCert4Lean.Lib.Integers.Int64.modulus :=
            ⟨hn0, n.intrange.2⟩
          have hseries := CompCert4Lean.Lib.Zbits.Z_one_bits_powerserie
            CompCert4Lean.Lib.Integers.Int64.wordsize
            (CompCert4Lean.Lib.Integers.Int64.unsigned n) hnrange
          rw [hbits] at hseries
          rw [hseries]
          apply intOfZ_injective
          simp only [CompCert4Lean.Lib.Zbits.powerserie, ZArith.BinInt.Z.add,
            intOfZ_zOfInt]
          change intOfZ (two_p i) + 0 = intOfZ (two_p i)
          omega
      | cons j rest => simp at hpow

private theorem worker_int64_is_power2'_range
    (n : CompCert4Lean.Lib.Integers.Int64.int)
    (logn : CompCert4Lean.Lib.Integers.Int.int)
    (hpow : CompCert4Lean.Lib.Integers.Int64.is_power2' n = some logn) :
    CompCert4Lean.Lib.Integers.Int.ltu logn
      CompCert4Lean.Lib.Integers.Int64.iwordsize' = true := by
  unfold CompCert4Lean.Lib.Integers.Int64.is_power2' at hpow
  generalize hbits : CompCert4Lean.Lib.Zbits.Z_one_bits
      CompCert4Lean.Lib.Integers.Int64.wordsize
      (CompCert4Lean.Lib.Integers.Int64.unsigned n) Z0 = bits at hpow
  cases bits with
  | nil => simp at hpow
  | cons i rest =>
      cases rest with
      | nil =>
          simp only at hpow
          cases hpow
          apply worker_int_ltu_repr_64
          exact CompCert4Lean.Lib.Zbits.Z_one_bits_range
            CompCert4Lean.Lib.Integers.Int64.wordsize
            (CompCert4Lean.Lib.Integers.Int64.unsigned n) i
            (by rw [hbits]; simp)
      | cons j rest => simp at hpow

private theorem worker_int64_mul_pow2
    (x n : CompCert4Lean.Lib.Integers.Int64.int)
    (logn : CompCert4Lean.Lib.Integers.Int.int)
    (hpow : CompCert4Lean.Lib.Integers.Int64.is_power2' n = some logn) :
    CompCert4Lean.Lib.Integers.Int64.mul x n =
      CompCert4Lean.Lib.Integers.Int64.shl' x logn := by
  have hc := worker_int64_is_power2'_correct n logn hpow
  have hc' : CompCert4Lean.Lib.Integers.WordCore.unsigned n =
      two_p (CompCert4Lean.Lib.Integers.Int.unsigned logn) := hc
  unfold CompCert4Lean.Lib.Integers.Int64.mul
    CompCert4Lean.Lib.Integers.WordCore.mul
    CompCert4Lean.Lib.Integers.Int64.shl'
  rw [hc']
  change CompCert4Lean.Lib.Integers.WordCore.repr
      CompCert4Lean.Lib.Integers.Int64.wordsize
      (ZArith.BinInt.Z.mul
        (CompCert4Lean.Lib.Integers.Int64.unsigned x)
        (two_p (CompCert4Lean.Lib.Integers.Int.unsigned logn))) =
    CompCert4Lean.Lib.Integers.WordCore.repr
      CompCert4Lean.Lib.Integers.Int64.wordsize
      (ZArith.BinInt.Z.shiftl
        (CompCert4Lean.Lib.Integers.Int64.unsigned x)
        (CompCert4Lean.Lib.Integers.Int.unsigned logn))
  rw [ZArith.BinInt.Z.shiftl_mul_pow2
    (CompCert4Lean.Lib.Integers.Int64.unsigned x)
    (CompCert4Lean.Lib.Integers.Int.unsigned logn) (by
      have h := logn.intrange.1
      change (-1 : Int) < intOfZ logn.intval at h
      change 0 ≤ intOfZ logn.intval
      omega)]
  rfl

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.ConstpropOp

private theorem worker_int64_mul_zero (x : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.mul x
        CompCert4Lean.Lib.Integers.Int64.zero =
      CompCert4Lean.Lib.Integers.Int64.zero := by
  unfold CompCert4Lean.Lib.Integers.Int64.mul
    CompCert4Lean.Lib.Integers.WordCore.mul
  rw [show CompCert4Lean.Lib.Integers.WordCore.unsigned
      CompCert4Lean.Lib.Integers.Int64.zero = Z0 by rfl]
  have hz : ZArith.BinInt.Z.mul
      (CompCert4Lean.Lib.Integers.WordCore.unsigned x) Z0 = Z0 := by
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    simp [intOfZ]
  change CompCert4Lean.Lib.Integers.WordCore.repr
      CompCert4Lean.Lib.Integers.Int64.wordsize
      (ZArith.BinInt.Z.mul
        (CompCert4Lean.Lib.Integers.WordCore.unsigned x) Z0) =
    CompCert4Lean.Lib.Integers.Int64.zero
  rw [hz]
  rfl

private theorem worker_int64_mul_one (x : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.mul x
        CompCert4Lean.Lib.Integers.Int64.one = x := by
  unfold CompCert4Lean.Lib.Integers.Int64.mul
    CompCert4Lean.Lib.Integers.WordCore.mul
  rw [show CompCert4Lean.Lib.Integers.WordCore.unsigned
      CompCert4Lean.Lib.Integers.Int64.one = Zpos xH by rfl]
  change CompCert4Lean.Lib.Integers.WordCore.repr
      CompCert4Lean.Lib.Integers.Int64.wordsize
      (ZArith.BinInt.Z.mul
        (CompCert4Lean.Lib.Integers.WordCore.unsigned x) (Zpos xH)) = x
  rw [ZArith.BinInt.Zmult_1_r_proof]
  exact worker_int64_repr_unsigned x

set_option maxHeartbeats 1000000 in
theorem make_mullimm_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @make_mullimm_correctStatement binary64_certificate binary32_certificate := by
  intro ge sp e m n r1
  dsimp [CompCert4Lean.X86.ConstpropOp.make_mullimm]
  split <;> rename_i hzero
  · have hn : n = CompCert4Lean.Lib.Integers.Int64.zero :=
      worker_int64_eq_true n CompCert4Lean.Lib.Integers.Int64.zero hzero
    subst n
    refine ⟨.Vlong CompCert4Lean.Lib.Integers.Int64.zero, ?_, ?_⟩
    · rfl
    · cases hr : CompCert4Lean.Backend.Registers.Regmap.get r1 e with
      | Vundef =>
          simp [CompCert4Lean.Common.Values.Val.mull]
          exact CompCert4Lean.Common.Values.Val.lessdef_undef _
      | Vint i =>
          simp [CompCert4Lean.Common.Values.Val.mull]
          exact CompCert4Lean.Common.Values.Val.lessdef_undef _
      | Vlong i =>
          change CompCert4Lean.Common.Values.Val.lessdef
            (.Vlong (CompCert4Lean.Lib.Integers.Int64.mul i
              CompCert4Lean.Lib.Integers.Int64.zero))
            (.Vlong CompCert4Lean.Lib.Integers.Int64.zero)
          rw [worker_int64_mul_zero]
          exact CompCert4Lean.Common.Values.Val.lessdef_refl _
      | Vfloat f =>
          simp [CompCert4Lean.Common.Values.Val.mull]
          exact CompCert4Lean.Common.Values.Val.lessdef_undef _
      | Vsingle f =>
          simp [CompCert4Lean.Common.Values.Val.mull]
          exact CompCert4Lean.Common.Values.Val.lessdef_undef _
      | Vptr b ofs =>
          simp [CompCert4Lean.Common.Values.Val.mull]
          exact CompCert4Lean.Common.Values.Val.lessdef_undef _
  · split <;> rename_i hone
    · have hn : n = CompCert4Lean.Lib.Integers.Int64.one :=
        worker_int64_eq_true n CompCert4Lean.Lib.Integers.Int64.one hone
      subst n
      refine ⟨CompCert4Lean.Backend.Registers.Regmap.get r1 e, ?_, ?_⟩
      · rfl
      · cases hr : CompCert4Lean.Backend.Registers.Regmap.get r1 e with
        | Vundef =>
            simp [CompCert4Lean.Common.Values.Val.mull]
            exact CompCert4Lean.Common.Values.Val.lessdef_refl _
        | Vint i =>
            simp [CompCert4Lean.Common.Values.Val.mull]
            exact CompCert4Lean.Common.Values.Val.lessdef_undef _
        | Vlong i =>
            change CompCert4Lean.Common.Values.Val.lessdef
              (.Vlong (CompCert4Lean.Lib.Integers.Int64.mul i
                CompCert4Lean.Lib.Integers.Int64.one)) (.Vlong i)
            rw [worker_int64_mul_one]
            exact CompCert4Lean.Common.Values.Val.lessdef_refl _
        | Vfloat f =>
            simp [CompCert4Lean.Common.Values.Val.mull]
            exact CompCert4Lean.Common.Values.Val.lessdef_undef _
        | Vsingle f =>
            simp [CompCert4Lean.Common.Values.Val.mull]
            exact CompCert4Lean.Common.Values.Val.lessdef_undef _
        | Vptr b ofs =>
            simp [CompCert4Lean.Common.Values.Val.mull]
            exact CompCert4Lean.Common.Values.Val.lessdef_undef _
    · cases hpow : CompCert4Lean.Lib.Integers.Int64.is_power2' n with
      | some l =>
          refine ⟨CompCert4Lean.Common.Values.Val.shll
            (CompCert4Lean.Backend.Registers.Regmap.get r1 e) (.Vint l), ?_, ?_⟩
          · rfl
          · cases hr : CompCert4Lean.Backend.Registers.Regmap.get r1 e with
            | Vundef =>
                simp [CompCert4Lean.Common.Values.Val.mull,
                  CompCert4Lean.Common.Values.Val.shll]
                exact CompCert4Lean.Common.Values.Val.lessdef_undef _
            | Vint i =>
                simp [CompCert4Lean.Common.Values.Val.mull,
                  CompCert4Lean.Common.Values.Val.shll]
                exact CompCert4Lean.Common.Values.Val.lessdef_undef _
            | Vlong i =>
                have hlt := worker_int64_is_power2'_range n l hpow
                simp only [CompCert4Lean.Common.Values.Val.mull,
                  CompCert4Lean.Common.Values.Val.shll, hlt, ↓reduceIte]
                change CompCert4Lean.Common.Values.Val.lessdef
                  (.Vlong (CompCert4Lean.Lib.Integers.Int64.mul i n))
                  (.Vlong (CompCert4Lean.Lib.Integers.Int64.shl' i l))
                rw [worker_int64_mul_pow2 i n l hpow]
                exact CompCert4Lean.Common.Values.Val.lessdef_refl _
            | Vfloat f =>
                simp [CompCert4Lean.Common.Values.Val.mull,
                  CompCert4Lean.Common.Values.Val.shll]
                exact CompCert4Lean.Common.Values.Val.lessdef_undef _
            | Vsingle f =>
                simp [CompCert4Lean.Common.Values.Val.mull,
                  CompCert4Lean.Common.Values.Val.shll]
                exact CompCert4Lean.Common.Values.Val.lessdef_undef _
            | Vptr b ofs =>
                simp [CompCert4Lean.Common.Values.Val.mull,
                  CompCert4Lean.Common.Values.Val.shll]
                exact CompCert4Lean.Common.Values.Val.lessdef_undef _
      | none =>
          refine ⟨CompCert4Lean.Common.Values.Val.mull
            (CompCert4Lean.Backend.Registers.Regmap.get r1 e) (.Vlong n), ?_,
            CompCert4Lean.Common.Values.Val.lessdef_refl _⟩
          rfl

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.ConstpropOp

private theorem worker_int64_one_mul (x : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.mul
        CompCert4Lean.Lib.Integers.Int64.one x = x := by
  unfold CompCert4Lean.Lib.Integers.Int64.mul
    CompCert4Lean.Lib.Integers.WordCore.mul
  rw [show CompCert4Lean.Lib.Integers.WordCore.unsigned
      CompCert4Lean.Lib.Integers.Int64.one = Zpos xH by rfl]
  change CompCert4Lean.Lib.Integers.WordCore.repr
      CompCert4Lean.Lib.Integers.Int64.wordsize
      (ZArith.BinInt.Z.mul (Zpos xH)
        (CompCert4Lean.Lib.Integers.WordCore.unsigned x)) = x
  rw [ZArith.BinInt.Zmult_1_l_proof]
  exact worker_int64_repr_unsigned x

private theorem worker_int64_divs_pow2
    (x n : CompCert4Lean.Lib.Integers.Int64.int)
    (logn : CompCert4Lean.Lib.Integers.Int.int)
    (hpow : CompCert4Lean.Lib.Integers.Int64.is_power2' n = some logn) :
    CompCert4Lean.Lib.Integers.Int64.divs x n =
      CompCert4Lean.Lib.Integers.Int64.shrx' x logn := by
  unfold CompCert4Lean.Lib.Integers.Int64.shrx'
  rw [← worker_int64_mul_pow2 CompCert4Lean.Lib.Integers.Int64.one n logn hpow]
  rw [worker_int64_one_mul]

private theorem worker_val_divls_pow2
    (x : CompCert4Lean.Common.Values.val)
    (n : CompCert4Lean.Lib.Integers.Int64.int)
    (logn : CompCert4Lean.Lib.Integers.Int.int)
    (y : CompCert4Lean.Common.Values.val)
    (hpow : CompCert4Lean.Lib.Integers.Int64.is_power2' n = some logn)
    (hlt : CompCert4Lean.Lib.Integers.Int.ltu logn
      (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 63)) = true)
    (hdiv : CompCert4Lean.Common.Values.Val.divls x (.Vlong n) = some y) :
    CompCert4Lean.Common.Values.Val.shrxl x (.Vint logn) = some y := by
  cases x with
  | Vlong i =>
      simp only [CompCert4Lean.Common.Values.Val.divls] at hdiv
      split at hdiv
      · cases hdiv
      · cases hdiv
        simp only [CompCert4Lean.Common.Values.Val.shrxl, hlt, if_true,
          Option.some.injEq, val.Vlong.injEq]
        exact (worker_int64_divs_pow2 i n logn hpow).symm
  | Vundef => simp [CompCert4Lean.Common.Values.Val.divls] at hdiv
  | Vint i => simp [CompCert4Lean.Common.Values.Val.divls] at hdiv
  | Vfloat f => simp [CompCert4Lean.Common.Values.Val.divls] at hdiv
  | Vsingle f => simp [CompCert4Lean.Common.Values.Val.divls] at hdiv
  | Vptr b ofs => simp [CompCert4Lean.Common.Values.Val.divls] at hdiv

theorem make_divlimm_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @make_divlimm_correctStatement binary64_certificate binary32_certificate := by
  intro ge sp e m n r1 r2 v hdiv hr2
  have hdivn : CompCert4Lean.Common.Values.Val.divls
      (CompCert4Lean.Backend.Registers.Regmap.get r1 e) (.Vlong n) = some v := by
    rw [← hr2]
    exact hdiv
  unfold CompCert4Lean.X86.ConstpropOp.make_divlimm
  cases hpow : CompCert4Lean.Lib.Integers.Int64.is_power2' n with
  | none =>
      simp only
      refine ⟨v, ?_, CompCert4Lean.Common.Values.Val.lessdef_refl _⟩
      change CompCert4Lean.Common.Values.Val.divls
        (CompCert4Lean.Backend.Registers.Regmap.get r1 e)
        (CompCert4Lean.Backend.Registers.Regmap.get r2 e) = some v
      exact hdiv
  | some logn =>
      simp only
      split <;> rename_i hlt
      · refine ⟨v, ?_, CompCert4Lean.Common.Values.Val.lessdef_refl _⟩
        change CompCert4Lean.Common.Values.Val.shrxl
          (CompCert4Lean.Backend.Registers.Regmap.get r1 e) (.Vint logn) = some v
        exact worker_val_divls_pow2
          (CompCert4Lean.Backend.Registers.Regmap.get r1 e) n logn v hpow hlt hdivn
      · refine ⟨v, ?_, CompCert4Lean.Common.Values.Val.lessdef_refl _⟩
        change CompCert4Lean.Common.Values.Val.divls
          (CompCert4Lean.Backend.Registers.Regmap.get r1 e)
          (CompCert4Lean.Backend.Registers.Regmap.get r2 e) = some v
        exact hdiv

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.ConstpropOp

private theorem worker_int64_mone_val :
    CompCert4Lean.Lib.Integers.Int64.mone.val = 2 ^ 64 - 1 := by
  unfold CompCert4Lean.Lib.Integers.Int64.mone
    CompCert4Lean.Lib.Integers.WordCore.mone
  change (CompCert4Lean.Lib.Integers.WordCore.repr
    CompCert4Lean.Lib.Integers.Int64.wordsize (zOfInt (-1))).val =
      2 ^ 64 - 1
  rw [cp_suffixWordValRepr64]
  decide

private theorem worker_int64_zOfNat_val
    (x : CompCert4Lean.Lib.Integers.Int64.int) :
    zOfNat x.val = CompCert4Lean.Lib.Integers.Int64.unsigned x := by
  have hx0 : ZArith.BinInt.Z.le .Z0 x.intval := by
    have h := x.intrange.1
    change (-1 : Int) < intOfZ x.intval at h
    change 0 ≤ intOfZ x.intval
    omega
  exact ZArith.Znat.Z2Nat.id x.intval hx0

private theorem worker_int64_and_zero
    (x : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.and x
        CompCert4Lean.Lib.Integers.Int64.zero =
      CompCert4Lean.Lib.Integers.Int64.zero := by
  unfold CompCert4Lean.Lib.Integers.Int64.and
    CompCert4Lean.Lib.Integers.WordCore.and
  change CompCert4Lean.Lib.Integers.Int64.repr
      (zOfNat (Nat.land x.val CompCert4Lean.Lib.Integers.Int64.zero.val)) =
    CompCert4Lean.Lib.Integers.Int64.zero
  rw [show CompCert4Lean.Lib.Integers.Int64.zero.val = 0 by rfl]
  rw [show Nat.land x.val 0 = 0 by
    simpa only [Nat.land_eq] using Nat.and_zero x.val]
  rfl

private theorem worker_int64_and_mone
    (x : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.and x
        CompCert4Lean.Lib.Integers.Int64.mone = x := by
  unfold CompCert4Lean.Lib.Integers.Int64.and
    CompCert4Lean.Lib.Integers.WordCore.and
  change CompCert4Lean.Lib.Integers.Int64.repr
      (zOfNat (Nat.land x.val CompCert4Lean.Lib.Integers.Int64.mone.val)) = x
  rw [worker_int64_mone_val]
  rw [Nat.land_eq,
    Nat.and_two_pow_sub_one_of_lt_two_pow (n := 64) (x := x.val) x.toFin.isLt]
  change CompCert4Lean.Lib.Integers.Int64.repr (zOfNat x.val) = x
  rw [worker_int64_zOfNat_val]
  exact worker_int64_repr_unsigned x

private theorem worker_int64_or_zero
    (x : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.or x
        CompCert4Lean.Lib.Integers.Int64.zero = x := by
  unfold CompCert4Lean.Lib.Integers.Int64.or
    CompCert4Lean.Lib.Integers.WordCore.or
  change CompCert4Lean.Lib.Integers.Int64.repr
      (zOfNat (Nat.lor x.val CompCert4Lean.Lib.Integers.Int64.zero.val)) = x
  rw [show CompCert4Lean.Lib.Integers.Int64.zero.val = 0 by rfl]
  rw [show Nat.lor x.val 0 = x.val by
    simpa only [Nat.lor_eq] using Nat.or_zero x.val]
  change CompCert4Lean.Lib.Integers.Int64.repr (zOfNat x.val) = x
  rw [worker_int64_zOfNat_val]
  exact worker_int64_repr_unsigned x

private theorem worker_int64_or_mone
    (x : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.or x
        CompCert4Lean.Lib.Integers.Int64.mone =
      CompCert4Lean.Lib.Integers.Int64.mone := by
  unfold CompCert4Lean.Lib.Integers.Int64.or
    CompCert4Lean.Lib.Integers.WordCore.or
  change CompCert4Lean.Lib.Integers.Int64.repr
      (zOfNat (Nat.lor x.val CompCert4Lean.Lib.Integers.Int64.mone.val)) =
    CompCert4Lean.Lib.Integers.Int64.mone
  rw [worker_int64_mone_val]
  have hor : Nat.lor x.val (2 ^ 64 - 1) = 2 ^ 64 - 1 := by
    rw [Nat.lor_eq]
    apply Nat.le_antisymm
    · have hlt : x.val ||| (2 ^ 64 - 1) < 2 ^ 64 :=
        Nat.or_lt_two_pow x.toFin.isLt (by omega)
      omega
    · exact Nat.right_le_or
  rw [hor]
  change CompCert4Lean.Lib.Integers.Int64.repr (zOfNat (2 ^ 64 - 1)) =
    CompCert4Lean.Lib.Integers.Int64.mone
  rw [← worker_int64_mone_val, worker_int64_zOfNat_val]
  exact worker_int64_repr_unsigned CompCert4Lean.Lib.Integers.Int64.mone

theorem make_andlimm_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @make_andlimm_correctStatement binary64_certificate binary32_certificate := by
  intro ge sp e m n r x
  dsimp [CompCert4Lean.X86.ConstpropOp.make_andlimm]
  split <;> rename_i hzero
  · have hn : n = CompCert4Lean.Lib.Integers.Int64.zero :=
      worker_int64_eq_true n CompCert4Lean.Lib.Integers.Int64.zero hzero
    subst n
    refine ⟨.Vlong CompCert4Lean.Lib.Integers.Int64.zero, ?_, ?_⟩
    · rfl
    · cases CompCert4Lean.Backend.Registers.Regmap.get r e with
      | Vlong i =>
          change CompCert4Lean.Common.Values.Val.lessdef
            (.Vlong (CompCert4Lean.Lib.Integers.Int64.and i
              CompCert4Lean.Lib.Integers.Int64.zero))
            (.Vlong CompCert4Lean.Lib.Integers.Int64.zero)
          rw [worker_int64_and_zero]
          exact CompCert4Lean.Common.Values.Val.lessdef_refl _
      | _ => exact CompCert4Lean.Common.Values.Val.lessdef_undef _
  · split <;> rename_i hmone
    · have hn : n = CompCert4Lean.Lib.Integers.Int64.mone :=
        worker_int64_eq_true n CompCert4Lean.Lib.Integers.Int64.mone hmone
      subst n
      refine ⟨CompCert4Lean.Backend.Registers.Regmap.get r e, ?_, ?_⟩
      · rfl
      · cases CompCert4Lean.Backend.Registers.Regmap.get r e with
        | Vlong i =>
            change CompCert4Lean.Common.Values.Val.lessdef
              (.Vlong (CompCert4Lean.Lib.Integers.Int64.and i
                CompCert4Lean.Lib.Integers.Int64.mone)) (.Vlong i)
            rw [worker_int64_and_mone]
            exact CompCert4Lean.Common.Values.Val.lessdef_refl _
        | _ => exact CompCert4Lean.Common.Values.Val.lessdef_undef _
    · refine ⟨CompCert4Lean.Common.Values.Val.andl
          (CompCert4Lean.Backend.Registers.Regmap.get r e) (.Vlong n), ?_,
          CompCert4Lean.Common.Values.Val.lessdef_refl _⟩
      rfl

theorem make_orlimm_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @make_orlimm_correctStatement binary64_certificate binary32_certificate := by
  intro ge sp e m n r
  dsimp [CompCert4Lean.X86.ConstpropOp.make_orlimm]
  split <;> rename_i hzero
  · have hn : n = CompCert4Lean.Lib.Integers.Int64.zero :=
      worker_int64_eq_true n CompCert4Lean.Lib.Integers.Int64.zero hzero
    subst n
    refine ⟨CompCert4Lean.Backend.Registers.Regmap.get r e, ?_, ?_⟩
    · rfl
    · cases CompCert4Lean.Backend.Registers.Regmap.get r e with
      | Vlong i =>
          change CompCert4Lean.Common.Values.Val.lessdef
            (.Vlong (CompCert4Lean.Lib.Integers.Int64.or i
              CompCert4Lean.Lib.Integers.Int64.zero)) (.Vlong i)
          rw [worker_int64_or_zero]
          exact CompCert4Lean.Common.Values.Val.lessdef_refl _
      | _ => exact CompCert4Lean.Common.Values.Val.lessdef_undef _
  · split <;> rename_i hmone
    · have hn : n = CompCert4Lean.Lib.Integers.Int64.mone :=
        worker_int64_eq_true n CompCert4Lean.Lib.Integers.Int64.mone hmone
      subst n
      refine ⟨.Vlong CompCert4Lean.Lib.Integers.Int64.mone, ?_, ?_⟩
      · rfl
      · cases CompCert4Lean.Backend.Registers.Regmap.get r e with
        | Vlong i =>
            change CompCert4Lean.Common.Values.Val.lessdef
              (.Vlong (CompCert4Lean.Lib.Integers.Int64.or i
                CompCert4Lean.Lib.Integers.Int64.mone))
              (.Vlong CompCert4Lean.Lib.Integers.Int64.mone)
            rw [worker_int64_or_mone]
            exact CompCert4Lean.Common.Values.Val.lessdef_refl _
        | _ => exact CompCert4Lean.Common.Values.Val.lessdef_undef _
    · refine ⟨CompCert4Lean.Common.Values.Val.orl
          (CompCert4Lean.Backend.Registers.Regmap.get r e) (.Vlong n), ?_,
          CompCert4Lean.Common.Values.Val.lessdef_refl _⟩
      rfl

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.ConstpropOp

private theorem worker_zshiftr_div_two_p (x y : Z)
    (hy : ZArith.BinInt.Z.le Z0 y) :
    ZArith.BinInt.Z.shiftr x y = ZArith.BinInt.Z.div x (two_p y) := by
  change 0 ≤ intOfZ y at hy
  have hpow : intOfZ (two_p y) =
      Int.pow 2 (Int.toNat (intOfZ y)) := by
    unfold two_p ZArith.Zpower.two_p ZArith.BinInt.Z.pow
    rw [if_neg (by omega)]
    simp only [intOfZ_zOfInt]
    have hbase : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
    rw [hbase]
  apply intOfZ_injective
  simp [ZArith.BinInt.Z.shiftr, ZArith.BinInt.Z.div, hy]
  rw [intOfZ_zOfInt, intOfZ_zOfInt, hpow]
  change Int.ediv (intOfZ x) (Int.pow 2 (Int.toNat (intOfZ y))) =
    (if Int.pow 2 (Int.toNat (intOfZ y)) = 0 then 0
      else if 0 < Int.pow 2 (Int.toNat (intOfZ y)) then
        Int.ediv (intOfZ x) (Int.pow 2 (Int.toNat (intOfZ y)))
      else
        let d := -(Int.pow 2 (Int.toNat (intOfZ y)))
        let q := Int.ediv (intOfZ x) d
        let r := Int.emod (intOfZ x) d
        if r = 0 then -q else -(q + 1))
  have hp : 0 < Int.pow 2 (Int.toNat (intOfZ y)) :=
    Int.pow_pos (by omega)
  simp [hp, Int.ne_of_gt hp]

private theorem worker_int64_shru'_div_two_p
    (x : CompCert4Lean.Lib.Integers.Int64.int)
    (y : CompCert4Lean.Lib.Integers.Int.int) :
    CompCert4Lean.Lib.Integers.Int64.shru' x y =
      CompCert4Lean.Lib.Integers.Int64.repr
        (ZArith.BinInt.Z.div (CompCert4Lean.Lib.Integers.Int64.unsigned x)
          (two_p (CompCert4Lean.Lib.Integers.Int.unsigned y))) := by
  unfold CompCert4Lean.Lib.Integers.Int64.shru'
  change CompCert4Lean.Lib.Integers.Int64.repr
      (ZArith.BinInt.Z.shiftr
        (CompCert4Lean.Lib.Integers.Int64.unsigned x)
        (CompCert4Lean.Lib.Integers.Int.unsigned y)) = _
  rw [worker_zshiftr_div_two_p]
  have h := y.intrange.1
  change (-1 : Int) < intOfZ y.intval at h
  change 0 ≤ intOfZ y.intval
  omega

private theorem worker_int64_divu_pow2
    (x n : CompCert4Lean.Lib.Integers.Int64.int)
    (logn : CompCert4Lean.Lib.Integers.Int.int)
    (hpow : CompCert4Lean.Lib.Integers.Int64.is_power2' n = some logn) :
    CompCert4Lean.Lib.Integers.Int64.divu x n =
      CompCert4Lean.Lib.Integers.Int64.shru' x logn := by
  have hc := worker_int64_is_power2'_correct n logn hpow
  unfold CompCert4Lean.Lib.Integers.Int64.divu
    CompCert4Lean.Lib.Integers.WordCore.divu
  change CompCert4Lean.Lib.Integers.Int64.repr
      (ZArith.BinInt.Z.div
        (CompCert4Lean.Lib.Integers.Int64.unsigned x)
        (CompCert4Lean.Lib.Integers.Int64.unsigned n)) =
    CompCert4Lean.Lib.Integers.Int64.shru' x logn
  rw [hc, worker_int64_shru'_div_two_p]

private theorem worker_val_divlu_pow2
    (x : CompCert4Lean.Common.Values.val)
    (n : CompCert4Lean.Lib.Integers.Int64.int)
    (logn : CompCert4Lean.Lib.Integers.Int.int)
    (y : CompCert4Lean.Common.Values.val)
    (hpow : CompCert4Lean.Lib.Integers.Int64.is_power2' n = some logn)
    (hdiv : CompCert4Lean.Common.Values.Val.divlu x (.Vlong n) = some y) :
    CompCert4Lean.Common.Values.Val.shrlu x (.Vint logn) = y := by
  cases x with
  | Vlong i =>
      simp only [CompCert4Lean.Common.Values.Val.divlu] at hdiv
      split at hdiv
      · cases hdiv
      · cases hdiv
        simp only [CompCert4Lean.Common.Values.Val.shrlu,
          worker_int64_is_power2'_range n logn hpow, if_true,
          val.Vlong.injEq]
        exact (worker_int64_divu_pow2 i n logn hpow).symm
  | Vundef => simp [CompCert4Lean.Common.Values.Val.divlu] at hdiv
  | Vint i => simp [CompCert4Lean.Common.Values.Val.divlu] at hdiv
  | Vfloat f => simp [CompCert4Lean.Common.Values.Val.divlu] at hdiv
  | Vsingle f => simp [CompCert4Lean.Common.Values.Val.divlu] at hdiv
  | Vptr b ofs => simp [CompCert4Lean.Common.Values.Val.divlu] at hdiv

theorem make_divluimm_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @make_divluimm_correctStatement binary64_certificate binary32_certificate := by
  intro ge sp e m n r1 r2 v hdiv hr2
  have hdivn : CompCert4Lean.Common.Values.Val.divlu
      (CompCert4Lean.Backend.Registers.Regmap.get r1 e) (.Vlong n) = some v := by
    rw [← hr2]
    exact hdiv
  unfold CompCert4Lean.X86.ConstpropOp.make_divluimm
  cases hpow : CompCert4Lean.Lib.Integers.Int64.is_power2' n with
  | none =>
      refine ⟨v, ?_, CompCert4Lean.Common.Values.Val.lessdef_refl _⟩
      change CompCert4Lean.Common.Values.Val.divlu
        (CompCert4Lean.Backend.Registers.Regmap.get r1 e)
        (CompCert4Lean.Backend.Registers.Regmap.get r2 e) = some v
      exact hdiv
  | some logn =>
      refine ⟨v, ?_, CompCert4Lean.Common.Values.Val.lessdef_refl _⟩
      change some (CompCert4Lean.Common.Values.Val.shrlu
        (CompCert4Lean.Backend.Registers.Regmap.get r1 e) (.Vint logn)) = some v
      exact congrArg some (worker_val_divlu_pow2
        (CompCert4Lean.Backend.Registers.Regmap.get r1 e) n logn v hpow hdivn)

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers
open Lean Elab Tactic Meta

private theorem worker_positive_is_power2
    (p : positive) (h : CompCert4Lean.Lib.Zbits.P_is_power2 p = true) :
    ∃ k : Nat, posToNat p = 2 ^ k := by
  induction p with
  | xH => exact ⟨0, rfl⟩
  | xI p ih => simp [CompCert4Lean.Lib.Zbits.P_is_power2] at h
  | xO p ih =>
      rcases ih h with ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      rw [posToNat, hk, Nat.pow_succ]
      omega

private theorem worker_int64_is_power2_nat
    (n logn : CompCert4Lean.Lib.Integers.Int64.int)
    (hpow : CompCert4Lean.Lib.Integers.Int64.is_power2 n = some logn) :
    ∃ k : Nat, n.val = 2 ^ k := by
  unfold CompCert4Lean.Lib.Integers.Int64.is_power2 at hpow
  cases hu : CompCert4Lean.Lib.Integers.Int64.unsigned n with
  | Z0 =>
      simp only [CompCert4Lean.Lib.Zbits.Z_is_power2, hu] at hpow
      cases hpow
  | Zneg p =>
      simp only [CompCert4Lean.Lib.Zbits.Z_is_power2, hu] at hpow
      cases hpow
  | Zpos p =>
      cases hp : CompCert4Lean.Lib.Zbits.P_is_power2 p with
      | false =>
          simp only [CompCert4Lean.Lib.Zbits.Z_is_power2, hu, hp,
            Bool.false_eq_true, ↓reduceIte] at hpow
          cases hpow
      | true =>
          rcases worker_positive_is_power2 p hp with ⟨k, hk⟩
          refine ⟨k, ?_⟩
          have hz := (worker_int64_zOfNat_val n).trans hu
          have hi : Int.ofNat n.val = Int.ofNat (posToNat p) := by
            calc
              Int.ofNat n.val = intOfZ (zOfNat n.val) := by
                exact (intOfZ_zOfInt (Int.ofNat n.val)).symm
              _ = intOfZ (Zpos p) := congrArg intOfZ hz
              _ = Int.ofNat (posToNat p) := rfl
          exact (Int.ofNat.inj hi).trans hk

private theorem worker_word_sub_val {bits : Nat}
    (x y : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    (CompCert4Lean.Lib.Integers.WordCore.sub x y).val =
      (2 ^ bits - y.val + x.val) % (2 ^ bits) := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let yF := (lctx.findFromUserName? `y).get!
    let e ← mkAppM
      (cp_suffixPrivateName "CompCert4Lean.Lib.Integers.WordCore.sub_val")
      #[mkFVar xF.fvarId, mkFVar yF.fvarId]
    closeMainGoal Name.anonymous e

private theorem worker_int64_sub_one_val
    (n : CompCert4Lean.Lib.Integers.Int64.int) (hnpos : 0 < n.val) :
    (CompCert4Lean.Lib.Integers.Int64.sub n
      CompCert4Lean.Lib.Integers.Int64.one).val = n.val - 1 := by
  change (CompCert4Lean.Lib.Integers.WordCore.sub n
      CompCert4Lean.Lib.Integers.Int64.one).val = n.val - 1
  rw [worker_word_sub_val]
  change (2 ^ 64 - 1 + n.val) % (2 ^ 64) = n.val - 1
  have hnlt : n.val < 2 ^ 64 := n.toFin.isLt
  have hadd : 2 ^ 64 - 1 + n.val = (n.val - 1) + 2 ^ 64 := by omega
  rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt]
  omega

private theorem worker_int64_and_val
    (x y : CompCert4Lean.Lib.Integers.Int64.int) :
    (CompCert4Lean.Lib.Integers.Int64.and x y).val = Nat.land x.val y.val := by
  unfold CompCert4Lean.Lib.Integers.Int64.and
    CompCert4Lean.Lib.Integers.WordCore.and
  change (CompCert4Lean.Lib.Integers.WordCore.repr 64
    (zOfNat (Nat.land x.val y.val))).val = Nat.land x.val y.val
  rw [show zOfNat (Nat.land x.val y.val) =
      zOfInt (Int.ofNat (Nat.land x.val y.val)) by rfl]
  rw [cp_suffixWordValRepr64]
  have hlt : Nat.land x.val y.val < 2 ^ 64 :=
    Nat.and_lt_two_pow x.val y.toFin.isLt
  have hmod : Int.ofNat (Nat.land x.val y.val) % ((2 ^ 64 : Nat) : Int) =
      Int.ofNat (Nat.land x.val y.val) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by
      change Int.ofNat (Nat.land x.val y.val) < Int.ofNat (2 ^ 64)
      exact Int.ofNat_lt.mpr hlt)
  rw [hmod]
  simp

private def worker_numbersPrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private")
    "CompCert4Lean") "Foundation") "Numbers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem worker_modulo_nat (a b : Nat) (hb : 0 < b) :
    ZArith.BinInt.Z.modulo (zOfNat a) (zOfNat b) = zOfNat (a % b) := by
  apply intOfZ_injective
  simp only [ZArith.BinInt.Z.modulo, intOfZ_zOfInt]
  run_tac
    let zmodName := Lean.mkIdent (worker_numbersPrivateName
      "CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.zModEucl")
    evalTactic (← `(tactic| unfold $zmodName))
  simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  have hb0 : Int.ofNat b ≠ 0 :=
    Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hb)
  have hbpos : (0 : Int) < Int.ofNat b := Int.natCast_pos.mpr hb
  simp only [hb0, hbpos, if_false, if_true]
  exact (Int.natCast_emod a b).symm

private theorem worker_int64_modu_val
    (x n : CompCert4Lean.Lib.Integers.Int64.int) (hnpos : 0 < n.val) :
    (CompCert4Lean.Lib.Integers.Int64.modu x n).val = x.val % n.val := by
  unfold CompCert4Lean.Lib.Integers.Int64.modu
    CompCert4Lean.Lib.Integers.WordCore.modu
  change (CompCert4Lean.Lib.Integers.WordCore.repr 64
    (ZArith.BinInt.Z.modulo
      (CompCert4Lean.Lib.Integers.Int64.unsigned x)
      (CompCert4Lean.Lib.Integers.Int64.unsigned n))).val = x.val % n.val
  rw [← worker_int64_zOfNat_val x, ← worker_int64_zOfNat_val n,
    worker_modulo_nat _ _ hnpos]
  rw [show zOfNat (x.val % n.val) = zOfInt (Int.ofNat (x.val % n.val)) by rfl,
    cp_suffixWordValRepr64]
  have hrem : x.val % n.val < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hnpos) (Nat.le_of_lt n.toFin.isLt)
  have hmod : Int.ofNat (x.val % n.val) % ((2 ^ 64 : Nat) : Int) =
      Int.ofNat (x.val % n.val) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by
      change Int.ofNat (x.val % n.val) < Int.ofNat (2 ^ 64)
      exact Int.ofNat_lt.mpr hrem)
  rw [hmod]
  change (Int.ofNat (x.val % n.val)).toNat = x.val % n.val
  exact Int.toNat_natCast _

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.ConstpropOp

private theorem worker_int64_modu_and
    (x n logn : CompCert4Lean.Lib.Integers.Int64.int)
    (hpow : CompCert4Lean.Lib.Integers.Int64.is_power2 n = some logn) :
    CompCert4Lean.Lib.Integers.Int64.modu x n =
      CompCert4Lean.Lib.Integers.Int64.and x
        (CompCert4Lean.Lib.Integers.Int64.sub n
          CompCert4Lean.Lib.Integers.Int64.one) := by
  rcases worker_int64_is_power2_nat n logn hpow with ⟨k, hnk⟩
  have hnpos : 0 < n.val := by
    rw [hnk]
    exact Nat.two_pow_pos k
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [worker_int64_modu_val x n hnpos, worker_int64_and_val,
    worker_int64_sub_one_val n hnpos, hnk]
  exact (Nat.and_two_pow_sub_one_eq_mod x.val k).symm

private theorem worker_val_modlu_pow2
    (x : CompCert4Lean.Common.Values.val)
    (n logn : CompCert4Lean.Lib.Integers.Int64.int)
    (y : CompCert4Lean.Common.Values.val)
    (hpow : CompCert4Lean.Lib.Integers.Int64.is_power2 n = some logn)
    (hmod : CompCert4Lean.Common.Values.Val.modlu x (.Vlong n) = some y) :
    CompCert4Lean.Common.Values.Val.andl x
      (.Vlong (CompCert4Lean.Lib.Integers.Int64.sub n
        CompCert4Lean.Lib.Integers.Int64.one)) = y := by
  cases x with
  | Vlong i =>
      simp only [CompCert4Lean.Common.Values.Val.modlu] at hmod
      split at hmod
      · cases hmod
      · cases hmod
        simp only [CompCert4Lean.Common.Values.Val.andl, val.Vlong.injEq]
        exact (worker_int64_modu_and i n logn hpow).symm
  | Vundef => simp [CompCert4Lean.Common.Values.Val.modlu] at hmod
  | Vint i => simp [CompCert4Lean.Common.Values.Val.modlu] at hmod
  | Vfloat f => simp [CompCert4Lean.Common.Values.Val.modlu] at hmod
  | Vsingle f => simp [CompCert4Lean.Common.Values.Val.modlu] at hmod
  | Vptr b ofs => simp [CompCert4Lean.Common.Values.Val.modlu] at hmod

theorem make_modluimm_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @make_modluimm_correctStatement binary64_certificate binary32_certificate := by
  intro ge sp e m n r1 r2 v hmod hr2
  have hmodn : CompCert4Lean.Common.Values.Val.modlu
      (CompCert4Lean.Backend.Registers.Regmap.get r1 e) (.Vlong n) = some v := by
    rw [← hr2]
    exact hmod
  unfold CompCert4Lean.X86.ConstpropOp.make_modluimm
  cases hpow : CompCert4Lean.Lib.Integers.Int64.is_power2 n with
  | none =>
      refine ⟨v, ?_, CompCert4Lean.Common.Values.Val.lessdef_refl _⟩
      change CompCert4Lean.Common.Values.Val.modlu
        (CompCert4Lean.Backend.Registers.Regmap.get r1 e)
        (CompCert4Lean.Backend.Registers.Regmap.get r2 e) = some v
      exact hmod
  | some logn =>
      refine ⟨v, ?_, CompCert4Lean.Common.Values.Val.lessdef_refl _⟩
      change some (CompCert4Lean.Common.Values.Val.andl
        (CompCert4Lean.Backend.Registers.Regmap.get r1 e)
        (.Vlong (CompCert4Lean.Lib.Integers.Int64.sub n
          CompCert4Lean.Lib.Integers.Int64.one))) = some v
      exact congrArg some (worker_val_modlu_pow2
        (CompCert4Lean.Backend.Registers.Regmap.get r1 e) n logn v hpow hmodn)

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.ConstpropOp

private theorem worker_int64_xor_zero
    (x : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.xor x
        CompCert4Lean.Lib.Integers.Int64.zero = x := by
  unfold CompCert4Lean.Lib.Integers.Int64.xor
    CompCert4Lean.Lib.Integers.WordCore.xor
  change CompCert4Lean.Lib.Integers.Int64.repr
      (zOfNat (Nat.xor x.val CompCert4Lean.Lib.Integers.Int64.zero.val)) = x
  rw [show CompCert4Lean.Lib.Integers.Int64.zero.val = 0 by rfl]
  rw [show Nat.xor x.val 0 = x.val by
    simpa only [Nat.xor_eq] using Nat.xor_zero x.val]
  change CompCert4Lean.Lib.Integers.Int64.repr (zOfNat x.val) = x
  rw [worker_int64_zOfNat_val]
  exact worker_int64_repr_unsigned x

theorem make_xorlimm_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @make_xorlimm_correctStatement binary64_certificate binary32_certificate := by
  intro ge sp e m n r
  dsimp [CompCert4Lean.X86.ConstpropOp.make_xorlimm]
  split <;> rename_i hzero
  · have hn : n = CompCert4Lean.Lib.Integers.Int64.zero :=
      worker_int64_eq_true n CompCert4Lean.Lib.Integers.Int64.zero hzero
    subst n
    refine ⟨CompCert4Lean.Backend.Registers.Regmap.get r e, ?_, ?_⟩
    · rfl
    · cases CompCert4Lean.Backend.Registers.Regmap.get r e with
      | Vlong i =>
          change CompCert4Lean.Common.Values.Val.lessdef
            (.Vlong (CompCert4Lean.Lib.Integers.Int64.xor i
              CompCert4Lean.Lib.Integers.Int64.zero)) (.Vlong i)
          rw [worker_int64_xor_zero]
          exact CompCert4Lean.Common.Values.Val.lessdef_refl _
      | _ => exact CompCert4Lean.Common.Values.Val.lessdef_undef _
  · split <;> rename_i hmone
    · have hn : n = CompCert4Lean.Lib.Integers.Int64.mone :=
        worker_int64_eq_true n CompCert4Lean.Lib.Integers.Int64.mone hmone
      subst n
      refine ⟨CompCert4Lean.Common.Values.Val.notl
          (CompCert4Lean.Backend.Registers.Regmap.get r e), ?_, ?_⟩
      · rfl
      · rw [← CompCert4Lean.Common.Values.Val.notl_xorl]
        exact CompCert4Lean.Common.Values.Val.lessdef_refl _
    · refine ⟨CompCert4Lean.Common.Values.Val.xorl
          (CompCert4Lean.Backend.Registers.Regmap.get r e) (.Vlong n), ?_,
          CompCert4Lean.Common.Values.Val.lessdef_refl _⟩
      rfl

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.ConstpropOp

theorem make_mulfsimm_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @make_mulfsimm_correctStatement binary64_certificate binary32_certificate := by
  intro ge sp e m n r1 r2 hr2
  dsimp [CompCert4Lean.X86.ConstpropOp.make_mulfsimm]
  split <;> rename_i htwo
  · refine ⟨CompCert4Lean.Common.Values.Val.addfs
        (CompCert4Lean.Backend.Registers.Regmap.get r1 e)
        (CompCert4Lean.Backend.Registers.Regmap.get r1 e), rfl, ?_⟩
    rw [hr2, htwo]
    cases CompCert4Lean.Backend.Registers.Regmap.get r1 e with
    | Vsingle f =>
        change CompCert4Lean.Common.Values.Val.lessdef
          (.Vsingle (CompCert4Lean.Lib.Floats.Float32.mul f
            (CompCert4Lean.Lib.Floats.Float32.of_int
              (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 2)))))
          (.Vsingle (CompCert4Lean.Lib.Floats.Float32.add f f))
        rw [← CompCert4Lean.Lib.Floats.Float32.mul2_add]
        exact CompCert4Lean.Common.Values.Val.lessdef_refl _
    | _ => exact CompCert4Lean.Common.Values.Val.lessdef_undef _
  · refine ⟨CompCert4Lean.Common.Values.Val.mulfs
        (CompCert4Lean.Backend.Registers.Regmap.get r1 e)
        (CompCert4Lean.Backend.Registers.Regmap.get r2 e), rfl,
        CompCert4Lean.Common.Values.Val.lessdef_refl _⟩

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Floats

private theorem worker_float64_of_int_two_bits
    [certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)] :
    Float.of_int (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 2)) =
      ⟨BitVec.ofNat 64 4611686018427387904⟩ := by
  rfl

private theorem worker_float64_unpack_two_bits :
    _root_.Float.Model.UnpackedFloat.unpack _root_.Float.Model.Format.binary64
        (BitVec.ofNat 64 4611686018427387904) =
      .finite .positive 4503599627370496 (-51) (by decide) := by
  rfl

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

private theorem worker_extendedMantissa_shift_pow (m k : Nat) :
    (_root_.Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
        (m * 2 ^ k) _root_.Float.Model.UnpackedFloat.Accuracy.exact >>> k) =
      _root_.Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
        m _root_.Float.Model.UnpackedFloat.Accuracy.exact := by
  change Nat.repeat
      _root_.Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne k
        (_root_.Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
          (m * 2 ^ k) _root_.Float.Model.UnpackedFloat.Accuracy.exact) = _
  induction k generalizing m with
  | zero => simp [Nat.repeat]
  | succ k ih =>
      rw [show m * 2 ^ (k + 1) = (m * 2) * 2 ^ k by
        simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]]
      simp only [Nat.repeat]
      rw [ih]
      simp [_root_.Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne,
        _root_.Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy]

private theorem worker_extendedMantissa_shift_zero
    (x : _root_.Float.Model.UnpackedFloat.ExtendedMantissa) : x >>> 0 = x := by
  change Nat.repeat
    _root_.Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne 0 x = x
  unfold Nat.repeat
  rfl

private theorem worker_extendedMantissa_shift_pow_add (m k q : Nat) :
    (_root_.Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
        (m * 2 ^ k) _root_.Float.Model.UnpackedFloat.Accuracy.exact >>> (k + q)) =
      (_root_.Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
        m _root_.Float.Model.UnpackedFloat.Accuracy.exact >>> q) := by
  induction q with
  | zero =>
      rw [worker_extendedMantissa_shift_zero]
      exact worker_extendedMantissa_shift_pow m k
  | succ q ih =>
      change
        _root_.Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne
            ((_root_.Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
              (m * 2 ^ k) _root_.Float.Model.UnpackedFloat.Accuracy.exact) >>> (k + q)) =
          _root_.Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne
            ((_root_.Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
              m _root_.Float.Model.UnpackedFloat.Accuracy.exact) >>> q)
      exact congrArg _ ih

private theorem worker_log2_mul_pow (m k : Nat) (hm : m ≠ 0) :
    (m * 2 ^ k).log2 = m.log2 + k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.pow_succ]
      rw [show m * (2 ^ k * 2) = 2 * (m * 2 ^ k) by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]]
      rw [Nat.log2_two_mul
        (Nat.mul_ne_zero hm (Nat.ne_of_gt (Nat.two_pow_pos k))), ih]
      omega

private theorem worker_shiftToTargetExponent_scale64
    (m k : Nat) (e : Int) (hm : m ≠ 0)
    (hle : e ≤ _root_.Float.Model.Format.binary64.targetExponent
      (_root_.Float.Model.totalExponent m e)) :
    _root_.Float.Model.UnpackedFloat.shiftToTargetExponent
        _root_.Float.Model.Format.binary64 (m * 2 ^ k) (e - (k : Int))
        _root_.Float.Model.UnpackedFloat.Accuracy.exact =
      _root_.Float.Model.UnpackedFloat.shiftToTargetExponent
        _root_.Float.Model.Format.binary64 m e
        _root_.Float.Model.UnpackedFloat.Accuracy.exact := by
  have htotal :
      _root_.Float.Model.totalExponent (m * 2 ^ k) (e - (k : Int)) =
        _root_.Float.Model.totalExponent m e := by
    unfold _root_.Float.Model.totalExponent
    rw [worker_log2_mul_pow m k hm]
    omega
  unfold _root_.Float.Model.UnpackedFloat.shiftToTargetExponent
  rw [htotal]
  unfold _root_.Float.Model.UnpackedFloat.shiftToExponent
  let t := _root_.Float.Model.Format.binary64.targetExponent
    (_root_.Float.Model.totalExponent m e)
  have hnonneg : 0 ≤ t - e := by omega
  have hdiff : t - (e - (k : Int)) = (k : Int) + (t - e) := by omega
  change
    ((_root_.Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
        (m * 2 ^ k) _root_.Float.Model.UnpackedFloat.Accuracy.exact >>>
          (t - (e - (k : Int))).toNat),
        e - (k : Int) + (t - (e - (k : Int))).toNat) =
      ((_root_.Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
        m _root_.Float.Model.UnpackedFloat.Accuracy.exact >>> (t - e).toNat),
        e + (t - e).toNat)
  rw [hdiff, Int.toNat_add (Int.ofNat_nonneg k) hnonneg]
  apply Prod.ext
  · exact worker_extendedMantissa_shift_pow_add m k (t - e).toNat
  · simp only [Int.toNat_natCast]
    have hcast : ((t - e).toNat : Int) = t - e := Int.toNat_of_nonneg hnonneg
    omega

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

private theorem worker_round_double64
    (s : _root_.Float.Model.UnpackedFloat.Sign) (m : Nat) (e : Int)
    (hm : 0 < m) :
    _root_.Float.Model.UnpackedFloat.round _root_.Float.Model.Format.binary64
        s (m + m) e =
      _root_.Float.Model.UnpackedFloat.roundWithAccuracy
        _root_.Float.Model.Format.binary64 s (m * 4503599627370496) (e - 51)
        _root_.Float.Model.UnpackedFloat.Accuracy.exact := by
  let a := m + m
  let t := _root_.Float.Model.Format.binary64.targetExponent
    (_root_.Float.Model.totalExponent a e)
  let d := (e - t).toNat
  have ha : a ≠ 0 := by simp [a, Nat.ne_of_gt hm]
  have hloga : a.log2 = m.log2 + 1 := by
    rw [show a = 2 * m by omega, Nat.log2_two_mul (Nat.ne_of_gt hm)]
  have ht_lower : e - 51 ≤ t := by
    dsimp [t]
    change e - 51 ≤ max ((a.log2 : Int) + 1 + e - 53) (-1074)
    rw [hloga]
    omega
  have hdle : d ≤ 51 := by
    dsimp [d]
    omega
  let c := a * 2 ^ d
  let ec := e - (d : Int)
  have hc : c ≠ 0 :=
    Nat.mul_ne_zero ha (Nat.ne_of_gt (Nat.two_pow_pos d))
  have htotalc :
      _root_.Float.Model.totalExponent c ec =
        _root_.Float.Model.totalExponent a e := by
    dsimp [c, ec]
    unfold _root_.Float.Model.totalExponent
    rw [worker_log2_mul_pow a d ha]
    omega
  have hlec : ec ≤ _root_.Float.Model.Format.binary64.targetExponent
      (_root_.Float.Model.totalExponent c ec) := by
    rw [htotalc]
    change e - (d : Int) ≤ t
    dsimp [d]
    omega
  have hscale := worker_shiftToTargetExponent_scale64 c (51 - d) ec hc hlec
  have hmant : c * 2 ^ (51 - d) = m * 4503599627370496 := by
    dsimp [c, a]
    rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le hdle]
    change (m + m) * 2251799813685248 = m * 4503599627370496
    omega
  have hexp : ec - ((51 - d : Nat) : Int) = e - 51 := by
    dsimp [ec]
    omega
  rw [hmant, hexp] at hscale
  unfold _root_.Float.Model.UnpackedFloat.round
    _root_.Float.Model.UnpackedFloat.decreaseExponent
  dsimp only
  change
    _root_.Float.Model.UnpackedFloat.roundWithAccuracy
        _root_.Float.Model.Format.binary64 s (a <<< d) ec
        _root_.Float.Model.UnpackedFloat.Accuracy.exact = _
  rw [Nat.shiftLeft_eq]
  change
    _root_.Float.Model.UnpackedFloat.roundWithAccuracy
        _root_.Float.Model.Format.binary64 s c ec
        _root_.Float.Model.UnpackedFloat.Accuracy.exact = _
  unfold _root_.Float.Model.UnpackedFloat.roundWithAccuracy
  rw [← hscale]

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

private theorem worker_unpacked_add_self_mul_two64
    (a : _root_.Float.Model.UnpackedFloat) :
    _root_.Float.Model.UnpackedFloat.add _root_.Float.Model.Format.binary64 a a =
      _root_.Float.Model.UnpackedFloat.mul _root_.Float.Model.Format.binary64 a
        (.finite .positive 4503599627370496 (-51) (by decide)) := by
  cases a with
  | notANumber => rfl
  | infinity s => cases s <;> rfl
  | zero s => cases s <;> rfl
  | finite s m e hm =>
      have hmI : (0 : Int) < (m : Int) := by omega
      cases s with
      | negative =>
        simp only [_root_.Float.Model.UnpackedFloat.add,
          _root_.Float.Model.UnpackedFloat.mul,
          _root_.Float.Model.UnpackedFloat.decreaseExponent,
          _root_.Float.Model.UnpackedFloat.Sign.apply,
          _root_.Float.Model.UnpackedFloat.normalize, Int.min_self, Int.sub_self,
          Int.toNat_zero, Nat.shiftLeft_zero]
        have hc : compare (-(m : Int) + -(m : Int)) 0 = .lt :=
          Int.compare_eq_lt.mpr (by omega)
        rw [hc]
        have hnat : (-(-(m : Int) + -(m : Int))).toNat = m + m := by omega
        rw [hnat]
        change
          _root_.Float.Model.UnpackedFloat.round _root_.Float.Model.Format.binary64
              .negative (m + m) e =
            _root_.Float.Model.UnpackedFloat.roundWithAccuracy
              _root_.Float.Model.Format.binary64 .negative
              (m * 4503599627370496) (e - 51)
              _root_.Float.Model.UnpackedFloat.Accuracy.exact
        exact worker_round_double64 .negative m e hm
      | positive =>
        simp only [_root_.Float.Model.UnpackedFloat.add,
          _root_.Float.Model.UnpackedFloat.mul,
          _root_.Float.Model.UnpackedFloat.decreaseExponent,
          _root_.Float.Model.UnpackedFloat.Sign.apply,
          _root_.Float.Model.UnpackedFloat.normalize, Int.min_self, Int.sub_self,
          Int.toNat_zero, Nat.shiftLeft_zero]
        have hc : compare ((m : Int) + (m : Int)) 0 = .gt :=
          Int.compare_eq_gt.mpr (by omega)
        rw [hc]
        have hnat : ((m : Int) + (m : Int)).toNat = m + m := by omega
        rw [hnat]
        change
          _root_.Float.Model.UnpackedFloat.round _root_.Float.Model.Format.binary64
              .positive (m + m) e =
            _root_.Float.Model.UnpackedFloat.roundWithAccuracy
              _root_.Float.Model.Format.binary64 .positive
              (m * 4503599627370496) (e - 51)
              _root_.Float.Model.UnpackedFloat.Accuracy.exact
        exact worker_round_double64 .positive m e hm

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Floats

private def worker_float64_sign (x : float) : Bool :=
  x.bits.toNat / (2 ^ 63) % 2 == 1

private def worker_float64_fraction (x : float) : Nat :=
  x.bits.toNat % (2 ^ 52)

private def worker_float64_isNaN (x : float) : Bool :=
  (x.bits.toNat / (2 ^ 52) % (2 ^ 11) == (2 ^ 11 - 1)) &&
    worker_float64_fraction x != 0

private def worker_float64_payload (x : float) : positive :=
  PArith.BinPos.Pos.of_nat (worker_float64_fraction x)

private def worker_float64_cons_pl
    (x : float) (l : List (Bool × positive)) : List (Bool × positive) :=
  if worker_float64_isNaN x then
    (worker_float64_sign x, worker_float64_payload x) :: l
  else l

private def worker_float64_binop_nan (x y : float) : float :=
  CompCert4Lean.Lib.Floats.quiet_nan_64
    (CompCert4Lean.X86_64.Archi.choose_nan_64
      (worker_float64_cons_pl x (worker_float64_cons_pl y [])))

private def worker_modelBinary64
    (op : _root_.Float.Model.UnpackedFloat →
      _root_.Float.Model.UnpackedFloat → _root_.Float.Model.UnpackedFloat)
    (x y : float) : float :=
  ⟨_root_.Float.Model.UnpackedFloat.pack _root_.Float.Model.Format.binary64
    (op
      (_root_.Float.Model.UnpackedFloat.unpack _root_.Float.Model.Format.binary64
        x.bits)
      (_root_.Float.Model.UnpackedFloat.unpack _root_.Float.Model.Format.binary64
        y.bits))⟩

private def worker_finishBinary64 (x y r : float) : float :=
  if worker_float64_isNaN x || worker_float64_isNaN y then
    worker_float64_binop_nan x y
  else if worker_float64_isNaN r then
    CompCert4Lean.Lib.Floats.default_nan_64 else r

private theorem worker_model_add_self_mul_two64
    [certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    (f : float) :
    worker_modelBinary64
        (_root_.Float.Model.UnpackedFloat.add _root_.Float.Model.Format.binary64)
        f f =
      worker_modelBinary64
        (_root_.Float.Model.UnpackedFloat.mul _root_.Float.Model.Format.binary64)
        f (CompCert4Lean.Lib.Floats.Float.of_int
          (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 2))) := by
  rw [worker_float64_of_int_two_bits]
  unfold worker_modelBinary64
  rw [worker_float64_unpack_two_bits, worker_unpacked_add_self_mul_two64]

private theorem worker_float64_two_not_nan
    [certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)] :
    worker_float64_isNaN
        (CompCert4Lean.Lib.Floats.Float.of_int
          (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 2))) = false := by
  rw [worker_float64_of_int_two_bits]
  rfl

private theorem worker_float64_mul2_add
    [certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    (f : float) :
    CompCert4Lean.Lib.Floats.Float.add f f =
      CompCert4Lean.Lib.Floats.Float.mul f
        (CompCert4Lean.Lib.Floats.Float.of_int
          (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 2))) := by
  unfold CompCert4Lean.Lib.Floats.Float.add CompCert4Lean.Lib.Floats.Float.mul
  change
    worker_finishBinary64 f f
        (worker_modelBinary64
          (_root_.Float.Model.UnpackedFloat.add _root_.Float.Model.Format.binary64)
          f f) =
      worker_finishBinary64 f
        (CompCert4Lean.Lib.Floats.Float.of_int
          (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 2)))
        (worker_modelBinary64
          (_root_.Float.Model.UnpackedFloat.mul _root_.Float.Model.Format.binary64)
          f (CompCert4Lean.Lib.Floats.Float.of_int
            (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 2))))
  rw [worker_model_add_self_mul_two64]
  have htwo := worker_float64_two_not_nan
  by_cases hf : worker_float64_isNaN f = true
  · simp only [worker_finishBinary64, worker_float64_binop_nan,
      worker_float64_cons_pl, hf, htwo, Bool.true_or, Bool.false_eq_true,
      ↓reduceIte]
    rw [CompCert4Lean.X86_64.Archi.choose_nan_64_idem]
  · simp [worker_finishBinary64, hf, htwo]

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.ConstpropOp

theorem make_mulfimm_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @make_mulfimm_correctStatement binary64_certificate binary32_certificate := by
  intro ge sp e m n r1 r2 hr2
  dsimp [CompCert4Lean.X86.ConstpropOp.make_mulfimm]
  split <;> rename_i htwo
  · refine ⟨CompCert4Lean.Common.Values.Val.addf
        (CompCert4Lean.Backend.Registers.Regmap.get r1 e)
        (CompCert4Lean.Backend.Registers.Regmap.get r1 e), rfl, ?_⟩
    rw [hr2, htwo]
    cases CompCert4Lean.Backend.Registers.Regmap.get r1 e with
    | Vfloat f =>
        change CompCert4Lean.Common.Values.Val.lessdef
          (.Vfloat (CompCert4Lean.Lib.Floats.Float.mul f
            (CompCert4Lean.Lib.Floats.Float.of_int
              (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 2)))))
          (.Vfloat (CompCert4Lean.Lib.Floats.Float.add f f))
        rw [← worker_float64_mul2_add]
        exact CompCert4Lean.Common.Values.Val.lessdef_refl _
    | _ => exact CompCert4Lean.Common.Values.Val.lessdef_undef _
  · refine ⟨CompCert4Lean.Common.Values.Val.mulf
        (CompCert4Lean.Backend.Registers.Regmap.get r1 e)
        (CompCert4Lean.Backend.Registers.Regmap.get r2 e), rfl,
        CompCert4Lean.Common.Values.Val.lessdef_refl _⟩

theorem make_mulfimm_correct_2
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @make_mulfimm_correct_2Statement binary64_certificate binary32_certificate := by
  intro ge sp e m n r1 r2 hr1
  dsimp [CompCert4Lean.X86.ConstpropOp.make_mulfimm]
  split <;> rename_i htwo
  · refine ⟨CompCert4Lean.Common.Values.Val.addf
        (CompCert4Lean.Backend.Registers.Regmap.get r2 e)
        (CompCert4Lean.Backend.Registers.Regmap.get r2 e), rfl, ?_⟩
    rw [hr1, htwo]
    cases CompCert4Lean.Backend.Registers.Regmap.get r2 e with
    | Vfloat f =>
        change CompCert4Lean.Common.Values.Val.lessdef
          (.Vfloat (CompCert4Lean.Lib.Floats.Float.mul
            (CompCert4Lean.Lib.Floats.Float.of_int
              (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 2))) f))
          (.Vfloat (CompCert4Lean.Lib.Floats.Float.add f f))
        have hcomm := CompCert4Lean.Lib.Floats.Float.mul_commut
          (CompCert4Lean.Lib.Floats.Float.of_int
            (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 2))) f
          (Or.inl worker_float64_two_not_nan)
        rw [hcomm, ← worker_float64_mul2_add]
        exact CompCert4Lean.Common.Values.Val.lessdef_refl _
    | _ => exact CompCert4Lean.Common.Values.Val.lessdef_undef _
  · refine ⟨CompCert4Lean.Common.Values.Val.mulf
        (CompCert4Lean.Backend.Registers.Regmap.get r1 e)
        (CompCert4Lean.Backend.Registers.Regmap.get r2 e), rfl,
        CompCert4Lean.Common.Values.Val.lessdef_refl _⟩

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

open Lean Elab Tactic Meta
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.Values

private def worker_boolOfSumbool {P Q : Prop} :
    CompCert4Lean.Foundation.Logic.Support.Sumbool P Q → Bool
  | .left _ => true
  | .right _ => false

private def worker_zlt
    (x y : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : Bool :=
  worker_boolOfSumbool (CompCert4Lean.Lib.Coqlib.zlt x y)

private def worker_zle
    (x y : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : Bool :=
  worker_boolOfSumbool (CompCert4Lean.Lib.Coqlib.zle x y)

private theorem worker_zlt_true
    {x y : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z}
    (h : worker_zlt x y = true) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt x y := by
  cases hd : CompCert4Lean.Lib.Coqlib.zlt x y with
  | left hxy => exact hxy
  | right hxy => simp [worker_zlt, worker_boolOfSumbool, hd] at h

private theorem worker_zle_true
    {x y : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z}
    (h : worker_zle x y = true) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le x y := by
  cases hd : CompCert4Lean.Lib.Coqlib.zle x y with
  | left hxy => exact hxy
  | right hxy => simp [worker_zle, worker_boolOfSumbool, hd] at h

private def worker_is_sgn
    (n : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (i : CompCert4Lean.Lib.Integers.int) : Prop :=
  ∀ m, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
      (.Z0) m ∧
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt m
        CompCert4Lean.Lib.Integers.Int.zwordsize →
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub n (.Zpos .xH)) m →
    CompCert4Lean.Lib.Integers.Int.testbit i m =
      CompCert4Lean.Lib.Integers.Int.testbit i
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub
          CompCert4Lean.Lib.Integers.Int.zwordsize (.Zpos .xH))

private def worker_private_name (suffix : String) : Lean.Name :=
  let p := Lean.Name.str
    (Lean.Name.str
      (Lean.Name.str
        (Lean.Name.str Lean.Name.anonymous "_private") "CompCert4Lean") "Lib")
    "Integers"
  let p := Lean.Name.num p 0
  suffix.splitOn "." |>.foldl Lean.Name.str p

private def worker_simp_private (suffixes : List String) : Lean.Elab.Tactic.TacticM Unit := do
  let mut ts : Lean.Meta.SimpTheorems := {}
  for suffix in suffixes do
    let eqs ← Lean.Meta.getEqnsFor? (worker_private_name suffix)
    match eqs with
    | some eqs =>
        for eqn in eqs do
          let xs ← Lean.Meta.mkSimpTheoremFromConst eqn
          for x in xs do ts := ts.addSimpTheorem x
    | none => pure ()
  let ctx ← Lean.Meta.Simp.mkContext {} #[ts]
  let g ← Lean.Elab.Tactic.getMainGoal
  let (r, _) ← Lean.Meta.simpGoal g ctx
  match r with
  | none => Lean.Elab.Tactic.replaceMainGoal []
  | some (_, g') => Lean.Elab.Tactic.replaceMainGoal [g']

private theorem worker_is_sgn_sign_ext_16
    (i : CompCert4Lean.Lib.Integers.int)
    (h : worker_is_sgn (zOfNat 16) i) :
    CompCert4Lean.Lib.Integers.Int.sign_ext (zOfNat 16) i = i := by
  apply CompCert4Lean.Lib.Integers.Int.same_bits_eq_proof
  intro j hj
  have hb := CompCert4Lean.Lib.Integers.Int.bits_sign_ext_proof
    (zOfNat 16) i j hj
  rw [hb]
  cases hs : CompCert4Lean.Lib.Coqlib.zlt j (zOfNat 16) with
  | left hlt =>
      run_tac worker_simp_private ["CompCert4Lean.Lib.Integers.zltSelect"]
      rw [hs]
      rfl
  | right hge =>
      run_tac worker_simp_private ["CompCert4Lean.Lib.Integers.zltSelect"]
      rw [hs]
      run_tac worker_simp_private ["CompCert4Lean.Lib.Integers.sumboolSelect"]
      have hkn : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub
            (zOfNat 16) (.Zpos .xH)) j := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub
              (zOfNat 16) (.Zpos .xH)) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ j
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zOfNat 16) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ j at hge
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        have h16 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zOfNat 16) = 16 := by rfl
        have h1 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (.Zpos .xH) = 1 := by rfl
        rw [h16] at hge
        simp only [h1]
        omega
      have h15 := h (zOfNat 15)
        (by
          constructor
          · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (.Z0) ≤
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zOfNat 15)
            change (0 : Int) ≤ 15
            omega
          · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zOfNat 15) <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                CompCert4Lean.Lib.Integers.Int.zwordsize
            change (15 : Int) < 32
            omega)
        (by
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub
                (zOfNat 16) (zOfNat 1)) ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zOfNat 15)
          simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          have h16 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zOfNat 16) = 16 := by rfl
          have h1 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zOfNat 1) = 1 := by rfl
          have h15' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zOfNat 15) = 15 := by rfl
          simp only [h16, h1, h15']
          omega)
      have hjbit := h j (by exact hj) hkn
      exact h15.trans hjbit.symm

theorem make_cast16signed_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @make_cast16signed_correctStatement binary64_certificate binary32_certificate := by
  intro bc ge sp e m r x hmatch
  dsimp [CompCert4Lean.X86.ConstpropOp.make_cast16signed]
  by_cases hincl : vincl x (Sgn Ptop (zOfNat 16)) = true
  · simp only [if_pos hincl]
    refine ⟨Regmap.get r e, rfl, ?_⟩
    generalize hv : Regmap.get r e = w at hmatch
    cases x with
    | Vbot => cases hmatch
    | I i =>
        have hrewrite :
            vincl (I i) (Sgn Ptop (zOfNat 16)) =
              (decide (CompCert4Lean.Lib.Integers.Int.sign_ext (zOfNat 16) i = i) &&
                worker_zlt (.Z0)
                  (zOfNat 16)) := by rfl
        rw [hrewrite] at hincl
        have hi : CompCert4Lean.Lib.Integers.Int.sign_ext (zOfNat 16) i = i :=
          of_decide_eq_true (Bool.and_eq_true_iff.mp hincl).1
        cases hmatch with
        | vmatch_i =>
            have hext : Val.sign_ext (zOfNat 16) (.Vint i) =
                .Vint (CompCert4Lean.Lib.Integers.Int.sign_ext (zOfNat 16) i) := by rfl
            rw [hext]
            rw [hi]
            exact CompCert4Lean.Common.Values.Val.lessdef_refl _
    | IU i =>
        have hrewrite :
            vincl (IU i) (Sgn Ptop (zOfNat 16)) =
              (decide (CompCert4Lean.Lib.Integers.Int.sign_ext (zOfNat 16) i = i) &&
                worker_zlt (.Z0)
                  (zOfNat 16)) := by rfl
        rw [hrewrite] at hincl
        have hi : CompCert4Lean.Lib.Integers.Int.sign_ext (zOfNat 16) i = i :=
          of_decide_eq_true (Bool.and_eq_true_iff.mp hincl).1
        cases hmatch with
        | vmatch_iu =>
            have hext : Val.sign_ext (zOfNat 16) (.Vint i) =
                .Vint (CompCert4Lean.Lib.Integers.Int.sign_ext (zOfNat 16) i) := by rfl
            rw [hext]
            rw [hi]
            exact CompCert4Lean.Common.Values.Val.lessdef_refl _
        | iuUndef =>
            exact CompCert4Lean.Common.Values.Val.lessdef_refl _
    | Uns p n =>
        have hrewrite :
            vincl (Uns p n) (Sgn Ptop (zOfNat 16)) =
              (worker_zlt n (zOfNat 16) && pincl p Ptop) := by rfl
        rw [hrewrite] at hincl
        have hp := Bool.and_eq_true_iff.mp hincl
        have hge : vge (Sgn Ptop (zOfNat 16)) (Uns p n) :=
          vge.sgnUns Ptop (zOfNat 16) p n (worker_zlt_true hp.1)
            (pincl_ge p Ptop hp.2)
        have hmv := vmatch_ge bc w (Sgn Ptop (zOfNat 16)) (Uns p n) hge hmatch
        cases hmv with
        | sgn _ i _ _ hi =>
            have hi' : worker_is_sgn (zOfNat 16) i := hi
            have hext : Val.sign_ext (zOfNat 16) (.Vint i) =
                .Vint (CompCert4Lean.Lib.Integers.Int.sign_ext (zOfNat 16) i) := by rfl
            rw [hext]
            rw [worker_is_sgn_sign_ext_16 i hi']
            exact CompCert4Lean.Common.Values.Val.lessdef_refl _
        | sgnUndef => exact CompCert4Lean.Common.Values.Val.lessdef_refl _
    | Sgn p n =>
        have hrewrite :
            vincl (Sgn p n) (Sgn Ptop (zOfNat 16)) =
              (worker_zle n (zOfNat 16) && pincl p Ptop) := by rfl
        rw [hrewrite] at hincl
        have hp := Bool.and_eq_true_iff.mp hincl
        have hge : vge (Sgn Ptop (zOfNat 16)) (Sgn p n) :=
          vge.sgnSgn Ptop (zOfNat 16) p n (worker_zle_true hp.1)
            (pincl_ge p Ptop hp.2)
        have hmv := vmatch_ge bc w (Sgn Ptop (zOfNat 16)) (Sgn p n) hge hmatch
        cases hmv with
        | sgn _ i _ _ hi =>
            have hi' : worker_is_sgn (zOfNat 16) i := hi
            have hext : Val.sign_ext (zOfNat 16) (.Vint i) =
                .Vint (CompCert4Lean.Lib.Integers.Int.sign_ext (zOfNat 16) i) := by rfl
            rw [hext]
            rw [worker_is_sgn_sign_ext_16 i hi']
            exact CompCert4Lean.Common.Values.Val.lessdef_refl _
        | sgnUndef => exact CompCert4Lean.Common.Values.Val.lessdef_refl _
    | L _ | F _ | FS _ | Num _ | Ptr _ | Ifptr _ =>
        simp [vincl] at hincl
  · simp only [if_neg hincl]
    refine ⟨Val.sign_ext (zOfNat 16) (Regmap.get r e), rfl,
      CompCert4Lean.Common.Values.Val.lessdef_refl _⟩

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.ConstpropOp
open Lean Elab Tactic Meta

private def worker_is_uns
    (n : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (i : CompCert4Lean.Lib.Integers.int) : Prop :=
  ∀ m, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
      (.Z0) m ∧
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt m
        CompCert4Lean.Lib.Integers.Int.zwordsize →
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le n m →
    CompCert4Lean.Lib.Integers.Int.testbit i m = false

private def worker_suffixPrivateName2 (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem worker_int_and_val (x y : CompCert4Lean.Lib.Integers.Int.int) :
    (CompCert4Lean.Lib.Integers.WordCore.and x y).val = Nat.land x.val y.val := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let yF := (lctx.findFromUserName? `y).get!
    let e ← mkAppM
      (worker_suffixPrivateName2 "CompCert4Lean.Lib.Integers.Int.suffix_and_val")
      #[mkFVar xF.fvarId, mkFVar yF.fvarId]
    closeMainGoal Name.anonymous e

private theorem worker_int_testbit_nat
    (x : CompCert4Lean.Lib.Integers.Int.int) (n : Nat) :
    CompCert4Lean.Lib.Integers.Int.testbit x (zOfNat n) = Nat.testBit x.val n := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let nF := (lctx.findFromUserName? `n).get!
    let e ← mkAppM
      (worker_suffixPrivateName2 "CompCert4Lean.Lib.Integers.Int.suffix_testbit_nat")
      #[mkFVar xF.fvarId, mkFVar nF.fvarId]
    closeMainGoal Name.anonymous e

private theorem worker_is_uns_zero_ext_16
    (i : CompCert4Lean.Lib.Integers.Int.int)
    (h : worker_is_uns (zOfNat 16) i) :
    CompCert4Lean.Lib.Integers.Int.zero_ext (zOfNat 16) i = i := by
  have hval : i.val < 2 ^ 16 := by
    by_cases hlt : i.val < 2 ^ 16
    · exact hlt
    have hge : 2 ^ 16 ≤ i.val := Nat.le_of_not_gt hlt
    rcases Nat.exists_ge_and_testBit_of_ge_two_pow hge with ⟨j, hj, hbit⟩
    have hjlt : j < 32 := by
      by_cases hjlt : j < 32
      · exact hjlt
      have hj32 : 32 ≤ j := Nat.le_of_not_gt hjlt
      have hp : 2 ^ 32 ≤ 2 ^ j := Nat.pow_le_pow_right Nat.zero_lt_two hj32
      have hival : i.val < 2 ^ 32 := i.toFin.isLt
      have hij : i.val < 2 ^ j := Nat.lt_of_lt_of_le hival hp
      rw [Nat.testBit_lt_two_pow hij] at hbit
      cases hbit
    have hfalse := h (zOfNat j) (by
      constructor
      · change intOfZ .Z0 ≤ intOfZ (zOfNat j)
        have hjz : zOfNat j = zOfInt (Int.ofNat j) := by rfl
        rw [hjz, intOfZ_zOfInt]
        change (0 : Int) ≤ Int.ofNat j
        exact Int.natCast_nonneg _
      · change intOfZ (zOfNat j) < intOfZ Int.zwordsize
        have hjz : zOfNat j = zOfInt (Int.ofNat j) := by rfl
        rw [hjz, intOfZ_zOfInt]
        change (Int.ofNat j) < 32
        exact Int.ofNat_lt.mpr hjlt)
      (by
        change intOfZ (zOfNat 16) ≤ intOfZ (zOfNat j)
        have hjz : zOfNat j = zOfInt (Int.ofNat j) := by rfl
        rw [hjz, intOfZ_zOfInt]
        have h16z : zOfNat 16 = zOfInt (Int.ofNat 16) := by rfl
        rw [h16z, intOfZ_zOfInt]
        change (Int.ofNat 16) ≤ Int.ofNat j
        exact Int.ofNat_le.mpr hj)
    have hbit' : CompCert4Lean.Lib.Integers.Int.testbit i (zOfNat j) = true := by
      rw [worker_int_testbit_nat]
      exact hbit
    rw [hbit'] at hfalse
    cases hfalse
  rw [CompCert4Lean.Lib.Integers.Int.zero_ext_and_proof (zOfNat 16) i
    (by change (0 : Int) ≤ 16; omega)]
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  change (CompCert4Lean.Lib.Integers.WordCore.and i
    (CompCert4Lean.Lib.Integers.Int.repr
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpower.two_p (zOfNat 16))
        (zOfNat 1)))).val = i.val
  rw [worker_int_and_val]
  change Nat.land i.val 65535 = i.val
  exact Nat.and_two_pow_sub_one_of_lt_two_pow hval

theorem make_cast16unsigned_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @make_cast16unsigned_correctStatement binary64_certificate binary32_certificate := by
  intro bc ge sp e m r x hmatch
  dsimp [CompCert4Lean.X86.ConstpropOp.make_cast16unsigned]
  by_cases hincl : vincl x (Uns Ptop (zOfNat 16)) = true
  · simp only [if_pos hincl]
    refine ⟨Regmap.get r e, rfl, ?_⟩
    generalize hv : Regmap.get r e = w at hmatch
    cases x with
    | Vbot => cases hmatch
    | I i =>
        have hrewrite :
            vincl (I i) (Uns Ptop (zOfNat 16)) =
              (decide (CompCert4Lean.Lib.Integers.Int.zero_ext (zOfNat 16) i = i) &&
                worker_zle (.Z0) (zOfNat 16)) := by rfl
        rw [hrewrite] at hincl
        have hi : CompCert4Lean.Lib.Integers.Int.zero_ext (zOfNat 16) i = i :=
          of_decide_eq_true (Bool.and_eq_true_iff.mp hincl).1
        cases hmatch with
        | vmatch_i =>
            have hext : Val.zero_ext (zOfNat 16) (.Vint i) =
                .Vint (CompCert4Lean.Lib.Integers.Int.zero_ext (zOfNat 16) i) := by rfl
            rw [hext]
            rw [hi]
            exact CompCert4Lean.Common.Values.Val.lessdef_refl _
    | IU i =>
        have hrewrite :
            vincl (IU i) (Uns Ptop (zOfNat 16)) =
              (decide (CompCert4Lean.Lib.Integers.Int.zero_ext (zOfNat 16) i = i) &&
                worker_zle (.Z0) (zOfNat 16)) := by rfl
        rw [hrewrite] at hincl
        have hi : CompCert4Lean.Lib.Integers.Int.zero_ext (zOfNat 16) i = i :=
          of_decide_eq_true (Bool.and_eq_true_iff.mp hincl).1
        cases hmatch with
        | vmatch_iu =>
            have hext : Val.zero_ext (zOfNat 16) (.Vint i) =
                .Vint (CompCert4Lean.Lib.Integers.Int.zero_ext (zOfNat 16) i) := by rfl
            rw [hext]
            rw [hi]
            exact CompCert4Lean.Common.Values.Val.lessdef_refl _
        | iuUndef => exact CompCert4Lean.Common.Values.Val.lessdef_refl _
    | Uns p n =>
        have hrewrite :
            vincl (Uns p n) (Uns Ptop (zOfNat 16)) =
              (worker_zle n (zOfNat 16) && pincl p Ptop) := by rfl
        rw [hrewrite] at hincl
        have hp := Bool.and_eq_true_iff.mp hincl
        have hge : vge (Uns Ptop (zOfNat 16)) (Uns p n) :=
          vge.vge_uns_uns Ptop (zOfNat 16) p n (worker_zle_true hp.1)
            (pincl_ge p Ptop hp.2)
        have hmv := vmatch_ge bc w (Uns Ptop (zOfNat 16)) (Uns p n) hge hmatch
        cases hmv with
        | uns _ i _ _ hi =>
            have hi' : worker_is_uns (zOfNat 16) i := hi
            have hext : Val.zero_ext (zOfNat 16) (.Vint i) =
                .Vint (CompCert4Lean.Lib.Integers.Int.zero_ext (zOfNat 16) i) := by rfl
            rw [hext]
            rw [worker_is_uns_zero_ext_16 i hi']
            exact CompCert4Lean.Common.Values.Val.lessdef_refl _
        | vmatch_Uns_undef => exact CompCert4Lean.Common.Values.Val.lessdef_refl _
    | Sgn p n | L _ | F _ | FS _ | Num _ | Ptr _ | Ifptr _ =>
        simp [vincl] at hincl
  · simp only [if_neg hincl]
    refine ⟨Val.zero_ext (zOfNat 16) (Regmap.get r e), rfl,
      CompCert4Lean.Common.Values.Val.lessdef_refl _⟩

end CompCert4Lean.X86.ConstpropOpproof

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

private theorem cp_ptrofs_eq_of_eq_true {x y : Ptrofs.int}
    (h : Ptrofs.eq x y = true) : x = y := by
  unfold Ptrofs.eq WordCore.eq at h
  apply WordCore.ext
  exact of_decide_eq_true h

theorem const_for_result_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @const_for_result_correctStatement binary64_certificate binary32_certificate := by
  intro cfg bc ge hgenv sp hstack m ctx a op v hconst hvm
  cases a with
  | Vbot => simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
  | I n =>
      simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
      cases hconst
      cases hvm
      exact ⟨.Vint n, rfl, Val.lessdef_refl _⟩
  | IU n =>
      simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
      cases hconst
      cases hvm with
      | vmatch_iu => exact ⟨.Vint n, rfl, Val.lessdef_refl _⟩
      | iuUndef => exact ⟨.Vint n, rfl, Val.lessdef_undef _⟩
  | Uns p n => simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
  | Sgn p n => simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
  | L n =>
      simp [CompCert4Lean.X86.ConstpropOp.const_for_result,
        CompCert4Lean.X86_64.Archi.ptr64] at hconst
      cases hconst
      cases hvm
      exact ⟨.Vlong n, rfl, Val.lessdef_refl _⟩
  | F f =>
      cases hgen : CompCert4Lean.Driver.Compopts.generate_float_constants cfg with
      | false => simp [CompCert4Lean.X86.ConstpropOp.const_for_result, hgen] at hconst
      | true =>
          simp [CompCert4Lean.X86.ConstpropOp.const_for_result, hgen] at hconst
          cases hconst
          cases hvm
          exact ⟨.Vfloat f, rfl, Val.lessdef_refl _⟩
  | FS f =>
      cases hgen : CompCert4Lean.Driver.Compopts.generate_float_constants cfg with
      | false => simp [CompCert4Lean.X86.ConstpropOp.const_for_result, hgen] at hconst
      | true =>
          simp [CompCert4Lean.X86.ConstpropOp.const_for_result, hgen]
            at hconst
          cases hconst
          cases hvm
          exact ⟨.Vsingle f, rfl, Val.lessdef_refl _⟩
  | Num p => simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
  | Ifptr p => simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
  | Ptr p =>
      cases p with
      | Pbot => simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
      | Glo id => simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
      | Glob => simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
      | Stack => simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
      | Nonstack => simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
      | Ptop => simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
      | Gl id ofs =>
          by_cases hrel : symbol_is_relocatable ctx id = true
          · by_cases hzero : Ptrofs.eq ofs Ptrofs.zero = true
            · simp [CompCert4Lean.X86.ConstpropOp.const_for_result, hrel, hzero] at hconst
              cases hconst
              cases hvm with
              | ptrUndef => exact ⟨Genv.symbol_address ge id Ptrofs.zero, rfl, Val.lessdef_undef _⟩
              | ptr b ofs' p hp =>
                  cases hp with
                  | gl id hbc =>
                      have hz : ofs = Ptrofs.zero :=
                        cp_ptrofs_eq_of_eq_true hzero
                      subst ofs
                      have hfind : Genv.find_symbol ge id = some b :=
                        (hgenv.1 id b).mpr hbc
                      have haddr : Genv.symbol_address ge id Ptrofs.zero =
                          .Vptr b Ptrofs.zero := by
                        simp [Genv.symbol_address, hfind]
                      refine ⟨Genv.symbol_address ge id Ptrofs.zero, rfl, ?_⟩
                      rw [haddr]
                      exact Val.lessdef_refl _
            · simp [CompCert4Lean.X86.ConstpropOp.const_for_result, hrel, hzero] at hconst
          · simp [CompCert4Lean.X86.ConstpropOp.const_for_result, hrel,
              CompCert4Lean.X86_64.Archi.ptr64] at hconst
            cases hconst
            cases hvm with
            | ptrUndef => exact ⟨Genv.symbol_address ge id ofs, rfl, Val.lessdef_undef _⟩
            | ptr b ofs' p hp =>
                cases hp with
                | gl id hbc =>
                    have hfind : Genv.find_symbol ge id = some b :=
                      (hgenv.1 id b).mpr hbc
                    have haddr : Genv.symbol_address ge id ofs =
                        .Vptr b ofs := by
                      simp [Genv.symbol_address, hfind]
                    refine ⟨Genv.symbol_address ge id ofs, ?_, ?_⟩
                    · rw [eval_Olea_ptr]
                      exact CompCert4Lean.X86.Op.eval_addressing_Aglobal _ _ ge (.Vptr sp Ptrofs.zero) id ofs
                    · rw [haddr]
                      exact Val.lessdef_refl _
      | Stk ofs =>
          simp [CompCert4Lean.X86.ConstpropOp.const_for_result,
            CompCert4Lean.X86_64.Archi.ptr64] at hconst
          cases hconst
          cases hvm with
          | ptrUndef => exact ⟨Val.offset_ptr (.Vptr sp Ptrofs.zero) ofs, rfl, Val.lessdef_undef _⟩
          | ptr b ofs' p hp =>
              cases hp with
              | stk hbc =>
                  have hb : b = sp := bc.bc_stack b sp hbc hstack
                  subst b
                  refine ⟨.Vptr sp ofs, ?_, Val.lessdef_refl _⟩
                  rw [eval_Olea_ptr]
                  have hz : Ptrofs.add Ptrofs.zero ofs = ofs := by
                    change WordCore.add (WordCore.zero Ptrofs.wordsize) ofs = ofs
                    apply WordCore.ext_of_val_eq
                    rw [cp_word_add_val]
                    change (0 + ofs.val) % (2 ^ Ptrofs.wordsize) = ofs.val
                    rw [Nat.zero_add, Nat.mod_eq_of_lt]
                    exact ofs.toFin.isLt
                  simpa [Val.offset_ptr, hz] using
                    (CompCert4Lean.X86.Op.eval_addressing_Ainstack _ _ ge
                      (.Vptr sp Ptrofs.zero) ofs)

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.ConstpropOp

private theorem cp_cond_int_value {bc : block_classification} {v : val} {n : int}
    (h : vmatch bc v (.I n)) : v = .Vint n := by
  cases h
  rfl

private theorem cp_cond_long_value {bc : block_classification} {v : val} {n : int64}
    (h : vmatch bc v (.L n)) : v = .Vlong n := by
  cases h
  rfl

theorem cond_strength_reduction_correct : cond_strength_reduction_correctStatement := by
  intro bc ae e m hem cond args vl hvl
  unfold cond_strength_reduction
  cases hred : cond_strength_reduction_match cond args vl with
  | cond_strength_reduction_case1 c r1 r2 n1 v2 =>
      have hv : Regmap.get r1 e = .Vint n1 := by
        apply cp_cond_int_value
        rw [(List.cons.inj hvl).1]
        exact hem r1
      simp only [reg_values, List.map_cons, List.map_nil, eval_condition, hv]
      exact Val.swap_cmp_bool c (Regmap.get r2 e) (.Vint n1)
  | cond_strength_reduction_case2 c r1 r2 v1 n2 =>
      have hv : Regmap.get r2 e = .Vint n2 := by
        apply cp_cond_int_value
        rw [(List.cons.inj (List.cons.inj hvl).2).1]
        exact hem r2
      simp only [reg_values, List.map_cons, List.map_nil, eval_condition, hv]
  | cond_strength_reduction_case3 c r1 r2 n1 v2 =>
      have hv : Regmap.get r1 e = .Vint n1 := by
        apply cp_cond_int_value
        rw [(List.cons.inj hvl).1]
        exact hem r1
      simp only [reg_values, List.map_cons, List.map_nil, eval_condition, hv]
      exact Val.swap_cmpu_bool _ c (Regmap.get r2 e) (.Vint n1)
  | cond_strength_reduction_case4 c r1 r2 v1 n2 =>
      have hv : Regmap.get r2 e = .Vint n2 := by
        apply cp_cond_int_value
        rw [(List.cons.inj (List.cons.inj hvl).2).1]
        exact hem r2
      simp only [reg_values, List.map_cons, List.map_nil, eval_condition, hv]
  | cond_strength_reduction_case5 c r1 r2 n1 v2 =>
      have hv : Regmap.get r1 e = .Vlong n1 := by
        apply cp_cond_long_value
        rw [(List.cons.inj hvl).1]
        exact hem r1
      simp only [reg_values, List.map_cons, List.map_nil, eval_condition, hv]
      exact Val.swap_cmpl_bool c (Regmap.get r2 e) (.Vlong n1)
  | cond_strength_reduction_case6 c r1 r2 v1 n2 =>
      have hv : Regmap.get r2 e = .Vlong n2 := by
        apply cp_cond_long_value
        rw [(List.cons.inj (List.cons.inj hvl).2).1]
        exact hem r2
      simp only [reg_values, List.map_cons, List.map_nil, eval_condition, hv]
  | cond_strength_reduction_case7 c r1 r2 n1 v2 =>
      have hv : Regmap.get r1 e = .Vlong n1 := by
        apply cp_cond_long_value
        rw [(List.cons.inj hvl).1]
        exact hem r1
      simp only [reg_values, List.map_cons, List.map_nil, eval_condition, hv]
      exact Val.swap_cmplu_bool _ c (Regmap.get r2 e) (.Vlong n1)
  | cond_strength_reduction_case8 c r1 r2 v1 n2 =>
      have hv : Regmap.get r2 e = .Vlong n2 := by
        apply cp_cond_long_value
        rw [(List.cons.inj (List.cons.inj hvl).2).1]
        exact hem r2
      simp only [reg_values, List.map_cons, List.map_nil, eval_condition, hv]
  | cond_strength_reduction_default cond args vl => rfl

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.ConstpropOp

private theorem cp_addr32_repr_add (x y : Z) :
    CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.add x y) =
      CompCert4Lean.Lib.Integers.Int.add
        (CompCert4Lean.Lib.Integers.Int.repr x)
        (CompCert4Lean.Lib.Integers.Int.repr y) := by
  apply CompCert4Lean.Lib.Integers.Int.eqm_samerepr_proof
  exact CompCert4Lean.Lib.Integers.Int.eqm_add_proof _ _ _ _
    (CompCert4Lean.Lib.Integers.Int.eqm_unsigned_repr_r_proof x x
      (CompCert4Lean.Lib.Integers.Int.eqm_refl_proof x))
    (CompCert4Lean.Lib.Integers.Int.eqm_unsigned_repr_r_proof y y
      (CompCert4Lean.Lib.Integers.Int.eqm_refl_proof y))

private theorem cp_addr32_signed_add (x : int) (y : Z) :
    CompCert4Lean.Lib.Integers.Int.repr
      (ZArith.BinInt.Z.add (CompCert4Lean.Lib.Integers.Int.signed x) y) =
      CompCert4Lean.Lib.Integers.Int.add x
        (CompCert4Lean.Lib.Integers.Int.repr y) := by
  rw [cp_addr32_repr_add, CompCert4Lean.Lib.Integers.Int.repr_signed_proof]

private theorem cp_addr32_signed_mul (x : int) (y : Z) :
    CompCert4Lean.Lib.Integers.Int.repr
      (ZArith.BinInt.Z.mul (CompCert4Lean.Lib.Integers.Int.signed x) y) =
      CompCert4Lean.Lib.Integers.Int.mul x
        (CompCert4Lean.Lib.Integers.Int.repr y) := by
  apply CompCert4Lean.Lib.Integers.Int.eqm_samerepr_proof
  exact CompCert4Lean.Lib.Zbits.eqmod_mult _ _ _ _ _
    (CompCert4Lean.Lib.Integers.Int.eqm_signed_unsigned_proof x)
    (CompCert4Lean.Lib.Integers.Int.eqm_unsigned_repr_r_proof y y
      (CompCert4Lean.Lib.Integers.Int.eqm_refl_proof y))

theorem addr_strength_reduction_32_generic_correct :
    addr_strength_reduction_32_generic_correctStatement := by
  intro bc ge sp ae e hem addr args vl res hvl heval
  unfold addr_strength_reduction_32_generic
  cases hred : addr_strength_reduction_32_generic_match addr args vl with
  | addr_strength_reduction_32_generic_case1 ofs r1 r2 n1 v2 =>
      have hv : Regmap.get r1 e = .Vint n1 := by
        apply cp_cond_int_value
        rw [(List.cons.inj hvl).1]
        exact hem r1
      simp only [reg_values, List.map_cons, List.map_nil, eval_addressing32,
        hv, Option.some.injEq] at heval
      refine ⟨_, rfl, ?_⟩
      rw [← heval, cp_addr32_signed_add]
      change Val.lessdef
        (Val.add (Val.add (.Vint n1) (Regmap.get r2 e))
          (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs)))
        (Val.add (Regmap.get r2 e)
          (Val.add (.Vint n1) (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs))))
      rw [Val.add_assoc, Val.add_permut (.Vint n1)]
      exact Val.lessdef_refl _
  | addr_strength_reduction_32_generic_case2 ofs r1 r2 v1 n2 =>
      have hv : Regmap.get r2 e = .Vint n2 := by
        apply cp_cond_int_value
        rw [(List.cons.inj (List.cons.inj hvl).2).1]
        exact hem r2
      simp only [reg_values, List.map_cons, List.map_nil, eval_addressing32,
        hv, Option.some.injEq] at heval
      refine ⟨_, rfl, ?_⟩
      rw [← heval, cp_addr32_signed_add]
      change Val.lessdef
        (Val.add (Val.add (Regmap.get r1 e) (.Vint n2))
          (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs)))
        (Val.add (Regmap.get r1 e)
          (Val.add (.Vint n2) (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs))))
      rw [Val.add_assoc]
      exact Val.lessdef_refl _
  | addr_strength_reduction_32_generic_case3 sc ofs r1 r2 v1 n2 =>
      have hv : Regmap.get r2 e = .Vint n2 := by
        apply cp_cond_int_value
        rw [(List.cons.inj (List.cons.inj hvl).2).1]
        exact hem r2
      simp only [reg_values, List.map_cons, List.map_nil, eval_addressing32,
        hv, Option.some.injEq] at heval
      refine ⟨_, rfl, ?_⟩
      rw [← heval, cp_addr32_repr_add, cp_addr32_signed_mul]
      exact Val.lessdef_refl _
  | addr_strength_reduction_32_generic_case4 sc ofs r1 r2 n1 v2 =>
      have hv : Regmap.get r1 e = .Vint n1 := by
        apply cp_cond_int_value
        rw [(List.cons.inj hvl).1]
        exact hem r1
      simp only [reg_values, List.map_cons, List.map_nil, eval_addressing32,
        hv, Option.some.injEq] at heval
      refine ⟨_, rfl, ?_⟩
      rw [← heval, cp_addr32_signed_add]
      change Val.lessdef
        (Val.add (.Vint n1)
          (Val.add (Val.mul (Regmap.get r2 e)
            (.Vint (CompCert4Lean.Lib.Integers.Int.repr sc)))
            (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs))))
        (Val.add (Val.mul (Regmap.get r2 e)
          (.Vint (CompCert4Lean.Lib.Integers.Int.repr sc)))
          (Val.add (.Vint n1) (.Vint (CompCert4Lean.Lib.Integers.Int.repr ofs))))
      rw [Val.add_permut (.Vint n1)]
      exact Val.lessdef_refl _
  | addr_strength_reduction_32_generic_default addr args vl =>
      exact ⟨res, heval, Val.lessdef_refl _⟩

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

/-- In the fixed x86-64 architecture, 32-bit address reduction uses the generic path. -/
theorem addr_strength_reduction_32_correct :
    addr_strength_reduction_32_correctStatement := by
  intro bc ge _ sp _ ae e hem addr args vl res hvl heval
  exact addr_strength_reduction_32_generic_correct
    bc ge sp ae e hem addr args vl res hvl heval

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.ConstpropOp

private theorem cp64_unsigned_nat (x : int64) :
    intOfZ (CompCert4Lean.Lib.Integers.Int64.unsigned x) = (x.val : _root_.Int) := by
  have hnonneg : ZArith.BinInt.Z.le .Z0 x.intval := by
    have h := x.intrange.1
    change (-1 : _root_.Int) < intOfZ x.intval at h
    change 0 ≤ intOfZ x.intval
    omega
  have h := (ZArith.Znat.Z2Nat.id x.intval hnonneg).symm
  change x.intval = zOfNat x.val at h
  change intOfZ x.intval = _
  rw [h]
  exact intOfZ_zOfInt _

private theorem cp64_unsigned_repr (x : Z) :
    intOfZ (CompCert4Lean.Lib.Integers.Int64.unsigned (CompCert4Lean.Lib.Integers.Int64.repr x)) =
      intOfZ x % (2 ^ 64 : _root_.Int) := by
  rw [cp64_unsigned_nat]
  have hx : x = zOfInt (intOfZ x) := (zOfInt_intOfZ x).symm
  rw [hx]
  change ((WordCore.repr 64 (zOfInt (intOfZ x))).val : _root_.Int) = _
  rw [cp_suffixWordValRepr64]
  simp only [intOfZ_zOfInt]
  exact _root_.Int.toNat_of_nonneg (_root_.Int.emod_nonneg _ (by decide))

private theorem cp64_repr_add (x y : Z) :
    CompCert4Lean.Lib.Integers.Int64.repr (ZArith.BinInt.Z.add x y) =
      CompCert4Lean.Lib.Integers.Int64.add (CompCert4Lean.Lib.Integers.Int64.repr x) (CompCert4Lean.Lib.Integers.Int64.repr y) := by
  apply WordCore.ext
  apply intOfZ_injective
  change intOfZ (CompCert4Lean.Lib.Integers.Int64.unsigned (CompCert4Lean.Lib.Integers.Int64.repr (ZArith.BinInt.Z.add x y))) =
    intOfZ (CompCert4Lean.Lib.Integers.Int64.unsigned (CompCert4Lean.Lib.Integers.Int64.repr
      (ZArith.BinInt.Z.add (CompCert4Lean.Lib.Integers.Int64.unsigned (CompCert4Lean.Lib.Integers.Int64.repr x))
        (CompCert4Lean.Lib.Integers.Int64.unsigned (CompCert4Lean.Lib.Integers.Int64.repr y)))))
  simp only [cp64_unsigned_repr, ZArith.BinInt.Z.add, intOfZ_zOfInt]
  exact _root_.Int.add_emod _ _ _

private theorem cp64_repr_mul (x y : Z) :
    CompCert4Lean.Lib.Integers.Int64.repr (ZArith.BinInt.Z.mul x y) =
      CompCert4Lean.Lib.Integers.Int64.mul (CompCert4Lean.Lib.Integers.Int64.repr x) (CompCert4Lean.Lib.Integers.Int64.repr y) := by
  apply WordCore.ext
  apply intOfZ_injective
  change intOfZ (CompCert4Lean.Lib.Integers.Int64.unsigned (CompCert4Lean.Lib.Integers.Int64.repr (ZArith.BinInt.Z.mul x y))) =
    intOfZ (CompCert4Lean.Lib.Integers.Int64.unsigned (CompCert4Lean.Lib.Integers.Int64.repr
      (ZArith.BinInt.Z.mul (CompCert4Lean.Lib.Integers.Int64.unsigned (CompCert4Lean.Lib.Integers.Int64.repr x))
        (CompCert4Lean.Lib.Integers.Int64.unsigned (CompCert4Lean.Lib.Integers.Int64.repr y)))))
  simp only [cp64_unsigned_repr, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
  exact _root_.Int.mul_emod _ _ _

private theorem cp64_signed_add (x : int64) (y : Z) :
    CompCert4Lean.Lib.Integers.Int64.repr (ZArith.BinInt.Z.add (CompCert4Lean.Lib.Integers.Int64.signed x) y) =
      CompCert4Lean.Lib.Integers.Int64.add x (CompCert4Lean.Lib.Integers.Int64.repr y) := by
  rw [cp64_repr_add, cp_int64_repr_signed]

private theorem cp64_signed_mul (x : int64) (y : Z) :
    CompCert4Lean.Lib.Integers.Int64.repr (ZArith.BinInt.Z.mul (CompCert4Lean.Lib.Integers.Int64.signed x) y) =
      CompCert4Lean.Lib.Integers.Int64.mul x (CompCert4Lean.Lib.Integers.Int64.repr y) := by
  rw [cp64_repr_mul, cp_int64_repr_signed]

private theorem cp64_generic :
    addr_strength_reduction_64_generic_correctStatement := by
  intro bc ge sp ae e hem addr args vl res hvl heval
  unfold addr_strength_reduction_64_generic
  cases hred : addr_strength_reduction_64_generic_match addr args vl with
  | addr_strength_reduction_64_generic_case1 ofs r1 r2 n1 v2 =>
      have hv : Regmap.get r1 e = .Vlong n1 := by
        apply cp_cond_long_value
        rw [(List.cons.inj hvl).1]
        exact hem r1
      simp only [reg_values, List.map_cons, List.map_nil, eval_addressing64,
        hv, Option.some.injEq] at heval
      refine ⟨_, rfl, ?_⟩
      rw [← heval, cp64_signed_add]
      change Val.lessdef
        (Val.addl (Val.addl (.Vlong n1) (Regmap.get r2 e))
          (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr ofs)))
        (Val.addl (Regmap.get r2 e)
          (Val.addl (.Vlong n1) (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr ofs))))
      rw [Val.addl_assoc, Val.addl_permut (.Vlong n1)]
      exact Val.lessdef_refl _
  | addr_strength_reduction_64_generic_case2 ofs r1 r2 v1 n2 =>
      have hv : Regmap.get r2 e = .Vlong n2 := by
        apply cp_cond_long_value
        rw [(List.cons.inj (List.cons.inj hvl).2).1]
        exact hem r2
      simp only [reg_values, List.map_cons, List.map_nil, eval_addressing64,
        hv, Option.some.injEq] at heval
      refine ⟨_, rfl, ?_⟩
      rw [← heval, cp64_signed_add]
      change Val.lessdef
        (Val.addl (Val.addl (Regmap.get r1 e) (.Vlong n2))
          (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr ofs)))
        (Val.addl (Regmap.get r1 e)
          (Val.addl (.Vlong n2) (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr ofs))))
      rw [Val.addl_assoc]
      exact Val.lessdef_refl _
  | addr_strength_reduction_64_generic_case3 sc ofs r1 r2 v1 n2 =>
      have hv : Regmap.get r2 e = .Vlong n2 := by
        apply cp_cond_long_value
        rw [(List.cons.inj (List.cons.inj hvl).2).1]
        exact hem r2
      simp only [reg_values, List.map_cons, List.map_nil, eval_addressing64,
        hv, Option.some.injEq] at heval
      refine ⟨_, rfl, ?_⟩
      rw [← heval, cp64_repr_add, cp64_signed_mul]
      exact Val.lessdef_refl _
  | addr_strength_reduction_64_generic_case4 sc ofs r1 r2 n1 v2 =>
      have hv : Regmap.get r1 e = .Vlong n1 := by
        apply cp_cond_long_value
        rw [(List.cons.inj hvl).1]
        exact hem r1
      simp only [reg_values, List.map_cons, List.map_nil, eval_addressing64,
        hv, Option.some.injEq] at heval
      refine ⟨_, rfl, ?_⟩
      rw [← heval, cp64_signed_add]
      change Val.lessdef
        (Val.addl (.Vlong n1)
          (Val.addl (Val.mull (Regmap.get r2 e)
            (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr sc)))
            (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr ofs))))
        (Val.addl (Val.mull (Regmap.get r2 e)
          (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr sc)))
          (Val.addl (.Vlong n1) (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr ofs))))
      rw [Val.addl_permut (.Vlong n1)]
      exact Val.lessdef_refl _
  | addr_strength_reduction_64_generic_default addr args vl =>
      exact ⟨res, heval, Val.lessdef_refl _⟩


end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.ConstpropOp

private theorem cp64_of_int64 (x : int64) : Ptrofs.of_int64 x = x := by
  exact worker_int64_repr_unsigned x

private theorem cp64_zero_add (x : ptrofs) : Ptrofs.add Ptrofs.zero x = x := by
  rw [Ptrofs.add_commut_proof_api, cp_ptrofs_add_zero]

private theorem cp64_gl {bc : block_classification} {ge : genv}
    {v : val} {id : ident} {ofs : ptrofs}
    (hge : genv_match bc ge) (hv : vmatch bc v (.Ptr (.Gl id ofs))) :
    Val.lessdef v (Genv.symbol_address ge id ofs) := by
  cases hv with
  | ptrUndef => exact Val.lessdef_undef _
  | ptr b ofs p hp =>
      cases hp with
      | gl id hbc =>
          have hf := (hge.1 id b).mpr hbc
          simp only [Genv.symbol_address, hf]
          exact Val.lessdef_refl _

private theorem cp64_stk {bc : block_classification} {sp : block}
    {v : val} {ofs : ptrofs}
    (hsp : bc sp = BCstack) (hv : vmatch bc v (.Ptr (.Stk ofs))) :
    Val.lessdef v (.Vptr sp ofs) := by
  cases hv with
  | ptrUndef => exact Val.lessdef_undef _
  | ptr b ofs p hp =>
      cases hp with
      | stk hbc =>
          have hb := bc.bc_stack b sp hbc hsp
          subst b
          exact Val.lessdef_refl _

private theorem cp64_shift (ge : genv) (id : ident) (ofs : ptrofs) (n : Z) :
    Genv.symbol_address ge id (Ptrofs.add ofs (Ptrofs.repr n)) =
      Val.addl (Genv.symbol_address ge id ofs)
        (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr n)) := by
  have h := Genv.shift_symbol_address_64 _ _ ge id ofs
    (CompCert4Lean.Lib.Integers.Int64.repr n) rfl
  rw [cp64_of_int64] at h
  exact h

end CompCert4Lean.X86.ConstpropOpproof

namespace CompCert4Lean.X86.ConstpropOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.ConstpropOp

private theorem cp64_of_repr (n : Z) :
    Ptrofs.of_int64 (CompCert4Lean.Lib.Integers.Int64.repr n) = Ptrofs.repr n := by
  exact cp64_of_int64 _

theorem addr_strength_reduction_64_correct :
    addr_strength_reduction_64_correctStatement := by
  intro bc ge hge sp hsp ae e hem addr args vl res hvl heval
  unfold addr_strength_reduction_64
  simp only [CompCert4Lean.X86_64.Archi.ptr64, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  cases hred : addr_strength_reduction_64_match addr args vl with
  | addr_strength_reduction_64_case1 ofs r1 symb n =>
      have hp : vmatch bc (Regmap.get r1 e) (.Ptr (.Gl symb n)) := by
        rw [(List.cons.inj hvl).1]
        exact hem r1
      simp only [reg_values, List.map_cons, List.map_nil, eval_addressing64,
        Option.some.injEq] at heval
      refine ⟨_, rfl, ?_⟩
      rw [← heval, cp64_shift]
      exact Val.addl_lessdef _ _ _ _ (cp64_gl hge hp) (Val.lessdef_refl _)
  | addr_strength_reduction_64_case2 ofs r1 n =>
      have hp : vmatch bc (Regmap.get r1 e) (.Ptr (.Stk n)) := by
        rw [(List.cons.inj hvl).1]
        exact hem r1
      simp only [reg_values, List.map_cons, List.map_nil, eval_addressing64,
        Option.some.injEq] at heval
      refine ⟨_, rfl, ?_⟩
      rw [← heval]
      have h := Val.addl_lessdef _ _ _ _ (cp64_stk hsp hp)
        (Val.lessdef_refl (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr ofs)))
      simpa only [Val.addl, Val.offset_ptr, CompCert4Lean.X86_64.Archi.ptr64,
        ↓reduceIte, cp64_of_repr, cp64_zero_add] using h
  | addr_strength_reduction_64_case3 ofs r1 r2 symb n1 n2 =>
      have hp : vmatch bc (Regmap.get r1 e) (.Ptr (.Gl symb n1)) := by
        rw [(List.cons.inj hvl).1]
        exact hem r1
      have hv : Regmap.get r2 e = .Vlong n2 := by
        apply cp_cond_long_value
        rw [(List.cons.inj (List.cons.inj hvl).2).1]
        exact hem r2
      simp only [reg_values, List.map_cons, List.map_nil, eval_addressing64,
        hv, Option.some.injEq] at heval
      refine ⟨_, rfl, ?_⟩
      rw [← heval, cp64_shift, Genv.shift_symbol_address_64 _ _ ge symb n1 n2 rfl]
      exact Val.addl_lessdef _ _ _ _
        (Val.addl_lessdef _ _ _ _ (cp64_gl hge hp) (Val.lessdef_refl _))
        (Val.lessdef_refl _)
  | addr_strength_reduction_64_case4 ofs r1 r2 n1 symb n2 =>
      have hv : Regmap.get r1 e = .Vlong n1 := by
        apply cp_cond_long_value
        rw [(List.cons.inj hvl).1]
        exact hem r1
      have hp : vmatch bc (Regmap.get r2 e) (.Ptr (.Gl symb n2)) := by
        rw [(List.cons.inj (List.cons.inj hvl).2).1]
        exact hem r2
      simp only [reg_values, List.map_cons, List.map_nil, eval_addressing64,
        hv, Option.some.injEq] at heval
      refine ⟨_, rfl, ?_⟩
      rw [← heval, cp64_shift, Genv.shift_symbol_address_64 _ _ ge symb n2 n1 rfl,
        Val.addl_commut (.Vlong n1)]
      exact Val.addl_lessdef _ _ _ _
        (Val.addl_lessdef _ _ _ _ (cp64_gl hge hp) (Val.lessdef_refl _))
        (Val.lessdef_refl _)
  | addr_strength_reduction_64_case5 ofs r1 r2 n1 n2 =>
      have hp : vmatch bc (Regmap.get r1 e) (.Ptr (.Stk n1)) := by
        rw [(List.cons.inj hvl).1]
        exact hem r1
      have hv : Regmap.get r2 e = .Vlong n2 := by
        apply cp_cond_long_value
        rw [(List.cons.inj (List.cons.inj hvl).2).1]
        exact hem r2
      simp only [reg_values, List.map_cons, List.map_nil, eval_addressing64,
        hv, Option.some.injEq] at heval
      refine ⟨_, rfl, ?_⟩
      rw [← heval]
      have h := Val.addl_lessdef _ _ _ _
        (Val.addl_lessdef _ _ _ _ (cp64_stk hsp hp) (Val.lessdef_refl (.Vlong n2)))
        (Val.lessdef_refl (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr ofs)))
      simpa only [Val.addl, Val.offset_ptr, CompCert4Lean.X86_64.Archi.ptr64,
        ↓reduceIte, cp64_of_repr, cp64_zero_add] using h
  | addr_strength_reduction_64_case6 ofs r1 r2 n1 n2 =>
      have hv : Regmap.get r1 e = .Vlong n1 := by
        apply cp_cond_long_value
        rw [(List.cons.inj hvl).1]
        exact hem r1
      have hp : vmatch bc (Regmap.get r2 e) (.Ptr (.Stk n2)) := by
        rw [(List.cons.inj (List.cons.inj hvl).2).1]
        exact hem r2
      simp only [reg_values, List.map_cons, List.map_nil, eval_addressing64,
        hv, Option.some.injEq] at heval
      refine ⟨_, rfl, ?_⟩
      rw [← heval, Val.addl_commut (.Vlong n1)]
      have h := Val.addl_lessdef _ _ _ _
        (Val.addl_lessdef _ _ _ _ (cp64_stk hsp hp) (Val.lessdef_refl (.Vlong n1)))
        (Val.lessdef_refl (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr ofs)))
      simpa only [Val.addl, Val.offset_ptr, CompCert4Lean.X86_64.Archi.ptr64,
        ↓reduceIte, cp64_of_repr, cp64_zero_add,
        Ptrofs.add_commut_proof_api n2 (Ptrofs.of_int64 n1)] using h
  | addr_strength_reduction_64_case7 sc ofs r1 r2 symb n1 n2 =>
      have hp : vmatch bc (Regmap.get r1 e) (.Ptr (.Gl symb n1)) := by
        rw [(List.cons.inj hvl).1]
        exact hem r1
      have hv : Regmap.get r2 e = .Vlong n2 := by
        apply cp_cond_long_value
        rw [(List.cons.inj (List.cons.inj hvl).2).1]
        exact hem r2
      simp only [reg_values, List.map_cons, List.map_nil, eval_addressing64,
        hv, Option.some.injEq] at heval
      refine ⟨_, rfl, ?_⟩
      rw [← heval, cp64_shift, Genv.shift_symbol_address_64 _ _ ge symb n1
          (CompCert4Lean.Lib.Integers.Int64.mul n2
            (CompCert4Lean.Lib.Integers.Int64.repr sc)) rfl,
        Val.addl_assoc]
      exact Val.addl_lessdef _ _ _ _ (cp64_gl hge hp) (Val.lessdef_refl _)
  | addr_strength_reduction_64_default addr args vl =>
      exact cp64_generic bc ge sp ae e hem addr args vl res hvl heval

end CompCert4Lean.X86.ConstpropOpproof
