import CompCert4Lean.Backend.Constprop
import CompCert4Lean.Backend.RTL
import CompCert4Lean.Backend.Registers
import CompCert4Lean.Backend.ValueAnalysis
import CompCert4Lean.Backend.ValueDomain
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Builtins
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Common.Values
import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Maps
import CompCert4Lean.X86.ConstpropOp
import CompCert4Lean.X86.Machregs
import CompCert4Lean.X86.Op

/-!
# Correctness surface for constant propagation

Definition-bearing translation of CompCert's `backend/Constpropproof.v`.
Opaque proof bodies are represented by transparent proposition descriptors for
the later proof-migration phase.
-/

namespace CompCert4Lean.Backend.Constpropproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Constprop
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueAnalysis
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.ConstpropOp
open CompCert4Lean.X86.Machregs
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

private abbrev node := CompCert4Lean.Backend.RTL.node
private abbrev function := CompCert4Lean.Backend.RTL.function
private abbrev fundef := CompCert4Lean.Backend.RTL.fundef
private abbrev program := CompCert4Lean.Backend.RTL.program
private abbrev state := CompCert4Lean.Backend.RTL.state
private abbrev stackframe := CompCert4Lean.Backend.RTL.stackframe
private abbrev regset := CompCert4Lean.Backend.RTL.regset
private abbrev reg := CompCert4Lean.Backend.Registers.reg
private abbrev aenv := CompCert4Lean.Backend.ValueDomain.aenv
private abbrev block_classification := CompCert4Lean.Backend.ValueDomain.block_classification
private abbrev genv := CompCert4Lean.Backend.RTL.genv
private abbrev romem := CompCert4Lean.Backend.ValueDomain.romem
private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

def match_prog
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (prog tprog : program) : Prop :=
  @match_program fundef Unit fundef Unit
    (Linker_fundef function) Linker_unit
    (fun cu f tf =>
      tf = CompCert4Lean.Backend.Constprop.transf_fundef
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg cu) f)
    (fun x y : Unit => x = y) prog tprog

inductive match_pc (f : function) (rs : regset) (m : mem) : Nat → node → node → Prop where
  | match_pc_base (f rs m) (n : Nat) (pc : node) :
      match_pc f rs m n pc pc
  | match_pc_nop (f rs m) (n : Nat) (pc s pcx : node)
      (hcode : PTree.get pc f.fn_code = some (Inop s))
      (hmatch : match_pc f rs m n s pcx) :
      match_pc f rs m (Nat.succ n) pc pcx
  | match_pc_cond (f rs m) (n : Nat) (pc : node) (cond : condition) (args : List reg)
      (s1 s2 pcx : node)
      (hcode : PTree.get pc f.fn_code = some (Icond cond args s1 s2))
      (hmatch : ∀ b,
        eval_condition cond (args.map (fun r => Regmap.get r rs)) m = some b →
          match_pc f rs m n (if b then s1 else s2) pcx) :
      match_pc f rs m (Nat.succ n) pc pcx

inductive match_stackframes
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (prog : program) :
  stackframe → stackframe → Prop where
  | match_stackframe_intro (cfg prog)
      (res : reg) (sp : val) (pc : node) (rs : regset)
      (f : function) (rs' : regset) (cu : program)
      (hlink : linkorder cu prog)
      (hld : regs_lessdef rs rs') :
      match_stackframes
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg prog
        (Stackframe res f sp pc rs)
        (Stackframe res
          (CompCert4Lean.Backend.Constprop.transf_function
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            cfg (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg cu) f)
          sp pc rs')

inductive match_states
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (prog : program) :
    Nat → state → state → Prop where
  | match_states_intro (cfg prog)
      (s : List stackframe) (sp : val) (pc : node) (rs : regset) (m : mem)
      (f : function) (s' : List stackframe) (pc' : node) (rs' : regset)
      (m' : mem) (cu : program) (n : Nat)
      (hlink : linkorder cu prog)
      (hstacks : list_forall2
        (match_stackframes
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg prog) s s')
      (hpc : match_pc f rs m n pc pc')
      (hregs : regs_lessdef rs rs')
      (hmem : Mem.extends m m') :
      match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg prog n
        (State s f sp pc rs m)
        (State s'
          (CompCert4Lean.Backend.Constprop.transf_function
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            cfg (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg cu) f)
          sp pc' rs' m')
  | match_states_call (cfg prog)
      (s : List stackframe) (f : fundef) (args : List val) (m : mem)
      (s' : List stackframe) (args' : List val) (m' : mem) (cu : program)
      (hlink : linkorder cu prog)
      (hstacks : list_forall2
        (match_stackframes
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg prog) s s')
      (hargs : Val.lessdef_list args args')
      (hmem : Mem.extends m m') :
      match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg prog 0
        (Callstate s f args m)
        (Callstate s'
          (CompCert4Lean.Backend.Constprop.transf_fundef
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            cfg (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg cu) f)
          args' m')
  | match_states_return (cfg prog)
      (s : List stackframe) (v : val) (m : mem)
      (s' : List stackframe) (v' : val) (m' : mem)
      (hstacks : list_forall2
        (match_stackframes
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg prog) s s')
      (hres : Val.lessdef v v')
      (hmem : Mem.extends m m')
      (hstacks' : list_forall2
        (match_stackframes
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg prog) s s') :
      match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg prog 0
        (Returnstate s v m)
        (Returnstate s' v' m')

export match_pc (match_pc_base match_pc_nop match_pc_cond)
export match_stackframes (match_stackframe_intro)
export match_states (match_states_intro match_states_call match_states_return)

/-! Exact source statement descriptors for later proof migration. -/

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig)

def symbols_preservedStatement : Prop :=
  ∀ (prog tprog : program),
    match_prog
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog tprog →
    ∀ s : ident,
      Genv.find_symbol (Genv.globalenv tprog) s =
        Genv.find_symbol (Genv.globalenv prog) s

def senv_preservedStatement : Prop :=
  ∀ (prog tprog : program),
    match_prog
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog tprog →
    Senv.equiv (Genv.to_senv (Genv.globalenv prog))
      (Genv.to_senv (Genv.globalenv tprog))

def functions_translatedStatement : Prop :=
  ∀ (prog tprog : program),
    match_prog
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog tprog →
    ∀ (v : val) (f : fundef),
      Genv.find_funct (Genv.globalenv prog) v = some f →
      ∃ cu, Genv.find_funct (Genv.globalenv tprog) v =
        some (CompCert4Lean.Backend.Constprop.transf_fundef
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          cfg (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg cu) f) ∧
        linkorder cu prog

def function_ptr_translatedStatement : Prop :=
  ∀ (prog tprog : program),
    match_prog
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog tprog →
    ∀ (b : block) (f : fundef),
      Genv.find_funct_ptr (Genv.globalenv prog) b = some f →
      ∃ cu, Genv.find_funct_ptr (Genv.globalenv tprog) b =
        some (CompCert4Lean.Backend.Constprop.transf_fundef
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          cfg (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg cu) f) ∧
        linkorder cu prog

def sig_function_translatedStatement : Prop :=
  ∀ (rm : romem) (f : fundef),
    CompCert4Lean.Backend.RTL.funsig
      (CompCert4Lean.Backend.Constprop.transf_fundef
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg rm f) =
      CompCert4Lean.Backend.RTL.funsig f

def init_regs_lessdefStatement : Prop :=
  ∀ (rl : List reg) (vl1 vl2 : List val),
    Val.lessdef_list vl1 vl2 →
      regs_lessdef (init_regs vl1 rl) (init_regs vl2 rl)

def transf_ros_correctStatement : Prop :=
  ∀ (prog tprog : program),
    match_prog
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog tprog →
    ∀ (bc : block_classification) (rs : regset) (ae : aenv)
      (ros : Sum reg ident) (f : fundef) (rs' : regset),
      genv_match bc (Genv.globalenv prog) →
      ematch bc rs ae →
      find_function (Genv.globalenv prog) ros rs = some f →
      regs_lessdef rs rs' →
      ∃ cu, find_function (Genv.globalenv tprog) (transf_ros ae ros) rs' =
        some (CompCert4Lean.Backend.Constprop.transf_fundef
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          cfg (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg cu) f) ∧
        linkorder cu prog

def const_for_result_correctStatement : Prop :=
  ∀ (prog tprog : program),
    match_prog
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog tprog →
    ∀ (a : aval) (op : operation) (bc : block_classification) (v : val)
      (sp : block) (m : mem),
      const_for_result cfg cfg.relocation a = some op →
      vmatch bc v a →
      bc sp = BCstack →
      genv_match bc (Genv.globalenv prog) →
      ∃ v', eval_operation
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (Genv.globalenv tprog) (Vptr sp Ptrofs.zero) op [] m = some v' ∧
        Val.lessdef v v'

def match_successor_recStatement : Prop :=
  ∀ (f : function) (rs : regset) (m : mem)
    (bc : block_classification) (ae : aenv),
    ematch bc rs ae →
    ∀ (n : Nat) (pc : node),
      match_pc f rs m n pc (successor_rec cfg n f ae pc)

def match_successorStatement : Prop :=
  ∀ (f : function) (rs : regset) (m : mem)
    (bc : block_classification) (ae : aenv) (pc : node),
    ematch bc rs ae →
      match_pc f rs m num_iter pc (successor cfg f ae pc)

def builtin_arg_reduction_correctStatement : Prop :=
  ∀ (prog : program),
    ∀ (bc : block_classification) (sp : val) (m : mem) (rs : regset)
      (ae : aenv),
      ematch bc rs ae →
      ∀ (a : builtin_arg reg) (v : val),
        eval_builtin_arg (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
          sp m a v →
        eval_builtin_arg (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
          sp m (builtin_arg_reduction cfg ae a) v

def builtin_arg_strength_reduction_correctStatement : Prop :=
  ∀ (prog : program),
    ∀ (bc : block_classification) (sp : val) (m : mem) (rs : regset)
      (ae : aenv) (a : builtin_arg reg) (v : val)
      (c : builtin_arg_constraint),
      ematch bc rs ae →
      eval_builtin_arg (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
        sp m a v →
      eval_builtin_arg (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
        sp m (builtin_arg_strength_reduction cfg ae a c) v

def builtin_args_strength_reduction_correctStatement : Prop :=
  ∀ (prog : program),
    ∀ (bc : block_classification) (sp : val) (m : mem) (rs : regset)
      (ae : aenv),
      ematch bc rs ae →
      ∀ (al : List (builtin_arg reg)) (vl : List val),
        eval_builtin_args (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
          sp m al vl →
        ∀ cl : List builtin_arg_constraint,
          eval_builtin_args (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
            sp m (builtin_args_strength_reduction cfg ae al cl) vl

def debug_strength_reduction_correctStatement : Prop :=
  ∀ (prog : program),
    ∀ (bc : block_classification) (sp : val) (m : mem) (rs : regset)
      (ae : aenv),
      ematch bc rs ae →
      ∀ (al : List (builtin_arg reg)) (vl : List val),
        eval_builtin_args (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
          sp m al vl →
        ∃ vl', eval_builtin_args (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
          sp m (debug_strength_reduction cfg ae al) vl'

def builtin_strength_reduction_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    ∀ (sp : val) (bc : block_classification) (ae : aenv) (rs : regset)
      (ef : external_function) (args : List (builtin_arg reg)) (vargs : List val)
      (m : mem) (t : trace) (vres : val) (m' : mem),
      ematch bc rs ae →
      eval_builtin_args (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
        sp m args vargs →
      external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ef (Genv.to_senv (Genv.globalenv prog)) vargs m t vres m' →
      ∃ vargs',
        eval_builtin_args (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
          sp m (builtin_strength_reduction cfg ae ef args) vargs' ∧
        external_call
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          xi ef (Genv.to_senv (Genv.globalenv prog)) vargs' m t vres m'

def match_states_succStatement : Prop :=
  ∀ (prog : program) (s : List stackframe) (f : function) (sp : val)
    (pc : node) (rs : regset) (m : mem) (s' : List stackframe)
    (rs' : regset) (m' : mem) (cu : program),
    linkorder cu prog →
    list_forall2
      (match_stackframes
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg prog) s s' →
    regs_lessdef rs rs' →
    Mem.extends m m' →
    match_states
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog 0
      (State s f sp pc rs m)
      (State s'
        (CompCert4Lean.Backend.Constprop.transf_function
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          cfg (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg cu) f)
        sp pc rs' m')

def transf_instr_atStatement : Prop :=
  ∀ (rm : romem) (f : function) (pc : node)
    (i : CompCert4Lean.Backend.RTL.instruction),
    PTree.get pc f.fn_code = some i →
    PTree.get pc
      (CompCert4Lean.Backend.Constprop.transf_function
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg rm f).fn_code =
      some (CompCert4Lean.Backend.Constprop.transf_instr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg f
        (CompCert4Lean.Backend.ValueAnalysis.analyze
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg rm f)
        rm pc i)

def transf_step_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog tprog : program),
    match_prog
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog tprog →
    ∀ (s1 : state) (t : trace) (s2 : state),
      step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) s1 t s2 →
      ∀ (n1 : Nat) (s1' : state),
        ValueAnalysis.sound_state
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg prog s1 →
        match_states
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg prog n1 s1 s1' →
        (∃ n2 s2',
          step
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            xi (Genv.globalenv tprog) s1' t s2' ∧
          match_states
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) cfg prog n2 s2 s2') ∨
        (∃ n2, n2 < n1 ∧ t = E0 ∧
          match_states
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) cfg prog n2 s2 s1')

def transf_initial_statesStatement : Prop :=
  ∀ (prog tprog : program),
    match_prog
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog tprog →
    ∀ (st1 : state), initial_state prog st1 →
      ∃ n st2, initial_state tprog st2 ∧
        match_states
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg prog n st1 st2

def transf_final_statesStatement : Prop :=
  ∀ (prog : program) (n : Nat) (st1 st2 : state) (r : int),
    match_states
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog n st1 st2 →
    final_state st1 r → final_state st2 r

def transf_program_matchStatement : Prop :=
  ∀ (prog : program),
    match_prog
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog
      (transf_program
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg prog)

def transf_program_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog tprog : program),
    match_prog
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg prog tprog →
    forward_simulation
      (semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi prog)
      (semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi tprog)

end CompCert4Lean.Backend.Constpropproof

namespace CompCert4Lean.Backend.Constpropproof

open CompCert4Lean.Backend.Constprop
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.ValueAnalysis
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values

theorem builtin_arg_reduction_correct :
    ∀ (cfg : CompCert4Lean.Config.CompilerConfig),
      builtin_arg_reduction_correctStatement cfg := by
  intro cfg prog bc sp m rs ae hmatch a v hev
  induction hev with
  | eval_BA x =>
      have hx := hmatch x
      generalize hreg : Regmap.get x rs = vx at hx ⊢
      unfold builtin_arg_reduction
      generalize hax : AE.get x ae = av at hx ⊢
      cases av with
      | Vbot => cases hx
      | I n =>
          cases hx
          simpa [areg, hax, hreg] using (eval_BA_int n :
            eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
              (fun r => Regmap.get r rs) sp m (BA_int n) (Vint n))
      | IU n =>
          rw [← hreg]
          simpa [areg, hax] using (eval_BA x :
          eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
            (fun r => Regmap.get r rs) sp m (BA x) (Regmap.get x rs))
      | Uns p n =>
          rw [← hreg]
          simpa [areg, hax] using (eval_BA x :
          eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
            (fun r => Regmap.get r rs) sp m (BA x) (Regmap.get x rs))
      | Sgn p n =>
          rw [← hreg]
          simpa [areg, hax] using (eval_BA x :
          eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
            (fun r => Regmap.get r rs) sp m (BA x) (Regmap.get x rs))
      | L n =>
          cases hx
          simpa [areg, hax, hreg] using (eval_BA_long n :
            eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
              (fun r => Regmap.get r rs) sp m (BA_long n) (Vlong n))
      | F f =>
          cases hx
          by_cases hgen : CompCert4Lean.Driver.Compopts.generate_float_constants cfg
          · simpa [areg, hax, hgen, hreg] using (eval_BA_float f :
              eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
                (fun r => Regmap.get r rs) sp m (BA_float f) (Vfloat f))
          · rw [← hreg]
            simpa [areg, hax, hgen] using (eval_BA x :
              eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
                (fun r => Regmap.get r rs) sp m (BA x) (Regmap.get x rs))
      | FS f =>
          cases hx
          by_cases hgen : CompCert4Lean.Driver.Compopts.generate_float_constants cfg
          · simpa [areg, hax, hgen, hreg] using (eval_BA_single f :
              eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
                (fun r => Regmap.get r rs) sp m (BA_single f) (Vsingle f))
          · rw [← hreg]
            simpa [areg, hax, hgen] using (eval_BA x :
              eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
                (fun r => Regmap.get r rs) sp m (BA x) (Regmap.get x rs))
      | Num p =>
          rw [← hreg]
          simpa [areg, hax] using (eval_BA x :
          eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
            (fun r => Regmap.get r rs) sp m (BA x) (Regmap.get x rs))
      | Ptr p =>
          rw [← hreg]
          simpa [areg, hax] using (eval_BA x :
          eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
            (fun r => Regmap.get r rs) sp m (BA x) (Regmap.get x rs))
      | Ifptr p =>
          rw [← hreg]
          simpa [areg, hax] using (eval_BA x :
          eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
            (fun r => Regmap.get r rs) sp m (BA x) (Regmap.get x rs))
  | eval_BA_int n => exact eval_BA_int n
  | eval_BA_long n => exact eval_BA_long n
  | eval_BA_float n => exact eval_BA_float n
  | eval_BA_single n => exact eval_BA_single n
  | eval_BA_loadstack chunk ofs v load => exact eval_BA_loadstack chunk ofs v load
  | eval_BA_addrstack ofs => exact eval_BA_addrstack ofs
  | eval_BA_loadglobal chunk id ofs v load => exact eval_BA_loadglobal chunk id ofs v load
  | eval_BA_addrglobal id ofs => exact eval_BA_addrglobal id ofs
  | @eval_BA_splitlong hi lo vhi vlo eval_hi eval_lo ih_hi ih_lo =>
      dsimp [builtin_arg_reduction]
      generalize hhi : builtin_arg_reduction cfg ae hi = hi' at ih_hi ⊢
      generalize hlo : builtin_arg_reduction cfg ae lo = lo' at ih_lo ⊢
      cases hi' with
      | BA_int nhi =>
          cases lo' with
          | BA_int nlo =>
              cases ih_hi
              cases ih_lo
              simpa [builtin_arg_reduction, hhi, hlo, Val.longofwords] using
                (eval_BA_long (CompCert4Lean.Lib.Integers.Int64.ofwords nhi nlo) :
                  eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
                    (fun r => Regmap.get r rs) sp m
                    (BA_long (CompCert4Lean.Lib.Integers.Int64.ofwords nhi nlo))
                    (Vlong (CompCert4Lean.Lib.Integers.Int64.ofwords nhi nlo)))
          | _ => exact eval_BA_splitlong _ _ _ _ ih_hi ih_lo
      | _ =>
          exact eval_BA_splitlong _ _ _ _ ih_hi ih_lo
  | @eval_BA_addptr a1 a2 v1 v2 eval_a1 eval_a2 ih_a1 ih_a2 =>
      simpa [builtin_arg_reduction] using
        (eval_BA_addptr (builtin_arg_reduction cfg ae a1)
          (builtin_arg_reduction cfg ae a2) v1 v2 ih_a1 ih_a2)

end CompCert4Lean.Backend.Constpropproof

namespace CompCert4Lean.Backend.Constpropproof

open CompCert4Lean.Backend.Constprop
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

theorem transf_program_match : ∀ cfg, transf_program_matchStatement cfg := by
  letI : Linker (CompCert4Lean.Backend.RTL.fundef) :=
    Linker_fundef CompCert4Lean.Backend.RTL.function
  letI : Linker Unit := Linker_unit
  letI : Linker (CompCert4Lean.Backend.RTL.program) :=
    Linker_prog (CompCert4Lean.Backend.RTL.fundef) Unit
  intro cfg p
  unfold match_prog CompCert4Lean.Backend.Constprop.transf_program
    CompCert4Lean.Common.AST.transform_program
  constructor
  · induction p.prog_defs with
    | nil => exact list_forall2.nil _
    | cons hd tl ih =>
        cases hd with
        | mk id gd =>
            cases gd with
            | Gfun f =>
                change list_forall2 _
                  ((id, Gfun f) :: tl)
                  ((id, Gfun (CompCert4Lean.Backend.Constprop.transf_fundef
                    (binary64_certificate := binary64_certificate)
                    (binary32_certificate := binary32_certificate)
                    cfg (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg p) f)) ::
                    List.map (transform_program_globdef (fun f =>
                      CompCert4Lean.Backend.Constprop.transf_fundef
                        (binary64_certificate := binary64_certificate)
                        (binary32_certificate := binary32_certificate)
                        cfg (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg p) f)) tl)
                apply list_forall2.cons
                · constructor
                  · rfl
                  · apply match_globdef.match_globdef_fun (ctx' := p)
                    · exact linkorder_refl _
                    · rfl
                · exact ih
            | Gvar v =>
                change list_forall2 _
                  ((id, Gvar v) :: tl)
                  ((id, Gvar v) ::
                    List.map (transform_program_globdef (fun f =>
                      CompCert4Lean.Backend.Constprop.transf_fundef
                        (binary64_certificate := binary64_certificate)
                        (binary32_certificate := binary32_certificate)
                        cfg (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg p) f)) tl)
                apply list_forall2.cons
                · constructor
                  · rfl
                  · apply match_globdef.match_globdef_var
                    exact match_globvar.match_globvar_intro _ _ _ _ _ _ rfl
                · exact ih
  · exact ⟨rfl, rfl⟩

end CompCert4Lean.Backend.Constpropproof

namespace CompCert4Lean.Backend.Constpropproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

private theorem constprop_symbols_add_global
    (ge1 ge2 : Genv.t fundef Unit) (id : ident)
    (hm : ∀ id', PTree.get (show positive from id') ge2.genv_symb =
      PTree.get (show positive from id') ge1.genv_symb)
    (hn : ge2.genv_next = ge1.genv_next) :
    ∀ id', PTree.get (show positive from id')
        (PTree.set (show positive from id) ge2.genv_next ge2.genv_symb) =
      PTree.get (show positive from id')
        (PTree.set (show positive from id) ge1.genv_next ge1.genv_symb) := by
  intro id'
  have h2 := @PTree.getSet_equation _ (show positive from id')
    (show positive from id) ge2.genv_next ge2.genv_symb
  have h1 := @PTree.getSet_equation _ (show positive from id')
    (show positive from id) ge1.genv_next ge1.genv_symb
  by_cases h : id' = id
  · rw [h2, h1]
    simp only [dif_pos h]
    exact congrArg some hn
  · rw [h2, h1]
    simp only [dif_neg h]
    exact hm id'

private theorem constprop_symbols_add_globals
    (ge : Genv.t fundef Unit) (tge : Genv.t fundef Unit)
    (hnext : tge.genv_next = ge.genv_next)
    (hsym : ∀ s, Genv.find_symbol tge s = Genv.find_symbol ge s) :
    ∀ (l : List (ident × globdef fundef Unit))
      (tl : List (ident × globdef fundef Unit)),
      list_forall2 (fun x y => x.1 = y.1) l tl →
      ∀ s, Genv.find_symbol (Genv.add_globals tge tl) s =
        Genv.find_symbol (Genv.add_globals ge l) s := by
  intro l tl hlist
  induction hlist generalizing ge tge with
  | nil =>
      simpa [Genv.add_globals] using hsym
  | cons x y hxy htail ih =>
      cases x with
      | mk id gd =>
          cases y with
          | mk tid tgd =>
              have hid : id = tid := hxy
              subst tid
              have hnext' :
                  (Genv.add_global tge (id, tgd)).genv_next =
                    (Genv.add_global ge (id, gd)).genv_next := by
                change PArith.BinPos.Pos.succ tge.genv_next =
                  PArith.BinPos.Pos.succ ge.genv_next
                exact congrArg _ hnext
              have hsym' : ∀ s,
                  Genv.find_symbol (Genv.add_global tge (id, tgd)) s =
                    Genv.find_symbol (Genv.add_global ge (id, gd)) s := by
                intro s
                by_cases hs : s = id
                · change PTree.get (show positive from s)
                      (PTree.set (show positive from id) tge.genv_next tge.genv_symb) =
                    PTree.get (show positive from s)
                      (PTree.set (show positive from id) ge.genv_next ge.genv_symb)
                  calc
                    _ = (if h : (show positive from s) = (show positive from id) then
                        some tge.genv_next else
                          PTree.get (show positive from s) tge.genv_symb) :=
                      @PTree.getSet_equation _ (show positive from s)
                        (show positive from id) tge.genv_next tge.genv_symb
                    _ = (if h : (show positive from s) = (show positive from id) then
                        some ge.genv_next else
                          PTree.get (show positive from s) ge.genv_symb) := by
                      by_cases hcase : (show positive from s) = (show positive from id)
                      · simp only [dif_pos hcase]
                        exact congrArg some hnext
                      · exact False.elim (hcase hs)
                    _ = _ := (@PTree.getSet_equation _ (show positive from s)
                      (show positive from id) ge.genv_next ge.genv_symb).symm
                · change PTree.get (show positive from s)
                      (PTree.set (show positive from id) tge.genv_next tge.genv_symb) =
                    PTree.get (show positive from s)
                      (PTree.set (show positive from id) ge.genv_next ge.genv_symb)
                  exact (constprop_symbols_add_global ge tge id
                    (fun id' => hsym id') hnext s)
              simpa [Genv.add_globals] using ih
                (Genv.add_global ge (id, gd))
                (Genv.add_global tge (id, tgd)) hnext' hsym'

theorem symbols_preserved : ∀ cfg, symbols_preservedStatement cfg := by
  letI : Linker fundef := Linker_fundef function
  letI : Linker Unit := Linker_unit
  letI : Linker program := Linker_prog fundef Unit
  intro cfg prog tprog hm id
  unfold match_prog CompCert4Lean.Common.Linking.match_program at hm
  rcases hm with ⟨hdefs, hmain, hpublic⟩
  have hlist_of : ∀ (xs ys : List (ident × globdef fundef Unit)),
      list_forall2 (@match_ident_globdef program fundef Unit fundef Unit
        (Linker_prog fundef Unit)
        (fun (cu : program) f tf => tf =
          CompCert4Lean.Backend.Constprop.transf_fundef
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) cfg
            (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg cu) f)
        (fun x y : Unit => x = y) prog) xs ys →
      list_forall2 (fun x y => x.1 = y.1) xs ys := by
    intro xs ys h
    induction h with
    | nil => exact list_forall2.nil _
    | @cons x xs y ys hxy htail ih =>
        exact list_forall2.cons x y hxy.1 ih
  have hdefs' := hlist_of prog.prog_defs tprog.prog_defs hdefs
  unfold Genv.globalenv
  apply constprop_symbols_add_globals
    (Genv.empty_genv fundef Unit prog.prog_public)
    (Genv.empty_genv fundef Unit tprog.prog_public)
  · rfl
  · intro id'
    rfl
  · exact hdefs'

end CompCert4Lean.Backend.Constpropproof

namespace CompCert4Lean.Backend.Constpropproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

private theorem constprop_match_genvs_add_global
    (R : globdef fundef Unit → globdef fundef Unit → Prop)
    (ge1 ge2 : Genv.t fundef Unit) (id : ident)
    (g1 g2 : globdef fundef Unit)
    (hm : Genv.match_genvs R ge1 ge2) (hg : R g1 g2) :
    Genv.match_genvs R (Genv.add_global ge1 (id, g1))
      (Genv.add_global ge2 (id, g2)) := by
  constructor
  · change PArith.BinPos.Pos.succ ge2.genv_next =
      PArith.BinPos.Pos.succ ge1.genv_next
    exact congrArg PArith.BinPos.Pos.succ hm.mge_next
  · intro id'
    change PTree.get id' (PTree.set id ge2.genv_next ge2.genv_symb) =
      PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb)
    rw [@PTree.getSet_equation _
      (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id')
      (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
      ge2.genv_next ge2.genv_symb,
      @PTree.getSet_equation _
        (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id')
        (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
        ge1.genv_next ge1.genv_symb]
    by_cases h : id' = id
    · simp only [dif_pos h]
      exact congrArg some hm.mge_next
    · simp only [dif_neg h]
      exact hm.mge_symb id'
  · intro b
    change option_rel R
      (PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs))
      (PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs))
    have h1 := @PTree.getSet_equation (globdef fundef Unit)
      b ge1.genv_next g1 ge1.genv_defs
    have h2 := @PTree.getSet_equation (globdef fundef Unit)
      b ge2.genv_next g2 ge2.genv_defs
    by_cases h : b = ge1.genv_next
    · have h' : b = ge2.genv_next := h.trans hm.mge_next.symm
      rw [h1, h2]
      simp only [dif_pos h, dif_pos h']
      exact option_rel.some g1 g2 hg
    · have h' : b ≠ ge2.genv_next := by
        intro hb
        apply h
        exact hb.trans hm.mge_next
      rw [h1, h2]
      simp only [dif_neg h, dif_neg h']
      exact hm.mge_defs b

private theorem constprop_match_genvs_add_globals
    (R : globdef fundef Unit → globdef fundef Unit → Prop)
    (xs ys : List (ident × globdef fundef Unit))
    (hxy : list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) xs ys)
    (ge1 ge2 : Genv.t fundef Unit) (hm : Genv.match_genvs R ge1 ge2) :
    Genv.match_genvs R (Genv.add_globals ge1 xs) (Genv.add_globals ge2 ys) := by
  induction hxy generalizing ge1 ge2 with
  | nil => simpa [Genv.add_globals] using hm
  | @cons a xs b ys hab htail ih =>
      rcases a with ⟨aid, ag⟩
      rcases b with ⟨bid, bg⟩
      change aid = bid ∧ R ag bg at hab
      rcases hab with ⟨rfl, hab⟩
      simp only [Genv.add_globals, List.foldl_cons]
      apply ih
      simpa using (constprop_match_genvs_add_global R ge1 ge2 aid ag bg hm hab)

private theorem constprop_globalenvs_match
    (cfg : CompilerConfig) (prog tprog : program)
    (hm : match_prog cfg prog tprog) :
    Genv.match_genvs
      (@match_globdef program fundef Unit fundef Unit
        (@Linker_prog fundef Unit (Linker_fundef function) Linker_unit)
        (fun (cu : program) f tf =>
          tf = CompCert4Lean.Backend.Constprop.transf_fundef
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) cfg
            (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg cu) f)
        (fun x y : Unit => x = y) prog)
      (Genv.globalenv prog) (Genv.globalenv tprog) := by
  let R : globdef fundef Unit → globdef fundef Unit → Prop :=
    @match_globdef program fundef Unit fundef Unit
      (@Linker_prog fundef Unit (Linker_fundef function) Linker_unit)
      (fun (cu : program) f tf =>
        tf = CompCert4Lean.Backend.Constprop.transf_fundef
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg
          (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg cu) f)
      (fun x y : Unit => x = y) prog
  unfold match_prog match_program match_program_gen at hm
  have hempty : Genv.match_genvs R
      (Genv.empty_genv fundef Unit prog.prog_public)
      (Genv.empty_genv fundef Unit tprog.prog_public) := by
    constructor
    · rfl
    · intro id'
      rfl
    · intro b
      exact option_rel.none R
  have hlist_of : ∀ (xs ys : List (ident × globdef fundef Unit)),
      list_forall2 (@match_ident_globdef program fundef Unit fundef Unit
        (@Linker_prog fundef Unit (Linker_fundef function) Linker_unit)
        (fun (cu : program) f tf =>
          tf = CompCert4Lean.Backend.Constprop.transf_fundef
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) cfg
            (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg cu) f)
        (fun x y : Unit => x = y) prog) xs ys →
      list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) xs ys := by
    intro xs ys h
    induction h with
    | nil => exact list_forall2.nil _
    | @cons a xs b ys hab htail ih =>
        apply list_forall2.cons
        · exact ⟨hab.1, by simpa [R] using hab.2⟩
        · exact ih
  have hlist := hlist_of prog.prog_defs tprog.prog_defs hm.1
  exact constprop_match_genvs_add_globals R prog.prog_defs tprog.prog_defs
    hlist _ _ hempty

theorem function_ptr_translated : ∀ cfg, function_ptr_translatedStatement cfg := by
  letI : Linker fundef := Linker_fundef function
  letI : Linker Unit := Linker_unit
  letI : Linker program := Linker_prog fundef Unit
  intro cfg prog tprog hm b f hfind
  have hg := constprop_globalenvs_match cfg prog tprog hm
  unfold Genv.find_funct_ptr Genv.find_def at hfind ⊢
  cases h1 : PTree.get b (Genv.globalenv prog).genv_defs with
  | none => simp [h1] at hfind
  | some gd1 =>
      cases gd1 with
      | Gfun f1 =>
          have hf : f1 = f := by simpa [h1] using hfind
          subst f1
          cases h2 : PTree.get b (Genv.globalenv tprog).genv_defs with
          | none =>
              have hd := hg.mge_defs b
              simp [h1, h2] at hd
              cases hd
          | some gd2 =>
              cases gd2 with
              | Gfun f2 =>
                  have hd := hg.mge_defs b
                  simp [h1, h2] at hd
                  cases hd with
                  | some x y hrel =>
                      cases hrel with
                      | match_globdef_fun ctx' f1 f2 horder htrans =>
                          refine ⟨ctx', ?_, horder⟩
                          simpa [h2, htrans]
              | Gvar v2 =>
                  have hd := hg.mge_defs b
                  simp [h1, h2] at hd
                  cases hd with
                  | some x y hrel => cases hrel
      | Gvar v1 => simp [h1] at hfind

end CompCert4Lean.Backend.Constpropproof

namespace CompCert4Lean.Backend.Constpropproof

open CompCert4Lean.Backend.Constprop
open CompCert4Lean.Backend.ValueAnalysis
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Op

theorem builtin_arg_strength_reduction_correct :
    ∀ (cfg : CompCert4Lean.Config.CompilerConfig),
      builtin_arg_strength_reduction_correctStatement cfg := by
  intro cfg prog bc sp m rs ae a v c hmatch hev
  unfold builtin_arg_strength_reduction
  by_cases hok : builtin_arg_ok (builtin_arg_reduction cfg ae a) c = true
  · rw [if_pos hok]
    exact builtin_arg_reduction_correct cfg prog bc sp m rs ae hmatch a v hev
  · rw [if_neg hok]
    exact hev

end CompCert4Lean.Backend.Constpropproof

namespace CompCert4Lean.Backend.Constpropproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Integers

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

theorem functions_translated : ∀ cfg, functions_translatedStatement cfg := by
  letI : Linker fundef := Linker_fundef function
  letI : Linker Unit := Linker_unit
  letI : Linker program := Linker_prog fundef Unit
  intro cfg prog tprog hm v f hfind
  unfold Genv.find_funct at hfind ⊢
  cases v with
  | Vundef => simp at hfind
  | Vint n => simp at hfind
  | Vlong n => simp at hfind
  | Vfloat n => simp at hfind
  | Vsingle n => simp at hfind
  | Vptr b ofs =>
      cases hzero : Ptrofs.eq ofs Ptrofs.zero with
      | false => simp [hzero] at hfind
      | true =>
          simp [hzero] at hfind ⊢
          exact function_ptr_translated cfg prog tprog hm b f hfind

end CompCert4Lean.Backend.Constpropproof

namespace CompCert4Lean.Backend.Constpropproof

open CompCert4Lean.Backend.Constprop
open CompCert4Lean.Backend.RTL

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

theorem sig_function_translated : ∀ cfg, sig_function_translatedStatement cfg := by
  intro cfg rm f
  cases f with
  | Internal fn => rfl
  | External ef => rfl

end CompCert4Lean.Backend.Constpropproof

namespace CompCert4Lean.Backend.Constpropproof

open CompCert4Lean.Backend.Constprop
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib

theorem builtin_args_strength_reduction_correct :
    ∀ (cfg : CompCert4Lean.Config.CompilerConfig),
      builtin_args_strength_reduction_correctStatement cfg := by
  intro cfg prog bc sp m rs ae hmatch al vl hev cl
  unfold eval_builtin_args at hev ⊢
  induction hev generalizing cl with
  | nil => exact list_forall2_nil _
  | @cons a al v vl ha htail ih =>
      unfold CompCert4Lean.Backend.Constprop.builtin_args_strength_reduction
      apply list_forall2.cons
      · exact builtin_arg_strength_reduction_correct cfg prog bc sp m rs ae a v
          (cl.headD OK_default) hmatch ha
      · exact ih cl.tail

end CompCert4Lean.Backend.Constpropproof

namespace CompCert4Lean.Backend.Constpropproof

open CompCert4Lean.Backend.Constprop
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.ValueAnalysis
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib

theorem debug_strength_reduction_correct :
    ∀ (cfg : CompCert4Lean.Config.CompilerConfig),
      debug_strength_reduction_correctStatement cfg := by
  intro cfg prog bc sp m rs ae hmatch al vl hev
  induction hev with
  | nil =>
      exact ⟨[], list_forall2_nil _⟩
  | @cons a1 al b1 vl ha htail ih =>
      obtain ⟨vl', hvl'⟩ := ih
      have htail' : eval_builtin_args
          (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
          sp m (a1 :: debug_strength_reduction cfg ae al) (b1 :: vl') := by
        exact list_forall2.cons a1 b1 ha hvl'
      have hred : eval_builtin_arg
          (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
          sp m (builtin_arg_reduction cfg ae a1) b1 :=
        builtin_arg_reduction_correct cfg prog bc sp m rs ae hmatch a1 b1 ha
      cases a1 with
      | BA r =>
          cases harg : builtin_arg_reduction cfg ae (.BA r) with
          | BA_int n =>
              refine ⟨b1 :: b1 :: vl', ?_⟩
              simp [debug_strength_reduction, harg]
              exact list_forall2.cons _ _ (by simpa [harg] using hred) htail'
          | BA_long n =>
              refine ⟨b1 :: b1 :: vl', ?_⟩
              simp [debug_strength_reduction, harg]
              exact list_forall2.cons _ _ (by simpa [harg] using hred) htail'
          | BA_float n =>
              refine ⟨b1 :: b1 :: vl', ?_⟩
              simp [debug_strength_reduction, harg]
              exact list_forall2.cons _ _ (by simpa [harg] using hred) htail'
          | BA_single n =>
              refine ⟨b1 :: b1 :: vl', ?_⟩
              simp [debug_strength_reduction, harg]
              exact list_forall2.cons _ _ (by simpa [harg] using hred) htail'
          | BA r' =>
              refine ⟨b1 :: vl', ?_⟩
              simpa [debug_strength_reduction, harg] using htail'
          | BA_loadstack chunk ofs =>
              refine ⟨b1 :: vl', ?_⟩
              simpa [debug_strength_reduction, harg] using htail'
          | BA_addrstack ofs =>
              refine ⟨b1 :: vl', ?_⟩
              simpa [debug_strength_reduction, harg] using htail'
          | BA_loadglobal chunk id ofs =>
              refine ⟨b1 :: vl', ?_⟩
              simpa [debug_strength_reduction, harg] using htail'
          | BA_addrglobal id =>
              refine ⟨b1 :: vl', ?_⟩
              simpa [debug_strength_reduction, harg] using htail'
          | BA_splitlong hi lo =>
              refine ⟨b1 :: vl', ?_⟩
              simpa [debug_strength_reduction, harg] using htail'
          | BA_addptr a1 a2 =>
              refine ⟨b1 :: vl', ?_⟩
              simpa [debug_strength_reduction, harg] using htail'
      | BA_int n =>
          refine ⟨b1 :: vl', ?_⟩
          simpa [debug_strength_reduction] using htail'
      | BA_long n =>
          refine ⟨b1 :: vl', ?_⟩
          simpa [debug_strength_reduction] using htail'
      | BA_float n =>
          refine ⟨b1 :: vl', ?_⟩
          simpa [debug_strength_reduction] using htail'
      | BA_single n =>
          refine ⟨b1 :: vl', ?_⟩
          simpa [debug_strength_reduction] using htail'
      | BA_loadstack chunk ofs =>
          refine ⟨b1 :: vl', ?_⟩
          simpa [debug_strength_reduction] using htail'
      | BA_addrstack ofs =>
          refine ⟨b1 :: vl', ?_⟩
          simpa [debug_strength_reduction] using htail'
      | BA_loadglobal chunk id ofs =>
          refine ⟨b1 :: vl', ?_⟩
          simpa [debug_strength_reduction] using htail'
      | BA_addrglobal id =>
          refine ⟨b1 :: vl', ?_⟩
          simpa [debug_strength_reduction] using htail'
      | BA_splitlong hi lo =>
          refine ⟨b1 :: vl', ?_⟩
          simpa [debug_strength_reduction] using htail'
      | BA_addptr a1 a2 =>
          refine ⟨b1 :: vl', ?_⟩
          simpa [debug_strength_reduction] using htail'

end CompCert4Lean.Backend.Constpropproof

namespace CompCert4Lean.Backend.Constpropproof

open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Values

theorem init_regs_lessdef : init_regs_lessdefStatement := by
  intro params
  induction params with
  | nil =>
      intro vl vl' h
      cases vl with
      | nil =>
          cases vl' with
          | nil =>
              intro r
              change Val.lessdef (Regmap.get r (Regmap.init Vundef))
                (Regmap.get r (Regmap.init Vundef))
              rw [Regmap.gi_proof]
              exact Val.lessdef.lessdef_refl _
          | cons v' vs' => cases h
      | cons v vs =>
          cases vl' with
          | nil => cases h
          | cons v' vs' =>
              intro r
              change Val.lessdef (Regmap.get r (Regmap.init Vundef))
                (Regmap.get r (Regmap.init Vundef))
              rw [Regmap.gi_proof]
              exact Val.lessdef.lessdef_refl _
  | cons r params ih =>
      intro vl vl' h
      cases vl with
      | nil =>
          cases vl' with
          | nil =>
              intro r0
              change Val.lessdef (Regmap.get r0 (Regmap.init Vundef))
                (Regmap.get r0 (Regmap.init Vundef))
              rw [Regmap.gi_proof]
              exact Val.lessdef.lessdef_refl _
          | cons v' vs' =>
              cases h
      | cons v vs =>
          cases vl' with
          | nil =>
              cases h
          | cons v' vs' =>
              cases h with
              | lessdef_list_cons v₁ v₂ vl₁ vl₂ hv htail =>
                  change regs_lessdef
                    (Regmap.set r v (init_regs vs params))
                    (Regmap.set r v' (init_regs vs' params))
                  exact set_reg_lessdef r v v'
                    (init_regs vs params) (init_regs vs' params)
                    hv (ih vs vs' htail)

end CompCert4Lean.Backend.Constpropproof

namespace CompCert4Lean.Backend.Constpropproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Constprop
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueAnalysis
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

private theorem transf_ros_lessdef_eq_of_find
    (p : program) (fd : fundef) (v v' : val)
    (hfind : Genv.find_funct (Genv.globalenv p) v = some fd)
    (hld : Val.lessdef v v') : v = v' := by
  cases hld with
  | lessdef_refl v => rfl
  | lessdef_undef v => simp [Genv.find_funct] at hfind

open CompCert4Lean.Lib.Integers

theorem transf_ros_correct : ∀ cfg, transf_ros_correctStatement cfg := by
  intro cfg prog tprog hm bc rs ae ros f rs' hgenv hmatch hfind hregs
  cases ros with
  | inr id =>
      simp [CompCert4Lean.Backend.Constprop.transf_ros,
        CompCert4Lean.Backend.RTL.find_function] at hfind ⊢
      rw [symbols_preserved cfg prog tprog hm id]
      cases hs : Genv.find_symbol (Genv.globalenv prog) id with
      | none => simp [hs] at hfind
      | some b =>
          simp [hs] at hfind ⊢
          exact function_ptr_translated cfg prog tprog hm b f hfind
  | inl r =>
      have hfind' : Genv.find_funct (Genv.globalenv prog) (Regmap.get r rs) = some f := by
        simpa [CompCert4Lean.Backend.RTL.find_function] using hfind
      have hreg : Regmap.get r rs = Regmap.get r rs' :=
        transf_ros_lessdef_eq_of_find prog f (Regmap.get r rs) (Regmap.get r rs')
          hfind' (hregs r)
      have hdefault := functions_translated cfg prog tprog hm (Regmap.get r rs) f hfind'
      have hvm := hmatch r
      change vmatch bc (Regmap.get r rs) (areg ae r) at hvm
      cases ha : areg ae r with
      | Vbot =>
          simpa [CompCert4Lean.Backend.Constprop.transf_ros, ha, hreg,
            CompCert4Lean.Backend.RTL.find_function] using hdefault
      | I n =>
          simpa [CompCert4Lean.Backend.Constprop.transf_ros, ha, hreg,
            CompCert4Lean.Backend.RTL.find_function] using hdefault
      | IU n =>
          simpa [CompCert4Lean.Backend.Constprop.transf_ros, ha, hreg,
            CompCert4Lean.Backend.RTL.find_function] using hdefault
      | Uns p n =>
          simpa [CompCert4Lean.Backend.Constprop.transf_ros, ha, hreg,
            CompCert4Lean.Backend.RTL.find_function] using hdefault
      | Sgn p n =>
          simpa [CompCert4Lean.Backend.Constprop.transf_ros, ha, hreg,
            CompCert4Lean.Backend.RTL.find_function] using hdefault
      | L n =>
          simpa [CompCert4Lean.Backend.Constprop.transf_ros, ha, hreg,
            CompCert4Lean.Backend.RTL.find_function] using hdefault
      | F n =>
          simpa [CompCert4Lean.Backend.Constprop.transf_ros, ha, hreg,
            CompCert4Lean.Backend.RTL.find_function] using hdefault
      | FS n =>
          simpa [CompCert4Lean.Backend.Constprop.transf_ros, ha, hreg,
            CompCert4Lean.Backend.RTL.find_function] using hdefault
      | Num p =>
          simpa [CompCert4Lean.Backend.Constprop.transf_ros, ha, hreg,
            CompCert4Lean.Backend.RTL.find_function] using hdefault
      | Ifptr p =>
          simpa [CompCert4Lean.Backend.Constprop.transf_ros, ha, hreg,
            CompCert4Lean.Backend.RTL.find_function] using hdefault
      | Ptr p =>
          cases p with
          | Pbot => simpa [CompCert4Lean.Backend.Constprop.transf_ros, ha, hreg,
              CompCert4Lean.Backend.RTL.find_function] using hdefault
          | Glo id' => simpa [CompCert4Lean.Backend.Constprop.transf_ros, ha, hreg,
              CompCert4Lean.Backend.RTL.find_function] using hdefault
          | Glob => simpa [CompCert4Lean.Backend.Constprop.transf_ros, ha, hreg,
              CompCert4Lean.Backend.RTL.find_function] using hdefault
          | Stk ofs' => simpa [CompCert4Lean.Backend.Constprop.transf_ros, ha, hreg,
              CompCert4Lean.Backend.RTL.find_function] using hdefault
          | Stack => simpa [CompCert4Lean.Backend.Constprop.transf_ros, ha, hreg,
              CompCert4Lean.Backend.RTL.find_function] using hdefault
          | Nonstack => simpa [CompCert4Lean.Backend.Constprop.transf_ros, ha, hreg,
              CompCert4Lean.Backend.RTL.find_function] using hdefault
          | Ptop => simpa [CompCert4Lean.Backend.Constprop.transf_ros, ha, hreg,
              CompCert4Lean.Backend.RTL.find_function] using hdefault
          | Gl id ofs =>
              cases hzero : Ptrofs.eq ofs Ptrofs.zero with
              | false =>
                  simpa [CompCert4Lean.Backend.Constprop.transf_ros, ha, hzero, hreg,
                    CompCert4Lean.Backend.RTL.find_function] using hdefault
              | true =>
                  have hvm' : vmatch bc (Regmap.get r rs) (Ptr (Gl id ofs)) := by
                    rw [← ha]
                    exact hvm
                  generalize hv : Regmap.get r rs = vv at hvm' hfind'
                  cases hvm' with
                  | ptr b ofs' p hpm =>
                      cases hpm with
                      | gl hbc =>
                          have hsym := hgenv.1 id b
                          have hfindsym : Genv.find_symbol (Genv.globalenv prog) id = some b :=
                            hsym.mpr (by assumption)
                          have hfindptr : Genv.find_funct_ptr (Genv.globalenv prog) b = some f := by
                            unfold Genv.find_funct at hfind'
                            simp [hzero] at hfind'
                            exact hfind'
                          rcases function_ptr_translated cfg prog tprog hm b f hfindptr with
                            ⟨cu, hfindptr', hlink⟩
                          refine ⟨cu, ?_, hlink⟩
                          have hros :
                              CompCert4Lean.Backend.Constprop.transf_ros ae (Sum.inl r) =
                                Sum.inr id := by
                            simp [CompCert4Lean.Backend.Constprop.transf_ros, ha, hzero]
                          rw [hros]
                          change (match Genv.find_symbol (Genv.globalenv tprog) id with
                            | none => none
                            | some b => Genv.find_funct_ptr (Genv.globalenv tprog) b) =
                            some (CompCert4Lean.Backend.Constprop.transf_fundef cfg
                              (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg cu) f)
                          rw [symbols_preserved cfg prog tprog hm id, hfindsym]
                          exact hfindptr'
                  | ptrUndef p =>
                      simp [Genv.find_funct] at hfind'

end CompCert4Lean.Backend.Constpropproof

namespace CompCert4Lean.Backend.Constpropproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Constprop
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueAnalysis
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.ConstpropOp
open CompCert4Lean.X86.Machregs
open CompCert4Lean.X86.Op

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

theorem match_states_succ : ∀ (cfg : CompilerConfig), match_states_succStatement cfg := by
  intro cfg prog s f sp pc rs m s' rs' m' cu hlink hstacks hregs hmem
  exact match_states_intro (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) cfg prog s sp pc rs m f s' pc rs' m' cu 0
    hlink hstacks (match_pc_base f rs m 0 pc) hregs hmem

theorem transf_instr_at : ∀ (cfg : CompilerConfig), transf_instr_atStatement cfg := by
  intro cfg rm f pc i hi
  unfold CompCert4Lean.Backend.Constprop.transf_function
  change PTree.get (show positive from pc)
      (PTree.map
        (CompCert4Lean.Backend.Constprop.transf_instr
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg f
          (CompCert4Lean.Backend.ValueAnalysis.analyze
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) cfg rm f) rm)
        f.fn_code) = _
  rw [@PTree.gmap instruction instruction
    (CompCert4Lean.Backend.Constprop.transf_instr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg f
      (CompCert4Lean.Backend.ValueAnalysis.analyze
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg rm f) rm)
    (show positive from pc) f.fn_code]
  simpa [hi]

end CompCert4Lean.Backend.Constpropproof

namespace CompCert4Lean.Backend.Constpropproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Constprop
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueAnalysis
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

theorem builtin_strength_reduction_correct :
    ∀ (cfg : CompilerConfig), builtin_strength_reduction_correctStatement cfg := by
  intro cfg xi prog sp bc ae rs ef args vargs m t vres m' hmatch hargs hcall
  have hdefault : ∀ cl,
      ∃ vargs',
        eval_builtin_args (Genv.to_senv (Genv.globalenv prog))
          (fun r => Regmap.get r rs) sp m
          (CompCert4Lean.Backend.Constprop.builtin_args_strength_reduction cfg ae args cl) vargs' ∧
        external_call (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ef
          (Genv.to_senv (Genv.globalenv prog)) vargs' m t vres m' := by
    intro cl
    refine ⟨vargs, ?_, hcall⟩
    exact builtin_args_strength_reduction_correct cfg prog bc sp m rs ae hmatch args vargs hargs cl
  unfold CompCert4Lean.Backend.Constprop.builtin_strength_reduction
  cases ef with
  | EF_debug kind text targs =>
      obtain ⟨vargs', hvals⟩ :=
        debug_strength_reduction_correct cfg prog bc sp m rs ae hmatch args vargs hargs
      refine ⟨vargs', hvals, ?_⟩
      cases hcall with
      | extcall_debug_sem_intro =>
          exact extcall_debug_sem_intro _ _
  | EF_external name sg => exact hdefault _
  | EF_builtin name sg => exact hdefault _
  | EF_runtime name sg => exact hdefault _
  | EF_vload chunk => exact hdefault _
  | EF_vstore chunk => exact hdefault _
  | EF_malloc => exact hdefault _
  | EF_free => exact hdefault _
  | EF_memcpy sz al => exact hdefault _
  | EF_annot kind text targs => exact hdefault _
  | EF_annot_val kind text targ => exact hdefault _
  | EF_inline_asm text sg clobbers => exact hdefault _

end CompCert4Lean.Backend.Constpropproof


namespace CompCert4Lean.Backend.Constpropproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Constprop
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.ConstpropOp
open CompCert4Lean.X86.Op
open Lean Elab Tactic Meta

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

private theorem constprop_ptrofs_eq_of_eq_true {x y : Ptrofs.int}
    (h : Ptrofs.eq x y = true) : x = y := by
  unfold Ptrofs.eq WordCore.eq at h
  apply WordCore.ext
  exact of_decide_eq_true h

private def constpropPrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem constprop_wordcore_add_val {bits : Nat}
    (x y : WordCore.Word bits) :
    (WordCore.add x y).val = (x.val + y.val) % (2 ^ bits) := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let yF := (lctx.findFromUserName? `y).get!
    let e ← mkAppM
      (constpropPrivateName "CompCert4Lean.Lib.Integers.WordCore.add_val")
      #[mkFVar xF.fvarId, mkFVar yF.fvarId]
    closeMainGoal Name.anonymous e

private theorem constprop_wordcore_zero_val (bits : Nat) :
    (WordCore.zero bits).val = 0 := by
  unfold WordCore.zero
  run_tac
    let lctx ← getLCtx
    let bF := (lctx.findFromUserName? `bits).get!
    let e ← mkAppM
      (constpropPrivateName "CompCert4Lean.Lib.Integers.WordCore.val_repr_residue")
      #[mkFVar bF.fvarId,
        mkConst ``CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0]
    closeMainGoal Name.anonymous e

private theorem constprop_wordcore_val_lt {bits : Nat}
    (x : WordCore.Word bits) : x.val < 2 ^ bits := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let e ← mkAppM
      (constpropPrivateName "CompCert4Lean.Lib.Integers.WordCore.val_lt")
      #[mkFVar xF.fvarId]
    closeMainGoal Name.anonymous e

private theorem constprop_ptrofs_add_zero_l (x : Ptrofs.int) :
    Ptrofs.add Ptrofs.zero x = x := by
  change WordCore.add (WordCore.zero Ptrofs.wordsize) x = x
  apply WordCore.ext_of_val_eq
  rw [constprop_wordcore_add_val, constprop_wordcore_zero_val, Nat.zero_add]
  exact Nat.mod_eq_of_lt (constprop_wordcore_val_lt x)

theorem const_for_result_correct :
    ∀ (cfg : CompilerConfig), const_for_result_correctStatement cfg := by
  intro cfg prog tprog hprog a op bc v sp m hconst hvm hstack hgenv
  cases a with
  | Vbot => simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
  | I n =>
      simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
      cases hconst
      cases hvm
      exact ⟨Vint n, rfl, Val.lessdef_refl _⟩
  | IU n =>
      simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
      cases hconst
      cases hvm with
      | vmatch_iu => exact ⟨Vint n, rfl, Val.lessdef_refl _⟩
      | iuUndef => exact ⟨Vint n, rfl, Val.lessdef_undef _⟩
  | Uns p n => simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
  | Sgn p n => simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
  | L n =>
      simp [CompCert4Lean.X86.ConstpropOp.const_for_result,
        CompCert4Lean.X86_64.Archi.ptr64] at hconst
      cases hconst
      cases hvm
      exact ⟨Vlong n, rfl, Val.lessdef_refl _⟩
  | F f =>
      cases hgen : CompCert4Lean.Driver.Compopts.generate_float_constants cfg with
      | false => simp [CompCert4Lean.X86.ConstpropOp.const_for_result, hgen] at hconst
      | true =>
          simp [CompCert4Lean.X86.ConstpropOp.const_for_result, hgen] at hconst
          cases hconst
          cases hvm
          exact ⟨Vfloat f, rfl, Val.lessdef_refl _⟩
  | FS f =>
      cases hgen : CompCert4Lean.Driver.Compopts.generate_float_constants cfg with
      | false => simp [CompCert4Lean.X86.ConstpropOp.const_for_result, hgen] at hconst
      | true =>
          simp [CompCert4Lean.X86.ConstpropOp.const_for_result, hgen] at hconst
          cases hconst
          cases hvm
          exact ⟨Vsingle f, rfl, Val.lessdef_refl _⟩
  | Num p => simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
  | Ifptr p => simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
  | Ptr p =>
      cases p with
      | Pbot => simp [CompCert4Lean.X86.ConstpropOp.const_for_result,
          CompCert4Lean.X86_64.Archi.ptr64] at hconst
      | Glo id => simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
      | Glob => simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
      | Stack => simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
      | Nonstack => simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
      | Ptop => simp [CompCert4Lean.X86.ConstpropOp.const_for_result] at hconst
      | Gl id ofs =>
          by_cases hrel : CompCert4Lean.X86.SelectOp.symbol_is_relocatable
              cfg.relocation id = true
          · by_cases hzero : Ptrofs.eq ofs Ptrofs.zero = true
            · simp [CompCert4Lean.X86.ConstpropOp.const_for_result, hrel, hzero] at hconst
              cases hconst
              have hz : ofs = Ptrofs.zero :=
                constprop_ptrofs_eq_of_eq_true hzero
              subst ofs
              cases hvm with
              | ptrUndef =>
                  exact ⟨Genv.symbol_address (Genv.globalenv tprog) id Ptrofs.zero,
                    rfl, Val.lessdef_undef _⟩
              | ptr b ofs p hp =>
                  cases hp with
                  | gl id hbc =>
                      have hfind : Genv.find_symbol (Genv.globalenv prog) id = some b :=
                        (hgenv.1 id b).mpr hbc
                      have hfind' : Genv.find_symbol (Genv.globalenv tprog) id = some b := by
                        rw [symbols_preserved cfg prog tprog hprog id]
                        exact hfind
                      have haddr : Genv.symbol_address (Genv.globalenv tprog)
                          id Ptrofs.zero = Vptr b Ptrofs.zero := by
                        simp [Genv.symbol_address, hfind']
                      refine ⟨Genv.symbol_address (Genv.globalenv tprog) id Ptrofs.zero,
                        rfl, ?_⟩
                      rw [haddr]
                      exact Val.lessdef_refl _
            · simp [CompCert4Lean.X86.ConstpropOp.const_for_result, hrel, hzero] at hconst
          · simp [CompCert4Lean.X86.ConstpropOp.const_for_result, hrel,
              CompCert4Lean.X86_64.Archi.ptr64,
              CompCert4Lean.X86.ConstpropOp.Olea_ptr] at hconst
            cases hconst
            cases hvm with
            | ptrUndef =>
                exact ⟨Genv.symbol_address (Genv.globalenv tprog) id ofs,
                  rfl, Val.lessdef_undef _⟩
            | ptr b ofs' p hp =>
                cases hp with
                | gl id hbc =>
                    have hfind : Genv.find_symbol (Genv.globalenv prog) id = some b :=
                      (hgenv.1 id b).mpr hbc
                    have hfind' : Genv.find_symbol (Genv.globalenv tprog) id = some b := by
                      rw [symbols_preserved cfg prog tprog hprog id]
                      exact hfind
                    have haddr : Genv.symbol_address (Genv.globalenv tprog)
                        id ofs = Vptr b ofs := by
                      simp [Genv.symbol_address, hfind']
                    refine ⟨Genv.symbol_address (Genv.globalenv tprog) id ofs,
                      rfl, ?_⟩
                    rw [haddr]
                    exact Val.lessdef_refl _
      | Stk ofs =>
          simp [CompCert4Lean.X86.ConstpropOp.const_for_result,
            CompCert4Lean.X86_64.Archi.ptr64,
            CompCert4Lean.X86.ConstpropOp.Olea_ptr] at hconst
          cases hconst
          cases hvm with
          | ptrUndef =>
              exact ⟨Val.offset_ptr (Vptr sp Ptrofs.zero) ofs,
                rfl, Val.lessdef_undef _⟩
          | ptr b ofs' p hp =>
              cases hp with
              | stk hbc =>
                  have hb : b = sp := bc.bc_stack b sp hbc hstack
                  subst b
                  refine ⟨Vptr sp ofs, ?_, ?_⟩
                  · change some (Val.offset_ptr (Vptr sp Ptrofs.zero) ofs) =
                      some (Vptr sp ofs)
                    simp only [Val.offset_ptr]
                    rw [constprop_ptrofs_add_zero_l]
                  · exact Val.lessdef_refl _

end CompCert4Lean.Backend.Constpropproof
