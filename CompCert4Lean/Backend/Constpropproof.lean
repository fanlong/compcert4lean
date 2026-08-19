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
private abbrev RelocationContext := CompCert4Lean.X86.SelectOp.RelocationContext

private def relocationContext : RelocationContext :=
  { pic := false
    pie := false
    common := false
    facts := fun _ => none }

def match_prog (prog tprog : program) : Prop :=
  @match_program fundef Unit fundef Unit
    (Linker_fundef function) Linker_unit
    (fun cu f tf =>
      tf = CompCert4Lean.Backend.Constprop.transf_fundef
        (CompCert4Lean.Backend.ValueAnalysis.romem_for cu) f)
    (fun x y : Unit => x = y) prog tprog

inductive match_pc (f : function) (rs : regset) (m : mem) : Nat → node → node → Prop where
  | match_pc_base (n : Nat) (pc : node) :
      match_pc f rs m n pc pc
  | match_pc_nop (n : Nat) (pc s pcx : node)
      (hcode : PTree.get pc f.fn_code = some (Inop s))
      (hmatch : match_pc f rs m n s pcx) :
      match_pc f rs m (Nat.succ n) pc pcx
  | match_pc_cond (n : Nat) (pc : node) (cond : condition) (args : List reg)
      (s1 s2 pcx : node)
      (hcode : PTree.get pc f.fn_code = some (Icond cond args s1 s2))
      (hmatch : ∀ b,
        eval_condition cond (args.map (fun r => Regmap.get r rs)) m = some b →
          match_pc f rs m n (if b then s1 else s2) pcx) :
      match_pc f rs m (Nat.succ n) pc pcx

inductive match_stackframes (prog : program) : stackframe → stackframe → Prop where
  | match_stackframe_intro
      (res : reg) (sp : val) (pc : node) (rs : regset)
      (f : function) (rs' : regset) (cu : program)
      (hlink : linkorder cu prog)
      (hld : regs_lessdef rs rs') :
      match_stackframes prog
        (Stackframe res f sp pc rs)
        (Stackframe res
          (CompCert4Lean.Backend.Constprop.transf_function
            (CompCert4Lean.Backend.ValueAnalysis.romem_for cu) f)
          sp pc rs')

inductive match_states (prog : program) : Nat → state → state → Prop where
  | match_states_intro
      (s : List stackframe) (sp : val) (pc : node) (rs : regset) (m : mem)
      (f : function) (s' : List stackframe) (pc' : node) (rs' : regset)
      (m' : mem) (cu : program) (n : Nat)
      (hlink : linkorder cu prog)
      (hstacks : list_forall2 (match_stackframes prog) s s')
      (hpc : match_pc f rs m n pc pc')
      (hregs : regs_lessdef rs rs')
      (hmem : Mem.extends m m') :
      match_states prog n
        (State s f sp pc rs m)
        (State s'
          (CompCert4Lean.Backend.Constprop.transf_function
            (CompCert4Lean.Backend.ValueAnalysis.romem_for cu) f)
          sp pc' rs' m')
  | match_states_call
      (s : List stackframe) (f : fundef) (args : List val) (m : mem)
      (s' : List stackframe) (args' : List val) (m' : mem) (cu : program)
      (hlink : linkorder cu prog)
      (hstacks : list_forall2 (match_stackframes prog) s s')
      (hargs : Val.lessdef_list args args')
      (hmem : Mem.extends m m') :
      match_states prog 0
        (Callstate s f args m)
        (Callstate s'
          (CompCert4Lean.Backend.Constprop.transf_fundef
            (CompCert4Lean.Backend.ValueAnalysis.romem_for cu) f)
          args' m')
  | match_states_return
      (s : List stackframe) (v : val) (m : mem)
      (s' : List stackframe) (v' : val) (m' : mem)
      (hstacks : list_forall2 (match_stackframes prog) s s')
      (hres : Val.lessdef v v')
      (hmem : Mem.extends m m')
      (hstacks' : list_forall2 (match_stackframes prog) s s') :
      match_states prog 0
        (Returnstate s v m)
        (Returnstate s' v' m')

export match_pc (match_pc_base match_pc_nop match_pc_cond)
export match_stackframes (match_stackframe_intro)
export match_states (match_states_intro match_states_call match_states_return)

/-! Exact source statement descriptors for later proof migration. -/

def symbols_preservedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ s : ident,
      Genv.find_symbol (Genv.globalenv tprog) s =
        Genv.find_symbol (Genv.globalenv prog) s

def senv_preservedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    Senv.equiv (Genv.to_senv (Genv.globalenv prog))
      (Genv.to_senv (Genv.globalenv tprog))

def functions_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ (v : val) (f : fundef),
      Genv.find_funct (Genv.globalenv prog) v = some f →
      ∃ cu, Genv.find_funct (Genv.globalenv tprog) v =
        some (CompCert4Lean.Backend.Constprop.transf_fundef
          (CompCert4Lean.Backend.ValueAnalysis.romem_for cu) f) ∧
        linkorder cu prog

def function_ptr_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ (b : block) (f : fundef),
      Genv.find_funct_ptr (Genv.globalenv prog) b = some f →
      ∃ cu, Genv.find_funct_ptr (Genv.globalenv tprog) b =
        some (CompCert4Lean.Backend.Constprop.transf_fundef
          (CompCert4Lean.Backend.ValueAnalysis.romem_for cu) f) ∧
        linkorder cu prog

def sig_function_translatedStatement : Prop :=
  ∀ (rm : romem) (f : fundef),
    CompCert4Lean.Backend.RTL.funsig
      (CompCert4Lean.Backend.Constprop.transf_fundef rm f) =
      CompCert4Lean.Backend.RTL.funsig f

def init_regs_lessdefStatement : Prop :=
  ∀ (rl : List reg) (vl1 vl2 : List val),
    Val.lessdef_list vl1 vl2 →
      regs_lessdef (init_regs vl1 rl) (init_regs vl2 rl)

def transf_ros_correctStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ (bc : block_classification) (rs : regset) (ae : aenv)
      (ros : Sum reg ident) (f : fundef) (rs' : regset),
      genv_match bc (Genv.globalenv prog) →
      ematch bc rs ae →
      find_function (Genv.globalenv prog) ros rs = some f →
      regs_lessdef rs rs' →
      ∃ cu, find_function (Genv.globalenv tprog) (transf_ros ae ros) rs' =
        some (CompCert4Lean.Backend.Constprop.transf_fundef
          (CompCert4Lean.Backend.ValueAnalysis.romem_for cu) f) ∧
        linkorder cu prog

def const_for_result_correctStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ (a : aval) (op : operation) (bc : block_classification) (v : val)
      (sp : block) (m : mem),
      const_for_result relocationContext a = some op →
      vmatch bc v a →
      bc sp = BCstack →
      genv_match bc (Genv.globalenv prog) →
      ∃ v', eval_operation (Genv.globalenv tprog) (Vptr sp Ptrofs.zero)
        op [] m = some v' ∧ Val.lessdef v v'

def match_successor_recStatement : Prop :=
  ∀ (f : function) (rs : regset) (m : mem)
    (bc : block_classification) (ae : aenv),
    ematch bc rs ae →
    ∀ (n : Nat) (pc : node),
      match_pc f rs m n pc (successor_rec n f ae pc)

def match_successorStatement : Prop :=
  ∀ (f : function) (rs : regset) (m : mem)
    (bc : block_classification) (ae : aenv) (pc : node),
    ematch bc rs ae →
      match_pc f rs m num_iter pc (successor f ae pc)

def builtin_arg_reduction_correctStatement : Prop :=
  ∀ (prog : program),
    ∀ (bc : block_classification) (sp : val) (m : mem) (rs : regset)
      (ae : aenv),
      ematch bc rs ae →
      ∀ (a : builtin_arg reg) (v : val),
        eval_builtin_arg (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
          sp m a v →
        eval_builtin_arg (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
          sp m (builtin_arg_reduction ae a) v

def builtin_arg_strength_reduction_correctStatement : Prop :=
  ∀ (prog : program),
    ∀ (bc : block_classification) (sp : val) (m : mem) (rs : regset)
      (ae : aenv) (a : builtin_arg reg) (v : val)
      (c : builtin_arg_constraint),
      ematch bc rs ae →
      eval_builtin_arg (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
        sp m a v →
      eval_builtin_arg (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
        sp m (builtin_arg_strength_reduction ae a c) v

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
            sp m (builtin_args_strength_reduction ae al cl) vl

def debug_strength_reduction_correctStatement : Prop :=
  ∀ (prog : program),
    ∀ (bc : block_classification) (sp : val) (m : mem) (rs : regset)
      (ae : aenv),
      ematch bc rs ae →
      ∀ (al : List (builtin_arg reg)) (vl : List val),
        eval_builtin_args (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
          sp m al vl →
        ∃ vl', eval_builtin_args (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
          sp m (debug_strength_reduction ae al) vl'

def builtin_strength_reduction_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    ∀ (sp : val) (bc : block_classification) (ae : aenv) (rs : regset)
      (ef : external_function) (args : List (builtin_arg reg)) (vargs : List val)
      (m : mem) (t : trace) (vres : val) (m' : mem),
      ematch bc rs ae →
      eval_builtin_args (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
        sp m args vargs →
      external_call xi ef (Genv.to_senv (Genv.globalenv prog)) vargs m t vres m' →
      ∃ vargs',
        eval_builtin_args (Genv.to_senv (Genv.globalenv prog)) (fun r => Regmap.get r rs)
          sp m (builtin_strength_reduction ae ef args) vargs' ∧
        external_call xi ef (Genv.to_senv (Genv.globalenv prog)) vargs' m t vres m'

def match_states_succStatement : Prop :=
  ∀ (prog : program) (s : List stackframe) (f : function) (sp : val)
    (pc : node) (rs : regset) (m : mem) (s' : List stackframe)
    (rs' : regset) (m' : mem) (cu : program),
    linkorder cu prog →
    list_forall2 (match_stackframes prog) s s' →
    regs_lessdef rs rs' →
    Mem.extends m m' →
    match_states prog 0
      (State s f sp pc rs m)
      (State s'
        (CompCert4Lean.Backend.Constprop.transf_function
          (CompCert4Lean.Backend.ValueAnalysis.romem_for cu) f)
        sp pc rs' m')

def transf_step_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog tprog : program), match_prog prog tprog →
    ∀ (s1 : state) (t : trace) (s2 : state),
      step xi (Genv.globalenv prog) s1 t s2 →
      ∀ (n1 : Nat) (s1' : state),
        ValueAnalysis.sound_state prog s1 →
        match_states prog n1 s1 s1' →
        (∃ n2 s2',
          step xi (Genv.globalenv tprog) s1' t s2' ∧
          match_states prog n2 s2 s2') ∨
        (∃ n2, n2 < n1 ∧ t = E0 ∧ match_states prog n2 s2 s1')

def transf_initial_statesStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ (st1 : state), initial_state prog st1 →
      ∃ n st2, initial_state tprog st2 ∧ match_states prog n st1 st2

def transf_final_statesStatement : Prop :=
  ∀ (prog : program) (n : Nat) (st1 st2 : state) (r : int),
    match_states prog n st1 st2 → final_state st1 r → final_state st2 r

def transf_program_matchStatement : Prop :=
  ∀ (prog : program), match_prog prog (transf_program prog)

def transf_program_correctStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog tprog : program), match_prog prog tprog →
    forward_simulation
      (semantics xi prog)
      (semantics xi tprog)

end CompCert4Lean.Backend.Constpropproof
