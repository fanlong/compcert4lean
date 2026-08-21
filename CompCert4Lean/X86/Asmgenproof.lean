import CompCert4Lean.Backend.Asmgenproof0
import CompCert4Lean.Backend.Mach
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Common.Values
import CompCert4Lean.Foundation.RocqStdlib
import CompCert4Lean.X86.Asm
import CompCert4Lean.X86.Asmgen

/-!
# Correctness surface for x86 generation

The executable definitions in this module are the direct translations of
`x86/Asmgenproof.v`. Proof-bearing source declarations remain transparent
proposition descriptors for the later proof-migration phase.
-/

namespace CompCert4Lean.X86.Asmgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Asmgenproof0
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Asm
open CompCert4Lean.X86.Asmgen

private abbrev MachProgram := CompCert4Lean.Backend.Mach.program
private abbrev AsmProgram := CompCert4Lean.X86.Asm.program
private abbrev AsmFundef := CompCert4Lean.X86.Asm.fundef
private abbrev MachFunction := CompCert4Lean.Backend.Mach.function
private abbrev MachFundef := CompCert4Lean.Backend.Mach.fundef
private abbrev MachInstruction := CompCert4Lean.Backend.Mach.instruction
private abbrev MachStackframe := CompCert4Lean.Backend.Mach.stackframe
private abbrev AsmFunction := CompCert4Lean.X86.Asm.function
private abbrev MachState := CompCert4Lean.Backend.Mach.state
private abbrev AsmState := CompCert4Lean.X86.Asm.state
private abbrev MachRegset := CompCert4Lean.Backend.Mach.regset
private abbrev AsmRegset := CompCert4Lean.X86.Asm.regset
private abbrev MachGenv := CompCert4Lean.Backend.Mach.genv
private abbrev AsmGenv := CompCert4Lean.X86.Asm.genv
private abbrev MachCode := CompCert4Lean.Backend.Mach.code
private abbrev AsmCode := CompCert4Lean.X86.Asm.code
private abbrev Mem := CompCert4Lean.Common.Memory.mem
private abbrev Val := CompCert4Lean.Common.Values.val
private abbrev PtrofsInt := CompCert4Lean.Lib.Integers.ptrofs
private abbrev Block := CompCert4Lean.Common.Values.block
private abbrev Mreg := CompCert4Lean.X86.Machregs.mreg
private abbrev Ireg := CompCert4Lean.X86.Asm.ireg
private abbrev Condition := CompCert4Lean.X86.Op.condition
private abbrev Addressing := CompCert4Lean.X86.Op.addressing
private abbrev Operation := CompCert4Lean.X86.Op.operation
private abbrev Extcond := CompCert4Lean.X86.Asmgen.extcond
private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev ExternalCalls := CompCert4Lean.Common.ExternalCalls.ExternalCalls

private def asmStep (cfg : CompilerConfig) (xi : ExternalCalls) :
    AsmGenv → AsmState → trace → AsmState → Prop :=
  CompCert4Lean.X86.Asm.step cfg xi

/-! ## Program matching -/

def match_prog (p : MachProgram) (tp : AsmProgram) : Prop :=
  @match_program MachFundef Unit AsmFundef Unit
    (Linker_fundef MachFunction) Linker_unit
    (fun _ f tf => CompCert4Lean.X86.Asmgen.transf_fundef f = .OK tf)
    (fun x y : Unit => x = y) p tp

/-! ## State matching for the simulation -/

inductive match_states (ge : MachGenv) : MachState → AsmState → Prop where
  | match_states_intro
      (s : List MachStackframe) (fb : Block) (sp : Val)
      (c : MachCode) (ep : Bool) (ms : MachRegset) (m m' : Mem)
      (rs : AsmRegset) (f : MachFunction) (tf : AsmFunction) (tc : AsmCode)
      (stacks : match_stack ge s)
      (find : Genv.find_funct_ptr ge fb = some (.Internal f))
      (mext : CompCert4Lean.Common.Memory.Mem.extends m m')
      (atpc : transl_code_at_pc ge (rs .PC) fb f c ep tf tc)
      (agree : CompCert4Lean.Backend.Asmgenproof0.agree ms sp rs)
      (axp : ep = true → rs (.IR .RAX) = parent_sp s) :
      match_states ge
        (.State s fb sp c ms m)
        (.State rs m')
  | match_states_call
      (s : List MachStackframe) (fb : Block) (ms : MachRegset)
      (m m' : Mem) (rs : AsmRegset)
      (stacks : match_stack ge s)
      (mext : CompCert4Lean.Common.Memory.Mem.extends m m')
      (agree : CompCert4Lean.Backend.Asmgenproof0.agree ms (parent_sp s) rs)
      (atpc : rs .PC = .Vptr fb Ptrofs.zero)
      (atlr : rs .RA = parent_ra s) :
      match_states ge
        (.Callstate s fb ms m)
        (.State rs m')
  | match_states_return
      (s : List MachStackframe) (ms : MachRegset) (m m' : Mem)
      (rs : AsmRegset)
      (stacks : match_stack ge s)
      (mext : CompCert4Lean.Common.Memory.Mem.extends m m')
      (agree : CompCert4Lean.Backend.Asmgenproof0.agree ms (parent_sp s) rs)
      (atpc : rs .PC = parent_ra s) :
      match_states ge
        (.Returnstate s ms m)
        (.State rs m')

export match_states (match_states_intro match_states_call match_states_return)

def measure : MachState → Nat
  | .State _ _ _ _ _ _ => 0
  | .Callstate _ _ _ _ => 0
  | .Returnstate _ _ _ => 1

/-! ## Exact statement descriptors for later proof migration -/

def transf_program_matchStatement : Prop :=
  ∀ (p : MachProgram) (tp : AsmProgram),
    CompCert4Lean.X86.Asmgen.transf_program p = .OK tp → match_prog p tp

def symbols_preservedStatement : Prop :=
  ∀ (prog : MachProgram) (tprog : AsmProgram), match_prog prog tprog →
    ∀ (s : ident),
      Genv.find_symbol (Genv.globalenv tprog) s =
        Genv.find_symbol (Genv.globalenv prog) s

def senv_preservedStatement : Prop :=
  ∀ (prog : MachProgram) (tprog : AsmProgram), match_prog prog tprog →
    Senv.equiv (Genv.to_senv (Genv.globalenv prog))
      (Genv.to_senv (Genv.globalenv tprog))

def functions_translatedStatement : Prop :=
  ∀ (prog : MachProgram) (tprog : AsmProgram), match_prog prog tprog →
    ∀ (b : Block) (f : MachFundef),
      Genv.find_funct_ptr (Genv.globalenv prog) b = some f →
      ∃ tf,
        Genv.find_funct_ptr (Genv.globalenv tprog) b = some tf ∧
          CompCert4Lean.X86.Asmgen.transf_fundef f = .OK tf

def functions_translStatement : Prop :=
  ∀ (prog : MachProgram) (tprog : AsmProgram), match_prog prog tprog →
    ∀ (fb : Block) (f : MachFunction) (tf : AsmFunction),
      Genv.find_funct_ptr (Genv.globalenv prog) fb = some (.Internal f) →
      CompCert4Lean.X86.Asmgen.transf_function f = .OK tf →
      Genv.find_funct_ptr (Genv.globalenv tprog) fb = some (.Internal tf)

def transf_function_no_overflowStatement : Prop :=
  ∀ (f : MachFunction) (tf : AsmFunction),
    CompCert4Lean.X86.Asmgen.transf_function f = .OK tf →
    ZArith.BinInt.Z.le (list_length_z tf.fn_code) Ptrofs.max_unsigned

def exec_straight_execStatement : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls)
    (prog : MachProgram) (tprog : AsmProgram), match_prog prog tprog →
    ∀ (fb : Block) (f : MachFunction) (c : MachCode) (ep : Bool)
      (tf : AsmFunction) (tc c' : AsmCode) (rs : AsmRegset) (m : Mem)
      (rs' : AsmRegset) (m' : Mem),
      transl_code_at_pc (Genv.globalenv prog) (rs .PC) fb f c ep tf tc →
      exec_straight (Genv.globalenv tprog) tf tc rs m c' rs' m' →
      plus (asmStep cfg xi) (Genv.globalenv tprog)
        (.State rs m) E0 (.State rs' m')

def exec_straight_atStatement : Prop :=
  ∀ (prog : MachProgram) (tprog : AsmProgram), match_prog prog tprog →
    ∀ (fb : Block) (f : MachFunction) (c : MachCode) (ep : Bool)
      (tf : AsmFunction) (tc tc' : AsmCode) (c' : MachCode) (ep' : Bool)
      (rs : AsmRegset) (m : Mem) (rs' : AsmRegset) (m' : Mem),
      transl_code_at_pc (Genv.globalenv prog) (rs .PC) fb f c ep tf tc →
      CompCert4Lean.X86.Asmgen.transl_code f c' ep' = .OK tc' →
      exec_straight (Genv.globalenv tprog) tf tc rs m tc' rs' m' →
      transl_code_at_pc (Genv.globalenv prog) (rs' .PC) fb f c' ep' tf tc'

def loadind_labelStatement : Prop :=
  ∀ (base : Ireg) (ofs : PtrofsInt) (ty : typ) (dst : Mreg)
    (k c : AsmCode),
    CompCert4Lean.X86.Asmgen.loadind base ofs ty dst k = .OK c →
    tail_nolabel k c

def storeind_labelStatement : Prop :=
  ∀ (base : Ireg) (ofs : PtrofsInt) (ty : typ) (src : Mreg)
    (k c : AsmCode),
    CompCert4Lean.X86.Asmgen.storeind src base ofs ty k = .OK c →
    tail_nolabel k c

def mk_setcc_base_labelStatement : Prop :=
  ∀ (xc : Extcond) (rd : Ireg) (k : AsmCode),
    tail_nolabel k (CompCert4Lean.X86.Asmgen.mk_setcc_base xc rd k)

def mk_setcc_labelStatement : Prop :=
  ∀ (xc : Extcond) (rd : Ireg) (k : AsmCode),
    tail_nolabel k (CompCert4Lean.X86.Asmgen.mk_setcc xc rd k)

def mk_jcc_labelStatement : Prop :=
  ∀ (xc : Extcond) (lbl : positive) (k : AsmCode),
    tail_nolabel k (CompCert4Lean.X86.Asmgen.mk_jcc xc lbl k)

def mk_sel_labelStatement : Prop :=
  ∀ (xc : Extcond) (rd r2 : Ireg) (k c : AsmCode),
    CompCert4Lean.X86.Asmgen.mk_sel xc rd r2 k = .OK c → tail_nolabel k c

def transl_cond_labelStatement : Prop :=
  ∀ (cond : Condition) (args : List Mreg) (k c : AsmCode),
    CompCert4Lean.X86.Asmgen.transl_cond cond args k = .OK c → tail_nolabel k c

def transl_op_labelStatement : Prop :=
  ∀ (op : Operation) (args : List Mreg) (r : Mreg) (k c : AsmCode),
    CompCert4Lean.X86.Asmgen.transl_op op args r k = .OK c → tail_nolabel k c

def transl_load_labelStatement : Prop :=
  ∀ (chunk : memory_chunk) (addr : Addressing) (args : List Mreg)
    (dest : Mreg) (k c : AsmCode),
    CompCert4Lean.X86.Asmgen.transl_load chunk addr args dest k = .OK c → tail_nolabel k c

def transl_store_labelStatement : Prop :=
  ∀ (chunk : memory_chunk) (addr : Addressing) (args : List Mreg)
    (src : Mreg) (k c : AsmCode),
    CompCert4Lean.X86.Asmgen.transl_store chunk addr args src k = .OK c → tail_nolabel k c

def transl_instr_labelStatement : Prop :=
  ∀ (f : MachFunction) (i : MachInstruction) (ep : Bool) (k c : AsmCode),
    CompCert4Lean.X86.Asmgen.transl_instr f i ep k = .OK c →
    match i with
    | .Mlabel lbl => c = .Plabel lbl :: k
    | _ => tail_nolabel k c

def transl_instr_label'Statement : Prop :=
  ∀ (lbl : positive) (f : MachFunction) (i : MachInstruction) (ep : Bool)
    (k c : AsmCode),
    CompCert4Lean.X86.Asmgen.transl_instr f i ep k = .OK c →
    CompCert4Lean.Backend.Asmgenproof0.find_label lbl c =
      if CompCert4Lean.Backend.Mach.is_label lbl i then some k else
        CompCert4Lean.Backend.Asmgenproof0.find_label lbl k

def transl_code_labelStatement : Prop :=
  ∀ (lbl : positive) (f : MachFunction) (c : MachCode) (ep : Bool)
    (tc : AsmCode),
    CompCert4Lean.X86.Asmgen.transl_code f c ep = .OK tc →
    match CompCert4Lean.Backend.Mach.find_label lbl c with
    | none => CompCert4Lean.Backend.Asmgenproof0.find_label lbl tc = none
    | some c' => ∃ tc',
        CompCert4Lean.Backend.Asmgenproof0.find_label lbl tc = some tc' ∧
        CompCert4Lean.X86.Asmgen.transl_code f c' false = .OK tc'

def transl_find_labelStatement : Prop :=
  ∀ (lbl : positive) (f : MachFunction) (tf : AsmFunction),
    CompCert4Lean.X86.Asmgen.transf_function f = .OK tf →
    match CompCert4Lean.Backend.Mach.find_label lbl f.fn_code with
    | none => CompCert4Lean.Backend.Asmgenproof0.find_label lbl tf.fn_code = none
    | some c => ∃ tc,
        CompCert4Lean.Backend.Asmgenproof0.find_label lbl tf.fn_code = some tc ∧
        CompCert4Lean.X86.Asmgen.transl_code f c false = .OK tc

def find_label_goto_labelStatement : Prop :=
  ∀ (prog : MachProgram) (tge : AsmGenv) (f : MachFunction) (tf : AsmFunction)
    (lbl : positive) (rs : AsmRegset) (m : Mem) (c' : MachCode)
    (b : Block) (ofs : PtrofsInt),
    Genv.find_funct_ptr (Genv.globalenv prog) b = some (.Internal f) →
    CompCert4Lean.X86.Asmgen.transf_function f = .OK tf →
    rs .PC = .Vptr b ofs →
    CompCert4Lean.Backend.Mach.find_label lbl f.fn_code = some c' →
    ∃ tc' rs',
      CompCert4Lean.X86.Asm.goto_label tge tf lbl rs m = .Next rs' m ∧
      transl_code_at_pc (Genv.globalenv prog) (rs' .PC) b f c' false tf tc' ∧
      (∀ r, r ≠ .PC → rs' r = rs r)

def return_address_existsStatement : Prop :=
  ∀ (f : MachFunction) (sg : signature) (ros : Sum Mreg ident) (c : MachCode),
    is_tail (.Mcall sg ros :: c) f.fn_code →
    ∃ ra, CompCert4Lean.Backend.Asmgenproof0.return_address_offset f c ra

def exec_straight_stepsStatement : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls)
    (prog : MachProgram) (tprog : AsmProgram), match_prog prog tprog →
    ∀ (s : List MachStackframe) (fb : Block) (f : MachFunction)
      (rs1 : AsmRegset) (i : MachInstruction) (c : MachCode) (ep : Bool)
      (tf : AsmFunction) (tc : AsmCode) (m1' m2 m2' : Mem)
      (sp : Val) (ms2 : MachRegset),
      match_stack (Genv.globalenv prog) s →
      CompCert4Lean.Common.Memory.Mem.extends m2 m2' →
      Genv.find_funct_ptr (Genv.globalenv prog) fb = some (.Internal f) →
      transl_code_at_pc (Genv.globalenv prog) (rs1 .PC) fb f (i :: c) ep tf tc →
      (∀ (k c' : AsmCode), CompCert4Lean.X86.Asmgen.transl_instr f i ep k = .OK c' →
        ∃ rs2,
          exec_straight (Genv.globalenv tprog) tf c' rs1 m1' k rs2 m2' ∧
          CompCert4Lean.Backend.Asmgenproof0.agree ms2 sp rs2 ∧
          (CompCert4Lean.X86.Asmgen.it1_is_parent ep i = true →
            rs2 (.IR .RAX) = parent_sp s)) →
      ∃ st',
        plus (asmStep cfg xi) (Genv.globalenv tprog) (.State rs1 m1') E0 st' ∧
        match_states (Genv.globalenv prog) (.State s fb sp c ms2 m2) st'

def exec_straight_steps_gotoStatement : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls)
    (prog : MachProgram) (tprog : AsmProgram), match_prog prog tprog →
    ∀ (s : List MachStackframe) (fb : Block) (f : MachFunction)
      (rs1 : AsmRegset) (i : MachInstruction) (c : MachCode) (ep : Bool)
      (tf : AsmFunction) (tc : AsmCode) (m1' m2 m2' : Mem)
      (sp : Val) (ms2 : MachRegset) (lbl : positive) (c' : MachCode),
      match_stack (Genv.globalenv prog) s →
      CompCert4Lean.Common.Memory.Mem.extends m2 m2' →
      Genv.find_funct_ptr (Genv.globalenv prog) fb = some (.Internal f) →
      CompCert4Lean.Backend.Mach.find_label lbl f.fn_code = some c' →
      transl_code_at_pc (Genv.globalenv prog) (rs1 .PC) fb f (i :: c) ep tf tc →
      CompCert4Lean.X86.Asmgen.it1_is_parent ep i = false →
      (∀ (k c'' : AsmCode), CompCert4Lean.X86.Asmgen.transl_instr f i ep k = .OK c'' →
        ∃ jmp k' rs2,
          exec_straight (Genv.globalenv tprog) tf c'' rs1 m1' (jmp :: k') rs2 m2' ∧
          CompCert4Lean.Backend.Asmgenproof0.agree ms2 sp rs2 ∧
          CompCert4Lean.X86.Asm.exec_instr (Genv.globalenv tprog) tf jmp rs2 m2' =
            CompCert4Lean.X86.Asm.goto_label (Genv.globalenv tprog) tf lbl rs2 m2') →
      ∃ st',
        plus (asmStep cfg xi) (Genv.globalenv tprog) (.State rs1 m1') E0 st' ∧
        match_states (Genv.globalenv prog) (.State s fb sp c' ms2 m2) st'

def step_simulationStatement : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls)
    (prog : MachProgram) (tprog : AsmProgram), match_prog prog tprog →
    ∀ (S1 : MachState) (t : trace) (S2 : MachState),
      CompCert4Lean.Backend.Mach.step cfg xi
        CompCert4Lean.Backend.Asmgenproof0.return_address_offset
        (Genv.globalenv prog) S1 t S2 →
      ∀ S1', match_states (Genv.globalenv prog) S1 S1' →
        (∃ S2',
          plus (asmStep cfg xi) (Genv.globalenv tprog) S1' t S2' ∧
            match_states (Genv.globalenv prog) S2 S2') ∨
        (measure S2 < measure S1 ∧ t = E0 ∧
          match_states (Genv.globalenv prog) S2 S1')

def transf_initial_statesStatement : Prop :=
  ∀ (prog : MachProgram) (tprog : AsmProgram), match_prog prog tprog →
    ∀ st1, CompCert4Lean.Backend.Mach.initial_state prog st1 →
      ∃ st2, CompCert4Lean.X86.Asm.initial_state tprog st2 ∧
        match_states (Genv.globalenv prog) st1 st2

def transf_final_statesStatement : Prop :=
  ∀ (prog : MachProgram) (tprog : AsmProgram), match_prog prog tprog →
    ∀ (st1 : MachState) (st2 : AsmState) (r : CompCert4Lean.Lib.Integers.int),
      match_states (Genv.globalenv prog) st1 st2 →
      CompCert4Lean.Backend.Mach.final_state st1 r →
        CompCert4Lean.X86.Asm.final_state st2 r

def transf_program_correctStatement : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls)
    (prog : MachProgram) (tprog : AsmProgram), match_prog prog tprog →
    forward_simulation
      (CompCert4Lean.Backend.Mach.semantics cfg xi
        CompCert4Lean.Backend.Asmgenproof0.return_address_offset prog)
      (CompCert4Lean.X86.Asm.semantics cfg xi tprog)

end CompCert4Lean.X86.Asmgenproof
