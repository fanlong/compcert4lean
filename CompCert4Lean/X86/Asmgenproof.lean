import CompCert4Lean.Backend.Asmgenproof0
import CompCert4Lean.Backend.Mach
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Common.Values
import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.X86.Asm
import CompCert4Lean.X86.Asmgen
import CompCert4Lean.X86.Asmgenproof1

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
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

private def asmStep
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (xi : ExternalCalls) :
    AsmGenv → AsmState → trace → AsmState → Prop :=
  CompCert4Lean.X86.Asm.step
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) cfg xi

/-! ## Program matching -/

def match_prog (p : MachProgram) (tp : AsmProgram) : Prop :=
  @match_program MachFundef Unit AsmFundef Unit
    (Linker_fundef MachFunction) Linker_unit
    (fun _ f tf => CompCert4Lean.X86.Asmgen.transf_fundef f = .OK tf)
    (fun x y : Unit => x = y) p tp

/-! ## State matching for the simulation -/

inductive match_states (prog : MachProgram) : MachState → AsmState → Prop where
  | match_states_intro
      (s : List MachStackframe) (fb : Block) (sp : Val)
      (c : MachCode) (ep : Bool) (ms : MachRegset) (m m' : Mem)
      (rs : AsmRegset) (f : MachFunction) (tf : AsmFunction) (tc : AsmCode)
      (stacks : match_stack (Genv.globalenv prog) s)
      (find : Genv.find_funct_ptr (Genv.globalenv prog) fb = some (.Internal f))
      (mext : CompCert4Lean.Common.Memory.Mem.extends m m')
      (atpc : transl_code_at_pc (Genv.globalenv prog) (rs .PC) fb f c ep tf tc)
      (agree : CompCert4Lean.Backend.Asmgenproof0.agree ms sp rs)
      (axp : ep = true → rs (.IR .RAX) = parent_sp s) :
      match_states prog
        (.State s fb sp c ms m)
        (.State rs m')
  | match_states_call
      (s : List MachStackframe) (fb : Block) (ms : MachRegset)
      (m m' : Mem) (rs : AsmRegset)
      (stacks : match_stack (Genv.globalenv prog) s)
      (mext : CompCert4Lean.Common.Memory.Mem.extends m m')
      (agree : CompCert4Lean.Backend.Asmgenproof0.agree ms (parent_sp s) rs)
      (atpc : rs .PC = .Vptr fb Ptrofs.zero)
      (atlr : rs .RA = parent_ra s) :
      match_states prog
        (.Callstate s fb ms m)
        (.State rs m')
  | match_states_return
      (s : List MachStackframe) (ms : MachRegset) (m m' : Mem)
      (rs : AsmRegset)
      (stacks : match_stack (Genv.globalenv prog) s)
      (mext : CompCert4Lean.Common.Memory.Mem.extends m m')
      (agree : CompCert4Lean.Backend.Asmgenproof0.agree ms (parent_sp s) rs)
      (atpc : rs .PC = parent_ra s) :
      match_states prog
        (.Returnstate s ms m)
        (.State rs m')

/-! Authenticated source-facing constructor endpoints.  The inductive
    parameter `prog` is implicit on the kernel constructors because it is a
    parameter of `match_states`; these aliases expose the exact Rocq
    application surface while retaining the namespaced kernel constructors. -/
abbrev match_states_intro (prog : MachProgram) := @match_states.match_states_intro prog
abbrev match_states_call (prog : MachProgram) := @match_states.match_states_call prog
abbrev match_states_return (prog : MachProgram) := @match_states.match_states_return prog

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

def exec_straight_execStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls)
    (prog : MachProgram) (tprog : AsmProgram), match_prog prog tprog →
    ∀ (fb : Block) (f : MachFunction) (c : MachCode) (ep : Bool)
      (tf : AsmFunction) (tc c' : AsmCode) (rs : AsmRegset) (m : Mem)
      (rs' : AsmRegset) (m' : Mem),
      transl_code_at_pc (Genv.globalenv prog) (rs .PC) fb f c ep tf tc →
      exec_straight
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (Genv.globalenv tprog) tf tc rs m c' rs' m' →
      plus (asmStep
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg xi) (Genv.globalenv tprog)
        (.State rs m) E0 (.State rs' m')

def exec_straight_atStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (prog : MachProgram) (tprog : AsmProgram), match_prog prog tprog →
    ∀ (fb : Block) (f : MachFunction) (c : MachCode) (ep : Bool)
      (tf : AsmFunction) (tc : AsmCode) (c' : MachCode) (ep' : Bool)
      (tc' : AsmCode) (rs : AsmRegset) (m : Mem) (rs' : AsmRegset) (m' : Mem),
      transl_code_at_pc (Genv.globalenv prog) (rs .PC) fb f c ep tf tc →
      CompCert4Lean.X86.Asmgen.transl_code f c' ep' = .OK tc' →
      exec_straight
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (Genv.globalenv tprog) tf tc rs m tc' rs' m' →
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
  ∀ (prog : MachProgram) (f : MachFunction) (tf : AsmFunction)
    (lbl : positive) (rs : AsmRegset) (m : Mem) (c' : MachCode)
    (b : Block) (ofs : PtrofsInt),
    Genv.find_funct_ptr (Genv.globalenv prog) b = some (.Internal f) →
    CompCert4Lean.X86.Asmgen.transf_function f = .OK tf →
    rs .PC = .Vptr b ofs →
    CompCert4Lean.Backend.Mach.find_label lbl f.fn_code = some c' →
    ∃ tc' rs',
      CompCert4Lean.X86.Asm.goto_label tf lbl rs m = .Next rs' m ∧
      transl_code_at_pc (Genv.globalenv prog) (rs' .PC) b f c' false tf tc' ∧
      (∀ r, r ≠ .PC → rs' r = rs r)

def return_address_existsStatement : Prop :=
  ∀ (f : MachFunction) (sg : signature) (ros : Sum Mreg ident) (c : MachCode),
    is_tail (.Mcall sg ros :: c) f.fn_code →
    ∃ ra, CompCert4Lean.Backend.Asmgenproof0.return_address_offset f c ra

def exec_straight_stepsStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
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
          exec_straight
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            (Genv.globalenv tprog) tf c' rs1 m1' k rs2 m2' ∧
          CompCert4Lean.Backend.Asmgenproof0.agree ms2 sp rs2 ∧
          (CompCert4Lean.X86.Asmgen.it1_is_parent ep i = true →
            rs2 (.IR .RAX) = parent_sp s)) →
      ∃ st',
        plus (asmStep
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          cfg xi) (Genv.globalenv tprog) (.State rs1 m1') E0 st' ∧
        match_states prog (.State s fb sp c ms2 m2) st'

def exec_straight_steps_gotoStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
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
          exec_straight
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            (Genv.globalenv tprog) tf c'' rs1 m1' (jmp :: k') rs2 m2' ∧
          CompCert4Lean.Backend.Asmgenproof0.agree ms2 sp rs2 ∧
          CompCert4Lean.X86.Asm.exec_instr
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            (Genv.globalenv tprog) tf jmp rs2 m2' =
            CompCert4Lean.X86.Asm.goto_label tf lbl rs2 m2') →
      ∃ st',
        plus (asmStep
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          cfg xi) (Genv.globalenv tprog) (.State rs1 m1') E0 st' ∧
        match_states prog (.State s fb sp c' ms2 m2) st'

def step_simulationStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls)
    (prog : MachProgram) (tprog : AsmProgram), match_prog prog tprog →
    ∀ (S1 : MachState) (t : trace) (S2 : MachState),
      CompCert4Lean.Backend.Mach.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg xi
        CompCert4Lean.Backend.Asmgenproof0.return_address_offset
        (Genv.globalenv prog) S1 t S2 →
      ∀ S1', match_states prog S1 S1' →
        (∃ S2',
          plus (asmStep
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            cfg xi) (Genv.globalenv tprog) S1' t S2' ∧
            match_states prog S2 S2') ∨
        (measure S2 < measure S1 ∧ t = E0 ∧
          match_states prog S2 S1')

def transf_initial_statesStatement : Prop :=
  ∀ (prog : MachProgram) (tprog : AsmProgram), match_prog prog tprog →
    ∀ st1, CompCert4Lean.Backend.Mach.initial_state prog st1 →
      ∃ st2, CompCert4Lean.X86.Asm.initial_state tprog st2 ∧
        match_states prog st1 st2

def transf_final_statesStatement : Prop :=
  ∀ (prog : MachProgram) (st1 : MachState) (st2 : AsmState)
    (r : CompCert4Lean.Lib.Integers.int),
    match_states prog st1 st2 →
    CompCert4Lean.Backend.Mach.final_state st1 r →
      CompCert4Lean.X86.Asm.final_state st2 r

def transf_program_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls)
    (prog : MachProgram) (tprog : AsmProgram), match_prog prog tprog →
    forward_simulation
      (CompCert4Lean.Backend.Mach.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg xi CompCert4Lean.Backend.Asmgenproof0.return_address_offset prog)
      (CompCert4Lean.X86.Asm.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg xi tprog)

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib

theorem transf_program_match : transf_program_matchStatement := by
  intro p tp h
  letI : Linker MachFundef := Linker_fundef MachFunction
  letI : Linker Unit := Linker_unit
  letI : Linker MachProgram := Linker_prog MachFundef Unit
  unfold match_prog
  cases htp : CompCert4Lean.X86.Asmgen.transf_program p with
  | Error msg =>
      rw [htp] at h
      cases h
  | OK defs =>
      rw [htp] at h
      injection h with hEq
      subst tp
      unfold CompCert4Lean.X86.Asmgen.transf_program
          CompCert4Lean.Common.AST.transform_partial_program
          CompCert4Lean.Common.AST.transform_partial_program2 at htp
      split at htp
      · cases htp
      · rename_i hdefs
        injection htp with hEq
        subst defs
        constructor
        · have hlist : ∀ (xs : List (ident × globdef MachFundef Unit))
            (ys : List (ident × globdef AsmFundef Unit)),
            CompCert4Lean.Common.AST.transf_globdefs
                (fun _ f => CompCert4Lean.X86.Asmgen.transf_fundef f)
                (fun _ v => .OK v) xs = .OK ys →
              list_forall2
                (match_ident_globdef
                  (fun _ f tf => CompCert4Lean.X86.Asmgen.transf_fundef f = .OK tf)
                  (fun x y : Unit => x = y) p) xs ys := by
            intro xs
            induction xs with
            | nil =>
                intro ys hys
                cases ys with
                | nil => exact list_forall2_nil _
                | cons y ys => cases hys
            | cons x xs ih =>
                intro ys hys
                cases x with
                | mk id gd =>
                    cases gd with
                    | Gfun f =>
                        cases htf : CompCert4Lean.X86.Asmgen.transf_fundef f with
                        | Error msg =>
                            simp [CompCert4Lean.Common.AST.transf_globdefs, htf] at hys
                        | OK tf =>
                            cases htail : CompCert4Lean.Common.AST.transf_globdefs
                                (fun _ f => CompCert4Lean.X86.Asmgen.transf_fundef f)
                                (fun _ v => .OK v) xs with
                            | Error msg =>
                                simp [CompCert4Lean.Common.AST.transf_globdefs, htf, htail] at hys
                            | OK ys' =>
                                cases ys with
                                | nil =>
                                    simp [CompCert4Lean.Common.AST.transf_globdefs, htf, htail] at hys
                                    cases hys
                                | cons y ys =>
                                    cases y with
                                    | mk id' gd' =>
                                        simp [CompCert4Lean.Common.AST.transf_globdefs, htf, htail] at hys
                                        cases hys
                                        apply list_forall2.cons
                                        · constructor
                                          · rfl
                                          · apply match_globdef_fun (ctx' := p)
                                            · exact linkorder_refl _
                                            · exact htf
                                        · exact ih ys' (by simp [htail])
                    | Gvar v =>
                        cases htail : CompCert4Lean.Common.AST.transf_globdefs
                            (fun _ f => CompCert4Lean.X86.Asmgen.transf_fundef f)
                            (fun _ v => .OK v) xs with
                        | Error msg =>
                            simp [CompCert4Lean.Common.AST.transf_globdefs,
                              CompCert4Lean.Common.AST.transf_globvar, htail] at hys
                        | OK ys' =>
                            cases ys with
                            | nil =>
                                simp [CompCert4Lean.Common.AST.transf_globdefs,
                                  CompCert4Lean.Common.AST.transf_globvar, htail] at hys
                                cases hys
                            | cons y ys =>
                                cases y with
                                | mk id' gd' =>
                                    simp [CompCert4Lean.Common.AST.transf_globdefs, htail] at hys
                                    cases hys
                                    apply list_forall2.cons
                                    · constructor
                                      · rfl
                                      · apply match_globdef_var
                                        exact match_globvar_intro _ _ _ _ _ _ rfl
                                    · exact ih ys' (by simp [htail])
          exact hlist p.prog_defs _ hdefs
        · exact ⟨rfl, rfl⟩

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Asm
open CompCert4Lean.X86.Asmgen

private theorem asmgenproof_ptree_get_set0 {A : Type} (x y : positive) (v : A) :
    PTree.get' x (PTree.set0 y v) = if _h : x = y then some v else none := by
  induction x generalizing y with
  | xH => cases y <;> simp [PTree.get', PTree.set0]
  | xO x ih => cases y <;> simp [PTree.get', PTree.set0, ih]
  | xI x ih => cases y <;> simp [PTree.get', PTree.set0, ih]

private theorem asmgenproof_ptree_get_set' {A : Type} (x y : positive) (v : A)
    (m : PTree.tree' A) :
    PTree.get' x (PTree.set' y v m) =
      if _h : x = y then some v else PTree.get' x m := by
  induction x generalizing y m with
  | xH => cases y <;> cases m <;> simp [PTree.get', PTree.set']
  | xO x ih =>
      cases y <;> cases m <;>
        simp [PTree.get', PTree.set', asmgenproof_ptree_get_set0, ih]
  | xI x ih =>
      cases y <;> cases m <;>
        simp [PTree.get', PTree.set', asmgenproof_ptree_get_set0, ih]

private theorem asmgenproof_ptree_get_set {A : Type} (i j : positive) (v : A)
    (m : PTree.t A) :
    PTree.get i (PTree.set j v m) = if _h : i = j then some v else PTree.get i m := by
  cases m with
  | Empty =>
      simpa [PTree.get, PTree.set] using asmgenproof_ptree_get_set0 i j v
  | Nodes m =>
      simpa [PTree.get, PTree.set] using asmgenproof_ptree_get_set' i j v m

private theorem asmgenproof_ptree_set_rel {A B : Type} (R : A → B → Prop)
    (i j : positive) (x : A) (y : B) (m1 : PTree.t A) (m2 : PTree.t B)
    (hxy : R x y)
    (h : ∀ k, option_rel R (PTree.get k m1) (PTree.get k m2)) :
    option_rel R (PTree.get i (PTree.set j x m1)) (PTree.get i (PTree.set j y m2)) := by
  rw [asmgenproof_ptree_get_set, asmgenproof_ptree_get_set]
  by_cases hij : i = j
  · simp only [dif_pos hij]
    exact .some _ _ hxy
  · simp only [dif_neg hij]
    exact h i

private theorem asmgenproof_add_global_match {A B V W : Type}
    (R : globdef A V → globdef B W → Prop)
    (ge1 : Genv.t A V) (ge2 : Genv.t B W) (id : positive)
    (g1 : globdef A V) (g2 : globdef B W)
    (hge : Genv.match_genvs R ge1 ge2) (hgd : R g1 g2) :
    Genv.match_genvs R (Genv.add_global ge1 (id, g1))
      (Genv.add_global ge2 (id, g2)) := by
  rcases hge with ⟨hnext, hsymb, hdefs⟩
  constructor
  · exact congrArg _ hnext
  · intro id'
    change PTree.get id' (PTree.set id ge2.genv_next ge2.genv_symb) =
      PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb)
    rw [asmgenproof_ptree_get_set, asmgenproof_ptree_get_set]
    split <;> simp_all
  · intro b
    change option_rel R
      (PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs))
      (PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs))
    rw [hnext]
    exact asmgenproof_ptree_set_rel R b ge1.genv_next g1 g2
      ge1.genv_defs ge2.genv_defs hgd hdefs

private theorem asmgenproof_add_globals_match {A B V W : Type}
    (R : globdef A V → globdef B W → Prop)
    (ge1 : Genv.t A V) (ge2 : Genv.t B W) (hge : Genv.match_genvs R ge1 ge2) :
    ∀ (xs : List (ident × globdef A V)) (ys : List (ident × globdef B W)),
      list_forall2
        (fun (x : ident × globdef A V) (y : ident × globdef B W) =>
          x.1 = y.1 ∧ R x.2 y.2) xs ys →
      Genv.match_genvs R (Genv.add_globals ge1 xs) (Genv.add_globals ge2 ys) := by
  intro xs ys h
  induction h generalizing ge1 ge2 with
  | nil => simpa [Genv.add_globals] using hge
  | cons x y hxy htail ih =>
      rcases x with ⟨id, g1⟩
      rcases y with ⟨id', g2⟩
      rcases hxy with ⟨hid, hg⟩
      change id = id' at hid
      change R g1 g2 at hg
      subst id'
      simp only [Genv.add_globals, List.foldl]
      exact ih (Genv.add_global ge1 (id, g1)) (Genv.add_global ge2 (id, g2))
        (asmgenproof_add_global_match R ge1 ge2 id g1 g2 hge hg)

private theorem asmgenproof_empty_genv_match {A B V W : Type}
    (R : globdef A V → globdef B W → Prop) (pub : List ident) :
    Genv.match_genvs R (Genv.empty_genv A V pub) (Genv.empty_genv B W pub) := by
  constructor
  · rfl
  · intro id
    rfl
  · intro b
    exact .none _

private theorem asmgenproof_globalenv_match {C F1 V1 F2 V2 : Type} [Linker C]
    (mf : C → F1 → F2 → Prop) (mv : V1 → V2 → Prop) (ctx : C)
    (p : program F1 V1) (tp : program F2 V2)
    (h : match_program_gen mf mv ctx p tp) :
    Genv.match_genvs (match_globdef mf mv ctx)
      (Genv.globalenv p) (Genv.globalenv tp) := by
  rcases h with ⟨hdefs, hmain, hpub⟩
  unfold Genv.globalenv
  rw [hpub]
  apply asmgenproof_add_globals_match
  apply asmgenproof_empty_genv_match
  exact hdefs

private theorem asmgenproof_volatile_match {C F1 V1 F2 V2 : Type} [Linker C]
    (mf : C → F1 → F2 → Prop) (mv : V1 → V2 → Prop) (ctx : C)
    (p : program F1 V1) (tp : program F2 V2)
    (hge : Genv.match_genvs (match_globdef mf mv ctx)
      (Genv.globalenv p) (Genv.globalenv tp)) (b : positive) :
    Genv.block_is_volatile (Genv.globalenv tp) b =
      Genv.block_is_volatile (Genv.globalenv p) b := by
  unfold Genv.block_is_volatile Genv.find_var_info Genv.find_def
  have hrel := hge.mge_defs b
  cases hs : PTree.get b (Genv.globalenv p).genv_defs with
  | none =>
      cases st : PTree.get b (Genv.globalenv tp).genv_defs with
      | none => simp [hs, st]
      | some tg => rw [hs, st] at hrel; cases hrel
  | some sg =>
      cases st : PTree.get b (Genv.globalenv tp).genv_defs with
      | none => rw [hs, st] at hrel; cases hrel
      | some tg =>
          rw [hs, st] at hrel
          cases hrel with
          | some _ _ hgd =>
              cases hgd with
              | match_globdef_fun _ _ _ _ _ => simp [hs, st]
              | match_globdef_var _ _ hgv =>
                  cases hgv
                  simp [hs, st]

private theorem asmgenproof_add_globals_public {F V : Type}
    (ge : Genv.t F V) (gl : List (ident × globdef F V)) :
    (Genv.add_globals ge gl).genv_public = ge.genv_public := by
  induction gl generalizing ge with
  | nil => rfl
  | cons x xs ih =>
      simp only [Genv.add_globals, List.foldl]
      exact ih (Genv.add_global ge x)

theorem symbols_preserved : symbols_preservedStatement := by
  intro prog tprog hprog s
  letI : Linker MachFundef := Linker_fundef MachFunction
  letI : Linker Unit := Linker_unit
  letI : Linker MachProgram := Linker_prog MachFundef Unit
  unfold match_prog at hprog
  exact (asmgenproof_globalenv_match _ _ _ prog tprog hprog).mge_symb s

theorem senv_preserved : senv_preservedStatement := by
  intro prog tprog hprog
  letI : Linker MachFundef := Linker_fundef MachFunction
  letI : Linker Unit := Linker_unit
  letI : Linker MachProgram := Linker_prog MachFundef Unit
  unfold match_prog CompCert4Lean.Common.Linking.match_program at hprog
  rcases hprog with ⟨hdefs, hmain, hpub⟩
  have hge := asmgenproof_globalenv_match _ _ _ prog tprog ⟨hdefs, hmain, hpub⟩
  constructor
  · exact hge.mge_symb
  · constructor
    · intro id
      change Genv.public_symbol (Genv.globalenv tprog) id =
        Genv.public_symbol (Genv.globalenv prog) id
      have hs : Genv.find_symbol (Genv.globalenv tprog) id =
          Genv.find_symbol (Genv.globalenv prog) id := hge.mge_symb id
      have hp : (Genv.globalenv tprog).genv_public =
          (Genv.globalenv prog).genv_public := by
        unfold Genv.globalenv
        rw [asmgenproof_add_globals_public, asmgenproof_add_globals_public]
        exact hpub
      unfold Genv.public_symbol
      rw [hs, hp]
    · intro b
      exact asmgenproof_volatile_match _ _ _ _ _ hge b

theorem functions_translated : functions_translatedStatement := by
  intro prog tprog hprog b f hfind
  letI : Linker MachFundef := Linker_fundef MachFunction
  letI : Linker Unit := Linker_unit
  letI : Linker MachProgram := Linker_prog MachFundef Unit
  unfold match_prog at hprog
  have hge := asmgenproof_globalenv_match _ _ _ prog tprog hprog
  unfold Genv.find_funct_ptr Genv.find_def at hfind
  cases hsrc : PTree.get b (Genv.globalenv prog).genv_defs with
  | none => simp [hsrc] at hfind
  | some gd =>
      cases gd with
      | Gfun f' =>
          simp [hsrc] at hfind
          subst f'
          have hrel := hge.mge_defs b
          rw [hsrc] at hrel
          cases htgt : PTree.get b (Genv.globalenv tprog).genv_defs with
          | none => rw [htgt] at hrel; cases hrel
          | some tgd =>
              rw [htgt] at hrel
              cases hrel with
              | some _ _ hfun =>
                  cases hfun with
                  | match_globdef_fun _ _ _ _ htrans =>
                      exact ⟨_, by
                        simp [Genv.find_funct_ptr, Genv.find_def, htgt], htrans⟩
      | Gvar v => simp [hsrc] at hfind

theorem functions_transl : functions_translStatement := by
  intro prog tprog hprog fb f tf hfind htrans
  rcases functions_translated prog tprog hprog fb (.Internal f) hfind with
    ⟨tf', hfind', hfund⟩
  unfold CompCert4Lean.X86.Asmgen.transf_fundef
    CompCert4Lean.Common.AST.transf_partial_fundef at hfund
  simp [htrans] at hfund
  injection hfund with heq
  subst tf'
  exact hfind'

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

theorem transf_function_no_overflow : transf_function_no_overflowStatement := by
  intro f tf h
  unfold CompCert4Lean.X86.Asmgen.transf_function at h
  cases htf : CompCert4Lean.X86.Asmgen.transl_function f with
  | Error msg =>
      rw [htf] at h
      cases h
  | OK tf0 =>
      rw [htf] at h
      change
        (match CompCert4Lean.Lib.Coqlib.zlt
            CompCert4Lean.Lib.Integers.Ptrofs.max_unsigned
            (CompCert4Lean.Lib.Coqlib.list_length_z tf0.fn_code) with
          | .left _ => _
          | .right _ => _) =
          CompCert4Lean.Common.Errors.OK tf at h
      cases hz : CompCert4Lean.Lib.Coqlib.zlt
          CompCert4Lean.Lib.Integers.Ptrofs.max_unsigned
          (CompCert4Lean.Lib.Coqlib.list_length_z tf0.fn_code) with
      | left hlt =>
          rw [hz] at h
          cases h
      | right hge =>
          rw [hz] at h
          cases h
          exact hge

theorem loadind_label : loadind_labelStatement := by
  intro base ofs ty dst k c h
  cases ty <;> cases hdst : CompCert4Lean.X86.Asm.preg_of dst <;>
    simp [CompCert4Lean.X86.Asmgen.loadind, hdst] at h <;>
    cases h <;>
    simp [CompCert4Lean.Backend.Asmgenproof0.tail_nolabel,
      CompCert4Lean.Backend.Asmgenproof0.find_label,
      CompCert4Lean.Lib.Coqlib.is_tail,
      CompCert4Lean.X86.Asm.is_label] <;>
    exact CompCert4Lean.Lib.Coqlib.is_tail.cons _
      (CompCert4Lean.Lib.Coqlib.is_tail.refl _)

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof
theorem storeind_label : storeind_labelStatement := by
  intro base ofs ty src k c h
  cases ty <;> cases hsrc : CompCert4Lean.X86.Asm.preg_of src <;>
    simp [CompCert4Lean.X86.Asmgen.storeind, hsrc] at h <;> cases h <;>
    simp [CompCert4Lean.Backend.Asmgenproof0.tail_nolabel,
      CompCert4Lean.Backend.Asmgenproof0.find_label, CompCert4Lean.X86.Asm.is_label]
  all_goals apply CompCert4Lean.Lib.Coqlib.is_tail.cons <;>
    exact CompCert4Lean.Lib.Coqlib.is_tail.refl _
end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

private theorem asmgenproof_tail_nolabel_if
    (p : Bool) (k c₁ c₂ : AsmCode)
    (h₁ : CompCert4Lean.Backend.Asmgenproof0.tail_nolabel k c₁)
    (h₂ : CompCert4Lean.Backend.Asmgenproof0.tail_nolabel k c₂) :
    CompCert4Lean.Backend.Asmgenproof0.tail_nolabel k (if p then c₁ else c₂) := by
  cases p <;> simp_all

private theorem asmgenproof_mk_setcc_base_label :
    ∀ (xc : Extcond) (rd : Ireg) (k : AsmCode),
      CompCert4Lean.Backend.Asmgenproof0.tail_nolabel k
        (CompCert4Lean.X86.Asmgen.mk_setcc_base xc rd k) := by
  intro xc rd k
  cases xc with
  | Cond_base c =>
      simp only [CompCert4Lean.X86.Asmgen.mk_setcc_base]
      constructor
      · exact CompCert4Lean.Lib.Coqlib.is_tail.cons _
          (CompCert4Lean.Lib.Coqlib.is_tail.refl _)
      · intro lbl
        simp [CompCert4Lean.Backend.Asmgenproof0.find_label,
          CompCert4Lean.X86.Asm.is_label]
  | Cond_or c1 c2 =>
      simp only [CompCert4Lean.X86.Asmgen.mk_setcc_base]
      apply asmgenproof_tail_nolabel_if
      · constructor
        · exact CompCert4Lean.Lib.Coqlib.is_tail.cons _
            (CompCert4Lean.Lib.Coqlib.is_tail.cons _
              (CompCert4Lean.Lib.Coqlib.is_tail.cons _
                (CompCert4Lean.Lib.Coqlib.is_tail.refl _)))
        · intro lbl
          simp [CompCert4Lean.Backend.Asmgenproof0.find_label,
            CompCert4Lean.X86.Asm.is_label]
      · constructor
        · exact CompCert4Lean.Lib.Coqlib.is_tail.cons _
            (CompCert4Lean.Lib.Coqlib.is_tail.cons _
              (CompCert4Lean.Lib.Coqlib.is_tail.cons _
                (CompCert4Lean.Lib.Coqlib.is_tail.refl _)))
        · intro lbl
          simp [CompCert4Lean.Backend.Asmgenproof0.find_label,
            CompCert4Lean.X86.Asm.is_label]
  | Cond_and c1 c2 =>
      simp only [CompCert4Lean.X86.Asmgen.mk_setcc_base]
      apply asmgenproof_tail_nolabel_if
      · constructor
        · exact CompCert4Lean.Lib.Coqlib.is_tail.cons _
            (CompCert4Lean.Lib.Coqlib.is_tail.cons _
              (CompCert4Lean.Lib.Coqlib.is_tail.cons _
                (CompCert4Lean.Lib.Coqlib.is_tail.refl _)))
        · intro lbl
          simp [CompCert4Lean.Backend.Asmgenproof0.find_label,
            CompCert4Lean.X86.Asm.is_label]
      · constructor
        · exact CompCert4Lean.Lib.Coqlib.is_tail.cons _
            (CompCert4Lean.Lib.Coqlib.is_tail.cons _
              (CompCert4Lean.Lib.Coqlib.is_tail.cons _
                (CompCert4Lean.Lib.Coqlib.is_tail.refl _)))
        · intro lbl
          simp [CompCert4Lean.Backend.Asmgenproof0.find_label,
            CompCert4Lean.X86.Asm.is_label]

theorem mk_setcc_label : mk_setcc_labelStatement := by
  intro xc rd k
  unfold CompCert4Lean.X86.Asmgen.mk_setcc
  simp [CompCert4Lean.X86_64.Archi.ptr64]
  exact asmgenproof_mk_setcc_base_label xc rd k

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

theorem mk_jcc_label : mk_jcc_labelStatement := by
  intro xc lbl k
  cases xc with
  | Cond_base c =>
      simp [CompCert4Lean.X86.Asmgen.mk_jcc,
        CompCert4Lean.Backend.Asmgenproof0.tail_nolabel,
        CompCert4Lean.Backend.Asmgenproof0.find_label,
        CompCert4Lean.X86.Asm.is_label]
      exact CompCert4Lean.Lib.Coqlib.is_tail.cons _
        (CompCert4Lean.Lib.Coqlib.is_tail.refl _)
  | Cond_and c1 c2 =>
      simp [CompCert4Lean.X86.Asmgen.mk_jcc,
        CompCert4Lean.Backend.Asmgenproof0.tail_nolabel,
        CompCert4Lean.Backend.Asmgenproof0.find_label,
        CompCert4Lean.X86.Asm.is_label]
      exact CompCert4Lean.Lib.Coqlib.is_tail.cons _
        (CompCert4Lean.Lib.Coqlib.is_tail.refl _)
  | Cond_or c1 c2 =>
      simp [CompCert4Lean.X86.Asmgen.mk_jcc,
        CompCert4Lean.Backend.Asmgenproof0.tail_nolabel,
        CompCert4Lean.Backend.Asmgenproof0.find_label,
        CompCert4Lean.X86.Asm.is_label]
      exact CompCert4Lean.Lib.Coqlib.is_tail.cons _
        (CompCert4Lean.Lib.Coqlib.is_tail.cons _
          (CompCert4Lean.Lib.Coqlib.is_tail.refl _))

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

theorem mk_sel_label : mk_sel_labelStatement := by
  intro xc rd r2 k c h
  cases xc <;> simp [CompCert4Lean.X86.Asmgen.mk_sel] at h <;> cases h
  all_goals
    simp [CompCert4Lean.Backend.Asmgenproof0.tail_nolabel,
      CompCert4Lean.Backend.Asmgenproof0.find_label,
      CompCert4Lean.X86.Asm.is_label]
    repeat' apply CompCert4Lean.Lib.Coqlib.is_tail.cons
    exact CompCert4Lean.Lib.Coqlib.is_tail.refl _

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

private theorem asmgenproof_tail_nolabel_cons (k : AsmCode)
    (i : CompCert4Lean.X86.Asm.instruction)
    (hi : ∀ lbl, CompCert4Lean.X86.Asm.is_label lbl i = false) :
    CompCert4Lean.Backend.Asmgenproof0.tail_nolabel k (i :: k) := by
  constructor
  · exact CompCert4Lean.Lib.Coqlib.is_tail.cons _
      (CompCert4Lean.Lib.Coqlib.is_tail.refl _)
  · intro lbl
    simp [CompCert4Lean.Backend.Asmgenproof0.find_label, hi]

private theorem asmgenproof_bind_ireg_cons
    (a : Mreg) (k c : AsmCode) (mk : Ireg → CompCert4Lean.X86.Asm.instruction)
    (hi : ∀ r lbl, CompCert4Lean.X86.Asm.is_label lbl (mk r) = false) :
    CompCert4Lean.Common.Errors.bind
      (CompCert4Lean.X86.Asmgen.ireg_of a)
      (fun r => .OK (mk r :: k)) = .OK c →
      CompCert4Lean.Backend.Asmgenproof0.tail_nolabel k c := by
  intro h
  cases hr : CompCert4Lean.X86.Asmgen.ireg_of a with
  | Error msg =>
      simp [hr, CompCert4Lean.Common.Errors.bind] at h
  | OK r =>
      simp [hr, CompCert4Lean.Common.Errors.bind] at h
      cases h
      apply asmgenproof_tail_nolabel_cons k (mk r)
      intro lbl
      exact hi r lbl

private theorem asmgenproof_bind_ireg2_cons
    (a1 a2 : Mreg) (k c : AsmCode)
    (mk : Ireg → Ireg → CompCert4Lean.X86.Asm.instruction)
    (hi : ∀ r1 r2 lbl, CompCert4Lean.X86.Asm.is_label lbl (mk r1 r2) = false) :
    CompCert4Lean.Common.Errors.bind
      (CompCert4Lean.X86.Asmgen.ireg_of a1)
      (fun r1 => CompCert4Lean.Common.Errors.bind
        (CompCert4Lean.X86.Asmgen.ireg_of a2)
        (fun r2 => .OK (mk r1 r2 :: k))) = .OK c →
      CompCert4Lean.Backend.Asmgenproof0.tail_nolabel k c := by
  intro h
  cases hr1 : CompCert4Lean.X86.Asmgen.ireg_of a1 with
  | Error msg =>
      simp [hr1, CompCert4Lean.Common.Errors.bind] at h
  | OK r1 =>
      cases hr2 : CompCert4Lean.X86.Asmgen.ireg_of a2 with
      | Error msg =>
          simp [hr1, hr2, CompCert4Lean.Common.Errors.bind] at h
      | OK r2 =>
          simp [hr1, hr2, CompCert4Lean.Common.Errors.bind] at h
          cases h
          apply asmgenproof_tail_nolabel_cons k (mk r1 r2)
          intro lbl
          exact hi r1 r2 lbl

private theorem asmgenproof_bind_freg2_cons
    (a1 a2 : Mreg) (k c : AsmCode)
    (mk : CompCert4Lean.X86.Asm.freg → CompCert4Lean.X86.Asm.freg →
      CompCert4Lean.X86.Asm.instruction)
    (hi : ∀ r1 r2 lbl, CompCert4Lean.X86.Asm.is_label lbl (mk r1 r2) = false) :
    CompCert4Lean.Common.Errors.bind
      (CompCert4Lean.X86.Asmgen.freg_of a1)
      (fun r1 => CompCert4Lean.Common.Errors.bind
        (CompCert4Lean.X86.Asmgen.freg_of a2)
        (fun r2 => .OK (mk r1 r2 :: k))) = .OK c →
      CompCert4Lean.Backend.Asmgenproof0.tail_nolabel k c := by
  intro h
  cases hr1 : CompCert4Lean.X86.Asmgen.freg_of a1 with
  | Error msg =>
      simp [hr1, CompCert4Lean.Common.Errors.bind] at h
  | OK r1 =>
      cases hr2 : CompCert4Lean.X86.Asmgen.freg_of a2 with
      | Error msg =>
          simp [hr1, hr2, CompCert4Lean.Common.Errors.bind] at h
      | OK r2 =>
          simp [hr1, hr2, CompCert4Lean.Common.Errors.bind] at h
          cases h
          apply asmgenproof_tail_nolabel_cons k (mk r1 r2)
          intro lbl
          exact hi r1 r2 lbl

theorem transl_cond_label : transl_cond_labelStatement := by
  intro cond args k c h
  cases args with
  | nil => simp [CompCert4Lean.X86.Asmgen.transl_cond] at h <;> cases h
  | cons a1 rest =>
      cases rest with
      | nil =>
          cases cond with
          | Ccomp cmp => simp [CompCert4Lean.X86.Asmgen.transl_cond] at h <;> cases h
          | Ccompu cmp => simp [CompCert4Lean.X86.Asmgen.transl_cond] at h <;> cases h
          | Ccompimm cmp n =>
              apply asmgenproof_bind_ireg_cons a1 k c
                (fun r => (if CompCert4Lean.Lib.Integers.Int.eq n
                  CompCert4Lean.Lib.Integers.Int.zero then
                  .Ptestl_rr r r else .Pcmpl_ri r n))
                (by intro r lbl; split <;> simp [CompCert4Lean.X86.Asm.is_label])
              change CompCert4Lean.Common.Errors.bind
                (CompCert4Lean.X86.Asmgen.ireg_of a1)
                (fun r => .OK ((if CompCert4Lean.Lib.Integers.Int.eq n
                  CompCert4Lean.Lib.Integers.Int.zero then
                  .Ptestl_rr r r else .Pcmpl_ri r n) :: k)) = .OK c at h
              exact h
          | Ccompuimm cmp n =>
              apply asmgenproof_bind_ireg_cons a1 k c
                (fun r => .Pcmpl_ri r n)
                (by intro r lbl; simp [CompCert4Lean.X86.Asm.is_label])
              change CompCert4Lean.Common.Errors.bind
                (CompCert4Lean.X86.Asmgen.ireg_of a1)
                (fun r => .OK (.Pcmpl_ri r n :: k)) = .OK c at h
              exact h
          | Ccompl cmp => simp [CompCert4Lean.X86.Asmgen.transl_cond] at h <;> cases h
          | Ccomplu cmp => simp [CompCert4Lean.X86.Asmgen.transl_cond] at h <;> cases h
          | Ccomplimm cmp n =>
              apply asmgenproof_bind_ireg_cons a1 k c
                (fun r => (if CompCert4Lean.Lib.Integers.Int64.eq n
                  CompCert4Lean.Lib.Integers.Int64.zero then
                  .Ptestq_rr r r else .Pcmpq_ri r n))
                (by intro r lbl; split <;> simp [CompCert4Lean.X86.Asm.is_label])
              change CompCert4Lean.Common.Errors.bind
                (CompCert4Lean.X86.Asmgen.ireg_of a1)
                (fun r => .OK ((if CompCert4Lean.Lib.Integers.Int64.eq n
                  CompCert4Lean.Lib.Integers.Int64.zero then
                  .Ptestq_rr r r else .Pcmpq_ri r n) :: k)) = .OK c at h
              exact h
          | Ccompluimm cmp n =>
              apply asmgenproof_bind_ireg_cons a1 k c
                (fun r => .Pcmpq_ri r n)
                (by intro r lbl; simp [CompCert4Lean.X86.Asm.is_label])
              change CompCert4Lean.Common.Errors.bind
                (CompCert4Lean.X86.Asmgen.ireg_of a1)
                (fun r => .OK (.Pcmpq_ri r n :: k)) = .OK c at h
              exact h
          | Ccompf cmp => simp [CompCert4Lean.X86.Asmgen.transl_cond] at h <;> cases h
          | Cnotcompf cmp => simp [CompCert4Lean.X86.Asmgen.transl_cond] at h <;> cases h
          | Ccompfs cmp => simp [CompCert4Lean.X86.Asmgen.transl_cond] at h <;> cases h
          | Cnotcompfs cmp => simp [CompCert4Lean.X86.Asmgen.transl_cond] at h <;> cases h
          | Cmaskzero n =>
              apply asmgenproof_bind_ireg_cons a1 k c
                (fun r => .Ptestl_ri r n)
                (by intro r lbl; simp [CompCert4Lean.X86.Asm.is_label])
              change CompCert4Lean.Common.Errors.bind
                (CompCert4Lean.X86.Asmgen.ireg_of a1)
                (fun r => .OK (.Ptestl_ri r n :: k)) = .OK c at h
              exact h
          | Cmasknotzero n =>
              apply asmgenproof_bind_ireg_cons a1 k c
                (fun r => .Ptestl_ri r n)
                (by intro r lbl; simp [CompCert4Lean.X86.Asm.is_label])
              change CompCert4Lean.Common.Errors.bind
                (CompCert4Lean.X86.Asmgen.ireg_of a1)
                (fun r => .OK (.Ptestl_ri r n :: k)) = .OK c at h
              exact h
      | cons a2 rest2 =>
          cases rest2 with
          | cons a3 rest3 =>
              simp [CompCert4Lean.X86.Asmgen.transl_cond] at h <;> cases h
          | nil =>
              cases cond with
              | Ccomp cmp =>
                  apply asmgenproof_bind_ireg2_cons a1 a2 k c
                    (fun r1 r2 => .Pcmpl_rr r1 r2)
                    (by intro r1 r2 lbl; simp [CompCert4Lean.X86.Asm.is_label])
                  change CompCert4Lean.Common.Errors.bind
                    (CompCert4Lean.X86.Asmgen.ireg_of a1)
                    (fun r1 => CompCert4Lean.Common.Errors.bind
                      (CompCert4Lean.X86.Asmgen.ireg_of a2)
                      (fun r2 => .OK (.Pcmpl_rr r1 r2 :: k))) = .OK c at h
                  exact h
              | Ccompu cmp =>
                  apply asmgenproof_bind_ireg2_cons a1 a2 k c
                    (fun r1 r2 => .Pcmpl_rr r1 r2)
                    (by intro r1 r2 lbl; simp [CompCert4Lean.X86.Asm.is_label])
                  change CompCert4Lean.Common.Errors.bind
                    (CompCert4Lean.X86.Asmgen.ireg_of a1)
                    (fun r1 => CompCert4Lean.Common.Errors.bind
                      (CompCert4Lean.X86.Asmgen.ireg_of a2)
                      (fun r2 => .OK (.Pcmpl_rr r1 r2 :: k))) = .OK c at h
                  exact h
              | Ccompl cmp =>
                  apply asmgenproof_bind_ireg2_cons a1 a2 k c
                    (fun r1 r2 => .Pcmpq_rr r1 r2)
                    (by intro r1 r2 lbl; simp [CompCert4Lean.X86.Asm.is_label])
                  change CompCert4Lean.Common.Errors.bind
                    (CompCert4Lean.X86.Asmgen.ireg_of a1)
                    (fun r1 => CompCert4Lean.Common.Errors.bind
                      (CompCert4Lean.X86.Asmgen.ireg_of a2)
                      (fun r2 => .OK (.Pcmpq_rr r1 r2 :: k))) = .OK c at h
                  exact h
              | Ccomplu cmp =>
                  apply asmgenproof_bind_ireg2_cons a1 a2 k c
                    (fun r1 r2 => .Pcmpq_rr r1 r2)
                    (by intro r1 r2 lbl; simp [CompCert4Lean.X86.Asm.is_label])
                  change CompCert4Lean.Common.Errors.bind
                    (CompCert4Lean.X86.Asmgen.ireg_of a1)
                    (fun r1 => CompCert4Lean.Common.Errors.bind
                      (CompCert4Lean.X86.Asmgen.ireg_of a2)
                      (fun r2 => .OK (.Pcmpq_rr r1 r2 :: k))) = .OK c at h
                  exact h
              | Ccompf cmp =>
                  apply asmgenproof_bind_freg2_cons a1 a2 k c
                    (fun r1 r2 => CompCert4Lean.X86.Asmgen.floatcomp cmp r1 r2)
                    (by intro r1 r2 lbl; cases cmp <;>
                      simp [CompCert4Lean.X86.Asmgen.floatcomp,
                        CompCert4Lean.X86.Asm.is_label])
                  change CompCert4Lean.Common.Errors.bind
                    (CompCert4Lean.X86.Asmgen.freg_of a1)
                    (fun r1 => CompCert4Lean.Common.Errors.bind
                      (CompCert4Lean.X86.Asmgen.freg_of a2)
                      (fun r2 => .OK (CompCert4Lean.X86.Asmgen.floatcomp cmp r1 r2 :: k))) = .OK c at h
                  exact h
              | Cnotcompf cmp =>
                  apply asmgenproof_bind_freg2_cons a1 a2 k c
                    (fun r1 r2 => CompCert4Lean.X86.Asmgen.floatcomp cmp r1 r2)
                    (by intro r1 r2 lbl; cases cmp <;>
                      simp [CompCert4Lean.X86.Asmgen.floatcomp,
                        CompCert4Lean.X86.Asm.is_label])
                  change CompCert4Lean.Common.Errors.bind
                    (CompCert4Lean.X86.Asmgen.freg_of a1)
                    (fun r1 => CompCert4Lean.Common.Errors.bind
                      (CompCert4Lean.X86.Asmgen.freg_of a2)
                      (fun r2 => .OK (CompCert4Lean.X86.Asmgen.floatcomp cmp r1 r2 :: k))) = .OK c at h
                  exact h
              | Ccompfs cmp =>
                  apply asmgenproof_bind_freg2_cons a1 a2 k c
                    (fun r1 r2 => CompCert4Lean.X86.Asmgen.floatcomp32 cmp r1 r2)
                    (by intro r1 r2 lbl; cases cmp <;>
                      simp [CompCert4Lean.X86.Asmgen.floatcomp32,
                        CompCert4Lean.X86.Asm.is_label])
                  change CompCert4Lean.Common.Errors.bind
                    (CompCert4Lean.X86.Asmgen.freg_of a1)
                    (fun r1 => CompCert4Lean.Common.Errors.bind
                      (CompCert4Lean.X86.Asmgen.freg_of a2)
                      (fun r2 => .OK (CompCert4Lean.X86.Asmgen.floatcomp32 cmp r1 r2 :: k))) = .OK c at h
                  exact h
              | Cnotcompfs cmp =>
                  apply asmgenproof_bind_freg2_cons a1 a2 k c
                    (fun r1 r2 => CompCert4Lean.X86.Asmgen.floatcomp32 cmp r1 r2)
                    (by intro r1 r2 lbl; cases cmp <;>
                      simp [CompCert4Lean.X86.Asmgen.floatcomp32,
                        CompCert4Lean.X86.Asm.is_label])
                  change CompCert4Lean.Common.Errors.bind
                    (CompCert4Lean.X86.Asmgen.freg_of a1)
                    (fun r1 => CompCert4Lean.Common.Errors.bind
                      (CompCert4Lean.X86.Asmgen.freg_of a2)
                      (fun r2 => .OK (CompCert4Lean.X86.Asmgen.floatcomp32 cmp r1 r2 :: k))) = .OK c at h
                  exact h
              | Ccompimm cmp n => simp [CompCert4Lean.X86.Asmgen.transl_cond] at h <;> cases h
              | Ccompuimm cmp n => simp [CompCert4Lean.X86.Asmgen.transl_cond] at h <;> cases h
              | Ccomplimm cmp n => simp [CompCert4Lean.X86.Asmgen.transl_cond] at h <;> cases h
              | Ccompluimm cmp n => simp [CompCert4Lean.X86.Asmgen.transl_cond] at h <;> cases h
              | Cmaskzero n => simp [CompCert4Lean.X86.Asmgen.transl_cond] at h <;> cases h
              | Cmasknotzero n => simp [CompCert4Lean.X86.Asmgen.transl_cond] at h <;> cases h

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

private theorem asmgenproof_tail_nolabel_cons_local (k : AsmCode)
    (i : CompCert4Lean.X86.Asm.instruction)
    (hi : ∀ lbl, CompCert4Lean.X86.Asm.is_label lbl i = false) :
    CompCert4Lean.Backend.Asmgenproof0.tail_nolabel k (i :: k) := by
  constructor
  · exact CompCert4Lean.Lib.Coqlib.is_tail.cons _
      (CompCert4Lean.Lib.Coqlib.is_tail.refl _)
  · intro lbl
    simp [CompCert4Lean.Backend.Asmgenproof0.find_label, hi]

private theorem asmgenproof_bind_cons_local {R : Type}
    (extract : Mreg → CompCert4Lean.Common.Errors.res R)
    (a : Mreg) (k c : AsmCode) (mk : R → CompCert4Lean.X86.Asm.instruction)
    (hi : ∀ r lbl, CompCert4Lean.X86.Asm.is_label lbl (mk r) = false) :
    CompCert4Lean.Common.Errors.bind (extract a)
      (fun r => .OK (mk r :: k)) = .OK c →
      CompCert4Lean.Backend.Asmgenproof0.tail_nolabel k c := by
  intro h
  cases hr : extract a with
  | Error msg =>
      simp [hr, CompCert4Lean.Common.Errors.bind] at h
  | OK r =>
      simp [hr, CompCert4Lean.Common.Errors.bind] at h
      cases h
      exact asmgenproof_tail_nolabel_cons_local k (mk r) (hi r)

theorem transl_load_label : transl_load_labelStatement := by
  intro chunk addr args dest k c h
  unfold CompCert4Lean.X86.Asmgen.transl_load at h
  change CompCert4Lean.Common.Errors.bind
    (CompCert4Lean.X86.Asmgen.transl_addressing addr args) (fun am => _) = .OK c at h
  obtain ⟨am, ham, hrest⟩ := CompCert4Lean.Common.Errors.bind_inversion _ _ _ _ _ h
  cases chunk with
  | Mbool =>
      cases hrest
  | Mint8signed =>
      apply asmgenproof_bind_cons_local CompCert4Lean.X86.Asmgen.ireg_of dest k c
        (fun r => .Pmovsb_rm r am)
        (by intro r lbl; simp [CompCert4Lean.X86.Asm.is_label])
      change CompCert4Lean.Common.Errors.bind
        (CompCert4Lean.X86.Asmgen.ireg_of dest)
        (fun r => .OK (.Pmovsb_rm r am :: k)) = .OK c
      exact hrest
  | Mint8unsigned =>
      apply asmgenproof_bind_cons_local CompCert4Lean.X86.Asmgen.ireg_of dest k c
        (fun r => .Pmovzb_rm r am)
        (by intro r lbl; simp [CompCert4Lean.X86.Asm.is_label])
      change CompCert4Lean.Common.Errors.bind
        (CompCert4Lean.X86.Asmgen.ireg_of dest)
        (fun r => .OK (.Pmovzb_rm r am :: k)) = .OK c
      exact hrest
  | Mint16signed =>
      apply asmgenproof_bind_cons_local CompCert4Lean.X86.Asmgen.ireg_of dest k c
        (fun r => .Pmovsw_rm r am)
        (by intro r lbl; simp [CompCert4Lean.X86.Asm.is_label])
      change CompCert4Lean.Common.Errors.bind
        (CompCert4Lean.X86.Asmgen.ireg_of dest)
        (fun r => .OK (.Pmovsw_rm r am :: k)) = .OK c
      exact hrest
  | Mint16unsigned =>
      apply asmgenproof_bind_cons_local CompCert4Lean.X86.Asmgen.ireg_of dest k c
        (fun r => .Pmovzw_rm r am)
        (by intro r lbl; simp [CompCert4Lean.X86.Asm.is_label])
      change CompCert4Lean.Common.Errors.bind
        (CompCert4Lean.X86.Asmgen.ireg_of dest)
        (fun r => .OK (.Pmovzw_rm r am :: k)) = .OK c
      exact hrest
  | Mint32 =>
      apply asmgenproof_bind_cons_local CompCert4Lean.X86.Asmgen.ireg_of dest k c
        (fun r => .Pmovl_rm r am)
        (by intro r lbl; simp [CompCert4Lean.X86.Asm.is_label])
      change CompCert4Lean.Common.Errors.bind
        (CompCert4Lean.X86.Asmgen.ireg_of dest)
        (fun r => .OK (.Pmovl_rm r am :: k)) = .OK c
      exact hrest
  | Mint64 =>
      apply asmgenproof_bind_cons_local CompCert4Lean.X86.Asmgen.ireg_of dest k c
        (fun r => .Pmovq_rm r am)
        (by intro r lbl; simp [CompCert4Lean.X86.Asm.is_label])
      change CompCert4Lean.Common.Errors.bind
        (CompCert4Lean.X86.Asmgen.ireg_of dest)
        (fun r => .OK (.Pmovq_rm r am :: k)) = .OK c
      exact hrest
  | Mfloat32 =>
      apply asmgenproof_bind_cons_local CompCert4Lean.X86.Asmgen.freg_of dest k c
        (fun r => .Pmovss_fm r am)
        (by intro r lbl; simp [CompCert4Lean.X86.Asm.is_label])
      change CompCert4Lean.Common.Errors.bind
        (CompCert4Lean.X86.Asmgen.freg_of dest)
        (fun r => .OK (.Pmovss_fm r am :: k)) = .OK c
      exact hrest
  | Mfloat64 =>
      apply asmgenproof_bind_cons_local CompCert4Lean.X86.Asmgen.freg_of dest k c
        (fun r => .Pmovsd_fm r am)
        (by intro r lbl; simp [CompCert4Lean.X86.Asm.is_label])
      change CompCert4Lean.Common.Errors.bind
        (CompCert4Lean.X86.Asmgen.freg_of dest)
        (fun r => .OK (.Pmovsd_fm r am :: k)) = .OK c
      exact hrest
  | Many32 =>
      cases hrest
  | Many64 =>
      cases hrest

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

private theorem asmgenproof_mk_storebyte_label_local
    (am : CompCert4Lean.X86.Asm.addrmode) (r : CompCert4Lean.X86.Asm.ireg)
    (k c : AsmCode) :
    CompCert4Lean.X86.Asmgen.mk_storebyte am r k = .OK c →
      CompCert4Lean.Backend.Asmgenproof0.tail_nolabel k c := by
  intro h
  unfold CompCert4Lean.X86.Asmgen.mk_storebyte at h
  simp [CompCert4Lean.X86_64.Archi.ptr64] at h
  cases h
  constructor
  · exact CompCert4Lean.Lib.Coqlib.is_tail.cons _
      (CompCert4Lean.Lib.Coqlib.is_tail.refl _)
  · intro lbl
    simp [CompCert4Lean.Backend.Asmgenproof0.find_label,
      CompCert4Lean.X86.Asm.is_label]

private theorem asmgenproof_bind_mk_storebyte_label_local
    (am : CompCert4Lean.X86.Asm.addrmode) (src : Mreg)
    (k c : AsmCode) :
    CompCert4Lean.Common.Errors.bind
      (CompCert4Lean.X86.Asmgen.ireg_of src)
      (fun r => CompCert4Lean.X86.Asmgen.mk_storebyte am r k) = .OK c →
      CompCert4Lean.Backend.Asmgenproof0.tail_nolabel k c := by
  intro h
  cases hr : CompCert4Lean.X86.Asmgen.ireg_of src with
  | Error msg =>
      simp [hr, CompCert4Lean.Common.Errors.bind] at h
  | OK r =>
      simp [hr, CompCert4Lean.Common.Errors.bind] at h
      exact asmgenproof_mk_storebyte_label_local am r k c h

theorem transl_store_label : transl_store_labelStatement := by
  intro chunk addr args src k c h
  unfold CompCert4Lean.X86.Asmgen.transl_store at h
  change CompCert4Lean.Common.Errors.bind
    (CompCert4Lean.X86.Asmgen.transl_addressing addr args) (fun am => _) = .OK c at h
  obtain ⟨am, ham, hrest⟩ := CompCert4Lean.Common.Errors.bind_inversion _ _ _ _ _ h
  cases chunk with
  | Mbool => cases hrest
  | Mint8unsigned => exact asmgenproof_bind_mk_storebyte_label_local am src k c hrest
  | Mint8signed => cases hrest
  | Mint16unsigned =>
      apply asmgenproof_bind_cons_local CompCert4Lean.X86.Asmgen.ireg_of src k c
        (fun r => .Pmovw_mr am r)
        (by intro r lbl; simp [CompCert4Lean.X86.Asm.is_label])
      exact hrest
  | Mint16signed => cases hrest
  | Mint32 =>
      apply asmgenproof_bind_cons_local CompCert4Lean.X86.Asmgen.ireg_of src k c
        (fun r => .Pmovl_mr am r)
        (by intro r lbl; simp [CompCert4Lean.X86.Asm.is_label])
      exact hrest
  | Mint64 =>
      apply asmgenproof_bind_cons_local CompCert4Lean.X86.Asmgen.ireg_of src k c
        (fun r => .Pmovq_mr am r)
        (by intro r lbl; simp [CompCert4Lean.X86.Asm.is_label])
      exact hrest
  | Mfloat32 =>
      apply asmgenproof_bind_cons_local CompCert4Lean.X86.Asmgen.freg_of src k c
        (fun r => .Pmovss_mf am r)
        (by intro r lbl; simp [CompCert4Lean.X86.Asm.is_label])
      exact hrest
  | Mfloat64 =>
      apply asmgenproof_bind_cons_local CompCert4Lean.X86.Asmgen.freg_of src k c
        (fun r => .Pmovsd_mf am r)
        (by intro r lbl; simp [CompCert4Lean.X86.Asm.is_label])
      exact hrest
  | Many32 => cases hrest
  | Many64 => cases hrest

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

private theorem asmgenproof_exec_straight_exec_local
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    exec_straight_execStatement := by
  intro cfg xi prog tprog hmatch
  intro fb f c ep tf tc c' rs m rs' m' hatpc hexec
  generalize hpc : rs .PC = pc at hatpc
  cases hatpc with
  | intro fb ofs f c ep tf tc hfind htrans hcode htail =>
      apply CompCert4Lean.Backend.Asmgenproof0.exec_straight_steps_1
        (cfg := cfg) (xi := xi)
        (ge := CompCert4Lean.Common.Globalenvs.Genv.globalenv tprog)
        (fn := tf) (c := tc) (rs := rs) (m := m)
        (c' := c') (rs' := rs') (m' := m')
        (b := fb) (ofs := ofs) hexec
      · exact transf_function_no_overflow f tf htrans
      · exact hpc
      · exact functions_transl prog tprog hmatch fb f tf hfind htrans
      · exact htail

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

private theorem asmgenproof_exec_straight_at_local
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    exec_straight_atStatement := by
  intro prog tprog hmatch
  intro fb f c ep tf tc c' ep' tc' rs m rs' m' hatpc hcode' hexec
  generalize hpc : rs .PC = pc at hatpc
  cases hatpc with
  | intro fb ofs f c ep tf tc hfind htrans hcode htail =>
      have hfind' :
          CompCert4Lean.Common.Globalenvs.Genv.find_funct_ptr
              (CompCert4Lean.Common.Globalenvs.Genv.globalenv tprog) fb =
            some (.Internal tf) :=
        functions_transl prog tprog hmatch fb f tf hfind htrans
      obtain ⟨ofs', hpc', htail'⟩ :=
        CompCert4Lean.Backend.Asmgenproof0.exec_straight_steps_2
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (ge := CompCert4Lean.Common.Globalenvs.Genv.globalenv tprog)
          (fn := tf) (c := tc) (rs := rs) (m := m)
          (c' := tc') (rs' := rs') (m' := m')
          (b := fb) (ofs := ofs) hexec
          (transf_function_no_overflow f tf htrans)
          hpc hfind' htail
      rw [hpc']
      exact CompCert4Lean.Backend.Asmgenproof0.transl_code_at_pc.intro
        fb ofs' f c' ep' tf tc' hfind htrans hcode' htail'

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

theorem exec_straight_steps
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    exec_straight_stepsStatement := by
  intro cfg xi prog tprog hmatch
  intro s fb f rs1 i ctail ep tf tc m1' m2 m2' sp ms2
  intro hstack hext hfind hatpc hstep
  generalize hpc : rs1 .PC = pc at hatpc
  cases hatpc with
  | intro fb ofs f _ ep tf tc hfind0 htrans hcode htail =>
      have hcode_full := hcode
      change CompCert4Lean.Common.Errors.bind
          (CompCert4Lean.X86.Asmgen.transl_code f ctail
            (CompCert4Lean.X86.Asmgen.it1_is_parent ep i))
          (fun k => CompCert4Lean.X86.Asmgen.transl_instr f i ep k) =
        .OK tc at hcode
      obtain ⟨k, htailcode, htrans_instr⟩ :=
        CompCert4Lean.Common.Errors.bind_inversion _ _ _ _ _ hcode
      obtain ⟨rs2, hexec_straight, hagree, hparent⟩ :=
        hstep k tc htrans_instr
      have hatpc0 :
          CompCert4Lean.Backend.Asmgenproof0.transl_code_at_pc
            (CompCert4Lean.Common.Globalenvs.Genv.globalenv prog)
            (rs1 .PC) fb f (i :: ctail) ep tf tc := by
        rw [hpc]
        exact CompCert4Lean.Backend.Asmgenproof0.transl_code_at_pc.intro
          fb ofs f (i :: ctail) ep tf tc hfind0 htrans hcode_full htail
      have hplus :=
        asmgenproof_exec_straight_exec_local
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          cfg xi prog tprog hmatch fb f (i :: ctail) ep tf tc k rs1 m1' rs2 m2'
          hatpc0 hexec_straight
      have hatpc_tail :=
        asmgenproof_exec_straight_at_local
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          prog tprog hmatch fb f (i :: ctail) ep tf tc ctail
          (CompCert4Lean.X86.Asmgen.it1_is_parent ep i) k rs1 m1' rs2 m2'
          hatpc0 htailcode hexec_straight
      refine ⟨.State rs2 m2', hplus, ?_⟩
      apply match_states.match_states_intro
      · exact hstack
      · exact hfind0
      · exact hext
      · exact hatpc_tail
      · exact hagree
      · exact hparent

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open Lean Elab Tactic Meta

private def asmgenproofPrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem asmgenproof_wordcore_add_val {bits : Nat}
    (x y : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    (CompCert4Lean.Lib.Integers.WordCore.add x y).val =
      (x.val + y.val) % (2 ^ bits) := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let yF := (lctx.findFromUserName? `y).get!
    let e ← mkAppM
      (asmgenproofPrivateName "CompCert4Lean.Lib.Integers.WordCore.add_val")
      #[mkFVar xF.fvarId, mkFVar yF.fvarId]
    closeMainGoal Name.anonymous e

private theorem asmgenproof_wordcore_zero_val (bits : Nat) :
    (CompCert4Lean.Lib.Integers.WordCore.zero bits).val = 0 := by
  unfold CompCert4Lean.Lib.Integers.WordCore.zero
  run_tac
    let lctx ← getLCtx
    let bF := (lctx.findFromUserName? `bits).get!
    let e ← mkAppM
      (asmgenproofPrivateName "CompCert4Lean.Lib.Integers.WordCore.val_repr_residue")
      #[mkFVar bF.fvarId,
        mkConst ``CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0]
    closeMainGoal Name.anonymous e

private theorem asmgenproof_wordcore_val_lt {bits : Nat}
    (x : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    x.val < 2 ^ bits := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let e ← mkAppM
      (asmgenproofPrivateName "CompCert4Lean.Lib.Integers.WordCore.val_lt")
      #[mkFVar xF.fvarId]
    closeMainGoal Name.anonymous e

private theorem asmgenproof_ptrofs_add_zero
    (x : CompCert4Lean.Lib.Integers.Ptrofs.int) :
    CompCert4Lean.Lib.Integers.Ptrofs.add x
        CompCert4Lean.Lib.Integers.Ptrofs.zero = x := by
  change CompCert4Lean.Lib.Integers.WordCore.add x
    (CompCert4Lean.Lib.Integers.WordCore.zero
      CompCert4Lean.Lib.Integers.Ptrofs.wordsize) = x
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [asmgenproof_wordcore_add_val, asmgenproof_wordcore_zero_val, Nat.add_zero]
  exact Nat.mod_eq_of_lt (asmgenproof_wordcore_val_lt x)

private theorem asmgenproof_initial_store_init_data
    {prog : MachProgram} {tprog : AsmProgram}
    (hsymb : ∀ id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id)
    (m : Mem) (b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
    (p : Z) (i : init_data) :
    Genv.store_init_data (Genv.globalenv prog) m b p i =
      Genv.store_init_data (Genv.globalenv tprog) m b p i := by
  cases i with
  | Init_addrof symb ofs =>
      simp [Genv.store_init_data, hsymb symb]
  | _ => rfl

private theorem asmgenproof_initial_store_init_data_list
    {prog : MachProgram} {tprog : AsmProgram}
    (hsymb : ∀ id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id) :
    ∀ (m : Mem) (b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
      (p : Z) (il : List init_data),
      Genv.store_init_data_list (Genv.globalenv prog) m b p il =
        Genv.store_init_data_list (Genv.globalenv tprog) m b p il := by
  intro m b p il
  induction il generalizing m b p with
  | nil => rfl
  | cons i rest ih =>
      simp only [Genv.store_init_data_list]
      rw [asmgenproof_initial_store_init_data hsymb]
      cases h : Genv.store_init_data (Genv.globalenv tprog) m b p i with
      | none => simp [h]
      | some m' =>
          simp only [h]
          exact ih m' b (ZArith.BinInt.Z.add p (init_data_size i))

private theorem asmgenproof_initial_alloc_global
    [Linker MachProgram]
    {prog : MachProgram} {tprog : AsmProgram}
    (hsymb : ∀ id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id)
    {id : ident} {gd : globdef MachFundef Unit}
    {tg : globdef AsmFundef Unit}
    (hgd : match_globdef
      (fun _ f tf =>
        CompCert4Lean.X86.Asmgen.transf_fundef f = .OK tf)
      (fun x y : Unit => x = y) prog gd tg)
    (m : Mem) :
    Genv.alloc_global (Genv.globalenv prog) m (id, gd) =
      Genv.alloc_global (Genv.globalenv tprog) m (id, tg) := by
  cases hgd with
  | match_globdef_fun ctx' f1 f2 horder htrans => rfl
  | match_globdef_var v1 v2 hvar =>
      cases hvar with
      | match_globvar_intro info1 info2 init ro vol hinfo =>
          cases hinfo
          simp only [Genv.alloc_global]
          simp [asmgenproof_initial_store_init_data_list (prog := prog) (tprog := tprog) hsymb]

private theorem asmgenproof_val_inject_refl (v : Val) :
    CompCert4Lean.Common.Values.Val.inject
      CompCert4Lean.Common.Values.inject_id v v := by
  cases v with
  | Vint i => exact CompCert4Lean.Common.Values.Val.inject.inject_int _
  | Vlong i => exact CompCert4Lean.Common.Values.Val.inject.inject_long _
  | Vfloat f => exact CompCert4Lean.Common.Values.Val.inject.inject_float _
  | Vsingle f => exact CompCert4Lean.Common.Values.Val.inject.inject_single _
  | Vptr b ofs =>
      apply CompCert4Lean.Common.Values.Val.inject.inject_ptr
      · rfl
      · exact (asmgenproof_ptrofs_add_zero ofs).symm
  | Vundef => exact CompCert4Lean.Common.Values.Val.inject.val_inject_undef _

private theorem asmgenproof_initial_alloc_globals
    [Linker MachProgram]
    {prog : MachProgram} {tprog : AsmProgram}
    (hsymb : ∀ id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id)
    (gl : List (ident × globdef MachFundef Unit))
    (tgl : List (ident × globdef AsmFundef Unit))
    (hlist : list_forall2
      (match_ident_globdef
        (fun _ f tf =>
          CompCert4Lean.X86.Asmgen.transf_fundef f = .OK tf)
        (fun x y : Unit => x = y) prog) gl tgl) :
    ∀ (m m' : Mem),
      Genv.alloc_globals (Genv.globalenv prog) m gl = some m' →
        Genv.alloc_globals (Genv.globalenv tprog) m tgl = some m' := by
  induction hlist with
  | nil =>
      intro m m' h
      simpa [Genv.alloc_globals] using h
  | cons hd thd hhd htl ih =>
      intro m m' h
      rcases hhd with ⟨hid, hgd⟩
      rcases hd with ⟨id, gd⟩
      rcases thd with ⟨tid, tgd⟩
      have halloc :
          Genv.alloc_global (Genv.globalenv prog) m (id, gd) =
            Genv.alloc_global (Genv.globalenv tprog) m (tid, tgd) := by
        change id = tid at hid
        subst tid
        exact asmgenproof_initial_alloc_global hsymb hgd m
      simp only [Genv.alloc_globals] at h ⊢
      rw [halloc] at h
      cases ha : Genv.alloc_global (Genv.globalenv tprog) m (tid, tgd) with
      | none => simp [ha] at h
      | some m1 =>
          simp only [ha] at h ⊢
          exact ih m1 m' h

private theorem asmgenproof_mem_extends_refl (m : Mem) :
    CompCert4Lean.Common.Memory.Mem.extends m m := by
  refine ⟨rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro b1 b2 delta ofs k p hmap hp
      have hpair : (b1, (.Z0 : Z)) = (b2, delta) := by
        simpa [CompCert4Lean.Common.Values.inject_id] using Option.some.inj hmap
      cases hpair
      change Mem.perm m b1 (ZArith.BinInt.Z.add ofs (.Z0 : Z)) k p
      have hzadd : ZArith.BinInt.Z.add ofs (.Z0 : Z) = ofs := by
        apply intOfZ_injective
        change intOfZ (zOfInt (intOfZ ofs + 0)) = intOfZ ofs
        rw [intOfZ_zOfInt]
        simp
      rw [hzadd]
      exact hp
    · intro b1 b2 delta chunk ofs p hmap hp
      have hpair : (b1, (.Z0 : Z)) = (b2, delta) := by
        simpa [CompCert4Lean.Common.Values.inject_id] using Option.some.inj hmap
      cases hpair
      refine ⟨.Z0, ?_⟩
      apply intOfZ_injective
      change 0 = intOfZ (ZArith.BinInt.Z.mul
        (CompCert4Lean.Common.Memdata.align_chunk chunk) (.Z0 : Z))
      change 0 = intOfZ (zOfInt (intOfZ
        (CompCert4Lean.Common.Memdata.align_chunk chunk) * 0))
      rw [intOfZ_zOfInt]
      simp
    · intro b1 ofs b2 delta hmap hp
      have hpair : (b1, (.Z0 : Z)) = (b2, delta) := by
        simpa [CompCert4Lean.Common.Values.inject_id] using Option.some.inj hmap
      cases hpair
      change CompCert4Lean.Common.Memdata.memval_inject inject_id
        (CompCert4Lean.Lib.Maps.ZMap.get ofs (CompCert4Lean.Lib.Maps.PMap.get b1 m.mem_contents))
        (CompCert4Lean.Lib.Maps.ZMap.get
          (ZArith.BinInt.Z.add ofs (.Z0 : Z))
          (CompCert4Lean.Lib.Maps.PMap.get b1 m.mem_contents))
      have hzadd : ZArith.BinInt.Z.add ofs (.Z0 : Z) = ofs := by
        apply intOfZ_injective
        change intOfZ (zOfInt (intOfZ ofs + 0)) = intOfZ ofs
        rw [intOfZ_zOfInt]
        simp
      rw [hzadd]
      cases hmv : CompCert4Lean.Lib.Maps.ZMap.get ofs
          (CompCert4Lean.Lib.Maps.PMap.get b1 m.mem_contents) with
      | Byte n => exact CompCert4Lean.Common.Memdata.memval_inject.byte _ _
      | Fragment v q n =>
          exact CompCert4Lean.Common.Memdata.memval_inject.fragment _ _ _ _ _
            (asmgenproof_val_inject_refl v)
      | Undef => exact CompCert4Lean.Common.Memdata.memval_inject.undef _ _
  · intro b ofs k p hp
    exact Or.inl hp

theorem transf_initial_states : transf_initial_statesStatement := by
  letI : Linker MachFundef := Linker_fundef MachFunction
  letI : Linker Unit := Linker_unit
  letI : Linker MachProgram := Linker_prog MachFundef Unit
  intro prog tprog hmatch st1 hinit
  have hmatch' := hmatch
  unfold match_prog at hmatch'
  cases hinit with
  | initial_state_intro fb m0 hmem hsymb =>
      let hsymb' : ∀ id,
          Genv.find_symbol (Genv.globalenv tprog) id =
            Genv.find_symbol (Genv.globalenv prog) id :=
        fun id => symbols_preserved prog tprog hmatch id
      refine ⟨.State (CompCert4Lean.X86.Asm.initial_regset tprog) m0, ?_, ?_⟩
      · apply CompCert4Lean.X86.Asm.initial_state.initial_state_intro m0
        unfold Genv.init_mem at hmem ⊢
        apply asmgenproof_initial_alloc_globals hsymb' prog.prog_defs tprog.prog_defs hmatch'.1
        exact hmem
      · apply match_states.match_states_call
        · exact CompCert4Lean.Backend.Asmgenproof0.match_stack_nil
        · exact asmgenproof_mem_extends_refl m0
        · constructor
          · simpa [CompCert4Lean.X86.Asm.initial_regset,
              CompCert4Lean.X86.Asm.Pregmap.set,
              CompCert4Lean.Backend.Mach.parent_sp,
              CompCert4Lean.X86.Asm.SP]
          · intro h
            cases hptr : CompCert4Lean.X86_64.Archi.ptr64 <;>
              simp [CompCert4Lean.Backend.Mach.parent_sp,
                CompCert4Lean.Common.Values.Vnullptr, hptr] at h
          · intro r
            exact Val.lessdef_undef _
        · change (CompCert4Lean.X86.Asm.initial_regset tprog) .PC =
            .Vptr fb CompCert4Lean.Lib.Integers.Ptrofs.zero
          simp [CompCert4Lean.X86.Asm.initial_regset,
            CompCert4Lean.X86.Asm.Pregmap.set,
            Genv.symbol_address, hmatch'.2.1,
            hsymb' prog.prog_main, hsymb]
        · simp [CompCert4Lean.X86.Asm.initial_regset,
            CompCert4Lean.X86.Asm.Pregmap.set,
            CompCert4Lean.Backend.Mach.parent_ra,
            CompCert4Lean.Common.Values.Vnullptr]

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

theorem transf_final_states : transf_final_statesStatement := by
  intro prog st1 st2 r hmatch hfinal
  cases hfinal with
  | final_state_intro rs m r0 retcode hresult hval =>
      cases hmatch with
      | match_states_return s ms m0 m1 rs' hstack hmem hagree hatpc =>
          apply CompCert4Lean.X86.Asm.final_state.final_state_intro
          · change rs' .PC = CompCert4Lean.Common.Values.Vnullptr
            simpa [CompCert4Lean.Backend.Mach.parent_ra] using hatpc
          · have hr0 : (.AX : CompCert4Lean.X86.Machregs.mreg) = r0 := by
              simpa [CompCert4Lean.X86.Conventions1.loc_result,
                CompCert4Lean.X86.Conventions1.loc_result_64,
                CompCert4Lean.X86.Conventions1.loc_result_32,
                CompCert4Lean.Common.AST.signature_main,
                CompCert4Lean.Common.AST.proj_sig_res,
                CompCert4Lean.Common.AST.proj_xtype,
                CompCert4Lean.X86_64.Archi.ptr64] using hresult
            subst r0
            have hld :=
              CompCert4Lean.Backend.Asmgenproof0.preg_val
                rs (CompCert4Lean.Backend.Mach.parent_sp []) rs' .AX hagree
            have hld' :
                CompCert4Lean.Common.Values.Val.lessdef
                  (rs .AX) (rs' (.IR .RAX)) := by
              simpa [CompCert4Lean.X86.Asm.preg_of] using hld
            have hld'' :
                CompCert4Lean.Common.Values.Val.lessdef
                  (.Vint r) (rs' (.IR .RAX)) := by
              simpa [hval] using hld'
            have htarget :
                ∀ v : CompCert4Lean.Common.Values.val,
                  CompCert4Lean.Common.Values.Val.lessdef (.Vint r) v →
                    v = .Vint r := by
              intro v h
              cases h with
              | lessdef_refl v => rfl
            exact htarget _ hld''

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

theorem exec_straight_exec
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    exec_straight_execStatement := by
  exact asmgenproof_exec_straight_exec_local

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

theorem exec_straight_at
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    exec_straight_atStatement := by
  exact asmgenproof_exec_straight_at_local

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

theorem mk_setcc_base_label : mk_setcc_base_labelStatement := by
  intro xc rd k
  exact asmgenproof_mk_setcc_base_label xc rd k

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

open CompCert4Lean.Backend.Asmgenproof0
open CompCert4Lean.Common.Errors
open CompCert4Lean.X86.Asmgen

private theorem asmgenproof_op_tail_refl (k : AsmCode) : tail_nolabel k k :=
  ⟨CompCert4Lean.Lib.Coqlib.is_tail.refl _, fun _ => rfl⟩

private theorem asmgenproof_op_tail_cons {k c : AsmCode}
    {i : CompCert4Lean.X86.Asm.instruction}
    (hi : ∀ lbl, CompCert4Lean.X86.Asm.is_label lbl i = false)
    (hc : tail_nolabel k c) : tail_nolabel k (i :: c) := by
  constructor
  · exact CompCert4Lean.Lib.Coqlib.is_tail.cons i hc.1
  · intro lbl
    simp only [find_label, hi, Bool.false_eq_true, if_false]
    exact hc.2 lbl

private theorem asmgenproof_op_bind {α : Type} {x : res α}
    {f : α → res AsmCode} {k c : AsmCode}
    (h : CompCert4Lean.Common.Errors.bind x f = .OK c)
    (hf : ∀ a, f a = .OK c → tail_nolabel k c) : tail_nolabel k c := by
  cases x with
  | Error msg => cases h
  | OK a => exact hf a h

private theorem asmgenproof_op_assert {x y : Mreg} {r : res AsmCode}
    {k c : AsmCode}
    (h : (match CompCert4Lean.Backend.Mach.RegEq.eq x y with
      | .left _ => r
      | .right _ => assertion_failed) = .OK c)
    (hr : r = .OK c → tail_nolabel k c) : tail_nolabel k c := by
  cases heq : CompCert4Lean.Backend.Mach.RegEq.eq x y with
  | left _ =>
      rw [heq] at h
      exact hr h
  | right _ =>
      rw [heq] at h
      cases h

private theorem asmgenproof_op_ok {k c c' : AsmCode}
    (h : (res.OK c' : res AsmCode) = .OK c)
    (hc : tail_nolabel k c') : tail_nolabel k c := by
  cases h
  exact hc

private theorem asmgenproof_op_cond {cond : Condition} {args : List Mreg}
    {k k' c : AsmCode} (h : transl_cond cond args k' = .OK c)
    (hk : tail_nolabel k k') : tail_nolabel k c :=
  tail_nolabel_trans k k' c (transl_cond_label cond args k' c h) hk

private theorem asmgenproof_op_sel {cond : Condition} {args : List Mreg}
    {rd r2 : Ireg} {k c : AsmCode}
    (h : transl_sel cond args rd r2 k = .OK c) : tail_nolabel k c := by
  unfold transl_sel at h
  split at h
  · apply asmgenproof_op_ok h
    exact asmgenproof_tail_nolabel_cons_local k _ (by intro lbl; rfl)
  · change CompCert4Lean.Common.Errors.bind
      (mk_sel (testcond_for_condition cond) rd r2 k)
      (fun k' => transl_cond cond args k') = .OK c at h
    obtain ⟨k', hk', h'⟩ := bind_inversion _ _ _ _ _ h
    exact tail_nolabel_trans k k' c
      (transl_cond_label cond args k' c h')
      (mk_sel_label _ rd r2 k k' hk')

set_option maxHeartbeats 8000000 in
theorem transl_op_label : transl_op_labelStatement := by
  intro op args dst k c h
  cases op
  all_goals rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, rest⟩⟩⟩
  all_goals delta transl_op at h
  all_goals dsimp only at h
  all_goals
    repeat first
      | exact asmgenproof_op_tail_refl _
      | exact mk_setcc_label _ _ _
      | (with_reducible exact asmgenproof_op_sel h)
      | (with_reducible apply asmgenproof_op_cond h; clear h)
      | (apply asmgenproof_op_ok h; clear h)
      | (apply asmgenproof_op_bind h; clear h; intro a h)
      | (apply asmgenproof_op_assert h; clear h; intro h)
      | (refine asmgenproof_op_tail_cons (by intro lbl; rfl) ?_)
      | apply asmgenproof_tail_nolabel_if
      | contradiction
      | unfold mk_mov at h
      | unfold mk_shrximm at h
      | unfold mk_shrxlimm at h
      | unfold mk_intconv at h
      | split at h
      | split

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

open CompCert4Lean.Backend.Asmgenproof0
open CompCert4Lean.Common.Errors
open CompCert4Lean.X86.Asmgen

theorem transl_instr_label : transl_instr_labelStatement := by
  intro f i ep k c h
  cases i with
  | Mgetstack ofs ty dst =>
      exact loadind_label _ _ _ _ _ _ h
  | Msetstack src ofs ty =>
      exact storeind_label _ _ _ _ _ _ h
  | Mgetparam ofs ty dst =>
      cases ep with
      | false =>
          change CompCert4Lean.Common.Errors.bind (loadind .RAX ofs ty dst k)
            (fun k1 => loadind .RSP f.fn_link_ofs
              CompCert4Lean.Common.AST.Tptr .AX k1) = .OK c at h
          obtain ⟨k1, h1, h2⟩ := bind_inversion _ _ _ _ _ h
          exact tail_nolabel_trans k k1 c
            (loadind_label _ _ _ _ _ _ h2) (loadind_label _ _ _ _ _ _ h1)
      | true => exact loadind_label _ _ _ _ _ _ h
  | Mop op args dst =>
      exact transl_op_label _ _ _ _ _ h
  | Mload chunk addr args dst =>
      exact transl_load_label _ _ _ _ _ _ h
  | Mstore chunk addr args src =>
      exact transl_store_label _ _ _ _ _ _ h
  | Mlabel lbl =>
      exact (res.OK.inj h).symm
  | Mcond cond args lbl =>
      exact tail_nolabel_trans k _ c
        (transl_cond_label _ _ _ _ h) (mk_jcc_label _ _ _)
  | Mcall sg callee =>
      cases callee <;> dsimp only [transl_instr] at h
      all_goals
        repeat first
          | exact asmgenproof_op_tail_refl _
          | (apply asmgenproof_op_ok h; clear h)
          | (apply asmgenproof_op_bind h; clear h; intro a h)
          | (refine asmgenproof_op_tail_cons (by intro lbl; rfl) ?_)
  | Mtailcall sg callee =>
      cases callee <;> dsimp only [transl_instr] at h
      all_goals
        repeat first
          | exact asmgenproof_op_tail_refl _
          | (apply asmgenproof_op_ok h; clear h)
          | (apply asmgenproof_op_bind h; clear h; intro a h)
          | (refine asmgenproof_op_tail_cons (by intro lbl; rfl) ?_)
  | Mgoto lbl | Mjumptable arg tbl | Mreturn | Mbuiltin ef args result =>
      dsimp only [transl_instr] at h
      all_goals
        repeat first
          | exact asmgenproof_op_tail_refl _
          | (apply asmgenproof_op_ok h; clear h)
          | (apply asmgenproof_op_bind h; clear h; intro a h)
          | (refine asmgenproof_op_tail_cons (by intro lbl; rfl) ?_)

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

theorem transl_instr_label' : transl_instr_label'Statement := by
  intro lbl f i ep k c h
  have hlabel := transl_instr_label f i ep k c h
  cases i with
  | Mlabel lbl' =>
      subst c
      simp only [CompCert4Lean.Backend.Asmgenproof0.find_label]
      cases hpeq : CompCert4Lean.Lib.Coqlib.peq lbl lbl' with
      | left heq =>
          simp only [CompCert4Lean.X86.Asm.is_label,
            CompCert4Lean.Backend.Mach.is_label, hpeq]
          rfl
      | right hne =>
          simp only [CompCert4Lean.X86.Asm.is_label,
            CompCert4Lean.Backend.Mach.is_label, hpeq]
          rfl
  | Mgetstack ofs ty dst
  | Msetstack src ofs ty
  | Mgetparam ofs ty dst
  | Mop op args dst
  | Mload chunk addr args dst
  | Mstore chunk addr args src
  | Mcall sg callee
  | Mtailcall sg callee
  | Mgoto lbl'
  | Mcond cond args lbl'
  | Mjumptable arg tbl
  | Mreturn
  | Mbuiltin ef args result =>
      exact hlabel.2 lbl

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

open CompCert4Lean.Backend.Asmgenproof0
open CompCert4Lean.Common.Errors
open CompCert4Lean.X86.Asmgen

set_option maxHeartbeats 8000000 in
theorem transl_code_label : transl_code_labelStatement := by
  intro lbl f c ep tc h
  induction c generalizing ep tc with
  | nil =>
      simp only [CompCert4Lean.X86.Asmgen.transl_code] at h
      cases h
      rfl
  | cons i c ih =>
      change CompCert4Lean.Common.Errors.bind
          (CompCert4Lean.X86.Asmgen.transl_code f c
            (CompCert4Lean.X86.Asmgen.it1_is_parent ep i))
          (fun k => CompCert4Lean.X86.Asmgen.transl_instr f i ep k) = .OK tc at h
      obtain ⟨k, hc, hi⟩ := CompCert4Lean.Common.Errors.bind_inversion _ _ _ _ _ h
      have hil := transl_instr_label' lbl f i ep k tc hi
      have hmach := CompCert4Lean.Backend.Mach.is_label_correct_proof lbl i
      cases hfind : CompCert4Lean.Backend.Mach.is_label lbl i with
      | true =>
          have heqi : i = .Mlabel lbl := by
            have := hmach
            rw [hfind] at this
            exact this
          subst i
          simp only [CompCert4Lean.Backend.Mach.find_label, hfind]
          change CompCert4Lean.X86.Asmgen.transl_code f c false = .OK k at hc
          exact ⟨k, (by simpa [hfind] using hil), hc⟩
      | false =>
          have heqi : i ≠ .Mlabel lbl := by
            have := hmach
            rw [hfind] at this
            exact this
          have hil' : CompCert4Lean.Backend.Asmgenproof0.find_label lbl tc =
              CompCert4Lean.Backend.Asmgenproof0.find_label lbl k := by
            simpa [hfind] using hil
          have hih := ih (CompCert4Lean.X86.Asmgen.it1_is_parent ep i) k hc
          simpa [CompCert4Lean.Backend.Mach.find_label, hfind, hil'] using hih

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

open CompCert4Lean.Backend.Asmgenproof0
open CompCert4Lean.Common.Errors
open CompCert4Lean.X86.Asmgen

theorem transl_find_label : transl_find_labelStatement := by
  intro lbl f tf h
  unfold CompCert4Lean.X86.Asmgen.transf_function at h
  obtain ⟨tf0, ht, hs⟩ := bind_inversion _ _ _ _ _ h
  cases hz : CompCert4Lean.Lib.Coqlib.zlt
      CompCert4Lean.Lib.Integers.Ptrofs.max_unsigned
      (CompCert4Lean.Lib.Coqlib.list_length_z tf0.fn_code) with
  | left hlt =>
      rw [hz] at hs
      cases hs
  | right hge =>
      rw [hz] at hs
      cases hs
      unfold CompCert4Lean.X86.Asmgen.transl_function at ht
      obtain ⟨c, hc, he⟩ := bind_inversion _ _ _ _ _ ht
      cases he
      rw [transl_code'_transl_code] at hc
      exact transl_code_label lbl f f.fn_code true c hc

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Asmgenproof0
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
open Lean Elab Tactic Meta

private theorem asmgenproof_ptrofs_unsigned_repr_local (z : Z)
    (hz : ZArith.BinInt.Z.le Z0 z ∧
      ZArith.BinInt.Z.le z Ptrofs.max_unsigned) :
    Ptrofs.unsigned (Ptrofs.repr z) = z := by
  have hzi : z = zOfInt (intOfZ z) := (zOfInt_intOfZ z).symm
  rw [hzi]
  change (CompCert4Lean.Lib.Integers.WordCore.repr Ptrofs.wordsize
      (zOfInt (intOfZ z))).intval = zOfInt (intOfZ z)
  let w := CompCert4Lean.Lib.Integers.WordCore.repr Ptrofs.wordsize
      (zOfInt (intOfZ z))
  have hi : w.val = Int.toNat
      (intOfZ z % ((2 ^ Ptrofs.wordsize : Nat) : Int)) := by
    dsimp [w]
    run_tac
      let env ← getEnv
      let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith "WordCore.val_repr")
        | throwError "frozen WordCore.val_repr helper not found"
      let stx := Lean.mkIdent n
      let arg := Lean.mkIdent `z
      evalTactic
        (← `(tactic| exact $stx Ptrofs.wordsize
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ $arg)))
  have hwi : w.intval = ZArith.BinInt.Z.of_nat w.val := by
    run_tac
      let env ← getEnv
      let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith
            "WordCore.intval_eq_zOfNat_val")
        | throwError "frozen WordCore.intval_eq_zOfNat_val helper not found"
      let stx := Lean.mkIdent n
      let arg := Lean.mkIdent `w
      evalTactic (← `(tactic| exact $stx $arg))
  change w.intval = _
  rw [hwi, hi]
  have hznonneg : 0 ≤ intOfZ z := hz.1
  have hzmax := hz.2
  have hm : intOfZ Ptrofs.max_unsigned =
      (2 ^ Ptrofs.wordsize : Int) - 1 := by rfl
  have hzlt : intOfZ z < ((2 ^ Ptrofs.wordsize : Nat) : Int) := by
    change intOfZ z ≤ intOfZ Ptrofs.max_unsigned at hzmax
    rw [hm] at hzmax
    have hpcast : ((2 ^ Ptrofs.wordsize : Nat) : Int) =
        (2 : Int) ^ Ptrofs.wordsize := by
      exact (Int.natCast_pow 2 Ptrofs.wordsize).symm
    rw [hpcast]
    omega
  rw [Int.emod_eq_of_lt hznonneg hzlt]
  change zOfInt (↑(Int.toNat (intOfZ z)) : Int) = _
  rw [Int.toNat_of_nonneg hznonneg]

theorem find_label_goto_label : find_label_goto_labelStatement := by
  intro prog f tf lbl rs m c' b ofs hfind htrans hpc hlabel
  have htl := transl_find_label lbl f tf htrans
  rw [hlabel] at htl
  rcases htl with ⟨tc, htcfind, htc⟩
  obtain ⟨pos', hpos, htail, hlt, hle⟩ :=
    label_pos_code_tail lbl tf.fn_code Z0 tc htcfind
  refine ⟨tc, CompCert4Lean.X86.Asm.Pregmap.set
    (.PC) (.Vptr b (Ptrofs.repr pos')) rs, ?_, ?_, ?_⟩
  · unfold CompCert4Lean.X86.Asm.goto_label
    rw [hpos]
    change (match rs PC with
      | .Vptr b a => CompCert4Lean.X86.Asm.outcome.Next
          (CompCert4Lean.X86.Asm.Pregmap.set PC
            (.Vptr b (Ptrofs.repr pos')) rs) m
      | _ => CompCert4Lean.X86.Asm.outcome.Stuck) = _
    rw [hpc]
  · change transl_code_at_pc (Genv.globalenv prog)
      (CompCert4Lean.X86.Asm.Pregmap.set PC (.Vptr b (Ptrofs.repr pos')) rs PC)
      b f c' false tf tc
    change transl_code_at_pc (Genv.globalenv prog)
      (.Vptr b (Ptrofs.repr pos')) b f c' false tf tc
    refine CompCert4Lean.Backend.Asmgenproof0.transl_code_at_pc.intro
      b (Ptrofs.repr pos') f c' false tf tc hfind htrans htc ?_
    have hpos_nonneg : ZArith.BinInt.Z.le Z0 pos' := by
      have hh := hlt
      change (0 : Int) < intOfZ pos' at hh
      change (0 : Int) ≤ intOfZ pos'
      omega
    have hlen := transf_function_no_overflow f tf htrans
    have hpos_max : ZArith.BinInt.Z.le pos' Ptrofs.max_unsigned := by
      have hadd : ZArith.BinInt.Z.add Z0 (list_length_z tf.fn_code) =
          list_length_z tf.fn_code := by
        apply intOfZ_injective
        simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
        rw [show intOfZ Z0 = 0 by rfl, Int.zero_add]
      have hle' : ZArith.BinInt.Z.le pos' (list_length_z tf.fn_code) := by
        rw [← hadd]
        exact hle
      exact ZArith.BinInt.Z.le_trans pos' (list_length_z tf.fn_code)
        Ptrofs.max_unsigned hle' hlen
    rw [asmgenproof_ptrofs_unsigned_repr_local pos' ⟨hpos_nonneg, hpos_max⟩]
    have hsub : ZArith.BinInt.Z.sub pos' Z0 = pos' := by
      apply intOfZ_injective
      simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      rw [show intOfZ Z0 = 0 by rfl]
      omega
    rw [hsub] at htail
    exact htail
  · intro r hr
    change (CompCert4Lean.X86.Asm.Pregmap.set PC
      (.Vptr b (Ptrofs.repr pos')) rs) r = rs r
    unfold CompCert4Lean.X86.Asm.Pregmap.set
    split
    · rename_i heq
      exact False.elim (hr heq)
    · rfl

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

open CompCert4Lean.Backend.Asmgenproof0
open CompCert4Lean.Common.Errors
open CompCert4Lean.Lib.Coqlib

theorem return_address_exists : return_address_existsStatement := by
  apply CompCert4Lean.Backend.Asmgenproof0.return_address_exists
  · intro f i ep k c h
    have hl := transl_instr_label f i ep k c h
    cases i <;> try exact hl.1
    subst c
    exact is_tail.cons _ (is_tail.refl k)
  · intro f tf h
    unfold CompCert4Lean.X86.Asmgen.transf_function at h
    obtain ⟨tf0, ht, hs⟩ := bind_inversion _ _ _ _ _ h
    cases hz : zlt CompCert4Lean.Lib.Integers.Ptrofs.max_unsigned
        (list_length_z tf0.fn_code) with
    | left hlt =>
        rw [hz] at hs
        cases hs
    | right hge =>
        rw [hz] at hs
        cases hs
        unfold CompCert4Lean.X86.Asmgen.transl_function at ht
        obtain ⟨c, hc, he⟩ := bind_inversion _ _ _ _ _ ht
        cases he
        rw [transl_code'_transl_code] at hc
        exact ⟨c, true, hc, is_tail.cons _ (is_tail.refl c)⟩
  · exact transf_function_no_overflow

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Asmgenproof0
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

theorem exec_straight_steps_goto
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    exec_straight_steps_gotoStatement := by
  intro cfg xi prog tprog hmatch
  intro s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c'
  intro hstack hext hfind hlabel hatpc hparent hstep
  generalize hpc : rs1 .PC = pc at hatpc
  cases hatpc with
  | intro fb ofs f cfull ep tf tc hfind0 htrans hcode htail =>
      change CompCert4Lean.Common.Errors.bind
          (CompCert4Lean.X86.Asmgen.transl_code f c
            (CompCert4Lean.X86.Asmgen.it1_is_parent ep i))
          (fun k => CompCert4Lean.X86.Asmgen.transl_instr f i ep k) =
        .OK tc at hcode
      obtain ⟨k, htailcode, htrans_instr⟩ :=
        CompCert4Lean.Common.Errors.bind_inversion _ _ _ _ _ hcode
      obtain ⟨jmp, k', rs2, hexec_straight, hagree, hgoto⟩ :=
        hstep k tc htrans_instr
      have hatpc0 :
          CompCert4Lean.Backend.Asmgenproof0.transl_code_at_pc
            (CompCert4Lean.Common.Globalenvs.Genv.globalenv prog)
            (rs1 .PC) fb f (i :: c) ep tf tc := by
        rw [hpc]
        exact CompCert4Lean.Backend.Asmgenproof0.transl_code_at_pc.intro
          fb ofs f (i :: c) ep tf tc hfind0 htrans hcode htail
      have hfind' :
          CompCert4Lean.Common.Globalenvs.Genv.find_funct_ptr
              (CompCert4Lean.Common.Globalenvs.Genv.globalenv tprog) fb =
            some (.Internal tf) :=
        functions_transl prog tprog hmatch fb f tf hfind0 htrans
      have hlen := transf_function_no_overflow f tf htrans
      obtain ⟨ofs', hpc', htail'⟩ :=
        CompCert4Lean.Backend.Asmgenproof0.exec_straight_steps_2
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (ge := CompCert4Lean.Common.Globalenvs.Genv.globalenv tprog)
          (fn := tf) (c := tc) (rs := rs1) (m := m1')
          (c' := jmp :: k') (rs' := rs2) (m' := m2')
          hexec_straight hlen fb ofs hpc hfind' htail
      obtain ⟨tc', rs3, hgoto_label, hatpc', hother⟩ :=
        find_label_goto_label prog f tf lbl rs2 m2' c' fb ofs'
          hfind0 htrans hpc' hlabel
      refine ⟨.State rs3 m2', ?_, ?_⟩
      · apply plus_right'
        · exact CompCert4Lean.Backend.Asmgenproof0.exec_straight_steps_1
            (cfg := cfg) (xi := xi)
            (ge := CompCert4Lean.Common.Globalenvs.Genv.globalenv tprog)
            (fn := tf) (c := tc) (rs := rs1) (m := m1')
            (c' := jmp :: k') (rs' := rs2) (m' := m2')
            hexec_straight hlen fb ofs hpc hfind' htail
        · apply CompCert4Lean.X86.Asm.exec_step_internal
          · exact hpc'
          · exact hfind'
          · exact CompCert4Lean.Backend.Asmgenproof0.find_instr_tail
              tf.fn_code jmp k' (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs')
              htail'
          · calc
              CompCert4Lean.X86.Asm.exec_instr
                  (binary64_certificate := binary64_certificate)
                  (binary32_certificate := binary32_certificate)
                  (CompCert4Lean.Common.Globalenvs.Genv.globalenv tprog)
                  tf jmp rs2 m2' =
                CompCert4Lean.X86.Asm.goto_label tf lbl rs2 m2' := hgoto
              _ = .Next rs3 m2' := hgoto_label
        · rfl
      · apply match_states.match_states_intro
        · exact hstack
        · exact hfind0
        · exact hext
        · exact hatpc'
        · exact CompCert4Lean.Backend.Asmgenproof0.agree_exten
            ms2 sp rs2 rs3 hagree (by
              intro r hr
              exact hother r (by
                intro heq
                subst r
                simpa [CompCert4Lean.X86.Asm.data_preg] using hr))
        · intro h
          cases h

end CompCert4Lean.X86.Asmgenproof

set_option maxHeartbeats 2000000

namespace CompCert4Lean.X86.Asmgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Asmgenproof0
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Asm
open CompCert4Lean.X86.Asmgen


variable [binary64_certificate : BinaryNormalizeCertificate
    (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
  [binary32_certificate : BinaryNormalizeCertificate
    (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

private theorem simulation_label_case
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (prog : CompCert4Lean.Backend.Mach.program) (tprog : program)
    (hprog : match_prog prog tprog)
    (stack : List CompCert4Lean.Backend.Mach.stackframe) (fb : block) (sp : val)
    (lbl : label) (code : CompCert4Lean.Backend.Mach.code)
    (regs : CompCert4Lean.Backend.Mach.regset) (memory : mem) (target : state)
    (hmatch : match_states prog
      (.State stack fb sp (.Mlabel lbl :: code) regs memory) target) :
    ∃ target', plus (CompCert4Lean.X86.Asm.step cfg xi) (Genv.globalenv tprog)
      target E0 target' ∧
      match_states prog (.State stack fb sp code regs memory) target' := by
  cases hmatch with
  | match_states_intro _ _ _ _ ep _ _ targetMemory targetRegs fn targetFn targetCode
      hstack hfind hext hatpc hagree hparent =>
    apply exec_straight_steps cfg xi prog tprog hprog stack fb fn targetRegs
      (.Mlabel lbl) code ep targetFn targetCode targetMemory memory targetMemory
      sp regs hstack hext hfind hatpc
    intro continuation translated htrans
    have hcode : .Plabel lbl :: continuation = translated := by
      exact CompCert4Lean.Common.Errors.res.OK.inj htrans
    subst translated
    refine ⟨nextinstr targetRegs, ?_, agree_nextinstr regs sp targetRegs hagree, ?_⟩
    · exact exec_straight_one _ _ _ _ _ _ rfl (by
        rfl)
    · intro impossible
      cases impossible

omit binary64_certificate binary32_certificate in
private theorem simulation_return_case
    (prog : CompCert4Lean.Backend.Mach.program)
    (stack : List CompCert4Lean.Backend.Mach.stackframe) (fb : block)
    (sp returnAddress : val) (code : CompCert4Lean.Backend.Mach.code)
    (regs : CompCert4Lean.Backend.Mach.regset) (memory : mem) (target : state)
    (hmatch : match_states prog
      (.Returnstate (.Stackframe fb sp returnAddress code :: stack) regs memory) target) :
    match_states prog (.State stack fb sp code regs memory) target := by
  cases hmatch with
  | match_states_return _ _ _ targetMemory targetRegs hstack hext hagree hpc =>
    cases hstack with
    | match_stack_cons _ _ _ _ _ fn targetFn targetCode hfind hatpc hsp htail =>
      apply match_states.match_states_intro stack fb sp code false regs memory
        targetMemory targetRegs fn targetFn targetCode htail hfind hext
      · simpa [hpc, CompCert4Lean.Backend.Mach.parent_ra] using hatpc
      · exact hagree
      · intro impossible
        cases impossible

private theorem simulation_getstack_case
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (prog : CompCert4Lean.Backend.Mach.program) (tprog : program)
    (hprog : match_prog prog tprog)
    (stack : List CompCert4Lean.Backend.Mach.stackframe) (fb : block) (sp : val)
    (ofs : ptrofs) (ty : typ) (dst : CompCert4Lean.X86.Machregs.mreg)
    (code : CompCert4Lean.Backend.Mach.code)
    (regs : CompCert4Lean.Backend.Mach.regset) (memory : mem) (value : val)
    (hload : CompCert4Lean.Backend.Mach.load_stack memory sp ty ofs = some value)
    (target : state)
    (hmatch : match_states prog
      (.State stack fb sp (.Mgetstack ofs ty dst :: code) regs memory) target) :
    ∃ target', plus (CompCert4Lean.X86.Asm.step cfg xi) (Genv.globalenv tprog)
      target E0 target' ∧
      match_states prog (.State stack fb sp code
        (CompCert4Lean.Backend.Mach.Regmap.set dst value regs) memory) target' := by
  cases hmatch with
  | match_states_intro _ _ _ _ ep _ _ targetMemory targetRegs fn targetFn targetCode
      hstack hfind hext hatpc hagree hparent =>
    obtain ⟨loaded, hloadTarget, hvalue⟩ := Mem.loadv_extends
      (chunk_of_type ty) memory targetMemory (Val.offset_ptr sp ofs)
      (Val.offset_ptr sp ofs) value hext hload (.lessdef_refl _)
    rw [sp_val regs sp targetRegs hagree] at hloadTarget
    apply exec_straight_steps cfg xi prog tprog hprog stack fb fn targetRegs
      (.Mgetstack ofs ty dst) code ep targetFn targetCode targetMemory memory
      targetMemory sp (CompCert4Lean.Backend.Mach.Regmap.set dst value regs)
      hstack hext hfind hatpc
    intro continuation translated htrans
    obtain ⟨resultRegs, hexec, hresult, hother⟩ :=
      CompCert4Lean.X86.Asmgenproof1.loadind_correct
        (Genv.globalenv tprog) targetFn .RSP ofs ty dst continuation targetRegs
        translated targetMemory loaded htrans hloadTarget
    refine ⟨resultRegs, hexec, ?_, ?_⟩
    · apply agree_set_mreg regs sp targetRegs dst value resultRegs hagree
      · rwa [hresult]
      · exact hother
    · intro impossible
      cases impossible

private theorem simulation_setstack_case
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (prog : CompCert4Lean.Backend.Mach.program) (tprog : program)
    (hprog : match_prog prog tprog)
    (stack : List CompCert4Lean.Backend.Mach.stackframe) (fb : block) (sp : val)
    (src : CompCert4Lean.X86.Machregs.mreg) (ofs : ptrofs) (ty : typ)
    (code : CompCert4Lean.Backend.Mach.code)
    (regs : CompCert4Lean.Backend.Mach.regset) (memory memory' : mem)
    (hstore : CompCert4Lean.Backend.Mach.store_stack memory sp ty ofs (regs src) =
      some memory') (target : state)
    (hmatch : match_states prog
      (.State stack fb sp (.Msetstack src ofs ty :: code) regs memory) target) :
    ∃ target', plus (CompCert4Lean.X86.Asm.step cfg xi) (Genv.globalenv tprog)
      target E0 target' ∧
      match_states prog (.State stack fb sp code
        (CompCert4Lean.Backend.Mach.undef_regs
          (CompCert4Lean.X86.Machregs.destroyed_by_setstack ty) regs) memory') target' := by
  cases hmatch with
  | match_states_intro _ _ _ _ ep _ _ targetMemory targetRegs fn targetFn targetCode
      hstack hfind hext hatpc hagree hparent =>
    obtain ⟨resultMemory, hstoreTarget, hext'⟩ := Mem.storev_extends
      (chunk_of_type ty) memory targetMemory (Val.offset_ptr sp ofs) (regs src)
      memory' (Val.offset_ptr sp ofs) (targetRegs (preg_of src)) hext hstore
      (.lessdef_refl _) (hagree.agree_mregs src)
    rw [sp_val regs sp targetRegs hagree] at hstoreTarget
    apply exec_straight_steps cfg xi prog tprog hprog stack fb fn targetRegs
      (.Msetstack src ofs ty) code ep targetFn targetCode targetMemory memory'
      resultMemory sp (CompCert4Lean.Backend.Mach.undef_regs
        (CompCert4Lean.X86.Machregs.destroyed_by_setstack ty) regs)
      hstack hext' hfind hatpc
    intro continuation translated htrans
    obtain ⟨resultRegs, hexec, hother⟩ :=
      CompCert4Lean.X86.Asmgenproof1.storeind_correct
        (Genv.globalenv tprog) targetFn .RSP ofs ty src continuation targetRegs
        translated targetMemory resultMemory htrans hstoreTarget
    refine ⟨resultRegs, hexec, ?_, ?_⟩
    · exact agree_undef_regs regs sp _ targetRegs resultRegs hagree hother
    · intro hparent'
      rw [hother (.IR .RAX) rfl]
      · exact hparent hparent'
      · cases ty <;> simp [CompCert4Lean.X86.Machregs.destroyed_by_setstack,
          preg_notin, preg_of]

private theorem simulation_goto_case
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (prog : CompCert4Lean.Backend.Mach.program) (tprog : program)
    (hprog : match_prog prog tprog)
    (stack : List CompCert4Lean.Backend.Mach.stackframe) (fb : block) (sp : val)
    (fn : CompCert4Lean.Backend.Mach.function) (lbl : label)
    (code destination : CompCert4Lean.Backend.Mach.code)
    (regs : CompCert4Lean.Backend.Mach.regset) (memory : mem)
    (hfind : Genv.find_funct_ptr (Genv.globalenv prog) fb = some (.Internal fn))
    (hlabel : CompCert4Lean.Backend.Mach.find_label lbl fn.fn_code = some destination)
    (target : state)
    (hmatch : match_states prog
      (.State stack fb sp (.Mgoto lbl :: code) regs memory) target) :
    ∃ target', plus (CompCert4Lean.X86.Asm.step cfg xi) (Genv.globalenv tprog)
      target E0 target' ∧
      match_states prog (.State stack fb sp destination regs memory) target' := by
  cases hmatch with
  | match_states_intro _ _ _ _ ep _ _ targetMemory targetRegs foundFn targetFn targetCode
      hstack hfound hext hatpc hagree hparent =>
    have heq : foundFn = fn := by
      cases hfound.symm.trans hfind
      rfl
    subst foundFn
    generalize hpc : targetRegs .PC = pc at hatpc
    cases hatpc with
    | intro _ ofs _ _ _ _ _ hfind' htrans hcode htail =>
      obtain ⟨continuation, hcontinuation, htranslation⟩ :
          ∃ continuation, transl_code fn code false = .OK continuation ∧
            targetCode = .Pjmp_l lbl :: continuation := by
        change CompCert4Lean.Common.Errors.bind (transl_code fn code false)
          (fun continuation => .OK (.Pjmp_l lbl :: continuation)) = .OK targetCode at hcode
        cases hcontinuation : transl_code fn code false with
        | Error message => simp [hcontinuation, CompCert4Lean.Common.Errors.bind] at hcode
        | OK continuation =>
          simp [hcontinuation, CompCert4Lean.Common.Errors.bind] at hcode
          exact ⟨continuation, rfl, (CompCert4Lean.Common.Errors.res.OK.inj hcode).symm⟩
      obtain ⟨destinationCode, resultRegs, hgoto, hatpc', hother⟩ :=
        find_label_goto_label prog fn targetFn lbl targetRegs targetMemory
          destination fb ofs hfind htrans hpc hlabel
      refine ⟨.State resultRegs targetMemory, ?_, ?_⟩
      · apply plus_one
        apply CompCert4Lean.X86.Asm.exec_step_internal
        · exact hpc
        · exact functions_transl prog tprog hprog fb fn targetFn hfind htrans
        · exact find_instr_tail targetFn.fn_code (.Pjmp_l lbl) continuation
            (Ptrofs.unsigned ofs) (htranslation ▸ htail)
        · exact hgoto
      · apply match_states.match_states_intro stack fb sp destination false regs
          memory targetMemory resultRegs fn targetFn destinationCode hstack hfind hext hatpc'
        · apply agree_exten regs sp targetRegs resultRegs hagree
          intro reg hdata
          exact hother reg (by
            intro heq
            subst reg
            cases hdata)
        · intro impossible
          cases impossible

private theorem simulation_getparam_case
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (prog : CompCert4Lean.Backend.Mach.program) (tprog : program)
    (hprog : match_prog prog tprog)
    (stack : List CompCert4Lean.Backend.Mach.stackframe) (fb : block) (sp : val)
    (fn : CompCert4Lean.Backend.Mach.function) (ofs : ptrofs) (ty : typ)
    (dst : CompCert4Lean.X86.Machregs.mreg) (code : CompCert4Lean.Backend.Mach.code)
    (regs : CompCert4Lean.Backend.Mach.regset) (memory : mem) (value : val)
    (hfind : Genv.find_funct_ptr (Genv.globalenv prog) fb = some (.Internal fn))
    (hlink : CompCert4Lean.Backend.Mach.load_stack memory sp Tptr fn.fn_link_ofs =
      some (CompCert4Lean.Backend.Mach.parent_sp stack))
    (hload : CompCert4Lean.Backend.Mach.load_stack memory
      (CompCert4Lean.Backend.Mach.parent_sp stack) ty ofs = some value)
    (target : state)
    (hmatch : match_states prog
      (.State stack fb sp (.Mgetparam ofs ty dst :: code) regs memory) target) :
    ∃ target', plus (CompCert4Lean.X86.Asm.step cfg xi) (Genv.globalenv tprog)
      target E0 target' ∧
      match_states prog (.State stack fb sp code
        (CompCert4Lean.Backend.Mach.Regmap.set dst value
          (CompCert4Lean.Backend.Mach.Regmap.set .AX .Vundef regs)) memory) target' := by
  cases hmatch with
  | match_states_intro _ _ _ _ ep _ _ targetMemory targetRegs foundFn targetFn targetCode
      hstack hfound hext hatpc hagree hparent =>
    have heq : foundFn = fn := by
      cases hfound.symm.trans hfind
      rfl
    subst foundFn
    obtain ⟨loadedParent, hlinkTarget, hparentValue⟩ := Mem.loadv_extends
      (chunk_of_type Tptr) memory targetMemory (Val.offset_ptr sp fn.fn_link_ofs)
      (Val.offset_ptr sp fn.fn_link_ofs) _ hext hlink (.lessdef_refl _)
    have hparentEq := lessdef_parent_sp (Genv.globalenv prog) stack loadedParent
      hstack hparentValue
    subst loadedParent
    rw [sp_val regs sp targetRegs hagree] at hlinkTarget
    obtain ⟨loaded, hloadTarget, hvalue⟩ := Mem.loadv_extends
      (chunk_of_type ty) memory targetMemory
      (Val.offset_ptr (CompCert4Lean.Backend.Mach.parent_sp stack) ofs)
      (Val.offset_ptr (CompCert4Lean.Backend.Mach.parent_sp stack) ofs)
      value hext hload (.lessdef_refl _)
    apply exec_straight_steps cfg xi prog tprog hprog stack fb fn targetRegs
      (.Mgetparam ofs ty dst) code ep targetFn targetCode targetMemory memory
      targetMemory sp _ hstack hext hfind hatpc
    intro continuation translated htrans
    have finish (middleRegs : regset) (middleCode : CompCert4Lean.X86.Asm.code)
        (hagreeMiddle : agree (CompCert4Lean.Backend.Mach.Regmap.set .AX .Vundef regs)
          sp middleRegs)
        (hparentMiddle : middleRegs (.IR .RAX) = CompCert4Lean.Backend.Mach.parent_sp stack)
        (htranslate : loadind .RAX ofs ty dst continuation = .OK middleCode) :
        ∃ resultRegs,
          exec_straight (Genv.globalenv tprog) targetFn middleCode middleRegs
            targetMemory continuation resultRegs targetMemory ∧
          agree (CompCert4Lean.Backend.Mach.Regmap.set dst value
            (CompCert4Lean.Backend.Mach.Regmap.set .AX .Vundef regs)) sp resultRegs ∧
          (it1_is_parent ep (.Mgetparam ofs ty dst) = true →
            resultRegs (.IR .RAX) = CompCert4Lean.Backend.Mach.parent_sp stack) := by
      obtain ⟨resultRegs, hexec, hresult, hother⟩ :=
        CompCert4Lean.X86.Asmgenproof1.loadind_correct
          (Genv.globalenv tprog) targetFn .RAX ofs ty dst continuation middleRegs
          middleCode targetMemory loaded htranslate (by rwa [hparentMiddle])
      refine ⟨resultRegs, hexec, ?_, ?_⟩
      · apply agree_set_mreg _ sp middleRegs dst value resultRegs hagreeMiddle
        · rwa [hresult]
        · exact hother
      · intro hparentNext
        rw [hother (.IR .RAX) rfl]
        · exact hparentMiddle
        · intro heq
          have hdst := preg_of_injective .AX dst heq
          subst dst
          cases hparentNext
    cases ep with
    | true =>
      exact finish targetRegs translated
        (agree_set_mreg regs sp targetRegs .AX .Vundef targetRegs hagree
          (.lessdef_undef _) (by intros; rfl)) (hparent rfl) htrans
    | false =>
      change CompCert4Lean.Common.Errors.bind (loadind .RAX ofs ty dst continuation)
        (fun middleCode => loadind .RSP fn.fn_link_ofs Tptr .AX middleCode) =
          .OK translated at htrans
      cases hmiddle : loadind .RAX ofs ty dst continuation with
      | Error message => simp [hmiddle, CompCert4Lean.Common.Errors.bind] at htrans
      | OK middleCode =>
        simp only [hmiddle, CompCert4Lean.Common.Errors.bind] at htrans
        obtain ⟨middleRegs, hexecFirst, hrax, hother⟩ :=
          CompCert4Lean.X86.Asmgenproof1.loadind_correct
            (Genv.globalenv tprog) targetFn .RSP fn.fn_link_ofs Tptr .AX middleCode
            targetRegs translated targetMemory _ htrans hlinkTarget
        obtain ⟨resultRegs, hexecLast, hagreeResult, hparentResult⟩ :=
          finish middleRegs middleCode
            (agree_set_mreg regs sp targetRegs .AX .Vundef middleRegs hagree
              (.lessdef_undef _) hother) hrax hmiddle
        exact ⟨resultRegs, exec_straight_trans _ _ _ _ _ _ _ _ _ _ _ hexecFirst hexecLast,
          hagreeResult, hparentResult⟩

private theorem simulation_external_case
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (prog : CompCert4Lean.Backend.Mach.program) (tprog : program)
    (hprog : match_prog prog tprog)
    (stack : List CompCert4Lean.Backend.Mach.stackframe) (fb : block)
    (regs : CompCert4Lean.Backend.Mach.regset) (memory memory' : mem)
    (ef : external_function) (args : List val) (value : val) (events : trace)
    (hfind : Genv.find_funct_ptr (Genv.globalenv prog) fb = some (.External ef))
    (hargs : CompCert4Lean.Backend.Mach.extcall_arguments cfg regs memory
      (CompCert4Lean.Backend.Mach.parent_sp stack) (ef_sig ef) args)
    (hcall : external_call xi ef (Genv.to_senv (Genv.globalenv prog))
      args memory events value memory') (target : state)
    (hmatch : match_states prog (.Callstate stack fb regs memory) target) :
    ∃ target', plus (CompCert4Lean.X86.Asm.step cfg xi) (Genv.globalenv tprog)
      target events target' ∧
      match_states prog (.Returnstate stack
        (CompCert4Lean.Backend.Mach.set_pair
          (CompCert4Lean.X86.Conventions1.loc_result (ef_sig ef)) value
          (CompCert4Lean.Backend.Mach.undef_caller_save_regs cfg regs)) memory') target' := by
  cases hmatch with
  | match_states_call _ _ _ _ targetMemory targetRegs hstack hext hagree hpc hra =>
    obtain ⟨translated, htranslated, htranslation⟩ :=
      functions_translated prog tprog hprog fb (.External ef) hfind
    have htranslatedEq : translated = .External ef := by
      exact (CompCert4Lean.Common.Errors.res.OK.inj htranslation).symm
    subst translated
    obtain ⟨targetArgs, htargetArgs, hargsLess⟩ := extcall_arguments_match
      cfg regs memory targetMemory (CompCert4Lean.Backend.Mach.parent_sp stack)
      targetRegs (ef_sig ef) args hagree hext hargs
    obtain ⟨targetValue, resultMemory, htargetCall, hvalue, hext', hunchanged⟩ :=
      external_call_mem_extends_proof xi ef _ _ _ _ _ _ _ _ hcall hext hargsLess
    let resultRegs := Pregmap.set .PC (targetRegs .RA)
      (set_pair (loc_external_result (ef_sig ef)) targetValue
        (undef_caller_save_regs cfg targetRegs))
    refine ⟨.State resultRegs resultMemory, ?_, ?_⟩
    · apply plus_one
      exact exec_step_external fb ef targetArgs targetValue targetRegs targetMemory
        events resultRegs resultMemory hpc htranslated htargetArgs
        (external_call_symbols_preserved_proof xi ef _ _ _ _ _ _ _
          (senv_preserved prog tprog hprog) htargetCall) rfl
    · apply match_states.match_states_return stack _ memory' resultMemory resultRegs
        hstack hext'
      · apply agree_set_other _ _ _ .PC (targetRegs .RA)
        · apply agree_set_pair _ _ _ _ _ _
          · exact agree_undef_caller_save_regs cfg regs _ targetRegs hagree
          · exact hvalue
        · rfl
      · change targetRegs .RA = _
        exact hra

omit binary64_certificate binary32_certificate in
private theorem simulation_translation_cons
    (fn : CompCert4Lean.Backend.Mach.function)
    (instr : CompCert4Lean.Backend.Mach.instruction)
    (code : CompCert4Lean.Backend.Mach.code) (parent : Bool)
    (translated : CompCert4Lean.X86.Asm.code)
    (htrans : transl_code fn (instr :: code) parent = .OK translated) :
    ∃ continuation,
      transl_code fn code (it1_is_parent parent instr) = .OK continuation ∧
      transl_instr fn instr parent continuation = .OK translated := by
  change CompCert4Lean.Common.Errors.bind
    (transl_code fn code (it1_is_parent parent instr))
    (transl_instr fn instr parent) = .OK translated at htrans
  cases htail : transl_code fn code (it1_is_parent parent instr) with
  | Error message => simp [htail, CompCert4Lean.Common.Errors.bind] at htrans
  | OK continuation =>
    exact ⟨continuation, rfl, by
      simpa only [htail, CompCert4Lean.Common.Errors.bind] using htrans⟩

omit binary64_certificate binary32_certificate in
private theorem simulation_pc_notin (regs : List CompCert4Lean.X86.Machregs.mreg) :
    preg_notin .PC regs := by
  apply (preg_notin_charact .PC regs).mpr
  intro reg hmem heq
  have hdata := preg_of_data reg
  rw [← heq] at hdata
  cases hdata

private theorem simulation_builtin_case
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (prog : CompCert4Lean.Backend.Mach.program) (tprog : program)
    (hprog : match_prog prog tprog)
    (stack : List CompCert4Lean.Backend.Mach.stackframe) (fb : block) (sp : val)
    (regs : CompCert4Lean.Backend.Mach.regset) (memory memory' : mem)
    (ef : external_function) (args : List (builtin_arg CompCert4Lean.X86.Machregs.mreg))
    (res : builtin_res CompCert4Lean.X86.Machregs.mreg)
    (code : CompCert4Lean.Backend.Mach.code) (values : List val)
    (value : val) (events : trace)
    (hargs : eval_builtin_args (Genv.to_senv (Genv.globalenv prog)) regs sp memory args values)
    (hcall : external_call xi ef (Genv.to_senv (Genv.globalenv prog))
      values memory events value memory') (target : state)
    (hmatch : match_states prog
      (.State stack fb sp (.Mbuiltin ef args res :: code) regs memory) target) :
    ∃ target', plus (CompCert4Lean.X86.Asm.step cfg xi) (Genv.globalenv tprog)
      target events target' ∧
      match_states prog (.State stack fb sp code
        (CompCert4Lean.Backend.Mach.set_res res value
          (CompCert4Lean.Backend.Mach.undef_regs
            (CompCert4Lean.X86.Machregs.destroyed_by_builtin ef) regs)) memory') target' := by
  cases hmatch with
  | match_states_intro _ _ _ _ ep _ _ targetMemory targetRegs fn targetFn targetCode
      hstack hfind hext hatpc hagree hparent =>
    generalize hpc : targetRegs .PC = pc at hatpc
    cases hatpc with
    | intro _ ofs _ _ _ _ _ hfind' htrans hcode htail =>
      obtain ⟨continuation, hcontinuation, htranslation⟩ :=
        simulation_translation_cons fn (.Mbuiltin ef args res) code ep targetCode hcode
      have hcodeEq : targetCode = .Pbuiltin ef (args.map (map_builtin_arg preg_of))
          (map_builtin_res preg_of res) :: continuation :=
        (CompCert4Lean.Common.Errors.res.OK.inj htranslation).symm
      subst targetCode
      obtain ⟨targetArgs, htargetArgs, hargsLess⟩ := builtin_args_match
        (Genv.to_senv (Genv.globalenv prog)) regs sp targetRegs memory targetMemory
        hagree hext args values hargs
      obtain ⟨targetValue, resultMemory, htargetCall, hvalue, hext', hunchanged⟩ :=
        external_call_mem_extends_proof xi ef _ _ _ _ _ _ _ _ hcall hext hargsLess
      let intermediateRegs := set_res (map_builtin_res preg_of res) targetValue
        (undef_regs ((CompCert4Lean.X86.Machregs.destroyed_by_builtin ef).map preg_of) targetRegs)
      let resultRegs := nextinstr_nf intermediateRegs
      have hresultPC : resultRegs .PC = .Vptr fb (Ptrofs.add ofs Ptrofs.one) := by
        change Val.offset_ptr
          ((undef_regs [.CR .ZF, .CR .CF, .CR .PF, .CR .SF, .CR .OF] intermediateRegs) .PC)
          Ptrofs.one = _
        rw [undef_regs_other .PC _ _ (by simp)]
        change Val.offset_ptr (set_res (map_builtin_res preg_of res) targetValue
          (undef_regs ((CompCert4Lean.X86.Machregs.destroyed_by_builtin ef).map preg_of)
            targetRegs) .PC) Ptrofs.one = _
        rw [set_res_other .PC res _ _ rfl,
          undef_regs_other_2 .PC _ _ (simulation_pc_notin _), hpc]
        rfl
      refine ⟨.State resultRegs resultMemory, ?_, ?_⟩
      · apply plus_one
        apply exec_step_builtin fb ofs targetFn ef _ _ targetRegs targetMemory
          targetArgs events targetValue resultRegs resultMemory hpc
          (functions_transl prog tprog hprog fb fn targetFn hfind htrans)
          (find_instr_tail _ _ _ _ htail)
        · change eval_builtin_args (Genv.to_senv (Genv.globalenv tprog)) targetRegs
            (targetRegs (.IR .RSP)) targetMemory _ targetArgs
          have hsp : targetRegs (.IR .RSP) = sp := hagree.agree_sp
          rw [hsp]
          exact eval_builtin_args_preserved _ _ _ _ _ _ _ _ _ _
            (symbols_preserved prog tprog hprog) _ _ htargetArgs
        · exact external_call_symbols_preserved_proof xi ef _ _ _ _ _ _ _
            (senv_preserved prog tprog hprog) htargetCall
        · rfl
      · apply match_states.match_states_intro stack fb sp code false _ memory'
          resultMemory resultRegs fn targetFn continuation hstack hfind hext'
        · rw [hresultPC]
          exact transl_code_at_pc.intro fb _ fn code false targetFn continuation
            hfind htrans hcontinuation
            (code_tail_next_int _ _ _ _ (transf_function_no_overflow fn targetFn htrans) htail)
        · apply CompCert4Lean.X86.Asmgenproof1.agree_nextinstr_nf
          apply agree_set_res res _ _ _ _ _
          · apply agree_undef_regs regs sp _ targetRegs _ hagree
            intro reg hdata hnotin
            exact undef_regs_other_2 reg _ _ hnotin
          · exact hvalue
        · intro impossible
          cases impossible

private theorem simulation_jumptable_case
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (prog : CompCert4Lean.Backend.Mach.program) (tprog : program)
    (hprog : match_prog prog tprog)
    (stack : List CompCert4Lean.Backend.Mach.stackframe) (fb : block) (sp : val)
    (fn : CompCert4Lean.Backend.Mach.function) (arg : CompCert4Lean.X86.Machregs.mreg)
    (table : List label) (lbl : label) (index : int)
    (code destination : CompCert4Lean.Backend.Mach.code)
    (regs : CompCert4Lean.Backend.Mach.regset) (memory : mem)
    (harg : regs arg = .Vint index)
    (hindex : CompCert4Lean.Lib.Coqlib.list_nth_z table (Int.unsigned index) = some lbl)
    (hfind : Genv.find_funct_ptr (Genv.globalenv prog) fb = some (.Internal fn))
    (hlabel : CompCert4Lean.Backend.Mach.find_label lbl fn.fn_code = some destination)
    (target : state)
    (hmatch : match_states prog
      (.State stack fb sp (.Mjumptable arg table :: code) regs memory) target) :
    ∃ target', plus (CompCert4Lean.X86.Asm.step cfg xi) (Genv.globalenv tprog)
      target E0 target' ∧
      match_states prog (.State stack fb sp destination
        (CompCert4Lean.Backend.Mach.undef_regs
          CompCert4Lean.X86.Machregs.destroyed_by_jumptable regs) memory) target' := by
  cases hmatch with
  | match_states_intro _ _ _ _ ep _ _ targetMemory targetRegs foundFn targetFn targetCode
      hstack hfound hext hatpc hagree hparent =>
    have heq : foundFn = fn := by
      cases hfound.symm.trans hfind
      rfl
    subst foundFn
    generalize hpc : targetRegs .PC = pc at hatpc
    cases hatpc with
    | intro _ ofs _ _ _ _ _ hfind' htrans hcode htail =>
      obtain ⟨continuation, hcontinuation, htranslation⟩ :=
        simulation_translation_cons fn (.Mjumptable arg table) code ep targetCode hcode
      change CompCert4Lean.Common.Errors.bind (ireg_of arg)
        (fun reg => .OK (.Pjmptbl reg table :: continuation)) = .OK targetCode at htranslation
      cases hreg : ireg_of arg with
      | Error message => simp [hreg, CompCert4Lean.Common.Errors.bind] at htranslation
      | OK reg =>
        simp only [hreg, CompCert4Lean.Common.Errors.bind] at htranslation
        have hcodeEq := CompCert4Lean.Common.Errors.res.OK.inj htranslation
        subst targetCode
        have hargTarget : targetRegs (.IR reg) = .Vint index := by
          have hless := ireg_val regs sp targetRegs arg reg hagree hreg
          rw [harg] at hless
          generalize htarget : targetRegs (.IR reg) = targetValue at hless
          cases hless
          rfl
        let middleRegs := Pregmap.set (.IR .RAX) .Vundef
          (Pregmap.set (.IR .RDX) .Vundef targetRegs)
        have hpcMiddle : middleRegs .PC = .Vptr fb ofs := hpc
        obtain ⟨destinationCode, resultRegs, hgoto, hatpc', hother⟩ :=
          find_label_goto_label prog fn targetFn lbl middleRegs targetMemory
            destination fb ofs hfind htrans hpcMiddle hlabel
        refine ⟨.State resultRegs targetMemory, ?_, ?_⟩
        · apply plus_one
          apply exec_step_internal fb ofs targetFn (.Pjmptbl reg table) targetRegs
            targetMemory resultRegs targetMemory hpc
            (functions_transl prog tprog hprog fb fn targetFn hfind htrans)
            (find_instr_tail _ _ _ _ htail)
          dsimp only [exec_instr, Pregmap.get]
          rw [hargTarget]
          dsimp only
          rw [hindex]
          exact hgoto
        · apply match_states.match_states_intro stack fb sp destination false _ memory
            targetMemory resultRegs fn targetFn destinationCode hstack hfind hext hatpc'
          · apply agree_undef_regs regs sp _ targetRegs resultRegs hagree
            intro preg hdata hnotin
            rw [hother preg (by intro heq; subst preg; cases hdata)]
            change preg ≠ .IR .RAX ∧ preg ≠ .IR .RDX at hnotin
            simp [middleRegs, Pregmap.set, hnotin.1, hnotin.2]
          · intro impossible
            cases impossible

omit binary64_certificate binary32_certificate in
private theorem simulation_indirect_target
    (ge : CompCert4Lean.Backend.Mach.genv)
    (regs : CompCert4Lean.Backend.Mach.regset) (sp : val) (targetRegs : regset)
    (sourceReg : CompCert4Lean.X86.Machregs.mreg) (targetReg : ireg) (callee : block)
    (hagree : agree regs sp targetRegs)
    (hreg : ireg_of sourceReg = .OK targetReg)
    (hfind : CompCert4Lean.Backend.Mach.find_function_ptr ge (.inl sourceReg) regs = some callee) :
    targetRegs (.IR targetReg) = .Vptr callee Ptrofs.zero := by
  have hsource : regs sourceReg = .Vptr callee Ptrofs.zero := by
    unfold CompCert4Lean.Backend.Mach.find_function_ptr at hfind
    cases hvalue : regs sourceReg <;> simp only [hvalue] at hfind <;> try cases hfind
    rename_i pointer offset
    split at hfind
    · rename_i heq
      have hoffset := Ptrofs.eq_spec_proof offset Ptrofs.zero
      rw [heq] at hoffset
      cases hfind
      exact congrArg (val.Vptr callee) hoffset
    · cases hfind
  have hless := ireg_val regs sp targetRegs sourceReg targetReg hagree hreg
  rw [hsource] at hless
  generalize htarget : targetRegs (.IR targetReg) = targetValue at hless
  cases hless
  rfl

private theorem simulation_call_case
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (prog : CompCert4Lean.Backend.Mach.program) (tprog : program)
    (hprog : match_prog prog tprog)
    (stack : List CompCert4Lean.Backend.Mach.stackframe) (fb : block) (sp : val)
    (fn : CompCert4Lean.Backend.Mach.function) (sig : signature)
    (ros : Sum CompCert4Lean.X86.Machregs.mreg ident)
    (code : CompCert4Lean.Backend.Mach.code)
    (regs : CompCert4Lean.Backend.Mach.regset) (memory : mem) (callee : block) (ra : ptrofs)
    (hcallee : CompCert4Lean.Backend.Mach.find_function_ptr (Genv.globalenv prog) ros regs = some callee)
    (hfind : Genv.find_funct_ptr (Genv.globalenv prog) fb = some (.Internal fn))
    (hreturn : return_address_offset fn code ra) (target : state)
    (hmatch : match_states prog
      (.State stack fb sp (.Mcall sig ros :: code) regs memory) target) :
    ∃ target', plus (CompCert4Lean.X86.Asm.step cfg xi) (Genv.globalenv tprog)
      target E0 target' ∧
      match_states prog (.Callstate (.Stackframe fb sp (.Vptr fb ra) code :: stack)
        callee regs memory) target' := by
  cases hmatch with
  | match_states_intro _ _ _ _ ep _ _ targetMemory targetRegs foundFn targetFn targetCode
      hstack hfound hext hatpc hagree hparent =>
    have heq : foundFn = fn := by
      cases hfound.symm.trans hfind
      rfl
    subst foundFn
    generalize hpc : targetRegs .PC = pc at hatpc
    cases hatpc with
    | intro _ ofs _ _ _ _ _ hfind' htrans hcode htail =>
      obtain ⟨continuation, hcontinuation, htranslation⟩ :=
        simulation_translation_cons fn (.Mcall sig ros) code ep targetCode hcode
      let resultRegs := Pregmap.set .RA (.Vptr fb (Ptrofs.add ofs Ptrofs.one))
        (Pregmap.set .PC (.Vptr callee Ptrofs.zero) targetRegs)
      obtain ⟨callInstr, hcodeEq, hstep⟩ : ∃ callInstr,
          targetCode = callInstr :: continuation ∧
          exec_instr (Genv.globalenv tprog) targetFn callInstr targetRegs targetMemory =
            .Next resultRegs targetMemory := by
        cases ros with
        | inl sourceReg =>
          change CompCert4Lean.Common.Errors.bind (ireg_of sourceReg)
            (fun reg => .OK (.Pcall_r reg sig :: continuation)) = .OK targetCode at htranslation
          cases hreg : ireg_of sourceReg with
          | Error message => simp [hreg, CompCert4Lean.Common.Errors.bind] at htranslation
          | OK reg =>
            simp only [hreg, CompCert4Lean.Common.Errors.bind] at htranslation
            refine ⟨.Pcall_r reg sig, (CompCert4Lean.Common.Errors.res.OK.inj htranslation).symm, ?_⟩
            have harg := simulation_indirect_target _ regs sp targetRegs sourceReg reg
              callee hagree hreg hcallee
            dsimp only [exec_instr, Pregmap.get]
            rw [harg, hpc]
            rfl
        | inr symbol =>
          refine ⟨.Pcall_s symbol sig,
            (CompCert4Lean.Common.Errors.res.OK.inj htranslation).symm, ?_⟩
          change Genv.find_symbol (Genv.globalenv prog) symbol = some callee at hcallee
          dsimp only [exec_instr, Pregmap.get]
          simp only [hpc, Genv.symbol_address,
            symbols_preserved prog tprog hprog, hcallee, Val.offset_ptr]
          rfl
      subst targetCode
      have hreturnAt : transl_code_at_pc (Genv.globalenv prog)
          (.Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb fn code false targetFn continuation :=
        transl_code_at_pc.intro fb _ fn code false targetFn continuation hfind htrans
          hcontinuation (code_tail_next_int _ _ _ _
            (transf_function_no_overflow fn targetFn htrans) htail)
      have hra := return_address_offset_correct (Genv.globalenv prog) fb _ fb fn code
        targetFn continuation ra hreturnAt hreturn
      subst ra
      refine ⟨.State resultRegs targetMemory, ?_, ?_⟩
      · apply plus_one
        exact exec_step_internal fb ofs targetFn callInstr targetRegs targetMemory
          resultRegs targetMemory hpc
          (functions_transl prog tprog hprog fb fn targetFn hfind htrans)
          (find_instr_tail _ _ _ _ htail) hstep
      · apply match_states.match_states_call _ callee regs memory targetMemory resultRegs
        · exact match_stack_cons fb sp _ code stack fn targetFn continuation
            hfind hreturnAt hagree.agree_sp_def hstack
        · exact hext
        · apply agree_set_other _ _ _ .RA _
          · exact agree_set_other regs sp targetRegs .PC _ hagree rfl
          · rfl
        · rfl
        · rfl

private theorem simulation_freeframe
    (prog : CompCert4Lean.Backend.Mach.program) (ge : genv) (targetFn : function)
    (stack : List CompCert4Lean.Backend.Mach.stackframe)
    (fn : CompCert4Lean.Backend.Mach.function) (stk : block) (offset : ptrofs)
    (regs : CompCert4Lean.Backend.Mach.regset) (targetRegs : regset)
    (memory targetMemory memory' : mem)
    (hstack : match_stack (Genv.globalenv prog) stack)
    (hext : Mem.extends memory targetMemory)
    (hagree : agree regs (.Vptr stk offset) targetRegs)
    (hlink : CompCert4Lean.Backend.Mach.load_stack memory (.Vptr stk offset)
      Tptr fn.fn_link_ofs = some (CompCert4Lean.Backend.Mach.parent_sp stack))
    (hreturn : CompCert4Lean.Backend.Mach.load_stack memory (.Vptr stk offset)
      Tptr fn.fn_retaddr_ofs = some (CompCert4Lean.Backend.Mach.parent_ra stack))
    (hfree : Mem.free memory stk .Z0 fn.fn_stacksize = some memory') :
    let resultRegs := nextinstr (Pregmap.set (.IR .RSP)
      (CompCert4Lean.Backend.Mach.parent_sp stack)
      (Pregmap.set .RA (CompCert4Lean.Backend.Mach.parent_ra stack) targetRegs))
    ∃ resultMemory, Mem.extends memory' resultMemory ∧
      exec_instr ge targetFn (.Pfreeframe fn.fn_stacksize fn.fn_retaddr_ofs fn.fn_link_ofs)
        targetRegs targetMemory = .Next resultRegs resultMemory ∧
      agree regs (CompCert4Lean.Backend.Mach.parent_sp stack) resultRegs := by
  dsimp only
  obtain ⟨loadedParent, hlinkTarget, hparentValue⟩ := Mem.loadv_extends
    (chunk_of_type Tptr) memory targetMemory (Val.offset_ptr (.Vptr stk offset) fn.fn_link_ofs)
    (Val.offset_ptr (.Vptr stk offset) fn.fn_link_ofs) _ hext hlink (.lessdef_refl _)
  have hparentEq := lessdef_parent_sp (Genv.globalenv prog) stack loadedParent hstack hparentValue
  subst loadedParent
  obtain ⟨loadedRA, hreturnTarget, hraValue⟩ := Mem.loadv_extends
    (chunk_of_type Tptr) memory targetMemory (Val.offset_ptr (.Vptr stk offset) fn.fn_retaddr_ofs)
    (Val.offset_ptr (.Vptr stk offset) fn.fn_retaddr_ofs) _ hext hreturn (.lessdef_refl _)
  have hraEq := lessdef_parent_ra (Genv.globalenv prog) stack loadedRA hstack hraValue
  subst loadedRA
  obtain ⟨resultMemory, hfreeTarget, hext'⟩ :=
    Mem.free_parallel_extends memory targetMemory stk .Z0 fn.fn_stacksize memory' hext hfree
  refine ⟨resultMemory, hext', ?_, ?_⟩
  · have hsp : targetRegs (.IR .RSP) = .Vptr stk offset := hagree.agree_sp
    dsimp only [exec_instr, Pregmap.get]
    rw [hsp]
    change Mem.loadv Mptr targetMemory (Val.offset_ptr (.Vptr stk offset) fn.fn_retaddr_ofs) =
      some (CompCert4Lean.Backend.Mach.parent_ra stack) at hreturnTarget
    change Mem.loadv Mptr targetMemory (Val.offset_ptr (.Vptr stk offset) fn.fn_link_ofs) =
      some (CompCert4Lean.Backend.Mach.parent_sp stack) at hlinkTarget
    rw [hreturnTarget]
    dsimp only
    rw [hlinkTarget]
    dsimp only
    rw [hfreeTarget]
  · apply agree_nextinstr
    apply agree_change_sp
    · exact agree_set_other regs _ targetRegs .RA _ hagree rfl
    · exact parent_sp_def (Genv.globalenv prog) stack hstack

private theorem simulation_Mreturn_case
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (prog : CompCert4Lean.Backend.Mach.program) (tprog : program)
    (hprog : match_prog prog tprog)
    (stack : List CompCert4Lean.Backend.Mach.stackframe) (fb stk : block) (offset : ptrofs)
    (fn : CompCert4Lean.Backend.Mach.function) (code : CompCert4Lean.Backend.Mach.code)
    (regs : CompCert4Lean.Backend.Mach.regset) (memory memory' : mem)
    (hfind : Genv.find_funct_ptr (Genv.globalenv prog) fb = some (.Internal fn))
    (hlink : CompCert4Lean.Backend.Mach.load_stack memory (.Vptr stk offset)
      Tptr fn.fn_link_ofs = some (CompCert4Lean.Backend.Mach.parent_sp stack))
    (hreturn : CompCert4Lean.Backend.Mach.load_stack memory (.Vptr stk offset)
      Tptr fn.fn_retaddr_ofs = some (CompCert4Lean.Backend.Mach.parent_ra stack))
    (hfree : Mem.free memory stk .Z0 fn.fn_stacksize = some memory') (target : state)
    (hmatch : match_states prog
      (.State stack fb (.Vptr stk offset) (.Mreturn :: code) regs memory) target) :
    ∃ target', plus (CompCert4Lean.X86.Asm.step cfg xi) (Genv.globalenv tprog)
      target E0 target' ∧
      match_states prog (.Returnstate stack regs memory') target' := by
  cases hmatch with
  | match_states_intro _ _ _ _ ep _ _ targetMemory targetRegs foundFn targetFn targetCode
      hstack hfound hext hatpc hagree hparent =>
    have heq : foundFn = fn := by
      cases hfound.symm.trans hfind
      rfl
    subst foundFn
    generalize hpc : targetRegs .PC = pc at hatpc
    cases hatpc with
    | intro _ ofs _ _ _ _ _ hfind' htrans hcode htail =>
      obtain ⟨continuation, hcontinuation, htranslation⟩ :=
        simulation_translation_cons fn .Mreturn code ep targetCode hcode
      have hcodeEq : targetCode =
          .Pfreeframe fn.fn_stacksize fn.fn_retaddr_ofs fn.fn_link_ofs :: .Pret :: continuation :=
        (CompCert4Lean.Common.Errors.res.OK.inj htranslation).symm
      subst targetCode
      let middleRegs := nextinstr (Pregmap.set (.IR .RSP)
        (CompCert4Lean.Backend.Mach.parent_sp stack)
        (Pregmap.set .RA (CompCert4Lean.Backend.Mach.parent_ra stack) targetRegs))
      obtain ⟨resultMemory, hext', hfreeTarget, hagreeMiddle⟩ :=
        simulation_freeframe prog (Genv.globalenv tprog) targetFn stack fn stk offset
          regs targetRegs memory targetMemory memory' hstack hext hagree hlink hreturn hfree
      let resultRegs := Pregmap.set .PC (CompCert4Lean.Backend.Mach.parent_ra stack) middleRegs
      have hpcMiddle : middleRegs .PC = .Vptr fb (Ptrofs.add ofs Ptrofs.one) := by
        change Val.offset_ptr (targetRegs .PC) Ptrofs.one = _
        rw [hpc]
        rfl
      have hfindTarget := functions_transl prog tprog hprog fb fn targetFn hfind htrans
      refine ⟨.State resultRegs resultMemory, ?_, ?_⟩
      · refine plus_two _ _ _ _ _ E0 (.State middleRegs resultMemory) E0 _ _ ?_ ?_ rfl
        · exact exec_step_internal fb ofs targetFn _ targetRegs targetMemory middleRegs
            resultMemory hpc hfindTarget (find_instr_tail _ _ _ _ htail) hfreeTarget
        · exact exec_step_internal fb _ targetFn .Pret middleRegs resultMemory resultRegs
            resultMemory hpcMiddle hfindTarget
            (find_instr_tail _ _ _ _ (code_tail_next_int _ _ _ _
              (transf_function_no_overflow fn targetFn htrans) htail)) rfl
      · exact match_states.match_states_return stack regs memory' resultMemory resultRegs
          hstack hext' (agree_set_other regs _ middleRegs .PC _ hagreeMiddle rfl) rfl

private theorem simulation_tailcall_case
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (prog : CompCert4Lean.Backend.Mach.program) (tprog : program)
    (hprog : match_prog prog tprog)
    (stack : List CompCert4Lean.Backend.Mach.stackframe) (fb stk : block) (offset : ptrofs)
    (fn : CompCert4Lean.Backend.Mach.function) (sig : signature)
    (ros : Sum CompCert4Lean.X86.Machregs.mreg ident)
    (code : CompCert4Lean.Backend.Mach.code)
    (regs : CompCert4Lean.Backend.Mach.regset) (memory memory' : mem) (callee : block)
    (hcallee : CompCert4Lean.Backend.Mach.find_function_ptr (Genv.globalenv prog) ros regs = some callee)
    (hfind : Genv.find_funct_ptr (Genv.globalenv prog) fb = some (.Internal fn))
    (hlink : CompCert4Lean.Backend.Mach.load_stack memory (.Vptr stk offset)
      Tptr fn.fn_link_ofs = some (CompCert4Lean.Backend.Mach.parent_sp stack))
    (hreturn : CompCert4Lean.Backend.Mach.load_stack memory (.Vptr stk offset)
      Tptr fn.fn_retaddr_ofs = some (CompCert4Lean.Backend.Mach.parent_ra stack))
    (hfree : Mem.free memory stk .Z0 fn.fn_stacksize = some memory') (target : state)
    (hmatch : match_states prog
      (.State stack fb (.Vptr stk offset) (.Mtailcall sig ros :: code) regs memory) target) :
    ∃ target', plus (CompCert4Lean.X86.Asm.step cfg xi) (Genv.globalenv tprog)
      target E0 target' ∧
      match_states prog (.Callstate stack callee regs memory') target' := by
  cases hmatch with
  | match_states_intro _ _ _ _ ep _ _ targetMemory targetRegs foundFn targetFn targetCode
      hstack hfound hext hatpc hagree hparent =>
    have heq : foundFn = fn := by
      cases hfound.symm.trans hfind
      rfl
    subst foundFn
    generalize hpc : targetRegs .PC = pc at hatpc
    cases hatpc with
    | intro _ ofs _ _ _ _ _ hfind' htrans hcode htail =>
      obtain ⟨continuation, hcontinuation, htranslation⟩ :=
        simulation_translation_cons fn (.Mtailcall sig ros) code ep targetCode hcode
      let middleRegs := nextinstr (Pregmap.set (.IR .RSP)
        (CompCert4Lean.Backend.Mach.parent_sp stack)
        (Pregmap.set .RA (CompCert4Lean.Backend.Mach.parent_ra stack) targetRegs))
      obtain ⟨resultMemory, hext', hfreeTarget, hagreeMiddle⟩ :=
        simulation_freeframe prog (Genv.globalenv tprog) targetFn stack fn stk offset
          regs targetRegs memory targetMemory memory' hstack hext hagree hlink hreturn hfree
      let resultRegs := Pregmap.set .PC (.Vptr callee Ptrofs.zero) middleRegs
      obtain ⟨jumpInstr, hcodeEq, hstep⟩ : ∃ jumpInstr,
          targetCode = .Pfreeframe fn.fn_stacksize fn.fn_retaddr_ofs fn.fn_link_ofs ::
            jumpInstr :: continuation ∧
          exec_instr (Genv.globalenv tprog) targetFn jumpInstr middleRegs resultMemory =
            .Next resultRegs resultMemory := by
        cases ros with
        | inl sourceReg =>
          change CompCert4Lean.Common.Errors.bind (ireg_of sourceReg)
            (fun reg => .OK (.Pfreeframe fn.fn_stacksize fn.fn_retaddr_ofs fn.fn_link_ofs ::
              .Pjmp_r reg sig :: continuation)) = .OK targetCode at htranslation
          cases hreg : ireg_of sourceReg with
          | Error message => simp [hreg, CompCert4Lean.Common.Errors.bind] at htranslation
          | OK reg =>
            simp only [hreg, CompCert4Lean.Common.Errors.bind] at htranslation
            refine ⟨.Pjmp_r reg sig, (CompCert4Lean.Common.Errors.res.OK.inj htranslation).symm, ?_⟩
            have harg := simulation_indirect_target _ regs _ targetRegs sourceReg reg
              callee hagree hreg hcallee
            have hnotsp : preg.IR reg ≠ .IR .RSP := by
              rw [← ireg_of_eq sourceReg reg hreg]
              exact preg_of_not_SP sourceReg
            have hargMiddle : middleRegs (.IR reg) = .Vptr callee Ptrofs.zero := by
              simpa [middleRegs, nextinstr, Pregmap.set, hnotsp] using harg
            change outcome.Next (Pregmap.set .PC (middleRegs (.IR reg)) middleRegs) resultMemory = _
            rw [hargMiddle]
        | inr symbol =>
          refine ⟨.Pjmp_s symbol sig,
            (CompCert4Lean.Common.Errors.res.OK.inj htranslation).symm, ?_⟩
          change Genv.find_symbol (Genv.globalenv prog) symbol = some callee at hcallee
          dsimp only [exec_instr, Pregmap.get]
          simp only [Genv.symbol_address, symbols_preserved prog tprog hprog, hcallee]
          rfl
      subst targetCode
      have hpcMiddle : middleRegs .PC = .Vptr fb (Ptrofs.add ofs Ptrofs.one) := by
        change Val.offset_ptr (targetRegs .PC) Ptrofs.one = _
        rw [hpc]
        rfl
      have hfindTarget := functions_transl prog tprog hprog fb fn targetFn hfind htrans
      refine ⟨.State resultRegs resultMemory, ?_, ?_⟩
      · refine plus_two _ _ _ _ _ E0 (.State middleRegs resultMemory) E0 _ _ ?_ ?_ rfl
        · exact exec_step_internal fb ofs targetFn _ targetRegs targetMemory middleRegs
            resultMemory hpc hfindTarget (find_instr_tail _ _ _ _ htail) hfreeTarget
        · exact exec_step_internal fb _ targetFn jumpInstr middleRegs resultMemory resultRegs
            resultMemory hpcMiddle hfindTarget
            (find_instr_tail _ _ _ _ (code_tail_next_int _ _ _ _
              (transf_function_no_overflow fn targetFn htrans) htail)) hstep
      · exact match_states.match_states_call stack callee regs memory' resultMemory resultRegs
          hstack hext' (agree_set_other regs _ middleRegs .PC _ hagreeMiddle rfl) rfl rfl

omit binary64_certificate binary32_certificate in
private theorem simulation_function_code
    (fn : CompCert4Lean.Backend.Mach.function) (targetFn : function)
    (htrans : transf_function fn = .OK targetFn) :
    ∃ continuation, transl_code fn fn.fn_code true = .OK continuation ∧
      targetFn.fn_code =
        .Pallocframe fn.fn_stacksize fn.fn_retaddr_ofs fn.fn_link_ofs :: continuation := by
  have hfunction : transl_function fn = .OK targetFn := by
    unfold transf_function at htrans
    cases htf : transl_function fn with
    | Error message => rw [htf] at htrans; cases htrans
    | OK translated =>
      rw [htf] at htrans
      change (match CompCert4Lean.Lib.Coqlib.zlt Ptrofs.max_unsigned
        (CompCert4Lean.Lib.Coqlib.list_length_z translated.fn_code) with
        | .left _ => _
        | .right _ => _) = CompCert4Lean.Common.Errors.res.OK targetFn at htrans
      split at htrans
      · cases htrans
      · cases htrans
        rfl
  unfold transl_function at hfunction
  rw [transl_code'_transl_code] at hfunction
  cases hcode : transl_code fn fn.fn_code true with
  | Error message => rw [hcode] at hfunction; cases hfunction
  | OK continuation =>
    rw [hcode] at hfunction
    cases hfunction
    exact ⟨continuation, rfl, rfl⟩

private theorem simulation_internal_case
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (prog : CompCert4Lean.Backend.Mach.program) (tprog : program)
    (hprog : match_prog prog tprog)
    (stack : List CompCert4Lean.Backend.Mach.stackframe) (fb stk : block)
    (fn : CompCert4Lean.Backend.Mach.function)
    (regs : CompCert4Lean.Backend.Mach.regset) (memory memory1 memory2 memory3 : mem)
    (hfind : Genv.find_funct_ptr (Genv.globalenv prog) fb = some (.Internal fn))
    (halloc : Mem.alloc memory .Z0 fn.fn_stacksize = (memory1, stk))
    (hlink : CompCert4Lean.Backend.Mach.store_stack memory1 (.Vptr stk Ptrofs.zero)
      Tptr fn.fn_link_ofs (CompCert4Lean.Backend.Mach.parent_sp stack) = some memory2)
    (hreturn : CompCert4Lean.Backend.Mach.store_stack memory2 (.Vptr stk Ptrofs.zero)
      Tptr fn.fn_retaddr_ofs (CompCert4Lean.Backend.Mach.parent_ra stack) = some memory3)
    (target : state)
    (hmatch : match_states prog (.Callstate stack fb regs memory) target) :
    ∃ target', plus (CompCert4Lean.X86.Asm.step cfg xi) (Genv.globalenv tprog)
      target E0 target' ∧
      match_states prog (.State stack fb (.Vptr stk Ptrofs.zero) fn.fn_code
        (CompCert4Lean.Backend.Mach.undef_regs
          CompCert4Lean.X86.Machregs.destroyed_at_function_entry regs) memory3) target' := by
  cases hmatch with
  | match_states_call _ _ _ _ targetMemory targetRegs hstack hext hagree hpc hra =>
    obtain ⟨translated, htranslated, htranslation⟩ :=
      functions_translated prog tprog hprog fb (.Internal fn) hfind
    unfold CompCert4Lean.X86.Asmgen.transf_fundef transf_partial_fundef at htranslation
    dsimp only at htranslation
    cases htrans : transf_function fn with
    | Error message => rw [htrans] at htranslation; cases htranslation
    | OK targetFn =>
      rw [htrans] at htranslation
      cases htranslation
      obtain ⟨continuation, hcontinuation, hcode⟩ := simulation_function_code fn targetFn htrans
      obtain ⟨targetMemory1, hallocTarget, hext1⟩ := Mem.alloc_extends
        memory targetMemory .Z0 fn.fn_stacksize stk memory1 .Z0 fn.fn_stacksize hext halloc
        (ZArith.BinInt.Z.le_refl _) (ZArith.BinInt.Z.le_refl _)
      obtain ⟨targetMemory2, hlinkTarget, hext2⟩ := Mem.storev_extends
        (chunk_of_type Tptr) memory1 targetMemory1 _ _ memory2 _ _ hext1 hlink
        (.lessdef_refl _) (.lessdef_refl _)
      obtain ⟨targetMemory3, hreturnTarget, hext3⟩ := Mem.storev_extends
        (chunk_of_type Tptr) memory2 targetMemory2 _ _ memory3 _ _ hext2 hreturn
        (.lessdef_refl _) (.lessdef_refl _)
      let resultRegs := nextinstr (Pregmap.set (.IR .RAX) (targetRegs (.IR .RSP))
        (Pregmap.set (.IR .RSP) (.Vptr stk Ptrofs.zero) targetRegs))
      have hstep : exec_instr (Genv.globalenv tprog) targetFn
          (.Pallocframe fn.fn_stacksize fn.fn_retaddr_ofs fn.fn_link_ofs)
          targetRegs targetMemory = .Next resultRegs targetMemory3 := by
        dsimp only [exec_instr, Pregmap.get]
        rw [hallocTarget]
        dsimp only
        have hsp : targetRegs (.IR .RSP) = CompCert4Lean.Backend.Mach.parent_sp stack := hagree.agree_sp
        rw [hsp]
        change Mem.storev Mptr targetMemory1 _ _ = some targetMemory2 at hlinkTarget
        rw [hlinkTarget]
        dsimp only
        rw [hra]
        change Mem.storev Mptr targetMemory2 _ _ = some targetMemory3 at hreturnTarget
        rw [hreturnTarget]
        dsimp only
        dsimp only [resultRegs]
        rw [hsp]
      have hresultPC : resultRegs .PC = .Vptr fb (Ptrofs.add Ptrofs.zero Ptrofs.one) := by
        change Val.offset_ptr (targetRegs .PC) Ptrofs.one = _
        rw [hpc]
        rfl
      refine ⟨.State resultRegs targetMemory3, ?_, ?_⟩
      · apply plus_one
        apply exec_step_internal fb Ptrofs.zero targetFn _ targetRegs targetMemory
          resultRegs targetMemory3 hpc htranslated
        · rw [hcode]
          rfl
        · exact hstep
      · apply match_states.match_states_intro stack fb (.Vptr stk Ptrofs.zero)
          fn.fn_code true _ memory3 targetMemory3 resultRegs fn targetFn continuation
          hstack hfind hext3
        · rw [hresultPC]
          apply transl_code_at_pc.intro fb _ fn fn.fn_code true targetFn continuation
            hfind htrans hcontinuation
          apply code_tail_next_int targetFn.fn_code Ptrofs.zero
            (.Pallocframe fn.fn_stacksize fn.fn_retaddr_ofs fn.fn_link_ofs) continuation
            (transf_function_no_overflow fn targetFn htrans)
          rw [hcode]
          constructor
        · apply agree_nextinstr
          apply agree_undef_regs regs (.Vptr stk Ptrofs.zero) _
            (Pregmap.set (.IR .RSP) (.Vptr stk Ptrofs.zero) targetRegs)
          · exact agree_change_sp regs _ targetRegs _ hagree (by intro impossible; cases impossible)
          · intro reg hdata hnotin
            change reg ≠ .IR .RAX ∧ reg ≠ .ST0 at hnotin
            simp [Pregmap.set, hnotin.1]
        · intro htrue
          change targetRegs (.IR .RSP) = _
          exact hagree.agree_sp

omit binary64_certificate binary32_certificate in
private theorem simulation_args_lessdef
    (regs : CompCert4Lean.Backend.Mach.regset) (sp : val) (targetRegs : regset)
    (hagree : agree regs sp targetRegs) (args : List CompCert4Lean.X86.Machregs.mreg) :
    Val.lessdef_list (args.map regs) (args.map (fun reg => targetRegs (preg_of reg))) := by
  induction args with
  | nil => exact Val.lessdef_list_nil
  | cons reg rest inductionHypothesis =>
    exact Val.lessdef_list_cons _ _ _ _ (hagree.agree_mregs reg) inductionHypothesis

private theorem simulation_op_case
    (operationCorrect : CompCert4Lean.X86.Asmgenproof1.transl_op_correctStatement)
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (prog : CompCert4Lean.Backend.Mach.program) (tprog : program)
    (hprog : match_prog prog tprog)
    (stack : List CompCert4Lean.Backend.Mach.stackframe) (fb : block) (sp : val)
    (op : CompCert4Lean.X86.Op.operation) (args : List CompCert4Lean.X86.Machregs.mreg)
    (dst : CompCert4Lean.X86.Machregs.mreg) (code : CompCert4Lean.Backend.Mach.code)
    (regs : CompCert4Lean.Backend.Mach.regset) (memory : mem) (value : val)
    (heval : CompCert4Lean.X86.Op.eval_operation (Genv.globalenv prog) sp op
      (args.map regs) memory = some value) (target : state)
    (hmatch : match_states prog
      (.State stack fb sp (.Mop op args dst :: code) regs memory) target) :
    ∃ target', plus (CompCert4Lean.X86.Asm.step cfg xi) (Genv.globalenv tprog)
      target E0 target' ∧
      match_states prog (.State stack fb sp code
        (CompCert4Lean.Backend.Mach.Regmap.set dst value
          (CompCert4Lean.Backend.Mach.undef_regs
            (CompCert4Lean.X86.Machregs.destroyed_by_op op) regs)) memory) target' := by
  cases hmatch with
  | match_states_intro _ _ _ _ ep _ _ targetMemory targetRegs fn targetFn targetCode
      hstack hfind hext hatpc hagree hparent =>
    have hevalTarget := (CompCert4Lean.X86.Op.eval_operation_preserved _ _ _ _
      (Genv.globalenv prog) (Genv.globalenv tprog) (symbols_preserved prog tprog hprog)
      sp op (args.map regs) memory).trans heval
    obtain ⟨targetValue, hevalTarget, hvalue⟩ :=
      CompCert4Lean.X86.Op.eval_operation_lessdef _ _ (Genv.globalenv tprog)
        sp op _ _ value memory targetMemory (simulation_args_lessdef regs sp targetRegs hagree args)
        hext hevalTarget
    have hsp : sp = targetRegs (.IR .RSP) := hagree.agree_sp.symm
    rw [hsp] at hevalTarget
    apply exec_straight_steps cfg xi prog tprog hprog stack fb fn targetRegs
      (.Mop op args dst) code ep targetFn targetCode targetMemory memory targetMemory
      sp _ hstack hext hfind hatpc
    intro continuation translated htrans
    obtain ⟨resultRegs, hexec, hresult, hother⟩ := operationCorrect
      (Genv.globalenv tprog) targetFn op args dst continuation translated targetRegs
      targetMemory targetValue htrans (by simpa only [List.map_map] using hevalTarget)
    refine ⟨resultRegs, hexec, ?_, ?_⟩
    · exact agree_set_undef_mreg regs sp targetRegs dst value _ resultRegs hagree
        (Val.lessdef_trans _ _ _ hvalue hresult) hother
    · intro impossible
      cases impossible

private theorem simulation_load_case
    (loadCorrect : CompCert4Lean.X86.Asmgenproof1.transl_load_correctStatement)
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (prog : CompCert4Lean.Backend.Mach.program) (tprog : program)
    (hprog : match_prog prog tprog)
    (stack : List CompCert4Lean.Backend.Mach.stackframe) (fb : block) (sp : val)
    (chunk : memory_chunk) (addr : CompCert4Lean.X86.Op.addressing)
    (args : List CompCert4Lean.X86.Machregs.mreg) (dst : CompCert4Lean.X86.Machregs.mreg)
    (code : CompCert4Lean.Backend.Mach.code)
    (regs : CompCert4Lean.Backend.Mach.regset) (memory : mem) (address value : val)
    (haddr : CompCert4Lean.X86.Op.eval_addressing (Genv.globalenv prog) sp addr
      (args.map regs) = some address)
    (hload : Mem.loadv chunk memory address = some value) (target : state)
    (hmatch : match_states prog
      (.State stack fb sp (.Mload chunk addr args dst :: code) regs memory) target) :
    ∃ target', plus (CompCert4Lean.X86.Asm.step cfg xi) (Genv.globalenv tprog)
      target E0 target' ∧
      match_states prog (.State stack fb sp code
        (CompCert4Lean.Backend.Mach.Regmap.set dst value
          (CompCert4Lean.Backend.Mach.undef_regs
            (CompCert4Lean.X86.Machregs.destroyed_by_load chunk addr) regs)) memory) target' := by
  cases hmatch with
  | match_states_intro _ _ _ _ ep _ _ targetMemory targetRegs fn targetFn targetCode
      hstack hfind hext hatpc hagree hparent =>
    have haddrTarget := (CompCert4Lean.X86.Op.eval_addressing_preserved _ _ _ _
      (Genv.globalenv prog) (Genv.globalenv tprog) (symbols_preserved prog tprog hprog)
      sp addr (args.map regs)).trans haddr
    obtain ⟨targetAddress, haddrTarget, haddress⟩ :=
      CompCert4Lean.X86.Op.eval_addressing_lessdef _ _ (Genv.globalenv tprog)
        sp addr _ _ address (simulation_args_lessdef regs sp targetRegs hagree args) haddrTarget
    have hsp : sp = targetRegs (.IR .RSP) := hagree.agree_sp.symm
    rw [hsp] at haddrTarget
    obtain ⟨targetValue, hloadTarget, hvalue⟩ := Mem.loadv_extends chunk memory
      targetMemory address targetAddress value hext hload haddress
    apply exec_straight_steps cfg xi prog tprog hprog stack fb fn targetRegs
      (.Mload chunk addr args dst) code ep targetFn targetCode targetMemory memory targetMemory
      sp _ hstack hext hfind hatpc
    intro continuation translated htrans
    obtain ⟨resultRegs, hexec, hresult, hother⟩ := loadCorrect
      (Genv.globalenv tprog) targetFn chunk addr args dst continuation translated targetRegs
      targetMemory targetAddress targetValue htrans
      (by simpa only [List.map_map] using haddrTarget) hloadTarget
    refine ⟨resultRegs, hexec, ?_, ?_⟩
    · apply agree_set_undef_mreg regs sp targetRegs dst value _ resultRegs hagree
      · rwa [hresult]
      · intro reg hdata hne hnotin
        exact hother reg hdata hne
    · intro impossible
      cases impossible

private theorem simulation_store_case
    (storeCorrect : CompCert4Lean.X86.Asmgenproof1.transl_store_correctStatement)
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (prog : CompCert4Lean.Backend.Mach.program) (tprog : program)
    (hprog : match_prog prog tprog)
    (stack : List CompCert4Lean.Backend.Mach.stackframe) (fb : block) (sp : val)
    (chunk : memory_chunk) (addr : CompCert4Lean.X86.Op.addressing)
    (args : List CompCert4Lean.X86.Machregs.mreg) (src : CompCert4Lean.X86.Machregs.mreg)
    (code : CompCert4Lean.Backend.Mach.code)
    (regs : CompCert4Lean.Backend.Mach.regset) (memory memory' : mem) (address : val)
    (haddr : CompCert4Lean.X86.Op.eval_addressing (Genv.globalenv prog) sp addr
      (args.map regs) = some address)
    (hstore : Mem.storev chunk memory address (regs src) = some memory') (target : state)
    (hmatch : match_states prog
      (.State stack fb sp (.Mstore chunk addr args src :: code) regs memory) target) :
    ∃ target', plus (CompCert4Lean.X86.Asm.step cfg xi) (Genv.globalenv tprog)
      target E0 target' ∧
      match_states prog (.State stack fb sp code
        (CompCert4Lean.Backend.Mach.undef_regs
          (CompCert4Lean.X86.Machregs.destroyed_by_store chunk addr) regs) memory') target' := by
  cases hmatch with
  | match_states_intro _ _ _ _ ep _ _ targetMemory targetRegs fn targetFn targetCode
      hstack hfind hext hatpc hagree hparent =>
    have haddrTarget := (CompCert4Lean.X86.Op.eval_addressing_preserved _ _ _ _
      (Genv.globalenv prog) (Genv.globalenv tprog) (symbols_preserved prog tprog hprog)
      sp addr (args.map regs)).trans haddr
    obtain ⟨targetAddress, haddrTarget, haddress⟩ :=
      CompCert4Lean.X86.Op.eval_addressing_lessdef _ _ (Genv.globalenv tprog)
        sp addr _ _ address (simulation_args_lessdef regs sp targetRegs hagree args) haddrTarget
    have hsp : sp = targetRegs (.IR .RSP) := hagree.agree_sp.symm
    rw [hsp] at haddrTarget
    obtain ⟨resultMemory, hstoreTarget, hext'⟩ := Mem.storev_extends chunk memory
      targetMemory address (regs src) memory' targetAddress (targetRegs (preg_of src))
      hext hstore haddress (hagree.agree_mregs src)
    apply exec_straight_steps cfg xi prog tprog hprog stack fb fn targetRegs
      (.Mstore chunk addr args src) code ep targetFn targetCode targetMemory memory' resultMemory
      sp _ hstack hext' hfind hatpc
    intro continuation translated htrans
    obtain ⟨resultRegs, hexec, hother⟩ := storeCorrect
      (Genv.globalenv tprog) targetFn chunk addr args src continuation translated targetRegs
      targetMemory targetAddress resultMemory htrans
      (by simpa only [List.map_map] using haddrTarget) hstoreTarget
    refine ⟨resultRegs, hexec, ?_, ?_⟩
    · exact agree_undef_regs regs sp _ targetRegs resultRegs hagree hother
    · intro impossible
      cases impossible

private theorem simulation_jcc_true
    (ge : genv) (fn : function) (cond : extcond) (lbl : label)
    (code continuation : CompCert4Lean.X86.Asm.code) (initial tested : regset) (memory : mem)
    (regs : CompCert4Lean.Backend.Mach.regset) (sp : val)
    (hexec : exec_straight ge fn code initial memory (mk_jcc cond lbl continuation) tested memory)
    (hagree : agree regs sp tested)
    (hcond : CompCert4Lean.X86.Asmgenproof1.eval_extcond cond tested = some true) :
    ∃ jump rest result,
      exec_straight ge fn code initial memory (jump :: rest) result memory ∧
      agree regs sp result ∧
      exec_instr ge fn jump result memory = goto_label fn lbl result memory := by
  cases cond with
  | Cond_base test =>
    refine ⟨.Pjcc test lbl, continuation, tested, hexec, hagree, ?_⟩
    dsimp only [exec_instr]
    change eval_testcond test tested = some true at hcond
    rw [hcond]
  | Cond_or firstTest secondTest =>
    change (match eval_testcond firstTest tested, eval_testcond secondTest tested with
      | some first, some second => some (first || second)
      | _, _ => none) = some true at hcond
    cases hfirst : eval_testcond firstTest tested with
    | none => simp [hfirst] at hcond
    | some firstValue =>
      cases hsecond : eval_testcond secondTest tested with
      | none => simp [hfirst, hsecond] at hcond
      | some secondValue =>
        cases firstValue with
        | true =>
          refine ⟨.Pjcc firstTest lbl, .Pjcc secondTest lbl :: continuation,
            tested, hexec, hagree, ?_⟩
          dsimp only [exec_instr]
          rw [hfirst]
        | false =>
          have hsecondValue : secondValue = true := by simpa [hfirst, hsecond] using hcond
          subst secondValue
          refine ⟨.Pjcc secondTest lbl, continuation, nextinstr tested, ?_,
            agree_nextinstr regs sp tested hagree, ?_⟩
          · apply exec_straight_trans _ _ _ _ _ _ _ _ _ _ _ hexec
            apply exec_straight_one _ _ _ _ _ _ ?_ rfl
            dsimp only [exec_instr]
            rw [hfirst]
          · dsimp only [exec_instr]
            rw [CompCert4Lean.X86.Asmgenproof1.eval_testcond_nextinstr, hsecond]
  | Cond_and firstTest secondTest =>
    change (match eval_testcond firstTest tested, eval_testcond secondTest tested with
      | some first, some second => some (first && second)
      | _, _ => none) = some true at hcond
    cases hfirst : eval_testcond firstTest tested with
    | none => simp [hfirst] at hcond
    | some firstValue =>
      cases hsecond : eval_testcond secondTest tested with
      | none => simp [hfirst, hsecond] at hcond
      | some secondValue =>
        have hvalues : firstValue = true ∧ secondValue = true := by
          simpa [hfirst, hsecond] using hcond
        rcases hvalues with ⟨rfl, rfl⟩
        refine ⟨.Pjcc2 firstTest secondTest lbl, continuation, tested, hexec, hagree, ?_⟩
        dsimp only [exec_instr]
        rw [hfirst, hsecond]

private theorem simulation_jcc_false
    (ge : genv) (fn : function) (cond : extcond) (lbl : label)
    (code continuation : CompCert4Lean.X86.Asm.code) (initial tested : regset) (memory : mem)
    (regs : CompCert4Lean.Backend.Mach.regset) (sp : val)
    (hexec : exec_straight ge fn code initial memory (mk_jcc cond lbl continuation) tested memory)
    (hagree : agree regs sp tested)
    (hcond : CompCert4Lean.X86.Asmgenproof1.eval_extcond cond tested = some false) :
    ∃ result, exec_straight ge fn code initial memory continuation result memory ∧
      agree regs sp result := by
  cases cond with
  | Cond_base test =>
    refine ⟨nextinstr tested, ?_, agree_nextinstr regs sp tested hagree⟩
    apply exec_straight_trans _ _ _ _ _ _ _ _ _ _ _ hexec
    apply exec_straight_one _ _ _ _ _ _ ?_ rfl
    dsimp only [exec_instr]
    change eval_testcond test tested = some false at hcond
    rw [hcond]
  | Cond_or firstTest secondTest =>
    change (match eval_testcond firstTest tested, eval_testcond secondTest tested with
      | some first, some second => some (first || second)
      | _, _ => none) = some false at hcond
    cases hfirst : eval_testcond firstTest tested with
    | none => simp [hfirst] at hcond
    | some firstValue =>
      cases hsecond : eval_testcond secondTest tested with
      | none => simp [hfirst, hsecond] at hcond
      | some secondValue =>
        have hvalues : firstValue = false ∧ secondValue = false := by
          simpa [hfirst, hsecond] using hcond
        rcases hvalues with ⟨rfl, rfl⟩
        refine ⟨nextinstr (nextinstr tested), ?_,
          agree_nextinstr regs sp _ (agree_nextinstr regs sp tested hagree)⟩
        apply exec_straight_trans _ _ _ _ _ _ _ _ _ _ _ hexec
        apply exec_straight_two _ _ _ _ _ tested memory (nextinstr tested) memory
          (nextinstr (nextinstr tested)) memory ?_ ?_ rfl rfl
        · dsimp only [exec_instr]
          rw [hfirst]
        · dsimp only [exec_instr]
          rw [CompCert4Lean.X86.Asmgenproof1.eval_testcond_nextinstr, hsecond]
  | Cond_and firstTest secondTest =>
    change (match eval_testcond firstTest tested, eval_testcond secondTest tested with
      | some first, some second => some (first && second)
      | _, _ => none) = some false at hcond
    cases hfirst : eval_testcond firstTest tested with
    | none => simp [hfirst] at hcond
    | some firstValue =>
      cases hsecond : eval_testcond secondTest tested with
      | none => simp [hfirst, hsecond] at hcond
      | some secondValue =>
        have hvalues : (firstValue && secondValue) = false := by
          simpa [hfirst, hsecond] using hcond
        refine ⟨nextinstr tested, ?_, agree_nextinstr regs sp tested hagree⟩
        apply exec_straight_trans _ _ _ _ _ _ _ _ _ _ _ hexec
        apply exec_straight_one _ _ _ _ _ _ ?_ rfl
        dsimp only [exec_instr]
        rw [hfirst, hsecond]
        cases firstValue <;> cases secondValue <;> cases hvalues <;> rfl

private theorem simulation_cond_true_case
    (conditionCorrect : CompCert4Lean.X86.Asmgenproof1.transl_cond_correctStatement)
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (prog : CompCert4Lean.Backend.Mach.program) (tprog : program)
    (hprog : match_prog prog tprog)
    (stack : List CompCert4Lean.Backend.Mach.stackframe) (fb : block) (sp : val)
    (fn : CompCert4Lean.Backend.Mach.function) (cond : CompCert4Lean.X86.Op.condition)
    (args : List CompCert4Lean.X86.Machregs.mreg) (lbl : label)
    (code destination : CompCert4Lean.Backend.Mach.code)
    (regs : CompCert4Lean.Backend.Mach.regset) (memory : mem)
    (heval : CompCert4Lean.X86.Op.eval_condition cond (args.map regs) memory = some true)
    (hfind : Genv.find_funct_ptr (Genv.globalenv prog) fb = some (.Internal fn))
    (hlabel : CompCert4Lean.Backend.Mach.find_label lbl fn.fn_code = some destination)
    (target : state)
    (hmatch : match_states prog
      (.State stack fb sp (.Mcond cond args lbl :: code) regs memory) target) :
    ∃ target', plus (CompCert4Lean.X86.Asm.step cfg xi) (Genv.globalenv tprog)
      target E0 target' ∧
      match_states prog (.State stack fb sp destination
        (CompCert4Lean.Backend.Mach.undef_regs
          (CompCert4Lean.X86.Machregs.destroyed_by_cond cond) regs) memory) target' := by
  cases hmatch with
  | match_states_intro _ _ _ _ ep _ _ targetMemory targetRegs foundFn targetFn targetCode
      hstack hfound hext hatpc hagree hparent =>
    have heq : foundFn = fn := by
      cases hfound.symm.trans hfind
      rfl
    subst foundFn
    have hevalTarget : CompCert4Lean.X86.Op.eval_condition cond
        (args.map (fun reg => targetRegs (preg_of reg))) targetMemory = some true := by
      simpa only [List.map_map] using CompCert4Lean.X86.Op.eval_condition_lessdef
        cond _ _ true memory targetMemory (simulation_args_lessdef regs sp targetRegs hagree args) hext heval
    apply exec_straight_steps_goto cfg xi prog tprog hprog stack fb fn targetRegs
      (.Mcond cond args lbl) code ep targetFn targetCode targetMemory memory targetMemory
      sp _ lbl destination hstack hext hfind hlabel hatpc rfl
    intro continuation translated htrans
    obtain ⟨tested, hexec, hcondition, hother⟩ := conditionCorrect
      (Genv.globalenv tprog) targetFn cond args (mk_jcc (testcond_for_condition cond) lbl continuation)
      translated targetRegs targetMemory htrans
    rw [hevalTarget] at hcondition
    exact simulation_jcc_true _ _ _ _ _ _ _ _ _ _ _ hexec
      (agree_exten regs sp targetRegs tested hagree hother) hcondition.1

private theorem simulation_cond_false_case
    (conditionCorrect : CompCert4Lean.X86.Asmgenproof1.transl_cond_correctStatement)
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (prog : CompCert4Lean.Backend.Mach.program) (tprog : program)
    (hprog : match_prog prog tprog)
    (stack : List CompCert4Lean.Backend.Mach.stackframe) (fb : block) (sp : val)
    (cond : CompCert4Lean.X86.Op.condition)
    (args : List CompCert4Lean.X86.Machregs.mreg) (lbl : label)
    (code : CompCert4Lean.Backend.Mach.code)
    (regs : CompCert4Lean.Backend.Mach.regset) (memory : mem)
    (heval : CompCert4Lean.X86.Op.eval_condition cond (args.map regs) memory = some false)
    (target : state)
    (hmatch : match_states prog
      (.State stack fb sp (.Mcond cond args lbl :: code) regs memory) target) :
    ∃ target', plus (CompCert4Lean.X86.Asm.step cfg xi) (Genv.globalenv tprog)
      target E0 target' ∧
      match_states prog (.State stack fb sp code
        (CompCert4Lean.Backend.Mach.undef_regs
          (CompCert4Lean.X86.Machregs.destroyed_by_cond cond) regs) memory) target' := by
  cases hmatch with
  | match_states_intro _ _ _ _ ep _ _ targetMemory targetRegs fn targetFn targetCode
      hstack hfind hext hatpc hagree hparent =>
    have hevalTarget : CompCert4Lean.X86.Op.eval_condition cond
        (args.map (fun reg => targetRegs (preg_of reg))) targetMemory = some false := by
      simpa only [List.map_map] using CompCert4Lean.X86.Op.eval_condition_lessdef
        cond _ _ false memory targetMemory (simulation_args_lessdef regs sp targetRegs hagree args) hext heval
    apply exec_straight_steps cfg xi prog tprog hprog stack fb fn targetRegs
      (.Mcond cond args lbl) code ep targetFn targetCode targetMemory memory targetMemory
      sp _ hstack hext hfind hatpc
    intro continuation translated htrans
    obtain ⟨tested, hexec, hcondition, hother⟩ := conditionCorrect
      (Genv.globalenv tprog) targetFn cond args (mk_jcc (testcond_for_condition cond) lbl continuation)
      translated targetRegs targetMemory htrans
    rw [hevalTarget] at hcondition
    obtain ⟨resultRegs, hexecResult, hagreeResult⟩ := simulation_jcc_false _ _ _ _ _ _ _ _ _ _ _
      hexec (agree_exten regs sp targetRegs tested hagree hother) hcondition.1
    refine ⟨resultRegs, hexecResult, hagreeResult, ?_⟩
    intro impossible
    cases impossible

theorem step_simulation_from_instruction_correctness
    (operationCorrect : CompCert4Lean.X86.Asmgenproof1.transl_op_correctStatement)
    (loadCorrect : CompCert4Lean.X86.Asmgenproof1.transl_load_correctStatement)
    (storeCorrect : CompCert4Lean.X86.Asmgenproof1.transl_store_correctStatement)
    (conditionCorrect : CompCert4Lean.X86.Asmgenproof1.transl_cond_correctStatement) :
    step_simulationStatement := by
  intro cfg xi prog tprog hprog source events source' hstep target hmatch
  cases hstep with
  | exec_Mlabel stack fb sp lbl code regs memory =>
    exact Or.inl (simulation_label_case cfg xi prog tprog hprog stack fb sp lbl code
      regs memory target hmatch)
  | exec_Mgetstack stack fb sp ofs ty dst code regs memory value hload =>
    exact Or.inl (simulation_getstack_case cfg xi prog tprog hprog stack fb sp ofs ty dst
      code regs memory value hload target hmatch)
  | exec_Msetstack stack fb sp src ofs ty code regs memory memory' regs' hstore hregs =>
    subst regs'
    exact Or.inl (simulation_setstack_case cfg xi prog tprog hprog stack fb sp src ofs ty
      code regs memory memory' hstore target hmatch)
  | exec_Mgetparam stack fb fn sp ofs ty dst code regs memory value regs' hfind hlink hload hregs =>
    subst regs'
    exact Or.inl (simulation_getparam_case cfg xi prog tprog hprog stack fb sp fn ofs ty dst
      code regs memory value hfind hlink hload target hmatch)
  | exec_Mop stack fb sp op args dst code regs memory value regs' heval hregs =>
    subst regs'
    exact Or.inl (simulation_op_case operationCorrect cfg xi prog tprog hprog stack fb sp
      op args dst code regs memory value heval target hmatch)
  | exec_Mload stack fb sp chunk addr args dst code regs memory address value regs' haddr hload hregs =>
    subst regs'
    exact Or.inl (simulation_load_case loadCorrect cfg xi prog tprog hprog stack fb sp
      chunk addr args dst code regs memory address value haddr hload target hmatch)
  | exec_Mstore stack fb sp chunk addr args src code regs memory memory' address regs' haddr hstore hregs =>
    subst regs'
    exact Or.inl (simulation_store_case storeCorrect cfg xi prog tprog hprog stack fb sp
      chunk addr args src code regs memory memory' address haddr hstore target hmatch)
  | exec_Mcall stack fb sp sig ros code regs memory fn callee ra hcallee hfind hreturn =>
    exact Or.inl (simulation_call_case cfg xi prog tprog hprog stack fb sp fn sig ros
      code regs memory callee ra hcallee hfind hreturn target hmatch)
  | exec_Mtailcall stack fb stk offset sig ros code regs memory fn callee memory'
      hcallee hfind hlink hreturn hfree =>
    exact Or.inl (simulation_tailcall_case cfg xi prog tprog hprog stack fb stk offset
      fn sig ros code regs memory memory' callee hcallee hfind hlink hreturn hfree target hmatch)
  | exec_Mbuiltin stack fb sp regs memory ef args res code values events value regs' memory'
      hargs hcall hregs =>
    subst regs'
    exact Or.inl (simulation_builtin_case cfg xi prog tprog hprog stack fb sp regs memory
      memory' ef args res code values value events hargs hcall target hmatch)
  | exec_Mgoto stack fb fn sp lbl code regs memory destination hfind hlabel =>
    exact Or.inl (simulation_goto_case cfg xi prog tprog hprog stack fb sp fn lbl code
      destination regs memory hfind hlabel target hmatch)
  | exec_Mcond_true stack fb fn sp cond args lbl code regs memory destination regs'
      heval hfind hlabel hregs =>
    subst regs'
    exact Or.inl (simulation_cond_true_case conditionCorrect cfg xi prog tprog hprog
      stack fb sp fn cond args lbl code destination regs memory heval hfind hlabel target hmatch)
  | exec_Mcond_false stack fb sp cond args lbl code regs memory regs' heval hregs =>
    subst regs'
    exact Or.inl (simulation_cond_false_case conditionCorrect cfg xi prog tprog hprog
      stack fb sp cond args lbl code regs memory heval target hmatch)
  | exec_Mjumptable stack fb fn sp arg table code regs memory index lbl destination regs'
      harg hindex hfind hlabel hregs =>
    subst regs'
    exact Or.inl (simulation_jumptable_case cfg xi prog tprog hprog stack fb sp fn arg table
      lbl index code destination regs memory harg hindex hfind hlabel target hmatch)
  | exec_Mreturn stack fb stk offset code regs memory fn memory' hfind hlink hreturn hfree =>
    exact Or.inl (simulation_Mreturn_case cfg xi prog tprog hprog stack fb stk offset fn
      code regs memory memory' hfind hlink hreturn hfree target hmatch)
  | exec_function_internal stack fb regs memory fn memory1 memory2 memory3 stk regs'
      hfind halloc hlink hreturn hregs =>
    subst regs'
    exact Or.inl (simulation_internal_case cfg xi prog tprog hprog stack fb stk fn regs
      memory memory1 memory2 memory3 hfind halloc hlink hreturn target hmatch)
  | exec_function_external stack fb regs memory events regs' ef args value memory'
      hfind hargs hcall hregs =>
    subst regs'
    exact Or.inl (simulation_external_case cfg xi prog tprog hprog stack fb regs memory
      memory' ef args value events hfind hargs hcall target hmatch)
  | exec_return =>
    refine Or.inr ⟨Nat.zero_lt_succ 0, rfl, ?_⟩
    exact simulation_return_case prog _ _ _ _ _ _ _ _ hmatch

end CompCert4Lean.X86.Asmgenproof

namespace CompCert4Lean.X86.Asmgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem step_simulation
    [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] :
    step_simulationStatement :=
  step_simulation_from_instruction_correctness
    CompCert4Lean.X86.Asmgenproof1.transl_op_correct
    CompCert4Lean.X86.Asmgenproof1.transl_load_correct
    CompCert4Lean.X86.Asmgenproof1.transl_store_correct
    CompCert4Lean.X86.Asmgenproof1.transl_cond_correct

end CompCert4Lean.X86.Asmgenproof
