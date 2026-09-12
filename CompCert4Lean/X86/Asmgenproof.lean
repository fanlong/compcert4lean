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
