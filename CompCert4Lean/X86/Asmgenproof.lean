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
