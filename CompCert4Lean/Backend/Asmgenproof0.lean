import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Backend.Mach
import CompCert4Lean.X86.Asm
import CompCert4Lean.X86.Asmgen
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Errors
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Values
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Integers

namespace CompCert4Lean.Backend.Asmgenproof0

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.X86.Asm
open CompCert4Lean.X86.Asmgen

private abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
private abbrev Mreg := CompCert4Lean.X86.Machregs.mreg
private abbrev Preg := CompCert4Lean.X86.Asm.preg
private abbrev Ireg := CompCert4Lean.X86.Asm.ireg
private abbrev Freg := CompCert4Lean.X86.Asm.freg
private abbrev Val := CompCert4Lean.Common.Values.val
private abbrev Mem := CompCert4Lean.Common.Memory.mem
private abbrev Block := CompCert4Lean.Common.Values.block
private abbrev Loc := CompCert4Lean.Backend.Locations.loc
private abbrev Signature := CompCert4Lean.Common.AST.signature
private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev ExternalCalls := CompCert4Lean.Common.ExternalCalls.ExternalCalls
private abbrev MachCode := CompCert4Lean.Backend.Mach.code
private abbrev MachFunction := CompCert4Lean.Backend.Mach.function
private abbrev MachInstruction := CompCert4Lean.Backend.Mach.instruction
private abbrev MachRegset := CompCert4Lean.Backend.Mach.regset
private abbrev MachGenv := CompCert4Lean.Backend.Mach.genv
private abbrev AsmCode := CompCert4Lean.X86.Asm.code
private abbrev AsmFunction := CompCert4Lean.X86.Asm.function
private abbrev AsmInstruction := CompCert4Lean.X86.Asm.instruction
private abbrev AsmRegset := CompCert4Lean.X86.Asm.regset
private abbrev AsmGenv := CompCert4Lean.X86.Asm.genv
private abbrev AsmState := CompCert4Lean.X86.Asm.state
private abbrev Ptrofs := CompCert4Lean.Lib.Integers.Ptrofs.int
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

private abbrev asmSP : Preg := .IR CompCert4Lean.X86.Asm.SP
private abbrev asmPC : Preg := .PC

private def asmStep
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (xi : ExternalCalls) :
    AsmGenv → AsmState → trace → AsmState → Prop :=
  CompCert4Lean.X86.Asm.step
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) cfg xi

/-! Agreement between machine and processor register states. -/

structure agree (ms : MachRegset) (sp : Val) (rs : AsmRegset) : Prop where
  mkagree ::
  agree_sp : rs asmSP = sp
  agree_sp_def : sp ≠ Vundef
  agree_mregs :
    ∀ r : Mreg, Val.lessdef (ms r) (rs (CompCert4Lean.X86.Asm.preg_of r))

export agree (mkagree agree_sp agree_sp_def agree_mregs)

/-! The suffix relation used for generated assembly code. -/

inductive code_tail : Z → AsmCode → AsmCode → Prop where
  | base (c : AsmCode) : code_tail ZArith.BinInt.Z.Z0 c c
  | step (pos : Z) (i : CompCert4Lean.X86.Asm.instruction)
      {c1 c2 : AsmCode} : code_tail pos c1 c2 →
      code_tail (ZArith.BinInt.Z.add pos (Zpos xH)) (i :: c1) c2

/-! Straight-line execution. -/

inductive exec_straight
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (ge : AsmGenv) (fn : AsmFunction) :
    AsmCode → AsmRegset → Mem → AsmCode → AsmRegset → Mem → Prop where
  | exec_straight_one (i1 : CompCert4Lean.X86.Asm.instruction)
      (c : AsmCode) (rs1 : AsmRegset) (m1 : Mem) (rs2 : AsmRegset) (m2 : Mem)
      (hstep : CompCert4Lean.X86.Asm.exec_instr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge fn i1 rs1 m1 = .Next rs2 m2)
      (hpc : rs2 asmPC = Val.offset_ptr (rs1 asmPC)
        CompCert4Lean.Lib.Integers.Ptrofs.one) :
      exec_straight
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge fn (i1 :: c) rs1 m1 c rs2 m2
  | exec_straight_step (i : CompCert4Lean.X86.Asm.instruction)
      (c : AsmCode) (rs1 : AsmRegset) (m1 : Mem) (rs2 : AsmRegset) (m2 : Mem)
      (c' : AsmCode) (rs3 : AsmRegset) (m3 : Mem)
      (hstep : CompCert4Lean.X86.Asm.exec_instr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge fn i rs1 m1 = .Next rs2 m2)
      (hpc : rs2 asmPC = Val.offset_ptr (rs1 asmPC)
        CompCert4Lean.Lib.Integers.Ptrofs.one)
      (htail : exec_straight
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge fn c rs2 m2 c' rs3 m3) :
      exec_straight
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge fn (i :: c) rs1 m1 c' rs3 m3

export exec_straight (exec_straight_one exec_straight_step)

/-! Translation of a source code pointer into generated code. -/

inductive transl_code_at_pc (ge : MachGenv) :
    Val → CompCert4Lean.Common.Values.block → MachFunction → MachCode → Bool →
      AsmFunction → AsmCode → Prop where
  | intro (b : CompCert4Lean.Common.Values.block) (ofs : Ptrofs)
      (f : MachFunction) (c : MachCode) (ep : Bool) (tf : AsmFunction) (tc : AsmCode)
      (hfind : Genv.find_funct_ptr ge b = some (Internal f))
      (htransf : CompCert4Lean.X86.Asmgen.transf_function f = .OK tf)
      (hcode : CompCert4Lean.X86.Asmgen.transl_code f c ep = .OK tc)
      (htail : code_tail (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs)
        tf.fn_code tc) :
      transl_code_at_pc ge (Vptr b ofs) b f c ep tf tc

/-! Properties of the Mach call stack. -/

inductive match_stack (ge : MachGenv) : List Mach.stackframe → Prop where
  | match_stack_nil : match_stack ge []
  | match_stack_cons (fb : Block) (sp ra : Val) (c : MachCode)
      (s : List Mach.stackframe) (f : MachFunction) (tf : AsmFunction)
      (tc : AsmCode)
      (hfind : Genv.find_funct_ptr ge fb = some (Internal f))
      (hatpc : transl_code_at_pc ge ra fb f c false tf tc)
      (hsp : sp ≠ Vundef)
      (hstacks : match_stack ge s) :
      match_stack ge (Mach.Stackframe fb sp ra c :: s)

export match_stack (match_stack_nil match_stack_cons)

/-! Executable source-shaped helpers. -/

def preg_notin (r : Preg) : List Mreg → Prop
  | [] => True
  | [r1] => r ≠ CompCert4Lean.X86.Asm.preg_of r1
  | r1 :: rl => r ≠ CompCert4Lean.X86.Asm.preg_of r1 ∧ preg_notin r rl

def return_address_offset (f : MachFunction) (c : MachCode) (ofs : Ptrofs) : Prop :=
  ∀ tf tc,
    CompCert4Lean.X86.Asmgen.transf_function f = .OK tf →
    CompCert4Lean.X86.Asmgen.transl_code f c false = .OK tc →
    code_tail (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) tf.fn_code tc

def find_label (lbl : CompCert4Lean.X86.Asm.label) (c : AsmCode) : Option AsmCode :=
  match c with
  | [] => none
  | i :: c' => if CompCert4Lean.X86.Asm.is_label lbl i then some c' else find_label lbl c'

def tail_nolabel (k c : AsmCode) : Prop :=
  is_tail k c ∧
    ∀ lbl, find_label lbl c = find_label lbl k

/-! Proof-bearing source declarations are represented by exact transparent
    proposition descriptors for the later proof migration phase. -/

def agree_change_spStatement : Prop :=
  ∀ (ms : MachRegset) (sp : Val) (rs : AsmRegset) (sp' : Val),
    agree ms sp rs → sp' ≠ Vundef →
      agree ms sp' (CompCert4Lean.X86.Asm.Pregmap.set asmSP sp' rs)

def agree_extenStatement : Prop :=
  ∀ (ms : MachRegset) (sp : Val) (rs rs' : AsmRegset),
    agree ms sp rs →
    (∀ r : Preg, CompCert4Lean.X86.Asm.data_preg r = true → rs' r = rs r) →
    agree ms sp rs'

def agree_nextinstrStatement : Prop :=
  ∀ (ms : MachRegset) (sp : Val) (rs : AsmRegset),
    agree ms sp rs → agree ms sp (CompCert4Lean.X86.Asm.nextinstr rs)

def agree_set_mregStatement : Prop :=
  ∀ (ms : MachRegset) (sp : Val) (rs : AsmRegset) (r : Mreg) (v : Val)
    (rs' : AsmRegset),
    agree ms sp rs →
    Val.lessdef v (rs' (CompCert4Lean.X86.Asm.preg_of r)) →
    (∀ r' : Preg,
      CompCert4Lean.X86.Asm.data_preg r' = true →
      r' ≠ CompCert4Lean.X86.Asm.preg_of r → rs' r' = rs r') →
    agree (CompCert4Lean.Backend.Mach.Regmap.set r v ms) sp rs'

def agree_set_mreg_parallelStatement : Prop :=
  ∀ (ms : MachRegset) (sp : Val) (rs : AsmRegset) (r : Mreg) (v v' : Val),
    agree ms sp rs → Val.lessdef v v' →
      agree (CompCert4Lean.Backend.Mach.Regmap.set r v ms) sp
        (CompCert4Lean.X86.Asm.Pregmap.set
          (CompCert4Lean.X86.Asm.preg_of r) v' rs)

def agree_set_otherStatement : Prop :=
  ∀ (ms : MachRegset) (sp : Val) (rs : AsmRegset) (r : Preg) (v : Val),
    agree ms sp rs → CompCert4Lean.X86.Asm.data_preg r = false →
      agree ms sp (CompCert4Lean.X86.Asm.Pregmap.set r v rs)

def agree_set_pairStatement : Prop :=
  ∀ (sp : Val) (p : rpair Mreg) (v v' : Val) (ms : MachRegset) (rs : AsmRegset),
    agree ms sp rs → Val.lessdef v v' →
      agree (CompCert4Lean.Backend.Mach.set_pair p v ms) sp
        (CompCert4Lean.X86.Asm.set_pair
          (map_rpair CompCert4Lean.X86.Asm.preg_of p) v' rs)

def agree_set_resStatement : Prop :=
  ∀ (res : builtin_res Mreg) (ms : MachRegset) (sp : Val) (rs : AsmRegset)
    (v v' : Val),
    agree ms sp rs → Val.lessdef v v' →
      agree (CompCert4Lean.Backend.Mach.set_res res v ms) sp
        (CompCert4Lean.X86.Asm.set_res
          (map_builtin_res CompCert4Lean.X86.Asm.preg_of res) v' rs)

def agree_set_undef_mregStatement : Prop :=
  ∀ (ms : MachRegset) (sp : Val) (rs : AsmRegset) (r : Mreg) (v : Val)
    (rl : List Mreg) (rs' : AsmRegset),
    agree ms sp rs →
    Val.lessdef v (rs' (CompCert4Lean.X86.Asm.preg_of r)) →
    (∀ r' : Preg,
      CompCert4Lean.X86.Asm.data_preg r' = true →
      r' ≠ CompCert4Lean.X86.Asm.preg_of r →
      preg_notin r' rl → rs' r' = rs r') →
    agree
      (CompCert4Lean.Backend.Mach.Regmap.set r v
        (CompCert4Lean.Backend.Mach.undef_regs rl ms)) sp rs'

def agree_undef_caller_save_regsStatement : Prop :=
  ∀ (cfg : CompilerConfig) (ms : MachRegset) (sp : Val) (rs : AsmRegset),
    agree ms sp rs →
      agree (CompCert4Lean.Backend.Mach.undef_caller_save_regs cfg ms) sp
        (CompCert4Lean.X86.Asm.undef_caller_save_regs cfg rs)

def agree_undef_nondata_regsStatement : Prop :=
  ∀ (ms : MachRegset) (sp : Val) (rl : List Preg) (rs : AsmRegset),
    agree ms sp rs →
    (∀ r : Preg, r ∈ rl → CompCert4Lean.X86.Asm.data_preg r = false) →
    agree ms sp (CompCert4Lean.X86.Asm.undef_regs rl rs)

def agree_undef_regsStatement : Prop :=
  ∀ (ms : MachRegset) (sp : Val) (rl : List Mreg) (rs rs' : AsmRegset),
    agree ms sp rs →
    (∀ r' : Preg,
      CompCert4Lean.X86.Asm.data_preg r' = true →
      preg_notin r' rl → rs' r' = rs r') →
    agree (CompCert4Lean.Backend.Mach.undef_regs rl ms) sp rs'

def builtin_arg_matchStatement : Prop :=
  ∀ (ge : Senv.t) (rs : AsmRegset) (sp : Val) (m : Mem)
    (a : builtin_arg Mreg) (v : Val),
    eval_builtin_arg ge (fun r => rs (CompCert4Lean.X86.Asm.preg_of r)) sp m a v →
      eval_builtin_arg ge rs sp m
        (map_builtin_arg CompCert4Lean.X86.Asm.preg_of a) v

def builtin_args_matchStatement : Prop :=
  ∀ (ge : Senv.t) (ms : MachRegset) (sp : Val) (rs : AsmRegset) (m m' : Mem),
    agree ms sp rs → Mem.extends m m' →
    ∀ (al : List (builtin_arg Mreg)) (vl : List Val),
      eval_builtin_args ge ms sp m al vl →
      ∃ vl',
        eval_builtin_args ge rs sp m'
          (List.map (map_builtin_arg CompCert4Lean.X86.Asm.preg_of) al) vl' ∧
        Val.lessdef_list vl vl'

def code_tail_bounds_1Statement : Prop :=
  ∀ (fn : AsmCode) (ofs : Z) (c : AsmCode),
    code_tail ofs fn c →
      ZArith.BinInt.Z.le ZArith.BinInt.Z.Z0 ofs ∧
      ZArith.BinInt.Z.le ofs (list_length_z fn)

def code_tail_bounds_2Statement : Prop :=
  ∀ (fn : AsmCode) (ofs : Z) (i : AsmInstruction) (c : AsmCode),
    code_tail ofs fn (i :: c) →
      ZArith.BinInt.Z.le ZArith.BinInt.Z.Z0 ofs ∧
      ZArith.BinInt.Z.lt ofs (list_length_z fn)

def code_tail_nextStatement : Prop :=
  ∀ (fn : AsmCode) (ofs : Z) (i : AsmInstruction) (c : AsmCode),
    code_tail ofs fn (i :: c) →
      code_tail (ZArith.BinInt.Z.add ofs (Zpos xH)) fn c

def code_tail_next_intStatement : Prop :=
  ∀ (fn : AsmCode) (ofs : Ptrofs) (i : AsmInstruction) (c : AsmCode),
    ZArith.BinInt.Z.le (list_length_z fn)
      CompCert4Lean.Lib.Integers.Ptrofs.max_unsigned →
    code_tail (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) fn (i :: c) →
    code_tail
      (CompCert4Lean.Lib.Integers.Ptrofs.unsigned
        (CompCert4Lean.Lib.Integers.Ptrofs.add ofs
          CompCert4Lean.Lib.Integers.Ptrofs.one)) fn c

def code_tail_no_biggerStatement : Prop :=
  ∀ (pos : Z) (c1 c2 : AsmCode),
    code_tail pos c1 c2 → c2.length ≤ c1.length

def code_tail_posStatement : Prop :=
  ∀ (pos : Z) (c1 c2 : AsmCode),
    code_tail pos c1 c2 → ZArith.BinInt.Z.ge pos ZArith.BinInt.Z.Z0

def code_tail_uniqueStatement : Prop :=
  ∀ (fn c : AsmCode) (pos pos' : Z),
    code_tail pos fn c → code_tail pos' fn c → pos = pos'

def exec_straight_steps_1Statement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (ge : AsmGenv)
    (fn : AsmFunction) (c : AsmCode) (rs : AsmRegset)
    (m : Mem) (c' : AsmCode) (rs' : AsmRegset) (m' : Mem),
    exec_straight
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn c rs m c' rs' m' →
    ZArith.BinInt.Z.le (list_length_z fn.fn_code)
      CompCert4Lean.Lib.Integers.Ptrofs.max_unsigned →
    ∀ (b : Block) (ofs : Ptrofs),
      rs asmPC = Vptr b ofs →
      Genv.find_funct_ptr ge b = some (Internal fn) →
      code_tail (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) fn.fn_code c →
      plus (asmStep
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg xi) ge (.State rs m) E0 (.State rs' m')

def exec_straight_steps_2Statement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction) (c : AsmCode) (rs : AsmRegset)
    (m : Mem) (c' : AsmCode) (rs' : AsmRegset) (m' : Mem),
    exec_straight
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn c rs m c' rs' m' →
    ZArith.BinInt.Z.le (list_length_z fn.fn_code)
      CompCert4Lean.Lib.Integers.Ptrofs.max_unsigned →
    ∀ (b : Block) (ofs : Ptrofs),
      rs asmPC = Vptr b ofs →
      Genv.find_funct_ptr ge b = some (Internal fn) →
      code_tail (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) fn.fn_code c →
      ∃ ofs',
        rs' asmPC = Vptr b ofs' ∧
        code_tail (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs') fn.fn_code c'

def exec_straight_threeStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction) (i1 i2 i3 : AsmInstruction)
    (c : AsmCode) (rs1 : AsmRegset) (m1 : Mem) (rs2 : AsmRegset) (m2 : Mem)
    (rs3 : AsmRegset) (m3 : Mem) (rs4 : AsmRegset) (m4 : Mem),
    CompCert4Lean.X86.Asm.exec_instr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn i1 rs1 m1 = .Next rs2 m2 →
    CompCert4Lean.X86.Asm.exec_instr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn i2 rs2 m2 = .Next rs3 m3 →
    CompCert4Lean.X86.Asm.exec_instr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn i3 rs3 m3 = .Next rs4 m4 →
    rs2 asmPC = Val.offset_ptr (rs1 asmPC) CompCert4Lean.Lib.Integers.Ptrofs.one →
    rs3 asmPC = Val.offset_ptr (rs2 asmPC) CompCert4Lean.Lib.Integers.Ptrofs.one →
    rs4 asmPC = Val.offset_ptr (rs3 asmPC) CompCert4Lean.Lib.Integers.Ptrofs.one →
    exec_straight
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn (i1 :: i2 :: i3 :: c) rs1 m1 c rs4 m4

def exec_straight_transStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction)
    (c1 : AsmCode) (rs1 : AsmRegset) (m1 : Mem)
    (c2 : AsmCode) (rs2 : AsmRegset) (m2 : Mem)
    (c3 : AsmCode) (rs3 : AsmRegset) (m3 : Mem),
    exec_straight
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn c1 rs1 m1 c2 rs2 m2 →
    exec_straight
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn c2 rs2 m2 c3 rs3 m3 →
    exec_straight
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn c1 rs1 m1 c3 rs3 m3

def exec_straight_twoStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction) (i1 i2 : AsmInstruction)
    (c : AsmCode) (rs1 : AsmRegset) (m1 : Mem) (rs2 : AsmRegset) (m2 : Mem)
    (rs3 : AsmRegset) (m3 : Mem),
    CompCert4Lean.X86.Asm.exec_instr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn i1 rs1 m1 = .Next rs2 m2 →
    CompCert4Lean.X86.Asm.exec_instr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn i2 rs2 m2 = .Next rs3 m3 →
    rs2 asmPC = Val.offset_ptr (rs1 asmPC) CompCert4Lean.Lib.Integers.Ptrofs.one →
    rs3 asmPC = Val.offset_ptr (rs2 asmPC) CompCert4Lean.Lib.Integers.Ptrofs.one →
    exec_straight
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      ge fn (i1 :: i2 :: c) rs1 m1 c rs3 m3

def extcall_arg_matchStatement : Prop :=
  ∀ (cfg : CompilerConfig) (ms : MachRegset) (sp : Val) (rs : AsmRegset)
    (m m' : Mem) (l : Loc) (v : Val),
    agree ms sp rs → Mem.extends m m' →
    CompCert4Lean.Backend.Mach.extcall_arg cfg ms m sp l v →
    ∃ v', CompCert4Lean.X86.Asm.extcall_arg cfg rs m' l v' ∧ Val.lessdef v v'

def extcall_arg_pair_matchStatement : Prop :=
  ∀ (cfg : CompilerConfig) (ms : MachRegset) (sp : Val) (rs : AsmRegset)
    (m m' : Mem) (p : rpair Loc) (v : Val),
    agree ms sp rs → Mem.extends m m' →
    CompCert4Lean.Backend.Mach.extcall_arg_pair cfg ms m sp p v →
    ∃ v', CompCert4Lean.X86.Asm.extcall_arg_pair cfg rs m' p v' ∧ Val.lessdef v v'

def extcall_args_matchStatement : Prop :=
  ∀ (cfg : CompilerConfig) (ms : MachRegset) (sp : Val) (rs : AsmRegset)
    (m m' : Mem),
    agree ms sp rs → Mem.extends m m' →
    ∀ (ll : List (rpair Loc)) (vl : List Val),
      list_forall2 (CompCert4Lean.Backend.Mach.extcall_arg_pair cfg ms m sp) ll vl →
      ∃ vl',
        list_forall2 (CompCert4Lean.X86.Asm.extcall_arg_pair cfg rs m') ll vl' ∧
        Val.lessdef_list vl vl'

def extcall_arguments_matchStatement : Prop :=
  ∀ (cfg : CompilerConfig) (ms : MachRegset) (m m' : Mem) (sp : Val)
    (rs : AsmRegset) (sg : Signature) (args : List Val),
    agree ms sp rs → Mem.extends m m' →
    CompCert4Lean.Backend.Mach.extcall_arguments cfg ms m sp sg args →
    ∃ args',
      CompCert4Lean.X86.Asm.extcall_arguments cfg rs m' sg args' ∧
      Val.lessdef_list args args'

def find_instr_tailStatement : Prop :=
  ∀ (c1 : AsmCode) (i : AsmInstruction) (c2 : AsmCode) (pos : Z),
    code_tail pos c1 (i :: c2) →
      CompCert4Lean.X86.Asm.find_instr pos c1 = some i

def freg_of_eqStatement : Prop :=
  ∀ (r : Mreg) (r' : Freg),
    CompCert4Lean.X86.Asmgen.freg_of r = .OK r' →
      CompCert4Lean.X86.Asm.preg_of r = .FR r'

def ireg_of_eqStatement : Prop :=
  ∀ (r : Mreg) (r' : Ireg),
    CompCert4Lean.X86.Asmgen.ireg_of r = .OK r' →
      CompCert4Lean.X86.Asm.preg_of r = .IR r'

def ireg_valStatement : Prop :=
  ∀ (ms : MachRegset) (sp : Val) (rs : AsmRegset) (r : Mreg) (r' : Ireg),
    agree ms sp rs →
    CompCert4Lean.X86.Asmgen.ireg_of r = .OK r' →
    Val.lessdef (ms r) (rs (.IR r'))

def is_tail_code_tailStatement : Prop :=
  ∀ (c1 c2 : AsmCode), is_tail c1 c2 → ∃ ofs, code_tail ofs c2 c1

def label_pos_code_tailStatement : Prop :=
  ∀ (lbl : CompCert4Lean.X86.Asm.label) (c : AsmCode) (pos : Z) (c' : AsmCode),
    find_label lbl c = some c' →
    ∃ pos',
      CompCert4Lean.X86.Asm.label_pos lbl pos c = some pos' ∧
      code_tail (ZArith.BinInt.Z.sub pos' pos) c c' ∧
      ZArith.BinInt.Z.lt pos pos' ∧
      ZArith.BinInt.Z.le pos'
        (ZArith.BinInt.Z.add pos (list_length_z c))

def lessdef_parent_raStatement : Prop :=
  ∀ (ge : MachGenv) (s : List Mach.stackframe) (v : Val),
    match_stack ge s → Val.lessdef (parent_ra s) v → v = parent_ra s

def lessdef_parent_spStatement : Prop :=
  ∀ (ge : MachGenv) (s : List Mach.stackframe) (v : Val),
    match_stack ge s → Val.lessdef (parent_sp s) v → v = parent_sp s

def nextinstr_invStatement : Prop :=
  ∀ (r : Preg) (rs : AsmRegset),
    r ≠ asmPC → CompCert4Lean.X86.Asm.nextinstr rs r = rs r

def parent_ra_defStatement : Prop :=
  ∀ (ge : MachGenv) (s : List Mach.stackframe),
    match_stack ge s → parent_ra s ≠ Vundef

def parent_sp_defStatement : Prop :=
  ∀ (ge : MachGenv) (s : List Mach.stackframe),
    match_stack ge s → parent_sp s ≠ Vundef

def preg_notin_charactStatement : Prop :=
  ∀ (r : Preg) (rl : List Mreg),
    preg_notin r rl ↔
      ∀ mr : Mreg, mr ∈ rl → r ≠ CompCert4Lean.X86.Asm.preg_of mr

def preg_of_dataStatement : Prop :=
  ∀ r : Mreg,
    CompCert4Lean.X86.Asm.data_preg (CompCert4Lean.X86.Asm.preg_of r) = true

def preg_of_injectiveStatement : Prop :=
  ∀ r1 r2 : Mreg,
    CompCert4Lean.X86.Asm.preg_of r1 = CompCert4Lean.X86.Asm.preg_of r2 → r1 = r2

def preg_of_not_SPStatement : Prop :=
  ∀ r : Mreg, CompCert4Lean.X86.Asm.preg_of r ≠ asmSP

def preg_valStatement : Prop :=
  ∀ (ms : MachRegset) (sp : Val) (rs : AsmRegset) (r : Mreg),
    agree ms sp rs →
      Val.lessdef (ms r) (rs (CompCert4Lean.X86.Asm.preg_of r))

def preg_valsStatement : Prop :=
  ∀ (ms : MachRegset) (sp : Val) (rs : AsmRegset),
    agree ms sp rs →
    ∀ l : List Mreg,
      Val.lessdef_list (List.map ms l)
        (List.map rs (List.map CompCert4Lean.X86.Asm.preg_of l))

def return_address_existsStatement : Prop :=
  ∀
    (transl_instr_tail :
      ∀ (f : MachFunction) (i : MachInstruction) (ep : Bool) (k c : AsmCode),
        CompCert4Lean.X86.Asmgen.transl_instr f i ep k = .OK c → is_tail k c)
    (transf_function_inv :
      ∀ (f : MachFunction) (tf : AsmFunction),
        CompCert4Lean.X86.Asmgen.transf_function f = .OK tf →
        ∃ tc ep,
          CompCert4Lean.X86.Asmgen.transl_code f f.fn_code ep = .OK tc ∧
          is_tail tc tf.fn_code)
    (transf_function_len :
      ∀ (f : MachFunction) (tf : AsmFunction),
        CompCert4Lean.X86.Asmgen.transf_function f = .OK tf →
        ZArith.BinInt.Z.le (list_length_z tf.fn_code)
          CompCert4Lean.Lib.Integers.Ptrofs.max_unsigned)
    (f : MachFunction) (sg : Signature) (ros : Sum Mreg ident) (c : MachCode),
    is_tail (.Mcall sg ros :: c) f.fn_code →
      ∃ ra, return_address_offset f c ra

def return_address_offset_correctStatement : Prop :=
  ∀ (ge : MachGenv) (b : Block) (ofs : Ptrofs) (fb : Block)
    (f : MachFunction) (c : MachCode) (tf : AsmFunction) (tc : AsmCode)
    (ofs' : Ptrofs),
    transl_code_at_pc ge (Vptr b ofs) fb f c false tf tc →
    return_address_offset f c ofs' → ofs' = ofs

def set_res_otherStatement : Prop :=
  ∀ (r : Preg) (res : builtin_res Mreg) (v : Val) (rs : AsmRegset),
    CompCert4Lean.X86.Asm.data_preg r = false →
      CompCert4Lean.X86.Asm.set_res
        (map_builtin_res CompCert4Lean.X86.Asm.preg_of res) v rs r = rs r

def sp_valStatement : Prop :=
  ∀ (ms : MachRegset) (sp : Val) (rs : AsmRegset),
    agree ms sp rs → sp = rs asmSP

def tail_nolabel_transStatement : Prop :=
  ∀ c1 c2 c3 : AsmCode,
    tail_nolabel c2 c3 → tail_nolabel c1 c2 → tail_nolabel c1 c3

def transl_code'_transl_codeStatement : Prop :=
  ∀ (f : MachFunction) (il : MachCode) (ep : Bool),
    CompCert4Lean.X86.Asmgen.transl_code' f il ep =
      CompCert4Lean.X86.Asmgen.transl_code f il ep

def transl_code_rec_transl_codeStatement : Prop :=
  ∀ (f : MachFunction) (il : MachCode) (ep : Bool)
    (k : AsmCode → CompCert4Lean.Common.Errors.res AsmCode),
    CompCert4Lean.X86.Asmgen.transl_code_rec f il ep k =
      CompCert4Lean.Common.Errors.bind
        (CompCert4Lean.X86.Asmgen.transl_code f il ep) k

def transl_code_tailStatement : Prop :=
  ∀
    (transl_instr_tail :
      ∀ (f : MachFunction) (i : MachInstruction) (ep : Bool) (k c : AsmCode),
        CompCert4Lean.X86.Asmgen.transl_instr f i ep k = .OK c → is_tail k c)
    (f : MachFunction) (c1 c2 : MachCode),
    is_tail c1 c2 →
    ∀ (tc2 : AsmCode) (ep2 : Bool),
      CompCert4Lean.X86.Asmgen.transl_code f c2 ep2 = .OK tc2 →
      ∃ tc1 ep1,
        CompCert4Lean.X86.Asmgen.transl_code f c1 ep1 = .OK tc1 ∧
        is_tail tc1 tc2

def undef_regs_otherStatement : Prop :=
  ∀ (r : Preg) (rl : List Preg) (rs : AsmRegset),
    (∀ r' : Preg, r' ∈ rl → r ≠ r') →
      CompCert4Lean.X86.Asm.undef_regs rl rs r = rs r

def undef_regs_other_2Statement : Prop :=
  ∀ (r : Preg) (rl : List Mreg) (rs : AsmRegset),
    preg_notin r rl →
      CompCert4Lean.X86.Asm.undef_regs
        (List.map CompCert4Lean.X86.Asm.preg_of rl) rs r = rs r

end CompCert4Lean.Backend.Asmgenproof0

namespace CompCert4Lean.Backend.Asmgenproof0

theorem ireg_of_eq : ireg_of_eqStatement := by
  intro r r' h
  simp [CompCert4Lean.X86.Asmgen.ireg_of] at h
  cases r <;> cases h <;> rfl

theorem freg_of_eq : freg_of_eqStatement := by
  intro r r' h
  simp [CompCert4Lean.X86.Asmgen.freg_of] at h
  cases r <;> cases h <;> rfl

theorem preg_of_injective : preg_of_injectiveStatement := by
  intro r1 r2 h
  cases r1 <;> cases r2 <;> simp [CompCert4Lean.X86.Asm.preg_of] at h ⊢

theorem preg_of_data : preg_of_dataStatement := by
  intro r
  cases r <;> rfl

end CompCert4Lean.Backend.Asmgenproof0

namespace CompCert4Lean.Backend.Asmgenproof0

theorem preg_of_not_SP : preg_of_not_SPStatement := by
  intro r
  cases r <;> simp [CompCert4Lean.X86.Asm.preg_of, asmSP, CompCert4Lean.X86.Asm.SP]

theorem nextinstr_inv : nextinstr_invStatement := by
  intro r rs h
  unfold CompCert4Lean.X86.Asm.nextinstr CompCert4Lean.X86.Asm.Pregmap.set
  split
  · rename_i heq
    exact (h heq).elim
  · rfl

theorem undef_regs_other : undef_regs_otherStatement := by
  intro r rl
  induction rl with
  | nil => intro rs h; rfl
  | cons x xs ih =>
      intro rs h
      change CompCert4Lean.X86.Asm.undef_regs xs
        (CompCert4Lean.X86.Asm.Pregmap.set x CompCert4Lean.Common.Values.Vundef rs) r = rs r
      calc
        _ = CompCert4Lean.X86.Asm.Pregmap.set x CompCert4Lean.Common.Values.Vundef rs r :=
          ih (CompCert4Lean.X86.Asm.Pregmap.set x CompCert4Lean.Common.Values.Vundef rs)
            (by intro x' hx'; exact h x' (by simp [hx']))
        _ = rs r := by
          unfold CompCert4Lean.X86.Asm.Pregmap.set
          split
          · rename_i heq
            exact (h x (by simp) heq).elim
          · rfl

theorem preg_notin_charact : preg_notin_charactStatement := by
  intro r rl
  induction rl with
  | nil => simp [preg_notin]
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [preg_notin]
      | cons y ys =>
          simp only [preg_notin]
          rw [ih]
          constructor
          · intro h mr hmr
            rcases List.mem_cons.mp hmr with hmx | hmr
            · subst mr; exact h.1
            · exact h.2 mr hmr
          · intro h
            refine ⟨h x (by simp), ?_⟩
            intro mr hmr
            exact h mr (List.mem_cons.mpr (Or.inr hmr))

end CompCert4Lean.Backend.Asmgenproof0

namespace CompCert4Lean.Backend.Asmgenproof0

theorem undef_regs_other_2 : undef_regs_other_2Statement := by
  intro r rl rs hnotin
  apply undef_regs_other
  intro r' hr'
  rcases List.mem_map.mp hr' with ⟨mr, hmr, rfl⟩
  exact ((preg_notin_charact r rl).mp hnotin) mr hmr

theorem preg_val : preg_valStatement := by
  intro ms sp rs r hagree
  exact hagree.agree_mregs r

theorem preg_vals : preg_valsStatement := by
  intro ms sp rs hagree l
  induction l with
  | nil => exact CompCert4Lean.Common.Values.Val.lessdef_list_nil
  | cons r l ih =>
      exact CompCert4Lean.Common.Values.Val.lessdef_list_cons _ _ _ _
        (preg_val ms sp rs r hagree) ih

theorem sp_val : sp_valStatement := by
  intro ms sp rs hagree
  exact hagree.agree_sp.symm

end CompCert4Lean.Backend.Asmgenproof0

namespace CompCert4Lean.Backend.Asmgenproof0

theorem ireg_val : ireg_valStatement := by
  intro ms sp rs r r' hagree hreg
  rw [← ireg_of_eq r r' hreg]
  exact hagree.agree_mregs r

theorem agree_exten : agree_extenStatement := by
  intro ms sp rs rs' hagree hext
  refine ⟨?_, hagree.agree_sp_def, ?_⟩
  · rw [hext asmSP (by rfl)]
    exact hagree.agree_sp
  · intro r
    rw [hext (CompCert4Lean.X86.Asm.preg_of r) (preg_of_data r)]
    exact hagree.agree_mregs r

theorem agree_set_mreg : agree_set_mregStatement := by
  intro ms sp rs r v rs' hagree hv hother
  refine ⟨?_, hagree.agree_sp_def, ?_⟩
  · rw [hother asmSP (by rfl) (by exact Ne.symm (preg_of_not_SP r))]
    exact hagree.agree_sp
  · intro r0
    unfold CompCert4Lean.Backend.Mach.Regmap.set
    cases hEq : CompCert4Lean.Backend.Mach.Regmap.elt_eq r0 r with
    | left heq =>
      subst r0
      exact hv
    | right hne =>
      rw [hother (CompCert4Lean.X86.Asm.preg_of r0) (preg_of_data r0)]
      · exact hagree.agree_mregs r0
      · intro hp
        exact hne (preg_of_injective r0 r hp)

theorem agree_set_mreg_parallel : agree_set_mreg_parallelStatement := by
  intro ms sp rs r v v' hagree hv
  apply agree_set_mreg ms sp rs r v
    (CompCert4Lean.X86.Asm.Pregmap.set
      (CompCert4Lean.X86.Asm.preg_of r) v' rs) hagree
  · simpa [CompCert4Lean.X86.Asm.Pregmap.set] using hv
  · intro r' _ hne
    simp [CompCert4Lean.X86.Asm.Pregmap.set, hne]

end CompCert4Lean.Backend.Asmgenproof0

namespace CompCert4Lean.Backend.Asmgenproof0

theorem agree_set_other : agree_set_otherStatement := by
  intro ms sp rs r v hagree hdata
  apply agree_exten ms sp rs
  · exact hagree
  · intro r' hdata'
    unfold CompCert4Lean.X86.Asm.Pregmap.set
    split
    · rename_i heq
      subst r'
      simp [hdata] at hdata'
    · rfl

theorem agree_nextinstr : agree_nextinstrStatement := by
  intro ms sp rs hagree
  unfold CompCert4Lean.X86.Asm.nextinstr
  apply agree_set_other ms sp rs CompCert4Lean.X86.Asm.PC
    (CompCert4Lean.Common.Values.Val.offset_ptr (rs asmPC)
      CompCert4Lean.Lib.Integers.Ptrofs.one) hagree
  rfl

private theorem loword_lessdef_aux :
    ∀ v v', CompCert4Lean.Common.Values.Val.lessdef v v' →
      CompCert4Lean.Common.Values.Val.lessdef
        (CompCert4Lean.Common.Values.Val.loword v)
        (CompCert4Lean.Common.Values.Val.loword v') := by
  intro v v' h
  cases h with
  | lessdef_refl v => exact CompCert4Lean.Common.Values.Val.lessdef.lessdef_refl _
  | lessdef_undef v => exact CompCert4Lean.Common.Values.Val.lessdef.lessdef_undef _

private theorem hiword_lessdef_aux :
    ∀ v v', CompCert4Lean.Common.Values.Val.lessdef v v' →
      CompCert4Lean.Common.Values.Val.lessdef
        (CompCert4Lean.Common.Values.Val.hiword v)
        (CompCert4Lean.Common.Values.Val.hiword v') := by
  intro v v' h
  cases h with
  | lessdef_refl v => exact CompCert4Lean.Common.Values.Val.lessdef.lessdef_refl _
  | lessdef_undef v => exact CompCert4Lean.Common.Values.Val.lessdef.lessdef_undef _

theorem agree_set_pair : agree_set_pairStatement := by
  intro sp p v v' ms rs hagree hv
  cases p with
  | One r =>
      simpa [CompCert4Lean.Backend.Mach.set_pair,
        CompCert4Lean.X86.Asm.set_pair, CompCert4Lean.Common.AST.map_rpair] using
        (agree_set_mreg_parallel ms sp rs r v v' hagree hv)
  | Twolong rhi rlo =>
      have hhi := agree_set_mreg_parallel ms sp rs rhi
        (CompCert4Lean.Common.Values.Val.hiword v)
        (CompCert4Lean.Common.Values.Val.hiword v') hagree
        (hiword_lessdef_aux v v' hv)
      have hlo := agree_set_mreg_parallel
        (CompCert4Lean.Backend.Mach.Regmap.set rhi
          (CompCert4Lean.Common.Values.Val.hiword v) ms)
        sp
        (CompCert4Lean.X86.Asm.Pregmap.set
          (CompCert4Lean.X86.Asm.preg_of rhi)
          (CompCert4Lean.Common.Values.Val.hiword v') rs)
        rlo (CompCert4Lean.Common.Values.Val.loword v)
          (CompCert4Lean.Common.Values.Val.loword v') hhi
        (loword_lessdef_aux v v' hv)
      simpa [CompCert4Lean.Backend.Mach.set_pair,
        CompCert4Lean.X86.Asm.set_pair, CompCert4Lean.Common.AST.map_rpair] using hlo

theorem agree_undef_nondata_regs : agree_undef_nondata_regsStatement := by
  intro ms sp rl rs hagree hnondata
  induction rl generalizing rs with
  | nil => exact hagree
  | cons r rl ih =>
      change agree ms sp
        (CompCert4Lean.X86.Asm.undef_regs rl
          (CompCert4Lean.X86.Asm.Pregmap.set r
            CompCert4Lean.Common.Values.Vundef rs))
      apply ih (rs := CompCert4Lean.X86.Asm.Pregmap.set r
        CompCert4Lean.Common.Values.Vundef rs)
      · have hset : agree ms sp
            (CompCert4Lean.X86.Asm.Pregmap.set r
              CompCert4Lean.Common.Values.Vundef rs) := by
          exact agree_exten ms sp rs
            (CompCert4Lean.X86.Asm.Pregmap.set r
              CompCert4Lean.Common.Values.Vundef rs) hagree (by
                intro r' hdata
                unfold CompCert4Lean.X86.Asm.Pregmap.set
                split
                · rename_i heq
                  subst r'
                  have hfalse : CompCert4Lean.X86.Asm.data_preg r = false :=
                    hnondata r (by simp)
                  simp [hfalse] at hdata
                · rfl)
        exact hset
      · intro r' hr'
        exact hnondata r' (by simp [hr'])

end CompCert4Lean.Backend.Asmgenproof0

namespace CompCert4Lean.Backend.Asmgenproof0

theorem agree_change_sp : agree_change_spStatement := by
  intro ms sp rs sp' hagree hsp'
  refine ⟨?_, hsp', ?_⟩
  · change (if asmSP = asmSP then sp' else rs asmSP) = sp'
    simp
  · intro r
    change CompCert4Lean.Common.Values.Val.lessdef (ms r)
      (if CompCert4Lean.X86.Asm.preg_of r = asmSP then sp'
      else rs (CompCert4Lean.X86.Asm.preg_of r))
    split
    · rename_i heq
      exact (preg_of_not_SP r heq).elim
    · exact hagree.agree_mregs r

end CompCert4Lean.Backend.Asmgenproof0

namespace CompCert4Lean.Backend.Asmgenproof0

theorem agree_undef_regs : agree_undef_regsStatement := by
  intro ms sp rl rs rs' hagree hother
  refine ⟨?_, hagree.agree_sp_def, ?_⟩
  · have hsp : preg_notin asmSP rl := by
      apply (preg_notin_charact asmSP rl).2
      intro mr hmr hEq
      exact (preg_of_not_SP mr hEq.symm).elim
    calc
      rs' asmSP = rs asmSP := hother asmSP (by rfl) hsp
      _ = sp := hagree.agree_sp
  · intro r
    by_cases hr : r ∈ rl
    · have hundef :=
        CompCert4Lean.Backend.Mach.undef_regs_same_proof r rl ms hr
      rw [hundef]
      exact CompCert4Lean.Common.Values.Val.lessdef.lessdef_undef _
    · have hkeep :=
        CompCert4Lean.Backend.Mach.undef_regs_other_proof r rl ms hr
      rw [hkeep]
      have hnotin : preg_notin (CompCert4Lean.X86.Asm.preg_of r) rl := by
        apply (preg_notin_charact (CompCert4Lean.X86.Asm.preg_of r) rl).2
        intro mr hmr hEq
        exact hr (by
          have hEq' : r = mr := preg_of_injective r mr hEq
          simpa [hEq'] using hmr)
      rw [hother (CompCert4Lean.X86.Asm.preg_of r)
        (preg_of_data r) hnotin]
      exact hagree.agree_mregs r

theorem agree_set_undef_mreg : agree_set_undef_mregStatement := by
  intro ms sp rs r v rl rs' hagree hv hother
  let rs0 := CompCert4Lean.X86.Asm.Pregmap.set
    (CompCert4Lean.X86.Asm.preg_of r) (rs (CompCert4Lean.X86.Asm.preg_of r)) rs'
  refine agree_set_mreg
    (CompCert4Lean.Backend.Mach.undef_regs rl ms) sp rs0 r v rs' ?_ hv ?_
  · apply agree_undef_regs ms sp rl rs rs0 hagree
    intro r' hdata hnotin
    simp only [rs0, CompCert4Lean.X86.Asm.Pregmap.set]
    split
    · rename_i heq
      subst r'
      rfl
    · rename_i hne
      exact hother r' hdata hne hnotin
  · intro r' hdata hne
    simp [rs0, CompCert4Lean.X86.Asm.Pregmap.set, hne]

theorem agree_undef_caller_save_regs : agree_undef_caller_save_regsStatement := by
  intro cfg ms sp rs hagree
  refine ⟨?_, hagree.agree_sp_def, ?_⟩
  · have hnomem : ¬ Foundation.Logic.Rocq.Coq.Lists.List.In asmSP
        (List.map CompCert4Lean.X86.Asm.preg_of
          (List.filter
            (fun mr => CompCert4Lean.X86.Conventions1.is_callee_save cfg mr)
            CompCert4Lean.X86.Machregs.all_mregs)) := by
      intro h
      rcases _root_.List.mem_map.mp h with ⟨mr, hmr, heq⟩
      exact (preg_of_not_SP mr heq).elim
    unfold CompCert4Lean.X86.Asm.undef_caller_save_regs
    dsimp
    cases hIn : CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec
        CompCert4Lean.X86.Asm.PregEq.eq asmSP
        (List.map CompCert4Lean.X86.Asm.preg_of
          (List.filter
            (fun mr => CompCert4Lean.X86.Conventions1.is_callee_save cfg mr)
            CompCert4Lean.X86.Machregs.all_mregs)) with
    | left h => exact (hnomem h).elim
    | right h =>
        cases hEq : CompCert4Lean.X86.Asm.PregEq.eq asmSP asmSP with
        | left heq => exact hagree.agree_sp
        | right hne => exact (hne rfl).elim
  · intro r
    cases hsave : CompCert4Lean.X86.Conventions1.is_callee_save cfg r with
    | false =>
        simp [CompCert4Lean.Backend.Mach.undef_caller_save_regs, hsave]
        exact CompCert4Lean.Common.Values.Val.lessdef.lessdef_undef _
    | true =>
        have hmem_filter : r ∈ List.filter
            (fun mr => CompCert4Lean.X86.Conventions1.is_callee_save cfg mr)
            CompCert4Lean.X86.Machregs.all_mregs := by
          exact _root_.List.mem_filter.mpr
            ⟨CompCert4Lean.X86.Machregs.all_mregs_complete r, hsave⟩
        have hmem_saved : CompCert4Lean.X86.Asm.preg_of r ∈ List.map
            CompCert4Lean.X86.Asm.preg_of
            (List.filter
              (fun mr => CompCert4Lean.X86.Conventions1.is_callee_save cfg mr)
              CompCert4Lean.X86.Machregs.all_mregs) := by
          exact _root_.List.mem_map.mpr ⟨r, hmem_filter, rfl⟩
        unfold CompCert4Lean.Backend.Mach.undef_caller_save_regs
        unfold CompCert4Lean.X86.Asm.undef_caller_save_regs
        dsimp
        simp [hsave]
        cases hIn : CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec
            CompCert4Lean.X86.Asm.PregEq.eq (CompCert4Lean.X86.Asm.preg_of r)
            (List.map CompCert4Lean.X86.Asm.preg_of
              (List.filter
                (fun mr => CompCert4Lean.X86.Conventions1.is_callee_save cfg mr)
                CompCert4Lean.X86.Machregs.all_mregs)) with
        | left h => exact hagree.agree_mregs r
        | right h => exact (h hmem_saved).elim

end CompCert4Lean.Backend.Asmgenproof0

namespace CompCert4Lean.Backend.Asmgenproof0

theorem builtin_arg_match : builtin_arg_matchStatement := by
  intro ge rs sp m a v h
  induction h with
  | eval_BA x =>
      simpa [CompCert4Lean.Common.AST.map_builtin_arg] using
        (@CompCert4Lean.Common.Events.eval_BA _ ge rs sp m
          (CompCert4Lean.X86.Asm.preg_of x))
  | eval_BA_int n =>
      simpa [CompCert4Lean.Common.AST.map_builtin_arg] using
        (@CompCert4Lean.Common.Events.eval_BA_int _ ge rs sp m n)
  | eval_BA_long n =>
      simpa [CompCert4Lean.Common.AST.map_builtin_arg] using
        (@CompCert4Lean.Common.Events.eval_BA_long _ ge rs sp m n)
  | eval_BA_float n =>
      simpa [CompCert4Lean.Common.AST.map_builtin_arg] using
        (@CompCert4Lean.Common.Events.eval_BA_float _ ge rs sp m n)
  | eval_BA_single n =>
      simpa [CompCert4Lean.Common.AST.map_builtin_arg] using
        (@CompCert4Lean.Common.Events.eval_BA_single _ ge rs sp m n)
  | eval_BA_loadstack chunk ofs v load =>
      simpa [CompCert4Lean.Common.AST.map_builtin_arg] using
        (@CompCert4Lean.Common.Events.eval_BA_loadstack _ ge rs sp m
          chunk ofs v load)
  | eval_BA_addrstack ofs =>
      simpa [CompCert4Lean.Common.AST.map_builtin_arg] using
        (@CompCert4Lean.Common.Events.eval_BA_addrstack _ ge rs sp m ofs)
  | eval_BA_loadglobal chunk id ofs v load =>
      simpa [CompCert4Lean.Common.AST.map_builtin_arg] using
        (@CompCert4Lean.Common.Events.eval_BA_loadglobal _ ge rs sp m
          chunk id ofs v load)
  | eval_BA_addrglobal id ofs =>
      simpa [CompCert4Lean.Common.AST.map_builtin_arg] using
        (@CompCert4Lean.Common.Events.eval_BA_addrglobal _ ge rs sp m id ofs)
  | eval_BA_splitlong hi lo vhi vlo eval_hi eval_lo ih_hi ih_lo =>
      simpa [CompCert4Lean.Common.AST.map_builtin_arg] using
        (@CompCert4Lean.Common.Events.eval_BA_splitlong _ ge rs sp m
          (CompCert4Lean.Common.AST.map_builtin_arg
            CompCert4Lean.X86.Asm.preg_of hi)
          (CompCert4Lean.Common.AST.map_builtin_arg
            CompCert4Lean.X86.Asm.preg_of lo)
          vhi vlo ih_hi ih_lo)
  | eval_BA_addptr a1 a2 v1 v2 eval_a1 eval_a2 ih_a1 ih_a2 =>
      simpa [CompCert4Lean.Common.AST.map_builtin_arg] using
        (@CompCert4Lean.Common.Events.eval_BA_addptr _ ge rs sp m
          (CompCert4Lean.Common.AST.map_builtin_arg
            CompCert4Lean.X86.Asm.preg_of a1)
          (CompCert4Lean.Common.AST.map_builtin_arg
            CompCert4Lean.X86.Asm.preg_of a2)
          v1 v2 ih_a1 ih_a2)

theorem agree_set_res : agree_set_resStatement := by
  intro res ms sp rs v v' hagree hv
  have hrec : ∀ (res : CompCert4Lean.Common.AST.builtin_res
        CompCert4Lean.X86.Machregs.mreg)
      (ms : CompCert4Lean.Backend.Mach.regset)
      (rs : CompCert4Lean.X86.Asm.regset)
      (v v' : CompCert4Lean.Common.Values.val),
      agree ms sp rs →
      CompCert4Lean.Common.Values.Val.lessdef v v' →
      agree (CompCert4Lean.Backend.Mach.set_res res v ms) sp
        (CompCert4Lean.X86.Asm.set_res
          (CompCert4Lean.Common.AST.map_builtin_res
            CompCert4Lean.X86.Asm.preg_of res) v' rs) := by
    intro res
    induction res with
    | BR r =>
        intro ms rs v v' hagree hv
        apply agree_set_mreg ms sp rs r v
          (CompCert4Lean.X86.Asm.Pregmap.set
            (CompCert4Lean.X86.Asm.preg_of r) v' rs) hagree
        · simpa [CompCert4Lean.X86.Asm.Pregmap.set] using hv
        · intro r' hdata hne
          simp [CompCert4Lean.X86.Asm.Pregmap.set, hne]
    | BR_none =>
        intro ms rs v v' hagree hv
        simpa [CompCert4Lean.Common.AST.map_builtin_res,
          CompCert4Lean.Backend.Mach.set_res,
          CompCert4Lean.X86.Asm.set_res] using hagree
    | BR_splitlong hi lo ih_hi ih_lo =>
        intro ms rs v v' hagree hv
        have hhi := ih_hi ms rs
          (CompCert4Lean.Common.Values.Val.hiword v)
          (CompCert4Lean.Common.Values.Val.hiword v') hagree
          (hiword_lessdef_aux v v' hv)
        have hlo := ih_lo
          (CompCert4Lean.Backend.Mach.set_res hi
            (CompCert4Lean.Common.Values.Val.hiword v) ms)
          (CompCert4Lean.X86.Asm.set_res
            (CompCert4Lean.Common.AST.map_builtin_res
              CompCert4Lean.X86.Asm.preg_of hi)
            (CompCert4Lean.Common.Values.Val.hiword v') rs)
          (CompCert4Lean.Common.Values.Val.loword v)
          (CompCert4Lean.Common.Values.Val.loword v') hhi
          (loword_lessdef_aux v v' hv)
        simpa [CompCert4Lean.Common.AST.map_builtin_res,
          CompCert4Lean.Backend.Mach.set_res,
          CompCert4Lean.X86.Asm.set_res] using hlo
  exact hrec res ms rs v v' hagree hv

theorem set_res_other : set_res_otherStatement := by
  intro r res v rs hdata
  have hrec : ∀ (res : CompCert4Lean.Common.AST.builtin_res
        CompCert4Lean.X86.Machregs.mreg)
      (r : CompCert4Lean.X86.Asm.preg)
      (v : CompCert4Lean.Common.Values.val)
      (rs : CompCert4Lean.X86.Asm.regset),
      CompCert4Lean.X86.Asm.data_preg r = false →
      CompCert4Lean.X86.Asm.set_res
        (CompCert4Lean.Common.AST.map_builtin_res
          CompCert4Lean.X86.Asm.preg_of res) v rs r = rs r := by
    intro res
    induction res with
    | BR r' =>
        intro r v rs hdata
        by_cases heq : r = CompCert4Lean.X86.Asm.preg_of r'
        · subst r
          have hp := preg_of_data r'
          have hfalse : false = true := hdata.symm.trans hp
          cases hfalse
        · simp [CompCert4Lean.Common.AST.map_builtin_res,
            CompCert4Lean.X86.Asm.set_res,
            CompCert4Lean.X86.Asm.Pregmap.set, heq]
    | BR_none =>
        intro r v rs hdata
        rfl
    | BR_splitlong hi lo ih_hi ih_lo =>
        intro r v rs hdata
        have hhi := ih_hi r (CompCert4Lean.Common.Values.Val.hiword v) rs hdata
        have hlo := ih_lo r (CompCert4Lean.Common.Values.Val.loword v)
          (CompCert4Lean.X86.Asm.set_res
            (CompCert4Lean.Common.AST.map_builtin_res
              CompCert4Lean.X86.Asm.preg_of hi)
            (CompCert4Lean.Common.Values.Val.hiword v) rs) hdata
        simpa [CompCert4Lean.X86.Asm.set_res,
          CompCert4Lean.Common.AST.map_builtin_res, hhi] using hlo
  exact hrec res r v rs hdata

end CompCert4Lean.Backend.Asmgenproof0

namespace CompCert4Lean.Backend.Asmgenproof0

theorem code_tail_pos : code_tail_posStatement := by
  intro pos c1 c2 h
  induction h with
  | base c =>
      exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le_refl _
  | @step pos i c1 c2 h ih =>
      change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add pos
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH))
      change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ pos at ih
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      have hone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH) = 1 := by rfl
      rw [hone]
      omega

end CompCert4Lean.Backend.Asmgenproof0

namespace CompCert4Lean.Backend.Asmgenproof0

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem list_length_z_aux_eq (l : List AsmInstruction) (n : Z) :
    intOfZ (CompCert4Lean.Lib.Coqlib.list_length_z_aux l n) =
      intOfZ n + intOfZ (CompCert4Lean.Lib.Coqlib.list_length_z l) := by
  induction l generalizing n with
  | nil =>
      simp [CompCert4Lean.Lib.Coqlib.list_length_z_aux,
        CompCert4Lean.Lib.Coqlib.list_length_z, intOfZ]
  | cons a tl ih =>
      simp only [CompCert4Lean.Lib.Coqlib.list_length_z_aux,
        CompCert4Lean.Lib.Coqlib.list_length_z]
      rw [ih (ZArith.BinInt.Z.succ n),
        ih (ZArith.BinInt.Z.succ ZArith.BinInt.Z.Z0)]
      have hone : intOfZ (Zpos xH) = 1 := by rfl
      simp only [ZArith.BinInt.Z.succ, ZArith.BinInt.Z.add,
        intOfZ_zOfInt, hone]
      simp only [intOfZ]
      omega

private theorem list_length_z_aux_nonneg :
    ∀ {α : Type} (l : List α) (n : Z),
      0 ≤ intOfZ n → 0 ≤ intOfZ
        (CompCert4Lean.Lib.Coqlib.list_length_z_aux l n) := by
  intro α l
  induction l with
  | nil =>
      intro n hn
      simpa [CompCert4Lean.Lib.Coqlib.list_length_z_aux] using hn
  | cons a tl ih =>
      intro n hn
      apply ih
      change 0 ≤ intOfZ (ZArith.BinInt.Z.add n (Zpos xH))
      simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
      have hone : intOfZ (Zpos xH) = 1 := by rfl
      rw [hone]
      omega

private theorem list_length_z_nonneg (l : AsmCode) :
    0 ≤ intOfZ (CompCert4Lean.Lib.Coqlib.list_length_z l) := by
  exact list_length_z_aux_nonneg l ZArith.BinInt.Z.Z0 (by exact Int.le_refl _)

theorem code_tail_bounds_1 : code_tail_bounds_1Statement := by
  intro fn ofs c h
  induction h with
  | base c =>
      constructor
      · exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le_refl _
      · exact list_length_z_nonneg c
  | @step pos i c1 c2 h ih =>
      change 0 ≤ intOfZ (ZArith.BinInt.Z.add pos (Zpos xH)) ∧
        intOfZ (ZArith.BinInt.Z.add pos (Zpos xH)) ≤
          intOfZ (CompCert4Lean.Lib.Coqlib.list_length_z (i :: c1))
      change 0 ≤ intOfZ pos ∧ intOfZ pos ≤
          intOfZ (CompCert4Lean.Lib.Coqlib.list_length_z c1) at ih
      simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
      have hone : intOfZ (Zpos xH) = 1 := by rfl
      rw [hone]
      simp only [CompCert4Lean.Lib.Coqlib.list_length_z,
        CompCert4Lean.Lib.Coqlib.list_length_z_aux]
      rw [list_length_z_aux_eq c1 (ZArith.BinInt.Z.succ ZArith.BinInt.Z.Z0)]
      simp only [ZArith.BinInt.Z.succ, ZArith.BinInt.Z.add,
        intOfZ_zOfInt, hone]
      simp only [intOfZ]
      change 0 ≤ intOfZ pos + 1 ∧
        intOfZ pos + 1 ≤ 1 + intOfZ
          (CompCert4Lean.Lib.Coqlib.list_length_z c1)
      omega

private theorem code_tail_bounds_2_aux :
    ∀ (fn : AsmCode) (ofs : Z) (c : AsmCode), code_tail ofs fn c →
      ∀ (i : AsmInstruction) (c' : AsmCode), c = i :: c' →
        0 ≤ intOfZ ofs ∧ intOfZ ofs < intOfZ
          (CompCert4Lean.Lib.Coqlib.list_length_z fn) := by
  intro fn ofs c h
  induction h with
  | base c =>
      intro i c' heq
      subst c
      change List AsmInstruction at c'
      constructor
      · exact Int.le_refl _
      · simp only [CompCert4Lean.Lib.Coqlib.list_length_z,
          CompCert4Lean.Lib.Coqlib.list_length_z_aux]
        have hlen := list_length_z_nonneg c'
        have hone : intOfZ (Zpos xH) = 1 := by rfl
        rw [list_length_z_aux_eq c' (ZArith.BinInt.Z.succ ZArith.BinInt.Z.Z0)]
        simp only [ZArith.BinInt.Z.succ, ZArith.BinInt.Z.add,
          intOfZ_zOfInt, hone]
        have hz0 : intOfZ ZArith.BinInt.Z.Z0 = 0 := by rfl
        rw [hz0]
        omega
  | @step pos i0 c1 c2 h ih =>
      intro i c' heq
      have hi := ih i c' heq
      constructor
      · simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
        have hone : intOfZ (Zpos xH) = 1 := by rfl
        rw [hone]
        omega
      · simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
        have hone : intOfZ (Zpos xH) = 1 := by rfl
        rw [hone]
        simp only [CompCert4Lean.Lib.Coqlib.list_length_z,
          CompCert4Lean.Lib.Coqlib.list_length_z_aux]
        rw [list_length_z_aux_eq c1 (ZArith.BinInt.Z.succ ZArith.BinInt.Z.Z0)]
        simp only [ZArith.BinInt.Z.succ, ZArith.BinInt.Z.add,
          intOfZ_zOfInt]
        change intOfZ pos + 1 < 1 + intOfZ
          (CompCert4Lean.Lib.Coqlib.list_length_z c1)
        omega

theorem code_tail_bounds_2 : code_tail_bounds_2Statement := by
  intro fn ofs i c h
  have h' := code_tail_bounds_2_aux fn ofs (i :: c) h i c rfl
  exact h'

private theorem find_instr_tail_aux :
    ∀ (c1 : AsmCode) (pos : Z) (ctail : AsmCode),
      code_tail pos c1 ctail →
      ∀ (i : AsmInstruction) (c2 : AsmCode), ctail = i :: c2 →
        CompCert4Lean.X86.Asm.find_instr pos c1 = some i := by
  intro c1 pos ctail h
  induction h with
  | base c =>
      intro i c2 heq
      subst c
      change some i = some i
      rfl
  | @step pos a c1 c2 h ih =>
      intro i c2' heq
      have hp := code_tail_pos pos c1 c2 h
      simp only [CompCert4Lean.X86.Asm.find_instr]
      have hne : ZArith.BinInt.Z.add pos (Zpos xH) ≠ Z0 := by
        intro hz
        have hz' : intOfZ pos + 1 = 0 := by
          have hz'' := congrArg intOfZ hz
          rw [show intOfZ Z0 = 0 by rfl] at hz''
          simpa [ZArith.BinInt.Z.add, intOfZ_zOfInt,
            show intOfZ (Zpos xH) = 1 by rfl] using hz''
        have hp' : 0 ≤ intOfZ pos := hp
        omega
      cases hzq : CompCert4Lean.Lib.Coqlib.zeq
          (ZArith.BinInt.Z.add pos (Zpos xH)) Z0 with
      | left heqz =>
          exact (hne heqz).elim
      | right heqz =>
        simp only [hzq]
        have heq' : ZArith.BinInt.Z.sub
            (ZArith.BinInt.Z.add pos (Zpos xH))
            (ZArith.BinInt.Z.of_nat 1) = pos := by
          apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
          simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add,
            ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
          have hone : intOfZ (Zpos xH) = 1 := by rfl
          rw [hone]
          have h1 : (Int.ofNat 1) = 1 := by rfl
          rw [h1]
          omega
        change CompCert4Lean.X86.Asm.find_instr
          (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.add pos (Zpos xH))
            (ZArith.BinInt.Z.of_nat 1)) c1 = some i
        rw [heq']
        exact ih i c2' heq

theorem find_instr_tail : find_instr_tailStatement := by
  intro c1 i c2 pos h
  exact find_instr_tail_aux c1 pos (i :: c2) h i c2 rfl

end CompCert4Lean.Backend.Asmgenproof0

namespace CompCert4Lean.Backend.Asmgenproof0

theorem code_tail_next : code_tail_nextStatement := by
  intro fn ofs i c h
  have aux : ∀
      (ofs : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
      (fn c : CompCert4Lean.X86.Asm.code), code_tail ofs fn c →
      ∀ (i : CompCert4Lean.X86.Asm.instruction)
        (c' : CompCert4Lean.X86.Asm.code), c = i :: c' →
        code_tail
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH)) fn c' := by
    intro ofs fn c h
    induction h with
    | base c =>
        intro i c' heq
        subst c
        exact code_tail.step
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0
          i (code_tail.base c')
    | @step pos i0 c1 c2 h ih =>
        intro i c' heq
        exact code_tail.step _ i0 (ih i c' heq)
  exact aux ofs fn (i :: c) h i c rfl

theorem transl_code_rec_transl_code : transl_code_rec_transl_codeStatement := by
  intro f il ep k
  induction il generalizing ep k with
  | nil => rfl
  | cons i1 il ih =>
      simp only [CompCert4Lean.X86.Asmgen.transl_code_rec,
        CompCert4Lean.X86.Asmgen.transl_code]
      rw [ih]
      cases hcode : CompCert4Lean.X86.Asmgen.transl_code f il
          (CompCert4Lean.X86.Asmgen.it1_is_parent ep i1) with
      | Error msg => rfl
      | OK c1 => rfl

theorem transl_code'_transl_code : transl_code'_transl_codeStatement := by
  intro f il ep
  unfold CompCert4Lean.X86.Asmgen.transl_code'
  rw [transl_code_rec_transl_code]
  cases h : CompCert4Lean.X86.Asmgen.transl_code f il ep with
  | Error msg => rfl
  | OK c => rfl

end CompCert4Lean.Backend.Asmgenproof0

namespace CompCert4Lean.Backend.Asmgenproof0

theorem is_tail_code_tail : is_tail_code_tailStatement := by
  intro c1 c2 h
  induction h with
  | refl c =>
      exact ⟨CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0,
        code_tail.base c⟩
  | @cons i c1 c2 h ih =>
      rcases ih with ⟨ofs, hofs⟩
      exact ⟨CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH),
        code_tail.step ofs i hofs⟩

theorem code_tail_no_bigger : code_tail_no_biggerStatement := by
  intro pos c1 c2 h
  induction h with
  | base c => exact Nat.le_refl _
  | @step pos i c1 c2 h ih =>
      change c2.length ≤ c1.length + 1
      exact Nat.le_trans ih (Nat.le_succ _)

end CompCert4Lean.Backend.Asmgenproof0

namespace CompCert4Lean.Backend.Asmgenproof0

theorem transl_code_tail : transl_code_tailStatement := by
  intro transl_instr_tail f c1 c2 h
  induction h with
  | refl c =>
      intro tc2 ep2 htrans
      exact ⟨tc2, ep2, htrans, CompCert4Lean.Lib.Coqlib.is_tail.refl _⟩
  | @cons i c1 c2 h ih =>
      intro tc2 ep2 htrans
      simp only [CompCert4Lean.X86.Asmgen.transl_code] at htrans
      cases hcode : CompCert4Lean.X86.Asmgen.transl_code f c2
          (CompCert4Lean.X86.Asmgen.it1_is_parent ep2 i) with
      | Error msg =>
          rw [hcode] at htrans
          change CompCert4Lean.Common.Errors.bind _ _ = _ at htrans
          obtain ⟨k, hk, hrest⟩ :=
            CompCert4Lean.Common.Errors.bind_inversion _ _ _ _ _ htrans
          cases hk
      | OK k =>
          rw [hcode] at htrans
          change CompCert4Lean.Common.Errors.bind _ _ = _ at htrans
          obtain ⟨k', hk, hrest⟩ :=
            CompCert4Lean.Common.Errors.bind_inversion _ _ _ _ _ htrans
          have htail := ih k
            (CompCert4Lean.X86.Asmgen.it1_is_parent ep2 i) hcode
          have hk' : k = k' := by cases hk; rfl
          subst k'
          have htail_instr := transl_instr_tail f i ep2 k tc2 hrest
          rcases htail with ⟨tc1, ep1, htrans1, htail1⟩
          have htrans_tail : ∀ {l1 l2 l3 : AsmCode},
              CompCert4Lean.Lib.Coqlib.is_tail l1 l2 →
              CompCert4Lean.Lib.Coqlib.is_tail l2 l3 →
              CompCert4Lean.Lib.Coqlib.is_tail l1 l3 := by
            intro l1 l2 l3 h12 h23
            induction h23 with
            | refl => exact h12
            | cons i h23 ih =>
                exact CompCert4Lean.Lib.Coqlib.is_tail.cons i (ih h12)
          exact ⟨tc1, ep1, htrans1,
            htrans_tail htail1 htail_instr⟩

end CompCert4Lean.Backend.Asmgenproof0

namespace CompCert4Lean.Backend.Asmgenproof0

theorem code_tail_unique : code_tail_uniqueStatement := by
  intro fn c pos pos' h1 h2
  induction h1 generalizing pos' with
  | base c =>
      cases h2 with
      | base => rfl
      | @step pos' i c1 c2 h2' =>
          have hn := code_tail_no_bigger pos' c1 (i :: c1) h2'
          change Nat.succ c1.length ≤ c1.length at hn
          omega
  | @step pos i c1 c2 h ih =>
      cases h2 with
      | base =>
          have hn := code_tail_no_bigger pos c1 (i :: c1) h
          change Nat.succ c1.length ≤ c1.length at hn
          omega
      | @step pos' i' c1' c2' h2' =>
          have hi := ih pos' h2'
          cases hi
          rfl

end CompCert4Lean.Backend.Asmgenproof0

namespace CompCert4Lean.Backend.Asmgenproof0

theorem return_address_offset_correct : return_address_offset_correctStatement := by
  intro ge b ofs fb f c tf tc ofs' hpc hret
  cases hpc with
  | intro b ofs f c ep tf tc hfind htransf hcode htail =>
      have htail' := hret tf tc htransf hcode
      have hu := code_tail_unique tf.fn_code tc
        (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs)
        (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs') htail htail'
      apply CompCert4Lean.Lib.Integers.WordCore.ext
      exact hu.symm

end CompCert4Lean.Backend.Asmgenproof0

namespace CompCert4Lean.Backend.Asmgenproof0

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem label_pos_code_tail : label_pos_code_tailStatement := by
  intro lbl c pos c' hfind
  induction c generalizing pos c' with
  | nil =>
      simp [find_label] at hfind
  | cons a tl ih =>
      cases hlabel : CompCert4Lean.X86.Asm.is_label lbl a with
      | true =>
          simp [find_label, hlabel] at hfind
          cases hfind
          refine ⟨ZArith.BinInt.Z.add pos (Zpos xH), ?_, ?_, ?_, ?_⟩
          · simp [CompCert4Lean.X86.Asm.label_pos, hlabel]
            rfl
          · have hsub : ZArith.BinInt.Z.sub
                (ZArith.BinInt.Z.add pos (Zpos xH)) pos =
              ZArith.BinInt.Z.add ZArith.BinInt.Z.Z0 (Zpos xH) := by
                apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
                simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add,
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
                have hz0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                    ZArith.BinInt.Z.Z0 = 0 := by rfl
                rw [hz0]
                omega
            rw [hsub]
            exact code_tail.step ZArith.BinInt.Z.Z0 a (code_tail.base tl)
          · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ pos <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (ZArith.BinInt.Z.add pos (Zpos xH))
            simp only [ZArith.BinInt.Z.add,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
            have hone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (Zpos xH) = 1 := by rfl
            rw [hone]
            have hlen := list_length_z_nonneg tl
            change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Lib.Coqlib.list_length_z tl) at hlen
            omega
          · unfold ZArith.BinInt.Z.le
            simp only [ZArith.BinInt.Z.add,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
            rw [CompCert4Lean.Lib.Coqlib.list_length_z_cons]
            simp only [ZArith.BinInt.Z.add,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
            have hone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (Zpos xH) = 1 := by rfl
            rw [hone]
            have hlen := list_length_z_nonneg tl
            change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Lib.Coqlib.list_length_z tl) at hlen
            omega
      | false =>
          simp [find_label, hlabel] at hfind
          have hi := ih (ZArith.BinInt.Z.add pos (Zpos xH)) c' hfind
          rcases hi with ⟨pos', hpos', htail, hlt, hle⟩
          refine ⟨pos', ?_, ?_, ?_, ?_⟩
          · simp [CompCert4Lean.X86.Asm.label_pos, hlabel]
            exact hpos'
          · have hsub : ZArith.BinInt.Z.sub pos' pos =
                ZArith.BinInt.Z.add
                  (ZArith.BinInt.Z.sub pos'
                    (ZArith.BinInt.Z.add pos (Zpos xH))) (Zpos xH) := by
                apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
                simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add,
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
                omega
            rw [hsub]
            exact code_tail.step _ a htail
          · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ pos <
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ pos'
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (ZArith.BinInt.Z.add pos (Zpos xH)) <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ pos' at hlt
            simp only [ZArith.BinInt.Z.add,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hlt
            have hone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (Zpos xH) = 1 := by rfl
            rw [hone] at hlt
            omega
          · unfold ZArith.BinInt.Z.le
            simp only [ZArith.BinInt.Z.add,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
            rw [CompCert4Lean.Lib.Coqlib.list_length_z_cons]
            simp only [ZArith.BinInt.Z.add,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ pos' ≤
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ pos +
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                  (CompCert4Lean.Lib.Coqlib.list_length_z tl) + 1)
            unfold ZArith.BinInt.Z.le at hle
            simp only [ZArith.BinInt.Z.add,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hle
            have hone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (Zpos xH) = 1 := by rfl
            rw [hone] at hle
            omega

end CompCert4Lean.Backend.Asmgenproof0

namespace CompCert4Lean.Backend.Asmgenproof0

theorem tail_nolabel_trans : tail_nolabel_transStatement := by
  intro c1 c2 c3 h23 h12
  rcases h23 with ⟨ht23, hl23⟩
  rcases h12 with ⟨ht12, hl12⟩
  have htrans : ∀ {l1 l2 l3 : AsmCode},
      CompCert4Lean.Lib.Coqlib.is_tail l1 l2 →
      CompCert4Lean.Lib.Coqlib.is_tail l2 l3 →
      CompCert4Lean.Lib.Coqlib.is_tail l1 l3 := by
    intro l1 l2 l3 h12' h23'
    induction h23' with
    | refl => exact h12'
    | cons i h23' ih =>
        exact CompCert4Lean.Lib.Coqlib.is_tail.cons i (ih h12')
  constructor
  · exact htrans ht12 ht23
  · intro lbl
    rw [hl23, hl12]

end CompCert4Lean.Backend.Asmgenproof0

namespace CompCert4Lean.Backend.Asmgenproof0

theorem exec_straight_trans
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    exec_straight_transStatement := by
  intro ge fn c1 rs1 m1 c2 rs2 m2 c3 rs3 m3 h12 h23
  induction h12 with
  | exec_straight_one i c rs1 m1 rs2 m2 hstep hpc =>
      apply exec_straight_step
      · exact hstep
      · exact hpc
      · exact h23
  | exec_straight_step i c rs1 m1 rs2 m2 c' rs3 m3 hstep hpc htail ih =>
      apply exec_straight_step
      · exact hstep
      · exact hpc
      · exact ih h23

theorem exec_straight_two
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    exec_straight_twoStatement := by
  intro ge fn i1 i2 c rs1 m1 rs2 m2 rs3 m3 h1 h2 hpc1 hpc2
  apply exec_straight_step
  · exact h1
  · exact hpc1
  · apply exec_straight_one
    · exact h2
    · exact hpc2

theorem exec_straight_three
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    exec_straight_threeStatement := by
  intro ge fn i1 i2 i3 c rs1 m1 rs2 m2 rs3 m3 rs4 m4 h1 h2 h3 hpc1 hpc2 hpc3
  apply exec_straight_step
  · exact h1
  · exact hpc1
  · apply exec_straight_two
    · exact h2
    · exact h3
    · exact hpc2
    · exact hpc3

end CompCert4Lean.Backend.Asmgenproof0

namespace CompCert4Lean.Backend.Asmgenproof0

open Lean Elab Tactic Meta
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Common.Smallstep

private def asmgenproof_hidden_name (s : String) : Name :=
  s.splitOn "." |>.foldl
    (fun n p => if p == "0" then Name.num n 0 else Name.str n p)
    Name.anonymous

private theorem unsigned_repr_nat_asmgenproof (bits n : Nat) :
    CompCert4Lean.Lib.Integers.WordCore.unsigned
      (CompCert4Lean.Lib.Integers.WordCore.repr bits (ZArith.BinInt.Z.of_nat n)) =
      ZArith.BinInt.Z.of_nat (n % (2 ^ bits)) := by
  unfold CompCert4Lean.Lib.Integers.WordCore.unsigned
    CompCert4Lean.Lib.Integers.WordCore.repr
  run_tac
    let g ← getMainGoal
    let ctx ← getLCtx
    let mut nId? : Option FVarId := none
    let mut bitsId? : Option FVarId := none
    for decl in ctx do
      if decl.userName == `n then nId? := some decl.fvarId
      if decl.userName == `bits then bitsId? := some decl.fvarId
    let nId := nId?.get!
    let bitsId := bitsId?.get!
    let nm := asmgenproof_hidden_name
      "_private.CompCert4Lean.Lib.Integers.0.CompCert4Lean.Lib.Integers.WordCore.residue_zOfNat"
    let th ← mkAppM nm #[mkFVar bitsId, mkFVar nId]
    let fn := mkConst (asmgenproof_hidden_name
      "CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat")
    let pr ← mkAppM ``congrArg #[fn, th]
    let _ ← g.apply pr
    pure ()

private theorem unsigned_add_one_asmgenproof (ofs : Ptrofs)
    (hu : ZArith.BinInt.Z.lt (Ptrofs.unsigned ofs) Ptrofs.max_unsigned) :
    Ptrofs.unsigned (Ptrofs.add ofs Ptrofs.one) =
      ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) (ZArith.BinInt.Z.of_nat 1) := by
  have hnonneg : ZArith.BinInt.Z.le ZArith.BinInt.Z.Z0
      (Ptrofs.unsigned ofs) := by
    have h := ofs.intrange.1
    change (-1 : Int) < intOfZ (Ptrofs.unsigned ofs) at h
    change 0 ≤ intOfZ (Ptrofs.unsigned ofs)
    omega
  have hz : Ptrofs.unsigned ofs =
      ZArith.BinInt.Z.of_nat (ZArith.BinInt.Z.to_nat (Ptrofs.unsigned ofs)) := by
    exact (ZArith.Znat.Z2Nat.id _ hnonneg).symm
  have hsum : ZArith.BinInt.Z.add (Ptrofs.unsigned ofs)
      (ZArith.BinInt.Z.of_nat 1) =
      ZArith.BinInt.Z.of_nat
        (ZArith.BinInt.Z.to_nat (Ptrofs.unsigned ofs) + 1) := by
    calc
      ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) (ZArith.BinInt.Z.of_nat 1) =
          ZArith.BinInt.Z.add
            (ZArith.BinInt.Z.of_nat
              (ZArith.BinInt.Z.to_nat (Ptrofs.unsigned ofs)))
            (ZArith.BinInt.Z.of_nat 1) := by
              congr 1
      _ = ZArith.BinInt.Z.of_nat
          (ZArith.BinInt.Z.to_nat (Ptrofs.unsigned ofs) + 1) := by
        apply intOfZ_injective
        simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.of_nat,
          intOfZ_zOfInt]
        rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast, Int.ofNat_eq_natCast]
        rw [Int.natCast_add]
  have hmax' : intOfZ (Ptrofs.unsigned ofs) <
      (2 ^ Ptrofs.wordsize : Int) - 1 := by
    have hmax := hu
    change intOfZ (Ptrofs.unsigned ofs) < intOfZ Ptrofs.max_unsigned at hmax
    have hm : intOfZ Ptrofs.max_unsigned =
        (2 ^ Ptrofs.wordsize : Int) - 1 := by rfl
    rw [hm] at hmax
    exact hmax
  have hnatlt : ZArith.BinInt.Z.to_nat (Ptrofs.unsigned ofs) + 1 <
      2 ^ Ptrofs.wordsize := by
    have hnatcast : Int.ofNat (ZArith.BinInt.Z.to_nat
        (Ptrofs.unsigned ofs)) = intOfZ (Ptrofs.unsigned ofs) := by
      have hh := congrArg intOfZ (ZArith.Znat.Z2Nat.id _ hnonneg)
      simpa only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] using hh
    have hltint : Int.ofNat (ZArith.BinInt.Z.to_nat
        (Ptrofs.unsigned ofs)) + Int.ofNat 1 <
        (2 : Int) ^ Ptrofs.wordsize := by
      rw [hnatcast]
      change intOfZ (Ptrofs.unsigned ofs) + 1 <
        (2 : Int) ^ Ptrofs.wordsize
      omega
    have hcast : Int.ofNat (ZArith.BinInt.Z.to_nat
        (Ptrofs.unsigned ofs) + 1) =
        Int.ofNat (ZArith.BinInt.Z.to_nat (Ptrofs.unsigned ofs)) +
          Int.ofNat 1 := by
      rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast, Int.ofNat_eq_natCast,
        Int.natCast_add]
    have hltint_nat : Int.ofNat (ZArith.BinInt.Z.to_nat
        (Ptrofs.unsigned ofs) + 1) < Int.ofNat (2 ^ Ptrofs.wordsize) := by
      rw [hcast]
      have hpcast : Int.ofNat (2 ^ Ptrofs.wordsize) =
          (2 : Int) ^ Ptrofs.wordsize := by
        rw [Int.ofNat_eq_natCast, Int.natCast_pow]
        rfl
      rw [hpcast]
      exact hltint
    exact Int.ofNat_lt.mp hltint_nat
  change CompCert4Lean.Lib.Integers.WordCore.unsigned
      (CompCert4Lean.Lib.Integers.WordCore.repr Ptrofs.wordsize
        (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs)
          (Ptrofs.unsigned Ptrofs.one))) = _
  rw [show Ptrofs.unsigned Ptrofs.one =
      ZArith.BinInt.Z.of_nat 1 by rfl, hsum]
  rw [unsigned_repr_nat_asmgenproof]
  rw [Nat.mod_eq_of_lt hnatlt]

private theorem code_tail_next_int_asmgenproof : code_tail_next_intStatement := by
  intro fn ofs i c hlen htail
  have hb := code_tail_bounds_2 fn (Ptrofs.unsigned ofs) i c htail
  have hltmax : ZArith.BinInt.Z.lt (Ptrofs.unsigned ofs)
      Ptrofs.max_unsigned :=
    Int.lt_of_lt_of_le hb.2 hlen
  have hn := code_tail_next fn (Ptrofs.unsigned ofs) i c htail
  have hadd := unsigned_add_one_asmgenproof ofs hltmax
  rw [hadd]
  exact hn

theorem exec_straight_steps_1
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    exec_straight_steps_1Statement := by
  intro cfg xi ge fn c rs m c' rs' m'
  intro hexec hlen
  induction hexec with
  | exec_straight_one i c rs1 m1 rs2 m2 hstep hpc' =>
      intro b ofs hpc hfind htail
      apply plus_one
      apply CompCert4Lean.X86.Asm.exec_step_internal
      · exact hpc
      · exact hfind
      · exact find_instr_tail fn.fn_code i c
          (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) htail
      · exact hstep
  | exec_straight_step i c rs1 m1 rs2 m2 c' rs3 m3 hstep hpc' htail' ih =>
      intro b ofs hpc hfind htail
      apply plus_left'
      · apply CompCert4Lean.X86.Asm.exec_step_internal
        · exact hpc
        · exact hfind
        · exact find_instr_tail fn.fn_code i c
            (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) htail
        · exact hstep
      · apply ih b (CompCert4Lean.Lib.Integers.Ptrofs.add ofs
          CompCert4Lean.Lib.Integers.Ptrofs.one)
        · rw [hpc', hpc]
          rfl
        · exact hfind
        · exact code_tail_next_int_asmgenproof fn.fn_code ofs i c hlen htail
      · rfl

end CompCert4Lean.Backend.Asmgenproof0
