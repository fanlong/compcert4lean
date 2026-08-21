import CompCert4Lean.Foundation.RocqStdlib
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

private abbrev asmSP : Preg := .IR CompCert4Lean.X86.Asm.SP
private abbrev asmPC : Preg := .PC

private def asmStep (cfg : CompilerConfig) (xi : ExternalCalls) :
    AsmGenv → AsmState → trace → AsmState → Prop :=
  CompCert4Lean.X86.Asm.step cfg xi

/-! Agreement between machine and processor register states. -/

def agree (ms : MachRegset) (sp : Val) (rs : AsmRegset) : Prop :=
  rs asmSP = sp ∧
    sp ≠ Vundef ∧
    ∀ r : Mreg, Val.lessdef (ms r) (rs (CompCert4Lean.X86.Asm.preg_of r))

def agree_sp (ms : MachRegset) (sp : Val) (rs : AsmRegset)
    (h : agree ms sp rs) : rs asmSP = sp := h.1

def agree_sp_def (ms : MachRegset) (sp : Val) (rs : AsmRegset)
    (h : agree ms sp rs) : sp ≠ Vundef := h.2.1

def agree_mregs (ms : MachRegset) (sp : Val) (rs : AsmRegset)
    (h : agree ms sp rs) :
    ∀ r : Mreg, Val.lessdef (ms r) (rs (CompCert4Lean.X86.Asm.preg_of r)) :=
  h.2.2

/-! The suffix relation used for generated assembly code. -/

inductive code_tail : Z → AsmCode → AsmCode → Prop where
  | base (c : AsmCode) : code_tail ZArith.BinInt.Z.Z0 c c
  | step (pos : Z) (i : CompCert4Lean.X86.Asm.instruction)
      {c1 c2 : AsmCode} : code_tail pos c1 c2 →
      code_tail (ZArith.BinInt.Z.add pos (Zpos xH)) (i :: c1) c2

/-! Straight-line execution. -/

inductive exec_straight (ge : AsmGenv) (fn : AsmFunction) :
    AsmCode → AsmRegset → Mem → AsmCode → AsmRegset → Mem → Prop where
  | exec_straight_one (i1 : CompCert4Lean.X86.Asm.instruction)
      (c : AsmCode) (rs1 : AsmRegset) (m1 : Mem) (rs2 : AsmRegset) (m2 : Mem)
      (hstep : CompCert4Lean.X86.Asm.exec_instr ge fn i1 rs1 m1 = .Next rs2 m2)
      (hpc : rs2 asmPC = Val.offset_ptr (rs1 asmPC)
        CompCert4Lean.Lib.Integers.Ptrofs.one) :
      exec_straight ge fn (i1 :: c) rs1 m1 c rs2 m2
  | exec_straight_step (i : CompCert4Lean.X86.Asm.instruction)
      (c : AsmCode) (rs1 : AsmRegset) (m1 : Mem) (rs2 : AsmRegset) (m2 : Mem)
      (c' : AsmCode) (rs3 : AsmRegset) (m3 : Mem)
      (hstep : CompCert4Lean.X86.Asm.exec_instr ge fn i rs1 m1 = .Next rs2 m2)
      (hpc : rs2 asmPC = Val.offset_ptr (rs1 asmPC)
        CompCert4Lean.Lib.Integers.Ptrofs.one)
      (htail : exec_straight ge fn c rs2 m2 c' rs3 m3) :
      exec_straight ge fn (i :: c) rs1 m1 c' rs3 m3

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

/-! The stack relation is written as a recursive source-facing predicate so
    excluded generated constructor identities are not reintroduced. -/

def match_stack (ge : MachGenv) : List Mach.stackframe → Prop
  | [] => True
  | Mach.Stackframe fb sp ra c :: s =>
      (∃ f, Genv.find_funct_ptr ge fb = some (Internal f) ∧
        ∃ tf tc,
          transl_code_at_pc ge ra fb f c false tf tc ∧ sp ≠ Vundef) ∧
      match_stack ge s

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

def exec_straight_steps_1Statement : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (ge : AsmGenv)
    (fn : AsmFunction) (c : AsmCode) (rs : AsmRegset)
    (m : Mem) (c' : AsmCode) (rs' : AsmRegset) (m' : Mem),
    exec_straight ge fn c rs m c' rs' m' →
    ZArith.BinInt.Z.le (list_length_z fn.fn_code)
      CompCert4Lean.Lib.Integers.Ptrofs.max_unsigned →
    ∀ (b : Block) (ofs : Ptrofs),
      rs asmPC = Vptr b ofs →
      Genv.find_funct_ptr ge b = some (Internal fn) →
      code_tail (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) fn.fn_code c →
      plus (asmStep cfg xi) ge (.State rs m) E0 (.State rs' m')

def exec_straight_steps_2Statement : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction) (c : AsmCode) (rs : AsmRegset)
    (m : Mem) (c' : AsmCode) (rs' : AsmRegset) (m' : Mem),
    exec_straight ge fn c rs m c' rs' m' →
    ZArith.BinInt.Z.le (list_length_z fn.fn_code)
      CompCert4Lean.Lib.Integers.Ptrofs.max_unsigned →
    ∀ (b : Block) (ofs : Ptrofs),
      rs asmPC = Vptr b ofs →
      Genv.find_funct_ptr ge b = some (Internal fn) →
      code_tail (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) fn.fn_code c →
      ∃ ofs',
        rs' asmPC = Vptr b ofs' ∧
        code_tail (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs') fn.fn_code c'

def exec_straight_threeStatement : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction) (i1 i2 i3 : AsmInstruction)
    (c : AsmCode) (rs1 : AsmRegset) (m1 : Mem) (rs2 : AsmRegset) (m2 : Mem)
    (rs3 : AsmRegset) (m3 : Mem) (rs4 : AsmRegset) (m4 : Mem),
    CompCert4Lean.X86.Asm.exec_instr ge fn i1 rs1 m1 = .Next rs2 m2 →
    CompCert4Lean.X86.Asm.exec_instr ge fn i2 rs2 m2 = .Next rs3 m3 →
    CompCert4Lean.X86.Asm.exec_instr ge fn i3 rs3 m3 = .Next rs4 m4 →
    rs2 asmPC = Val.offset_ptr (rs1 asmPC) CompCert4Lean.Lib.Integers.Ptrofs.one →
    rs3 asmPC = Val.offset_ptr (rs2 asmPC) CompCert4Lean.Lib.Integers.Ptrofs.one →
    rs4 asmPC = Val.offset_ptr (rs3 asmPC) CompCert4Lean.Lib.Integers.Ptrofs.one →
    exec_straight ge fn (i1 :: i2 :: i3 :: c) rs1 m1 c rs4 m4

def exec_straight_transStatement : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction)
    (c1 : AsmCode) (rs1 : AsmRegset) (m1 : Mem)
    (c2 : AsmCode) (rs2 : AsmRegset) (m2 : Mem)
    (c3 : AsmCode) (rs3 : AsmRegset) (m3 : Mem),
    exec_straight ge fn c1 rs1 m1 c2 rs2 m2 →
    exec_straight ge fn c2 rs2 m2 c3 rs3 m3 →
    exec_straight ge fn c1 rs1 m1 c3 rs3 m3

def exec_straight_twoStatement : Prop :=
  ∀ (ge : AsmGenv) (fn : AsmFunction) (i1 i2 : AsmInstruction)
    (c : AsmCode) (rs1 : AsmRegset) (m1 : Mem) (rs2 : AsmRegset) (m2 : Mem)
    (rs3 : AsmRegset) (m3 : Mem),
    CompCert4Lean.X86.Asm.exec_instr ge fn i1 rs1 m1 = .Next rs2 m2 →
    CompCert4Lean.X86.Asm.exec_instr ge fn i2 rs2 m2 = .Next rs3 m3 →
    rs2 asmPC = Val.offset_ptr (rs1 asmPC) CompCert4Lean.Lib.Integers.Ptrofs.one →
    rs3 asmPC = Val.offset_ptr (rs2 asmPC) CompCert4Lean.Lib.Integers.Ptrofs.one →
    exec_straight ge fn (i1 :: i2 :: c) rs1 m1 c rs3 m3

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
