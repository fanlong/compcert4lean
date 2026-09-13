import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Backend.Deadcode
import CompCert4Lean.Backend.RTL
import CompCert4Lean.Backend.ValueAnalysis
import CompCert4Lean.Backend.NeedDomain
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Builtins
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.ExternalCalls
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Memdata
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Common.Values
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Maps

/-!
# Correctness surface for dead-code elimination

The executable relations and definitions assigned to this packet are kept as
ordinary Lean definitions.  The proof-heavy source declarations are exposed
as proposition-valued statement descriptors for the later proof phase.
-/

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Backend.Deadcode
open CompCert4Lean.Backend.NeedDomain
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
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private instance rtlFundefLinker : Linker RTL.fundef :=
  Linker_fundef RTL.function

private instance rtlProgramLinker : Linker RTL.program :=
  Linker_prog RTL.fundef Unit

private abbrev block := CompCert4Lean.Common.Values.block
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev memval := CompCert4Lean.Common.Memdata.memval
private abbrev fundef := CompCert4Lean.Backend.RTL.fundef
private abbrev function := CompCert4Lean.Backend.RTL.function
private abbrev program := CompCert4Lean.Backend.RTL.program
private abbrev state := CompCert4Lean.Backend.RTL.state
private abbrev genv := CompCert4Lean.Backend.RTL.genv
private abbrev stackframe := CompCert4Lean.Backend.RTL.stackframe
private abbrev reg := CompCert4Lean.Backend.Registers.reg
private abbrev regset := CompCert4Lean.Backend.RTL.regset
private abbrev node := CompCert4Lean.Backend.RTL.node
private abbrev instruction := CompCert4Lean.Backend.RTL.instruction
private abbrev trace := CompCert4Lean.Common.Events.trace
private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

/-! ## Program matching and memory agreement -/

def match_prog (cfg : CompilerConfig) (prog tprog : program) : Prop :=
  @match_program fundef Unit fundef Unit
    (Linker_fundef function) Linker_unit
    (fun cu f tf =>
      CompCert4Lean.Backend.Deadcode.transf_fundef
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg (prog_defmap cu) (romem_for cfg cu) f = .OK tf)
    (fun x y : Unit => x = y) prog tprog

abbrev locset := block → Z → Prop

structure magree (m1 m2 : mem) (P : locset) : Prop where
  ma_perm :
    ∀ b ofs k p, Mem.perm m1 b ofs k p → Mem.perm m2 b ofs k p
  ma_perm_inv :
    ∀ b ofs k p, Mem.perm m2 b ofs k p →
      Mem.perm m1 b ofs k p ∨ ¬ Mem.perm m1 b ofs Max Nonempty
  ma_memval :
    ∀ b ofs, Mem.perm m1 b ofs Cur Readable → P b ofs →
      memval_lessdef
        (ZMap.get ofs (PMap.get b m1.mem_contents))
        (ZMap.get ofs (PMap.get b m2.mem_contents))
  ma_nextblock : m2.nextblock = m1.nextblock

export magree (ma_perm ma_perm_inv ma_memval ma_nextblock)

/-! ## Static-analysis and state relations -/

def vanalyze (cfg : CompilerConfig) (cu : program) (f : function) : PMap.t VA.t :=
  ValueAnalysis.analyze
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    cfg (romem_for cfg cu) f

inductive match_stackframes (cfg : CompilerConfig) (prog : program) :
    stackframe → stackframe → Prop where
  | match_stackframes_intro
      (res : reg) (f : function) (sp : block) (pc : node)
      (e : regset) (tf : function) (te : regset) (cu : program)
      (an : PMap.t NA.t)
      (hlink : linkorder cu prog)
      (hfun : CompCert4Lean.Backend.Deadcode.transf_function
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg (prog_defmap cu) (romem_for cfg cu) f = .OK tf)
      (han : CompCert4Lean.Backend.Deadcode.analyze
        cfg f (prog_defmap cu) (vanalyze cfg cu f) = some an)
      (hres : ∀ v tv, Val.lessdef v tv →
        eagree
          (Regmap.set res v e) (Regmap.set res tv te)
          (CompCert4Lean.Backend.Deadcode.transfer
            cfg f (prog_defmap cu) (vanalyze cfg cu f) pc (PMap.get pc an)).1) :
      match_stackframes cfg prog
        (Stackframe res f (Vptr sp Ptrofs.zero) pc e)
        (Stackframe res tf (Vptr sp Ptrofs.zero) pc te)

export match_stackframes (match_stackframes_intro)

inductive match_states (cfg : CompilerConfig) (prog : program) :
    state → state → Prop where
  | match_regular_states
      (s : List stackframe) (f : function) (sp : block) (pc : node)
      (e : regset) (m : mem) (ts : List stackframe) (tf : function)
      (te : regset) (tm : mem) (cu : program) (an : PMap.t NA.t)
      (hstacks : list_forall2 (match_stackframes cfg prog) s ts)
      (hlink : linkorder cu prog)
      (hfun : CompCert4Lean.Backend.Deadcode.transf_function
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg (prog_defmap cu) (romem_for cfg cu) f = .OK tf)
      (han : CompCert4Lean.Backend.Deadcode.analyze
        cfg f (prog_defmap cu) (vanalyze cfg cu f) = some an)
      (henv : eagree e te
        (CompCert4Lean.Backend.Deadcode.transfer
          cfg f (prog_defmap cu) (vanalyze cfg cu f) pc (PMap.get pc an)).1)
      (hmem : magree m tm
        (fun b ofs => nlive (Genv.globalenv prog) sp
          (CompCert4Lean.Backend.Deadcode.transfer
            cfg f (prog_defmap cu) (vanalyze cfg cu f) pc (PMap.get pc an)).2 b ofs)) :
      match_states cfg prog
        (State s f (Vptr sp Ptrofs.zero) pc e m)
        (State ts tf (Vptr sp Ptrofs.zero) pc te tm)
  | match_call_states
      (s : List stackframe) (f : fundef) (args : List val) (m : mem)
      (ts : List stackframe) (tf : fundef) (targs : List val) (tm : mem)
      (cu : program)
      (hstacks : list_forall2 (match_stackframes cfg prog) s ts)
      (hlink : linkorder cu prog)
      (hfun : CompCert4Lean.Backend.Deadcode.transf_fundef
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg (prog_defmap cu) (romem_for cfg cu) f = .OK tf)
      (hargs : Val.lessdef_list args targs)
      (hmem : Mem.extends m tm) :
      match_states cfg prog
        (Callstate s f args m)
        (Callstate ts tf targs tm)
  | match_return_states
      (s : List stackframe) (v : val) (m : mem)
      (ts : List stackframe) (tv : val) (tm : mem)
      (hstacks : list_forall2 (match_stackframes cfg prog) s ts)
      (hres : Val.lessdef v tv)
      (hmem : Mem.extends m tm) :
      match_states cfg prog
        (Returnstate s v m)
        (Returnstate ts tv tm)

export match_states (match_regular_states match_call_states match_return_states)

/-! ## Simulation endpoint -/

def eventually (prog : program) (xi : ExternalCalls) (n : Nat)
    (s : state) (P : state → Prop) : Prop :=
  CompCert4Lean.Common.Smallstep.eventually
    (fun ge => CompCert4Lean.Backend.RTL.step
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge)
    CompCert4Lean.Backend.RTL.final_state
    (Genv.globalenv prog) n s P

/-! ## Exact statement descriptors for later proof migration -/

variable (cfg : CompilerConfig)

def transf_program_matchStatement : Prop :=
  ∀ (p tp : program),
    CompCert4Lean.Backend.Deadcode.transf_program
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg p = .OK tp →
      match_prog cfg p tp

def magree_monotoneStatement : Prop :=
  ∀ m1 m2 (P Q : locset), magree m1 m2 P →
    (∀ b ofs, Q b ofs → P b ofs) → magree m1 m2 Q

def mextends_agreeStatement : Prop :=
  ∀ m1 m2 (P : locset), Mem.extends m1 m2 → magree m1 m2 P

def magree_extendsStatement : Prop :=
  ∀ m1 m2 (P : locset), (∀ b ofs, P b ofs) →
    magree m1 m2 P → Mem.extends m1 m2

def magree_loadbytesStatement : Prop :=
  ∀ m1 m2 (P : locset) b ofs n bytes,
    magree m1 m2 P →
    Mem.loadbytes m1 b ofs n = some bytes →
    (∀ i, zLe ofs i ∧ zLt i (zAdd ofs n) → P b i) →
    ∃ bytes', Mem.loadbytes m2 b ofs n = some bytes' ∧
      list_forall2 memval_lessdef bytes bytes'

def magree_loadStatement : Prop :=
  ∀ m1 m2 (P : locset) chunk b ofs v,
    magree m1 m2 P →
    Mem.load chunk m1 b ofs = some v →
    (∀ i, zLe ofs i ∧ zLt i (zAdd ofs (size_chunk chunk)) → P b i) →
    ∃ v', Mem.load chunk m2 b ofs = some v' ∧ Val.lessdef v v'

def magree_storebytes_parallelStatement : Prop :=
  ∀ m1 m2 (P Q : locset) b ofs bytes1 m1' bytes2,
    magree m1 m2 P →
    Mem.storebytes m1 b ofs bytes1 = some m1' →
    (∀ b' i, Q b' i →
      b' ≠ b ∨ zLt i ofs ∨
        zLe (zAdd ofs (zOfNat bytes1.length)) i → P b' i) →
    list_forall2 memval_lessdef bytes1 bytes2 →
    ∃ m2', Mem.storebytes m2 b ofs bytes2 = some m2' ∧ magree m1' m2' Q

def magree_store_parallelStatement : Prop :=
  ∀ m1 m2 (P Q : locset) chunk b ofs v1 m1' v2,
    magree m1 m2 P →
    Mem.store chunk m1 b ofs v1 = some m1' →
    vagree v1 v2 (store_argument chunk) →
    (∀ b' i, Q b' i →
      b' ≠ b ∨ zLt i ofs ∨
        zLe (zAdd ofs (size_chunk chunk)) i → P b' i) →
    ∃ m2', Mem.store chunk m2 b ofs v2 = some m2' ∧ magree m1' m2' Q

def magree_storebytes_leftStatement : Prop :=
  ∀ m1 m2 (P : locset) b ofs bytes1 m1',
    magree m1 m2 P →
    Mem.storebytes m1 b ofs bytes1 = some m1' →
    (∀ i, zLe ofs i ∧ zLt i (zAdd ofs (zOfNat bytes1.length)) → ¬ P b i) →
    magree m1' m2 P

def magree_store_leftStatement : Prop :=
  ∀ m1 m2 (P : locset) chunk b ofs v1 m1',
    magree m1 m2 P →
    Mem.store chunk m1 b ofs v1 = some m1' →
    (∀ i, zLe ofs i ∧ zLt i (zAdd ofs (size_chunk chunk)) → ¬ P b i) →
    magree m1' m2 P

def magree_freeStatement : Prop :=
  ∀ m1 m2 (P Q : locset) b lo hi m1',
    magree m1 m2 P →
    Mem.free m1 b lo hi = some m1' →
    (∀ b' i, Q b' i → b' ≠ b ∨ ¬ (zLe lo i ∧ zLt i hi) → P b' i) →
    ∃ m2', Mem.free m2 b lo hi = some m2' ∧ magree m1' m2' Q

def magree_valid_accessStatement : Prop :=
  ∀ m1 m2 (P : locset) chunk b ofs p,
    magree m1 m2 P → Mem.valid_access m1 chunk b ofs p →
    Mem.valid_access m2 chunk b ofs p

def add_need_all_eagreeStatement : Prop :=
  ∀ e e' r ne, eagree e e' (add_need_all r ne) → eagree e e' ne

def add_need_all_lessdefStatement : Prop :=
  ∀ e e' r ne, eagree e e' (add_need_all r ne) →
    Val.lessdef (Regmap.get r e) (Regmap.get r e')

def add_need_eagreeStatement : Prop :=
  ∀ e e' r nv ne, eagree e e' (add_need r nv ne) → eagree e e' ne

def add_need_vagreeStatement : Prop :=
  ∀ e e' r nv ne, eagree e e' (add_need r nv ne) →
    vagree (Regmap.get r e) (Regmap.get r e') nv

def add_needs_all_lessdefStatement : Prop :=
  ∀ rl e e' ne, eagree e e' (add_needs_all rl ne) →
    Val.lessdef_list (rl.map (fun r => Regmap.get r e))
      (rl.map (fun r => Regmap.get r e'))

def add_needs_vagreeStatement : Prop :=
  ∀ rl nvl e e' ne, eagree e e' (add_needs rl nvl ne) →
    vagree_list
      (rl.map (fun r => Regmap.get r e))
      (rl.map (fun r => Regmap.get r e')) nvl

def eagree_init_regsStatement : Prop :=
  ∀ rl vl1 vl2 ne, Val.lessdef_list vl1 vl2 →
    eagree (init_regs vl1 rl) (init_regs vl2 rl) ne

def symbols_preservedStatement : Prop :=
  ∀ (prog tprog : program), match_prog cfg prog tprog → ∀ id,
    Genv.find_symbol (Genv.globalenv tprog) id =
      Genv.find_symbol (Genv.globalenv prog) id

def senv_preservedStatement : Prop :=
  ∀ (prog tprog : program), match_prog cfg prog tprog →
    Senv.equiv (Genv.to_senv (Genv.globalenv prog))
      (Genv.to_senv (Genv.globalenv tprog))

def functions_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog cfg prog tprog →
    ∀ (v : val) (f : fundef),
      Genv.find_funct (Genv.globalenv prog) v = some f →
      ∃ cu tf,
        Genv.find_funct (Genv.globalenv tprog) v = some tf ∧
        CompCert4Lean.Backend.Deadcode.transf_fundef
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          cfg (prog_defmap cu) (romem_for cfg cu) f = .OK tf ∧
        linkorder cu prog

def function_ptr_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog cfg prog tprog →
    ∀ (b : block) (f : fundef),
      Genv.find_funct_ptr (Genv.globalenv prog) b = some f →
      ∃ cu tf,
        Genv.find_funct_ptr (Genv.globalenv tprog) b = some tf ∧
        CompCert4Lean.Backend.Deadcode.transf_fundef
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          cfg (prog_defmap cu) (romem_for cfg cu) f = .OK tf ∧
        linkorder cu prog

def sig_function_translatedStatement : Prop :=
  ∀ dm rm f tf,
    CompCert4Lean.Backend.Deadcode.transf_fundef
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg dm rm f = .OK tf →
      RTL.funsig tf = RTL.funsig f

def stacksize_translatedStatement : Prop :=
  ∀ dm rm f tf,
    CompCert4Lean.Backend.Deadcode.transf_function
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg dm rm f = .OK tf →
      tf.fn_stacksize = f.fn_stacksize

def transf_function_atStatement : Prop :=
  ∀ cu f tf an pc instr,
    CompCert4Lean.Backend.Deadcode.transf_function
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      cfg (prog_defmap cu) (romem_for cfg cu) f = .OK tf →
    CompCert4Lean.Backend.Deadcode.analyze
      cfg f (prog_defmap cu) (vanalyze cfg cu f) = some an →
    PTree.get pc f.fn_code = some instr →
    PTree.get pc tf.fn_code = some
      (CompCert4Lean.Backend.Deadcode.transf_instr
        cfg (prog_defmap cu) (vanalyze cfg cu f) an pc instr)
def is_int_zero_soundStatement : Prop :=
  ∀ nv, CompCert4Lean.Backend.Deadcode.is_int_zero nv = true →
    nv = CompCert4Lean.Backend.NeedDomain.nval.I CompCert4Lean.Lib.Integers.Int.zero
def find_function_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog cfg prog tprog →
    ∀ (ros : Sum reg ident) (rs : regset) (fd : fundef) (trs : regset) ne,
      RTL.find_function (Genv.globalenv prog) ros rs = some fd →
      eagree rs trs (add_ros_need_all ros ne) →
      ∃ cu tfd,
        RTL.find_function (Genv.globalenv tprog) ros trs = some tfd ∧
        CompCert4Lean.Backend.Deadcode.transf_fundef
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          cfg (prog_defmap cu) (romem_for cfg cu) fd = .OK tfd ∧
        linkorder cu prog
def analyze_successorsStatement : Prop :=
  ∀ cu f an pc instr pc',
    CompCert4Lean.Backend.Deadcode.analyze
      cfg f (prog_defmap cu) (vanalyze cfg cu f) = some an →
    PTree.get pc f.fn_code = some instr →
    pc' ∈ RTL.successors_instr instr →
    NA.ge (PMap.get pc an)
      (CompCert4Lean.Backend.Deadcode.transfer
        cfg f (prog_defmap cu) (vanalyze cfg cu f) pc' (PMap.get pc' an))
def match_succ_statesStatement : Prop :=
  ∀ (prog : program) s f sp pc e m ts tf te tm an pc' cu instr ne nm,
    linkorder cu prog →
    list_forall2 (match_stackframes cfg prog) s ts →
    CompCert4Lean.Backend.Deadcode.transf_function
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      cfg (prog_defmap cu) (romem_for cfg cu) f = .OK tf →
    CompCert4Lean.Backend.Deadcode.analyze
      cfg f (prog_defmap cu) (vanalyze cfg cu f) = some an →
    PTree.get pc f.fn_code = some instr →
    pc' ∈ RTL.successors_instr instr →
    PMap.get pc an = (ne, nm) →
    eagree e te ne →
    magree m tm (fun b ofs => nlive (Genv.globalenv prog) sp nm b ofs) →
    match_states cfg prog
      (State s f (Vptr sp Ptrofs.zero) pc' e m)
      (State ts tf (Vptr sp Ptrofs.zero) pc' te tm)
def eagree_set_resStatement : Prop :=
  ∀ e1 e2 v1 v2 res ne,
    Val.lessdef v1 v2 →
    eagree e1 e2 (kill_builtin_res res ne) →
    eagree (regmap_setres res v1 e1) (regmap_setres res v2 e2) ne
def transfer_builtin_arg_soundStatement : Prop :=
  ∀ (prog : program) (bc : block_classification) e e' sp m m' a v,
    eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
      (fun r => Regmap.get r e) (Vptr sp Ptrofs.zero) m a v →
    ∀ nv ne1 nm1 ne2 nm2,
      transfer_builtin_arg nv (ne1, nm1) a = (ne2, nm2) →
      eagree e e' ne2 →
      magree m m' (fun b ofs => nlive (Genv.globalenv prog) sp nm2 b ofs) →
      genv_match bc (Genv.globalenv prog) →
      bc sp = BCstack →
      ∃ v',
        eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
          (fun r => Regmap.get r e') (Vptr sp Ptrofs.zero) m' a v' ∧
        vagree v v' nv ∧
        eagree e e' ne1 ∧
        magree m m' (fun b ofs => nlive (Genv.globalenv prog) sp nm1 b ofs)

def transfer_builtin_args_soundStatement : Prop :=
  ∀ (prog : program) e sp m e' m' bc al vl,
    eval_builtin_args (Genv.to_senv (Genv.globalenv prog))
      (fun r => Regmap.get r e) (Vptr sp Ptrofs.zero) m al vl →
    ∀ ne1 nm1 ne2 nm2,
      transfer_builtin_args (ne1, nm1) al = (ne2, nm2) →
      eagree e e' ne2 →
      magree m m' (fun b ofs => nlive (Genv.globalenv prog) sp nm2 b ofs) →
      genv_match bc (Genv.globalenv prog) →
      bc sp = BCstack →
      ∃ vl',
        eval_builtin_args (Genv.to_senv (Genv.globalenv prog))
          (fun r => Regmap.get r e') (Vptr sp Ptrofs.zero) m' al vl' ∧
        Val.lessdef_list vl vl' ∧
        eagree e e' ne1 ∧
        magree m m' (fun b ofs => nlive (Genv.globalenv prog) sp nm1 b ofs)

def can_eval_builtin_argStatement : Prop :=
  ∀ (prog tprog : program), match_prog cfg prog tprog →
    ∀ (sp : block) e m e' m' P,
    magree m m' P →
    ∀ a v,
      eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
        (fun r => Regmap.get r e) (Vptr sp Ptrofs.zero) m a v →
      ∃ v',
        eval_builtin_arg (Genv.to_senv (Genv.globalenv tprog))
          (fun r => Regmap.get r e') (Vptr sp Ptrofs.zero) m' a v'

def can_eval_builtin_argsStatement : Prop :=
  ∀ (prog tprog : program), match_prog cfg prog tprog →
    ∀ (sp : block) e m e' m' P,
    magree m m' P →
    ∀ al vl,
      eval_builtin_args (Genv.to_senv (Genv.globalenv prog))
        (fun r => Regmap.get r e) (Vptr sp Ptrofs.zero) m al vl →
      ∃ vl',
        eval_builtin_args (Genv.to_senv (Genv.globalenv tprog))
          (fun r => Regmap.get r e') (Vptr sp Ptrofs.zero) m' al vl'

def transf_volatile_storeStatement : Prop :=
  ∀ (prog : program) v1 v2 v1' v2' m tm chunk sp nm t v m',
    volatile_store_sem chunk (Genv.to_senv (Genv.globalenv prog))
      [v1, v2] m t v m' →
    Val.lessdef v1 v1' →
    vagree v2 v2' (store_argument chunk) →
    magree m tm (fun b ofs => nlive (Genv.globalenv prog) sp nm b ofs) →
    v = Vundef ∧
      ∃ tm',
        volatile_store_sem chunk (Genv.to_senv (Genv.globalenv prog))
          [v1', v2'] tm t Vundef tm' ∧
        magree m' tm' (fun b ofs => nlive (Genv.globalenv prog) sp nm b ofs)
def eagree_set_undefStatement : Prop :=
  ∀ e1 e2 ne r, eagree e1 e2 ne →
    eagree (Regmap.set r Vundef e1) e2 ne
def transf_external_callStatement : Prop :=
  ∀ (prog tprog : program), match_prog cfg prog tprog →
    ∀ xi e sp m args vargs ef t vres m' res
      ne2 nm2 ne1 nm1 bc te tm,
    eval_builtin_args (Genv.to_senv (Genv.globalenv prog))
      (fun r => Regmap.get r e) (Vptr sp Ptrofs.zero) m args vargs →
    external_call
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ef (Genv.to_senv (Genv.globalenv prog)) vargs m t vres m' →
    transfer_builtin_args (kill_builtin_res res ne2, nmem_all) args =
      (ne1, nm1) →
    eagree e te ne1 →
    magree m tm (fun b ofs => nlive (Genv.globalenv prog) sp nm1 b ofs) →
    genv_match bc (Genv.globalenv prog) →
    bc sp = BCstack →
    ∃ tvargs tvres tm',
      eval_builtin_args (Genv.to_senv (Genv.globalenv tprog))
        (fun r => Regmap.get r te) (Vptr sp Ptrofs.zero) tm args tvargs ∧
      external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ef (Genv.to_senv (Genv.globalenv tprog))
        tvargs tm t tvres tm' ∧
      eagree (regmap_setres res vres e) (regmap_setres res tvres te) ne2 ∧
      magree m' tm' (fun b ofs => nlive (Genv.globalenv prog) sp nm2 b ofs)
def step_simulationStatement : Prop :=
  ∀ (prog tprog : program), match_prog cfg prog tprog →
    ∀ (xi : ExternalCalls) S1 t S2,
    RTL.step
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) S1 t S2 →
    ∀ S1', match_states cfg prog S1 S1' →
      sound_state cfg prog S1 →
      (∃ S2',
        RTL.step
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          xi (Genv.globalenv tprog) S1' t S2' ∧
          match_states cfg prog S2 S2') ∨
      (∃ S2' n,
        plus (RTL.step
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi)
          (Genv.globalenv tprog) S1' t S2' ∧
          eventually prog xi n S2 (fun S3 => match_states cfg prog S3 S2'))

def transf_initial_statesStatement : Prop :=
  ∀ (prog tprog : program), match_prog cfg prog tprog →
    ∀ st1, RTL.initial_state prog st1 →
      ∃ st2, RTL.initial_state tprog st2 ∧ match_states cfg prog st1 st2

def transf_final_statesStatement : Prop :=
  ∀ (prog : program) st1 st2 r,
    match_states cfg prog st1 st2 →
    RTL.final_state st1 r → RTL.final_state st2 r

def transf_program_correctStatement : Prop :=
  ∀ (prog tprog : program) (xi : ExternalCalls),
    match_prog cfg prog tprog →
    forward_simulation
      (RTL.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi prog)
      (RTL.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi tprog)

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

theorem magree_loadbytes : magree_loadbytesStatement := by
  intro m1 m2 P b ofs n bytes h hload hP
  have getN_aux : ∀ (N : Nat)
      (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
      (c1 c2 : CompCert4Lean.Lib.Maps.ZMap.t CompCert4Lean.Common.Memdata.memval),
      (∀ i, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le p i ∧
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt i
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat N)) →
          CompCert4Lean.Common.Memdata.memval_lessdef
            (CompCert4Lean.Lib.Maps.ZMap.get i c1)
            (CompCert4Lean.Lib.Maps.ZMap.get i c2)) →
      CompCert4Lean.Lib.Coqlib.list_forall2
        CompCert4Lean.Common.Memdata.memval_lessdef
        (CompCert4Lean.Common.Memory.Mem.getN N p c1)
        (CompCert4Lean.Common.Memory.Mem.getN N p c2) := by
    intro N
    induction N with
    | zero =>
        intro p c1 c2 hN
        exact CompCert4Lean.Lib.Coqlib.list_forall2_nil _
    | succ N ih =>
        intro p c1 c2 hN
        apply CompCert4Lean.Lib.Coqlib.list_forall2.cons
        · apply hN p
          constructor
          · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ p ≤
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ p
            omega
          · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ p <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (N + 1)))
            simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
            omega
        · apply ih
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1)) c1 c2
          intro i hi
          apply hN i
          rcases hi with ⟨hile, hilt⟩
          constructor
          · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ p ≤
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ i
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1)) ≤
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ i at hile
            simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hile
            omega
          · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ i <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (N + 1)))
            simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ i <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add p
                    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1))
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat N)) at hilt
            simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hilt
            omega
  unfold CompCert4Lean.Common.Memory.Mem.loadbytes at hload
  generalize hd1 : CompCert4Lean.Common.Memory.Mem.range_perm_dec m1 b ofs
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs n)
      CompCert4Lean.Common.Memtype.Cur CompCert4Lean.Common.Memtype.Readable = d1 at hload
  cases d1 with
  | left hr1 =>
      simp [hd1] at hload
      rcases hload with ⟨_, hbytes⟩
      subst bytes
      have hr2 : CompCert4Lean.Common.Memory.Mem.range_perm m2 b ofs
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs n)
          CompCert4Lean.Common.Memtype.Cur CompCert4Lean.Common.Memtype.Readable := by
        intro i hi
        exact h.ma_perm b i CompCert4Lean.Common.Memtype.Cur
          CompCert4Lean.Common.Memtype.Readable (hr1 i hi)
      refine ⟨CompCert4Lean.Common.Memory.Mem.getN
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat n) ofs
          (CompCert4Lean.Lib.Maps.PMap.get b m2.mem_contents), ?_, ?_⟩
      · unfold CompCert4Lean.Common.Memory.Mem.loadbytes
        generalize hd2 : CompCert4Lean.Common.Memory.Mem.range_perm_dec m2 b ofs
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs n)
          CompCert4Lean.Common.Memtype.Cur CompCert4Lean.Common.Memtype.Readable = d2
        cases d2 with
        | left hp => rfl
        | right hn => exact False.elim (hn hr2)
      · by_cases hnpos : 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n
        · have hn_eq : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat n) = n := by
            exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Z2Nat.id n hnpos
          apply getN_aux
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat n) ofs
            (CompCert4Lean.Lib.Maps.PMap.get b m1.mem_contents)
            (CompCert4Lean.Lib.Maps.PMap.get b m2.mem_contents)
          intro i hi
          rw [hn_eq] at hi
          apply h.ma_memval b i
          · exact hr1 i hi
          · exact hP i hi
        · have hnzero :
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat n = 0 := by
            change Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n) = 0
            omega
          simpa [CompCert4Lean.Common.Memory.Mem.getN, hnzero] using
            (CompCert4Lean.Lib.Coqlib.list_forall2_nil
              CompCert4Lean.Common.Memdata.memval_lessdef)
  | right hr1 =>
      exact False.elim (by
        change none = some bytes at hload
        cases hload)

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

theorem magree_extends : magree_extendsStatement := by
  intro m1 m2 P hP h
  refine ⟨h.ma_nextblock.symm, ?_, h.ma_perm_inv⟩
  refine ⟨?_, ?_, ?_⟩
  · intro b1 b2 delta ofs k p hmap hp
    have hpair : (b1, (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)) =
        (b2, delta) := by
      simpa [CompCert4Lean.Common.Values.inject_id] using Option.some.inj hmap
    cases hpair
    change CompCert4Lean.Common.Memory.Mem.perm m2 b1
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs (.Z0)) k p
    have hzadd : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs (.Z0) = ofs := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs + 0)) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs
      rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      simp
    rw [hzadd]
    exact h.ma_perm b1 ofs k p hp
  · intro b1 b2 delta chunk ofs p hmap hp
    have hpair : (b1, (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)) =
        (b2, delta) := by
      simpa [CompCert4Lean.Common.Values.inject_id] using Option.some.inj hmap
    cases hpair
    refine ⟨.Z0, ?_⟩
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    change 0 = CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
        (CompCert4Lean.Common.Memdata.align_chunk chunk) (.Z0))
    change 0 = CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Common.Memdata.align_chunk chunk) * 0))
    rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    simp
  · intro b1 ofs b2 delta hmap hp
    have hpair : (b1, (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)) =
        (b2, delta) := by
      simpa [CompCert4Lean.Common.Values.inject_id] using Option.some.inj hmap
    cases hpair
    change CompCert4Lean.Common.Memdata.memval_inject CompCert4Lean.Common.Values.inject_id
      (CompCert4Lean.Lib.Maps.ZMap.get ofs (CompCert4Lean.Lib.Maps.PMap.get b1 m1.mem_contents))
      (CompCert4Lean.Lib.Maps.ZMap.get
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs (.Z0))
        (CompCert4Lean.Lib.Maps.PMap.get b1 m2.mem_contents))
    have hzadd : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs (.Z0) = ofs := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs + 0)) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs
      rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      simp
    rw [hzadd]
    exact h.ma_memval b1 ofs hp (hP b1 ofs)

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

theorem mextends_agree : mextends_agreeStatement := by
  intro m1 m2 P h
  have hzadd : ∀ ofs : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs (.Z0) = ofs := by
    intro ofs
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs + 0)) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ofs
    rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    simp
  refine ⟨?_, h.mext_perm_inv, ?_, h.mext_next.symm⟩
  · intro b ofs k p hp
    have hi := h.mext_inj.mi_perm b b (.Z0) ofs k p (by rfl) hp
    change CompCert4Lean.Common.Memory.Mem.perm m2 b
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs (.Z0)) k p at hi
    rw [hzadd ofs] at hi
    exact hi
  · intro b ofs hp hP
    have hi := h.mext_inj.mi_memval b ofs b (.Z0) (by rfl) hp
    unfold CompCert4Lean.Common.Memdata.memval_lessdef
    change CompCert4Lean.Common.Memdata.memval_inject CompCert4Lean.Common.Values.inject_id
      (CompCert4Lean.Lib.Maps.ZMap.get ofs (CompCert4Lean.Lib.Maps.PMap.get b m1.mem_contents))
      (CompCert4Lean.Lib.Maps.ZMap.get
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs (.Z0))
        (CompCert4Lean.Lib.Maps.PMap.get b m2.mem_contents)) at hi
    rw [hzadd ofs] at hi
    exact hi

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

theorem magree_monotone : magree_monotoneStatement := by
  intro m1 m2 P Q h hQ
  exact
    { ma_perm := h.ma_perm
      ma_perm_inv := h.ma_perm_inv
      ma_memval := fun b ofs hp hq => h.ma_memval b ofs hp (hQ b ofs hq)
      ma_nextblock := h.ma_nextblock }

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

theorem transf_program_match : ∀ cfg, transf_program_matchStatement cfg := by
  intro cfg p tp h
  unfold CompCert4Lean.Backend.Deadcode.transf_program
    CompCert4Lean.Common.AST.transform_partial_program
    CompCert4Lean.Common.AST.transform_partial_program2 at h
  have hlist :
      ∀ (xs : List (CompCert4Lean.Common.AST.ident ×
          CompCert4Lean.Common.AST.globdef
            CompCert4Lean.Backend.RTL.fundef Unit))
        (ys : List (CompCert4Lean.Common.AST.ident ×
          CompCert4Lean.Common.AST.globdef
            CompCert4Lean.Backend.RTL.fundef Unit)),
        CompCert4Lean.Common.AST.transf_globdefs
            (fun _ f => CompCert4Lean.Backend.Deadcode.transf_fundef
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate)
              cfg (CompCert4Lean.Common.AST.prog_defmap p)
              (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg p) f)
            (fun _ v => .OK v) xs = .OK ys →
          CompCert4Lean.Lib.Coqlib.list_forall2
            (CompCert4Lean.Common.Linking.match_ident_globdef
              (fun q f tf => CompCert4Lean.Backend.Deadcode.transf_fundef
                (binary64_certificate := binary64_certificate)
                (binary32_certificate := binary32_certificate)
                cfg (CompCert4Lean.Common.AST.prog_defmap q)
                (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg q) f = .OK tf)
              (fun x y : Unit => x = y) p) xs ys := by
    intro xs
    induction xs with
    | nil =>
        intro ys hys
        cases hys
        exact CompCert4Lean.Lib.Coqlib.list_forall2.nil _
    | cons hd tl ih =>
        intro ys hys
        cases hd with
        | mk id gd =>
            cases gd with
            | Gfun f =>
                cases hf : CompCert4Lean.Backend.Deadcode.transf_fundef
                    (binary64_certificate := binary64_certificate)
                    (binary32_certificate := binary32_certificate)
                    cfg (CompCert4Lean.Common.AST.prog_defmap p)
                    (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg p) f with
                | Error msg =>
                    simp [CompCert4Lean.Common.AST.transf_globdefs, hf] at hys
                | OK tf =>
                    cases ht : CompCert4Lean.Common.AST.transf_globdefs
                        (fun _ f => CompCert4Lean.Backend.Deadcode.transf_fundef
                          (binary64_certificate := binary64_certificate)
                          (binary32_certificate := binary32_certificate)
                          cfg (CompCert4Lean.Common.AST.prog_defmap p)
                          (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg p) f)
                        (fun _ v => .OK v) tl with
                    | Error msg =>
                        simp [CompCert4Lean.Common.AST.transf_globdefs, hf, ht] at hys
                    | OK ysTail =>
                        simp only [CompCert4Lean.Common.AST.transf_globdefs, hf, ht] at hys
                        cases hys
                        apply CompCert4Lean.Lib.Coqlib.list_forall2.cons
                        · constructor
                          · rfl
                          · apply CompCert4Lean.Common.Linking.match_globdef.match_globdef_fun
                              (ctx' := p)
                            · exact CompCert4Lean.Common.Linking.Linker.linkorder_refl p
                            · exact hf
                        · exact ih ysTail ht
            | Gvar v =>
                cases ht : CompCert4Lean.Common.AST.transf_globdefs
                    (fun _ f => CompCert4Lean.Backend.Deadcode.transf_fundef
                      (binary64_certificate := binary64_certificate)
                      (binary32_certificate := binary32_certificate)
                      cfg (CompCert4Lean.Common.AST.prog_defmap p)
                      (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg p) f)
                    (fun _ v => .OK v) tl with
                | Error msg =>
                    simp [CompCert4Lean.Common.AST.transf_globdefs,
                      CompCert4Lean.Common.AST.transf_globvar, ht] at hys
                | OK ysTail =>
                    simp only [CompCert4Lean.Common.AST.transf_globdefs,
                      CompCert4Lean.Common.AST.transf_globvar, ht] at hys
                    cases hys
                    apply CompCert4Lean.Lib.Coqlib.list_forall2.cons
                    · constructor
                      · rfl
                      · apply CompCert4Lean.Common.Linking.match_globdef.match_globdef_var
                        exact CompCert4Lean.Common.Linking.match_globvar.match_globvar_intro
                          _ _ _ _ _ _ rfl
                    · exact ih ysTail ht
  cases hdefs : CompCert4Lean.Common.AST.transf_globdefs
      (fun _ f => CompCert4Lean.Backend.Deadcode.transf_fundef
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg (CompCert4Lean.Common.AST.prog_defmap p)
        (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg p) f)
      (fun _ v => .OK v) p.prog_defs with
  | Error msg => simp [hdefs] at h
  | OK defs =>
      simp only [hdefs] at h
      cases h
      unfold match_prog CompCert4Lean.Common.Linking.match_program
        CompCert4Lean.Common.Linking.match_program_gen
      exact ⟨hlist p.prog_defs defs hdefs, rfl, rfl⟩

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem intOfZ_add_one_local (x : Z) :
    intOfZ (zAdd x (.Zpos .xH)) = intOfZ x + 1 := by
  change intOfZ (zOfInt (intOfZ x + intOfZ (.Zpos .xH))) = intOfZ x + 1
  rw [intOfZ_zOfInt]
  rfl

private theorem pmap_get_set_same_local {A : Type} (i : positive) (x : A)
    (m : PMap.t A) : PMap.get i (PMap.set i x m) = x := by
  change (match PTree.get i (PTree.set i x m.2) with
    | some y => y
    | none => m.1) = x
  rw [PTree.gsspec_proof]
  cases hpeq : peq i i with
  | left h => simp [hpeq]
  | right h => exact False.elim (h rfl)

private theorem pmap_get_set_other_local {A : Type} (i j : positive) (x : A)
    (m : PMap.t A) (h : i ≠ j) : PMap.get i (PMap.set j x m) = PMap.get i m := by
  change (match PTree.get i (PTree.set j x m.2) with
    | some y => y
    | none => m.1) =
    (match PTree.get i m.2 with
    | some y => y
    | none => m.1)
  rw [PTree.gsspec_proof]
  cases hpeq : peq i j with
  | left hij => exact False.elim (h hij)
  | right hne => simp [hpeq]

private theorem zmap_get_set_same_local {A : Type} (i : Z) (x : A)
    (m : ZMap.t A) : ZMap.get i (ZMap.set i x m) = x := by
  exact pmap_get_set_same_local (ZIndexed.index i) x m

private theorem zmap_get_set_other_local {A : Type} (i j : Z) (x : A)
    (m : ZMap.t A) (h : i ≠ j) : ZMap.get i (ZMap.set j x m) = ZMap.get i m := by
  apply pmap_get_set_other_local (ZIndexed.index i) (ZIndexed.index j) x m
  intro hij
  apply h
  exact ZIndexed.index_inj i j hij

private theorem setN_outside_local : ∀ (vl : List memval) (c : ZMap.t memval)
    (p q : Z),
    zLt q p ∨ zLe (zAdd p (zOfNat vl.length)) q →
      ZMap.get q (CompCert4Lean.Common.Memory.Mem.setN vl p c) = ZMap.get q c
  | [], c, p, q, h => rfl
  | v :: rest, c, p, q, h => by
      have hTail : zLt q (zAdd p (.Zpos .xH)) ∨
          zLe (zAdd (zAdd p (.Zpos .xH)) (zOfNat rest.length)) q := by
        rcases h with hlt | hge
        · left
          change intOfZ q < intOfZ (zAdd p (.Zpos .xH))
          rw [intOfZ_add_one_local]
          change intOfZ q < intOfZ p at hlt
          omega
        · right
          change intOfZ (zAdd (zAdd p (.Zpos .xH)) (zOfNat rest.length)) ≤ intOfZ q
          change intOfZ (zAdd p (zOfNat (List.length (v :: rest)))) ≤ intOfZ q at hge
          have hlen : (List.length (v :: rest) : Nat) = rest.length + 1 := by rfl
          rw [hlen] at hge
          simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
            intOfZ_zOfInt] at hge ⊢
          have hone : intOfZ (.Zpos .xH) = 1 := by rfl
          simp [hone] at hge ⊢
          omega
      have hs := setN_outside_local rest (ZMap.set p v c)
        (zAdd p (.Zpos .xH)) q hTail
      have hneq : q ≠ p := by
        intro heq
        subst q
        rcases h with hlt | hge
        · change intOfZ p < intOfZ p at hlt
          omega
        · change intOfZ (zAdd p (zOfNat (List.length (v :: rest)))) ≤ intOfZ p at hge
          simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
            intOfZ_zOfInt] at hge
          omega
      rw [zmap_get_set_other_local q p v c hneq] at hs
      simpa [CompCert4Lean.Common.Memory.Mem.setN] using hs

theorem magree_storebytes_left : magree_storebytes_leftStatement := by
  intro m1 m2 P b ofs bytes1 m1' h hstore hP
  unfold CompCert4Lean.Common.Memory.Mem.storebytes at hstore
  split at hstore
  next hcond =>
    injection hstore with hm1'
    subst m1'
    constructor
    · intro b' ofs' k p hp
      exact h.ma_perm b' ofs' k p hp
    · intro b' ofs' k p hp
      exact h.ma_perm_inv b' ofs' k p hp
    · intro b' ofs' hp hPb'
      by_cases hbb : b' = b
      · subst b'
        rw [pmap_get_set_same_local]
        have hnotrange : ¬ (zLe ofs ofs' ∧
            zLt ofs' (zAdd ofs (zOfNat bytes1.length))) := by
          intro hr
          exact (hP ofs' hr) hPb'
        have hOut : zLt ofs' ofs ∨
            zLe (zAdd ofs (zOfNat bytes1.length)) ofs' := by
          change intOfZ ofs' < intOfZ ofs ∨
            intOfZ (zAdd ofs (zOfNat bytes1.length)) ≤ intOfZ ofs'
          by_cases hlt : intOfZ ofs' < intOfZ ofs
          · exact Or.inl hlt
          · right
            by_cases hge : intOfZ (zAdd ofs (zOfNat bytes1.length)) ≤ intOfZ ofs'
            · exact hge
            · exfalso
              apply hnotrange
              change intOfZ ofs ≤ intOfZ ofs' ∧
                intOfZ ofs' < intOfZ (zAdd ofs (zOfNat bytes1.length))
              constructor <;> omega
        have hset := setN_outside_local bytes1
          (PMap.get b m1.mem_contents) ofs ofs' hOut
        change memval_lessdef
          (ZMap.get ofs' (CompCert4Lean.Common.Memory.Mem.setN bytes1 ofs
            (PMap.get b m1.mem_contents)))
          (ZMap.get ofs' (PMap.get b m2.mem_contents))
        rw [hset]
        exact h.ma_memval b ofs' hp hPb'
      · change memval_lessdef
          (ZMap.get ofs'
            (PMap.get b' (PMap.set b
              (CompCert4Lean.Common.Memory.Mem.setN bytes1 ofs
                (PMap.get b m1.mem_contents)) m1.mem_contents)))
          (ZMap.get ofs' (PMap.get b' m2.mem_contents))
        rw [pmap_get_set_other_local _ _ _ _ hbb]
        exact h.ma_memval b' ofs' hp hPb'
    · simpa using h.ma_nextblock
  next hcond =>
    cases hstore

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

theorem magree_valid_access : magree_valid_accessStatement := by
  intro m1 m2 P chunk b ofs p hma hvalid
  constructor
  · intro ofs' hofs'
    exact hma.ma_perm b ofs' CompCert4Lean.Common.Memtype.Cur p (hvalid.1 ofs' hofs')
  · exact hvalid.2

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem pgetsetN_local (q r : positive) (v : NVal.t) (m : NE.t) :
    PTree.get q (PTree.set r v m) =
      match peq q r with | .left _ => some v | .right _ => PTree.get q m := by
  exact @PTree.gsspec_proof NVal.t q r v m

private theorem premoveN_local (q r : positive) (m : NE.t) :
    PTree.get q (PTree.remove r m) =
      if h : q = r then none else PTree.get q m := by
  exact @PTree.getRemove_equation NVal.t q r m

private theorem peq_self_local (r : positive) : peq r r = .left rfl := by
  cases h : peq r r with
  | left heq => cases heq; rfl
  | right hne => exact False.elim (hne rfl)

private theorem ne_get_set_local (r q : positive) (v : nval) (ne : nenv) :
    NE.get q (NE.set r v ne) =
      match peq q r with | .left _ => (v : NVal.t) | .right _ => NE.get q ne := by
  cases v with
  | Nothing =>
      have hbeq : NVal.beq Nothing NVal.bot = true := by rfl
      unfold NE.get NE.set
      rw [hbeq]
      simp only [↓reduceIte]
      have hs := premoveN_local q r ne
      rw [hs]
      cases h : peq q r with
      | left hqr => subst r; simp [NVal.bot] <;> rfl
      | right hqr => simp [hqr]
  | I m =>
      have hbeq : NVal.beq (I m) NVal.bot = false := by rfl
      unfold NE.get NE.set
      rw [hbeq]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hs := pgetsetN_local q r (I m : NVal.t) ne
      rw [hs]
      cases h : peq q r with
      | left hqr => simp only [h]; rfl
      | right hqr => simp only [h]
  | L m =>
      have hbeq : NVal.beq (L m) NVal.bot = false := by rfl
      unfold NE.get NE.set
      rw [hbeq]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hs := pgetsetN_local q r (L m : NVal.t) ne
      rw [hs]
      cases h : peq q r with
      | left hqr => simp only [h]; rfl
      | right hqr => simp only [h]
  | All =>
      have hbeq : NVal.beq All NVal.bot = false := by rfl
      unfold NE.get NE.set
      rw [hbeq]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hs := pgetsetN_local q r (All : NVal.t) ne
      rw [hs]
      cases h : peq q r with
      | left hqr =>
          simp only [h]
          change (All : NVal.t) = All
          rfl
      | right hqr => simp only [h]

theorem add_need_all_eagree : add_need_all_eagreeStatement := by
  intro e e' r ne h r0
  change eagree e e' (NE.set r All ne) at h
  have hr := h r0
  rw [ne_get_set_local r r0 All ne] at hr
  cases hp : peq r0 r with
  | left hEq =>
      simp only [hp] at hr
      exact nge_agree _ _ _ _ (nge.nge_nothing _) hr
  | right hNe =>
      simp only [hp] at hr
      exact hr

theorem add_need_all_lessdef : add_need_all_lessdefStatement := by
  intro e e' r ne h
  change eagree e e' (NE.set r All ne) at h
  have hr := h r
  rw [ne_get_set_local r r All ne] at hr
  rw [peq_self_local r] at hr
  change Val.lessdef (Regmap.get r e) (Regmap.get r e') at hr
  exact hr

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers
open Lean Elab Tactic Meta

private def privateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem residue_zOfNat_local (bits n : Nat) :
    (WordCore.repr bits (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)).val = n % (2 ^ bits) := by
  run_tac
    let lctx ← getLCtx
    let bitsF := (lctx.findFromUserName? `bits).get!
    let nF := (lctx.findFromUserName? `n).get!
    let bitsE := mkFVar bitsF.fvarId
    let nE := mkFVar nF.fvarId
    let z := mkApp (mkConst ``CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat) nE
    let e1 := mkApp2 (mkConst (privateName "CompCert4Lean.Lib.Integers.WordCore.val_repr_residue")) bitsE z
    let e2 := mkApp2 (mkConst (privateName "CompCert4Lean.Lib.Integers.WordCore.residue_zOfNat")) bitsE nE
    let t1 ← inferType e1
    let t2 ← inferType e2
    let (α, lhs, mid) := match_expr t1 with
      | _root_.Eq α lhs mid => (α, lhs, mid)
      | _ => panic! "not eq1"
    let (_, _, rhs) := match_expr t2 with
      | _root_.Eq _ mid' rhs => (α, mid', rhs)
      | _ => panic! "not eq2"
    let eqtrans := mkConst ``Eq.trans [.succ .zero]
    let e := mkAppN eqtrans #[α, lhs, mid, rhs, e1, e2]
    closeMainGoal Name.anonymous e

private theorem int_or_val_local (x y : Int.int) :
    (Int.or x y).val = Nat.lor x.val y.val % (2 ^ Int.wordsize) := by
  unfold Int.or WordCore.or
  exact residue_zOfNat_local Int.wordsize (Nat.lor x.val y.val)

private theorem int64_or_val_local (x y : Int64.int) :
    (Int64.or x y).val = Nat.lor x.val y.val % (2 ^ Int64.wordsize) := by
  unfold Int64.or WordCore.or
  exact residue_zOfNat_local Int64.wordsize (Nat.lor x.val y.val)

private theorem word_val_lt_local (x : Int.int) : x.val < 2 ^ Int.wordsize := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let xE := mkFVar xF.fvarId
    let e ← mkAppM (privateName "CompCert4Lean.Lib.Integers.WordCore.val_lt") #[xE]
    closeMainGoal Name.anonymous e

private theorem word64_val_lt_local (x : Int64.int) : x.val < 2 ^ Int64.wordsize := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let xE := mkFVar xF.fvarId
    let e ← mkAppM (privateName "CompCert4Lean.Lib.Integers.WordCore.val_lt") #[xE]
    closeMainGoal Name.anonymous e

private theorem nat_or_mod_testbit (a b w k : Nat) (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    (Nat.lor a b % 2 ^ w).testBit k = (a.testBit k || b.testBit k) := by
  rw [Nat.testBit_mod_two_pow]
  by_cases hk : k < w
  · simp only [hk]
    simpa using (Nat.testBit_or a b k)
  · have hkw : w ≤ k := Nat.le_of_not_gt hk
    have hpow : 2 ^ w ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hkw
    have ha' : a < 2 ^ k := Nat.lt_of_lt_of_le ha hpow
    have hb' : b < 2 ^ k := Nat.lt_of_lt_of_le hb hpow
    have hfa := Nat.testBit_lt_two_pow ha'
    have hfb := Nat.testBit_lt_two_pow hb'
    simp [hk, hfa, hfb]

private theorem int_or_testbit_local (x y : Int.int) (i : Z) :
    Int.testbit (Int.or x y) i = (Int.testbit x i || Int.testbit y i) := by
  cases i with
  | Zneg p => rfl
  | Z0 =>
      simp only [Int.testbit, WordCore.testbit]
      change Nat.testBit (Int.or x y).val 0 = (Nat.testBit x.val 0 || Nat.testBit y.val 0)
      rw [int_or_val_local]
      exact nat_or_mod_testbit x.val y.val Int.wordsize 0
        (word_val_lt_local x) (word_val_lt_local y)
  | Zpos p =>
      simp only [Int.testbit, WordCore.testbit]
      change Nat.testBit (Int.or x y).val _ = _
      rw [int_or_val_local]
      exact nat_or_mod_testbit x.val y.val Int.wordsize _
        (word_val_lt_local x) (word_val_lt_local y)

private theorem int64_or_testbit_local (x y : Int64.int) (i : Z) :
    Int64.testbit (Int64.or x y) i = (Int64.testbit x i || Int64.testbit y i) := by
  cases i with
  | Zneg p => rfl
  | Z0 =>
      simp only [Int64.testbit, WordCore.testbit]
      change Nat.testBit (Int64.or x y).val 0 = (Nat.testBit x.val 0 || Nat.testBit y.val 0)
      rw [int64_or_val_local]
      exact nat_or_mod_testbit x.val y.val Int64.wordsize 0
        (word64_val_lt_local x) (word64_val_lt_local y)
  | Zpos p =>
      simp only [Int64.testbit, WordCore.testbit]
      change Nat.testBit (Int64.or x y).val _ = _
      rw [int64_or_val_local]
      exact nat_or_mod_testbit x.val y.val Int64.wordsize _
        (word64_val_lt_local x) (word64_val_lt_local y)

private theorem nge_lub_r_local : ∀ x y : nval, nge (nlub x y) y := by
  intro x y
  cases y with
  | Nothing =>
      cases x with
      | Nothing => exact nge.nge_all Nothing
      | I m => exact nge.nge_all (I m)
      | L m => exact nge.nge_all (L m)
      | All => exact nge.nge_all All
  | All =>
      cases x <;> exact nge.nge_nothing All
  | I m2 =>
      cases x with
      | Nothing =>
          apply nge.nge_int m2 m2
          intro i hi hm
          exact hm
      | I m1 =>
          apply nge.nge_int (Int.or m1 m2) m2
          intro i hi hm
          rw [int_or_testbit_local]
          exact Bool.or_eq_true_iff.mpr (Or.inr hm)
      | L m1 => exact nge.nge_nothing (I m2)
      | All => exact nge.nge_nothing (I m2)
  | L m2 =>
      cases x with
      | Nothing =>
          apply nge.nge_long m2 m2
          intro i hi hm
          exact hm
      | I m1 => exact nge.nge_nothing (L m2)
      | L m1 =>
          apply nge.nge_long (Int64.or m1 m2) m2
          intro i hi hm
          rw [int64_or_testbit_local]
          exact Bool.or_eq_true_iff.mpr (Or.inr hm)
      | All => exact nge.nge_nothing (L m2)

theorem add_need_eagree : add_need_eagreeStatement := by
  intro e e' r nv ne h r0
  change eagree e e' (NE.set r (nlub nv (NE.get r ne)) ne) at h
  have hr := h r0
  rw [ne_get_set_local r r0 (nlub nv (NE.get r ne)) ne] at hr
  cases hp : peq r0 r with
  | left hEq =>
      subst r0
      simp only [hp] at hr
      exact nge_agree _ _ _ _ (nge_lub_r_local nv (NE.get r ne)) hr
  | right hNe =>
      simp only [hp] at hr
      exact hr

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Backend.Deadcode
open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private theorem nge_lub_l_local : ∀ x y : nval, nge (nlub x y) x := by
  intro x y
  cases x with
  | Nothing => exact nge.nge_all y
  | All =>
      cases y <;> exact nge.nge_nothing All
  | I m1 =>
      cases y with
      | Nothing =>
          apply nge.nge_int m1 m1
          intro i hi hm
          exact hm
      | I m2 =>
          apply nge.nge_int (Int.or m1 m2) m1
          intro i hi hm
          rw [int_or_testbit_local]
          exact Bool.or_eq_true_iff.mpr (Or.inl hm)
      | L m => exact nge.nge_nothing (I m1)
      | All => exact nge.nge_nothing (I m1)
  | L m1 =>
      cases y with
      | Nothing =>
          apply nge.nge_long m1 m1
          intro i hi hm
          exact hm
      | I m => exact nge.nge_nothing (L m1)
      | L m2 =>
          apply nge.nge_long (Int64.or m1 m2) m1
          intro i hi hm
          rw [int64_or_testbit_local]
          exact Bool.or_eq_true_iff.mpr (Or.inl hm)
      | All => exact nge.nge_nothing (L m1)

theorem add_need_vagree : add_need_vagreeStatement := by
  intro e e' r nv ne h
  change eagree e e' (NE.set r (nlub nv (NE.get r ne)) ne) at h
  have hr := h r
  rw [ne_get_set_local r r (nlub nv (NE.get r ne)) ne] at hr
  rw [peq_self_local r] at hr
  exact nge_agree _ _ _ _ (nge_lub_l_local nv (NE.get r ne)) hr

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Backend.Deadcode
open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Maps

theorem add_needs_all_lessdef : add_needs_all_lessdefStatement := by
  intro rl
  induction rl with
  | nil =>
      intro e e' ne h
      exact Val.lessdef_list_nil
  | cons r rs ih =>
      intro e e' ne h
      apply Val.lessdef_list_cons
      · exact add_need_all_lessdef e e' r (add_needs_all rs ne) h
      · apply ih e e' ne
        exact add_need_all_eagree e e' r (add_needs_all rs ne) h

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Backend.Deadcode
open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Maps

theorem add_needs_vagree : add_needs_vagreeStatement := by
  intro rl
  induction rl with
  | nil =>
      intro nvl e e' ne h
      exact vagree_list.vagree_list_nil nvl
  | cons r rs ih =>
      intro nvl e e' ne h
      cases nvl with
      | nil =>
          apply vagree_lessdef_list
          exact add_needs_all_lessdef (r :: rs) e e' ne h
      | cons nv nvs =>
          apply vagree_list.vagree_list_cons
          · exact add_need_vagree e e' r nv (add_needs rs nvs ne) h
          · exact ih nvs e e' ne (add_need_eagree e e' r nv (add_needs rs nvs ne) h)

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Backend.Deadcode
open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueAnalysis
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

variable
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53)
        (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24)
        (ZArith.BinInt.Z.of_nat 128)]

private theorem deadcode_symbol_add_global
    {A B V W : Type} (ge1 : Genv.t A V) (ge2 : Genv.t B W) (id : ident)
    (hm : ∀ id', PTree.get id' ge2.genv_symb = PTree.get id' ge1.genv_symb)
    (hn : ge2.genv_next = ge1.genv_next) :
    ∀ id', PTree.get id' (PTree.set id ge2.genv_next ge2.genv_symb) =
      PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb) := by
  intro id'
  have h2 := @PTree.getSet_equation _ id' id ge2.genv_next ge2.genv_symb
  have h1 := @PTree.getSet_equation _ id' id ge1.genv_next ge1.genv_symb
  by_cases h : id' = id
  · rw [h2, h1]
    simp only [dif_pos h]
    exact congrArg some hn
  · rw [h2, h1]
    simp only [dif_neg h]
    exact hm id'

private theorem deadcode_match_genvs_add_global
    {A B V W : Type} (R : globdef A V → globdef B W → Prop)
    (ge1 : Genv.t A V) (ge2 : Genv.t B W) (id : ident)
    (g1 : globdef A V) (g2 : globdef B W)
    (hm : Genv.match_genvs R ge1 ge2) (hg : R g1 g2) :
    Genv.match_genvs R (Genv.add_global ge1 (id, g1))
      (Genv.add_global ge2 (id, g2)) := by
  constructor
  · exact congrArg _ hm.mge_next
  · exact deadcode_symbol_add_global ge1 ge2 id hm.mge_symb hm.mge_next
  · intro b
    change option_rel R
      (PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs))
      (PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs))
    have h1 := @PTree.getSet_equation (globdef A V) b ge1.genv_next g1 ge1.genv_defs
    have h2 := @PTree.getSet_equation (globdef B W) b ge2.genv_next g2 ge2.genv_defs
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

private theorem deadcode_match_genvs_add_globals
    {A B V W : Type} (R : globdef A V → globdef B W → Prop)
    (xs : List (ident × globdef A V)) (ys : List (ident × globdef B W))
    (hxy : list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) xs ys)
    (ge1 : Genv.t A V) (ge2 : Genv.t B W) (hm : Genv.match_genvs R ge1 ge2) :
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
      exact deadcode_match_genvs_add_global R ge1 ge2 aid ag bg hm hab

private theorem deadcode_globalenv_match
    {C F1 V1 F2 V2 : Type} [Linker C]
    (mf : C → F1 → F2 → Prop) (mv : V1 → V2 → Prop) (ctx : C)
    (p : CompCert4Lean.Common.AST.program F1 V1)
    (tp : CompCert4Lean.Common.AST.program F2 V2)
    (h : match_program_gen mf mv ctx p tp) :
    Genv.match_genvs (match_globdef mf mv ctx)
      (Genv.globalenv p) (Genv.globalenv tp) := by
  rcases h with ⟨hdefs, hmain, hpub⟩
  unfold Genv.globalenv
  rw [hpub]
  apply deadcode_match_genvs_add_globals
  · exact hdefs
  · constructor
    · rfl
    · intro id
      rfl
    · intro b
      exact option_rel.none _

private theorem deadcode_volatile_match
    {C F1 V1 F2 V2 : Type} [Linker C]
    (mf : C → F1 → F2 → Prop) (mv : V1 → V2 → Prop) (ctx : C)
    (p : CompCert4Lean.Common.AST.program F1 V1)
    (tp : CompCert4Lean.Common.AST.program F2 V2)
    (hge : Genv.match_genvs (match_globdef mf mv ctx)
      (Genv.globalenv p) (Genv.globalenv tp))
    (b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) :
    Genv.block_is_volatile (Genv.globalenv tp) b =
      Genv.block_is_volatile (Genv.globalenv p) b := by
  unfold Genv.block_is_volatile Genv.find_var_info Genv.find_def
  have hrel := hge.mge_defs b
  cases hs : PTree.get b (Genv.globalenv p).genv_defs with
  | none =>
      cases ht : PTree.get b (Genv.globalenv tp).genv_defs with
      | none => simp [hs, ht]
      | some tg => rw [hs, ht] at hrel; cases hrel
  | some sg =>
      cases ht : PTree.get b (Genv.globalenv tp).genv_defs with
      | none => rw [hs, ht] at hrel; cases hrel
      | some tg =>
          rw [hs, ht] at hrel
          cases hrel with
          | some _ _ hgd =>
              cases hgd with
              | match_globdef_fun _ _ _ _ _ => simp [hs, ht]
              | match_globdef_var _ _ hgv =>
                  cases hgv
                  simp [hs, ht]

private theorem deadcode_add_globals_public {F V : Type}
    (ge : Genv.t F V) (gl : List (ident × globdef F V)) :
    (Genv.add_globals ge gl).genv_public = ge.genv_public := by
  induction gl generalizing ge with
  | nil => rfl
  | cons x xs ih =>
      simp only [Genv.add_globals, List.foldl]
      exact ih (Genv.add_global ge x)

theorem senv_preserved : ∀ cfg, senv_preservedStatement cfg := by
  intro cfg prog tprog hm
  letI : Linker fundef := Linker_fundef function
  letI : Linker Unit := Linker_unit
  letI : Linker program := Linker_prog fundef Unit
  unfold match_prog CompCert4Lean.Common.Linking.match_program
    CompCert4Lean.Common.Linking.match_program_gen at hm
  have hge := deadcode_globalenv_match
    (fun (cu : program) f tf =>
      CompCert4Lean.Backend.Deadcode.transf_fundef
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg (prog_defmap cu) (romem_for cfg cu) f = .OK tf)
    (fun x y : Unit => x = y) prog prog tprog hm
  unfold Senv.equiv
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
        rw [deadcode_add_globals_public, deadcode_add_globals_public]
        exact hm.2.2
      unfold Genv.public_symbol
      rw [hs, hp]
    · intro b
      exact deadcode_volatile_match _ _ _ prog tprog hge b

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Backend.Deadcode
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.ValueAnalysis
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

theorem functions_translated
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    ∀ cfg, functions_translatedStatement cfg := by
  intro cfg prog tprog hm v f hfind
  letI : Linker fundef := Linker_fundef function
  letI : Linker Unit := Linker_unit
  letI : Linker program := Linker_prog fundef Unit
  unfold match_prog CompCert4Lean.Common.Linking.match_program
    CompCert4Lean.Common.Linking.match_program_gen at hm
  have hge := deadcode_globalenv_match
    (fun (cu : program) f tf =>
      CompCert4Lean.Backend.Deadcode.transf_fundef
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg (prog_defmap cu) (romem_for cfg cu) f = .OK tf)
    (fun x y : Unit => x = y) prog prog tprog hm
  unfold Genv.find_funct at hfind ⊢
  cases v with
  | Vundef => simp at hfind
  | Vint n => simp at hfind
  | Vlong n => simp at hfind
  | Vfloat n => simp at hfind
  | Vsingle n => simp at hfind
  | Vptr b ofs =>
      by_cases hz : Ptrofs.eq ofs Ptrofs.zero
      · simp [hz] at hfind ⊢
        unfold Genv.find_funct_ptr Genv.find_def at hfind ⊢
        have hd := hge.mge_defs b
        generalize hs : PTree.get b (Genv.globalenv prog).genv_defs = src at hfind hd
        generalize ht : PTree.get b (Genv.globalenv tprog).genv_defs = tgt at hd ⊢
        cases src with
        | none => simp at hfind
        | some gd =>
            cases gd with
            | Gfun sf =>
                simp at hfind
                cases hfind
                cases hd with
                | some gd tg hrel =>
                    cases hrel with
                    | match_globdef_fun ctx' f1 f2 horder htrans =>
                        refine ⟨ctx', f2, ?_, htrans, horder⟩
                        simp [Genv.find_funct_ptr, Genv.find_def]
            | Gvar gv => simp at hfind
      · simp [hz] at hfind

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Backend.Deadcode
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.ValueAnalysis
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

theorem function_ptr_translated
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    ∀ cfg, function_ptr_translatedStatement cfg := by
  intro cfg prog tprog hm b f hfind
  letI : Linker fundef := Linker_fundef function
  letI : Linker Unit := Linker_unit
  letI : Linker program := Linker_prog fundef Unit
  unfold match_prog CompCert4Lean.Common.Linking.match_program
    CompCert4Lean.Common.Linking.match_program_gen at hm
  have hge := deadcode_globalenv_match
    (fun (cu : program) f tf =>
      CompCert4Lean.Backend.Deadcode.transf_fundef
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg (prog_defmap cu) (romem_for cfg cu) f = .OK tf)
    (fun x y : Unit => x = y) prog prog tprog hm
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
              have hd := hge.mge_defs b
              simp [h1, h2] at hd
              cases hd
          | some gd2 =>
              cases gd2 with
              | Gfun f2 =>
                  have hd := hge.mge_defs b
                  simp [h1, h2] at hd
                  cases hd with
                  | some x y hrel =>
                      cases hrel with
                      | match_globdef_fun ctx' f1 f2 horder htrans =>
                          refine ⟨ctx', f2, ?_, htrans, horder⟩
                          simp [h2]
              | Gvar v2 =>
                  have hd := hge.mge_defs b
                  simp [h1, h2] at hd
                  cases hd with
                  | some x y hrel => cases hrel
      | Gvar v1 => simp [h1] at hfind

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

theorem sig_function_translated : ∀ cfg, sig_function_translatedStatement cfg := by
  intro cfg dm rm f tf h
  cases f with
  | Internal fn =>
      let approx := CompCert4Lean.Backend.ValueAnalysis.analyze cfg rm fn
      cases ha : CompCert4Lean.Backend.Deadcode.analyze cfg fn dm approx with
      | none =>
          simp [CompCert4Lean.Backend.Deadcode.transf_fundef,
            CompCert4Lean.Common.AST.transf_partial_fundef,
            CompCert4Lean.Backend.Deadcode.transf_function, approx, ha] at h
      | some an =>
          simp [CompCert4Lean.Backend.Deadcode.transf_fundef,
            CompCert4Lean.Common.AST.transf_partial_fundef,
            CompCert4Lean.Backend.Deadcode.transf_function, approx, ha] at h
          injection h with htf
          rw [← htf]
          rfl
  | External ef =>
      simp [CompCert4Lean.Backend.Deadcode.transf_fundef,
        CompCert4Lean.Common.AST.transf_partial_fundef] at h
      injection h with htf
      rw [← htf]

end CompCert4Lean.Backend.Deadcodeproof
