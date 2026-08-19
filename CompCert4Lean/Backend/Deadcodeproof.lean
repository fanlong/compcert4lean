import CompCert4Lean.Foundation.RocqStdlib
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
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

/-! ## Program matching and memory agreement -/

def match_prog (prog tprog : program) : Prop :=
  @match_program fundef Unit fundef Unit
    (Linker_fundef function) Linker_unit
    (fun cu f tf =>
      CompCert4Lean.Backend.Deadcode.transf_fundef
        (prog_defmap cu) (romem_for cu) f = .OK tf)
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

def vanalyze (cu : program) (f : function) : PMap.t VA.t :=
  ValueAnalysis.analyze (romem_for cu) f

inductive match_stackframes (prog : program) : stackframe → stackframe → Prop where
  | match_stackframes_intro
      (res : reg) (f : function) (sp : block) (pc : node)
      (e : regset) (tf : function) (te : regset) (cu : program)
      (an : PMap.t NA.t)
      (hlink : linkorder cu prog)
      (hfun : CompCert4Lean.Backend.Deadcode.transf_function
        (prog_defmap cu) (romem_for cu) f = .OK tf)
      (han : CompCert4Lean.Backend.Deadcode.analyze
        f (prog_defmap cu) (vanalyze cu f) = some an)
      (hres : ∀ v tv, Val.lessdef v tv →
        eagree
          (Regmap.set res v e) (Regmap.set res tv te)
          (CompCert4Lean.Backend.Deadcode.transfer
            f (prog_defmap cu) (vanalyze cu f) pc (PMap.get pc an)).1) :
      match_stackframes prog
        (Stackframe res f (Vptr sp Ptrofs.zero) pc e)
        (Stackframe res tf (Vptr sp Ptrofs.zero) pc te)

export match_stackframes (match_stackframes_intro)

inductive match_states (prog : program) : state → state → Prop where
  | match_call_states
      (s : List stackframe) (f : fundef) (args : List val) (m : mem)
      (ts : List stackframe) (tf : fundef) (targs : List val) (tm : mem)
      (cu : program)
      (hstacks : list_forall2 (match_stackframes prog) s ts)
      (hlink : linkorder cu prog)
      (hfun : CompCert4Lean.Backend.Deadcode.transf_fundef
        (prog_defmap cu) (romem_for cu) f = .OK tf)
      (hargs : Val.lessdef_list args targs)
      (hmem : Mem.extends m tm) :
      match_states prog
        (Callstate s f args m)
        (Callstate ts tf targs tm)

export match_states (match_call_states)

/-! ## Simulation endpoint -/

def eventually (prog : program) (xi : ExternalCalls) (n : Nat)
    (s : state) (P : state → Prop) : Prop :=
  CompCert4Lean.Common.Smallstep.eventually
    (fun ge => CompCert4Lean.Backend.RTL.step xi ge)
    CompCert4Lean.Backend.RTL.final_state
    (Genv.globalenv prog) n s P

/-! ## Exact statement descriptors for later proof migration -/

def transf_program_matchStatement : Prop :=
  ∀ (p tp : program),
    CompCert4Lean.Backend.Deadcode.transf_program p = .OK tp →
      match_prog p tp

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
  ∀ (prog tprog : program), match_prog prog tprog → ∀ id,
    Genv.find_symbol (Genv.globalenv tprog) id =
      Genv.find_symbol (Genv.globalenv prog) id

def senv_preservedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    Senv.equiv (Genv.to_senv (Genv.globalenv prog))
      (Genv.to_senv (Genv.globalenv tprog))

def functions_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ (v : val) (f : fundef),
      Genv.find_funct (Genv.globalenv prog) v = some f →
      ∃ cu tf,
        Genv.find_funct (Genv.globalenv tprog) v = some tf ∧
        CompCert4Lean.Backend.Deadcode.transf_fundef
          (prog_defmap cu) (romem_for cu) f = .OK tf ∧
        linkorder cu prog

def function_ptr_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ (b : block) (f : fundef),
      Genv.find_funct_ptr (Genv.globalenv prog) b = some f →
      ∃ cu tf,
        Genv.find_funct_ptr (Genv.globalenv tprog) b = some tf ∧
        CompCert4Lean.Backend.Deadcode.transf_fundef
          (prog_defmap cu) (romem_for cu) f = .OK tf ∧
        linkorder cu prog

def sig_function_translatedStatement : Prop :=
  ∀ dm rm f tf,
    CompCert4Lean.Backend.Deadcode.transf_fundef dm rm f = .OK tf →
      RTL.funsig tf = RTL.funsig f

def stacksize_translatedStatement : Prop :=
  ∀ dm rm f tf,
    CompCert4Lean.Backend.Deadcode.transf_function dm rm f = .OK tf →
      tf.fn_stacksize = f.fn_stacksize

def transf_function_atStatement : Prop :=
  ∀ cu f tf an pc instr,
    CompCert4Lean.Backend.Deadcode.transf_function
      (prog_defmap cu) (romem_for cu) f = .OK tf →
    CompCert4Lean.Backend.Deadcode.analyze
      f (prog_defmap cu) (vanalyze cu f) = some an →
    PTree.get pc f.fn_code = some instr →
    PTree.get pc tf.fn_code = some
      (CompCert4Lean.Backend.Deadcode.transf_instr
        (prog_defmap cu) (vanalyze cu f) an pc instr)
def is_int_zero_soundStatement : Prop :=
  ∀ nv, CompCert4Lean.Backend.Deadcode.is_int_zero nv = true →
    nv = CompCert4Lean.Backend.NeedDomain.nval.I CompCert4Lean.Lib.Integers.Int.zero
def find_function_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ (ros : Sum reg ident) (rs trs : regset) (fd : fundef) ne,
      RTL.find_function (Genv.globalenv prog) ros rs = some fd →
      eagree rs trs (add_ros_need_all ros ne) →
      ∃ cu tfd,
        RTL.find_function (Genv.globalenv tprog) ros trs = some tfd ∧
        CompCert4Lean.Backend.Deadcode.transf_fundef
          (prog_defmap cu) (romem_for cu) fd = .OK tfd ∧
        linkorder cu prog
def analyze_successorsStatement : Prop :=
  ∀ cu f an pc instr pc',
    CompCert4Lean.Backend.Deadcode.analyze
      f (prog_defmap cu) (vanalyze cu f) = some an →
    PTree.get pc f.fn_code = some instr →
    pc' ∈ RTL.successors_instr instr →
    NA.ge (PMap.get pc an)
      (CompCert4Lean.Backend.Deadcode.transfer
        f (prog_defmap cu) (vanalyze cu f) pc' (PMap.get pc' an))
def match_succ_statesStatement : Prop :=
  ∀ (prog : program) s f sp pc e m ts tf te tm an pc' cu instr ne nm,
    linkorder cu prog →
    list_forall2 (match_stackframes prog) s ts →
    CompCert4Lean.Backend.Deadcode.transf_function
      (prog_defmap cu) (romem_for cu) f = .OK tf →
    CompCert4Lean.Backend.Deadcode.analyze
      f (prog_defmap cu) (vanalyze cu f) = some an →
    PTree.get pc f.fn_code = some instr →
    pc' ∈ RTL.successors_instr instr →
    PMap.get pc an = (ne, nm) →
    eagree e te ne →
    magree m tm (fun b ofs => nlive (Genv.globalenv prog) sp nm b ofs) →
    match_states prog
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
  ∀ (prog tprog : program) (sp : block) e m e' m' P,
    magree m m' P →
    ∀ a v,
      eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
        (fun r => Regmap.get r e) (Vptr sp Ptrofs.zero) m a v →
      ∃ v',
        eval_builtin_arg (Genv.to_senv (Genv.globalenv tprog))
          (fun r => Regmap.get r e') (Vptr sp Ptrofs.zero) m' a v'

def can_eval_builtin_argsStatement : Prop :=
  ∀ (prog tprog : program) (sp : block) e m e' m' P,
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
  ∀ (prog tprog : program) xi e sp m args vargs ef t vres m' res
      ne2 nm2 ne1 nm1 bc te tm,
    eval_builtin_args (Genv.to_senv (Genv.globalenv prog))
      (fun r => Regmap.get r e) (Vptr sp Ptrofs.zero) m args vargs →
    external_call xi ef (Genv.to_senv (Genv.globalenv prog)) vargs m t vres m' →
    transfer_builtin_args (kill_builtin_res res ne2, nmem_all) args =
      (ne1, nm1) →
    eagree e te ne1 →
    magree m tm (fun b ofs => nlive (Genv.globalenv prog) sp nm1 b ofs) →
    genv_match bc (Genv.globalenv prog) →
    bc sp = BCstack →
    ∃ tvargs tvres tm',
      eval_builtin_args (Genv.to_senv (Genv.globalenv tprog))
        (fun r => Regmap.get r te) (Vptr sp Ptrofs.zero) tm args tvargs ∧
      external_call xi ef (Genv.to_senv (Genv.globalenv tprog))
        tvargs tm t tvres tm' ∧
      eagree (regmap_setres res vres e) (regmap_setres res tvres te) ne2 ∧
      magree m' tm' (fun b ofs => nlive (Genv.globalenv prog) sp nm2 b ofs)
def step_simulationStatement : Prop :=
  ∀ (prog tprog : program) (xi : ExternalCalls) S1 t S2,
    RTL.step xi (Genv.globalenv prog) S1 t S2 →
    ∀ S1', match_states prog S1 S1' →
      sound_state prog S1 →
      (∃ S2',
        RTL.step xi (Genv.globalenv tprog) S1' t S2' ∧
          match_states prog S2 S2') ∨
      (∃ S2' n,
        plus (RTL.step xi) (Genv.globalenv tprog) S1' t S2' ∧
          eventually prog xi n S2 (fun S3 => match_states prog S3 S2'))

def transf_initial_statesStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ st1, RTL.initial_state prog st1 →
      ∃ st2, RTL.initial_state tprog st2 ∧ match_states prog st1 st2

def transf_final_statesStatement : Prop :=
  ∀ (prog : program) st1 st2 r,
    match_states prog st1 st2 →
    RTL.final_state st1 r → RTL.final_state st2 r

def transf_program_correctStatement : Prop :=
  ∀ (prog tprog : program) (xi : ExternalCalls),
    match_prog prog tprog →
    forward_simulation (RTL.semantics xi prog) (RTL.semantics xi tprog)

end CompCert4Lean.Backend.Deadcodeproof
