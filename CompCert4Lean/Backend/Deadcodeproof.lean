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
