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

namespace CompCert4Lean.Backend.Deadcodeproof

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

theorem stacksize_translated : ∀ cfg, stacksize_translatedStatement cfg := by
  intro cfg dm rm f tf h
  unfold CompCert4Lean.Backend.Deadcode.transf_function at h
  cases ha : CompCert4Lean.Backend.Deadcode.analyze cfg f dm
      (CompCert4Lean.Backend.ValueAnalysis.analyze cfg rm f) with
  | none => simp [ha] at h
  | some an =>
      simp only [ha] at h
      injection h with htf
      rw [← htf]

omit binary64_certificate binary32_certificate in
theorem is_int_zero_sound : is_int_zero_soundStatement := by
  intro nv h
  cases nv with
  | Nothing => simp [CompCert4Lean.Backend.Deadcode.is_int_zero] at h
  | I n =>
      apply congrArg CompCert4Lean.Backend.NeedDomain.nval.I
      apply CompCert4Lean.Lib.Integers.WordCore.ext
      simpa [CompCert4Lean.Backend.Deadcode.is_int_zero,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq] using h
  | L n => simp [CompCert4Lean.Backend.Deadcode.is_int_zero] at h
  | All => simp [CompCert4Lean.Backend.Deadcode.is_int_zero] at h

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

theorem transf_function_at : ∀ cfg, transf_function_atStatement cfg := by
  intro cfg cu f tf an pc instr htf han hcode
  unfold CompCert4Lean.Backend.Deadcode.transf_function at htf
  dsimp only at htf
  unfold vanalyze at han
  rw [han] at htf
  injection htf with htf
  rw [← htf]
  simp only
  let tr : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive →
      CompCert4Lean.Backend.RTL.instruction →
      CompCert4Lean.Backend.RTL.instruction :=
    fun p i => CompCert4Lean.Backend.Deadcode.transf_instr cfg
      (CompCert4Lean.Common.AST.prog_defmap cu)
      (CompCert4Lean.Backend.ValueAnalysis.analyze cfg
        (CompCert4Lean.Backend.ValueAnalysis.romem_for cfg cu) f) an p i
  let code : CompCert4Lean.Lib.Maps.PTree.t
      CompCert4Lean.Backend.RTL.instruction := f.fn_code
  have hcode' : CompCert4Lean.Lib.Maps.PTree.get pc code = some instr := hcode
  change CompCert4Lean.Lib.Maps.PTree.get pc
      (CompCert4Lean.Lib.Maps.PTree.map tr code) = some (tr pc instr)
  rw [CompCert4Lean.Lib.Maps.PTree.gmap
    (A := CompCert4Lean.Backend.RTL.instruction)
    (B := CompCert4Lean.Backend.RTL.instruction), hcode']
  rfl

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Backend.Deadcode
open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

theorem find_function_translated : ∀ cfg, find_function_translatedStatement cfg := by
  intro cfg prog tprog hm ros rs fd trs ne hfind hagree
  cases ros with
  | inl r =>
      change Genv.find_funct (Genv.globalenv prog) (Regmap.get r rs) = some fd at hfind
      change eagree rs trs (add_need_all r ne) at hagree
      have hld := add_need_all_lessdef rs trs r ne hagree
      simp only [CompCert4Lean.Backend.RTL.find_function] at hfind ⊢
      generalize hsrc : Regmap.get r rs = sv at hfind hld
      generalize htgt : Regmap.get r trs = tv at hld ⊢
      cases hld with
      | lessdef_refl v =>
          exact functions_translated cfg prog tprog hm sv fd hfind
      | lessdef_undef v =>
          simp [Genv.find_funct] at hfind
  | inr id =>
      have hsym : Genv.find_symbol (Genv.globalenv tprog) id =
          Genv.find_symbol (Genv.globalenv prog) id :=
        (senv_preserved cfg prog tprog hm).1 id
      simp only [CompCert4Lean.Backend.RTL.find_function] at hfind ⊢
      rw [hsym]
      cases hs : Genv.find_symbol (Genv.globalenv prog) id with
      | none => simp [hs] at hfind
      | some b =>
          simp only [hs] at hfind ⊢
          exact function_ptr_translated cfg prog tprog hm b fd hfind

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Backend.Deadcode
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

theorem can_eval_builtin_arg : ∀ cfg, can_eval_builtin_argStatement cfg := by
  intro cfg prog tprog hm sp e m e' m' P hma
  have hload : ∀ (chunk : memory_chunk) (addr : val) v,
      Mem.loadv chunk m addr = some v →
        ∃ v', Mem.loadv chunk m' addr = some v' := by
    intro chunk addr v hv
    cases addr with
    | Vundef => simp [Mem.loadv] at hv
    | Vint n => simp [Mem.loadv] at hv
    | Vlong n => simp [Mem.loadv] at hv
    | Vfloat n => simp [Mem.loadv] at hv
    | Vsingle n => simp [Mem.loadv] at hv
    | Vptr b ofs =>
        have hvalid := Mem.load_valid_access m chunk b (Ptrofs.unsigned ofs) v hv
        have hvalid' := magree_valid_access m m' P chunk b
          (Ptrofs.unsigned ofs) CompCert4Lean.Common.Memtype.Readable hma hvalid
        rcases Mem.valid_access_load m' chunk b (Ptrofs.unsigned ofs) hvalid' with
          ⟨v', hv'⟩
        exact ⟨v', hv'⟩
  have hsenv := senv_preserved cfg prog tprog hm
  have hsym : ∀ id ofs,
      Senv.symbol_address (Genv.to_senv (Genv.globalenv prog)) id ofs =
        Senv.symbol_address (Genv.to_senv (Genv.globalenv tprog)) id ofs := by
    intro id ofs
    unfold Senv.symbol_address
    rw [hsenv.1 id]
  intro a v hev
  induction hev with
  | eval_BA x =>
      exact ⟨CompCert4Lean.Backend.Registers.Regmap.get x e', eval_BA x⟩
  | eval_BA_int n => exact ⟨Vint n, eval_BA_int n⟩
  | eval_BA_long n => exact ⟨Vlong n, eval_BA_long n⟩
  | eval_BA_float n => exact ⟨Vfloat n, eval_BA_float n⟩
  | eval_BA_single n => exact ⟨Vsingle n, eval_BA_single n⟩
  | eval_BA_loadstack chunk ofs v hv =>
      rcases hload chunk (Val.offset_ptr (Vptr sp Ptrofs.zero) ofs) v hv with
        ⟨v', hv'⟩
      exact ⟨v', eval_BA_loadstack chunk ofs v' hv'⟩
  | eval_BA_addrstack ofs =>
      exact ⟨Val.offset_ptr (Vptr sp Ptrofs.zero) ofs,
        eval_BA_addrstack ofs⟩
  | eval_BA_loadglobal chunk id ofs v hv =>
      rw [hsym id ofs] at hv
      rcases hload chunk (Senv.symbol_address
        (Genv.to_senv (Genv.globalenv tprog)) id ofs) v hv with ⟨v', hv'⟩
      exact ⟨v', eval_BA_loadglobal chunk id ofs v' hv'⟩
  | eval_BA_addrglobal id ofs =>
      exact ⟨Senv.symbol_address
        (Genv.to_senv (Genv.globalenv tprog)) id ofs,
        eval_BA_addrglobal id ofs⟩
  | eval_BA_splitlong hi lo vhi vlo hhi hlo ihhi ihlo =>
      rcases ihhi with ⟨vhi', hhi'⟩
      rcases ihlo with ⟨vlo', hlo'⟩
      exact ⟨Val.longofwords vhi' vlo', eval_BA_splitlong _ _ _ _ hhi' hlo'⟩
  | eval_BA_addptr a1 a2 v1 v2 h1 h2 ih1 ih2 =>
      rcases ih1 with ⟨v1', h1'⟩
      rcases ih2 with ⟨v2', h2'⟩
      exact ⟨_, eval_BA_addptr _ _ _ _ h1' h2'⟩

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Backend.Deadcode
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

theorem can_eval_builtin_args : ∀ cfg, can_eval_builtin_argsStatement cfg := by
  intro cfg prog tprog hm sp e m e' m' P hma al vl hev
  unfold eval_builtin_args at hev ⊢
  induction hev with
  | nil => exact ⟨[], list_forall2.nil _⟩
  | @cons a1 al v1 vl h1 htail ih =>
      rcases can_eval_builtin_arg cfg prog tprog hm sp e m e' m' P hma
        a1 v1 h1 with ⟨v1', hv1'⟩
      rcases ih with ⟨vl', htail'⟩
      exact ⟨v1' :: vl', list_forall2.cons _ _ hv1' htail'⟩

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

theorem eagree_set_undef : eagree_set_undefStatement := by
  intro e1 e2 ne r h r'
  unfold NeedDomain.eagree at h
  by_cases hr : r' = r
  · subst r'
    change NeedDomain.vagree
      (CompCert4Lean.Lib.Maps.PMap.get r
        (CompCert4Lean.Lib.Maps.PMap.set r Common.Values.Vundef e1))
      (CompCert4Lean.Lib.Maps.PMap.get r e2) (NeedDomain.NE.get r ne)
    have hset : CompCert4Lean.Lib.Maps.PMap.get r
        (CompCert4Lean.Lib.Maps.PMap.set r Common.Values.Vundef e1) = Common.Values.Vundef := by
      exact CompCert4Lean.Lib.Maps.PMap.gss (A := Common.Values.val) r
        Common.Values.Vundef e1
    rw [hset]
    cases hn : NeedDomain.NE.get r ne with
    | Nothing => trivial
    | I m => change True; trivial
    | L m => change True; trivial
    | All => exact Common.Values.Val.lessdef_undef _
  · change NeedDomain.vagree
      (CompCert4Lean.Lib.Maps.PMap.get r'
        (CompCert4Lean.Lib.Maps.PMap.set r Common.Values.Vundef e1))
      (CompCert4Lean.Lib.Maps.PMap.get r' e2) (NeedDomain.NE.get r' ne)
    rw [CompCert4Lean.Lib.Maps.PMap.gso (A := Common.Values.val)
      (i := r') (j := r) (x := Common.Values.Vundef) (m := e1) hr]
    exact h r'

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Deadcode
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.ValueAnalysis
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open Lean Elab Tactic Meta

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

private theorem deadcode_ptrofs_add_zero_l (x : Ptrofs.int) :
    Ptrofs.add Ptrofs.zero x = x := by
  change WordCore.add (WordCore.zero Ptrofs.wordsize) x = x
  apply WordCore.ext_of_val_eq
  have hadd : (WordCore.add (WordCore.zero Ptrofs.wordsize) x).val =
      ((WordCore.zero Ptrofs.wordsize).val + x.val) % (2 ^ Ptrofs.wordsize) := by
    run_tac
      let lctx ← getLCtx
      let xF := (lctx.findFromUserName? `x).get!
      let zeroE ← mkAppM ``CompCert4Lean.Lib.Integers.WordCore.zero
        #[mkConst ``CompCert4Lean.Lib.Integers.Ptrofs.wordsize]
      let e ← mkAppM (privateName "CompCert4Lean.Lib.Integers.WordCore.add_val")
        #[zeroE, mkFVar xF.fvarId]
      closeMainGoal Name.anonymous e
  rw [hadd]
  have hz : (WordCore.zero Ptrofs.wordsize).val = 0 := by
    change (WordCore.repr Ptrofs.wordsize (zOfNat 0)).val = 0
    simpa using (residue_zOfNat_local Ptrofs.wordsize 0)
  rw [hz, Nat.zero_add]
  exact Nat.mod_eq_of_lt (word64_val_lt_local x)

private theorem deadcode_val_inject_refl (v : val) :
    Val.inject inject_id v v := by
  cases v with
  | Vint i => exact Val.inject.inject_int _
  | Vlong i => exact Val.inject.inject_long _
  | Vfloat f => exact Val.inject.inject_float _
  | Vsingle f => exact Val.inject.inject_single _
  | Vptr b ofs =>
      apply Val.inject.inject_ptr
      · rfl
      · exact ((Ptrofs.add_commut_proof_api ofs Ptrofs.zero).trans
          (deadcode_ptrofs_add_zero_l ofs)).symm
  | Vundef => exact Val.inject.val_inject_undef _

private theorem deadcode_initial_store_init_data
    {prog tprog : program}
    (hsymb : ∀ id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id)
    (m : mem) (b : block) (p : Z) (i : init_data) :
    Genv.store_init_data (Genv.globalenv prog) m b p i =
      Genv.store_init_data (Genv.globalenv tprog) m b p i := by
  cases i with
  | Init_addrof symb ofs => simp [Genv.store_init_data, hsymb symb]
  | _ => rfl

private theorem deadcode_initial_store_init_data_list
    {prog tprog : program}
    (hsymb : ∀ id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id) :
    ∀ (m : mem) (b : block) (p : Z) (il : List init_data),
      Genv.store_init_data_list (Genv.globalenv prog) m b p il =
        Genv.store_init_data_list (Genv.globalenv tprog) m b p il := by
  intro m b p il
  induction il generalizing m b p with
  | nil => rfl
  | cons i rest ih =>
      simp only [Genv.store_init_data_list]
      rw [deadcode_initial_store_init_data hsymb]
      cases h : Genv.store_init_data (Genv.globalenv tprog) m b p i with
      | none => simp [h]
      | some m' => simp only [h]; exact ih m' b (zAdd p (init_data_size i))

private theorem deadcode_initial_alloc_global
    (cfg : CompilerConfig) [Linker program]
    {prog tprog : program}
    (hsymb : ∀ id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id)
    {id : ident} {gd tg : globdef fundef Unit}
    (hgd : match_globdef
      (fun (cu : program) f tf =>
        CompCert4Lean.Backend.Deadcode.transf_fundef
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          cfg (prog_defmap cu) (romem_for cfg cu) f = .OK tf)
      (fun x y : Unit => x = y) prog gd tg)
    (m : mem) :
    Genv.alloc_global (Genv.globalenv prog) m (id, gd) =
      Genv.alloc_global (Genv.globalenv tprog) m (id, tg) := by
  cases hgd with
  | match_globdef_fun ctx' f1 f2 horder htrans => rfl
  | match_globdef_var v1 v2 hvar =>
      cases hvar with
      | match_globvar_intro info1 info2 init ro vol hinfo =>
          cases hinfo
          simp only [Genv.alloc_global, CompCert4Lean.Common.Values.block]
          congr 1
          funext m2
          congr 1
          exact deadcode_initial_store_init_data_list hsymb _ _ _ _

private theorem deadcode_initial_alloc_globals
    (cfg : CompilerConfig) [Linker program]
    {prog tprog : program}
    (hsymb : ∀ id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id)
    (gl tgl : List (ident × globdef fundef Unit))
    (hlist : list_forall2
      (match_ident_globdef
        (fun (cu : program) f tf =>
          CompCert4Lean.Backend.Deadcode.transf_fundef
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            cfg (prog_defmap cu) (romem_for cfg cu) f = .OK tf)
        (fun x y : Unit => x = y) prog) gl tgl) :
    ∀ (m m' : mem),
      Genv.alloc_globals (Genv.globalenv prog) m gl = some m' →
        Genv.alloc_globals (Genv.globalenv tprog) m tgl = some m' := by
  induction hlist with
  | nil => intro m m' h; simpa [Genv.alloc_globals] using h
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
        exact deadcode_initial_alloc_global cfg hsymb hgd m
      simp only [Genv.alloc_globals] at h ⊢
      rw [halloc] at h
      cases ha : Genv.alloc_global (Genv.globalenv tprog) m (tid, tgd) with
      | none => simp [ha] at h
      | some m1 => simp only [ha] at h ⊢; exact ih m1 m' h

private theorem deadcode_mem_extends_refl (m : mem) : Mem.extends m m := by
  refine ⟨rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro b1 b2 delta ofs k p hmap hp
      have hpair : (b1, (.Z0 : Z)) = (b2, delta) := by
        simpa [CompCert4Lean.Common.Values.inject_id] using Option.some.inj hmap
      cases hpair
      change Mem.perm m b1 (zAdd ofs (.Z0 : Z)) k p
      have hz : zAdd ofs (.Z0 : Z) = ofs := by
        apply intOfZ_injective
        change intOfZ (zOfInt (intOfZ ofs + 0)) = intOfZ ofs
        rw [intOfZ_zOfInt]
        simp
      rw [hz]
      exact hp
    · intro b1 b2 delta chunk ofs p hmap hp
      have hpair : (b1, (.Z0 : Z)) = (b2, delta) := by
        simpa [CompCert4Lean.Common.Values.inject_id] using Option.some.inj hmap
      cases hpair
      refine ⟨.Z0, ?_⟩
      apply intOfZ_injective
      change 0 = intOfZ (ZArith.BinInt.Z.mul (align_chunk chunk) (.Z0 : Z))
      change 0 = intOfZ (zOfInt (intOfZ (align_chunk chunk) * 0))
      rw [intOfZ_zOfInt]
      simp
    · intro b1 ofs b2 delta hmap hp
      have hpair : (b1, (.Z0 : Z)) = (b2, delta) := by
        simpa [CompCert4Lean.Common.Values.inject_id] using Option.some.inj hmap
      cases hpair
      change memval_inject inject_id
        (ZMap.get ofs (PMap.get b1 m.mem_contents))
        (ZMap.get (zAdd ofs (.Z0 : Z)) (PMap.get b1 m.mem_contents))
      have hz : zAdd ofs (.Z0 : Z) = ofs := by
        apply intOfZ_injective
        change intOfZ (zOfInt (intOfZ ofs + 0)) = intOfZ ofs
        rw [intOfZ_zOfInt]
        simp
      rw [hz]
      cases hmv : ZMap.get ofs (PMap.get b1 m.mem_contents) with
      | Byte n => exact memval_inject.byte _ _
      | Fragment v q n =>
          exact memval_inject.fragment _ _ _ _ _ (deadcode_val_inject_refl v)
      | Undef => exact memval_inject.undef _ _
  · intro b ofs k p hp
    exact Or.inl hp

theorem transf_initial_states : ∀ cfg, transf_initial_statesStatement cfg := by
  letI : Linker fundef := Linker_fundef function
  letI : Linker Unit := Linker_unit
  letI : Linker program := Linker_prog fundef Unit
  intro cfg prog tprog hmatch st1 hinit
  have hge := deadcode_globalenv_match
    (fun (cu : program) f tf =>
      CompCert4Lean.Backend.Deadcode.transf_fundef
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg (prog_defmap cu) (romem_for cfg cu) f = .OK tf)
    (fun x y : Unit => x = y) prog prog tprog hmatch
  cases hinit with
  | intro b f m0 hmem hsymb hfun hsig =>
      rcases function_ptr_translated cfg prog tprog hmatch b f hfun with
        ⟨cu, tf, hfind, htrans, hlink⟩
      refine ⟨Callstate [] tf [] m0, ?_, ?_⟩
      · apply initial_state.intro b tf m0
        · unfold Genv.init_mem at hmem ⊢
          apply deadcode_initial_alloc_globals cfg
            (fun id => hge.mge_symb id)
            prog.prog_defs tprog.prog_defs hmatch.1
          exact hmem
        · change Genv.find_symbol (Genv.globalenv tprog) tprog.prog_main = some b
          calc
            Genv.find_symbol (Genv.globalenv tprog) tprog.prog_main =
                Genv.find_symbol (Genv.globalenv tprog) prog.prog_main := by
                  rw [hmatch.2.1]
            _ = Genv.find_symbol (Genv.globalenv prog) prog.prog_main :=
              hge.mge_symb prog.prog_main
            _ = some b := hsymb
        · exact hfind
        · rw [sig_function_translated cfg (prog_defmap cu) (romem_for cfg cu) f tf htrans]
          exact hsig
      · exact match_call_states [] f [] m0 [] tf [] m0 cu
          (list_forall2.nil _) hlink htrans
          Val.lessdef_list.lessdef_list_nil (deadcode_mem_extends_refl m0)

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

theorem transf_final_states : ∀ cfg, transf_final_statesStatement cfg := by
  intro cfg prog st1 st2 r hmatch hfinal
  cases hfinal with
  | intro r m =>
      cases hmatch with
      | match_return_states s v m s' v' m' hstacks hres hmem =>
          cases hstacks
          cases hres
          exact CompCert4Lean.Backend.RTL.final_state.intro r m'

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

 theorem magree_load : magree_loadStatement := by
  intro m1 m2 P chunk b ofs v h hload hP
  have hvalid := Mem.load_valid_access m1 chunk b ofs v hload
  rcases Mem.load_loadbytes chunk m1 b ofs v hload with
    ⟨bytes, hbytes, hv⟩
  rcases magree_loadbytes m1 m2 P b ofs (size_chunk chunk) bytes h hbytes hP with
    ⟨bytes', hbytes', hrel⟩
  refine ⟨decode_val chunk bytes', ?_, ?_⟩
  · exact Mem.loadbytes_load chunk m2 b ofs bytes' hbytes' hvalid.2
  · rw [hv]
    apply (val_inject_id _ _).mp
    exact decode_val_inject inject_id bytes bytes' chunk hrel

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem magree_parallel_setN_aux (access : Z → Prop)
    (bytes1 bytes2 : List memval) (hbytes : list_forall2 memval_lessdef bytes1 bytes2) :
    ∀ (p : Z) (c1 c2 : ZMap.t memval),
      (∀ i, access i →
        zLt i p ∨ zLe (zAdd p (zOfNat bytes1.length)) i →
        memval_lessdef (ZMap.get i c1) (ZMap.get i c2)) →
      ∀ q, access q →
        memval_lessdef (ZMap.get q (Mem.setN bytes1 p c1))
          (ZMap.get q (Mem.setN bytes2 p c2)) := by
  induction hbytes with
  | nil =>
      intro p c1 c2 h q hq
      apply h q hq
      change intOfZ q < intOfZ p ∨
        intOfZ (zAdd p (zOfNat 0)) ≤ intOfZ q
      simp [zAdd, zOfNat, ZArith.BinInt.Z.add, ZArith.BinInt.Z.of_nat,
        intOfZ_zOfInt]
      omega
  | @cons v1 tail1 v2 tail2 hv htail ih =>
      intro p c1 c2 h q hq
      change memval_lessdef
        (ZMap.get q (Mem.setN tail1 (zAdd p (.Zpos .xH)) (ZMap.set p v1 c1)))
        (ZMap.get q (Mem.setN tail2 (zAdd p (.Zpos .xH)) (ZMap.set p v2 c2)))
      apply ih (zAdd p (.Zpos .xH)) (ZMap.set p v1 c1) (ZMap.set p v2 c2) _ q hq
      intro i hi hout
      by_cases heq : i = p
      · subst i
        rw [zmap_get_set_same_local, zmap_get_set_same_local]
        exact hv
      · rw [zmap_get_set_other_local _ _ _ _ heq,
          zmap_get_set_other_local _ _ _ _ heq]
        apply h i hi
        have hne : intOfZ i ≠ intOfZ p := fun e => heq (intOfZ_injective e)
        change intOfZ i < intOfZ (zAdd p (.Zpos .xH)) ∨
          intOfZ (zAdd (zAdd p (.Zpos .xH)) (zOfNat tail1.length)) ≤ intOfZ i at hout
        change intOfZ i < intOfZ p ∨
          intOfZ (zAdd p (zOfNat (v1 :: tail1).length)) ≤ intOfZ i
        simp [zAdd, zOfNat, ZArith.BinInt.Z.add, ZArith.BinInt.Z.of_nat,
          intOfZ_zOfInt] at hout ⊢
        have hone : intOfZ (.Zpos .xH) = 1 := rfl
        rw [hone] at hout
        omega

theorem magree_storebytes_parallel : magree_storebytes_parallelStatement := by
  intro m1 m2 P Q b ofs bytes1 m1' bytes2 hma hstore hPQ hbytes
  have hlen : bytes1.length = bytes2.length :=
    list_forall2_length _ _ _ _ _ hbytes
  have hrange : Mem.range_perm m2 b ofs (zAdd ofs (zOfNat bytes2.length)) Cur Writable := by
    rw [← hlen]
    intro i hi
    exact hma.ma_perm b i Cur Writable
      (Mem.storebytes_range_perm m1 b ofs bytes1 m1' hstore i hi)
  obtain ⟨m2', hstore2⟩ := Mem.range_perm_storebytes m2 b ofs bytes2 hrange
  refine ⟨m2', hstore2, ?_⟩
  constructor
  · intro b' i k p hp
    apply Mem.perm_storebytes_1 m2 b ofs bytes2 m2' hstore2 b' i k p
    apply hma.ma_perm b' i k p
    exact Mem.perm_storebytes_2 m1 b ofs bytes1 m1' hstore b' i k p hp
  · intro b' i k p hp
    have hp2 := Mem.perm_storebytes_2 m2 b ofs bytes2 m2' hstore2 b' i k p hp
    rcases hma.ma_perm_inv b' i k p hp2 with hp1 | hn
    · exact Or.inl (Mem.perm_storebytes_1 m1 b ofs bytes1 m1' hstore b' i k p hp1)
    · right
      intro hp1
      exact hn (Mem.perm_storebytes_2 m1 b ofs bytes1 m1' hstore b' i Max Nonempty hp1)
  · intro b' i hp hQ
    rw [Mem.storebytes_mem_contents m1 b ofs bytes1 m1' hstore,
      Mem.storebytes_mem_contents m2 b ofs bytes2 m2' hstore2]
    by_cases hbb : b' = b
    · subst b'
      rw [pmap_get_set_same_local, pmap_get_set_same_local]
      apply magree_parallel_setN_aux
        (fun j => Mem.perm m1' b j Cur Readable ∧ Q b j) bytes1 bytes2 hbytes
        ofs (PMap.get b m1.mem_contents) (PMap.get b m2.mem_contents) _ i ⟨hp, hQ⟩
      intro j hj hout
      apply hma.ma_memval b j
      · exact Mem.perm_storebytes_2 m1 b ofs bytes1 m1' hstore b j Cur Readable hj.1
      · exact hPQ b j hj.2 (Or.inr hout)
    · rw [pmap_get_set_other_local _ _ _ _ hbb,
        pmap_get_set_other_local _ _ _ _ hbb]
      apply hma.ma_memval b' i
      · exact Mem.perm_storebytes_2 m1 b ofs bytes1 m1' hstore b' i Cur Readable hp
      · exact hPQ b' i hQ (Or.inl hbb)
  · rw [Mem.nextblock_storebytes m1 b ofs bytes1 m1' hstore,
      Mem.nextblock_storebytes m2 b ofs bytes2 m2' hstore2]
    exact hma.ma_nextblock

end CompCert4Lean.Backend.Deadcodeproof
namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers

private theorem magree_store_encode_aux (chunk : memory_chunk) (v w : val)
    (h : vagree v w (store_argument chunk)) :
    list_forall2 memval_lessdef (encode_val chunk v) (encode_val chunk w) := by
  have hmask8 : complete_mask (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 255)) =
      CompCert4Lean.Lib.Integers.Int.repr (zOfNat 255) := by
    decide
  have hsize8 : CompCert4Lean.Lib.Integers.Int.size
      (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 255)) = zOfNat 8 := by decide
  have hmask16 : complete_mask (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 65535)) =
      CompCert4Lean.Lib.Integers.Int.repr (zOfNat 65535) := by
    set_option maxRecDepth 100000 in decide
  have hsize16 : CompCert4Lean.Lib.Integers.Int.size
      (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 65535)) = zOfNat 16 := by
    set_option maxRecDepth 100000 in decide
  cases chunk with
  | Mbool | Mint8signed | Mint8unsigned =>
      cases v <;> first
        | exact repeat_Undef_inject_encode_val inject_id _ _
        | skip
      cases w <;> try (exact False.elim h)
      rename_i a b
      change iagree a b (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 255)) at h
      have hm := iagree_eqmod a b
        (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 255)) (by simpa [hmask8] using h)
      change CompCert4Lean.Lib.Zbits.eqmod (two_p (zOfNat 8)) (Int.unsigned a) (Int.unsigned b) at hm
      change list_forall2 memval_lessdef
        (inj_bytes (encode_int 1 (Int.unsigned a)))
        (inj_bytes (encode_int 1 (Int.unsigned b)))
      rw [encode_int_8_mod _ _ hm]
      exact inj_bytes_inject inject_id _
  | Mint16signed | Mint16unsigned =>
      cases v <;> first
        | exact repeat_Undef_inject_encode_val inject_id _ _
        | skip
      cases w <;> try (exact False.elim h)
      rename_i a b
      change iagree a b (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 65535)) at h
      have hm := iagree_eqmod a b
        (CompCert4Lean.Lib.Integers.Int.repr (zOfNat 65535)) (by simpa [hmask16] using h)
      change CompCert4Lean.Lib.Zbits.eqmod (two_p (zOfNat 16)) (Int.unsigned a) (Int.unsigned b) at hm
      have he : encode_int 2 (Int.unsigned a) = encode_int 2 (Int.unsigned b) := by
        unfold encode_int
        congr 1
        exact bytes_of_int_mod 2 _ _ hm
      change list_forall2 memval_lessdef
        (inj_bytes (encode_int 2 (Int.unsigned a)))
        (inj_bytes (encode_int 2 (Int.unsigned b)))
      rw [he]
      exact inj_bytes_inject inject_id _
  | Mint32 | Mint64 | Mfloat32 | Mfloat64 | Many32 | Many64 =>
      exact encode_val_inject inject_id v w _ ((val_inject_id v w).mpr h)

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers

 theorem magree_store_parallel : magree_store_parallelStatement := by
  intro m1 m2 P Q chunk b ofs v1 m1' v2 hma hstore hv hPQ
  have hvalid := Mem.store_valid_access_3 chunk m1 b ofs v1 m1' hstore
  have hbytes := Mem.store_storebytes m1 b ofs chunk v1 m1' hstore
  have hout : ∀ b' i, Q b' i →
      b' ≠ b ∨ zLt i ofs ∨ zLe (zAdd ofs (zOfNat (encode_val chunk v1).length)) i →
      P b' i := by
    intro b' i hQ hi
    have hlen : (encode_val chunk v1).length = size_chunk_nat chunk :=
      encode_val_length chunk v1
    have hz : zOfNat (encode_val chunk v1).length = size_chunk chunk := by
      rw [hlen]
      exact (size_chunk_conv chunk).symm
    rw [hz] at hi
    exact hPQ b' i hQ hi
  obtain ⟨m2', hbytes2, hagree⟩ := magree_storebytes_parallel m1 m2 P Q b ofs
    (encode_val chunk v1) m1' (encode_val chunk v2) hma hbytes hout
    (magree_store_encode_aux chunk v1 v2 hv)
  exact ⟨m2', Mem.storebytes_store m2 b ofs chunk v2 m2' hbytes2 hvalid.2, hagree⟩

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata

theorem magree_store_left : magree_store_leftStatement := by
  intro m1 m2 P chunk b ofs v1 m1' hma hstore hP
  apply magree_storebytes_left m1 m2 P b ofs (encode_val chunk v1) m1' hma
    (Mem.store_storebytes m1 b ofs chunk v1 m1' hstore)
  intro i hi
  have hsize : zOfNat (encode_val chunk v1).length = size_chunk chunk := by
    rw [encode_val_length chunk v1]
    exact (size_chunk_conv chunk).symm
  rw [hsize] at hi
  exact hP i hi

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype

theorem magree_free : magree_freeStatement := by
  intro m1 m2 P Q b lo hi m1' hma hfree hPQ
  obtain ⟨m2', hfree2⟩ := Mem.range_perm_free m2 b lo hi (by
    intro ofs hbounds
    exact hma.ma_perm b ofs Cur Freeable
      (Mem.free_range_perm m1 b lo hi m1' hfree ofs hbounds))
  refine ⟨m2', hfree2, ?_⟩
  constructor
  · intro b' ofs k p hp
    have hp2 := hma.ma_perm b' ofs k p
      (Mem.perm_free_3 m1 b lo hi m1' hfree b' ofs k p hp)
    rcases Mem.perm_free_inv m2 b lo hi m2' hfree2 b' ofs k p hp2 with
      ⟨heq, hbounds⟩ | hout
    · subst b'
      exact False.elim (Mem.perm_free_2 m1 b lo hi m1' hfree ofs k p hbounds hp)
    · exact hout
  · intro b' ofs k p hp
    rcases hma.ma_perm_inv b' ofs k p
        (Mem.perm_free_3 m2 b lo hi m2' hfree2 b' ofs k p hp) with hp1 | hn
    · rcases Mem.perm_free_inv m1 b lo hi m1' hfree b' ofs k p hp1 with
        ⟨heq, hbounds⟩ | hout
      · subst b'
        exact Or.inr (Mem.perm_free_2 m1 b lo hi m1' hfree ofs Max Nonempty hbounds)
      · exact Or.inl hout
    · exact Or.inr (fun hp1 => hn
        (Mem.perm_free_3 m1 b lo hi m1' hfree b' ofs Max Nonempty hp1))
  · intro b' ofs hp hQ
    have hP : P b' ofs := by
      apply hPQ b' ofs hQ
      by_cases heq : b' = b
      · subst b'
        exact Or.inr (fun hbounds =>
          Mem.perm_free_2 m1 b lo hi m1' hfree ofs Cur Readable hbounds hp)
      · exact Or.inl heq
    have hval := hma.ma_memval b' ofs
      (Mem.perm_free_3 m1 b lo hi m1' hfree b' ofs Cur Readable hp) hP
    rw [Mem.free_result m1 b lo hi m1' hfree,
      Mem.free_result m2 b lo hi m2' hfree2]
    exact hval
  · rw [Mem.nextblock_free m1 b lo hi m1' hfree,
      Mem.nextblock_free m2 b lo hi m2' hfree2]
    exact hma.ma_nextblock

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.Values

set_option maxHeartbeats 1000000 in
theorem eagree_init_regs : eagree_init_regsStatement := by
  intro rl
  induction rl with
  | nil =>
      intro vl1 vl2 ne hld
      change NeedDomain.NE.t at ne
      cases vl1 with
      | nil =>
          cases vl2 with
          | nil =>
              intro r
              change vagree Vundef Vundef _
              exact NeedDomain.vagree_same _ _
          | cons v2 vl2 => cases hld
      | cons v1 vl1 =>
          cases vl2 with
          | nil => cases hld
          | cons v2 vl2 =>
              intro r
              change vagree Vundef Vundef _
              exact NeedDomain.vagree_same _ _
  | cons r rl ih =>
      intro vl1 vl2 ne hld
      change NeedDomain.NE.t at ne
      cases vl1 with
      | nil =>
          cases vl2 with
          | nil =>
              intro r0
              change vagree Vundef Vundef _
              exact NeedDomain.vagree_same _ _
          | cons v2 vl2 =>
              cases hld
      | cons v1 vl1 =>
          cases vl2 with
          | nil =>
              cases hld
          | cons v2 vl2 =>
              cases hld with
              | lessdef_list_cons _ _ _ _ hv htail =>
                  intro r0
                  have hinit1 :
                      CompCert4Lean.Backend.RTL.init_regs (v1 :: vl1) (r :: rl) =
                        CompCert4Lean.Lib.Maps.PMap.set r v1
                          (CompCert4Lean.Backend.RTL.init_regs vl1 rl) := rfl
                  have hinit2 :
                      CompCert4Lean.Backend.RTL.init_regs (v2 :: vl2) (r :: rl) =
                        CompCert4Lean.Lib.Maps.PMap.set r v2
                          (CompCert4Lean.Backend.RTL.init_regs vl2 rl) := rfl
                  rw [hinit1, hinit2]
                  have hg1 := Regmap.gsspec_proof Common.Values.val r0 r v1
                    (CompCert4Lean.Backend.RTL.init_regs vl1 rl)
                  have hg2 := Regmap.gsspec_proof Common.Values.val r0 r v2
                    (CompCert4Lean.Backend.RTL.init_regs vl2 rl)
                  rw [hg1, hg2]
                  cases CompCert4Lean.Lib.Coqlib.peq r0 r with
                  | left heq =>
                      subst r0
                      exact NeedDomain.vagree_lessdef v1 v2 _ hv
                  | right hne =>
                      exact ih vl1 vl2 ne htail r0

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Backend.ValueAnalysis
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

theorem symbols_preserved : ∀ cfg, symbols_preservedStatement cfg := by
  intro cfg prog tprog hmatch id
  unfold match_prog at hmatch
  exact Genv.find_symbol_match RTL.program RTL.fundef Unit RTL.fundef Unit
    (fun q f tf => CompCert4Lean.Backend.Deadcode.transf_fundef
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      cfg (prog_defmap q) (romem_for cfg q) f = .OK tf)
    (fun x y : Unit => x = y) prog prog tprog hmatch id

end CompCert4Lean.Backend.Deadcodeproof


namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Backend.Deadcode
open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Maps

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

theorem analyze_successors : ∀ cfg, analyze_successorsStatement cfg := by
  intro cfg cu f an pc instr pc' hAnalyze hpc hs
  apply CompCert4Lean.Backend.Deadcode.DS.fixpoint_solution_proof
    CompCert4Lean.Backend.Deadcode.solver_law_obligation_proof
    (A := CompCert4Lean.Backend.RTL.instruction)
    (code := f.fn_code)
    (successors := CompCert4Lean.Backend.RTL.successors_instr)
    (transf := CompCert4Lean.Backend.Deadcode.transfer cfg f (prog_defmap cu)
      (vanalyze cfg cu f))
    (res := an) (n := pc) (instr := instr) (s := pc')
    hAnalyze hpc hs
  intro n a hnone
  unfold CompCert4Lean.Backend.Deadcode.transfer
  rw [hnone]
  change NA.eq NA.bot NA.bot
  constructor
  · intro p
    rfl
  · intro ge sp b ofs
    rfl

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Backend.Deadcode
open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Maps

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

private theorem deadcode_eagree_ge : ∀ e1 e2 ne ne',
    eagree e1 e2 ne → NE.ge ne ne' → eagree e1 e2 ne' := by
  intro e1 e2 ne ne' h hge r
  exact NeedDomain.nge_agree _ _ _ _ (hge r) (h r)

theorem match_succ_states : ∀ cfg, match_succ_statesStatement cfg := by
  intro cfg prog s f sp pc e m ts tf te tm an pc' cu instr ne nm
  intro hlink hstacks hfun han hpc hsucc hanpc henv hmem
  have hge := analyze_successors cfg cu f an pc instr pc' han hpc hsucc
  rw [hanpc] at hge
  change
    NE.ge ne
        (CompCert4Lean.Backend.Deadcode.transfer cfg f (prog_defmap cu)
          (vanalyze cfg cu f) pc' (PMap.get pc' an)).1 ∧
      (∀ ge sp b ofs,
        nlive ge sp
            (CompCert4Lean.Backend.Deadcode.transfer cfg f (prog_defmap cu)
              (vanalyze cfg cu f) pc' (PMap.get pc' an)).2 b ofs →
          nlive ge sp nm b ofs) at hge
  apply match_regular_states s f sp pc' e m ts tf te tm cu an
    hstacks hlink hfun han
  · exact deadcode_eagree_ge e te ne _ henv hge.1
  · exact magree_monotone m tm
      (fun b ofs => nlive (Genv.globalenv prog) sp nm b ofs)
      (fun b ofs => nlive (Genv.globalenv prog) sp
        (CompCert4Lean.Backend.Deadcode.transfer cfg f (prog_defmap cu)
          (vanalyze cfg cu f) pc' (PMap.get pc' an)).2 b ofs)
      hmem (by
        intro b ofs h
        exact hge.2 (Genv.globalenv prog) sp b ofs h)

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Backend.Deadcode
open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib

theorem eagree_set_res : eagree_set_resStatement := by
  intro e1 e2 v1 v2 res ne hv he
  cases res with
  | BR r =>
      intro q
      change vagree (Regmap.get q (Regmap.set r v1 e1))
        (Regmap.get q (Regmap.set r v2 e2)) (NE.get q ne)
      have hq := he q
      change vagree (Regmap.get q e1) (Regmap.get q e2)
        (NE.get q (NE.set r Nothing ne)) at hq
      rw [ne_get_set_local r q Nothing ne] at hq
      cases hp : peq q r with
      | left hqr =>
          subst q
          rw [Regmap.gss_proof Common.Values.val r v1 e1,
            Regmap.gss_proof Common.Values.val r v2 e2]
          exact vagree_lessdef v1 v2 (NE.get r ne) hv
      | right hqr =>
          rw [Regmap.gso_proof Common.Values.val q r v1 e1 hqr,
            Regmap.gso_proof Common.Values.val q r v2 e2 hqr]
          simpa only [hp] using hq
  | BR_none => exact he
  | BR_splitlong hi lo => exact he

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Backend.Deadcode
open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.IntvSets
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem builtin_nlive_all (ge : RTL.genv) (sp b : block) (i : Z) :
    nlive ge sp nmem_all b i := by
  constructor
  · intro _
    exact ISet.In_empty i
  · intro id iv _ h
    rw [PTree.gempty ISet.t id] at h
    cases h

private theorem builtin_nlive_stack_mono (ge : RTL.genv) (sp b : block)
    (i : Z) (nm : nmem) (ofs : Ptrofs.int) (sz : Z)
    (h : nlive ge sp nm b i) : nlive ge sp (nmem_add nm (Stk ofs) sz) b i := by
  cases h with
  | nlive_intro stk gl b i hs hg =>
      constructor
      · intro hb hi
        exact hs hb ((ISet.In_remove _ _ _ _).mp hi).2
      · exact hg

private theorem builtin_nlive_global_mono (ge : RTL.genv) (sp b : block)
    (i : Z) (nm : nmem) (id : ident) (ofs : Ptrofs.int) (sz : Z)
    (h : nlive ge sp nm b i) : nlive ge sp (nmem_add nm (Gl id ofs) sz) b i := by
  cases h with
  | nlive_intro stk gl b i hs hg =>
      simp only [nmem_add]
      cases hx : PTree.get id gl with
      | none => exact nlive.nlive_intro _ _ _ _ hs hg
      | some iv =>
          constructor
          · exact hs
          · intro id' iv' hsym hget hi
            by_cases heq : id' = id
            · subst id'
              rw [PTree.gss (A := ISet.t) id _ gl] at hget
              cases hget
              exact hg id iv hsym hx ((ISet.In_remove _ _ _ _).mp hi).2
            · rw [PTree.gso (A := ISet.t) (i := id') (j := id) _ gl heq] at hget
              exact hg id' iv' hsym hget hi

private theorem builtin_nlive_stack (ge : RTL.genv) (sp : block)
    (bc : block_classification) (nm : nmem) (ofs : Ptrofs.int) (sz i : Z)
    (gm : genv_match bc ge) (hsp : bc sp = BCstack)
    (hi : zLe (Ptrofs.unsigned ofs) i ∧ zLt i (zAdd (Ptrofs.unsigned ofs) sz)) :
    nlive ge sp (nmem_add nm (Stk ofs) sz) sp i := by
  cases nm with
  | NMemDead => exact builtin_nlive_all ge sp sp i
  | NMem stk gl =>
      constructor
      · intro _ h
        exact ((ISet.In_remove _ _ _ _).mp h).1 hi
      · intro id iv hsym _
        have hc := (gm.1 id sp).mp hsym
        rw [hsp] at hc
        cases hc

private theorem builtin_nlive_global (ge : RTL.genv) (sp b : block)
    (bc : block_classification) (nm : nmem) (id : ident) (ofs : Ptrofs.int) (sz i : Z)
    (gm : genv_match bc ge) (hsp : bc sp = BCstack)
    (hsym : Genv.find_symbol ge id = some b)
    (hi : zLe (Ptrofs.unsigned ofs) i ∧ zLt i (zAdd (Ptrofs.unsigned ofs) sz)) :
    nlive ge sp (nmem_add nm (Gl id ofs) sz) b i := by
  have hb := (gm.1 id b).mp hsym
  have hbs : b ≠ sp := by
    intro h
    subst b
    rw [hsp] at hb
    cases hb
  have hid : ∀ id', Genv.find_symbol ge id' = some b → id' = id := by
    intro id' hsym'
    have hb' := (gm.1 id' b).mp hsym'
    rw [hb] at hb'
    cases hb'
    rfl
  cases nm with
  | NMemDead => exact builtin_nlive_all ge sp b i
  | NMem stk gl =>
      simp only [nmem_add]
      cases hx : PTree.get id gl with
      | none =>
          constructor
          · intro h
            exact False.elim (hbs h)
          · intro id' iv hsym' hget
            have heq := hid id' hsym'
            subst id'
            rw [hx] at hget
            cases hget
      | some iv =>
          constructor
          · intro h
            exact False.elim (hbs h)
          · intro id' iv' hsym' hget hmem
            have heq := hid id' hsym'
            subst id'
            rw [PTree.gss (A := ISet.t) id _ gl] at hget
            cases hget
            exact ((ISet.In_remove _ _ _ _).mp hmem).1 hi

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Backend.Deadcode
open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open Lean Elab Tactic Meta

private theorem builtin_ptrofs_zero_add (x : Ptrofs.int) :
    Ptrofs.add Ptrofs.zero x = x := by
  change WordCore.add (WordCore.zero Ptrofs.wordsize) x = x
  apply WordCore.ext_of_val_eq
  have hadd : (WordCore.add (WordCore.zero Ptrofs.wordsize) x).val =
      ((WordCore.zero Ptrofs.wordsize).val + x.val) % (2 ^ Ptrofs.wordsize) := by
    run_tac
      let lctx ← getLCtx
      let xF := (lctx.findFromUserName? `x).get!
      let zeroE ← mkAppM ``CompCert4Lean.Lib.Integers.WordCore.zero
        #[mkConst ``CompCert4Lean.Lib.Integers.Ptrofs.wordsize]
      let e ← mkAppM (privateName "CompCert4Lean.Lib.Integers.WordCore.add_val")
        #[zeroE, mkFVar xF.fvarId]
      closeMainGoal Name.anonymous e
  rw [hadd]
  have hz : (WordCore.zero Ptrofs.wordsize).val = 0 := by
    change (WordCore.repr Ptrofs.wordsize (zOfNat 0)).val = 0
    simpa using (residue_zOfNat_local Ptrofs.wordsize 0)
  rw [hz, Nat.zero_add]
  exact Nat.mod_eq_of_lt (word64_val_lt_local x)

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Backend.Deadcode
open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

theorem transfer_builtin_arg_sound : transfer_builtin_arg_soundStatement := by
  intro prog bc e e' sp m m' a v heval
  induction heval with
  | eval_BA x =>
      intro nv ne1 nm1 ne2 nm2 htr he hm gm hs
      rcases Prod.mk.inj htr with ⟨rfl, rfl⟩
      exact ⟨Regmap.get x e', eval_BA x, add_need_vagree e e' x nv ne1 he,
        add_need_eagree e e' x nv ne1 he, hm⟩
  | eval_BA_int n =>
      intro nv ne1 nm1 ne2 nm2 htr he hm gm hs
      rcases Prod.mk.inj htr with ⟨rfl, rfl⟩
      exact ⟨_, eval_BA_int n, vagree_same _ nv, he, hm⟩
  | eval_BA_long n =>
      intro nv ne1 nm1 ne2 nm2 htr he hm gm hs
      rcases Prod.mk.inj htr with ⟨rfl, rfl⟩
      exact ⟨_, eval_BA_long n, vagree_same _ nv, he, hm⟩
  | eval_BA_float n =>
      intro nv ne1 nm1 ne2 nm2 htr he hm gm hs
      rcases Prod.mk.inj htr with ⟨rfl, rfl⟩
      exact ⟨_, eval_BA_float n, vagree_same _ nv, he, hm⟩
  | eval_BA_single n =>
      intro nv ne1 nm1 ne2 nm2 htr he hm gm hs
      rcases Prod.mk.inj htr with ⟨rfl, rfl⟩
      exact ⟨_, eval_BA_single n, vagree_same _ nv, he, hm⟩
  | eval_BA_loadstack chunk ofs v hload =>
      intro nv ne1 nm1 ne2 nm2 htr he hm gm hs
      rcases Prod.mk.inj htr with ⟨rfl, rfl⟩
      simp only [Val.offset_ptr, Mem.loadv, builtin_ptrofs_zero_add] at hload
      rcases magree_load _ _ _ chunk sp (Ptrofs.unsigned ofs) v hm hload
        (fun i hi => builtin_nlive_stack _ sp bc nm1 ofs _ i gm hs hi) with
        ⟨v', hl', hv'⟩
      refine ⟨v', eval_BA_loadstack chunk ofs v' ?_,
        vagree_lessdef _ _ nv hv', he, ?_⟩
      · simpa only [Val.offset_ptr, Mem.loadv, builtin_ptrofs_zero_add] using hl'
      · exact magree_monotone _ _ _ _ hm
          (fun b i hi => builtin_nlive_stack_mono _ sp b i nm1 ofs _ hi)
  | eval_BA_addrstack ofs =>
      intro nv ne1 nm1 ne2 nm2 htr he hm gm hs
      rcases Prod.mk.inj htr with ⟨rfl, rfl⟩
      exact ⟨_, eval_BA_addrstack ofs, vagree_same _ nv, he, hm⟩
  | eval_BA_loadglobal chunk id ofs v hload =>
      intro nv ne1 nm1 ne2 nm2 htr he hm gm hs
      rcases Prod.mk.inj htr with ⟨rfl, rfl⟩
      change Mem.loadv chunk m
        (match Genv.find_symbol (Genv.globalenv prog) id with
        | some b => Vptr b ofs | none => Vundef) = some v at hload
      cases hsym : Genv.find_symbol (Genv.globalenv prog) id with
      | none => simp only [hsym, Mem.loadv] at hload; cases hload
      | some b =>
          simp only [hsym, Mem.loadv] at hload
          rcases magree_load _ _ _ chunk b (Ptrofs.unsigned ofs) v hm hload
            (fun i hi => builtin_nlive_global _ sp b bc nm1 id ofs _ i gm hs hsym hi) with
            ⟨v', hl', hv'⟩
          refine ⟨v', eval_BA_loadglobal chunk id ofs v' ?_,
            vagree_lessdef _ _ nv hv', he, ?_⟩
          · change Mem.loadv chunk m'
              (match Genv.find_symbol (Genv.globalenv prog) id with
              | some b => Vptr b ofs | none => Vundef) = some v'
            simpa only [hsym, Mem.loadv] using hl'
          · exact magree_monotone _ _ _ _ hm
              (fun b i hi => builtin_nlive_global_mono _ sp b i nm1 id ofs _ hi)
  | eval_BA_addrglobal id ofs =>
      intro nv ne1 nm1 ne2 nm2 htr he hm gm hs
      rcases Prod.mk.inj htr with ⟨rfl, rfl⟩
      exact ⟨_, eval_BA_addrglobal id ofs, vagree_same _ nv, he, hm⟩
  | eval_BA_splitlong hi lo vhi vlo hhi hlo ihhi ihlo =>
      intro nv ne1 nm1 ne2 nm2 htr he hm gm hs
      change transfer_builtin_arg All (transfer_builtin_arg All (ne1, nm1) hi) lo =
        (ne2, nm2) at htr
      rcases hna : transfer_builtin_arg All (ne1, nm1) hi with ⟨ne, nm⟩
      rw [hna] at htr
      rcases ihlo All ne nm ne2 nm2 htr he hm gm hs with ⟨vlo', hlo', hvlo, he', hm'⟩
      rcases ihhi All ne1 nm1 ne nm hna he' hm' gm hs with ⟨vhi', hhi', hvhi, he'', hm''⟩
      exact ⟨_, eval_BA_splitlong hi lo vhi' vlo' hhi' hlo',
        vagree_lessdef _ _ nv (Val.longofwords_lessdef _ _ _ _ hvhi hvlo), he'', hm''⟩
  | eval_BA_addptr a1 a2 v1 v2 ha1 ha2 ih1 ih2 =>
      intro nv ne1 nm1 ne2 nm2 htr he hm gm hs
      change transfer_builtin_arg All (transfer_builtin_arg All (ne1, nm1) a1) a2 =
        (ne2, nm2) at htr
      rcases hna : transfer_builtin_arg All (ne1, nm1) a1 with ⟨ne, nm⟩
      rw [hna] at htr
      rcases ih2 All ne nm ne2 nm2 htr he hm gm hs with ⟨v2', h2', hv2, he', hm'⟩
      rcases ih1 All ne1 nm1 ne nm hna he' hm' gm hs with ⟨v1', h1', hv1, he'', hm''⟩
      exact ⟨_, eval_BA_addptr a1 a2 v1' v2' h1' h2',
        vagree_lessdef _ _ nv (Val.addl_lessdef _ _ _ _ hv1 hv2), he'', hm''⟩

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Backend.Deadcode
open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Coqlib

theorem transfer_builtin_args_sound : transfer_builtin_args_soundStatement := by
  intro prog e sp m e' m' bc al vl hEval
  unfold eval_builtin_args at hEval ⊢
  induction al generalizing vl with
  | nil =>
      cases hEval
      intro ne1 nm1 ne2 nm2 htr he hm gm hs
      simp [transfer_builtin_args] at htr
      cases htr
      exact ⟨[], list_forall2.nil _, Val.lessdef_list_nil, he, hm⟩
  | cons a al ih =>
      cases hEval with
      | cons _ _ ha htail =>
          intro ne1 nm1 ne2 nm2 htr he hm gm hs
          let p := transfer_builtin_arg All (ne1, nm1) a
          cases hp : transfer_builtin_arg All (ne1, nm1) a with
          | mk ne nm =>
              have htr' : transfer_builtin_args (ne, nm) al = (ne2, nm2) := by
                simpa [transfer_builtin_args, List.foldl, hp] using htr
              obtain ⟨vl', hEval', hLess', he', hm'⟩ :=
                ih _ htail ne nm ne2 nm2 htr' he hm gm hs
              obtain ⟨v', hEvalHead, hv, heHead, hmHead⟩ :=
                transfer_builtin_arg_sound prog bc e e' sp m m' a _ ha
                  All ne1 nm1 ne nm hp he' hm' gm hs
              refine ⟨v' :: vl', ?_, ?_, heHead, hmHead⟩
              · exact list_forall2.cons _ _ hEvalHead hEval'
              · exact Val.lessdef_list_cons _ _ _ _ hv hLess'

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers

theorem transf_volatile_store : transf_volatile_storeStatement := by
  intro prog v1 v2 v1' v2' m tm chunk sp nm t v m' hsem hptr hv hm
  cases hsem with
  | volatile_store_sem_intro b ofs _ _ _ _ hstore =>
      cases hptr
      refine ⟨rfl, ?_⟩
      cases hstore with
      | volatile_store_vol id ev v2 hvol hfind hmatch =>
          refine ⟨tm, ?_, hm⟩
          apply volatile_store_sem_intro
          exact volatile_store_vol chunk tm b ofs id ev v2' hvol hfind
            (eventval_match_lessdef _ ev (type_of_chunk chunk) _ _ hmatch
              (store_argument_load_result chunk v2 v2' hv))
      | volatile_store_nonvol v2 m' hvol hstore =>
          obtain ⟨tm', hstore', hm'⟩ :=
            magree_store_parallel m tm _ _ chunk b (Ptrofs.unsigned ofs) v2 m' v2'
              hm hstore hv (fun _ _ h _ => h)
          refine ⟨tm', ?_, hm'⟩
          apply volatile_store_sem_intro
          exact volatile_store_nonvol chunk tm b ofs v2' tm' hvol hstore'

end CompCert4Lean.Backend.Deadcodeproof


namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Deadcode
open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers

private theorem deadcode_add_zero (x : Z) : zOfInt (intOfZ x + 0) = x := by
  simp [zOfInt_intOfZ]

private theorem deadcode_id_no_overlap (m : mem) :
    Mem.meminj_no_overlap inject_id m := by
  intro b1 b1' d1 b2 b2' d2 ofs1 ofs2 hne h1 h2 _ _
  have h1' : (b1, (.Z0 : Z)) = (b1', d1) := Option.some.inj h1
  have h2' : (b2, (.Z0 : Z)) = (b2', d2) := Option.some.inj h2
  cases h1'
  cases h2'
  exact Or.inl hne

private theorem deadcode_store_extends : Mem.store_within_extendsStatement := by
  intro chunk m1 m2 b ofs v1 n1 v2 hext hs hv
  obtain ⟨n2, hs2, hi⟩ := Mem.store_mapped_inj inject_id chunk m1 b ofs v1 n1
    m2 b .Z0 v2 hext.mext_inj hs (deadcode_id_no_overlap m1) rfl
    ((val_inject_id v1 v2).mpr hv)
  change Mem.store chunk m2 b (zOfInt (intOfZ ofs + 0)) v2 = some n2 at hs2
  rw [deadcode_add_zero] at hs2
  refine ⟨n2, hs2, ?_⟩
  constructor
  · rw [Mem.nextblock_store _ _ _ _ _ _ hs, Mem.nextblock_store _ _ _ _ _ _ hs2]
    exact hext.mext_next
  · exact hi
  · intro b' ofs' k p hp
    obtain hp | hn := hext.mext_perm_inv b' ofs' k p
      (Mem.perm_store_2 _ _ _ _ _ _ hs2 _ _ _ _ hp)
    · exact Or.inl (Mem.perm_store_1 _ _ _ _ _ _ hs _ _ _ _ hp)
    · exact Or.inr (fun h => hn (Mem.perm_store_2 _ _ _ _ _ _ hs _ _ _ _ h))

private theorem deadcode_storebytes_extends : Mem.storebytes_within_extendsStatement := by
  intro m1 m2 b ofs bytes1 n1 bytes2 hext hs hv
  obtain ⟨n2, hs2, hi⟩ := Mem.storebytes_mapped_inj inject_id m1 b ofs bytes1 n1
    m2 b .Z0 bytes2 hext.mext_inj hs (deadcode_id_no_overlap m1) rfl hv
  change Mem.storebytes m2 b (zOfInt (intOfZ ofs + 0)) bytes2 = some n2 at hs2
  rw [deadcode_add_zero] at hs2
  refine ⟨n2, hs2, ?_⟩
  constructor
  · rw [Mem.nextblock_storebytes _ _ _ _ _ hs, Mem.nextblock_storebytes _ _ _ _ _ hs2]
    exact hext.mext_next
  · exact hi
  · intro b' ofs' k p hp
    obtain hp | hn := hext.mext_perm_inv b' ofs' k p
      (Mem.perm_storebytes_2 _ _ _ _ _ hs2 _ _ _ _ hp)
    · exact Or.inl (Mem.perm_storebytes_1 _ _ _ _ _ hs _ _ _ _ hp)
    · exact Or.inr (fun h => hn (Mem.perm_storebytes_2 _ _ _ _ _ hs _ _ _ _ h))

private theorem deadcode_free_extends : Mem.free_parallel_extendsStatement := by
  intro m1 m2 b lo hi n1 hext hf
  have hr := Mem.range_perm_inj inject_id m1 m2 b lo hi Cur Freeable b .Z0
    hext.mext_inj (Mem.free_range_perm _ _ _ _ _ hf) rfl
  change Mem.range_perm m2 b (zOfInt (intOfZ lo + 0))
    (zOfInt (intOfZ hi + 0)) Cur Freeable at hr
  rw [deadcode_add_zero, deadcode_add_zero] at hr
  obtain ⟨n2, hf2⟩ := Mem.range_perm_free m2 b lo hi hr
  refine ⟨n2, hf2, ?_⟩
  constructor
  · rw [Mem.nextblock_free _ _ _ _ _ hf, Mem.nextblock_free _ _ _ _ _ hf2]
    exact hext.mext_next
  · apply Mem.free_right_inj inject_id n1 m2 b lo hi n2
      (Mem.free_left_inj inject_id m1 m2 b lo hi n1 hext.mext_inj hf) hf2
    intro b' delta ofs k p hmap hp hb
    have heq : (b', (.Z0 : Z)) = (b, delta) := Option.some.inj hmap
    cases heq
    change intOfZ lo ≤ intOfZ (zOfInt (intOfZ ofs + 0)) ∧
      intOfZ (zOfInt (intOfZ ofs + 0)) < intOfZ hi at hb
    rw [deadcode_add_zero] at hb
    exact Mem.perm_free_2 _ _ _ _ _ hf _ _ _ hb hp
  · intro b' ofs k p hp
    obtain hp1 | hn := hext.mext_perm_inv b' ofs k p
      (Mem.perm_free_3 _ _ _ _ _ hf2 _ _ _ _ hp)
    · obtain ⟨hb, hlo, hhi⟩ | hp1' := Mem.perm_free_inv _ _ _ _ _ hf _ _ _ _ hp1
      · subst b'
        exact False.elim (Mem.perm_free_2 _ _ _ _ _ hf2 _ _ _ ⟨hlo, hhi⟩ hp)
      · exact Or.inl hp1'
    · exact Or.inr (fun h => hn (Mem.perm_free_3 _ _ _ _ _ hf _ _ _ _ h))

private theorem deadcode_alloc_extends
    (m1 m2 : mem) (lo hi : Z) (n1 : mem) (b : block)
    (hext : Mem.extends m1 m2) (ha : Mem.alloc m1 lo hi = (n1, b)) :
    ∃ n2, Mem.alloc m2 lo hi = (n2, b) ∧ Mem.extends n1 n2 := by
  cases ha2 : Mem.alloc m2 lo hi with
  | mk n2 b2 =>
    have hb : b2 = b := by
      rw [Mem.alloc_result _ _ _ _ _ ha2, Mem.alloc_result _ _ _ _ _ ha]
      exact hext.mext_next.symm
    subst b2
    have hperm : ∀ ofs k p, intOfZ lo ≤ intOfZ ofs ∧ intOfZ ofs < intOfZ hi → Mem.perm n2 b ofs k p := by
      intro ofs k p hr
      exact Mem.perm_implies _ _ _ _ _ _
        (Mem.perm_alloc_2 _ _ _ _ _ ha2 _ _ hr) (perm_F_any p)
    refine ⟨n2, rfl, ?_⟩
    constructor
    · rw [Mem.nextblock_alloc _ _ _ _ _ ha, Mem.nextblock_alloc _ _ _ _ _ ha2,
        hext.mext_next]
    · apply Mem.alloc_left_mapped_inj inject_id m1 n2 lo hi n1 b b .Z0
        (Mem.alloc_right_inj inject_id m1 m2 lo hi b n2 hext.mext_inj ha2) ha
        (Mem.valid_new_block _ _ _ _ _ ha2)
      · intro chunk _
        refine ⟨.Z0, ?_⟩
        apply intOfZ_injective
        change 0 = intOfZ (zOfInt (intOfZ (align_chunk chunk) * 0))
        rw [intOfZ_zOfInt]
        simp
      · intro ofs k p hr
        change Mem.perm n2 b (zOfInt (intOfZ ofs + 0)) k p
        rw [deadcode_add_zero]
        exact hperm ofs k p hr
      · rfl
    · intro b' ofs k p hp
      by_cases hb : b' = b
      · subst b'
        apply Or.inl
        exact Mem.perm_implies _ _ _ _ _ _
          (Mem.perm_alloc_2 _ _ _ _ _ ha _ _
            (Mem.perm_alloc_3 _ _ _ _ _ ha2 _ _ _ hp)) (perm_F_any p)
      · obtain hp1 | hn := hext.mext_perm_inv b' ofs k p
          (Mem.perm_alloc_4 _ _ _ _ _ ha2 _ _ _ _ hp hb)
        · exact Or.inl (Mem.perm_alloc_1 _ _ _ _ _ ha _ _ _ _ hp1)
        · exact Or.inr (fun h => hn (Mem.perm_alloc_4 _ _ _ _ _ ha _ _ _ _ h hb))

private theorem deadcode_lessdef_one {v : val} {vs : List val}
    (h : Val.lessdef_list [v] vs) :
    ∃ v', vs = [v'] ∧ Val.lessdef v v' := by
  cases h with
  | lessdef_list_cons v1 v2 vl1 vl2 hv ht =>
    cases ht
    exact ⟨v2, rfl, hv⟩

private theorem deadcode_lessdef_two {v w : val} {vs : List val}
    (h : Val.lessdef_list [v, w] vs) :
    ∃ v' w', vs = [v', w'] ∧ Val.lessdef v v' ∧ Val.lessdef w w' := by
  cases h with
  | lessdef_list_cons v1 v2 vl1 vl2 hv ht =>
    obtain ⟨w', hw, hl⟩ := deadcode_lessdef_one ht
    subst vl2
    exact ⟨v2, w', rfl, hv, hl⟩

private theorem deadcode_call_extends
    [binary64_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ef : external_function) (ge : Senv.t)
    (vargs : List val) (m1 : mem) (t : trace) (vres : val) (m2 m1' : mem)
    (vargs' : List val)
    (hc : external_call xi ef ge vargs m1 t vres m2)
    (hext : Mem.extends m1 m1') (hargs : Val.lessdef_list vargs vargs') :
    ∃ vres' m2', external_call xi ef ge vargs' m1' t vres' m2' ∧
      Val.lessdef vres vres' ∧ Mem.extends m2 m2' := by
  cases ef with
  | EF_external name sg =>
    obtain ⟨v', m', hcall, hval, hmem, _⟩ :=
      (external_functions_properties xi name sg).ec_mem_extends
        ge vargs m1 t vres m2 m1' vargs' hc hext hargs
    exact ⟨v', m', hcall, hval, hmem⟩
  | EF_inline_asm text sg clobbers =>
    obtain ⟨v', m', hcall, hval, hmem, _⟩ :=
      (inline_assembly_properties xi text sg).ec_mem_extends
        ge vargs m1 t vres m2 m1' vargs' hc hext hargs
    exact ⟨v', m', hcall, hval, hmem⟩
  | EF_builtin name sg | EF_runtime name sg =>
    change builtin_or_external_sem xi name sg ge vargs m1 t vres m2 at hc
    change ∃ vres' m2', builtin_or_external_sem xi name sg ge vargs' m1' t vres' m2' ∧
      Val.lessdef vres vres' ∧ Mem.extends m2 m2'
    unfold builtin_or_external_sem at hc ⊢
    cases hlookup : CompCert4Lean.Common.Builtins.lookup_builtin_function name sg with
    | some bf =>
      rw [hlookup] at hc
      obtain ⟨v', hcall, hval⟩ := known_builtin_sem_lessdef bf ge vargs m1 t vres m2
        ge vargs' m1' hc hargs
      cases hc
      exact ⟨v', m1', hcall, hval, hext⟩
    | none =>
      rw [hlookup] at hc
      obtain ⟨v', m', hcall, hval, hmem, _⟩ :=
        (external_functions_properties xi name sg).ec_mem_extends
          ge vargs m1 t vres m2 m1' vargs' hc hext hargs
      exact ⟨v', m', hcall, hval, hmem⟩
  | EF_vload chunk =>
    cases hc with
    | volatile_load_sem_intro b ofs m t v hl =>
      obtain ⟨vptr, rfl, hp⟩ := deadcode_lessdef_one hargs
      cases hp
      obtain ⟨v', hload, hval⟩ := volatile_load_extends ge chunk m1 b ofs t vres m1' hl hext
      exact ⟨v', m1', volatile_load_sem_intro b ofs m1' t v' hload, hval, hext⟩
  | EF_vstore chunk =>
    cases hc with
    | volatile_store_sem_intro b ofs m v t n hs =>
      obtain ⟨vptr, v', rfl, hp, hv⟩ := deadcode_lessdef_two hargs
      cases hp
      cases hs with
      | volatile_store_vol id ev v hvol hfind hmatch =>
        refine ⟨Vundef, m1', volatile_store_sem_intro b ofs m1' v' _ m1' ?_,
          Val.lessdef_refl _, hext⟩
        exact volatile_store_vol chunk m1' b ofs id ev v' hvol hfind
          (eventval_match_lessdef ge ev (type_of_chunk chunk) _ _ hmatch
            (Val.load_result_lessdef chunk v v' hv))
      | volatile_store_nonvol =>
        rename_i hvol hstore
        obtain ⟨n', hstore', hext'⟩ := deadcode_store_extends chunk m1 m1' b
          (Ptrofs.unsigned ofs) v m2 v' hext hstore hv
        exact ⟨Vundef, n', volatile_store_sem_intro b ofs m1' v' _ n'
          (volatile_store_nonvol chunk m1' b ofs v' n' hvol hstore'),
          Val.lessdef_refl _, hext'⟩
  | EF_malloc =>
    cases hc with
    | extcall_malloc_sem_intro sz m n b n' ha hs =>
      obtain ⟨v', rfl, hv⟩ := deadcode_lessdef_one hargs
      change Val.lessdef (.Vlong _) v' at hv
      cases hv
      obtain ⟨n2, ha2, hext2⟩ := deadcode_alloc_extends m1 m1' _ _ n b hext ha
      obtain ⟨n2', hs2, hext2'⟩ := deadcode_store_extends _ n n2 b _ _ m2 _
        hext2 hs (Val.lessdef_refl _)
      exact ⟨Vptr b Ptrofs.zero, n2', extcall_malloc_sem_intro sz m1' n2 b n2' ha2 hs2,
        Val.lessdef_refl _, hext2'⟩
  | EF_free =>
    cases hc with
    | extcall_free_sem_ptr b lo sz m n hl hf =>
      obtain ⟨v', rfl, hv⟩ := deadcode_lessdef_one hargs
      cases hv
      obtain ⟨sz', hl', hsz⟩ := Mem.load_extends _ m1 m1' b _ _ hext hl
      change Val.lessdef (.Vlong _) sz' at hsz
      cases hsz
      obtain ⟨n', hf', hext'⟩ := deadcode_free_extends m1 m1' b _ _ m2 hext hf
      exact ⟨Vundef, n', extcall_free_sem_ptr b lo sz m1' n' hl' hf',
        Val.lessdef_refl _, hext'⟩
    | extcall_free_sem_null m =>
      obtain ⟨v', rfl, hv⟩ := deadcode_lessdef_one hargs
      change Val.lessdef (.Vlong _) v' at hv
      cases hv
      exact ⟨Vundef, m1', extcall_free_sem_null m1', Val.lessdef_refl _, hext⟩
  | EF_memcpy sz al =>
    cases hc with
    | extcall_memcpy_sem_intro bd od bs os m bytes n hal hsz hsa hsrc hdst hno hl hs =>
      obtain ⟨v1, v2, rfl, hv1, hv2⟩ := deadcode_lessdef_two hargs
      cases hv1
      cases hv2
      obtain ⟨bytes', hl', hbytes⟩ := Mem.loadbytes_inj inject_id m1 m1' sz bs
        (Ptrofs.unsigned os) bs .Z0 bytes hext.mext_inj hl rfl
      change Mem.loadbytes m1' bs (zOfInt (intOfZ (Ptrofs.unsigned os) + 0)) sz =
        some bytes' at hl'
      rw [deadcode_add_zero] at hl'
      obtain ⟨n', hs', hext'⟩ := deadcode_storebytes_extends m1 m1' bd
        (Ptrofs.unsigned od) bytes m2 bytes' hext hs hbytes
      exact ⟨Vundef, n', extcall_memcpy_sem_intro bd od bs os m1' bytes' n'
        hal hsz hsa hsrc hdst hno hl' hs', Val.lessdef_refl _, hext'⟩
  | EF_annot kind text targs =>
    cases hc with
    | extcall_annot_sem_intro evs hm =>
      exact ⟨Vundef, m1', extcall_annot_sem_intro vargs' m1' evs
        (eventval_list_match_lessdef ge evs targs vargs hm vargs' hargs),
        Val.lessdef_refl _, hext⟩
  | EF_annot_val kind text targ =>
    cases hc with
    | extcall_annot_val_sem_intro v m ev hm =>
      obtain ⟨v', rfl, hv⟩ := deadcode_lessdef_one hargs
      exact ⟨v', m1', extcall_annot_val_sem_intro v' m1' ev
        (eventval_match_lessdef ge ev targ vres v' hm hv), hv, hext⟩
  | EF_debug kind text targs =>
    cases hc
    exact ⟨Vundef, m1', extcall_debug_sem_intro vargs' m1', Val.lessdef_refl _, hext⟩

private theorem deadcode_symbols
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ef : external_function) (ge1 ge2 : Senv.t)
    (args : List val) (m : mem) (t : trace) (v : val) (m' : mem)
    (heq : Senv.equiv ge1 ge2)
    (hc : external_call xi ef ge1 args m t v m') :
    external_call xi ef ge2 args m t v m' := by
  cases ef with
  | EF_external name sg =>
      exact (external_functions_properties xi name sg).ec_symbols_preserved
        ge1 ge2 args m t v m' heq hc
  | EF_inline_asm text sg clobbers =>
      exact (inline_assembly_properties xi text sg).ec_symbols_preserved
        ge1 ge2 args m t v m' heq hc
  | EF_builtin name sg | EF_runtime name sg =>
      change builtin_or_external_sem xi name sg ge1 args m t v m' at hc
      change builtin_or_external_sem xi name sg ge2 args m t v m'
      unfold builtin_or_external_sem at hc ⊢
      cases hlookup : CompCert4Lean.Common.Builtins.lookup_builtin_function name sg with
      | some bf =>
          rw [hlookup] at hc
          cases hc with
          | known_builtin_sem_intro args v hev =>
              exact known_builtin_sem_intro args v m hev
      | none =>
          rw [hlookup] at hc
          exact (external_functions_properties xi name sg).ec_symbols_preserved
            ge1 ge2 args m t v m' heq hc
  | EF_vload chunk =>
      cases hc with
      | volatile_load_sem_intro b ofs m t v hload =>
          exact volatile_load_sem_intro b ofs m t v
            (volatile_load_preserved ge1 ge2 chunk m b ofs t v heq hload)
  | EF_vstore chunk =>
      cases hc with
      | volatile_store_sem_intro b ofs m v t m' hstore =>
          exact volatile_store_sem_intro b ofs m v t m'
            (volatile_store_preserved ge1 ge2 chunk m b ofs v t m' heq hstore)
  | EF_malloc =>
      cases hc with
      | extcall_malloc_sem_intro sz m n b n' ha hs =>
          exact extcall_malloc_sem_intro sz m n b m' ha hs
  | EF_free =>
      cases hc with
      | extcall_free_sem_ptr b lo sz m n hl hf =>
          exact extcall_free_sem_ptr b lo sz m m' hl hf
      | extcall_free_sem_null m => exact extcall_free_sem_null m
  | EF_memcpy sz al =>
      cases hc with
      | extcall_memcpy_sem_intro bd od bs os m bytes n hal hsz hsa hsrc hdst hno hl hs =>
          exact extcall_memcpy_sem_intro bd od bs os m bytes m'
            hal hsz hsa hsrc hdst hno hl hs
  | EF_annot kind text targs =>
      cases hc with
      | extcall_annot_sem_intro evs hm =>
          exact extcall_annot_sem_intro args m evs
            (eventval_list_match_preserved ge1 ge2 heq.2.1 heq.1 evs targs args hm)
  | EF_annot_val kind text targ =>
      cases hc with
      | extcall_annot_val_sem_intro v m ev hm =>
          exact extcall_annot_val_sem_intro v m ev
            (eventval_match_preserved ge1 ge2 heq.2.1 heq.1 ev targ v hm)
  | EF_debug kind text targs =>
      cases hc
      exact extcall_debug_sem_intro args m


end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Backend.Deadcode
open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

theorem transf_external_call : ∀ cfg, transf_external_callStatement cfg := by
  intro cfg prog tprog hmatch xi e sp m args vargs ef t vres m' res
    ne2 nm2 ne1 nm1 bc te tm hargs hcall htransfer he hm hgm hsp
  obtain ⟨tvargs, heval, hless, he', hm'⟩ :=
    transfer_builtin_args_sound prog e sp m te tm bc args vargs hargs
      (kill_builtin_res res ne2) nmem_all ne1 nm1 htransfer he hm hgm hsp
  have hevalt :
      eval_builtin_args (Genv.to_senv (Genv.globalenv tprog))
        (fun r => Regmap.get r te) (Vptr sp Ptrofs.zero) tm args tvargs :=
    eval_builtin_args_preserved reg RTL.fundef Unit RTL.fundef Unit
      (Genv.globalenv prog) (Genv.globalenv tprog)
      (fun r => Regmap.get r te) (Vptr sp Ptrofs.zero) tm
      (symbols_preserved cfg prog tprog hmatch) args tvargs heval
  have hmext : Mem.extends m tm :=
    magree_extends m tm
      (fun b ofs => nlive (Genv.globalenv prog) sp nmem_all b ofs)
      (fun b ofs => builtin_nlive_all (Genv.globalenv prog) sp b ofs) hm'
  obtain ⟨tvres, tm', hcall', hvres, hmext'⟩ :=
    deadcode_call_extends xi ef
      (Genv.to_senv (Genv.globalenv prog)) vargs m t vres m' tm tvargs
      hcall hmext hless
  refine ⟨tvargs, tvres, tm', hevalt, ?_, ?_, ?_⟩
  · exact deadcode_symbols xi ef
      (Genv.to_senv (Genv.globalenv prog))
      (Genv.to_senv (Genv.globalenv tprog)) tvargs tm t tvres tm'
      (senv_preserved cfg prog tprog hmatch) hcall'
  · exact eagree_set_res e te vres tvres res ne2 hvres he'
  · exact mextends_agree m' tm'
      (fun b ofs => nlive (Genv.globalenv prog) sp nm2 b ofs) hmext'

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.X86.Op CompCert4Lean.X86.NeedOp
open CompCert4Lean.Backend.Deadcode CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Backend.Registers CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueAnalysis CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Events CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Smallstep CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib CompCert4Lean.Lib.Integers CompCert4Lean.Lib.Maps
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

private theorem deadcode_add_needs_all_eagree (args : List reg)
    (e te : regset) (ne : nenv) :
    eagree e te (add_needs_all args ne) → eagree e te ne := by
  induction args with
  | nil => exact id
  | cons arg args ih =>
      intro henv
      exact ih (add_need_all_eagree _ _ _ _ henv)

private theorem deadcode_add_needs_eagree (args : List reg)
    (needs : List nval) (e te : regset) (ne : nenv) :
    eagree e te (add_needs args needs ne) → eagree e te ne := by
  induction args generalizing needs with
  | nil => exact id
  | cons arg args ih =>
      cases needs with
      | nil => exact deadcode_add_needs_all_eagree (arg :: args) e te ne
      | cons need needs =>
          intro henv
          exact ih needs (add_need_eagree _ _ _ _ _ henv)

private theorem deadcode_dead {need : nval} :
    is_dead need = true → need = Nothing := by
  cases need <;> simp [is_dead]

private theorem deadcode_live {need : nval} (hdead : is_dead need = false) :
    need ≠ Nothing := by
  intro heq
  cases heq
  contradiction

private theorem deadcode_zero_agree (value : val) :
    vagree value (Vint Int.zero) (nval.I Int.zero) := by
  cases value <;> try trivial
  exact iagree_zero _ _

private theorem deadcode_step_op
    (cfg : CompilerConfig) (prog tprog : program) (xi : ExternalCalls)
    (s ts : List stackframe) (f tf : function) (sp : block) (pc next : node)
    (e te : regset) (m tm : mem) (cu : program) (an : PMap.t NA.t)
    (op : operation) (args : List reg) (res : reg) (value : val)
    (hprog : match_prog cfg prog tprog)
    (hstacks : list_forall2 (match_stackframes cfg prog) s ts)
    (hlink : linkorder cu prog)
    (hfun : Deadcode.transf_function cfg (prog_defmap cu) (romem_for cfg cu) f = .OK tf)
    (han : Deadcode.analyze cfg f (prog_defmap cu) (vanalyze cfg cu f) = some an)
    (hcode : PTree.get pc f.fn_code = some (.Iop op args res next))
    (heval : eval_operation (Genv.globalenv prog) (Vptr sp Ptrofs.zero) op
      (args.map (fun arg => Regmap.get arg e)) m = some value)
    (henv : eagree e te (Deadcode.transfer cfg f (prog_defmap cu)
      (vanalyze cfg cu f) pc (PMap.get pc an)).1)
    (hmem : magree m tm (nlive (Genv.globalenv prog) sp
      (Deadcode.transfer cfg f (prog_defmap cu) (vanalyze cfg cu f) pc
        (PMap.get pc an)).2)) :
    ∃ target,
      RTL.step xi (Genv.globalenv tprog) (State ts tf (Vptr sp Ptrofs.zero) pc te tm)
        E0 target ∧
      match_states cfg prog
        (State s f (Vptr sp Ptrofs.zero) next (Regmap.set res value e) m) target := by
  have htarget := transf_function_at cfg cu f tf an pc _ hfun han hcode
  generalize hanpc : PMap.get pc an = after at henv hmem
  obtain ⟨ne, nm⟩ := after
  simp only [Deadcode.transf_instr, hanpc] at htarget
  simp only [Deadcode.transfer, hcode] at henv hmem
  have hsucc := match_succ_states cfg prog s f sp pc (Regmap.set res value e) m
    ts tf
  by_cases hdead : is_dead (nreg ne res) = true
  · simp only [hdead, ↓reduceIte] at henv hmem
    refine ⟨State ts tf (Vptr sp Ptrofs.zero) next te tm, ?_, ?_⟩
    · apply RTL.exec_Inop
      simpa only [Deadcode.transf_instr, hdead, ↓reduceIte] using htarget
    · exact hsucc te tm an next cu (.Iop op args res next) ne nm
        hlink hstacks hfun han hcode (by simp [RTL.successors_instr]) hanpc
        (eagree_update_dead _ _ _ _ _ (deadcode_dead hdead) henv) hmem
  · have hdead' : is_dead (nreg ne res) = false := Bool.eq_false_iff.mpr hdead
    by_cases hzero : is_int_zero (nreg ne res) = true
    · simp only [hdead, hzero, ↓reduceIte] at henv hmem
      refine ⟨State ts tf (Vptr sp Ptrofs.zero) next (Regmap.set res (Vint Int.zero) te) tm,
        ?_, ?_⟩
      · apply RTL.exec_Iop
        · simpa [hdead, hzero] using htarget
        · rfl
      · apply hsucc _ tm an next cu (.Iop op args res next) ne nm
          hlink hstacks hfun han hcode (by simp [RTL.successors_instr]) hanpc
        · apply eagree_update _ _ _ _ _ _ _ henv
          rw [is_int_zero_sound _ hzero]
          exact deadcode_zero_agree value
        · exact hmem
    · simp only [hdead, hzero, ↓reduceIte] at henv hmem
      have hargs := add_needs_vagree args (needs_of_operation op (nreg ne res)) e te _ henv
      have hbase := deadcode_add_needs_eagree args (needs_of_operation op (nreg ne res)) e te _ henv
      have hpreserve : ∀ tv,
          eval_operation (Genv.globalenv prog) (Vptr sp Ptrofs.zero) op
            (args.map (fun arg => Regmap.get arg te)) tm = some tv →
          vagree value tv (nreg ne res) →
          PTree.get pc tf.fn_code = some (.Iop op args res next) →
          ∃ target,
            RTL.step xi (Genv.globalenv tprog)
              (State ts tf (Vptr sp Ptrofs.zero) pc te tm) E0 target ∧
            match_states cfg prog
              (State s f (Vptr sp Ptrofs.zero) next (Regmap.set res value e) m) target := by
        intro tv heval' hagree hcode'
        refine ⟨State ts tf (Vptr sp Ptrofs.zero) next (Regmap.set res tv te) tm, ?_, ?_⟩
        · apply RTL.exec_Iop _ _ _ _ _ _ _ _ _ _ _ hcode'
          rw [eval_operation_preserved _ _ _ _ (Genv.globalenv prog) (Genv.globalenv tprog)
            (symbols_preserved cfg prog tprog hprog)]
          exact heval'
        · exact hsucc _ tm an next cu (.Iop op args res next) ne nm
            hlink hstacks hfun han hcode (by simp [RTL.successors_instr]) hanpc
            (eagree_update _ _ _ _ _ _ hagree hbase) hmem
      by_cases hred : operation_is_redundant op (nreg ne res) = true
      · cases args with
        | nil =>
            obtain ⟨tv, heval', hagree⟩ := needs_of_operation_sound _ _ _ _ hmem.ma_perm
              op [] value (nreg ne res) [] heval hargs (deadcode_live hdead')
            apply hpreserve tv heval' hagree
            simpa [hdead, hzero, hred] using htarget
        | cons arg args =>
            have hagree := operation_is_redundant_sound _ _ _ op (nreg ne res)
              (Regmap.get arg e) (args.map (fun arg => Regmap.get arg e)) value
              (Regmap.get arg te) (args.map (fun arg => Regmap.get arg te)) hred heval hargs
            refine ⟨State ts tf (Vptr sp Ptrofs.zero) next
              (Regmap.set res (Regmap.get arg te) te) tm, ?_, ?_⟩
            · apply RTL.exec_Iop
              · simpa [hdead, hzero, hred] using htarget
              · rfl
            · exact hsucc _ tm an next cu (.Iop op (arg :: args) res next) ne nm
                hlink hstacks hfun han hcode (by simp [RTL.successors_instr]) hanpc
                (eagree_update _ _ _ _ _ _ hagree hbase) hmem
      · obtain ⟨tv, heval', hagree⟩ := needs_of_operation_sound _ _ _ _ hmem.ma_perm
          op _ value (nreg ne res) _ heval hargs (deadcode_live hdead')
        apply hpreserve tv heval' hagree
        simpa [hdead, hzero, hred] using htarget

private theorem deadcode_step_load
    (cfg : CompilerConfig) (prog tprog : program) (xi : ExternalCalls)
    (s ts : List stackframe) (f tf : function) (sp : block) (pc next : node)
    (e te : regset) (m tm : mem) (cu : program) (an : PMap.t NA.t)
    (chunk : memory_chunk) (addr : addressing) (args : List reg) (dst : reg)
    (address value : val)
    (hprog : match_prog cfg prog tprog)
    (hstacks : list_forall2 (match_stackframes cfg prog) s ts)
    (hlink : linkorder cu prog)
    (hfun : Deadcode.transf_function cfg (prog_defmap cu) (romem_for cfg cu) f = .OK tf)
    (han : Deadcode.analyze cfg f (prog_defmap cu) (vanalyze cfg cu f) = some an)
    (hcode : PTree.get pc f.fn_code = some (.Iload chunk addr args dst next))
    (haddr : eval_addressing (Genv.globalenv prog) (Vptr sp Ptrofs.zero) addr
      (args.map (fun arg => Regmap.get arg e)) = some address)
    (hload : Mem.loadv chunk m address = some value)
    (hsound : sound_state cfg prog (State s f (Vptr sp Ptrofs.zero) pc e m))
    (henv : eagree e te (Deadcode.transfer cfg f (prog_defmap cu)
      (vanalyze cfg cu f) pc (PMap.get pc an)).1)
    (hmem : magree m tm (nlive (Genv.globalenv prog) sp
      (Deadcode.transfer cfg f (prog_defmap cu) (vanalyze cfg cu f) pc
        (PMap.get pc an)).2)) :
    ∃ target,
      RTL.step xi (Genv.globalenv tprog) (State ts tf (Vptr sp Ptrofs.zero) pc te tm)
        E0 target ∧
      match_states cfg prog
        (State s f (Vptr sp Ptrofs.zero) next (Regmap.set dst value e) m) target := by
  have htarget := transf_function_at cfg cu f tf an pc _ hfun han hcode
  generalize hanpc : PMap.get pc an = after at henv hmem
  obtain ⟨ne, nm⟩ := after
  simp only [Deadcode.transf_instr, hanpc] at htarget
  simp only [Deadcode.transfer, hcode] at henv hmem
  have hsucc := match_succ_states cfg prog s f sp pc (Regmap.set dst value e) m
    ts tf
  by_cases hdead : is_dead (nreg ne dst) = true
  · simp only [hdead, ↓reduceIte] at henv hmem
    refine ⟨State ts tf (Vptr sp Ptrofs.zero) next te tm, ?_, ?_⟩
    · apply RTL.exec_Inop
      simpa [hdead] using htarget
    · exact hsucc te tm an next cu (.Iload chunk addr args dst next) ne nm
        hlink hstacks hfun han hcode (by simp [RTL.successors_instr]) hanpc
        (eagree_update_dead _ _ _ _ _ (deadcode_dead hdead) henv) hmem
  · by_cases hzero : is_int_zero (nreg ne dst) = true
    · simp only [hdead, hzero, ↓reduceIte] at henv hmem
      refine ⟨State ts tf (Vptr sp Ptrofs.zero) next (Regmap.set dst (Vint Int.zero) te) tm,
        ?_, ?_⟩
      · apply RTL.exec_Iop
        · simpa [hdead, hzero] using htarget
        · rfl
      · apply hsucc _ tm an next cu (.Iload chunk addr args dst next) ne nm
          hlink hstacks hfun han hcode (by simp [RTL.successors_instr]) hanpc
        · apply eagree_update _ _ _ _ _ _ _ henv
          rw [is_int_zero_sound _ hzero]
          exact deadcode_zero_agree value
        · exact hmem
    · simp only [hdead, hzero, ↓reduceIte] at henv hmem
      have hargs := add_needs_all_lessdef args e te _ henv
      have hbase := deadcode_add_needs_all_eagree args e te _ henv
      cases address with
      | Vptr loc ofs =>
          obtain ⟨taddr, htaddr, hless⟩ := eval_addressing_lessdef _ _ _ _ _ _ _ _ hargs haddr
          cases hless
          obtain ⟨bc, hptr, hge, hsp⟩ :=
            aaddressing_sound cfg cu prog s f sp pc e m addr args loc ofs hsound hlink haddr
          obtain ⟨tv, htload, hv⟩ := magree_load m tm _ chunk loc (Ptrofs.unsigned ofs) value
            hmem hload (fun index hrange => nlive_add _ _ bc loc ofs _ nm _ index hge hsp hptr hrange)
          refine ⟨State ts tf (Vptr sp Ptrofs.zero) next (Regmap.set dst tv te) tm, ?_, ?_⟩
          · apply RTL.exec_Iload _ _ _ _ _ _ chunk addr args dst next (Vptr loc ofs) tv
            · simpa [hdead, hzero] using htarget
            · rw [eval_addressing_preserved _ _ _ _ (Genv.globalenv prog) (Genv.globalenv tprog)
                (symbols_preserved cfg prog tprog hprog)]
              exact htaddr
            · exact htload
          · apply hsucc _ tm an next cu (.Iload chunk addr args dst next) ne nm
              hlink hstacks hfun han hcode (by simp [RTL.successors_instr]) hanpc
            · exact eagree_update _ _ _ _ _ _ (vagree_lessdef _ _ _ hv) hbase
            · apply magree_monotone _ _ _ _ hmem
              intro loc index hlive
              exact incl_nmem_add _ _ _ _ _ _ _ hlive
      | _ => simp [Mem.loadv] at hload

private theorem deadcode_step_store
    (cfg : CompilerConfig) (prog tprog : program) (xi : ExternalCalls)
    (s ts : List stackframe) (f tf : function) (sp : block) (pc next : node)
    (e te : regset) (m tm result : mem) (cu : program) (an : PMap.t NA.t)
    (chunk : memory_chunk) (addr : addressing) (args : List reg) (src : reg)
    (address : val)
    (hprog : match_prog cfg prog tprog)
    (hstacks : list_forall2 (match_stackframes cfg prog) s ts)
    (hlink : linkorder cu prog)
    (hfun : Deadcode.transf_function cfg (prog_defmap cu) (romem_for cfg cu) f = .OK tf)
    (han : Deadcode.analyze cfg f (prog_defmap cu) (vanalyze cfg cu f) = some an)
    (hcode : PTree.get pc f.fn_code = some (.Istore chunk addr args src next))
    (haddr : eval_addressing (Genv.globalenv prog) (Vptr sp Ptrofs.zero) addr
      (args.map (fun arg => Regmap.get arg e)) = some address)
    (hstore : Mem.storev chunk m address (Regmap.get src e) = some result)
    (hsound : sound_state cfg prog (State s f (Vptr sp Ptrofs.zero) pc e m))
    (henv : eagree e te (Deadcode.transfer cfg f (prog_defmap cu)
      (vanalyze cfg cu f) pc (PMap.get pc an)).1)
    (hmem : magree m tm (nlive (Genv.globalenv prog) sp
      (Deadcode.transfer cfg f (prog_defmap cu) (vanalyze cfg cu f) pc
        (PMap.get pc an)).2)) :
    ∃ target,
      RTL.step xi (Genv.globalenv tprog) (State ts tf (Vptr sp Ptrofs.zero) pc te tm)
        E0 target ∧
      match_states cfg prog (State s f (Vptr sp Ptrofs.zero) next e result) target := by
  have htarget := transf_function_at cfg cu f tf an pc _ hfun han hcode
  generalize hanpc : PMap.get pc an = after at henv hmem
  obtain ⟨ne, nm⟩ := after
  simp only [Deadcode.transf_instr, hanpc] at htarget
  simp only [Deadcode.transfer, hcode] at henv hmem
  have hsucc := match_succ_states cfg prog s f sp pc e result ts tf
  cases address with
  | Vptr loc ofs =>
      obtain ⟨bc, hptr, hge, hsp⟩ :=
        aaddressing_sound cfg cu prog s f sp pc e m addr args loc ofs hsound hlink haddr
      by_cases hcontains : nmem_contains nm
          (aaddressing cfg (PMap.get pc (vanalyze cfg cu f)) addr args) (size_chunk chunk) = true
      · simp only [hcontains, ↓reduceIte] at henv hmem
        have hargs := add_needs_all_lessdef args e te _ henv
        have hneed := deadcode_add_needs_all_eagree args e te _ henv
        have hvalue := add_need_vagree _ _ _ _ _ hneed
        have hbase := add_need_eagree _ _ _ _ _ hneed
        obtain ⟨taddr, htaddr, hless⟩ := eval_addressing_lessdef _ _ _ _ _ _ _ _ hargs haddr
        cases hless
        obtain ⟨tm', htstore, hmem'⟩ := magree_store_parallel m tm _
          (nlive (Genv.globalenv prog) sp nm) chunk loc (Ptrofs.unsigned ofs)
          (Regmap.get src e) result (Regmap.get src te) hmem hstore hvalue
          (fun other index hlive hrange =>
            nlive_remove _ _ bc loc ofs _ nm _ other index hge hsp hptr hlive hrange)
        refine ⟨State ts tf (Vptr sp Ptrofs.zero) next te tm', ?_, ?_⟩
        · apply RTL.exec_Istore _ _ _ _ _ _ chunk addr args src next (Vptr loc ofs) tm'
          · simpa [hcontains] using htarget
          · rw [eval_addressing_preserved _ _ _ _ (Genv.globalenv prog) (Genv.globalenv tprog)
              (symbols_preserved cfg prog tprog hprog)]
            exact htaddr
          · exact htstore
        · exact hsucc te tm' an next cu (.Istore chunk addr args src next) ne nm
            hlink hstacks hfun han hcode (by simp [RTL.successors_instr]) hanpc hbase hmem'
      · simp only [hcontains, ↓reduceIte] at henv hmem
        refine ⟨State ts tf (Vptr sp Ptrofs.zero) next te tm, ?_, ?_⟩
        · apply RTL.exec_Inop
          simpa [hcontains] using htarget
        · apply hsucc te tm an next cu (.Istore chunk addr args src next) ne nm
            hlink hstacks hfun han hcode (by simp [RTL.successors_instr]) hanpc henv
          exact magree_store_left m tm _ chunk loc (Ptrofs.unsigned ofs)
            (Regmap.get src e) result hmem hstore
            (fun index hrange => nlive_contains _ _ bc loc ofs _ nm _ index
              hge hsp hptr (Bool.eq_false_iff.mpr hcontains) hrange)
  | _ => simp [Mem.storev] at hstore

private theorem deadcode_eventually_runtime
    (prog : program) (xi : ExternalCalls)
    (s : List stackframe) (f : function) (sp : block) (next : node)
    (e : regset) (m : mem) (args : List val) (res : reg)
    {name sg bf} (hlookup : lookup_builtin_function name sg = some bf)
    (post : state → Prop)
    (hpost : ∀ value, builtin_function_sem bf args = some value →
      post (State s f (Vptr sp Ptrofs.zero) next (Regmap.set res value e) m)) :
    eventually prog xi 2
      (Callstate (Stackframe res f (Vptr sp Ptrofs.zero) next e :: s)
        (.External (.EF_runtime name sg)) args m) post := by
  apply eventually_later
  · intro result hfinal
    cases hfinal
  · intro tr target hstep
    cases hstep with
    | exec_function_external _ _ _ value _ _ _ hcall =>
        simp only [external_call, builtin_or_external_sem, hlookup] at hcall
        cases hcall
        rfl
  · intro tr target hstep
    cases hstep with
    | exec_function_external _ _ _ value _ _ _ hcall =>
        simp only [external_call, builtin_or_external_sem, hlookup] at hcall
        cases hcall with
        | known_builtin_sem_intro _ _ heval =>
            apply eventually_later
            · intro result hfinal
              cases hfinal
            · intro tr target hstep
              cases hstep
              rfl
            · intro tr target hstep
              cases hstep
              exact CompCert4Lean.Common.Smallstep.eventually.eventually_now _ _ (hpost value heval)

private theorem deadcode_step_call
    (cfg : CompilerConfig) (prog tprog : program) (xi : ExternalCalls)
    (s ts : List stackframe) (f tf : function) (sp : block) (pc next : node)
    (e te : regset) (m tm : mem) (cu : program) (an : PMap.t NA.t)
    (sig : signature) (ros : Sum reg ident) (args : List reg) (res : reg) (fd : fundef)
    (hprog : match_prog cfg prog tprog)
    (hstacks : list_forall2 (match_stackframes cfg prog) s ts)
    (hlink : linkorder cu prog)
    (hfun : Deadcode.transf_function cfg (prog_defmap cu) (romem_for cfg cu) f = .OK tf)
    (han : Deadcode.analyze cfg f (prog_defmap cu) (vanalyze cfg cu f) = some an)
    (hcode : PTree.get pc f.fn_code = some (.Icall sig ros args res next))
    (hfind : RTL.find_function (Genv.globalenv prog) ros e = some fd)
    (hsig : RTL.funsig fd = sig)
    (henv : eagree e te (Deadcode.transfer cfg f (prog_defmap cu)
      (vanalyze cfg cu f) pc (PMap.get pc an)).1)
    (hmem : magree m tm (nlive (Genv.globalenv prog) sp
      (Deadcode.transfer cfg f (prog_defmap cu) (vanalyze cfg cu f) pc
        (PMap.get pc an)).2)) :
    (∃ target,
      RTL.step xi (Genv.globalenv tprog) (State ts tf (Vptr sp Ptrofs.zero) pc te tm)
        E0 target ∧
      match_states cfg prog
        (Callstate (Stackframe res f (Vptr sp Ptrofs.zero) next e :: s) fd
          (args.map (fun arg => Regmap.get arg e)) m) target) ∨
    (∃ target count,
      plus (RTL.step xi) (Genv.globalenv tprog)
        (State ts tf (Vptr sp Ptrofs.zero) pc te tm) E0 target ∧
      eventually prog xi count
        (Callstate (Stackframe res f (Vptr sp Ptrofs.zero) next e :: s) fd
          (args.map (fun arg => Regmap.get arg e)) m)
        (fun source => match_states cfg prog source target)) := by
  have htarget := transf_function_at cfg cu f tf an pc _ hfun han hcode
  generalize hanpc : PMap.get pc an = after at henv hmem
  obtain ⟨ne, nm⟩ := after
  simp only [Deadcode.transf_instr, hanpc] at htarget
  simp only [Deadcode.transfer, hcode] at henv hmem
  cases hknown : is_known_runtime_function (prog_defmap cu) ros with
  | none =>
      simp only [hknown] at htarget henv hmem
      have hargs := add_needs_all_lessdef args e te _ henv
      have hros := deadcode_add_needs_all_eagree args e te _ henv
      obtain ⟨cu', tfd, htfind, htfun, htlink⟩ :=
        find_function_translated cfg prog tprog hprog ros e fd te _ hfind hros
      have hbase : eagree e te (kill res ne) := by
        cases ros with
        | inl arg => exact add_need_all_eagree _ _ _ _ hros
        | inr symbol => exact hros
      refine Or.inl ⟨Callstate (Stackframe res tf (Vptr sp Ptrofs.zero) next te :: ts)
        tfd (args.map (fun arg => Regmap.get arg te)) tm, ?_, ?_⟩
      · exact RTL.exec_Icall _ _ _ _ _ _ _ _ _ _ _ _ htarget htfind
          ((sig_function_translated cfg _ _ _ _ htfun).trans hsig)
      · refine match_call_states _ _ _ _ _ _ _ _ cu' ?_ htlink htfun hargs ?_
        · constructor
          · apply match_stackframes_intro _ _ _ _ _ _ _ _ _ hlink hfun han
            intro value tvalue hvalue
            have hge := analyze_successors cfg cu f an pc _ next han hcode
              (by simp [RTL.successors_instr])
            rw [hanpc] at hge
            exact deadcode_eagree_ge _ _ _ _
              (eagree_update _ _ _ _ _ _ (vagree_lessdef _ _ _ hvalue) hbase) hge.1
          · exact hstacks
        · exact magree_extends _ _ _ (nlive_all _ sp) hmem
  | some bf =>
      obtain ⟨name, sg, rfl, hlookup⟩ :=
        is_known_runtime_function_sound cu prog ros bf e fd hknown hlink hfind
      simp only [hknown] at htarget henv hmem
      by_cases hdead : is_dead (nreg ne res) = true
      · simp only [hdead, ↓reduceIte] at htarget henv hmem
        refine Or.inr ⟨State ts tf (Vptr sp Ptrofs.zero) next te tm, 2, ?_, ?_⟩
        · exact plus_one _ _ _ _ _ _ _ (RTL.exec_Inop _ _ _ _ _ _ _ htarget)
        · apply deadcode_eventually_runtime prog xi s f sp next e m _ res hlookup
          intro value heval
          exact match_succ_states cfg prog s f sp pc _ m ts tf te tm an next cu
            (.Icall sig ros args res next) ne nm hlink hstacks hfun han hcode
            (by simp [RTL.successors_instr]) hanpc
            (eagree_update_dead _ _ _ _ _ (deadcode_dead hdead) henv) hmem
      · simp only [hdead, ↓reduceIte] at henv hmem
        have htcode : PTree.get pc tf.fn_code = some (.Icall sig ros args res next) := by
          simpa [hdead] using htarget
        have hargs := add_needs_all_lessdef args e te _ henv
        have hros := deadcode_add_needs_all_eagree args e te _ henv
        obtain ⟨cu', tfd, htfind, htfun, htlink⟩ :=
          find_function_translated cfg prog tprog hprog ros e _ te _ hfind hros
        have htfd : tfd = .External (.EF_runtime name sg) := by
          exact (Common.Errors.res.OK.inj htfun).symm
        subst tfd
        have htcall := RTL.exec_Icall (xi := xi) ts tf (Vptr sp Ptrofs.zero) pc te tm
          sig ros args res next (.External (.EF_runtime name sg)) htcode htfind hsig
        cases heval : builtin_function_sem bf (args.map (fun arg => Regmap.get arg e)) with
        | none =>
            refine Or.inr ⟨_, 2, plus_one _ _ _ _ _ _ _ htcall, ?_⟩
            apply deadcode_eventually_runtime prog xi s f sp next e m _ res hlookup
            intro value hvalue
            rw [heval] at hvalue
            contradiction
        | some value =>
            obtain ⟨tv, hteval, hv⟩ := builtin_function_sem_lessdef bf _ value _ heval hargs
            have hbase : eagree e te (kill res ne) := by
              cases ros with
              | inl arg => exact add_need_all_eagree _ _ _ _ hros
              | inr symbol => exact hros
            refine Or.inr ⟨State ts tf (Vptr sp Ptrofs.zero) next (Regmap.set res tv te) tm,
              2, ?_, ?_⟩
            · apply plus_three _ _ _ _ _ _ _ _ _ _ _ _ htcall
                (RTL.exec_function_external _ _ _ tv E0 _ _ ?_) (RTL.exec_return ..) rfl
              simp only [external_call, builtin_or_external_sem, hlookup]
              exact known_builtin_sem_intro _ _ _ hteval
            · apply deadcode_eventually_runtime prog xi s f sp next e m _ res hlookup
              intro result hresult
              rw [heval] at hresult
              cases hresult
              exact match_succ_states cfg prog s f sp pc _ m ts tf _ tm an next cu
                (.Icall sig ros args res next) ne nm hlink hstacks hfun han hcode
                (by simp [RTL.successors_instr]) hanpc
                (eagree_update _ _ _ _ _ _ (vagree_lessdef _ _ _ hv) hbase) hmem

set_option maxHeartbeats 2000000 in
private theorem deadcode_step_builtin
    (cfg : CompilerConfig) (prog tprog : program) (xi : ExternalCalls)
    (s ts : List stackframe) (f tf : function) (sp : block) (pc next : node)
    (e te : regset) (m tm result : mem) (cu : program) (an : PMap.t NA.t)
    (ef : external_function) (args : List (builtin_arg reg)) (res : builtin_res reg)
    (vargs : List val) (tr : trace) (value : val)
    (hprog : match_prog cfg prog tprog)
    (hstacks : list_forall2 (match_stackframes cfg prog) s ts)
    (hlink : linkorder cu prog)
    (hfun : Deadcode.transf_function cfg (prog_defmap cu) (romem_for cfg cu) f = .OK tf)
    (han : Deadcode.analyze cfg f (prog_defmap cu) (vanalyze cfg cu f) = some an)
    (hcode : PTree.get pc f.fn_code = some (.Ibuiltin ef args res next))
    (hargs : eval_builtin_args (Genv.to_senv (Genv.globalenv prog))
      (fun arg => Regmap.get arg e) (Vptr sp Ptrofs.zero) m args vargs)
    (hcall : external_call xi ef (Genv.to_senv (Genv.globalenv prog)) vargs m tr value result)
    (hsound : sound_state cfg prog (State s f (Vptr sp Ptrofs.zero) pc e m))
    (henv : eagree e te (Deadcode.transfer cfg f (prog_defmap cu)
      (vanalyze cfg cu f) pc (PMap.get pc an)).1)
    (hmem : magree m tm (nlive (Genv.globalenv prog) sp
      (Deadcode.transfer cfg f (prog_defmap cu) (vanalyze cfg cu f) pc
        (PMap.get pc an)).2)) :
    ∃ target,
      RTL.step xi (Genv.globalenv tprog) (State ts tf (Vptr sp Ptrofs.zero) pc te tm)
        tr target ∧
      match_states cfg prog
        (State s f (Vptr sp Ptrofs.zero) next (regmap_setres res value e) result) target := by
  have htarget := transf_function_at cfg cu f tf an pc _ hfun han hcode
  generalize hanpc : PMap.get pc an = after at henv hmem
  obtain ⟨ne, nm⟩ := after
  simp only [Deadcode.transfer, hcode] at henv hmem
  have hbase := sound_state_inv cfg prog _ cu hsound hlink
  cases hbase with
  | sound_regular_state _ _ _ _ _ _ ae am bc hstk happ hem hrom hmm hge hsp =>
    have hfinish : ∀ targetEnv targetMem,
        RTL.step xi (Genv.globalenv tprog) (State ts tf (Vptr sp Ptrofs.zero) pc te tm)
          tr (State ts tf (Vptr sp Ptrofs.zero) next targetEnv targetMem) →
        eagree (regmap_setres res value e) targetEnv ne →
        magree result targetMem (nlive (Genv.globalenv prog) sp nm) →
        ∃ target,
          RTL.step xi (Genv.globalenv tprog) (State ts tf (Vptr sp Ptrofs.zero) pc te tm)
            tr target ∧
          match_states cfg prog
            (State s f (Vptr sp Ptrofs.zero) next (regmap_setres res value e) result) target := by
      intro targetEnv targetMem hstep he hm
      refine ⟨_, hstep, ?_⟩
      exact match_succ_states cfg prog s f sp pc _ result ts tf _ targetMem an next cu
        (.Ibuiltin ef args res next) ne nm hlink hstacks hfun han hcode
        (by simp [RTL.successors_instr]) hanpc he hm
    have hkeep : ∀ tvargs tv tm',
        PTree.get pc tf.fn_code = some (.Ibuiltin ef args res next) →
        eval_builtin_args (Genv.to_senv (Genv.globalenv prog))
          (fun arg => Regmap.get arg te) (Vptr sp Ptrofs.zero) tm args tvargs →
        external_call xi ef (Genv.to_senv (Genv.globalenv prog)) tvargs tm tr tv tm' →
        eagree e te (kill_builtin_res res ne) → Val.lessdef value tv →
        magree result tm' (nlive (Genv.globalenv prog) sp nm) →
        ∃ target,
          RTL.step xi (Genv.globalenv tprog) (State ts tf (Vptr sp Ptrofs.zero) pc te tm)
            tr target ∧
          match_states cfg prog
            (State s f (Vptr sp Ptrofs.zero) next (regmap_setres res value e) result) target := by
      intro tvargs tv tm' htcode htargs htcall he hv hm
      apply hfinish (regmap_setres res tv te) tm'
      · apply RTL.exec_Ibuiltin _ _ _ _ _ _ ef args res next tvargs tr tv tm' htcode
        · exact eval_builtin_args_preserved _ _ _ _ _ (Genv.globalenv prog) (Genv.globalenv tprog)
            _ _ _ (symbols_preserved cfg prog tprog hprog) args tvargs htargs
        · exact deadcode_symbols xi ef _ _ _ _ _ _ _ (senv_preserved cfg prog tprog hprog) htcall
      · exact eagree_set_res _ _ _ _ _ _ hv he
      · exact hm
    have hother
        (htcode : PTree.get pc tf.fn_code = some (.Ibuiltin ef args res next))
        (he : eagree e te (transfer_builtin_args (kill_builtin_res res ne, nmem_all) args).1)
        (hm : magree m tm (nlive (Genv.globalenv prog) sp
          (transfer_builtin_args (kill_builtin_res res ne, nmem_all) args).2)) :
        ∃ target,
          RTL.step xi (Genv.globalenv tprog) (State ts tf (Vptr sp Ptrofs.zero) pc te tm)
            tr target ∧
          match_states cfg prog
            (State s f (Vptr sp Ptrofs.zero) next (regmap_setres res value e) result) target := by
      obtain ⟨tvargs, tv, tm', htargs, htcall, he', hm'⟩ :=
        transf_external_call cfg prog tprog hprog xi e sp m args vargs ef tr value result
          res ne nm _ _ bc te tm hargs hcall rfl he hm hge hsp
      apply hfinish _ _ (RTL.exec_Ibuiltin _ _ _ _ _ _ _ _ _ _ _ _ _ _ htcode htargs htcall) he' hm'
    cases ef with
    | EF_external name sig => exact hother htarget henv hmem
    | EF_runtime name sig => exact hother htarget henv hmem
    | EF_malloc => exact hother htarget henv hmem
    | EF_free => exact hother htarget henv hmem
    | EF_inline_asm text sig clobbers => exact hother htarget henv hmem
    | EF_vload chunk =>
        cases hcall with
        | volatile_load_sem_intro loc ofs _ _ _ hload =>
          cases hargs with
          | cons arg _ harg htail =>
            cases htail
            obtain ⟨tvptr, htarg, hvptr, he', hm'⟩ := transfer_builtin_arg_sound
              prog bc e te sp m tm arg (Vptr loc ofs) harg All
              (kill_builtin_res res ne)
              (nmem_add nm (aaddr_arg cfg (PMap.get pc (vanalyze cfg cu f)) arg) (size_chunk chunk))
              _ _ rfl henv hmem hge hsp
            cases hvptr
            have hptr := aaddr_arg_sound_1 cfg bc e ae m (romem_for cfg cu) am
              (Genv.globalenv prog) sp arg loc ofs hem hrom hmm hge hsp harg
            have hbytes : ∀ index,
                zLe (Ptrofs.unsigned ofs) index ∧
                  zLt index (zAdd (Ptrofs.unsigned ofs) (size_chunk chunk)) →
                nlive (Genv.globalenv prog) sp
                  (nmem_add nm (aaddr_arg cfg (PMap.get pc (vanalyze cfg cu f)) arg)
                    (size_chunk chunk)) loc index := by
              intro index hrange
              apply nlive_add _ _ bc loc ofs _ nm _ index hge hsp _ hrange
              simpa only [vanalyze, happ] using hptr
            have hloaded : ∃ tv,
                volatile_load (Genv.to_senv (Genv.globalenv prog)) chunk tm loc ofs tr tv ∧
                  Val.lessdef value tv := by
              cases hload with
              | volatile_load_vol symbol event loaded hvol hsymbol hevent =>
                  exact ⟨_, volatile_load_vol _ _ _ _ _ _ _ hvol hsymbol hevent, Val.lessdef_refl _⟩
              | volatile_load_nonvol loaded hvol hload =>
                  obtain ⟨tv, htload, hv⟩ := magree_load _ _ _ _ _ _ _ hm' hload hbytes
                  exact ⟨tv, volatile_load_nonvol _ _ _ _ _ hvol htload, hv⟩
            obtain ⟨tv, htload, hv⟩ := hloaded
            apply hkeep [Vptr loc ofs] tv tm htarget
              (list_forall2.cons _ _ htarg (list_forall2_nil _))
              (volatile_load_sem_intro _ _ _ _ _ htload) he' hv
            apply magree_monotone _ _ _ _ hm'
            exact fun loc index hlive => incl_nmem_add _ _ _ _ _ _ _ hlive
    | EF_vstore chunk =>
        cases hargs with
        | nil => cases hcall
        | cons arg1 value1 harg1 htail =>
          cases htail with
          | nil => cases hcall
          | cons arg2 value2 harg2 htail =>
            have hvalues := hcall
            cases hvalues
            cases htail
            obtain ⟨tvptr, htarg1, hvptr, he1, hm1⟩ := transfer_builtin_arg_sound
              prog bc e te sp m tm arg1 _ harg1 All
              (transfer_builtin_arg (store_argument chunk) (kill_builtin_res res ne, nm) arg2).1
              (transfer_builtin_arg (store_argument chunk) (kill_builtin_res res ne, nm) arg2).2
              _ _ rfl henv hmem hge hsp
            obtain ⟨tvvalue, htarg2, hvvalue, he2, hm2⟩ := transfer_builtin_arg_sound
              prog bc e te sp m tm arg2 value2 harg2 (store_argument chunk)
              (kill_builtin_res res ne) nm _ _ rfl he1 hm1 hge hsp
            obtain ⟨_, tm', htstore, hm'⟩ := transf_volatile_store prog _ _ _ _ _ _ chunk sp nm
              tr _ result hcall hvptr hvvalue hm2
            exact hkeep [tvptr, tvvalue] Vundef tm' htarget
              (list_forall2.cons _ _ htarg1
                (list_forall2.cons _ _ htarg2 (list_forall2_nil _)))
              htstore he2 (Val.lessdef_refl _) hm'
    | EF_memcpy size align =>
        cases hcall with
        | extcall_memcpy_sem_intro dstBlock dstOfs srcBlock srcOfs _ bytes _
            halign hsize hsizealign hsrcalign hdstalign hdisjoint hload hstore =>
          cases hargs with
          | cons dst _ hdst htail =>
            cases htail with
            | cons src _ hsrc htail =>
              cases htail
              let dstAddr := aaddr_arg cfg (PMap.get pc (vanalyze cfg cu f)) dst
              let srcAddr := aaddr_arg cfg (PMap.get pc (vanalyze cfg cu f)) src
              have hdstptr : pmatch bc dstBlock dstOfs dstAddr := by
                simpa only [dstAddr, vanalyze, happ] using
                  aaddr_arg_sound_1 cfg bc e ae m (romem_for cfg cu) am
                    (Genv.globalenv prog) sp dst dstBlock dstOfs hem hrom hmm hge hsp hdst
              have hsrcptr : pmatch bc srcBlock srcOfs srcAddr := by
                simpa only [srcAddr, vanalyze, happ] using
                  aaddr_arg_sound_1 cfg bc e ae m (romem_for cfg cu) am
                    (Genv.globalenv prog) sp src srcBlock srcOfs hem hrom hmm hge hsp hsrc
              have hlength : zOfNat bytes.length = size := by
                rw [Mem.loadbytes_length _ _ _ _ _ hload]
                exact ZArith.Znat.Z2Nat.id size hsize
              by_cases hcontains : nmem_contains nm dstAddr size = true
              · dsimp only [dstAddr] at hcontains
                have hbefore : Deadcode.transfer_builtin cfg (PMap.get pc (vanalyze cfg cu f))
                    (.EF_memcpy size align) [dst, src] res ne nm =
                    transfer_builtin_args
                      (kill_builtin_res res ne, nmem_add (nmem_remove nm dstAddr size) srcAddr size)
                      [dst, src] := by
                  change (if nmem_contains nm dstAddr size then
                    transfer_builtin_args
                      (kill_builtin_res res ne, nmem_add (nmem_remove nm dstAddr size) srcAddr size)
                      [dst, src] else (ne, nm)) = _
                  exact if_pos hcontains
                rw [hbefore] at henv hmem
                obtain ⟨tvargs, htargs, hvargs, he', hm'⟩ := transfer_builtin_args_sound
                  prog e sp m te tm bc [dst, src] [Vptr dstBlock dstOfs, Vptr srcBlock srcOfs]
                  (list_forall2.cons _ _ hdst (list_forall2.cons _ _ hsrc (list_forall2_nil _)))
                  (kill_builtin_res res ne)
                  (nmem_add (nmem_remove nm dstAddr size) srcAddr size) _ _ rfl henv hmem hge hsp
                obtain ⟨tv1, tv2, rfl, hv1, hv2⟩ := deadcode_lessdef_two hvargs
                cases hv1
                cases hv2
                obtain ⟨tbytes, htload, hbytes⟩ := magree_loadbytes m tm _ srcBlock
                  (Ptrofs.unsigned srcOfs) size bytes hm' hload
                  (fun index hrange => nlive_add _ _ bc srcBlock srcOfs srcAddr _ size index
                    hge hsp hsrcptr hrange)
                have hremoved : magree m tm (nlive (Genv.globalenv prog) sp (nmem_remove nm dstAddr size)) :=
                  magree_monotone _ _ _ _ hm'
                    (fun loc index hlive => incl_nmem_add _ _ _ _ _ _ _ hlive)
                obtain ⟨tm', htstore, hmresult⟩ := magree_storebytes_parallel m tm _
                  (nlive (Genv.globalenv prog) sp nm) dstBlock (Ptrofs.unsigned dstOfs)
                  bytes result tbytes hremoved hstore (by
                    intro loc index hlive hrange
                    rw [hlength] at hrange
                    exact nlive_remove _ _ bc dstBlock dstOfs dstAddr nm size loc index
                      hge hsp hdstptr hlive hrange) hbytes
                apply hkeep [Vptr dstBlock dstOfs, Vptr srcBlock srcOfs] Vundef tm' _ htargs
                  (extcall_memcpy_sem_intro _ _ _ _ _ _ _ halign hsize hsizealign
                    hsrcalign hdstalign hdisjoint htload htstore)
                  he' (Val.lessdef_refl _) hmresult
                simpa [Deadcode.transf_instr, hanpc, hcontains] using htarget
              · dsimp only [dstAddr] at hcontains
                have hbefore : Deadcode.transfer_builtin cfg (PMap.get pc (vanalyze cfg cu f))
                    (.EF_memcpy size align) [dst, src] res ne nm = (ne, nm) := by
                  change (if nmem_contains nm dstAddr size then
                    transfer_builtin_args
                      (kill_builtin_res res ne, nmem_add (nmem_remove nm dstAddr size) srcAddr size)
                      [dst, src] else (ne, nm)) = _
                  exact if_neg hcontains
                rw [hbefore] at henv hmem
                apply hfinish te tm
                · apply RTL.exec_Inop
                  simpa [Deadcode.transf_instr, hanpc, hcontains] using htarget
                · cases res with
                  | BR targetReg => exact eagree_set_undef _ _ _ _ henv
                  | _ => exact henv
                · apply magree_storebytes_left m tm _ dstBlock (Ptrofs.unsigned dstOfs) bytes result hmem hstore
                  intro index hrange
                  rw [hlength] at hrange
                  exact nlive_contains _ _ bc dstBlock dstOfs dstAddr nm size index
                    hge hsp hdstptr (Bool.eq_false_iff.mpr hcontains) hrange
    | EF_annot kind text types =>
        obtain ⟨tvargs, htargs, hvargs, he', hm'⟩ := transfer_builtin_args_sound
          prog e sp m te tm bc args vargs hargs (kill_builtin_res res ne) nm
          _ _ rfl henv hmem hge hsp
        cases hcall with
        | extcall_annot_sem_intro events hevents =>
            exact hkeep tvargs Vundef tm htarget htargs
              (extcall_annot_sem_intro _ _ _ (eventval_list_match_lessdef _ _ _ _ hevents _ hvargs))
              he' (Val.lessdef_refl _) hm'
    | EF_annot_val kind text typ =>
        obtain ⟨tvargs, htargs, hvargs, he', hm'⟩ := transfer_builtin_args_sound
          prog e sp m te tm bc args vargs hargs (kill_builtin_res res ne) nm
          _ _ rfl henv hmem hge hsp
        cases hcall with
        | extcall_annot_val_sem_intro _ _ event hevent =>
            obtain ⟨tv, rfl, hv⟩ := deadcode_lessdef_one hvargs
            exact hkeep [tv] tv tm htarget htargs
              (extcall_annot_val_sem_intro _ _ _ (eventval_match_lessdef _ _ _ _ _ hevent hv)) he' hv hm'
    | EF_debug kind symbol types =>
        cases hcall
        obtain ⟨tvargs, htargs⟩ := can_eval_builtin_args cfg prog tprog hprog sp e m te tm _ hmem args vargs hargs
        apply hfinish (regmap_setres res Vundef te) tm
          (RTL.exec_Ibuiltin _ _ _ _ _ _ _ _ _ _ _ _ _ _ htarget htargs (extcall_debug_sem_intro ..))
          (eagree_set_res _ _ _ _ _ _ (Val.lessdef_refl _) henv) hmem
    | EF_builtin name sig =>
        have htcode : PTree.get pc tf.fn_code = some
            (match lookup_builtin_function name sig, builtin_res_dead res ne with
            | some _, true => .Inop next
            | _, _ => .Ibuiltin (.EF_builtin name sig) args res next) := by
          have htarget' := htarget
          change PTree.get pc tf.fn_code = some
            (match lookup_builtin_function name sig, builtin_res_dead res (PMap.get pc an).1 with
            | some _, true => .Inop next
            | _, _ => .Ibuiltin (.EF_builtin name sig) args res next) at htarget'
          simpa only [hanpc] using htarget'
        change eagree e te
          ((match lookup_builtin_function name sig with
            | some _ => if builtin_res_dead res ne then (ne, nm)
              else transfer_builtin_args (kill_builtin_res res ne, nm) args
            | none => transfer_builtin_args (kill_builtin_res res ne, nmem_all) args) : NA.t).1 at henv
        change magree m tm (nlive (Genv.globalenv prog) sp
          ((match lookup_builtin_function name sig with
            | some _ => if builtin_res_dead res ne then (ne, nm)
              else transfer_builtin_args (kill_builtin_res res ne, nm) args
            | none => transfer_builtin_args (kill_builtin_res res ne, nmem_all) args) : NA.t).2) at hmem
        cases hlookup : lookup_builtin_function name sig with
        | none =>
            apply hother
            · simpa only [hlookup] using htcode
            · simpa only [hlookup] using henv
            · simpa only [hlookup] using hmem
        | some bf =>
            simp only [external_call, builtin_or_external_sem, hlookup] at hcall
            by_cases hdead : builtin_res_dead res ne = true
            · simp only [hlookup, hdead, ↓reduceIte] at henv hmem
              cases hcall with
              | known_builtin_sem_intro _ _ heval =>
                  apply hfinish te tm
                  · apply RTL.exec_Inop
                    simpa only [hlookup, hdead] using htcode
                  · cases res with
                    | BR targetReg => exact eagree_update_dead _ _ _ _ _ (deadcode_dead hdead) henv
                    | _ => exact henv
                  · exact hmem
            · simp only [hlookup, hdead, ↓reduceIte] at henv hmem
              obtain ⟨tvargs, htargs, hvargs, he', hm'⟩ := transfer_builtin_args_sound
                prog e sp m te tm bc args vargs hargs (kill_builtin_res res ne) nm
                _ _ rfl henv hmem hge hsp
              obtain ⟨tv, htcall, hv⟩ := known_builtin_sem_lessdef bf _ _ _ _ _ _ _ _ _ hcall hvargs
              cases hcall with
              | known_builtin_sem_intro _ _ heval =>
                  apply hkeep tvargs tv tm _ htargs _ he' hv hm'
                  · simpa only [hlookup, Bool.eq_false_iff.mpr hdead] using htcode
                  · simpa only [external_call, builtin_or_external_sem, hlookup] using htcall

set_option maxHeartbeats 2000000 in
theorem step_simulation : ∀ cfg, step_simulationStatement cfg := by
  intro cfg prog tprog hprog xi source tr result hstep target hmatch hsound
  cases hmatch with
  | match_regular_states s f sp pc e m ts tf te tm cu an
      hstacks hlink hfun han henv hmem =>
    cases hstep with
    | exec_Inop _ _ _ _ _ _ next hcode =>
        have htarget := transf_function_at cfg cu f tf an pc _ hfun han hcode
        simp only [Deadcode.transfer, hcode] at henv hmem
        refine Or.inl ⟨_, RTL.exec_Inop _ _ _ _ _ _ _ htarget, ?_⟩
        exact match_succ_states cfg prog s f sp pc e m ts tf te tm an next cu (.Inop next)
          _ _ hlink hstacks hfun han hcode (by simp [RTL.successors_instr]) rfl henv hmem
    | exec_Iop _ _ _ _ _ _ op args res next value hcode heval =>
        exact Or.inl (deadcode_step_op cfg prog tprog xi s ts f tf sp pc next e te m tm cu an
          op args res value hprog hstacks hlink hfun han hcode heval henv hmem)
    | exec_Iload _ _ _ _ _ _ chunk addr args dst next address value hcode haddr hload =>
        exact Or.inl (deadcode_step_load cfg prog tprog xi s ts f tf sp pc next e te m tm cu an
          chunk addr args dst address value hprog hstacks hlink hfun han hcode haddr hload hsound henv hmem)
    | exec_Istore _ _ _ _ _ _ chunk addr args src next address result hcode haddr hstore =>
        exact Or.inl (deadcode_step_store cfg prog tprog xi s ts f tf sp pc next e te m tm result cu an
          chunk addr args src address hprog hstacks hlink hfun han hcode haddr hstore hsound henv hmem)
    | exec_Icall _ _ _ _ _ _ sig ros args res next fd hcode hfind hsig =>
        exact deadcode_step_call cfg prog tprog xi s ts f tf sp pc next e te m tm cu an
          sig ros args res fd hprog hstacks hlink hfun han hcode hfind hsig henv hmem
    | exec_Itailcall _ _ _ _ _ _ sig ros args fd result hcode hfind hsig hfree =>
        have htarget := transf_function_at cfg cu f tf an pc _ hfun han hcode
        simp only [Deadcode.transfer, hcode] at henv hmem
        have hargs := add_needs_all_lessdef args e te _ henv
        have hros := deadcode_add_needs_all_eagree args e te _ henv
        obtain ⟨cu', tfd, htfind, htfun, htlink⟩ :=
          find_function_translated cfg prog tprog hprog ros e fd te _ hfind hros
        obtain ⟨tm', htfree, hm'⟩ := magree_free m tm _ (nlive (Genv.globalenv prog) sp nmem_all)
          sp .Z0 f.fn_stacksize result hmem hfree
          (fun loc index _ hrange => nlive_dead_stack _ _ _ _ _ hrange)
        refine Or.inl ⟨Callstate ts tfd (args.map (fun arg => Regmap.get arg te)) tm', ?_, ?_⟩
        · apply RTL.exec_Itailcall _ _ _ _ _ _ _ _ _ _ _ htarget htfind
            ((sig_function_translated cfg _ _ _ _ htfun).trans hsig)
          simpa only [stacksize_translated cfg _ _ _ _ hfun] using htfree
        · exact match_call_states _ _ _ _ _ _ _ _ cu' hstacks htlink htfun hargs
            (magree_extends _ _ _ (nlive_all _ sp) hm')
    | exec_Ibuiltin _ _ _ _ _ _ ef args res next vargs tr value result hcode hargs hcall =>
        exact Or.inl (deadcode_step_builtin cfg prog tprog xi s ts f tf sp pc next e te m tm result cu an
          ef args res vargs tr value hprog hstacks hlink hfun han hcode hargs hcall hsound henv hmem)
    | exec_Icond _ _ _ _ _ _ cond args ifso ifnot choice next hcode heval hnext =>
        have htarget := transf_function_at cfg cu f tf an pc _ hfun han hcode
        simp only [Deadcode.transfer, hcode] at henv hmem
        have hsucc : next ∈ RTL.successors_instr (.Icond cond args ifso ifnot) := by
          cases choice <;> simp_all [RTL.successors_instr]
        have hfinish := match_succ_states cfg prog s f sp pc e m ts tf te tm an next cu
          (.Icond cond args ifso ifnot) (PMap.get pc an).1 (PMap.get pc an).2
          hlink hstacks hfun han hcode hsucc rfl
        cases hpeq : peq ifso ifnot with
        | left heq =>
            simp only [hpeq] at henv hmem
            have hnext' : next = ifso := by simp [hnext, heq]
            refine Or.inl ⟨State ts tf (Vptr sp Ptrofs.zero) next te tm, ?_, hfinish henv hmem⟩
            rw [hnext']
            apply RTL.exec_Inop
            simpa only [Deadcode.transf_instr, hpeq] using htarget
        | right hne =>
            simp only [hpeq] at henv hmem
            refine Or.inl ⟨State ts tf (Vptr sp Ptrofs.zero) next te tm, ?_, ?_⟩
            · apply RTL.exec_Icond _ _ _ _ _ _ cond args ifso ifnot choice next
              · simpa only [Deadcode.transf_instr, hpeq] using htarget
              · exact needs_of_condition_sound m tm hmem.ma_perm cond _ choice _ heval
                  (add_needs_vagree args (needs_of_condition cond) e te _ henv)
              · exact hnext
            · exact hfinish (deadcode_add_needs_eagree args (needs_of_condition cond) e te _ henv) hmem
    | exec_Ijumptable _ _ _ _ _ _ arg table index next hcode harg hnth =>
        have htarget := transf_function_at cfg cu f tf an pc _ hfun han hcode
        simp only [Deadcode.transfer, hcode] at henv hmem
        have hvalue := add_need_all_lessdef e te arg _ henv
        rw [harg] at hvalue
        have htarg : Regmap.get arg te = Vint index := by
          generalize htv : Regmap.get arg te = tv at hvalue
          cases hvalue
          rfl
        refine Or.inl ⟨_, RTL.exec_Ijumptable _ _ _ _ _ _ _ _ _ _ htarget htarg hnth, ?_⟩
        exact match_succ_states cfg prog s f sp pc e m ts tf te tm an next cu
          (.Ijumptable arg table) _ _ hlink hstacks hfun han hcode
          (list_nth_z_in _ _ _ _ hnth) rfl (add_need_all_eagree _ _ _ _ henv) hmem
    | exec_Ireturn _ _ _ _ _ _ opt result hcode hfree =>
        have htarget := transf_function_at cfg cu f tf an pc _ hfun han hcode
        simp only [Deadcode.transfer, hcode] at henv hmem
        obtain ⟨tm', htfree, hm'⟩ := magree_free m tm _ (nlive (Genv.globalenv prog) sp nmem_all)
          sp .Z0 f.fn_stacksize result hmem hfree
          (fun loc index _ hrange => nlive_dead_stack _ _ _ _ _ hrange)
        refine Or.inl ⟨Returnstate ts (regmap_optget opt Vundef te) tm', ?_, ?_⟩
        · apply RTL.exec_Ireturn _ _ _ _ _ _ opt tm' htarget
          simpa only [stacksize_translated cfg _ _ _ _ hfun] using htfree
        · refine match_return_states _ _ _ _ _ _ hstacks ?_
            (magree_extends _ _ _ (nlive_all _ sp) hm')
          cases opt with
          | none => exact Val.lessdef_refl _
          | some arg => exact add_need_all_lessdef _ _ _ _ henv
  | match_call_states s fd args m ts tfd targs tm cu hstacks hlink hfun hargs hmem =>
    cases hstep with
    | exec_function_internal _ f _ _ result sp htypes halloc =>
        cases han : Deadcode.analyze cfg f (prog_defmap cu) (vanalyze cfg cu f) with
        | none =>
            simp [Deadcode.transf_fundef, transf_partial_fundef, Deadcode.transf_function,
              vanalyze] at han hfun
            rw [han] at hfun
            contradiction
        | some an =>
            have htf := hfun
            simp only [Deadcode.transf_fundef, transf_partial_fundef, Deadcode.transf_function] at htf
            have han' := han
            unfold vanalyze at han'
            rw [han'] at htf
            cases htf
            obtain ⟨tm', htalloc, hm'⟩ := deadcode_alloc_extends m tm .Z0 f.fn_stacksize result sp hmem halloc
            refine Or.inl ⟨_, RTL.exec_function_internal _ _ _ _ _ _
              (Val.has_argtype_list_lessdef _ _ _ htypes hargs) htalloc, ?_⟩
            apply match_regular_states _ _ _ _ _ _ _ _ _ _ cu an hstacks hlink
            · simp only [Deadcode.transf_function, han']
            · exact han
            · exact eagree_init_regs _ _ _ _ hargs
            · exact mextends_agree _ _ _ hm'
    | exec_function_external _ ef _ value tr resultMem result hcall =>
        have htfd : tfd = .External ef := (Common.Errors.res.OK.inj hfun).symm
        subst tfd
        obtain ⟨tv, tm', htcall, hv, hm'⟩ :=
          deadcode_call_extends xi ef _ args m tr value result tm targs hcall hmem hargs
        refine Or.inl ⟨_, RTL.exec_function_external _ _ _ _ _ _ _
          (deadcode_symbols xi ef _ _ _ _ _ _ _ (senv_preserved cfg prog tprog hprog) htcall), ?_⟩
        exact match_return_states _ _ _ _ _ _ hstacks hv hm'
  | match_return_states s value m ts tv tm hstacks hv hm =>
      cases hstep
      cases hstacks with
      | cons sourceFrame targetFrame hframe hframes =>
        cases hframe with
        | match_stackframes_intro res f sp next e tf te cu an hlink hfun han he =>
            refine Or.inl ⟨_, RTL.exec_return _ _ _ _ _ _ _ _, ?_⟩
            exact match_regular_states _ _ _ _ _ _ _ _ _ _ cu an hframes hlink hfun han
              (he _ _ hv) (mextends_agree _ _ _ hm)

end CompCert4Lean.Backend.Deadcodeproof

namespace CompCert4Lean.Backend.Deadcodeproof

open CompCert4Lean.Backend.ValueAnalysis CompCert4Lean.Common.Smallstep

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

theorem transf_program_correct : ∀ cfg, transf_program_correctStatement cfg := by
  intro cfg prog tprog xi hprog
  apply forward_simulation_eventually_plus (RTL.semantics xi prog) (RTL.semantics xi tprog)
    (fun source target => match_states cfg prog source target ∧ sound_state cfg prog source)
  · exact (senv_preserved cfg prog tprog hprog).2.1
  · intro source hinitial
    obtain ⟨target, htinitial, hmatch⟩ := transf_initial_states cfg prog tprog hprog source hinitial
    exact ⟨target, htinitial, hmatch, sound_initial cfg prog source hinitial⟩
  · intro source target result hmatch hfinal
    exact transf_final_states cfg prog source target result hmatch.1 hfinal
  · intro source tr result hstep target hmatch
    have hsound := sound_step cfg prog xi source tr result hstep hmatch.2
    rcases step_simulation cfg prog tprog hprog xi source tr result hstep target
        hmatch.1 hmatch.2 with hsingle | heventual
    · obtain ⟨target', htstep, hmatched⟩ := hsingle
      exact ⟨0, target', plus_one _ _ _ _ _ _ _ htstep,
        CompCert4Lean.Common.Smallstep.eventually.eventually_now _ _ ⟨hmatched, hsound⟩⟩
    · obtain ⟨target', count, htsteps, heventual⟩ := heventual
      refine ⟨count, target', htsteps, ?_⟩
      exact eventually_and_invariant _ _ _ _ _ (sound_state cfg prog) count result
        (fun source' => match_states cfg prog source' target')
        (sound_step cfg prog xi) heventual hsound

end CompCert4Lean.Backend.Deadcodeproof
