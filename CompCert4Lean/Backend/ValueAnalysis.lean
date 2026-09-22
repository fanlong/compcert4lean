import CompCert4Lean.Config
import CompCert4Lean.Backend.ValueDomain
import CompCert4Lean.Backend.Kildall
import CompCert4Lean.Backend.Liveness
import CompCert4Lean.Backend.RTL
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Builtins
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Values
import CompCert4Lean.Driver.Compopts
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Maps
import CompCert4Lean.X86.ValueAOp

/-!
# Value analysis

Definition-bearing translation of CompCert's `backend/ValueAnalysis.v`.
Proof declarations assigned to later migration are represented by exact
statement descriptors below; no theorem placeholders are introduced.
-/

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Kildall
open CompCert4Lean.Backend.Liveness
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private instance rtlFundefLinker :
    CompCert4Lean.Common.Linking.Linker CompCert4Lean.Backend.RTL.fundef :=
  CompCert4Lean.Common.Linking.Linker_fundef CompCert4Lean.Backend.RTL.function

private instance rtlProgramLinker :
    CompCert4Lean.Common.Linking.Linker CompCert4Lean.Backend.RTL.program :=
  CompCert4Lean.Common.Linking.Linker_prog
    CompCert4Lean.Backend.RTL.fundef Unit

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev int := CompCert4Lean.Lib.Integers.int
private abbrev int64 := CompCert4Lean.Lib.Integers.int64
private abbrev float := CompCert4Lean.Lib.Floats.float
private abbrev float32 := CompCert4Lean.Lib.Floats.float32
private abbrev ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev z0 : Z := .Z0
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zToNat := ZArith.BinInt.Z.to_nat

private abbrev val := CompCert4Lean.Common.Values.val
private abbrev memval := CompCert4Lean.Common.Memdata.memval
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev reg := CompCert4Lean.Backend.Registers.reg
private abbrev node := CompCert4Lean.Backend.RTL.node
private abbrev function := CompCert4Lean.Backend.RTL.function
private abbrev fundef := CompCert4Lean.Backend.RTL.fundef
private abbrev instruction := CompCert4Lean.Backend.RTL.instruction
private abbrev addressing := CompCert4Lean.X86.Op.addressing
private abbrev state := CompCert4Lean.Backend.RTL.state
private abbrev stackframe := CompCert4Lean.Backend.RTL.stackframe
private abbrev program := CompCert4Lean.Backend.RTL.program
private abbrev genv := CompCert4Lean.Backend.RTL.genv

private def boolOfSumbool {P Q : Prop} :
    CompCert4Lean.Foundation.Logic.Support.Sumbool P Q → Bool
  | .left _ => true
  | .right _ => false

private def boolEq {A : Type} [DecidableEq A] (x y : A) : Bool := decide (x = y)

/-! ## Dataflow lattice adapter (the source functor is not a public surface). -/

def va_lat (cfg : CompilerConfig) : SemiLattice :=
  { t := VA.t
    bot := VA.bot
    lub := VA.lub cfg
    beq := VA.beq
    eq := VA.eq
    ge := VA.ge }

def solver_law_obligation (cfg : CompilerConfig) : Prop :=
  SemiLatticeLaws (va_lat cfg) ∧ NodeSetForward.law_obligation

/-! Canonical generated surface for
`Kildall.Dataflow_Solver(VA)(NodeSetForward)`.  The accepted compiler
configuration adaptation is explicit on the specialized lattice. -/
namespace DS

def L (cfg : CompilerConfig) : SemiLattice := va_lat cfg

def law_obligation (cfg : CompilerConfig) : Prop :=
  SemiLatticeLaws (L cfg) ∧ NodeSetForward.law_obligation

abbrev state (cfg : CompilerConfig) : Type :=
  Dataflow_Solver.state (LAT := L cfg) (NS := NodeSetForward)

def aval (cfg : CompilerConfig) (s : state cfg) : PTree.t (L cfg).t := s.aval
def worklist (cfg : CompilerConfig) (s : state cfg) : NodeSetForward.t := s.worklist
def visited (cfg : CompilerConfig) (s : state cfg) : positive → Prop := s.visited

def abstr_value (cfg : CompilerConfig) (n : positive) (s : state cfg) : (L cfg).t :=
  Dataflow_Solver.abstr_value n s

def propagate_succ (cfg : CompilerConfig) (s : state cfg)
    (out : (L cfg).t) (n : positive) : state cfg :=
  Dataflow_Solver.propagate_succ s out n

def propagate_succ_list (cfg : CompilerConfig) (s : state cfg)
    (out : (L cfg).t) (nodes : List positive) : state cfg :=
  Dataflow_Solver.propagate_succ_list s out nodes

def step (cfg : CompilerConfig) {A : Type} (code : PTree.t A)
    (successors : A → List positive) (transf : positive → (L cfg).t → (L cfg).t)
    (s : state cfg) : Sum (PMap.t (L cfg).t) (state cfg) :=
  Dataflow_Solver.step code successors transf s

def fixpoint_from (cfg : CompilerConfig) {A : Type} (code : PTree.t A)
    (successors : A → List positive) (transf : positive → (L cfg).t → (L cfg).t)
    (start : state cfg) : Option (PMap.t (L cfg).t) :=
  Dataflow_Solver.fixpoint_from code successors transf start

def start_state (cfg : CompilerConfig) (enode : positive)
    (eval : (L cfg).t) : state cfg :=
  Dataflow_Solver.start_state (NS := NodeSetForward) enode eval

def fixpoint (cfg : CompilerConfig) {A : Type} (code : PTree.t A)
    (successors : A → List positive) (transf : positive → (L cfg).t → (L cfg).t)
    (enode : positive) (eval : (L cfg).t) : Option (PMap.t (L cfg).t) :=
  Dataflow_Solver.fixpoint (L cfg) NodeSetForward code successors transf enode eval

def start_state_nodeset (cfg : CompilerConfig) (enodes : NodeSetForward.t) : state cfg :=
  Dataflow_Solver.start_state_nodeset NodeSetForward enodes

def fixpoint_nodeset (cfg : CompilerConfig) {A : Type} (code : PTree.t A)
    (successors : A → List positive) (transf : positive → (L cfg).t → (L cfg).t)
    (enodes : NodeSetForward.t) : Option (PMap.t (L cfg).t) :=
  Dataflow_Solver.fixpoint_nodeset (L cfg) NodeSetForward code successors transf enodes

def start_state_allnodes (cfg : CompilerConfig) {A : Type}
    (code : PTree.t A) : state cfg :=
  Dataflow_Solver.start_state_allnodes NodeSetForward code

def fixpoint_allnodes (cfg : CompilerConfig) {A : Type} (code : PTree.t A)
    (successors : A → List positive) (transf : positive → (L cfg).t → (L cfg).t) :
    Option (PMap.t (L cfg).t) :=
  Dataflow_Solver.fixpoint_allnodes (L cfg) NodeSetForward code successors transf

abbrev optge (cfg : CompilerConfig) := Dataflow_Solver.optge (L cfg)
abbrev steps (cfg : CompilerConfig) {A : Type} (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → (L cfg).t → (L cfg).t) :=
  Dataflow_Solver.steps (LAT := L cfg) (NS := NodeSetForward)
    code successors transf
abbrev good_state (cfg : CompilerConfig) {A : Type} (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → (L cfg).t → (L cfg).t) (st : state cfg) :=
  Dataflow_Solver.good_state code successors transf st

def fixpoint_solution (_laws : law_obligation cfg) : Prop :=
  ∀ (A : Type) (code : PTree.t A) (successors : A → List positive)
    (transf : positive → (L cfg).t → (L cfg).t) (ep : positive)
    (ev : (L cfg).t) (res : PMap.t (L cfg).t) (n : positive)
    (instr : A) (s : positive),
    fixpoint cfg code successors transf ep ev = some res →
    PTree.get n code = some instr → s ∈ successors instr →
    (∀ n, (L cfg).eq (transf n (L cfg).bot) (L cfg).bot) →
    (L cfg).ge (PMap.get s res) (transf n (PMap.get n res))

def fixpoint_entry (_laws : law_obligation cfg) : Prop :=
  ∀ (A : Type) (code : PTree.t A) (successors : A → List positive)
    (transf : positive → (L cfg).t → (L cfg).t) (ep : positive)
    (ev : (L cfg).t) (res : PMap.t (L cfg).t),
    fixpoint cfg code successors transf ep ev = some res →
    (L cfg).ge (PMap.get ep res) ev

def fixpoint_allnodes_solution (_laws : law_obligation cfg) : Prop :=
  ∀ (A : Type) (code : PTree.t A) (successors : A → List positive)
    (transf : positive → (L cfg).t → (L cfg).t) (res : PMap.t (L cfg).t)
    (n : positive) (instr : A) (s : positive),
    fixpoint_allnodes cfg code successors transf = some res →
    PTree.get n code = some instr → s ∈ successors instr →
    (L cfg).ge (PMap.get s res) (transf n (PMap.get n res))

def fixpoint_nodeset_solution (_laws : law_obligation cfg) : Prop :=
  ∀ (A : Type) (code : PTree.t A) (successors : A → List positive)
    (transf : positive → (L cfg).t → (L cfg).t) (enodes : NodeSetForward.t)
    (res : PMap.t (L cfg).t) (e n : positive) (instr : A) (s : positive),
    fixpoint_nodeset cfg code successors transf enodes = some res →
    NodeSetForward.In e enodes → reachable code successors e n →
    PTree.get n code = some instr → s ∈ successors instr →
    (L cfg).ge (PMap.get s res) (transf n (PMap.get n res))

def fixpoint_invariant (_laws : law_obligation cfg) : Prop :=
  ∀ (A : Type) (code : PTree.t A) (successors : A → List positive)
    (transf : positive → (L cfg).t → (L cfg).t) (ep : positive)
    (ev : (L cfg).t) (P : (L cfg).t → Prop), P (L cfg).bot →
    (∀ x y, P x → P y → P ((L cfg).lub x y)) →
    (∀ pc instr x, PTree.get pc code = some instr → P x → P (transf pc x)) →
    P ev → ∀ res pc, fixpoint cfg code successors transf ep ev = some res →
    P (PMap.get pc res)

end DS

/-! ## Executable analysis definitions -/

def areg (ae : aenv) (r : reg) : aval := AE.get r ae

def aregs (ae : aenv) (rl : List reg) : List aval := rl.map (areg ae)

def mafter_public_call : amem := mtop

def mafter_private_call (am_before : amem) : amem :=
  { am_stack := am_before.am_stack
    am_glob := PTree.empty ablock
    am_nonstack := Nonstack
    am_top := plub (am_before.am_stack.ab_summary) Nonstack }

def analyze_call (am : amem) (aargs : List aval) : aval × amem :=
  if pincl am.am_nonstack Nonstack = true &&
      aargs.all (fun av => vpincl av Nonstack = true) then
    (Ifptr Nonstack, mafter_private_call am)
  else
    (Vtop, mafter_public_call)

def transfer_call (ae : aenv) (am : amem) (args : List reg) (res : reg) : VA.t :=
  let (av, am') := analyze_call am (aregs ae args)
  VA.State (AE.set res av ae) am'

def abuiltin_arg (cfg : CompilerConfig) (ae : aenv) (am : amem)
    (rm : romem) : builtin_arg reg → aval
  | .BA r => areg ae r
  | .BA_int n => I n
  | .BA_long n => L n
  | .BA_float n => F n
  | .BA_single n => FS n
  | .BA_loadstack chunk ofs => loadv cfg chunk rm am (Ptr (Stk ofs))
  | .BA_addrstack ofs => Ptr (Stk ofs)
  | .BA_loadglobal chunk id ofs => loadv cfg chunk rm am (Ptr (Gl id ofs))
  | .BA_addrglobal id ofs => Ptr (Gl id ofs)
  | .BA_splitlong hi lo =>
      longofwords (abuiltin_arg cfg ae am rm hi) (abuiltin_arg cfg ae am rm lo)
  | .BA_addptr ba1 ba2 =>
      let v1 := abuiltin_arg cfg ae am rm ba1
      let v2 := abuiltin_arg cfg ae am rm ba2
      if CompCert4Lean.X86_64.Archi.ptr64 then addl v1 v2 else add v1 v2

def set_builtin_res (br : builtin_res reg) (av : aval) (ae : aenv) : aenv :=
  match br with
  | .BR r => AE.set r av ae
  | _ => ae

def transfer_builtin_default (cfg : CompilerConfig) (ae : aenv) (am : amem) (rm : romem)
    (args : List (builtin_arg reg)) (res : builtin_res reg) : VA.t :=
  let (av, am') := analyze_call am (args.map (abuiltin_arg cfg ae am rm))
  VA.State (set_builtin_res res av ae) am'

def eval_static_builtin_function
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (ae : aenv) (am : amem) (rm : romem)
    (bf : builtin_function) (args : List (builtin_arg reg)) : Option aval :=
  match builtin_function_sem
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) bf
      (List.map val_of_aval (args.map (abuiltin_arg cfg ae am rm))) with
  | some v => aval_of_val v
  | none => none

def transfer_builtin
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (ae : aenv) (am : amem)
    (rm : romem) (ef : external_function)
    (args : List (builtin_arg reg)) (res : builtin_res reg) : VA.t :=
  match ef, args with
  | .EF_vload chunk, addr :: [] =>
      let aaddr := abuiltin_arg cfg ae am rm addr
      let a := if CompCert4Lean.Driver.Compopts.va_strict cfg
        then vlub cfg (loadv cfg chunk rm am aaddr)
          (vnormalize chunk (Ifptr Glob))
        else vnormalize chunk Vtop
      VA.State (set_builtin_res res a ae) am
  | .EF_vstore chunk, addr :: v :: [] =>
      let aaddr := abuiltin_arg cfg ae am rm addr
      let av := abuiltin_arg cfg ae am rm v
      let am' := storev cfg chunk am aaddr av
      VA.State (set_builtin_res res ntop ae) (mlub cfg am am')
  | .EF_memcpy sz al, dst :: src :: [] =>
      let adst := abuiltin_arg cfg ae am rm dst
      let asrc := abuiltin_arg cfg ae am rm src
      let p := loadbytes cfg am rm (aptr_of_aval cfg asrc)
      let am' := storebytes am (aptr_of_aval cfg adst) sz p
      VA.State (set_builtin_res res ntop ae) am'
  | .EF_annot _ _ _, _ =>
      VA.State (set_builtin_res res ntop ae) am
  | .EF_debug _ _ _, _ =>
      VA.State (set_builtin_res res ntop ae) am
  | .EF_annot_val _ _ _, v :: [] =>
      VA.State (set_builtin_res res (abuiltin_arg cfg ae am rm v) ae) am
  | .EF_builtin name sg, _ =>
      match lookup_builtin_function name sg with
      | some bf =>
          match eval_static_builtin_function
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate)
              cfg ae am rm bf args with
          | some av => VA.State (set_builtin_res res av ae) am
          | none => transfer_builtin_default cfg ae am rm args res
      | none => transfer_builtin_default cfg ae am rm args res
  | _, _ => transfer_builtin_default cfg ae am rm args res

def transfer
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (f : function) (rm : romem)
    (pc : node) (ae : aenv) (am : amem) : VA.t :=
  match PTree.get pc f.fn_code with
  | none => VA.Bot
  | some (.Inop _) => VA.State ae am
  | some (.Iop op args res _) =>
      VA.State (AE.set res (CompCert4Lean.X86.ValueAOp.eval_static_operation
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg op (aregs ae args)) ae) am
  | some (.Iload chunk addr args dst _) =>
      VA.State (AE.set dst (loadv cfg chunk rm am
        (CompCert4Lean.X86.ValueAOp.eval_static_addressing addr (aregs ae args))) ae) am
  | some (.Istore chunk addr args src _) =>
      VA.State ae (storev cfg chunk am
        (CompCert4Lean.X86.ValueAOp.eval_static_addressing addr (aregs ae args)) (areg ae src))
  | some (.Icall _ _ args res _) => transfer_call ae am args res
  | some (.Itailcall _ _ _) => VA.Bot
  | some (.Ibuiltin ef args res _) => transfer_builtin
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg ae am rm ef args res
  | some (.Icond _ _ _ _) => VA.State ae am
  | some (.Ijumptable _ _) => VA.State ae am
  | some (.Ireturn _) => VA.Bot

def transfer'
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (f : function)
    (lastuses : PTree.t (List reg)) (rm : romem)
    (pc : node) (before : VA.t) : VA.t :=
  match before with
  | .Bot => .Bot
  | .State ae am =>
      match transfer
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          cfg f rm pc ae am with
      | .Bot => .Bot
      | .State ae' am' =>
          let ae'' := match PTree.get pc lastuses with
            | none => ae'
            | some regs => eforget regs ae'
          VA.State ae'' am'

def mfunction_entry : amem :=
  { am_stack := ablock_init Pbot
    am_glob := PTree.empty ablock
    am_nonstack := Nonstack
    am_top := Nonstack }

def analyze
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (rm : romem) (f : function) : PMap.t VA.t :=
  let lu := Liveness.last_uses f
  let entry := VA.State (einit_regs f.fn_params f.fn_sig.sig_args) mfunction_entry
  match DS.fixpoint cfg f.fn_code
      successors_instr (fun pc before => transfer'
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg f lu rm pc before)
      f.fn_entrypoint entry with
  | none => PMap.init (VA.State AE.top mtop)
  | some res => res

def store_init_data (cfg : CompilerConfig) (ab : ablock) (p : Z) : init_data → ablock
  | .Init_int8 n => ablock_store .Mint8unsigned ab p (I n)
  | .Init_int16 n => ablock_store .Mint16unsigned ab p (I n)
  | .Init_int32 n => ablock_store .Mint32 ab p (I n)
  | .Init_int64 n => ablock_store .Mint64 ab p (L n)
  | .Init_float32 n => ablock_store .Mfloat32 ab p
      (if CompCert4Lean.Driver.Compopts.propagate_float_constants cfg then FS n else ntop)
  | .Init_float64 n => ablock_store .Mfloat64 ab p
      (if CompCert4Lean.Driver.Compopts.propagate_float_constants cfg then F n else ntop)
  | .Init_addrof symb ofs => ablock_store Mptr ab p (Ptr (Gl symb ofs))
  | .Init_space _ => ab

def store_init_data_list (cfg : CompilerConfig) (ab : ablock) (p : Z) :
    List init_data → ablock
  | [] => ab
  | id :: ids => store_init_data_list cfg (store_init_data cfg ab p id)
      (zAdd p (init_data_size id)) ids

def definitive_initializer : List init_data → Bool
  | [] => false
  | [.Init_space _] => false
  | _ => true

def alloc_global (cfg : CompilerConfig) (rm : romem)
    (idg : ident × globdef fundef Unit) : romem :=
  match idg with
  | (id, .Gfun _) => PTree.remove id rm
  | (id, .Gvar v) =>
      if v.gvar_readonly && !v.gvar_volatile && definitive_initializer v.gvar_init then
        PTree.set id (store_init_data_list cfg (ablock_init Pbot) z0 v.gvar_init) rm
      else PTree.remove id rm

def romem_for (cfg : CompilerConfig) (p : program) : romem :=
  p.prog_defs.foldl (fun rm idg => alloc_global cfg rm idg) (PTree.empty ablock)

def bc_nostack (bc : block_classification) : Prop := ∀ b, bc b ≠ BCstack

def initial_mem_match (cfg : CompilerConfig) (bc : block_classification)
    (m : mem) (g : genv) : Prop :=
  ∀ id b v,
    Genv.find_symbol g id = some b →
    Genv.find_var_info g b = some v →
    v.gvar_volatile = false → v.gvar_readonly = true →
    bmatch bc m b (store_init_data_list cfg (ablock_init Pbot) z0 v.gvar_init)

def romem_consistent (cfg : CompilerConfig)
    (defmap : PTree.t (globdef fundef Unit)) (rm : romem) : Prop :=
  ∀ id ab, PTree.get id rm = some ab →
    ∃ v,
      PTree.get id defmap = some (.Gvar v) ∧
      v.gvar_readonly = true ∧ v.gvar_volatile = false ∧
      definitive_initializer v.gvar_init = true ∧
      ab = store_init_data_list cfg (ablock_init Pbot) z0 v.gvar_init

/-! ## Generated invariant carriers and constructors -/

inductive sound_stack
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig)
    (prog : CompCert4Lean.Backend.RTL.program)
    (ge : CompCert4Lean.Backend.RTL.genv) :
    block_classification → List stackframe → mem → block → Prop where
  | sound_stack_nil (bc : block_classification) (m : mem) (bound : block) :
      sound_stack cfg prog ge bc [] m bound
  | sound_stack_public_call
      (bc : block_classification) (res : reg) (f : function) (sp : block)
      (pc : node) (e : regset) (stk : List stackframe) (m : mem) (bound : block)
      (bc' : block_classification) (bound' : block) (ae : aenv)
      (STK : sound_stack cfg prog ge bc' stk m sp)
      (INCR : Ple bound' bound)
      (BELOW : bc_below bc' bound')
      (SP : bc sp = BCother)
      (SP' : bc' sp = BCstack)
      (SAME : ∀ b, Plt b bound' → b ≠ sp → bc b = bc' b)
      (GE : genv_match bc' ge)
      (AN : VA.ge (PMap.get pc (analyze
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg (romem_for cfg prog) f))
        (VA.State (AE.set res Vtop ae) mafter_public_call))
      (EM : ematch bc' e ae) :
      sound_stack cfg prog ge bc
        (Stackframe res f (Vptr sp Ptrofs.zero) pc e :: stk) m bound
  | sound_stack_private_call
      (bc : block_classification) (res : reg) (f : function) (sp : block)
      (pc : node) (e : regset) (stk : List stackframe) (m : mem) (bound : block)
      (bc' : block_classification) (bound' : block) (ae : aenv) (am : amem)
      (STK : sound_stack cfg prog ge bc' stk m sp)
      (INCR : Ple bound' bound)
      (BELOW : bc_below bc' bound')
      (SP : bc sp = BCinvalid)
      (SP' : bc' sp = BCstack)
      (SAME : ∀ b, Plt b bound' → b ≠ sp → bc b = bc' b)
      (GE : genv_match bc' ge)
      (AN : VA.ge (PMap.get pc (analyze
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg (romem_for cfg prog) f))
        (VA.State (AE.set res (Ifptr Nonstack) ae) (mafter_private_call am)))
      (EM : ematch bc' e ae)
      (CONTENTS : bmatch bc' m sp am.am_stack) :
      sound_stack cfg prog ge bc
        (Stackframe res f (Vptr sp Ptrofs.zero) pc e :: stk) m bound

export sound_stack (sound_stack_nil sound_stack_public_call sound_stack_private_call)

inductive sound_state_base
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig)
    (prog : CompCert4Lean.Backend.RTL.program)
    (ge : CompCert4Lean.Backend.RTL.genv) : state → Prop where
  | sound_regular_state
      (s : List stackframe) (f : function) (sp : block) (pc : node)
      (e : regset) (m : mem) (ae : aenv) (am : amem) (bc : block_classification)
      (STK : sound_stack cfg prog ge bc s m sp)
      (AN : PMap.get pc (analyze
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg (romem_for cfg prog) f) = VA.State ae am)
      (EM : ematch bc e ae)
      (RO : romatch bc m (romem_for cfg prog))
      (MM : mmatch bc m am)
      (GE : genv_match bc ge)
      (SP : bc sp = BCstack) :
      sound_state_base cfg prog ge (State s f (Vptr sp Ptrofs.zero) pc e m)
  | sound_call_state
      (s : List stackframe) (fd : fundef) (args : List val) (m : mem)
      (bc : block_classification)
      (STK : sound_stack cfg prog ge bc s m m.nextblock)
      (ARGS : ∀ v, v ∈ args → vmatch bc v Vtop)
      (RO : romatch bc m (romem_for cfg prog))
      (MM : mmatch bc m mtop)
      (GE : genv_match bc ge)
      (NOSTK : bc_nostack bc) :
      sound_state_base cfg prog ge (Callstate s fd args m)
  | sound_return_state
      (s : List stackframe) (v : val) (m : mem) (bc : block_classification)
      (STK : sound_stack cfg prog ge bc s m m.nextblock)
      (RES : vmatch bc v Vtop)
      (RO : romatch bc m (romem_for cfg prog))
      (MM : mmatch bc m mtop)
      (GE : genv_match bc ge)
      (NOSTK : bc_nostack bc) :
      sound_state_base cfg prog ge (Returnstate s v m)

export sound_state_base (sound_regular_state sound_call_state sound_return_state)

inductive sound_state
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig)
    (prog : CompCert4Lean.Backend.RTL.program) : state → Prop where
  | sound_state_intro (st : state)
      (H : ∀ cunit, linkorder cunit prog →
        sound_state_base cfg cunit (Genv.globalenv prog) st) :
      sound_state cfg prog st

export sound_state (sound_state_intro)

def avalue (a : VA.t) (r : reg) : aval :=
  match a with
  | .Bot => Vbot
  | .State ae _ => AE.get r ae

def aaddressing (cfg : CompilerConfig) (a : VA.t)
    (addr : CompCert4Lean.X86.Op.addressing) (args : List reg) : aptr :=
  match a with
  | .Bot => Pbot
  | .State ae _ => aptr_of_aval cfg
      (CompCert4Lean.X86.ValueAOp.eval_static_addressing addr (aregs ae args))

def aaddr_arg (cfg : CompilerConfig) (a : VA.t) (ba : builtin_arg reg) : aptr :=
  match a with
  | .Bot => Pbot
  | .State ae _ =>
      match ba with
      | .BA r => aptr_of_aval cfg (AE.get r ae)
      | .BA_addrstack ofs => Stk ofs
      | .BA_addrglobal id ofs => Gl id ofs
      | _ => Ptop

/-! ## Later-proof statement descriptors -/

def analyze_entrypointStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (rm : romem) (f : function) (vl : List val) (m : mem)
    (bc : block_classification),
    (∀ v, v ∈ vl → vmatch bc v (Ifptr Nonstack)) →
    Val.has_argtype_list vl f.fn_sig.sig_args →
    mmatch bc m mfunction_entry →
    ∃ ae am,
      PMap.get f.fn_entrypoint (analyze
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg rm f) = VA.State ae am ∧
      ematch bc (init_regs vl f.fn_params) ae ∧ mmatch bc m am

def analyze_successorStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (f : function) (n : node)
    (ae : aenv) (am : amem) (instr : instruction)
    (s : node) (rm : romem) (ae' : aenv) (am' : amem),
    PMap.get n (analyze
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg rm f) = VA.State ae am →
    PTree.get n f.fn_code = some instr →
    s ∈ successors_instr instr →
    transfer
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg f rm n ae am = VA.State ae' am' →
    VA.ge (PMap.get s (analyze
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg rm f))
      (transfer
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg f rm n ae am)

def analyze_succStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (e : regset) (m : mem) (rm : romem)
    (f : function) (n : node)
    (ae : aenv) (am : amem) (instr : instruction) (s : node)
    (ae' : aenv) (am' : amem) (bc : block_classification),
    PMap.get n (analyze
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg rm f) = VA.State ae am →
    PTree.get n f.fn_code = some instr →
    s ∈ successors_instr instr →
    transfer
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg f rm n ae am = VA.State ae' am' →
    ematch bc e ae' → mmatch bc m am' →
    ∃ ae'' am'',
      PMap.get s (analyze
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg rm f) = VA.State ae'' am'' ∧
      ematch bc e ae'' ∧ mmatch bc m am''

def areg_soundStatement : Prop :=
  ∀ bc e ae r, ematch bc e ae → vmatch bc (Regmap.get r e) (areg ae r)

def aregs_soundStatement : Prop :=
  ∀ bc e ae rl, ematch bc e ae →
    list_forall2 (vmatch bc) (rl.map (fun r => Regmap.get r e)) (aregs ae rl)

def abuiltin_arg_soundStatement : Prop :=
  ∀ (cfg : CompilerConfig) (bc : block_classification) (ge : genv)
    (rs : regset) (sp : block)
    (m : mem) (ae : aenv) (rm : romem) (am : amem),
    ematch bc rs ae →
    romatch bc m rm →
    mmatch bc m am →
    genv_match bc ge →
    bc sp = BCstack →
    ∀ (a : builtin_arg reg) (v : val),
      eval_builtin_arg (Genv.to_senv ge) (fun r => Regmap.get r rs)
        (Vptr sp Ptrofs.zero) m a v →
      vmatch bc v (abuiltin_arg cfg ae am rm a)

def abuiltin_args_soundStatement : Prop :=
  ∀ (cfg : CompilerConfig) (bc : block_classification) (ge : genv)
    (rs : regset) (sp : block)
    (m : mem) (ae : aenv) (rm : romem) (am : amem),
    ematch bc rs ae →
    romatch bc m rm →
    mmatch bc m am →
    genv_match bc ge →
    bc sp = BCstack →
    ∀ (al : List (builtin_arg reg)) (vl : List val),
      eval_builtin_args (Genv.to_senv ge) (fun r => Regmap.get r rs)
        (Vptr sp Ptrofs.zero) m al vl →
      list_forall2 (vmatch bc) vl (al.map (abuiltin_arg cfg ae am rm))
def set_builtin_res_soundStatement : Prop :=
  ∀ bc rs ae v av res, ematch bc rs ae → vmatch bc v av →
    ematch bc (regmap_setres res v rs) (set_builtin_res res av ae)
def eval_static_builtin_function_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (bc : block_classification) (ge : genv)
    (rs : regset) (sp : block)
    (m : mem) (ae : aenv) (rm : romem) (am : amem)
    (bf : builtin_function) (al : List (builtin_arg reg)) (vl : List val)
    (v : val) (va : aval),
    ematch bc rs ae →
    romatch bc m rm →
    mmatch bc m am →
    genv_match bc ge →
    bc sp = BCstack →
    eval_builtin_args (Genv.to_senv ge) (fun r => Regmap.get r rs)
      (Vptr sp Ptrofs.zero) m al vl →
    eval_static_builtin_function
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg ae am rm bf al = some va →
    builtin_function_sem
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) bf vl = some v →
    vmatch bc v va

def pmatch_no_stackStatement : Prop :=
  ∀ (bc : block_classification), bc_nostack bc →
    ∀ b ofs p, pmatch bc b ofs p → pmatch bc b ofs Nonstack
def vmatch_no_stackStatement : Prop :=
  ∀ (bc : block_classification), bc_nostack bc →
    ∀ v x, vmatch bc v x → vmatch bc v (Ifptr Nonstack)
def smatch_no_stackStatement : Prop :=
  ∀ (bc : block_classification), bc_nostack bc →
    ∀ m b p, smatch bc m b p → smatch bc m b Nonstack

def allocate_stackStatement : Prop :=
  ∀ (m : mem) (sz : Z) (m' : mem) (sp : block) (bc : block_classification)
    (ge : genv) (rm : romem) (am : amem),
    Mem.alloc m z0 sz = (m', sp) →
    genv_match bc ge →
    romatch bc m rm →
    mmatch bc m am →
    bc_nostack bc →
    ∃ bc',
      bc_incr bc bc' ∧
      bc' sp = BCstack ∧
      genv_match bc' ge ∧
      romatch bc' m' rm ∧
      mmatch bc' m' mfunction_entry ∧
      (∀ b, Plt b sp → bc' b = bc b) ∧
      (∀ v x, vmatch bc v x → vmatch bc' v (Ifptr Nonstack))

def anonymize_stackStatement : Prop :=
  ∀ (m : mem) (sp : block) (bc : block_classification) (ge : genv)
    (rm : romem) (am : amem),
    genv_match bc ge →
    romatch bc m rm →
    mmatch bc m am →
    bc sp = BCstack →
    ∃ bc',
      bc_nostack bc' ∧
      bc' sp = BCother ∧
      (∀ b, b ≠ sp → bc' b = bc b) ∧
      (∀ v x, vmatch bc v x → vmatch bc' v Vtop) ∧
      genv_match bc' ge ∧
      romatch bc' m rm ∧
      mmatch bc' m mtop

def hide_stackStatement : Prop :=
  ∀ (m : mem) (sp : block) (bc : block_classification) (ge : genv)
    (rm : romem) (am : amem),
    genv_match bc ge →
    romatch bc m rm →
    mmatch bc m am →
    bc sp = BCstack →
    pge Nonstack am.am_nonstack →
    ∃ bc',
      bc_nostack bc' ∧
      bc' sp = BCinvalid ∧
      (∀ b, b ≠ sp → bc' b = bc b) ∧
      (∀ v x, vge (Ifptr Nonstack) x → vmatch bc v x → vmatch bc' v Vtop) ∧
      genv_match bc' ge ∧
      romatch bc' m rm ∧
      mmatch bc' m mtop

def return_from_public_callStatement : Prop :=
  ∀ (caller callee : block_classification) (bound sp : block) (ge : genv)
    (e : regset) (ae : aenv) (v : val) (m : mem) (rm : romem),
    bc_below caller bound →
    callee sp = BCother →
    caller sp = BCstack →
    (∀ b, Plt b bound → b ≠ sp → caller b = callee b) →
    genv_match caller ge →
    ematch caller e ae →
    Ple bound m.nextblock →
    vmatch callee v Vtop →
    romatch callee m rm →
    mmatch callee m mtop →
    genv_match callee ge →
    bc_nostack callee →
    ∃ bc,
      vmatch bc v Vtop ∧
      ematch bc e ae ∧
      romatch bc m rm ∧
      mmatch bc m mafter_public_call ∧
      genv_match bc ge ∧
      bc sp = BCstack ∧
      (∀ b, Plt b sp → bc b = caller b)

def return_from_private_callStatement : Prop :=
  ∀ (caller callee : block_classification) (bound sp : block) (ge : genv)
    (e : regset) (ae : aenv) (v : val) (m : mem) (rm : romem) (am : amem),
    bc_below caller bound →
    callee sp = BCinvalid →
    caller sp = BCstack →
    (∀ b, Plt b bound → b ≠ sp → caller b = callee b) →
    genv_match caller ge →
    ematch caller e ae →
    bmatch caller m sp am.am_stack →
    Ple bound m.nextblock →
    vmatch callee v Vtop →
    romatch callee m rm →
    mmatch callee m mtop →
    genv_match callee ge →
    bc_nostack callee →
    ∃ bc,
      vmatch bc v (Ifptr Nonstack) ∧
      ematch bc e ae ∧
      romatch bc m rm ∧
      mmatch bc m (mafter_private_call am) ∧
      genv_match bc ge ∧
      bc sp = BCstack ∧
      (∀ b, Plt b sp → bc b = caller b)

def external_call_matchStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (ef : external_function) (ge : genv) (vargs : List val) (m : mem)
    (t : trace) (vres : val) (m' : mem) (bc : block_classification)
    (rm : romem) (am : amem),
    external_call
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi ef (Genv.to_senv ge) vargs m t vres m' →
    genv_match bc ge →
    (∀ v, v ∈ vargs → vmatch bc v Vtop) →
    romatch bc m rm →
    mmatch bc m am →
    bc_nostack bc →
    ∃ bc',
      bc_incr bc bc' ∧
      (∀ b, Plt b m.nextblock → bc' b = bc b) ∧
      vmatch bc' vres Vtop ∧
      genv_match bc' ge ∧
      romatch bc' m' rm ∧
      mmatch bc' m' mtop ∧
      bc_nostack bc' ∧
      (∀ b ofs n, Mem.valid_block m b → bc b = BCinvalid →
        Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n)

def sound_stack_extStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) (ge : genv) (m' : mem) (bc : block_classification)
    (stk : List stackframe) (m : mem) (bound : block),
    sound_stack cfg prog ge bc stk m bound →
    (∀ b ofs n bytes, Plt b bound → bc b = BCinvalid → zLe z0 n →
      Mem.loadbytes m' b ofs n = some bytes →
      Mem.loadbytes m b ofs n = some bytes) →
    sound_stack cfg prog ge bc stk m' bound

def sound_stack_invStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) (ge : genv) (m' : mem) (bc : block_classification)
    (stk : List stackframe) (m : mem) (bound : block),
    sound_stack cfg prog ge bc stk m bound →
    (∀ b ofs n, Plt b bound → bc b = BCinvalid → zLe z0 n →
      Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n) →
    sound_stack cfg prog ge bc stk m' bound

def sound_stack_storevStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) (ge : genv) (chunk : memory_chunk)
    (m : mem) (addr v : val)
    (m' : mem) (bc : block_classification) (aaddr : aval)
    (stk : List stackframe) (bound : block),
    Mem.storev chunk m addr v = some m' →
    vmatch bc addr aaddr →
    sound_stack cfg prog ge bc stk m bound →
    sound_stack cfg prog ge bc stk m' bound

def sound_stack_storebytesStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) (ge : genv) (m : mem) (b : block)
    (ofs : ptrofs)
    (bytes : List memval) (m' : mem) (bc : block_classification)
    (aaddr : aval) (stk : List stackframe) (bound : block),
    Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = some m' →
    vmatch bc (Vptr b ofs) aaddr →
    sound_stack cfg prog ge bc stk m bound →
    sound_stack cfg prog ge bc stk m' bound

def sound_stack_freeStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) (ge : genv) (m : mem) (b : block)
    (lo hi : Z) (m' : mem)
    (bc : block_classification) (stk : List stackframe) (bound : block),
    Mem.free m b lo hi = some m' →
    sound_stack cfg prog ge bc stk m bound →
    sound_stack cfg prog ge bc stk m' bound

def sound_stack_new_boundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) (ge : genv) (bc : block_classification)
    (stk : List stackframe)
    (m : mem) (bound bound' : block),
    sound_stack cfg prog ge bc stk m bound →
    Ple bound bound' →
    sound_stack cfg prog ge bc stk m bound'

def sound_stack_extenStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) (ge : genv) (bc : block_classification)
    (stk : List stackframe)
    (m : mem) (bound : block) (bc1 : block_classification),
    sound_stack cfg prog ge bc stk m bound →
    (∀ b, Plt b bound → bc1 b = bc b) →
    sound_stack cfg prog ge bc1 stk m bound

def sound_succ_stateStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) (ge : genv)
    (bc : block_classification) (pc : node)
    (ae : aenv) (am : amem) (instr : instruction) (ae' : aenv) (am' : amem)
    (s : List stackframe) (f : function) (sp : block) (pc' : node) (e' : regset)
    (m' : mem),
    PMap.get pc (analyze
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg (romem_for cfg prog) f) = VA.State ae am →
    PTree.get pc f.fn_code = some instr →
    pc' ∈ successors_instr instr →
    transfer
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg f (romem_for cfg prog) pc ae am = VA.State ae' am' →
    ematch bc e' ae' →
    mmatch bc m' am' →
    romatch bc m' (romem_for cfg prog) →
    genv_match bc ge →
    bc sp = BCstack →
    sound_stack cfg prog ge bc s m' sp →
    sound_state_base cfg prog ge (State s f (Vptr sp Ptrofs.zero) pc' e' m')

def sound_step_baseStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (ge : genv) (st : state) (t : trace) (st' : state),
    RTL.step
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge st t st' →
    sound_state_base cfg prog ge st →
    sound_state_base cfg prog ge st'

def sound_stepStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (st : state) (t : trace) (st' : state),
    RTL.step
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) st t st' →
    sound_state cfg prog st →
    sound_state cfg prog st'

def sound_state_invStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) (st : state) (cunit : program),
    sound_state cfg prog st →
    linkorder cunit prog →
    sound_state_base cfg cunit (Genv.globalenv prog) st

def initial_block_classificationStatement : Prop :=
  ∀ (prog : program) (m : mem),
    Genv.init_mem prog = some m →
    ∃ bc,
      genv_match bc (Genv.globalenv prog) ∧
      bc_below bc m.nextblock ∧
      bc_nostack bc ∧
      (∀ b id, bc b = BCglob id →
        Genv.find_symbol (Genv.globalenv prog) id = some b) ∧
      (∀ b, Mem.valid_block m b → bc b ≠ BCinvalid)
def store_init_data_summaryStatement : Prop :=
  ∀ (cfg : CompilerConfig) (ab : ablock) (p : Z) (id : init_data),
    pge Glob ab.ab_summary →
    pge Glob (store_init_data cfg ab p id).ab_summary
def store_init_data_list_summaryStatement : Prop :=
  ∀ (cfg : CompilerConfig) (idl : List init_data) (ab : ablock) (p : Z),
    pge Glob ab.ab_summary →
    pge Glob (store_init_data_list cfg ab p idl).ab_summary
def store_init_data_soundStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) (bc : block_classification)
    (m : mem) (b : block)
    (p : Z) (id : init_data) (m' : mem) (ab : ablock),
    genv_match bc (Genv.globalenv prog) →
    Genv.store_init_data (Genv.globalenv prog) m b p id = some m' →
    bmatch bc m b ab →
    bmatch bc m' b (store_init_data cfg ab p id)

def store_init_data_list_soundStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) (bc : block_classification)
    (idl : List init_data)
    (m : mem) (b : block) (p : Z) (m' : mem) (ab : ablock),
    genv_match bc (Genv.globalenv prog) →
    Genv.store_init_data_list (Genv.globalenv prog) m b p idl = some m' →
    bmatch bc m b ab →
    bmatch bc m' b (store_init_data_list cfg ab p idl)

def store_init_data_otherStatement : Prop :=
  ∀ (prog : program) (bc : block_classification) (m : mem) (b : block)
    (p : Z) (id : init_data) (m' : mem) (ab : ablock) (b' : block),
    Genv.store_init_data (Genv.globalenv prog) m b p id = some m' →
    b' ≠ b →
    bmatch bc m b' ab →
    bmatch bc m' b' ab

def store_init_data_list_otherStatement : Prop :=
  ∀ (prog : program) (bc : block_classification) (b b' : block)
    (ab : ablock) (idl : List init_data) (m : mem) (p : Z) (m' : mem),
    Genv.store_init_data_list (Genv.globalenv prog) m b p idl = some m' →
    b' ≠ b →
    bmatch bc m b' ab →
    bmatch bc m' b' ab
def store_zeros_sameStatement : Prop :=
  ∀ (bc : block_classification) (p : aptr) (m : mem) (b : block)
    (pos n : Z) (m' : mem),
    store_zeros m b pos n = some m' →
    smatch bc m b p →
    smatch bc m' b p

def store_zeros_otherStatement : Prop :=
  ∀ (bc : block_classification) (b' : block) (ab : ablock)
    (m : mem) (b : block) (p n : Z) (m' : mem),
    store_zeros m b p n = some m' →
    b' ≠ b →
    bmatch bc m b' ab →
    bmatch bc m' b' ab
def initial_mem_matchesStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) (m : mem),
    Genv.init_mem prog = some m →
    ∃ bc,
      genv_match bc (Genv.globalenv prog) ∧
      bc_below bc m.nextblock ∧
      bc_nostack bc ∧
      (∀ cunit, linkorder cunit prog → romatch bc m (romem_for cfg cunit)) ∧
      (∀ b, Mem.valid_block m b → bc b ≠ BCinvalid)

def alloc_global_matchStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) (bc : block_classification),
    genv_match bc (Genv.globalenv prog) →
    ∀ (m : mem) (g : genv) (idg : ident × globdef fundef Unit) (m' : mem),
      g.genv_next = m.nextblock →
      initial_mem_match cfg bc m g →
      Genv.alloc_global (Genv.globalenv prog) m idg = some m' →
      initial_mem_match cfg bc m' (Genv.add_global g idg)

def alloc_globals_matchStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) (bc : block_classification),
    genv_match bc (Genv.globalenv prog) →
    ∀ (gl : List (ident × globdef fundef Unit)) (m : mem) (g : genv) (m' : mem),
      g.genv_next = m.nextblock →
      initial_mem_match cfg bc m g →
      Genv.alloc_globals (Genv.globalenv prog) m gl = some m' →
      initial_mem_match cfg bc m' (Genv.add_globals g gl)
def romem_for_consistentStatement : Prop :=
  ∀ (cfg : CompilerConfig) (cunit : program),
    romem_consistent cfg (prog_defmap cunit) (romem_for cfg cunit)
def romem_for_consistent_2Statement : Prop :=
  ∀ (cfg : CompilerConfig) (prog cunit : program),
    linkorder cunit prog →
    romem_consistent cfg (prog_defmap prog) (romem_for cfg cunit)
def alloc_global_consistentStatement : Prop :=
  ∀ (cfg : CompilerConfig) (dm : PTree.t (globdef fundef Unit)) (rm : romem)
    (idg : ident × globdef fundef Unit),
    romem_consistent cfg dm rm →
    romem_consistent cfg (PTree.set idg.1 idg.2 dm) (alloc_global cfg rm idg)

def sound_initialStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) (st : state),
    RTL.initial_state prog st →
    sound_state cfg prog st

def aaddressing_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (cunit prog : program) (s : List stackframe) (f : function)
    (sp : block) (pc : node) (e : regset) (m : mem)
    (addr : addressing) (args : List reg) (b : block) (ofs : ptrofs),
    sound_state cfg prog (State s f (Vptr sp Ptrofs.zero) pc e m) →
    linkorder cunit prog →
    CompCert4Lean.X86.Op.eval_addressing (Genv.globalenv prog) (Vptr sp Ptrofs.zero) addr
      (args.map (fun r => Regmap.get r e)) = some (Vptr b ofs) →
    ∃ bc,
      pmatch bc b ofs
        (aaddressing cfg (PMap.get pc (analyze
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          cfg (romem_for cfg cunit) f)) addr args) ∧
      genv_match bc (Genv.globalenv prog) ∧
      bc sp = BCstack

def aaddr_arg_sound_1Statement : Prop :=
  ∀ (cfg : CompilerConfig) (bc : block_classification) (rs : regset)
    (ae : aenv) (m : mem)
    (rm : romem) (am : amem) (ge : genv) (sp : block)
    (a : builtin_arg reg) (b : block) (ofs : ptrofs),
    ematch bc rs ae →
    romatch bc m rm →
    mmatch bc m am →
    genv_match bc ge →
    bc sp = BCstack →
    eval_builtin_arg (Genv.to_senv ge) (fun r => Regmap.get r rs)
      (Vptr sp Ptrofs.zero) m a (Vptr b ofs) →
    pmatch bc b ofs (aaddr_arg cfg (VA.State ae am) a)

def aaddr_arg_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (cunit prog : program) (s : List stackframe) (f : function)
    (sp : block) (pc : node) (e : regset) (m : mem)
    (a : builtin_arg reg) (b : block) (ofs : ptrofs),
    sound_state cfg prog (State s f (Vptr sp Ptrofs.zero) pc e m) →
    linkorder cunit prog →
    eval_builtin_arg (Genv.to_senv (Genv.globalenv prog))
      (fun r => Regmap.get r e) (Vptr sp Ptrofs.zero) m a (Vptr b ofs) →
    ∃ bc,
      pmatch bc b ofs
        (aaddr_arg cfg (PMap.get pc (analyze
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          cfg (romem_for cfg cunit) f)) a) ∧
      genv_match bc (Genv.globalenv prog) ∧
      bc sp = BCstack

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

theorem areg_sound : areg_soundStatement := by
  intro bc e ae r h
  exact h r

theorem aregs_sound : aregs_soundStatement := by
  intro bc e ae rl h
  induction rl with
  | nil => exact .nil _
  | cons r rl ih =>
      exact .cons _ _ (h r) ih

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem value_analysis_set_result_ae_get_self
    (p : positive) (v : aval) (x : AE.t)
    (hx : x ≠ AE.Bot) (hv : v ≠ Vbot) :
    AE.get p (AE.set p v x) = v := by
  cases x with
  | Bot => exact False.elim (hx rfl)
  | Top_except t =>
      by_cases htop : v = Vtop
      · subst v
        have hvtop : ¬ Vtop = Vbot := by intro h; cases h
        simp only [AE.set, AE.get, if_neg hvtop, if_true]
        change (PTree.get p (PTree.remove p t)).getD Vtop = Vtop
        have h := PTree.grs_proof p t
        simp [h]
      · simp only [AE.set, AE.get, if_neg hv, if_neg htop]
        change (PTree.get p (PTree.set p v t)).getD Vtop = v
        have h := PTree.gsspec_proof (A := aval) p p v t
        simp [CompCert4Lean.Lib.Coqlib.peq, PArith.BinPos.Pos.eq_dec] at h
        rw [h]
        simp

theorem set_builtin_res_sound : set_builtin_res_soundStatement := by
  intro bc rs ae v av res hEm hVm
  change CompCert4Lean.Backend.Registers.Regmap.t
    CompCert4Lean.Common.Values.val at rs
  cases res with
  | BR r =>
      change positive at r
      intro r'
      change positive at r'
      by_cases hr : r' = r
      · subst r'
        have hrg : Regmap.get r (Regmap.set r v rs) = v :=
          Regmap.gss_proof _ _ _ _
        have hav : av ≠ Vbot := by
          intro h
          subst av
          cases hVm
        have hae : AE.get r (AE.set r av ae) = av := by
          cases ae with
          | Bot =>
              have h : vmatch bc (Regmap.get r rs) Vbot := by
                simpa [AE.get] using hEm r
              generalize hx : Regmap.get r rs = vv at h
              cases vv <;> cases h
          | Top_except t =>
              by_cases hvb : av = Vbot
              · subst av; cases hVm
              · by_cases hvt : av = Vtop
                · subst av
                  have hvtop : ¬ Vtop = Vbot := by intro h; cases h
                  simp only [AE.set, AE.get, if_neg hvtop, if_true]
                  change (PTree.get r (PTree.remove r t)).getD Vtop = Vtop
                  have h := PTree.grs_proof r t
                  rw [h]
                  simp
                · simp only [AE.set, AE.get, if_neg hvb, if_neg hvt]
                  change (PTree.get r (PTree.set r av t)).getD Vtop = av
                  have h := PTree.gsspec_proof (A := aval) r r av t
                  simp [CompCert4Lean.Lib.Coqlib.peq, PArith.BinPos.Pos.eq_dec] at h
                  rw [h]
                  simp
        change vmatch bc (Regmap.get r (Regmap.set r v rs))
          (AE.get r (AE.set r av ae))
        rw [hrg, hae]
        exact hVm
      · have hs := hEm r'
        have hrg : Regmap.get r' (Regmap.set r v rs) = Regmap.get r' rs := by
          apply Regmap.gso_proof
          exact hr
        have hae : AE.get r' (AE.set r av ae) = AE.get r' ae := by
          cases ae with
          | Bot => rfl
          | Top_except t =>
              by_cases hvb : av = Vbot
              · subst av; cases hVm
              · by_cases hvt : av = Vtop
                · subst av
                  have hvtop : ¬ Vtop = Vbot := by intro h; cases h
                  simp only [AE.set, AE.get, if_neg hvtop, if_true]
                  change (PTree.get r' (PTree.remove r t)).getD Vtop =
                    (PTree.get r' t).getD Vtop
                  have h := PTree.gro_proof (m := t) (by exact hr)
                  rw [h]
                · simp only [AE.set, AE.get, if_neg hvb, if_neg hvt]
                  change (PTree.get r' (PTree.set r av t)).getD Vtop =
                    (PTree.get r' t).getD Vtop
                  have h := PTree.gsspec_proof (A := aval) r' r av t
                  simp [CompCert4Lean.Lib.Coqlib.peq, PArith.BinPos.Pos.eq_dec, hr] at h
                  rw [h]
        change vmatch bc (Regmap.get r' (Regmap.set r v rs))
          (AE.get r' (AE.set r av ae))
        rw [hrg, hae]
        exact hs
  | BR_none => exact hEm
  | BR_splitlong hi lo => exact hEm
end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

theorem pmatch_no_stack : pmatch_no_stackStatement := by
  intro bc hnostack b ofs p hpm
  cases hpm with
  | gl id hbc =>
      apply CompCert4Lean.Backend.ValueDomain.pmatch.nonstack
      · exact hnostack b
      · intro hi
        have h' : CompCert4Lean.Backend.ValueDomain.BCglob id = CompCert4Lean.Backend.ValueDomain.BCinvalid := by simpa [hbc] using hi
        cases h'
  | glo id hbc =>
      apply CompCert4Lean.Backend.ValueDomain.pmatch.nonstack
      · exact hnostack b
      · intro hi
        have h' : CompCert4Lean.Backend.ValueDomain.BCglob id = CompCert4Lean.Backend.ValueDomain.BCinvalid := by simpa [hbc] using hi
        cases h'
  | glob id hbc =>
      apply CompCert4Lean.Backend.ValueDomain.pmatch.nonstack
      · exact hnostack b
      · intro hi
        have h' : CompCert4Lean.Backend.ValueDomain.BCglob id = CompCert4Lean.Backend.ValueDomain.BCinvalid := by simpa [hbc] using hi
        cases h'
  | stk hbc => exact False.elim (hnostack b hbc)
  | stack hbc => exact False.elim (hnostack b hbc)
  | nonstack hns hni => exact CompCert4Lean.Backend.ValueDomain.pmatch.nonstack hns hni
  | top hni =>
      apply CompCert4Lean.Backend.ValueDomain.pmatch.nonstack
      · exact hnostack b
      · exact hni

theorem vmatch_no_stack : vmatch_no_stackStatement := by
  intro bc hnostack v x hvm
  apply CompCert4Lean.Backend.ValueDomain.vmatch_ifptr bc v
    CompCert4Lean.Backend.ValueDomain.Nonstack
  intro b ofs hv
  subst v
  cases hvm with
  | ptr b ofs p hpm => exact pmatch_no_stack bc hnostack b ofs p hpm
  | ifptrPtr b ofs p hpm => exact pmatch_no_stack bc hnostack b ofs p hpm

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

theorem smatch_no_stack : smatch_no_stackStatement := by
  intro bc hnostack m b p hsm
  rcases hsm with ⟨hload, hbytes⟩
  constructor
  · intro chunk ofs v h
    exact vmatch_no_stack bc hnostack v _ (hload chunk ofs v h)
  · intro ofs b' ofs' q i h
    exact pmatch_no_stack bc hnostack b' ofs' p (hbytes ofs b' ofs' q i h)

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Maps

private theorem anonymize_genv_match_exten
    (ge : genv) (bc1 bc2 : block_classification)
    (hge : genv_match bc1 ge)
    (hglob : ∀ b id, bc1 b = BCglob id ↔ bc2 b = BCglob id)
    (hother : ∀ b, bc1 b = BCother → bc2 b = BCother) :
    genv_match bc2 ge := by
  rcases hge with ⟨hsym, hbelow⟩
  constructor
  · intro id b
    rw [← hglob b id]
    exact hsym id b
  · intro b hb
    have h := hbelow b hb
    constructor
    · intro hi
      cases hbc : bc1 b with
      | BCinvalid => exact False.elim (h.1 (by simpa [hbc]))
      | BCglob id =>
          have hg' : bc2 b = BCglob id := (hglob b id).1 hbc
          exact False.elim (by simpa [hg'] using hi)
      | BCstack => exact False.elim (h.2 (by simpa [hbc]))
      | BCother =>
          have ho := hother b hbc
          exact False.elim (by simpa [ho] using hi)
    · intro hs
      cases hbc : bc1 b with
      | BCinvalid => exact False.elim (h.1 (by simpa [hbc]))
      | BCglob id =>
          have hg' : bc2 b = BCglob id := (hglob b id).1 hbc
          exact False.elim (by simpa [hg'] using hs)
      | BCstack => exact False.elim (h.2 (by simpa [hbc]))
      | BCother =>
          have ho := hother b hbc
          exact False.elim (by simpa [ho] using hs)

private theorem anonymize_romatch_exten
    (bc1 bc2 : block_classification) (m : mem) (rm : romem)
    (hrom : romatch bc1 m rm)
    (hglob : ∀ b id, bc2 b = BCglob id ↔ bc1 b = BCglob id) :
    romatch bc2 m rm := by
  intro b id ab hbc2 hget
  have hbc1 : bc1 b = BCglob id := (hglob b id).1 hbc2
  rcases hrom b id ab hbc1 hget with ⟨hpg, hbm, hperm⟩
  have hPM : ∀ b' ofs p,
      pmatch bc1 b' ofs p → pmatch bc1 b' ofs ab.ab_summary →
        pmatch bc2 b' ofs p := by
    intro b' ofs p hp hsum
    have hglobp : pmatch bc1 b' ofs Glob :=
      CompCert4Lean.Backend.ValueDomain.pmatch_ge bc1 b' ofs Glob
        ab.ab_summary hpg hsum
    cases hp with
    | gl id' hbc1' =>
        exact pmatch.gl id' ((hglob b' id').2 hbc1')
    | glo id' hbc1' =>
        exact pmatch.glo id' ((hglob b' id').2 hbc1')
    | glob id' hbc1' =>
        exact pmatch.glob id' ((hglob b' id').2 hbc1')
    | stk hbc1' =>
        cases hglobp with
        | glob id'' hbc1'' =>
            exact False.elim (by simpa [hbc1'] using hbc1'')
    | stack hbc1' =>
        cases hglobp with
        | glob id'' hbc1'' =>
            exact False.elim (by simpa [hbc1'] using hbc1'')
    | nonstack hns hni =>
        cases hglobp with
        | glob id'' hbc1'' =>
            have hbc2' : bc2 b' = BCglob id'' := (hglob b' id'').2 hbc1''
            exact pmatch.nonstack (by simpa [hbc2']) (by simpa [hbc2'])
    | top hni =>
        cases hglobp with
        | glob id'' hbc1'' =>
            have hbc2' : bc2 b' = BCglob id'' := (hglob b' id'').2 hbc1''
            exact pmatch.top (by simpa [hbc2'])
  have hVM : ∀ v x,
      vmatch bc1 v x → vmatch bc1 v (Ifptr ab.ab_summary) →
        vmatch bc2 v x := by
    intro v x hv hsum
    cases hv with
    | vmatch_i i => exact vmatch.vmatch_i i
    | vmatch_iu i => exact vmatch.vmatch_iu i
    | iuUndef i => exact vmatch.iuUndef i
    | uns p i n hz hi => exact vmatch.uns p i n hz hi
    | vmatch_Uns_undef p n => exact vmatch.vmatch_Uns_undef p n
    | sgn p i n hz hi => exact vmatch.sgn p i n hz hi
    | sgnUndef p n => exact vmatch.sgnUndef p n
    | long i => exact vmatch.long i
    | float f => exact vmatch.float f
    | single f => exact vmatch.single f
    | numUndef p => exact vmatch.numUndef p
    | numInt i p => exact vmatch.numInt i p
    | numLong i p => exact vmatch.numLong i p
    | numFloat f p => exact vmatch.numFloat f p
    | numSingle f p => exact vmatch.numSingle f p
    | ptr b' ofs p hp =>
        cases hsum with
        | ifptrPtr _ _ q hq =>
            exact vmatch.ptr b' ofs p (hPM b' ofs p hp hq)
    | ptrUndef p => exact vmatch.ptrUndef p
    | ifptrUndef p => exact vmatch.ifptrUndef p
    | ifptrInt i p => exact vmatch.ifptrInt i p
    | ifptrLong i p => exact vmatch.ifptrLong i p
    | ifptrFloat f p => exact vmatch.ifptrFloat f p
    | ifptrSingle f p => exact vmatch.ifptrSingle f p
    | ifptrPtr b' ofs p hp =>
        cases hsum with
        | ifptrPtr _ _ q hq =>
            exact vmatch.ifptrPtr b' ofs p (hPM b' ofs p hp hq)
  refine ⟨hpg, ?_, hperm⟩
  rcases hbm with ⟨hsm, hload⟩
  refine ⟨?_, ?_⟩
  · rcases hsm with ⟨hsmLoad, hsmBytes⟩
    refine ⟨?_, ?_⟩
    · intro chunk ofs v h
      exact hVM v _ (hsmLoad chunk ofs v h) (hsmLoad chunk ofs v h)
    · intro ofs b' ofs' q i h
      exact hPM b' ofs' ab.ab_summary
        (hsmBytes ofs b' ofs' q i h) (hsmBytes ofs b' ofs' q i h)
  · intro chunk ofs v h
    exact hVM v _ (hload chunk ofs v h) (hsm.1 chunk ofs v h)

private theorem anonymize_smatch_top
    (bc bc' : block_classification) (m : mem)
    (hVM : ∀ v x, vmatch bc v x → vmatch bc' v Vtop)
    (hPM : ∀ b ofs p, pmatch bc b ofs p → pmatch bc' b ofs Ptop) :
    ∀ b p, smatch bc m b p → smatch bc' m b Ptop := by
  intro b p hsm
  rcases hsm with ⟨hload, hbytes⟩
  constructor
  · intro chunk ofs v h
    exact hVM v _ (hload chunk ofs v h)
  · intro ofs b' ofs' q i h
    exact hPM b' ofs' p (hbytes ofs b' ofs' q i h)

theorem anonymize_stack : anonymize_stackStatement := by
  intro m sp bc ge rm am hgenv hrom hmm hsp
  let f : block → block_class := fun b => if b = sp then BCother else bc b
  have hstack : ∀ b1 b2, f b1 = BCstack → f b2 = BCstack → b1 = b2 := by
    intro b1 b2 h1 h2
    by_cases hb1 : b1 = sp
    · subst b1; simp [f] at h1
    · by_cases hb2 : b2 = sp
      · subst b2; simp [f] at h2
      · have h1' : bc b1 = BCstack := by simpa [f, hb1] using h1
        have h2' : bc b2 = BCstack := by simpa [f, hb2] using h2
        exact bc.bc_stack b1 b2 h1' h2'
  have hglobuniq : ∀ b1 b2 id, f b1 = BCglob id → f b2 = BCglob id → b1 = b2 := by
    intro b1 b2 id h1 h2
    have h1' : bc b1 = BCglob id := by
      by_cases hb : b1 = sp
      · subst b1; simp [f] at h1
      · simpa [f, hb] using h1
    have h2' : bc b2 = BCglob id := by
      by_cases hb : b2 = sp
      · subst b2; simp [f] at h2
      · simpa [f, hb] using h2
    exact bc.bc_glob b1 b2 id h1' h2'
  let bc' : block_classification :=
    { bc_img := f, bc_stack := hstack, bc_glob := hglobuniq }
  have hPM : ∀ b ofs p, pmatch bc b ofs p → pmatch bc' b ofs Ptop := by
    intro b ofs p hp
    apply CompCert4Lean.Backend.ValueDomain.pmatch.top
    by_cases hb : b = sp
    · subst b; simp [bc', f]
    · have hni : bc b ≠ BCinvalid := by
        cases hp with
        | gl _ h => intro hi; rw [h] at hi; cases hi
        | glo _ h => intro hi; rw [h] at hi; cases hi
        | glob _ h => intro hi; rw [h] at hi; cases hi
        | stk h => intro hi; rw [h] at hi; cases hi
        | stack h => intro hi; rw [h] at hi; cases hi
        | nonstack _ h => exact h
        | top h => exact h
      simpa [bc', f, hb] using hni
  have hVM : ∀ v x, vmatch bc v x → vmatch bc' v Vtop := by
    intro v x hv
    apply CompCert4Lean.Backend.ValueDomain.vmatch_ifptr bc' v
    intro b ofs hptr
    subst v
    cases hv with
    | ptr _ _ _ hp => exact hPM _ _ _ hp
    | ifptrPtr _ _ _ hp => exact hPM _ _ _ hp
  have hSM : ∀ b p, smatch bc m b p → smatch bc' m b Ptop :=
    anonymize_smatch_top bc bc' m hVM hPM
  have hglob_eq : ∀ b id, bc b = BCglob id ↔ bc' b = BCglob id := by
    intro b id
    by_cases hb : b = sp
    · subst b; simp [bc', f, hsp]
    · simp [bc', f, hb]
  have hglob_eq_rev : ∀ b id, bc' b = BCglob id ↔ bc b = BCglob id := by
    intro b id; exact Iff.symm (hglob_eq b id)
  have hgenv' : genv_match bc' ge :=
    anonymize_genv_match_exten ge bc bc' hgenv hglob_eq
      (by
        intro b hb
        by_cases h : b = sp
        · subst b; rw [hsp] at hb; cases hb
        · simp [bc', f, h, hb])
  have hrom' : romatch bc' m rm :=
    anonymize_romatch_exten bc bc' m rm hrom hglob_eq_rev
  have hnostack' : bc_nostack bc' := by
    intro b hb
    by_cases h : b = sp
    · subst b; simp [bc', f] at hb
    · by_cases hs : bc b = BCstack
      · have heq : b = sp := bc.bc_stack b sp hs hsp
        exact False.elim (h heq)
      · have hbc : bc b = bc' b := by simpa [bc', f, h]
        apply hs
        exact hbc.symm ▸ hb
  have hsp' : bc' sp = BCother := by simp [bc', f]
  have hsame : ∀ b, b ≠ sp → bc' b = bc b := by
    intro b hb; simp [bc', f, hb]
  have hmm' : mmatch bc' m mtop := by
    constructor
    · intro b hb
      exact False.elim (hnostack' b hb)
    · intro id ab b hb hget
      change positive at id
      change PTree.get id (PTree.empty ablock) = some ab at hget
      have hempty : PTree.get id (PTree.empty ablock) = none :=
        PTree.gempty ablock id
      rw [hempty] at hget
      cases hget
    · intro b hbStack hbInvalid
      have hni : bc b ≠ BCinvalid := by
        by_cases h : b = sp
        · subst b; simp [hsp]
        · intro hi; apply hbInvalid; simpa [bc', f, h] using hi
      exact hSM b am.am_top (hmm.mmatch_top b hni)
    · intro b hbInvalid
      have hni : bc b ≠ BCinvalid := by
        by_cases h : b = sp
        · subst b; simp [hsp]
        · intro hi; apply hbInvalid; simpa [bc', f, h] using hi
      exact hSM b am.am_top (hmm.mmatch_top b hni)
    · intro b hbInvalid
      have hni : bc b ≠ BCinvalid := by
        by_cases h : b = sp
        · subst b; simp [hsp]
        · intro hi; apply hbInvalid; simpa [bc', f, h] using hi
      exact hmm.mmatch_below b hni
  exact ⟨bc', hnostack', hsp', hsame, hVM, hgenv', hrom', hmm'⟩

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Maps

theorem hide_stack : hide_stackStatement := by
  intro m sp bc ge rm am hgenv hrom hmm hsp hnoleak
  let f : block → block_class := fun b => if b = sp then BCinvalid else bc b
  have hstack : ∀ b1 b2, f b1 = BCstack → f b2 = BCstack → b1 = b2 := by
    intro b1 b2 h1 h2
    by_cases hb1 : b1 = sp
    · subst b1; simp [f] at h1
    · by_cases hb2 : b2 = sp
      · subst b2; simp [f] at h2
      · have h1' : bc b1 = BCstack := by simpa [f, hb1] using h1
        have h2' : bc b2 = BCstack := by simpa [f, hb2] using h2
        exact bc.bc_stack b1 b2 h1' h2'
  have hglobuniq : ∀ b1 b2 id, f b1 = BCglob id → f b2 = BCglob id → b1 = b2 := by
    intro b1 b2 id h1 h2
    have h1' : bc b1 = BCglob id := by
      by_cases hb : b1 = sp
      · subst b1; simp [f] at h1
      · simpa [f, hb] using h1
    have h2' : bc b2 = BCglob id := by
      by_cases hb : b2 = sp
      · subst b2; simp [f] at h2
      · simpa [f, hb] using h2
    exact bc.bc_glob b1 b2 id h1' h2'
  let bc' : block_classification :=
    { bc_img := f, bc_stack := hstack, bc_glob := hglobuniq }
  have hPM : ∀ b ofs p,
      pge Nonstack p → pmatch bc b ofs p → pmatch bc' b ofs Ptop := by
    intro b ofs p hge hp
    have hpns : pmatch bc b ofs Nonstack :=
      CompCert4Lean.Backend.ValueDomain.pmatch_ge bc b ofs Nonstack p hge hp
    cases hpns with
    | nonstack hns hni =>
        apply CompCert4Lean.Backend.ValueDomain.pmatch.top
        by_cases hb : b = sp
        · subst b
          exact False.elim (hns hsp)
        · intro hi
          apply hni
          simpa [bc', f, hb] using hi
  have hVM : ∀ v x,
      vge (Ifptr Nonstack) x → vmatch bc v x → vmatch bc' v Vtop := by
    intro v x hge hvm
    apply CompCert4Lean.Backend.ValueDomain.vmatch_ifptr bc' v Ptop
    intro b ofs hptr
    subst v
    cases hge <;> cases hvm
    all_goals first | exact hPM _ _ _ (by assumption) (by assumption) | contradiction
  have hSM : ∀ b p,
      pge Nonstack p → smatch bc m b p → smatch bc' m b Ptop := by
    intro b p hge hsm
    rcases hsm with ⟨hload, hbytes⟩
    constructor
    · intro chunk ofs v h
      exact hVM v (Ifptr p) (.ifptrIfptr Nonstack p hge) (hload chunk ofs v h)
    · intro ofs b' ofs' q i h
      exact hPM b' ofs' p hge (hbytes ofs b' ofs' q i h)
  have hglob_eq : ∀ b id, bc b = BCglob id ↔ bc' b = BCglob id := by
    intro b id
    by_cases hb : b = sp
    · subst b; simp [bc', f, hsp]
    · simp [bc', f, hb]
  have hglob_eq_rev : ∀ b id, bc' b = BCglob id ↔ bc b = BCglob id := by
    intro b id; exact Iff.symm (hglob_eq b id)
  have hgenv' : genv_match bc' ge :=
    anonymize_genv_match_exten ge bc bc' hgenv hglob_eq
      (by
        intro b hb
        by_cases h : b = sp
        · subst b; rw [hsp] at hb; cases hb
        · simpa [bc', f, h] using hb)
  have hrom' : romatch bc' m rm :=
    anonymize_romatch_exten bc bc' m rm hrom hglob_eq_rev
  have hnostack' : bc_nostack bc' := by
    intro b hb
    by_cases h : b = sp
    · subst b; simp [bc', f] at hb
    · by_cases hs : bc b = BCstack
      · have heq : b = sp := bc.bc_stack b sp hs hsp
        exact False.elim (h heq)
      · have hbc : bc b = bc' b := by simpa [bc', f, h]
        apply hs
        exact hbc.symm ▸ hb
  have hsp' : bc' sp = BCinvalid := by simp [bc', f]
  have hsame : ∀ b, b ≠ sp → bc' b = bc b := by
    intro b hb; simp [bc', f, hb]
  have hmm' : mmatch bc' m mtop := by
    constructor
    · intro b hb
      exact False.elim (hnostack' b hb)
    · intro id ab b hb hget
      change positive at id
      change PTree.get id (PTree.empty ablock) = some ab at hget
      have hempty : PTree.get id (PTree.empty ablock) = none :=
        PTree.gempty ablock id
      rw [hempty] at hget
      cases hget
    · intro b hbStack hbInvalid
      have hbsp : b ≠ sp := by
        intro h; subst b; exact hbInvalid hsp'
      have hstackOld : bc b ≠ BCstack := by
        intro hs
        exact hbsp (bc.bc_stack b sp hs hsp)
      have hinvalidOld : bc b ≠ BCinvalid := by
        intro hi
        apply hbInvalid
        simpa [bc', f, hbsp] using hi
      exact hSM b am.am_nonstack hnoleak
        (hmm.mmatch_nonstack b hstackOld hinvalidOld)
    · intro b hbInvalid
      have hbsp : b ≠ sp := by
        intro h; subst b; exact hbInvalid hsp'
      have hstackOld : bc b ≠ BCstack := by
        intro hs
        exact hbsp (bc.bc_stack b sp hs hsp)
      have hinvalidOld : bc b ≠ BCinvalid := by
        intro hi
        apply hbInvalid
        simpa [bc', f, hbsp] using hi
      exact hSM b am.am_nonstack hnoleak
        (hmm.mmatch_nonstack b hstackOld hinvalidOld)
    · intro b hbInvalid
      have hbsp : b ≠ sp := by
        intro h; subst b; exact hbInvalid hsp'
      have hinvalidOld : bc b ≠ BCinvalid := by
        intro hi
        apply hbInvalid
        simpa [bc', f, hbsp] using hi
      exact hmm.mmatch_below b hinvalidOld
  exact ⟨bc', hnostack', hsp', hsame, hVM, hgenv', hrom', hmm'⟩

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib

theorem sound_stack_new_bound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    sound_stack_new_boundStatement := by
  intro cfg prog ge bc stk m bound bound' hstk hle
  cases hstk with
  | sound_stack_nil =>
      exact sound_stack_nil bc m bound'
  | sound_stack_public_call =>
      rename_i res f sp pc e stk bc0 bound0 ae below sp' ge' an em sp0 same stk0 incr
      exact sound_stack_public_call
        (bc := bc) (res := res) (f := f) (sp := sp) (pc := pc) (e := e)
        (stk := stk) (m := m) (bound := bound') (bc' := bc0) (bound' := bound0)
        (ae := ae) (STK := stk0)
        (INCR := Ple_trans bound0 bound bound' incr hle)
        (BELOW := below) (SP := sp0) (SP' := sp') (SAME := same)
        (GE := ge') (AN := an) (EM := em)
  | sound_stack_private_call =>
      rename_i res f sp pc e stk bc0 bound0 ae am below sp' ge' an em sp0 same stk0 contents incr
      exact sound_stack_private_call
        (bc := bc) (res := res) (f := f) (sp := sp) (pc := pc) (e := e)
        (stk := stk) (m := m) (bound := bound') (bc' := bc0) (bound' := bound0)
        (ae := ae) (am := am) (STK := stk0)
        (INCR := Ple_trans bound0 bound bound' incr hle)
        (BELOW := below) (SP := sp0) (SP' := sp') (SAME := same)
        (GE := ge') (AN := an) (EM := em) (CONTENTS := contents)

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Lib.Coqlib

theorem sound_stack_exten
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    sound_stack_extenStatement := by
  intro cfg prog ge bc stk m bound bc1 hstk hbc
  cases hstk with
  | sound_stack_nil =>
      exact sound_stack_nil bc1 m bound
  | sound_stack_public_call =>
      rename_i res f sp pc e stk bc0 bound0 ae below spNew geMatch analyze ematch spOld same stkProof incr
      have hspBelow : Plt sp bound0 := by
        apply below
        rw [spNew]
        intro h
        cases h
      have hspBound : Plt sp bound :=
        Plt_Ple_trans sp bound0 bound hspBelow incr
      have spNewClass : bc1 sp = BCother := by
        rw [hbc sp hspBound, spOld]
      have sameNew : ∀ b, Plt b bound0 → b ≠ sp → bc1 b = bc0 b := by
        intro b hb hne
        rw [hbc b (Plt_Ple_trans b bound0 bound hb incr)]
        exact same b hb hne
      exact sound_stack_public_call
        (bc := bc1) (res := res) (f := f) (sp := sp) (pc := pc) (e := e)
        (stk := stk) (m := m) (bound := bound) (bc' := bc0) (bound' := bound0)
        (ae := ae) (STK := stkProof) (INCR := incr) (BELOW := below)
        (SP := spNewClass) (SP' := spNew) (SAME := sameNew)
        (GE := geMatch) (AN := analyze) (EM := ematch)
  | sound_stack_private_call =>
      rename_i res f sp pc e stk bc0 bound0 ae am below spNew geMatch analyze ematch spOld same stkProof contents incr
      have hspBelow : Plt sp bound0 := by
        apply below
        rw [spNew]
        intro h
        cases h
      have hspBound : Plt sp bound :=
        Plt_Ple_trans sp bound0 bound hspBelow incr
      have spNewClass : bc1 sp = BCinvalid := by
        rw [hbc sp hspBound, spOld]
      have sameNew : ∀ b, Plt b bound0 → b ≠ sp → bc1 b = bc0 b := by
        intro b hb hne
        rw [hbc b (Plt_Ple_trans b bound0 bound hb incr)]
        exact same b hb hne
      exact sound_stack_private_call
        (bc := bc1) (res := res) (f := f) (sp := sp) (pc := pc) (e := e)
        (stk := stk) (m := m) (bound := bound) (bc' := bc0) (bound' := bound0)
        (ae := ae) (am := am) (STK := stkProof) (INCR := incr) (BELOW := below)
        (SP := spNewClass) (SP' := spNew) (SAME := sameNew)
        (GE := geMatch) (AN := analyze) (EM := ematch) (CONTENTS := contents)

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

theorem sound_state_inv
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    sound_state_invStatement := by
  intro cfg prog st cunit hstate hlink
  cases hstate with
  | sound_state_intro h =>
      exact h cunit hlink

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.ValueDomain

theorem store_init_data_summary : store_init_data_summaryStatement := by
  intro cfg ab p id h
  cases id with
  | Init_int8 n => simpa [store_init_data, ablock_store, vplub] using h
  | Init_int16 n => simpa [store_init_data, ablock_store, vplub] using h
  | Init_int32 n => simpa [store_init_data, ablock_store, vplub] using h
  | Init_int64 n => simpa [store_init_data, ablock_store, vplub] using h
  | Init_float32 n =>
      by_cases hp : CompCert4Lean.Driver.Compopts.propagate_float_constants cfg = true <;>
        simpa [store_init_data, ablock_store, vplub, ntop, hp] using h
  | Init_float64 n =>
      by_cases hp : CompCert4Lean.Driver.Compopts.propagate_float_constants cfg = true <;>
        simpa [store_init_data, ablock_store, vplub, ntop, hp] using h
  | Init_addrof symb ofs =>
      exact plub_least Glob (Gl symb ofs) ab.ab_summary
        (pge.globGl symb ofs) h
  | Init_space n => exact h

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.ValueDomain

theorem store_init_data_list_summary : store_init_data_list_summaryStatement := by
  intro cfg idl
  induction idl with
  | nil =>
      intro ab p h
      exact h
  | cons id ids ih =>
      intro ab p h
      unfold store_init_data_list
      apply ih
      exact store_init_data_summary cfg ab p id h

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem initial_block_classification : initial_block_classificationStatement := by
  intro prog m hmem
  let ge := Genv.globalenv prog
  let f : positive → block_class := fun b =>
    match plt b ge.genv_next with
    | .left _ =>
        match Genv.invert_symbol ge b with
        | none => BCother
        | some id => BCglob id
    | .right _ => BCinvalid
  have hstack : ∀ b1 b2, f b1 = BCstack → f b2 = BCstack → b1 = b2 := by
    intro b1 b2 h1 h2
    cases hp1 : plt b1 ge.genv_next with
    | right hn1 => simp [f, hp1] at h1
    | left ht1 =>
        cases hi1 : Genv.invert_symbol ge b1 <;>
          simp [f, hp1, hi1] at h1
  have hglobuniq : ∀ b1 b2 id, f b1 = BCglob id → f b2 = BCglob id → b1 = b2 := by
    intro b1 b2 id h1 h2
    cases hp1 : plt b1 ge.genv_next with
    | right hn1 => simp [f, hp1] at h1
    | left ht1 =>
        cases hi1 : Genv.invert_symbol ge b1 with
        | none => simp [f, hp1, hi1] at h1
        | some id1 =>
            have hid1 : id1 = id := by simpa [f, hp1, hi1] using h1
            cases hp2 : plt b2 ge.genv_next with
            | right hn2 => simp [f, hp2] at h2
            | left ht2 =>
                cases hi2 : Genv.invert_symbol ge b2 with
                | none => simp [f, hp2, hi2] at h2
                | some id2 =>
                    have hid2 : id2 = id := by simpa [f, hp2, hi2] using h2
                    subst id1
                    subst id2
                    have hs1 : Genv.find_symbol ge id = some b1 :=
                      Genv.invert_find_symbol _ _ ge id b1 hi1
                    have hs2 : Genv.find_symbol ge id = some b2 :=
                      Genv.invert_find_symbol _ _ ge id b2 hi2
                    exact Option.some.inj (hs1.symm.trans hs2)
  let bc : block_classification :=
    { bc_img := f, bc_stack := hstack, bc_glob := hglobuniq }
  have hgenv : genv_match bc ge := by
    constructor
    · intro id b
      constructor
      · intro hs
        have hi : Genv.invert_symbol ge b = some id :=
          Genv.find_invert_symbol _ _ ge id b hs
        have hrange : Plt b ge.genv_next := ge.genv_symb_range id hs
        cases hp : plt b ge.genv_next with
        | right hn => exact False.elim (hn hrange)
        | left ht =>
            cases hi' : Genv.invert_symbol ge b with
            | none => simp [bc, f, hp, hi'] at hi
            | some id' =>
                have : id' = id := by simpa [hi'] using hi
                simpa [bc, f, hp, hi'] using this
      · intro hf
        cases hp : plt b ge.genv_next with
        | right hn => simp [bc, f, hp] at hf
        | left ht =>
            cases hi : Genv.invert_symbol ge b with
            | none => simp [bc, f, hp, hi] at hf
            | some id' =>
                have : id' = id := by simpa [bc, f, hp, hi] using hf
                subst id'
                exact Genv.invert_find_symbol _ _ ge id b hi
    · intro b hb
      cases hp : plt b ge.genv_next with
      | right hn => exact False.elim (hn hb)
      | left ht =>
          cases hi : Genv.invert_symbol ge b <;>
            simp [bc, f, hp, hi]
  have hnext : ge.genv_next = m.nextblock :=
    Genv.init_mem_genv_next _ _ prog m hmem
  have hbelow : bc_below bc m.nextblock := by
    intro b hb
    have hrange : Plt b ge.genv_next := by
      cases hp : plt b ge.genv_next with
      | left ht => exact ht
      | right hn =>
          exfalso
          apply hb
          simp [bc, f, hp]
    rw [hnext] at hrange
    exact hrange
  have hnostack : bc_nostack bc := by
    intro b hb
    cases hp : plt b ge.genv_next with
    | right hn => simp [bc, f, hp] at hb
    | left ht =>
        cases hi : Genv.invert_symbol ge b <;>
          simp [bc, f, hp, hi] at hb
  have hglob : ∀ b id, bc b = BCglob id →
      Genv.find_symbol ge id = some b := by
    intro b id hb
    exact hgenv.1 id b |>.mpr hb
  have hvalid : ∀ b, Mem.valid_block m b → bc b ≠ BCinvalid := by
    intro b hv hb
    change Plt b m.nextblock at hv
    have hrange : Plt b ge.genv_next := by
      rw [hnext]
      exact hv
    cases hp : plt b ge.genv_next with
    | right hn => exact hn hrange
    | left ht =>
        cases hi : Genv.invert_symbol ge b <;>
          simp [bc, f, hp, hi] at hb
  exact ⟨bc, hgenv, hbelow, hnostack, hglob, hvalid⟩

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps

private theorem pg_loadbytes_store_other_block
    (chunk : memory_chunk) (m : mem) (b : block) (ofs : Z) (v : val)
    (m' : mem) (hstore : Mem.store chunk m b ofs v = some m')
    (b' : block) (hne : b' ≠ b) (ofs' n : Z) :
    Mem.loadbytes m' b' ofs' n = Mem.loadbytes m b' ofs' n := by
  have hcontents : PMap.get b' m'.mem_contents = PMap.get b' m.mem_contents := by
    rw [Mem.store_mem_contents chunk m b ofs v m' hstore]
    exact PMap.gso
      (A := CompCert4Lean.Lib.Maps.ZMap.t memval)
      (i := b') (j := b)
      (Mem.setN (encode_val chunk v) ofs (PMap.get b m.mem_contents))
      m.mem_contents hne
  unfold Mem.loadbytes
  cases hm : Mem.range_perm_dec m b' ofs' (zAdd ofs' n) Cur Readable with
  | left hrange =>
      have hrange' : Mem.range_perm m' b' ofs' (zAdd ofs' n) Cur Readable := by
        intro q hq
        exact Mem.perm_store_1 chunk m b ofs v m' hstore b' q Cur Readable
          (hrange q hq)
      cases hm' : Mem.range_perm_dec m' b' ofs' (zAdd ofs' n) Cur Readable with
      | left _ => rw [hcontents]; rfl
      | right hn => exact False.elim (hn hrange')
  | right hnrange =>
      have hnrange' : ¬ Mem.range_perm m' b' ofs' (zAdd ofs' n) Cur Readable := by
        intro hrange'
        apply hnrange
        intro q hq
        exact Mem.perm_store_2 chunk m b ofs v m' hstore b' q Cur Readable
          (hrange' q hq)
      cases hm' : Mem.range_perm_dec m' b' ofs' (zAdd ofs' n) Cur Readable with
      | left hrange' => exact False.elim (hnrange' hrange')
      | right _ => rfl

private theorem pg_bmatch_store_other
    (bc : block_classification) (chunk : memory_chunk) (m : mem)
    (b : block) (ofs : Z) (v : val) (m' : mem)
    (hstore : Mem.store chunk m b ofs v = some m')
    (b' : block) (hne : b' ≠ b) (ab : ablock)
    (hmatch : bmatch bc m b' ab) : bmatch bc m' b' ab := by
  rcases hmatch with ⟨⟨hload, hfragment⟩, habload⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro chunk' ofs' v' hload'
    apply hload chunk' ofs' v'
    have heq := Mem.load_store_other chunk m b ofs v m' hstore chunk' b' ofs'
      (Or.inl hne)
    rw [heq] at hload'
    exact hload'
  · intro ofs' bx bxofs q i hloadbytes
    apply hfragment ofs' bx bxofs q i
    rw [pg_loadbytes_store_other_block chunk m b ofs v m' hstore b' hne]
      at hloadbytes
    exact hloadbytes
  · intro chunk' ofs' v' hload'
    apply habload chunk' ofs' v'
    have heq := Mem.load_store_other chunk m b ofs v m' hstore chunk' b' ofs'
      (Or.inl hne)
    rw [heq] at hload'
    exact hload'

theorem store_init_data_other : store_init_data_otherStatement := by
  intro prog bc m b p id m' ab b' hstore hne hmatch
  cases id with
  | Init_int8 n =>
      exact pg_bmatch_store_other bc Mint8unsigned m b p (Vint n) m'
        hstore b' hne ab hmatch
  | Init_int16 n =>
      exact pg_bmatch_store_other bc Mint16unsigned m b p (Vint n) m'
        hstore b' hne ab hmatch
  | Init_int32 n =>
      exact pg_bmatch_store_other bc Mint32 m b p (Vint n) m'
        hstore b' hne ab hmatch
  | Init_int64 n =>
      exact pg_bmatch_store_other bc Mint64 m b p (Vlong n) m'
        hstore b' hne ab hmatch
  | Init_float32 n =>
      exact pg_bmatch_store_other bc Mfloat32 m b p (Vsingle n) m'
        hstore b' hne ab hmatch
  | Init_float64 n =>
      exact pg_bmatch_store_other bc Mfloat64 m b p (Vfloat n) m'
        hstore b' hne ab hmatch
  | Init_addrof id ofs =>
      change (match Genv.find_symbol (Genv.globalenv prog) id with
        | none => none
        | some bx => Mem.store Mptr m b p (Vptr bx ofs)) = some m' at hstore
      cases hfind : Genv.find_symbol (Genv.globalenv prog) id with
      | none => simp [hfind] at hstore
      | some bx =>
          simp [hfind] at hstore
          exact pg_bmatch_store_other bc Mptr m b p (Vptr bx ofs) m'
            hstore b' hne ab hmatch
  | Init_space n =>
      change some m = some m' at hstore
      cases hstore
      exact hmatch

theorem store_init_data_list_other : store_init_data_list_otherStatement := by
  intro prog bc b b' ab idl
  induction idl with
  | nil =>
      intro m p m' hstore hne hmatch
      change some m = some m' at hstore
      cases hstore
      exact hmatch
  | cons id ids ih =>
      intro m p m' hstore hne hmatch
      change (match Genv.store_init_data (Genv.globalenv prog) m b p id with
        | none => none
        | some m1 => Genv.store_init_data_list (Genv.globalenv prog) m1 b
            (zAdd p (init_data_size id)) ids) = some m' at hstore
      cases hhead : Genv.store_init_data (Genv.globalenv prog) m b p id with
      | none => simp [hhead] at hstore
      | some m1 =>
          have htail : Genv.store_init_data_list (Genv.globalenv prog) m1 b
              (zAdd p (init_data_size id)) ids = some m' := by
            simpa [hhead] using hstore
          apply ih m1 (zAdd p (init_data_size id)) m' htail hne
          exact store_init_data_other prog bc m b p id m1 ab b' hhead hne hmatch

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps

theorem store_zeros_other : store_zeros_otherStatement := by
  intro bc b' ab m b p n m' hzeros hne hmatch
  let P : mem → block → Z → Z → Option mem → Prop :=
    fun m0 b0 _ _ result =>
      match result with
      | some m1 =>
          ∀ (b'' : block) (ab'' : ablock) (m'' : mem),
            m1 = m'' → b'' ≠ b0 →
            bmatch bc m0 b'' ab'' → bmatch bc m'' b'' ab''
      | none => True
  have hP : ∀ m0 b0 p0 n0, P m0 b0 p0 n0 (store_zeros m0 b0 p0 n0) := by
    apply store_zeros_ind (P := P)
    · intro m0 b0 p0 n0 x hx
      intro b'' ab'' m'' heq hne' hmatch'
      cases heq
      exact hmatch'
    · intro m0 b0 p0 n0 x hx m1 hstore hrec
      cases hresult : store_zeros m1 b0 (zAdd p0 (.Zpos .xH))
          (ZArith.BinInt.Z.sub n0 (.Zpos .xH)) with
      | none => trivial
      | some m2 =>
          rw [hresult] at hrec
          intro b'' ab'' m'' heq hne' hmatch'
          apply hrec b'' ab'' m'' heq hne'
          exact pg_bmatch_store_other bc Mint8unsigned m0 b0 p0 Vzero m1
            hstore b'' hne' ab'' hmatch'
    · intro m0 b0 p0 n0 x hx hnone
      trivial
  have hs := hP m b p n
  rw [hzeros] at hs
  exact hs b' ab m' rfl hne hmatch

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps

private theorem pg_alloc_global_set_same {A : Type} (i : positive) (x : A)
    (m : PTree.t A) : PTree.get i (PTree.set i x m) = some x := by
  have h := PTree.gsspec_proof i i x m
  cases hp : CompCert4Lean.Lib.Coqlib.peq i i with
  | left _ => simpa [hp] using h
  | right hn => exact False.elim (hn rfl)

private theorem pg_alloc_global_set_other {A : Type} (i j : positive) (x : A)
    (m : PTree.t A) (hne : i ≠ j) :
    PTree.get i (PTree.set j x m) = PTree.get i m := by
  have h := PTree.gsspec_proof i j x m
  cases hp : CompCert4Lean.Lib.Coqlib.peq i j with
  | left he => exact False.elim (hne he)
  | right _ => simpa [hp, PTree.t] using h

private theorem pg_alloc_global_remove_same {A : Type} (i : positive)
    (m : PTree.t A) : PTree.get i (PTree.remove i m) = none := by
  exact PTree.grs_proof i m

private theorem pg_alloc_global_remove_other {A : Type} (i j : positive)
    (m : PTree.t A) (hne : i ≠ j) :
    PTree.get i (PTree.remove j m) = PTree.get i m := by
  exact PTree.gro_proof m hne

theorem alloc_global_consistent : alloc_global_consistentStatement := by
  intro cfg dm rm idg hcons
  unfold romem_consistent at hcons ⊢
  rcases idg with ⟨id1, gd⟩
  cases gd with
  | Gfun f =>
      change positive at id1
      intro id ab hab
      change PTree.get id (PTree.remove id1 rm) = some ab at hab
      have hne : id ≠ id1 := by
        intro heq
        subst id
        have hn : PTree.get id1 (PTree.remove id1 rm) = none :=
          pg_alloc_global_remove_same id1 rm
        rw [hn] at hab
        contradiction
      have horig : PTree.get id rm = some ab := by
        have hr : PTree.get id (PTree.remove id1 rm) = PTree.get id rm :=
          pg_alloc_global_remove_other id id1 rm hne
        rw [hr] at hab
        exact hab
      obtain ⟨v, hdm, hro, hvol, hdef, habv⟩ := hcons id ab horig
      refine ⟨v, ?_, hro, hvol, hdef, habv⟩
      change PTree.get id (PTree.set id1 (Gfun f) dm) = some (Gvar v)
      have hs : PTree.get id (PTree.set id1 (Gfun f) dm) = PTree.get id dm :=
        pg_alloc_global_set_other id id1 (Gfun f) dm hne
      rw [hs]
      exact hdm
  | Gvar v1 =>
      change positive at id1
      intro id ab hab
      change PTree.get id
        (if (v1.gvar_readonly && !v1.gvar_volatile &&
            definitive_initializer v1.gvar_init) = true then
          PTree.set id1
            (store_init_data_list cfg (ablock_init Pbot) (.Z0) v1.gvar_init) rm
        else PTree.remove id1 rm) = some ab at hab
      by_cases hguard :
          (v1.gvar_readonly && !v1.gvar_volatile &&
            definitive_initializer v1.gvar_init) = true
      · rw [if_pos hguard] at hab
        by_cases heq : id = id1
        · subst id
          have hs : PTree.get id1
              (PTree.set id1
                (store_init_data_list cfg (ablock_init Pbot) (.Z0) v1.gvar_init) rm) =
              some (store_init_data_list cfg (ablock_init Pbot) (.Z0) v1.gvar_init) :=
            pg_alloc_global_set_same id1 _ rm
          rw [hs] at hab
          cases hab
          rw [Bool.and_eq_true, Bool.and_eq_true] at hguard
          rcases hguard with ⟨⟨hro, hnvol⟩, hdef⟩
          have hvol : v1.gvar_volatile = false := by
            cases hv : v1.gvar_volatile <;> simp [hv] at hnvol ⊢
          refine ⟨v1, ?_, hro, hvol, hdef, rfl⟩
          change PTree.get id1 (PTree.set id1 (Gvar v1) dm) = some (Gvar v1)
          exact pg_alloc_global_set_same id1 (Gvar v1) dm
        · have horig : PTree.get id rm = some ab := by
            have hs : PTree.get id
                (PTree.set id1
                  (store_init_data_list cfg (ablock_init Pbot) (.Z0) v1.gvar_init) rm) =
                PTree.get id rm := pg_alloc_global_set_other id id1 _ rm heq
            rw [hs] at hab
            exact hab
          obtain ⟨v, hdm, hro, hvol, hdef, habv⟩ := hcons id ab horig
          refine ⟨v, ?_, hro, hvol, hdef, habv⟩
          change PTree.get id (PTree.set id1 (Gvar v1) dm) = some (Gvar v)
          have hs : PTree.get id (PTree.set id1 (Gvar v1) dm) = PTree.get id dm :=
            pg_alloc_global_set_other id id1 (Gvar v1) dm heq
          rw [hs]
          exact hdm
      · rw [if_neg hguard] at hab
        have hne : id ≠ id1 := by
          intro heq
          subst id
          have hn : PTree.get id1 (PTree.remove id1 rm) = none :=
            pg_alloc_global_remove_same id1 rm
          rw [hn] at hab
          contradiction
        have horig : PTree.get id rm = some ab := by
          have hr : PTree.get id (PTree.remove id1 rm) = PTree.get id rm :=
            pg_alloc_global_remove_other id id1 rm hne
          rw [hr] at hab
          exact hab
        obtain ⟨v, hdm, hro, hvol, hdef, habv⟩ := hcons id ab horig
        refine ⟨v, ?_, hro, hvol, hdef, habv⟩
        change PTree.get id (PTree.set id1 (Gvar v1) dm) = some (Gvar v)
        have hs : PTree.get id (PTree.set id1 (Gvar v1) dm) = PTree.get id dm :=
          pg_alloc_global_set_other id id1 (Gvar v1) dm hne
        rw [hs]
        exact hdm

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Lib.Maps

theorem romem_for_consistent : romem_for_consistentStatement := by
  intro cfg cunit
  have hfold : ∀ (l : List (ident × globdef CompCert4Lean.Backend.RTL.fundef Unit))
      (dm : PTree.t (globdef CompCert4Lean.Backend.RTL.fundef Unit))
      (rm : PTree.t ablock),
      romem_consistent cfg dm rm →
        romem_consistent cfg
          (l.foldl (fun m idg => PTree.set idg.1 idg.2 m) dm)
          (l.foldl (fun rm idg => alloc_global cfg rm idg) rm) := by
    intro l
    induction l with
    | nil =>
        intro dm rm h
        simpa only [List.foldl] using h
    | cons idg l ih =>
        intro dm rm h
        apply ih
        exact alloc_global_consistent cfg dm rm idg h
  have hbase : romem_consistent cfg
      (PTree.empty (globdef CompCert4Lean.Backend.RTL.fundef Unit))
      (PTree.empty ablock) := by
    intro id ab hget
    have hempty : PTree.get id (PTree.empty ablock) = none :=
      PTree.gempty ablock id
    rw [hempty] at hget
    contradiction
  exact hfold cunit.prog_defs
    (PTree.empty (globdef CompCert4Lean.Backend.RTL.fundef Unit))
    (PTree.empty ablock) hbase

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Maps

theorem romem_for_consistent_2 : romem_for_consistent_2Statement := by
  intro cfg prog cunit hlink
  intro id ab hab
  obtain ⟨v, hdm, hro, hvol, hdef, habv⟩ :=
    romem_for_consistent cfg cunit id ab hab
  obtain ⟨gd, hprog, hgd⟩ :=
    prog_defmap_linkorder_proof
      (F := CompCert4Lean.Backend.RTL.fundef) (V := Unit)
      (LF := Linker_fundef CompCert4Lean.Backend.RTL.function) (LV := Linker_unit)
      cunit prog id (.Gvar v) hlink hdm
  cases hgd with
  | linkorder_def_var v1 v2 hvar =>
      cases hvar with
      | linkorder_vardef_intro info1 info2 i1 i2 ro vo hinfo hinit =>
          have hinit_eq : i2 = i1 := by
            cases hinit with
            | linkorder_varinit_refl il => rfl
            | linkorder_varinit_extern il =>
                simp [definitive_initializer] at hdef
            | linkorder_varinit_common size il hne hsize =>
                simp [definitive_initializer] at hdef
          have hro' : ro = true := by
            simpa using hro
          have hvol' : vo = false := by
            simpa using hvol
          subst i2
          subst ro
          subst vo
          refine ⟨({ gvar_info := info2, gvar_init := i1, gvar_readonly := true, gvar_volatile := false } : globvar Unit),
            hprog, ?_, ?_, ?_, ?_⟩
          · exact rfl
          · exact rfl
          · exact hdef
          · exact habv

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis.DS

theorem fixpoint_solution_proof {cfg : CompCert4Lean.Config.CompilerConfig}
    (laws : law_obligation cfg) : fixpoint_solution laws := by
  intro A code successors transf ep ev res n instr s hfix hcode hsucc hbot
  exact CompCert4Lean.Backend.Kildall.Dataflow_Solver.fixpoint_solution
    (L cfg) CompCert4Lean.Backend.Kildall.NodeSetForward laws.1 laws.2
    code successors transf ep ev res n instr s hfix hcode hsucc hbot

end CompCert4Lean.Backend.ValueAnalysis.DS

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private theorem pg_static_ptrofs_zero_add (ofs : ptrofs) :
    Ptrofs.add Ptrofs.zero ofs = ofs := by
  apply WordCore.ext_of_val_eq
  have hadd : (Ptrofs.add Ptrofs.zero ofs).val =
      (Ptrofs.zero.val + ofs.val) % (2 ^ Ptrofs.wordsize) := by
    run_tac
      let env ← Lean.getEnv
      let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith ".WordCore.add_val")
        | throwError "WordCore addition lemma unavailable"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n) Ptrofs.zero $(Lean.mkIdent `ofs)))
  rw [hadd]
  change (0 + ofs.val) % (2 ^ Ptrofs.wordsize) = ofs.val
  have hlt : ofs.val < 2 ^ Ptrofs.wordsize := by
    run_tac
      let env ← Lean.getEnv
      let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith ".WordCore.val_lt")
        | throwError "WordCore range lemma unavailable"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n) $(Lean.mkIdent `ofs)))
  rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]

private theorem pg_static_normalize_ifptr (chunk : memory_chunk) (p : aptr) :
    val_of_aval (vnormalize chunk (Ifptr p)) = Vundef := by
  cases chunk <;> rfl

private theorem pg_static_longofwords_lessdef (a b : aval) (v w : val)
    (hv : Val.lessdef (val_of_aval a) v)
    (hw : Val.lessdef (val_of_aval b) w) :
    Val.lessdef (val_of_aval (longofwords a b)) (Val.longofwords v w) := by
  cases a <;> cases b <;>
    simp only [longofwords, val_of_aval, ntop2] <;>
    try exact Val.lessdef_undef _
  cases hv
  cases hw
  exact Val.lessdef_refl _

private theorem pg_static_addl_lessdef (a b : aval) (v w : val)
    (hv : Val.lessdef (val_of_aval a) v)
    (hw : Val.lessdef (val_of_aval b) w) :
    Val.lessdef (val_of_aval (addl a b)) (Val.addl v w) := by
  cases a <;> cases b <;>
    simp only [addl, val_of_aval, ntop2] <;>
    try exact Val.lessdef_undef _
  cases hv
  cases hw
  exact Val.lessdef_refl _

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private theorem pg_static_arg_lessdef
    (cfg : CompilerConfig) (bc : block_classification) (ge : genv)
    (rs : regset) (sp : block) (m : mem) (ae : aenv) (rm : romem) (am : amem)
    (hem : ematch bc rs ae) (hro : romatch bc m rm) (hmm : mmatch bc m am)
    (hge : genv_match bc ge) (hsp : bc sp = BCstack)
    (a : builtin_arg reg) (v : val)
    (heval : eval_builtin_arg (Genv.to_senv ge) (fun r => Regmap.get r rs)
      (Vptr sp Ptrofs.zero) m a v) :
    Val.lessdef (val_of_aval (abuiltin_arg cfg ae am rm a)) v := by
  induction heval with
  | eval_BA r =>
      exact val_of_aval_sound bc _ _ (areg_sound bc rs ae r hem)
  | eval_BA_int n => exact Val.lessdef_refl _
  | eval_BA_long n => exact Val.lessdef_refl _
  | eval_BA_float n => exact Val.lessdef_refl _
  | eval_BA_single n => exact Val.lessdef_refl _
  | eval_BA_loadstack chunk ofs v hload =>
      have hl : Mem.load chunk m sp (Ptrofs.unsigned ofs) = some v := by
        simpa only [Val.offset_ptr, pg_static_ptrofs_zero_add, Mem.loadv] using hload
      exact val_of_aval_sound bc v _
        ((hmm.mmatch_stack sp hsp).2 chunk (Ptrofs.unsigned ofs) v hl)
  | eval_BA_addrstack ofs => exact Val.lessdef_undef _
  | eval_BA_loadglobal chunk id ofs v hload =>
      change Mem.loadv chunk m
        (match Genv.find_symbol ge id with
          | some b => Vptr b ofs
          | none => Vundef) = some v at hload
      cases hf : Genv.find_symbol ge id with
      | none => simp [hf, Mem.loadv] at hload
      | some b =>
          have hl : Mem.load chunk m b (Ptrofs.unsigned ofs) = some v := by
            simpa only [hf, Mem.loadv] using hload
          have hb : bc b = BCglob id := (hge.1 id b).mp hf
          change Val.lessdef (val_of_aval (load cfg chunk rm am (Gl id ofs))) v
          simp only [load]
          cases hr : PTree.get id rm with
          | some ab =>
              exact val_of_aval_sound bc v _
                ((hro b id ab hb hr).2.1.2 chunk (Ptrofs.unsigned ofs) v hl)
          | none =>
              cases hg : PTree.get id am.am_glob with
              | some ab =>
                  exact val_of_aval_sound bc v _
                    ((hmm.mmatch_glob id ab b hb hg).2 chunk (Ptrofs.unsigned ofs) v hl)
              | none =>
                  rw [pg_static_normalize_ifptr]
                  exact Val.lessdef_undef _
  | eval_BA_addrglobal id ofs => exact Val.lessdef_undef _
  | eval_BA_splitlong hi lo vhi vlo _ _ ihhi ihlo =>
      exact pg_static_longofwords_lessdef _ _ _ _ ihhi ihlo
  | eval_BA_addptr a1 a2 v1 v2 _ _ ih1 ih2 =>
      exact pg_static_addl_lessdef _ _ _ _ ih1 ih2

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib

theorem eval_static_builtin_function_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_static_builtin_function_soundStatement := by
  intro cfg bc ge rs sp m ae rm am bf al vl v va hem hro hmm hge hsp heval hstatic hsem
  have hargs : Val.lessdef_list
      (List.map val_of_aval (al.map (abuiltin_arg cfg ae am rm))) vl := by
    clear hstatic hsem
    induction heval with
    | nil => exact Val.lessdef_list_nil
    | cons a w ha _ ih =>
        exact Val.lessdef_list_cons _ _ _ _
          (pg_static_arg_lessdef cfg bc ge rs sp m ae rm am hem hro hmm hge hsp a w ha) ih
  unfold eval_static_builtin_function at hstatic
  cases hs : builtin_function_sem
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) bf
      (List.map val_of_aval (al.map (abuiltin_arg cfg ae am rm))) with
  | none => simp only [hs] at hstatic; contradiction
  | some v0 =>
      simp only [hs] at hstatic
      obtain ⟨v', hsem', hless⟩ := builtin_function_sem_lessdef
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        bf _ v0 vl hs hargs
      have hv : v' = v := Option.some.inj (hsem'.symm.trans hsem)
      subst v'
      cases hless with
      | lessdef_refl => exact aval_of_val_sound bc v va hstatic
      | lessdef_undef => simp [aval_of_val] at hstatic

end CompCert4Lean.Backend.ValueAnalysis
namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private theorem pg_alloc_stack_undef_vmatch (bc : block_classification)
    (chunk : memory_chunk) (ofs : Z) :
    vmatch bc Vundef (ablock_load chunk (ablock_init Pbot) ofs) := by
  simp only [ablock_load, ablock_init]
  rw [show ZTree.get ofs (ZTree.empty acontent) = none by exact PTree.gempty _ _]
  cases chunk <;> simp [vnormalize, ntop1, provenance, poffset]
  all_goals first | exact vmatch.ifptrUndef _ | exact vmatch.numUndef _ | exact vmatch.vmatch_Uns_undef _ _ | exact vmatch.sgnUndef _ _

private theorem pg_pmatch_incr
    (bc bc' : block_classification) (b : block) (ofs : ptrofs) (p : aptr)
    (hincr : bc_incr bc bc') (h : pmatch bc b ofs p) :
    pmatch bc' b ofs p := by
  cases h with
  | gl id hb => apply pmatch.gl; rw [hincr b (by simp [hb])]; exact hb
  | glo id hb => apply pmatch.glo; rw [hincr b (by simp [hb])]; exact hb
  | glob id hb => apply pmatch.glob; rw [hincr b (by simp [hb])]; exact hb
  | stk hb => apply pmatch.stk; rw [hincr b (by simp [hb])]; exact hb
  | stack hb => apply pmatch.stack; rw [hincr b (by simp [hb])]; exact hb
  | nonstack hs hi =>
      apply pmatch.nonstack
      · intro h'; apply hs
        rw [hincr b hi] at h'
        exact h'
      · intro h'; apply hi
        rw [hincr b hi] at h'
        exact h'
  | top hi =>
      apply pmatch.top
      intro h'; apply hi
      rw [hincr b hi] at h'
      exact h'

private theorem pg_vmatch_incr
    (bc bc' : block_classification) (v : val) (x : aval)
    (hincr : bc_incr bc bc') (h : vmatch bc v x) :
    vmatch bc' v x := by
  cases h with
  | vmatch_i i => exact vmatch.vmatch_i i
  | vmatch_iu i => exact vmatch.vmatch_iu i
  | iuUndef i => exact vmatch.iuUndef i
  | uns p i n h1 h2 => exact vmatch.uns p i n h1 h2
  | vmatch_Uns_undef p n => exact vmatch.vmatch_Uns_undef p n
  | sgn p i n h1 h2 => exact vmatch.sgn p i n h1 h2
  | sgnUndef p n => exact vmatch.sgnUndef p n
  | long i => exact vmatch.long i
  | float f => exact vmatch.float f
  | single f => exact vmatch.single f
  | numUndef p => exact vmatch.numUndef p
  | numInt i p => exact vmatch.numInt i p
  | numLong i p => exact vmatch.numLong i p
  | numFloat f p => exact vmatch.numFloat f p
  | numSingle f p => exact vmatch.numSingle f p
  | ptr b ofs p hp => exact vmatch.ptr b ofs p (pg_pmatch_incr bc bc' b ofs p hincr hp)
  | ptrUndef p => exact vmatch.ptrUndef p
  | ifptrUndef p => exact vmatch.ifptrUndef p
  | ifptrInt i p => exact vmatch.ifptrInt i p
  | ifptrLong i p => exact vmatch.ifptrLong i p
  | ifptrFloat f p => exact vmatch.ifptrFloat f p
  | ifptrSingle f p => exact vmatch.ifptrSingle f p
  | ifptrPtr b ofs p hp => exact vmatch.ifptrPtr b ofs p (pg_pmatch_incr bc bc' b ofs p hincr hp)

private theorem pg_smatch_incr
    (bc bc' : block_classification) (m : mem) (b : block) (p : aptr)
    (hincr : bc_incr bc bc') (h : smatch bc m b p) :
    smatch bc' m b p := by
  rcases h with ⟨hload, hbytes⟩
  constructor
  · intro chunk ofs v hv
    exact pg_vmatch_incr bc bc' v (Ifptr p) hincr (hload chunk ofs v hv)
  · intro ofs b' ofs' q i hv
    exact pg_pmatch_incr bc bc' b' ofs' p hincr (hbytes ofs b' ofs' q i hv)

private theorem pg_alloc_preserve_bmatch
    (bc : block_classification) (m m' : mem) (b : block) (ab : ablock)
    (sp : block) (sz : Z) (halloc : Mem.alloc m z0 sz = (m', sp))
    (hbelow : Plt b m.nextblock) (hbm : bmatch bc m b ab) :
    bmatch bc m' b ab := by
  apply bmatch_inv bc m b ab m' hbm
  intro ofs n hn
  exact Mem.loadbytes_alloc_unchanged m z0 sz m' sp halloc b ofs n
    (by unfold Mem.valid_block; exact hbelow)

private theorem pg_alloc_preserve_smatch
    (bc : block_classification) (m m' : mem) (b : block) (p : aptr)
    (sp : block) (sz : Z) (halloc : Mem.alloc m z0 sz = (m', sp))
    (hbelow : Plt b m.nextblock) (hsm : smatch bc m b p) :
    smatch bc m' b p := by
  apply smatch_inv bc m b p m' hsm
  intro ofs n hn
  exact Mem.loadbytes_alloc_unchanged m z0 sz m' sp halloc b ofs n
    (by unfold Mem.valid_block; exact hbelow)

private theorem pg_alloc_stack_undef_smatch
    (bc : block_classification) (m m' : mem) (sp : block) (sz : Z)
    (halloc : Mem.alloc m z0 sz = (m', sp)) :
    smatch bc m' sp Nonstack := by
  constructor
  · intro chunk ofs v hload
    have hv : v = Vundef := Mem.load_alloc_same m z0 sz m' sp halloc chunk ofs v hload
    subst v
    exact vmatch.ifptrUndef Nonstack
  · intro ofs b' ofs' q i hbytes
    have hm : Fragment (Vptr b' ofs') q i ∈
        [Fragment (Vptr b' ofs') q i] := by simp
    have hu := Mem.loadbytes_alloc_same m z0 sz m' sp halloc ((.Zpos .xH) : Z) ofs
      [Fragment (Vptr b' ofs') q i] (Fragment (Vptr b' ofs') q i) hbytes hm
    cases hu

private theorem pg_alloc_stack_undef_bmatch
    (bc : block_classification) (m m' : mem) (sp : block) (sz : Z)
    (halloc : Mem.alloc m z0 sz = (m', sp)) :
    bmatch bc m' sp (ablock_init Pbot) := by
  constructor
  · constructor
    · intro chunk ofs v hload
      have hv : v = Vundef := Mem.load_alloc_same m z0 sz m' sp halloc chunk ofs v hload
      subst v
      exact vmatch.ifptrUndef Pbot
    · intro ofs b' ofs' q i hbytes
      have hm : Fragment (Vptr b' ofs') q i ∈
          [Fragment (Vptr b' ofs') q i] := by simp
      have hu := Mem.loadbytes_alloc_same m z0 sz m' sp halloc ((.Zpos .xH) : Z) ofs
        [Fragment (Vptr b' ofs') q i] (Fragment (Vptr b' ofs') q i) hbytes hm
      cases hu
  · intro chunk ofs v hload
    have hv : v = Vundef := Mem.load_alloc_same m z0 sz m' sp halloc chunk ofs v hload
    subst v
    exact pg_alloc_stack_undef_vmatch bc chunk ofs

theorem allocate_stack : allocate_stackStatement := by
  classical
  intro m sz m' sp bc ge rm am halloc hgenv hrom hmm hnostack
  have hnext : m'.nextblock = PArith.BinPos.Pos.succ m.nextblock :=
    Mem.nextblock_alloc m z0 sz m' sp halloc
  have hsp : sp = m.nextblock := Mem.alloc_result m z0 sz m' sp halloc
  have hspinvalid : bc sp = BCinvalid := by
    rw [hsp]
    apply bc_below_invalid m.nextblock
    · exact Plt_strict _
    · exact hmm.mmatch_below
  let f : block → block_class := fun b => if b = sp then BCstack else bc b
  have hfstack : ∀ b1 b2, f b1 = BCstack → f b2 = BCstack → b1 = b2 := by
    intro b1 b2 h1 h2
    by_cases hb1 : b1 = sp
    · subst b1
      by_cases hb2 : b2 = sp
      · exact hb2.symm
      · have : bc b2 = BCstack := by simpa [f, hb2] using h2
        exact False.elim (hnostack b2 this)
    · by_cases hb2 : b2 = sp
      · subst b2
        have : bc b1 = BCstack := by simpa [f, hb1] using h1
        exact False.elim (hnostack b1 this)
      · have h1' : bc b1 = BCstack := by simpa [f, hb1] using h1
        have h2' : bc b2 = BCstack := by simpa [f, hb2] using h2
        exact bc.bc_stack b1 b2 h1' h2'
  have hfglob : ∀ b1 b2 id, f b1 = BCglob id → f b2 = BCglob id → b1 = b2 := by
    intro b1 b2 id h1 h2
    have h1' : bc b1 = BCglob id := by
      by_cases hb : b1 = sp
      · subst b1; simp [f] at h1
      · simpa [f, hb] using h1
    have h2' : bc b2 = BCglob id := by
      by_cases hb : b2 = sp
      · subst b2; simp [f] at h2
      · simpa [f, hb] using h2
    exact bc.bc_glob b1 b2 id h1' h2'
  let bc' : block_classification := { bc_img := f, bc_stack := hfstack, bc_glob := hfglob }
  have hf_eq : ∀ b, bc b ≠ BCinvalid → bc' b = bc b := by
    intro b hb
    by_cases hbs : b = sp
    · subst b; exact False.elim (hb hspinvalid)
    · simp [bc', f, hbs]
  have hincr : bc_incr bc bc' := fun b hb => hf_eq b hb
  have hgenv' : genv_match bc' ge := by
    rcases hgenv with ⟨hsym, hbelow⟩
    constructor
    · intro id b
      constructor
      · intro hfind
        have hold := (hsym id b).mp hfind
        by_cases hbs : b = sp
        · subst b; rw [hspinvalid] at hold; cases hold
        · simpa [bc', f, hbs] using hold
      · intro hbc
        have hold : bc b = BCglob id := by
          by_cases hbs : b = sp
          · subst b; simp [bc', f] at hbc
          · simpa [bc', f, hbs] using hbc
        exact (hsym id b).mpr hold
    · intro b hb
      have hold := hbelow b hb
      have hne : bc b ≠ BCinvalid := by exact hold.1
      have heq := hf_eq b hne
      constructor
      · intro hi; apply hold.1; exact heq ▸ hi
      · intro hs; apply hold.2; exact heq ▸ hs
  have hrom' : romatch bc' m' rm := by
    intro b id ab hbc hget
    have hbcold : bc b = BCglob id := by
      by_cases hbs : b = sp
      · subst b; simp [bc', f] at hbc
      · simpa [bc', f, hbs] using hbc
    rcases hrom b id ab hbcold hget with ⟨hglob, hbm, hperm⟩
    have hbelow : Plt b m.nextblock := hmm.mmatch_below b (by intro hi; rw [hbcold] at hi; cases hi)
    have hbm' := pg_alloc_preserve_bmatch bc m m' b ab sp sz halloc hbelow hbm
    have hbm'' : bmatch bc' m' b ab := by
      rcases hbm' with ⟨hsm, hload⟩
      constructor
      · exact pg_smatch_incr bc bc' m' b ab.ab_summary hincr hsm
      · intro chunk ofs v hl
        exact pg_vmatch_incr bc bc' v _ hincr (hload chunk ofs v hl)
    refine ⟨hglob, hbm'', ?_⟩
    intro ofs hp
    apply hperm ofs
    exact Mem.perm_alloc_4 m z0 sz m' sp halloc b ofs .Max .Writable hp
      (by intro heq; subst b; apply Plt_strict m.nextblock; exact hsp ▸ hbelow)
  have hmm' : mmatch bc' m' mfunction_entry := by
    constructor
    · intro b hb
      have hbs : b = sp := bc'.bc_stack b sp hb (by simp [bc', f])
      subst b
      simpa [mfunction_entry] using (pg_alloc_stack_undef_bmatch bc' m m' sp sz halloc)
    · intro id ab b hb hget
      have hbcold : bc b = BCglob id := by
        by_cases hbs : b = sp
        · subst b; simp [bc', f] at hb
        · simpa [bc', f, hbs] using hb
      change PTree.get id (PTree.empty ablock) = some ab at hget
      have hnone : PTree.get id (PTree.empty ablock) = none := PTree.gempty _ _
      rw [hnone] at hget
      cases hget
    · intro b hb1 hb2
      have hbcold2 : bc b ≠ BCinvalid := by
        intro hi
        apply hb2
        by_cases hbs : b = sp
        · subst b; exact False.elim (hb1 (by simp [bc', f]))
        · rw [show bc' b = bc b by simp [bc', f, hbs]]
          exact hi
      have hbcold1 : bc b ≠ BCstack := by
        intro hs
        by_cases hbs : b = sp
        · subst b; exact hbcold2 hspinvalid
        · have hb' : bc' b = BCstack := by rw [show bc' b = bc b by simp [bc', f, hbs]]; exact hs
          have : b = sp := bc'.bc_stack b sp hb' (by simp [bc', f])
          exact hbs this
      have hbelow : Plt b m.nextblock := hmm.mmatch_below b hbcold2
      have hsm := smatch_no_stack bc hnostack m b am.am_nonstack
        (hmm.mmatch_nonstack b hbcold1 hbcold2)
      have hsm' := pg_alloc_preserve_smatch bc m m' b Nonstack sp sz halloc hbelow hsm
      exact pg_smatch_incr bc bc' m' b Nonstack hincr hsm'
    · intro b hb
      by_cases hbs : b = sp
      · subst b
        exact pg_alloc_stack_undef_smatch bc' m m' sp sz halloc
      · have hbcold : bc b ≠ BCinvalid := by
          intro hi
          apply hb
          rw [show bc' b = bc b by simp [bc', f, hbs], hi]
        have hbelow : Plt b m.nextblock := hmm.mmatch_below b hbcold
        have hsm := smatch_no_stack bc hnostack m b am.am_top
          (hmm.mmatch_top b hbcold)
        have hsm' := pg_alloc_preserve_smatch bc m m' b Nonstack sp sz halloc hbelow hsm
        exact pg_smatch_incr bc bc' m' b Nonstack hincr hsm'
    · intro b hb
      by_cases hbs : b = sp
      · subst b
        exact Mem.valid_new_block m z0 sz m' sp halloc
      · have hbcold : bc b ≠ BCinvalid := by
          intro hi
          apply hb
          rw [show bc' b = bc b by simp [bc', f, hbs], hi]
        have hbelow := hmm.mmatch_below b hbcold
        exact Plt_Ple_trans _ _ _ hbelow (by rw [hnext]; exact Ple_succ _)
  have hsame : ∀ b, Plt b sp → bc' b = bc b := by
    intro b hb
    have hne : b ≠ sp := by intro heq; subst b; exact Plt_strict _ hb
    dsimp [bc']
    exact if_neg hne
  have hvm : ∀ v x, vmatch bc v x → vmatch bc' v (Ifptr Nonstack) := by
    intro v x hv
    exact pg_vmatch_incr bc bc' v (Ifptr Nonstack) hincr
      (vmatch_no_stack bc hnostack v x hv)
  refine ⟨bc', hincr, ?_, hgenv', hrom', hmm', hsame, hvm⟩
  · simp [bc', f]

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem return_from_private_call : return_from_private_callStatement := by
  classical
  intro caller callee bound sp ge e ae v m rm am
    hbelow hcallee_sp hcaller_sp hsame hge_caller hem hcontents hbound
    hresult hrom hmm hge_callee hnostack
  let f : block → block_class := fun b => if b = sp then BCstack else callee b
  have hfstack : ∀ b, f b = BCstack → b = sp := by
    intro b hb
    by_cases hbs : b = sp
    · exact hbs
    · exact False.elim (hnostack b (by simpa [f, hbs] using hb))
  have hfglob : ∀ b id, f b = BCglob id ↔ callee b = BCglob id := by
    intro b id
    by_cases hbs : b = sp
    · subst b
      simp [f, hcallee_sp]
    · simp [f, hbs]
  let bc : block_classification :=
    { bc_img := f
      bc_stack := fun b1 b2 h1 h2 => (hfstack b1 h1).trans (hfstack b2 h2).symm
      bc_glob := fun b1 b2 id h1 h2 =>
        callee.bc_glob b1 b2 id ((hfglob b1 id).1 h1) ((hfglob b2 id).1 h2) }
  have hbc_sp : bc sp = BCstack := by simp [bc, f]
  have hbc_other : ∀ b, b ≠ sp → bc b = callee b := by
    intro b hb
    simp [bc, f, hb]
  have hincr_caller : bc_incr caller bc := by
    intro b hb
    by_cases hbs : b = sp
    · subst b
      exact hbc_sp.trans hcaller_sp.symm
    · exact (hbc_other b hbs).trans (hsame b (hbelow b hb) hbs).symm
  have hincr_callee : bc_incr callee bc := by
    intro b hb
    by_cases hbs : b = sp
    · subst b
      exact False.elim (hb hcallee_sp)
    · exact hbc_other b hbs
  have hspbelow : Plt sp bound := hbelow sp (by simp [hcaller_sp])
  have hbstack : bmatch bc m sp am.am_stack := by
    constructor
    · exact pg_smatch_incr caller bc m sp am.am_stack.ab_summary
        hincr_caller hcontents.1
    · intro chunk ofs w hw
      exact pg_vmatch_incr caller bc w _ hincr_caller (hcontents.2 chunk ofs w hw)
  have hsm : ∀ b p, smatch callee m b p → smatch bc m b Nonstack := by
    intro b p hb
    exact pg_smatch_incr callee bc m b Nonstack hincr_callee
      (smatch_no_stack callee hnostack m b p hb)
  have hglob : ∀ b id, bc b = BCglob id ↔ callee b = BCglob id := hfglob
  have hge : genv_match bc ge := by
    apply anonymize_genv_match_exten ge callee bc hge_callee
    · intro b id
      exact (hglob b id).symm
    · intro b hb
      have hbs : b ≠ sp := by
        intro heq
        subst b
        rw [hcallee_sp] at hb
        cases hb
      exact (hbc_other b hbs).trans hb
  have hmem : mmatch bc m (mafter_private_call am) := by
    constructor
    · intro b hb
      have hbs : b = sp := bc.bc_stack b sp hb hbc_sp
      subst b
      exact hbstack
    · intro id ab b hb hget
      change PTree.get id (PTree.empty ablock) = some ab at hget
      have hnone : PTree.get id (PTree.empty ablock) = none := PTree.gempty _ _
      rw [hnone] at hget
      cases hget
    · intro b hns hni
      have hbs : b ≠ sp := by intro heq; subst b; exact hns hbc_sp
      have hni' : callee b ≠ BCinvalid := by rwa [hbc_other b hbs] at hni
      exact hsm b _ (hmm.mmatch_nonstack b (hnostack b) hni')
    · intro b hni
      change smatch bc m b (plub am.am_stack.ab_summary Nonstack)
      by_cases hbs : b = sp
      · subst b
        exact smatch_ge bc m sp _ _ hbstack.1 (pge_lub_l _ _)
      · have hni' : callee b ≠ BCinvalid := by rwa [hbc_other b hbs] at hni
        exact smatch_ge bc m b _ _ (hsm b _ (hmm.mmatch_top b hni'))
          (pge_lub_r _ _)
    · intro b hni
      by_cases hbs : b = sp
      · subst b
        exact Plt_Ple_trans sp bound m.nextblock hspbelow hbound
      · exact hmm.mmatch_below b (by rwa [hbc_other b hbs] at hni)
  refine ⟨bc, ?_, ?_, ?_, hmem, hge, hbc_sp, ?_⟩
  · exact pg_vmatch_incr callee bc v (Ifptr Nonstack) hincr_callee
      (vmatch_no_stack callee hnostack v Vtop hresult)
  · intro r
    exact pg_vmatch_incr caller bc _ (AE.get r ae) hincr_caller (hem r)
  · exact anonymize_romatch_exten callee bc m rm hrom hglob
  · intro b hb
    have hbs : b ≠ sp := by intro heq; subst b; exact Plt_strict sp hb
    exact (hbc_other b hbs).trans (hsame b (Plt_trans b sp bound hb hspbelow) hbs).symm

end CompCert4Lean.Backend.ValueAnalysis
namespace CompCert4Lean.Backend.ValueAnalysis
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Coqlib

theorem sound_stack_ext
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    sound_stack_extStatement := by
  intro cfg prog ge m' bc stk m bound hstk
  induction hstk with
  | sound_stack_nil =>
      rename_i bcNil mNil boundNil
      intro _
      exact sound_stack_nil (cfg := cfg) (prog := prog) (ge := ge) bcNil m' boundNil
  | sound_stack_public_call =>
      rename_i bcOuter res f sp pc e stkInner mInner boundInner bc0 bound0 ae stkProof incr below spClass spClass' same geMatch analyze ematch ih
      intro INV
      have hspBelow : Plt sp bound0 := by
        apply below
        simp [spClass']
      have hstk' : sound_stack cfg prog ge bc0 stkInner m' sp := by
        apply ih
        intro b ofs n bytes hb hbinv hn hload
        have hb0 : Plt b bound0 := Plt_trans b sp bound0 hb hspBelow
        have hne : b ≠ sp := by
          intro heq
          subst b
          exact Plt_strict _ hb
        have houter : bcOuter b = BCinvalid := by
          rw [same b hb0 hne]
          exact hbinv
        exact INV b ofs n bytes (Plt_Ple_trans b bound0 boundInner hb0 incr)
          houter hn hload
      exact sound_stack_public_call
        (cfg := cfg) (prog := prog) (ge := ge)
        (bc := bcOuter) (res := res) (f := f) (sp := sp) (pc := pc) (e := e)
        (stk := stkInner) (m := m') (bound := boundInner)
        (bc' := bc0) (bound' := bound0) (ae := ae)
        (STK := hstk') (INCR := incr) (BELOW := below)
        (SP := spClass) (SP' := spClass') (SAME := same) (GE := geMatch)
        (AN := analyze) (EM := ematch)
  | sound_stack_private_call =>
      rename_i bcOuter res f sp pc e stkInner mInner boundInner bc0 bound0 ae am stkProof incr below spClass spClass' same geMatch analyze ematch contents ih
      intro INV
      have hspBelow : Plt sp bound0 := by
        apply below
        simp [spClass']
      have hstk' : sound_stack cfg prog ge bc0 stkInner m' sp := by
        apply ih
        intro b ofs n bytes hb hbinv hn hload
        have hb0 : Plt b bound0 := Plt_trans b sp bound0 hb hspBelow
        have hne : b ≠ sp := by
          intro heq
          subst b
          exact Plt_strict _ hb
        have houter : bcOuter b = BCinvalid := by
          rw [same b hb0 hne]
          exact hbinv
        exact INV b ofs n bytes (Plt_Ple_trans b bound0 boundInner hb0 incr)
          houter hn hload
      have hspBound : Plt sp boundInner :=
        Plt_Ple_trans sp bound0 boundInner hspBelow incr
      have hcontents' : bmatch bc0 m' sp am.am_stack := by
        apply bmatch_ext bc0 mInner sp am.am_stack m' contents
        intro ofs n bytes hload hn
        exact INV sp ofs n bytes hspBound spClass hn hload
      exact sound_stack_private_call
        (cfg := cfg) (prog := prog) (ge := ge)
        (bc := bcOuter) (res := res) (f := f) (sp := sp) (pc := pc) (e := e)
        (stk := stkInner) (m := m') (bound := boundInner)
        (bc' := bc0) (bound' := bound0) (ae := ae) (am := am)
        (STK := hstk') (INCR := incr) (BELOW := below)
        (SP := spClass) (SP' := spClass') (SAME := same) (GE := geMatch)
        (AN := analyze) (EM := ematch) (CONTENTS := hcontents')

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

theorem sound_stack_inv
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    sound_stack_invStatement := by
  intro cfg prog ge m' bc stk m bound hstk hinv
  apply sound_stack_ext
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    cfg prog ge m' bc stk m bound hstk
  intro b ofs n bytes hb hbc hn hload
  rw [← hinv b ofs n hb hbc hn]
  exact hload

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Integers

theorem sound_stack_storev
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    sound_stack_storevStatement := by
  intro cfg prog ge chunk m addr v m' bc aaddr stk bound hstore hvmatch hstk
  apply sound_stack_inv
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    cfg prog ge m' bc stk m bound hstk
  intro b ofs n hbound hbinv hnonneg
  cases addr with
  | Vundef =>
      simp [Mem.storev] at hstore
  | Vint i =>
      simp [Mem.storev] at hstore
  | Vlong i =>
      simp [Mem.storev] at hstore
  | Vfloat f =>
      simp [Mem.storev] at hstore
  | Vsingle f =>
      simp [Mem.storev] at hstore
  | Vptr b0 ofs0 =>
      change Mem.store chunk m b0 (Ptrofs.unsigned ofs0) v = some m' at hstore
      have htop : pmatch bc b0 ofs0 Ptop := by
        cases hvmatch with
        | ptr _ _ p hp =>
            exact pmatch_top' bc b0 ofs0 p hp
        | ifptrPtr _ _ p hp =>
            exact pmatch_top' bc b0 ofs0 p hp
      have hnotinvalid : bc b0 ≠ BCinvalid := by
        cases htop with
        | top h => exact h
      have hne : b ≠ b0 := by
        intro heq
        subst b
        exact hnotinvalid hbinv
      apply Mem.loadbytes_store_other chunk m b0 (Ptrofs.unsigned ofs0) v m'
        hstore b ofs n
      exact Or.inl hne

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Integers

theorem sound_stack_storebytes
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    sound_stack_storebytesStatement := by
  intro cfg prog ge m b ofs bytes m' bc aaddr stk bound hstore hvmatch hstk
  apply sound_stack_inv
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    cfg prog ge m' bc stk m bound hstk
  intro b' ofs' n hbound hbinv hnonneg
  have htop : pmatch bc b ofs Ptop := by
    cases hvmatch with
    | ptr _ _ p hp =>
        exact pmatch_top' bc b ofs p hp
    | ifptrPtr _ _ p hp =>
        exact pmatch_top' bc b ofs p hp
  have hnotinvalid : bc b ≠ BCinvalid := by
    cases htop with
    | top h => exact h
  have hne : b' ≠ b := by
    intro heq
    subst b'
    exact hnotinvalid hbinv
  apply Mem.loadbytes_storebytes_other m b (Ptrofs.unsigned ofs) bytes m' hstore b' ofs' n
    hnonneg
  exact Or.inl hne

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Integers

theorem sound_stack_free
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    sound_stack_freeStatement := by
  intro cfg prog ge m b lo hi m' bc stk bound hfree hstk
  apply sound_stack_ext
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    cfg prog ge m' bc stk m bound hstk
  intro b' ofs n bytes hbound hbinv hnonneg hload
  exact Mem.loadbytes_free_2 m b lo hi m' hfree b' ofs n bytes hload

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps

theorem store_zeros_same : store_zeros_sameStatement := by
  intro bc p m b pos n m' hzeros hmatch
  let P : mem → block → Z → Z → Option mem → Prop :=
    fun m0 b0 _ _ result =>
      ∀ p0, smatch bc m0 b0 p0 →
        match result with
        | some m1 => smatch bc m1 b0 p0
        | none => True
  have hP : ∀ m0 b0 p0 n0, P m0 b0 p0 n0 (store_zeros m0 b0 p0 n0) := by
    apply store_zeros_ind (P := P)
    · intro m0 b0 p0 n0 x hx
      intro p1 hsm
      exact hsm
    · intro m0 b0 p0 n0 x hx m1 hstore hrec
      cases hresult : store_zeros m1 b0 (zAdd p0 (.Zpos .xH))
          (ZArith.BinInt.Z.sub n0 (.Zpos .xH)) with
      | none => simp [P]
      | some m2 =>
          rw [hresult] at hrec
          intro p1 hsm
          apply hrec p1
          have hvzero : vmatch bc Vzero
              (I CompCert4Lean.Lib.Integers.Int.zero) := by
            exact vmatch.vmatch_i _
          exact smatch_store bc Mint8unsigned m0 b0 p0 Vzero m1 b0 p1
            (I CompCert4Lean.Lib.Integers.Int.zero) hstore hsm hvzero
    · intro m0 b0 p0 n0 x hx hnone
      intro p1 hsm
      trivial
  have hs := hP m b pos n
  rw [hzeros] at hs
  exact hs p hmatch

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis.DS

theorem fixpoint_entry_proof {cfg : CompCert4Lean.Config.CompilerConfig}
    (laws : law_obligation cfg) : fixpoint_entry laws := by
  intro A code successors transf ep ev res hfix
  exact CompCert4Lean.Backend.Kildall.Dataflow_Solver.fixpoint_entry
    (L cfg) CompCert4Lean.Backend.Kildall.NodeSetForward laws.1 laws.2
    code successors transf ep ev res hfix

end CompCert4Lean.Backend.ValueAnalysis.DS

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Kildall
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem va_sumbool_eq {Value : Type} (first second : Value)
    (comparison : CompCert4Lean.Foundation.Logic.Support.Sumbool
      (first = second) (first ≠ second))
    (equal : proj_sumbool comparison = true) : first = second := by
  cases comparison with
  | left same => exact same
  | right different => cases equal

private theorem va_tree_beq_eq {Value : Type} (compare : Value → Value → Bool)
    (correct : ∀ first second, compare first second = true → first = second)
    (first second : PTree.t Value) (equal : PTree.beq compare first second = true) :
    first = second := by
  apply PTree.extensionality
  intro index
  have compared := (PTree.beq_correct_proof compare first second).mp equal index
  cases found_first : PTree.get index first <;>
    cases found_second : PTree.get index second <;>
    simp only [found_first, found_second] at compared ⊢
  exact congrArg some (correct _ _ compared)

private theorem va_bbeq_eq (first second : ablock)
    (equal : bbeq first second = true) : first = second := by
  have parts : proj_sumbool (eq_aptr first.ab_summary second.ab_summary) = true ∧
      ZTree.beq (fun left right => proj_sumbool (eq_acontent left right))
        first.ab_contents second.ab_contents = true := by
    simpa only [bbeq, Bool.and_eq_true] using equal
  obtain ⟨summary, contents⟩ := parts
  have same_summary := va_sumbool_eq _ _ (eq_aptr _ _) summary
  have same_contents := va_tree_beq_eq _
    (fun left right => va_sumbool_eq left right (eq_acontent left right))
    first.ab_contents second.ab_contents contents
  cases first
  cases second
  simp_all

private theorem va_mbeq_eq (first second : amem)
    (equal : mbeq first second = true) : first = second := by
  simp only [mbeq, Bool.and_eq_true] at equal
  obtain ⟨⟨⟨top, nonstack⟩, stack⟩, globals⟩ := equal
  have same_top := va_sumbool_eq _ _ (eq_aptr _ _) top
  have same_nonstack := va_sumbool_eq _ _ (eq_aptr _ _) nonstack
  have same_stack := va_bbeq_eq _ _ stack
  have same_globals := va_tree_beq_eq bbeq va_bbeq_eq _ _ globals
  cases first
  cases second
  simp_all

private theorem va_ae_beq_eq (first second : aenv)
    (equal : AE.beq first second = true) : AE.eq first second := by
  cases first with
  | Bot => cases second <;> simp_all [AE.beq, AE.eq]
  | Top_except first_tree =>
      cases second with
      | Bot => cases equal
      | Top_except second_tree =>
          have same := va_tree_beq_eq _
            (fun left right => va_sumbool_eq left right (eq_aval left right))
            first_tree second_tree equal
          subst second_tree
          intro register
          rfl

private theorem va_vge_refl (value : aval) : vge value value := by
  cases value <;> try constructor
  all_goals first
    | exact ZArith.BinInt.Z.le_refl _
    | exact pge.pge_refl _

private theorem va_vge_top (value : aval) : vge Vtop value := by
  cases value <;> constructor <;> exact pge.pge_top _

private theorem va_ae_lub_ge (cfg : CompilerConfig) (first second : aenv) :
    AE.ge (AE.lub cfg first second) first ∧ AE.ge (AE.lub cfg first second) second := by
  cases first with
  | Bot => exact ⟨fun _ => .bot _, fun _ => va_vge_refl _⟩
  | Top_except first_tree =>
      cases second with
      | Bot => exact ⟨fun _ => va_vge_refl _, fun _ => .bot _⟩
      | Top_except second_tree =>
          have bounds : ∀ register,
              vge (AE.get register (AE.lub cfg (.Top_except first_tree) (.Top_except second_tree)))
                (AE.get register (.Top_except first_tree)) ∧
              vge (AE.get register (AE.lub cfg (.Top_except first_tree) (.Top_except second_tree)))
                (AE.get register (.Top_except second_tree)) := by
            intro register
            simp only [AE.lub, AE.get, AE.LM.combine]
            rw [PTree.gcombine_proof _ rfl]
            cases first_found : PTree.get register first_tree with
            | none =>
                cases second_found : PTree.get register second_tree <;>
                  exact ⟨va_vge_top _, va_vge_top _⟩
            | some first_value =>
                cases second_found : PTree.get register second_tree with
                | none => exact ⟨va_vge_top _, va_vge_top _⟩
                | some second_value =>
                    simp only [AE.opt_lub]
                    split
                    · exact ⟨va_vge_top _, va_vge_top _⟩
                    · exact ⟨vge_lub_l cfg first_value second_value,
                        vge_lub_r cfg first_value second_value⟩
          exact ⟨fun register => (bounds register).1, fun register => (bounds register).2⟩

theorem solver_law_obligation_proof (cfg : CompilerConfig) : solver_law_obligation cfg := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_, VA.ge_trans, ?_, ?_, ?_⟩
    · intro value
      cases value <;> simp [va_lat, VA.eq, AE.eq]
    · intro first second equal
      cases first <;> cases second <;>
        simp only [va_lat, VA.eq] at equal ⊢ <;> try contradiction <;> try trivial
      exact ⟨fun register => (equal.1 register).symm,
        fun classification memory => (equal.2 classification memory).symm⟩
    · intro first second third first_second second_third
      cases first <;> cases second <;> cases third <;>
        simp only [va_lat, VA.eq] at * <;> try contradiction <;> try trivial
      exact ⟨fun register => (first_second.1 register).trans (second_third.1 register),
        fun classification memory => (first_second.2 classification memory).trans
          (second_third.2 classification memory)⟩
    · intro first second equal
      cases first <;> cases second <;>
        simp only [va_lat, VA.beq, VA.eq, Bool.and_eq_true] at equal ⊢ <;>
        try contradiction <;> try trivial
      have same_memory := va_mbeq_eq _ _ equal.2
      exact ⟨va_ae_beq_eq _ _ equal.1, by simp only [same_memory, iff_self, implies_true]⟩
    · intro first second equal
      cases first <;> cases second <;>
        simp only [va_lat, VA.eq, VA.ge] at equal ⊢ <;>
        try contradiction <;> try trivial
      refine ⟨?_, fun classification memory => (equal.2 classification memory).mpr⟩
      intro register
      rw [equal.1 register]
      exact va_vge_refl _
    · intro value
      cases value <;> trivial
    · intro first second
      cases first <;> cases second <;>
        simp only [va_lat, VA.lub, VA.ge] <;> try trivial
      · exact ⟨fun _ => va_vge_refl _, fun _ _ matched => matched⟩
      · exact ⟨(va_ae_lub_ge cfg _ _).1,
          fun classification memory => mmatch_lub_l cfg classification memory _ _⟩
    · intro first second
      cases first <;> cases second <;>
        simp only [va_lat, VA.lub, VA.ge] <;> try trivial
      · exact ⟨fun _ => va_vge_refl _, fun _ _ matched => matched⟩
      · exact ⟨(va_ae_lub_ge cfg _ _).2,
          fun classification memory => mmatch_lub_r cfg classification memory _ _⟩
  · exact NodeSetForward.law_obligation_proof

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Lib.Maps

theorem analyze_entrypoint
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    analyze_entrypointStatement := by
  intro cfg readonly body values memory classification arguments typed matched
  have initial_match := ematch_init classification body.fn_params values
    body.fn_sig.sig_args typed arguments
  unfold analyze
  dsimp only
  split
  · refine ⟨AE.top, mtop, ?_, ?_, mmatch_top' classification memory _ matched⟩
    · rfl
    · exact ematch_ge classification _ _ _ initial_match (AE.ge_top_proof _)
  · rename_i solution fixed
    have above := DS.fixpoint_entry_proof (solver_law_obligation_proof cfg)
      instruction body.fn_code successors_instr
      (transfer' cfg body (CompCert4Lean.Backend.Liveness.last_uses body) readonly)
      body.fn_entrypoint
      (VA.State (einit_regs body.fn_params body.fn_sig.sig_args) mfunction_entry)
      solution fixed
    change VA.ge (PMap.get body.fn_entrypoint solution)
      (VA.State (einit_regs body.fn_params body.fn_sig.sig_args) mfunction_entry) at above
    cases current : PMap.get body.fn_entrypoint solution with
    | Bot =>
        erw [current] at above
        exact False.elim above
    | State environment abstract_memory =>
        erw [current] at above
        exact ⟨environment, abstract_memory, current,
          ematch_ge classification _ _ _ initial_match above.1,
          above.2 classification memory matched⟩

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Lib.Maps

theorem analyze_successor
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    analyze_successorStatement := by
  intro cfg body current environment abstract_memory instr successor readonly
    next_environment next_memory analyzed code member transferred
  unfold analyze at analyzed ⊢
  dsimp only at analyzed ⊢
  split at analyzed
  · rename_i fixed
    erw [transferred]
    exact ⟨AE.ge_top_proof _, fun classification memory => mmatch_top' classification memory _⟩
  · rename_i solution fixed
    have above := DS.fixpoint_solution_proof (solver_law_obligation_proof cfg)
      instruction body.fn_code successors_instr
      (transfer' cfg body (CompCert4Lean.Backend.Liveness.last_uses body) readonly)
      body.fn_entrypoint
      (VA.State (einit_regs body.fn_params body.fn_sig.sig_args) mfunction_entry)
      solution current instr successor fixed code member (by intro query; trivial)
    change VA.ge (PMap.get successor solution)
      (transfer' cfg body (CompCert4Lean.Backend.Liveness.last_uses body) readonly current
        (PMap.get current solution)) at above
    erw [analyzed] at above
    unfold transfer' at above
    dsimp only at above
    erw [transferred] at above ⊢
    dsimp only at above
    cases forgotten : PTree.get current (CompCert4Lean.Backend.Liveness.last_uses body) with
    | none =>
        erw [forgotten] at above
        exact above
    | some registers =>
        erw [forgotten] at above
        apply VA.ge_trans _ _ _ above
        exact ⟨eforget_ge registers next_environment, fun _ _ matched => matched⟩

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Lib.Maps

theorem analyze_succ
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    analyze_succStatement := by
  intro cfg registers memory readonly body current environment abstract_memory instr successor
    next_environment next_memory classification analyzed code member transferred
    environment_match memory_match
  have above := analyze_successor cfg body current environment abstract_memory instr successor
    readonly next_environment next_memory analyzed code member transferred
  erw [transferred] at above
  cases found : PMap.get successor (analyze cfg readonly body) with
  | Bot =>
      erw [found] at above
      exact False.elim above
  | State successor_environment successor_memory =>
      erw [found] at above
      exact ⟨successor_environment, successor_memory, rfl,
        ematch_ge classification registers _ _ environment_match above.1,
        above.2 classification memory memory_match⟩

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers

set_option maxHeartbeats 2000000 in
private theorem va_longofwords_match (classification : block_classification)
    (first_value second_value : val) (first second : aval)
    (first_match : vmatch classification first_value first)
    (second_match : vmatch classification second_value second) :
    vmatch classification (Val.longofwords first_value second_value) (longofwords first second) := by
  cases first_match <;> cases second_match <;>
    simp only [Val.longofwords, longofwords, ntop2]
  all_goals first
    | exact vmatch.long _
    | exact vmatch.numUndef _
    | exact vmatch.numLong _ _

private theorem va_addl_match (classification : block_classification)
    (first_value second_value : val) (first second : aval)
    (first_match : vmatch classification first_value first)
    (second_match : vmatch classification second_value second) :
    vmatch classification (Val.addl first_value second_value) (addl first second) := by
  run_tac
    let environment ← Lean.getEnv
    let some (proofName, _) := environment.constants.toList.find?
        (fun (name, _) => name.toString.endsWith ".CompCert4Lean.X86.ValueAOp.addr64_add_match")
      | throwError "Checked 64-bit abstract addition proof unavailable"
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply $(Lean.mkIdent proofName) <;> assumption))

theorem abuiltin_arg_sound : abuiltin_arg_soundStatement := by
  intro cfg classification globals registers stack memory environment readonly abstract_memory
    environment_match readonly_match memory_match global_match stack_match argument value evaluated
  induction evaluated with
  | eval_BA register => exact areg_sound classification registers environment register environment_match
  | eval_BA_int integer => exact .vmatch_i integer
  | eval_BA_long integer => exact .long integer
  | eval_BA_float number => exact .float number
  | eval_BA_single number => exact .single number
  | eval_BA_loadstack chunk offset value loaded =>
      apply loadv_sound cfg classification chunk memory _ value readonly abstract_memory _
        loaded readonly_match memory_match
      simpa only [Val.offset_ptr, pg_static_ptrofs_zero_add] using
        (vmatch.ptr stack offset (Stk offset) (pmatch.stk stack_match))
  | eval_BA_addrstack offset =>
      simpa only [Val.offset_ptr, pg_static_ptrofs_zero_add, abuiltin_arg] using
        (vmatch.ptr stack offset (Stk offset) (pmatch.stk stack_match))
  | eval_BA_loadglobal chunk identifier offset value loaded =>
      apply loadv_sound cfg classification chunk memory _ value readonly abstract_memory _
        loaded readonly_match memory_match
      exact symbol_address_sound classification globals identifier offset global_match
  | eval_BA_addrglobal identifier offset =>
      exact symbol_address_sound classification globals identifier offset global_match
  | eval_BA_splitlong high low high_value low_value _ _ high_match low_match =>
      exact va_longofwords_match classification high_value low_value _ _ high_match low_match
  | eval_BA_addptr first_arg second_arg first_value second_value _ _ first_match second_match =>
      exact va_addl_match classification first_value second_value _ _ first_match second_match

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

theorem abuiltin_args_sound : abuiltin_args_soundStatement := by
  intro cfg classification globals registers stack memory environment readonly abstract_memory
    environment_match readonly_match memory_match global_match stack_match arguments values evaluated
  induction evaluated with
  | nil => exact .nil _
  | cons argument value head tail induction_hypothesis =>
      exact .cons _ _
        (abuiltin_arg_sound cfg classification globals registers stack memory environment
          readonly abstract_memory environment_match readonly_match memory_match global_match
          stack_match argument value head)
        induction_hypothesis

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.ValueDomain

theorem aaddr_arg_sound_1 : aaddr_arg_sound_1Statement := by
  intro cfg classification registers environment memory readonly abstract_memory globals stack
    argument source offset environment_match readonly_match memory_match global_match stack_match
    evaluated
  have matched := abuiltin_arg_sound cfg classification globals registers stack memory environment
    readonly abstract_memory environment_match readonly_match memory_match global_match stack_match
    argument _ evaluated
  have pointer_match := match_aptr_of_aval cfg classification source offset _ matched
  cases argument <;> first
    | exact pointer_match
    | exact pmatch_top' classification source offset _ pointer_match

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

theorem aaddr_arg_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    aaddr_arg_soundStatement := by
  intro cfg compilation_unit program frames body stack current registers memory argument source
    offset sound linked evaluated
  have invariant := sound_state_inv cfg program _ compilation_unit sound linked
  cases invariant
  rename_i environment abstract_memory classification global_match stack_match analyzed
    environment_match readonly_match memory_match stack_sound
  refine ⟨classification, ?_, global_match, stack_match⟩
  erw [analyzed]
  exact aaddr_arg_sound_1 cfg classification registers environment memory
    (romem_for cfg compilation_unit) abstract_memory _ stack argument source offset
    environment_match readonly_match memory_match global_match stack_match evaluated

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Globalenvs

theorem aaddressing_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    aaddressing_soundStatement := by
  intro cfg compilation_unit program frames body stack current registers memory address arguments
    source offset sound linked evaluated
  have invariant := sound_state_inv cfg program _ compilation_unit sound linked
  cases invariant
  rename_i environment abstract_memory classification global_match stack_match analyzed
    environment_match readonly_match memory_match stack_sound
  refine ⟨classification, ?_, global_match, stack_match⟩
  erw [analyzed]
  apply match_aptr_of_aval cfg classification source offset
  exact CompCert4Lean.X86.ValueAOp.eval_static_addressing_sound classification
    (Genv.globalenv program) global_match stack stack_match address _ _ (aregs environment arguments)
    evaluated (aregs_sound classification registers environment arguments environment_match)

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

theorem sound_succ_state
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    sound_succ_stateStatement := by
  intro cfg program globals classification current environment abstract_memory instr next_environment
    next_memory frames body stack successor registers memory analyzed code member transferred
    environment_match memory_match readonly_match global_match stack_match stack_sound
  obtain ⟨successor_environment, successor_memory, successor_analyzed, successor_registers,
    successor_matched⟩ := analyze_succ cfg registers memory (romem_for cfg program) body current
      environment abstract_memory instr successor next_environment next_memory classification
      analyzed code member transferred environment_match memory_match
  exact sound_regular_state frames body stack successor registers memory successor_environment
    successor_memory classification stack_sound successor_analyzed successor_registers readonly_match
    successor_matched global_match stack_match

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values

theorem store_init_data_sound : store_init_data_soundStatement := by
  intro cfg program classification memory source position datum result abstract_block
    global_match stored matched
  cases datum with
  | Init_int8 integer =>
      exact ablock_store_sound classification _ memory source position _ result abstract_block _
        stored matched (.vmatch_i integer)
  | Init_int16 integer =>
      exact ablock_store_sound classification _ memory source position _ result abstract_block _
        stored matched (.vmatch_i integer)
  | Init_int32 integer =>
      exact ablock_store_sound classification _ memory source position _ result abstract_block _
        stored matched (.vmatch_i integer)
  | Init_int64 integer =>
      exact ablock_store_sound classification _ memory source position _ result abstract_block _
        stored matched (.long integer)
  | Init_float32 number =>
      apply ablock_store_sound classification _ memory source position _ result abstract_block _
        stored matched
      change vmatch classification (Vsingle number)
        (if CompCert4Lean.Driver.Compopts.propagate_float_constants cfg then FS number else ntop)
      split
      · exact .single number
      · exact .numSingle number _
  | Init_float64 number =>
      apply ablock_store_sound classification _ memory source position _ result abstract_block _
        stored matched
      change vmatch classification (Vfloat number)
        (if CompCert4Lean.Driver.Compopts.propagate_float_constants cfg then F number else ntop)
      split
      · exact .float number
      · exact .numFloat number _
  | Init_addrof identifier offset =>
      unfold Genv.store_init_data at stored
      dsimp only at stored
      split at stored
      · contradiction
      · rename_i target found
        exact ablock_store_sound classification _ memory source position _ result abstract_block _
          stored matched (.ptr target offset _ (.gl identifier ((global_match.1 identifier target).mp found)))
  | Init_space size =>
      change some memory = some result at stored
      cases stored
      exact matched

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs

theorem store_init_data_list_sound : store_init_data_list_soundStatement := by
  intro cfg program classification data
  induction data with
  | nil =>
      intro memory source position result abstract_block global_match stored matched
      change some memory = some result at stored
      cases stored
      exact matched
  | cons datum rest induction_hypothesis =>
      intro memory source position result abstract_block global_match stored matched
      unfold Genv.store_init_data_list at stored
      split at stored
      · contradiction
      · rename_i intermediate first_stored
        exact induction_hypothesis intermediate source (zAdd position (init_data_size datum))
          result (store_init_data cfg abstract_block position datum) global_match stored
          (store_init_data_sound cfg program classification memory source position datum intermediate
            abstract_block global_match first_stored matched)

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem va_add_global_old (globals : genv) (identifier query : ident)
    (definition : globdef fundef Unit) (source : block) (global_variable : globvar Unit)
    (symbol : Genv.find_symbol (Genv.add_global globals (identifier, definition)) query = some source)
    (info : Genv.find_var_info (Genv.add_global globals (identifier, definition)) source = some global_variable)
    (different : source ≠ globals.genv_next) :
    Genv.find_symbol globals query = some source ∧ Genv.find_var_info globals source = some global_variable := by
  constructor
  · change PTree.get query (PTree.set identifier globals.genv_next globals.genv_symb) = some source at symbol
    by_cases same : query = identifier
    · subst query
      erw [PTree.gss] at symbol
      exact False.elim (different (Option.some.inj symbol).symm)
    · erw [PTree.gso _ _ same] at symbol
      exact symbol
  · simp only [Genv.find_var_info, Genv.find_def, Genv.add_global] at info
    erw [PTree.gso _ _ different] at info
    exact info

theorem alloc_global_match : alloc_global_matchStatement := by
  intro cfg program classification global_match memory globals entry result bound initial allocated_global
  obtain ⟨identifier, definition⟩ := entry
  cases definition with
  | Gfun body =>
      let intermediate := (Mem.alloc memory z0 (zOfNat 1)).1
      let fresh := (Mem.alloc memory z0 (zOfNat 1)).2
      have allocated : Mem.alloc memory z0 (zOfNat 1) = (intermediate, fresh) := rfl
      change Mem.drop_perm intermediate fresh z0 (zOfNat 1) .Nonempty = some result at allocated_global
      intro query source global_variable symbol info not_volatile readonly
      by_cases same : source = globals.genv_next
      · simp only [Genv.find_var_info, Genv.find_def, Genv.add_global] at info
        erw [same, PTree.gss] at info
        cases info
      · obtain ⟨old_symbol, old_info⟩ :=
          va_add_global_old globals identifier query (.Gfun body) source global_variable symbol info same
        have below : Plt source memory.nextblock := by
          rw [← bound]
          exact globals.genv_symb_range query old_symbol
        have different : source ≠ fresh := by
          rw [Mem.alloc_result memory z0 (zOfNat 1) intermediate fresh allocated, ← bound]
          exact same
        apply bmatch_inv classification memory source _ result
          (initial query source global_variable old_symbol old_info not_volatile readonly)
        intro offset count nonnegative
        exact (Mem.loadbytes_drop intermediate fresh z0 (zOfNat 1) .Nonempty result
          allocated_global source offset count (.inl different)).trans
          (Mem.loadbytes_alloc_unchanged memory z0 (zOfNat 1) intermediate fresh allocated
            source offset count below)
  | Gvar declared =>
      let size := init_data_list_size declared.gvar_init
      let intermediate := (Mem.alloc memory z0 size).1
      let fresh := (Mem.alloc memory z0 size).2
      have allocated : Mem.alloc memory z0 size = (intermediate, fresh) := rfl
      change (match store_zeros intermediate fresh z0 size with
        | none => none
        | some zeroed => match Genv.store_init_data_list (Genv.globalenv program) zeroed fresh z0 declared.gvar_init with
          | none => none
          | some initialized => Mem.drop_perm initialized fresh z0 size (Genv.perm_globvar declared)) = some result
        at allocated_global
      cases zeroed_eq : store_zeros intermediate fresh z0 size with
      | none => simp only [zeroed_eq] at allocated_global; contradiction
      | some zeroed =>
          simp only [zeroed_eq] at allocated_global
          cases initialized_eq : Genv.store_init_data_list (Genv.globalenv program) zeroed fresh z0 declared.gvar_init with
          | none => simp only [initialized_eq] at allocated_global; contradiction
          | some initialized =>
              simp only [initialized_eq] at allocated_global
              intro query source global_variable symbol info not_volatile readonly
              by_cases same : source = globals.genv_next
              · simp only [Genv.find_var_info, Genv.find_def, Genv.add_global] at info
                erw [same, PTree.gss] at info
                have same_variable : declared = global_variable := Option.some.inj info
                subst global_variable
                have same_fresh : source = fresh := same.trans
                  (bound.trans (Mem.alloc_result memory z0 size intermediate fresh allocated).symm)
                rw [same_fresh]
                have empty_match := (pg_alloc_stack_undef_bmatch classification memory intermediate fresh size allocated).1
                have zeros_match := store_zeros_same classification Pbot intermediate fresh z0 size zeroed zeroed_eq empty_match
                have initialized_match := store_init_data_list_sound cfg program classification declared.gvar_init
                  zeroed fresh z0 initialized (ablock_init Pbot) global_match initialized_eq
                  (ablock_init_sound classification zeroed fresh Pbot zeros_match)
                apply bmatch_inv classification initialized fresh _ result initialized_match
                intro offset count nonnegative
                apply Mem.loadbytes_drop initialized fresh z0 size (Genv.perm_globvar declared) result
                  allocated_global fresh offset count
                right; right; right
                simp only [Genv.perm_globvar, not_volatile, readonly, Bool.false_eq_true,
                  ↓reduceIte]
                exact .perm_refl .Readable
              · obtain ⟨old_symbol, old_info⟩ :=
                  va_add_global_old globals identifier query (.Gvar declared) source global_variable symbol info same
                have below : Plt source memory.nextblock := by
                  rw [← bound]
                  exact globals.genv_symb_range query old_symbol
                have different : source ≠ fresh := by
                  rw [Mem.alloc_result memory z0 size intermediate fresh allocated, ← bound]
                  exact same
                have old_match := initial query source global_variable old_symbol old_info not_volatile readonly
                have allocated_match := pg_alloc_preserve_bmatch classification memory intermediate source _
                  fresh size allocated below old_match
                have zeroed_match := store_zeros_other classification source _ intermediate fresh z0 size zeroed
                  zeroed_eq different allocated_match
                have initialized_match := store_init_data_list_other program classification fresh source _
                  declared.gvar_init zeroed z0 initialized initialized_eq different zeroed_match
                apply bmatch_inv classification initialized source _ result initialized_match
                intro offset count nonnegative
                exact Mem.loadbytes_drop initialized fresh z0 size (Genv.perm_globvar declared) result
                  allocated_global source offset count (.inl different)

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Common.Globalenvs

theorem alloc_globals_match : alloc_globals_matchStatement := by
  intro cfg program classification global_match declarations
  induction declarations with
  | nil =>
      intro memory globals result bound initial allocated
      change some memory = some result at allocated
      cases allocated
      exact initial
  | cons entry rest induction_hypothesis =>
      intro memory globals result bound initial allocated
      unfold Genv.alloc_globals at allocated
      split at allocated
      · contradiction
      · rename_i intermediate first_allocated
        have next := Genv.alloc_global_nextblock fundef Unit (Genv.globalenv program)
          entry memory intermediate first_allocated
        have next_bound : (Genv.add_global globals entry).genv_next = intermediate.nextblock := by
          rw [next]
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ globals.genv_next =
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ memory.nextblock
          exact congrArg _ bound
        exact induction_hypothesis intermediate (Genv.add_global globals entry) result next_bound
          (alloc_global_match cfg program classification global_match memory globals entry intermediate
            bound initial first_allocated) allocated

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Maps

theorem initial_mem_matches : initial_mem_matchesStatement := by
  intro cfg program memory initialized
  obtain ⟨classification, global_match, below, no_stack, symbols, valid⟩ :=
    initial_block_classification program memory initialized
  refine ⟨classification, global_match, below, no_stack, ?_, valid⟩
  intro compilation_unit linked
  have initial : initial_mem_match cfg classification memory (Genv.globalenv program) := by
    apply alloc_globals_match cfg program classification global_match program.prog_defs Mem.empty
      (Genv.empty_genv fundef Unit program.prog_public) memory rfl
    · intro identifier source global_variable symbol info not_volatile readonly
      change PTree.get identifier (PTree.empty block) = some source at symbol
      erw [PTree.gempty] at symbol
      cases symbol
    · exact initialized
  have consistent := romem_for_consistent_2 cfg program compilation_unit linked
  intro source identifier abstract_block global found
  obtain ⟨global_variable, definition, readonly, not_volatile, definitive, abstract_eq⟩ :=
    consistent identifier abstract_block found
  obtain ⟨symbol_block, symbol_found, definition_found⟩ :=
    (Genv.find_def_symbol fundef Unit program identifier (.Gvar global_variable)).mp definition
  have same_block : symbol_block = source :=
    Option.some.inj (symbol_found.symm.trans (symbols source identifier global))
  subst symbol_block
  have info := (Genv.find_var_info_iff fundef Unit (Genv.globalenv program) source global_variable).mpr
    definition_found
  refine ⟨?_, ?_, ?_⟩
  · rw [abstract_eq]
    exact store_init_data_list_summary cfg global_variable.gvar_init (ablock_init Pbot) z0 (.bot Glob)
  · rw [abstract_eq]
    exact initial identifier source global_variable symbol_found info not_volatile readonly
  · have characterization := Genv.init_mem_characterization fundef Unit program source global_variable
      memory info initialized
    intro offset allowed
    have order := (characterization.2.1 offset .Max .Writable allowed).2
    simp only [Genv.perm_globvar, not_volatile, readonly, Bool.false_eq_true, ↓reduceIte] at order
    cases order

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Coqlib

theorem sound_initial
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    sound_initialStatement := by
  intro cfg program current started
  cases started with
  | intro entry callee memory initialized symbol function_found signature =>
      obtain ⟨classification, global_match, below, no_stack, readonly, valid⟩ :=
        initial_mem_matches cfg program memory initialized
      have injection_eq : inj_of_bc classification = Mem.flat_inj memory.nextblock := by
        funext source
        unfold Mem.flat_inj
        cases compared : plt source memory.nextblock with
        | left within => exact inj_of_bc_valid classification source (valid source within)
        | right outside =>
            have invalid := bc_below_invalid source classification memory.nextblock outside below
            simp only [inj_of_bc, invalid]
      have injected : Mem.inject (inj_of_bc classification) memory memory := by
        rw [injection_eq]
        exact Genv.initmem_inject fundef Unit program memory initialized
      refine sound_state_intro _ ?_
      intro compilation_unit linked
      apply sound_call_state [] callee [] memory classification
      · constructor
      · intro value member
        cases member
      · exact readonly compilation_unit linked
      · exact mmatch_inj_top classification memory memory injected
      · exact global_match
      · exact no_stack

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem return_from_public_call : return_from_public_callStatement := by
  classical
  intro caller callee bound stack globals registers environment value memory readonly
    caller_below callee_stack caller_stack same caller_globals environment_match bound_below
    result_match readonly_match memory_match callee_globals no_stack
  let classify : block → block_class := fun source => if source = stack then BCstack else callee source
  have unique_stack : ∀ source, classify source = BCstack → source = stack := by
    intro source stack_class
    by_cases equal : source = stack
    · exact equal
    · exact False.elim (no_stack source (by simpa only [classify, if_neg equal] using stack_class))
  have same_globals : ∀ source identifier,
      classify source = BCglob identifier ↔ callee source = BCglob identifier := by
    intro source identifier
    by_cases equal : source = stack
    · subst source
      simp [classify, callee_stack]
    · simp only [classify, if_neg equal]
  let classification : block_classification :=
    { bc_img := classify
      bc_stack := fun first second first_stack second_stack =>
        (unique_stack first first_stack).trans (unique_stack second second_stack).symm
      bc_glob := fun first second identifier first_global second_global =>
        callee.bc_glob first second identifier ((same_globals first identifier).mp first_global)
          ((same_globals second identifier).mp second_global) }
  have classified_stack : classification stack = BCstack := by simp [classification, classify]
  have unchanged : ∀ source, source ≠ stack → classification source = callee source := by
    intro source different
    simp only [classification, classify, if_neg different]
  have caller_increases : bc_incr caller classification := by
    intro source valid
    by_cases equal : source = stack
    · subst source
      exact classified_stack.trans caller_stack.symm
    · exact (unchanged source equal).trans (same source (caller_below source valid) equal).symm
  have callee_valid : ∀ source, classification source ≠ BCinvalid ↔ callee source ≠ BCinvalid := by
    intro source
    by_cases equal : source = stack
    · subst source
      simp only [classified_stack, callee_stack, ne_eq, reduceCtorEq, not_false_eq_true]
    · rw [unchanged source equal]
  have pointer_top : ∀ source offset pointer, pmatch callee source offset pointer →
      pmatch classification source offset Ptop := by
    intro source offset pointer matched
    cases pmatch_top' callee source offset pointer matched with
    | top valid => exact .top ((callee_valid source).mpr valid)
  have value_top : ∀ concrete abstract, vmatch callee concrete abstract →
      vmatch classification concrete Vtop := by
    intro concrete abstract matched
    cases vmatch_top callee concrete abstract matched <;> constructor
    exact pointer_top _ _ _ ‹_›
  have summary_top : ∀ source pointer, smatch callee memory source pointer →
      smatch classification memory source Ptop := by
    intro source pointer matched
    exact ⟨fun chunk offset concrete loaded => value_top _ _ (matched.1 chunk offset concrete loaded),
      fun offset target target_offset quantity index loaded =>
        pointer_top _ _ _ (matched.2 offset target target_offset quantity index loaded)⟩
  have classified_globals : genv_match classification globals := by
    constructor
    · intro identifier source
      exact (callee_globals.1 identifier source).trans (same_globals source identifier).symm
    · intro source below_globals
      have different : source ≠ stack := by
        intro equal
        subst source
        exact (caller_globals.2 stack below_globals).2 caller_stack
      erw [unchanged source different]
      exact callee_globals.2 source below_globals
  have classified_memory : mmatch classification memory mafter_public_call := by
    constructor
    · intro source stack_class
      exact ablock_init_sound classification memory source Ptop
        (summary_top source _ (memory_match.mmatch_top source
          ((callee_valid source).mp (by simp [stack_class]))))
    · intro identifier abstract_block source global found
      change PTree.get identifier (PTree.empty ablock) = some abstract_block at found
      erw [PTree.gempty] at found
      cases found
    · intro source not_stack valid
      exact summary_top source _ (memory_match.mmatch_top source ((callee_valid source).mp valid))
    · intro source valid
      exact summary_top source _ (memory_match.mmatch_top source ((callee_valid source).mp valid))
    · intro source valid
      exact memory_match.mmatch_below source ((callee_valid source).mp valid)
  refine ⟨classification, value_top _ _ result_match,
    ematch_incr caller classification registers environment environment_match caller_increases,
    anonymize_romatch_exten callee classification memory readonly readonly_match same_globals,
    classified_memory, classified_globals, classified_stack, ?_⟩
  intro source before_stack
  have different : source ≠ stack := Plt_ne source stack before_stack
  have stack_below : Plt stack bound := caller_below stack (by simp [caller_stack])
  exact (unchanged source different).trans
    (same source (Plt_trans source stack bound before_stack stack_below) different).symm

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem external_call_match
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    external_call_matchStatement := by
  classical
  intro providers function globals arguments before trace result after classification readonly abstract_memory
    called global_match argument_match readonly_match memory_match no_stack
  have arguments_injected : Val.inject_list (inj_of_bc classification) arguments arguments := by
    clear called
    induction arguments with
    | nil => exact .inject_list_nil
    | cons first rest induction_hypothesis =>
        exact .inject_list_cons first first rest rest
          (vmatch_inj classification first Vtop (argument_match first (by simp)))
          (induction_hypothesis (fun value member => argument_match value (List.mem_cons_of_mem first member)))
  obtain ⟨injection, injected_result, injected_memory, injected_call, result_injection,
    memory_injection, unmapped_unchanged, unreachable_unchanged, injection_increases, separated⟩ :=
    external_call_mem_inject providers function fundef Unit globals arguments before trace result after
      (inj_of_bc classification) before arguments
      (inj_of_bc_preserves_globals classification globals global_match) called
      (mmatch_inj classification before abstract_memory memory_match memory_match.mmatch_below)
      arguments_injected
  have injection_below : ∀ source, Plt source before.nextblock →
      injection source = inj_of_bc classification source := by
    intro source below
    cases original : inj_of_bc classification source with
    | some destination =>
        obtain ⟨target, delta⟩ := destination
        exact injection_increases source target delta original
    | none =>
        cases extended : injection source with
        | none => rfl
        | some destination =>
            obtain ⟨target, delta⟩ := destination
            exact False.elim ((separated source target delta original extended).1 below)
  let classify : block → block_class := fun source =>
    if Plt source before.nextblock then classification source
    else match injection source with | none => BCinvalid | some _ => BCother
  have classify_old : ∀ source, classification source ≠ BCinvalid → classify source = classification source := by
    intro source valid
    exact if_pos (memory_match.mmatch_below source valid)
  have classify_globals : ∀ source identifier,
      classify source = BCglob identifier ↔ classification source = BCglob identifier := by
    intro source identifier
    by_cases below : Plt source before.nextblock
    · simp only [classify, if_pos below]
    · have invalid := bc_below_invalid source classification before.nextblock below memory_match.mmatch_below
      cases mapped : injection source <;> simp [classify, below, mapped, invalid]
  have classify_no_stack : ∀ source, classify source ≠ BCstack := by
    intro source
    by_cases below : Plt source before.nextblock
    · simpa only [classify, if_pos below] using no_stack source
    · cases mapped : injection source <;> simp [classify, below, mapped]
  let extended : block_classification :=
    { bc_img := classify
      bc_stack := fun first second first_stack second_stack => False.elim (classify_no_stack first first_stack)
      bc_glob := fun first second identifier first_global second_global =>
        classification.bc_glob first second identifier ((classify_globals first identifier).mp first_global)
          ((classify_globals second identifier).mp second_global) }
  have increases : bc_incr classification extended := classify_old
  have unchanged : ∀ source, Plt source before.nextblock → extended source = classification source := by
    intro source below
    exact if_pos below
  have mapped_valid : ∀ source target delta,
      injection source = some (target, delta) → extended source ≠ BCinvalid := by
    intro source target delta mapped
    by_cases below : Plt source before.nextblock
    · rw [unchanged source below]
      rw [injection_below source below] at mapped
      exact (inj_of_bc_inv classification source target delta mapped).1
    · change (if Plt source before.nextblock then classification source else
        match injection source with | none => BCinvalid | some _ => BCother) ≠ BCinvalid
      simp only [if_neg below, mapped, ne_eq, reduceCtorEq, not_false_eq_true]
  have valid_mapped : ∀ source, extended source ≠ BCinvalid →
      ∃ target delta, injection source = some (target, delta) := by
    intro source valid
    by_cases below : Plt source before.nextblock
    · refine ⟨source, z0, ?_⟩
      rw [injection_below source below]
      apply inj_of_bc_valid classification source
      rwa [unchanged source below] at valid
    · change (if Plt source before.nextblock then classification source else
        match injection source with | none => BCinvalid | some _ => BCother) ≠ BCinvalid at valid
      rw [if_neg below] at valid
      cases mapped : injection source with
      | none => simp only [mapped, ne_eq, not_true_eq_false] at valid
      | some destination => exact ⟨destination.1, destination.2, rfl⟩
  have pointer_top : ∀ source target delta offset,
      injection source = some (target, delta) → pmatch extended source offset Ptop := by
    intro source target delta offset mapped
    exact .top (mapped_valid source target delta mapped)
  have value_top : ∀ concrete target, Val.inject injection concrete target →
      vmatch extended concrete Vtop := by
    intro concrete target injected
    cases injected with
    | inject_int integer => exact .ifptrInt integer Ptop
    | inject_long integer => exact .ifptrLong integer Ptop
    | inject_float number => exact .ifptrFloat number Ptop
    | inject_single number => exact .ifptrSingle number Ptop
    | val_inject_undef target => exact .ifptrUndef Ptop
    | inject_ptr source offset destination target_offset delta mapped shifted =>
        exact .ifptrPtr source offset Ptop (pointer_top source destination delta offset mapped)
  have summary_top : ∀ source, extended source ≠ BCinvalid → smatch extended after source Ptop := by
    intro source valid
    obtain ⟨target, delta, mapped⟩ := valid_mapped source valid
    constructor
    · intro chunk offset concrete loaded
      obtain ⟨target_value, target_loaded, injected⟩ := Mem.load_inject injection after injected_memory
        chunk source offset target delta concrete memory_injection loaded mapped
      exact value_top concrete target_value injected
    · intro offset pointer pointer_offset quantity index loaded
      obtain ⟨target_bytes, target_loaded, injected⟩ := Mem.loadbytes_inject injection after injected_memory
        source offset (zOfNat 1) target delta _ memory_injection loaded mapped
      cases injected with
      | cons byte target_byte byte_injection rest =>
          cases byte_injection with
          | fragment first second quantity index value_injection =>
              cases value_injection with
              | inject_ptr pointer pointer_offset target_pointer target_offset delta pointer_injection offset_eq =>
                  exact pointer_top pointer target_pointer delta pointer_offset pointer_injection
  have extended_globals : genv_match extended globals := by
    apply genv_match_exten globals classification extended global_match
    · intro source identifier
      exact (classify_globals source identifier).symm
    · intro source other
      exact (increases source (by simp [other])).trans other
  have extended_readonly : romatch extended after readonly := by
    intro source identifier abstract_block global found
    have old_global := (classify_globals source identifier).mp global
    have valid := memory_match.mmatch_below source (by simp [old_global])
    obtain ⟨summary, block_match, not_writable⟩ := readonly_match source identifier abstract_block old_global found
    refine ⟨summary, ?_, ?_⟩
    · apply bmatch_incr classification extended increases after source abstract_block
      apply bmatch_ext classification before source abstract_block after block_match
      intro offset count bytes loaded nonnegative
      exact external_call_readonly_proof providers function (Genv.to_senv globals) arguments before trace
        result after source offset count bytes called valid loaded (fun position inside => not_writable position)
    · intro offset writable
      exact not_writable offset (external_call_max_perm_proof providers function (Genv.to_senv globals)
        arguments before trace result after source offset .Writable called valid writable)
  have extended_memory : mmatch extended after mtop := by
    constructor
    · intro source stack
      exact ablock_init_sound extended after source Ptop (summary_top source (by simp [stack]))
    · intro identifier abstract_block source global found
      change PTree.get identifier (PTree.empty ablock) = some abstract_block at found
      erw [PTree.gempty] at found
      cases found
    · intro source not_stack valid
      exact summary_top source valid
    · exact summary_top
    · intro source valid
      obtain ⟨target, delta, mapped⟩ := valid_mapped source valid
      exact Mem.valid_block_inject_1 injection after injected_memory source target delta mapped memory_injection
  refine ⟨extended, increases, unchanged, value_top result injected_result result_injection,
    extended_globals, extended_readonly, extended_memory, classify_no_stack, ?_⟩
  intro source offset count valid invalid
  apply Mem.loadbytes_unchanged_on_1 (loc_unmapped (inj_of_bc classification)) before after source offset count
    unmapped_unchanged valid
  intro position inside
  simp only [loc_unmapped, inj_of_bc, invalid]

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib

private theorem va_call_return_match
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (program : program) (globals : genv)
    (providers : CompCert4Lean.Common.ExternalCalls.ExternalCalls) (function : external_function)
    (classification : block_classification) (frames : List stackframe) (stack : block)
    (registers : regset) (environment : aenv) (before after : mem) (abstract_memory : amem)
    (arguments : List val) (abstract_arguments : List aval) (trace : trace) (result : val)
    (called : external_call providers function (Genv.to_senv globals) arguments before trace result after)
    (argument_match : list_forall2 (vmatch classification) arguments abstract_arguments)
    (environment_match : ematch classification registers environment)
    (readonly_match : romatch classification before (romem_for cfg program))
    (memory_match : mmatch classification before abstract_memory)
    (global_match : genv_match classification globals)
    (stack_match : classification stack = BCstack)
    (stack_sound : sound_stack cfg program globals classification frames before stack) :
    ∃ restored,
      vmatch restored result (analyze_call abstract_memory abstract_arguments).1 ∧
      ematch restored registers environment ∧
      romatch restored after (romem_for cfg program) ∧
      mmatch restored after (analyze_call abstract_memory abstract_arguments).2 ∧
      genv_match restored globals ∧ restored stack = BCstack ∧
      sound_stack cfg program globals restored frames after stack := by
  have stack_valid : Plt stack before.nextblock := memory_match.mmatch_below stack (by simp [stack_match])
  have next_bound := external_call_nextblock providers function (Genv.to_senv globals) arguments
    before trace result after called
  unfold analyze_call
  split
  · rename_i private_call
    have private_parts : pincl abstract_memory.am_nonstack Nonstack = true ∧
        abstract_arguments.all (fun abstract => vpincl abstract Nonstack = true) = true := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using private_call
    obtain ⟨hidden, hidden_nostack, hidden_stack, hidden_other, hidden_values,
      hidden_globals, hidden_readonly, hidden_memory⟩ := hide_stack before stack classification globals
        (romem_for cfg program) abstract_memory global_match readonly_match memory_match stack_match
        (pincl_ge _ _ private_parts.1)
    have hidden_arguments : ∀ value, value ∈ arguments → vmatch hidden value Vtop := by
      intro value member
      obtain ⟨abstract, abstract_member, matched⟩ :=
        list_forall2_in_left val aval (vmatch classification) value arguments abstract_arguments argument_match member
      apply hidden_values value abstract
      · apply vpincl_ge abstract Nonstack
        simpa only [decide_eq_true_eq] using (List.all_eq_true.mp private_parts.2) abstract abstract_member
      · exact matched
    obtain ⟨extended, increases, unchanged, result_match, extended_globals, extended_readonly,
      extended_memory, extended_nostack, preserved⟩ := external_call_match providers function globals
        arguments before trace result after hidden (romem_for cfg program) mtop called hidden_globals
        hidden_arguments hidden_readonly hidden_memory hidden_nostack
    have extended_stack : extended stack = BCinvalid := (unchanged stack stack_valid).trans hidden_stack
    have same : ∀ source, Plt source before.nextblock → source ≠ stack →
        classification source = extended source := by
      intro source below different
      exact ((unchanged source below).trans (hidden_other source different)).symm
    have contents : bmatch classification after stack abstract_memory.am_stack := by
      apply bmatch_inv classification before stack _ after (memory_match.mmatch_stack stack stack_match)
      intro offset count nonnegative
      exact preserved stack offset count stack_valid hidden_stack
    obtain ⟨restored, restored_result, restored_environment, restored_readonly, restored_memory,
      restored_globals, restored_stack, restored_same⟩ := return_from_private_call classification extended
        before.nextblock stack globals registers environment result after (romem_for cfg program) abstract_memory
        memory_match.mmatch_below extended_stack stack_match same global_match environment_match contents next_bound
        result_match extended_readonly extended_memory extended_globals extended_nostack
    refine ⟨restored, restored_result, restored_environment, restored_readonly, restored_memory,
      restored_globals, restored_stack, ?_⟩
    apply sound_stack_exten cfg program globals classification frames after stack restored
      (sound_stack_inv cfg program globals after classification frames before stack stack_sound ?_) restored_same
    intro source offset count below invalid nonnegative
    exact preserved source offset count (Plt_trans source stack before.nextblock below stack_valid)
      ((hidden_other source (Plt_ne source stack below)).trans invalid)
  · obtain ⟨hidden, hidden_nostack, hidden_stack, hidden_other, hidden_values,
      hidden_globals, hidden_readonly, hidden_memory⟩ := anonymize_stack before stack classification globals
        (romem_for cfg program) abstract_memory global_match readonly_match memory_match stack_match
    have hidden_arguments : ∀ value, value ∈ arguments → vmatch hidden value Vtop := by
      intro value member
      obtain ⟨abstract, abstract_member, matched⟩ :=
        list_forall2_in_left val aval (vmatch classification) value arguments abstract_arguments argument_match member
      exact hidden_values value abstract matched
    obtain ⟨extended, increases, unchanged, result_match, extended_globals, extended_readonly,
      extended_memory, extended_nostack, preserved⟩ := external_call_match providers function globals
        arguments before trace result after hidden (romem_for cfg program) mtop called hidden_globals
        hidden_arguments hidden_readonly hidden_memory hidden_nostack
    have extended_stack : extended stack = BCother := (unchanged stack stack_valid).trans hidden_stack
    have same : ∀ source, Plt source before.nextblock → source ≠ stack →
        classification source = extended source := by
      intro source below different
      exact ((unchanged source below).trans (hidden_other source different)).symm
    obtain ⟨restored, restored_result, restored_environment, restored_readonly, restored_memory,
      restored_globals, restored_stack, restored_same⟩ := return_from_public_call classification extended
        before.nextblock stack globals registers environment result after (romem_for cfg program)
        memory_match.mmatch_below extended_stack stack_match same global_match environment_match next_bound
        result_match extended_readonly extended_memory extended_globals extended_nostack
    refine ⟨restored, restored_result, restored_environment, restored_readonly, restored_memory,
      restored_globals, restored_stack, ?_⟩
    apply sound_stack_exten cfg program globals classification frames after stack restored
      (sound_stack_inv cfg program globals after classification frames before stack stack_sound ?_) restored_same
    intro source offset count below invalid nonnegative
    exact preserved source offset count (Plt_trans source stack before.nextblock below stack_valid)
      ((hidden_other source (Plt_ne source stack below)).trans invalid)

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem va_builtin_state
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (program : program) (globals : genv)
    (providers : CompCert4Lean.Common.ExternalCalls.ExternalCalls) (function : external_function)
    (classification : block_classification) (frames : List stackframe)
    (body : CompCert4Lean.Backend.RTL.function) (stack : block)
    (current successor : node) (registers : regset) (environment : aenv) (before after : mem)
    (abstract_memory : amem) (arguments : List (builtin_arg reg)) (values : List val)
    (destination : builtin_res reg) (trace : trace) (result : val)
    (code : PTree.get current body.fn_code = some (.Ibuiltin function arguments destination successor))
    (analyzed : PMap.get current (analyze cfg (romem_for cfg program) body) = VA.State environment abstract_memory)
    (evaluated : eval_builtin_args (Genv.to_senv globals) (fun register => Regmap.get register registers)
      (Vptr stack CompCert4Lean.Lib.Integers.Ptrofs.zero) before arguments values)
    (called : external_call providers function (Genv.to_senv globals) values before trace result after)
    (environment_match : ematch classification registers environment)
    (readonly_match : romatch classification before (romem_for cfg program))
    (memory_match : mmatch classification before abstract_memory)
    (global_match : genv_match classification globals)
    (stack_match : classification stack = BCstack)
    (stack_sound : sound_stack cfg program globals classification frames before stack) :
    sound_state_base cfg program globals
      (State frames body (Vptr stack CompCert4Lean.Lib.Integers.Ptrofs.zero) successor
        (regmap_setres destination result registers) after) := by
  have finish : ∀ restored next_environment next_memory,
      transfer_builtin cfg environment abstract_memory (romem_for cfg program) function arguments destination =
        VA.State next_environment next_memory →
      ematch restored (regmap_setres destination result registers) next_environment →
      mmatch restored after next_memory → romatch restored after (romem_for cfg program) →
      genv_match restored globals → restored stack = BCstack →
      sound_stack cfg program globals restored frames after stack →
      sound_state_base cfg program globals
        (State frames body (Vptr stack CompCert4Lean.Lib.Integers.Ptrofs.zero) successor
          (regmap_setres destination result registers) after) := by
    intro restored next_environment next_memory transferred next_registers next_matched next_readonly
      next_globals next_stack next_frames
    apply sound_succ_state cfg program globals restored current environment abstract_memory
      (.Ibuiltin function arguments destination successor) next_environment next_memory frames body stack successor
      _ after analyzed code (by simp [successors_instr]) _ next_registers next_matched next_readonly
      next_globals next_stack next_frames
    simpa only [transfer, code] using transferred
  have default : transfer_builtin cfg environment abstract_memory (romem_for cfg program) function arguments destination =
      transfer_builtin_default cfg environment abstract_memory (romem_for cfg program) arguments destination →
      sound_state_base cfg program globals
        (State frames body (Vptr stack CompCert4Lean.Lib.Integers.Ptrofs.zero) successor
          (regmap_setres destination result registers) after) := by
    intro transferred
    have argument_match := abuiltin_args_sound cfg classification globals registers stack before environment
      (romem_for cfg program) abstract_memory environment_match readonly_match memory_match global_match stack_match
      arguments values evaluated
    obtain ⟨restored, restored_result, restored_registers, restored_readonly, restored_memory,
      restored_globals, restored_stack, restored_frames⟩ := va_call_return_match cfg program globals providers function
        classification frames stack registers environment before after abstract_memory values
        (arguments.map (abuiltin_arg cfg environment abstract_memory (romem_for cfg program))) trace result called
        argument_match environment_match readonly_match memory_match global_match stack_match stack_sound
    apply finish restored _ _ (transferred.trans rfl)
      (set_builtin_res_sound restored registers environment result _ destination restored_registers restored_result)
      restored_memory restored_readonly restored_globals restored_stack restored_frames
  cases function <;> try exact default rfl
  case EF_builtin name signature =>
    cases lookup : lookup_builtin_function name signature with
    | none => apply default; simp only [transfer_builtin, lookup]
    | some builtin =>
        cases static : eval_static_builtin_function cfg environment abstract_memory (romem_for cfg program) builtin arguments with
        | none => apply default; simp only [transfer_builtin, lookup, static]
        | some abstract_value =>
            simp only [external_call, builtin_or_external_sem, lookup] at called
            cases called
            rename_i computed
            apply finish classification _ _ (by simp only [transfer_builtin, lookup, static])
              (set_builtin_res_sound classification registers environment _ abstract_value destination environment_match ?_)
              memory_match readonly_match global_match stack_match stack_sound
            exact eval_static_builtin_function_sound cfg classification globals registers stack before environment
              (romem_for cfg program) abstract_memory builtin arguments values _ abstract_value environment_match
              readonly_match memory_match global_match stack_match evaluated static computed
  case EF_annot kind text types =>
    cases called
    exact finish classification _ _ rfl
      (set_builtin_res_sound classification registers environment Vundef ntop destination environment_match (.numUndef _))
      memory_match readonly_match global_match stack_match stack_sound
  case EF_debug kind text types =>
    cases called
    exact finish classification _ _ rfl
      (set_builtin_res_sound classification registers environment Vundef ntop destination environment_match (.numUndef _))
      memory_match readonly_match global_match stack_match stack_sound
  case EF_annot_val kind text type =>
    cases arguments with
    | nil => exact default rfl
    | cons argument rest =>
        cases rest with
        | cons extra rest => exact default rfl
        | nil =>
            cases called
            cases evaluated
            rename_i argument_eval remaining
            cases remaining
            exact finish classification _ _ rfl
              (set_builtin_res_sound classification registers environment _ _ destination environment_match
                (abuiltin_arg_sound cfg classification globals registers stack before environment
                  (romem_for cfg program) abstract_memory environment_match readonly_match memory_match global_match
                  stack_match argument _ argument_eval))
              memory_match readonly_match global_match stack_match stack_sound
  case EF_vload chunk =>
    cases arguments with
    | nil => exact default rfl
    | cons argument rest =>
        cases rest with
        | cons extra rest => exact default rfl
        | nil =>
            cases called
            rename_i source offset loaded
            cases evaluated
            rename_i argument_eval remaining
            cases remaining
            have address_match := abuiltin_arg_sound cfg classification globals registers stack before environment
              (romem_for cfg program) abstract_memory environment_match readonly_match memory_match global_match
              stack_match argument _ argument_eval
            cases loaded with
            | volatile_load_vol identifier event concrete volatile symbol event_match =>
                apply finish classification _ abstract_memory rfl
                  (set_builtin_res_sound classification registers environment _ _ destination environment_match ?_)
                  memory_match readonly_match global_match stack_match stack_sound
                have concrete_match : vmatch classification concrete (Ifptr Glob) := by
                  generalize type_of_chunk chunk = matched_type at event_match
                  cases event_match with
                  | ev_match_int integer => exact .ifptrInt integer Glob
                  | ev_match_long integer => exact .ifptrLong integer Glob
                  | ev_match_float number => exact .ifptrFloat number Glob
                  | ev_match_single number => exact .ifptrSingle number Glob
                  | ev_match_ptr identifier target target_offset public_symbol found =>
                      exact .ifptrPtr target target_offset Glob
                        (.glob identifier ((global_match.1 identifier target).mp found))
                split
                · exact vmatch_lub_r cfg classification _ _ _
                    (vnormalize_sound classification chunk concrete _ concrete_match)
                · exact vnormalize_sound classification chunk concrete Vtop
                    (vmatch_top classification concrete _ concrete_match)
            | volatile_load_nonvol =>
                rename_i not_volatile memory_load
                apply finish classification _ abstract_memory rfl
                  (set_builtin_res_sound classification registers environment _ _ destination environment_match ?_)
                  memory_match readonly_match global_match stack_match stack_sound
                have concrete_match := loadv_sound cfg classification chunk before (Vptr source offset) result
                  (romem_for cfg program) abstract_memory _ memory_load readonly_match memory_match address_match
                split
                · exact vmatch_lub_l cfg classification _ _ _ concrete_match
                · exact vnormalize_cast classification chunk before source
                    (CompCert4Lean.Lib.Integers.Ptrofs.unsigned offset) result Ptop memory_load
                    (vmatch_top classification result _ concrete_match)
  case EF_vstore chunk =>
    cases arguments with
    | nil => exact default rfl
    | cons address rest =>
        cases rest with
        | nil => exact default rfl
        | cons argument rest =>
            cases rest with
            | cons extra rest => exact default rfl
            | nil =>
                cases called
                rename_i source offset concrete stored
                cases evaluated
                rename_i address_eval remaining
                cases remaining
                rename_i value_eval remaining
                cases remaining
                have address_match := abuiltin_arg_sound cfg classification globals registers stack before environment
                  (romem_for cfg program) abstract_memory environment_match readonly_match memory_match global_match
                  stack_match address _ address_eval
                have value_match := abuiltin_arg_sound cfg classification globals registers stack before environment
                  (romem_for cfg program) abstract_memory environment_match readonly_match memory_match global_match
                  stack_match argument _ value_eval
                cases stored with
                | volatile_store_vol identifier event volatile symbol event_match =>
                    exact finish classification _ _ rfl
                      (set_builtin_res_sound classification registers environment Vundef ntop destination
                        environment_match (.numUndef _))
                      (mmatch_lub_l cfg classification before abstract_memory _ memory_match)
                      readonly_match global_match stack_match stack_sound
                | volatile_store_nonvol =>
                    rename_i not_volatile memory_store
                    apply finish classification _ _ rfl
                      (set_builtin_res_sound classification registers environment Vundef ntop destination
                        environment_match (.numUndef _))
                    · exact mmatch_lub_r cfg classification after abstract_memory _
                        (storev_sound cfg classification chunk before (Vptr source offset) concrete after abstract_memory _ _
                          memory_store memory_match address_match value_match)
                    · exact romatch_store classification chunk before source _ concrete after _ memory_store readonly_match
                    · exact global_match
                    · exact stack_match
                    · exact sound_stack_storev cfg program globals chunk before (Vptr source offset) concrete after classification _
                        frames stack memory_store address_match stack_sound
  case EF_memcpy size alignment =>
    cases arguments with
    | nil => exact default rfl
    | cons destination_arg rest =>
        cases rest with
        | nil => exact default rfl
        | cons source_arg rest =>
            cases rest with
            | cons extra rest => exact default rfl
            | nil =>
                cases called
                rename_i destination_block destination_offset source_block source_offset bytes
                  aligned nonnegative size_aligned source_aligned destination_aligned disjoint loaded stored
                cases evaluated
                rename_i destination_eval remaining
                cases remaining
                rename_i source_eval remaining
                cases remaining
                have destination_match := abuiltin_arg_sound cfg classification globals registers stack before environment
                  (romem_for cfg program) abstract_memory environment_match readonly_match memory_match global_match
                  stack_match destination_arg _ destination_eval
                have source_match := abuiltin_arg_sound cfg classification globals registers stack before environment
                  (romem_for cfg program) abstract_memory environment_match readonly_match memory_match global_match
                  stack_match source_arg _ source_eval
                apply finish classification _ _ rfl
                  (set_builtin_res_sound classification registers environment Vundef ntop destination
                    environment_match (.numUndef _))
                · apply storebytes_sound classification before destination_block destination_offset bytes after
                    abstract_memory _ size _ stored memory_match
                    (match_aptr_of_aval cfg classification _ _ _ destination_match)
                    (Mem.loadbytes_length before source_block _ size bytes loaded)
                  exact loadbytes_sound cfg classification before source_block source_offset size bytes abstract_memory
                    (romem_for cfg program) _ loaded readonly_match memory_match
                    (match_aptr_of_aval cfg classification _ _ _ source_match)
                · exact romatch_storebytes classification before destination_block _ bytes after _ stored readonly_match
                · exact global_match
                · exact stack_match
                · exact sound_stack_storebytes cfg program globals before destination_block destination_offset bytes after
                    classification _ frames stack stored destination_match stack_sound

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.ValueAOp

private theorem va_sound_step_base
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (operation_sound : eval_static_operation_soundStatement) : sound_step_baseStatement := by
  intro cfg program providers globals initial trace final stepped sound
  cases stepped with
  | exec_Inop frames body pointer current registers memory successor code =>
      cases sound
      rename_i stack environment abstract_memory classification global_match stack_match analyzed
        environment_match readonly_match memory_match stack_sound
      exact sound_succ_state cfg program globals classification current environment abstract_memory
        (.Inop successor) environment abstract_memory frames body stack successor registers memory
        analyzed code (by simp [successors_instr]) (by simp only [transfer, code])
        environment_match memory_match readonly_match global_match stack_match stack_sound
  | exec_Iop frames body pointer current registers memory operation arguments destination successor value code evaluated =>
      cases sound
      rename_i stack environment abstract_memory classification global_match stack_match analyzed
        environment_match readonly_match memory_match stack_sound
      exact sound_succ_state cfg program globals classification current environment abstract_memory
        (.Iop operation arguments destination successor) _ abstract_memory frames body stack successor _ memory
        analyzed code (by simp [successors_instr]) (by simp only [transfer, code])
        (ematch_update classification registers environment value _ destination environment_match
          (operation_sound cfg classification globals global_match stack stack_match operation _ memory value _
            evaluated (aregs_sound classification registers environment arguments environment_match)))
        memory_match readonly_match global_match stack_match stack_sound
  | exec_Iload frames body pointer current registers memory chunk addressing arguments destination successor
      address value code evaluated loaded =>
      cases sound
      rename_i stack environment abstract_memory classification global_match stack_match analyzed
        environment_match readonly_match memory_match stack_sound
      have address_match := eval_static_addressing_sound classification globals global_match stack stack_match
        addressing _ address _ evaluated (aregs_sound classification registers environment arguments environment_match)
      exact sound_succ_state cfg program globals classification current environment abstract_memory
        (.Iload chunk addressing arguments destination successor) _ abstract_memory frames body stack successor _ memory
        analyzed code (by simp [successors_instr]) (by simp only [transfer, code])
        (ematch_update classification registers environment value _ destination environment_match
          (loadv_sound cfg classification chunk memory address value (romem_for cfg program) abstract_memory _
            loaded readonly_match memory_match address_match))
        memory_match readonly_match global_match stack_match stack_sound
  | exec_Istore frames body pointer current registers memory chunk addressing arguments source successor
      address after code evaluated stored =>
      cases sound
      rename_i stack environment abstract_memory classification global_match stack_match analyzed
        environment_match readonly_match memory_match stack_sound
      have address_match := eval_static_addressing_sound classification globals global_match stack stack_match
        addressing _ address _ evaluated (aregs_sound classification registers environment arguments environment_match)
      have next_readonly : romatch classification after (romem_for cfg program) := by
        cases address <;> simp only [Mem.storev, reduceCtorEq] at stored
        rename_i target offset
        exact romatch_store classification chunk memory target (Ptrofs.unsigned offset) _ after _ stored readonly_match
      exact sound_succ_state cfg program globals classification current environment abstract_memory
        (.Istore chunk addressing arguments source successor) environment _ frames body stack successor registers after
        analyzed code (by simp [successors_instr]) (by simp only [transfer, code]) environment_match
        (storev_sound cfg classification chunk memory address _ after abstract_memory _ _ stored memory_match
          address_match (areg_sound classification registers environment source environment_match))
        next_readonly global_match stack_match
        (sound_stack_storev cfg program globals chunk memory address _ after classification _ frames stack
          stored address_match stack_sound)
  | exec_Icall frames body pointer current registers memory signature function arguments destination successor
      callee code found matching_signature =>
      cases sound
      rename_i stack environment abstract_memory classification global_match stack_match analyzed
        environment_match readonly_match memory_match stack_sound
      have transferred : transfer cfg body (romem_for cfg program) current environment abstract_memory =
          transfer_call environment abstract_memory arguments destination := by simp only [transfer, code]
      by_cases private_parts : pincl abstract_memory.am_nonstack Nonstack = true ∧
          (aregs environment arguments).all (fun abstract => vpincl abstract Nonstack = true) = true
      · simp only [transfer_call, analyze_call, Bool.and_eq_true, decide_eq_true_eq, private_parts,
          ↓reduceIte] at transferred
        have successor_match := analyze_successor cfg body current environment abstract_memory _ successor
          (romem_for cfg program) _ _ analyzed code (by simp [successors_instr]) transferred
        erw [transferred] at successor_match
        obtain ⟨hidden, hidden_nostack, hidden_stack, hidden_other, hidden_values,
          hidden_globals, hidden_readonly, hidden_memory⟩ := hide_stack memory stack classification globals
            (romem_for cfg program) abstract_memory global_match readonly_match memory_match stack_match
            (pincl_ge _ _ private_parts.1)
        refine sound_call_state _ _ _ _ hidden ?_ ?_ hidden_readonly hidden_memory hidden_globals hidden_nostack
        · exact sound_stack_private_call hidden destination body stack successor registers frames memory memory.nextblock
            classification memory.nextblock environment abstract_memory stack_sound (Ple_refl _) memory_match.mmatch_below
            hidden_stack stack_match (fun source below different => hidden_other source different) global_match
            successor_match environment_match (memory_match.mmatch_stack stack stack_match)
        · intro value member
          obtain ⟨register, register_member, rfl⟩ := List.mem_map.mp member
          apply hidden_values _ (areg environment register)
          · apply vpincl_ge _ Nonstack
            have abstract_member : areg environment register ∈ aregs environment arguments :=
              List.mem_map.mpr ⟨register, register_member, rfl⟩
            simpa only [decide_eq_true_eq] using
              (List.all_eq_true.mp private_parts.2) _ abstract_member
          · exact areg_sound classification registers environment register environment_match
      · simp only [transfer_call, analyze_call, Bool.and_eq_true, decide_eq_true_eq, private_parts,
          ↓reduceIte] at transferred
        have successor_match := analyze_successor cfg body current environment abstract_memory _ successor
          (romem_for cfg program) _ _ analyzed code (by simp [successors_instr]) transferred
        erw [transferred] at successor_match
        obtain ⟨hidden, hidden_nostack, hidden_stack, hidden_other, hidden_values,
          hidden_globals, hidden_readonly, hidden_memory⟩ := anonymize_stack memory stack classification globals
            (romem_for cfg program) abstract_memory global_match readonly_match memory_match stack_match
        refine sound_call_state _ _ _ _ hidden ?_ ?_ hidden_readonly hidden_memory hidden_globals hidden_nostack
        · exact sound_stack_public_call hidden destination body stack successor registers frames memory memory.nextblock
            classification memory.nextblock environment stack_sound (Ple_refl _) memory_match.mmatch_below hidden_stack
            stack_match (fun source below different => hidden_other source different) global_match successor_match
            environment_match
        · intro value member
          obtain ⟨register, register_member, rfl⟩ := List.mem_map.mp member
          exact hidden_values _ (areg environment register)
            (areg_sound classification registers environment register environment_match)
  | exec_Itailcall frames body stack current registers memory signature function arguments callee after
      code found matching_signature freed =>
      cases sound
      rename_i environment abstract_memory classification global_match stack_match analyzed
        environment_match readonly_match memory_match stack_sound
      obtain ⟨hidden, hidden_nostack, hidden_stack, hidden_other, hidden_values,
        hidden_globals, hidden_readonly, hidden_memory⟩ := anonymize_stack memory stack classification globals
          (romem_for cfg program) abstract_memory global_match readonly_match memory_match stack_match
      refine sound_call_state _ _ _ _ hidden ?_ ?_
        (romatch_free hidden memory stack _ _ after _ freed hidden_readonly)
        (mmatch_free hidden memory stack _ _ after _ freed hidden_memory) hidden_globals hidden_nostack
      · apply sound_stack_new_bound cfg program globals hidden frames after stack after.nextblock
        · apply sound_stack_exten cfg program globals classification frames after stack hidden
            (sound_stack_free cfg program globals memory stack _ _ after classification frames stack freed stack_sound)
          intro source below
          exact hidden_other source (Plt_ne source stack below)
        · rw [Mem.nextblock_free memory stack _ _ after freed]
          exact Plt_Ple _ _ (memory_match.mmatch_below stack (by simp [stack_match]))
      · intro value member
        obtain ⟨register, register_member, rfl⟩ := List.mem_map.mp member
        exact hidden_values _ (areg environment register)
          (areg_sound classification registers environment register environment_match)
  | exec_Ibuiltin frames body pointer current registers memory function arguments destination successor
      values events result after code evaluated called =>
      cases sound
      rename_i stack environment abstract_memory classification global_match stack_match analyzed
        environment_match readonly_match memory_match stack_sound
      exact va_builtin_state cfg program globals providers function classification frames body stack current successor
        registers environment memory after abstract_memory arguments values destination trace result code analyzed
        evaluated called environment_match readonly_match memory_match global_match stack_match stack_sound
  | exec_Icond frames body pointer current registers memory condition arguments if_true if_false value successor
      code evaluated target =>
      cases sound
      rename_i stack environment abstract_memory classification global_match stack_match analyzed
        environment_match readonly_match memory_match stack_sound
      exact sound_succ_state cfg program globals classification current environment abstract_memory
        (.Icond condition arguments if_true if_false) environment abstract_memory frames body stack successor registers memory
        analyzed code (by cases value <;> simp_all [successors_instr]) (by simp only [transfer, code])
        environment_match memory_match readonly_match global_match stack_match stack_sound
  | exec_Ijumptable frames body pointer current registers memory argument targets index successor code value selected =>
      cases sound
      rename_i stack environment abstract_memory classification global_match stack_match analyzed
        environment_match readonly_match memory_match stack_sound
      exact sound_succ_state cfg program globals classification current environment abstract_memory
        (.Ijumptable argument targets) environment abstract_memory frames body stack successor registers memory
        analyzed code (list_nth_z_in node targets (Int.unsigned index) successor selected)
        (by simp only [transfer, code]) environment_match memory_match readonly_match global_match stack_match stack_sound
  | exec_Ireturn frames body stack current registers memory result after code freed =>
      cases sound
      rename_i environment abstract_memory classification global_match stack_match analyzed
        environment_match readonly_match memory_match stack_sound
      obtain ⟨hidden, hidden_nostack, hidden_stack, hidden_other, hidden_values,
        hidden_globals, hidden_readonly, hidden_memory⟩ := anonymize_stack memory stack classification globals
          (romem_for cfg program) abstract_memory global_match readonly_match memory_match stack_match
      refine sound_return_state _ _ _ hidden ?_ ?_
        (romatch_free hidden memory stack _ _ after _ freed hidden_readonly)
        (mmatch_free hidden memory stack _ _ after _ freed hidden_memory) hidden_globals hidden_nostack
      · apply sound_stack_new_bound cfg program globals hidden frames after stack after.nextblock
        · apply sound_stack_exten cfg program globals classification frames after stack hidden
            (sound_stack_free cfg program globals memory stack _ _ after classification frames stack freed stack_sound)
          intro source below
          exact hidden_other source (Plt_ne source stack below)
        · rw [Mem.nextblock_free memory stack _ _ after freed]
          exact Plt_Ple _ _ (memory_match.mmatch_below stack (by simp [stack_match]))
      · cases result with
        | none => exact .ifptrUndef _
        | some register =>
            exact hidden_values _ (areg environment register)
              (areg_sound classification registers environment register environment_match)
  | exec_function_internal frames body arguments before after stack typed allocated =>
      cases sound
      rename_i classification global_match no_stack arguments_match readonly_match memory_match stack_sound
      obtain ⟨extended, increases, extended_stack, extended_globals, extended_readonly,
        extended_memory, same, extended_values⟩ := allocate_stack before body.fn_stacksize after stack classification
          globals (romem_for cfg program) mtop allocated global_match readonly_match memory_match no_stack
      obtain ⟨environment, abstract_memory, analyzed, environment_match, matched⟩ :=
        analyze_entrypoint cfg (romem_for cfg program) body arguments after extended
          (fun value member => extended_values value Vtop (arguments_match value member)) typed extended_memory
      refine sound_regular_state _ _ _ _ _ _ environment abstract_memory extended ?_ analyzed environment_match
        extended_readonly matched extended_globals extended_stack
      have allocated_block := Mem.alloc_result before _ _ after stack allocated
      rw [allocated_block]
      apply sound_stack_exten cfg program globals classification frames after before.nextblock extended
        (sound_stack_inv cfg program globals after classification frames before before.nextblock stack_sound ?_)
      · intro source below
        exact same source (by simpa only [allocated_block] using below)
      · intro source offset count below invalid nonnegative
        exact Mem.loadbytes_alloc_unchanged before _ _ after stack allocated source offset count below
  | exec_function_external frames function arguments result events before after called =>
      cases sound
      rename_i classification global_match no_stack arguments_match readonly_match memory_match stack_sound
      obtain ⟨extended, increases, same, result_match, extended_globals, extended_readonly,
        extended_memory, extended_nostack, preserved⟩ := external_call_match providers function globals arguments
          before trace result after classification (romem_for cfg program) mtop called global_match arguments_match
          readonly_match memory_match no_stack
      refine sound_return_state _ _ _ extended ?_ result_match extended_readonly extended_memory
        extended_globals extended_nostack
      apply sound_stack_new_bound cfg program globals extended frames after before.nextblock after.nextblock
      · apply sound_stack_exten cfg program globals classification frames after before.nextblock extended
          (sound_stack_inv cfg program globals after classification frames before before.nextblock stack_sound ?_) same
        intro source offset count below invalid nonnegative
        exact preserved source offset count below invalid
      · exact external_call_nextblock providers function (Genv.to_senv globals) arguments before trace result after called
  | exec_return destination body pointer current registers frames result memory =>
      cases sound
      rename_i classification global_match no_stack result_match readonly_match memory_match stack_sound
      cases stack_sound
      case sound_stack_public_call stack caller bound environment below caller_stack caller_globals stack_class
          same analyzed environment_match stack_sound increasing =>
        obtain ⟨restored, restored_result, restored_environment, restored_readonly, restored_memory,
          restored_globals, restored_stack, restored_same⟩ := return_from_public_call caller classification bound stack
            globals registers environment result memory (romem_for cfg program) below stack_class caller_stack
            (fun source source_below different => (same source source_below different).symm) caller_globals
            environment_match increasing result_match readonly_match memory_match global_match no_stack
        cases analysis : PMap.get current (analyze cfg (romem_for cfg program) body) with
        | Bot => erw [analysis] at analyzed; exact False.elim analyzed
        | State next_environment next_memory =>
            erw [analysis] at analyzed
            exact sound_regular_state _ _ _ _ _ _ next_environment next_memory restored
              (sound_stack_exten cfg program globals caller frames memory stack restored stack_sound restored_same)
              analysis
              (ematch_ge restored _ _ next_environment
                (ematch_update restored registers environment result Vtop destination restored_environment restored_result)
                analyzed.1)
              restored_readonly (analyzed.2 restored memory restored_memory) restored_globals restored_stack
      case sound_stack_private_call stack caller bound environment abstract_memory below caller_stack caller_globals stack_class
          same analyzed environment_match contents stack_sound increasing =>
        obtain ⟨restored, restored_result, restored_environment, restored_readonly, restored_memory,
          restored_globals, restored_stack, restored_same⟩ := return_from_private_call caller classification bound stack
            globals registers environment result memory (romem_for cfg program) abstract_memory below stack_class caller_stack
            (fun source source_below different => (same source source_below different).symm) caller_globals
            environment_match contents increasing result_match readonly_match memory_match global_match no_stack
        cases analysis : PMap.get current (analyze cfg (romem_for cfg program) body) with
        | Bot => erw [analysis] at analyzed; exact False.elim analyzed
        | State next_environment next_memory =>
            erw [analysis] at analyzed
            exact sound_regular_state _ _ _ _ _ _ next_environment next_memory restored
              (sound_stack_exten cfg program globals caller frames memory stack restored stack_sound restored_same)
              analysis
              (ematch_ge restored _ _ next_environment
                (ematch_update restored registers environment result (Ifptr Nonstack) destination
                  restored_environment restored_result) analyzed.1)
              restored_readonly (analyzed.2 restored memory restored_memory) restored_globals restored_stack

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

theorem sound_step_base
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    sound_step_baseStatement :=
  va_sound_step_base CompCert4Lean.X86.ValueAOp.eval_static_operation_sound

end CompCert4Lean.Backend.ValueAnalysis

namespace CompCert4Lean.Backend.ValueAnalysis

theorem sound_step
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    sound_stepStatement := by
  intro cfg program providers initial trace final stepped sound
  cases sound with
  | sound_state_intro matched =>
      exact sound_state_intro final (fun compilation_unit linked =>
        sound_step_base cfg compilation_unit providers (CompCert4Lean.Common.Globalenvs.Genv.globalenv program)
          initial trace final stepped (matched compilation_unit linked))

end CompCert4Lean.Backend.ValueAnalysis
