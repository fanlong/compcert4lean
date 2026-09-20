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
