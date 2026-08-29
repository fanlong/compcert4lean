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
    (s : List stackframe) (f : function) (sp pc' : node) (e' : regset)
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
