import CompCert4Lean.Backend.ValueAnalysis
import CompCert4Lean.Backend.NeedDomain
import CompCert4Lean.Backend.RTL
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Builtins
import CompCert4Lean.Common.Errors
import CompCert4Lean.Common.Memdata
import CompCert4Lean.Lib.IntvSets
import CompCert4Lean.Lib.Maps
import CompCert4Lean.X86.NeedOp

/-!
# Elimination of unneeded computations over RTL

Definition-bearing translation of CompCert's `backend/Deadcode.v`.
-/

namespace CompCert4Lean.Backend.Deadcode

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Kildall
open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueAnalysis
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Lib.IntvSets
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.NeedOp
open CompCert4Lean.X86.Op

private abbrev int := CompCert4Lean.Lib.Integers.int
private abbrev int64 := CompCert4Lean.Lib.Integers.int64
private abbrev reg := CompCert4Lean.Backend.Registers.reg
private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string

private def bytesToString : List UInt8 → RocqString
  | [] => .EmptyString
  | b :: bs => .String b (bytesToString bs)

private def needednessAnalysisFailedText : RocqString :=
  bytesToString [78, 101, 101, 100, 101, 100, 110, 101, 115, 115, 32, 97,
    110, 97, 108, 121, 115, 105, 115, 32, 102, 97, 105, 108, 101, 100]

def na_lattice : SemiLattice :=
  { t := NA.t
    bot := NA.bot
    lub := NA.lub
    beq := NA.beq
    eq := NA.eq
    ge := NA.ge }

def solver_law_obligation : Prop :=
  SemiLatticeLaws na_lattice ∧ NodeSetBackward.law_obligation

/-! Canonical generated surface for
`Kildall.Backward_Dataflow_Solver(NA)(NodeSetBackward)`. -/
namespace DS

def L : SemiLattice := na_lattice

def law_obligation : Prop :=
  SemiLatticeLaws L ∧ NodeSetBackward.law_obligation

def fixpoint {A : Type} (code : PTree.t A) (successors : A → List positive)
    (transf : positive → L.t → L.t) : Option (PMap.t L.t) :=
  Backward_Dataflow_Solver.fixpoint L NodeSetBackward code successors transf

def fixpoint_solution (_laws : law_obligation) : Prop :=
  ∀ (A : Type) (code : PTree.t A) (successors : A → List positive)
    (transf : positive → L.t → L.t) (res : PMap.t L.t)
    (n : positive) (instr : A) (s : positive),
    fixpoint code successors transf = some res →
    PTree.get n code = some instr → s ∈ successors instr →
    (∀ n a, PTree.get n code = none → L.eq (transf n a) L.bot) →
    L.ge (PMap.get n res) (transf s (PMap.get s res))

def fixpoint_allnodes {A : Type} (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t) : Option (PMap.t L.t) :=
  Backward_Dataflow_Solver.fixpoint_allnodes L NodeSetBackward code successors transf

def fixpoint_allnodes_solution (_laws : law_obligation) : Prop :=
  ∀ (A : Type) (code : PTree.t A) (successors : A → List positive)
    (transf : positive → L.t → L.t) (res : PMap.t L.t)
    (n : positive) (instr : A) (s : positive),
    fixpoint_allnodes code successors transf = some res →
    PTree.get n code = some instr → s ∈ successors instr →
    L.ge (PMap.get n res) (transf s (PMap.get s res))

end DS

def add_need_all (r : reg) (ne : nenv) : nenv :=
  NE.set r All ne

def add_need (r : reg) (nv : nval) (ne : nenv) : nenv :=
  NE.set r (nlub nv (NE.get r ne)) ne

def add_needs_all : List reg → nenv → nenv
  | [], ne => ne
  | r :: rs, ne => add_need_all r (add_needs_all rs ne)

def add_needs : List reg → List nval → nenv → nenv
  | [], _, ne => ne
  | rl, [], ne => add_needs_all rl ne
  | r :: rs, nv :: nvs, ne => add_need r nv (add_needs rs nvs ne)

def add_ros_need_all (ros : Sum reg ident) (ne : nenv) : nenv :=
  match ros with
  | .inl r => add_need_all r ne
  | .inr _ => ne

def add_opt_need_all (or : Option reg) (ne : nenv) : nenv :=
  match or with
  | some r => add_need_all r ne
  | none => ne

def kill (r : reg) (ne : nenv) : nenv :=
  NE.set r Nothing ne

def is_dead (v : nval) : Bool :=
  match v with
  | Nothing => true
  | _ => false

def is_int_zero (v : nval) : Bool :=
  match v with
  | nval.I n => CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero
  | _ => false

def transfer_builtin_arg (nv : nval) (na : NA.t) (a : builtin_arg reg) : NA.t :=
  let (ne, nm) := na
  match a with
  | .BA r => (add_need r nv ne, nm)
  | .BA_int _ | .BA_long _ | .BA_float _ | .BA_single _
  | .BA_addrstack _ | .BA_addrglobal _ _ => (ne, nm)
  | .BA_loadstack chunk ofs => (ne, nmem_add nm (Stk ofs) (size_chunk chunk))
  | .BA_loadglobal chunk id ofs => (ne, nmem_add nm (Gl id ofs) (size_chunk chunk))
  | .BA_splitlong hi lo =>
      transfer_builtin_arg All (transfer_builtin_arg All na hi) lo
  | .BA_addptr hi lo =>
      transfer_builtin_arg All (transfer_builtin_arg All na hi) lo

def transfer_builtin_args (na : NA.t) (al : List (builtin_arg reg)) : NA.t :=
  al.foldl (fun acc a => transfer_builtin_arg All acc a) na

def kill_builtin_res (res : builtin_res reg) (ne : NE.t) : NE.t :=
  match res with
  | .BR r => kill r ne
  | _ => ne

def builtin_res_dead (res : builtin_res reg) (ne : NE.t) : Bool :=
  match res with
  | .BR r => is_dead (nreg ne r)
  | _ => false

def transfer_builtin (cfg : CompilerConfig) (app : VA.t) (ef : external_function)
    (args : List (builtin_arg reg)) (res : builtin_res reg)
    (ne : NE.t) (nm : nmem) : NA.t :=
  match ef, args with
  | .EF_vload chunk, a1 :: [] =>
      transfer_builtin_arg All
        (kill_builtin_res res ne,
          nmem_add nm (aaddr_arg cfg app a1) (size_chunk chunk)) a1
  | .EF_vstore chunk, a1 :: a2 :: [] =>
      transfer_builtin_arg All
        (transfer_builtin_arg (store_argument chunk) (kill_builtin_res res ne, nm) a2) a1
  | .EF_memcpy sz _, dst :: src :: [] =>
      if nmem_contains nm (aaddr_arg cfg app dst) sz then
        transfer_builtin_args
          (kill_builtin_res res ne,
            nmem_add (nmem_remove nm (aaddr_arg cfg app dst) sz)
              (aaddr_arg cfg app src) sz) args
      else
        (ne, nm)
  | .EF_annot _ _ _, _ =>
      transfer_builtin_args (kill_builtin_res res ne, nm) args
  | .EF_annot_val _ _ _, _ =>
      transfer_builtin_args (kill_builtin_res res ne, nm) args
  | .EF_debug _ _ _, _ => (kill_builtin_res res ne, nm)
  | .EF_builtin name sg, args =>
      match lookup_builtin_function name sg with
      | some _ =>
          if builtin_res_dead res ne then (ne, nm)
          else transfer_builtin_args (kill_builtin_res res ne, nm) args
      | none => transfer_builtin_args (kill_builtin_res res ne, nmem_all) args
  | _, _ => transfer_builtin_args (kill_builtin_res res ne, nmem_all) args

def transfer (cfg : CompilerConfig) (f : function) (dm : defmap)
    (approx : PMap.t VA.t)
    (pc : node) (after : NA.t) : NA.t :=
  let (ne, nm) := after
  match PTree.get pc f.fn_code with
  | none => NA.bot
  | some (.Inop _) => after
  | some (.Iop op args res _) =>
      let nres := nreg ne res
      if is_dead nres then after
      else if is_int_zero nres then (kill res ne, nm)
      else (add_needs args (needs_of_operation op nres) (kill res ne), nm)
  | some (.Iload chunk addr args dst _) =>
      let ndst := nreg ne dst
      if is_dead ndst then after
      else if is_int_zero ndst then (kill dst ne, nm)
      else
        (add_needs_all args (kill dst ne),
          nmem_add nm (aaddressing cfg (PMap.get pc approx) addr args)
            (size_chunk chunk))
  | some (.Istore chunk addr args src _) =>
      let p := aaddressing cfg (PMap.get pc approx) addr args
      if nmem_contains nm p (size_chunk chunk) then
        (add_needs_all args (add_need src (store_argument chunk) ne),
          nmem_remove nm p (size_chunk chunk))
      else after
  | some (.Icall _ ros args res _) =>
      match is_known_runtime_function dm ros with
      | none => (add_needs_all args (add_ros_need_all ros (kill res ne)), nmem_all)
      | some _ =>
          let nres := nreg ne res
          if is_dead nres then after
          else (add_needs_all args (add_ros_need_all ros (kill res ne)), nm)
  | some (.Itailcall _ ros args) =>
      (add_needs_all args (add_ros_need_all ros NE.bot),
        nmem_dead_stack f.fn_stacksize)
  | some (.Ibuiltin ef args res _) =>
      transfer_builtin cfg (PMap.get pc approx) ef args res ne nm
  | some (.Icond cond args s1 s2) =>
      match peq s1 s2 with
      | .left _ => after
      | .right _ => (add_needs args (needs_of_condition cond) ne, nm)
  | some (.Ijumptable arg _) => (add_need_all arg ne, nm)
  | some (.Ireturn optarg) =>
      (add_opt_need_all optarg ne, nmem_dead_stack f.fn_stacksize)

def analyze (cfg : CompilerConfig) (f : function) (dm : defmap)
    (approx : PMap.t VA.t) : Option (PMap.t NA.t) :=
  DS.fixpoint f.fn_code successors_instr (transfer cfg f dm approx)

def transf_instr (cfg : CompilerConfig) (dm : defmap) (approx : PMap.t VA.t)
    (an : PMap.t NA.t)
    (pc : node) (instr : instruction) : instruction :=
  match instr with
  | .Iop op args res s =>
      let nres := nreg (PMap.get pc an).1 res
      if is_dead nres then
        .Inop s
      else if is_int_zero nres then
        .Iop (.Ointconst CompCert4Lean.Lib.Integers.Int.zero) [] res s
      else if operation_is_redundant op nres then
        match args with
        | arg :: _ => .Iop .Omove [arg] res s
        | [] => instr
      else instr
  | .Iload chunk addr args dst s =>
      let ndst := nreg (PMap.get pc an).1 dst
      if is_dead ndst then .Inop s
      else if is_int_zero ndst then
        .Iop (.Ointconst CompCert4Lean.Lib.Integers.Int.zero) [] dst s
      else instr
  | .Istore chunk addr args src s =>
      let p := aaddressing cfg (PMap.get pc approx) addr args
      if nmem_contains (PMap.get pc an).2 p (size_chunk chunk) then instr else .Inop s
  | .Icall sig ros args res s =>
      match is_known_runtime_function dm ros with
      | none => instr
      | some _ =>
          let nres := nreg (PMap.get pc an).1 res
          if is_dead nres then .Inop s else instr
  | .Ibuiltin (.EF_memcpy sz _) (dst :: src :: []) res s =>
      if nmem_contains (PMap.get pc an).2
          (aaddr_arg cfg (PMap.get pc approx) dst) sz
      then instr else .Inop s
  | .Ibuiltin (.EF_builtin name sg) args res s =>
      match lookup_builtin_function name sg, builtin_res_dead res (PMap.get pc an).1 with
      | some _, true => .Inop s
      | _, _ => instr
  | .Icond _ _ s1 s2 =>
      match peq s1 s2 with
      | .left _ => .Inop s1
      | .right _ => instr
  | _ => instr

def transf_function (cfg : CompilerConfig) (dm : defmap) (rm : romem)
    (f : function) : res function :=
  let approx := ValueAnalysis.analyze cfg rm f
  match analyze cfg f dm approx with
  | some an =>
      OK
        { fn_sig := f.fn_sig
          fn_params := f.fn_params
          fn_stacksize := f.fn_stacksize
          fn_code := PTree.map (transf_instr cfg dm approx an) f.fn_code
          fn_entrypoint := f.fn_entrypoint }
  | none => Error (msg needednessAnalysisFailedText)

def transf_fundef (cfg : CompilerConfig) (dm : defmap) (rm : romem)
    (fd : fundef) : res fundef :=
  CompCert4Lean.Common.AST.transf_partial_fundef
    (transf_function cfg dm rm) fd

def transf_program (cfg : CompilerConfig) (p : program) : res program :=
  CompCert4Lean.Common.AST.transform_partial_program
    (transf_fundef cfg (prog_defmap p) (romem_for cfg p)) p

end CompCert4Lean.Backend.Deadcode
