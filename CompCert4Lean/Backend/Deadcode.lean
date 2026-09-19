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
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
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

/-! Exact proposition of Rocq's generated `transfer_builtin_ind` scheme.
The explicit `CompilerConfig` parameter is the authenticated configuration
seam used by the translated source equations.  Its proof term remains assigned
to the later proof-migration phase. -/
def transfer_builtin_indStatement (cfg : CompilerConfig) : Prop :=
  ∀ (app : VA.t)
    (P : external_function → List (builtin_arg reg) → builtin_res reg →
      NE.t → nmem → NA.t → Prop),
    (∀ (ef : external_function) (args : List (builtin_arg reg))
      (res : builtin_res reg) (ne : NE.t) (nm : nmem) (chunk : memory_chunk),
      ef = .EF_vload chunk →
      ∀ (a1 : builtin_arg reg), args = [a1] →
        P (.EF_vload chunk) [a1] res ne nm
          (transfer_builtin_arg All
            (kill_builtin_res res ne,
              nmem_add nm (aaddr_arg cfg app a1) (size_chunk chunk)) a1)) →
    (∀ (ef : external_function) (args : List (builtin_arg reg))
      (res : builtin_res reg) (ne : NE.t) (nm : nmem) (chunk : memory_chunk),
      ef = .EF_vstore chunk →
      ∀ (a1 a2 : builtin_arg reg), args = [a1, a2] →
        P (.EF_vstore chunk) [a1, a2] res ne nm
          (transfer_builtin_arg All
            (transfer_builtin_arg (store_argument chunk)
              (kill_builtin_res res ne, nm) a2) a1)) →
    (∀ (ef : external_function) (args : List (builtin_arg reg))
      (res : builtin_res reg) (ne : NE.t) (nm : nmem) (sz al : Z),
      ef = .EF_memcpy sz al →
      ∀ (dst src : builtin_arg reg), args = [dst, src] →
      nmem_contains nm (aaddr_arg cfg app dst) sz = true →
        P (.EF_memcpy sz al) [dst, src] res ne nm
          (transfer_builtin_args
            (kill_builtin_res res ne,
              nmem_add (nmem_remove nm (aaddr_arg cfg app dst) sz)
                (aaddr_arg cfg app src) sz) args)) →
    (∀ (ef : external_function) (args : List (builtin_arg reg))
      (res : builtin_res reg) (ne : NE.t) (nm : nmem) (sz al : Z),
      ef = .EF_memcpy sz al →
      ∀ (dst src : builtin_arg reg), args = [dst, src] →
      nmem_contains nm (aaddr_arg cfg app dst) sz = false →
        P (.EF_memcpy sz al) [dst, src] res ne nm (ne, nm)) →
    (∀ (ef : external_function) (args : List (builtin_arg reg))
      (res : builtin_res reg) (ne : NE.t) (nm : nmem) (kind : positive)
      (text : RocqString) (targs : List typ),
      ef = .EF_annot kind text targs →
      ∀ (args' : List (builtin_arg reg)), args = args' →
        P (.EF_annot kind text targs) args' res ne nm
          (transfer_builtin_args (kill_builtin_res res ne, nm) args)) →
    (∀ (ef : external_function) (args : List (builtin_arg reg))
      (res : builtin_res reg) (ne : NE.t) (nm : nmem) (kind : positive)
      (text : RocqString) (targ : typ),
      ef = .EF_annot_val kind text targ →
      ∀ (args' : List (builtin_arg reg)), args = args' →
        P (.EF_annot_val kind text targ) args' res ne nm
          (transfer_builtin_args (kill_builtin_res res ne, nm) args)) →
    (∀ (ef : external_function) (args : List (builtin_arg reg))
      (res : builtin_res reg) (ne : NE.t) (nm : nmem) (kind : positive)
      (id : ident) (targs : List typ),
      ef = .EF_debug kind id targs →
      ∀ (args' : List (builtin_arg reg)), args = args' →
        P (.EF_debug kind id targs) args' res ne nm
          (kill_builtin_res res ne, nm)) →
    (∀ (ef : external_function) (args : List (builtin_arg reg))
      (res : builtin_res reg) (ne : NE.t) (nm : nmem)
      (name : RocqString) (sg : signature),
      ef = .EF_builtin name sg →
      ∀ (args' : List (builtin_arg reg)), args = args' →
      ∀ (bf : builtin_function), lookup_builtin_function name sg = some bf →
      builtin_res_dead res ne = true →
        P (.EF_builtin name sg) args' res ne nm (ne, nm)) →
    (∀ (ef : external_function) (args : List (builtin_arg reg))
      (res : builtin_res reg) (ne : NE.t) (nm : nmem)
      (name : RocqString) (sg : signature),
      ef = .EF_builtin name sg →
      ∀ (args' : List (builtin_arg reg)), args = args' →
      ∀ (bf : builtin_function), lookup_builtin_function name sg = some bf →
      builtin_res_dead res ne = false →
        P (.EF_builtin name sg) args' res ne nm
          (transfer_builtin_args (kill_builtin_res res ne, nm) args')) →
    (∀ (ef : external_function) (args : List (builtin_arg reg))
      (res : builtin_res reg) (ne : NE.t) (nm : nmem)
      (name : RocqString) (sg : signature),
      ef = .EF_builtin name sg →
      ∀ (args' : List (builtin_arg reg)), args = args' →
      ∀ (found : Option builtin_function), lookup_builtin_function name sg = found →
      (match found with
       | some _ => False
       | none => True) →
        P (.EF_builtin name sg) args' res ne nm
          (transfer_builtin_args (kill_builtin_res res ne, nmem_all) args')) →
    (∀ (ef : external_function) (args : List (builtin_arg reg))
      (res : builtin_res reg) (ne : NE.t) (nm : nmem)
      (ef' : external_function),
      ef = ef' →
      ∀ (args' : List (builtin_arg reg)), args = args' →
      (match ef' with
       | .EF_vload _ =>
           match args' with
           | [_] => False
           | _ => True
       | .EF_vstore _ | .EF_memcpy _ _ =>
           match args' with
           | [_, _] => False
           | _ => True
       | .EF_builtin _ _ | .EF_annot _ _ _ | .EF_annot_val _ _ _ |
         .EF_debug _ _ _ => False
       | _ => True) →
        P ef' args' res ne nm
          (transfer_builtin_args (kill_builtin_res res ne, nmem_all) args)) →
    ∀ (ef : external_function) (args : List (builtin_arg reg))
      (res : builtin_res reg) (ne : NE.t) (nm : nmem),
      P ef args res ne nm (transfer_builtin cfg app ef args res ne nm)

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

def transf_function
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (dm : defmap) (rm : romem)
    (f : function) : res function :=
  let approx := ValueAnalysis.analyze
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) cfg rm f
  match analyze cfg f dm approx with
  | some an =>
      OK
        { fn_sig := f.fn_sig
          fn_params := f.fn_params
          fn_stacksize := f.fn_stacksize
          fn_code := PTree.map (transf_instr cfg dm approx an) f.fn_code
          fn_entrypoint := f.fn_entrypoint }
  | none => Error (msg needednessAnalysisFailedText)

def transf_fundef
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (dm : defmap) (rm : romem)
    (fd : fundef) : res fundef :=
  CompCert4Lean.Common.AST.transf_partial_fundef
    (transf_function
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      cfg dm rm) fd

def transf_program
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (p : program) : res program :=
  CompCert4Lean.Common.AST.transform_partial_program
    (transf_fundef
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      cfg (prog_defmap p) (romem_for cfg p)) p

end CompCert4Lean.Backend.Deadcode

namespace CompCert4Lean.Backend.Deadcode

open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Backend.ValueAnalysis
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Memdata

set_option maxHeartbeats 200000 in
theorem transfer_builtin_ind :
    ∀ (cfg : CompilerConfig), transfer_builtin_indStatement cfg := by
  intro cfg app P hvload hvstore hmemcpy_true hmemcpy_false hannot hannval hdebug
    hbuiltin_dead hbuiltin_live hbuiltin_missing hother ef args res ne nm
  cases ef with
  | EF_external name sg =>
      change P (.EF_external name sg) args res ne nm
        (transfer_builtin_args (kill_builtin_res res ne, nmem_all) args)
      exact hother _ _ _ _ _ _ rfl args rfl (by simp)
  | EF_runtime name sg =>
      change P (.EF_runtime name sg) args res ne nm
        (transfer_builtin_args (kill_builtin_res res ne, nmem_all) args)
      exact hother _ _ _ _ _ _ rfl args rfl (by simp)
  | EF_malloc =>
      change P .EF_malloc args res ne nm
        (transfer_builtin_args (kill_builtin_res res ne, nmem_all) args)
      exact hother _ _ _ _ _ _ rfl args rfl (by simp)
  | EF_free =>
      change P .EF_free args res ne nm
        (transfer_builtin_args (kill_builtin_res res ne, nmem_all) args)
      exact hother _ _ _ _ _ _ rfl args rfl (by simp)
  | EF_inline_asm text sg clobbers =>
      change P (.EF_inline_asm text sg clobbers) args res ne nm
        (transfer_builtin_args (kill_builtin_res res ne, nmem_all) args)
      exact hother _ _ _ _ _ _ rfl args rfl (by simp)
  | EF_vload chunk =>
      cases args with
      | nil =>
          change P (.EF_vload chunk) [] res ne nm
            (transfer_builtin_args (kill_builtin_res res ne, nmem_all) [])
          exact hother _ _ _ _ _ _ rfl [] rfl (by simp)
      | cons a1 rest =>
          cases rest with
          | nil =>
              change P (.EF_vload chunk) [a1] res ne nm
                (transfer_builtin_arg All
                  (kill_builtin_res res ne,
                    nmem_add nm (aaddr_arg cfg app a1) (size_chunk chunk)) a1)
              exact hvload _ _ _ _ _ _ rfl a1 rfl
          | cons a2 rest' =>
              change P (.EF_vload chunk) (a1 :: a2 :: rest') res ne nm
                (transfer_builtin_args (kill_builtin_res res ne, nmem_all)
                  (a1 :: a2 :: rest'))
              exact hother _ _ _ _ _ _ rfl (a1 :: a2 :: rest') rfl (by simp)
  | EF_vstore chunk =>
      cases args with
      | nil =>
          change P (.EF_vstore chunk) [] res ne nm
            (transfer_builtin_args (kill_builtin_res res ne, nmem_all) [])
          exact hother _ _ _ _ _ _ rfl [] rfl (by simp)
      | cons a1 rest =>
          cases rest with
          | nil =>
              change P (.EF_vstore chunk) [a1] res ne nm
                (transfer_builtin_args (kill_builtin_res res ne, nmem_all) [a1])
              exact hother _ _ _ _ _ _ rfl [a1] rfl (by simp)
          | cons a2 rest' =>
              cases rest' with
              | nil =>
                  change P (.EF_vstore chunk) [a1, a2] res ne nm
                    (transfer_builtin_arg All
                      (transfer_builtin_arg (store_argument chunk)
                        (kill_builtin_res res ne, nm) a2) a1)
                  exact hvstore _ _ _ _ _ _ rfl a1 a2 rfl
              | cons a3 rest'' =>
                  change P (.EF_vstore chunk) (a1 :: a2 :: a3 :: rest'')
                    res ne nm
                    (transfer_builtin_args (kill_builtin_res res ne, nmem_all)
                      (a1 :: a2 :: a3 :: rest''))
                  exact hother _ _ _ _ _ _ rfl (a1 :: a2 :: a3 :: rest'') rfl
                    (by simp)
  | EF_memcpy sz al =>
      cases args with
      | nil =>
          change P (.EF_memcpy sz al) [] res ne nm
            (transfer_builtin_args (kill_builtin_res res ne, nmem_all) [])
          exact hother _ _ _ _ _ _ rfl [] rfl (by simp)
      | cons dst rest =>
          cases rest with
          | nil =>
              change P (.EF_memcpy sz al) [dst] res ne nm
                (transfer_builtin_args (kill_builtin_res res ne, nmem_all) [dst])
              exact hother _ _ _ _ _ _ rfl [dst] rfl (by simp)
          | cons src rest' =>
              cases rest' with
              | nil =>
                  by_cases hcontains : nmem_contains nm (aaddr_arg cfg app dst) sz = true
                  · dsimp [transfer_builtin]
                    simp only [hcontains]
                    exact hmemcpy_true _ _ _ _ _ _ _ rfl dst src rfl hcontains
                  · have hfalse : nmem_contains nm (aaddr_arg cfg app dst) sz = false := by
                      cases h : nmem_contains nm (aaddr_arg cfg app dst) sz <;> simp_all
                    dsimp [transfer_builtin]
                    simp only [hcontains]
                    exact hmemcpy_false _ _ _ _ _ _ _ rfl dst src rfl hfalse
              | cons a3 rest'' =>
                  change P (.EF_memcpy sz al) (dst :: src :: a3 :: rest'')
                    res ne nm
                    (transfer_builtin_args (kill_builtin_res res ne, nmem_all)
                      (dst :: src :: a3 :: rest''))
                  exact hother _ _ _ _ _ _ rfl (dst :: src :: a3 :: rest'') rfl
                    (by simp)
  | EF_annot kind text targs =>
      change P (.EF_annot kind text targs) args res ne nm
        (transfer_builtin_args (kill_builtin_res res ne, nm) args)
      exact hannot _ _ _ _ _ _ _ _ rfl args rfl
  | EF_annot_val kind text targ =>
      change P (.EF_annot_val kind text targ) args res ne nm
        (transfer_builtin_args (kill_builtin_res res ne, nm) args)
      exact hannval _ _ _ _ _ _ _ _ rfl args rfl
  | EF_debug kind id targs =>
      change P (.EF_debug kind id targs) args res ne nm
        (kill_builtin_res res ne, nm)
      exact hdebug _ _ _ _ _ _ _ _ rfl args rfl
  | EF_builtin name sg =>
      cases hlookup : lookup_builtin_function name sg with
      | none =>
          dsimp [transfer_builtin]
          rw [hlookup]
          exact hbuiltin_missing _ _ _ _ _ _ _ rfl args rfl none hlookup (by simp)
      | some bf =>
          cases hdead : builtin_res_dead res ne with
          | false =>
              dsimp [transfer_builtin]
              rw [hlookup]
              simp only [hdead]
              exact hbuiltin_live _ _ _ _ _ _ _ rfl args rfl bf hlookup hdead
          | true =>
              dsimp [transfer_builtin]
              rw [hlookup]
              simp only [hdead]
              exact hbuiltin_dead _ _ _ _ _ _ _ rfl args rfl bf hlookup hdead

end CompCert4Lean.Backend.Deadcode

namespace CompCert4Lean.Backend.Deadcode
namespace DS

theorem fixpoint_solution_proof :
    ∀ (laws : law_obligation), fixpoint_solution laws := by
  intro laws
  intro A code successors transf res n instr s hfix hcode hsucc hbot
  exact CompCert4Lean.Backend.Kildall.Backward_Dataflow_Solver.fixpoint_solution
    (LAT := L) (NS := CompCert4Lean.Backend.Kildall.NodeSetBackward) laws.1 laws.2
    code successors transf res n instr s hfix hcode hsucc hbot

end DS
end CompCert4Lean.Backend.Deadcode

namespace CompCert4Lean.Backend.Deadcode
open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Backend.Kildall
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.IntvSets
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open Lean Elab Tactic Meta
private theorem t1 : ∀ x, NVal.eq x x := by intro x; rfl
private theorem t2 : ∀ x y, NVal.eq x y → NVal.eq y x := by intro x y h; exact h.symm
private theorem t3 : ∀ x y z, NVal.eq x y → NVal.eq y z → NVal.eq x z := by intro x y z h1 h2; exact h1.trans h2
private theorem t4 : ∀ x y, NVal.beq x y = true → NVal.eq x y := by
  intro x y h
  unfold NVal.beq at h
  cases he : eq_nval x y with
  | left hxy => exact hxy
  | right hxy => simp [CompCert4Lean.Lib.Coqlib.proj_sumbool, he] at h
private theorem t5 : ∀ x y, NVal.eq x y → NVal.ge x y := by
  intro x y h; subst y
  cases x with
  | Nothing => exact nge.nge_all _
  | All => exact nge.nge_nothing _
  | I m => exact nge.nge_int m m (by intro i hi hm; exact hm)
  | L m => exact nge.nge_long m m (by intro i hi hm; exact hm)
private theorem t6 : ∀ x y z, NVal.ge x y → NVal.ge y z → NVal.ge x z := by
  intro x y z hxy hyz
  cases hxy with
  | nge_nothing a => exact nge.nge_nothing z
  | nge_all a =>
      cases hyz with
      | nge_all => exact nge.nge_all _
  | nge_int m1 m2 h12 =>
      cases hyz with
      | nge_all => exact nge.nge_all _
      | nge_int m2' m3 h23 =>
          apply nge.nge_int m1 m3
          intro i hi hm
          exact h12 i hi (h23 i hi hm)
  | nge_long m1 m2 h12 =>
      cases hyz with
      | nge_all => exact nge.nge_all _
      | nge_long m2' m3 h23 =>
          apply nge.nge_long m1 m3
          intro i hi hm
          exact h12 i hi (h23 i hi hm)
private theorem t7 : ∀ x, NVal.ge x NVal.bot := by intro x; exact nge.nge_all x
private theorem t8 : ∀ x y, NVal.ge (NVal.lub x y) x := by intro x y; exact CompCert4Lean.Backend.NeedDomain.nge_lub_l x y
private def privateNameX (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base
private theorem residue_zOfNatX (bits n : Nat) :
    (WordCore.repr bits (ZArith.BinInt.Z.of_nat n)).val = n % (2 ^ bits) := by
  run_tac
    let lctx ← getLCtx
    let bitsF := (lctx.findFromUserName? `bits).get!
    let nF := (lctx.findFromUserName? `n).get!
    let bitsE := mkFVar bitsF.fvarId
    let nE := mkFVar nF.fvarId
    let z := mkApp (mkConst ``ZArith.BinInt.Z.of_nat) nE
    let e1 := mkApp2 (mkConst (privateNameX "CompCert4Lean.Lib.Integers.WordCore.val_repr_residue")) bitsE z
    let e2 := mkApp2 (mkConst (privateNameX "CompCert4Lean.Lib.Integers.WordCore.residue_zOfNat")) bitsE nE
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
private theorem int64_or_valX (x y : Int64.int) :
    (Int64.or x y).val = Nat.lor x.val y.val % (2 ^ Int64.wordsize) := by
  unfold Int64.or WordCore.or
  exact residue_zOfNatX Int64.wordsize (Nat.lor x.val y.val)
private theorem word64_val_ltX (x : Int64.int) : x.val < 2 ^ Int64.wordsize := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let xE := mkFVar xF.fvarId
    let e ← mkAppM (privateNameX "CompCert4Lean.Lib.Integers.WordCore.val_lt") #[xE]
    closeMainGoal Name.anonymous e
private theorem nat_or_mod_testbitX (a b w k : Nat) (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
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
private theorem int64_or_testbitX (x y : Int64.int) (i : Z) :
    Int64.testbit (Int64.or x y) i = (Int64.testbit x i || Int64.testbit y i) := by
  cases i with
  | Zneg p => rfl
  | Z0 =>
      simp only [Int64.testbit, WordCore.testbit]
      change Nat.testBit (Int64.or x y).val 0 = (Nat.testBit x.val 0 || Nat.testBit y.val 0)
      rw [int64_or_valX]
      exact nat_or_mod_testbitX x.val y.val Int64.wordsize 0
        (word64_val_ltX x) (word64_val_ltX y)
  | Zpos p =>
      simp only [Int64.testbit, WordCore.testbit]
      change Nat.testBit (Int64.or x y).val _ = _
      rw [int64_or_valX]
      exact nat_or_mod_testbitX x.val y.val Int64.wordsize _
        (word64_val_ltX x) (word64_val_ltX y)

private theorem t9 : ∀ x y, NVal.ge (NVal.lub x y) y := by
  intro x y
  cases y with
  | Nothing => exact nge.nge_all _
  | All => cases x <;> change nge All All <;> exact nge.nge_nothing All
  | I m2 =>
      cases x with
      | Nothing => exact nge.nge_int m2 m2 (by intro i hi hm; exact hm)
      | I m1 =>
          apply nge.nge_int (Int.or m1 m2) m2
          intro i hi hm
          rw [CompCert4Lean.Lib.Integers.Int.bits_or_proof m1 m2 i hi]
          exact Bool.or_eq_true_iff.mpr (Or.inr hm)
      | L _ | All => exact nge.nge_nothing _
  | L m2 =>
      cases x with
      | Nothing => exact nge.nge_long m2 m2 (by intro i hi hm; exact hm)
      | I _ | All => exact nge.nge_nothing _
      | L m1 =>
          apply nge.nge_long (Int64.or m1 m2) m2
          intro i hi hm
          rw [int64_or_testbitX]
          exact Bool.or_eq_true_iff.mpr (Or.inr hm)

private theorem na_iset_beq_eq : ∀ (s1 s2 : ISet.t), ISet.beq s1 s2 = true → s1 = s2 := by
  intro s1 s2 h
  rcases s1 with ⟨r1, o1⟩
  rcases s2 with ⟨r2, o2⟩
  apply Subtype.ext
  change r1 = r2
  change ISet.R.beq r1 r2 = true at h
  clear o1 o2
  induction r1 generalizing r2 with
  | Nil =>
      cases r2 <;> simp [ISet.R.beq] at h
      exact rfl
  | Cons l h1 t ih =>
      cases r2 with
      | Nil => simp [ISet.R.beq] at h
      | Cons l2 h2 t2 =>
          have hhall : (l = l2 ∧ h1 = h2) ∧ ISet.R.beq t t2 = true := by
            simpa [ISet.R.beq] using h
          have hp : l = l2 ∧ h1 = h2 := hhall.1
          have ht : ISet.R.beq t t2 = true := hhall.2
          have ht' : t = t2 := ih t2 ht
          rcases hp with ⟨hl, hh⟩
          subst l2; subst h2; subst t2
          rfl
private theorem na_nmem_beq_eq : ∀ (m1 m2 : nmem), nmem_beq m1 m2 = true → m1 = m2 := by
  intro m1 m2 h
  cases m1 with
  | NMemDead =>
      cases m2 with
      | NMemDead => rfl
      | NMem stk gl => simp [nmem_beq] at h
  | NMem stk1 gl1 =>
      cases m2 with
      | NMemDead => simp [nmem_beq] at h
      | NMem stk2 gl2 =>
          have hh : ISet.beq stk1 stk2 = true ∧ PTree.beq ISet.beq gl1 gl2 = true := by
            simpa [nmem_beq] using h
          have hstk : stk1 = stk2 := na_iset_beq_eq stk1 stk2 hh.1
          have hpt := (PTree.beq_correct_proof ISet.beq gl1 gl2).mp hh.2
          have hgl : gl1 = gl2 := PTree.extensionality gl1 gl2 (by
            intro id
            cases h1 : PTree.get id gl1 with
            | none =>
                cases h2 : PTree.get id gl2 with
                | none => simp [h1, h2]
                | some s2 =>
                    have hx := hpt id
                    simp [h1, h2] at hx
            | some s1 =>
                cases h2 : PTree.get id gl2 with
                | none =>
                    have hx := hpt id
                    simp [h1, h2] at hx
                | some s2 =>
                    have hx := hpt id
                    have hs : ISet.beq s1 s2 = true := by simpa [h1, h2] using hx
                    have he := na_iset_beq_eq s1 s2 hs
                    simpa [h1, h2] using he)
          subst stk2
          subst gl2
          rfl
private theorem na_nlive_lub_left :
    ∀ (ge : CompCert4Lean.Backend.RTL.genv) (sp : CompCert4Lean.Common.Values.block)
      (m1 m2 : nmem) (b : CompCert4Lean.Common.Values.block)
      (ofs : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z),
      nlive ge sp m1 b ofs → nlive ge sp (nmem_lub m1 m2) b ofs := by
  intro ge sp m1 m2 b ofs h
  cases m1 with
  | NMemDead => cases h
  | NMem stk1 gl1 =>
      cases m2 with
      | NMemDead => simpa [nmem_lub]
      | NMem stk2 gl2 =>
          cases h with
          | nlive_intro _ _ _ _ hstk hgl =>
              apply nlive.nlive_intro (ISet.inter stk1 stk2)
                (PTree.combine (fun o1 o2 =>
                  match o1, o2 with
                  | some iv1, some iv2 => some (ISet.inter iv1 iv2)
                  | _, _ => none) gl1 gl2) b ofs
              · intro hbsp hmem
                apply hstk hbsp
                have hi := ISet.R.In_inter ofs stk1.1 stk1.2 stk2.1 stk2.2
                exact hi.mp hmem |>.1
              · intro id iv hfind hget
                have hc := PTree.gcombine_proof (A := ISet.t) (B := ISet.t) (C := ISet.t)
                  (fun o1 o2 => match o1, o2 with
                  | some iv1, some iv2 => some (ISet.inter iv1 iv2)
                  | _, _ => none) (by rfl) gl1 gl2 (id : positive)
                rw [hc] at hget
                cases h1 : PTree.get id gl1 with
                | none => cases h2 : PTree.get id gl2 <;> simp [h1, h2] at hget
                | some iv1 =>
                    cases h2 : PTree.get id gl2 with
                    | none => simp [h1, h2] at hget
                    | some iv2 =>
                        simp [h1, h2] at hget
                        subst iv
                        intro hin
                        apply hgl id iv1 hfind h1
                        have hi := ISet.R.In_inter ofs iv1.1 iv1.2 iv2.1 iv2.2
                        exact (hi.mp hin).1
private theorem na_nlive_lub_right :
    ∀ (ge : CompCert4Lean.Backend.RTL.genv) (sp : CompCert4Lean.Common.Values.block)
      (m1 m2 : nmem) (b : CompCert4Lean.Common.Values.block)
      (ofs : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z),
      nlive ge sp m2 b ofs → nlive ge sp (nmem_lub m1 m2) b ofs := by
  intro ge sp m1 m2 b ofs h
  cases m2 with
  | NMemDead => cases m1 with
      | NMemDead => cases h
      | NMem _ _ => cases h
  | NMem stk2 gl2 =>
      cases m1 with
      | NMemDead => simpa [nmem_lub]
      | NMem stk1 gl1 =>
          cases h with
          | nlive_intro _ _ _ _ hstk hgl =>
              apply nlive.nlive_intro (ISet.inter stk1 stk2)
                (PTree.combine (fun o1 o2 =>
                  match o1, o2 with
                  | some iv1, some iv2 => some (ISet.inter iv1 iv2)
                  | _, _ => none) gl1 gl2) b ofs
              · intro hbsp hmem
                apply hstk hbsp
                have hi := ISet.R.In_inter ofs stk1.1 stk1.2 stk2.1 stk2.2
                exact hi.mp hmem |>.2
              · intro id iv hfind hget
                have hc := PTree.gcombine_proof (A := ISet.t) (B := ISet.t) (C := ISet.t)
                  (fun o1 o2 => match o1, o2 with
                  | some iv1, some iv2 => some (ISet.inter iv1 iv2)
                  | _, _ => none) (by rfl) gl1 gl2 (id : positive)
                rw [hc] at hget
                cases h1 : PTree.get id gl1 with
                | none => cases h2 : PTree.get id gl2 <;> simp [h1, h2] at hget
                | some iv1 =>
                    cases h2 : PTree.get id gl2 with
                    | none => simp [h1, h2] at hget
                    | some iv2 =>
                        simp [h1, h2] at hget
                        subst iv
                        intro hin
                        apply hgl id iv2 hfind h2
                        have hi := ISet.R.In_inter ofs iv1.1 iv1.2 iv2.1 iv2.2
                        exact (hi.mp hin).2
private def na_getD : Option NVal.t → NVal.t
  | none => NVal.bot
  | some v => v
private theorem na_ne_lub_get : ∀ (x y : NE.t) (p : positive),
  NE.get p (NE.lub x y) = na_getD ((fun a b =>
    match a,b with | some u,some v=>some (NVal.lub u v) | none,_=>b | _,none=>a)
       (PTree.get p x) (PTree.get p y)) := by
  intro x y p
  unfold NE.get NE.lub
  have hc := PTree.gcombine_proof (A:=NVal.t) (B:=NVal.t) (C:=NVal.t)
    (fun a b => match a,b with | some u,some v=>some (NVal.lub u v) | none,_=>b | _,none=>a)
    (by rfl) x y p
  exact congrArg na_getD hc
private theorem na_ne_eq_refl : ∀ x : NE.t, NE.eq x x := by intro x p; exact t1 _
private theorem na_ne_eq_sym : ∀ x y : NE.t, NE.eq x y -> NE.eq y x := by intro x y h p; exact t2 _ _ (h p)
private theorem na_ne_eq_trans : ∀ x y z : NE.t, NE.eq x y -> NE.eq y z -> NE.eq x z := by intro x y z h k p; exact t3 _ _ _ (h p) (k p)
private theorem na_ne_beq : ∀ x y : NE.t, NE.beq x y = true -> NE.eq x y := by
  intro x y h p
  have hp := (PTree.beq_correct_proof NVal.beq x y).mp h p
  cases hx : PTree.get p x with
  | none =>
      cases hy : PTree.get p y with
      | none => simpa only [NE.get, hx, hy] using (t1 NVal.bot)
      | some v => simp [NE.get, hx, hy] at hp
  | some u =>
      cases hy : PTree.get p y with
      | none => simp [NE.get, hx, hy] at hp
      | some v =>
          have huv : NVal.eq u v := t4 u v (by simpa [hx, hy] using hp)
          simpa only [NE.get, hx, hy] using huv
private theorem na_ne_ge_refl : ∀ x y : NE.t, NE.eq x y -> NE.ge x y := by intro x y h p; exact t5 _ _ (h p)
private theorem na_ne_ge_trans : ∀ x y z : NE.t, NE.ge x y -> NE.ge y z -> NE.ge x z := by intro x y z h k p; exact t6 _ _ _ (h p) (k p)
private theorem na_ne_ge_bot : ∀ x : NE.t, NE.ge x NE.bot := by intro x p; exact t7 _
private theorem na_ne_lub_left : ∀ x y : NE.t, NE.ge (NE.lub x y) x := by
  intro x y p
  cases hx : PTree.get p x with
  | none =>
      cases hy : PTree.get p y with
      | none =>
          rw [na_ne_lub_get]
          simp [na_getD, hx, hy, NE.get]
          exact t7 _
      | some v =>
          rw [na_ne_lub_get]
          simp [na_getD, hx, hy, NE.get]
          exact t7 _
  | some u =>
      cases hy : PTree.get p y with
      | none =>
          rw [na_ne_lub_get]
          simp [na_getD, hx, hy, NE.get]
          exact t5 u u rfl
      | some v =>
          rw [na_ne_lub_get]
          simp [na_getD, hx, hy, NE.get]
          exact t8 u v
private theorem na_ne_lub_right : ∀ x y : NE.t, NE.ge (NE.lub x y) y := by
  intro x y p
  cases hx : PTree.get p x with
  | none =>
      cases hy : PTree.get p y with
      | none =>
          rw [na_ne_lub_get]
          simp [na_getD, hx, hy, NE.get]
          exact t7 _
      | some v =>
          rw [na_ne_lub_get]
          simp [na_getD, hx, hy, NE.get]
          exact t5 v v rfl
  | some u =>
      cases hy : PTree.get p y with
      | none =>
          rw [na_ne_lub_get]
          simp [na_getD, hx, hy, NE.get]
          exact t7 _
      | some v =>
          rw [na_ne_lub_get]
          simp [na_getD, hx, hy, NE.get]
          exact t9 u v
theorem solver_law_obligation_proof : solver_law_obligation := by
  unfold solver_law_obligation na_lattice
  constructor
  · constructor
    · intro x
      change NA.t at x
      exact ⟨na_ne_eq_refl x.1, by intro ge sp b ofs; rfl⟩
    · intro x y h
      change NA.t at x y
      exact ⟨na_ne_eq_sym _ _ h.1, by intro ge sp b ofs; exact (h.2 ge sp b ofs).symm⟩
    · intro x y z hxy hyz
      change NA.t at x y z
      exact ⟨na_ne_eq_trans _ _ _ hxy.1 hyz.1, by intro ge sp b ofs; exact Iff.trans (hxy.2 ge sp b ofs) (hyz.2 ge sp b ofs)⟩
    · intro x y h
      change NA.t at x y
      have hh : NE.beq x.1 y.1 = true ∧ nmem_beq x.2 y.2 = true := by simpa [NA.beq] using h
      have hne : NE.eq x.1 y.1 := na_ne_beq _ _ hh.1
      have hmem : x.2 = y.2 := na_nmem_beq_eq _ _ hh.2
      have hmiff : ∀ ge sp b ofs, nlive ge sp x.2 b ofs ↔ nlive ge sp y.2 b ofs := by
        intro ge sp b ofs
        rw [hmem]
      exact ⟨hne, hmiff⟩
    · intro x y h
      change NA.t at x y
      exact ⟨na_ne_ge_refl _ _ h.1, by intro ge sp b ofs hm; exact (h.2 ge sp b ofs).mpr hm⟩
    · intro x y z hxy hyz
      change NA.t at x y z
      exact ⟨na_ne_ge_trans _ _ _ hxy.1 hyz.1, by intro ge sp b ofs hm; exact hxy.2 ge sp b ofs (hyz.2 ge sp b ofs hm)⟩
    · intro x
      change NA.t at x
      exact ⟨na_ne_ge_bot _, by intro ge sp b ofs hm; cases hm⟩
    · intro x y
      change NA.t at x y
      exact ⟨na_ne_lub_left _ _, by intro ge sp b ofs hm; exact na_nlive_lub_left ge sp x.2 y.2 b ofs hm⟩
    · intro x y
      change NA.t at x y
      exact ⟨na_ne_lub_right _ _, by intro ge sp b ofs hm; exact na_nlive_lub_right ge sp x.2 y.2 b ofs hm⟩
  · exact CompCert4Lean.Backend.Kildall.NodeSetBackward.law_obligation_proof
end CompCert4Lean.Backend.Deadcode
