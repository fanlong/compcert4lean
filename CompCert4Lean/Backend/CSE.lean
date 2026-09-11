import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.RocqString
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Builtins
import CompCert4Lean.Common.Errors
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Memdata
import CompCert4Lean.Common.Values
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Maps
import CompCert4Lean.Backend.CSEdomain
import CompCert4Lean.Backend.Kildall
import CompCert4Lean.Backend.Registers
import CompCert4Lean.Backend.RTL
import CompCert4Lean.Backend.ValueAnalysis
import CompCert4Lean.Backend.ValueDomain
import CompCert4Lean.X86.CombineOp
import CompCert4Lean.X86.Op

/-!
# Common-subexpression elimination

Definition-bearing translation of CompCert's `backend/CSE.v`.  The source
solver and proof modules are outside this packet; the executable value-numbering
and transformation surfaces are retained here with the source names.
-/

namespace CompCert4Lean.Backend.CSE

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List
open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Backend.Kildall
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueAnalysis
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Op

private abbrev Ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev z0 : Z := .Z0
private abbrev z1 : Z := .Zpos .xH
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zMod := ZArith.BinInt.Z.modulo
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zToNat := ZArith.BinInt.Z.to_nat
private abbrev reg := CompCert4Lean.Backend.Registers.reg
private abbrev node := CompCert4Lean.Backend.RTL.node
private abbrev function := CompCert4Lean.Backend.RTL.function
private abbrev instruction := CompCert4Lean.Backend.RTL.instruction
private abbrev defmap := CompCert4Lean.Backend.RTL.defmap
private abbrev program := CompCert4Lean.Backend.RTL.program
private abbrev romem := CompCert4Lean.Backend.ValueDomain.romem
private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

/- Public names for the two fixed certificate domains make the exact generated
   solver theorem telescopes addressable by inventory probes without exposing
   the file-local representation aliases above. -/
abbrev Binary64NormalizeCertificate :=
  BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)

abbrev Binary32NormalizeCertificate :=
  BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)
private abbrev Res := CompCert4Lean.Common.Errors.res
private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string
private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
private abbrev valnum := CompCert4Lean.Backend.CSEdomain.valnum

private def boolOfSumbool {P Q : Prop} : Sumbool P Q → Bool
  | .left _ => true
  | .right _ => false

private def bytesToString : List UInt8 → RocqString
  | [] => .EmptyString
  | b :: bs => .String b (bytesToString bs)

private def zleBool (x y : Z) : Bool :=
  boolOfSumbool (CompCert4Lean.Lib.Coqlib.zle x y)

private def cseFailureText : RocqString :=
  bytesToString [67, 83, 69, 32, 102, 97, 105, 108, 117, 114, 101]

def valnum_reg (n : numbering) (r : reg) : numbering × valnum :=
  match PTree.get r n.num_reg with
  | some v => (n, v)
  | none =>
      let v := n.num_next
      ({ num_next := PArith.BinPos.Pos.succ v
         num_eqs := n.num_eqs
         num_reg := PTree.set r v n.num_reg
         num_val := PMap.set v (r :: []) n.num_val }, v)

def valnum_regs (n : numbering) : List reg → numbering × List valnum
  | [] => (n, [])
  | r :: rs =>
      let (n1, v1) := valnum_reg n r
      let (ns, vs) := valnum_regs n1 rs
      (ns, v1 :: vs)

def valnum_builtin_arg (n : numbering) : builtin_arg reg → numbering × builtin_arg valnum
  | .BA r =>
      let (n', v) := valnum_reg n r
      (n', .BA v)
  | .BA_int i => (n, .BA_int i)
  | .BA_long i => (n, .BA_long i)
  | .BA_float f => (n, .BA_float f)
  | .BA_single f => (n, .BA_single f)
  | .BA_loadstack chunk ofs => (n, .BA_loadstack chunk ofs)
  | .BA_addrstack ofs => (n, .BA_addrstack ofs)
  | .BA_loadglobal chunk id ofs => (n, .BA_loadglobal chunk id ofs)
  | .BA_addrglobal id ofs => (n, .BA_addrglobal id ofs)
  | .BA_splitlong a1 a2 =>
      let (n1, v1) := valnum_builtin_arg n a1
      let (n2, v2) := valnum_builtin_arg n1 a2
      (n2, .BA_splitlong v1 v2)
  | .BA_addptr a1 a2 =>
      let (n1, v1) := valnum_builtin_arg n a1
      let (n2, v2) := valnum_builtin_arg n1 a2
      (n2, .BA_addptr v1 v2)

def valnum_builtin_args (n : numbering) : List (builtin_arg reg) → numbering × List (builtin_arg valnum)
  | [] => (n, [])
  | arg1 :: args =>
      let (n1, v1) := valnum_builtin_arg n arg1
      let (ns, vs) := valnum_builtin_args n1 args
      (ns, v1 :: vs)

def find_valnum_rhs (r : rhs) : List equation → Option valnum
  | [] => none
  | .Eq v strict r' :: eqs1 =>
      if strict && compat_rhs r r' then some v else find_valnum_rhs r eqs1

def find_valnum_rhs' (r : rhs) : List equation → Option valnum
  | [] => none
  | .Eq v _ r' :: eqs1 =>
      if compat_rhs r r' then some v else find_valnum_rhs' r eqs1

def find_valnum_num (v : valnum) : List equation → Option rhs
  | [] => none
  | .Eq v' strict r' :: eqs1 =>
      if strict && boolOfSumbool (peq v v') then some r' else find_valnum_num v eqs1

def reg_valnum (n : numbering) (vn : valnum) : Option reg :=
  match PMap.get vn n.num_val with
  | [] => none
  | r :: _ => some r

def regs_valnums (n : numbering) : List valnum → Option (List reg)
  | [] => some []
  | v1 :: vs =>
      match reg_valnum n v1, regs_valnums n vs with
      | some r1, some rs => some (r1 :: rs)
      | _, _ => none

def find_rhs (n : numbering) (rh : rhs) : Option reg :=
  match find_valnum_rhs' rh n.num_eqs with
  | none => none
  | some vres => reg_valnum n vres

def forget_reg (n : numbering) (rd : reg) : PMap.t (List reg) :=
  match PTree.get rd n.num_reg with
  | none => n.num_val
  | some v =>
      PMap.set v
        (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.remove peq rd
          (PMap.get v n.num_val)) n.num_val

def update_reg (n : numbering) (rd : reg) (vn : valnum) : PMap.t (List reg) :=
  let nv := forget_reg n rd
  PMap.set vn (rd :: PMap.get vn nv) nv

def add_rhs (n : numbering) (rd : reg) (rh : rhs) : numbering :=
  match find_valnum_rhs rh n.num_eqs with
  | some vres =>
      { num_next := n.num_next
        num_eqs := n.num_eqs
        num_reg := PTree.set rd vres n.num_reg
        num_val := update_reg n rd vres }
  | none =>
      { num_next := PArith.BinPos.Pos.succ n.num_next
        num_eqs := .Eq n.num_next true rh :: n.num_eqs
        num_reg := PTree.set rd n.num_next n.num_reg
        num_val := update_reg n rd n.num_next }

def add_op (n : numbering) (rd : reg) (op : operation) (rs : List reg) : numbering :=
  match is_move_operation op rs with
  | some r =>
      let (n1, v) := valnum_reg n r
      { num_next := n1.num_next
        num_eqs := n1.num_eqs
        num_reg := PTree.set rd v n1.num_reg
        num_val := update_reg n1 rd v }
  | none =>
      let (n1, vs) := valnum_regs n rs
      add_rhs n1 rd (.Op op vs)

def add_load (n : numbering) (rd : reg) (chunk : memory_chunk)
    (addr : addressing) (rs : List reg) (p : aptr) : numbering :=
  let (n1, vs) := valnum_regs n rs
  add_rhs n1 rd (.Load chunk addr vs p)

def add_builtin (n : numbering) (dst : builtin_res reg)
    (bf : builtin_function) (args : List (builtin_arg reg)) : numbering :=
  match dst with
  | .BR rd =>
      let (n1, args1) := valnum_builtin_args n args
      add_rhs n1 rd (.Builtin bf args1)
  | _ => n

def set_unknown (n : numbering) (rd : reg) : numbering :=
  { num_next := n.num_next
    num_eqs := n.num_eqs
    num_reg := PTree.remove rd n.num_reg
    num_val := forget_reg n rd }

def set_res_unknown (n : numbering) (res : builtin_res reg) : numbering :=
  match res with
  | .BR r => set_unknown n r
  | _ => n

def kill_eqs (pred : rhs → Bool) : List equation → List equation
  | [] => []
  | (.Eq l strict r) :: rem =>
      if pred r then kill_eqs pred rem else .Eq l strict r :: kill_eqs pred rem

def kill_equations (pred : rhs → Bool) (n : numbering) : numbering :=
  { num_next := n.num_next
    num_eqs := kill_eqs pred n.num_eqs
    num_reg := n.num_reg
    num_val := n.num_val }

def filter_loads : rhs → Bool
  | .Op op _ => op_depends_on_memory op
  | .Load _ _ _ _ => true
  | .Builtin _ args => builtin_args_depends_on_memory args

def kill_all_loads (n : numbering) : numbering :=
  kill_equations filter_loads n

def filter_after_store (n : numbering) (p : aptr) (sz : Z) : rhs → Bool
  | .Op op _ => op_depends_on_memory op
  | .Load chunk _ _ q => !pdisjoint q (size_chunk chunk) p sz
  | .Builtin _ args => builtin_args_depends_on_memory args

def kill_loads_after_store (cfg : CompilerConfig) (app : VA.t) (n : numbering)
    (chunk : memory_chunk) (addr : addressing) (args : List reg) : numbering :=
  let p := aaddressing cfg app addr args
  kill_equations (filter_after_store n p (size_chunk chunk)) n

def filter_cheap : rhs → Bool
  | .Op _ _ => true
  | .Load _ _ _ _ => true
  | .Builtin _ _ => false

def kill_cheap_computations (n : numbering) : numbering :=
  kill_equations filter_cheap n

def store_normalized_range : memory_chunk → aval
  | .Mbool => Uns Ptop (ZArith.BinInt.Z.of_nat 1)
  | .Mint8signed => Sgn Ptop (ZArith.BinInt.Z.of_nat 8)
  | .Mint8unsigned => Uns Ptop (ZArith.BinInt.Z.of_nat 8)
  | .Mint16signed => Sgn Ptop (ZArith.BinInt.Z.of_nat 16)
  | .Mint16unsigned => Uns Ptop (ZArith.BinInt.Z.of_nat 16)
  | _ => Vtop

def add_store_result (cfg : CompilerConfig) (app : VA.t) (n : numbering)
    (chunk : memory_chunk)
    (addr : addressing) (rargs : List reg) (rsrc : reg) : numbering :=
  if vincl (avalue app rsrc) (store_normalized_range chunk) then
    let (n1, vsrc) := valnum_reg n rsrc
    let (n2, vargs) := valnum_regs n1 rargs
    { num_next := n2.num_next
      num_eqs := .Eq vsrc false
          (.Load chunk addr vargs (aaddressing cfg app addr rargs)) :: n2.num_eqs
      num_reg := n2.num_reg
      num_val := n2.num_val }
  else n

def kill_loads_after_storebytes (n : numbering) (dst : aptr) (sz : Z) : numbering :=
  kill_equations (filter_after_store n dst sz) n

def shift_memcpy_eq (src sz delta : Z) (e : equation) : Option equation :=
  match e with
  | .Eq l strict (.Load chunk (.Ainstack i) _ _) =>
      let i' := Ptrofs.unsigned i
      let j := zAdd i' delta
      if zleBool src i' && zleBool (zAdd i' (size_chunk chunk)) (zAdd src sz) &&
          boolOfSumbool (zeq (zMod delta (align_chunk chunk)) z0) &&
          zleBool z0 j && zleBool j Ptrofs.max_unsigned then
        some (.Eq l strict
          (.Load chunk (.Ainstack (Ptrofs.repr j)) [] (Stk (Ptrofs.repr j))))
      else none
  | _ => none

def add_memcpy_eqs (src sz delta : Z) : List equation → List equation → List equation
  | [], eqs2 => eqs2
  | e :: eqs, eqs2 =>
      match shift_memcpy_eq src sz delta e with
      | none => add_memcpy_eqs src sz delta eqs eqs2
      | some e' => e' :: add_memcpy_eqs src sz delta eqs eqs2

def add_memcpy (n1 n2 : numbering) (asrc adst : aptr) (sz : Z) : numbering :=
  match asrc, adst with
  | .Stk src, .Stk dst =>
      { num_next := n2.num_next
        num_eqs := add_memcpy_eqs (Ptrofs.unsigned src) sz
          (zSub (Ptrofs.unsigned dst) (Ptrofs.unsigned src)) n1.num_eqs n2.num_eqs
        num_reg := n2.num_reg
        num_val := n2.num_val }
  | _, _ => n2

section REDUCE

def reduce_rec {A : Type} (f : (valnum → Option rhs) → A → List valnum → Option (A × List valnum))
    (n : numbering) : Nat → A → List valnum → Option (A × List reg)
  | 0, _, _ => none
  | niter + 1, op, args =>
      match f (fun v => find_valnum_num v n.num_eqs) op args with
      | none => none
      | some (op', args') =>
          match reduce_rec f n niter op' args' with
          | none =>
              match regs_valnums n args' with
              | some rl => some (op', rl)
              | none => none
          | some res => some res

def reduce {A : Type} (f : (valnum → Option rhs) → A → List valnum → Option (A × List valnum))
    (n : numbering) (op : A) (rl : List reg) (vl : List valnum) : A × List reg :=
  match reduce_rec f n 4 op vl with
  | none => (op, rl)
  | some res => res

end REDUCE

namespace Numbering

def ge
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (n1 n2 : numbering) : Prop :=
  ∀ (valu : valuation) (genv : CompCert4Lean.Backend.RTL.genv)
    (sp : val) (rs : regset) (m : mem),
    numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      valu genv sp rs m n2 →
      numbering_holds
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        valu genv sp rs m n1

end Numbering

private def numberingSolver
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : OrderedTop :=
  { t := numbering
    ge := Numbering.ge
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
    top := empty_numbering }

/-! Generated surface for `Kildall.BBlock_solver(Numbering)`. -/
namespace Solver

def L
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : OrderedTop :=
  numberingSolver
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)

def law_obligation
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  OrderedTopLaws
    (L
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate))

def Solver
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Type 1 :=
  { solver : BBLOCK_SOLVER //
      solver.L = L
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ∧
      law_obligation
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) }

def fixpoint
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    {A : Type} (code : PTree.t A)
    (successors : A -> List positive)
    (transf : positive ->
      (L
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)).t ->
      (L
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)).t)
    (entrypoint : positive) : Option (PMap.t L.t) :=
  BBlock_solver.fixpoint
    (L
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate))
    code successors transf entrypoint

def fixpoint_solution
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (_laws : law_obligation
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)) : Prop :=
  ∀ (A : Type) (code : PTree.t A)
    (successors : A -> List positive)
    (transf : positive -> L.t -> L.t)
    (entrypoint : positive) (res : PMap.t L.t)
    (n : positive) (instr : A) (s : positive),
    fixpoint
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      code successors transf entrypoint = some res ->
    PTree.get n code = some instr ->
    s ∈ successors instr ->
    (L
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)).ge
      (PMap.get s res) (transf n (PMap.get n res))

def fixpoint_entry
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (_laws : law_obligation
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)) : Prop :=
  ∀ (A : Type) (code : PTree.t A)
    (successors : A -> List positive)
    (transf : positive -> L.t -> L.t)
    (entrypoint : positive) (res : PMap.t L.t),
    fixpoint
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      code successors transf entrypoint = some res ->
    PMap.get entrypoint res =
      (L
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)).top

def fixpoint_invariant
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (_laws : law_obligation
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)) : Prop :=
  ∀ (A : Type) (code : PTree.t A)
    (successors : A -> List positive)
    (transf : positive -> L.t -> L.t)
    (entrypoint : positive) (P : L.t -> Prop),
    P
      (L
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)).top ->
    (∀ pc instr x, PTree.get pc code = some instr ->
      P x -> P (transf pc x)) ->
    ∀ (res : PMap.t L.t) (pc : positive),
      fixpoint
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        code successors transf entrypoint = some res ->
      P (PMap.get pc res)

end Solver

def transfer (cfg : CompilerConfig) (f : function) (dm : defmap)
    (approx : PMap.t VA.t)
    (pc : node) (before : numbering) : numbering :=
  match PTree.get pc f.fn_code with
  | none => before
  | some i =>
      match i with
      | .Inop _ => before
      | .Iop op args res _ => add_op before res op args
      | .Iload chunk addr args dst _ =>
          add_load before dst chunk addr args
            (aaddressing cfg (PMap.get pc approx) addr args)
      | .Istore chunk addr args src _ =>
          let app := PMap.get pc approx
          let n := kill_loads_after_store cfg app before chunk addr args
          add_store_result cfg app n chunk addr args src
      | .Icall _ ros args res _ =>
          match is_known_runtime_function dm ros with
          | none => empty_numbering
          | some bf =>
              let n := kill_cheap_computations before
              add_builtin n (.BR res) bf (args.map (fun r => .BA r))
      | .Itailcall _ _ _ => empty_numbering
      | .Ibuiltin ef args res _ =>
          match ef with
          | .EF_external _ _ | .EF_runtime _ _ | .EF_malloc | .EF_free
          | .EF_inline_asm _ _ _ => empty_numbering
          | .EF_vstore _ => set_res_unknown (kill_all_loads before) res
          | .EF_builtin name sg =>
              match lookup_builtin_function name sg with
              | some bf => add_builtin before res bf args
              | none => set_res_unknown (kill_all_loads before) res
          | .EF_memcpy sz _ =>
              match args with
              | dst :: src :: [] =>
                  let app := PMap.get pc approx
                  let adst := aaddr_arg cfg app dst
                  let asrc := aaddr_arg cfg app src
                  let n := kill_loads_after_storebytes before adst sz
                  set_res_unknown (add_memcpy before n asrc adst sz) res
              | _ => empty_numbering
          | .EF_vload _ | .EF_annot _ _ _ | .EF_annot_val _ _ _ | .EF_debug _ _ _ =>
              set_res_unknown before res
      | .Icond _ _ _ _ => before
      | .Ijumptable _ _ => before
      | .Ireturn _ => before

def analyze
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (f : function) (dm : defmap)
    (approx : PMap.t VA.t) : Option (PMap.t numbering) :=
  Solver.fixpoint
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    f.fn_code successors_instr
    (transfer cfg f dm approx) f.fn_entrypoint

def transf_instr (dm : defmap) (n : numbering) (instr : instruction) : instruction :=
  match instr with
  | .Iop op args res s =>
      if is_trivial_op op then instr else
        let (n1, vl) := valnum_regs n args
        match find_rhs n1 (.Op op vl) with
        | some r => .Iop .Omove [r] res s
        | none =>
            let (op', args') :=
              reduce CompCert4Lean.X86.CombineOp.combine_op n1 op args vl
            .Iop op' args' res s
  | .Iload chunk addr args dst s =>
      let (n1, vl) := valnum_regs n args
      match find_rhs n1 (.Load chunk addr vl Ptop) with
      | some r => .Iop .Omove [r] dst s
      | none =>
            let (addr', args') := reduce (CompCert4Lean.X86.CombineOp.combine_addr) n1 addr args vl
          .Iload chunk addr' args' dst s
  | .Istore chunk addr args src s =>
      let (n1, vl) := valnum_regs n args
      let (addr', args') := reduce (CompCert4Lean.X86.CombineOp.combine_addr) n1 addr args vl
      .Istore chunk addr' args' src s
  | .Icall sg ros args res s =>
      match is_known_runtime_function dm ros with
      | none => instr
      | some bf =>
          let (n1, args') := valnum_builtin_args n (args.map (fun r => .BA r))
          match find_rhs n1 (.Builtin bf args') with
          | some r => .Iop .Omove [r] res s
          | none => instr
  | .Ibuiltin (.EF_builtin name sg) args (.BR res) s =>
      match lookup_builtin_function name sg with
      | some bf =>
          let (n1, args') := valnum_builtin_args n args
          match find_rhs n1 (.Builtin bf args') with
          | some r => .Iop .Omove [r] res s
          | none => instr
      | none => instr
  | .Icond cond args s1 s2 =>
      let (n1, vl) := valnum_regs n args
      match CompCert4Lean.X86.CombineOp.combine_cond' cond vl with
      | some b => .Inop (if b then s1 else s2)
      | none =>
          let (cond', args') :=
            reduce CompCert4Lean.X86.CombineOp.combine_cond n1 cond args vl
          .Icond cond' args' s1 s2
  | _ => instr

def transf_code (dm : defmap) (approxs : PMap.t numbering)
    (instrs : code) : code :=
  PTree.map
    (fun pc instr => transf_instr dm (PMap.get pc approxs) instr)
    instrs

def vanalyze
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) :=
  ValueAnalysis.analyze
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) cfg

def transf_function
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (dm : defmap) (rm : romem)
    (f : function) : Res function :=
  let approx := vanalyze
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) cfg rm f
  match analyze
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg f dm approx with
  | none => Error (msg cseFailureText)
  | some approxs =>
      OK { fn_sig := f.fn_sig
           fn_params := f.fn_params
           fn_stacksize := f.fn_stacksize
           fn_code := transf_code dm approxs f.fn_code
           fn_entrypoint := f.fn_entrypoint }

def transf_fundef
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (dm : defmap) (rm : romem)
    (f : fundef) : Res fundef :=
  transf_partial_fundef
    (transf_function
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cfg dm rm) f

def transf_program
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (p : program) : Res program :=
  transform_partial_program
    (transf_fundef
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      cfg (prog_defmap p) (romem_for cfg p)) p

end CompCert4Lean.Backend.CSE

namespace CompCert4Lean.Backend.CSE.Solver

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Backend.Kildall
open CompCert4Lean.Lib.Iteration

private theorem cse_propagate_entry {LAT : OrderedTop}
    (bb : BBlock_solver.bbmap) (entrypoint : positive) (hbb : bb entrypoint = true)
    (succs : List positive) (l : LAT.t) (st : BBlock_solver.state LAT) :
    PMap.get entrypoint (BBlock_solver.propagate_successors bb succs l st).aval =
      PMap.get entrypoint st.aval := by
  induction succs generalizing st with
  | nil => rfl
  | cons s succs ih =>
      simp only [BBlock_solver.propagate_successors]
      split
      · exact ih st
      · rename_i hs
        have hne : entrypoint ≠ s := by
          intro heq
          subst s
          simp [hbb] at hs
        rw [ih]
        simp only [PMap.get, PMap.set]
        rw [PTree.gsspec_proof]
        cases hpeq : CompCert4Lean.Lib.Coqlib.peq entrypoint s with
        | left heq => exact False.elim (hne heq)
        | right _ => rfl

private theorem cse_bblock_fixpoint_entry {A : Type} (LAT : OrderedTop)
    (code : PTree.t A) (successors : A -> List positive)
    (transf : positive -> LAT.t -> LAT.t) (entrypoint : positive)
    (res : PMap.t LAT.t) :
    BBlock_solver.fixpoint LAT code successors transf entrypoint = some res ->
    PMap.get entrypoint res = LAT.top := by
  unfold BBlock_solver.fixpoint
  let bb := BBlock_solver.basic_block_map entrypoint code successors
  apply PrimIter.iter_prop (A := BBlock_solver.state LAT) (B := BBlock_solver.result LAT)
    (step := BBlock_solver.step code successors transf bb)
    (P := fun st => PMap.get entrypoint st.aval = LAT.top)
    (Q := fun result => PMap.get entrypoint result = LAT.top)
  · intro st hst
    unfold BBlock_solver.step
    cases st.worklist with
    | nil => exact hst
    | cons pc rem =>
      cases hcode : PTree.get pc code with
      | none =>
        simp only [hcode]
        exact hst
      | some instr =>
        simp only [hcode]
        rw [cse_propagate_entry bb entrypoint
          (by simp [bb, BBlock_solver.basic_block_map, BBlock_solver.is_basic_block_head])
          (successors instr) (transf pc (PMap.get pc st.aval))
          { aval := st.aval, worklist := rem }]
        exact hst
  · exact rfl

theorem fixpoint_entry_proof
    [binary64_certificate : CompCert4Lean.Backend.CSE.Binary64NormalizeCertificate]
    [binary32_certificate : CompCert4Lean.Backend.CSE.Binary32NormalizeCertificate]
    (laws : CompCert4Lean.Backend.CSE.Solver.law_obligation
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)) :
    CompCert4Lean.Backend.CSE.Solver.fixpoint_entry
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) laws := by
  intro A code successors transf entrypoint res hfix
  exact cse_bblock_fixpoint_entry
    (L
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate))
    code successors transf entrypoint res hfix

end CompCert4Lean.Backend.CSE.Solver

namespace CompCert4Lean.Backend.CSE.Solver

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Backend.Kildall
open CompCert4Lean.Lib.Iteration

private theorem cse_add_successors_correct
    (tolist : List positive) (src : positive) (pred : PTree.t (List positive))
    (n s : positive) :
    n ∈ successors_list pred s ∨ (n = src ∧ s ∈ tolist) ->
    n ∈ successors_list (add_successors pred src tolist) s := by
  induction tolist generalizing pred with
  | nil =>
      intro h
      simpa [add_successors] using h
  | cons to rem ih =>
      intro h
      simp only [add_successors]
      apply ih
      unfold successors_list
      rw [PTree.gsspec_proof]
      cases hpeq : CompCert4Lean.Lib.Coqlib.peq s to with
      | left heq =>
          subst s
          simp at h ⊢
          exact h.elim (fun hn => Or.inl (Or.inr hn)) (fun hn => Or.inl (Or.inl hn))
      | right hne =>
          simp [hne] at h ⊢
          exact h

private theorem cse_make_predecessors_correct {A : Type}
    (code : PTree.t A) (successors : A -> List positive)
    (n : positive) (instr : A) (s : positive) :
    PTree.get n code = some instr -> s ∈ successors instr ->
    n ∈ successors_list (make_predecessors code successors) s := by
  let P : PTree.t A -> PTree.t (List positive) -> Prop := fun m pred =>
    PTree.get n m = some instr -> s ∈ successors instr -> n ∈ successors_list pred s
  unfold make_predecessors
  apply PTree_Properties.fold_rec_proof (P := P)
  · intro m m' pred hext hm hinstr
    apply hm
    rw [hext n]
    exact hinstr
  · intro hinstr
    cases hinstr
  · intro m pred k value hnone hfinal hm hinstr hsucc
    apply cse_add_successors_correct
    rw [PTree.getSet_equation] at hinstr
    split at hinstr
    · rename_i hnk
      subst n
      cases hinstr
      exact Or.inr ⟨rfl, hsucc⟩
    · exact Or.inl (hm hinstr hsucc)

private theorem cse_multiple_predecessors {A : Type}
    (entrypoint : positive) (code : PTree.t A) (successors : A -> List positive)
    (s n1 : positive) (instr1 : A) (n2 : positive) (instr2 : A) :
    PTree.get n1 code = some instr1 -> s ∈ successors instr1 ->
    PTree.get n2 code = some instr2 -> s ∈ successors instr2 -> n1 ≠ n2 ->
    BBlock_solver.basic_block_map entrypoint code successors s = true := by
  intro hcode1 hsucc1 hcode2 hsucc2 hneq
  have hpred1 := cse_make_predecessors_correct code successors n1 instr1 s hcode1 hsucc1
  have hpred2 := cse_make_predecessors_correct code successors n2 instr2 s hcode2 hsucc2
  unfold BBlock_solver.basic_block_map BBlock_solver.is_basic_block_head
  split
  · rfl
  · rename_i hentry
    unfold successors_list at hpred1 hpred2
    cases hpreds : PTree.get s (make_predecessors code successors) with
    | none => simp [hpreds] at hpred1
    | some preds =>
      cases preds with
      | nil => simp [hpreds] at hpred1
      | cons pred preds =>
        cases preds with
        | nil =>
          simp [hpreds] at hpred1 hpred2
          exact False.elim (hneq (hpred1.trans hpred2.symm))
        | cons pred' preds => simp [successors_list, hpreds]

private theorem cse_no_self_loop {A : Type}
    (entrypoint : positive) (code : PTree.t A) (successors : A -> List positive)
    (n : positive) (instr : A) :
    PTree.get n code = some instr -> n ∈ successors instr ->
    BBlock_solver.basic_block_map entrypoint code successors n = true := by
  intro hcode hsucc
  have hpred := cse_make_predecessors_correct code successors n instr n hcode hsucc
  unfold BBlock_solver.basic_block_map BBlock_solver.is_basic_block_head
  split
  · rfl
  · rename_i hentry
    unfold successors_list at hpred
    cases hpreds : PTree.get n (make_predecessors code successors) with
    | none => simp [hpreds] at hpred
    | some preds =>
      cases preds with
      | nil => simp [hpreds] at hpred
      | cons pred preds =>
        cases preds with
        | nil =>
          simp [hpreds] at hpred
          subst pred
          simp [successors_list, hpreds]
        | cons pred' preds => simp [successors_list, hpreds]

private theorem cse_result_get_set {LAT : OrderedTop} (i j : positive) (x : LAT.t)
    (m : BBlock_solver.result LAT) :
    PMap.get i (PMap.set j x m) =
      if _h : i = j then x else PMap.get i m := by
  change PMap.get i (PMap.set j x m) = _
  simp only [PMap.get, PMap.set]
  rw [PTree.gsspec_proof]
  cases hpeq : CompCert4Lean.Lib.Coqlib.peq i j with
  | left heq => simp [heq]
  | right hne => simp [hne]

private theorem cse_propagate_successors_charact1 {LAT : OrderedTop}
    (bb : BBlock_solver.bbmap) (succs : List positive)
    (l : LAT.t) (st : BBlock_solver.state LAT) (n : positive) :
    n ∈ st.worklist -> n ∈ (BBlock_solver.propagate_successors bb succs l st).worklist := by
  induction succs generalizing st with
  | nil => exact fun h => h
  | cons s succs ih =>
      simp only [BBlock_solver.propagate_successors]
      split
      · exact ih st
      · exact fun h =>
          ih { aval := PMap.set s l st.aval, worklist := s :: st.worklist }
            (List.mem_cons.mpr (Or.inr h))

private theorem cse_propagate_successors_charact2 {LAT : OrderedTop}
    (bb : BBlock_solver.bbmap) (succs : List positive)
    (l : LAT.t) (st : BBlock_solver.state LAT) (n : positive) :
    let st' := BBlock_solver.propagate_successors bb succs l st
    (n ∈ succs -> bb n = false -> n ∈ st'.worklist ∧ PMap.get n st'.aval = l) ∧
    (n ∉ succs ∨ bb n = true -> PMap.get n st'.aval = PMap.get n st.aval) := by
  induction succs generalizing st with
  | nil =>
      simp only [BBlock_solver.propagate_successors]
      constructor
      · intro h
        simp at h
      · intro _
        exact True.intro
  | cons s succs ih =>
      simp only [BBlock_solver.propagate_successors]
      split
      · rename_i hbs
        constructor
        · intro hmem hbn
          rcases List.mem_cons.mp hmem with hns | hmem
          · subst n
            simp [hbs] at hbn
          · exact (ih st).1 hmem hbn
        · intro h
          apply (ih st).2
          rcases h with hnot | hbn
          · exact Or.inl (by
              intro hmem
              exact hnot (List.mem_cons.mpr (Or.inr hmem)))
          · exact Or.inr hbn
      · rename_i hbs
        let st1 : BBlock_solver.state LAT :=
          { aval := PMap.set s l st.aval, worklist := s :: st.worklist }
        constructor
        · intro hmem hbn
          rcases List.mem_cons.mp hmem with hns | hmem
          · subst n
            constructor
            · apply cse_propagate_successors_charact1 bb succs l st1 s
              exact List.mem_cons.mpr (Or.inl rfl)
            · by_cases hrem : s ∈ succs
              · exact ((ih st1).1 hrem (by simpa using hbn)).2
              · rw [(ih st1).2 (Or.inl hrem)]
                dsimp [st1]
                rw [cse_result_get_set]
                simp
          · exact (ih st1).1 hmem hbn
        · intro h
          rw [(ih st1).2 (by
            rcases h with hnot | hbn
            · exact Or.inl (by
              intro hmem
              exact hnot (List.mem_cons.mpr (Or.inr hmem)))
            · exact Or.inr hbn)]
          rcases h with hnot | hbn
          · have hne : n ≠ s := by
              intro heq
              subst n
              exact hnot (List.mem_cons.mpr (Or.inl rfl))
            dsimp [st1]
            rw [cse_result_get_set]
            simp [hne]
          · have hne : n ≠ s := by
              intro heq
              subst n
              simp [hbs] at hbn
            dsimp [st1]
            rw [cse_result_get_set]
            simp [hne]

private def cse_state_invariant {A : Type} {LAT : OrderedTop}
    (entrypoint : positive) (code : PTree.t A) (successors : A -> List positive)
    (transf : positive -> LAT.t -> LAT.t) (st : BBlock_solver.state LAT) : Prop :=
  (∀ n, BBlock_solver.basic_block_map entrypoint code successors n = true ->
      PMap.get n st.aval = LAT.top) ∧
  (∀ n, n ∈ st.worklist ∨ ∀ instr s, PTree.get n code = some instr ->
      s ∈ successors instr -> LAT.ge (PMap.get s st.aval) (transf n (PMap.get n st.aval)))

private theorem cse_propagate_successors_invariant {A : Type} {LAT : OrderedTop}
    (entrypoint : positive) (laws : OrderedTopLaws LAT) (code : PTree.t A)
    (successors : A -> List positive) (transf : positive -> LAT.t -> LAT.t)
    (pc : positive) (instr : A) (res : BBlock_solver.result LAT) (rem : List positive) :
    PTree.get pc code = some instr ->
    cse_state_invariant entrypoint code successors transf { aval := res, worklist := pc :: rem } ->
    cse_state_invariant entrypoint code successors transf
      (BBlock_solver.propagate_successors (BBlock_solver.basic_block_map entrypoint code successors)
        (successors instr) (transf pc (PMap.get pc res)) { aval := res, worklist := rem }) := by
  intro hcode hinv
  rcases hinv with ⟨hheads, hstable⟩
  let bb := BBlock_solver.basic_block_map entrypoint code successors
  let l := transf pc (PMap.get pc res)
  let st0 : BBlock_solver.state LAT := { aval := res, worklist := rem }
  constructor
  · intro n hbb
    rw [(cse_propagate_successors_charact2 bb (successors instr) l st0 n).2 (Or.inr hbb)]
    exact hheads n hbb
  · intro n
    by_cases hpc : n = pc
    · subst n
      right
      intro instr' s hget hsucc
      have hinstr : instr' = instr := Option.some.inj (hget.symm.trans hcode)
      subst instr'
      have hmappc := (cse_propagate_successors_charact2 bb (successors instr) l st0 pc).2 (by
        by_cases hself : pc ∈ successors instr
        · right
          exact cse_no_self_loop entrypoint code successors pc instr hcode hself
        · left
          exact hself)
      cases hsbb : bb s with
      | true =>
          have hmaps := (cse_propagate_successors_charact2 bb (successors instr) l st0 s).2 (Or.inr hsbb)
          rw [hmaps, hmappc, hheads s hsbb]
          exact laws.top_ge _
      | false =>
          have hmaps := (cse_propagate_successors_charact2 bb (successors instr) l st0 s).1 hsucc hsbb
          rw [hmaps.2, hmappc]
          exact laws.refl_ge _
    · rcases hstable n with hold | hold
      · left
        rcases List.mem_cons.mp hold with hnp | hrem
        · exact False.elim (hpc hnp)
        · exact cse_propagate_successors_charact1 bb (successors instr) l st0 n hrem
      · by_cases hnsucc : n ∈ successors instr
        · cases hnbb : bb n with
          | true =>
              right
              intro instr' s hget hsucc
              have hmapn := (cse_propagate_successors_charact2 bb (successors instr) l st0 n).2 (Or.inr hnbb)
              have hmaps := (cse_propagate_successors_charact2 bb (successors instr) l st0 s).2 (by
                by_cases hssucc : s ∈ successors instr
                · right
                  exact cse_multiple_predecessors entrypoint code successors s pc instr n instr'
                    hcode hssucc hget hsucc (by intro h; exact hpc h.symm)
                · left
                  exact hssucc)
              rw [hmaps, hmapn]
              exact hold instr' s hget hsucc
          | false =>
              exact Or.inl ((cse_propagate_successors_charact2 bb (successors instr) l st0 n).1 hnsucc hnbb).1
        · right
          intro instr' s hget hsucc
          have hmapn := (cse_propagate_successors_charact2 bb (successors instr) l st0 n).2 (Or.inl hnsucc)
          have hmaps := (cse_propagate_successors_charact2 bb (successors instr) l st0 s).2 (by
            by_cases hssucc : s ∈ successors instr
            · right
              exact cse_multiple_predecessors entrypoint code successors s pc instr n instr'
                hcode hssucc hget hsucc (by intro h; exact hpc h.symm)
            · left
              exact hssucc)
          rw [hmaps, hmapn]
          exact hold instr' s hget hsucc

private theorem cse_drop_invariant {A : Type} {LAT : OrderedTop}
    (entrypoint : positive) (code : PTree.t A) (successors : A -> List positive)
    (transf : positive -> LAT.t -> LAT.t) (pc : positive)
    (res : BBlock_solver.result LAT) (rem : List positive) :
    PTree.get pc code = none ->
    cse_state_invariant entrypoint code successors transf { aval := res, worklist := pc :: rem } ->
    cse_state_invariant entrypoint code successors transf { aval := res, worklist := rem } := by
  intro hcode hinv
  rcases hinv with ⟨hheads, hstable⟩
  constructor
  · exact hheads
  · intro n
    rcases hstable n with hwork | hstable
    · rcases List.mem_cons.mp hwork with hnp | hrem
      · subst n
        right
        intro instr s hget hsucc
        rw [hcode] at hget
        cases hget
      · exact Or.inl hrem
    · exact Or.inr hstable

private theorem cse_initial_state_invariant {A : Type} {LAT : OrderedTop}
    (entrypoint : positive) (laws : OrderedTopLaws LAT) (code : PTree.t A)
    (successors : A -> List positive) (transf : positive -> LAT.t -> LAT.t) :
    cse_state_invariant entrypoint code successors transf
      { aval := PMap.init LAT.top,
        worklist := BBlock_solver.basic_block_list (BBlock_solver.basic_block_map entrypoint code successors) code } := by
  constructor
  · intro n _
    cases n <;> rfl
  · intro n
    right
    intro instr s hcode hsucc
    have hinit : PMap.get s (PMap.init LAT.top) = LAT.top := by
      cases s <;> rfl
    rw [hinit]
    exact laws.top_ge _

private theorem cse_analyze_invariant {A : Type} {LAT : OrderedTop}
    (entrypoint : positive) (laws : OrderedTopLaws LAT) (code : PTree.t A)
    (successors : A -> List positive) (transf : positive -> LAT.t -> LAT.t)
    (res : BBlock_solver.result LAT) :
    BBlock_solver.fixpoint LAT code successors transf entrypoint = some res ->
    cse_state_invariant entrypoint code successors transf { aval := res, worklist := [] } := by
  unfold BBlock_solver.fixpoint
  let bb := BBlock_solver.basic_block_map entrypoint code successors
  apply PrimIter.iter_prop (A := BBlock_solver.state LAT) (B := BBlock_solver.result LAT)
    (step := BBlock_solver.step code successors transf bb)
    (P := cse_state_invariant entrypoint code successors transf)
    (Q := fun result => cse_state_invariant entrypoint code successors transf
      { aval := result, worklist := [] })
  · intro st hinv
    cases st with
    | mk aval worklist =>
      cases worklist with
      | nil =>
        simp only [BBlock_solver.step]
        exact hinv
      | cons pc rem =>
        cases hcode : PTree.get pc code with
        | none =>
          simp only [BBlock_solver.step, hcode]
          exact cse_drop_invariant entrypoint code successors transf pc aval rem hcode hinv
        | some instr =>
          simp only [BBlock_solver.step, hcode]
          exact cse_propagate_successors_invariant entrypoint laws code successors transf
            pc instr aval rem hcode hinv
  · exact cse_initial_state_invariant entrypoint laws code successors transf

private theorem cse_bblock_fixpoint_solution {A : Type} (LAT : OrderedTop)
    (laws : OrderedTopLaws LAT) (code : PTree.t A) (successors : A -> List positive)
    (transf : positive -> LAT.t -> LAT.t) (entrypoint : positive)
    (res : BBlock_solver.result LAT) (n : positive) (instr : A) (s : positive) :
    BBlock_solver.fixpoint LAT code successors transf entrypoint = some res ->
    PTree.get n code = some instr -> s ∈ successors instr ->
    LAT.ge (PMap.get s res) (transf n (PMap.get n res)) := by
  intro hfix hcode hsucc
  have hinv := cse_analyze_invariant entrypoint laws code successors transf res hfix
  rcases hinv.2 n with hwork | hstable
  · simp at hwork
  · exact hstable instr s hcode hsucc

theorem fixpoint_solution_proof
    [binary64_certificate : CompCert4Lean.Backend.CSE.Binary64NormalizeCertificate]
    [binary32_certificate : CompCert4Lean.Backend.CSE.Binary32NormalizeCertificate]
    (laws : CompCert4Lean.Backend.CSE.Solver.law_obligation
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)) :
    CompCert4Lean.Backend.CSE.Solver.fixpoint_solution
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) laws := by
  intro A code successors transf entrypoint res n instr s hfix hcode hsucc
  exact cse_bblock_fixpoint_solution
    (L
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)) laws
    code successors transf entrypoint res n instr s hfix hcode hsucc

end CompCert4Lean.Backend.CSE.Solver

namespace CompCert4Lean.Backend.CSE.Solver

theorem law_obligation_proof
    [binary64_certificate : CompCert4Lean.Backend.CSE.Binary64NormalizeCertificate]
    [binary32_certificate : CompCert4Lean.Backend.CSE.Binary32NormalizeCertificate] :
    CompCert4Lean.Backend.CSE.Solver.law_obligation
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) := by
  constructor
  · intro x valu genv sp rs m hholds
    exact CompCert4Lean.Backend.CSEdomain.empty_numbering_holds
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      valu genv sp rs m
  · intro x valu genv sp rs m hholds
    exact hholds

end CompCert4Lean.Backend.CSE.Solver
