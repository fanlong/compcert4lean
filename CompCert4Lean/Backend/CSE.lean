import CompCert4Lean.Foundation.RocqStdlib
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

/-! The source CombineOp module keeps these helpers in a section parameterized
by the value-number lookup.  They are private adapters here because the
corresponding proof module deliberately does not export them. -/

private def combine_compimm_ne_0 (get : valnum → Option rhs) (x : valnum) :
    Option (condition × List valnum) :=
  match get x with
  | some (.Op (.Ocmp c) ys) => some (c, ys)
  | some (.Op (.Oandimm n) ys) => some (.Cmasknotzero n, ys)
  | some (.Op (.Oxorimm n) ys) => some (.Ccompimm .Cne n, ys)
  | _ => none

private def combine_compimm_eq_0 (get : valnum → Option rhs) (x : valnum) :
    Option (condition × List valnum) :=
  match get x with
  | some (.Op (.Ocmp c) ys) => some (negate_condition c, ys)
  | some (.Op (.Oandimm n) ys) => some (.Cmaskzero n, ys)
  | some (.Op (.Oxorimm n) ys) => some (.Ccompimm .Ceq n, ys)
  | _ => none

private def combine_compimm_eq_1 (get : valnum → Option rhs) (x : valnum) :
    Option (condition × List valnum) :=
  match get x with
  | some (.Op (.Ocmp c) ys) => some (c, ys)
  | _ => none

private def combine_compimm_ne_1 (get : valnum → Option rhs) (x : valnum) :
    Option (condition × List valnum) :=
  match get x with
  | some (.Op (.Ocmp c) ys) => some (negate_condition c, ys)
  | _ => none

private def combine_cond (get : valnum → Option rhs) (cond : condition)
    (args : List valnum) : Option (condition × List valnum) :=
  match cond, args with
  | .Ccompimm .Cne n, [x] =>
      if n = Int.zero then combine_compimm_ne_0 get x
      else if n = Int.one then combine_compimm_ne_1 get x
      else none
  | .Ccompimm .Ceq n, [x] =>
      if n = Int.zero then combine_compimm_eq_0 get x
      else if n = Int.one then combine_compimm_eq_1 get x
      else none
  | .Ccompuimm .Cne n, [x] =>
      if n = Int.zero then combine_compimm_ne_0 get x
      else if n = Int.one then combine_compimm_ne_1 get x
      else none
  | .Ccompuimm .Ceq n, [x] =>
      if n = Int.zero then combine_compimm_eq_0 get x
      else if n = Int.one then combine_compimm_eq_1 get x
      else none
  | _, _ => none

private def combine_addr_32 (get : valnum → Option rhs) (addr : addressing)
    (args : List valnum) : Option (addressing × List valnum) :=
  match addr, args with
  | .Aindexed n, [x] =>
      match get x with
      | some (.Op (.Olea a) ys) =>
          match offset_addressing a n with
          | some a' => some (a', ys)
          | none => none
      | _ => none
  | _, _ => none

private def combine_addr_64 (get : valnum → Option rhs) (addr : addressing)
    (args : List valnum) : Option (addressing × List valnum) :=
  match addr, args with
  | .Aindexed n, [x] =>
      match get x with
      | some (.Op (.Oleal a) ys) =>
          match offset_addressing a n with
          | some a' => some (a', ys)
          | none => none
      | _ => none
  | _, _ => none

private def combine_op (get : valnum → Option rhs) (op : operation)
    (args : List valnum) : Option (operation × List valnum) :=
  match op, args with
  | .Olea addr, _ =>
      match combine_addr_32 get addr args with
      | some (addr', args') => some (.Olea addr', args')
      | none => none
  | .Oleal addr, _ =>
      match combine_addr_64 get addr args with
      | some (addr', args') => some (.Oleal addr', args')
      | none => none
  | .Oandimm n, [x] =>
      match get x with
      | some (.Op (.Oandimm m) ys) => some (.Oandimm (Int.and m n), ys)
      | _ => none
  | .Oorimm n, [x] =>
      match get x with
      | some (.Op (.Oorimm m) ys) => some (.Oorimm (Int.or m n), ys)
      | _ => none
  | .Oxorimm n, [x] =>
      match get x with
      | some (.Op (.Oxorimm m) ys) => some (.Oxorimm (Int.xor m n), ys)
      | _ => none
  | .Oandlimm n, [x] =>
      match get x with
      | some (.Op (.Oandlimm m) ys) =>
          some (.Oandlimm (CompCert4Lean.Lib.Integers.Int64.and m n), ys)
      | _ => none
  | .Oorlimm n, [x] =>
      match get x with
      | some (.Op (.Oorlimm m) ys) =>
          some (.Oorlimm (CompCert4Lean.Lib.Integers.Int64.or m n), ys)
      | _ => none
  | .Oxorlimm n, [x] =>
      match get x with
      | some (.Op (.Oxorlimm m) ys) =>
          some (.Oxorlimm (CompCert4Lean.Lib.Integers.Int64.xor m n), ys)
      | _ => none
  | .Ocmp cond, _ =>
      match CompCert4Lean.X86.CombineOp.combine_cond' cond args with
      | some b => some ((if b then .Ointconst Int.one else .Ointconst Int.zero), [])
      | none =>
          match combine_cond get cond args with
          | some (cond', args') => some (.Ocmp cond', args')
          | none => none
  | .Osel cond ty, x :: y :: rest =>
      match CompCert4Lean.X86.CombineOp.combine_cond' cond rest with
      | some b => some (.Omove, [(if b then x else y)])
      | none =>
          match eq_valnum x y with
          | .left _ => some (.Omove, [x])
          | .right _ =>
              match combine_cond get cond rest with
              | some (cond', args') => some (.Osel cond' ty, x :: y :: args')
              | none => none
  | _, _ => none

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

def kill_loads_after_store (app : VA.t) (n : numbering)
    (chunk : memory_chunk) (addr : addressing) (args : List reg) : numbering :=
  let p := aaddressing app addr args
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

def add_store_result (app : VA.t) (n : numbering) (chunk : memory_chunk)
    (addr : addressing) (rargs : List reg) (rsrc : reg) : numbering :=
  if vincl (avalue app rsrc) (store_normalized_range chunk) then
    let (n1, vsrc) := valnum_reg n rsrc
    let (n2, vargs) := valnum_regs n1 rargs
    { num_next := n2.num_next
      num_eqs := .Eq vsrc false
          (.Load chunk addr vargs (aaddressing app addr rargs)) :: n2.num_eqs
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

def ge (n1 n2 : numbering) : Prop :=
  ∀ (valu : valuation) (genv : CompCert4Lean.Backend.RTL.genv)
    (sp : val) (rs : regset) (m : mem),
    numbering_holds valu genv sp rs m n2 →
      numbering_holds valu genv sp rs m n1

end Numbering

private def numberingSolver : OrderedTop :=
  { t := numbering
    ge := Numbering.ge
    top := empty_numbering }

/-! Generated surface for `Kildall.BBlock_solver(Numbering)`. -/
namespace Solver

def L : OrderedTop := numberingSolver

def Solver : Type :=
  BBlock_solver L

def fixpoint {A : Type} (code : PTree.t A)
    (successors : A -> List positive)
    (transf : positive -> L.t -> L.t)
    (entrypoint : positive) : Option (PMap.t L.t) :=
  BBlock_solver.fixpoint L code successors transf entrypoint

def fixpoint_solution : Prop :=
  ∀ (A : Type) (code : PTree.t A)
    (successors : A -> List positive)
    (transf : positive -> L.t -> L.t)
    (entrypoint : positive) (res : PMap.t L.t)
    (n : positive) (instr : A) (s : positive),
    fixpoint code successors transf entrypoint = some res ->
    PTree.get n code = some instr ->
    s ∈ successors instr ->
    L.ge (PMap.get s res) (transf n (PMap.get n res))

def fixpoint_entry : Prop :=
  ∀ (A : Type) (code : PTree.t A)
    (successors : A -> List positive)
    (transf : positive -> L.t -> L.t)
    (entrypoint : positive) (res : PMap.t L.t),
    fixpoint code successors transf entrypoint = some res ->
    PMap.get entrypoint res = L.top

def fixpoint_invariant : Prop :=
  ∀ (A : Type) (code : PTree.t A)
    (successors : A -> List positive)
    (transf : positive -> L.t -> L.t)
    (entrypoint : positive) (P : L.t -> Prop),
    P L.top ->
    (∀ pc instr x, PTree.get pc code = some instr ->
      P x -> P (transf pc x)) ->
    ∀ (res : PMap.t L.t) (pc : positive),
      fixpoint code successors transf entrypoint = some res ->
      P (PMap.get pc res)

end Solver

def transfer (f : function) (dm : defmap) (approx : PMap.t VA.t)
    (pc : node) (before : numbering) : numbering :=
  match PTree.get pc f.fn_code with
  | none => before
  | some i =>
      match i with
      | .Inop _ => before
      | .Iop op args res _ => add_op before res op args
      | .Iload chunk addr args dst _ =>
          add_load before dst chunk addr args (aaddressing (PMap.get pc approx) addr args)
      | .Istore chunk addr args src _ =>
          let app := PMap.get pc approx
          let n := kill_loads_after_store app before chunk addr args
          add_store_result app n chunk addr args src
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
                  let adst := aaddr_arg app dst
                  let asrc := aaddr_arg app src
                  let n := kill_loads_after_storebytes before adst sz
                  set_res_unknown (add_memcpy before n asrc adst sz) res
              | _ => empty_numbering
          | .EF_vload _ | .EF_annot _ _ _ | .EF_annot_val _ _ _ | .EF_debug _ _ _ =>
              set_res_unknown before res
      | .Icond _ _ _ _ => before
      | .Ijumptable _ _ => before
      | .Ireturn _ => before

def analyze (f : function) (dm : defmap) (approx : PMap.t VA.t) : Option (PMap.t numbering) :=
  BBlock_solver.fixpoint numberingSolver f.fn_code successors_instr
    (transfer f dm approx) f.fn_entrypoint

def transf_instr (dm : defmap) (n : numbering) (instr : instruction) : instruction :=
  match instr with
  | .Iop op args res s =>
      if is_trivial_op op then instr else
        let (n1, vl) := valnum_regs n args
        match find_rhs n1 (.Op op vl) with
        | some r => .Iop .Omove [r] res s
        | none =>
            let (op', args') := reduce (combine_op) n1 op args vl
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
          let (cond', args') := reduce (combine_cond) n1 cond args vl
          .Icond cond' args' s1 s2
  | _ => instr

def transf_code (dm : defmap) (approxs : PMap.t numbering)
    (instrs : code) : code :=
  PTree.map (fun pc instr => transf_instr dm (PMap.get pc approxs) instr) instrs

def vanalyze := ValueAnalysis.analyze

def transf_function (dm : defmap) (rm : romem) (f : function) : Res function :=
  let approx := vanalyze rm f
  match analyze f dm approx with
  | none => Error (msg cseFailureText)
  | some approxs =>
      OK { fn_sig := f.fn_sig
           fn_params := f.fn_params
           fn_stacksize := f.fn_stacksize
           fn_code := transf_code dm approxs f.fn_code
           fn_entrypoint := f.fn_entrypoint }

def transf_fundef (dm : defmap) (rm : romem) (f : fundef) : Res fundef :=
  transf_partial_fundef (transf_function dm rm) f

def transf_program (p : program) : Res program :=
  transform_partial_program (transf_fundef (prog_defmap p) (romem_for p)) p

end CompCert4Lean.Backend.CSE
