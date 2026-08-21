import CompCert4Lean.Backend.Kildall
import CompCert4Lean.Backend.LTL
import CompCert4Lean.Backend.Linear
import CompCert4Lean.Backend.Registers
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Errors
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Lattice
import CompCert4Lean.Lib.Maps

/-!
# Linearization of LTL control-flow graphs

Definition-bearing translation of CompCert's `backend/Linearize.v`.  The
untrusted node enumerator is represented by explicit proposal data; the pure
validator remains the authority for accepting a proposal.
-/

namespace CompCert4Lean.Backend.Linearize

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.LTL
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Op

private abbrev res (A : Type) := CompCert4Lean.Common.Errors.res A
private abbrev node_set := List LTL.node

private def bytesToString : List UInt8 →
    CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string
  | [] => .EmptyString
  | byte :: rest => .String byte (bytesToString rest)

private def duplicateEnumerationText := bytesToString
  [76, 105, 110, 101, 97, 114, 105, 122, 101, 58, 32, 100, 117, 112, 108,
    105, 99, 97, 116, 101, 115, 32, 105, 110, 32, 101, 110, 117, 109, 101,
    114, 97, 116, 105, 111, 110]

private def wrongEnumerationText := bytesToString
  [76, 105, 110, 101, 97, 114, 105, 122, 101, 58, 32, 119, 114, 111, 110,
    103, 32, 101, 110, 117, 109, 101, 114, 97, 116, 105, 111, 110]

/-! ## Reachability analysis -/

private def booleanLattice : CompCert4Lean.Backend.Kildall.SemiLattice :=
  { t := Bool
    bot := false
    lub := (· || ·)
    beq := (· == ·)
    eq := (· = ·)
    ge := CompCert4Lean.Lib.Lattice.LBoolean.ge }

def reachable_aux (f : LTL.function) : Option (PMap.t Bool) :=
  CompCert4Lean.Backend.Kildall.Dataflow_Solver.fixpoint
    booleanLattice CompCert4Lean.Backend.Kildall.NodeSetForward
    f.fn_code LTL.successors_block (fun _ reachable => reachable)
    f.fn_entrypoint true

def reachable (f : LTL.function) : PMap.t Bool :=
  match reachable_aux f with
  | none => PMap.init true
  | some rs => rs

/-! ## Proposal interface and validation -/

abbrev EnumerationProposal := List LTL.node

def enumerate_aux (proposal : EnumerationProposal)
    (_f : LTL.function) (_reach : PMap.t Bool) : EnumerationProposal :=
  proposal

private def nodeMem : LTL.node → node_set → Bool
  | _, [] => false
  | x, y :: ys =>
      match peq x y with
      | .left _ => true
      | .right _ => nodeMem x ys

def nodeset_of_list (l : List LTL.node) (s : node_set) : res node_set :=
  match l with
  | [] => .OK s
  | hd :: tl =>
      if nodeMem hd s then
        .Error (msg duplicateEnumerationText)
      else
        nodeset_of_list tl (hd :: s)

def check_reachable_aux
    (reach : PMap.t Bool) (s : node_set) (ok : Bool)
    (pc : LTL.node) (_bb : LTL.bblock) : Bool :=
  if PMap.get pc reach then ok && nodeMem pc s else ok

def check_reachable
    (f : LTL.function) (reach : PMap.t Bool) (s : node_set) : Bool :=
  PTree.fold (check_reachable_aux reach s) f.fn_code true

def enumerateWithProposal
    (f : LTL.function) (proposal : EnumerationProposal) : res (List LTL.node) :=
  let reach := reachable f
  let enum := enumerate_aux proposal f reach
  match nodeset_of_list enum [] with
  | .Error message => .Error message
  | .OK s =>
      if check_reachable f reach s then
        .OK enum
      else
        .Error (msg wrongEnumerationText)

private def allNodes (f : LTL.function) : EnumerationProposal :=
  (PTree.elements f.fn_code).map Prod.fst

def enumerate (f : LTL.function) : res (List LTL.node) :=
  enumerateWithProposal f (allNodes f)

/-! ## Translation from LTL blocks to linear code -/

def starts_with (lbl : Linear.label) (k : Linear.code) : Bool :=
  match k with
  | Linear.Llabel lbl' :: k' =>
      match peq lbl lbl' with
      | .left _ => true
      | .right _ => starts_with lbl k'
  | _ => false

def add_branch (s : Linear.label) (k : Linear.code) : Linear.code :=
  if starts_with s k then k else Linear.Lgoto s :: k

def linearize_block (b : LTL.bblock) (k : Linear.code) : Linear.code :=
  match b with
  | [] => k
  | LTL.Lop op args res :: b' =>
      Linear.Lop op args res :: linearize_block b' k
  | LTL.Lload chunk addr args dst :: b' =>
      Linear.Lload chunk addr args dst :: linearize_block b' k
  | LTL.Lgetstack sl ofs ty dst :: b' =>
      Linear.Lgetstack sl ofs ty dst :: linearize_block b' k
  | LTL.Lsetstack src sl ofs ty :: b' =>
      Linear.Lsetstack src sl ofs ty :: linearize_block b' k
  | LTL.Lstore chunk addr args src :: b' =>
      Linear.Lstore chunk addr args src :: linearize_block b' k
  | LTL.Lcall sig ros :: b' =>
      Linear.Lcall sig ros :: linearize_block b' k
  | LTL.Ltailcall sig ros :: _ =>
      Linear.Ltailcall sig ros :: k
  | LTL.Lbuiltin ef args res :: b' =>
      Linear.Lbuiltin ef args res :: linearize_block b' k
  | LTL.Lbranch s :: _ =>
      add_branch s k
  | LTL.Lcond cond args s1 s2 :: _ =>
      if starts_with s1 k then
        Linear.Lcond (negate_condition cond) args s2 :: add_branch s1 k
      else
        Linear.Lcond cond args s1 :: add_branch s2 k
  | LTL.Ljumptable arg tbl :: _ =>
      Linear.Ljumptable arg tbl :: k
  | LTL.Lreturn :: _ =>
      Linear.Lreturn :: k

def linearize_node
    (f : LTL.function) (pc : LTL.node) (k : Linear.code) : Linear.code :=
  match PTree.get pc f.fn_code with
  | none => k
  | some b => Linear.Llabel pc :: linearize_block b k

def linearize_body (f : LTL.function) (enum : List LTL.node) : Linear.code :=
  list_fold_right (linearize_node f) enum []

/-! ## Entry points -/

def transf_function (f : LTL.function) : res Linear.function :=
  match enumerate f with
  | .Error message => .Error message
  | .OK enum =>
      .OK
        { fn_sig := f.fn_sig
          fn_stacksize := f.fn_stacksize
          fn_code := add_branch f.fn_entrypoint (linearize_body f enum) }

def transf_fundef (f : LTL.fundef) : res Linear.fundef :=
  CompCert4Lean.Common.AST.transf_partial_fundef transf_function f

def transf_program (p : LTL.program) : res Linear.program :=
  CompCert4Lean.Common.AST.transform_partial_program transf_fundef p

/-! ## Generated finite-set and dataflow surfaces -/

namespace Nodeset

def Nodeset : Type := Unit

abbrev elt : Type := CompCert4Lean.Backend.Registers.Regset.elt
abbrev t : Type := CompCert4Lean.Backend.Registers.Regset.t

def «X'» : Type := CompCert4Lean.Backend.Registers.Regset.«X'»
def MSet : Type := CompCert4Lean.Backend.Registers.Regset.MSet
def MF : Type := CompCert4Lean.Backend.Registers.Regset.MF
def E : Type := CompCert4Lean.Backend.Registers.Regset.E

def In : elt → t → Prop := CompCert4Lean.Backend.Registers.Regset.In
def Equal : t → t → Prop := CompCert4Lean.Backend.Registers.Regset.Equal
def Subset : t → t → Prop := CompCert4Lean.Backend.Registers.Regset.Subset
def Empty : t → Prop := CompCert4Lean.Backend.Registers.Regset.Empty
def For_all : (elt → Prop) → t → Prop := CompCert4Lean.Backend.Registers.Regset.For_all
def Exists : (elt → Prop) → t → Prop := CompCert4Lean.Backend.Registers.Regset.Exists

def empty : t := CompCert4Lean.Backend.Registers.Regset.empty
def is_empty : t → Bool := CompCert4Lean.Backend.Registers.Regset.is_empty
def mem : elt → t → Bool := CompCert4Lean.Backend.Registers.Regset.mem
def add : elt → t → t := CompCert4Lean.Backend.Registers.Regset.add
def singleton : elt → t := CompCert4Lean.Backend.Registers.Regset.singleton
def remove : elt → t → t := CompCert4Lean.Backend.Registers.Regset.remove
def union : t → t → t := CompCert4Lean.Backend.Registers.Regset.union
def inter : t → t → t := CompCert4Lean.Backend.Registers.Regset.inter
def diff : t → t → t := CompCert4Lean.Backend.Registers.Regset.diff
def eq : t → t → Prop := CompCert4Lean.Backend.Registers.Regset.eq
def eq_dec (s s' : t) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (eq s s') (¬ eq s s') :=
  CompCert4Lean.Backend.Registers.Regset.eq_dec s s'
def equal : t → t → Bool := CompCert4Lean.Backend.Registers.Regset.equal
def subset : t → t → Bool := CompCert4Lean.Backend.Registers.Regset.subset
def fold {A : Type} : (elt → A → A) → t → A → A :=
  CompCert4Lean.Backend.Registers.Regset.fold
def for_all : (elt → Bool) → t → Bool := CompCert4Lean.Backend.Registers.Regset.for_all
def exists_ : (elt → Bool) → t → Bool := CompCert4Lean.Backend.Registers.Regset.exists_
def filter : (elt → Bool) → t → t := CompCert4Lean.Backend.Registers.Regset.filter
def partition : (elt → Bool) → t → t × t := CompCert4Lean.Backend.Registers.Regset.partition
def cardinal : t → Nat := CompCert4Lean.Backend.Registers.Regset.cardinal
def elements : t → List elt := CompCert4Lean.Backend.Registers.Regset.elements
def choose : t → Option elt := CompCert4Lean.Backend.Registers.Regset.choose
def lt : t → t → Prop := CompCert4Lean.Backend.Registers.Regset.lt
def min_elt : t → Option elt := CompCert4Lean.Backend.Registers.Regset.min_elt
def max_elt : t → Option elt := CompCert4Lean.Backend.Registers.Regset.max_elt

def In_1 : Prop := CompCert4Lean.Backend.Registers.Regset.In_1
def eq_refl : Prop := CompCert4Lean.Backend.Registers.Regset.eq_refl
def eq_sym : Prop := CompCert4Lean.Backend.Registers.Regset.eq_sym
def eq_trans : Prop := CompCert4Lean.Backend.Registers.Regset.eq_trans
def mem_1 : Prop := CompCert4Lean.Backend.Registers.Regset.mem_1
def mem_2 : Prop := CompCert4Lean.Backend.Registers.Regset.mem_2
def equal_1 : Prop := CompCert4Lean.Backend.Registers.Regset.equal_1
def equal_2 : Prop := CompCert4Lean.Backend.Registers.Regset.equal_2
def subset_1 : Prop := CompCert4Lean.Backend.Registers.Regset.subset_1
def subset_2 : Prop := CompCert4Lean.Backend.Registers.Regset.subset_2
def empty_1 : Prop := CompCert4Lean.Backend.Registers.Regset.empty_1
def is_empty_1 : Prop := CompCert4Lean.Backend.Registers.Regset.is_empty_1
def is_empty_2 : Prop := CompCert4Lean.Backend.Registers.Regset.is_empty_2
def add_1 : Prop := CompCert4Lean.Backend.Registers.Regset.add_1
def add_2 : Prop := CompCert4Lean.Backend.Registers.Regset.add_2
def add_3 : Prop := CompCert4Lean.Backend.Registers.Regset.add_3
def remove_1 : Prop := CompCert4Lean.Backend.Registers.Regset.remove_1
def remove_2 : Prop := CompCert4Lean.Backend.Registers.Regset.remove_2
def remove_3 : Prop := CompCert4Lean.Backend.Registers.Regset.remove_3
def union_1 : Prop := CompCert4Lean.Backend.Registers.Regset.union_1
def union_2 : Prop := CompCert4Lean.Backend.Registers.Regset.union_2
def union_3 : Prop := CompCert4Lean.Backend.Registers.Regset.union_3
def inter_1 : Prop := CompCert4Lean.Backend.Registers.Regset.inter_1
def inter_2 : Prop := CompCert4Lean.Backend.Registers.Regset.inter_2
def inter_3 : Prop := CompCert4Lean.Backend.Registers.Regset.inter_3
def diff_1 : Prop := CompCert4Lean.Backend.Registers.Regset.diff_1
def diff_2 : Prop := CompCert4Lean.Backend.Registers.Regset.diff_2
def diff_3 : Prop := CompCert4Lean.Backend.Registers.Regset.diff_3
def singleton_1 : Prop := CompCert4Lean.Backend.Registers.Regset.singleton_1
def singleton_2 : Prop := CompCert4Lean.Backend.Registers.Regset.singleton_2
def fold_1 : Prop := CompCert4Lean.Backend.Registers.Regset.fold_1
def cardinal_1 : Prop := CompCert4Lean.Backend.Registers.Regset.cardinal_1
def filter_1 : Prop := CompCert4Lean.Backend.Registers.Regset.filter_1
def filter_2 : Prop := CompCert4Lean.Backend.Registers.Regset.filter_2
def filter_3 : Prop := CompCert4Lean.Backend.Registers.Regset.filter_3
def for_all_1 : Prop := CompCert4Lean.Backend.Registers.Regset.for_all_1
def for_all_2 : Prop := CompCert4Lean.Backend.Registers.Regset.for_all_2
def exists_1 : Prop := CompCert4Lean.Backend.Registers.Regset.exists_1
def exists_2 : Prop := CompCert4Lean.Backend.Registers.Regset.exists_2
def partition_1 : Prop := CompCert4Lean.Backend.Registers.Regset.partition_1
def partition_2 : Prop := CompCert4Lean.Backend.Registers.Regset.partition_2
def choose_1 : Prop := CompCert4Lean.Backend.Registers.Regset.choose_1
def choose_2 : Prop := CompCert4Lean.Backend.Registers.Regset.choose_2
def elements_1 : Prop := CompCert4Lean.Backend.Registers.Regset.elements_1
def elements_2 : Prop := CompCert4Lean.Backend.Registers.Regset.elements_2
def elements_3w : Prop := CompCert4Lean.Backend.Registers.Regset.elements_3w
def min_elt_1 : Prop := CompCert4Lean.Backend.Registers.Regset.min_elt_1
def min_elt_2 : Prop := CompCert4Lean.Backend.Registers.Regset.min_elt_2
def min_elt_3 : Prop := CompCert4Lean.Backend.Registers.Regset.min_elt_3
def max_elt_1 : Prop := CompCert4Lean.Backend.Registers.Regset.max_elt_1
def max_elt_2 : Prop := CompCert4Lean.Backend.Registers.Regset.max_elt_2
def max_elt_3 : Prop := CompCert4Lean.Backend.Registers.Regset.max_elt_3
def elements_3 : Prop := CompCert4Lean.Backend.Registers.Regset.elements_3
def choose_3 : Prop := CompCert4Lean.Backend.Registers.Regset.choose_3
def lt_trans : Prop := CompCert4Lean.Backend.Registers.Regset.lt_trans
def lt_not_eq : Prop := CompCert4Lean.Backend.Registers.Regset.lt_not_eq
def compare : Type := CompCert4Lean.Backend.Registers.Regset.compare

end Nodeset

namespace DS

def L : CompCert4Lean.Backend.Kildall.SemiLattice := booleanLattice

def law_obligation : Prop :=
  CompCert4Lean.Backend.Kildall.SemiLatticeLaws L ∧
    CompCert4Lean.Backend.Kildall.NodeSetForward.law_obligation

def DS : Type :=
  CompCert4Lean.Backend.Kildall.Dataflow_Solver L
    CompCert4Lean.Backend.Kildall.NodeSetForward

abbrev state :=
  CompCert4Lean.Backend.Kildall.Dataflow_Solver.state L
    CompCert4Lean.Backend.Kildall.NodeSetForward

def aval (st : state) : PTree.t L.t :=
  CompCert4Lean.Backend.Kildall.Dataflow_Solver.aval st

def worklist (st : state) : CompCert4Lean.Backend.Kildall.NodeSetForward.t :=
  CompCert4Lean.Backend.Kildall.Dataflow_Solver.worklist st

def visited (st : state) (n : positive) : Prop :=
  CompCert4Lean.Backend.Kildall.Dataflow_Solver.visited st n

def abstr_value (n : positive) (st : state) : L.t :=
  CompCert4Lean.Backend.Kildall.Dataflow_Solver.abstr_value n st

def propagate_succ (st : state) (out : L.t) (n : positive) : state :=
  CompCert4Lean.Backend.Kildall.Dataflow_Solver.propagate_succ st out n

def propagate_succ_list (st : state) (out : L.t) (l : List positive) : state :=
  CompCert4Lean.Backend.Kildall.Dataflow_Solver.propagate_succ_list st out l

def step {A : Type} (code : PTree.t A) (successors : A → List positive)
    (transf : positive → L.t → L.t) (st : state) :
    Sum (PMap.t L.t) state :=
  CompCert4Lean.Backend.Kildall.Dataflow_Solver.step
    code successors transf st

def fixpoint_from {A : Type} (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t) (st : state) : Option (PMap.t L.t) :=
  CompCert4Lean.Backend.Kildall.Dataflow_Solver.fixpoint_from
    code successors transf st

def start_state (enode : positive) (eval : L.t) : state :=
  CompCert4Lean.Backend.Kildall.Dataflow_Solver.start_state enode eval

def fixpoint {A : Type} (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t)
    (enode : positive) (eval : L.t) : Option (PMap.t L.t) :=
  CompCert4Lean.Backend.Kildall.Dataflow_Solver.fixpoint
    L CompCert4Lean.Backend.Kildall.NodeSetForward
    code successors transf enode eval

def start_state_nodeset
    (enodes : CompCert4Lean.Backend.Kildall.NodeSetForward.t) : state :=
  CompCert4Lean.Backend.Kildall.Dataflow_Solver.start_state_nodeset
    CompCert4Lean.Backend.Kildall.NodeSetForward enodes

def fixpoint_nodeset {A : Type} (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t)
    (enodes : CompCert4Lean.Backend.Kildall.NodeSetForward.t) :
    Option (PMap.t L.t) :=
  CompCert4Lean.Backend.Kildall.Dataflow_Solver.fixpoint_nodeset
    L CompCert4Lean.Backend.Kildall.NodeSetForward
    code successors transf enodes

def start_state_allnodes {A : Type} (code : PTree.t A) : state :=
  CompCert4Lean.Backend.Kildall.Dataflow_Solver.start_state_allnodes
    CompCert4Lean.Backend.Kildall.NodeSetForward code

def fixpoint_allnodes {A : Type} (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t) : Option (PMap.t L.t) :=
  CompCert4Lean.Backend.Kildall.Dataflow_Solver.fixpoint_allnodes
    L CompCert4Lean.Backend.Kildall.NodeSetForward
    code successors transf

abbrev optge : Option L.t → Option L.t → Prop :=
  CompCert4Lean.Backend.Kildall.Dataflow_Solver.optge L

def optge_refl : Prop :=
  ∀ ol : Option L.t, optge ol ol

def optge_trans : Prop :=
  ∀ ol1 ol2 ol3 : Option L.t,
    optge ol1 ol2 → optge ol2 ol3 → optge ol1 ol3

def optge_abstr_value : Prop :=
  ∀ (st st' : state) (n : positive),
    optge (PTree.get n (aval st)) (PTree.get n (aval st')) →
    L.ge (abstr_value n st) (abstr_value n st')

def propagate_succ_charact : Prop :=
  ∀ (transf : positive → L.t → L.t) (st : state) (out : L.t) (n : positive),
    let st' := propagate_succ st out n
    optge (PTree.get n (aval st')) (some out) ∧
      (∀ s : positive, n ≠ s →
        PTree.get s (aval st') = PTree.get s (aval st)) ∧
      (∀ s : positive,
        optge (PTree.get s (aval st')) (PTree.get s (aval st))) ∧
      (CompCert4Lean.Backend.Kildall.NodeSetForward.In n (worklist st') ∨
        PTree.get n (aval st') = PTree.get n (aval st)) ∧
      (∀ n',
        CompCert4Lean.Backend.Kildall.NodeSetForward.In n' (worklist st) →
          CompCert4Lean.Backend.Kildall.NodeSetForward.In n' (worklist st')) ∧
      (∀ n',
        CompCert4Lean.Backend.Kildall.NodeSetForward.In n' (worklist st') →
          n' = n ∨
            CompCert4Lean.Backend.Kildall.NodeSetForward.In n' (worklist st)) ∧
      (∀ n', visited st n' → visited st' n') ∧
      (∀ n', visited st' n' →
        CompCert4Lean.Backend.Kildall.NodeSetForward.In n' (worklist st') ∨
          visited st n') ∧
      (∀ n', PTree.get n' (aval st) = none →
        PTree.get n' (aval st') ≠ none → visited st' n')

def propagate_succ_list_charact : Prop :=
  ∀ (transf : positive → L.t → L.t) (out : L.t)
    (l : List positive) (st : state),
    let st' := propagate_succ_list st out l
    (∀ n : positive, n ∈ l →
      optge (PTree.get n (aval st')) (some out)) ∧
      (∀ n : positive, n ∉ l →
        PTree.get n (aval st') = PTree.get n (aval st)) ∧
      (∀ n : positive,
        optge (PTree.get n (aval st')) (PTree.get n (aval st))) ∧
      (∀ n : positive,
        CompCert4Lean.Backend.Kildall.NodeSetForward.In n (worklist st') ∨
          PTree.get n (aval st') = PTree.get n (aval st)) ∧
      (∀ n',
        CompCert4Lean.Backend.Kildall.NodeSetForward.In n' (worklist st) →
          CompCert4Lean.Backend.Kildall.NodeSetForward.In n' (worklist st')) ∧
      (∀ n',
        CompCert4Lean.Backend.Kildall.NodeSetForward.In n' (worklist st') →
          n' ∈ l ∨
            CompCert4Lean.Backend.Kildall.NodeSetForward.In n' (worklist st)) ∧
      (∀ n', visited st n' → visited st' n') ∧
      (∀ n', visited st' n' →
        CompCert4Lean.Backend.Kildall.NodeSetForward.In n' (worklist st') ∨
          visited st n') ∧
      (∀ n', PTree.get n' (aval st) = none →
        PTree.get n' (aval st') ≠ none → visited st' n')

abbrev steps {A : Type} (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t) : state → state → Prop :=
  CompCert4Lean.Backend.Kildall.Dataflow_Solver.steps code successors transf

def steps_ind : Type := Unit

def fixpoint_from_charact : Prop :=
  ∀ (A : Type) (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t) (start : state)
    (res : PMap.t L.t),
    fixpoint_from code successors transf start = some res →
    ∃ st : state,
      steps code successors transf start st ∧
        CompCert4Lean.Backend.Kildall.NodeSetForward.pick (worklist st) = none ∧
        res = (L.bot, aval st)

def step_incr : Prop :=
  ∀ (A : Type) (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t) (n : positive)
    (s1 s2 : state),
    step code successors transf s1 = Sum.inr s2 →
    optge (PTree.get n (aval s2)) (PTree.get n (aval s1)) ∧
      (visited s1 n → visited s2 n)

def steps_incr : Prop :=
  ∀ (A : Type) (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t) (n : positive)
    (s1 s2 : state),
    steps code successors transf s1 s2 →
    optge (PTree.get n (aval s2)) (PTree.get n (aval s1)) ∧
      (visited s1 n → visited s2 n)

abbrev good_state {A : Type} (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t) (st : state) : Prop :=
  CompCert4Lean.Backend.Kildall.Dataflow_Solver.good_state
    code successors transf st

def gs_stable : Prop :=
  ∀ {A : Type} (code : PTree.t A) (successors : A → List positive)
    (transf : positive → L.t → L.t) (st : state),
    good_state code successors transf st →
    ∀ n, visited st n →
      CompCert4Lean.Backend.Kildall.NodeSetForward.In n (worklist st) ∨
        ∀ (i : A) (s : positive), PTree.get n code = some i →
          s ∈ successors i →
          optge (PTree.get s (aval st))
            (some (transf n (abstr_value n st)))

def gs_defined : Prop :=
  ∀ {A : Type} (code : PTree.t A) (successors : A → List positive)
    (transf : positive → L.t → L.t) (st : state),
    good_state code successors transf st →
    ∀ (n : positive) (v : L.t),
      PTree.get n (aval st) = some v → visited st n

def step_state_good : Prop :=
  ∀ (A : Type) (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t) (st : state)
    (pc : positive)
    (rem : CompCert4Lean.Backend.Kildall.NodeSetForward.t) (instr : A),
    CompCert4Lean.Backend.Kildall.NodeSetForward.pick (worklist st) =
      some (pc, rem) →
    PTree.get pc code = some instr →
    good_state code successors transf st →
      good_state code successors transf
      (propagate_succ_list
        { aval := aval st
          worklist := rem
          visited := visited st }
        (transf pc (abstr_value pc st)) (successors instr))

def step_state_good_2 : Prop :=
  ∀ (A : Type) (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t) (st : state)
    (pc : positive)
    (rem : CompCert4Lean.Backend.Kildall.NodeSetForward.t),
    good_state code successors transf st →
    CompCert4Lean.Backend.Kildall.NodeSetForward.pick (worklist st) =
      some (pc, rem) →
    PTree.get pc code = none →
    good_state code successors transf
      { aval := aval st
        worklist := rem
        visited := visited st }

def steps_state_good : Prop :=
  ∀ (A : Type) (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t) (st1 st2 : state),
    steps code successors transf st1 st2 →
    good_state code successors transf st1 →
    good_state code successors transf st2

def start_state_good : Prop :=
  ∀ (A : Type) (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t)
    (enode : positive) (eval : L.t),
    good_state code successors transf (start_state enode eval)

def start_state_nodeset_good : Prop :=
  ∀ (A : Type) (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t)
    (enodes : CompCert4Lean.Backend.Kildall.NodeSetForward.t),
    good_state code successors transf (start_state_nodeset enodes)

def start_state_allnodes_good : Prop :=
  ∀ (A : Type) (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t),
    good_state code successors transf (start_state_allnodes code)

def reachable_visited : Prop :=
  ∀ (A : Type) (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t) (st : state),
    good_state code successors transf st →
    CompCert4Lean.Backend.Kildall.NodeSetForward.pick (worklist st) = none →
    ∀ p q,
      CompCert4Lean.Backend.Kildall.reachable code successors p q →
      visited st p → visited st q

def fixpoint_solution : Prop :=
  ∀ (A : Type) (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t)
    (ep : positive) (ev : L.t) (res : PMap.t L.t)
    (n : positive) (instr : A) (s : positive),
    fixpoint code successors transf ep ev = some res →
    PTree.get n code = some instr →
    s ∈ successors instr →
    (∀ n0, L.eq (transf n0 L.bot) L.bot) →
    L.ge (PMap.get s res) (transf n (PMap.get n res))

def fixpoint_entry : Prop :=
  ∀ (A : Type) (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t)
    (ep : positive) (ev : L.t) (res : PMap.t L.t),
    fixpoint code successors transf ep ev = some res →
    L.ge (PMap.get ep res) ev

def fixpoint_allnodes_solution : Prop :=
  ∀ (A : Type) (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t) (res : PMap.t L.t)
    (n : positive) (instr : A) (s : positive),
    fixpoint_allnodes code successors transf = some res →
    PTree.get n code = some instr →
    s ∈ successors instr →
    L.ge (PMap.get n res) (transf n (PMap.get n res))

def fixpoint_nodeset_solution : Prop :=
  ∀ (A : Type) (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t)
    (enodes : CompCert4Lean.Backend.Kildall.NodeSetForward.t)
    (res : PMap.t L.t) (e n : positive) (instr : A) (s : positive),
    fixpoint_nodeset code successors transf enodes = some res →
    CompCert4Lean.Backend.Kildall.NodeSetForward.In e enodes →
    CompCert4Lean.Backend.Kildall.reachable code successors e n →
    PTree.get n code = some instr →
    s ∈ successors instr →
    L.ge (PMap.get s res) (transf n (PMap.get n res))

def fixpoint_invariant : Prop :=
  ∀ (A : Type) (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t)
    (ep : positive) (ev : L.t) (P : L.t → Prop),
    P L.bot →
    (∀ x y, P x → P y → P (L.lub x y)) →
    (∀ pc instr x, PTree.get pc code = some instr →
      P x → P (transf pc x)) →
    P ev →
    ∀ (res : PMap.t L.t) (pc : positive),
      fixpoint code successors transf ep ev = some res →
      P (PMap.get pc res)

end DS

end CompCert4Lean.Backend.Linearize
