import CompCert4Lean.Backend.RTL
import CompCert4Lean.Common.Errors
import CompCert4Lean.Lib.Iteration

/-!
# Elimination of unreferenced static definitions

Definition-bearing translation of CompCert's `backend/Unusedglob.v`.  The
generated `FSetAVL.Make(OrderedPositive)` surface is adapted to the already
integrated positive finite-set implementation used by `Registers.Regset`.
-/

namespace CompCert4Lean.Backend.Unusedglob

open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Lib.Iteration
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Op

/-! ## Generated positive finite-set application -/

namespace IS

def IS : Type := Unit

abbrev elt : Type := CompCert4Lean.Backend.Registers.Regset.elt
abbrev t : Type := CompCert4Lean.Backend.Registers.Regset.t

def «X'» : Type := CompCert4Lean.Backend.Registers.Regset.«X'»

namespace X'

abbrev t : Type := CompCert4Lean.Backend.Registers.Regset.X'.t
def eq : t → t → Prop := CompCert4Lean.Backend.Registers.Regset.X'.eq
def lt : t → t → Prop := CompCert4Lean.Backend.Registers.Regset.X'.lt

end X'

def MSet : Type := CompCert4Lean.Backend.Registers.Regset.MSet

namespace MSet
end MSet

def MF : Type := CompCert4Lean.Backend.Registers.Regset.MF

namespace MF
end MF

def E : Type := CompCert4Lean.Backend.Registers.Regset.E

namespace E
end E

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
def fold {A : Type} : (elt → A → A) → t → A → A := CompCert4Lean.Backend.Registers.Regset.fold
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

/-! Proof-bearing generated members are exact proposition/type descriptors. -/

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

end IS

/-! ## Referenced globals -/

structure workset : Type where
  w_seen : IS.t
  w_todo : List ident

export workset (w_seen w_todo)

instance : Coe workset IS.t where
  coe := workset.w_seen

def add_workset (id : ident) (w : workset) : workset :=
  if IS.mem id w.w_seen then
    w
  else
    { w_seen := IS.add id w.w_seen
      w_todo := id :: w.w_todo }

def addlist_workset : List ident → workset → workset
  | [], w => w
  | id :: rest, w => addlist_workset rest (add_workset id w)

def ref_instruction : instruction → List ident
  | .Inop _ => []
  | .Iop op _ _ _ => globals_operation op
  | .Iload _ addr _ _ _ => globals_addressing addr
  | .Istore _ addr _ _ _ => globals_addressing addr
  | .Icall _ (.inl _) _ _ _ => []
  | .Icall _ (.inr id) _ _ _ => [id]
  | .Itailcall _ (.inl _) _ => []
  | .Itailcall _ (.inr id) _ => [id]
  | .Ibuiltin _ args _ _ => globals_of_builtin_args args
  | .Icond _ _ _ _ => []
  | .Ijumptable _ _ => []
  | .Ireturn _ => []

def add_ref_instruction (w : workset) (_pc : node) (i : instruction) : workset :=
  addlist_workset (ref_instruction i) w

def add_ref_function (f : function) (w : workset) : workset :=
  PTree.fold add_ref_instruction f.fn_code w

def add_ref_init_data (w : workset) (i : init_data) : workset :=
  match i with
  | .Init_addrof id _ => add_workset id w
  | _ => w

def add_ref_globvar (gv : globvar Unit) (w : workset) : workset :=
  gv.gvar_init.foldl add_ref_init_data w

def prog_map : Type := PTree.t (globdef fundef Unit)

def add_ref_definition (pm : prog_map) (id : ident) (w : workset) : workset :=
  match PTree.get id pm with
  | none => w
  | some (.Gfun (.Internal f)) => add_ref_function f w
  | some (.Gfun (.External _)) => w
  | some (.Gvar gv) => add_ref_globvar gv w

def initial_workset (p : program) : workset :=
  add_workset p.prog_main
    (p.prog_public.foldl
      (fun w id => add_workset id w)
      { w_seen := IS.empty, w_todo := [] })

/-! ## Dependency-graph traversal -/

def iter_step (pm : prog_map) (w : workset) : Sum IS.t workset :=
  match w.w_todo with
  | [] => .inl w.w_seen
  | id :: remaining =>
      .inr (add_ref_definition pm id
        { w_seen := w.w_seen, w_todo := remaining })

def used_globals (p : program) (pm : prog_map) : Option IS.t :=
  PrimIter.iterate (iter_step pm) (initial_workset p)

/-! ## Filtering global definitions -/

def filter_globdefs (used : IS.t)
    (accu defs : List (ident × globdef fundef Unit)) :
    List (ident × globdef fundef Unit) :=
  match defs with
  | [] => accu
  | (id, gd) :: rest =>
      if IS.mem id used then
        filter_globdefs (IS.remove id used) ((id, gd) :: accu) rest
      else
        filter_globdefs used accu rest

def global_defined (p : program) (pm : prog_map) (id : ident) : Bool :=
  match PTree.get id pm with
  | some _ => true
  | none =>
      match ident_eq id p.prog_main with
      | .left _ => true
      | .right _ => false

private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string

private def rocqStringOfBytes : List UInt8 → RocqString
  | [] => .EmptyString
  | byte :: rest => .String byte (rocqStringOfBytes rest)

private def analysisFailedText : RocqString :=
  rocqStringOfBytes
    [85, 110, 117, 115, 101, 100, 103, 108, 111, 98, 58, 32, 97, 110, 97,
      108, 121, 115, 105, 115, 32, 102, 97, 105, 108, 101, 100]

private def undefinedGlobalText : RocqString :=
  rocqStringOfBytes
    [85, 110, 117, 115, 101, 100, 103, 108, 111, 98, 58, 32, 114, 101, 102,
      101, 114, 101, 110, 99, 101, 32, 116, 111, 32, 117, 110, 100, 101, 102,
      105, 110, 101, 100, 32, 103, 108, 111, 98, 97, 108]

def transform_program (p : program) : res program :=
  let pm := prog_defmap p
  match used_globals p pm with
  | none => .Error (msg analysisFailedText)
  | some used =>
      if IS.for_all (global_defined p pm) used then
        .OK
          { prog_defs := filter_globdefs used [] p.prog_defs.reverse
            prog_public := p.prog_public
            prog_main := p.prog_main }
      else
        .Error (msg undefinedGlobalText)

end CompCert4Lean.Backend.Unusedglob
