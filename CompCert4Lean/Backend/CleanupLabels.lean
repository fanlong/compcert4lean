import CompCert4Lean.Backend.Linear
import CompCert4Lean.Backend.Registers
import CompCert4Lean.Lib.Coqlib

/-!
# Removal of labels that are not branch targets

Definition-bearing translation of CompCert's `backend/CleanupLabels.v`.
The generated `FSetAVL.Make(OrderedPositive)` application is exposed through
the integrated positive finite-set API owned by `Registers.Regset`.
-/

namespace CompCert4Lean.Backend.CleanupLabels

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Coqlib

/-! ## Generated positive finite-set application -/

namespace Labelset

def Labelset : Type := Unit

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

end Labelset

/-! ## Label-target analysis and transformation -/

def add_label_branched_to (ls : Labelset.t) (i : instruction) : Labelset.t :=
  match i with
  | Lgoto lbl => Labelset.add lbl ls
  | Lcond _ _ lbl => Labelset.add lbl ls
  | Ljumptable _ tbl => tbl.foldr Labelset.add ls
  | _ => ls

def labels_branched_to (c : code) : Labelset.t :=
  c.foldl (fun ls i => add_label_branched_to ls i) Labelset.empty

def remove_unused (bto : Labelset.t) (i : instruction) (k : code) : code :=
  match i with
  | Llabel lbl => if Labelset.mem lbl bto then i :: k else k
  | _ => i :: k

def remove_unused_labels (bto : Labelset.t) (c : code) : code :=
  list_fold_right (remove_unused bto) c []

def cleanup_labels (c : code) : code :=
  remove_unused_labels (labels_branched_to c) c

def transf_function (f : function) : function :=
  { fn_sig := f.fn_sig
    fn_stacksize := f.fn_stacksize
    fn_code := cleanup_labels f.fn_code }

def transf_fundef (f : fundef) : fundef :=
  CompCert4Lean.Common.AST.transf_fundef transf_function f

def transf_program (p : program) : program :=
  CompCert4Lean.Common.AST.transform_program transf_fundef p

end CompCert4Lean.Backend.CleanupLabels
