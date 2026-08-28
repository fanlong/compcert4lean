import CompCert4Lean.Backend.Linear
import CompCert4Lean.Backend.Registers
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.FSetAVLplus
import CompCert4Lean.Lib.Ordered

/-!
# Removal of labels that are not branch targets

Definition-bearing translation of CompCert's `backend/CleanupLabels.v`.
The generated `FSetAVL.Make(OrderedPositive)` application is exposed through
the local source-shaped finite-set API, with comparison supplied by the
canonical `Lib.Ordered.OrderedPositive` provider.
-/

namespace CompCert4Lean.Backend.CleanupLabels

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Coqlib

/-! ## Generated positive finite-set application -/

namespace Labelset

def Labelset : Type := Unit

open CompCert4Lean.Lib.FSetAVLplus
open CompCert4Lean.Lib.Ordered

private abbrev OrderedType :=
  CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.OrderedType
private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool

def EOrder : OrderedType where
  t := OrderedPositive.t
  eq := OrderedPositive.eq
  lt := OrderedPositive.lt
  eq_refl := fun _ => rfl
  eq_sym := by intro x y h; exact h.symm
  eq_trans := by intro x y z hxy hyz; exact hxy.trans hyz
  lt_trans := by intro x y z hxy hyz; exact Nat.lt_trans hxy hyz
  lt_not_eq := by
    intro x y hxy heq
    cases heq
    exact Nat.lt_irrefl _ hxy
  compare := OrderedPositive.compare
  eq_dec := CompCert4Lean.Lib.Coqlib.peq

abbrev E : Type := EOrder.t
abbrev «X'» : Type := E

namespace X'

abbrev orderedType : OrderedType := EOrder
abbrev t : Type := E
abbrev eq : t → t → Prop := EOrder.eq
abbrev lt : t → t → Prop := EOrder.lt

end X'

abbrev MSet : Type := Make.MSet EOrder
namespace MSet

abbrev Mkt (this : Make.Raw.tree EOrder) (is_ok : Make.Raw.Ok this) : MSet :=
  @Make.MSet.Mkt EOrder this is_ok
abbrev this : MSet → Make.Raw.tree EOrder := @Make.MSet.this EOrder
abbrev is_ok (self : MSet) : Make.Raw.Ok (@Make.MSet.this EOrder self) :=
  @Make.MSet.is_ok EOrder self

end MSet

abbrev MFType := CompCert4Lean.Lib.FSetFacts.WFacts_fun
  (CompCert4Lean.Lib.FSetInterface.OrderedType.toDecidableType EOrder)
  (Make.toSfun EOrder).toWSfun
def MFProvider : MFType := Make.MF EOrder
abbrev MF : Type := PLift (Nonempty MFType)
namespace MF

abbrev provider : MFType := MFProvider

end MF

namespace E

abbrev orderedType : OrderedType := EOrder
abbrev t : Type := E
abbrev eq : t → t → Prop := EOrder.eq
abbrev lt : t → t → Prop := EOrder.lt
abbrev compare := EOrder.compare
abbrev eq_dec := EOrder.eq_dec

end E

abbrev elt : Type := Make.elt EOrder
abbrev t : Type := Make.t EOrder

def In : elt → t → Prop := Make.In (X := EOrder)
def Equal : t → t → Prop := Make.Equal (X := EOrder)
def Subset : t → t → Prop := Make.Subset (X := EOrder)
def Empty : t → Prop := Make.Empty (X := EOrder)
def For_all : (elt → Prop) → t → Prop := Make.For_all (X := EOrder)
def Exists : (elt → Prop) → t → Prop := Make.Exists (X := EOrder)

def empty : t := Make.empty (X := EOrder)
def is_empty : t → Bool := Make.is_empty (X := EOrder)
def mem : elt → t → Bool := Make.mem (X := EOrder)
def add : elt → t → t := Make.add (X := EOrder)
def singleton : elt → t := Make.singleton (X := EOrder)
def remove : elt → t → t := Make.remove (X := EOrder)
def union : t → t → t := Make.union (X := EOrder)
def inter : t → t → t := Make.inter (X := EOrder)
def diff : t → t → t := Make.diff (X := EOrder)
def eq : t → t → Prop := Make.eq (X := EOrder)
def eq_dec (s s' : t) : Sumbool (eq s s') (¬ eq s s') :=
  Make.eq_dec s s'
def equal : t → t → Bool := Make.equal (X := EOrder)
def subset : t → t → Bool := Make.subset (X := EOrder)
def fold {A : Type} (f : elt → A → A) (s : t) (i : A) : A :=
  Make.fold (X := EOrder) f s i
def for_all : (elt → Bool) → t → Bool := Make.for_all (X := EOrder)
def exists_ : (elt → Bool) → t → Bool := Make.exists_ (X := EOrder)
def filter : (elt → Bool) → t → t := Make.filter (X := EOrder)
def partition : (elt → Bool) → t → t × t := Make.partition (X := EOrder)
def cardinal : t → Nat := Make.cardinal (X := EOrder)
def elements : t → List elt := Make.elements (X := EOrder)
def choose : t → Option elt := Make.choose (X := EOrder)
def lt : t → t → Prop := Make.lt (X := EOrder)
def min_elt : t → Option elt := Make.min_elt (X := EOrder)
def max_elt : t → Option elt := Make.max_elt (X := EOrder)

/-! Proof-bearing generated members are exact proposition/type descriptors. -/

private abbrev CompatBool (R : elt → elt → Prop) (f : elt → Bool) : Prop :=
  CompCert4Lean.Lib.FSetInterface.compat_bool R f
private abbrev NoDupA (R : elt → elt → Prop) (l : List elt) : Prop :=
  CompCert4Lean.Lib.FSetInterface.NoDupA R l
private abbrev Sorted (R : elt → elt → Prop) (l : List elt) : Prop :=
  CompCert4Lean.Lib.FSetInterface.sort R l

def In_1 : Prop := ∀ (s : t) (x y : elt), x = y → In x s → In y s
def eq_refl : Prop := ∀ s : t, eq s s
def eq_sym : Prop := ∀ s s' : t, eq s s' → eq s' s
def eq_trans : Prop := ∀ s s' s'' : t, eq s s' → eq s' s'' → eq s s''
def mem_1 : Prop := ∀ (s : t) (x : elt), In x s → mem x s = true
def mem_2 : Prop := ∀ (s : t) (x : elt), mem x s = true → In x s
def equal_1 : Prop := ∀ s s' : t, Equal s s' → equal s s' = true
def equal_2 : Prop := ∀ s s' : t, equal s s' = true → Equal s s'
def subset_1 : Prop := ∀ s s' : t, Subset s s' → subset s s' = true
def subset_2 : Prop := ∀ s s' : t, subset s s' = true → Subset s s'
def empty_1 : Prop := Empty empty
def is_empty_1 : Prop := ∀ s : t, Empty s → is_empty s = true
def is_empty_2 : Prop := ∀ s : t, is_empty s = true → Empty s
def add_1 : Prop := ∀ (s : t) (x y : elt), x = y → In y (add x s)
def add_2 : Prop := ∀ (s : t) (x y : elt), In y s → In y (add x s)
def add_3 : Prop := ∀ (s : t) (x y : elt), x ≠ y → In y (add x s) → In y s
def remove_1 : Prop := ∀ (s : t) (x y : elt), x = y → ¬ In y (remove x s)
def remove_2 : Prop := ∀ (s : t) (x y : elt), x ≠ y → In y s → In y (remove x s)
def remove_3 : Prop := ∀ (s : t) (x y : elt), In y (remove x s) → In y s
def union_1 : Prop := ∀ (s s' : t) (x : elt), In x (union s s') → In x s ∨ In x s'
def union_2 : Prop := ∀ (s s' : t) (x : elt), In x s → In x (union s s')
def union_3 : Prop := ∀ (s s' : t) (x : elt), In x s' → In x (union s s')
def inter_1 : Prop := ∀ (s s' : t) (x : elt), In x (inter s s') → In x s
def inter_2 : Prop := ∀ (s s' : t) (x : elt), In x (inter s s') → In x s'
def inter_3 : Prop := ∀ (s s' : t) (x : elt), In x s → In x s' → In x (inter s s')
def diff_1 : Prop := ∀ (s s' : t) (x : elt), In x (diff s s') → In x s
def diff_2 : Prop := ∀ (s s' : t) (x : elt), In x (diff s s') → ¬ In x s'
def diff_3 : Prop := ∀ (s s' : t) (x : elt), In x s → ¬ In x s' → In x (diff s s')
def singleton_1 : Prop := ∀ x y : elt, In y (singleton x) → x = y
def singleton_2 : Prop := ∀ x y : elt, x = y → In y (singleton x)
def fold_1 : Prop :=
  ∀ (s : t) (A : Type) (i : A) (f : elt → A → A),
    fold f s i = List.foldl (fun a e => f e a) i (elements s)
def cardinal_1 : Prop := ∀ s : t, cardinal s = (elements s).length
def filter_1 : Prop :=
  ∀ (s : t) (x : elt) (f : elt → Bool),
    CompatBool (fun x y => x = y) f → In x (filter f s) → In x s
def filter_2 : Prop :=
  ∀ (s : t) (x : elt) (f : elt → Bool),
    CompatBool (fun x y => x = y) f → In x (filter f s) → f x = true
def filter_3 : Prop :=
  ∀ (s : t) (x : elt) (f : elt → Bool),
    CompatBool (fun x y => x = y) f → In x s → f x = true → In x (filter f s)
def for_all_1 : Prop :=
  ∀ (s : t) (f : elt → Bool), CompatBool (fun x y => x = y) f →
    For_all (fun x => f x = true) s → for_all f s = true
def for_all_2 : Prop :=
  ∀ (s : t) (f : elt → Bool), CompatBool (fun x y => x = y) f →
    for_all f s = true → For_all (fun x => f x = true) s
def exists_1 : Prop :=
  ∀ (s : t) (f : elt → Bool), CompatBool (fun x y => x = y) f →
    Exists (fun x => f x = true) s → exists_ f s = true
def exists_2 : Prop :=
  ∀ (s : t) (f : elt → Bool), CompatBool (fun x y => x = y) f →
    exists_ f s = true → Exists (fun x => f x = true) s
def partition_1 : Prop :=
  ∀ (s : t) (f : elt → Bool), CompatBool (fun x y => x = y) f →
    Equal (partition f s).1 (filter f s)
def partition_2 : Prop :=
  ∀ (s : t) (f : elt → Bool), CompatBool (fun x y => x = y) f →
    Equal (partition f s).2 (filter (fun x => !(f x)) s)
def choose_1 : Prop := ∀ (s : t) (x : elt), choose s = some x → In x s
def choose_2 : Prop := ∀ s : t, choose s = none → Empty s
def elements_1 : Prop :=
  ∀ (s : t) (x : elt), In x s →
    CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA
      (fun x y : elt => x = y) x (elements s)
def elements_2 : Prop :=
  ∀ (s : t) (x : elt),
    CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA
      (fun x y : elt => x = y) x (elements s) → In x s
def elements_3w : Prop :=
  ∀ s : t, NoDupA (fun x y : elt => x = y) (elements s)
def min_elt_1 : Prop := ∀ (s : t) (x : elt), min_elt s = some x → In x s
def min_elt_2 : Prop :=
  ∀ (s : t) (x y : elt), min_elt s = some x → In y s →
    ¬ CompCert4Lean.Lib.Coqlib.Plt y x
def min_elt_3 : Prop := ∀ s : t, min_elt s = none → Empty s
def max_elt_1 : Prop := ∀ (s : t) (x : elt), max_elt s = some x → In x s
def max_elt_2 : Prop :=
  ∀ (s : t) (x y : elt), max_elt s = some x → In y s →
    ¬ CompCert4Lean.Lib.Coqlib.Plt x y
def max_elt_3 : Prop := ∀ s : t, max_elt s = none → Empty s
def elements_3 : Prop :=
  ∀ s : t, Sorted CompCert4Lean.Lib.Coqlib.Plt (elements s)
def choose_3 : Prop :=
  ∀ (s s' : t) (x y : elt), choose s = some x → choose s' = some y →
    Equal s s' → x = y
def lt_trans : Prop := ∀ s s' s'' : t, lt s s' → lt s' s'' → lt s s''
def lt_not_eq : Prop := ∀ s s' : t, lt s s' → ¬ eq s s'
def compare : Type :=
  ∀ s s' : t,
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.Compare
      lt eq s s'

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
