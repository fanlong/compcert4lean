import CompCert4Lean.Common.Values
import CompCert4Lean.Lib.FSetAVLplus
import CompCert4Lean.Lib.Maps
import CompCert4Lean.Lib.Ordered

/-!
# Pseudo-registers and register states

This module is the checked definition-translation surface for
`backend/Registers.v`. Executable declarations are translated directly over
the source-shaped positive-number and applicative-map providers. Proof
declarations assigned to later proof migration are retained as exact
proposition descriptors.
-/

namespace CompCert4Lean.Backend.Registers

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values

def reg : Type := positive

instance : DecidableEq reg := by
  change DecidableEq positive
  exact inferInstance

namespace Reg

def eq (x y : reg) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) :=
  CompCert4Lean.Lib.Coqlib.peq x y

end Reg

namespace Regmap

abbrev Regmap (A : Type) : Type := CompCert4Lean.Lib.Maps.PMap.t A
abbrev elt : Type := CompCert4Lean.Lib.Maps.PMap.elt
abbrev t (A : Type) : Type := CompCert4Lean.Lib.Maps.PMap.t A
def elt_eq (x y : elt) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) :=
  CompCert4Lean.Lib.Coqlib.peq x y
abbrev init {A : Type} (x : A) : t A :=
  CompCert4Lean.Lib.Maps.PMap.init x
abbrev get {A : Type} (r : reg) (rs : t A) : A :=
  CompCert4Lean.Lib.Maps.PMap.get r rs
abbrev set {A : Type} (r : reg) (v : A) (rs : t A) : t A :=
  CompCert4Lean.Lib.Maps.PMap.set r v rs

def gi : Prop :=
  ∀ (A : Type) (i : reg) (x : A), get i (init x) = x

def gss : Prop :=
  ∀ (A : Type) (i : reg) (x : A) (m : t A),
    get i (set i x m) = x

def gso : Prop :=
  ∀ (A : Type) (i j : reg) (x : A) (m : t A),
    i ≠ j → get i (set j x m) = get i m

def gsspec : Prop :=
  ∀ (A : Type) (i j : reg) (x : A) (m : t A),
    get i (set j x m) =
      match CompCert4Lean.Lib.Coqlib.peq i j with
      | .left _ => x
      | .right _ => get i m

def gsident : Prop :=
  ∀ (A : Type) (i j : reg) (m : t A),
    get j (set i (get i m) m) = get j m

def map {A B : Type} (f : A → B) (m : t A) : t B :=
  (f m.1, CompCert4Lean.Lib.Maps.PTree.map1 f m.2)

def gmap : Prop :=
  ∀ (A B : Type) (f : A → B) (i : reg) (m : t A),
    get i (map f m) = f (get i m)

def set2 : Prop :=
  ∀ (A : Type) (i : elt) (x y : A) (m : t A),
    set i y (set i x m) = set i y m

end Regmap

namespace Regset

/-! Specialized generated application: FSetAVL.Make(OrderedPositive). -/

open CompCert4Lean.Lib.FSetAVLplus
open CompCert4Lean.Lib.Ordered

private abbrev OrderedType :=
  CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.OrderedType

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

/- Consumer-facing element-module type; EOrder is the canonical OrderedType value. -/
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
/- The generated facts record lives one universe above the legacy module alias;
   retain its exact provider alongside a universe-0 carrier for consumers. -/
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
abbrev Regset : Type := t

abbrev In : elt → t → Prop := Make.In (X := EOrder)
abbrev Equal : t → t → Prop := Make.Equal (X := EOrder)
abbrev Subset : t → t → Prop := Make.Subset (X := EOrder)
abbrev Empty : t → Prop := Make.Empty (X := EOrder)
abbrev For_all : (elt → Prop) → t → Prop := Make.For_all (X := EOrder)
abbrev Exists : (elt → Prop) → t → Prop := Make.Exists (X := EOrder)

abbrev empty : t := Make.empty (X := EOrder)
abbrev is_empty : t → Bool := Make.is_empty (X := EOrder)
abbrev mem : elt → t → Bool := Make.mem (X := EOrder)
abbrev add : elt → t → t := Make.add (X := EOrder)
abbrev singleton : elt → t := Make.singleton (X := EOrder)
abbrev remove : elt → t → t := Make.remove (X := EOrder)
abbrev union : t → t → t := Make.union (X := EOrder)
abbrev inter : t → t → t := Make.inter (X := EOrder)
abbrev diff : t → t → t := Make.diff (X := EOrder)
abbrev eq : t → t → Prop := Make.eq (X := EOrder)
abbrev eq_dec := Make.eq_dec (X := EOrder)
abbrev equal : t → t → Bool := Make.equal (X := EOrder)
abbrev subset : t → t → Bool := Make.subset (X := EOrder)
abbrev fold {A : Type} (f : elt → A → A) (s : t) (i : A) : A :=
  Make.fold (X := EOrder) f s i
abbrev for_all : (elt → Bool) → t → Bool := Make.for_all (X := EOrder)
abbrev exists_ : (elt → Bool) → t → Bool := Make.exists_ (X := EOrder)
abbrev filter : (elt → Bool) → t → t := Make.filter (X := EOrder)
abbrev partition : (elt → Bool) → t → t × t := Make.partition (X := EOrder)
abbrev cardinal : t → Nat := Make.cardinal (X := EOrder)
abbrev elements : t → List elt := Make.elements (X := EOrder)
abbrev choose : t → Option elt := Make.choose (X := EOrder)
abbrev lt : t → t → Prop := Make.lt (X := EOrder)
abbrev min_elt : t → Option elt := Make.min_elt (X := EOrder)
abbrev max_elt : t → Option elt := Make.max_elt (X := EOrder)

private abbrev CompatBool (f : elt → Bool) : Prop :=
  CompCert4Lean.Lib.FSetInterface.compat_bool EOrder.eq f

def In_1 : Prop :=
  ∀ (s : t) (x y : elt), EOrder.eq x y → In x s → In y s

def eq_refl : Prop :=
  ∀ s : t, eq s s

def eq_sym : Prop :=
  ∀ s s' : t, eq s s' → eq s' s

def eq_trans : Prop :=
  ∀ s s' s'' : t, eq s s' → eq s' s'' → eq s s''

def mem_1 : Prop :=
  ∀ (s : t) (x : elt), In x s → mem x s = true

def mem_2 : Prop :=
  ∀ (s : t) (x : elt), mem x s = true → In x s

def equal_1 : Prop :=
  ∀ s s' : t, Equal s s' → equal s s' = true

def equal_2 : Prop :=
  ∀ s s' : t, equal s s' = true → Equal s s'

def subset_1 : Prop :=
  ∀ s s' : t, Subset s s' → subset s s' = true

def subset_2 : Prop :=
  ∀ s s' : t, subset s s' = true → Subset s s'

def empty_1 : Prop :=
  Empty empty

def is_empty_1 : Prop :=
  ∀ s : t, Empty s → is_empty s = true

def is_empty_2 : Prop :=
  ∀ s : t, is_empty s = true → Empty s

def add_1 : Prop :=
  ∀ (s : t) (x y : elt), EOrder.eq x y → In y (add x s)

def add_2 : Prop :=
  ∀ (s : t) (x y : elt), In y s → In y (add x s)

def add_3 : Prop :=
  ∀ (s : t) (x y : elt), ¬ EOrder.eq x y → In y (add x s) → In y s

def remove_1 : Prop :=
  ∀ (s : t) (x y : elt), EOrder.eq x y → ¬ In y (remove x s)

def remove_2 : Prop :=
  ∀ (s : t) (x y : elt), ¬ EOrder.eq x y → In y s → In y (remove x s)

def remove_3 : Prop :=
  ∀ (s : t) (x y : elt), In y (remove x s) → In y s

def union_1 : Prop :=
  ∀ (s s' : t) (x : elt), In x (union s s') → In x s ∨ In x s'

def union_2 : Prop :=
  ∀ (s s' : t) (x : elt), In x s → In x (union s s')

def union_3 : Prop :=
  ∀ (s s' : t) (x : elt), In x s' → In x (union s s')

def inter_1 : Prop :=
  ∀ (s s' : t) (x : elt), In x (inter s s') → In x s

def inter_2 : Prop :=
  ∀ (s s' : t) (x : elt), In x (inter s s') → In x s'

def inter_3 : Prop :=
  ∀ (s s' : t) (x : elt), In x s → In x s' → In x (inter s s')

def diff_1 : Prop :=
  ∀ (s s' : t) (x : elt), In x (diff s s') → In x s

def diff_2 : Prop :=
  ∀ (s s' : t) (x : elt), In x (diff s s') → ¬ In x s'

def diff_3 : Prop :=
  ∀ (s s' : t) (x : elt), In x s → ¬ In x s' → In x (diff s s')

def singleton_1 : Prop :=
  ∀ x y : elt, In y (singleton x) → EOrder.eq x y

def singleton_2 : Prop :=
  ∀ x y : elt, EOrder.eq x y → In y (singleton x)

def fold_1 : Prop :=
  ∀ (s : t) (A : Type) (i : A) (f : elt → A → A),
    fold f s i = List.foldl (fun a e => f e a) i (elements s)

def cardinal_1 : Prop :=
  ∀ s : t, cardinal s = (elements s).length

def filter_1 : Prop :=
  ∀ (s : t) (x : elt) (f : elt → Bool),
    CompatBool f → In x (filter f s) → In x s

def filter_2 : Prop :=
  ∀ (s : t) (x : elt) (f : elt → Bool),
    CompatBool f → In x (filter f s) → f x = true

def filter_3 : Prop :=
  ∀ (s : t) (x : elt) (f : elt → Bool),
    CompatBool f → In x s → f x = true → In x (filter f s)

def for_all_1 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool f → For_all (fun x => f x = true) s → for_all f s = true

def for_all_2 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool f → for_all f s = true →
      For_all (fun x => f x = true) s

def exists_1 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool f → Exists (fun x => f x = true) s → exists_ f s = true

def exists_2 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool f → exists_ f s = true →
      Exists (fun x => f x = true) s

def partition_1 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool f → Equal (partition f s).1 (filter f s)

def partition_2 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool f →
      Equal (partition f s).2 (filter (fun x => !(f x)) s)

def choose_1 : Prop :=
  ∀ (s : t) (x : elt), choose s = some x → In x s

def choose_2 : Prop :=
  ∀ (s : t), choose s = none → Empty s

def elements_1 : Prop :=
  ∀ (s : t) (x : elt), In x s →
    CompCert4Lean.Lib.FSetInterface.InA EOrder.eq x (elements s)

def elements_2 : Prop :=
  ∀ (s : t) (x : elt),
    CompCert4Lean.Lib.FSetInterface.InA EOrder.eq x (elements s) → In x s

def elements_3w : Prop :=
  ∀ s : t, CompCert4Lean.Lib.FSetInterface.NoDupA EOrder.eq (elements s)

def min_elt_1 : Prop :=
  ∀ (s : t) (x : elt), min_elt s = some x → In x s

def min_elt_2 : Prop :=
  ∀ (s : t) (x y : elt), min_elt s = some x → In y s → ¬ EOrder.lt y x

def min_elt_3 : Prop :=
  ∀ (s : t), min_elt s = none → Empty s

def max_elt_1 : Prop :=
  ∀ (s : t) (x : elt), max_elt s = some x → In x s

def max_elt_2 : Prop :=
  ∀ (s : t) (x y : elt), max_elt s = some x → In y s → ¬ EOrder.lt x y

def max_elt_3 : Prop :=
  ∀ (s : t), max_elt s = none → Empty s

def elements_3 : Prop :=
  ∀ s : t, CompCert4Lean.Lib.FSetInterface.sort EOrder.lt (elements s)

def choose_3 : Prop :=
  ∀ (s s' : t) (x y : elt),
    choose s = some x → choose s' = some y → Equal s s' → EOrder.eq x y

def lt_trans : Prop :=
  ∀ s s' s'' : t, lt s s' → lt s' s'' → lt s s''

def lt_not_eq : Prop :=
  ∀ s s' : t, lt s s' → ¬ eq s s'

/- The generated comparison member is retained as its exact type descriptor. -/
def compare : Type :=
  ∀ s s' : t, CompCert4Lean.Lib.FSetInterface.Compare lt eq s s'

end Regset

/-! ## Canonical source-shaped facts for `FSetFacts.Facts(Regset)`

The Coq backend instantiates `FSetFacts.Facts` for both `Labelset` and
`Nodeset`.  This provider is shared by those consumers: executable members
remain owned by `Regset`, while every fact below is the exact proposition or
type descriptor supplied by the source functor.  Morphism declarations are
written in their expanded form, and the otherwise-empty Coq relation record is
kept distinct from the preorder record.
-/

namespace RegsetFacts

abbrev RegsetFacts := Regset.MFType

def eqb (x y : Regset.elt) : Bool :=
  match Regset.E.eq_dec x y with
  | .left _ => true
  | .right _ => false

def existsb (f : Regset.elt → Bool) (s : List Regset.elt) : Bool :=
  s.any f

def forallb (f : Regset.elt → Bool) (s : List Regset.elt) : Bool :=
  s.all f

def CompatBool (f : Regset.elt → Bool) : Prop :=
  ∀ x y, x = y → f x = f y

structure PreOrder {α : Type} (r : α → α → Prop) : Prop where
  reflexive : ∀ s, r s s
  transitive : ∀ s s' s'', r s s' → r s' s'' → r s s''

structure RewriteRelation {α : Type} (r : α → α → Prop) : Prop where

def E_ST : Prop := Equivalence (fun x y : Regset.elt => x = y)

def Equal_ST : Prop := Equivalence Regset.Equal

def In_eq_iff : Prop :=
  ∀ s x y, x = y → (Regset.In x s ↔ Regset.In y s)

def mem_iff : Prop :=
  ∀ s x, Regset.In x s ↔ Regset.mem x s = true

def not_mem_iff : Prop :=
  ∀ s x, ¬ Regset.In x s ↔ Regset.mem x s = false

def equal_iff : Prop :=
  ∀ s s', Regset.Equal s s' ↔ Regset.equal s s' = true

def subset_iff : Prop :=
  ∀ s s', Regset.Subset s s' ↔ Regset.subset s s' = true

def empty_iff : Prop :=
  ∀ x, Regset.In x Regset.empty ↔ False

def is_empty_iff : Prop :=
  ∀ s, Regset.Empty s ↔ Regset.is_empty s = true

def singleton_iff : Prop :=
  ∀ x y, Regset.In y (Regset.singleton x) ↔ x = y

def add_iff : Prop :=
  ∀ s x y, Regset.In y (Regset.add x s) ↔ x = y ∨ Regset.In y s

def add_neq_iff : Prop :=
  ∀ s x y, x ≠ y →
    (Regset.In y (Regset.add x s) ↔ Regset.In y s)

def remove_iff : Prop :=
  ∀ s x y, Regset.In y (Regset.remove x s) ↔
    Regset.In y s ∧ ¬ x = y

def remove_neq_iff : Prop :=
  ∀ s x y, x ≠ y →
    (Regset.In y (Regset.remove x s) ↔ Regset.In y s)

def union_iff : Prop :=
  ∀ s s' x, Regset.In x (Regset.union s s') ↔
    Regset.In x s ∨ Regset.In x s'

def inter_iff : Prop :=
  ∀ s s' x, Regset.In x (Regset.inter s s') ↔
    Regset.In x s ∧ Regset.In x s'

def diff_iff : Prop :=
  ∀ s s' x, Regset.In x (Regset.diff s s') ↔
    Regset.In x s ∧ ¬ Regset.In x s'

def filter_iff : Prop :=
  ∀ s x f, CompatBool f →
    (Regset.In x (Regset.filter f s) ↔
      Regset.In x s ∧ f x = true)

def for_all_iff : Prop :=
  ∀ s f, CompatBool f →
    (Regset.For_all (fun x => f x = true) s ↔
      Regset.for_all f s = true)

def exists_iff : Prop :=
  ∀ s f, CompatBool f →
    (Regset.Exists (fun x => f x = true) s ↔
      Regset.exists_ f s = true)

def elements_iff : Prop :=
  ∀ s x, Regset.In x s ↔
    CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA
      (fun x y : Regset.elt => x = y) x (Regset.elements s)

def mem_b : Prop :=
  ∀ s x y, x = y → Regset.mem x s = Regset.mem y s

def empty_b : Prop :=
  ∀ y, Regset.mem y Regset.empty = false

def add_b : Prop :=
  ∀ s x y, Regset.mem y (Regset.add x s) =
    (eqb x y || Regset.mem y s)

def add_neq_b : Prop :=
  ∀ s x y, x ≠ y → Regset.mem y (Regset.add x s) = Regset.mem y s

def remove_b : Prop :=
  ∀ s x y, Regset.mem y (Regset.remove x s) =
    (Regset.mem y s && !(eqb x y))

def remove_neq_b : Prop :=
  ∀ s x y, x ≠ y → Regset.mem y (Regset.remove x s) = Regset.mem y s

def singleton_b : Prop :=
  ∀ x y, Regset.mem y (Regset.singleton x) = eqb x y

def union_b : Prop :=
  ∀ s s' x, Regset.mem x (Regset.union s s') =
    (Regset.mem x s || Regset.mem x s')

def inter_b : Prop :=
  ∀ s s' x, Regset.mem x (Regset.inter s s') =
    (Regset.mem x s && Regset.mem x s')

def diff_b : Prop :=
  ∀ s s' x, Regset.mem x (Regset.diff s s') =
    (Regset.mem x s && !(Regset.mem x s'))

def elements_b : Prop :=
  ∀ s x, Regset.mem x s = existsb (eqb x) (Regset.elements s)

def filter_b : Prop :=
  ∀ s x f, CompatBool f →
    Regset.mem x (Regset.filter f s) = Regset.mem x s && f x

def for_all_b : Prop :=
  ∀ s f, CompatBool f →
    Regset.for_all f s = forallb f (Regset.elements s)

def exists_b : Prop :=
  ∀ s f, CompatBool f →
    Regset.exists_ f s = existsb f (Regset.elements s)

def In_m : Prop :=
  ∀ x y, x = y → ∀ s s', Regset.Equal s s' →
    (Regset.In x s → Regset.In y s') ∧
    (Regset.In y s' → Regset.In x s)

def In_s_m : Prop :=
  ∀ x y, x = y → ∀ s s', Regset.Subset s s' →
    (Regset.In x s → Regset.In y s')

def Empty_m : Prop :=
  ∀ s s', Regset.Equal s s' →
    (Regset.Empty s → Regset.Empty s') ∧
    (Regset.Empty s' → Regset.Empty s)

def Empty_s_m : Prop :=
  ∀ s s', Regset.Subset s' s →
    (Regset.Empty s → Regset.Empty s')

def Empty_s_m_Proper : Prop :=
  ∀ s s', Regset.Subset s' s →
    Regset.Empty s → Regset.Empty s'

def Subset_m : Prop :=
  ∀ s s', Regset.Equal s s' → ∀ s'' s''', Regset.Equal s'' s''' →
    (Regset.Subset s s'' → Regset.Subset s' s''') ∧
    (Regset.Subset s' s''' → Regset.Subset s s'')

def Subset_refl : Prop :=
  ∀ s, Regset.Subset s s

def Subset_trans : Prop :=
  ∀ s s' s'', Regset.Subset s s' → Regset.Subset s' s'' →
    Regset.Subset s s''

def SubsetSetoid : Prop := PreOrder Regset.Subset

def SubsetSetoid_Reflexive : Prop :=
  ∀ s, Regset.Subset s s

def SubsetSetoid_Transitive : Prop :=
  ∀ s s' s'', Regset.Subset s s' → Regset.Subset s' s'' →
    Regset.Subset s s''

def SubsetSetoid_relation : Prop := RewriteRelation Regset.Subset

def add_m : Prop :=
  ∀ x y, x = y → ∀ s s', Regset.Equal s s' → ∀ a,
    (Regset.In a (Regset.add x s) → Regset.In a (Regset.add y s')) ∧
    (Regset.In a (Regset.add y s') → Regset.In a (Regset.add x s))

def add_s_m : Prop :=
  ∀ x y, x = y → ∀ s s', Regset.Subset s s' →
    Regset.Subset (Regset.add x s) (Regset.add y s')

def add_s_m_Proper : Prop :=
  ∀ x y, x = y → ∀ s s', Regset.Subset s s' →
    Regset.Subset (Regset.add x s) (Regset.add y s')

def remove_m : Prop :=
  ∀ x y, x = y → ∀ s s', Regset.Equal s s' → ∀ a,
    (Regset.In a (Regset.remove x s) → Regset.In a (Regset.remove y s')) ∧
    (Regset.In a (Regset.remove y s') → Regset.In a (Regset.remove x s))

def remove_s_m : Prop :=
  ∀ x y, x = y → ∀ s s', Regset.Subset s s' →
    Regset.Subset (Regset.remove x s) (Regset.remove y s')

def remove_s_m_Proper : Prop :=
  ∀ x y, x = y → ∀ s s', Regset.Subset s s' →
    Regset.Subset (Regset.remove x s) (Regset.remove y s')

def union_m : Prop :=
  ∀ s s', Regset.Equal s s' → ∀ s'' s''', Regset.Equal s'' s''' → ∀ a,
    (Regset.In a (Regset.union s s'') →
      Regset.In a (Regset.union s' s''')) ∧
    (Regset.In a (Regset.union s' s''') →
      Regset.In a (Regset.union s s''))

def union_s_m : Prop :=
  ∀ s s', Regset.Subset s s' → ∀ s'' s''', Regset.Subset s'' s''' →
    Regset.Subset (Regset.union s s'') (Regset.union s' s''')

def union_s_m_Proper : Prop :=
  ∀ s s', Regset.Subset s s' → ∀ s'' s''', Regset.Subset s'' s''' →
    Regset.Subset (Regset.union s s'') (Regset.union s' s''')

def inter_m : Prop :=
  ∀ s s', Regset.Equal s s' → ∀ s'' s''', Regset.Equal s'' s''' → ∀ a,
    (Regset.In a (Regset.inter s s'') →
      Regset.In a (Regset.inter s' s''')) ∧
    (Regset.In a (Regset.inter s' s''') →
      Regset.In a (Regset.inter s s''))

def inter_s_m : Prop :=
  ∀ s s', Regset.Subset s s' → ∀ s'' s''', Regset.Subset s'' s''' →
    Regset.Subset (Regset.inter s s'') (Regset.inter s' s''')

def inter_s_m_Proper : Prop :=
  ∀ s s', Regset.Subset s s' → ∀ s'' s''', Regset.Subset s'' s''' →
    Regset.Subset (Regset.inter s s'') (Regset.inter s' s''')

def diff_m : Prop :=
  ∀ s s', Regset.Equal s s' → ∀ s'' s''', Regset.Equal s'' s''' → ∀ a,
    (Regset.In a (Regset.diff s s'') →
      Regset.In a (Regset.diff s' s''')) ∧
    (Regset.In a (Regset.diff s' s''') →
      Regset.In a (Regset.diff s s''))

def diff_s_m : Prop :=
  ∀ s s', Regset.Subset s s' → ∀ s'' s''', Regset.Subset s''' s'' →
    Regset.Subset (Regset.diff s s'') (Regset.diff s' s''')

def diff_s_m_Proper : Prop :=
  ∀ s s', Regset.Subset s s' → ∀ s'' s''', Regset.Subset s''' s'' →
    Regset.Subset (Regset.diff s s'') (Regset.diff s' s''')

def singleton_m : Prop :=
  ∀ x y, x = y → ∀ a,
    (Regset.In a (Regset.singleton x) → Regset.In a (Regset.singleton y)) ∧
    (Regset.In a (Regset.singleton y) → Regset.In a (Regset.singleton x))

def is_empty_m : Prop :=
  ∀ s s', Regset.Equal s s' → Regset.is_empty s = Regset.is_empty s'

def mem_m : Prop :=
  ∀ x y, x = y → ∀ s s', Regset.Equal s s' →
    Regset.mem x s = Regset.mem y s'

def equal_m : Prop :=
  ∀ s s', Regset.Equal s s' → ∀ s'' s''', Regset.Equal s'' s''' →
    Regset.equal s s'' = Regset.equal s' s'''

def subset_m : Prop :=
  ∀ s s', Regset.Equal s s' → ∀ s'' s''', Regset.Equal s'' s''' →
    Regset.subset s s'' = Regset.subset s' s'''

def filter_equal : Prop :=
  ∀ f, CompatBool f → ∀ s s', Regset.Equal s s' →
    Regset.Equal (Regset.filter f s) (Regset.filter f s')

def filter_ext : Prop :=
  ∀ f f', CompatBool f → (∀ x, f x = f' x) → ∀ s s',
    Regset.Equal s s' →
    Regset.Equal (Regset.filter f s) (Regset.filter f' s')

def filter_subset : Prop :=
  ∀ f, CompatBool f → ∀ s s', Regset.Subset s s' →
    Regset.Subset (Regset.filter f s) (Regset.filter f s')

end RegsetFacts

def regmap_optget {A : Type}
    (or : Option reg) (dfl : A) (rs : Regmap.t A) : A :=
  match or with
  | none => dfl
  | some r => Regmap.get r rs

def regmap_setres {A : Type}
    (res : builtin_res reg) (v : A) (rs : Regmap.t A) : Regmap.t A :=
  match res with
  | .BR r => Regmap.set r v rs
  | _ => rs

def regs_lessdef (rs1 rs2 : Regmap.t val) : Prop :=
  ∀ r, Val.lessdef (Regmap.get r rs1) (Regmap.get r rs2)

def regs_lessdef_regsStatement : Prop :=
  ∀ (rs1 rs2 : Regmap.t val), regs_lessdef rs1 rs2 →
    ∀ rl : List reg,
      Val.lessdef_list
        (List.map (fun r => Regmap.get r rs1) rl)
        (List.map (fun r => Regmap.get r rs2) rl)

def set_reg_lessdefStatement : Prop :=
  ∀ (r : reg) (v1 v2 : val) (rs1 rs2 : Regmap.t val),
    Val.lessdef v1 v2 → regs_lessdef rs1 rs2 →
      regs_lessdef (Regmap.set r v1 rs1) (Regmap.set r v2 rs2)

def set_res_lessdefStatement : Prop :=
  ∀ (res : builtin_res reg) (v1 v2 : val) (rs1 rs2 : Regmap.t val),
    Val.lessdef v1 v2 → regs_lessdef rs1 rs2 →
      regs_lessdef
        (regmap_setres res v1 rs1)
        (regmap_setres res v2 rs2)

end CompCert4Lean.Backend.Registers

namespace CompCert4Lean.Backend.Registers

namespace Regmap

theorem gi_proof : gi := by
  intro A i x
  rfl

theorem gss_proof : gss := by
  intro A i x m
  rcases m with ⟨d, m⟩
  change CompCert4Lean.Lib.Maps.PTree.tree A at m
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive at i
  change (match CompCert4Lean.Lib.Maps.PTree.get i
      (CompCert4Lean.Lib.Maps.PTree.set i x m) with
    | some y => y
    | none => d) = x
  rw [CompCert4Lean.Lib.Maps.PTree.getSet_equation]
  simp

theorem gso_proof : gso := by
  intro A i j x m hij
  rcases m with ⟨d, m⟩
  change CompCert4Lean.Lib.Maps.PTree.tree A at m
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive at i
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive at j
  change (match CompCert4Lean.Lib.Maps.PTree.get i
      (CompCert4Lean.Lib.Maps.PTree.set j x m) with
    | some y => y
    | none => d) =
    match CompCert4Lean.Lib.Maps.PTree.get i m with
    | some y => y
    | none => d
  rw [CompCert4Lean.Lib.Maps.PTree.getSet_equation]
  by_cases heq : i = j
  · exact False.elim (hij heq)
  · simp [heq]

theorem gsspec_proof : gsspec := by
  intro A i j x m
  rcases m with ⟨d, m⟩
  change CompCert4Lean.Lib.Maps.PTree.tree A at m
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive at i
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive at j
  change (match CompCert4Lean.Lib.Maps.PTree.get i
      (CompCert4Lean.Lib.Maps.PTree.set j x m) with
    | some y => y
    | none => d) =
    match CompCert4Lean.Lib.Coqlib.peq i j with
    | .left _ => x
    | .right _ =>
      match CompCert4Lean.Lib.Maps.PTree.get i m with
      | some y => y
      | none => d
  rw [CompCert4Lean.Lib.Maps.PTree.getSet_equation]
  cases CompCert4Lean.Lib.Coqlib.peq i j with
  | left hij =>
      subst j
      simp
  | right hij =>
      simp [hij]

end Regmap

end CompCert4Lean.Backend.Registers
