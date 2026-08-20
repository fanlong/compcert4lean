import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Ordered

/-!
# Generic finite-set interfaces

This module is the definition-level translation of the non-dependent finite
set signatures from Rocq's `FSets/FSetInterface.v`.  The records are generic
in their element provider and retain both the executable operations and the
logical relations/specifications consumed by the generated facts, decision,
and properties functors.
-/

namespace CompCert4Lean.Lib.FSetInterface

abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
abbrev Compare {X : Type} (lt eq : X → X → Prop) (x y : X) : Type :=
  CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.Compare lt eq x y
abbrev InA {A : Type} (eqA : A → A → Prop) (x : A) (l : List A) : Prop :=
  CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA eqA x l
abbrev NoDupA {A : Type} (eqA : A → A → Prop) (l : List A) : Prop :=
  CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.NoDupA eqA l
abbrev sort {A : Type} (lt : A → A → Prop) (l : List A) : Prop :=
  CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Sorted.Sorted lt l

/-- Source-shaped decidable equality provider. -/
structure DecidableType where
  t : Type
  eq : t → t → Prop
  eq_refl : ∀ x : t, eq x x
  eq_sym : ∀ x y : t, eq x y → eq y x
  eq_trans : ∀ x y z : t, eq x y → eq y z → eq x z
  eq_dec : ∀ x y : t, Sumbool (eq x y) (¬ eq x y)

abbrev OrderedType :=
  CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.OrderedType

namespace OrderedType

def toDecidableType (E : OrderedType) : DecidableType where
  t := E.t
  eq := E.eq
  eq_refl := E.eq_refl
  eq_sym := E.eq_sym
  eq_trans := E.eq_trans
  eq_dec := E.eq_dec

end OrderedType

def compat_bool {A : Type} (eqA : A → A → Prop) (f : A → Bool) : Prop :=
  ∀ x y, eqA x y → f x = f y

def compat_op {A B : Type} (eqA : A → A → Prop)
    (eqB : B → B → Prop) (f : A → B → B) : Prop :=
  ∀ x y, eqA x y → ∀ a b, eqB a b → eqB (f x a) (f y b)

def transpose {A B : Type} (eqB : B → B → Prop)
    (f : A → B → B) : Prop :=
  ∀ x y a, eqB (f x (f y a)) (f y (f x a))

def EqualOf {A S : Type} (In : A → S → Prop) (s s' : S) : Prop :=
  ∀ a, In a s ↔ In a s'

def SubsetOf {A S : Type} (In : A → S → Prop) (s s' : S) : Prop :=
  ∀ a, In a s → In a s'

def EmptyOf {A S : Type} (In : A → S → Prop) (s : S) : Prop :=
  ∀ a, ¬ In a s

def ForAllOf {A S : Type} (In : A → S → Prop)
    (P : A → Prop) (s : S) : Prop :=
  ∀ x, In x s → P x

def ExistsOf {A S : Type} (In : A → S → Prop)
    (P : A → Prop) (s : S) : Prop :=
  ∃ x, In x s ∧ P x

/-- Functorial weak-set signature (`WSfun`). -/
structure WSfun (E : DecidableType) where
  t : Type
  In : E.t → t → Prop
  empty : t
  is_empty : t → Bool
  mem : E.t → t → Bool
  add : E.t → t → t
  singleton : E.t → t
  remove : E.t → t → t
  union : t → t → t
  inter : t → t → t
  diff : t → t → t
  eq_dec : ∀ s s', Sumbool (EqualOf In s s') (¬ EqualOf In s s')
  equal : t → t → Bool
  subset : t → t → Bool
  fold : ∀ {A : Type _}, (E.t → A → A) → t → A → A
  for_all : (E.t → Bool) → t → Bool
  exists_ : (E.t → Bool) → t → Bool
  filter : (E.t → Bool) → t → t
  partition : (E.t → Bool) → t → t × t
  cardinal : t → Nat
  elements : t → List E.t
  choose : t → Option E.t
  In_1 : ∀ s x y, E.eq x y → In x s → In y s
  eq_refl : ∀ s, EqualOf In s s
  eq_sym : ∀ s s', EqualOf In s s' → EqualOf In s' s
  eq_trans : ∀ s s' s'',
    EqualOf In s s' → EqualOf In s' s'' → EqualOf In s s''
  mem_1 : ∀ s x, In x s → mem x s = true
  mem_2 : ∀ s x, mem x s = true → In x s
  equal_1 : ∀ s s', EqualOf In s s' → equal s s' = true
  equal_2 : ∀ s s', equal s s' = true → EqualOf In s s'
  subset_1 : ∀ s s', SubsetOf In s s' → subset s s' = true
  subset_2 : ∀ s s', subset s s' = true → SubsetOf In s s'
  empty_1 : EmptyOf In empty
  is_empty_1 : ∀ s, EmptyOf In s → is_empty s = true
  is_empty_2 : ∀ s, is_empty s = true → EmptyOf In s
  add_1 : ∀ s x y, E.eq x y → In y (add x s)
  add_2 : ∀ s x y, In y s → In y (add x s)
  add_3 : ∀ s x y, ¬ E.eq x y → In y (add x s) → In y s
  remove_1 : ∀ s x y, E.eq x y → ¬ In y (remove x s)
  remove_2 : ∀ s x y, ¬ E.eq x y → In y s → In y (remove x s)
  remove_3 : ∀ s x y, In y (remove x s) → In y s
  singleton_1 : ∀ x y, In y (singleton x) → E.eq x y
  singleton_2 : ∀ x y, E.eq x y → In y (singleton x)
  union_1 : ∀ s s' x, In x (union s s') → In x s ∨ In x s'
  union_2 : ∀ s s' x, In x s → In x (union s s')
  union_3 : ∀ s s' x, In x s' → In x (union s s')
  inter_1 : ∀ s s' x, In x (inter s s') → In x s
  inter_2 : ∀ s s' x, In x (inter s s') → In x s'
  inter_3 : ∀ s s' x, In x s → In x s' → In x (inter s s')
  diff_1 : ∀ s s' x, In x (diff s s') → In x s
  diff_2 : ∀ s s' x, In x (diff s s') → ¬ In x s'
  diff_3 : ∀ s s' x, In x s → ¬ In x s' → In x (diff s s')
  fold_1 : ∀ s (A : Type) (i : A) (f : E.t → A → A),
    fold f s i = List.foldl (fun a e => f e a) i (elements s)
  cardinal_1 : ∀ s, cardinal s = (elements s).length
  filter_1 : ∀ s x f, compat_bool E.eq f → In x (filter f s) → In x s
  filter_2 : ∀ s x f, compat_bool E.eq f → In x (filter f s) → f x = true
  filter_3 : ∀ s x f,
    compat_bool E.eq f → In x s → f x = true → In x (filter f s)
  for_all_1 : ∀ s f, compat_bool E.eq f →
    ForAllOf In (fun x => f x = true) s → for_all f s = true
  for_all_2 : ∀ s f, compat_bool E.eq f →
    for_all f s = true → ForAllOf In (fun x => f x = true) s
  exists_1 : ∀ s f, compat_bool E.eq f →
    ExistsOf In (fun x => f x = true) s → exists_ f s = true
  exists_2 : ∀ s f, compat_bool E.eq f →
    exists_ f s = true → ExistsOf In (fun x => f x = true) s
  partition_1 : ∀ s f, compat_bool E.eq f →
    EqualOf In (partition f s).1 (filter f s)
  partition_2 : ∀ s f, compat_bool E.eq f →
    EqualOf In (partition f s).2 (filter (fun x => !(f x)) s)
  elements_1 : ∀ s x, In x s → InA E.eq x (elements s)
  elements_2 : ∀ s x, InA E.eq x (elements s) → In x s
  elements_3w : ∀ s, NoDupA E.eq (elements s)
  choose_1 : ∀ s x, choose s = some x → In x s
  choose_2 : ∀ s, choose s = none → EmptyOf In s

namespace WSfun

abbrev elt {E : DecidableType} (_M : WSfun E) : Type := E.t
def Equal {E : DecidableType} (M : WSfun E) : M.t → M.t → Prop := EqualOf M.In
def Subset {E : DecidableType} (M : WSfun E) : M.t → M.t → Prop := SubsetOf M.In
def Empty {E : DecidableType} (M : WSfun E) : M.t → Prop := EmptyOf M.In
def For_all {E : DecidableType} (M : WSfun E) : (E.t → Prop) → M.t → Prop :=
  ForAllOf M.In
def Exists {E : DecidableType} (M : WSfun E) : (E.t → Prop) → M.t → Prop :=
  ExistsOf M.In
def eq {E : DecidableType} (M : WSfun E) : M.t → M.t → Prop := M.Equal

end WSfun

/-- Self-contained weak-set signature (`WS`). -/
structure WS where
  E : DecidableType
  toWSfun : WSfun E

/-- Ordered functorial set signature (`Sfun`). -/
structure Sfun (E : OrderedType) : Type 1 extends WSfun E.toDecidableType where
  lt : toWSfun.t → toWSfun.t → Prop
  compare : ∀ s s', Compare lt toWSfun.Equal s s'
  min_elt : toWSfun.t → Option E.t
  max_elt : toWSfun.t → Option E.t
  lt_trans : ∀ s s' s'', lt s s' → lt s' s'' → lt s s''
  lt_not_eq : ∀ s s', lt s s' → ¬ toWSfun.Equal s s'
  elements_3 : ∀ s, sort E.lt (toWSfun.elements s)
  min_elt_1 : ∀ s x, min_elt s = some x → toWSfun.In x s
  min_elt_2 : ∀ s x y,
    min_elt s = some x → toWSfun.In y s → ¬ E.lt y x
  min_elt_3 : ∀ s, min_elt s = none → toWSfun.Empty s
  max_elt_1 : ∀ s x, max_elt s = some x → toWSfun.In x s
  max_elt_2 : ∀ s x y,
    max_elt s = some x → toWSfun.In y s → ¬ E.lt x y
  max_elt_3 : ∀ s, max_elt s = none → toWSfun.Empty s
  choose_3 : ∀ s s' x y,
    toWSfun.choose s = some x → toWSfun.choose s' = some y →
      toWSfun.Equal s s' → E.eq x y

/-- Self-contained ordered-set signature (`S`). -/
structure S where
  E : OrderedType
  toSfun : Sfun E

namespace WS

abbrev elt (M : WS) : Type := M.E.t
abbrev t (M : WS) : Type := M.toWSfun.t

end WS

namespace S

abbrev elt (M : S) : Type := M.E.t
abbrev t (M : S) : Type := M.toSfun.t
def toWS (M : S) : WS := ⟨M.E.toDecidableType, M.toSfun.toWSfun⟩

end S

end CompCert4Lean.Lib.FSetInterface
