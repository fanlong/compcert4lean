import CompCert4Lean.Lib.MSetAVL
import CompCert4Lean.Lib.FSetFacts
import CompCert4Lean.Lib.FSetDecide
import CompCert4Lean.Lib.FSetProperties

/-!
# AVL finite sets with interval operations

This is the source-shaped adapter for `lib/FSetAVLplus.v`. Its raw surface is
the canonical `MSetAVL` implementation, and its public set type encapsulates a
raw tree together with the binary-search-tree invariant, as `FSetAVL.Make`
does in Rocq.
-/

namespace CompCert4Lean.Lib.FSetAVLplus

open CompCert4Lean.Foundation.Logic.Support
open CompCert4Lean.Lib.FSetInterface

abbrev OrderedType :=
  CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.OrderedType

/-- Materialized Lean facade for the source functor-module identity. -/
def Make : Type := Unit

namespace Make

/-- Materialized Lean facade for the source `Module Raw := MSet.Raw` identity. -/
def Raw : Type := Unit

namespace Raw

export CompCert4Lean.Lib.MSetAVL
  (OrderedType tree t Leaf Node empty is_empty mem min_elt max_elt choose fold
   elements_aux elements rev_elements_aux rev_elements cardinal maxdepth mindepth
   for_all exists_ compare equal subset subsetl subsetr ltb_tree gtb_tree isok
   In InT IsRoot InLeft InRight Equal Subset Empty For_all Exists lt_tree
   gt_tree bst InA NoDupA Sorted RespectsEq enumeration End More cons
   compare_more compare_cont compare_end flatten_e eq lt CompSpec CompareSpec
   CompEq CompLt CompGt Cmp height singleton create assert_false bal add join
   remove_min merge remove concat triple split inter diff union filter partition
   singleton_spec create_spec create_bst singleton_bst bal_spec bal_bst add_spec
   add_bst join_spec join_bst remove_min_spec remove_min_bst_gt remove_min_bst
   remove_min_ok remove_min_gt_tree merge_spec merge_bst concat_spec concat_bst
   remove_spec remove_bst split_left_spec split_right_spec split_in_spec split_bst
   split_membership_spec union_spec union_bst inter_spec_bst inter_spec inter_bst
   diff_spec_bst diff_spec diff_bst filter_weak_spec filter_spec filter_bst
   partition_fst partition_snd partition_bst ltb_tree_iff gtb_tree_iff isok_iff
   In_1 In_node_iff In_leaf_iff lt_leaf gt_leaf lt_tree_node gt_tree_node
   lt_tree_not_in gt_tree_not_in lt_tree_trans gt_tree_trans empty_spec empty_ok
   is_empty_spec mem_spec min_elt_spec1 min_elt_spec2 min_elt_spec3 max_elt_spec1
   max_elt_spec2 max_elt_spec3 choose_spec1 choose_spec2 choose_spec3
   elements_spec1' elements_spec1 elements_spec2' elements_spec2 elements_spec2w
   elements_aux_cardinal elements_cardinal cardinal_spec elements_app
   elements_node rev_elements_app rev_elements_node rev_elements_rev
   sorted_app_inv elements_sort_ok for_all_spec exists_spec fold_spec' fold_spec
   subsetl_spec subsetr_spec subset_spec eq_Leq eq_equiv lt_strorder lt_compat
   flatten_e_elements cons_1 compare_end_Cmp compare_more_Cmp compare_cont_Cmp
   compare_Cmp compare_spec equal_spec mindepth_maxdepth maxdepth_cardinal
   mindepth_cardinal maxdepth_log_cardinal mindepth_log_cardinal)

abbrev IsOk {X : OrderedType} (s : tree X) : Prop :=
  CompCert4Lean.Lib.MSetAVL.IsOk s

/-- `MSetAVL` supplies the canonical tree and `bst` lemmas, but its Lean
provider does not yet expose Rocq's class-shaped invariant carrier. -/
class Ok {X : OrderedType} (s : tree X) : Prop where
  ok : bst s

theorem join_ok {X : OrderedType} (left : tree X) (x : X.t) (right : tree X)
    (hleft : Ok left) (hright : Ok right)
    (hlt : lt_tree x left) (hgt : gt_tree x right) :
    Ok (join left x right) :=
  ⟨join_bst left x right hleft.ok hright.ok hlt hgt⟩

theorem concat_ok {X : OrderedType} (left right : tree X)
    (hleft : Ok left) (hright : Ok right)
    (hbetween : ∀ x y, InT x left → InT y right → X.lt x y) :
    Ok (concat left right) :=
  ⟨concat_bst left right hleft.ok hright.ok hbetween⟩

end Raw

abbrev E (X : OrderedType) := X
abbrev «X'» (X : OrderedType) := X

structure MSet (X : OrderedType) where
  this : Raw.tree X
  is_ok : Raw.Ok this

namespace MSet

abbrev Mkt {X : OrderedType} (this : Raw.tree X) {is_ok : Raw.Ok this} :
    MSet X := ⟨this, is_ok⟩

end MSet

abbrev Set (X : OrderedType) := MSet X
abbrev t (X : OrderedType) := MSet X
abbrev elt (X : OrderedType) := X.t

variable {X : OrderedType}

def In (x : X.t) (s : t X) : Prop := Raw.InT x s.this
def Equal (s s' : t X) : Prop := ∀ x, In x s ↔ In x s'
def Subset (s s' : t X) : Prop := ∀ x, In x s → In x s'
def Empty (s : t X) : Prop := ∀ x, ¬ In x s
def For_all (P : X.t → Prop) (s : t X) : Prop := ∀ x, In x s → P x
def Exists (P : X.t → Prop) (s : t X) : Prop := ∃ x, In x s ∧ P x
def eq (s s' : t X) : Prop := Equal s s'
def lt (s s' : t X) : Prop := Raw.lt s.this s'.this

def empty : t X := ⟨Raw.empty, ⟨Raw.empty_ok⟩⟩
def is_empty (s : t X) : Bool := Raw.is_empty s.this
def mem (x : X.t) (s : t X) : Bool := Raw.mem x s.this
def add (x : X.t) (s : t X) : t X := ⟨Raw.add x s.this, ⟨Raw.add_bst s.is_ok.ok x⟩⟩
def singleton (x : X.t) : t X := ⟨Raw.singleton x, ⟨Raw.singleton_bst x⟩⟩
def remove (x : X.t) (s : t X) : t X :=
  ⟨Raw.remove x s.this, ⟨Raw.remove_bst s.is_ok.ok x⟩⟩
def union (s s' : t X) : t X :=
  ⟨Raw.union s.this s'.this, ⟨Raw.union_bst s.is_ok.ok s'.is_ok.ok⟩⟩
def inter (s s' : t X) : t X :=
  ⟨Raw.inter s.this s'.this, ⟨Raw.inter_bst s.is_ok.ok s'.is_ok.ok⟩⟩
def diff (s s' : t X) : t X :=
  ⟨Raw.diff s.this s'.this, ⟨Raw.diff_bst s.is_ok.ok s'.is_ok.ok⟩⟩
def equal (s s' : t X) : Bool := Raw.equal s.this s'.this
def subset (s s' : t X) : Bool := Raw.subset s.this s'.this
def fold {A : Type} (f : X.t → A → A) (s : t X) (base : A) : A :=
  Raw.fold f s.this base
def for_all (f : X.t → Bool) (s : t X) : Bool := Raw.for_all f s.this
def exists_ (f : X.t → Bool) (s : t X) : Bool := Raw.exists_ f s.this
def filter (f : X.t → Bool) (s : t X) : t X :=
  ⟨Raw.filter f s.this, ⟨Raw.filter_bst s.is_ok.ok f⟩⟩
def partition (f : X.t → Bool) (s : t X) : t X × t X :=
  let p := Raw.partition f s.this
  let hp := Raw.partition_bst s.is_ok.ok f
  (⟨p.1, ⟨hp.1⟩⟩, ⟨p.2, ⟨hp.2⟩⟩)
def cardinal (s : t X) : Nat := Raw.cardinal s.this
def elements (s : t X) : List X.t := Raw.elements s.this
def choose (s : t X) : Option X.t := Raw.choose s.this
def min_elt (s : t X) : Option X.t := Raw.min_elt s.this
def max_elt (s : t X) : Option X.t := Raw.max_elt s.this

def eq_dec (s s' : t X) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (eq s s') (¬ eq s s') :=
  match h : Raw.equal s.this s'.this with
  | true => .left ((Raw.equal_spec s.this s'.this s.is_ok.ok s'.is_ok.ok).mp h)
  | false => .right (fun heq => by
      have ht : Raw.equal s.this s'.this = true :=
        (Raw.equal_spec s.this s'.this s.is_ok.ok s'.is_ok.ok).mpr heq
      rw [h] at ht
      cases ht)

def compare (s s' : t X) :
    CompCert4Lean.Lib.FSetInterface.Compare lt eq s s' := by
  match hcmp : Raw.compare s.this s'.this with
  | .Eq =>
      have heq : eq s s' := by
        have hspec := Raw.compare_spec s.this s'.this s.is_ok.ok s'.is_ok.ok
        rw [hcmp] at hspec
        cases hspec with
        | CompEq h => exact h
      exact CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.Compare.EQ heq
  | .Lt =>
      have hlt : lt s s' := by
        have hspec := Raw.compare_spec s.this s'.this s.is_ok.ok s'.is_ok.ok
        rw [hcmp] at hspec
        cases hspec with
        | CompLt h => exact h
      exact CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.Compare.LT hlt
  | .Gt =>
      have hgt : lt s' s := by
        have hspec := Raw.compare_spec s.this s'.this s.is_ok.ok s'.is_ok.ok
        rw [hcmp] at hspec
        cases hspec with
        | CompGt h => exact h
      exact CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.Compare.GT hgt

theorem In_1 (s : t X) (x y : X.t) (hxy : X.eq x y) :
    In x s → In y s :=
  Raw.In_1 s.this x y hxy

theorem eq_refl (s : t X) : eq s s := fun _ => Iff.rfl

theorem eq_sym (s s' : t X) : eq s s' → eq s' s := by
  intro h x
  exact (h x).symm

theorem eq_trans (s s' s'' : t X) : eq s s' → eq s' s'' → eq s s'' := by
  intro h₁ h₂ x
  exact (h₁ x).trans (h₂ x)

theorem mem_1 (s : t X) (x : X.t) (h : In x s) : mem x s = true :=
  (Raw.mem_spec s.this x s.is_ok.ok).mpr h

theorem mem_2 (s : t X) (x : X.t) (h : mem x s = true) : In x s :=
  (Raw.mem_spec s.this x s.is_ok.ok).mp h

theorem equal_1 (s s' : t X) (h : Equal s s') : equal s s' = true :=
  (Raw.equal_spec s.this s'.this s.is_ok.ok s'.is_ok.ok).mpr h

theorem equal_2 (s s' : t X) (h : equal s s' = true) : Equal s s' :=
  (Raw.equal_spec s.this s'.this s.is_ok.ok s'.is_ok.ok).mp h

theorem subset_1 (s s' : t X) (h : Subset s s') : subset s s' = true :=
  (Raw.subset_spec s.this s'.this s.is_ok.ok s'.is_ok.ok).mpr h

theorem subset_2 (s s' : t X) (h : subset s s' = true) : Subset s s' :=
  (Raw.subset_spec s.this s'.this s.is_ok.ok s'.is_ok.ok).mp h

theorem empty_1 : Empty (empty : t X) := Raw.empty_spec

theorem is_empty_1 (s : t X) (h : Empty s) : is_empty s = true :=
  (Raw.is_empty_spec s.this).mpr h

theorem is_empty_2 (s : t X) (h : is_empty s = true) : Empty s :=
  (Raw.is_empty_spec s.this).mp h

theorem add_1 (s : t X) (x y : X.t) (hxy : X.eq x y) : In y (add x s) :=
  (Raw.add_spec s.this x y).mpr (Or.inl (X.eq_sym x y hxy))

theorem add_2 (s : t X) (x y : X.t) (hy : In y s) : In y (add x s) :=
  (Raw.add_spec s.this x y).mpr (Or.inr hy)

theorem add_3 (s : t X) (x y : X.t) (hne : ¬ X.eq x y)
    (hy : In y (add x s)) : In y s := by
  rcases (Raw.add_spec s.this x y).mp hy with hyx | hy
  · exact False.elim (hne (X.eq_sym y x hyx))
  · exact hy

theorem remove_1 (s : t X) (x y : X.t) (hxy : X.eq x y) :
    ¬ In y (remove x s) := by
  intro hy
  exact (Raw.remove_spec s.is_ok.ok x y).mp hy |>.2 (X.eq_sym x y hxy)

theorem remove_2 (s : t X) (x y : X.t) (hne : ¬ X.eq x y)
    (hy : In y s) : In y (remove x s) :=
  (Raw.remove_spec s.is_ok.ok x y).mpr
    ⟨hy, fun hyx => hne (X.eq_sym y x hyx)⟩

theorem remove_3 (s : t X) (x y : X.t) (hy : In y (remove x s)) : In y s :=
  (Raw.remove_spec s.is_ok.ok x y).mp hy |>.1

theorem singleton_1 (x y : X.t) (hy : In y (singleton x)) : X.eq x y :=
  X.eq_sym y x ((Raw.singleton_spec x y).mp hy)

theorem singleton_2 (x y : X.t) (hxy : X.eq x y) : In y (singleton x) :=
  (Raw.singleton_spec x y).mpr (X.eq_sym x y hxy)

theorem union_1 (s s' : t X) (x : X.t) (h : In x (union s s')) :
    In x s ∨ In x s' :=
  (Raw.union_spec s.is_ok.ok s'.is_ok.ok x).mp h

theorem union_2 (s s' : t X) (x : X.t) (h : In x s) : In x (union s s') :=
  (Raw.union_spec s.is_ok.ok s'.is_ok.ok x).mpr (Or.inl h)

theorem union_3 (s s' : t X) (x : X.t) (h : In x s') : In x (union s s') :=
  (Raw.union_spec s.is_ok.ok s'.is_ok.ok x).mpr (Or.inr h)

theorem inter_1 (s s' : t X) (x : X.t) (h : In x (inter s s')) : In x s :=
  (Raw.inter_spec s.is_ok.ok s'.is_ok.ok x).mp h |>.1

theorem inter_2 (s s' : t X) (x : X.t) (h : In x (inter s s')) : In x s' :=
  (Raw.inter_spec s.is_ok.ok s'.is_ok.ok x).mp h |>.2

theorem inter_3 (s s' : t X) (x : X.t) (h : In x s) (h' : In x s') :
    In x (inter s s') :=
  (Raw.inter_spec s.is_ok.ok s'.is_ok.ok x).mpr ⟨h, h'⟩

theorem diff_1 (s s' : t X) (x : X.t) (h : In x (diff s s')) : In x s :=
  (Raw.diff_spec s.is_ok.ok s'.is_ok.ok x).mp h |>.1

theorem diff_2 (s s' : t X) (x : X.t) (h : In x (diff s s')) : ¬ In x s' :=
  (Raw.diff_spec s.is_ok.ok s'.is_ok.ok x).mp h |>.2

theorem diff_3 (s s' : t X) (x : X.t) (h : In x s) (hn : ¬ In x s') :
    In x (diff s s') :=
  (Raw.diff_spec s.is_ok.ok s'.is_ok.ok x).mpr ⟨h, hn⟩

theorem fold_1 (s : t X) (A : Type) (i : A) (f : X.t → A → A) :
    fold f s i = List.foldl (fun a e => f e a) i (elements s) :=
  Raw.fold_spec s.this i f

theorem cardinal_1 (s : t X) : cardinal s = (elements s).length :=
  Raw.elements_cardinal s.this

theorem filter_1 (s : t X) (x : X.t) (f : X.t → Bool)
    (_hf : compat_bool X.eq f) (h : In x (filter f s)) : In x s :=
  Raw.filter_weak_spec s.this f x h

theorem filter_2 (s : t X) (x : X.t) (f : X.t → Bool)
    (hf : compat_bool X.eq f) (h : In x (filter f s)) : f x = true :=
  (Raw.filter_spec s.this f hf x).mp h |>.2

theorem filter_3 (s : t X) (x : X.t) (f : X.t → Bool)
    (hf : compat_bool X.eq f) (hx : In x s) (hfx : f x = true) :
    In x (filter f s) :=
  (Raw.filter_spec s.this f hf x).mpr ⟨hx, hfx⟩

theorem for_all_1 (s : t X) (f : X.t → Bool) (hf : compat_bool X.eq f)
    (h : For_all (fun x => f x = true) s) : for_all f s = true :=
  (Raw.for_all_spec s.this f hf).mpr h

theorem for_all_2 (s : t X) (f : X.t → Bool) (hf : compat_bool X.eq f)
    (h : for_all f s = true) : For_all (fun x => f x = true) s :=
  (Raw.for_all_spec s.this f hf).mp h

theorem exists_1 (s : t X) (f : X.t → Bool) (hf : compat_bool X.eq f)
    (h : Exists (fun x => f x = true) s) : exists_ f s = true :=
  (Raw.exists_spec s.this f hf).mpr h

theorem exists_2 (s : t X) (f : X.t → Bool) (hf : compat_bool X.eq f)
    (h : exists_ f s = true) : Exists (fun x => f x = true) s :=
  (Raw.exists_spec s.this f hf).mp h

theorem partition_1 (s : t X) (f : X.t → Bool) (_hf : compat_bool X.eq f) :
    Equal (partition f s).1 (filter f s) := by
  intro x
  change Raw.InT x (Raw.partition f s.this).1 ↔ Raw.InT x (Raw.filter f s.this)
  rw [Raw.partition_fst]

theorem partition_2 (s : t X) (f : X.t → Bool) (_hf : compat_bool X.eq f) :
    Equal (partition f s).2 (filter (fun x => !(f x)) s) := by
  intro x
  change Raw.InT x (Raw.partition f s.this).2 ↔
    Raw.InT x (Raw.filter (fun x => !(f x)) s.this)
  rw [Raw.partition_snd]

theorem elements_1 (s : t X) (x : X.t) (h : In x s) :
    InA X.eq x (elements s) :=
  (Raw.elements_spec1 s.this x).mpr h

theorem elements_2 (s : t X) (x : X.t) (h : InA X.eq x (elements s)) :
    In x s :=
  (Raw.elements_spec1 s.this x).mp h

theorem elements_3w (s : t X) : NoDupA X.eq (elements s) :=
  Raw.elements_spec2w s.this s.is_ok.ok

theorem choose_1 (s : t X) (x : X.t) (h : choose s = some x) : In x s :=
  Raw.choose_spec1 s.this x h

theorem choose_2 (s : t X) (h : choose s = none) : Empty s :=
  Raw.choose_spec2 s.this h

theorem lt_trans (s s' s'' : t X) (h₁ : lt s s') (h₂ : lt s' s'') :
    lt s s'' :=
  Raw.lt_strorder.trans h₁ h₂

theorem lt_not_eq (s s' : t X) (hlt : lt s s') : ¬ eq s s' := by
  intro heq
  have hself : Raw.lt s'.this s'.this :=
    (Raw.lt_compat heq (fun _ => Iff.rfl)).mp hlt
  exact Raw.lt_strorder.irrefl s'.this hself

theorem elements_3 (s : t X) : sort X.lt (elements s) :=
  Raw.elements_spec2 s.this s.is_ok.ok

theorem min_elt_1 (s : t X) (x : X.t) (h : min_elt s = some x) : In x s :=
  Raw.min_elt_spec1 s.this x h

theorem min_elt_2 (s : t X) (x y : X.t) (h : min_elt s = some x)
    (hy : In y s) : ¬ X.lt y x :=
  Raw.min_elt_spec2 s.this x y s.is_ok.ok h hy

theorem min_elt_3 (s : t X) (h : min_elt s = none) : Empty s :=
  Raw.min_elt_spec3 s.this h

theorem max_elt_1 (s : t X) (x : X.t) (h : max_elt s = some x) : In x s :=
  Raw.max_elt_spec1 s.this x h

theorem max_elt_2 (s : t X) (x y : X.t) (h : max_elt s = some x)
    (hy : In y s) : ¬ X.lt x y :=
  Raw.max_elt_spec2 s.this x y s.is_ok.ok h hy

theorem max_elt_3 (s : t X) (h : max_elt s = none) : Empty s :=
  Raw.max_elt_spec3 s.this h

theorem choose_3 (s s' : t X) (x y : X.t) (hx : choose s = some x)
    (hy : choose s' = some y) (heq : Equal s s') : X.eq x y :=
  Raw.choose_spec3 s.this s'.this x y s.is_ok.ok s'.is_ok.ok hx hy heq

def toSfun (X : OrderedType) : CompCert4Lean.Lib.FSetInterface.Sfun X where
  t := t X
  In := In
  empty := empty
  is_empty := is_empty
  mem := mem
  add := add
  singleton := singleton
  remove := remove
  union := union
  inter := inter
  diff := diff
  eq_dec := eq_dec
  equal := equal
  subset := subset
  fold := fold
  for_all := for_all
  exists_ := exists_
  filter := filter
  partition := partition
  cardinal := cardinal
  elements := elements
  choose := choose
  In_1 := In_1
  eq_refl := eq_refl
  eq_sym := eq_sym
  eq_trans := eq_trans
  mem_1 := mem_1
  mem_2 := mem_2
  equal_1 := equal_1
  equal_2 := equal_2
  subset_1 := subset_1
  subset_2 := subset_2
  empty_1 := empty_1
  is_empty_1 := is_empty_1
  is_empty_2 := is_empty_2
  add_1 := add_1
  add_2 := add_2
  add_3 := add_3
  remove_1 := remove_1
  remove_2 := remove_2
  remove_3 := remove_3
  singleton_1 := singleton_1
  singleton_2 := singleton_2
  union_1 := union_1
  union_2 := union_2
  union_3 := union_3
  inter_1 := inter_1
  inter_2 := inter_2
  inter_3 := inter_3
  diff_1 := diff_1
  diff_2 := diff_2
  diff_3 := diff_3
  fold_1 := fold_1
  cardinal_1 := cardinal_1
  filter_1 := filter_1
  filter_2 := filter_2
  filter_3 := filter_3
  for_all_1 := for_all_1
  for_all_2 := for_all_2
  exists_1 := exists_1
  exists_2 := exists_2
  partition_1 := partition_1
  partition_2 := partition_2
  elements_1 := elements_1
  elements_2 := elements_2
  elements_3w := elements_3w
  choose_1 := choose_1
  choose_2 := choose_2
  lt := lt
  compare := compare
  min_elt := min_elt
  max_elt := max_elt
  lt_trans := lt_trans
  lt_not_eq := lt_not_eq
  elements_3 := elements_3
  min_elt_1 := min_elt_1
  min_elt_2 := min_elt_2
  min_elt_3 := min_elt_3
  max_elt_1 := max_elt_1
  max_elt_2 := max_elt_2
  max_elt_3 := max_elt_3
  choose_3 := choose_3

abbrev WSfun (X : OrderedType) := (toSfun X).toWSfun
def S (X : OrderedType) : CompCert4Lean.Lib.FSetInterface.S := ⟨X, toSfun X⟩
def WS (X : OrderedType) : CompCert4Lean.Lib.FSetInterface.WS :=
  ⟨CompCert4Lean.Lib.FSetInterface.OrderedType.toDecidableType X,
    (toSfun X).toWSfun⟩
def MF (X : OrderedType) :=
  CompCert4Lean.Lib.FSetFacts.WFacts_fun.make
    (CompCert4Lean.Lib.FSetInterface.OrderedType.toDecidableType X)
    (toSfun X).toWSfun

def AboveMonotone (above_low_bound : X.t → Bool) : Prop :=
  ∀ x1 x2, X.eq x1 x2 ∨ X.lt x1 x2 →
    above_low_bound x1 = true → above_low_bound x2 = true

def BelowMonotone (below_high_bound : X.t → Bool) : Prop :=
  ∀ x1 x2, X.eq x1 x2 ∨ X.lt x2 x1 →
    below_high_bound x1 = true → below_high_bound x2 = true

def PredCompat (pred : X.t → Bool) : Prop :=
  ∀ x1 x2, X.eq x1 x2 → pred x1 = pred x2

section MEM_BETWEEN

def raw_mem_between (above_low_bound below_high_bound : X.t → Bool) :
    Raw.tree X → Bool
  | .Leaf => false
  | .Node _ left value right =>
      if above_low_bound value then
        if below_high_bound value then true
        else raw_mem_between above_low_bound below_high_bound left
      else
        raw_mem_between above_low_bound below_high_bound right

def mem_between (above_low_bound below_high_bound : X.t → Bool) (m : t X) : Bool :=
  raw_mem_between above_low_bound below_high_bound m.this

def raw_mem_between_1Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.t → Bool)
    (m : Raw.tree X),
    raw_mem_between above_low_bound below_high_bound m = true →
      ∃ x, Raw.InT x m ∧ above_low_bound x = true ∧ below_high_bound x = true

def raw_mem_between_2Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.t → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.t) (m : Raw.tree X),
      Raw.bst m → Raw.InT x m → above_low_bound x = true →
        below_high_bound x = true →
          raw_mem_between above_low_bound below_high_bound m = true

def mem_between_1Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.t → Bool)
    (s : t X),
    mem_between above_low_bound below_high_bound s = true →
      ∃ x, In x s ∧ above_low_bound x = true ∧ below_high_bound x = true

def mem_between_2Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.t → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.t) (s : t X),
      In x s → above_low_bound x = true → below_high_bound x = true →
        mem_between above_low_bound below_high_bound s = true

end MEM_BETWEEN

section ELEMENTS_BETWEEN

def raw_elements_between (above_low_bound below_high_bound : X.t → Bool) :
    Raw.tree X → Raw.tree X
  | .Leaf => .Leaf
  | .Node _ left value right =>
      if above_low_bound value then
        if below_high_bound value then
          Raw.join
            (raw_elements_between above_low_bound below_high_bound left)
            value
            (raw_elements_between above_low_bound below_high_bound right)
        else
          raw_elements_between above_low_bound below_high_bound left
      else
        raw_elements_between above_low_bound below_high_bound right

private theorem in_raw_elements_between
    (above_low_bound below_high_bound : X.t → Bool) (x : X.t) :
    ∀ m, Raw.InT x (raw_elements_between above_low_bound below_high_bound m) →
      Raw.InT x m := by
  intro m
  induction m with
  | Leaf => simp [raw_elements_between]
  | Node height left value right left_ih right_ih =>
      rw [raw_elements_between]
      split
      next =>
        split
        next =>
          intro hjoin
          rcases (Raw.join_spec
            (raw_elements_between above_low_bound below_high_bound left)
            value
            (raw_elements_between above_low_bound below_high_bound right)
            x).mp hjoin with hx | hx | hx
          · exact .IsRoot height left right value hx
          · exact .InLeft height left right value (left_ih hx)
          · exact .InRight height left right value (right_ih hx)
        next => exact fun hx => .InLeft height left right value (left_ih hx)
      next => exact fun hx => .InRight height left right value (right_ih hx)

private theorem raw_elements_between_bst
    (above_low_bound below_high_bound : X.t → Bool) :
    ∀ m, Raw.bst m →
      Raw.bst (raw_elements_between above_low_bound below_high_bound m) := by
  intro m hbst
  induction hbst with
  | BSLeaf => exact .BSLeaf
  | BSNode height value left right left_bst right_bst left_lt right_gt
      left_ih right_ih =>
      rw [raw_elements_between]
      split
      next =>
        split
        next =>
          apply Raw.join_bst _ value _ left_ih right_ih
          · intro x hx
            exact left_lt x (in_raw_elements_between _ _ x left hx)
          · intro x hx
            exact right_gt x (in_raw_elements_between _ _ x right hx)
        next => exact left_ih
      next => exact right_ih

def elements_between (above_low_bound below_high_bound : X.t → Bool) (s : t X) :
    t X :=
  ⟨raw_elements_between above_low_bound below_high_bound s.this,
    ⟨raw_elements_between_bst above_low_bound below_high_bound s.this s.is_ok.ok⟩⟩

def In_raw_elements_between_1Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.t → Bool)
    (x : X.t) (m : Raw.tree X),
    Raw.InT x (raw_elements_between above_low_bound below_high_bound m) →
      Raw.InT x m

def raw_elements_between_okStatement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.t → Bool)
    (m : Raw.tree X),
    Raw.bst m → Raw.bst (raw_elements_between above_low_bound below_high_bound m)

def In_raw_elements_between_2Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.t → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.t) (m : Raw.tree X),
      Raw.InT x (raw_elements_between above_low_bound below_high_bound m) →
        above_low_bound x = true ∧ below_high_bound x = true

def In_raw_elements_between_3Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.t → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.t) (m : Raw.tree X),
      Raw.bst m → Raw.InT x m → above_low_bound x = true →
        below_high_bound x = true →
          Raw.InT x (raw_elements_between above_low_bound below_high_bound m)

def elements_between_iffStatement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.t → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.t) (s : t X),
      In x (elements_between above_low_bound below_high_bound s) ↔
        In x s ∧ above_low_bound x = true ∧ below_high_bound x = true

end ELEMENTS_BETWEEN

section FOR_ALL_BETWEEN

def raw_for_all_between
    (pred above_low_bound below_high_bound : X.t → Bool) : Raw.tree X → Bool
  | .Leaf => true
  | .Node _ left value right =>
      if above_low_bound value then
        if below_high_bound value then
          raw_for_all_between pred above_low_bound below_high_bound left &&
            pred value &&
            raw_for_all_between pred above_low_bound below_high_bound right
        else
          raw_for_all_between pred above_low_bound below_high_bound left
      else
        raw_for_all_between pred above_low_bound below_high_bound right

def for_all_between (pred above_low_bound below_high_bound : X.t → Bool)
    (m : t X) : Bool :=
  raw_for_all_between pred above_low_bound below_high_bound m.this

def raw_for_all_between_1Statement : Prop :=
  ∀ (X : OrderedType) (pred above_low_bound below_high_bound : X.t → Bool),
    PredCompat pred → AboveMonotone above_low_bound →
    BelowMonotone below_high_bound →
    ∀ (x : X.t) (m : Raw.tree X),
      Raw.bst m →
      raw_for_all_between pred above_low_bound below_high_bound m = true →
      Raw.InT x m → above_low_bound x = true → below_high_bound x = true →
      pred x = true

def raw_for_all_between_2Statement : Prop :=
  ∀ (X : OrderedType) (pred above_low_bound below_high_bound : X.t → Bool)
    (m : Raw.tree X),
    Raw.bst m →
    (∀ x, Raw.InT x m → above_low_bound x = true →
      below_high_bound x = true → pred x = true) →
    raw_for_all_between pred above_low_bound below_high_bound m = true

def for_all_between_iffStatement : Prop :=
  ∀ (X : OrderedType) (pred above_low_bound below_high_bound : X.t → Bool),
    PredCompat pred → AboveMonotone above_low_bound →
    BelowMonotone below_high_bound →
    ∀ s : t X,
      for_all_between pred above_low_bound below_high_bound s = true ↔
        ∀ x, In x s → above_low_bound x = true →
          below_high_bound x = true → pred x = true

end FOR_ALL_BETWEEN

section PARTITION_BETWEEN

def raw_partition_between (above_low_bound below_high_bound : X.t → Bool) :
    Raw.tree X → Raw.tree X × Raw.tree X
  | .Leaf => (.Leaf, .Leaf)
  | .Node _ left value right =>
      if above_low_bound value then
        if below_high_bound value then
          let (left₁, left₂) :=
            raw_partition_between above_low_bound below_high_bound left
          let (right₁, right₂) :=
            raw_partition_between above_low_bound below_high_bound right
          (Raw.join left₁ value right₁, Raw.concat left₂ right₂)
        else
          let (left₁, left₂) :=
            raw_partition_between above_low_bound below_high_bound left
          (left₁, Raw.join left₂ value right)
      else
        let (right₁, right₂) :=
          raw_partition_between above_low_bound below_high_bound right
        (right₁, Raw.join left value right₂)

private theorem raw_partition_between_subset
    (above_low_bound below_high_bound : X.t → Bool) :
    ∀ m,
      (∀ x, Raw.InT x
          (raw_partition_between above_low_bound below_high_bound m).1 →
        Raw.InT x m) ∧
      (∀ x, Raw.InT x
          (raw_partition_between above_low_bound below_high_bound m).2 →
        Raw.InT x m) := by
  intro m
  induction m with
  | Leaf =>
      constructor <;> intro x hx <;> cases hx
  | Node height left value right left_ih right_ih =>
      rw [raw_partition_between]
      split
      next =>
        split
        next =>
          cases hl : raw_partition_between above_low_bound below_high_bound left with
          | mk left₁ left₂ =>
            cases hr : raw_partition_between above_low_bound below_high_bound right with
            | mk right₁ right₂ =>
              have hil := left_ih
              have hir := right_ih
              rw [hl] at hil
              rw [hr] at hir
              constructor
              · intro x hx
                rcases (Raw.join_spec left₁ value right₁ x).mp hx with hx | hx | hx
                · exact .IsRoot height left right value hx
                · exact .InLeft height left right value (hil.1 x hx)
                · exact .InRight height left right value (hir.1 x hx)
              · intro x hx
                rcases (Raw.concat_spec left₂ right₂ x).mp hx with hx | hx
                · exact .InLeft height left right value (hil.2 x hx)
                · exact .InRight height left right value (hir.2 x hx)
        next =>
          cases hl : raw_partition_between above_low_bound below_high_bound left with
          | mk left₁ left₂ =>
            have hil := left_ih
            rw [hl] at hil
            constructor
            · intro x hx
              exact .InLeft height left right value (hil.1 x hx)
            · intro x hx
              rcases (Raw.join_spec left₂ value right x).mp hx with hx | hx | hx
              · exact .IsRoot height left right value hx
              · exact .InLeft height left right value (hil.2 x hx)
              · exact .InRight height left right value hx
      next =>
        cases hr : raw_partition_between above_low_bound below_high_bound right with
        | mk right₁ right₂ =>
          have hir := right_ih
          rw [hr] at hir
          constructor
          · intro x hx
            exact .InRight height left right value (hir.1 x hx)
          · intro x hx
            rcases (Raw.join_spec left value right₂ x).mp hx with hx | hx | hx
            · exact .IsRoot height left right value hx
            · exact .InLeft height left right value hx
            · exact .InRight height left right value (hir.2 x hx)

private theorem raw_partition_between_bst
    (above_low_bound below_high_bound : X.t → Bool) :
    ∀ m, Raw.bst m →
      Raw.bst (raw_partition_between above_low_bound below_high_bound m).1 ∧
      Raw.bst (raw_partition_between above_low_bound below_high_bound m).2 := by
  intro m hbst
  induction hbst with
  | BSLeaf => exact ⟨.BSLeaf, .BSLeaf⟩
  | BSNode height value left right left_bst right_bst left_lt right_gt
      left_ih right_ih =>
      rw [raw_partition_between]
      split
      next =>
        split
        next =>
          cases hl : raw_partition_between above_low_bound below_high_bound left with
          | mk left₁ left₂ =>
            cases hr : raw_partition_between above_low_bound below_high_bound right with
            | mk right₁ right₂ =>
              have hbl := left_ih
              have hbr := right_ih
              have hsl := raw_partition_between_subset
                above_low_bound below_high_bound left
              have hsr := raw_partition_between_subset
                above_low_bound below_high_bound right
              rw [hl] at hbl hsl
              rw [hr] at hbr hsr
              constructor
              · apply Raw.join_bst left₁ value right₁ hbl.1 hbr.1
                · intro x hx
                  exact left_lt x (hsl.1 x hx)
                · intro x hx
                  exact right_gt x (hsr.1 x hx)
              · apply Raw.concat_bst left₂ right₂ hbl.2 hbr.2
                intro x y hx hy
                exact X.lt_trans x value y
                  (left_lt x (hsl.2 x hx)) (right_gt y (hsr.2 y hy))
        next =>
          cases hl : raw_partition_between above_low_bound below_high_bound left with
          | mk left₁ left₂ =>
            have hbl := left_ih
            have hsl := raw_partition_between_subset
              above_low_bound below_high_bound left
            rw [hl] at hbl hsl
            constructor
            · exact hbl.1
            · apply Raw.join_bst left₂ value right hbl.2 right_bst
              · intro x hx
                exact left_lt x (hsl.2 x hx)
              · exact right_gt
      next =>
        cases hr : raw_partition_between above_low_bound below_high_bound right with
        | mk right₁ right₂ =>
          have hbr := right_ih
          have hsr := raw_partition_between_subset
            above_low_bound below_high_bound right
          rw [hr] at hbr hsr
          constructor
          · exact hbr.1
          · apply Raw.join_bst left value right₂ left_bst hbr.2
            · exact left_lt
            · intro x hx
              exact right_gt x (hsr.2 x hx)

def partition_between (above_low_bound below_high_bound : X.t → Bool)
    (s : t X) : t X × t X :=
  let p := raw_partition_between above_low_bound below_high_bound s.this
  let hp := raw_partition_between_bst
    above_low_bound below_high_bound s.this s.is_ok.ok
  (⟨p.1, ⟨hp.1⟩⟩, ⟨p.2, ⟨hp.2⟩⟩)

def In_raw_partition_between_1Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.t → Bool)
    (x : X.t) (m : Raw.tree X),
    Raw.InT x (raw_partition_between above_low_bound below_high_bound m).1 →
      Raw.InT x m

def In_raw_partition_between_2Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.t → Bool)
    (x : X.t) (m : Raw.tree X),
    Raw.InT x (raw_partition_between above_low_bound below_high_bound m).2 →
      Raw.InT x m

def raw_partition_between_okStatement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.t → Bool)
    (m : Raw.tree X),
    Raw.bst m →
      Raw.bst (raw_partition_between above_low_bound below_high_bound m).1 ∧
      Raw.bst (raw_partition_between above_low_bound below_high_bound m).2

def In_raw_partition_between_3Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.t → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.t) (m : Raw.tree X),
      Raw.InT x (raw_partition_between above_low_bound below_high_bound m).1 →
        above_low_bound x = true ∧ below_high_bound x = true

def In_raw_partition_between_4Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.t → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.t) (m : Raw.tree X),
      Raw.bst m →
      Raw.InT x (raw_partition_between above_low_bound below_high_bound m).2 →
        above_low_bound x = false ∨ below_high_bound x = false

def In_raw_partition_between_5Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.t → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.t) (m : Raw.tree X),
      Raw.bst m → Raw.InT x m → above_low_bound x = true →
        below_high_bound x = true →
          Raw.InT x (raw_partition_between above_low_bound below_high_bound m).1

def In_raw_partition_between_6Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.t → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.t) (m : Raw.tree X),
      Raw.bst m → Raw.InT x m →
        (above_low_bound x = false ∨ below_high_bound x = false) →
          Raw.InT x (raw_partition_between above_low_bound below_high_bound m).2

def partition_between_iff_1Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.t → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.t) (s : t X),
      In x (partition_between above_low_bound below_high_bound s).1 ↔
        In x s ∧ above_low_bound x = true ∧ below_high_bound x = true

def partition_between_iff_2Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.t → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.t) (s : t X),
      In x (partition_between above_low_bound below_high_bound s).2 ↔
        In x s ∧ (above_low_bound x = false ∨ below_high_bound x = false)

end PARTITION_BETWEEN

end Make
end CompCert4Lean.Lib.FSetAVLplus

namespace CompCert4Lean.Lib.FSetAVLplus.Make

theorem raw_mem_between_1 : raw_mem_between_1Statement := by
  intro X above_low_bound below_high_bound m hmem
  induction m with
  | Leaf => simp [raw_mem_between] at hmem
  | Node height left value right left_ih right_ih =>
      cases habove : above_low_bound value with
      | false =>
          simp only [raw_mem_between, habove] at hmem
          rcases right_ih hmem with ⟨x, hx, habove, hbelow⟩
          exact ⟨x, .InRight height left right value hx, habove, hbelow⟩
      | true =>
          cases hbelow : below_high_bound value with
          | false =>
              simp only [raw_mem_between, habove, hbelow] at hmem
              rcases left_ih hmem with ⟨x, hx, habove, hbelow⟩
              exact ⟨x, .InLeft height left right value hx, habove, hbelow⟩
          | true =>
              exact ⟨value, .IsRoot height left right value (X.eq_refl value),
                habove, hbelow⟩

theorem raw_mem_between_2 : raw_mem_between_2Statement := by
  intro X above_low_bound below_high_bound above_monotone below_monotone
    x m hbst hx habove hbelow
  induction hbst generalizing x with
  | BSLeaf => exact False.elim ((Raw.In_leaf_iff x).mp hx)
  | BSNode info value left right hleft hright hlt hgt left_ih right_ih =>
      rw [Raw.In_node_iff] at hx
      cases hvalue_above : above_low_bound value with
      | false =>
          simp only [raw_mem_between, hvalue_above]
          cases hx with
          | inl hxleft =>
              have hcontra : above_low_bound value = true :=
                above_monotone x value (Or.inr (hlt x hxleft)) habove
              rw [hvalue_above] at hcontra
              cases hcontra
          | inr hx =>
              cases hx with
              | inl hxeq =>
                  have hcontra : above_low_bound value = true :=
                    above_monotone x value (Or.inl hxeq) habove
                  rw [hvalue_above] at hcontra
                  cases hcontra
              | inr hxright => exact right_ih x hxright habove hbelow
      | true =>
          cases hvalue_below : below_high_bound value with
          | false =>
              simp only [raw_mem_between, hvalue_above, hvalue_below]
              cases hx with
              | inl hxleft => exact left_ih x hxleft habove hbelow
              | inr hx =>
                  cases hx with
                  | inl hxeq =>
                      have hcontra : below_high_bound value = true :=
                        below_monotone x value (Or.inl hxeq) hbelow
                      rw [hvalue_below] at hcontra
                      cases hcontra
                  | inr hxright =>
                      have hcontra : below_high_bound value = true :=
                        below_monotone x value (Or.inr (hgt x hxright)) hbelow
                      rw [hvalue_below] at hcontra
                      cases hcontra
          | true => simp [raw_mem_between, hvalue_above, hvalue_below]

theorem mem_between_1 : mem_between_1Statement := by
  intro X above_low_bound below_high_bound s hmem
  exact raw_mem_between_1 X above_low_bound below_high_bound s.this hmem

theorem mem_between_2 : mem_between_2Statement := by
  intro X above_low_bound below_high_bound above_monotone below_monotone
    x s hx habove hbelow
  exact raw_mem_between_2 X above_low_bound below_high_bound
    above_monotone below_monotone x s.this s.is_ok.ok hx habove hbelow

end CompCert4Lean.Lib.FSetAVLplus.Make

namespace CompCert4Lean.Lib.FSetAVLplus.Make

theorem In_raw_elements_between_1 : In_raw_elements_between_1Statement := by
  intro X above_low_bound below_high_bound x m hx
  exact in_raw_elements_between above_low_bound below_high_bound x m hx

end CompCert4Lean.Lib.FSetAVLplus.Make
