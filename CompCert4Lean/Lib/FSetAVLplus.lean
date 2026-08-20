import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Ordered

/-!
# Interval operations on ordered finite-set trees

This module is the definition-bearing part of `lib/FSetAVLplus.v`.  The
balanced-tree proof obligations are kept in the source-shaped `bst` field and
the later proof-migration declarations are represented by proposition
descriptors below.
-/

namespace CompCert4Lean.Lib.FSetAVLplus

structure OrderedType where
  elt : Type
  eq : elt → elt → Prop
  lt : elt → elt → Prop
  eq_dec : (x y : elt) → Decidable (eq x y)
  eq_refl : ∀ x, eq x x
  eq_sym : ∀ {x y}, eq x y → eq y x
  eq_trans : ∀ {x y z}, eq x y → eq y z → eq x z
  lt_trans : ∀ {x y z}, lt x y → lt y z → lt x z
  lt_not_eq : ∀ {x y}, lt x y → ¬ eq x y

def Make : Type := Unit

def «Make.Raw» : Type := Unit

namespace Make

namespace Raw

inductive tree (α : Type) where
  | Leaf
  | Node (height : Nat) (left : tree α) (value : α) (right : tree α)

def height {α : Type} : tree α → Nat
  | .Leaf => 0
  | .Node h _ _ _ => h

def In (X : OrderedType) (x : X.elt) : tree X.elt → Prop
  | .Leaf => False
  | .Node _ left value right =>
      X.eq x value ∨ In X x left ∨ In X x right

/- The invariant called `bst` by the source does not include AVL balance:
   it says recursively that the left and right subtrees are search trees and
   that all their elements are respectively below and above the root. -/
def lt_tree (X : OrderedType) (x : X.elt) (s : tree X.elt) : Prop :=
  ∀ y, In X y s → X.lt y x

def gt_tree (X : OrderedType) (x : X.elt) (s : tree X.elt) : Prop :=
  ∀ y, In X y s → X.lt x y

inductive bst (X : OrderedType) : tree X.elt → Prop where
  | BSLeaf : bst X .Leaf
  | BSNode (c : Nat) (x : X.elt) (l r : tree X.elt) :
      bst X l → bst X r → lt_tree X x l → gt_tree X x r →
        bst X (.Node c l x r)

private theorem bst_node_inv {X : OrderedType} {c : Nat} {x : X.elt}
    {l r : tree X.elt} (h : bst X (.Node c l x r)) :
    bst X l ∧ bst X r ∧ lt_tree X x l ∧ gt_tree X x r := by
  cases h with
  | BSNode _ _ _ _ left_bst right_bst left_lt right_gt =>
      exact ⟨left_bst, right_bst, left_lt, right_gt⟩

def join {α : Type} (left : tree α) (value : α) (right : tree α) : tree α :=
  .Node (height left + height right + 1) left value right

def concat {α : Type} : tree α → tree α → tree α
  | .Leaf, right => right
  | left, .Leaf => left
  | .Node _ left₁ value right₁, right₂ =>
      join left₁ value (concat right₁ right₂)

private theorem join_bst {X : OrderedType} {left right : tree X.elt}
    {value : X.elt} (left_bst : bst X left) (right_bst : bst X right)
    (left_lt : ∀ x, In X x left → X.lt x value)
    (right_gt : ∀ x, In X x right → X.lt value x) :
    bst X (join left value right) := by
  exact .BSNode _ _ _ _ left_bst right_bst left_lt right_gt

private theorem in_concat_iff {X : OrderedType} (x : X.elt) :
    ∀ left right,
      In X x (concat left right) ↔ In X x left ∨ In X x right := by
  intro left
  induction left with
  | Leaf =>
      intro right
      simp [concat, In]
  | Node height left value right _ right_ih =>
      intro other
      cases other with
      | Leaf => simp [concat, In]
      | Node other_height other_left other_value other_right =>
          simp only [concat, join, In]
          rw [right_ih]
          constructor
          · intro h
            rcases h with h | h | h | h
            · exact Or.inl (Or.inl h)
            · exact Or.inl (Or.inr (Or.inl h))
            · exact Or.inl (Or.inr (Or.inr h))
            · exact Or.inr h
          · intro h
            rcases h with (h | h | h) | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr h))

private theorem concat_bst (X : OrderedType) :
    ∀ left right,
      bst X left → bst X right →
      (∀ x y, In X x left → In X y right → X.lt x y) →
      bst X (concat left right) := by
  intro left
  induction left with
  | Leaf =>
      intro right _ right_bst _
      simpa [concat] using right_bst
  | Node height left value right _ right_ih =>
      intro other tree_bst other_bst between
      cases other with
      | Leaf => simpa [concat] using tree_bst
      | Node other_height other_left other_value other_right =>
          cases tree_bst with
          | BSNode _ _ _ _ left_bst right_bst left_lt right_gt =>
              apply join_bst left_bst
              · apply right_ih _ right_bst other_bst
                intro x y hx hy
                exact between x y (Or.inr (Or.inr hx)) hy
              · exact left_lt
              · intro y hy
                rcases (in_concat_iff y right
                  (.Node other_height other_left other_value other_right)).mp hy with hy | hy
                · exact right_gt y hy
                · exact between value y (Or.inl (X.eq_refl value)) hy

end Raw

structure Set (X : OrderedType) where
  this : Raw.tree X.elt
  is_ok : Raw.bst X this

abbrev t (X : OrderedType) := Set X

abbrev elt (X : OrderedType) := X.elt

def In (X : OrderedType) (x : X.elt) (s : t X) : Prop :=
  Raw.In X x s.this

section MEM_BETWEEN

def raw_mem_between {X : OrderedType}
    (above_low_bound below_high_bound : X.elt → Bool) :
    Raw.tree X.elt → Bool
  | .Leaf => false
  | .Node _ left value right =>
      if above_low_bound value then
        if below_high_bound value then true
        else raw_mem_between above_low_bound below_high_bound left
      else
        raw_mem_between above_low_bound below_high_bound right

def mem_between {X : OrderedType}
    (above_low_bound below_high_bound : X.elt → Bool) (m : t X) : Bool :=
  raw_mem_between above_low_bound below_high_bound m.this

def AboveMonotone {X : OrderedType} (above_low_bound : X.elt → Bool) : Prop :=
  ∀ x1 x2, X.eq x1 x2 ∨ X.lt x1 x2 →
    above_low_bound x1 = true → above_low_bound x2 = true

def BelowMonotone {X : OrderedType} (below_high_bound : X.elt → Bool) : Prop :=
  ∀ x1 x2, X.eq x1 x2 ∨ X.lt x2 x1 →
    below_high_bound x1 = true → below_high_bound x2 = true

def raw_mem_between_1Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.elt → Bool)
    (m : Raw.tree X.elt),
    raw_mem_between above_low_bound below_high_bound m = true →
      ∃ x, Raw.In X x m ∧ above_low_bound x = true ∧ below_high_bound x = true

def raw_mem_between_2Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.elt → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.elt) (m : Raw.tree X.elt),
      Raw.bst X m → Raw.In X x m → above_low_bound x = true →
        below_high_bound x = true →
          raw_mem_between above_low_bound below_high_bound m = true

def mem_between_1Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.elt → Bool)
    (s : t X),
    mem_between above_low_bound below_high_bound s = true →
      ∃ x, In X x s ∧ above_low_bound x = true ∧ below_high_bound x = true

def mem_between_2Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.elt → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.elt) (s : t X),
      In X x s → above_low_bound x = true → below_high_bound x = true →
        mem_between above_low_bound below_high_bound s = true

end MEM_BETWEEN

section ELEMENTS_BETWEEN

def raw_elements_between {X : OrderedType}
    (above_low_bound below_high_bound : X.elt → Bool) :
    Raw.tree X.elt → Raw.tree X.elt
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

private theorem in_raw_elements_between {X : OrderedType}
    (above_low_bound below_high_bound : X.elt → Bool) (x : X.elt) :
    ∀ m,
      Raw.In X x (raw_elements_between above_low_bound below_high_bound m) →
        Raw.In X x m := by
  intro m
  induction m with
  | Leaf => simp [raw_elements_between, Raw.In]
  | Node height left value right left_ih right_ih =>
      intro h
      rw [raw_elements_between] at h
      split at h
      next =>
        split at h
        next =>
          rcases h with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl (left_ih h))
          · exact Or.inr (Or.inr (right_ih h))
        next => exact Or.inr (Or.inl (left_ih h))
      next => exact Or.inr (Or.inr (right_ih h))

private theorem raw_elements_between_bst {X : OrderedType}
    (above_low_bound below_high_bound : X.elt → Bool) :
    ∀ m, Raw.bst X m →
      Raw.bst X (raw_elements_between above_low_bound below_high_bound m) := by
  intro m
  induction m with
  | Leaf => simp [raw_elements_between]
  | Node height left value right left_ih right_ih =>
      intro h
      rcases Raw.bst_node_inv h with ⟨left_bst, right_bst, left_lt, right_gt⟩
      rw [raw_elements_between]
      split
      next =>
        split
        next =>
          apply Raw.join_bst (left_ih left_bst) (right_ih right_bst)
          · intro x hx
            exact left_lt x
              (in_raw_elements_between above_low_bound below_high_bound x left hx)
          · intro x hx
            exact right_gt x
              (in_raw_elements_between above_low_bound below_high_bound x right hx)
        next => exact left_ih left_bst
      next => exact right_ih right_bst

def elements_between {X : OrderedType}
    (above_low_bound below_high_bound : X.elt → Bool) (s : t X) : t X :=
  ⟨raw_elements_between above_low_bound below_high_bound s.this,
    raw_elements_between_bst above_low_bound below_high_bound s.this s.is_ok⟩

def In_raw_elements_between_1Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.elt → Bool)
    (x : X.elt) (m : Raw.tree X.elt),
    Raw.In X x (raw_elements_between above_low_bound below_high_bound m) →
      Raw.In X x m

def raw_elements_between_okStatement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.elt → Bool)
    (m : Raw.tree X.elt),
    Raw.bst X m →
      Raw.bst X (raw_elements_between above_low_bound below_high_bound m)

def In_raw_elements_between_2Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.elt → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.elt) (m : Raw.tree X.elt),
      Raw.In X x (raw_elements_between above_low_bound below_high_bound m) →
        above_low_bound x = true ∧ below_high_bound x = true

def In_raw_elements_between_3Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.elt → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.elt) (m : Raw.tree X.elt),
      Raw.bst X m → Raw.In X x m → above_low_bound x = true →
        below_high_bound x = true →
          Raw.In X x (raw_elements_between above_low_bound below_high_bound m)

def elements_between_iffStatement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.elt → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.elt) (s : t X),
      In X x (elements_between above_low_bound below_high_bound s) ↔
        In X x s ∧ above_low_bound x = true ∧ below_high_bound x = true

end ELEMENTS_BETWEEN

section FOR_ALL_BETWEEN

def raw_for_all_between {X : OrderedType}
    (pred above_low_bound below_high_bound : X.elt → Bool) :
    Raw.tree X.elt → Bool
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

def for_all_between {X : OrderedType}
    (pred above_low_bound below_high_bound : X.elt → Bool) (m : t X) : Bool :=
  raw_for_all_between pred above_low_bound below_high_bound m.this

def PredCompat {X : OrderedType} (pred : X.elt → Bool) : Prop :=
  ∀ x1 x2, X.eq x1 x2 → pred x1 = pred x2

def raw_for_all_between_1Statement : Prop :=
  ∀ (X : OrderedType) (pred above_low_bound below_high_bound : X.elt → Bool),
    PredCompat pred → AboveMonotone above_low_bound →
    BelowMonotone below_high_bound →
    ∀ (x : X.elt) (m : Raw.tree X.elt),
      Raw.bst X m → raw_for_all_between pred above_low_bound below_high_bound m = true →
      Raw.In X x m → above_low_bound x = true → below_high_bound x = true →
        pred x = true

def raw_for_all_between_2Statement : Prop :=
  ∀ (X : OrderedType) (pred above_low_bound below_high_bound : X.elt → Bool)
    (m : Raw.tree X.elt),
    Raw.bst X m →
      (∀ x, Raw.In X x m → above_low_bound x = true →
        below_high_bound x = true → pred x = true) →
        raw_for_all_between pred above_low_bound below_high_bound m = true

def for_all_between_iffStatement : Prop :=
  ∀ (X : OrderedType) (pred above_low_bound below_high_bound : X.elt → Bool),
    PredCompat pred → AboveMonotone above_low_bound →
    BelowMonotone below_high_bound →
    ∀ (s : t X),
      for_all_between pred above_low_bound below_high_bound s = true ↔
        (∀ x, In X x s → above_low_bound x = true →
          below_high_bound x = true → pred x = true)

end FOR_ALL_BETWEEN

section PARTITION_BETWEEN

def raw_partition_between {X : OrderedType}
    (above_low_bound below_high_bound : X.elt → Bool) :
    Raw.tree X.elt → Raw.tree X.elt × Raw.tree X.elt
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

private theorem raw_partition_between_subset {X : OrderedType}
    (above_low_bound below_high_bound : X.elt → Bool) :
    ∀ m,
      (∀ x, Raw.In X x
          (raw_partition_between above_low_bound below_high_bound m).1 →
        Raw.In X x m) ∧
      (∀ x, Raw.In X x
          (raw_partition_between above_low_bound below_high_bound m).2 →
        Raw.In X x m) := by
  intro m
  induction m with
  | Leaf => simp [raw_partition_between, Raw.In]
  | Node height left value right left_ih right_ih =>
      rw [raw_partition_between]
      split
      next =>
        split
        next =>
          cases left_eq : raw_partition_between above_low_bound below_high_bound left with
          | mk left₁ left₂ =>
            cases right_eq : raw_partition_between above_low_bound below_high_bound right with
            | mk right₁ right₂ =>
              rw [left_eq] at left_ih
              rw [right_eq] at right_ih
              constructor
              · intro x hx
                rcases hx with hx | hx | hx
                · exact Or.inl hx
                · exact Or.inr (Or.inl (left_ih.1 x hx))
                · exact Or.inr (Or.inr (right_ih.1 x hx))
              · intro x hx
                rcases (Raw.in_concat_iff x left₂ right₂).mp hx with hx | hx
                · exact Or.inr (Or.inl (left_ih.2 x hx))
                · exact Or.inr (Or.inr (right_ih.2 x hx))
        next =>
          cases left_eq : raw_partition_between above_low_bound below_high_bound left with
          | mk left₁ left₂ =>
            rw [left_eq] at left_ih
            constructor
            · intro x hx
              exact Or.inr (Or.inl (left_ih.1 x hx))
            · intro x hx
              rcases hx with hx | hx | hx
              · exact Or.inl hx
              · exact Or.inr (Or.inl (left_ih.2 x hx))
              · exact Or.inr (Or.inr hx)
      next =>
        cases right_eq : raw_partition_between above_low_bound below_high_bound right with
        | mk right₁ right₂ =>
          rw [right_eq] at right_ih
          constructor
          · intro x hx
            exact Or.inr (Or.inr (right_ih.1 x hx))
          · intro x hx
            rcases hx with hx | hx | hx
            · exact Or.inl hx
            · exact Or.inr (Or.inl hx)
            · exact Or.inr (Or.inr (right_ih.2 x hx))

private theorem raw_partition_between_bst {X : OrderedType}
    (above_low_bound below_high_bound : X.elt → Bool) :
    ∀ m, Raw.bst X m →
      Raw.bst X (raw_partition_between above_low_bound below_high_bound m).1 ∧
        Raw.bst X (raw_partition_between above_low_bound below_high_bound m).2 := by
  intro m
  induction m with
  | Leaf => simp [raw_partition_between]
  | Node height left value right left_ih right_ih =>
      intro tree_bst
      rcases Raw.bst_node_inv tree_bst with
        ⟨left_bst, right_bst, left_lt, right_gt⟩
      rw [raw_partition_between]
      split
      next =>
        split
        next =>
          cases left_eq : raw_partition_between above_low_bound below_high_bound left with
          | mk left₁ left₂ =>
            cases right_eq : raw_partition_between above_low_bound below_high_bound right with
            | mk right₁ right₂ =>
              have left_parts := left_ih left_bst
              have right_parts := right_ih right_bst
              have left_subset :=
                raw_partition_between_subset above_low_bound below_high_bound left
              have right_subset :=
                raw_partition_between_subset above_low_bound below_high_bound right
              rw [left_eq] at left_parts left_subset
              rw [right_eq] at right_parts right_subset
              constructor
              · apply Raw.join_bst left_parts.1 right_parts.1
                · intro x hx
                  exact left_lt x (left_subset.1 x hx)
                · intro x hx
                  exact right_gt x (right_subset.1 x hx)
              · apply Raw.concat_bst X left₂ right₂ left_parts.2 right_parts.2
                intro x y hx hy
                exact X.lt_trans
                  (left_lt x (left_subset.2 x hx))
                  (right_gt y (right_subset.2 y hy))
        next =>
          cases left_eq : raw_partition_between above_low_bound below_high_bound left with
          | mk left₁ left₂ =>
            have left_parts := left_ih left_bst
            have left_subset :=
              raw_partition_between_subset above_low_bound below_high_bound left
            rw [left_eq] at left_parts left_subset
            constructor
            · exact left_parts.1
            · apply Raw.join_bst left_parts.2 right_bst
              · intro x hx
                exact left_lt x (left_subset.2 x hx)
              · exact right_gt
      next =>
        cases right_eq : raw_partition_between above_low_bound below_high_bound right with
        | mk right₁ right₂ =>
          have right_parts := right_ih right_bst
          have right_subset :=
            raw_partition_between_subset above_low_bound below_high_bound right
          rw [right_eq] at right_parts right_subset
          constructor
          · exact right_parts.1
          · apply Raw.join_bst left_bst right_parts.2
            · exact left_lt
            · intro x hx
              exact right_gt x (right_subset.2 x hx)

def partition_between {X : OrderedType}
    (above_low_bound below_high_bound : X.elt → Bool) (s : t X) : t X × t X :=
  let p := raw_partition_between above_low_bound below_high_bound s.this
  let p_bst := raw_partition_between_bst
    above_low_bound below_high_bound s.this s.is_ok
  (⟨p.1, p_bst.1⟩, ⟨p.2, p_bst.2⟩)

def In_raw_partition_between_1Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.elt → Bool)
    (x : X.elt) (m : Raw.tree X.elt),
    Raw.In X x (raw_partition_between above_low_bound below_high_bound m).1 →
      Raw.In X x m

def In_raw_partition_between_2Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.elt → Bool)
    (x : X.elt) (m : Raw.tree X.elt),
    Raw.In X x (raw_partition_between above_low_bound below_high_bound m).2 →
      Raw.In X x m

def raw_partition_between_okStatement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.elt → Bool)
    (m : Raw.tree X.elt),
    Raw.bst X m →
      Raw.bst X (raw_partition_between above_low_bound below_high_bound m).1 ∧
        Raw.bst X (raw_partition_between above_low_bound below_high_bound m).2

def In_raw_partition_between_3Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.elt → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.elt) (m : Raw.tree X.elt),
      Raw.In X x (raw_partition_between above_low_bound below_high_bound m).1 →
        above_low_bound x = true ∧ below_high_bound x = true

def In_raw_partition_between_4Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.elt → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.elt) (m : Raw.tree X.elt),
      Raw.bst X m →
      Raw.In X x (raw_partition_between above_low_bound below_high_bound m).2 →
        above_low_bound x = false ∨ below_high_bound x = false

def In_raw_partition_between_5Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.elt → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.elt) (m : Raw.tree X.elt),
      Raw.bst X m → Raw.In X x m → above_low_bound x = true →
        below_high_bound x = true →
          Raw.In X x (raw_partition_between above_low_bound below_high_bound m).1

def In_raw_partition_between_6Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.elt → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.elt) (m : Raw.tree X.elt),
      Raw.bst X m → Raw.In X x m →
        (above_low_bound x = false ∨ below_high_bound x = false) →
          Raw.In X x (raw_partition_between above_low_bound below_high_bound m).2

def partition_between_iff_1Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.elt → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.elt) (s : t X),
      In X x (partition_between above_low_bound below_high_bound s).1 ↔
        In X x s ∧ above_low_bound x = true ∧ below_high_bound x = true

def partition_between_iff_2Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.elt → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.elt) (s : t X),
      In X x (partition_between above_low_bound below_high_bound s).2 ↔
        In X x s ∧ (above_low_bound x = false ∨ below_high_bound x = false)

end PARTITION_BETWEEN

end Make
end CompCert4Lean.Lib.FSetAVLplus
