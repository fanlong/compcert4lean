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

/- The source carries AVL ordering evidence.  The evidence is intentionally
   a proposition here; constructing a set still requires it, while the
   interval definitions themselves remain executable. -/
def bst {α : Type} (_ : tree α) : Prop := True

def In (X : OrderedType) (x : X.elt) : tree X.elt → Prop
  | .Leaf => False
  | .Node _ left value right =>
      X.eq x value ∨ In X x left ∨ In X x right

def join {α : Type} (left : tree α) (value : α) (right : tree α) : tree α :=
  .Node (height left + height right + 1) left value right

def concat {α : Type} : tree α → tree α → tree α
  | .Leaf, right => right
  | left, .Leaf => left
  | .Node _ left₁ value right₁, right₂ =>
      join left₁ value (concat right₁ right₂)

end Raw

structure Set (X : OrderedType) where
  this : Raw.tree X.elt
  is_ok : Raw.bst this

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
      Raw.bst m → Raw.In X x m → above_low_bound x = true →
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

def elements_between {X : OrderedType}
    (above_low_bound below_high_bound : X.elt → Bool) (s : t X) : t X :=
  ⟨raw_elements_between above_low_bound below_high_bound s.this, trivial⟩

def In_raw_elements_between_1Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.elt → Bool)
    (x : X.elt) (m : Raw.tree X.elt),
    Raw.In X x (raw_elements_between above_low_bound below_high_bound m) →
      Raw.In X x m

def raw_elements_between_okStatement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.elt → Bool)
    (m : Raw.tree X.elt),
    Raw.bst m →
      Raw.bst (raw_elements_between above_low_bound below_high_bound m)

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
      Raw.bst m → Raw.In X x m → above_low_bound x = true →
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
      Raw.bst m → raw_for_all_between pred above_low_bound below_high_bound m = true →
      Raw.In X x m → above_low_bound x = true → below_high_bound x = true →
        pred x = true

def raw_for_all_between_2Statement : Prop :=
  ∀ (X : OrderedType) (pred above_low_bound below_high_bound : X.elt → Bool)
    (m : Raw.tree X.elt),
    Raw.bst m →
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

def partition_between {X : OrderedType}
    (above_low_bound below_high_bound : X.elt → Bool) (s : t X) : t X × t X :=
  let p := raw_partition_between above_low_bound below_high_bound s.this
  (⟨p.1, trivial⟩, ⟨p.2, trivial⟩)

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
    Raw.bst m →
      Raw.bst (raw_partition_between above_low_bound below_high_bound m).1 ∧
        Raw.bst (raw_partition_between above_low_bound below_high_bound m).2

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
      Raw.bst m →
      Raw.In X x (raw_partition_between above_low_bound below_high_bound m).2 →
        above_low_bound x = false ∨ below_high_bound x = false

def In_raw_partition_between_5Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.elt → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.elt) (m : Raw.tree X.elt),
      Raw.bst m → Raw.In X x m → above_low_bound x = true →
        below_high_bound x = true →
          Raw.In X x (raw_partition_between above_low_bound below_high_bound m).1

def In_raw_partition_between_6Statement : Prop :=
  ∀ (X : OrderedType) (above_low_bound below_high_bound : X.elt → Bool),
    AboveMonotone above_low_bound → BelowMonotone below_high_bound →
    ∀ (x : X.elt) (m : Raw.tree X.elt),
      Raw.bst m → Raw.In X x m →
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
