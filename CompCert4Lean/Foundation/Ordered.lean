import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers

/-!
# Rocq ordered-container and relation compatibility surface

This module provides the consumer-scoped Rocq standard-library identities
owned by the ordered foundation provider.  Native Lean decision procedures,
relations, and list permutations are reused where their observations agree;
the source's proof-carrying comparison type is represented directly.
-/

namespace CompCert4Lean.Foundation.Ordered
namespace Rocq.Coq

namespace Classes.DecidableClass

class Decidable (P : Prop) where
  witness : Bool
  spec : witness = true ↔ P

def Decidable_witness {P : Prop} {H : Decidable P} : Bool := H.witness

def Decidable_spec {P : Prop} {H : Decidable P} :
    @Decidable_witness P H = true ↔ P := H.spec

def Decidable_complete_altStatement : Prop :=
  ∀ (P : Prop) (H : Decidable P),
    @Decidable_witness P H = false → ¬ P

def Decidable_completeStatement : Prop :=
  ∀ (P : Prop) (H : Decidable P),
    P → @Decidable_witness P H = true

def Decidable_sound_altStatement : Prop :=
  ∀ (P : Prop) (H : Decidable P),
    (¬ P) → @Decidable_witness P H = false

def Decidable_soundStatement : Prop :=
  ∀ (P : Prop) (H : Decidable P),
    @Decidable_witness P H = true → P

end Classes.DecidableClass

namespace FSets.FSetAVL.Make

def ImportMarker : Type := Unit

end FSets.FSetAVL.Make

namespace Relations.Relation_Operators

inductive clos_trans : (A : Type) → (A → A → Prop) → A → A → Prop where
  | t_step (A : Type) (R : A → A → Prop) (x y : A) :
      R x y → clos_trans A R x y
  | t_trans (A : Type) (R : A → A → Prop) (x y z : A) :
      clos_trans A R x y → clos_trans A R y z → clos_trans A R x z

export clos_trans (t_step t_trans)

end Relations.Relation_Operators

namespace Sorting.Sorted

inductive LocallySorted {A : Type} (R : A → A → Prop) : List A → Prop where
  | LSorted_nil : LocallySorted R []
  | LSorted_cons1 (a : A) : LocallySorted R [a]
  | LSorted_consn (a b : A) (l : List A) :
      LocallySorted R (b :: l) → R a b → LocallySorted R (a :: b :: l)

export LocallySorted (LSorted_nil LSorted_cons1 LSorted_consn)

inductive HdRel {A : Type} (R : A → A → Prop) (a : A) : List A → Prop where
  | nil : HdRel R a []
  | cons (b : A) (l : List A) : R a b → HdRel R a (b :: l)

abbrev HdRel_nil {A : Type} (R : A → A → Prop) (a : A) : HdRel R a [] :=
  HdRel.nil

abbrev HdRel_cons {A : Type} (R : A → A → Prop) (a b : A) (l : List A)
    (rel : R a b) : HdRel R a (b :: l) :=
  HdRel.cons b l rel

def HdRel_ind {A : Type} {R : A → A → Prop} {a : A}
    (P : List A → Prop)
    (nilCase : P [])
    (consCase : ∀ (b : A) (l : List A), R a b → P (b :: l))
    {l : List A} (hdRel : HdRel R a l) : P l := by
  cases hdRel with
  | nil => exact nilCase
  | cons b l rel => exact consCase b l rel

inductive Sorted {A : Type} (R : A → A → Prop) : List A → Prop where
  | nil : Sorted R []
  | cons {a : A} {l : List A} :
      Sorted R l → HdRel R a l → Sorted R (a :: l)

abbrev Sorted_nil {A : Type} (R : A → A → Prop) : Sorted R [] :=
  Sorted.nil

abbrev Sorted_cons {A : Type} {R : A → A → Prop} {a : A} {l : List A}
    (sorted : Sorted R l) (hdRel : HdRel R a l) : Sorted R (a :: l) :=
  Sorted.cons sorted hdRel

def Sorted_ind {A : Type} {R : A → A → Prop}
    (P : List A → Prop)
    (nilCase : P [])
    (consCase : ∀ (a : A) (l : List A),
      Sorted R l → P l → HdRel R a l → P (a :: l))
    {l : List A} (sorted : Sorted R l) : P l := by
  induction sorted with
  | nil => exact nilCase
  | @cons a l sorted hdRel ih => exact consCase a l sorted ih hdRel

theorem HdRel_inv {A : Type} {R : A → A → Prop}
    {a b : A} {l : List A} (hdRel : HdRel R a (b :: l)) : R a b := by
  cases hdRel with
  | cons _ _ rel => exact rel

theorem Sorted_inv {A : Type} {R : A → A → Prop}
    {a : A} {l : List A} (sorted : Sorted R (a :: l)) :
    Sorted R l ∧ HdRel R a l := by
  cases sorted with
  | cons sorted hdRel => exact ⟨sorted, hdRel⟩

inductive StronglySorted {A : Type} (R : A → A → Prop) : List A → Prop where
  | SSorted_nil : StronglySorted R []
  | SSorted_cons (a : A) (l : List A) :
      StronglySorted R l →
      _root_.CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.Forall (R a) l →
      StronglySorted R (a :: l)

export StronglySorted (SSorted_nil SSorted_cons)

noncomputable opaque Sorted_rect {A : Type} {R : A → A → Prop}
    (P : List A → Type)
    (nilCase : P [])
    (consCase : ∀ (a : A) (l : List A),
      Sorted R l → P l → HdRel R a l → P (a :: l))
    {l : List A} (sorted : Sorted R l) : P l := by
  induction l with
  | nil => exact nilCase
  | cons a l ih =>
      exact consCase a l (Sorted_inv sorted).1 (ih (Sorted_inv sorted).1)
        (Sorted_inv sorted).2

end Sorting.Sorted

namespace Sorting.Permutation

inductive Permutation : {A : Type} → List A → List A → Prop where
  | perm_nil (A : Type) : @Permutation A [] []
  | perm_skip {A : Type} (x : A) {l l' : List A} :
      @Permutation A l l' → @Permutation A (x :: l) (x :: l')
  | perm_swap {A : Type} (x y : A) (l : List A) :
      @Permutation A (y :: x :: l) (x :: y :: l)
  | perm_trans {A : Type} {l l' l'' : List A} :
      @Permutation A l l' → @Permutation A l' l'' → @Permutation A l l''

export Permutation (perm_nil perm_skip perm_swap perm_trans)

def Permutation_inStatement : Prop :=
  ∀ {A : Type} {l l' : List A} (x : A),
    Permutation l l' →
    _root_.CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.In x l →
    _root_.CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.In x l'

def Permutation_mapStatement : Prop :=
  ∀ {A B : Type} (f : A → B) {l l' : List A},
    Permutation l l' →
    Permutation
      (_root_.CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.map f l)
      (_root_.CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.map f l')

def Permutation_symStatement : Prop :=
  ∀ {A : Type} {l l' : List A},
    Permutation l l' → Permutation l' l

end Sorting.Permutation

namespace Structures.OrderedType

inductive Compare {X : Type} (lt eq : X → X → Prop) (x y : X) : Type where
  | LT (h : lt x y)
  | EQ (h : eq x y)
  | GT (h : lt y x)

export Compare (LT EQ GT)

/- `OrderedType.v` gives its legacy module type the same name as the file.
   Keep the canonical source-facing record at that exact identity so provider
   consumers do not have to invent a namespace-only substitute. -/
structure OrderedType where
  t : Type
  eq : t → t → Prop
  lt : t → t → Prop
  eq_refl : ∀ x : t, eq x x
  eq_sym : ∀ x y : t, eq x y → eq y x
  eq_trans : ∀ x y z : t, eq x y → eq y z → eq x z
  lt_trans : ∀ x y z : t, lt x y → lt y z → lt x z
  lt_not_eq : ∀ x y : t, lt x y → ¬ eq x y
  compare : ∀ x y : t, Compare lt eq x y
  eq_dec : ∀ x y : t,
    _root_.CompCert4Lean.Foundation.Logic.Support.Sumbool
      (eq x y) (¬ eq x y)

namespace OrderedType

def ImportMarker : Type := Unit

end OrderedType

/- Compatibility spelling retained for already-authored provider clients. -/
abbrev OrderedTypeSpec := OrderedType

end Structures.OrderedType

end Rocq.Coq
end CompCert4Lean.Foundation.Ordered

namespace CompCert4Lean.Foundation.Ordered
namespace Rocq.Coq.Classes.DecidableClass

theorem Decidable_sound : Decidable_soundStatement := by
  intro P H hw
  exact (Decidable_spec (P := P) (H := H)).mp hw

theorem Decidable_complete : Decidable_completeStatement := by
  intro P H hp
  exact (Decidable_spec (P := P) (H := H)).mpr hp

theorem Decidable_sound_alt : Decidable_sound_altStatement := by
  intro P H hnp
  cases h : @Decidable_witness P H with
  | false => rfl
  | true =>
      exact False.elim (hnp ((Decidable_spec (P := P) (H := H)).mp h))

theorem Decidable_complete_alt : Decidable_complete_altStatement := by
  intro P H hw hP
  have ht : @Decidable_witness P H = true :=
    (Decidable_spec (P := P) (H := H)).mpr hP
  rw [hw] at ht
  cases ht

end Rocq.Coq.Classes.DecidableClass
end CompCert4Lean.Foundation.Ordered
