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

abbrev Decidable (P : Prop) := _root_.Decidable P

def Decidable_witness {P : Prop} (H : Decidable P) : Bool :=
  match H with
  | .isTrue _ => true
  | .isFalse _ => false

def Decidable_complete_altStatement : Prop :=
  ∀ (P : Prop) (H : Decidable P),
    Decidable_witness H = false → ¬ P

def Decidable_completeStatement : Prop :=
  ∀ (P : Prop) (H : Decidable P),
    P → Decidable_witness H = true

def Decidable_sound_altStatement : Prop :=
  ∀ (P : Prop) (H : Decidable P),
    (¬ P) → Decidable_witness H = false

def Decidable_soundStatement : Prop :=
  ∀ (P : Prop) (H : Decidable P),
    Decidable_witness H = true → P

end Classes.DecidableClass

namespace FSets.FSetAVL.Make

def ImportMarker : Type := Unit

end FSets.FSetAVL.Make

namespace Relations.Relation_Operators

abbrev clos_trans (A : Type) (R : A → A → Prop) (x y : A) : Prop :=
  Relation.TransGen R x y

abbrev t_step (A : Type) (R : A → A → Prop) (x y : A)
    (h : R x y) : clos_trans A R x y :=
  Relation.TransGen.single h

abbrev t_trans (A : Type) (R : A → A → Prop) (x y z : A)
    (hxy : clos_trans A R x y) (hyz : clos_trans A R y z) :
    clos_trans A R x z :=
  Relation.TransGen.trans hxy hyz

end Relations.Relation_Operators

namespace Sorting.Sorted

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

abbrev Permutation {A : Type} (l l' : List A) : Prop :=
  List.Perm l l'

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
  | lt (h : lt x y)
  | eq (h : eq x y)
  | gt (h : lt y x)

abbrev LT {X : Type} {lt eq : X → X → Prop} {x y : X}
    (h : lt x y) : Compare lt eq x y :=
  Compare.lt h

abbrev EQ {X : Type} {lt eq : X → X → Prop} {x y : X}
    (h : eq x y) : Compare lt eq x y :=
  Compare.eq h

abbrev GT {X : Type} {lt eq : X → X → Prop} {x y : X}
    (h : lt y x) : Compare lt eq x y :=
  Compare.gt h

/- `OrderedType.v` gives its legacy module type the same name as the file.
   Keep the record name distinct from this namespace, and expose the
   source-facing name as a reducible alias below. -/
structure OrderedTypeSpec where
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

/- `CompCert4Lean.Lib.FSetAVLplus.OrderedType` is currently a consumer-local
   record using `elt`, Lean's `Decidable`, and no `compare` field.  Its later
   migration should make that name an alias of this provider, update the
   projections, and supply the proof-carrying comparison rather than retain a
   duplicate record. -/
abbrev OrderedType := OrderedTypeSpec

end Structures.OrderedType

end Rocq.Coq
end CompCert4Lean.Foundation.Ordered
