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

namespace OrderedType

def ImportMarker : Type := Unit

end OrderedType
end Structures.OrderedType

end Rocq.Coq
end CompCert4Lean.Foundation.Ordered
