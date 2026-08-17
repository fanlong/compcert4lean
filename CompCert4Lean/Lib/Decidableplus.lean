import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.Ordered

/-!
# Decidable propositions and finite types

This module translates the definition-bearing surface of
`compcert.lib.Decidableplus`.  Lean's checked `Decidable` type is used as the
proof-carrying decision carrier; the source-facing finite-type projections and
list membership observations retain their mapped names.
-/

namespace CompCert4Lean.Lib.Decidableplus

open CompCert4Lean.Foundation.Logic
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private def decidableOfSumbool {P : Prop}
    (d : CompCert4Lean.Foundation.Logic.Support.Sumbool P (¬ P)) :
    _root_.Decidable P :=
  match d with
  | .left h => .isTrue h
  | .right h => .isFalse h

def Decidable_not (P : Prop) (dP : _root_.Decidable P) : _root_.Decidable (¬ P) :=
  match dP with
  | .isTrue h => .isFalse (fun hn => hn h)
  | .isFalse h => .isTrue h

def Decidable_equiv (P Q : Prop) (dP : _root_.Decidable P)
    (dQ : _root_.Decidable Q) : _root_.Decidable (P ↔ Q) :=
  match dP, dQ with
  | .isTrue hp, .isTrue hq =>
      .isTrue ⟨fun _ => hq, fun _ => hp⟩
  | .isTrue hp, .isFalse hnq =>
      .isFalse (fun h => hnq (h.mp hp))
  | .isFalse hnp, .isTrue hq =>
      .isFalse (fun h => hnp (h.mpr hq))
  | .isFalse hnp, .isFalse hnq =>
      .isTrue ⟨fun hp => (hnp hp).elim, fun hq => (hnq hq).elim⟩

def Decidable_and (P Q : Prop) (dP : _root_.Decidable P)
    (dQ : _root_.Decidable Q) : _root_.Decidable (P ∧ Q) :=
  match dP, dQ with
  | .isTrue hp, .isTrue hq => .isTrue ⟨hp, hq⟩
  | .isFalse hnp, _ => .isFalse (fun h => hnp h.1)
  | _, .isFalse hnq => .isFalse (fun h => hnq h.2)

def Decidable_or (P Q : Prop) (dP : _root_.Decidable P)
    (dQ : _root_.Decidable Q) : _root_.Decidable (P ∨ Q) :=
  match dP, dQ with
  | .isTrue hp, _ => .isTrue (Or.inl hp)
  | _, .isTrue hq => .isTrue (Or.inr hq)
  | .isFalse hnp, .isFalse hnq =>
      .isFalse (fun h => h.elim hnp hnq)

def Decidable_implies (P Q : Prop) (dP : _root_.Decidable P)
    (dQ : _root_.Decidable Q) : _root_.Decidable (P → Q) :=
  match dP, dQ with
  | .isTrue _, .isTrue hq => .isTrue (fun _ => hq)
  | .isTrue hp, .isFalse hnq => .isFalse (fun h => hnq (h hp))
  | .isFalse hnp, _ => .isTrue (fun hp => (hnp hp).elim)

def Decidable_eq {A : Type}
    (eqdec : ∀ (x y : A),
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (¬ x = y))
    (x y : A) : _root_.Decidable (x = y) :=
  match eqdec x y with
  | .left h => .isTrue h
  | .right h => .isFalse h

def Decidable_eq_bool (x y : Bool) : _root_.Decidable (x = y) :=
  if h : x = y then .isTrue h else .isFalse h

def Decidable_eq_nat (x y : Nat) : _root_.Decidable (x = y) :=
  if h : x = y then .isTrue h else .isFalse h

def Decidable_eq_positive (x y : positive) : _root_.Decidable (x = y) :=
  if h : x = y then .isTrue h else .isFalse h

def Decidable_eq_Z (x y : Z) : _root_.Decidable (x = y) :=
  if h : x = y then .isTrue h else .isFalse h

def Decidable_le_Z (x y : Z) :
    _root_.Decidable (ZArith.BinInt.Z.le x y) :=
  decidableOfSumbool (ZArith.ZArith_dec.Z_le_dec x y)

def Decidable_lt_Z (x y : Z) :
    _root_.Decidable (ZArith.BinInt.Z.lt x y) :=
  decidableOfSumbool (ZArith.ZArith_dec.Z_lt_dec x y)

def Decidable_ge_Z (x y : Z) :
    _root_.Decidable (ZArith.BinInt.Z.ge x y) :=
  decidableOfSumbool (ZArith.ZArith_dec.Z_le_dec y x)

def Decidable_gt_Z (x y : Z) :
    _root_.Decidable (ZArith.BinInt.Z.gt x y) :=
  decidableOfSumbool (ZArith.ZArith_dec.Z_lt_dec y x)

noncomputable def Decidable_divides (x y : Z) :
    _root_.Decidable (ZArith.BinInt.Z.divide x y) := by
  classical
  exact Classical.propDecidable _

def Decidable_forall_in_list {A : Type} (l : List A) (P : A → Prop)
    (dP : ∀ x : A, _root_.Decidable (P x)) :
    _root_.Decidable (∀ x : A, In x l → P x) :=
  match l with
  | [] =>
      .isTrue (by
        intro x hx
        exact (_root_.List.not_mem_nil hx).elim)
  | a :: l =>
      match dP a, Decidable_forall_in_list l P dP with
      | .isTrue ha, .isTrue hl =>
          .isTrue (by
            intro x hx
            cases (_root_.List.mem_cons.mp hx) with
            | inl hxa => simpa [hxa] using ha
            | inr htail => exact hl x htail)
      | .isFalse hna, _ =>
          .isFalse (by
            intro h
            exact hna (h a (_root_.List.Mem.head l)))
      | _, .isFalse hnl =>
          .isFalse (by
            intro h
            apply hnl
            intro x hx
            exact h x (_root_.List.Mem.tail a hx))

def Decidable_exists_in_list {A : Type} (l : List A) (P : A → Prop)
    (dP : ∀ x : A, _root_.Decidable (P x)) :
    _root_.Decidable (∃ x : A, In x l ∧ P x) :=
  match l with
  | [] =>
      .isFalse (by
        rintro ⟨x, hx, _⟩
        exact (_root_.List.not_mem_nil hx).elim)
  | a :: l =>
      match dP a, Decidable_exists_in_list l P dP with
      | .isTrue ha, _ =>
          .isTrue ⟨a, _root_.List.Mem.head l, ha⟩
      | .isFalse hna, .isTrue hl =>
          .isTrue (by
            rcases hl with ⟨x, hx, hpx⟩
            exact ⟨x, _root_.List.Mem.tail a hx, hpx⟩)
      | .isFalse hna, .isFalse hnl =>
          .isFalse (by
            rintro ⟨x, hx, hpx⟩
            cases (_root_.List.mem_cons.mp hx) with
            | inl hxa => exact hna (hxa ▸ hpx)
            | inr htail => exact hnl ⟨x, htail, hpx⟩)

class Finite (T : Type) where
  elements : List T
  elements_spec : ∀ x : T, In x elements

def Finite_elements {T : Type} (fT : Finite T) : List T := fT.elements

def Finite_elements_spec {T : Type} (fT : Finite T) :
    ∀ x : T, In x (Finite_elements fT) :=
  fT.elements_spec

def Decidable_forall {T : Type} (fT : Finite T) (P : T → Prop)
    (dP : ∀ x : T, _root_.Decidable (P x)) :
    _root_.Decidable (∀ x : T, P x) :=
  match Decidable_forall_in_list (Finite_elements fT) P dP with
  | .isTrue h =>
      .isTrue (by intro x; exact h x (Finite_elements_spec fT x))
  | .isFalse h =>
      .isFalse (by intro hall; apply h; intro x _; exact hall x)

def Decidable_exists {T : Type} (fT : Finite T) (P : T → Prop)
    (dP : ∀ x : T, _root_.Decidable (P x)) :
    _root_.Decidable (∃ x : T, P x) :=
  match Decidable_exists_in_list (Finite_elements fT) P dP with
  | .isTrue h =>
      .isTrue (by
        rcases h with ⟨x, _, hpx⟩
        exact ⟨x, hpx⟩)
  | .isFalse h =>
      .isFalse (by
        rintro ⟨x, hpx⟩
        exact h ⟨x, Finite_elements_spec fT x, hpx⟩)

instance Finite_bool : Finite Bool where
  elements := [false, true]
  elements_spec := by
    intro x
    cases x with
    | false => exact _root_.List.Mem.head _
    | true => exact _root_.List.Mem.tail false (_root_.List.Mem.head _)

instance Finite_pair {A B : Type} [fA : Finite A] [fB : Finite B] :
    Finite (A × B) where
  elements :=
    CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.list_prod
      (Finite_elements fA) (Finite_elements fB)
  elements_spec := by
    intro x
    rcases x with ⟨a, b⟩
    exact
      CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_prod
        (Finite_elements fA) (Finite_elements fB) a b
        (Finite_elements_spec fA a) (Finite_elements_spec fB b)

instance Finite_option {A : Type} [fA : Finite A] : Finite (Option A) where
  elements :=
    none :: CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.map
      some (Finite_elements fA)
  elements_spec := by
    intro x
    cases x with
    | none => exact _root_.List.Mem.head _
    | some a =>
        exact _root_.List.Mem.tail none
          (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_map
            some (Finite_elements fA) a (Finite_elements_spec fA a))

end CompCert4Lean.Lib.Decidableplus
