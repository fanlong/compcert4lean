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

/- Lean cannot register the five source-named declarations directly: their
   source-shaped explicit dP/dQ arguments do not occur in the result and are
   not instance-implicit, so instance synthesis cannot infer them.  These
   low-priority adapters are the minimal compatibility endpoints; each only
   applies its source-named implementation, and Lean's core logical decisions
   retain priority. -/

instance (priority := 900) instDecidable_not (P : Prop)
    [dP : _root_.Decidable P] : _root_.Decidable (¬ P) :=
  Decidable_not P dP

instance (priority := 900) instDecidable_equiv (P Q : Prop)
    [dP : _root_.Decidable P] [dQ : _root_.Decidable Q] :
    _root_.Decidable (P ↔ Q) :=
  Decidable_equiv P Q dP dQ

instance (priority := 900) instDecidable_and (P Q : Prop)
    [dP : _root_.Decidable P] [dQ : _root_.Decidable Q] :
    _root_.Decidable (P ∧ Q) :=
  Decidable_and P Q dP dQ

instance (priority := 900) instDecidable_or (P Q : Prop)
    [dP : _root_.Decidable P] [dQ : _root_.Decidable Q] :
    _root_.Decidable (P ∨ Q) :=
  Decidable_or P Q dP dQ

instance (priority := 900) instDecidable_implies (P Q : Prop)
    [dP : _root_.Decidable P] [dQ : _root_.Decidable Q] :
    _root_.Decidable (P → Q) :=
  Decidable_implies P Q dP dQ

def Decidable_eq {A : Type}
    (eqdec : ∀ (x y : A),
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (¬ x = y))
    (x y : A) : _root_.Decidable (x = y) :=
  match eqdec x y with
  | .left h => .isTrue h
  | .right h => .isFalse h

instance (priority := 900) Decidable_eq_bool (x y : Bool) :
    _root_.Decidable (x = y) :=
  if h : x = y then .isTrue h else .isFalse h

instance (priority := 900) Decidable_eq_nat (x y : Nat) :
    _root_.Decidable (x = y) :=
  if h : x = y then .isTrue h else .isFalse h

instance (priority := 900) Decidable_eq_positive (x y : positive) :
    _root_.Decidable (x = y) :=
  if h : x = y then .isTrue h else .isFalse h

instance (priority := 900) Decidable_eq_Z (x y : Z) :
    _root_.Decidable (x = y) :=
  if h : x = y then .isTrue h else .isFalse h

/- The source divisibility decision reflects the equality
   [y = (y / x) * x].  The small integer lemma below exposes the one
   arithmetic fact needed to discharge the checked branches without using a
   proposition-level divisibility decider. -/

private theorem zdiv_eucl_mul_of_dvd (a b : Int) (h : b ∣ a) :
    (if b = 0 then 0 else if 0 < b then Int.ediv a b else
      let d := -b
      let q := Int.ediv a d
      let r := Int.emod a d
      if r = 0 then -q else -(q + 1)) * b = a := by
  by_cases hb0 : b = 0
  · subst b
    rcases h with ⟨k, hk⟩
    simp at hk
    subst a
    rfl
  · by_cases hbpos : 0 < b
    · simp only [if_neg hb0, if_pos hbpos]
      exact Int.ediv_mul_cancel h
    · have hbneg : b < 0 := by omega
      rcases h with ⟨k, hk⟩
      have hdvd : -b ∣ a := by
        refine ⟨-k, ?_⟩
        calc
          a = b * k := hk
          _ = (-b) * (-k) := (Int.neg_mul_neg b k).symm
      have hdmod : Int.emod a (-b) = 0 := Int.emod_eq_zero_of_dvd hdvd
      have hmul : Int.ediv a (-b) * (-b) = a := Int.ediv_mul_cancel hdvd
      simp only [if_neg hb0, if_neg hbpos, hdmod, if_pos]
      calc
        -(Int.ediv a (-b)) * b = -(Int.ediv a (-b) * b) := Int.neg_mul _ _
        _ = Int.ediv a (-b) * (-b) := (Int.mul_neg _ _).symm
        _ = a := hmul

private theorem intOfZ_div_mul_of_dvd (x y : Z) (h : intOfZ x ∣ intOfZ y) :
    intOfZ (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.div y x) x) = intOfZ y := by
  simp only [ZArith.BinInt.Z.mul, ZArith.BinInt.Z.div, intOfZ_zOfInt]
  change
    (if intOfZ x = 0 then 0 else
      if 0 < intOfZ x then Int.ediv (intOfZ y) (intOfZ x) else
        let d := -intOfZ x
        let q := Int.ediv (intOfZ y) d
        let r := Int.emod (intOfZ y) d
        if r = 0 then -q else -(q + 1)) * intOfZ x = intOfZ y
  exact zdiv_eucl_mul_of_dvd _ _ h

private theorem divide_of_eqb_true (x y : Z)
    (h : ZArith.BinInt.Z.eqb y
      (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.div y x) x) = true) :
    ZArith.BinInt.Z.divide x y := by
  have hy : y = ZArith.BinInt.Z.mul (ZArith.BinInt.Z.div y x) x :=
    @of_decide_eq_true _
      (Numbers.BinNums.instDecidableEqZ _ _) h
  refine ⟨ZArith.BinInt.Z.div y x, ?_⟩
  calc
    y = ZArith.BinInt.Z.mul (ZArith.BinInt.Z.div y x) x := hy
    _ = ZArith.BinInt.Z.mul x (ZArith.BinInt.Z.div y x) := by
      simp only [ZArith.BinInt.Z.mul]
      exact congrArg zOfInt (Int.mul_comm _ _)

private theorem eqb_true_of_divide (x y : Z)
    (h : ZArith.BinInt.Z.divide x y) :
    ZArith.BinInt.Z.eqb y
      (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.div y x) x) = true := by
  rcases h with ⟨k, hk⟩
  have hInt : intOfZ x ∣ intOfZ y := by
    refine ⟨intOfZ k, ?_⟩
    calc
      intOfZ y = intOfZ (ZArith.BinInt.Z.mul x k) := congrArg intOfZ hk
      _ = intOfZ x * intOfZ k := by
        simp only [ZArith.BinInt.Z.mul, intOfZ_zOfInt]
  have hmul : ZArith.BinInt.Z.mul (ZArith.BinInt.Z.div y x) x = y := by
    apply intOfZ_injective
    exact intOfZ_div_mul_of_dvd x y hInt
  exact @decide_eq_true _ (Numbers.BinNums.instDecidableEqZ _ _) hmul.symm

instance (priority := 1001) Decidable_le_Z (x y : Z) :
    _root_.Decidable (ZArith.BinInt.Z.le x y) :=
  decidableOfSumbool (ZArith.ZArith_dec.Z_le_dec x y)

instance (priority := 1001) Decidable_lt_Z (x y : Z) :
    _root_.Decidable (ZArith.BinInt.Z.lt x y) :=
  decidableOfSumbool (ZArith.ZArith_dec.Z_lt_dec x y)

instance (priority := 1000) Decidable_ge_Z (x y : Z) :
    _root_.Decidable (ZArith.BinInt.Z.ge x y) :=
  decidableOfSumbool (ZArith.ZArith_dec.Z_le_dec y x)

instance (priority := 1000) Decidable_gt_Z (x y : Z) :
    _root_.Decidable (ZArith.BinInt.Z.gt x y) :=
  decidableOfSumbool (ZArith.ZArith_dec.Z_lt_dec y x)

instance Decidable_divides (x y : Z) :
    _root_.Decidable (ZArith.BinInt.Z.divide x y) :=
  if h : ZArith.BinInt.Z.eqb y
      (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.div y x) x) = true then
    .isTrue (divide_of_eqb_true x y h)
  else
    .isFalse (fun hdiv => h (eqb_true_of_divide x y hdiv))

instance (priority := 1002) Decidable_forall_in_list {A : Type} (l : List A) (P : A → Prop)
    [dP : ∀ x : A, _root_.Decidable (P x)] :
    _root_.Decidable (∀ x : A, In x l → P x) :=
  match l with
  | [] =>
      .isTrue (by
        intro x hx
        exact (_root_.List.not_mem_nil hx).elim)
  | a :: l =>
      match dP a, Decidable_forall_in_list (dP := dP) l P with
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

instance (priority := 1002) Decidable_exists_in_list {A : Type} (l : List A) (P : A → Prop)
    [dP : ∀ x : A, _root_.Decidable (P x)] :
    _root_.Decidable (∃ x : A, In x l ∧ P x) :=
  match l with
  | [] =>
      .isFalse (by
        rintro ⟨x, hx, _⟩
        exact (_root_.List.not_mem_nil hx).elim)
  | a :: l =>
      match dP a, Decidable_exists_in_list (dP := dP) l P with
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
  Finite_elements : List T
  Finite_elements_spec : ∀ x : T, In x Finite_elements

export Finite (Finite_elements Finite_elements_spec)

instance (priority := 1001) Decidable_forall {T : Type} [fT : Finite T] (P : T → Prop)
    [dP : ∀ x : T, _root_.Decidable (P x)] :
    _root_.Decidable (∀ x : T, P x) :=
  match Decidable_forall_in_list (dP := dP)
      (Finite.Finite_elements (self := fT)) P with
  | .isTrue h =>
      .isTrue (by intro x; exact h x (Finite.Finite_elements_spec (self := fT) x))
  | .isFalse h =>
      .isFalse (by intro hall; apply h; intro x _; exact hall x)

instance (priority := 1001) Decidable_exists {T : Type} [fT : Finite T] (P : T → Prop)
    [dP : ∀ x : T, _root_.Decidable (P x)] :
    _root_.Decidable (∃ x : T, P x) :=
  match Decidable_exists_in_list (dP := dP)
      (Finite.Finite_elements (self := fT)) P with
  | .isTrue h =>
      .isTrue (by
        rcases h with ⟨x, _, hpx⟩
        exact ⟨x, hpx⟩)
  | .isFalse h =>
      .isFalse (by
        rintro ⟨x, hpx⟩
        exact h ⟨x, Finite.Finite_elements_spec (self := fT) x, hpx⟩)

instance Finite_bool : Finite Bool where
  Finite_elements := [false, true]
  Finite_elements_spec := by
    intro x
    cases x with
    | false => exact _root_.List.Mem.head _
    | true => exact _root_.List.Mem.tail false (_root_.List.Mem.head _)

instance Finite_pair {A B : Type} [fA : Finite A] [fB : Finite B] :
    Finite (A × B) where
  Finite_elements :=
    CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.list_prod
      (Finite.Finite_elements (self := fA)) (Finite.Finite_elements (self := fB))
  Finite_elements_spec := by
    intro x
    rcases x with ⟨a, b⟩
    exact
      CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_prod
        (Finite.Finite_elements (self := fA)) (Finite.Finite_elements (self := fB)) a b
        (Finite.Finite_elements_spec (self := fA) a)
        (Finite.Finite_elements_spec (self := fB) b)

instance Finite_option {A : Type} [fA : Finite A] : Finite (Option A) where
  Finite_elements :=
    none :: CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.map
      some (Finite.Finite_elements (self := fA))
  Finite_elements_spec := by
    intro x
    cases x with
    | none => exact _root_.List.Mem.head _
    | some a =>
        exact _root_.List.Mem.tail none
          (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_map
            some (Finite.Finite_elements (self := fA)) a
            (Finite.Finite_elements_spec (self := fA) a))

end CompCert4Lean.Lib.Decidableplus
