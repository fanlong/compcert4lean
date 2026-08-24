import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.Ordered
import CompCert4Lean.Lib.Coqlib

/-!
# Decidable propositions and finite types

This module translates the definition-bearing surface of
`compcert.lib.Decidableplus`.  Source-named declarations use the canonical
Rocq `DecidableClass.Decidable` Boolean-reflection carrier.  Native Lean
decision procedures are only secondary implementation aids.
-/

namespace CompCert4Lean.Lib.Decidableplus

open CompCert4Lean.Foundation.Logic
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Ordered.Rocq.Coq.Classes.DecidableClass

private abbrev RocqDecidable (P : Prop) :=
  CompCert4Lean.Foundation.Ordered.Rocq.Coq.Classes.DecidableClass.Decidable P

private theorem rocqTrue {P : Prop} (d : RocqDecidable P)
    (h : d.Decidable_witness = true) : P := d.Decidable_spec.mp h

private theorem rocqFalse {P : Prop} (d : RocqDecidable P)
    (h : d.Decidable_witness = false) : ¬ P := by
  intro hp
  have ht := d.Decidable_spec.mpr hp
  rw [h] at ht
  cases ht

private def decidableOfSumbool {P : Prop}
    (d : CompCert4Lean.Foundation.Logic.Support.Sumbool P (¬ P)) :
    _root_.Decidable P :=
  match d with
  | .left h => .isTrue h
  | .right h => .isFalse h

def Decidable_not (P : Prop) (dP : RocqDecidable P) : RocqDecidable (¬ P) where
  Decidable_witness := !dP.Decidable_witness
  Decidable_spec := by
    cases hP : dP.Decidable_witness with
    | false =>
        simp only [Bool.not_false, Bool.true_eq, true_iff]
        intro hp
        have : dP.Decidable_witness = true := dP.Decidable_spec.mpr hp
        simp [hP] at this
    | true =>
        simp only [Bool.not_true, Bool.false_eq_true, false_iff]
        intro hnP
        exact hnP (rocqTrue dP hP)

def Decidable_equiv (P Q : Prop) (dP : RocqDecidable P)
    (dQ : RocqDecidable Q) : RocqDecidable (P ↔ Q) where
  Decidable_witness :=
    match dP.Decidable_witness, dQ.Decidable_witness with
    | false, false => true
    | false, true => false
    | true, false => false
    | true, true => true
  Decidable_spec := by
    cases hP : dP.Decidable_witness <;> cases hQ : dQ.Decidable_witness
    · simp only [hP, hQ, true_iff]
      exact ⟨fun hp => (rocqFalse dP hP hp).elim,
        fun hq => (rocqFalse dQ hQ hq).elim⟩
    · simp only [hP, hQ, Bool.false_eq_true, false_iff]
      intro h
      exact rocqFalse dP hP (h.mpr (rocqTrue dQ hQ))
    · simp only [hP, hQ, Bool.false_eq_true, false_iff]
      intro h
      exact rocqFalse dQ hQ (h.mp (rocqTrue dP hP))
    · simp only [hP, hQ, true_iff]
      exact ⟨fun _ => rocqTrue dQ hQ, fun _ => rocqTrue dP hP⟩

def Decidable_and (P Q : Prop) (dP : RocqDecidable P)
    (dQ : RocqDecidable Q) : RocqDecidable (P ∧ Q) where
  Decidable_witness := dP.Decidable_witness && dQ.Decidable_witness
  Decidable_spec := by
    rw [Bool.and_eq_true]
    constructor
    · rintro ⟨hp, hq⟩
      exact ⟨dP.Decidable_spec.mp hp, dQ.Decidable_spec.mp hq⟩
    · rintro ⟨hp, hq⟩
      exact ⟨dP.Decidable_spec.mpr hp, dQ.Decidable_spec.mpr hq⟩

def Decidable_or (P Q : Prop) (dP : RocqDecidable P)
    (dQ : RocqDecidable Q) : RocqDecidable (P ∨ Q) where
  Decidable_witness := dP.Decidable_witness || dQ.Decidable_witness
  Decidable_spec := by
    rw [Bool.or_eq_true]
    constructor
    · intro h
      exact h.elim (Or.inl ∘ dP.Decidable_spec.mp) (Or.inr ∘ dQ.Decidable_spec.mp)
    · intro h
      exact h.elim (Or.inl ∘ dP.Decidable_spec.mpr) (Or.inr ∘ dQ.Decidable_spec.mpr)

def Decidable_implies (P Q : Prop) (dP : RocqDecidable P)
    (dQ : RocqDecidable Q) : RocqDecidable (P → Q) where
  Decidable_witness :=
    match dP.Decidable_witness with
    | false => true
    | true => dQ.Decidable_witness
  Decidable_spec := by
    cases hP : dP.Decidable_witness with
    | false =>
        simp only [hP, true_iff]
        intro hp
        exact (rocqFalse dP hP hp).elim
    | true =>
        simp only [hP]
        constructor
        · intro hq _
          exact dQ.Decidable_spec.mp hq
        · intro hpq
          exact dQ.Decidable_spec.mpr (hpq (dP.Decidable_spec.mp hP))

instance instDecidable_not (P : Prop) [dP : RocqDecidable P] : RocqDecidable (¬ P) :=
  Decidable_not P dP

instance instDecidable_equiv (P Q : Prop) [dP : RocqDecidable P]
    [dQ : RocqDecidable Q] : RocqDecidable (P ↔ Q) :=
  Decidable_equiv P Q dP dQ

instance instDecidable_and (P Q : Prop) [dP : RocqDecidable P]
    [dQ : RocqDecidable Q] : RocqDecidable (P ∧ Q) :=
  Decidable_and P Q dP dQ

instance instDecidable_or (P Q : Prop) [dP : RocqDecidable P]
    [dQ : RocqDecidable Q] : RocqDecidable (P ∨ Q) :=
  Decidable_or P Q dP dQ

instance instDecidable_implies (P Q : Prop) [dP : RocqDecidable P]
    [dQ : RocqDecidable Q] : RocqDecidable (P → Q) :=
  Decidable_implies P Q dP dQ

def Decidable_eq {A : Type}
    (eqdec : ∀ (x y : A),
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (¬ x = y))
    (x y : A) : RocqDecidable (x = y) where
  Decidable_witness := CompCert4Lean.Lib.Coqlib.proj_sumbool (eqdec x y)
  Decidable_spec := by
    cases h : eqdec x y with
    | left hxy => simp [CompCert4Lean.Lib.Coqlib.proj_sumbool, hxy]
    | right hxy => simp [CompCert4Lean.Lib.Coqlib.proj_sumbool, hxy]

instance Decidable_eq_bool (x y : Bool) : RocqDecidable (x = y) where
  Decidable_witness := CompCert4Lean.Foundation.Logic.Rocq.Coq.Bool.Bool.eqb x y
  Decidable_spec := by
    by_cases h : x = y <;>
      simp [CompCert4Lean.Foundation.Logic.Rocq.Coq.Bool.Bool.eqb, h]

instance Decidable_eq_nat (x y : Nat) : RocqDecidable (x = y) where
  Decidable_witness :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.Arith.PeanoNat.Nat.eqb x y
  Decidable_spec := by
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.Arith.PeanoNat.Nat.eqb]

instance Decidable_eq_positive (x y : positive) : RocqDecidable (x = y) where
  Decidable_witness :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.eqb x y
  Decidable_spec := by
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.eqb]

instance Decidable_eq_Z (x y : Z) : RocqDecidable (x = y) where
  Decidable_witness := ZArith.BinInt.Z.eqb x y
  Decidable_spec := by simp [ZArith.BinInt.Z.eqb]

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

instance Decidable_le_Z (x y : Z) : RocqDecidable (ZArith.BinInt.Z.le x y) where
  Decidable_witness := ZArith.BinInt.Z.leb x y
  Decidable_spec := by
    by_cases h : intOfZ x ≤ intOfZ y <;>
      simp [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.le, h]

instance Decidable_lt_Z (x y : Z) : RocqDecidable (ZArith.BinInt.Z.lt x y) where
  Decidable_witness := ZArith.BinInt.Z.ltb x y
  Decidable_spec := by
    by_cases h : intOfZ x < intOfZ y <;>
      simp [ZArith.BinInt.Z.ltb, ZArith.BinInt.Z.lt, h]

instance Decidable_ge_Z (x y : Z) : RocqDecidable (ZArith.BinInt.Z.ge x y) where
  Decidable_witness := ZArith.BinInt.Z.geb x y
  Decidable_spec := by
    by_cases h : intOfZ y ≤ intOfZ x <;>
      simp [ZArith.BinInt.Z.geb, ZArith.BinInt.Z.ge, h]

instance Decidable_gt_Z (x y : Z) : RocqDecidable (ZArith.BinInt.Z.gt x y) where
  Decidable_witness := ZArith.BinInt.Z.gtb x y
  Decidable_spec := by
    by_cases h : intOfZ y < intOfZ x <;>
      simp [ZArith.BinInt.Z.gtb, ZArith.BinInt.Z.gt, ZArith.BinInt.Z.lt, h]

instance Decidable_divides (x y : Z) : RocqDecidable (ZArith.BinInt.Z.divide x y) where
  Decidable_witness := ZArith.BinInt.Z.eqb y
    (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.div y x) x)
  Decidable_spec := ⟨divide_of_eqb_true x y, eqb_true_of_divide x y⟩

private theorem forallb_decidable_spec (A : Type) (l : List A) (P : A → Prop)
    (dP : ∀ x : A, RocqDecidable (P x)) :
    forallb (fun x => (dP x).Decidable_witness) l = true ↔
      ∀ x : A, In x l → P x := by
  induction l with
  | nil =>
      simp only [forallb, Bool.true_eq, true_iff]
      intro x hx
      cases hx
  | cons a l ih =>
      simp only [forallb, Bool.and_eq_true, ih, (dP a).Decidable_spec]
      constructor
      · rintro ⟨ha, hl⟩ x hx
        rcases _root_.List.mem_cons.mp hx with hxa | hxl
        · simpa [hxa] using ha
        · exact hl x hxl
      · intro hall
        exact ⟨hall a (_root_.List.Mem.head l),
          fun x hx => hall x (_root_.List.Mem.tail a hx)⟩

private theorem existsb_decidable_spec (A : Type) (l : List A) (P : A → Prop)
    (dP : ∀ x : A, RocqDecidable (P x)) :
    existsb (fun x => (dP x).Decidable_witness) l = true ↔
      ∃ x : A, In x l ∧ P x := by
  induction l with
  | nil =>
      simp only [existsb, Bool.false_eq_true, false_iff]
      rintro ⟨x, hx, _⟩
      cases hx
  | cons a l ih =>
      simp only [existsb, Bool.or_eq_true, ih, (dP a).Decidable_spec]
      constructor
      · intro h
        rcases h with ha | ⟨x, hx, hpx⟩
        · exact ⟨a, _root_.List.Mem.head l, ha⟩
        · exact ⟨x, _root_.List.Mem.tail a hx, hpx⟩
      · rintro ⟨x, hx, hpx⟩
        rcases _root_.List.mem_cons.mp hx with hxa | hxl
        · exact Or.inl (hxa ▸ hpx)
        · exact Or.inr ⟨x, hxl, hpx⟩

def Decidable_forall_in_list (A : Type) (l : List A) (P : A → Prop)
    (dP : ∀ x : A, RocqDecidable (P x)) :
    RocqDecidable (∀ x : A, In x l → P x) where
  Decidable_witness := forallb (fun x => (dP x).Decidable_witness) l
  Decidable_spec := forallb_decidable_spec A l P dP

def Decidable_exists_in_list (A : Type) (l : List A) (P : A → Prop)
    (dP : ∀ x : A, RocqDecidable (P x)) :
    RocqDecidable (∃ x : A, In x l ∧ P x) where
  Decidable_witness := existsb (fun x => (dP x).Decidable_witness) l
  Decidable_spec := existsb_decidable_spec A l P dP

instance instDecidable_forall_in_list {A : Type} (l : List A) (P : A → Prop)
    [dP : ∀ x : A, RocqDecidable (P x)] :
    RocqDecidable (∀ x : A, In x l → P x) :=
  Decidable_forall_in_list A l P dP

instance instDecidable_exists_in_list {A : Type} (l : List A) (P : A → Prop)
    [dP : ∀ x : A, RocqDecidable (P x)] :
    RocqDecidable (∃ x : A, In x l ∧ P x) :=
  Decidable_exists_in_list A l P dP

class Finite (T : Type) where
  Finite_elements : List T
  Finite_elements_spec : ∀ x : T, In x Finite_elements

export Finite (Finite_elements Finite_elements_spec)

def Decidable_forall (T : Type) (fT : Finite T) (P : T → Prop)
    (dP : ∀ x : T, RocqDecidable (P x)) : RocqDecidable (∀ x : T, P x) where
  Decidable_witness := forallb (fun x => (dP x).Decidable_witness)
    (Finite.Finite_elements (self := fT))
  Decidable_spec := by
    rw [forallb_decidable_spec T (Finite.Finite_elements (self := fT)) P dP]
    constructor
    · intro h x
      exact h x (Finite.Finite_elements_spec (self := fT) x)
    · intro h x _
      exact h x

def Decidable_exists (T : Type) (fT : Finite T) (P : T → Prop)
    (dP : ∀ x : T, RocqDecidable (P x)) : RocqDecidable (∃ x : T, P x) where
  Decidable_witness := existsb (fun x => (dP x).Decidable_witness)
    (Finite.Finite_elements (self := fT))
  Decidable_spec := by
    rw [existsb_decidable_spec T (Finite.Finite_elements (self := fT)) P dP]
    constructor
    · rintro ⟨x, _, hpx⟩
      exact ⟨x, hpx⟩
    · rintro ⟨x, hpx⟩
      exact ⟨x, Finite.Finite_elements_spec (self := fT) x, hpx⟩

instance instDecidable_forall {T : Type} [fT : Finite T] (P : T → Prop)
    [dP : ∀ x : T, RocqDecidable (P x)] : RocqDecidable (∀ x : T, P x) :=
  Decidable_forall T fT P dP

instance instDecidable_exists {T : Type} [fT : Finite T] (P : T → Prop)
    [dP : ∀ x : T, RocqDecidable (P x)] : RocqDecidable (∃ x : T, P x) :=
  Decidable_exists T fT P dP

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
