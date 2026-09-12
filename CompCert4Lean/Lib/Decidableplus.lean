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

universe u v

open CompCert4Lean.Foundation.Logic
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Ordered.Rocq.Coq.Classes.DecidableClass

/- The foundation list facade predates the universe-polymorphic source API and
   exposes these Boolean traversals only at `Type 0`.  Keep the source
   computation local here so the public declarations can retain their full
   carrier universes without changing the provider-owned file. -/
private def forallbU {A : Type u} (f : A → Bool) (l : List A) : Bool :=
  match l with
  | [] => true
  | x :: xs => f x && forallbU f xs

private def existsbU {A : Type u} (f : A → Bool) (l : List A) : Bool :=
  match l with
  | [] => false
  | x :: xs => f x || existsbU f xs

private def listProdU {A : Type u} {B : Type v} (l : List A) (l' : List B) : List (A × B) :=
  l.flatMap (fun x => l'.map (fun y => (x, y)))

private abbrev RocqDecidable (P : Prop) :=
  CompCert4Lean.Foundation.Ordered.Rocq.Coq.Classes.DecidableClass.Decidable P

private theorem rocqTrue {P : Prop} (d : RocqDecidable P)
    (h : d.witness = true) : P := d.spec.mp h

private theorem rocqFalse {P : Prop} (d : RocqDecidable P)
    (h : d.witness = false) : ¬ P := by
  intro hp
  have ht := d.spec.mpr hp
  rw [h] at ht
  cases ht

private def decidableOfSumbool {P : Prop}
    (d : CompCert4Lean.Foundation.Logic.Support.Sumbool P (¬ P)) :
    _root_.Decidable P :=
  match d with
  | .left h => .isTrue h
  | .right h => .isFalse h

def Decidable_not (P : Prop) (dP : RocqDecidable P) : RocqDecidable (¬ P) where
  witness := !dP.witness
  spec := by
    cases hP : dP.witness with
    | false =>
        simp only [Bool.not_false, Bool.true_eq, true_iff]
        intro hp
        have : dP.witness = true := dP.spec.mpr hp
        simp [hP] at this
    | true =>
        simp only [Bool.not_true, Bool.false_eq_true, false_iff]
        intro hnP
        exact hnP (rocqTrue dP hP)

def Decidable_equiv (P Q : Prop) (dP : RocqDecidable P)
    (dQ : RocqDecidable Q) : RocqDecidable (P ↔ Q) where
  witness :=
    match dP.witness, dQ.witness with
    | false, false => true
    | false, true => false
    | true, false => false
    | true, true => true
  spec := by
    cases hP : dP.witness <;> cases hQ : dQ.witness
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
  witness := dP.witness && dQ.witness
  spec := by
    rw [Bool.and_eq_true]
    constructor
    · rintro ⟨hp, hq⟩
      exact ⟨dP.spec.mp hp, dQ.spec.mp hq⟩
    · rintro ⟨hp, hq⟩
      exact ⟨dP.spec.mpr hp, dQ.spec.mpr hq⟩

def Decidable_or (P Q : Prop) (dP : RocqDecidable P)
    (dQ : RocqDecidable Q) : RocqDecidable (P ∨ Q) where
  witness := dP.witness || dQ.witness
  spec := by
    rw [Bool.or_eq_true]
    constructor
    · intro h
      exact h.elim (Or.inl ∘ dP.spec.mp) (Or.inr ∘ dQ.spec.mp)
    · intro h
      exact h.elim (Or.inl ∘ dP.spec.mpr) (Or.inr ∘ dQ.spec.mpr)

def Decidable_implies (P Q : Prop) (dP : RocqDecidable P)
    (dQ : RocqDecidable Q) : RocqDecidable (P → Q) where
  witness :=
    match dP.witness with
    | false => true
    | true => dQ.witness
  spec := by
    cases hP : dP.witness with
    | false =>
        simp only [hP, true_iff]
        intro hp
        exact (rocqFalse dP hP hp).elim
    | true =>
        simp only [hP]
        constructor
        · intro hq _
          exact dQ.spec.mp hq
        · intro hpq
          exact dQ.spec.mpr (hpq (dP.spec.mp hP))

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

def Decidable_eq {A : Type u}
    (eqdec : ∀ (x y : A),
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (¬ x = y))
    (x y : A) : RocqDecidable (x = y) where
  witness := CompCert4Lean.Lib.Coqlib.proj_sumbool (eqdec x y)
  spec := by
    cases h : eqdec x y with
    | left hxy => simp [CompCert4Lean.Lib.Coqlib.proj_sumbool, hxy]
    | right hxy => simp [CompCert4Lean.Lib.Coqlib.proj_sumbool, hxy]

instance Decidable_eq_bool (x y : Bool) : RocqDecidable (x = y) where
  witness := CompCert4Lean.Foundation.Logic.Rocq.Coq.Bool.Bool.eqb x y
  spec := by
    by_cases h : x = y <;>
      simp [CompCert4Lean.Foundation.Logic.Rocq.Coq.Bool.Bool.eqb, h]

instance Decidable_eq_nat (x y : Nat) : RocqDecidable (x = y) where
  witness :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.Arith.PeanoNat.Nat.eqb x y
  spec := by
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.Arith.PeanoNat.Nat.eqb]

instance Decidable_eq_positive (x y : positive) : RocqDecidable (x = y) where
  witness :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.eqb x y
  spec := by
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.eqb]

instance Decidable_eq_Z (x y : Z) : RocqDecidable (x = y) where
  witness := ZArith.BinInt.Z.eqb x y
  spec := by simp [ZArith.BinInt.Z.eqb]

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
  witness := ZArith.BinInt.Z.leb x y
  spec := by
    by_cases h : intOfZ x ≤ intOfZ y <;>
      simp [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.le, h]

instance Decidable_lt_Z (x y : Z) : RocqDecidable (ZArith.BinInt.Z.lt x y) where
  witness := ZArith.BinInt.Z.ltb x y
  spec := by
    by_cases h : intOfZ x < intOfZ y <;>
      simp [ZArith.BinInt.Z.ltb, ZArith.BinInt.Z.lt, h]

instance Decidable_ge_Z (x y : Z) : RocqDecidable (ZArith.BinInt.Z.ge x y) where
  witness := ZArith.BinInt.Z.geb x y
  spec := by
    by_cases h : intOfZ y ≤ intOfZ x <;>
      simp [ZArith.BinInt.Z.geb, ZArith.BinInt.Z.ge, h]

instance Decidable_gt_Z (x y : Z) : RocqDecidable (ZArith.BinInt.Z.gt x y) where
  witness := ZArith.BinInt.Z.gtb x y
  spec := by
    by_cases h : intOfZ y < intOfZ x <;>
      simp [ZArith.BinInt.Z.gtb, ZArith.BinInt.Z.gt, ZArith.BinInt.Z.lt, h]

instance Decidable_divides (x y : Z) : RocqDecidable (ZArith.BinInt.Z.divide x y) where
  witness := ZArith.BinInt.Z.eqb y
    (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.div y x) x)
  spec := ⟨divide_of_eqb_true x y, eqb_true_of_divide x y⟩

private theorem forallb_decidable_spec (A : Type u) (l : List A) (P : A → Prop)
    (dP : ∀ x : A, RocqDecidable (P x)) :
    forallbU (fun x => (dP x).witness) l = true ↔
      ∀ x : A, _root_.List.Mem x l → P x := by
  induction l with
  | nil =>
      simp only [forallbU, Bool.true_eq, true_iff]
      intro x hx
      cases hx
  | cons a l ih =>
      simp only [forallbU, Bool.and_eq_true, ih, (dP a).spec]
      constructor
      · rintro ⟨ha, hl⟩ x hx
        rcases _root_.List.mem_cons.mp hx with hxa | hxl
        · simpa [hxa] using ha
        · exact hl x hxl
      · intro hall
        exact ⟨hall a (_root_.List.Mem.head l),
          fun x hx => hall x (_root_.List.Mem.tail a hx)⟩

private theorem existsb_decidable_spec (A : Type u) (l : List A) (P : A → Prop)
    (dP : ∀ x : A, RocqDecidable (P x)) :
    existsbU (fun x => (dP x).witness) l = true ↔
      ∃ x : A, _root_.List.Mem x l ∧ P x := by
  induction l with
  | nil =>
      simp only [existsbU, Bool.false_eq_true, false_iff]
      rintro ⟨x, hx, _⟩
      cases hx
  | cons a l ih =>
      simp only [existsbU, Bool.or_eq_true, ih, (dP a).spec]
      constructor
      · intro h
        rcases h with ha | ⟨x, hx, hpx⟩
        · exact ⟨a, _root_.List.Mem.head l, ha⟩
        · exact ⟨x, _root_.List.Mem.tail a hx, hpx⟩
      · rintro ⟨x, hx, hpx⟩
        rcases _root_.List.mem_cons.mp hx with hxa | hxl
        · exact Or.inl (hxa ▸ hpx)
        · exact Or.inr ⟨x, hxl, hpx⟩

def Decidable_forall_in_list (A : Type u) (l : List A) (P : A → Prop)
    (dP : ∀ x : A, RocqDecidable (P x)) :
    RocqDecidable (∀ x : A, _root_.List.Mem x l → P x) where
  witness := forallbU (fun x => (dP x).witness) l
  spec := forallb_decidable_spec A l P dP

def Decidable_exists_in_list (A : Type u) (l : List A) (P : A → Prop)
    (dP : ∀ x : A, RocqDecidable (P x)) :
    RocqDecidable (∃ x : A, _root_.List.Mem x l ∧ P x) where
  witness := existsbU (fun x => (dP x).witness) l
  spec := existsb_decidable_spec A l P dP

instance instDecidable_forall_in_list {A : Type u} (l : List A) (P : A → Prop)
    [dP : ∀ x : A, RocqDecidable (P x)] :
    RocqDecidable (∀ x : A, _root_.List.Mem x l → P x) :=
  Decidable_forall_in_list A l P dP

instance instDecidable_exists_in_list {A : Type u} (l : List A) (P : A → Prop)
    [dP : ∀ x : A, RocqDecidable (P x)] :
    RocqDecidable (∃ x : A, _root_.List.Mem x l ∧ P x) :=
  Decidable_exists_in_list A l P dP

class Finite (T : Type u) where
  Finite_elements : List T
  Finite_elements_spec : ∀ x : T, _root_.List.Mem x Finite_elements

export Finite (Finite_elements Finite_elements_spec)

/- Lean makes a structure parameter implicit in its generated constructor
   whenever the fields determine it.  Keep that implementation detail behind
   the source-named constructor endpoint, whose carrier and fields are explicit
   in the same order as Rocq's `Build_Finite`. -/
def Build_Finite (T : Type u) (Finite_elements : List T)
    (Finite_elements_spec : ∀ x : T, _root_.List.Mem x Finite_elements) : Finite T :=
  Finite.mk Finite_elements Finite_elements_spec

def Decidable_forall (T : Type u) (fT : Finite T) (P : T → Prop)
    (dP : ∀ x : T, RocqDecidable (P x)) : RocqDecidable (∀ x : T, P x) where
  witness := forallbU (fun x => (dP x).witness)
    (Finite.Finite_elements (self := fT))
  spec := by
    rw [forallb_decidable_spec T (Finite.Finite_elements (self := fT)) P dP]
    constructor
    · intro h x
      exact h x (Finite.Finite_elements_spec (self := fT) x)
    · intro h x _
      exact h x

def Decidable_exists (T : Type u) (fT : Finite T) (P : T → Prop)
    (dP : ∀ x : T, RocqDecidable (P x)) : RocqDecidable (∃ x : T, P x) where
  witness := existsbU (fun x => (dP x).witness)
    (Finite.Finite_elements (self := fT))
  spec := by
    rw [existsb_decidable_spec T (Finite.Finite_elements (self := fT)) P dP]
    constructor
    · rintro ⟨x, _, hpx⟩
      exact ⟨x, hpx⟩
    · rintro ⟨x, hpx⟩
      exact ⟨x, Finite.Finite_elements_spec (self := fT) x, hpx⟩

instance instDecidable_forall {T : Type u} [fT : Finite T] (P : T → Prop)
    [dP : ∀ x : T, RocqDecidable (P x)] : RocqDecidable (∀ x : T, P x) :=
  Decidable_forall T fT P dP

instance instDecidable_exists {T : Type u} [fT : Finite T] (P : T → Prop)
    [dP : ∀ x : T, RocqDecidable (P x)] : RocqDecidable (∃ x : T, P x) :=
  Decidable_exists T fT P dP

instance Finite_bool : Finite Bool :=
  Build_Finite Bool [false, true] (by
    intro x
    cases x with
    | false => exact _root_.List.Mem.head _
    | true => exact _root_.List.Mem.tail false (_root_.List.Mem.head _))

def Finite_pair (A : Type u) (B : Type v) (fA : Finite A) (fB : Finite B) :
    Finite (A × B) :=
  Build_Finite (A × B)
    (listProdU (Finite.Finite_elements (self := fA))
      (Finite.Finite_elements (self := fB))) (by
    intro x
    rcases x with ⟨a, b⟩
    change (a, b) ∈
      ((Finite.Finite_elements (self := fA)).flatMap
        (fun x => (Finite.Finite_elements (self := fB)).map (fun y => (x, y))))
    rw [_root_.List.mem_flatMap]
    exact ⟨a, Finite.Finite_elements_spec (self := fA) a,
      _root_.List.mem_map.mpr
        ⟨b, Finite.Finite_elements_spec (self := fB) b, rfl⟩⟩)

instance instFinite_pair {A : Type u} {B : Type v} [fA : Finite A] [fB : Finite B] :
    Finite (A × B) :=
  Finite_pair A B fA fB

def Finite_option (A : Type u) (fA : Finite A) : Finite (Option A) :=
  Build_Finite (Option A)
    (none :: _root_.List.map some (Finite.Finite_elements (self := fA))) (by
    intro x
    cases x with
    | none => exact _root_.List.Mem.head _
    | some a =>
        exact _root_.List.Mem.tail none
          (_root_.List.mem_map.mpr
            ⟨a, Finite.Finite_elements_spec (self := fA) a, rfl⟩))

instance instFinite_option {A : Type u} [fA : Finite A] : Finite (Option A) :=
  Finite_option A fA

/-! Exact proposition descriptors for the 22 opaque obligations generated by
Rocq `Program`.  The computational definitions above retain their inline Lean
proofs; these source-named descriptors keep each generated kernel obligation
separate for proof-inventory accounting. -/

def Decidable_not_obligation_1Statement : Prop :=
  ∀ (P : Prop) (dP : RocqDecidable P),
    (Decidable_not P dP).witness = true ↔ ¬ P

def Decidable_equiv_obligation_1Statement : Prop :=
  ∀ (P Q : Prop) (dP : RocqDecidable P) (dQ : RocqDecidable Q),
    (Decidable_equiv P Q dP dQ).witness = true ↔ (P ↔ Q)

def Decidable_and_obligation_1Statement : Prop :=
  ∀ (P Q : Prop) (dP : RocqDecidable P) (dQ : RocqDecidable Q),
    (Decidable_and P Q dP dQ).witness = true ↔ P ∧ Q

def Decidable_or_obligation_1Statement : Prop :=
  ∀ (P Q : Prop) (dP : RocqDecidable P) (dQ : RocqDecidable Q),
    (Decidable_or P Q dP dQ).witness = true ↔ P ∨ Q

def Decidable_implies_obligation_1Statement : Prop :=
  ∀ (P Q : Prop) (dP : RocqDecidable P) (dQ : RocqDecidable Q),
    (Decidable_implies P Q dP dQ).witness = true ↔ (P → Q)

def Decidable_eq_obligation_1Statement : Prop :=
  ∀ (A : Type u)
    (eqdec : ∀ x y : A,
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (¬ x = y))
    (x y : A),
    (Decidable_eq eqdec x y).witness = true ↔ x = y

def Decidable_eq_bool_obligation_1Statement : Prop :=
  ∀ x y : Bool, (Decidable_eq_bool x y).witness = true ↔ x = y

def Decidable_eq_nat_obligation_1Statement : Prop :=
  ∀ x y : Nat, (Decidable_eq_nat x y).witness = true ↔ x = y

def Decidable_eq_positive_obligation_1Statement : Prop :=
  ∀ x y : positive, (Decidable_eq_positive x y).witness = true ↔ x = y

def Decidable_eq_Z_obligation_1Statement : Prop :=
  ∀ x y : Z, (Decidable_eq_Z x y).witness = true ↔ x = y

def Decidable_le_Z_obligation_1Statement : Prop :=
  ∀ x y : Z,
    (Decidable_le_Z x y).witness = true ↔ ZArith.BinInt.Z.le x y

def Decidable_lt_Z_obligation_1Statement : Prop :=
  ∀ x y : Z,
    (Decidable_lt_Z x y).witness = true ↔ ZArith.BinInt.Z.lt x y

def Decidable_ge_Z_obligation_1Statement : Prop :=
  ∀ x y : Z,
    (Decidable_ge_Z x y).witness = true ↔ ZArith.BinInt.Z.ge x y

def Decidable_gt_Z_obligation_1Statement : Prop :=
  ∀ x y : Z,
    (Decidable_gt_Z x y).witness = true ↔ ZArith.BinInt.Z.gt x y

def Decidable_divides_obligation_1Statement : Prop :=
  ∀ x y : Z,
    (Decidable_divides x y).witness = true ↔ ZArith.BinInt.Z.divide x y

def Decidable_forall_in_list_obligation_1Statement : Prop :=
  ∀ (A : Type u) (l : List A) (P : A → Prop)
    (dP : ∀ x : A, RocqDecidable (P x)),
    (Decidable_forall_in_list A l P dP).witness = true ↔
      ∀ x : A, _root_.List.Mem x l → P x

def Decidable_exists_in_list_obligation_1Statement : Prop :=
  ∀ (A : Type u) (l : List A) (P : A → Prop)
    (dP : ∀ x : A, RocqDecidable (P x)),
    (Decidable_exists_in_list A l P dP).witness = true ↔
      ∃ x : A, _root_.List.Mem x l ∧ P x

def Decidable_forall_obligation_1Statement : Prop :=
  ∀ (T : Type u) (fT : Finite T) (P : T → Prop)
    (dP : ∀ x : T, RocqDecidable (P x)),
    (Decidable_forall T fT P dP).witness = true ↔ ∀ x : T, P x

def Decidable_exists_obligation_1Statement : Prop :=
  ∀ (T : Type u) (fT : Finite T) (P : T → Prop)
    (dP : ∀ x : T, RocqDecidable (P x)),
    (Decidable_exists T fT P dP).witness = true ↔ ∃ x : T, P x

def Finite_bool_obligation_1Statement : Prop :=
  ∀ x : Bool,
    _root_.List.Mem x (Finite.Finite_elements (self := Finite_bool))

def Finite_pair_obligation_1Statement : Prop :=
  ∀ (A : Type u) (B : Type v) (fA : Finite A) (fB : Finite B) (x : A × B),
    _root_.List.Mem x
      (Finite.Finite_elements (self := Finite_pair A B fA fB))

def Finite_option_obligation_1Statement : Prop :=
  ∀ (A : Type u) (fA : Finite A) (x : Option A),
    _root_.List.Mem x
      (Finite.Finite_elements (self := Finite_option A fA))

end CompCert4Lean.Lib.Decidableplus

namespace CompCert4Lean.Lib.Decidableplus

theorem Decidable_not_obligation_1 : Decidable_not_obligation_1Statement := by
  intro P dP
  exact (Decidable_not P dP).spec

theorem Decidable_equiv_obligation_1 : Decidable_equiv_obligation_1Statement := by
  intro P Q dP dQ
  exact (Decidable_equiv P Q dP dQ).spec

theorem Decidable_and_obligation_1 : Decidable_and_obligation_1Statement := by
  intro P Q dP dQ
  exact (Decidable_and P Q dP dQ).spec

theorem Decidable_or_obligation_1 : Decidable_or_obligation_1Statement := by
  intro P Q dP dQ
  exact (Decidable_or P Q dP dQ).spec

end CompCert4Lean.Lib.Decidableplus

namespace CompCert4Lean.Lib.Decidableplus

theorem Decidable_implies_obligation_1 : Decidable_implies_obligation_1Statement := by
  intro P Q dP dQ
  exact (Decidable_implies P Q dP dQ).spec

theorem Decidable_eq_obligation_1 : Decidable_eq_obligation_1Statement := by
  intro A eqdec x y
  exact (Decidable_eq eqdec x y).spec

theorem Decidable_eq_bool_obligation_1 : Decidable_eq_bool_obligation_1Statement := by
  intro x y
  exact (Decidable_eq_bool x y).spec

theorem Decidable_eq_nat_obligation_1 : Decidable_eq_nat_obligation_1Statement := by
  intro x y
  exact (Decidable_eq_nat x y).spec

end CompCert4Lean.Lib.Decidableplus

namespace CompCert4Lean.Lib.Decidableplus

theorem Decidable_eq_positive_obligation_1 : Decidable_eq_positive_obligation_1Statement := by
  intro x y
  exact (Decidable_eq_positive x y).spec

theorem Decidable_eq_Z_obligation_1 : Decidable_eq_Z_obligation_1Statement := by
  intro x y
  exact (Decidable_eq_Z x y).spec

theorem Decidable_le_Z_obligation_1 : Decidable_le_Z_obligation_1Statement := by
  intro x y
  exact (Decidable_le_Z x y).spec

theorem Decidable_lt_Z_obligation_1 : Decidable_lt_Z_obligation_1Statement := by
  intro x y
  exact (Decidable_lt_Z x y).spec

end CompCert4Lean.Lib.Decidableplus

namespace CompCert4Lean.Lib.Decidableplus

theorem Decidable_ge_Z_obligation_1 : Decidable_ge_Z_obligation_1Statement := by
  intro x y
  exact (Decidable_ge_Z x y).spec

theorem Decidable_gt_Z_obligation_1 : Decidable_gt_Z_obligation_1Statement := by
  intro x y
  exact (Decidable_gt_Z x y).spec

theorem Decidable_divides_obligation_1 : Decidable_divides_obligation_1Statement := by
  intro x y
  exact (Decidable_divides x y).spec

theorem Decidable_forall_in_list_obligation_1 :
    Decidable_forall_in_list_obligation_1Statement := by
  intro A l P dP
  exact (Decidable_forall_in_list A l P dP).spec

end CompCert4Lean.Lib.Decidableplus

namespace CompCert4Lean.Lib.Decidableplus

theorem Decidable_exists_in_list_obligation_1 :
    Decidable_exists_in_list_obligation_1Statement := by
  intro A l P dP
  exact (Decidable_exists_in_list A l P dP).spec

theorem Decidable_forall_obligation_1 :
    Decidable_forall_obligation_1Statement := by
  intro T fT P dP
  exact (Decidable_forall T fT P dP).spec

theorem Decidable_exists_obligation_1 :
    Decidable_exists_obligation_1Statement := by
  intro T fT P dP
  exact (Decidable_exists T fT P dP).spec

theorem Finite_bool_obligation_1 : Finite_bool_obligation_1Statement := by
  intro x
  cases x with
  | false => exact _root_.List.Mem.head _
  | true => exact _root_.List.Mem.tail false (_root_.List.Mem.head _)

end CompCert4Lean.Lib.Decidableplus

namespace CompCert4Lean.Lib.Decidableplus

theorem Finite_pair_obligation_1 : Finite_pair_obligation_1Statement := by
  intro A B fA fB x
  rcases x with ⟨a, b⟩
  change (a, b) ∈
    ((Finite.Finite_elements (self := fA)).flatMap
      (fun x => (Finite.Finite_elements (self := fB)).map (fun y => (x, y))))
  rw [_root_.List.mem_flatMap]
  exact ⟨a, Finite.Finite_elements_spec (self := fA) a,
    _root_.List.mem_map.mpr
      ⟨b, Finite.Finite_elements_spec (self := fB) b, rfl⟩⟩

theorem Finite_option_obligation_1 : Finite_option_obligation_1Statement := by
  intro A fA x
  cases x with
  | none => exact _root_.List.Mem.head _
  | some a =>
      exact _root_.List.Mem.tail none
        (_root_.List.mem_map.mpr
          ⟨a, Finite.Finite_elements_spec (self := fA) a, rfl⟩)

end CompCert4Lean.Lib.Decidableplus
