import CompCert4Lean.Flocq.Core.Zaux

/-!
# Flocq integer digit counts

This module contains the executable surfaces selected from `Flocq.Core.Digits`.
Proof-heavy source declarations are represented by exact proposition descriptors
for the later proof-migration phase.
-/

namespace CompCert4Lean.Flocq.Core.Digits

abbrev Z := CompCert4Lean.Flocq.Core.Zaux.Z
abbrev positive := CompCert4Lean.Flocq.Core.Zaux.positive
abbrev radix := CompCert4Lean.Flocq.Core.Zaux.radix

abbrev Z0 : Z := CompCert4Lean.Flocq.Core.Zaux.Z0
abbrev Zone : Z := CompCert4Lean.Flocq.Core.Zaux.Zone
abbrev Ztwo : Z := CompCert4Lean.Flocq.Core.Zaux.Ztwo

abbrev Zpos := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
abbrev Zadd := CompCert4Lean.Flocq.Core.Zaux.Zadd
abbrev Zsub := CompCert4Lean.Flocq.Core.Zaux.Zsub
abbrev Zmul := CompCert4Lean.Flocq.Core.Zaux.Zmul
abbrev Zabs := CompCert4Lean.Flocq.Core.Zaux.Zabs
abbrev Zle := CompCert4Lean.Flocq.Core.Zaux.Zle
abbrev Zlt := CompCert4Lean.Flocq.Core.Zaux.Zlt
abbrev Zlt_bool := CompCert4Lean.Flocq.Core.Zaux.Zlt_bool
abbrev Zpower := CompCert4Lean.Flocq.Core.Zaux.Zpower
abbrev Zpower_nat := CompCert4Lean.Flocq.Core.Zaux.Zpower_nat
abbrev Z_of_nat := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
abbrev radix2 := CompCert4Lean.Flocq.Core.Zaux.radix2

abbrev digits2_pos (n : positive) : positive :=
  CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos n

abbrev Zdigits2 (n : Z) : Z :=
  CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.Zdigits2 n

def digits2_Pnat : positive → Nat
  | .xH => 0
  | .xO p => Nat.succ (digits2_Pnat p)
  | .xI p => Nat.succ (digits2_Pnat p)

def Zdigits_aux (beta : radix) (p nb pow : Z) : Nat → Z
  | 0 => nb
  | Nat.succ n =>
      if Zlt_bool p pow then
        nb
      else
        Zdigits_aux beta p (Zadd nb Zone) (Zmul (beta : Z) pow) n

def Zdigits (beta : radix) (n : Z) : Z :=
  match n with
  | .Z0 => Z0
  | .Zneg p => Zdigits_aux beta (Zpos p) Zone (beta : Z) (digits2_Pnat p)
  | .Zpos p => Zdigits_aux beta n Zone (beta : Z) (digits2_Pnat p)

/-! Exact source proposition descriptors for later proof migration. -/

def digits2_Pnat_correctStatement : Prop :=
  ∀ n : positive,
    let d := digits2_Pnat n
    Zle (Zpower_nat Ztwo d) (Zpos n) ∧
      Zlt (Zpos n) (Zpower_nat Ztwo (Nat.succ d))

def Zdigits_correctStatement : Prop :=
  ∀ (beta : radix) (n : Z),
    Zle (Zpower (beta : Z) (Zsub (Zdigits beta n) Zone)) (Zabs n) ∧
      Zlt (Zabs n) (Zpower (beta : Z) (Zdigits beta n))

def Zdigits_uniqueStatement : Prop :=
  ∀ (beta : radix) (n d : Z),
    (Zle (Zpower (beta : Z) (Zsub d Zone)) (Zabs n) ∧
      Zlt (Zabs n) (Zpower (beta : Z) d)) →
      Zdigits beta n = d

def Zdigits_absStatement : Prop :=
  ∀ (beta : radix) (n : Z), Zdigits beta (Zabs n) = Zdigits beta n

def Zdigits_gt_0Statement : Prop :=
  ∀ (beta : radix) (n : Z), n ≠ Z0 → Zlt Z0 (Zdigits beta n)

def Zpower_le_ZdigitsStatement : Prop :=
  ∀ (beta : radix) (e x : Z),
    Zlt e (Zdigits beta x) →
      Zle (Zpower (beta : Z) e) (Zabs x)

def Zdigits_le_ZpowerStatement : Prop :=
  ∀ (beta : radix) (e x : Z),
    Zlt (Zabs x) (Zpower (beta : Z) e) →
      Zle (Zdigits beta x) e

def Zpower_gt_ZdigitsStatement : Prop :=
  ∀ (beta : radix) (e x : Z),
    Zle (Zdigits beta x) e →
      Zlt (Zabs x) (Zpower (beta : Z) e)

def Zdigits_gt_ZpowerStatement : Prop :=
  ∀ (beta : radix) (e x : Z),
    Zle (Zpower (beta : Z) e) (Zabs x) →
      Zlt e (Zdigits beta x)

def Zdigits_mult_geStatement : Prop :=
  ∀ (beta : radix) (x y : Z),
    x ≠ Z0 → y ≠ Z0 →
      Zle
        (Zsub (Zadd (Zdigits beta x) (Zdigits beta y)) Zone)
        (Zdigits beta (Zmul x y))

def Z_of_nat_S_digits2_PnatStatement : Prop :=
  ∀ m : positive,
    Z_of_nat (Nat.succ (digits2_Pnat m)) = Zdigits radix2 (Zpos m)

def Zpos_digits2_posStatement : Prop :=
  ∀ m : positive, Zpos (digits2_pos m) = Zdigits radix2 (Zpos m)

def Zdigits2_ZdigitsStatement : Prop :=
  ∀ n : Z, Zdigits2 n = Zdigits radix2 n

end CompCert4Lean.Flocq.Core.Digits

namespace CompCert4Lean.Flocq.Core.Digits

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt

private theorem digits_intOfZ_of_nat (n : Nat) :
    intOfZ (ZArith.BinInt.Z.of_nat n) = Int.ofNat n := by
  unfold ZArith.BinInt.Z.of_nat
  exact intOfZ_zOfInt _

private theorem digits_intOfZ_power_nat (x : Z) (n : Nat) :
    intOfZ (Zpower_nat x n) = (intOfZ x) ^ n := by
  change intOfZ (ZArith.BinInt.Z.pow x (ZArith.BinInt.Z.of_nat n)) = _
  unfold ZArith.BinInt.Z.pow
  rw [digits_intOfZ_of_nat]
  split
  · next h => exact False.elim ((Int.not_lt_of_ge (Int.natCast_nonneg _)) h)
  · next h =>
      change intOfZ (zOfInt ((intOfZ x).pow n)) = (intOfZ x) ^ n
      exact intOfZ_zOfInt _

theorem digits2_Pnat_correct : digits2_Pnat_correctStatement := by
  intro n
  let d := digits2_Pnat n
  dsimp [d]
  induction n with
  | xH =>
      constructor
      · change intOfZ (Zpower_nat Ztwo 0) <= intOfZ (Zpos .xH)
        rw [digits_intOfZ_power_nat]
        simp [intOfZ, posToNat]
      · change intOfZ (Zpos .xH) < intOfZ (Zpower_nat Ztwo (Nat.succ 0))
        rw [digits_intOfZ_power_nat]
        simp [intOfZ, posToNat]
  | xI p ih =>
      have ih1 :
          intOfZ (Zpower_nat Ztwo (digits2_Pnat p)) <= intOfZ (Zpos p) := by
        exact ih.1
      have ih2 :
          intOfZ (Zpos p) < intOfZ (Zpower_nat Ztwo (Nat.succ (digits2_Pnat p))) := by
        exact ih.2
      rw [digits_intOfZ_power_nat] at ih1 ih2
      simp [intOfZ, posToNat] at ih1 ih2
      constructor
      · change intOfZ (Zpower_nat Ztwo (Nat.succ (digits2_Pnat p))) <=
          intOfZ (Zpos (.xI p))
        rw [digits_intOfZ_power_nat]
        simp [intOfZ, posToNat]
        rw [Int.pow_succ]
        omega
      · change intOfZ (Zpos (.xI p)) <
          intOfZ (Zpower_nat Ztwo (Nat.succ (Nat.succ (digits2_Pnat p))))
        rw [digits_intOfZ_power_nat]
        simp [intOfZ, posToNat]
        rw [Int.pow_succ, Int.pow_succ]
        omega
  | xO p ih =>
      have ih1 :
          intOfZ (Zpower_nat Ztwo (digits2_Pnat p)) <= intOfZ (Zpos p) := by
        exact ih.1
      have ih2 :
          intOfZ (Zpos p) < intOfZ (Zpower_nat Ztwo (Nat.succ (digits2_Pnat p))) := by
        exact ih.2
      rw [digits_intOfZ_power_nat] at ih1 ih2
      simp [intOfZ, posToNat] at ih1 ih2
      constructor
      · change intOfZ (Zpower_nat Ztwo (Nat.succ (digits2_Pnat p))) <=
          intOfZ (Zpos (.xO p))
        rw [digits_intOfZ_power_nat]
        simp [intOfZ, posToNat]
        rw [Int.pow_succ]
        omega
      · change intOfZ (Zpos (.xO p)) <
          intOfZ (Zpower_nat Ztwo (Nat.succ (Nat.succ (digits2_Pnat p))))
        rw [digits_intOfZ_power_nat]
        simp [intOfZ, posToNat]
        rw [Int.pow_succ, Int.pow_succ]
        omega

private theorem digits_Zabs_pos (p : positive) : Zabs (Zpos p) = Zpos p := by
  apply intOfZ_injective
  change intOfZ (zOfInt (Int.natAbs (Int.ofNat (posToNat p)))) =
    Int.ofNat (posToNat p)
  rw [intOfZ_zOfInt]
  exact Int.natAbs_of_nonneg (Int.natCast_nonneg _)

private theorem digits_Zabs_neg (p : positive) : Zabs (Zneg p) = Zpos p := by
  apply intOfZ_injective
  change intOfZ (zOfInt (Int.natAbs (-Int.ofNat (posToNat p)))) =
    Int.ofNat (posToNat p)
  rw [intOfZ_zOfInt]
  simp

theorem Zdigits_abs : Zdigits_absStatement := by
  intro beta n
  cases n
  · rfl
  · rw [digits_Zabs_pos]
  · rw [digits_Zabs_neg]
    rfl

end CompCert4Lean.Flocq.Core.Digits

namespace CompCert4Lean.Flocq.Core.Digits

private theorem digits_intOfZ_add_one_pos (nb : Z)
    (hnb : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ nb) :
    0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd nb Zone) := by
  simp only [Zadd,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ nb + 1
  omega

private theorem digits_Zdigits_aux_pos (beta : radix) (p nb pow : Z) :
    0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ nb →
      ∀ k : Nat, 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zdigits_aux beta p nb pow k) := by
  intro hnb k
  induction k generalizing nb pow with
  | zero => simpa [Zdigits_aux] using hnb
  | succ k ih =>
      simp only [Zdigits_aux]
      split
      · exact hnb
      · apply ih
        exact digits_intOfZ_add_one_pos nb hnb

theorem Zdigits_gt_0 : Zdigits_gt_0Statement := by
  intro beta n hn
  cases n with
  | Z0 => exact False.elim (hn rfl)
  | Zpos p =>
      change 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zdigits beta (.Zpos p))
      unfold Zdigits
      exact digits_Zdigits_aux_pos beta (.Zpos p) Zone (beta : Z)
        (by simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]) (digits2_Pnat p)
  | Zneg p =>
      change 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zdigits beta (.Zneg p))
      unfold Zdigits
      exact digits_Zdigits_aux_pos beta (.Zpos p) Zone (beta : Z)
        (by simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]) (digits2_Pnat p)

end CompCert4Lean.Flocq.Core.Digits
