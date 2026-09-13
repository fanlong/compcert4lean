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
namespace CompCert4Lean.Flocq.Core.Digits
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt
private theorem digits_int_pow_mono (b : Int) (hb : 1 ≤ b) : ∀ {m n : Nat}, m ≤ n → b ^ m ≤ b ^ n := by
  intro m n hmn
  induction n with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      exact Int.le_refl _
  | succ n ih =>
      by_cases heq : m = Nat.succ n
      · subst m
        exact Int.le_refl _
      · have hmlt : m < Nat.succ n := Nat.lt_of_le_of_ne hmn heq
        have hmle : m ≤ n := Nat.le_of_lt_succ hmlt
        have hbn : 0 ≤ b ^ n := Int.pow_nonneg (by omega)
        have hstep : b ^ n ≤ b ^ n * b := by
          have hh := Int.mul_le_mul_of_nonneg_left hb hbn
          simpa using hh
        rw [Int.pow_succ]
        exact Int.le_trans (ih hmle) hstep

private theorem digits_power_le_of_exp_lt
    (beta : radix) (b : Int) (hb : 1 ≤ b)
    (e : Z) (j : Nat) (p : Int)
    (he : intOfZ e < Int.ofNat j)
    (hj : 1 ≤ j)
    (hlower : b ^ (j - 1) ≤ p)
    (hbrel : intOfZ (beta : Z) = b) :
    intOfZ (Zpower (beta : Z) e) ≤ p := by
  cases e with
  | Z0 =>
      have hmono : b ^ 0 ≤ b ^ (j - 1) := digits_int_pow_mono b hb (Nat.zero_le _)
      have hpow : b ^ 0 = 1 := by simp
      have h1 : (1 : Int) ≤ p := by
        rw [← hpow]
        exact Int.le_trans hmono hlower
      change intOfZ (Zpower (beta : Z) Z0) ≤ p
      change intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow (beta : Z) Z0) ≤ p
      unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
      have hz : ¬ (intOfZ (Z0 : Z) < 0) := by simp [intOfZ]
      rw [if_neg hz]
      rw [intOfZ_zOfInt]
      have hto : (intOfZ (Z0 : Z)).toNat = 0 := rfl
      rw [hto]
      have hzpow : (intOfZ (beta : Z)).pow 0 = 1 := by
        change @HPow.hPow Int Nat Int _ (intOfZ (beta : Z)) 0 = 1
        simp
      rw [hzpow]
      exact h1
  | Zneg q =>
      have hnonneg : 0 ≤ b ^ (j - 1) := Int.pow_nonneg (by omega)
      have hpnonneg : 0 ≤ p := Int.le_trans hnonneg hlower
      change intOfZ (Zpower (beta : Z) (.Zneg q)) ≤ p
      change intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow (beta : Z) (.Zneg q)) ≤ p
      have heqneg : ¬ (0 ≤ intOfZ (.Zneg q : Z)) := by
        change ¬ (0 ≤ -Int.ofNat (posToNat q))
        have hq : 0 < posToNat q := posToNat_positive q
        have hpos : 0 < Int.ofNat (posToNat q) := Int.natCast_pos.mpr hq
        intro h
        exact (Int.not_le_of_gt hpos) (Int.neg_nonneg.mp h)
      have helt : intOfZ (.Zneg q : Z) < 0 := Int.lt_of_not_ge heqneg
      unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
      rw [if_pos helt]
      change intOfZ (Z0 : Z) ≤ p
      simpa [intOfZ] using hpnonneg
  | Zpos q =>
      have hnlt : posToNat q < j := by
        change Int.ofNat (posToNat q) < Int.ofNat j at he
        exact Int.ofNat_lt.mp he
      have hnle : posToNat q ≤ j - 1 := by omega
      have hmono : b ^ (posToNat q) ≤ b ^ (j - 1) := digits_int_pow_mono b hb hnle
      have hpowrel : intOfZ (Zpower (beta : Z) (.Zpos q)) = b ^ (posToNat q) := by
        change intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow (beta : Z) (.Zpos q)) = _
        have heq : ¬ (intOfZ (.Zpos q : Z) < 0) := by
          change ¬ (Int.ofNat (posToNat q) < 0)
          exact Int.not_lt_of_ge (Int.ofNat_nonneg _)
        unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
        rw [if_neg heq]
        have hto : (intOfZ (.Zpos q : Z)).toNat = posToNat q := rfl
        rw [hto]
        rw [intOfZ_zOfInt]
        rw [hbrel]
        rfl
      rw [hpowrel]
      exact Int.le_trans hmono hlower

private theorem digits_intOfZ_add (a b : Z) :
    intOfZ (Zadd a b) = intOfZ a + intOfZ b := by
  simp only [Zadd,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]

private theorem digits_intOfZ_mul (a b : Z) :
    intOfZ (Zmul a b) = intOfZ a * intOfZ b := by
  simp only [Zmul,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]

private theorem digits_aux_lower
    (beta : radix) (b : Int) (hb : 1 ≤ b)
    (p nb pow : Z) (j k : Nat)
    (hbrel : intOfZ (beta : Z) = b)
    (hnb : intOfZ nb = Int.ofNat j)
    (hpow : intOfZ pow = b ^ j)
    (hj : 1 ≤ j)
    (hlower : b ^ (j - 1) ≤ intOfZ p) :
    ∀ e : Z, Zlt e (Zdigits_aux beta p nb pow k) →
      intOfZ (Zpower (beta : Z) e) ≤ intOfZ p := by
  induction k generalizing nb pow j with
  | zero =>
      intro e he
      change intOfZ e < intOfZ nb at he
      have he' : intOfZ e < Int.ofNat j := by
        rw [← hnb]
        exact he
      exact digits_power_le_of_exp_lt beta b hb e j (intOfZ p) he' hj hlower hbrel
  | succ k ih =>
      intro e he
      simp only [Zdigits_aux] at he
      split at he
      · rename_i hcond
        have he' : intOfZ e < Int.ofNat j := by
          rw [← hnb]
          exact he
        exact digits_power_le_of_exp_lt beta b hb e j (intOfZ p) he' hj hlower hbrel
      · rename_i hcond
        have hnlt : ¬ (intOfZ p < intOfZ pow) := by
            intro hlt
            apply hcond
            change (if intOfZ p < intOfZ pow then true else false) = true
            simp [hlt]
        have hpow_le : intOfZ pow ≤ intOfZ p := Int.le_of_not_gt hnlt
        have hnb' : intOfZ (Zadd nb Zone) = Int.ofNat (j + 1) := by
          rw [digits_intOfZ_add, hnb]
          rfl
        have hpow' : intOfZ (Zmul (beta : Z) pow) = b ^ (j + 1) := by
          rw [digits_intOfZ_mul, hbrel, hpow]
          change b * b ^ j = b ^ (j + 1)
          rw [Int.pow_succ]
          exact Int.mul_comm _ _
        have hlower' : b ^ ((j + 1) - 1) ≤ intOfZ p := by
          have hh : b ^ j ≤ intOfZ p := by
            rw [← hpow]
            exact hpow_le
          simpa using hh
        have hj' : 1 ≤ j + 1 := by omega
        exact ih (nb := Zadd nb Zone) (pow := Zmul (beta : Z) pow)
          (j := j + 1) hnb' hpow' hj' hlower' e he

private theorem digits_abs_pos (p : positive) : Zabs (.Zpos p : Z) = .Zpos p := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change intOfZ (zOfInt (Int.natAbs (Int.ofNat (posToNat p)))) =
    Int.ofNat (posToNat p)
  rw [intOfZ_zOfInt]
  exact Int.natAbs_of_nonneg (Int.natCast_nonneg _)

private theorem digits_abs_neg (p : positive) : Zabs (.Zneg p : Z) = .Zpos p := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change intOfZ (zOfInt (Int.natAbs (-Int.ofNat (posToNat p)))) =
    Int.ofNat (posToNat p)
  rw [intOfZ_zOfInt]
  simp

theorem Zpower_le_Zdigits : Zpower_le_ZdigitsStatement := by
  intro beta e x h
  have hb : 1 ≤ intOfZ (beta : Z) := by
    have hp := beta.radix_prop
    change (if intOfZ (Ztwo : Z) ≤ intOfZ (beta : Z) then true else false) = true at hp
    have htwo : intOfZ (Ztwo : Z) = 2 := by simp [intOfZ, posToNat]
    split at hp <;> simp_all <;> omega
  cases x with
  | Z0 =>
      change intOfZ e < intOfZ (Z0 : Z) at h
      cases e with
      | Z0 => simp at h
      | Zpos p =>
          have hf : False := (Int.not_lt_of_ge (Int.ofNat_nonneg _)) h
          exact hf.elim
      | Zneg q =>
          change intOfZ (Zpower (beta : Z) (.Zneg q)) ≤ intOfZ (Zabs (Z0 : Z))
          have heqneg : ¬ (0 ≤ intOfZ (.Zneg q : Z)) := by
            change ¬ (0 ≤ -Int.ofNat (posToNat q))
            have hq : 0 < posToNat q := posToNat_positive q
            have hpos : 0 < Int.ofNat (posToNat q) := Int.natCast_pos.mpr hq
            intro hh
            exact (Int.not_le_of_gt hpos) (Int.neg_nonneg.mp hh)
          have helt : intOfZ (.Zneg q : Z) < 0 := Int.lt_of_not_ge heqneg
          change intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow (beta : Z) (.Zneg q)) ≤ _
          unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
          rw [if_pos helt]
          change (0 : Int) ≤ 0
          omega
  | Zpos p =>
      change intOfZ e < intOfZ (Zdigits_aux beta (.Zpos p) Zone (beta : Z) (digits2_Pnat p)) at h
      change intOfZ (Zpower (beta : Z) e) ≤ intOfZ (Zabs (.Zpos p : Z))
      rw [digits_abs_pos]
      have hp : 0 < posToNat p := posToNat_positive p
      have hlower : (intOfZ (beta : Z)) ^ (1 - 1) ≤ intOfZ (.Zpos p : Z) := by
        have hpos : 0 < Int.ofNat (posToNat p) := Int.natCast_pos.mpr hp
        have hone : (intOfZ (beta : Z)) ^ (1 - 1) = 1 := by simp
        rw [hone]
        change 1 ≤ Int.ofNat (posToNat p)
        omega
      exact digits_aux_lower beta (intOfZ (beta : Z)) hb (.Zpos p) Zone (beta : Z) 1 (digits2_Pnat p)
        rfl rfl (by rw [Int.pow_one]) (by omega) hlower e h
  | Zneg p =>
      change intOfZ e < intOfZ (Zdigits_aux beta (.Zpos p) Zone (beta : Z) (digits2_Pnat p)) at h
      change intOfZ (Zpower (beta : Z) e) ≤ intOfZ (Zabs (.Zneg p : Z))
      rw [digits_abs_neg]
      have hp : 0 < posToNat p := posToNat_positive p
      have hlower : (intOfZ (beta : Z)) ^ (1 - 1) ≤ intOfZ (.Zpos p : Z) := by
        have hpos : 0 < Int.ofNat (posToNat p) := Int.natCast_pos.mpr hp
        have hone : (intOfZ (beta : Z)) ^ (1 - 1) = 1 := by simp
        rw [hone]
        change 1 ≤ Int.ofNat (posToNat p)
        omega
      exact digits_aux_lower beta (intOfZ (beta : Z)) hb (.Zpos p) Zone (beta : Z) 1 (digits2_Pnat p)
        rfl rfl (by rw [Int.pow_one]) (by omega) hlower e h
end CompCert4Lean.Flocq.Core.Digits

namespace CompCert4Lean.Flocq.Core.Digits

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem Zdigits_le_Zpower : Zdigits_le_ZpowerStatement := by
  intro beta e x h
  change intOfZ (Zdigits beta x) ≤ intOfZ e
  by_cases hle : intOfZ (Zdigits beta x) ≤ intOfZ e
  · exact hle
  · have hlt : intOfZ e < intOfZ (Zdigits beta x) := Int.lt_of_not_ge hle
    have hbound := Zpower_le_Zdigits beta e x hlt
    change intOfZ (Zpower (beta : Z) e) ≤ intOfZ (Zabs x) at hbound
    change intOfZ (Zabs x) < intOfZ (Zpower (beta : Z) e) at h
    omega

end CompCert4Lean.Flocq.Core.Digits
namespace CompCert4Lean.Flocq.Core.Digits
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt

private theorem add_int (a b : Z) : intOfZ (Zadd a b) = intOfZ a + intOfZ b := by
  simp only [Zadd, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]

private theorem int_lt_succ_le (a b : Int) (h : a < b) : a + 1 ≤ b := by omega

private theorem int_sub_add_identity2 (a b : Int) :
    a - 1 + (b - 1) + 1 = (a + b) - 1 := by
  omega

private theorem mul_int (a b : Z) : intOfZ (Zmul a b) = intOfZ a * intOfZ b := by
  simp only [Zmul, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]

private theorem sub_int (a b : Z) : intOfZ (Zsub a b) = intOfZ a - intOfZ b := by
  simp only [Zsub, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]

private theorem pow_nat_int (x : Z) (n : Nat) :
    intOfZ (Zpower_nat x n) = (intOfZ x) ^ n := by
  change intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow x
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)) = _
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  split
  · next h => exact False.elim ((Int.not_lt_of_ge (Int.natCast_nonneg _)) h)
  · next h =>
      change intOfZ (zOfInt ((intOfZ x).pow n)) = (intOfZ x) ^ n
      exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt _

private theorem int_pow_zero (x : Int) : x ^ 0 = 1 := by
  exact Int.pow_zero _

private theorem zpower_zero_int (beta : radix) :
    intOfZ (Zpower (beta : Z) (.Z0)) = 1 := by
  change intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
    (beta : Z) (.Z0)) = 1
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
  have h : ¬ intOfZ (Z0 : Z) < 0 := by simp [intOfZ]
  rw [if_neg h]
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  exact Int.pow_zero _

private theorem aux_bounds
    (beta : radix) (b : Int) (p nb pow : Z) (j k : Nat)
    (hb : 2 ≤ b)
    (hbrel : intOfZ (beta : Z) = b)
    (hnb : intOfZ nb = Int.ofNat j)
    (hpow : intOfZ pow = b ^ j)
    (hlower : b ^ (j - 1) ≤ intOfZ p)
    (hupper : intOfZ p < b ^ (j + k)) :
    ∃ d : Nat, intOfZ (Zdigits_aux beta p nb pow k) = Int.ofNat d ∧
      b ^ (d - 1) ≤ intOfZ p ∧ intOfZ p < b ^ d := by
  induction k generalizing nb pow j with
  | zero =>
      refine ⟨j, ?_, hlower, hupper⟩
      simpa [Zdigits_aux] using hnb
  | succ k ih =>
      simp only [Zdigits_aux]
      split
      · rename_i hcond
        have hcond' : intOfZ p < intOfZ pow := by
          change (if intOfZ p < intOfZ pow then true else false) = true at hcond
          simpa using hcond
        refine ⟨j, ?_, hlower, ?_⟩
        · simp [Zdigits_aux, hnb]
        · rw [← hpow]
          exact hcond'
      · rename_i hcond
        have hnot : ¬ intOfZ p < intOfZ pow := by
          intro hp
          apply hcond
          change (if intOfZ p < intOfZ pow then true else false) = true
          simp [hp]
        have hpowl : intOfZ pow ≤ intOfZ p := Int.le_of_not_gt hnot
        have hnb' : intOfZ (Zadd nb Zone) = Int.ofNat (j + 1) := by
          rw [add_int, hnb]
          change Int.ofNat j + intOfZ Zone = Int.ofNat (j + 1)
          simp [intOfZ, posToNat]
        have hpow' : intOfZ (Zmul (beta : Z) pow) = b ^ (j + 1) := by
          rw [mul_int]
          rw [hbrel, hpow]
          change b * b ^ j = b ^ (j + 1)
          rw [Int.pow_succ]
          simp [Int.mul_comm]
        have hlower' : b ^ ((j + 1) - 1) ≤ intOfZ p := by
          have : b ^ j ≤ intOfZ p := by
            rw [← hpow]
            exact hpowl
          simpa using this
        have hupper' : intOfZ p < b ^ ((j + 1) + k) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hupper
        exact ih (nb := Zadd nb Zone) (pow := Zmul (beta : Z) pow)
          (j := j + 1) hnb' hpow' hlower' hupper'

private theorem pow_base_mono (b : Int) (hb : 2 ≤ b) :
    ∀ n : Nat, (2 : Int) ^ n ≤ b ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Int.pow_succ, Int.pow_succ]
      have hnonneg : 0 ≤ (2 : Int) ^ n := Int.pow_nonneg (by omega)
      have hbnnonneg : 0 ≤ b ^ n := Int.pow_nonneg (by omega)
      have hstep : (2 : Int) ^ n * 2 ≤ b ^ n * b := by
        calc
          (2 : Int) ^ n * 2 ≤ 2 * b ^ n := by
            simpa [Int.mul_comm] using
              (Int.mul_le_mul_of_nonneg_left ih (by omega : (0 : Int) ≤ 2))
          _ ≤ b ^ n * 2 := by simp [Int.mul_comm]
          _ ≤ b ^ n * b := Int.mul_le_mul_of_nonneg_left hb hbnnonneg

      simpa [Int.mul_comm] using hstep

private theorem radix_int_ge_two (beta : radix) :
    2 ≤ intOfZ (beta : Z) := by
  have hp := beta.radix_prop
  change (if intOfZ (Ztwo : Z) ≤ intOfZ (beta : Z) then true else false) = true at hp
  have htwo : intOfZ (Ztwo : Z) = 2 := by simp [intOfZ, posToNat]
  rw [htwo] at hp
  split at hp <;> simp_all

private theorem digits_bounds_pos (beta : radix) (p : positive) :
    ∃ d : Nat, intOfZ (Zdigits beta (.Zpos p)) = Int.ofNat d ∧
      (intOfZ (beta : Z)) ^ (d - 1) ≤ intOfZ (.Zpos p : Z) ∧
      intOfZ (.Zpos p : Z) < (intOfZ (beta : Z)) ^ d := by
  let b : Int := intOfZ (beta : Z)
  let d := digits2_Pnat p
  have hb : 2 ≤ b := by simpa [b] using radix_int_ge_two beta
  have hd := digits2_Pnat_correct p
  have hd' : intOfZ (.Zpos p : Z) < (2 : Int) ^ (Nat.succ d) := by
    have hh := hd.2
    change intOfZ (.Zpos p : Z) < intOfZ (Zpower_nat Ztwo (Nat.succ d)) at hh
    rw [pow_nat_int] at hh
    simpa [intOfZ, posToNat] using hh
  simp [intOfZ, posToNat] at hd'
  have hmono := pow_base_mono b hb (Nat.succ d)
  have hupper' : Int.ofNat (posToNat p) < b ^ (1 + d) := by
    have : (2 : Int) ^ (Nat.succ d) ≤ b ^ (Nat.succ d) := by simpa [Nat.succ_eq_add_one] using hmono
    simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Int.lt_of_lt_of_le hd' this)
  have hupper : intOfZ (.Zpos p : Z) < b ^ (1 + d) := by simpa [intOfZ] using hupper'
  have hp : 0 < intOfZ (.Zpos p : Z) := by
    simp [intOfZ, posToNat]
    exact posToNat_positive p
  have hlower : b ^ (1 - 1) ≤ intOfZ (.Zpos p : Z) := by
    simp
    omega
  have heqnb : intOfZ (Zone : Z) = Int.ofNat 1 := by simp [intOfZ, posToNat]
  have heqpow : intOfZ (beta : Z) = b ^ 1 := by simp [b, Int.pow_one]
  obtain ⟨n, hn, hnl, hnu⟩ := aux_bounds beta b (.Zpos p) Zone (beta : Z)
    1 d hb (by simp [b]) heqnb heqpow hlower hupper
  exact ⟨n, by simpa [Zdigits, b] using hn, by simpa [b] using hnl, by simpa [b] using hnu⟩

private theorem pow_mono_nat (b : Int) (hb : 1 ≤ b) :
    ∀ {m n : Nat}, m ≤ n → b ^ m ≤ b ^ n := by
  intro m n hmn
  induction n with
  | zero =>
      have : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      exact Int.le_refl _
  | succ n ih =>
      by_cases hEq : m = Nat.succ n
      · subst m
        exact Int.le_refl _
      · have hmlt : m < Nat.succ n := Nat.lt_of_le_of_ne hmn hEq
        have hmle : m ≤ n := Nat.le_of_lt_succ hmlt
        have hmono := ih hmle
        have hnonneg : 0 ≤ b ^ n := Int.pow_nonneg (by omega)
        have hstep : b ^ n ≤ b ^ n * b := by
          simpa using (Int.mul_le_mul_of_nonneg_left hb hnonneg)
        rw [Int.pow_succ]
        exact Int.le_trans hmono hstep

private theorem zpower_pos_int (beta : radix) (q : positive) :
    intOfZ (Zpower (beta : Z) (.Zpos q)) =
      (intOfZ (beta : Z)) ^ posToNat q := by
  change intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
    (beta : Z) (.Zpos q)) = _
  have hq : ¬ intOfZ (.Zpos q : Z) < 0 := by
    simp [intOfZ]
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
  rw [if_neg hq]
  have hto : (intOfZ (.Zpos q : Z)).toNat = posToNat q := rfl
  rw [hto]
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  rfl

private theorem abs_pos (p : positive) : Zabs (.Zpos p : Z) = .Zpos p := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change intOfZ (zOfInt (Int.natAbs (Int.ofNat (posToNat p)))) =
    Int.ofNat (posToNat p)
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  exact Int.natAbs_of_nonneg (Int.natCast_nonneg _)

private theorem abs_neg (p : positive) : Zabs (.Zneg p : Z) = .Zpos p := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change intOfZ (zOfInt (Int.natAbs (-Int.ofNat (posToNat p)))) =
    Int.ofNat (posToNat p)
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  simp

private theorem zpower_int_nat (beta : radix) (e : Z)
    (he : 0 ≤ intOfZ e) :
    intOfZ (Zpower (beta : Z) e) =
      (intOfZ (beta : Z)) ^ Int.toNat (intOfZ e) := by
  cases e with
  | Z0 =>
      rw [zpower_zero_int]
      change (1 : Int) = (intOfZ (beta : Z)) ^ 0
      simp
  | Zpos q =>
      rw [zpower_pos_int]
      rfl
  | Zneg q =>
      simp [intOfZ] at he
      have hq := posToNat_positive q
      omega

private theorem zpower_add_mul (beta : radix) (a b : Z)
    (ha : 0 ≤ intOfZ a) (hb : 0 ≤ intOfZ b) :
    intOfZ (Zpower (beta : Z) (Zadd a b)) =
      intOfZ (Zpower (beta : Z) a) * intOfZ (Zpower (beta : Z) b) := by
  have hab : intOfZ (Zadd a b) = intOfZ a + intOfZ b := add_int a b
  have hsum : 0 ≤ intOfZ (Zadd a b) := by
    rw [hab]
    exact Int.add_nonneg ha hb
  rw [zpower_int_nat beta (Zadd a b) hsum]
  rw [hab, Int.toNat_add ha hb, Int.pow_add]
  rw [zpower_int_nat beta a ha, zpower_int_nat beta b hb]

private theorem abs_mul_int (a b : Z) :
    intOfZ (Zabs (Zmul a b)) = intOfZ (Zabs a) * intOfZ (Zabs b) := by
  change intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs (Zmul a b)) =
    intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs a) *
      intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs b)
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  rw [mul_int, Int.natAbs_mul]
  exact Int.natCast_mul _ _

private theorem zpower_gt_digits_local : Zpower_gt_ZdigitsStatement := by
  intro beta e x hle
  cases x with
  | Z0 =>
      change intOfZ (Zabs (Z0 : Z)) < intOfZ (Zpower (beta : Z) e)
      cases e with
      | Z0 =>
          rw [show Zabs (Z0 : Z) = Z0 by rfl]
          change (0 : Int) < intOfZ (Zpower (beta : Z) (.Z0))
          rw [zpower_zero_int]
          omega
      | Zpos q =>
          rw [show Zabs (Z0 : Z) = Z0 by rfl]
          change (0 : Int) < intOfZ (Zpower (beta : Z) (.Zpos q))
          rw [zpower_pos_int]
          have hb : 1 ≤ intOfZ (beta : Z) := by
            have := radix_int_ge_two beta
            omega
          exact Int.pow_pos (by omega)
      | Zneg q =>
          exfalso
          change intOfZ (Zdigits beta (Z0 : Z)) ≤ intOfZ (.Zneg q : Z) at hle
          simp [Zdigits, intOfZ] at hle
          have hqpos := posToNat_positive q
          omega
  | Zpos p =>
      obtain ⟨d, hd, hdl, hdu⟩ := digits_bounds_pos beta p
      have hdpos : 0 < d := by
        have hz := Zdigits_gt_0 beta (.Zpos p) (by intro h; cases h)
        change 0 < intOfZ (Zdigits beta (.Zpos p)) at hz
        have hz' : 0 < Int.ofNat d := by simpa [hd] using hz
        exact Int.natCast_pos.mp hz'
      cases e with
      | Z0 =>
          exfalso
          change intOfZ (Zdigits beta (.Zpos p)) ≤ 0 at hle
          rw [hd] at hle
          change Int.ofNat d ≤ 0 at hle
          have hdposI : (0 : Int) < Int.ofNat d := Int.natCast_pos.mpr hdpos
          exact (Int.not_le_of_gt hdposI) hle
      | Zneg q =>
          exfalso
          change intOfZ (Zdigits beta (.Zpos p)) ≤ intOfZ (.Zneg q : Z) at hle
          rw [hd] at hle
          simp [intOfZ] at hle
          omega
      | Zpos q =>
          have hq : d ≤ posToNat q := by
            change intOfZ (Zdigits beta (.Zpos p)) ≤ intOfZ (.Zpos q : Z) at hle
            rw [hd] at hle
            simp [intOfZ] at hle
            omega
          have hb : 1 ≤ intOfZ (beta : Z) := by
            have := radix_int_ge_two beta
            omega
          have hpow := pow_mono_nat (intOfZ (beta : Z)) hb hq
          have hpow' : intOfZ (Zpower (beta : Z) (.Zpos q)) =
              (intOfZ (beta : Z)) ^ posToNat q := zpower_pos_int beta q
          change intOfZ (Zabs (.Zpos p : Z)) < intOfZ (Zpower (beta : Z) (.Zpos q))
          rw [abs_pos]
          rw [hpow']
          exact Int.lt_of_lt_of_le hdu hpow

  | Zneg p =>
      obtain ⟨d, hd, hdl, hdu⟩ := digits_bounds_pos beta p
      have hdneg : intOfZ (Zdigits beta (.Zneg p)) = Int.ofNat d := by
        simpa [Zdigits] using hd
      have hdpos : 0 < d := by
        have hz := Zdigits_gt_0 beta (.Zneg p) (by intro h; cases h)
        change 0 < intOfZ (Zdigits beta (.Zneg p)) at hz
        have hz' : 0 < Int.ofNat d := by simpa [hdneg] using hz
        exact Int.natCast_pos.mp hz'
      cases e with
      | Z0 =>
          exfalso
          change intOfZ (Zdigits beta (.Zneg p)) ≤ 0 at hle
          rw [hdneg] at hle
          change Int.ofNat d ≤ 0 at hle
          have hdposI : (0 : Int) < Int.ofNat d := Int.natCast_pos.mpr hdpos
          exact (Int.not_le_of_gt hdposI) hle
      | Zneg q =>
          exfalso
          change intOfZ (Zdigits beta (.Zneg p)) ≤ intOfZ (.Zneg q : Z) at hle
          rw [hdneg] at hle
          simp [intOfZ] at hle
          omega
      | Zpos q =>
          have hq : d ≤ posToNat q := by
            change intOfZ (Zdigits beta (.Zneg p)) ≤ intOfZ (.Zpos q : Z) at hle
            rw [hdneg] at hle
            simp [intOfZ] at hle
            omega
          have hb : 1 ≤ intOfZ (beta : Z) := by
            have := radix_int_ge_two beta
            omega
          have hpow := pow_mono_nat (intOfZ (beta : Z)) hb hq
          have hpow' : intOfZ (Zpower (beta : Z) (.Zpos q)) =
              (intOfZ (beta : Z)) ^ posToNat q := zpower_pos_int beta q
          change intOfZ (Zabs (.Zneg p : Z)) < intOfZ (Zpower (beta : Z) (.Zpos q))
          rw [abs_neg]
          rw [hpow']
          exact Int.lt_of_lt_of_le hdu hpow

theorem Zdigits_gt_Zpower : Zdigits_gt_ZpowerStatement := by
  intro beta e x h
  change intOfZ e < intOfZ (Zdigits beta x)
  by_cases hlt : intOfZ e < intOfZ (Zdigits beta x)
  · exact hlt
  · have hle : intOfZ (Zdigits beta x) ≤ intOfZ e := Int.le_of_not_gt hlt
    have hu := zpower_gt_digits_local beta e x hle
    change intOfZ (Zpower (beta : Z) e) ≤ intOfZ (Zabs x) at h
    change intOfZ (Zabs x) < intOfZ (Zpower (beta : Z) e) at hu
    omega

theorem Zdigits_mult_ge : Zdigits_mult_geStatement := by
  intro beta x y hx hy
  have hzone : intOfZ (Zone : Z) = (1 : Int) := by simp [intOfZ, posToNat]
  have hx0 := Zdigits_gt_0 beta x hx
  have hy0 := Zdigits_gt_0 beta y hy
  change 0 < intOfZ (Zdigits beta x) at hx0
  change 0 < intOfZ (Zdigits beta y) at hy0
  let ex : Z := Zsub (Zdigits beta x) Zone
  let ey : Z := Zsub (Zdigits beta y) Zone
  have hex : 0 ≤ intOfZ ex := by
    dsimp [ex]
    rw [sub_int]
    rw [hzone]
    omega
  have hey : 0 ≤ intOfZ ey := by
    dsimp [ey]
    rw [sub_int]
    rw [hzone]
    omega
  have hxlt : intOfZ ex < intOfZ (Zdigits beta x) := by
    dsimp [ex]
    rw [sub_int]
    rw [hzone]
    omega
  have hylt : intOfZ ey < intOfZ (Zdigits beta y) := by
    dsimp [ey]
    rw [sub_int]
    rw [hzone]
    omega
  have hxp := Zpower_le_Zdigits beta ex x hxlt
  have hyp := Zpower_le_Zdigits beta ey y hylt
  change intOfZ (Zpower (beta : Z) ex) ≤ intOfZ (Zabs x) at hxp
  change intOfZ (Zpower (beta : Z) ey) ≤ intOfZ (Zabs y) at hyp
  have hpowx : 0 ≤ intOfZ (Zpower (beta : Z) ex) := by
    rw [zpower_int_nat beta ex hex]
    have hb0 := radix_int_ge_two beta
    exact Int.pow_nonneg (by omega)
  have habsx : 0 ≤ intOfZ (Zabs x) := by
    change 0 ≤ intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs x)
    unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    omega
  have habsy : 0 ≤ intOfZ (Zabs y) := by
    change 0 ≤ intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs y)
    unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    omega
  have hpowy : 0 ≤ intOfZ (Zpower (beta : Z) ey) := by
    rw [zpower_int_nat beta ey hey]
    have hb0 := radix_int_ge_two beta
    exact Int.pow_nonneg (by omega)
  have hprod := Int.mul_le_mul hxp hyp hpowy habsx
  have hpowadd := zpower_add_mul beta ex ey hex hey
  rw [← hpowadd] at hprod
  have hprod' : intOfZ (Zpower (beta : Z) (Zadd ex ey)) ≤
      intOfZ (Zabs (Zmul x y)) := by
    simpa [abs_mul_int] using hprod
  have hlt := Zdigits_gt_Zpower beta (Zadd ex ey) (Zmul x y) hprod'
  change intOfZ (Zadd ex ey) < intOfZ (Zdigits beta (Zmul x y)) at hlt
  change intOfZ (Zsub (Zadd (Zdigits beta x) (Zdigits beta y)) Zone) ≤
    intOfZ (Zdigits beta (Zmul x y))
  have heq : intOfZ (Zadd ex ey) + 1 =
      intOfZ (Zsub (Zadd (Zdigits beta x) (Zdigits beta y)) Zone) := by
    have hex' : intOfZ ex = intOfZ (Zdigits beta x) - 1 := by
      dsimp [ex]
      rw [sub_int, hzone]
    have hey' : intOfZ ey = intOfZ (Zdigits beta y) - 1 := by
      dsimp [ey]
      rw [sub_int, hzone]
    have hleft : intOfZ (Zadd ex ey) + 1 =
        intOfZ (Zdigits beta x) - 1 + (intOfZ (Zdigits beta y) - 1) + 1 := by
      rw [add_int, hex', hey']
    have hright : intOfZ (Zsub (Zadd (Zdigits beta x) (Zdigits beta y)) Zone) =
        (intOfZ (Zdigits beta x) + intOfZ (Zdigits beta y)) - 1 := by
      rw [sub_int, add_int, hzone]
    rw [hleft, hright]
    omega
  have hlt' := int_lt_succ_le _ _ hlt
  calc
    intOfZ (Zsub (Zadd (Zdigits beta x) (Zdigits beta y)) Zone) =
        intOfZ (Zadd ex ey) + 1 := heq.symm
    _ ≤ intOfZ (Zdigits beta (Zmul x y)) := hlt'

private theorem test_radix2_zpower_of_nat (n : Nat) :
    intOfZ (Zpower (radix2 : Z) (Z_of_nat n)) = (2 : Int) ^ n := by
  have hnat : intOfZ (Z_of_nat n) = Int.ofNat n := by
    unfold Z_of_nat
    exact intOfZ_zOfInt _
  have h := zpower_int_nat radix2 (Z_of_nat n) (by rw [hnat]; exact Int.ofNat_nonneg n)
  rw [h]
  rw [hnat]
  have hb : intOfZ (radix2 : Z) = 2 := by decide
  rw [hb]
  simp

private theorem test_zpower_nat_two (n : Nat) :
    intOfZ (Zpower_nat Ztwo n) = (2 : Int) ^ n := by
  rw [pow_nat_int]
  simp [intOfZ, posToNat]

private theorem test_radix2_zpower_of_pred_succ (n : Nat) :
    intOfZ (Zpower (radix2 : Z)
      (Zsub (Z_of_nat (Nat.succ n)) Zone)) = (2 : Int) ^ n := by
  have hsub : intOfZ (Zsub (Z_of_nat (Nat.succ n)) Zone) = Int.ofNat n := by
    rw [sub_int]
    have hn : intOfZ (Z_of_nat (Nat.succ n)) = Int.ofNat (Nat.succ n) := by
      unfold Z_of_nat
      exact intOfZ_zOfInt _
    rw [hn]
    have h1 : intOfZ (Zone : Z) = 1 := by simp [intOfZ, posToNat]
    rw [h1]
    simpa [Int.natCast_succ]
  have h := zpower_int_nat radix2
    (Zsub (Z_of_nat (Nat.succ n)) Zone) (by rw [hsub]; exact Int.ofNat_nonneg n)
  rw [h, hsub]
  have hb : intOfZ (radix2 : Z) = 2 := by decide
  rw [hb]
  simp

theorem Z_of_nat_S_digits2_Pnat : Z_of_nat_S_digits2_PnatStatement := by
  intro m
  apply intOfZ_injective
  have hd := digits2_Pnat_correct m
  change intOfZ (Z_of_nat (Nat.succ (digits2_Pnat m))) =
    intOfZ (Zdigits radix2 (Zpos m))
  rw [show intOfZ (Z_of_nat (Nat.succ (digits2_Pnat m))) =
      Int.ofNat (Nat.succ (digits2_Pnat m)) by
    unfold Z_of_nat
    exact intOfZ_zOfInt _]
  have hdlo : intOfZ (Zpower_nat Ztwo (digits2_Pnat m)) ≤
      intOfZ (Zpos m) := by
    change intOfZ (Zpower_nat Ztwo (digits2_Pnat m)) ≤ intOfZ (Zpos m)
    exact hd.1
  have hdhi : intOfZ (Zpos m) <
      intOfZ (Zpower_nat Ztwo (Nat.succ (digits2_Pnat m))) := by
    change intOfZ (Zpos m) < intOfZ (Zpower_nat Ztwo (Nat.succ (digits2_Pnat m)))
    exact hd.2
  have hlow : intOfZ (Zpower (radix2 : Z) (Z_of_nat (digits2_Pnat m))) ≤
      intOfZ (Zabs (Zpos m)) := by
    calc
      intOfZ (Zpower (radix2 : Z) (Z_of_nat (digits2_Pnat m))) =
          intOfZ (Zpower_nat Ztwo (digits2_Pnat m)) := by
            rw [test_radix2_zpower_of_nat, test_zpower_nat_two]
      _ ≤ intOfZ (Zpos m) := hdlo
      _ = intOfZ (Zabs (Zpos m)) := by rw [abs_pos]
  have hgt := Zdigits_gt_Zpower radix2 (Z_of_nat (digits2_Pnat m)) (Zpos m) hlow
  have hupper : intOfZ (Zabs (Zpos m)) <
      intOfZ (Zpower (radix2 : Z) (Z_of_nat (Nat.succ (digits2_Pnat m)))) := by
    calc
      intOfZ (Zabs (Zpos m)) = intOfZ (Zpos m) := by rw [abs_pos]
      _ < intOfZ (Zpower_nat Ztwo (Nat.succ (digits2_Pnat m))) := hdhi
      _ = intOfZ (Zpower (radix2 : Z) (Z_of_nat (Nat.succ (digits2_Pnat m)))) := by
        rw [test_radix2_zpower_of_nat, test_zpower_nat_two]
  have hle := Zdigits_le_Zpower radix2 (Z_of_nat (Nat.succ (digits2_Pnat m))) (Zpos m)
    (by exact hupper)
  change intOfZ (Z_of_nat (digits2_Pnat m)) < intOfZ (Zdigits radix2 (Zpos m)) at hgt
  change intOfZ (Zdigits radix2 (Zpos m)) ≤
      intOfZ (Z_of_nat (Nat.succ (digits2_Pnat m))) at hle
  have hn : intOfZ (Z_of_nat (digits2_Pnat m)) = Int.ofNat (digits2_Pnat m) := by
    unfold Z_of_nat
    exact intOfZ_zOfInt _
  have hsn : intOfZ (Z_of_nat (Nat.succ (digits2_Pnat m))) =
      Int.ofNat (Nat.succ (digits2_Pnat m)) := by
    unfold Z_of_nat
    exact intOfZ_zOfInt _
  have hgt' : Int.ofNat (digits2_Pnat m) < intOfZ (Zdigits radix2 (Zpos m)) := by
    simpa [hn] using hgt
  have hle' : intOfZ (Zdigits radix2 (Zpos m)) ≤ Int.ofNat (Nat.succ (digits2_Pnat m)) := by
    simpa [hsn] using hle
  have hge : Int.ofNat (digits2_Pnat m) + 1 ≤
      intOfZ (Zdigits radix2 (Zpos m)) := by
    omega
  have heqI : intOfZ (Zdigits radix2 (Zpos m)) =
      Int.ofNat (Nat.succ (digits2_Pnat m)) := by
    apply Int.le_antisymm hle'
    simpa [Int.natCast_succ] using hge
  exact heqI.symm

theorem Zpos_digits2_pos : Zpos_digits2_posStatement := by
  intro m
  rw [← Z_of_nat_S_digits2_Pnat m]
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change intOfZ (Zpos (digits2_pos m)) = intOfZ (Z_of_nat (Nat.succ (digits2_Pnat m)))
  have hnat : posToNat (digits2_pos m) = Nat.succ (digits2_Pnat m) := by
    have hsucc (q : positive) :
        posToNat (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posSucc q) =
          posToNat q + 1 := by
      induction q with
      | xH => rfl
      | xI q ih =>
          change 2 * posToNat
              (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posSucc q) =
            2 * posToNat q + 1 + 1
          rw [ih]
          omega
      | xO q ih =>
          change posToNat (.xI q) = 2 * posToNat q + 1
          rfl
    induction m with
    | xH => rfl
    | xO p ih =>
        rw [show digits2_pos (.xO p) =
          CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posSucc
            (digits2_pos p) by rfl]
        rw [hsucc, ih]
        simp [digits2_Pnat]
    | xI p ih =>
        rw [show digits2_pos (.xI p) =
          CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posSucc
            (digits2_pos p) by rfl]
        rw [hsucc, ih]
        simp [digits2_Pnat]
  change intOfZ (Zpos (digits2_pos m)) = intOfZ (Z_of_nat (Nat.succ (digits2_Pnat m)))
  rw [show intOfZ (Zpos (digits2_pos m)) = Int.ofNat (posToNat (digits2_pos m)) by rfl]
  rw [show intOfZ (Z_of_nat (Nat.succ (digits2_Pnat m))) =
      Int.ofNat (Nat.succ (digits2_Pnat m)) by
    unfold Z_of_nat
    exact intOfZ_zOfInt _]
  rw [hnat]

end CompCert4Lean.Flocq.Core.Digits

namespace CompCert4Lean.Flocq.Core.Digits

theorem Zdigits2_Zdigits : Zdigits2_ZdigitsStatement := by
  intro n
  cases n with
  | Z0 => rfl
  | Zpos p => exact Zpos_digits2_pos p
  | Zneg p =>
      change Zpos (digits2_pos p) = Zdigits radix2 (.Zneg p)
      rw [← Zdigits_abs radix2 (.Zneg p)]
      rw [digits_Zabs_neg]
      exact Zpos_digits2_pos p

end CompCert4Lean.Flocq.Core.Digits
