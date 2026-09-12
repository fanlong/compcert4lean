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
