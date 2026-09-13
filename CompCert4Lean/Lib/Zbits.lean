import CompCert4Lean.Lib.Coqlib

/-!
# Additional binary-integer operations

This module translates the definition-bearing surface of `compcert.lib.Zbits`.
Proof-bearing source declarations are retained as exact statement descriptors;
their proof bodies belong to the later proof-migration phase.
-/

namespace CompCert4Lean.Lib.Zbits

universe u

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
private abbrev zZero : Z :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0
private abbrev zPos : positive → Z :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Zpos
private abbrev zAdd : Z → Z → Z :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
private abbrev zMul : Z → Z → Z :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
private abbrev zOpp : Z → Z :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
private abbrev zLe : Z → Z → Prop :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
private abbrev zLt : Z → Z → Prop :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt
private abbrev zGt : Z → Z → Prop :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.gt
private abbrev zDiv : Z → Z → Z :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div
private abbrev zModulo : Z → Z → Z :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo
private abbrev zDivide : Z → Z → Prop :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.divide
private abbrev zDiv2 : Z → Z :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div2
private abbrev zDouble : Z → Z :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.double
private abbrev zSuccDouble : Z → Z :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.succ_double
private abbrev zSucc : Z → Z :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.succ
private abbrev zPred : Z → Z :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pred
private abbrev zOdd : Z → Bool :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.odd
private abbrev zTestbit : Z → Z → Bool :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.testbit
private abbrev zLog2 : Z → Z :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.log2
private def zIter {A : Type u} (n : Z) (f : A → A) (x : A) : A :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.iter n f x
private abbrev zShiftl : Z → Z → Z :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftl
private abbrev zShiftr : Z → Z → Z :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftr
private abbrev zOfNat : Nat → Z :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
private abbrev zTwoP : Z → Z :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.two_p
private abbrev zTwoPowerNat : Nat → Z :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.two_power_nat
private abbrev zPosSize : positive → positive :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.size
private abbrev zltDec := CompCert4Lean.Lib.Coqlib.zlt
private abbrev zleDec := CompCert4Lean.Lib.Coqlib.zle
private abbrev zeqDec := CompCert4Lean.Lib.Coqlib.zeq

private abbrev one : Z := zPos xH
private abbrev two : Z := zPos (xO xH)

private def sumboolSelect {P Q : Prop} {A : Type}
    (d : CompCert4Lean.Foundation.Logic.Support.Sumbool P Q)
    (ifso ifnot : A) : A :=
  match d with
  | .left _ => ifso
  | .right _ => ifnot

/-! ## Modulo arithmetic -/

def eqmod (modul x y : Z) : Prop :=
  ∃ k : Z, x = zAdd (zMul k modul) y

/-! ## Fast normalization modulo `2^n` -/

def P_mod_two_p (p : positive) : Nat → Z
  | 0 => zZero
  | n + 1 =>
      match p with
      | .xH => one
      | .xO q => zDouble (P_mod_two_p q n)
      | .xI q => zSuccDouble (P_mod_two_p q n)

/-! ## Bit-level operations -/

def Zshiftin (b : Bool) (x : Z) : Z :=
  if b then zSuccDouble x else zDouble x

/-! ## Zero extension -/

def Zzero_ext (n x : Z) : Z :=
  let step : (Z → Z) → (Z → Z) :=
    fun rec y => Zshiftin (zOdd y) (rec (zDiv2 y))
  (zIter n step (fun _ => zZero)) x

/-! ## Decomposition into powers of two -/

def Z_one_bits : Nat → Z → Z → List Z
  | 0, _, _ => []
  | n + 1, x, i =>
      if zOdd x then
        i :: Z_one_bits n (zDiv2 x) (zAdd i one)
      else
        Z_one_bits n (zDiv2 x) (zAdd i one)

def powerserie : List Z → Z
  | [] => zZero
  | x :: xs => zAdd (zTwoP x) (powerserie xs)

/-! ## Recognition of powers of two -/

def P_is_power2 : positive → Bool
  | .xH => true
  | .xO q => P_is_power2 q
  | .xI _ => false

def Z_is_power2 : Z → Option Z
  | .Z0 => none
  | x@(.Zpos p) => if P_is_power2 p then some (zLog2 x) else none
  | .Zneg _ => none

/-! ## Size of integers -/

def Zsize (x : Z) : Z :=
  match x with
  | .Zpos p => zPos (zPosSize p)
  | _ => zZero

/-! ## Exact statement descriptors for later proofs -/

def P_mod_two_p_rangeStatement : Prop :=
  ∀ (n : Nat) (p : positive),
    zLe zZero (P_mod_two_p p n) ∧ zLt (P_mod_two_p p n) (zTwoPowerNat n)

def Z_one_bits_powerserieStatement : Prop :=
  ∀ (n : Nat) (x : Z),
    zLe zZero x ∧ zLt x (zTwoPowerNat n) →
      x = powerserie (Z_one_bits n x zZero)

def Z_one_bits_rangeStatement : Prop :=
  ∀ (n : Nat) (x i : Z),
    i ∈ Z_one_bits n x zZero →
      zLe zZero i ∧ zLt i (zOfNat n)

def ZdecompStatement : Prop :=
  ∀ (x : Z), x = Zshiftin (zOdd x) (zDiv2 x)

def Ziter_baseStatement : Prop :=
  ∀ (A : Type u) (n : Z) (f : A → A) (x : A),
    zLe n zZero → zIter n f x = x

def Ziter_succStatement : Prop :=
  ∀ (A : Type u) (n : Z) (f : A → A) (x : A),
    zLe zZero n → zIter (zSucc n) f x = f (zIter n f x)

def Znatlike_indStatement : Prop :=
  ∀ (P : Z → Prop),
    (∀ n : Z, zLe n zZero → P n) →
    (∀ n : Z, zLe zZero n → P n → P (zSucc n)) →
    ∀ n : Z, P n

def Zshiftin_injStatement : Prop :=
  ∀ (b1 : Bool) (x1 : Z) (b2 : Bool) (x2 : Z),
    Zshiftin b1 x1 = Zshiftin b2 x2 → b1 = b2 ∧ x1 = x2

def Zshiftin_specStatement : Prop :=
  ∀ (b : Bool) (x : Z),
    Zshiftin b x = zAdd (zMul two x) (if b then one else zZero)

def Zshiftl_mul_two_pStatement : Prop :=
  ∀ (x n : Z), zLe zZero n → zShiftl x n = zMul x (zTwoP n)

def Zshiftr_div_two_pStatement : Prop :=
  ∀ (x n : Z), zLe zZero n → zShiftr x n = zDiv x (zTwoP n)

def Zsize_pos'Statement : Prop :=
  ∀ (x : Z), zLt zZero x → zLt zZero (Zsize x)

def Ztestbit_0Statement : Prop :=
  ∀ (n : Z), zTestbit zZero n = false

def Ztestbit_baseStatement : Prop :=
  ∀ (x : Z), zTestbit x zZero = zOdd x

def Ztestbit_eqStatement : Prop :=
  ∀ (n x : Z), zLe zZero n →
    zTestbit x n = sumboolSelect (zeqDec n zZero) (zOdd x)
      (zTestbit (zDiv2 x) (zPred n))

def Ztestbit_mod_two_pStatement : Prop :=
  ∀ (n x i : Z), zLe zZero n → zLe zZero i →
    zTestbit (zModulo x (zTwoP n)) i =
      sumboolSelect (zltDec i n) (zTestbit x i) false

def Ztestbit_shiftinStatement : Prop :=
  ∀ (b : Bool) (x n : Z), zLe zZero n →
    zTestbit (Zshiftin b x) n =
      sumboolSelect (zeqDec n zZero) b (zTestbit x (zPred n))

def Ztestbit_succStatement : Prop :=
  ∀ (n x : Z), zLe zZero n → zTestbit x (zSucc n) = zTestbit (zDiv2 x) n

def Zzero_ext_modStatement : Prop :=
  ∀ (n x : Z), zLe zZero n → Zzero_ext n x = zModulo x (zTwoP n)

def Zzero_ext_specStatement : Prop :=
  ∀ (n x i : Z), zLe zZero i →
    zTestbit (Zzero_ext n x) i =
      sumboolSelect (zltDec i n) (zTestbit x i) false

def eqmod_addStatement : Prop :=
  ∀ (modul a b c d : Z),
    eqmod modul a b → eqmod modul c d →
      eqmod modul (zAdd a c) (zAdd b d)

def eqmod_dividesStatement : Prop :=
  ∀ (n m x y : Z), eqmod n x y → zDivide m n → eqmod m x y

def eqmod_modStatement : Prop :=
  ∀ (modul : Z), zGt modul zZero → ∀ x : Z,
    eqmod modul x (zModulo x modul)

def eqmod_multStatement : Prop :=
  ∀ (modul a b c d : Z),
    eqmod modul a c → eqmod modul b d →
      eqmod modul (zMul a b) (zMul c d)

def eqmod_negStatement : Prop :=
  ∀ (modul x y : Z), eqmod modul x y →
    eqmod modul (zOpp x) (zOpp y)

def eqmod_reflStatement : Prop :=
  ∀ (modul x : Z), eqmod modul x x

def eqmod_refl2Statement : Prop :=
  ∀ (modul x y : Z), x = y → eqmod modul x y

def eqmod_same_bitsStatement : Prop :=
  ∀ (n : Nat) (x y : Z),
    (∀ i : Z, zLe zZero i ∧ zLt i (zOfNat n) →
      zTestbit x i = zTestbit y i) →
      eqmod (zTwoPowerNat n) x y

def eqmod_small_eqStatement : Prop :=
  ∀ (modul x y : Z),
    eqmod modul x y →
    (zLe zZero x ∧ zLt x modul) →
    (zLe zZero y ∧ zLt y modul) →
      x = y

def eqmod_transStatement : Prop :=
  ∀ (modul x y z : Z),
    eqmod modul x y → eqmod modul y z → eqmod modul x z

def equal_same_bitsStatement : Prop :=
  ∀ (x y : Z),
    (∀ i : Z, zLe zZero i → zTestbit x i = zTestbit y i) → x = y

def same_bits_eqmodStatement : Prop :=
  ∀ (n : Nat) (x y i : Z),
    eqmod (zTwoPowerNat n) x y →
    (zLe zZero i ∧ zLt i (zOfNat n)) →
      zTestbit x i = zTestbit y i

end CompCert4Lean.Lib.Zbits

namespace CompCert4Lean.Lib.Zbits

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eqmod_refl : eqmod_reflStatement := by
  intro modul x
  unfold eqmod
  refine ⟨zZero, ?_⟩
  apply intOfZ_injective
  simp only [zAdd, zMul, zZero, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul]
  simp only [intOfZ_zOfInt]
  change intOfZ x = 0 * intOfZ modul + intOfZ x
  omega

theorem eqmod_refl2 : eqmod_refl2Statement := by
  intro modul x y h
  subst y
  exact eqmod_refl modul x

theorem eqmod_trans : eqmod_transStatement := by
  intro modul x y z hxy hyz
  unfold eqmod at hxy hyz ⊢
  rcases hxy with ⟨k1, h1⟩
  rcases hyz with ⟨k2, h2⟩
  refine ⟨zAdd k1 k2, ?_⟩
  apply intOfZ_injective
  simp only [zAdd, zMul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul] at h1 h2 ⊢
  have h1' := congrArg intOfZ h1
  have h2' := congrArg intOfZ h2
  simp only [intOfZ_zOfInt] at h1' h2' ⊢
  change intOfZ x = (intOfZ k1 + intOfZ k2) * intOfZ modul + intOfZ z
  change intOfZ x = intOfZ k1 * intOfZ modul + intOfZ y at h1'
  change intOfZ y = intOfZ k2 * intOfZ modul + intOfZ z at h2'
  rw [h1', h2', Int.add_mul]
  omega

theorem eqmod_small_eq : eqmod_small_eqStatement := by
  intro modul x y h hx hy
  unfold eqmod at h
  rcases h with ⟨k, h⟩
  have h' := congrArg intOfZ h
  simp only [zAdd, zMul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, intOfZ_zOfInt] at h'
  change intOfZ x = intOfZ k * intOfZ modul + intOfZ y at h'
  change 0 ≤ intOfZ x ∧ intOfZ x < intOfZ modul at hx
  change 0 ≤ intOfZ y ∧ intOfZ y < intOfZ modul at hy
  have hmpos : 0 < intOfZ modul := by omega
  have hmnonneg : 0 ≤ intOfZ modul := Int.le_of_lt hmpos
  apply intOfZ_injective
  by_cases hkpos : 0 < intOfZ k
  · have hkone : 1 ≤ intOfZ k := by omega
    have hkm : intOfZ modul ≤ intOfZ k * intOfZ modul := by
      have := Int.mul_le_mul_of_nonneg_right hkone hmnonneg
      simpa [Int.one_mul] using this
    omega
  · by_cases hkzero : intOfZ k = 0
    · simpa [hkzero] using h'
    · have hkneg : intOfZ k < 0 := by omega
      have hkminusone : intOfZ k ≤ -1 := by omega
      have hkm : intOfZ k * intOfZ modul ≤ (-1) * intOfZ modul :=
        Int.mul_le_mul_of_nonneg_right hkminusone hmnonneg
      have hkm' : intOfZ k * intOfZ modul ≤ -intOfZ modul := by
        simpa [Int.neg_one_mul] using hkm
      have hsum : intOfZ k * intOfZ modul + intOfZ y < 0 := by omega
      omega

end CompCert4Lean.Lib.Zbits

namespace CompCert4Lean.Lib.Zbits

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eqmod_add : eqmod_addStatement := by
  intro modul a b c d h₁ h₂
  unfold eqmod at h₁ h₂ ⊢
  rcases h₁ with ⟨k₁, hk₁⟩
  rcases h₂ with ⟨k₂, hk₂⟩
  refine ⟨zAdd k₁ k₂, ?_⟩
  apply intOfZ_injective
  simp only [zAdd, zMul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul] at hk₁ hk₂ ⊢
  have hk₁' := congrArg intOfZ hk₁
  have hk₂' := congrArg intOfZ hk₂
  simp only [intOfZ_zOfInt] at hk₁' hk₂' ⊢
  change intOfZ a + intOfZ c =
    (intOfZ k₁ + intOfZ k₂) * intOfZ modul + (intOfZ b + intOfZ d)
  change intOfZ a = intOfZ k₁ * intOfZ modul + intOfZ b at hk₁'
  change intOfZ c = intOfZ k₂ * intOfZ modul + intOfZ d at hk₂'
  rw [hk₁', hk₂']
  rw [Int.add_mul]
  omega

theorem eqmod_neg : eqmod_negStatement := by
  intro modul x y h
  unfold eqmod at h ⊢
  rcases h with ⟨k, hk⟩
  refine ⟨zOpp k, ?_⟩
  apply intOfZ_injective
  simp only [zOpp, zAdd, zMul, ZArith.BinInt.Z.opp,
    ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul] at hk ⊢
  have hk' := congrArg intOfZ hk
  simp only [intOfZ_zOfInt] at hk' ⊢
  change -intOfZ x = -intOfZ k * intOfZ modul + -intOfZ y
  change intOfZ x = intOfZ k * intOfZ modul + intOfZ y at hk'
  rw [hk']
  rw [Int.neg_add, Int.neg_mul]

theorem eqmod_mult : eqmod_multStatement := by
  intro modul a b c d h₁ h₂
  unfold eqmod at h₁ h₂ ⊢
  rcases h₁ with ⟨k₁, hk₁⟩
  rcases h₂ with ⟨k₂, hk₂⟩
  refine ⟨zAdd (zAdd (zMul (zMul k₁ k₂) modul) (zMul k₁ d)) (zMul c k₂), ?_⟩
  apply intOfZ_injective
  simp only [zAdd, zMul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul] at hk₁ hk₂ ⊢
  have hk₁' := congrArg intOfZ hk₁
  have hk₂' := congrArg intOfZ hk₂
  simp only [intOfZ_zOfInt] at hk₁' hk₂' ⊢
  change intOfZ a * intOfZ b =
    (intOfZ k₁ * intOfZ k₂ * intOfZ modul + intOfZ k₁ * intOfZ d + intOfZ c * intOfZ k₂) * intOfZ modul +
      intOfZ c * intOfZ d
  change intOfZ a = intOfZ k₁ * intOfZ modul + intOfZ c at hk₁'
  change intOfZ b = intOfZ k₂ * intOfZ modul + intOfZ d at hk₂'
  rw [hk₁', hk₂']
  simp [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm,
    Int.add_assoc, Int.add_comm, Int.add_left_comm]

end CompCert4Lean.Lib.Zbits

namespace CompCert4Lean.Lib.Zbits

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eqmod_divides : eqmod_dividesStatement := by
  intro n m x y hxy hmn
  unfold eqmod at hxy ⊢
  rcases hxy with ⟨k₁, hk₁⟩
  rcases hmn with ⟨k₂, hk₂⟩
  refine ⟨zMul k₁ k₂, ?_⟩
  apply intOfZ_injective
  simp only [zAdd, zMul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul] at hk₁ hk₂ ⊢
  have hk₁' := congrArg intOfZ hk₁
  have hk₂' := congrArg intOfZ hk₂
  simp only [intOfZ_zOfInt] at hk₁' hk₂' ⊢
  change intOfZ x = intOfZ k₁ * intOfZ n + intOfZ y at hk₁'
  change intOfZ n = intOfZ m * intOfZ k₂ at hk₂'
  change intOfZ x = (intOfZ k₁ * intOfZ k₂) * intOfZ m + intOfZ y
  rw [hk₁', hk₂']
  simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem Ztestbit_0 : Ztestbit_0Statement := by
  intro n
  cases n <;> rfl

theorem Zshiftin_spec : Zshiftin_specStatement := by
  intro b x
  have hzero : intOfZ zZero = (0 : Int) := by decide
  have hone : intOfZ one = (1 : Int) := by decide
  have htwo : intOfZ two = (2 : Int) := by decide
  cases b
  · apply intOfZ_injective
    simp [Zshiftin, zDouble, zAdd, zMul,
      ZArith.BinInt.Z.double, ZArith.BinInt.Z.add,
      ZArith.BinInt.Z.mul, intOfZ_zOfInt, htwo, hzero]
  · apply intOfZ_injective
    simp [Zshiftin, zSuccDouble, zSucc, zDouble, zAdd, zMul,
      ZArith.BinInt.Z.succ_double, ZArith.BinInt.Z.succ,
      ZArith.BinInt.Z.double, ZArith.BinInt.Z.add,
      ZArith.BinInt.Z.mul, intOfZ_zOfInt, htwo, hone]

end CompCert4Lean.Lib.Zbits

namespace CompCert4Lean.Lib.Zbits

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem zbits_two_power_nat_succ (n : Nat) :
    two_power_nat (Nat.succ n) = zDouble (two_power_nat n) := by
  have hpow (m : Nat) :
      ZArith.BinInt.Z.pow (Zpos (.xO .xH))
          (ZArith.BinInt.Z.of_nat m) = zOfInt (2 ^ m) := by
    unfold ZArith.BinInt.Z.pow ZArith.BinInt.Z.of_nat
    simp only [intOfZ_zOfInt]
    have h2 : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
    rw [h2]
    change (if (Int.ofNat m) < 0 then Z0 else
      zOfInt ((2 : Int) ^ (Int.ofNat m).toNat)) = zOfInt (2 ^ m)
    split
    · next h => exact (Int.not_lt_of_ge (Int.natCast_nonneg _) h).elim
    · next h => simp
  unfold two_power_nat ZArith.Zpower.two_power_nat
  rw [hpow, hpow]
  apply intOfZ_injective
  simp [zDouble, zMul, ZArith.BinInt.Z.double,
    ZArith.BinInt.Z.mul, intOfZ_zOfInt, Int.pow_succ]
  have h2 : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
  rw [h2]
  exact Int.mul_comm _ _

private theorem zbits_two_power_nat_zero :
    two_power_nat 0 = Zpos .xH := by decide

private theorem zbits_double_int (x : Z) :
    intOfZ (zDouble x) = 2 * intOfZ x := by
  unfold zDouble ZArith.BinInt.Z.double ZArith.BinInt.Z.mul
  simp only [intOfZ_zOfInt]
  have h2 : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
  rw [h2]

private theorem zbits_succ_double_int (x : Z) :
    intOfZ (zSuccDouble x) = 2 * intOfZ x + 1 := by
  unfold zSuccDouble ZArith.BinInt.Z.succ_double
  unfold ZArith.BinInt.Z.double
  unfold ZArith.BinInt.Z.succ ZArith.BinInt.Z.add ZArith.BinInt.Z.mul
  simp only [intOfZ_zOfInt]
  have h2 : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
  have h1 : intOfZ (Zpos .xH) = (1 : Int) := by decide
  rw [h2, h1]

private theorem zbits_two_power_nat_pos (n : Nat) :
    0 < intOfZ (two_power_nat n) := by
  induction n with
  | zero => rw [zbits_two_power_nat_zero]; decide
  | succ n ih =>
      rw [zbits_two_power_nat_succ, zbits_double_int]
      omega

theorem P_mod_two_p_range : P_mod_two_p_rangeStatement := by
  intro n
  induction n with
  | zero =>
      intro p
      simp only [P_mod_two_p]
      change (0 ≤ intOfZ zZero ∧ intOfZ zZero < intOfZ (two_power_nat 0))
      rw [zbits_two_power_nat_zero]
      decide
  | succ n ih =>
      intro p
      have hpow := zbits_two_power_nat_succ n
      cases p with
      | xH =>
          simp only [P_mod_two_p]
          change (0 ≤ intOfZ one ∧ intOfZ one < intOfZ (two_power_nat (Nat.succ n)))
          rw [hpow]
          rw [zbits_double_int]
          have hone : intOfZ one = (1 : Int) := by decide
          rw [hone]
          have hn := zbits_two_power_nat_pos n
          omega
      | xO q =>
          have h := ih q
          simp only [P_mod_two_p]
          change (0 ≤ intOfZ (zDouble (P_mod_two_p q n)) ∧
            intOfZ (zDouble (P_mod_two_p q n)) < intOfZ (two_power_nat (Nat.succ n)))
          rw [hpow, zbits_double_int, zbits_double_int]
          change (0 ≤ intOfZ (P_mod_two_p q n) ∧
            intOfZ (P_mod_two_p q n) < intOfZ (two_power_nat n)) at h
          omega
      | xI q =>
          have h := ih q
          simp only [P_mod_two_p]
          change (0 ≤ intOfZ (zSuccDouble (P_mod_two_p q n)) ∧
            intOfZ (zSuccDouble (P_mod_two_p q n)) < intOfZ (two_power_nat (Nat.succ n)))
          rw [hpow, zbits_succ_double_int, zbits_double_int]
          change (0 ≤ intOfZ (P_mod_two_p q n) ∧
            intOfZ (P_mod_two_p q n) < intOfZ (two_power_nat n)) at h
          omega

end CompCert4Lean.Lib.Zbits

namespace CompCert4Lean.Lib.Zbits

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem Zshiftin_inj : Zshiftin_injStatement := by
  intro b1 x1 b2 x2 h
  rw [Zshiftin_spec, Zshiftin_spec] at h
  have htwo : intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Zpos
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.positive.xO
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.positive.xH)) = (2 : Int) := by
    decide
  have hzero : intOfZ CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0 = (0 : Int) := by
    decide
  have hone : intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Zpos
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.positive.xH) = (1 : Int) := by
    decide
  cases b1 <;> cases b2
  · have hi := congrArg intOfZ h
    simp [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, intOfZ_zOfInt, htwo, hzero, hone] at hi
    exact ⟨rfl, by apply intOfZ_injective; omega⟩
  · have hi := congrArg intOfZ h
    simp [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, intOfZ_zOfInt, htwo, hzero, hone] at hi
    have : False := by omega
    exact this.elim
  · have hi := congrArg intOfZ h
    simp [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, intOfZ_zOfInt, htwo, hzero, hone] at hi
    have : False := by omega
    exact this.elim
  · have hi := congrArg intOfZ h
    simp [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, intOfZ_zOfInt, htwo, hzero, hone] at hi
    exact ⟨rfl, by apply intOfZ_injective; omega⟩

end CompCert4Lean.Lib.Zbits

namespace CompCert4Lean.Lib.Zbits

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem Zdecomp : ZdecompStatement := by
  intro x
  rw [Zshiftin_spec]
  apply intOfZ_injective
  simp only [zAdd, zMul, zZero, one, two,
    ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
  have htwo : intOfZ (zPos (xO xH)) = (2 : Int) := by decide
  rw [htwo]
  have hdiv := congrArg intOfZ
    (ZArith.Zdiv.Z_div_mod_eq_full x (zPos (xO xH)))
  simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
    intOfZ_zOfInt] at hdiv
  rw [htwo] at hdiv
  have hmod : intOfZ (ZArith.BinInt.Z.modulo x (zPos (xO xH))) =
      intOfZ x % 2 := by
    change intOfZ (zOfInt (
      if intOfZ (zPos (xO xH)) = 0 then intOfZ x
      else if 0 < intOfZ (zPos (xO xH)) then
        Int.emod (intOfZ x) (intOfZ (zPos (xO xH)))
      else
        let d := -intOfZ (zPos (xO xH))
        let r := Int.emod (intOfZ x) d
        if r = 0 then 0 else r - d)) = _
    simp [htwo]
    rw [intOfZ_zOfInt]
    rfl
  cases hodd : zOdd x
  · have heven : ZArith.BinInt.Z.even x = true := by
      simpa [zOdd, ZArith.BinInt.Z.odd] using hodd
    have hpar : Int.natAbs (intOfZ x) % 2 = 0 := by
      exact of_decide_eq_true (by simpa [ZArith.BinInt.Z.even] using heven)
    have hrem : intOfZ x % 2 = 0 := by
      rcases Int.emod_two_eq (intOfZ x) with hr | hr
      · exact hr
      · have hp := Int.natAbs_emod_two (intOfZ x)
        rw [hr] at hp
        simp at hp
        omega
    have hmod0 : intOfZ (ZArith.BinInt.Z.modulo x (zPos (xO xH))) = 0 := by
      rw [hmod, hrem]
    change intOfZ x = 2 * intOfZ (ZArith.BinInt.Z.div x (zPos (xO xH))) + 0
    simpa [hmod0] using hdiv
  · have heven : ZArith.BinInt.Z.even x = false := by
      simpa [zOdd, ZArith.BinInt.Z.odd] using hodd
    have hpar : ¬ Int.natAbs (intOfZ x) % 2 = 0 := by
      exact of_decide_eq_false (by simpa [ZArith.BinInt.Z.even] using heven)
    have hrem : intOfZ x % 2 = 1 := by
      rcases Int.emod_two_eq (intOfZ x) with hr | hr
      · have hp := Int.natAbs_emod_two (intOfZ x)
        rw [hr] at hp
        simp at hp
        exact (hpar hp).elim
      · exact hr
    have hmod1 : intOfZ (ZArith.BinInt.Z.modulo x (zPos (xO xH))) = 1 := by
      rw [hmod, hrem]
    change intOfZ x = 2 * intOfZ (ZArith.BinInt.Z.div x (zPos (xO xH))) + 1
    simpa [hmod1] using hdiv

end CompCert4Lean.Lib.Zbits
namespace CompCert4Lean.Lib.Zbits

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem zbits_nat_testbit_double_zero (a : Nat) :
    Nat.testBit (2 * a) 0 = false := by
  rw [Nat.testBit_zero]
  simp

private theorem zbits_nat_testbit_succ_double_zero (a : Nat) :
    Nat.testBit (2 * a + 1) 0 = true := by
  rw [Nat.testBit_zero]
  simp

private theorem zbits_nat_testbit_double_succ (a j : Nat) :
    Nat.testBit (2 * a) (j + 1) = Nat.testBit a j := by
  rw [Nat.testBit_succ]
  congr 1
  omega

private theorem zbits_nat_testbit_succ_double_succ (a j : Nat) :
    Nat.testBit (2 * a + 1) (j + 1) = Nat.testBit a j := by
  rw [Nat.testBit_succ]
  congr 1
  omega

private theorem zbits_nat_testbit_pred_double_zero (a : Nat) (ha : 0 < a) :
    Nat.testBit (2 * a - 1) 0 = true := by
  rw [Nat.testBit_zero]
  have h : (2 * a - 1) % 2 = 1 := by omega
  simp [h]

private theorem zbits_nat_testbit_pred_double_succ (a j : Nat) (ha : 0 < a) :
    Nat.testBit (2 * a - 1) (j + 1) = Nat.testBit (a - 1) j := by
  rw [Nat.testBit_succ]
  have h : (2 * a - 1) / 2 = a - 1 := by omega
  rw [h]

private theorem zbits_nat_testbit_pred_double_pred_succ (a j : Nat) (ha : 0 < a) :
    Nat.testBit ((2 * a - 1) - 1) (j + 1) = Nat.testBit (a - 1) j := by
  have h : (2 * a - 1) - 1 = 2 * (a - 1) := by omega
  rw [h]
  exact zbits_nat_testbit_double_succ (a - 1) j

private theorem zbits_double_pos (q : positive) :
    zDouble (Zpos q) = Zpos (PArith.BinPos.Pos.of_nat (2 * posToNat q)) := by
  apply intOfZ_injective
  simp only [zDouble, ZArith.BinInt.Z.double, zMul, ZArith.BinInt.Z.mul,
    intOfZ_zOfInt]
  simp only [intOfZ, posToNat]
  have hq : 0 < 2 * posToNat q := by
    have := posToNat_positive q
    omega
  have hpos : posToNat (PArith.BinPos.Pos.of_nat (2 * posToNat q)) =
      2 * posToNat q := by
    simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat hq
  rw [hpos]
  simp [Int.mul_neg, Int.natCast_mul]

private theorem zbits_double_neg (q : positive) :
    zDouble (Zneg q) = Zneg (PArith.BinPos.Pos.of_nat (2 * posToNat q)) := by
  apply intOfZ_injective
  simp only [zDouble, ZArith.BinInt.Z.double, zMul, ZArith.BinInt.Z.mul,
    intOfZ_zOfInt]
  simp only [intOfZ, posToNat]
  have hq : 0 < 2 * posToNat q := by
    have := posToNat_positive q
    omega
  have hpos : posToNat (PArith.BinPos.Pos.of_nat (2 * posToNat q)) =
      2 * posToNat q := by
    simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat hq
  rw [hpos]
  simp [Int.mul_neg, Int.natCast_mul]

private theorem zbits_succ_double_pos (q : positive) :
    zSuccDouble (Zpos q) = Zpos (PArith.BinPos.Pos.of_nat (2 * posToNat q + 1)) := by
  apply intOfZ_injective
  simp only [zSuccDouble, ZArith.BinInt.Z.succ_double, zSucc,
    ZArith.BinInt.Z.succ, zDouble, ZArith.BinInt.Z.double, zMul,
    ZArith.BinInt.Z.mul, zAdd, ZArith.BinInt.Z.add,
    intOfZ_zOfInt]
  simp only [intOfZ, posToNat]
  have hq : 0 < 2 * posToNat q + 1 := by
    have := posToNat_positive q
    omega
  have hpos : posToNat (PArith.BinPos.Pos.of_nat (2 * posToNat q + 1)) =
      2 * posToNat q + 1 := by
    simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat hq
  rw [hpos]
  simp [Int.natCast_mul, Int.natCast_add]

private theorem zbits_succ_double_neg (q : positive) :
    zSuccDouble (Zneg q) = Zneg (PArith.BinPos.Pos.of_nat (2 * posToNat q - 1)) := by
  have hq : 0 < posToNat q := posToNat_positive q
  have hq' : 0 < 2 * posToNat q - 1 := by omega
  apply intOfZ_injective
  simp only [zSuccDouble, ZArith.BinInt.Z.succ_double, zSucc,
    ZArith.BinInt.Z.succ, zDouble, ZArith.BinInt.Z.double, zMul,
    ZArith.BinInt.Z.mul, zAdd, ZArith.BinInt.Z.add,
    intOfZ_zOfInt]
  simp only [intOfZ, posToNat]
  have hpos : posToNat (PArith.BinPos.Pos.of_nat (2 * posToNat q - 1)) =
      2 * posToNat q - 1 := by
    simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat hq'
  rw [hpos]
  have hsub : (Int.ofNat (2 * posToNat q - 1) : Int) =
      Int.ofNat (2 * posToNat q) - 1 := by
    simpa [Int.ofNat_eq_natCast] using
      (Int.ofNat_sub (m := 1) (n := 2 * posToNat q) (by omega))
  rw [hsub]
  simp [Int.mul_neg, Int.natCast_mul]
  omega

private theorem zbits_pred_pos_xH :
    zPred (Zpos xH) = zZero := by rfl

private theorem zbits_pred_pos (p : positive) (hp : 1 < posToNat p) :
    zPred (Zpos p) = Zpos (PArith.BinPos.Pos.of_nat (posToNat p - 1)) := by
  have hp' : 0 < posToNat p - 1 := by omega
  apply intOfZ_injective
  simp only [zPred, ZArith.BinInt.Z.pred, ZArith.BinInt.Z.sub,
    intOfZ_zOfInt]
  simp only [intOfZ, posToNat]
  have hpos : posToNat (PArith.BinPos.Pos.of_nat (posToNat p - 1)) =
      posToNat p - 1 := by
    simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat hp'
  rw [hpos]
  have hsub : (Int.ofNat (posToNat p - 1) : Int) =
      Int.ofNat (posToNat p) - 1 := by
    simpa [Int.ofNat_eq_natCast] using
      (Int.ofNat_sub (m := 1) (n := posToNat p) (by omega))
  rw [hsub]
  simp [Int.natCast_mul]

private theorem zbits_testbit_pos_index (q : positive) (N : Nat) (hN : 0 < N) :
    zTestbit (Zpos q) (Zpos (PArith.BinPos.Pos.of_nat N)) =
      Nat.testBit (posToNat q) N := by
  have hidx : posToNat (PArith.BinPos.Pos.of_nat N) = N := by
    simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat hN
  simp [zTestbit, ZArith.BinInt.Z.testbit, hidx]

private theorem zbits_testbit_neg_index (q : positive) (N : Nat) (hN : 0 < N) :
    zTestbit (Zneg q) (Zpos (PArith.BinPos.Pos.of_nat N)) =
      !(Nat.testBit (posToNat q - 1) N) := by
  have hidx : posToNat (PArith.BinPos.Pos.of_nat N) = N := by
    simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat hN
  simp [zTestbit, ZArith.BinInt.Z.testbit, hidx]

private theorem zbits_testbit_pos_raw (q p : positive) :
    zTestbit (Zpos q) (Zpos p) = Nat.testBit (posToNat q) (posToNat p) := by
  rfl

private theorem zbits_testbit_neg_raw (q p : positive) :
    zTestbit (Zneg q) (Zpos p) = !(Nat.testBit (posToNat q - 1) (posToNat p)) := by
  rfl

private theorem zbits_testbit_pos_zero (q : positive) :
    zTestbit (Zpos q) zZero = Nat.testBit (posToNat q) 0 := by
  simp only [zTestbit, ZArith.BinInt.Z.testbit, ZArith.BinInt.Z.odd,
    ZArith.BinInt.Z.even, intOfZ]
  rw [Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one (posToNat q) with h | h <;> simp [h]

private theorem zbits_testbit_neg_zero (q : positive) :
    zTestbit (Zneg q) zZero = !(Nat.testBit (posToNat q - 1) 0) := by
  simp only [zTestbit, ZArith.BinInt.Z.testbit, ZArith.BinInt.Z.odd,
    ZArith.BinInt.Z.even, intOfZ]
  rw [Nat.testBit_zero]
  have hq : 0 < posToNat q := posToNat_positive q
  rcases Nat.mod_two_eq_zero_or_one (posToNat q) with h | h <;> simp [h] <;> omega

private theorem zbits_testbit_pos_one (q : positive) :
    zTestbit (Zpos q) (Zpos xH) = Nat.testBit (posToNat q) 1 := by
  rfl

private theorem zbits_testbit_neg_one (q : positive) :
    zTestbit (Zneg q) (Zpos xH) = !(Nat.testBit (posToNat q - 1) 1) := by
  rfl

private theorem zbits_odd_double_pos (q : positive) :
    ZArith.BinInt.Z.odd (Zpos (PArith.BinPos.Pos.of_nat (2 * posToNat q))) = false := by
  have hq : 0 < 2 * posToNat q := by
    have := posToNat_positive q
    omega
  have hidx : posToNat (PArith.BinPos.Pos.of_nat (2 * posToNat q)) =
      2 * posToNat q := by
    simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat hq
  simp only [ZArith.BinInt.Z.odd, ZArith.BinInt.Z.even, intOfZ, hidx]
  simp [Int.natAbs] <;> omega

private theorem zbits_odd_double_neg (q : positive) :
    ZArith.BinInt.Z.odd (Zneg (PArith.BinPos.Pos.of_nat (2 * posToNat q))) = false := by
  have hq : 0 < 2 * posToNat q := by
    have := posToNat_positive q
    omega
  have hidx : posToNat (PArith.BinPos.Pos.of_nat (2 * posToNat q)) =
      2 * posToNat q := by
    simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat hq
  simp only [ZArith.BinInt.Z.odd, ZArith.BinInt.Z.even, intOfZ, hidx]
  rw [Int.natAbs_neg]
  simp [Int.natAbs] <;> omega

private theorem zbits_odd_succ_double_pos (q : positive) :
    ZArith.BinInt.Z.odd (Zpos (PArith.BinPos.Pos.of_nat (2 * posToNat q + 1))) = true := by
  have hq : 0 < 2 * posToNat q + 1 := by
    have := posToNat_positive q
    omega
  have hidx : posToNat (PArith.BinPos.Pos.of_nat (2 * posToNat q + 1)) =
      2 * posToNat q + 1 := by
    simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat hq
  simp only [ZArith.BinInt.Z.odd, ZArith.BinInt.Z.even, intOfZ, hidx]
  simp [Int.natAbs] <;> omega

private theorem zbits_odd_succ_double_neg (q : positive) :
    ZArith.BinInt.Z.odd (Zneg (PArith.BinPos.Pos.of_nat (2 * posToNat q - 1))) = true := by
  have hq : 0 < posToNat q := posToNat_positive q
  have hq' : 0 < 2 * posToNat q - 1 := by omega
  have hidx : posToNat (PArith.BinPos.Pos.of_nat (2 * posToNat q - 1)) =
      2 * posToNat q - 1 := by
    simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat hq'
  simp only [ZArith.BinInt.Z.odd, ZArith.BinInt.Z.even, intOfZ, hidx]
  rw [Int.natAbs_neg]
  simp [Int.natAbs] <;> omega

private theorem zbits_double_shift_pos (x : Z) (p : positive) (hp : 1 < posToNat p) :
    zTestbit (zDouble x) (Zpos p) =
      zTestbit x (Zpos (PArith.BinPos.Pos.of_nat (posToNat p - 1))) := by
  cases p with
  | xH => simp [posToNat] at hp
  | xI r =>
      have hr : 0 < posToNat r := posToNat_positive r
      have hri : posToNat (xI r) = 2 * posToNat r + 1 := rfl
      cases x with
      | Z0 => rfl
      | Zpos q =>
          have hq : 0 < posToNat q := posToNat_positive q
          rw [zbits_double_pos]
          simp only [zTestbit, ZArith.BinInt.Z.testbit]
          have hleft : posToNat (PArith.BinPos.Pos.of_nat (2 * posToNat q)) =
              2 * posToNat q := by
            simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat (by omega : 0 < 2 * posToNat q)
          have hright : posToNat (PArith.BinPos.Pos.of_nat
              (posToNat (xI r) - 1)) = 2 * posToNat r := by
            rw [hri]
            simpa [PArith.BinPos.Pos.of_nat] using
              posToNat_posOfNat (by omega : 0 < 2 * posToNat r)
          rw [hleft, hright, hri]
          exact zbits_nat_testbit_double_succ _ _
      | Zneg q =>
          have hq : 0 < posToNat q := posToNat_positive q
          rw [zbits_double_neg]
          simp only [zTestbit, ZArith.BinInt.Z.testbit]
          have hleft : posToNat (PArith.BinPos.Pos.of_nat (2 * posToNat q)) =
              2 * posToNat q := by
            simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat (by omega : 0 < 2 * posToNat q)
          have hright : posToNat (PArith.BinPos.Pos.of_nat
              (posToNat (xI r) - 1)) = 2 * posToNat r := by
            rw [hri]
            simpa [PArith.BinPos.Pos.of_nat] using
              posToNat_posOfNat (by omega : 0 < 2 * posToNat r)
          rw [hleft, hright, hri]
          exact congrArg Bool.not (zbits_nat_testbit_pred_double_succ
            (posToNat q) (2 * posToNat r) (posToNat_positive q))
  | xO r =>
      have hr : 0 < posToNat r := posToNat_positive r
      have hro : posToNat (xO r) = 2 * posToNat r := rfl
      have hj : 0 < 2 * posToNat r - 1 := by omega
      cases x with
      | Z0 => rfl
      | Zpos q =>
          have hq : 0 < posToNat q := posToNat_positive q
          rw [zbits_double_pos]
          simp only [zTestbit, ZArith.BinInt.Z.testbit]
          have hleft : posToNat (PArith.BinPos.Pos.of_nat (2 * posToNat q)) =
              2 * posToNat q := by
            simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat (by omega : 0 < 2 * posToNat q)
          have hright : posToNat (PArith.BinPos.Pos.of_nat
              (posToNat (xO r) - 1)) = 2 * posToNat r - 1 := by
            rw [hro]
            simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat hj
          rw [hleft, hright, hro]
          have heq : 2 * posToNat r = (2 * posToNat r - 1) + 1 := by omega
          rw [heq]
          exact zbits_nat_testbit_double_succ _ _
      | Zneg q =>
          have hq : 0 < posToNat q := posToNat_positive q
          rw [zbits_double_neg]
          simp only [zTestbit, ZArith.BinInt.Z.testbit]
          have hleft : posToNat (PArith.BinPos.Pos.of_nat (2 * posToNat q)) =
              2 * posToNat q := by
            simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat (by omega : 0 < 2 * posToNat q)
          have hright : posToNat (PArith.BinPos.Pos.of_nat
              (posToNat (xO r) - 1)) = 2 * posToNat r - 1 := by
            rw [hro]
            simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat hj
          rw [hleft, hright, hro]
          have heq : 2 * posToNat r = (2 * posToNat r - 1) + 1 := by omega
          rw [heq]
          have hs : (2 * posToNat r - 1 + 1 - 1) = 2 * posToNat r - 1 := by omega
          rw [hs]
          exact congrArg Bool.not (zbits_nat_testbit_pred_double_succ
            (posToNat q) (2 * posToNat r - 1) (posToNat_positive q))

private theorem zbits_succ_double_shift_pos (x : Z) (p : positive) (hp : 1 < posToNat p) :
    zTestbit (zSuccDouble x) (Zpos p) =
      zTestbit x (Zpos (PArith.BinPos.Pos.of_nat (posToNat p - 1))) := by
  cases p with
  | xH => simp [posToNat] at hp
  | xI r =>
      have hr : 0 < posToNat r := posToNat_positive r
      have hri : posToNat (xI r) = 2 * posToNat r + 1 := rfl
      cases x with
      | Z0 =>
          simp [zSuccDouble, ZArith.BinInt.Z.succ_double, zSucc,
            ZArith.BinInt.Z.succ, zDouble, ZArith.BinInt.Z.double,
            zMul, ZArith.BinInt.Z.mul, zAdd, ZArith.BinInt.Z.add,
            zTestbit, ZArith.BinInt.Z.testbit, ZArith.BinInt.Z.odd,
            ZArith.BinInt.Z.even, intOfZ, zOfInt, posToNat]
          apply Nat.testBit_lt_two_pow
          apply Nat.one_lt_two_pow
          omega
      | Zpos q =>
          have hq : 0 < posToNat q := posToNat_positive q
          rw [zbits_succ_double_pos]
          simp only [zTestbit, ZArith.BinInt.Z.testbit]
          have hleft : posToNat (PArith.BinPos.Pos.of_nat (2 * posToNat q + 1)) =
              2 * posToNat q + 1 := by
            simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat (by omega : 0 < 2 * posToNat q + 1)
          have hright : posToNat (PArith.BinPos.Pos.of_nat
              (posToNat (xI r) - 1)) = 2 * posToNat r := by
            rw [hri]
            simpa [PArith.BinPos.Pos.of_nat] using
              posToNat_posOfNat (by omega : 0 < 2 * posToNat r)
          rw [hleft, hright, hri]
          exact zbits_nat_testbit_succ_double_succ _ _
      | Zneg q =>
          have hq : 0 < posToNat q := posToNat_positive q
          rw [zbits_succ_double_neg]
          simp only [zTestbit, ZArith.BinInt.Z.testbit]
          have hleft : posToNat (PArith.BinPos.Pos.of_nat (2 * posToNat q - 1)) =
              2 * posToNat q - 1 := by
            simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat (by omega : 0 < 2 * posToNat q - 1)
          have hright : posToNat (PArith.BinPos.Pos.of_nat
              (posToNat (xI r) - 1)) = 2 * posToNat r := by
            rw [hri]
            simpa [PArith.BinPos.Pos.of_nat] using
              posToNat_posOfNat (by omega : 0 < 2 * posToNat r)
          rw [hleft, hright, hri]
          exact congrArg Bool.not (zbits_nat_testbit_pred_double_pred_succ
            (posToNat q) (2 * posToNat r) (posToNat_positive q))
  | xO r =>
      have hr : 0 < posToNat r := posToNat_positive r
      have hro : posToNat (xO r) = 2 * posToNat r := rfl
      have hj : 0 < 2 * posToNat r - 1 := by omega
      cases x with
      | Z0 =>
          simp [zSuccDouble, ZArith.BinInt.Z.succ_double, zSucc,
            ZArith.BinInt.Z.succ, zDouble, ZArith.BinInt.Z.double,
            zMul, ZArith.BinInt.Z.mul, zAdd, ZArith.BinInt.Z.add,
            zTestbit, ZArith.BinInt.Z.testbit, ZArith.BinInt.Z.odd,
            ZArith.BinInt.Z.even, intOfZ, zOfInt, posToNat]
          apply Nat.testBit_lt_two_pow
          apply Nat.one_lt_two_pow
          omega
      | Zpos q =>
          have hq : 0 < posToNat q := posToNat_positive q
          rw [zbits_succ_double_pos]
          simp only [zTestbit, ZArith.BinInt.Z.testbit]
          have hleft : posToNat (PArith.BinPos.Pos.of_nat (2 * posToNat q + 1)) =
              2 * posToNat q + 1 := by
            simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat (by omega : 0 < 2 * posToNat q + 1)
          have hright : posToNat (PArith.BinPos.Pos.of_nat
              (posToNat (xO r) - 1)) = 2 * posToNat r - 1 := by
            rw [hro]
            simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat hj
          rw [hleft, hright, hro]
          have heq : 2 * posToNat r = (2 * posToNat r - 1) + 1 := by omega
          rw [heq]
          exact zbits_nat_testbit_succ_double_succ _ _
      | Zneg q =>
          have hq : 0 < posToNat q := posToNat_positive q
          rw [zbits_succ_double_neg]
          simp only [zTestbit, ZArith.BinInt.Z.testbit]
          have hleft : posToNat (PArith.BinPos.Pos.of_nat (2 * posToNat q - 1)) =
              2 * posToNat q - 1 := by
            simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat (by omega : 0 < 2 * posToNat q - 1)
          have hright : posToNat (PArith.BinPos.Pos.of_nat
              (posToNat (xO r) - 1)) = 2 * posToNat r - 1 := by
            rw [hro]
            simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat hj
          rw [hleft, hright, hro]
          have heq : (2 * posToNat q - 1 - 1) = 2 * (posToNat q - 1) := by omega
          rw [heq]
          have heq' : 2 * posToNat r = (2 * posToNat r - 1) + 1 := by omega
          rw [heq']
          exact congrArg Bool.not (zbits_nat_testbit_double_succ
            (posToNat q - 1) (2 * posToNat r - 1))

theorem Ztestbit_shiftin : Ztestbit_shiftinStatement := by
  intro b x n hn
  cases n with
  | Zneg p =>
      have hp : 0 < posToNat p := posToNat_positive p
      simp [ZArith.BinInt.Z.le, intOfZ] at hn
      omega
  | Z0 =>
      simp [sumboolSelect, zeqDec, CompCert4Lean.Lib.Coqlib.zeq,
        ZArith.BinInt.Z.eq_dec]
      cases b with
      | false =>
          rw [show Zshiftin false x = zDouble x by rfl]
          cases x with
          | Z0 => rfl
          | Zpos q =>
              rw [zbits_double_pos]
              exact zbits_odd_double_pos q
          | Zneg q =>
              rw [zbits_double_neg]
              exact zbits_odd_double_neg q
      | true =>
          rw [show Zshiftin true x = zSuccDouble x by rfl]
          cases x with
          | Z0 => rfl
          | Zpos q =>
              rw [zbits_succ_double_pos]
              exact zbits_odd_succ_double_pos q
          | Zneg q =>
              rw [zbits_succ_double_neg]
              exact zbits_odd_succ_double_neg q
  | Zpos p =>
      simp [sumboolSelect, zeqDec, CompCert4Lean.Lib.Coqlib.zeq,
        ZArith.BinInt.Z.eq_dec]
      cases p with
      | xH =>
          rw [zbits_pred_pos_xH]
          cases b with
          | false =>
              rw [show Zshiftin false x = zDouble x by rfl]
              cases x with
              | Z0 => rfl
              | Zpos q =>
                  rw [zbits_double_pos]
                  have hq : 0 < 2 * posToNat q := by
                    have := posToNat_positive q
                    omega
                  have hidx : posToNat (PArith.BinPos.Pos.of_nat (2 * posToNat q)) =
                      2 * posToNat q := by
                    simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat hq
                  rw [zbits_testbit_pos_one, zbits_testbit_pos_zero]
                  rw [hidx]
                  exact zbits_nat_testbit_double_succ _ 0
              | Zneg q =>
                  rw [zbits_double_neg]
                  have hq : 0 < 2 * posToNat q := by
                    have := posToNat_positive q
                    omega
                  have hidx : posToNat (PArith.BinPos.Pos.of_nat (2 * posToNat q)) =
                      2 * posToNat q := by
                    simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat hq
                  rw [zbits_testbit_neg_one, zbits_testbit_neg_zero]
                  rw [hidx]
                  exact congrArg Bool.not (zbits_nat_testbit_pred_double_succ
                    (posToNat q) 0 (posToNat_positive q))
          | true =>
              rw [show Zshiftin true x = zSuccDouble x by rfl]
              cases x with
              | Z0 => rfl
              | Zpos q =>
                  rw [zbits_succ_double_pos]
                  have hq : 0 < 2 * posToNat q + 1 := by
                    have := posToNat_positive q
                    omega
                  have hidx : posToNat (PArith.BinPos.Pos.of_nat (2 * posToNat q + 1)) =
                      2 * posToNat q + 1 := by
                    simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat hq
                  rw [zbits_testbit_pos_one, zbits_testbit_pos_zero]
                  rw [hidx]
                  exact zbits_nat_testbit_succ_double_succ _ 0
              | Zneg q =>
                  rw [zbits_succ_double_neg]
                  have hq : 0 < 2 * posToNat q - 1 := by
                    have := posToNat_positive q
                    omega
                  have hidx : posToNat (PArith.BinPos.Pos.of_nat (2 * posToNat q - 1)) =
                      2 * posToNat q - 1 := by
                    simpa [PArith.BinPos.Pos.of_nat] using posToNat_posOfNat hq
                  rw [zbits_testbit_neg_one, zbits_testbit_neg_zero]
                  rw [hidx]
                  exact congrArg Bool.not (zbits_nat_testbit_pred_double_pred_succ
                    (posToNat q) 0 (posToNat_positive q))
      | xI q =>
          have hp : 1 < posToNat (xI q) := by
            simp [posToNat]
            have := posToNat_positive q
            omega
          rw [zbits_pred_pos _ hp]
          cases b with
          | false =>
              rw [show Zshiftin false x = zDouble x by rfl]
              exact zbits_double_shift_pos x (xI q) hp
          | true =>
              rw [show Zshiftin true x = zSuccDouble x by rfl]
              exact zbits_succ_double_shift_pos x (xI q) hp
      | xO q =>
          have hp : 1 < posToNat (xO q) := by
            simp [posToNat]
            have := posToNat_positive q
            omega
          rw [zbits_pred_pos _ hp]
          cases b with
          | false =>
              rw [show Zshiftin false x = zDouble x by rfl]
              exact zbits_double_shift_pos x (xO q) hp
          | true =>
              rw [show Zshiftin true x = zSuccDouble x by rfl]
              exact zbits_succ_double_shift_pos x (xO q) hp

end CompCert4Lean.Lib.Zbits

namespace CompCert4Lean.Lib.Zbits

theorem Ztestbit_eq : Ztestbit_eqStatement := by
  intro n x hn
  calc
    zTestbit x n = zTestbit (Zshiftin (zOdd x) (zDiv2 x)) n :=
      congrArg (fun y => zTestbit y n) (Zdecomp x)
    _ = sumboolSelect (zeqDec n zZero) (zOdd x)
        (zTestbit (zDiv2 x) (zPred n)) :=
      Ztestbit_shiftin (zOdd x) (zDiv2 x) n hn
