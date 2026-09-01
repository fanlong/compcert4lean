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
