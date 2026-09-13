import Std
import CompCert4Lean.Foundation.Logic

/-!
# Rocq numerical standard-library facade

This module is the checked definition-translation surface for the numerical
parts of the Rocq standard library used by CompCert and Flocq.  The binary
positive and signed integer representations are source-shaped; arithmetic is
performed through Lean's checked `Nat`/`Int` primitives and converted back to
the source representation.  In particular, `Z.div`/`Z.modulo` use Euclidean
division while `Z.quot` uses truncating division, matching the two operations
used by CompCert.
-/

namespace CompCert4Lean.Foundation.Numbers
namespace Rocq.Coq

universe u

abbrev comparison := _root_.CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.comparison
abbrev Lt : comparison := _root_.CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.comparison.Lt
abbrev Eq : comparison := _root_.CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.comparison.Eq
abbrev Gt : comparison := _root_.CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.comparison.Gt
abbrev CompOpp := _root_.CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.CompOpp

namespace Support
abbrev Sumbool := _root_.CompCert4Lean.Foundation.Logic.Support.Sumbool
abbrev Sumor := _root_.CompCert4Lean.Foundation.Logic.Support.Sumor
end Support

instance : DecidableEq comparison := fun a b =>
  match a, b with
  | .Lt, .Lt => isTrue rfl
  | .Lt, .Eq => isFalse (by intro h; cases h)
  | .Lt, .Gt => isFalse (by intro h; cases h)
  | .Eq, .Lt => isFalse (by intro h; cases h)
  | .Eq, .Eq => isTrue rfl
  | .Eq, .Gt => isFalse (by intro h; cases h)
  | .Gt, .Lt => isFalse (by intro h; cases h)
  | .Gt, .Eq => isFalse (by intro h; cases h)
  | .Gt, .Gt => isTrue rfl

namespace Numbers.BinNums

inductive positive : Type where
  | xH : positive
  | xI : positive → positive
  | xO : positive → positive
deriving DecidableEq

inductive N : Type where
  | N0 : N
  | Npos : positive → N
deriving DecidableEq

inductive Z : Type where
  | Z0 : Z
  | Zpos : positive → Z
  | Zneg : positive → Z
deriving DecidableEq

end Numbers.BinNums

abbrev positive := Numbers.BinNums.positive
abbrev N := Numbers.BinNums.N
abbrev Z := Numbers.BinNums.Z
abbrev xH : positive := Numbers.BinNums.positive.xH
abbrev xI : positive → positive := Numbers.BinNums.positive.xI
abbrev xO : positive → positive := Numbers.BinNums.positive.xO
abbrev Z0 : Z := Numbers.BinNums.Z.Z0
abbrev Zneg : positive → Z := Numbers.BinNums.Z.Zneg
abbrev Zpos : positive → Z := Numbers.BinNums.Z.Zpos
abbrev le := _root_.Nat.le
abbrev lt := _root_.Nat.lt
abbrev orb := _root_.Bool.or

namespace Numbers.BinNums

export positive (xH xI xO)
export N (N0 Npos)
export Z (Z0 Zneg Zpos)

end Numbers.BinNums

def posToNat : positive → Nat
  | .xH => 1
  | .xI p => 2 * posToNat p + 1
  | .xO p => 2 * posToNat p

private def collectBits : Nat → Nat → List Bool
  | 0, _ => []
  | fuel + 1, n =>
      if n < 2 then []
      else (n % 2 = 1) :: collectBits fuel (n / 2)

private def foldBits : List Bool → positive
  | [] => .xH
  | b :: bs =>
      let p := foldBits bs
      if b then .xI p else .xO p

def posOfNat (n : Nat) : positive := foldBits (collectBits n n)

private theorem posToNat_foldBits_collectBits
    (fuel n : Nat) (hn : 0 < n) (hpow : n < 2 ^ fuel) :
    posToNat (foldBits (collectBits fuel n)) = n := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
      by_cases hsmall : n < 2
      · have hn1 : n = 1 := by omega
        simp [collectBits, foldBits, posToNat, hn1]
      · have hn2 : 2 ≤ n := by omega
        have hqpos : 0 < n / 2 := Nat.div_pos (by omega) (by omega)
        have hqpow : n / 2 < 2 ^ fuel := by
          apply (Nat.div_lt_iff_lt_mul (by omega)).2
          simpa [Nat.pow_succ, Nat.mul_comm] using hpow
        have hi := ih (n / 2) hqpos hqpow
        by_cases hbit : n % 2 = 1
        · simp [collectBits, foldBits, posToNat, hsmall, hbit, hi]
          omega
        · have hmod : n % 2 = 0 := by
            have hlt : n % 2 < 2 := Nat.mod_lt _ (by omega)
            omega
          simp [collectBits, foldBits, posToNat, hsmall, hmod, hi]
          omega

theorem posToNat_posOfNat {n : Nat} (hn : 0 < n) : posToNat (posOfNat n) = n := by
  exact posToNat_foldBits_collectBits n n hn (Nat.lt_pow_self (by omega))

theorem posToNat_positive (p : positive) : 0 < posToNat p := by
  induction p <;> simp [posToNat] <;> omega

theorem posToNat_injective : Function.Injective posToNat := by
  intro p
  induction p with
  | xH =>
      intro q h
      cases q with
      | xH => rfl
      | xI q =>
          simp [posToNat] at h
          have := posToNat_positive q
          omega
      | xO q =>
          simp [posToNat] at h
          have := posToNat_positive q
          omega
  | xI p ih =>
      intro q h
      cases q with
      | xH =>
          simp [posToNat] at h
          have := posToNat_positive p
          omega
      | xI q =>
          have hq : posToNat p = posToNat q := by simp [posToNat] at h ⊢; omega
          exact congrArg Numbers.BinNums.positive.xI (ih hq)
      | xO q => simp [posToNat] at h; omega
  | xO p ih =>
      intro q h
      cases q with
      | xH =>
          simp [posToNat] at h
          have := posToNat_positive p
          omega
      | xI q => simp [posToNat] at h; omega
      | xO q =>
          have hq : posToNat p = posToNat q := by simp [posToNat] at h ⊢; omega
          exact congrArg Numbers.BinNums.positive.xO (ih hq)

theorem posOfNat_posToNat (p : positive) : posOfNat (posToNat p) = p := by
  apply posToNat_injective
  simpa using posToNat_posOfNat (posToNat_positive p)

private def comparisonOfNat (a b : Nat) : comparison :=
  if a < b then .Lt else if a = b then .Eq else .Gt

private def comparisonOfInt (a b : Int) : comparison :=
  if a < b then .Lt else if a = b then .Eq else .Gt

def intOfZ : Z → Int
  | .Z0 => 0
  | .Zpos p => Int.ofNat (posToNat p)
  | .Zneg p => -Int.ofNat (posToNat p)

def zOfInt : Int → Z
  | .ofNat 0 => .Z0
  | .ofNat (n + 1) => .Zpos (posOfNat (n + 1))
  | .negSucc n => .Zneg (posOfNat (n + 1))

theorem intOfZ_zOfInt (i : Int) : intOfZ (zOfInt i) = i := by
  cases i with
  | ofNat n =>
      cases n with
      | zero => rfl
      | succ n =>
          change Int.ofNat (posToNat (posOfNat (n + 1))) = Int.ofNat (n + 1)
          rw [posToNat_posOfNat (by omega)]
  | negSucc n =>
      change -Int.ofNat (posToNat (posOfNat (n + 1))) = Int.negSucc n
      rw [posToNat_posOfNat (by omega)]
      rfl

theorem zOfInt_intOfZ (z : Z) : zOfInt (intOfZ z) = z := by
  cases z with
  | Z0 => rfl
  | Zpos p =>
      have hp := posToNat_positive p
      cases h : posToNat p with
      | zero => omega
      | succ n =>
          change zOfInt (Int.ofNat (posToNat p)) = .Zpos p
          rw [h]
          change Numbers.BinNums.Z.Zpos (posOfNat (n + 1)) = Numbers.BinNums.Z.Zpos p
          exact congrArg Numbers.BinNums.Z.Zpos (by simpa [h] using posOfNat_posToNat p)
  | Zneg p =>
      have hp := posToNat_positive p
      cases h : posToNat p with
      | zero => omega
      | succ n =>
          change zOfInt (-Int.ofNat (posToNat p)) = .Zneg p
          rw [h]
          change Numbers.BinNums.Z.Zneg (posOfNat (n + 1)) = Numbers.BinNums.Z.Zneg p
          exact congrArg Numbers.BinNums.Z.Zneg (by simpa [h] using posOfNat_posToNat p)

theorem intOfZ_injective : Function.Injective intOfZ := by
  intro x y h
  calc
    x = zOfInt (intOfZ x) := (zOfInt_intOfZ x).symm
    _ = zOfInt (intOfZ y) := congrArg zOfInt h
    _ = y := zOfInt_intOfZ y

private def natIter {α : Type u} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => natIter f n (f x)

private def zNonneg (z : Z) : Bool := 0 ≤ intOfZ z

namespace Arith.Compare_dec

def le_gt_dec (n m : Nat) : Support.Sumbool (n ≤ m) (m < n) := by
  by_cases h : n ≤ m
  · exact .left h
  · exact .right (Nat.lt_of_not_ge h)

end Arith.Compare_dec

namespace Arith.Peano_dec

abbrev eq_nat_dec (n m : Nat) : Support.Sumbool (n = m) (¬ n = m) :=
  if h : n = m then .left h else .right h

end Arith.Peano_dec

namespace Arith.PeanoNat.Nat

def eqb (n m : Nat) : Bool := decide (n = m)
def lt (n m : Nat) : Prop := n < m
def max (n m : Nat) : Nat := _root_.Nat.max n m

end Arith.PeanoNat.Nat

namespace Init.Peano

def ge (n m : Nat) : Prop := m ≤ n
def lt (n m : Nat) : Prop := n < m

end Init.Peano

namespace NArith.BinNat.N

def eq_dec (n m : N) : Support.Sumbool (n = m) (¬ n = m) := by
  cases n with
  | N0 =>
      cases m with
      | N0 => exact .left rfl
      | Npos p => exact .right (by intro h; cases h)
  | Npos p =>
      cases m with
      | N0 => exact .right (by intro h; cases h)
      | Npos q =>
          by_cases h : p = q
          · exact .left (by cases h; rfl)
          · exact .right (by intro h'; cases h'; exact h rfl)

def to_nat : N → Nat
  | .N0 => 0
  | .Npos p => posToNat p

end NArith.BinNat.N

namespace N
abbrev to_nat := NArith.BinNat.N.to_nat
end N

namespace PArith.BinPos

namespace Pos

def to_nat (p : positive) : Nat := posToNat p
abbrev nat_of_P := to_nat

def add (p q : positive) : positive := posOfNat (posToNat p + posToNat q)
def succ : positive → positive
  | .xH => .xO .xH
  | .xI p => .xO (succ p)
  | .xO p => .xI p
def pred_double : positive → positive
  | .xH => .xH
  | .xI p => .xI (.xO p)
  | .xO p => .xI (pred_double p)
def pred : positive → positive
  | .xH => .xH
  | .xI p => .xO p
  | .xO p => pred_double p
def sub (p q : positive) : positive := posOfNat (posToNat p - posToNat q)
def of_nat (n : Nat) : positive := posOfNat n
def compare (p q : positive) : comparison := comparisonOfNat (posToNat p) (posToNat q)
def compare_cont (c : comparison) (p q : positive) : comparison :=
  match c with
  | .Eq => compare p q
  | .Lt => if compare p q = .Eq then .Lt else compare p q
  | .Gt => if compare p q = .Eq then .Gt else compare p q
def eqb (p q : positive) : Bool := decide (p = q)
def le (p q : positive) : Prop := posToNat p ≤ posToNat q
def lt (p q : positive) : Prop := posToNat p < posToNat q
def leb (p q : positive) : Bool := if posToNat p ≤ posToNat q then true else false
def lor (p q : positive) : positive := posOfNat (Nat.lor (posToNat p) (posToNat q))
def max (p q : positive) : positive := if posToNat p ≤ posToNat q then q else p
def mul (p q : positive) : positive := posOfNat (posToNat p * posToNat q)
def iter {A : Type u} (f : A → A) (x : A) (p : positive) : A := natIter f (posToNat p) x

private theorem succ_pred_double (p : positive) : succ (pred_double p) = .xO p := by
  induction p with
  | xH => rfl
  | xI q ih => rfl
  | xO q ih => simp [pred_double, succ, ih]

private theorem succ_pred_nonH (p : positive) (h : p ≠ .xH) : succ (pred p) = p := by
  cases p with
  | xH => contradiction
  | xI q => rfl
  | xO q => simpa [pred] using succ_pred_double q

private theorem posToNat_pred_double_lt (p : positive) :
    posToNat (pred_double p) < 2 * posToNat p := by
  induction p with
  | xH => simp [pred_double, posToNat]
  | xI q ih => simp [pred_double, posToNat]; omega
  | xO q ih =>
      simp [pred_double, posToNat]
      omega

private theorem posToNat_pred_lt (p : positive) (h : p ≠ .xH) :
    posToNat (pred p) < posToNat p := by
  cases p with
  | xH => contradiction
  | xI q => simp [pred, posToNat]
  | xO q =>
      simpa [pred, posToNat] using posToNat_pred_double_lt q

def peano_ind (P : positive → Prop) (a : P .xH)
    (f : ∀ p, P p → P (succ p)) : ∀ p, P p := by
  let rec go (p : positive) : P p :=
    if h : p = .xH then by
      simpa [h] using a
    else
      have hp : P (pred p) := go (pred p)
      have hs : P (succ (pred p)) := f (pred p) hp
      by simpa [succ_pred_nonH p h] using hs
  termination_by posToNat p
  decreasing_by exact posToNat_pred_lt _ h
  exact go
def shiftl_nat (p : positive) (n : Nat) : positive := posOfNat (posToNat p * 2 ^ n)
def shiftr_nat (p : positive) (n : Nat) : positive := posOfNat (posToNat p / 2 ^ n)
def size (p : positive) : positive := posOfNat (Nat.log2 (posToNat p) + 1)

def eq_dec (p q : positive) : Support.Sumbool (p = q) (¬ p = q) := by
  by_cases h : p = q
  · exact .left h
  · exact .right h

end Pos

end PArith.BinPos

abbrev PArith.BinPos.nat_of_P := PArith.BinPos.Pos.to_nat
abbrev PArith.BinPos.Pcompare_antisym : Prop :=
  ∀ (p q : positive) (c : comparison),
    CompOpp (PArith.BinPos.Pos.compare_cont c p q) = PArith.BinPos.Pos.compare_cont (CompOpp c) q p
abbrev PArith.Pnat.lt_O_nat_of_P : Prop := ∀ p : positive, 0 < PArith.BinPos.Pos.to_nat p

namespace PArith.Pnat.Pos2Nat

theorem id (p : positive) :
    PArith.BinPos.Pos.of_nat (PArith.BinPos.Pos.to_nat p) = p :=
  posOfNat_posToNat p

end PArith.Pnat.Pos2Nat

namespace ZArith.BinInt

namespace Z

abbrev Z0 : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z :=
  _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0
abbrev Zpos : positive → _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z :=
  _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Zpos
abbrev Zneg : positive → _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z :=
  _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Zneg

def abs (z : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) :=
  zOfInt (Int.natAbs (intOfZ z))
def abs_nat (z : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : Nat := Int.toNat (intOfZ (abs z))
def add (x y : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) := zOfInt (intOfZ x + intOfZ y)
def sub (x y : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) := zOfInt (intOfZ x - intOfZ y)
def mul (x y : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) := zOfInt (intOfZ x * intOfZ y)
def opp (x : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) := zOfInt (-intOfZ x)
/- The Rocq `Z.neg` name is the negative constructor, not integer
   opposition.  Keep opposition under its source name `Z.opp` and reserve
   `Z.neg` for the constructor-shaped `positive -> Z` API. -/
abbrev neg : positive → _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z := Zneg
def compare (x y : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) := comparisonOfInt (intOfZ x) (intOfZ y)
def le (x y : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : Prop := intOfZ x ≤ intOfZ y
def lt (x y : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : Prop := intOfZ x < intOfZ y
def ge (x y : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : Prop := intOfZ y ≤ intOfZ x
abbrev gt (x y : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : Prop := lt y x
def geb (x y : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : Bool := if intOfZ y ≤ intOfZ x then true else false
def gtb (x y : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : Bool := if intOfZ y < intOfZ x then true else false
def leb (x y : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : Bool := if intOfZ x ≤ intOfZ y then true else false
def ltb (x y : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : Bool := if intOfZ x < intOfZ y then true else false
def max (x y : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) := if intOfZ x ≤ intOfZ y then y else x
def min (x y : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) := if intOfZ x ≤ intOfZ y then x else y
def eqb (x y : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : Bool := decide (x = y)

private def zDivEucl (a b : Int) : Int :=
  if b = 0 then 0
  else if 0 < b then Int.ediv a b
  else
    let d := -b
    let q := Int.ediv a d
    let r := Int.emod a d
    if r = 0 then -q else -(q + 1)

private def zModEucl (a b : Int) : Int :=
  if b = 0 then a
  else if 0 < b then Int.emod a b
  else
    let d := -b
    let r := Int.emod a d
    if r = 0 then 0 else r - d

private theorem zModEucl_add_mul (a b c : Int) :
    zModEucl (a + b * c) c = zModEucl a c := by
  by_cases hc0 : c = 0
  · simp [zModEucl, hc0]
  by_cases hcpos : 0 < c
  · unfold zModEucl
    simp only [hc0, hcpos, if_false, if_true]
    exact Int.add_mul_emod_self_right a b c
  · have hcneg : c < 0 := by omega
    have hr : (a + b * c) % (-c) = a % (-c) := by
      simpa [Int.mul_neg] using Int.add_neg_mul_emod_self_right a b (-c)
    unfold zModEucl
    simp only [hc0, hcpos, if_false]
    exact congrArg (fun r : Int => if r = 0 then 0 else r - (-c)) hr

def div (x y : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) := zOfInt (zDivEucl (intOfZ x) (intOfZ y))
def modulo (x y : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) := zOfInt (zModEucl (intOfZ x) (intOfZ y))
def quot (x y : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) := zOfInt (Int.tdiv (intOfZ x) (intOfZ y))
def div_eucl (x y : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) := (div x y, modulo x y)
def div2 (x : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) := div x (Zpos (.xO .xH))
def divide (a b : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : Prop := ∃ k, b = mul a k
def double (x : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) := mul (Zpos (.xO .xH)) x
def even (x : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : Bool := decide (Int.natAbs (intOfZ x) % 2 = 0)
def odd (x : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : Bool := !even x
def of_N : N → _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
  | .N0 => Z0
  | .Npos p => Zpos p
def of_nat (n : Nat) := zOfInt (Int.ofNat n)
def to_nat (z : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : Nat := Int.toNat (intOfZ z)
def to_pos (z : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : positive := PArith.BinPos.Pos.of_nat (to_nat z)
abbrev pos := Zpos
def pred (z : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) := sub z (Zpos .xH)
def succ (z : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) := add z (Zpos .xH)
def succ_double (z : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) := succ (double z)
def shiftl (x n : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) :=
  if 0 ≤ intOfZ n then zOfInt (intOfZ x * Int.pow 2 (Int.toNat (intOfZ n))) else zOfInt (Int.ediv (intOfZ x) (Int.pow 2 (Int.toNat (-intOfZ n))))
def shiftr (x n : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) :=
  if 0 ≤ intOfZ n then zOfInt (Int.ediv (intOfZ x) (Int.pow 2 (Int.toNat (intOfZ n)))) else zOfInt (intOfZ x * Int.pow 2 (Int.toNat (-intOfZ n)))
def log2 (x : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) := zOfInt (Int.ofNat (Nat.log2 (Int.toNat (intOfZ x))))
def pow (x n : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) :=
  if intOfZ n < 0 then Z0
  else zOfInt (Int.pow (intOfZ x) (Int.toNat (intOfZ n)))
def pow_pos (x : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (n : positive) := zOfInt (Int.pow (intOfZ x) (PArith.BinPos.Pos.to_nat n))
def iter (n : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    {α : Type u} (f : α → α) (x : α) : α :=
  natIter f (Int.toNat (intOfZ n)) x
def testbit (x n : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : Bool :=
  match n with
  | .Zneg _ => false
  | .Z0 => odd x
  | .Zpos p =>
      match x with
      | .Z0 => false
      | .Zpos q => Nat.testBit (posToNat q) (posToNat p)
      | .Zneg q => !(Nat.testBit (posToNat q - 1) (posToNat p))
def sqrtrem (x : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) :=
  let n := Int.toNat (intOfZ x)
  let s := Nat.sqrt n
  (zOfInt (Int.ofNat s), zOfInt (Int.ofNat (n - s * s)))
def eq_dec (x y : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) : Support.Sumbool (x = y) (¬ x = y) := by
  by_cases h : x = y
  · exact .left h
  · exact .right h

theorem modulo_add_mul
    (a b c : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) :
    modulo (add a (mul b c)) c = modulo a c := by
  apply intOfZ_injective
  simp only [modulo, add, mul, intOfZ_zOfInt]
  exact zModEucl_add_mul (intOfZ a) (intOfZ b) (intOfZ c)

theorem modulo_range
    (a b : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (hb : gt b Z0) : le Z0 (modulo a b) ∧ lt (modulo a b) b := by
  change 0 < intOfZ b at hb
  change 0 ≤ intOfZ (modulo a b) ∧ intOfZ (modulo a b) < intOfZ b
  simp only [modulo, intOfZ_zOfInt]
  unfold zModEucl
  have hb0 : intOfZ b ≠ 0 := Int.ne_of_gt hb
  simp only [hb, hb0, if_false, if_true]
  exact ⟨Int.emod_nonneg _ hb0, Int.emod_lt_of_pos _ hb⟩

theorem mod_small (a b : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (h : le Z0 a ∧ lt a b) : modulo a b = a := by
  change 0 ≤ intOfZ a ∧ intOfZ a < intOfZ b at h
  have hb : 0 < intOfZ b := Int.lt_of_le_of_lt h.1 h.2
  have hb0 : intOfZ b ≠ 0 := Int.ne_of_gt hb
  apply intOfZ_injective
  change intOfZ (zOfInt (zModEucl (intOfZ a) (intOfZ b))) = intOfZ a
  rw [intOfZ_zOfInt]
  unfold zModEucl
  simp only [hb, hb0, if_false, if_true]
  exact Int.emod_eq_of_lt h.1 h.2

end Z

abbrev Z_of_nat := Z.of_nat

abbrev Zmult_0_l (n : Z) : Prop := Z.mul Z0 n = Z0
abbrev Zmult_1_l (n : Z) : Prop := Z.mul (Zpos .xH) n = n
abbrev Zmult_1_r (n : Z) : Prop := Z.mul n (Zpos .xH) = n
abbrev Zmult := Z.mul
abbrev Zmult_comm (n m : Z) : Prop := Z.mul n m = Z.mul m n
abbrev Zmult_plus_distr_l (n m p : Z) : Prop := Z.mul (Z.add n m) p = Z.add (Z.mul n p) (Z.mul m p)
abbrev Zmult_plus_distr_r (n m p : Z) : Prop := Z.mul n (Z.add m p) = Z.add (Z.mul n m) (Z.mul n p)
abbrev Zopp_plus_distr (n m : Z) : Prop := Z.opp (Z.add n m) = Z.add (Z.opp n) (Z.opp m)
abbrev Zplus_0_r (n : Z) : Prop := Z.add n Z0 = n
abbrev Zplus := Z.add
abbrev Zplus_assoc (n m p : Z) : Prop := Z.add n (Z.add m p) = Z.add (Z.add n m) p
abbrev Zplus_comm (n m : Z) : Prop := Z.add n m = Z.add m n
abbrev Zplus_opp_l (n : Z) : Prop := Z.add (Z.opp n) n = Z0
abbrev Zplus_opp_r (n : Z) : Prop := Z.add n (Z.opp n) = Z0
abbrev Zpos_xI (p : positive) : Prop :=
  Zpos (.xI p) = Z.add (Z.mul (Zpos (.xO .xH)) (Zpos p)) (Zpos .xH)
abbrev Zpos_xO (p : positive) : Prop :=
  Zpos (.xO p) = Z.mul (Zpos (.xO .xH)) (Zpos p)

end ZArith.BinInt

namespace ZArith.ZArith_dec

def Z_dec (n m : Z) :
    _root_.CompCert4Lean.Foundation.Logic.Support.Sumor
      (_root_.CompCert4Lean.Foundation.Logic.Support.Sumbool
        (ZArith.BinInt.Z.lt n m) (ZArith.BinInt.Z.gt n m))
      (n = m) := by
  if hnm : intOfZ n < intOfZ m then
    exact .inleft (.left (show ZArith.BinInt.Z.lt n m from hnm))
  else if hmn : intOfZ m < intOfZ n then
    exact .inleft (.right (show ZArith.BinInt.Z.gt n m from hmn))
  else
    exact .inright (intOfZ_injective
      (Int.le_antisymm (Int.le_of_not_gt hmn) (Int.le_of_not_gt hnm)))

def Z_dec_type : Type :=
  ∀ n m : Z, Support.Sumor
    (Support.Sumbool (ZArith.BinInt.Z.lt n m) (ZArith.BinInt.Z.gt n m))
    (n = m)
def Z_le_dec (x y : Z) : Support.Sumbool (ZArith.BinInt.Z.le x y) (¬ ZArith.BinInt.Z.le x y) := by
  exact if h : intOfZ x ≤ intOfZ y then
    .left (show ZArith.BinInt.Z.le x y from h)
  else
    .right (show ¬ ZArith.BinInt.Z.le x y from h)
def Z_le_gt_dec (x y : Z) : Support.Sumbool (ZArith.BinInt.Z.le x y) (ZArith.BinInt.Z.lt y x) := by
  exact if h : intOfZ x ≤ intOfZ y then
    .left (show ZArith.BinInt.Z.le x y from h)
  else
    .right (show ZArith.BinInt.Z.lt y x from Int.lt_of_not_ge h)
def Z_lt_dec (x y : Z) : Support.Sumbool (ZArith.BinInt.Z.lt x y) (¬ ZArith.BinInt.Z.lt x y) := by
  exact if h : intOfZ x < intOfZ y then
    .left (show ZArith.BinInt.Z.lt x y from h)
  else
    .right (show ¬ ZArith.BinInt.Z.lt x y from h)

end ZArith.ZArith_dec

namespace ZArith.Zbool

def Zeq_bool (x y : Z) : Bool := decide (x = y)
abbrev Zle_bool := ZArith.BinInt.Z.leb
abbrev Zle_bool_refl (x : Z) : Prop := Zle_bool x x = true
abbrev Zlt_bool := ZArith.BinInt.Z.ltb

end ZArith.Zbool

namespace ZArith.Zcompare

abbrev Zcompare_Eq_iff_eq (x y : Z) : Prop := ZArith.BinInt.Z.compare x y = .Eq ↔ x = y

end ZArith.Zcompare

namespace ZArith.Zabs

abbrev inj_Zabs_nat (n : Z) : Prop :=
  ZArith.BinInt.Z.of_nat (ZArith.BinInt.Z.abs_nat n) = ZArith.BinInt.Z.abs n
abbrev Zabs_nat_Z_of_nat (n : Nat) : Prop := ZArith.BinInt.Z.abs_nat (ZArith.BinInt.Z.of_nat n) = n
abbrev Zabs_non_eq (n : Z) : Prop :=
  ZArith.BinInt.Z.le n Z0 → ZArith.BinInt.Z.abs n = ZArith.BinInt.Z.opp n
abbrev Zabs_Zmult (n m : Z) : Prop := ZArith.BinInt.Z.abs (ZArith.BinInt.Z.mul n m) = ZArith.BinInt.Z.mul (ZArith.BinInt.Z.abs n) (ZArith.BinInt.Z.abs m)
abbrev Zabs_Zopp (n : Z) : Prop := ZArith.BinInt.Z.abs (ZArith.BinInt.Z.opp n) = ZArith.BinInt.Z.abs n

end ZArith.Zabs

namespace ZArith.Zdiv

abbrev Zmod := ZArith.BinInt.Z.modulo
def Remainder (r b : Z) : Prop :=
  (ZArith.BinInt.Z.le Z0 r ∧ ZArith.BinInt.Z.lt r b) ∨
    (ZArith.BinInt.Z.lt b r ∧ ZArith.BinInt.Z.le r Z0)

theorem Z_mod_plus_full (a b c : Z) :
    ZArith.BinInt.Z.modulo
      (ZArith.BinInt.Z.add a (ZArith.BinInt.Z.mul b c)) c =
      ZArith.BinInt.Z.modulo a c :=
  ZArith.BinInt.Z.modulo_add_mul a b c

theorem Z_mod_plus (a b c : Z) (_ : ZArith.BinInt.Z.gt c Z0) :
    ZArith.BinInt.Z.modulo
      (ZArith.BinInt.Z.add a (ZArith.BinInt.Z.mul b c)) c =
      ZArith.BinInt.Z.modulo a c :=
  ZArith.BinInt.Z.modulo_add_mul a b c

theorem Z_mod_lt (a b : Z) (hb : ZArith.BinInt.Z.gt b Z0) :
    ZArith.BinInt.Z.le Z0 (ZArith.BinInt.Z.modulo a b) ∧
      ZArith.BinInt.Z.lt (ZArith.BinInt.Z.modulo a b) b :=
  ZArith.BinInt.Z.modulo_range a b hb

theorem Zmod_small (a b : Z)
    (h : ZArith.BinInt.Z.le Z0 a ∧ ZArith.BinInt.Z.lt a b) :
    ZArith.BinInt.Z.modulo a b = a :=
  ZArith.BinInt.Z.mod_small a b h

end ZArith.Zdiv

namespace ZArith.Zmax

abbrev Zmax_right (n m : Z) (_ : ZArith.BinInt.Z.le n m) : Prop :=
  ZArith.BinInt.Z.max n m = m

end ZArith.Zmax

namespace ZArith.Znat

abbrev inj_S (n : Nat) : Prop := ZArith.BinInt.Z.of_nat (n + 1) = ZArith.BinInt.Z.succ (ZArith.BinInt.Z.of_nat n)

theorem positive_nat_Z (p : positive) :
    ZArith.BinInt.Z.of_nat (PArith.BinPos.Pos.to_nat p) = Zpos p := by
  change zOfInt (Int.ofNat (posToNat p)) = Zpos p
  simpa [intOfZ] using zOfInt_intOfZ (Zpos p)

namespace Nat2Z

theorem id (n : Nat) :
    ZArith.BinInt.Z.to_nat (ZArith.BinInt.Z.of_nat n) = n := by
  simp [ZArith.BinInt.Z.to_nat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]

end Nat2Z

namespace Z2Nat

theorem id (z : Z) (hz : ZArith.BinInt.Z.le Z0 z) :
    ZArith.BinInt.Z.of_nat (ZArith.BinInt.Z.to_nat z) = z := by
  change 0 ≤ intOfZ z at hz
  change zOfInt (Int.ofNat (Int.toNat (intOfZ z))) = z
  have hcast : Int.ofNat (Int.toNat (intOfZ z)) = intOfZ z := Int.toNat_of_nonneg hz
  rw [hcast]
  exact zOfInt_intOfZ z

end Z2Nat

end ZArith.Znat

namespace ZArith.Zorder

abbrev Zeq_le (n m : Z) (h : n = m) : Prop := ZArith.BinInt.Z.le n m
abbrev Zle_antisym (n m : Z) (h₁ : ZArith.BinInt.Z.le n m) (h₂ : ZArith.BinInt.Z.le m n) : Prop := n = m
abbrev Zle_or_lt (n m : Z) : Prop := ZArith.BinInt.Z.le n m ∨ ZArith.BinInt.Z.lt m n
abbrev Zle_pred (n : Z) : Prop := ZArith.BinInt.Z.le (ZArith.BinInt.Z.pred n) n
abbrev Zle_succ (n : Z) : Prop := ZArith.BinInt.Z.le n (ZArith.BinInt.Z.succ n)
abbrev Zlt_le_weak (n m : Z) : Prop := ZArith.BinInt.Z.lt n m → ZArith.BinInt.Z.le n m
abbrev Zlt_lt_succ (n m : Z) : Prop := ZArith.BinInt.Z.lt n m → ZArith.BinInt.Z.lt n (ZArith.BinInt.Z.succ m)
abbrev Zlt_pred (n : Z) : Prop := ZArith.BinInt.Z.lt (ZArith.BinInt.Z.pred n) n
abbrev Zlt_succ (n : Z) : Prop := ZArith.BinInt.Z.lt n (ZArith.BinInt.Z.succ n)
abbrev Zmult_le_0_compat (n m : Z) : Prop :=
  ZArith.BinInt.Z.le Z0 n → ZArith.BinInt.Z.le Z0 m →
    ZArith.BinInt.Z.le Z0 (ZArith.BinInt.Z.mul n m)
abbrev Zmult_lt_0_compat (n m : Z) : Prop :=
  ZArith.BinInt.Z.lt Z0 n → ZArith.BinInt.Z.lt Z0 m →
    ZArith.BinInt.Z.lt Z0 (ZArith.BinInt.Z.mul n m)
abbrev Zplus_le_0_compat (n m : Z) : Prop :=
  ZArith.BinInt.Z.le Z0 n → ZArith.BinInt.Z.le Z0 m →
    ZArith.BinInt.Z.le Z0 (ZArith.BinInt.Z.add n m)
abbrev Zplus_le_compat (n m p q : Z) : Prop :=
  ZArith.BinInt.Z.le n m → ZArith.BinInt.Z.le p q →
    ZArith.BinInt.Z.le (ZArith.BinInt.Z.add n p) (ZArith.BinInt.Z.add m q)

end ZArith.Zorder

namespace ZArith.Zpow_def

abbrev Zpower := ZArith.BinInt.Z.pow
abbrev Zpower_pos := ZArith.BinInt.Z.pow_pos

end ZArith.Zpow_def

namespace ZArith.Zpower

def shift_pos (p q : positive) : positive := PArith.BinPos.Pos.shiftl_nat q (PArith.BinPos.Pos.to_nat p)
def two_p (x : Z) : Z := ZArith.BinInt.Z.pow (Zpos (.xO .xH)) x
def two_power_nat (n : Nat) : Z := ZArith.BinInt.Z.pow (Zpos (.xO .xH)) (ZArith.BinInt.Z.of_nat n)
def two_power_pos (p : positive) : Z := ZArith.BinInt.Z.pow_pos (Zpos (.xO .xH)) p
def Zpower_nat (x : Z) (n : Nat) : Z := ZArith.BinInt.Z.pow x (ZArith.BinInt.Z.of_nat n)

end ZArith.Zpower

abbrev Zeq_bool := ZArith.Zbool.Zeq_bool
abbrev nat_rect := _root_.CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.nat_rect
abbrev n_to_nat := NArith.BinNat.N.to_nat
abbrev shift_pos := ZArith.Zpower.shift_pos
abbrev two_p := ZArith.Zpower.two_p
abbrev two_power_nat := ZArith.Zpower.two_power_nat
abbrev two_power_pos := ZArith.Zpower.two_power_pos
abbrev Zpower_nat := ZArith.Zpower.Zpower_nat

namespace ZArith.Zquot

end ZArith.Zquot

/-! The remaining theorem-shaped provider APIs are exact source proposition
    descriptors.  Their proof bodies belong to the later proof-migration
    phase. -/

namespace _StatementDescriptors

end _StatementDescriptors

def Arith.PeanoNat.Nat.add_0_rStatement := ∀ n : Nat, ((Nat.add n 0) = n)
def Arith.PeanoNat.Nat.add_lt_mono_rStatement := ∀ n m p : Nat, Iff (Arith.PeanoNat.Nat.lt n m) (Arith.PeanoNat.Nat.lt (Nat.add n p) (Nat.add m p))
def Arith.PeanoNat.Nat.eqb_eqStatement := ∀ n m : Nat, Iff (((Arith.PeanoNat.Nat.eqb n m) = true)) ((n = m))
def Arith.PeanoNat.Nat.eqb_reflStatement := ∀ x : Nat, ((Arith.PeanoNat.Nat.eqb x x) = true)
def Arith.PeanoNat.Nat.lt_0_succStatement := ∀ n : Nat, Arith.PeanoNat.Nat.lt 0 (Nat.succ n)
def Arith.PeanoNat.Nat.sub_addStatement := ∀ (n m : Nat) (_ : le n m), ((Nat.add (Nat.sub m n) n) = m)
def Init.Peano.le_0_nStatement := ∀ n : Nat, le 0 n
def Init.Peano.le_n_SStatement := ∀ (n m : Nat) (_ : le n m), le (Nat.succ n) (Nat.succ m)
def Init.Peano.plus_n_SmStatement := ∀ n m : Nat, ((Nat.succ (Nat.add n m)) = (Nat.add n (Nat.succ m)))
def PArith.BinPos.Pos.add_1_rStatement := ∀ p : positive, ((PArith.BinPos.Pos.add p xH) = (PArith.BinPos.Pos.succ p))
def PArith.BinPos.Pos.compare_antisymStatement := ∀ p q : positive, ((PArith.BinPos.Pos.compare q p) = (CompOpp (PArith.BinPos.Pos.compare p q)))
def PArith.BinPos.Pos.compare_eq_iffStatement := ∀ p q : positive, Iff (((PArith.BinPos.Pos.compare p q) = Eq)) ((p = q))
def PArith.BinPos.Pos.compare_gt_iffStatement := ∀ x y : positive, Iff (((PArith.BinPos.Pos.compare x y) = Gt)) (PArith.BinPos.Pos.lt y x)
def PArith.BinPos.Pos.compare_reflStatement := ∀ x : positive, ((PArith.BinPos.Pos.compare x x) = Eq)
def PArith.BinPos.Pos.eqb_eqStatement := ∀ p q : positive, Iff (((PArith.BinPos.Pos.eqb p q) = true)) ((p = q))
def PArith.BinPos.Pos.iter_succStatement := ∀ (p : positive) (A : Type) (f : ∀ _ : A, A) (x : A), ((@PArith.BinPos.Pos.iter A f x (PArith.BinPos.Pos.succ p)) = (f (@PArith.BinPos.Pos.iter A f x p)))
def PArith.BinPos.Pos.le_reflStatement := ∀ p : positive, PArith.BinPos.Pos.le p p
def PArith.BinPos.Pos.le_transStatement := ∀ (n m p : positive) (_ : PArith.BinPos.Pos.le n m) (_ : PArith.BinPos.Pos.le m p), PArith.BinPos.Pos.le n p
def PArith.BinPos.Pos.leb_leStatement := ∀ p q : positive, Iff (((PArith.BinPos.Pos.leb p q) = true)) (PArith.BinPos.Pos.le p q)
def PArith.BinPos.Pos.leb_reflStatement := ∀ x : positive, ((PArith.BinPos.Pos.leb x x) = true)
def PArith.BinPos.Pos.lt_irreflStatement := ∀ x : positive, Not (PArith.BinPos.Pos.lt x x)
def PArith.BinPos.Pos.lt_le_inclStatement := ∀ (p q : positive) (_ : PArith.BinPos.Pos.lt p q), PArith.BinPos.Pos.le p q
def PArith.BinPos.Pos.lt_le_transStatement := ∀ (n m p : positive) (_ : PArith.BinPos.Pos.lt n m) (_ : PArith.BinPos.Pos.le m p), PArith.BinPos.Pos.lt n p
def PArith.BinPos.Pos.lt_succ_rStatement := ∀ p q : positive, Iff (PArith.BinPos.Pos.lt p (PArith.BinPos.Pos.succ q)) (PArith.BinPos.Pos.le p q)
def PArith.BinPos.Pos.lt_transStatement := ∀ (n m p : positive) (_ : PArith.BinPos.Pos.lt n m) (_ : PArith.BinPos.Pos.lt m p), PArith.BinPos.Pos.lt n p
def PArith.BinPos.Pos.mul_commStatement := ∀ p q : positive, ((PArith.BinPos.Pos.mul p q) = (PArith.BinPos.Pos.mul q p))
def PArith.BinPos.Pos.pred_double_succStatement := ∀ p : positive, ((PArith.BinPos.Pos.pred_double (PArith.BinPos.Pos.succ p)) = (xI p))
def PArith.BinPos.Pos.succ_pred_orStatement := ∀ p : positive, Or ((p = xH)) (((PArith.BinPos.Pos.succ (PArith.BinPos.Pos.pred p)) = p))
def PArith.BinPos.Pplus_one_succ_lStatement := ∀ p : positive, ((PArith.BinPos.Pos.succ p) = (PArith.BinPos.Pos.add xH p))
def PArith.Pnat.nat_of_P_lt_Lt_compare_morphismStatement := ∀ (p q : positive) (_ : ((PArith.BinPos.Pos.compare_cont Eq p q) = Lt)), lt (PArith.BinPos.Pos.to_nat p) (PArith.BinPos.Pos.to_nat q)
def PArith.Pnat.Pos2Nat.idStatement := ∀ p : positive, ((PArith.BinPos.Pos.of_nat (PArith.BinPos.Pos.to_nat p)) = p)
def PArith.Pnat.Pos2Nat.inj_xIStatement := ∀ p : positive, ((PArith.BinPos.Pos.to_nat (xI p)) = (Nat.succ (Nat.mul (Nat.succ (Nat.succ 0)) (PArith.BinPos.Pos.to_nat p))))
def PArith.Pnat.Pos2Nat.inj_xOStatement := ∀ p : positive, ((PArith.BinPos.Pos.to_nat (xO p)) = (Nat.mul (Nat.succ (Nat.succ 0)) (PArith.BinPos.Pos.to_nat p)))
def ZArith.auxiliary.Zle_leftStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.le n m), ZArith.BinInt.Z.le Z0 (ZArith.BinInt.Z.add m (ZArith.BinInt.Z.opp n))
def ZArith.BinInt.Pos2Z.inj_subStatement := ∀ (p q : positive) (_ : PArith.BinPos.Pos.lt p q), ((Zpos (PArith.BinPos.Pos.sub q p)) = (ZArith.BinInt.Z.sub (Zpos q) (Zpos p)))
def ZArith.BinInt.Z.abs_eqStatement := ∀ (n : Z) (_ : ZArith.BinInt.Z.le Z0 n), ((ZArith.BinInt.Z.abs n) = n)
def ZArith.BinInt.Z.abs_mulStatement := ∀ n m : Z, ((ZArith.BinInt.Z.abs (ZArith.BinInt.Z.mul n m)) = (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.abs n) (ZArith.BinInt.Z.abs m)))
def ZArith.BinInt.Z.abs_neqStatement := ∀ (n : Z) (_ : ZArith.BinInt.Z.le n Z0), ((ZArith.BinInt.Z.abs n) = (ZArith.BinInt.Z.opp n))
def ZArith.BinInt.Z.abs_oppStatement := ∀ n : Z, ((ZArith.BinInt.Z.abs (ZArith.BinInt.Z.opp n)) = (ZArith.BinInt.Z.abs n))
def ZArith.BinInt.Z.add_0_lStatement := ∀ n : Z, ((ZArith.BinInt.Z.add Z0 n) = n)
def ZArith.BinInt.Z.add_0_rStatement := ∀ n : Z, ((ZArith.BinInt.Z.add n Z0) = n)
def ZArith.BinInt.Z.add_assocStatement := ∀ n m p : Z, ((ZArith.BinInt.Z.add n (ZArith.BinInt.Z.add m p)) = (ZArith.BinInt.Z.add (ZArith.BinInt.Z.add n m) p))
def ZArith.BinInt.Z.add_commStatement := ∀ n m : Z, ((ZArith.BinInt.Z.add n m) = (ZArith.BinInt.Z.add m n))
def ZArith.BinInt.Z.bits_inj'Statement := ∀ (a b : Z) (_ : ∀ (n : Z) (_ : ZArith.BinInt.Z.le Z0 n), ((ZArith.BinInt.Z.testbit a n) = (ZArith.BinInt.Z.testbit b n))), (a = b)
def ZArith.BinInt.Z.compare_antisymStatement := ∀ n m : Z, ((ZArith.BinInt.Z.compare m n) = (CompOpp (ZArith.BinInt.Z.compare n m)))
def ZArith.BinInt.Z.compare_eq_iffStatement := ∀ n m : Z, Iff (((ZArith.BinInt.Z.compare n m) = Eq)) ((n = m))
def ZArith.BinInt.Z.compare_eqStatement := ∀ (x y : Z) (_ : ((ZArith.BinInt.Z.compare x y) = Eq)), (x = y)
def ZArith.BinInt.Z.compare_gt_iffStatement := ∀ x y : Z, Iff (((ZArith.BinInt.Z.compare x y) = Gt)) (ZArith.BinInt.Z.lt y x)
def ZArith.BinInt.Z.div_divStatement := ∀ (a b c : Z) (_ : Not ((b = Z0))) (_ : ZArith.BinInt.Z.lt Z0 c), ((ZArith.BinInt.Z.div (ZArith.BinInt.Z.div a b) c) = (ZArith.BinInt.Z.div a (ZArith.BinInt.Z.mul b c)))
def ZArith.BinInt.Z.div_le_monoStatement := ∀ (a b c : Z) (_ : ZArith.BinInt.Z.lt Z0 c) (_ : ZArith.BinInt.Z.le a b), ZArith.BinInt.Z.le (ZArith.BinInt.Z.div a c) (ZArith.BinInt.Z.div b c)
def ZArith.BinInt.Z.div_modStatement := ∀ (a b : Z) (_ : Not ((b = Z0))), (a = (ZArith.BinInt.Z.add (ZArith.BinInt.Z.mul b (ZArith.BinInt.Z.div a b)) (ZArith.BinInt.Z.modulo a b)))
def ZArith.BinInt.Z.div_smallStatement := ∀ (a b : Z) (_ : And (ZArith.BinInt.Z.le Z0 a) (ZArith.BinInt.Z.lt a b)), ((ZArith.BinInt.Z.div a b) = Z0)
def ZArith.BinInt.Z.divide_0_rStatement := ∀ n : Z, ZArith.BinInt.Z.divide n Z0
def ZArith.BinInt.Z.divide_1_lStatement := ∀ n : Z, ZArith.BinInt.Z.divide (Zpos xH) n
def ZArith.BinInt.Z.divide_add_rStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.divide n m) (_ : ZArith.BinInt.Z.divide n p), ZArith.BinInt.Z.divide n (ZArith.BinInt.Z.add m p)
def ZArith.BinInt.Z.divide_factor_rStatement := ∀ n m : Z, ZArith.BinInt.Z.divide n (ZArith.BinInt.Z.mul m n)
def ZArith.BinInt.Z.divide_mul_lStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.divide n m), ZArith.BinInt.Z.divide n (ZArith.BinInt.Z.mul m p)
def ZArith.BinInt.Z.divide_reflStatement := ∀ n : Z, ZArith.BinInt.Z.divide n n
def ZArith.BinInt.Z.divide_transStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.divide n m) (_ : ZArith.BinInt.Z.divide m p), ZArith.BinInt.Z.divide n p
def ZArith.BinInt.Z.double_specStatement := ∀ n : Z, ((ZArith.BinInt.Z.double n) = (ZArith.BinInt.Z.mul (Zpos (xO xH)) n))
def ZArith.BinInt.Z.eqb_eqStatement := ∀ n m : Z, Iff (((ZArith.BinInt.Z.eqb n m) = true)) ((n = m))
def ZArith.BinInt.Z.even_addStatement := ∀ n m : Z, ((ZArith.BinInt.Z.even (ZArith.BinInt.Z.add n m)) = (Logic.Rocq.Coq.Bool.Bool.eqb (ZArith.BinInt.Z.even n) (ZArith.BinInt.Z.even m)))
def ZArith.BinInt.Z.even_mulStatement := ∀ n m : Z, ((ZArith.BinInt.Z.even (ZArith.BinInt.Z.mul n m)) = (orb (ZArith.BinInt.Z.even n) (ZArith.BinInt.Z.even m)))
def ZArith.BinInt.Z.even_oppStatement := ∀ n : Z, ((ZArith.BinInt.Z.even (ZArith.BinInt.Z.opp n)) = (ZArith.BinInt.Z.even n))
def ZArith.BinInt.Z.even_powStatement := ∀ (a b : Z) (_ : ZArith.BinInt.Z.lt Z0 b), ((ZArith.BinInt.Z.even (ZArith.BinInt.Z.pow a b)) = (ZArith.BinInt.Z.even a))
def ZArith.BinInt.Z.ge_leStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.ge n m), ZArith.BinInt.Z.le m n
def ZArith.BinInt.Z.geb_leStatement := ∀ n m : Z, Iff (((ZArith.BinInt.Z.geb n m) = true)) (ZArith.BinInt.Z.le m n)
def ZArith.BinInt.Z.gt_ltStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.gt n m), ZArith.BinInt.Z.lt m n
def ZArith.BinInt.Z.gtb_ltStatement := ∀ n m : Z, Iff (((ZArith.BinInt.Z.gtb n m) = true)) (ZArith.BinInt.Z.lt m n)
def ZArith.BinInt.Z.le_0_subStatement := ∀ n m : Z, Iff (ZArith.BinInt.Z.le Z0 (ZArith.BinInt.Z.sub m n)) (ZArith.BinInt.Z.le n m)
def ZArith.BinInt.Z.le_geStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.le n m), ZArith.BinInt.Z.ge m n
def ZArith.BinInt.Z.le_lt_transStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.le n m) (_ : ZArith.BinInt.Z.lt m p), ZArith.BinInt.Z.lt n p
def ZArith.BinInt.Z.le_max_lStatement := ∀ n m : Z, ZArith.BinInt.Z.le n (ZArith.BinInt.Z.max n m)
def ZArith.BinInt.Z.le_max_rStatement := ∀ n m : Z, ZArith.BinInt.Z.le m (ZArith.BinInt.Z.max n m)
def ZArith.BinInt.Z.le_min_lStatement := ∀ n m : Z, ZArith.BinInt.Z.le (ZArith.BinInt.Z.min n m) n
def ZArith.BinInt.Z.le_min_rStatement := ∀ n m : Z, ZArith.BinInt.Z.le (ZArith.BinInt.Z.min n m) m
def ZArith.BinInt.Z.le_reflStatement := ∀ n : Z, ZArith.BinInt.Z.le n n
def ZArith.BinInt.Z.le_transStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.le n m) (_ : ZArith.BinInt.Z.le m p), ZArith.BinInt.Z.le n p
def ZArith.BinInt.Z.leb_gtStatement := ∀ x y : Z, Iff (((ZArith.BinInt.Z.leb x y) = false)) (ZArith.BinInt.Z.lt y x)
def ZArith.BinInt.Z.leb_leStatement := ∀ n m : Z, Iff (((ZArith.BinInt.Z.leb n m) = true)) (ZArith.BinInt.Z.le n m)
def ZArith.BinInt.Z.lt_gtStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.lt n m), ZArith.BinInt.Z.gt m n
def ZArith.BinInt.Z.lt_irreflStatement := ∀ x : Z, Not (ZArith.BinInt.Z.lt x x)
def ZArith.BinInt.Z.lt_le_predStatement := ∀ n m : Z, Iff (ZArith.BinInt.Z.lt n m) (ZArith.BinInt.Z.le n (ZArith.BinInt.Z.pred m))
def ZArith.BinInt.Z.lt_le_transStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.lt n m) (_ : ZArith.BinInt.Z.le m p), ZArith.BinInt.Z.lt n p
def ZArith.BinInt.Z.lt_pred_lStatement := ∀ n : Z, ZArith.BinInt.Z.lt (ZArith.BinInt.Z.pred n) n
def ZArith.BinInt.Z.lt_pred_leStatement := ∀ n m : Z, Iff (ZArith.BinInt.Z.lt (ZArith.BinInt.Z.pred n) m) (ZArith.BinInt.Z.le n m)
def ZArith.BinInt.Z.lt_sub_0Statement := ∀ n m : Z, Iff (ZArith.BinInt.Z.lt (ZArith.BinInt.Z.sub n m) Z0) (ZArith.BinInt.Z.lt n m)
def ZArith.BinInt.Z.lt_succ_rStatement := ∀ n m : Z, Iff (ZArith.BinInt.Z.lt n (ZArith.BinInt.Z.succ m)) (ZArith.BinInt.Z.le n m)
def ZArith.BinInt.Z.ltb_ltStatement := ∀ n m : Z, Iff (((ZArith.BinInt.Z.ltb n m) = true)) (ZArith.BinInt.Z.lt n m)
def ZArith.BinInt.Z.ltb_specStatement :=
  ∀ x y : Z,
    _root_.CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.BoolSpec
      (ZArith.BinInt.Z.lt x y) (ZArith.BinInt.Z.le y x) (ZArith.BinInt.Z.ltb x y)
def ZArith.BinInt.Z.max_case_strongStatement := ∀ (n m : Z) (P : ∀ _ : Z, Type) (_ : ∀ _ : ZArith.BinInt.Z.le m n, P n) (_ : ∀ _ : ZArith.BinInt.Z.le n m, P m), P (ZArith.BinInt.Z.max n m)
def ZArith.BinInt.Z.max_caseStatement := ∀ (n m : Z) (P : ∀ _ : Z, Type) (_ : P n) (_ : P m), P (ZArith.BinInt.Z.max n m)
def ZArith.BinInt.Z.max_commStatement := ∀ n m : Z, ((ZArith.BinInt.Z.max n m) = (ZArith.BinInt.Z.max m n))
def ZArith.BinInt.Z.max_l_iffStatement := ∀ n m : Z, Iff (((ZArith.BinInt.Z.max n m) = n)) (ZArith.BinInt.Z.le m n)
def ZArith.BinInt.Z.max_lStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.le m n), ((ZArith.BinInt.Z.max n m) = n)
def ZArith.BinInt.Z.max_lubStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.le n p) (_ : ZArith.BinInt.Z.le m p), ZArith.BinInt.Z.le (ZArith.BinInt.Z.max n m) p
def ZArith.BinInt.Z.max_rStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.le n m), ((ZArith.BinInt.Z.max n m) = m)
def ZArith.BinInt.Z.min_caseStatement := ∀ (n m : Z) (P : ∀ _ : Z, Type) (_ : P n) (_ : P m), P (ZArith.BinInt.Z.min n m)
def ZArith.BinInt.Z.min_lStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.le n m), ((ZArith.BinInt.Z.min n m) = n)
def ZArith.BinInt.Z.min_rStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.le m n), ((ZArith.BinInt.Z.min n m) = m)
def ZArith.BinInt.Z.mod_smallStatement := ∀ (a b : Z) (_ : And (ZArith.BinInt.Z.le Z0 a) (ZArith.BinInt.Z.lt a b)), ((ZArith.BinInt.Z.modulo a b) = a)
def ZArith.BinInt.Z.mul_0_rStatement := ∀ n : Z, ((ZArith.BinInt.Z.mul n Z0) = Z0)
def ZArith.BinInt.Z.mul_assocStatement := ∀ n m p : Z, ((ZArith.BinInt.Z.mul n (ZArith.BinInt.Z.mul m p)) = (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.mul n m) p))
def ZArith.BinInt.Z.mul_commStatement := ∀ n m : Z, ((ZArith.BinInt.Z.mul n m) = (ZArith.BinInt.Z.mul m n))
def ZArith.BinInt.Z.mul_divide_mono_lStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.divide n m), ZArith.BinInt.Z.divide (ZArith.BinInt.Z.mul p n) (ZArith.BinInt.Z.mul p m)
def ZArith.BinInt.Z.mul_le_mono_nonneg_lStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.le Z0 p) (_ : ZArith.BinInt.Z.le n m), ZArith.BinInt.Z.le (ZArith.BinInt.Z.mul p n) (ZArith.BinInt.Z.mul p m)
def ZArith.BinInt.Z.mul_le_mono_nonneg_rStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.le Z0 p) (_ : ZArith.BinInt.Z.le n m), ZArith.BinInt.Z.le (ZArith.BinInt.Z.mul n p) (ZArith.BinInt.Z.mul m p)
def ZArith.BinInt.Z.mul_le_mono_nonpos_lStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.le p Z0) (_ : ZArith.BinInt.Z.le n m), ZArith.BinInt.Z.le (ZArith.BinInt.Z.mul p m) (ZArith.BinInt.Z.mul p n)
def ZArith.BinInt.Z.mul_nonneg_nonnegStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.le Z0 n) (_ : ZArith.BinInt.Z.le Z0 m), ZArith.BinInt.Z.le Z0 (ZArith.BinInt.Z.mul n m)
def ZArith.BinInt.Z.mul_pos_posStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.lt Z0 n) (_ : ZArith.BinInt.Z.lt Z0 m), ZArith.BinInt.Z.lt Z0 (ZArith.BinInt.Z.mul n m)
def ZArith.BinInt.Z.opp_injStatement := ∀ (n m : Z) (_ : ((ZArith.BinInt.Z.opp n) = (ZArith.BinInt.Z.opp m))), (n = m)
def ZArith.BinInt.Z.opp_involutiveStatement := ∀ n : Z, ((ZArith.BinInt.Z.opp (ZArith.BinInt.Z.opp n)) = n)
def ZArith.BinInt.Z.pred_succStatement := ∀ n : Z, ((ZArith.BinInt.Z.pred (ZArith.BinInt.Z.succ n)) = n)
def ZArith.BinInt.Z.quot_1_rStatement := ∀ a : Z, ((ZArith.BinInt.Z.quot a (Zpos xH)) = a)
def ZArith.BinInt.Z.quot_opp_lStatement := ∀ (a b : Z) (_ : Not ((b = Z0))), ((ZArith.BinInt.Z.quot (ZArith.BinInt.Z.opp a) b) = (ZArith.BinInt.Z.opp (ZArith.BinInt.Z.quot a b)))
def ZArith.BinInt.Z.shiftl_0_rStatement := ∀ a : Z, ((ZArith.BinInt.Z.shiftl a Z0) = a)
def ZArith.BinInt.Z.shiftl_mul_pow2Statement := ∀ (a n : Z) (_ : ZArith.BinInt.Z.le Z0 n), ((ZArith.BinInt.Z.shiftl a n) = (ZArith.BinInt.Z.mul a (ZArith.BinInt.Z.pow (Zpos (xO xH)) n)))
def ZArith.BinInt.Z.shiftl_spec_highStatement := ∀ (a n m : Z) (_ : ZArith.BinInt.Z.le Z0 m) (_ : ZArith.BinInt.Z.le n m), ((ZArith.BinInt.Z.testbit (ZArith.BinInt.Z.shiftl a n) m) = (ZArith.BinInt.Z.testbit a (ZArith.BinInt.Z.sub m n)))
def ZArith.BinInt.Z.shiftl_spec_lowStatement := ∀ (a n m : Z) (_ : ZArith.BinInt.Z.lt m n), ((ZArith.BinInt.Z.testbit (ZArith.BinInt.Z.shiftl a n) m) = false)
def ZArith.BinInt.Z.shiftr_0_rStatement := ∀ a : Z, ((ZArith.BinInt.Z.shiftr a Z0) = a)
def ZArith.BinInt.Z.shiftr_specStatement := ∀ (a n m : Z) (_ : ZArith.BinInt.Z.le Z0 m), ((ZArith.BinInt.Z.testbit (ZArith.BinInt.Z.shiftr a n) m) = (ZArith.BinInt.Z.testbit a (ZArith.BinInt.Z.add m n)))
def ZArith.BinInt.Z.sqrtrem_specStatement :=
  ∀ n : Z, ZArith.BinInt.Z.le Z0 n →
    let sr := ZArith.BinInt.Z.sqrtrem n
    n = ZArith.BinInt.Z.add (ZArith.BinInt.Z.mul sr.1 sr.1) sr.2 ∧
      ZArith.BinInt.Z.le Z0 sr.2 ∧
      ZArith.BinInt.Z.le sr.2 (ZArith.BinInt.Z.mul (Zpos (xO xH)) sr.1)
def ZArith.BinInt.Z.succ_double_specStatement := ∀ n : Z, ((ZArith.BinInt.Z.succ_double n) = (ZArith.BinInt.Z.add (ZArith.BinInt.Z.mul (Zpos (xO xH)) n) (Zpos xH)))
def ZArith.BinInt.Z.testbit_0_lStatement := ∀ n : Z, ((ZArith.BinInt.Z.testbit Z0 n) = false)
def ZArith.BinInt.Z.testbit_even_0Statement := ∀ a : Z, ((ZArith.BinInt.Z.testbit (ZArith.BinInt.Z.mul (Zpos (xO xH)) a) Z0) = false)
def ZArith.BinInt.Z.testbit_even_succStatement := ∀ (a n : Z) (_ : ZArith.BinInt.Z.le Z0 n), ((ZArith.BinInt.Z.testbit (ZArith.BinInt.Z.mul (Zpos (xO xH)) a) (ZArith.BinInt.Z.succ n)) = (ZArith.BinInt.Z.testbit a n))
def ZArith.BinInt.Z.testbit_odd_0Statement := ∀ a : Z, ((ZArith.BinInt.Z.testbit (ZArith.BinInt.Z.add (ZArith.BinInt.Z.mul (Zpos (xO xH)) a) (Zpos xH)) Z0) = true)
def ZArith.BinInt.Z.testbit_odd_succStatement := ∀ (a n : Z) (_ : ZArith.BinInt.Z.le Z0 n), ((ZArith.BinInt.Z.testbit (ZArith.BinInt.Z.add (ZArith.BinInt.Z.mul (Zpos (xO xH)) a) (Zpos xH)) (ZArith.BinInt.Z.succ n)) = (ZArith.BinInt.Z.testbit a n))
def ZArith.BinInt.Z2Pos.idStatement := ∀ (x : Z) (_ : ZArith.BinInt.Z.lt Z0 x), ((Zpos (ZArith.BinInt.Z.to_pos x)) = x)
def ZArith.BinInt.Zopp_mult_distr_lStatement := ∀ n m : Z, ((ZArith.BinInt.Z.opp (ZArith.BinInt.Z.mul n m)) = (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.opp n) m))
def ZArith.BinInt.Zplus_diag_eq_mult_2Statement := ∀ n : Z, ((ZArith.BinInt.Z.add n n) = (ZArith.BinInt.Z.mul n (Zpos (xO xH))))
def ZArith.BinInt.Zpred_succStatement := ∀ n : Z, (n = (ZArith.BinInt.Z.pred (ZArith.BinInt.Z.succ n)))
def ZArith.BinInt.Zsucc_predStatement := ∀ n : Z, (n = (ZArith.BinInt.Z.succ (ZArith.BinInt.Z.pred n)))
def ZArith.ZArith_dec.Z_decStatement := ∀ n m : Z, Support.Sumor (Support.Sumbool (ZArith.BinInt.Z.lt n m) (ZArith.BinInt.Z.gt n m)) ((n = m))
def ZArith.ZArith_dec.Z_lt_le_decStatement := ∀ x y : Z, Support.Sumbool (ZArith.BinInt.Z.lt x y) (ZArith.BinInt.Z.le y x)
def ZArith.Zbool.Zeq_bool_eqStatement := ∀ (x y : Z) (_ : ((Zeq_bool x y) = true)), (x = y)
def ZArith.Zbool.Zeq_is_eq_boolStatement := ∀ x y : Z, Iff ((x = y)) (((Zeq_bool x y) = true))
def ZArith.Zbool.Zle_bool_imp_leStatement := ∀ (n m : Z) (_ : ((ZArith.BinInt.Z.leb n m) = true)), ZArith.BinInt.Z.le n m
def ZArith.Zbool.Zle_casesStatement :=
  ∀ n m : Z, match ZArith.BinInt.Z.leb n m with
    | true => ZArith.BinInt.Z.le n m
    | false => ZArith.BinInt.Z.gt n m
def ZArith.Zbool.Zle_is_le_boolStatement := ∀ n m : Z, Iff (ZArith.BinInt.Z.le n m) (((ZArith.BinInt.Z.leb n m) = true))
def ZArith.Zbool.Zlt_casesStatement :=
  ∀ n m : Z, match ZArith.BinInt.Z.ltb n m with
    | true => ZArith.BinInt.Z.lt n m
    | false => ZArith.BinInt.Z.ge n m
def ZArith.Zbool.Zlt_is_lt_boolStatement := ∀ n m : Z, Iff (ZArith.BinInt.Z.lt n m) (((ZArith.BinInt.Z.ltb n m) = true))
def ZArith.Zcompare.Zcompare_antisymStatement := ∀ n m : Z, ((CompOpp (ZArith.BinInt.Z.compare n m)) = (ZArith.BinInt.Z.compare m n))
def ZArith.Zcompare.Zgt_compareStatement :=
  ∀ (n m : Z) (_ : ZArith.BinInt.Z.gt n m),
    match ZArith.BinInt.Z.compare n m with
    | .Eq => False
    | .Lt => False
    | .Gt => True
def ZArith.Zcompare.Zlt_compareStatement :=
  ∀ (n m : Z) (_ : ZArith.BinInt.Z.lt n m),
    match ZArith.BinInt.Z.compare n m with
    | .Eq => False
    | .Lt => True
    | .Gt => False
def ZArith.Zdiv.Z_div_mod_eq_fullStatement := ∀ a b : Z, (a = (ZArith.BinInt.Z.add (ZArith.BinInt.Z.mul b (ZArith.BinInt.Z.div a b)) (ZArith.BinInt.Z.modulo a b)))
def ZArith.Zdiv.Z_div_modStatement :=
  ∀ (a b : Z) (_ : ZArith.BinInt.Z.gt b Z0),
    let qr := ZArith.BinInt.Z.div_eucl a b
    a = ZArith.BinInt.Z.add (ZArith.BinInt.Z.mul b qr.1) qr.2 ∧
      ZArith.BinInt.Z.le Z0 qr.2 ∧ ZArith.BinInt.Z.lt qr.2 b
def ZArith.Zdiv.Z_div_plus_full_lStatement := ∀ (a b c : Z) (_ : Not ((b = Z0))), ((ZArith.BinInt.Z.div (ZArith.BinInt.Z.add (ZArith.BinInt.Z.mul a b) c) b) = (ZArith.BinInt.Z.add a (ZArith.BinInt.Z.div c b)))
def ZArith.Zdiv.Z_div_plusStatement := ∀ (a b c : Z) (_ : ZArith.BinInt.Z.gt c Z0), ((ZArith.BinInt.Z.div (ZArith.BinInt.Z.add a (ZArith.BinInt.Z.mul b c)) c) = (ZArith.BinInt.Z.add (ZArith.BinInt.Z.div a c) b))
def ZArith.Zdiv.Z_mod_ltStatement := ∀ (a b : Z) (_ : ZArith.BinInt.Z.gt b Z0), And (ZArith.BinInt.Z.le Z0 (ZArith.BinInt.Z.modulo a b)) (ZArith.BinInt.Z.lt (ZArith.BinInt.Z.modulo a b) b)
def ZArith.Zdiv.Z_mod_plus_fullStatement := ∀ a b c : Z, ((ZArith.BinInt.Z.modulo (ZArith.BinInt.Z.add a (ZArith.BinInt.Z.mul b c)) c) = (ZArith.BinInt.Z.modulo a c))
def ZArith.Zdiv.Z_mod_plusStatement := ∀ (a b c : Z) (_ : ZArith.BinInt.Z.gt c Z0), ((ZArith.BinInt.Z.modulo (ZArith.BinInt.Z.add a (ZArith.BinInt.Z.mul b c)) c) = (ZArith.BinInt.Z.modulo a c))
def ZArith.Zdiv.Zdiv_0_lStatement := ∀ a : Z, ((ZArith.BinInt.Z.div Z0 a) = Z0)
def ZArith.Zdiv.Zdiv_1_rStatement := ∀ a : Z, ((ZArith.BinInt.Z.div a (Zpos xH)) = a)
def ZArith.Zdiv.Zdiv_smallStatement := ∀ (a b : Z) (_ : And (ZArith.BinInt.Z.le Z0 a) (ZArith.BinInt.Z.lt a b)), ((ZArith.BinInt.Z.div a b) = Z0)
def ZArith.Zdiv.Zdiv_unique_fullStatement :=
  ∀ (a b q r : Z) (_ : ZArith.Zdiv.Remainder r b)
    (_ : a = ZArith.BinInt.Z.add (ZArith.BinInt.Z.mul b q) r),
    q = ZArith.BinInt.Z.div a b
def ZArith.Zdiv.Zdiv2_divStatement := ∀ a : Z, ((ZArith.BinInt.Z.div2 a) = (ZArith.BinInt.Z.div a (Zpos (xO xH))))
def ZArith.Zdiv.Zmod_0_lStatement := ∀ a : Z, ((ZArith.BinInt.Z.modulo Z0 a) = Z0)
def ZArith.Zdiv.Zmod_1_rStatement := ∀ a : Z, ((ZArith.BinInt.Z.modulo a (Zpos xH)) = Z0)
def ZArith.Zdiv.Zmod_opp_oppStatement := ∀ a b : Z, ((ZArith.BinInt.Z.modulo (ZArith.BinInt.Z.opp a) (ZArith.BinInt.Z.opp b)) = (ZArith.BinInt.Z.opp (ZArith.BinInt.Z.modulo a b)))
def ZArith.Zdiv.Zmod_smallStatement := ∀ (a n : Z) (_ : And (ZArith.BinInt.Z.le Z0 a) (ZArith.BinInt.Z.lt a n)), ((ZArith.BinInt.Z.modulo a n) = a)
def ZArith.Zeven.Zdiv2_odd_eqnStatement :=
  ∀ n : Z,
    n = ZArith.BinInt.Z.add
      (ZArith.BinInt.Z.mul (Zpos (xO xH)) (ZArith.BinInt.Z.div2 n))
      (if ZArith.BinInt.Z.odd n then Zpos xH else Z0)
def ZArith.Zmax.Zmax_leftStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.ge n m), ((ZArith.BinInt.Z.max n m) = n)
def ZArith.Zmax.Zmax_specStatement := ∀ x y : Z, Or (And (ZArith.BinInt.Z.ge x y) (((ZArith.BinInt.Z.max x y) = x))) (And (ZArith.BinInt.Z.lt x y) (((ZArith.BinInt.Z.max x y) = y)))
def ZArith.Zmin.Zmin_specStatement := ∀ x y : Z, Or (And (ZArith.BinInt.Z.le x y) (((ZArith.BinInt.Z.min x y) = x))) (And (ZArith.BinInt.Z.gt x y) (((ZArith.BinInt.Z.min x y) = y)))
def ZArith.Zmisc.iter_nat_of_ZStatement := ∀ (n : Z) (A : Type) (f : ∀ _ : A, A) (x : A) (_ : ZArith.BinInt.Z.le Z0 n), ((@ZArith.BinInt.Z.iter n A f x) = (nat_rect (fun _ : Nat => A) x (fun _ : Nat => f) (ZArith.BinInt.Z.abs_nat n)))
def ZArith.Znat.N_nat_ZStatement := ∀ n : N, ((ZArith.BinInt.Z.of_nat (N.to_nat n)) = (ZArith.BinInt.Z.of_N n))
def ZArith.Znat.Nat2Z.idStatement := ∀ n : Nat, ((ZArith.BinInt.Z.to_nat (ZArith.BinInt.Z.of_nat n)) = n)
def ZArith.Znat.Nat2Z.inj_addStatement := ∀ n m : Nat, ((ZArith.BinInt.Z.of_nat (Nat.add n m)) = (ZArith.BinInt.Z.add (ZArith.BinInt.Z.of_nat n) (ZArith.BinInt.Z.of_nat m)))
def ZArith.Znat.Nat2Z.inj_succStatement := ∀ n : Nat, ((ZArith.BinInt.Z.of_nat (Nat.succ n)) = (ZArith.BinInt.Z.succ (ZArith.BinInt.Z.of_nat n)))
def ZArith.Znat.Nat2Z.injStatement := ∀ (n m : Nat) (_ : ((ZArith.BinInt.Z.of_nat n) = (ZArith.BinInt.Z.of_nat m))), (n = m)
def ZArith.Znat.positive_nat_ZStatement := ∀ p : positive, ((ZArith.BinInt.Z.of_nat (PArith.BinPos.Pos.to_nat p)) = (Zpos p))
def ZArith.Znat.Z2Nat.idStatement := ∀ (n : Z) (_ : ZArith.BinInt.Z.le Z0 n), ((ZArith.BinInt.Z.of_nat (ZArith.BinInt.Z.to_nat n)) = n)
def ZArith.Znat.Z2Nat.inj_addStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.le Z0 n) (_ : ZArith.BinInt.Z.le Z0 m), ((ZArith.BinInt.Z.to_nat (ZArith.BinInt.Z.add n m)) = (Nat.add (ZArith.BinInt.Z.to_nat n) (ZArith.BinInt.Z.to_nat m)))
def ZArith.Znat.Z2Nat.inj_subStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.le Z0 m), ((ZArith.BinInt.Z.to_nat (ZArith.BinInt.Z.sub n m)) = (Nat.sub (ZArith.BinInt.Z.to_nat n) (ZArith.BinInt.Z.to_nat m)))
def ZArith.Znat.Zabs2Nat.abs_nat_nonnegStatement := ∀ (n : Z) (_ : ZArith.BinInt.Z.le Z0 n), ((ZArith.BinInt.Z.abs_nat n) = (ZArith.BinInt.Z.to_nat n))
def ZArith.Znat.Zabs2Nat.id_absStatement := ∀ n : Z, ((ZArith.BinInt.Z.of_nat (ZArith.BinInt.Z.abs_nat n)) = (ZArith.BinInt.Z.abs n))
def ZArith.Znumtheory.Zdivide_boundsStatement := ∀ (a b : Z) (_ : ZArith.BinInt.Z.divide a b) (_ : Not ((b = Z0))), ZArith.BinInt.Z.le (ZArith.BinInt.Z.abs a) (ZArith.BinInt.Z.abs b)
def ZArith.Znumtheory.Zdivide_decStatement := ∀ a b : Z, Support.Sumbool (ZArith.BinInt.Z.divide a b) (Not (ZArith.BinInt.Z.divide a b))
def ZArith.Znumtheory.Zmod_divideStatement := ∀ (a b : Z) (_ : Not ((b = Z0))) (_ : ((ZArith.BinInt.Z.modulo a b) = Z0)), ZArith.BinInt.Z.divide b a
def ZArith.Zorder.Zge_transStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.ge n m) (_ : ZArith.BinInt.Z.ge m p), ZArith.BinInt.Z.ge n p
def ZArith.Zorder.Zle_0_minus_leStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.le Z0 (ZArith.BinInt.Z.sub n m)), ZArith.BinInt.Z.le m n
def ZArith.Zorder.Zle_0_natStatement := ∀ n : Nat, ZArith.BinInt.Z.le Z0 (ZArith.BinInt.Z.of_nat n)
def ZArith.Zorder.Zle_lt_or_eqStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.le n m), Or (ZArith.BinInt.Z.lt n m) ((n = m))
def ZArith.Zorder.Zle_lt_succStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.le n m), ZArith.BinInt.Z.lt n (ZArith.BinInt.Z.succ m)
def ZArith.Zorder.Zle_minus_le_0Statement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.le m n), ZArith.BinInt.Z.le Z0 (ZArith.BinInt.Z.sub n m)
def ZArith.Zorder.Zle_not_gtStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.le n m), Not (ZArith.BinInt.Z.gt n m)
def ZArith.Zorder.Zle_succ_leStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.le (ZArith.BinInt.Z.succ n) m), ZArith.BinInt.Z.le n m
def ZArith.Zorder.Zlt_0_le_0_predStatement := ∀ (n : Z) (_ : ZArith.BinInt.Z.lt Z0 n), ZArith.BinInt.Z.le Z0 (ZArith.BinInt.Z.pred n)
def ZArith.Zorder.Zlt_le_succStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.lt n m), ZArith.BinInt.Z.le (ZArith.BinInt.Z.succ n) m
def ZArith.Zorder.Zlt_not_leStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.lt n m), Not (ZArith.BinInt.Z.le m n)
def ZArith.Zorder.Zlt_succ_leStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.lt n (ZArith.BinInt.Z.succ m)), ZArith.BinInt.Z.le n m
def ZArith.Zorder.Zlt_succ_predStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.lt (ZArith.BinInt.Z.succ n) m), ZArith.BinInt.Z.lt n (ZArith.BinInt.Z.pred m)
def ZArith.Zorder.Zmult_ge_compat_rStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.ge n m) (_ : ZArith.BinInt.Z.ge p Z0), ZArith.BinInt.Z.ge (ZArith.BinInt.Z.mul n p) (ZArith.BinInt.Z.mul m p)
def ZArith.Zorder.Zmult_le_0_reg_rStatement := ∀ (n m : Z) (_ : ZArith.BinInt.Z.gt n Z0) (_ : ZArith.BinInt.Z.le Z0 (ZArith.BinInt.Z.mul m n)), ZArith.BinInt.Z.le Z0 m
def ZArith.Zorder.Zmult_le_compat_lStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.le n m) (_ : ZArith.BinInt.Z.le Z0 p), ZArith.BinInt.Z.le (ZArith.BinInt.Z.mul p n) (ZArith.BinInt.Z.mul p m)
def ZArith.Zorder.Zmult_le_compat_rStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.le n m) (_ : ZArith.BinInt.Z.le Z0 p), ZArith.BinInt.Z.le (ZArith.BinInt.Z.mul n p) (ZArith.BinInt.Z.mul m p)
def ZArith.Zorder.Zmult_le_compatStatement := ∀ (n m p q : Z) (_ : ZArith.BinInt.Z.le n p) (_ : ZArith.BinInt.Z.le m q) (_ : ZArith.BinInt.Z.le Z0 n) (_ : ZArith.BinInt.Z.le Z0 m), ZArith.BinInt.Z.le (ZArith.BinInt.Z.mul n m) (ZArith.BinInt.Z.mul p q)
def ZArith.Zorder.Zmult_le_reg_rStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.gt p Z0) (_ : ZArith.BinInt.Z.le (ZArith.BinInt.Z.mul n p) (ZArith.BinInt.Z.mul m p)), ZArith.BinInt.Z.le n m
def ZArith.Zorder.Zmult_lt_compat_lStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.lt Z0 p) (_ : ZArith.BinInt.Z.lt n m), ZArith.BinInt.Z.lt (ZArith.BinInt.Z.mul p n) (ZArith.BinInt.Z.mul p m)
def ZArith.Zorder.Zmult_lt_compat_rStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.lt Z0 p) (_ : ZArith.BinInt.Z.lt n m), ZArith.BinInt.Z.lt (ZArith.BinInt.Z.mul n p) (ZArith.BinInt.Z.mul m p)
def ZArith.Zorder.Zmult_lt_compat2Statement := ∀ (n m p q : Z) (_ : And (ZArith.BinInt.Z.lt Z0 n) (ZArith.BinInt.Z.le n p)) (_ : And (ZArith.BinInt.Z.lt Z0 m) (ZArith.BinInt.Z.lt m q)), ZArith.BinInt.Z.lt (ZArith.BinInt.Z.mul n m) (ZArith.BinInt.Z.mul p q)
def ZArith.Zorder.Zmult_lt_reg_rStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.lt Z0 p) (_ : ZArith.BinInt.Z.lt (ZArith.BinInt.Z.mul n p) (ZArith.BinInt.Z.mul m p)), ZArith.BinInt.Z.lt n m
def ZArith.Zorder.Znot_ge_ltStatement := ∀ (n m : Z) (_ : Not (ZArith.BinInt.Z.ge n m)), ZArith.BinInt.Z.lt n m
def ZArith.Zorder.Znot_gt_leStatement := ∀ (n m : Z) (_ : Not (ZArith.BinInt.Z.gt n m)), ZArith.BinInt.Z.le n m
def ZArith.Zorder.Znot_le_gtStatement := ∀ (n m : Z) (_ : Not (ZArith.BinInt.Z.le n m)), ZArith.BinInt.Z.gt n m
def ZArith.Zorder.Zplus_le_compat_rStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.le n m), ZArith.BinInt.Z.le (ZArith.BinInt.Z.add n p) (ZArith.BinInt.Z.add m p)
def ZArith.Zorder.Zplus_le_reg_rStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.le (ZArith.BinInt.Z.add n p) (ZArith.BinInt.Z.add m p)), ZArith.BinInt.Z.le n m
def ZArith.Zorder.Zplus_lt_compat_lStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.lt n m), ZArith.BinInt.Z.lt (ZArith.BinInt.Z.add p n) (ZArith.BinInt.Z.add p m)
def ZArith.Zorder.Zplus_lt_compat_rStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.lt n m), ZArith.BinInt.Z.lt (ZArith.BinInt.Z.add n p) (ZArith.BinInt.Z.add m p)
def ZArith.Zorder.Zplus_lt_reg_lStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.lt (ZArith.BinInt.Z.add p n) (ZArith.BinInt.Z.add p m)), ZArith.BinInt.Z.lt n m
def ZArith.Zorder.Zplus_lt_reg_rStatement := ∀ (n m p : Z) (_ : ZArith.BinInt.Z.lt (ZArith.BinInt.Z.add n p) (ZArith.BinInt.Z.add m p)), ZArith.BinInt.Z.lt n m
def ZArith.Zpower.shift_pos_correctStatement := ∀ p x : positive, ((Zpos (shift_pos p x)) = (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.pow_pos (Zpos (xO xH)) p) (Zpos x)))
def ZArith.Zpower.two_p_gt_ZEROStatement := ∀ (x : Z) (_ : ZArith.BinInt.Z.le Z0 x), ZArith.BinInt.Z.gt (two_p x) Z0
def ZArith.Zpower.two_p_is_expStatement := ∀ (x y : Z) (_ : ZArith.BinInt.Z.le Z0 x) (_ : ZArith.BinInt.Z.le Z0 y), ((two_p (ZArith.BinInt.Z.add x y)) = (ZArith.BinInt.Z.mul (two_p x) (two_p y)))
def ZArith.Zpower.two_p_SStatement := ∀ (x : Z) (_ : ZArith.BinInt.Z.le Z0 x), ((two_p (ZArith.BinInt.Z.succ x)) = (ZArith.BinInt.Z.mul (Zpos (xO xH)) (two_p x)))
def ZArith.Zpower.two_power_nat_equivStatement := ∀ n : Nat, ((two_power_nat n) = (ZArith.BinInt.Z.pow (Zpos (xO xH)) (ZArith.BinInt.Z.of_nat n)))
def ZArith.Zpower.two_power_nat_SStatement := ∀ n : Nat, ((two_power_nat (Nat.succ n)) = (ZArith.BinInt.Z.mul (Zpos (xO xH)) (two_power_nat n)))
def ZArith.Zpower.two_power_pos_is_expStatement := ∀ x y : positive, ((two_power_pos (PArith.BinPos.Pos.add x y)) = (ZArith.BinInt.Z.mul (two_power_pos x) (two_power_pos y)))
def ZArith.Zpower.two_power_pos_natStatement := ∀ p : positive, ((two_power_pos p) = (two_power_nat (PArith.BinPos.Pos.to_nat p)))
def ZArith.Zpower.Zpower_expStatement := ∀ (x n m : Z) (_ : ZArith.BinInt.Z.ge n Z0) (_ : ZArith.BinInt.Z.ge m Z0), ((ZArith.BinInt.Z.pow x (ZArith.BinInt.Z.add n m)) = (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.pow x n) (ZArith.BinInt.Z.pow x m)))
def ZArith.Zpower.Zpower_nat_is_expStatement := ∀ (n m : Nat) (z : Z), ((Zpower_nat z (Nat.add n m)) = (ZArith.BinInt.Z.mul (Zpower_nat z n) (Zpower_nat z m)))
def ZArith.Zpower.Zpower_nat_ZStatement := ∀ (z : Z) (n : Nat), ((Zpower_nat z n) = (ZArith.BinInt.Z.pow z (ZArith.BinInt.Z.of_nat n)))
def ZArith.Zpower.Zpower_pos_natStatement := ∀ (z : Z) (p : positive), ((ZArith.BinInt.Z.pow_pos z p) = (Zpower_nat z (PArith.BinPos.Pos.to_nat p)))
def ZArith.Zquot.Zquot_Zdiv_posStatement := ∀ (a b : Z) (_ : ZArith.BinInt.Z.le Z0 a) (_ : ZArith.BinInt.Z.le Z0 b), ((ZArith.BinInt.Z.quot a b) = (ZArith.BinInt.Z.div a b))
end Rocq.Coq
end CompCert4Lean.Foundation.Numbers

namespace CompCert4Lean.Foundation.Numbers
namespace Rocq.Coq

theorem ZArith.BinInt.Z.le_refl :
    ZArith.BinInt.Z.le_reflStatement := by
  intro n
  exact Int.le_refl (intOfZ n)

end Rocq.Coq
end CompCert4Lean.Foundation.Numbers

namespace CompCert4Lean.Foundation.Numbers
namespace Rocq.Coq

theorem ZArith.Zorder.Zlt_le_succ :
    ZArith.Zorder.Zlt_le_succStatement := by
  intro n m h
  change intOfZ n < intOfZ m at h
  change intOfZ (ZArith.BinInt.Z.succ n) ≤ intOfZ m
  simp only [ZArith.BinInt.Z.succ, ZArith.BinInt.Z.add,
    intOfZ_zOfInt]
  change intOfZ n + 1 ≤ intOfZ m
  exact (Int.add_one_le_iff).2 h

theorem ZArith.BinInt.Z.le_max_r :
    ZArith.BinInt.Z.le_max_rStatement := by
  intro n m
  change intOfZ m ≤ intOfZ (ZArith.BinInt.Z.max n m)
  by_cases h : intOfZ n ≤ intOfZ m
  · simp [ZArith.BinInt.Z.max, h]
  · simp [ZArith.BinInt.Z.max, h, Int.le_of_not_le h]

theorem ZArith.BinInt.Z.le_lt_trans :
    ZArith.BinInt.Z.le_lt_transStatement := by
  intro n m p hnm hmp
  exact Int.lt_of_le_of_lt hnm hmp

theorem ZArith.BinInt.Z.max_r :
    ZArith.BinInt.Z.max_rStatement := by
  intro n m h
  apply intOfZ_injective
  change intOfZ (ZArith.BinInt.Z.max n m) = intOfZ m
  change intOfZ n ≤ intOfZ m at h
  simp [ZArith.BinInt.Z.max, h]

end Rocq.Coq
end CompCert4Lean.Foundation.Numbers

namespace CompCert4Lean.Foundation.Numbers
namespace Rocq.Coq

theorem ZArith.BinInt.Z.mul_nonneg_nonneg :
    ZArith.BinInt.Z.mul_nonneg_nonnegStatement := by
  intro n m hn hm
  change 0 ≤ intOfZ (ZArith.BinInt.Z.mul n m)
  simp only [ZArith.BinInt.Z.mul, intOfZ_zOfInt]
  exact Int.mul_nonneg hn hm

theorem ZArith.BinInt.Z.max_lub :
    ZArith.BinInt.Z.max_lubStatement := by
  intro n m p hnp hmp
  change intOfZ (ZArith.BinInt.Z.max n m) ≤ intOfZ p
  change intOfZ n ≤ intOfZ p at hnp
  change intOfZ m ≤ intOfZ p at hmp
  by_cases h : intOfZ n ≤ intOfZ m
  · simp [ZArith.BinInt.Z.max, h]
    exact hmp
  · simp [ZArith.BinInt.Z.max, h]
    exact hnp

theorem ZArith.Zorder.Zlt_le_weak_proof :
    ∀ (n m : Z), ZArith.Zorder.Zlt_le_weak n m := by
  intro n m h
  exact Int.le_of_lt h

def ZArith.BinInt.Z.max_case :
    ZArith.BinInt.Z.max_caseStatement := by
  intro n m P hn hm
  by_cases h : intOfZ n ≤ intOfZ m
  · simp [ZArith.BinInt.Z.max, h]
    exact hm
  · simp [ZArith.BinInt.Z.max, h]
    exact hn

end Rocq.Coq
end CompCert4Lean.Foundation.Numbers

namespace CompCert4Lean.Foundation.Numbers
namespace Rocq.Coq

theorem ZArith.BinInt.Z.add_0_r :
    ZArith.BinInt.Z.add_0_rStatement := by
  intro n
  apply intOfZ_injective
  change intOfZ (zOfInt (intOfZ n + 0)) = intOfZ n
  rw [intOfZ_zOfInt]
  simp

theorem ZArith.BinInt.Z.lt_gt :
    ZArith.BinInt.Z.lt_gtStatement := by
  intro n m h
  exact h

theorem ZArith.Zbool.Zle_cases :
    ZArith.Zbool.Zle_casesStatement := by
  intro n m
  by_cases h : intOfZ n ≤ intOfZ m
  · have h' : ZArith.BinInt.Z.le n m := h
    simp [ZArith.BinInt.Z.leb, h, h']
  · simp [ZArith.BinInt.Z.leb, h]
    exact Int.lt_of_not_ge h

theorem ZArith.BinInt.Z.sqrtrem_spec :
    ZArith.BinInt.Z.sqrtrem_specStatement := by
  intro n hn
  change 0 ≤ intOfZ n at hn
  cases n with
  | Z0 =>
      dsimp [ZArith.BinInt.Z.sqrtrem]
      constructor
      · apply intOfZ_injective
        simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
        change (0:Int) =
          (↑(Nat.sqrt 0) : Int) * ↑(Nat.sqrt 0) +
          ↑(0 - Nat.sqrt 0 * Nat.sqrt 0)
        simp [Nat.sqrt]
      constructor
      · unfold ZArith.BinInt.Z.le
        change (0:Int) ≤ intOfZ (zOfInt (Int.ofNat (0 - Nat.sqrt 0 * Nat.sqrt 0)))
        rw [intOfZ_zOfInt]
        exact Int.ofNat_zero_le _
      · unfold ZArith.BinInt.Z.le
        unfold ZArith.BinInt.Z.mul
        simp only [intOfZ_zOfInt]
        change (↑(0 - Nat.sqrt 0 * Nat.sqrt 0) : Int) ≤
          (↑(posToNat (xO xH)) : Int) * ↑(Nat.sqrt 0)
        rw [← Int.natCast_mul]
        apply Int.ofNat_le.mpr
        simp [Nat.sqrt, posToNat]
  | Zpos p =>
      dsimp [ZArith.BinInt.Z.sqrtrem]
      have hsq : Nat.sqrt (posToNat p) * Nat.sqrt (posToNat p) ≤ posToNat p := Nat.sqrt_le _
      have hlt : posToNat p < (Nat.sqrt (posToNat p) + 1) * (Nat.sqrt (posToNat p) + 1) := Nat.lt_succ_sqrt _
      constructor
      · apply intOfZ_injective
        simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
        change (↑(posToNat p) : Int) =
          ↑(Nat.sqrt (posToNat p)) * ↑(Nat.sqrt (posToNat p)) +
          ↑(posToNat p - Nat.sqrt (posToNat p) * Nat.sqrt (posToNat p))
        rw [← Int.natCast_mul, ← Int.natCast_add]
        exact congrArg (fun x : Nat => (↑x : Int)) (by simpa [Nat.add_comm] using (Nat.sub_add_cancel hsq).symm)
      constructor
      · unfold ZArith.BinInt.Z.le
        change (0:Int) ≤ intOfZ (zOfInt (Int.ofNat (posToNat p - Nat.sqrt (posToNat p) * Nat.sqrt (posToNat p))))
        rw [intOfZ_zOfInt]
        exact Int.ofNat_zero_le _
      · unfold ZArith.BinInt.Z.le
        unfold ZArith.BinInt.Z.mul
        simp only [intOfZ_zOfInt]
        change (↑(posToNat p - Nat.sqrt (posToNat p) * Nat.sqrt (posToNat p)) : Int) ≤
          (↑(posToNat (xO xH)) : Int) * ↑(Nat.sqrt (posToNat p))
        rw [← Int.natCast_mul]
        apply Int.ofNat_le.mpr
        simp only [posToNat]
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at hlt
        omega
  | Zneg p =>
      have hp := posToNat_positive p
      have : ¬ (0 ≤ intOfZ (Zneg p)) := by simp [intOfZ]; omega
      exact (this hn).elim

end Rocq.Coq
end CompCert4Lean.Foundation.Numbers

namespace CompCert4Lean.Foundation.Numbers
namespace Rocq.Coq

theorem Arith.PeanoNat.Nat.eqb_refl :
    Arith.PeanoNat.Nat.eqb_reflStatement := by
  intro x
  simp [Arith.PeanoNat.Nat.eqb]

theorem Arith.PeanoNat.Nat.lt_0_succ :
    Arith.PeanoNat.Nat.lt_0_succStatement := by
  intro n
  exact Nat.zero_lt_succ n

theorem ZArith.Zorder.Zplus_le_reg_r :
    ZArith.Zorder.Zplus_le_reg_rStatement := by
  intro n m p h
  simp only [ZArith.BinInt.Z.le, ZArith.BinInt.Z.add, intOfZ_zOfInt] at h
  exact (Int.add_le_add_iff_right (intOfZ p)).mp h

end Rocq.Coq
end CompCert4Lean.Foundation.Numbers

namespace CompCert4Lean.Foundation.Numbers
namespace Rocq.Coq

theorem ZArith.Zdiv.Z_div_mod_eq_full :
    ZArith.Zdiv.Z_div_mod_eq_fullStatement := by
  intro a b
  apply intOfZ_injective
  dsimp [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
    ZArith.BinInt.Z.div, ZArith.BinInt.Z.modulo, intOfZ_zOfInt]
  simp only [intOfZ_zOfInt]
  unfold ZArith.BinInt.Z.zDivEucl ZArith.BinInt.Z.zModEucl
  by_cases hb0 : intOfZ b = 0
  · simp [hb0]
  by_cases hbpos : 0 < intOfZ b
  · simp only [hb0, hbpos, if_false, if_true]
    calc
      intOfZ a =
          (intOfZ a).ediv (intOfZ b) * intOfZ b +
            (intOfZ a).emod (intOfZ b) :=
        (Int.ediv_mul_add_emod (intOfZ a) (intOfZ b)).symm
      _ = intOfZ b * (intOfZ a).ediv (intOfZ b) +
            (intOfZ a).emod (intOfZ b) := by rw [Int.mul_comm]
  · have hbneg : intOfZ b < 0 := by omega
    simp only [hb0, hbpos, if_false]
    by_cases hr : (intOfZ a).emod (-intOfZ b) = 0
    · simp only [hr, if_true]
      calc
        intOfZ a =
            (intOfZ a).ediv (-intOfZ b) * (-intOfZ b) := by
          have hde :
              (intOfZ a).ediv (-intOfZ b) * (-intOfZ b) +
                (intOfZ a).emod (-intOfZ b) = intOfZ a :=
            Int.ediv_mul_add_emod (intOfZ a) (-intOfZ b)
          rw [hr, Int.add_zero] at hde
          exact hde.symm
        _ = intOfZ b * -(intOfZ a).ediv (-intOfZ b) + 0 := by
          calc
            (intOfZ a).ediv (-intOfZ b) * (-intOfZ b) =
                -((intOfZ a).ediv (-intOfZ b) * intOfZ b) :=
              Int.mul_neg _ _
            _ = -(intOfZ b * (intOfZ a).ediv (-intOfZ b)) := by
              exact congrArg Int.neg (Int.mul_comm _ _)
            _ = intOfZ b * -(intOfZ a).ediv (-intOfZ b) :=
              (Int.mul_neg _ _).symm
            _ = intOfZ b * -(intOfZ a).ediv (-intOfZ b) + 0 := by
              exact (Int.add_zero _).symm
    · simp only [hr, if_false]
      calc
        intOfZ a =
            (intOfZ a).ediv (-intOfZ b) * (-intOfZ b) +
              (intOfZ a).emod (-intOfZ b) := by
          exact (Int.ediv_mul_add_emod (intOfZ a) (-intOfZ b)).symm
        _ = intOfZ b * -((intOfZ a).ediv (-intOfZ b) + 1) +
              ((intOfZ a).emod (-intOfZ b) - (-intOfZ b)) := by
          simp only [Int.sub_eq_add_neg, Int.mul_neg, Int.neg_add,
            Int.mul_add, Int.mul_one, Int.mul_neg_one, Int.neg_neg]
          rw [Int.mul_comm ((intOfZ a).ediv (-intOfZ b)) (intOfZ b)]
          omega

end Rocq.Coq
end CompCert4Lean.Foundation.Numbers

namespace CompCert4Lean.Foundation.Numbers.Rocq.Coq.Arith.PeanoNat.Nat

theorem sub_add : sub_addStatement := by
  intro n m h
  exact Nat.sub_add_cancel h

end CompCert4Lean.Foundation.Numbers.Rocq.Coq.Arith.PeanoNat.Nat

namespace CompCert4Lean.Foundation.Numbers
namespace Rocq.Coq

theorem Arith.PeanoNat.Nat.add_0_r :
    Arith.PeanoNat.Nat.add_0_rStatement := by
  intro n
  exact Nat.add_zero n

end Rocq.Coq
end CompCert4Lean.Foundation.Numbers

namespace CompCert4Lean.Foundation.Numbers
namespace Rocq.Coq

theorem Arith.PeanoNat.Nat.add_lt_mono_r :
    Arith.PeanoNat.Nat.add_lt_mono_rStatement := by
  intro n m p
  unfold Arith.PeanoNat.Nat.lt
  exact (Nat.add_lt_add_iff_right (k := p) (n := n) (m := m)).symm

end Rocq.Coq
end CompCert4Lean.Foundation.Numbers

namespace CompCert4Lean.Foundation.Numbers
namespace Rocq.Coq

theorem Arith.PeanoNat.Nat.eqb_eq :
    Arith.PeanoNat.Nat.eqb_eqStatement := by
  intro n m
  simp [Arith.PeanoNat.Nat.eqb]

end Rocq.Coq
end CompCert4Lean.Foundation.Numbers

namespace CompCert4Lean.Foundation.Numbers
namespace Rocq.Coq

theorem Init.Peano.plus_n_Sm :
    Init.Peano.plus_n_SmStatement := by
  intro n m
  exact (Nat.add_succ n m).symm

theorem Init.Peano.le_0_n :
    Init.Peano.le_0_nStatement := by
  intro n
  exact Nat.zero_le n

theorem Init.Peano.le_n_S :
    Init.Peano.le_n_SStatement := by
  intro n m h
  exact Nat.succ_le_succ h

theorem PArith.BinPos.Pos.compare_refl :
    PArith.BinPos.Pos.compare_reflStatement := by
  intro x
  unfold PArith.BinPos.Pos.compare
  change (if posToNat x < posToNat x then (Lt : comparison)
    else if posToNat x = posToNat x then (Eq : comparison)
    else (Gt : comparison)) = (Eq : comparison)
  split
  · rename_i h
    exact (Nat.lt_irrefl _ h).elim
  · split
    · rfl
    · rename_i hlt heq
      exact (heq rfl).elim

end Rocq.Coq
end CompCert4Lean.Foundation.Numbers

namespace CompCert4Lean.Foundation.Numbers
namespace Rocq.Coq

theorem PArith.BinPos.Pos.leb_refl :
    PArith.BinPos.Pos.leb_reflStatement := by
  intro x
  unfold PArith.BinPos.Pos.leb
  simp

theorem PArith.BinPos.Pos.lt_irrefl :
    PArith.BinPos.Pos.lt_irreflStatement := by
  intro x h
  exact Nat.lt_irrefl _ h

theorem PArith.BinPos.Pos.pred_double_succ :
    PArith.BinPos.Pos.pred_double_succStatement := by
  intro p
  induction p with
  | xH => rfl
  | xI q ih => simp [PArith.BinPos.Pos.succ, PArith.BinPos.Pos.pred_double, ih]
  | xO q ih => rfl

theorem PArith.BinPos.Pos.compare_gt_iff :
    PArith.BinPos.Pos.compare_gt_iffStatement := by
  intro x y
  unfold PArith.BinPos.Pos.compare PArith.BinPos.Pos.lt
  change (if posToNat x < posToNat y then (Lt : comparison)
    else if posToNat x = posToNat y then (Eq : comparison)
    else (Gt : comparison)) = (Gt : comparison) ↔
      posToNat y < posToNat x
  by_cases hxy : posToNat x < posToNat y
  · have hnot : ¬ posToNat y < posToNat x :=
      Nat.not_lt_of_ge (Nat.le_of_lt hxy)
    simp [hxy, hnot]
  · by_cases heq : posToNat x = posToNat y
    · simp [hxy, heq]
    · have hyx : posToNat y < posToNat x := by omega
      simp [hxy, heq, hyx]

end Rocq.Coq
end CompCert4Lean.Foundation.Numbers

namespace CompCert4Lean.Foundation.Numbers
namespace Rocq.Coq

theorem PArith.BinPos.Pos.posToNat_succ (p : positive) :
    posToNat (PArith.BinPos.Pos.succ p) = posToNat p + 1 := by
  induction p with
  | xH => simp [PArith.BinPos.Pos.succ, posToNat]
  | xI q ih => simp [PArith.BinPos.Pos.succ, posToNat, ih] <;> omega
  | xO q ih => simp [PArith.BinPos.Pos.succ, posToNat]

theorem PArith.BinPos.Pos.succ_pred_or :
    PArith.BinPos.Pos.succ_pred_orStatement := by
  intro p
  cases p with
  | xH => exact Or.inl rfl
  | xI q => exact Or.inr rfl
  | xO q =>
      right
      change PArith.BinPos.Pos.succ (PArith.BinPos.Pos.pred_double q) = .xO q
      induction q with
      | xH => rfl
      | xI r ih => rfl
      | xO r ih => simp [PArith.BinPos.Pos.pred_double, PArith.BinPos.Pos.succ, ih]

theorem PArith.BinPos.Pos.add_1_r :
    PArith.BinPos.Pos.add_1_rStatement := by
  intro p
  apply posToNat_injective
  calc
    posToNat (PArith.BinPos.Pos.add p xH) = posToNat p + posToNat xH := by
      unfold PArith.BinPos.Pos.add
      apply posToNat_posOfNat
      have hp := posToNat_positive p
      simp [posToNat]
    _ = posToNat (PArith.BinPos.Pos.succ p) := by
      simpa [posToNat] using (PArith.BinPos.Pos.posToNat_succ p).symm

theorem PArith.BinPos.Pos.mul_comm :
    PArith.BinPos.Pos.mul_commStatement := by
  intro p q
  apply posToNat_injective
  calc
    posToNat (PArith.BinPos.Pos.mul p q) = posToNat p * posToNat q := by
      unfold PArith.BinPos.Pos.mul
      apply posToNat_posOfNat
      have hp := posToNat_positive p
      have hq := posToNat_positive q
      exact Nat.mul_pos hp hq
    _ = posToNat q * posToNat p := Nat.mul_comm _ _
    _ = posToNat (PArith.BinPos.Pos.mul q p) := by
      symm
      unfold PArith.BinPos.Pos.mul
      apply posToNat_posOfNat
      have hp := posToNat_positive p
      have hq := posToNat_positive q
      exact Nat.mul_pos hq hp

private theorem natIter_comp_succ {A : Type} (f : A → A) (n : Nat) (x : A) :
    natIter f n (f x) = f (natIter f n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [natIter, ih]

theorem PArith.BinPos.Pos.iter_succ :
    PArith.BinPos.Pos.iter_succStatement := by
  intro p A f x
  unfold PArith.BinPos.Pos.iter
  rw [PArith.BinPos.Pos.posToNat_succ]
  change natIter f (posToNat p) (f x) = f (natIter f (posToNat p) x)
  exact natIter_comp_succ f (posToNat p) x

end Rocq.Coq
end CompCert4Lean.Foundation.Numbers

namespace CompCert4Lean.Foundation.Numbers
namespace Rocq.Coq

theorem PArith.BinPos.Pos.eqb_eq :
    PArith.BinPos.Pos.eqb_eqStatement := by
  intro p q
  simp [PArith.BinPos.Pos.eqb]

end Rocq.Coq
end CompCert4Lean.Foundation.Numbers

namespace CompCert4Lean.Foundation.Numbers
namespace Rocq.Coq

theorem PArith.BinPos.Pos.leb_le :
    PArith.BinPos.Pos.leb_leStatement := by
  intro p q
  unfold PArith.BinPos.Pos.leb PArith.BinPos.Pos.le
  by_cases h : posToNat p ≤ posToNat q
  · simp [h]
  · simp [h]

end Rocq.Coq
end CompCert4Lean.Foundation.Numbers

namespace CompCert4Lean.Foundation.Numbers
namespace Rocq.Coq

private theorem comparisonOfNat_antisym (a b : Nat) :
    CompOpp (comparisonOfNat a b) = comparisonOfNat b a := by
  unfold comparisonOfNat
  by_cases hab : a < b
  · have hba : ¬ b < a := Nat.not_lt_of_ge (Nat.le_of_lt hab)
    have hne : a ≠ b := by omega
    have hne' : b ≠ a := by omega
    simp only [if_pos hab, if_neg hba, if_neg hne']
    rfl
  · by_cases heq : a = b
    · subst b
      simp only [if_neg hab, if_pos rfl]
      rfl
    · have hba : b < a := by omega
      have hne : b ≠ a := by omega
      simp only [if_neg hab, if_neg heq, if_pos hba]
      rfl

private theorem compare_antisym_aux (p q : positive) :
    CompOpp (PArith.BinPos.Pos.compare p q) =
      PArith.BinPos.Pos.compare q p := by
  unfold PArith.BinPos.Pos.compare
  exact comparisonOfNat_antisym (posToNat p) (posToNat q)

private theorem compare_eq_iff_aux (p q : positive) :
    PArith.BinPos.Pos.compare p q = Eq ↔
      PArith.BinPos.Pos.compare q p = Eq := by
  constructor
  · intro h
    have h' := compare_antisym_aux p q
    rw [h] at h'
    change Eq = PArith.BinPos.Pos.compare q p at h'
    exact h'.symm
  · intro h
    have h' := compare_antisym_aux q p
    rw [h] at h'
    change Eq = PArith.BinPos.Pos.compare p q at h'
    exact h'.symm

theorem PArith.BinPos.Pcompare_antisym_proof :
    PArith.BinPos.Pcompare_antisym := by
  intro p q c
  cases c with
  | Eq =>
      exact compare_antisym_aux p q
  | Lt =>
      by_cases h : PArith.BinPos.Pos.compare p q = Eq
      · have h' : PArith.BinPos.Pos.compare q p = Eq :=
          compare_eq_iff_aux p q |>.mp h
        change CompOpp (if PArith.BinPos.Pos.compare p q = Eq then Lt
          else PArith.BinPos.Pos.compare p q) =
          (if PArith.BinPos.Pos.compare q p = Eq then Gt
          else PArith.BinPos.Pos.compare q p)
        simp only [if_pos h, if_pos h']
        rfl
      · have h' : PArith.BinPos.Pos.compare q p ≠ Eq := by
          intro hq
          exact h (compare_eq_iff_aux p q |>.mpr hq)
        change CompOpp (if PArith.BinPos.Pos.compare p q = Eq then Lt
          else PArith.BinPos.Pos.compare p q) =
          (if PArith.BinPos.Pos.compare q p = Eq then Gt
          else PArith.BinPos.Pos.compare q p)
        simp only [if_neg h, if_neg h']
        exact compare_antisym_aux p q
  | Gt =>
      by_cases h : PArith.BinPos.Pos.compare p q = Eq
      · have h' : PArith.BinPos.Pos.compare q p = Eq :=
          compare_eq_iff_aux p q |>.mp h
        change CompOpp (if PArith.BinPos.Pos.compare p q = Eq then Gt
          else PArith.BinPos.Pos.compare p q) =
          (if PArith.BinPos.Pos.compare q p = Eq then Lt
          else PArith.BinPos.Pos.compare q p)
        simp only [if_pos h, if_pos h']
        rfl
      · have h' : PArith.BinPos.Pos.compare q p ≠ Eq := by
          intro hq
          exact h (compare_eq_iff_aux p q |>.mpr hq)
        change CompOpp (if PArith.BinPos.Pos.compare p q = Eq then Gt
          else PArith.BinPos.Pos.compare p q) =
          (if PArith.BinPos.Pos.compare q p = Eq then Lt
          else PArith.BinPos.Pos.compare q p)
        simp only [if_neg h, if_neg h']
        exact compare_antisym_aux p q

end Rocq.Coq
end CompCert4Lean.Foundation.Numbers

namespace CompCert4Lean.Foundation.Numbers
namespace Rocq.Coq

theorem PArith.BinPos.Pos.compare_eq_iff :
    PArith.BinPos.Pos.compare_eq_iffStatement := by
  intro p q
  constructor
  · intro h
    unfold PArith.BinPos.Pos.compare at h
    change (if posToNat p < posToNat q then (Lt : comparison)
      else if posToNat p = posToNat q then (Eq : comparison)
      else (Gt : comparison)) = (Eq : comparison) at h
    by_cases hpq : posToNat p < posToNat q
    · simp [hpq] at h
    · by_cases heq : posToNat p = posToNat q
      · apply posToNat_injective
        exact heq
      · simp [hpq, heq] at h
  · intro hpq
    cases hpq
    unfold PArith.BinPos.Pos.compare
    change (if posToNat p < posToNat p then (Lt : comparison)
      else if posToNat p = posToNat p then (Eq : comparison)
      else (Gt : comparison)) = (Eq : comparison)
    simp

end Rocq.Coq
end CompCert4Lean.Foundation.Numbers

namespace CompCert4Lean.Foundation.Numbers
namespace Rocq.Coq

theorem PArith.BinPos.Pos.compare_antisym :
    PArith.BinPos.Pos.compare_antisymStatement := by
  intro p q
  exact (compare_antisym_aux p q).symm

theorem PArith.BinPos.Pos.lt_succ_r :
    PArith.BinPos.Pos.lt_succ_rStatement := by
  intro p q
  unfold PArith.BinPos.Pos.lt PArith.BinPos.Pos.le
  rw [PArith.BinPos.Pos.posToNat_succ]
  omega

theorem PArith.BinPos.Pos.lt_le_incl :
    PArith.BinPos.Pos.lt_le_inclStatement := by
  intro p q h
  change posToNat p < posToNat q at h
  change posToNat p ≤ posToNat q
  exact Nat.le_of_lt h

theorem PArith.BinPos.Pos.lt_trans :
    PArith.BinPos.Pos.lt_transStatement := by
  intro n m p hnm hmp
  unfold PArith.BinPos.Pos.lt at hnm hmp ⊢
  exact Nat.lt_trans hnm hmp

end Rocq.Coq
end CompCert4Lean.Foundation.Numbers
