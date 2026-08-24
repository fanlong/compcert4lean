import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Zbits
import CompCert4Lean.X86_64.Archi

/-!
# Fixed-width CompCert integers

This file provides the definition-translation surface selected from
`compcert.lib.Integers`.  Fixed-width values retain the source's proof-carrying
record carrier (`intval` together with `intrange`).  The executable bitvector
operations use the normalized natural-number view of that carrier.
-/

namespace CompCert4Lean.Lib.Integers

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private abbrev zZero : Z := Z0
private abbrev zOne : Z := Zpos xH
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zMul := ZArith.BinInt.Z.mul
private abbrev zOpp := ZArith.BinInt.Z.opp
private abbrev zDiv := ZArith.BinInt.Z.div
private abbrev zMod := ZArith.BinInt.Z.modulo
private abbrev zQuot := ZArith.BinInt.Z.quot
private abbrev zShiftl := ZArith.BinInt.Z.shiftl
private abbrev zShiftr := ZArith.BinInt.Z.shiftr
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev zLtb := ZArith.BinInt.Z.ltb
private abbrev zDivide := ZArith.BinInt.Z.divide
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev zToNat := ZArith.BinInt.Z.to_nat
private abbrev zTestbit := ZArith.BinInt.Z.testbit
private abbrev zTwoP := two_p
private abbrev zTwoPowerNat := two_power_nat

private def sumboolSelect {P Q : Prop} {A : Type}
    (d : CompCert4Lean.Foundation.Logic.Support.Sumbool P Q)
    (ifso ifnot : A) : A :=
  match d with
  | .left _ => ifso
  | .right _ => ifnot

private abbrev zltSelect (x y : Z) {A : Type} (ifso ifnot : A) : A :=
  sumboolSelect (CompCert4Lean.Lib.Coqlib.zlt x y) ifso ifnot

inductive comparison : Type where
  | Ceq
  | Cne
  | Clt
  | Cle
  | Cgt
  | Cge
deriving DecidableEq

export comparison (Ceq Cne Clt Cle Cgt Cge)

def negate_comparison : comparison → comparison
  | .Ceq => .Cne
  | .Cne => .Ceq
  | .Clt => .Cge
  | .Cle => .Cgt
  | .Cgt => .Cle
  | .Cge => .Clt

def swap_comparison : comparison → comparison
  | .Ceq => .Ceq
  | .Cne => .Cne
  | .Clt => .Cgt
  | .Cle => .Cge
  | .Cgt => .Clt
  | .Cge => .Cle

namespace WordCore

private theorem twoPowerNat_eq_zOfNat_twoPow (bits : Nat) :
    zTwoPowerNat bits = zOfNat (2 ^ bits) := by
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
      (Zpos (.xO .xH))
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat bits) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (2 ^ bits)
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
  rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat bits =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat bits) by rfl]
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  have hnonneg : ¬Int.ofNat bits < 0 :=
    Int.not_lt.mpr (Int.natCast_nonneg bits)
  rw [if_neg hnonneg]
  simp only [Int.ofNat_eq_natCast, Int.toNat_natCast]
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
    show CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (2 ^ bits) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat (2 ^ bits)) by rfl,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change (2 : Int) ^ bits = Int.ofNat (2 ^ bits)
  exact (Int.natCast_pow 2 bits).symm

structure Word (bits : Nat) where
  mkint ::
  intval : Z
  intrange : zLt (zOpp zOne) intval ∧ zLt intval (zTwoPowerNat bits)
deriving DecidableEq

theorem ext {bits : Nat} {x y : Word bits} (h : x.intval = y.intval) : x = y := by
  cases x with
  | mkint xv xh =>
    cases y with
    | mkint yv yh =>
      cases h
      rfl

private def positiveToNat : positive → Nat
  | .xH => 1
  | .xI p => 2 * positiveToNat p + 1
  | .xO p => 2 * positiveToNat p

private theorem positiveToNat_eq_posToNat (p : positive) :
    positiveToNat p = CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p := by
  induction p with
  | xH => rfl
  | xI p ih => simp [positiveToNat, CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat, ih]
  | xO p ih => simp [positiveToNat, CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat, ih]

@[simp] private theorem zToNat_zOfNat (n : Nat) : zToNat (zOfNat n) = n := by
  exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Nat2Z.id n

def Word.val {bits : Nat} (x : Word bits) : Nat := zToNat x.intval

private abbrev natVal {bits : Nat} (x : Word bits) : Nat := Word.val x

private theorem intval_eq_zOfNat_val {bits : Nat} (x : Word bits) :
    x.intval = zOfNat x.val := by
  have hx : zLe zZero x.intval := by
    have h := x.intrange.1
    change (-1 : Int) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval at h
    change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval
    omega
  exact (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Z2Nat.id
    x.intval hx).symm

theorem ext_of_val_eq {bits : Nat} {x y : Word bits} (h : x.val = y.val) : x = y := by
  apply ext
  rw [intval_eq_zOfNat_val x, intval_eq_zOfNat_val y, h]

private theorem val_lt {bits : Nat} (x : Word bits) : x.val < 2 ^ bits := by
  have h := x.intrange.2
  rw [twoPowerNat_eq_zOfNat_twoPow] at h
  rw [intval_eq_zOfNat_val x] at h
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat x.val)) <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat (2 ^ bits))) at h
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at h
  exact Int.ofNat_lt.mp h

/-- Computational finite residue view used at the bitvector boundary. -/
def Word.toFin {bits : Nat} (x : Word bits) : Fin (2 ^ bits) :=
  ⟨x.val, val_lt x⟩

private def residue (bits : Nat) : Z → Nat
  | .Z0 => 0
  | .Zpos p => positiveToNat p % (2 ^ bits)
  | .Zneg p =>
      let modulus := 2 ^ bits
      let r := positiveToNat p % modulus
      if r = 0 then 0 else modulus - r

private theorem residue_range (bits : Nat) (x : Z) :
    residue bits x < 2 ^ bits := by
  cases x with
  | Z0 => exact Nat.two_pow_pos bits
  | Zpos p => exact Nat.mod_lt _ (Nat.two_pow_pos bits)
  | Zneg p =>
      dsimp [residue]
      split <;> omega

private theorem repr_intrange (bits : Nat) (x : Z) :
    zLt (zOpp zOne) (zOfNat (residue bits x)) ∧
      zLt (zOfNat (residue bits x)) (zTwoPowerNat bits) := by
  have hr := residue_range bits x
  constructor
  · have hnonneg : (0 : Int) ≤ Int.ofNat (residue bits x) :=
      Int.natCast_nonneg _
    have h : (-1 : Int) < Int.ofNat (residue bits x) := by omega
    have hneg : zOpp zOne = CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (-1) := by rfl
    have hn : zOfNat (residue bits x) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (Int.ofNat (residue bits x)) := by rfl
    rw [hneg, hn]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (-1)) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (Int.ofNat (residue bits x)))
    simpa only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] using h
  · have h : Int.ofNat (residue bits x) < Int.ofNat (2 ^ bits) :=
      Int.ofNat_lt.mpr hr
    have hn : zOfNat (residue bits x) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (Int.ofNat (residue bits x)) := by rfl
    have hm : zTwoPowerNat bits =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (Int.ofNat (2 ^ bits)) := by
      rw [twoPowerNat_eq_zOfNat_twoPow]
      rfl
    rw [hn, hm]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (Int.ofNat (residue bits x))) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat (2 ^ bits)))
    simpa only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] using h

private theorem residue_zOfNat (bits n : Nat) :
    residue bits (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat n)) =
      n % (2 ^ bits) := by
  cases n with
  | zero => rfl
  | succ n =>
      simp [residue, CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt,
        positiveToNat_eq_posToNat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat
          (n := n + 1) (Nat.succ_pos n)]

private theorem nat_sub_of_eq_sub {m r t : Nat} (h : r = m - t) (ht : t < m) :
    m - r = t := by
  omega

private theorem residue_zOfInt (bits : Nat) (i : Int) :
    residue bits (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt i) =
      Int.toNat (i % ((2 ^ bits : Nat) : Int)) := by
  cases i with
  | ofNat n =>
    rw [residue_zOfNat]
    simpa using
      (Int.emod_natAbs_of_nonneg (x := Int.ofNat n) (n := 2 ^ bits)
        (Int.natCast_nonneg n))
  | negSucc n =>
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt, residue,
        positiveToNat_eq_posToNat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat
          (n := n + 1) (Nat.succ_pos n)]
    have hm : 2 ^ bits ≠ 0 := Nat.ne_of_gt (Nat.two_pow_pos bits)
    have hneg : Int.negSucc n < 0 := Int.negSucc_lt_zero n
    have hbridge :=
      Int.emod_natAbs_of_neg (x := Int.negSucc n) hneg (n := 2 ^ bits) hm
    by_cases hdvd : ((2 ^ bits : Nat) : Int) ∣ Int.negSucc n
    · rw [if_pos hdvd] at hbridge
      have hz : Int.negSucc n % ((2 ^ bits : Nat) : Int) = 0 :=
        Int.emod_eq_zero_of_dvd hdvd
      have hrem : (n + 1) % (2 ^ bits) = 0 := by
        simpa only [Int.natAbs_negSucc] using hbridge
      rw [if_pos hrem, hz]
      rfl
    · rw [if_neg hdvd] at hbridge
      simp only [Int.natAbs_negSucc] at hbridge
      have hmpos : (0 : Int) < Int.ofNat (2 ^ bits) :=
        by simpa only [Int.ofNat_eq_natCast] using
          Int.natCast_pos.mpr (Nat.two_pow_pos bits)
      have hmodlt :
          Int.negSucc n % ((2 ^ bits : Nat) : Int) < ((2 ^ bits : Nat) : Int) :=
        Int.emod_lt_of_pos _ (by simpa only [Int.ofNat_eq_natCast] using hmpos)
      have hmodnonneg : 0 ≤ Int.negSucc n % ((2 ^ bits : Nat) : Int) :=
        Int.emod_nonneg _ (Int.ne_of_gt (by simpa only [Int.ofNat_eq_natCast] using hmpos))
      have hmodnatlt :
          Int.toNat (Int.negSucc n % ((2 ^ bits : Nat) : Int)) < 2 ^ bits :=
        (Int.toNat_lt hmodnonneg).mpr hmodlt
      have hrem : (n + 1) % (2 ^ bits) ≠ 0 := by
        intro hzero
        rw [hzero] at hbridge
        omega
      rw [if_neg hrem]
      exact nat_sub_of_eq_sub hbridge hmodnatlt

def repr (bits : Nat) (x : Z) : Word bits :=
  Word.mkint (zOfNat (residue bits x)) (repr_intrange bits x)

/-- Re-embed a finite residue into the source-shaped proof-carrying carrier. -/
def Word.ofFin {bits : Nat} (x : Fin (2 ^ bits)) : Word bits :=
  repr bits (zOfNat x.val)

@[simp] private theorem val_repr_residue (bits : Nat) (x : Z) :
    (repr bits x).val = residue bits x := by
  exact zToNat_zOfNat (residue bits x)

def unsigned {bits : Nat} (x : Word bits) : Z :=
  x.intval

private theorem val_repr (bits : Nat) (i : Int) :
    (repr bits (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt i)).val =
      Int.toNat (i % ((2 ^ bits : Nat) : Int)) := by
  rw [val_repr_residue, residue_zOfInt]

def signed {bits : Nat} (x : Word bits) : Z :=
  let modulus := zTwoPowerNat bits
  let half := zTwoPowerNat (bits - 1)
  let u := unsigned x
  zltSelect u half u (zSub u modulus)

def zero (bits : Nat) : Word bits := repr bits zZero
def one (bits : Nat) : Word bits := repr bits zOne
def mone (bits : Nat) : Word bits := repr bits (zOpp zOne)
def iwordsize (bits : Nat) : Word bits := repr bits (zOfNat bits)

def eq {bits : Nat} (x y : Word bits) : Bool := decide (x.intval = y.intval)
def lt {bits : Nat} (x y : Word bits) : Bool :=
  zltSelect (signed x) (signed y) true false
def ltu {bits : Nat} (x y : Word bits) : Bool :=
  zltSelect (unsigned x) (unsigned y) true false

def neg {bits : Nat} (x : Word bits) : Word bits :=
  repr bits (zOpp (unsigned x))
def add {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zAdd (unsigned x) (unsigned y))

private theorem add_val {bits : Nat} (x y : Word bits) :
    (add x y).val = (x.val + y.val) % (2 ^ bits) := by
  rw [add, val_repr_residue]
  simp only [unsigned]
  rw [intval_eq_zOfNat_val x, intval_eq_zOfNat_val y]
  simp only [zAdd, zOfNat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  have hadd :
      Int.ofNat x.val + Int.ofNat y.val = Int.ofNat (x.val + y.val) := by
    rfl
  rw [hadd]
  rw [residue_zOfNat]

private theorem add_val_int {bits : Nat} (x y : Word bits) :
    Int.ofNat (add x y).val =
      (Int.ofNat x.val + Int.ofNat y.val) % Int.ofNat (2 ^ bits) := by
  rw [add_val]
  simp only [Int.ofNat_eq_natCast, Int.natCast_emod, Int.natCast_add]

def sub {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zSub (unsigned x) (unsigned y))

private theorem sub_val {bits : Nat} (x y : Word bits) :
    (sub x y).val = (2 ^ bits - y.val + x.val) % (2 ^ bits) := by
  rw [sub, val_repr_residue]
  simp only [unsigned]
  rw [intval_eq_zOfNat_val x, intval_eq_zOfNat_val y]
  simp only [zSub, zOfNat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  rw [residue_zOfInt]
  have hmpos : (0 : Int) < ((2 ^ bits : Nat) : Int) :=
    Int.natCast_pos.mpr (Nat.two_pow_pos bits)
  have hnonneg :
      0 ≤ ((x.val : Int) - (y.val : Int)) % ((2 ^ bits : Nat) : Int) :=
    Int.emod_nonneg _ (Int.ne_of_gt hmpos)
  have hlt :
      ((x.val : Int) - (y.val : Int)) % ((2 ^ bits : Nat) : Int) <
        ((2 ^ bits : Nat) : Int) :=
    Int.emod_lt_of_pos _ hmpos
  apply Int.ofNat.inj
  simp only [Int.ofNat_eq_natCast]
  rw [Int.toNat_of_nonneg hnonneg, Int.natCast_emod]
  have hinside :
      (((2 ^ bits - y.val + x.val : Nat) : Int)) =
        ((x.val : Int) - (y.val : Int)) + ((2 ^ bits : Nat) : Int) := by
    rw [Int.natCast_add, Int.ofNat_sub (Nat.le_of_lt (val_lt y))]
    omega
  rw [hinside, Int.add_emod_right]

private theorem sub_val_int {bits : Nat} (x y : Word bits) :
    Int.ofNat (sub x y).val =
      (Int.ofNat x.val - Int.ofNat y.val) % Int.ofNat (2 ^ bits) := by
  rw [sub, val_repr_residue]
  simp only [unsigned]
  rw [intval_eq_zOfNat_val x, intval_eq_zOfNat_val y]
  simp only [zSub, zOfNat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  rw [residue_zOfInt]
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (Int.ne_of_gt (Int.natCast_pos.mpr (Nat.two_pow_pos bits)))

def mul {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zMul (unsigned x) (unsigned y))
def divs {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zQuot (signed x) (signed y))
def mods {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zSub (signed x) (zMul (zQuot (signed x) (signed y)) (signed y)))
def divu {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zDiv (unsigned x) (unsigned y))
def modu {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zMod (unsigned x) (unsigned y))

def negative {bits : Nat} (x : Word bits) : Word bits :=
  if lt x (zero bits) then one bits else zero bits

def add_carry {bits : Nat} (x y cin : Word bits) : Word bits :=
  let sum := zAdd (zAdd (unsigned x) (unsigned y)) (unsigned cin)
  zltSelect sum (zTwoPowerNat bits) (zero bits) (one bits)

def sub_overflow {bits : Nat} (x y bin : Word bits) : Word bits :=
  let difference := zSub (zSub (signed x) (signed y)) (signed bin)
  let halfModulus := zTwoPowerNat (bits - 1)
  let minSigned := zOpp halfModulus
  let maxSigned := zSub halfModulus zOne
  zltSelect difference minSigned (one bits)
    (zltSelect maxSigned difference (one bits) (zero bits))

def and {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zOfNat (Nat.land (natVal x) (natVal y)))
def or {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zOfNat (Nat.lor (natVal x) (natVal y)))
def xor {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zOfNat (Nat.xor (natVal x) (natVal y)))
def not {bits : Nat} (x : Word bits) : Word bits :=
  repr bits (zOfNat (Nat.xor (natVal x) (2 ^ bits - 1)))

def shl {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zShiftl (unsigned x) (unsigned y))
def shru {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zShiftr (unsigned x) (unsigned y))
def shr {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zShiftr (signed x) (unsigned y))

def rol {bits : Nat} (x y : Word bits) : Word bits :=
  let amount := if bits = 0 then 0 else natVal y % bits
  repr bits (zOfNat
    (Nat.lor (Nat.shiftLeft (natVal x) amount)
      (Nat.shiftRight (natVal x) (bits - amount))))

def ror {bits : Nat} (x y : Word bits) : Word bits :=
  let amount := if bits = 0 then 0 else natVal y % bits
  repr bits (zOfNat
    (Nat.lor (Nat.shiftRight (natVal x) amount)
      (Nat.shiftLeft (natVal x) (bits - amount))))

def shrx {bits : Nat} (x y : Word bits) : Word bits :=
  divs x (shl (one bits) y)

def zero_ext {bits : Nat} (n : Z) (x : Word bits) : Word bits :=
  repr bits (zMod (unsigned x) (zTwoP n))

def sign_ext {bits : Nat} (n : Z) (x : Word bits) : Word bits :=
  let modulus := zTwoP n
  let residue := zMod (unsigned x) modulus
  if zLtb residue (zTwoP (zSub n zOne)) then
    repr bits residue
  else
    repr bits (zSub residue modulus)

def testbit {bits : Nat} (x : Word bits) : Z → Bool
  | .Zneg _ => false
  | .Z0 => Nat.testBit (natVal x) 0
  | .Zpos p => Nat.testBit (natVal x) (positiveToNat p)

def eqm (bits : Nat) (x y : Z) : Prop :=
  CompCert4Lean.Lib.Zbits.eqmod (zTwoPowerNat bits) x y

/--
The concrete member correspondence for a source application of `Make`.
Its dependent carrier fields retain the generated constructor, projections,
and exact `intrange` proposition; the remaining fields identify the selected
executable surface shared by the four owned applications.
-/
structure GeneratedApplication where
  wordsize : Nat
  modulus : Z
  int : Type
  mkint : (intval : Z) →
    zLt (zOpp zOne) intval ∧ zLt intval (zTwoPowerNat wordsize) → int
  intval : int → Z
  intrange : ∀ x : int,
    zLt (zOpp zOne) (intval x) ∧ zLt (intval x) (zTwoPowerNat wordsize)
  repr : Z → int
  unsigned : int → Z
  signed : int → Z
  zero : int
  one : int
  eq : int → int → Bool
  lt : int → int → Bool
  ltu : int → int → Bool
  neg : int → int
  add : int → int → int
  sub : int → int → int
  mul : int → int → int
  divs : int → int → int
  divu : int → int → int
  and : int → int → int
  or : int → int → int
  xor : int → int → int
  shl : int → int → int
  shru : int → int → int
  shr : int → int → int
  zero_ext : Z → int → int
  sign_ext : Z → int → int

def makeGeneratedApplication (bits : Nat) : GeneratedApplication where
  wordsize := bits
  modulus := zTwoPowerNat bits
  int := Word bits
  mkint := fun intval intrange => Word.mkint intval intrange
  intval := Word.intval
  intrange := Word.intrange
  repr := repr bits
  unsigned := unsigned
  signed := signed
  zero := zero bits
  one := one bits
  eq := eq
  lt := lt
  ltu := ltu
  neg := neg
  add := add
  sub := sub
  mul := mul
  divs := divs
  divu := divu
  and := and
  or := or
  xor := xor
  shl := shl
  shru := shru
  shr := shr
  zero_ext := zero_ext
  sign_ext := sign_ext

end WordCore

namespace Int

def wordsize : Nat := 32
def zwordsize : Z := zOfNat wordsize
def modulus : Z := zTwoPowerNat wordsize
def half_modulus : Z := zTwoPowerNat (wordsize - 1)
def max_unsigned : Z := zSub modulus zOne
def max_signed : Z := zSub half_modulus zOne
def min_signed : Z := zOpp half_modulus

abbrev int := WordCore.Word wordsize

def repr (x : Z) : int := WordCore.repr wordsize x
def ofFin (x : Fin (2 ^ wordsize)) : int := WordCore.Word.ofFin x
def toFin (x : int) : Fin (2 ^ wordsize) := x.toFin
def unsigned (x : int) : Z := WordCore.unsigned x
def signed (x : int) : Z := WordCore.signed x
def zero : int := WordCore.zero wordsize
def one : int := WordCore.one wordsize
def mone : int := WordCore.mone wordsize
def iwordsize : int := WordCore.iwordsize wordsize
def eq : int → int → Bool := WordCore.eq
def eq_dec (x y : int) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) :=
  if h : x = y then .left h else .right h
def lt : int → int → Bool := WordCore.lt
def ltu : int → int → Bool := WordCore.ltu
def neg : int → int := WordCore.neg
def add : int → int → int := WordCore.add
def sub : int → int → int := WordCore.sub
def mul : int → int → int := WordCore.mul
def mulhs (x y : int) : int :=
  repr (zDiv (zMul (signed x) (signed y)) modulus)
def mulhu (x y : int) : int :=
  repr (zDiv (zMul (unsigned x) (unsigned y)) modulus)
def divs : int → int → int := WordCore.divs
def mods : int → int → int := WordCore.mods
def divu : int → int → int := WordCore.divu
def modu : int → int → int := WordCore.modu
def negative : int → int := WordCore.negative
def add_carry : int → int → int → int := WordCore.add_carry
def sub_overflow : int → int → int → int := WordCore.sub_overflow
def and : int → int → int := WordCore.and
def or : int → int → int := WordCore.or
def xor : int → int → int := WordCore.xor
def not : int → int := WordCore.not
def shl : int → int → int := WordCore.shl
def shru : int → int → int := WordCore.shru
def shr : int → int → int := WordCore.shr
def sign_ext (n : Z) (x : int) : int := WordCore.sign_ext n x
def rol : int → int → int := WordCore.rol
def ror : int → int → int := WordCore.ror
def shrx : int → int → int := WordCore.shrx
def testbit : int → Z → Bool := WordCore.testbit
def eqm : Z → Z → Prop := WordCore.eqm wordsize

def is_power2 (x : int) : Option int :=
  match CompCert4Lean.Lib.Zbits.Z_is_power2 (unsigned x) with
  | some i => some (repr i)
  | none => none

def zero_ext (n : Z) (x : int) : int :=
  WordCore.zero_ext n x

def one_bits (x : int) : List int :=
  List.map repr
    (CompCert4Lean.Lib.Zbits.Z_one_bits wordsize (unsigned x) zZero)

def cmp (c : comparison) (x y : int) : Bool :=
  match c with
  | .Ceq => eq x y
  | .Cne => !(eq x y)
  | .Clt => lt x y
  | .Cle => !(lt y x)
  | .Cgt => lt y x
  | .Cge => !(lt x y)

def cmpu (c : comparison) (x y : int) : Bool :=
  match c with
  | .Ceq => eq x y
  | .Cne => !(eq x y)
  | .Clt => ltu x y
  | .Cle => !(ltu y x)
  | .Cgt => ltu y x
  | .Cge => !(ltu x y)

/-! Selected generated members of `Make(Wordsize_32)` retain their exact
    source propositions here; proof discharge remains a later phase. -/
def add_unsigned : Prop :=
  ∀ x y : int, add x y = repr (zAdd (unsigned x) (unsigned y))

def bits_above : Prop :=
  ∀ (x : int) (i : Z), zLe zwordsize i → testbit x i = false

def bits_and : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (and x y) i = (testbit x i && testbit y i)

def bits_or : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (or x y) i = (testbit x i || testbit y i)

def bits_shl : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (shl x y) i =
      zltSelect i (unsigned y) false (testbit x (zSub i (unsigned y)))

def bits_shr : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (shr x y) i =
      testbit x (zltSelect (zAdd i (unsigned y)) zwordsize
        (zAdd i (unsigned y)) (zSub zwordsize zOne))

def bits_shru : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (shru x y) i =
      zltSelect (zAdd i (unsigned y)) zwordsize
        (testbit x (zAdd i (unsigned y))) false

def bits_xor : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (xor x y) i = Bool.xor (testbit x i) (testbit y i)

def bits_zero : Prop := ∀ i : Z, testbit zero i = false

def eq_signed : Prop :=
  ∀ x y : int,
    eq x y = sumboolSelect (CompCert4Lean.Lib.Coqlib.zeq (signed x) (signed y))
      true false

def eq_sym : Prop := ∀ x y : int, eq x y = eq y x

def eqm_add : Prop :=
  ∀ a b c d : Z, eqm a b → eqm c d → eqm (zAdd a c) (zAdd b d)

def eqm_refl : Prop := ∀ x : Z, eqm x x

def eqm_signed_unsigned : Prop :=
  ∀ x : int, eqm (signed x) (unsigned x)

def eqm_sym : Prop := ∀ x y : Z, eqm x y → eqm y x

def eqm_unsigned_repr : Prop :=
  ∀ z : Z, eqm z (unsigned (repr z))

def eqm_unsigned_repr_l : Prop :=
  ∀ a b : Z, eqm a b → eqm (unsigned (repr a)) b

def ltu_inv : Prop :=
  ∀ x y : int, ltu x y = true →
    zLe zZero (unsigned x) ∧ zLt (unsigned x) (unsigned y)

def modulus_pos : Prop := zLt zZero modulus

def repr_unsigned : Prop := ∀ i : int, repr (unsigned i) = i

def same_bits_eq : Prop :=
  ∀ x y : int,
    (∀ i : Z, zLe zZero i ∧ zLt i zwordsize → testbit x i = testbit y i) →
      x = y

def signed_range : Prop :=
  ∀ i : int, zLe min_signed (signed i) ∧ zLe (signed i) max_signed

def testbit_repr : Prop :=
  ∀ x i : Z, zLe zZero i ∧ zLt i zwordsize →
    testbit (repr x) i = zTestbit x i

def unsigned_range : Prop :=
  ∀ i : int, zLe zZero (unsigned i) ∧ zLt (unsigned i) modulus

def unsigned_range_2 : Prop :=
  ∀ i : int, zLe zZero (unsigned i) ∧ zLe (unsigned i) max_unsigned

def unsigned_repr : Prop :=
  ∀ z : Z, zLe zZero z ∧ zLe z max_unsigned → unsigned (repr z) = z

def unsigned_repr_eq : Prop :=
  ∀ x : Z, unsigned (repr x) = zMod x modulus

def unsigned_repr_wordsize : Prop := unsigned iwordsize = zwordsize

def wordsize_max_unsigned : Prop := zLe zwordsize max_unsigned

private theorem zero_ext_modulo (n : Z) (x : int) (hn : zLe zZero n) :
    ZArith.BinInt.Z.modulo (unsigned x) (two_p n) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (Int.ofNat (x.val % (2 ^ zToNat n))) := by
  change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n at hn
  let p : Nat := 2 ^ zToNat n
  let r : Nat := x.val % p
  let q : Nat := x.val / p
  have hp : 0 < p := Nat.two_pow_pos _
  have htwo :
      two_p n = CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat p) := by
    cases n with
    | Z0 => rfl
    | Zpos exponent =>
        have hexp : ¬(Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat exponent) < 0) :=
          Int.not_lt.mpr (Int.natCast_nonneg _)
        simp only [p, zToNat, two_p, ZArith.Zpower.two_p, ZArith.BinInt.Z.pow,
          ZArith.BinInt.Z.to_nat,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat, hexp, if_false]
        apply congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        change (2 : Int) ^
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat exponent =
          (2 : Int) ^ CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat exponent
        rfl
    | Zneg exponent =>
        have := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive exponent
        simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at hn
        omega
  have hdecomp :
      unsigned x =
        ZArith.BinInt.Z.add
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat r))
            (ZArith.BinInt.Z.mul
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat q))
            (two_p n)) := by
    change x.intval = _
    rw [WordCore.intval_eq_zOfNat_val x]
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [unsigned, WordCore.unsigned, zOfNat,
      ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt, htwo]
    have hnat : x.val = r + q * p := by
      simpa [r, q, Nat.mul_comm] using (Nat.mod_add_div x.val p).symm
    change Int.ofNat x.val = Int.ofNat (r + q * p)
    exact congrArg Int.ofNat hnat
  have hrange :
      zLe zZero (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat r)) ∧
        zLt (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat r)) (two_p n) := by
    constructor
    · change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat r))
      rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      exact Int.natCast_nonneg r
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat r)) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (two_p n)
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt, htwo]
      exact Int.ofNat_lt.mpr (Nat.mod_lt _ hp)
  rw [hdecomp]
  rw [ZArith.BinInt.Z.modulo_add_mul]
  exact ZArith.BinInt.Z.mod_small _ _ hrange

private theorem zero_ext_val (n : Z) (x : int) (hn : zLe zZero n) :
    (zero_ext n x).val =
      (x.val % (2 ^ zToNat n)) % (2 ^ wordsize) := by
  unfold zero_ext WordCore.zero_ext
  change (repr (ZArith.BinInt.Z.modulo (unsigned x) (two_p n))).val =
    (x.val % (2 ^ zToNat n)) % (2 ^ wordsize)
  rw [zero_ext_modulo n x hn]
  simp only [repr]
  rw [WordCore.val_repr]
  change Int.toNat
      (Int.ofNat (x.val % (2 ^ zToNat n)) % ((2 ^ wordsize : Nat) : Int)) =
        (x.val % (2 ^ zToNat n)) % (2 ^ wordsize)
  have hbridge := Int.emod_natAbs_of_nonneg
    (x := ((x.val % (2 ^ zToNat n) : Nat) : Int)) (n := 2 ^ wordsize)
    (Int.natCast_nonneg _)
  simp only [Int.natAbs_natCast] at hbridge
  simp only [Int.ofNat_eq_natCast]
  rw [← hbridge]

private theorem nested_power_mod_idem (a k w : Nat) :
    ((((a % (2 ^ k)) % (2 ^ w)) % (2 ^ k)) % (2 ^ w)) =
      (a % (2 ^ k)) % (2 ^ w) := by
  by_cases hkw : k ≤ w
  · have hpLe : 2 ^ k ≤ 2 ^ w :=
      Nat.pow_le_pow_right Nat.zero_lt_two hkw
    have haLt : a % (2 ^ k) < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
    have haLtW : a % (2 ^ k) < 2 ^ w := Nat.lt_of_lt_of_le haLt hpLe
    rw [Nat.mod_eq_of_lt haLtW, Nat.mod_mod, Nat.mod_eq_of_lt haLtW]
  · have hwk : w ≤ k := Nat.le_of_not_ge hkw
    have hpLe : 2 ^ w ≤ 2 ^ k :=
      Nat.pow_le_pow_right Nat.zero_lt_two hwk
    have haLt : (a % (2 ^ k)) % (2 ^ w) < 2 ^ w :=
      Nat.mod_lt _ (Nat.two_pow_pos w)
    have haLtK : (a % (2 ^ k)) % (2 ^ w) < 2 ^ k :=
      Nat.lt_of_lt_of_le haLt hpLe
    rw [Nat.mod_eq_of_lt haLtK, Nat.mod_mod]

theorem zero_ext_idem_proof_api (n : Z) (x : int) (hn : zLe zZero n) :
    zero_ext n (zero_ext n x) = zero_ext n x := by
  apply WordCore.ext_of_val_eq
  rw [zero_ext_val n (zero_ext n x) hn, zero_ext_val n x hn]
  exact nested_power_mod_idem x.val (zToNat n) wordsize

/-- `GENAPP-COMPCERT-LIB-INTEGERS-3562-ASSIGNMENT`: `Make(Wordsize_32)`. -/
def generatedApplication : WordCore.GeneratedApplication :=
  WordCore.makeGeneratedApplication wordsize

theorem generatedApplication_zero_ext_idem
    (n : Z) (x : generatedApplication.int) (hn : zLe zZero n) :
    generatedApplication.zero_ext n (generatedApplication.zero_ext n x) =
      generatedApplication.zero_ext n x := by
  change zero_ext n (zero_ext n x) = zero_ext n x
  exact zero_ext_idem_proof_api n x hn

end Int

namespace Byte

def wordsize : Nat := 8
abbrev int := WordCore.Word wordsize
def repr (x : Z) : int := WordCore.repr wordsize x

/-- `GENAPP-COMPCERT-LIB-INTEGERS-3582-ASSIGNMENT`: `Make(Wordsize_8)`. -/
def generatedApplication : WordCore.GeneratedApplication :=
  WordCore.makeGeneratedApplication wordsize

end Byte

abbrev int := Int.int
abbrev byte := Byte.int

def int_wordsize_divides_modulusStatement : Prop :=
  zDivide (zOfNat Int.wordsize) Int.modulus

namespace Int64

def wordsize : Nat := 64
def zwordsize : Z := zOfNat wordsize
def modulus : Z := zTwoPowerNat wordsize
def half_modulus : Z := zTwoPowerNat (wordsize - 1)
def max_unsigned : Z := zSub modulus zOne
def max_signed : Z := zSub half_modulus zOne
def min_signed : Z := zOpp half_modulus

abbrev int := WordCore.Word wordsize

def repr (x : Z) : int := WordCore.repr wordsize x
def ofFin (x : Fin (2 ^ wordsize)) : int := WordCore.Word.ofFin x
def toFin (x : int) : Fin (2 ^ wordsize) := x.toFin
def unsigned (x : int) : Z := WordCore.unsigned x
def signed (x : int) : Z := WordCore.signed x
def zero : int := WordCore.zero wordsize
def one : int := WordCore.one wordsize
def mone : int := WordCore.mone wordsize
def iwordsize : int := WordCore.iwordsize wordsize
def eq : int → int → Bool := WordCore.eq
def lt : int → int → Bool := WordCore.lt
def ltu : int → int → Bool := WordCore.ltu
def neg : int → int := WordCore.neg
def add : int → int → int := WordCore.add
def sub : int → int → int := WordCore.sub
def mul : int → int → int := WordCore.mul
def mulhs (x y : int) : int :=
  repr (zDiv (zMul (signed x) (signed y)) modulus)
def mulhu (x y : int) : int :=
  repr (zDiv (zMul (unsigned x) (unsigned y)) modulus)
def divs : int → int → int := WordCore.divs
def mods : int → int → int := WordCore.mods
def divu : int → int → int := WordCore.divu
def modu : int → int → int := WordCore.modu
def negative : int → int := WordCore.negative
def add_carry : int → int → int → int := WordCore.add_carry
def sub_overflow : int → int → int → int := WordCore.sub_overflow
def and : int → int → int := WordCore.and
def or : int → int → int := WordCore.or
def xor : int → int → int := WordCore.xor
def not : int → int := WordCore.not
def shl : int → int → int := WordCore.shl
def shru : int → int → int := WordCore.shru
def shr : int → int → int := WordCore.shr
def sign_ext (n : Z) (x : int) : int := WordCore.sign_ext n x
def rol : int → int → int := WordCore.rol
def ror : int → int → int := WordCore.ror
def shrx : int → int → int := WordCore.shrx
def testbit : int → Z → Bool := WordCore.testbit
def eqm : Z → Z → Prop := WordCore.eqm wordsize

def is_power2 (x : int) : Option int :=
  match CompCert4Lean.Lib.Zbits.Z_is_power2 (unsigned x) with
  | some i => some (repr i)
  | none => none

def iwordsize' : Int.int := Int.repr zwordsize

def shl' (x : int) (y : Int.int) : int :=
  repr (zShiftl (unsigned x) (Int.unsigned y))

def shru' (x : int) (y : Int.int) : int :=
  repr (zShiftr (unsigned x) (Int.unsigned y))

def shr' (x : int) (y : Int.int) : int :=
  repr (zShiftr (signed x) (Int.unsigned y))

def rol' (x : int) (y : Int.int) : int :=
  rol x (repr (Int.unsigned y))

def ror' (x : int) (y : Int.int) : int :=
  ror x (repr (Int.unsigned y))

def shrx' (x : int) (y : Int.int) : int :=
  divs x (shl' one y)

def one_bits' (x : int) : List Int.int :=
  List.map Int.repr (CompCert4Lean.Lib.Zbits.Z_one_bits wordsize (unsigned x) zZero)

def is_power2' (x : int) : Option Int.int :=
  match CompCert4Lean.Lib.Zbits.Z_one_bits wordsize (unsigned x) zZero with
  | [i] => some (Int.repr i)
  | _ => none

def int_of_one_bits' : List Int.int → int
  | [] => zero
  | a :: rest => add (shl' one a) (int_of_one_bits' rest)

def loword (n : int) : Int.int :=
  Int.repr (unsigned n)

def hiword (n : int) : Int.int :=
  Int.repr (unsigned (shru n (repr Int.zwordsize)))

def ofwords (hi lo : Int.int) : int :=
  or (shl (repr (Int.unsigned hi)) (repr Int.zwordsize))
    (repr (Int.unsigned lo))

def mul' (x y : Int.int) : int :=
  repr (zMul (Int.unsigned x) (Int.unsigned y))

/-! Selected generated members of `Include Make(Wordsize_64)` retain their
    exact source propositions; proof discharge remains a later phase. -/
def bits_above : Prop :=
  ∀ (x : int) (i : Z), zLe zwordsize i → testbit x i = false

def bits_and : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (and x y) i = (testbit x i && testbit y i)

def bits_or : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (or x y) i = (testbit x i || testbit y i)

def bits_shl : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (shl x y) i =
      zltSelect i (unsigned y) false (testbit x (zSub i (unsigned y)))

def bits_shru : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (shru x y) i =
      zltSelect (zAdd i (unsigned y)) zwordsize
        (testbit x (zAdd i (unsigned y))) false

def bits_signed : Prop :=
  ∀ (x : int) (i : Z), zLe zZero i →
    zTestbit (signed x) i =
      testbit x (zltSelect i zwordsize i (zSub zwordsize zOne))

def bits_xor : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (xor x y) i = Bool.xor (testbit x i) (testbit y i)

def eqm_add : Prop :=
  ∀ a b c d : Z, eqm a b → eqm c d → eqm (zAdd a c) (zAdd b d)

def eqm_mult : Prop :=
  ∀ a b c d : Z, eqm a c → eqm b d → eqm (zMul a b) (zMul c d)

def eqm_refl : Prop := ∀ x : Z, eqm x x

def eqm_samerepr : Prop :=
  ∀ x y : Z, eqm x y → repr x = repr y

def eqm_sym : Prop := ∀ x y : Z, eqm x y → eqm y x

def eqm_unsigned_repr : Prop :=
  ∀ z : Z, eqm z (unsigned (repr z))

def eqm_unsigned_repr_l : Prop :=
  ∀ a b : Z, eqm a b → eqm (unsigned (repr a)) b

def mul_commut : Prop := ∀ x y : int, mul x y = mul y x

def mul_one : Prop := ∀ x : int, mul x one = x

def or_ror : Prop :=
  ∀ x y z : int, ltu y iwordsize = true → ltu z iwordsize = true →
    add y z = iwordsize → ror x z = or (shl x y) (shru x z)

def repr_unsigned : Prop := ∀ i : int, repr (unsigned i) = i

def same_bits_eq : Prop :=
  ∀ x y : int,
    (∀ i : Z, zLe zZero i ∧ zLt i zwordsize → testbit x i = testbit y i) →
      x = y

def shifted_or_is_add : Prop :=
  ∀ (x y : int) (n : Z), zLe zZero n ∧ zLt n zwordsize →
    zLt (unsigned y) (zTwoP n) →
      or (shl x (repr n)) y =
        repr (zAdd (zMul (unsigned x) (zTwoP n)) (unsigned y))

def shl_shl : Prop :=
  ∀ x y z : int, ltu y iwordsize = true → ltu z iwordsize = true →
    ltu (add y z) iwordsize = true → shl (shl x y) z = shl x (add y z)

def shr_shr : Prop :=
  ∀ x y z : int, ltu y iwordsize = true → ltu z iwordsize = true →
    ltu (add y z) iwordsize = true → shr (shr x y) z = shr x (add y z)

def shru_shru : Prop :=
  ∀ x y z : int, ltu y iwordsize = true → ltu z iwordsize = true →
    ltu (add y z) iwordsize = true → shru (shru x y) z = shru x (add y z)

def shrx_shr_2 : Prop :=
  ∀ x y : int,
    ltu y (repr (zSub zwordsize zOne)) = true →
      shrx x y =
        shr (add x (shru (shr x (repr (zSub zwordsize zOne)))
          (sub iwordsize y))) y

def shrx_zero : Prop :=
  ∀ x : int, zLt zOne zwordsize → shrx x zero = x

def signed_repr : Prop :=
  ∀ z : Z, zLe min_signed z ∧ zLe z max_signed → signed (repr z) = z

def testbit_repr : Prop :=
  ∀ x i : Z, zLe zZero i ∧ zLt i zwordsize →
    testbit (repr x) i = zTestbit x i

def unsigned_range : Prop :=
  ∀ i : int, zLe zZero (unsigned i) ∧ zLt (unsigned i) modulus

def unsigned_repr : Prop :=
  ∀ z : Z, zLe zZero z ∧ zLe z max_unsigned → unsigned (repr z) = z

def unsigned_repr_eq : Prop :=
  ∀ x : Z, unsigned (repr x) = zMod x modulus

/-! ## Exact statement descriptors for the deferred Int64 proofs -/

def bits_shl'Statement : Prop :=
  ∀ (x : int) (y : Int.int) (i : Z),
    zLe zZero i ∧ zLt i zwordsize →
      testbit (shl' x y) i =
        zltSelect i (Int.unsigned y) false
          (testbit x (zSub i (Int.unsigned y)))

def bits_shru'Statement : Prop :=
  ∀ (x : int) (y : Int.int) (i : Z),
    zLe zZero i ∧ zLt i zwordsize →
      testbit (shru' x y) i =
        zltSelect (zAdd i (Int.unsigned y)) zwordsize
          (testbit x (zAdd i (Int.unsigned y))) false

def bits_shr'Statement : Prop :=
  ∀ (x : int) (y : Int.int) (i : Z),
    zLe zZero i ∧ zLt i zwordsize →
      testbit (shr' x y) i =
        testbit x
          (zltSelect (zAdd i (Int.unsigned y)) zwordsize
            (zAdd i (Int.unsigned y)) (zSub zwordsize zOne))

def shl'_mul_two_pStatement : Prop :=
  ∀ (x : int) (y : Int.int),
    shl' x y = mul x (repr (zTwoP (Int.unsigned y)))

def shl'_one_two_pStatement : Prop :=
  ∀ y : Int.int, shl' one y = repr (zTwoP (Int.unsigned y))

def shl'_mulStatement : Prop :=
  ∀ (x : int) (y : Int.int), shl' x y = mul x (shl' one y)

def shrx'_zeroStatement : Prop :=
  ∀ x : int, shrx' x Int.zero = x

def shrx'_shr_2Statement : Prop :=
  ∀ (x : int) (y : Int.int),
    Int.ltu y (Int.repr (zOfNat 63)) = true →
      shrx' x y =
        shr'
          (add x
            (shru' (shr' x (Int.repr (zOfNat 63)))
              (Int.sub (Int.repr (zOfNat 64)) y))) y

def int_ltu_2_invStatement : Prop :=
  ∀ y z : Int.int,
    Int.ltu y iwordsize' = true →
    Int.ltu z iwordsize' = true →
    zLe (Int.unsigned (Int.add y z)) (Int.unsigned iwordsize') →
      let y' := repr (Int.unsigned y)
      let z' := repr (Int.unsigned z)
      Int.unsigned y = unsigned y' ∧
      Int.unsigned z = unsigned z' ∧
      ltu y' iwordsize = true ∧
      ltu z' iwordsize = true ∧
      Int.unsigned (Int.add y z) = unsigned (add y' z') ∧
      add y' z' = repr (Int.unsigned (Int.add y z))

def or_ror'Statement : Prop :=
  ∀ (x : int) (y z : Int.int),
    Int.ltu y iwordsize' = true →
    Int.ltu z iwordsize' = true →
    Int.add y z = iwordsize' →
      ror x (repr (Int.unsigned z)) = or (shl' x y) (shru' x z)

def shl'_shl'Statement : Prop :=
  ∀ (x : int) (y z : Int.int),
    Int.ltu y iwordsize' = true →
    Int.ltu z iwordsize' = true →
    Int.ltu (Int.add y z) iwordsize' = true →
      shl' (shl' x y) z = shl' x (Int.add y z)

def shru'_shru'Statement : Prop :=
  ∀ (x : int) (y z : Int.int),
    Int.ltu y iwordsize' = true →
    Int.ltu z iwordsize' = true →
    Int.ltu (Int.add y z) iwordsize' = true →
      shru' (shru' x y) z = shru' x (Int.add y z)

def shr'_shr'Statement : Prop :=
  ∀ (x : int) (y z : Int.int),
    Int.ltu y iwordsize' = true →
    Int.ltu z iwordsize' = true →
    Int.ltu (Int.add y z) iwordsize' = true →
      shr' (shr' x y) z = shr' x (Int.add y z)

def one_bits'_rangeStatement : Prop :=
  ∀ (x : int) (i : Int.int),
    i ∈ one_bits' x → Int.ltu i iwordsize' = true

def one_bits'_decompStatement : Prop :=
  ∀ x : int, x = int_of_one_bits' (one_bits' x)

def is_power2'_rngStatement : Prop :=
  ∀ (n : int) (logn : Int.int),
    is_power2' n = some logn →
      zLe zZero (Int.unsigned logn) ∧ zLt (Int.unsigned logn) zwordsize

def is_power2'_rangeStatement : Prop :=
  ∀ (n : int) (logn : Int.int),
    is_power2' n = some logn → Int.ltu logn iwordsize' = true

def is_power2'_correctStatement : Prop :=
  ∀ (n : int) (logn : Int.int),
    is_power2' n = some logn →
      unsigned n = zTwoP (Int.unsigned logn)

def mul_pow2'Statement : Prop :=
  ∀ (x n : int) (logn : Int.int),
    is_power2' n = some logn → mul x n = shl' x logn

def divu_pow2'Statement : Prop :=
  ∀ (x n : int) (logn : Int.int),
    is_power2' n = some logn → divu x n = shru' x logn

def bits_lowordStatement : Prop :=
  ∀ (n : int) (i : Z),
    zLe zZero i ∧ zLt i Int.zwordsize →
      Int.testbit (loword n) i = testbit n i

def bits_hiwordStatement : Prop :=
  ∀ (n : int) (i : Z),
    zLe zZero i ∧ zLt i Int.zwordsize →
      Int.testbit (hiword n) i = testbit n (zAdd i Int.zwordsize)

def bits_ofwordsStatement : Prop :=
  ∀ (hi lo : Int.int) (i : Z),
    zLe zZero i ∧ zLt i zwordsize →
      testbit (ofwords hi lo) i =
        zltSelect i Int.zwordsize (Int.testbit lo i)
          (Int.testbit hi (zSub i Int.zwordsize))

def lo_ofwordsStatement : Prop :=
  ∀ hi lo : Int.int, loword (ofwords hi lo) = lo

def hi_ofwordsStatement : Prop :=
  ∀ hi lo : Int.int, hiword (ofwords hi lo) = hi

def ofwords_recomposeStatement : Prop :=
  ∀ n : int, ofwords (hiword n) (loword n) = n

def ofwords_addStatement : Prop :=
  ∀ lo hi : Int.int,
    ofwords hi lo =
      repr (zAdd (zMul (Int.unsigned hi) (zTwoP (zOfNat 32)))
        (Int.unsigned lo))

def ofwords_add'Statement : Prop :=
  ∀ lo hi : Int.int,
    unsigned (ofwords hi lo) =
      zAdd (zMul (Int.unsigned hi) (zTwoP (zOfNat 32)))
        (Int.unsigned lo)

def eqm_mul_2p32Statement : Prop :=
  ∀ x y : Z,
    Int.eqm x y →
      eqm (zMul x (zTwoP (zOfNat 32))) (zMul y (zTwoP (zOfNat 32)))

def ofwords_add''Statement : Prop :=
  ∀ lo hi : Int.int,
    signed (ofwords hi lo) =
      zAdd (zMul (Int.signed hi) (zTwoP (zOfNat 32)))
        (Int.unsigned lo)

def decompose_bitwise_binopStatement : Prop :=
  ∀ (f : Bool → Bool → Bool)
    (f64 : int → int → int) (f32 : Int.int → Int.int → Int.int)
    (xh xl yh yl : Int.int),
    (∀ (x y : int) (i : Z),
      zLe zZero i ∧ zLt i zwordsize →
        testbit (f64 x y) i = f (testbit x i) (testbit y i)) →
    (∀ (x y : Int.int) (i : Z),
      zLe zZero i ∧ zLt i Int.zwordsize →
        Int.testbit (f32 x y) i = f (Int.testbit x i) (Int.testbit y i)) →
      f64 (ofwords xh xl) (ofwords yh yl) =
        ofwords (f32 xh yh) (f32 xl yl)

def decompose_andStatement : Prop :=
  ∀ xh xl yh yl : Int.int,
    and (ofwords xh xl) (ofwords yh yl) =
      ofwords (Int.and xh yh) (Int.and xl yl)

def decompose_orStatement : Prop :=
  ∀ xh xl yh yl : Int.int,
    or (ofwords xh xl) (ofwords yh yl) =
      ofwords (Int.or xh yh) (Int.or xl yl)

def decompose_xorStatement : Prop :=
  ∀ xh xl yh yl : Int.int,
    xor (ofwords xh xl) (ofwords yh yl) =
      ofwords (Int.xor xh yh) (Int.xor xl yl)

def decompose_shl_1Statement : Prop :=
  ∀ xh xl y : Int.int,
    zLe zZero (Int.unsigned y) ∧ zLt (Int.unsigned y) Int.zwordsize →
      shl' (ofwords xh xl) y =
        ofwords
          (Int.or (Int.shl xh y)
            (Int.shru xl (Int.sub Int.iwordsize y)))
          (Int.shl xl y)

def decompose_shl_2Statement : Prop :=
  ∀ xh xl y : Int.int,
    zLe Int.zwordsize (Int.unsigned y) ∧ zLt (Int.unsigned y) zwordsize →
      shl' (ofwords xh xl) y =
        ofwords (Int.shl xl (Int.sub y Int.iwordsize)) Int.zero

def decompose_shru_1Statement : Prop :=
  ∀ xh xl y : Int.int,
    zLe zZero (Int.unsigned y) ∧ zLt (Int.unsigned y) Int.zwordsize →
      shru' (ofwords xh xl) y =
        ofwords (Int.shru xh y)
          (Int.or (Int.shru xl y)
            (Int.shl xh (Int.sub Int.iwordsize y)))

def decompose_shru_2Statement : Prop :=
  ∀ xh xl y : Int.int,
    zLe Int.zwordsize (Int.unsigned y) ∧ zLt (Int.unsigned y) zwordsize →
      shru' (ofwords xh xl) y =
        ofwords Int.zero (Int.shru xh (Int.sub y Int.iwordsize))

def decompose_shr_1Statement : Prop :=
  ∀ xh xl y : Int.int,
    zLe zZero (Int.unsigned y) ∧ zLt (Int.unsigned y) Int.zwordsize →
      shr' (ofwords xh xl) y =
        ofwords (Int.shr xh y)
          (Int.or (Int.shru xl y)
            (Int.shl xh (Int.sub Int.iwordsize y)))

def decompose_shr_2Statement : Prop :=
  ∀ xh xl y : Int.int,
    zLe Int.zwordsize (Int.unsigned y) ∧ zLt (Int.unsigned y) zwordsize →
      shr' (ofwords xh xl) y =
        ofwords (Int.shr xh (Int.sub Int.iwordsize Int.one))
          (Int.shr xh (Int.sub y Int.iwordsize))

def decompose_mulStatement : Prop :=
  ∀ xh xl yh yl : Int.int,
    mul (ofwords xh xl) (ofwords yh yl) =
      ofwords
        (Int.add
          (Int.add (hiword (mul' xl yl)) (Int.mul xl yh))
          (Int.mul xh yl))
        (loword (mul' xl yl))

def decompose_ltuStatement : Prop :=
  ∀ xh xl yh yl : Int.int,
    ltu (ofwords xh xl) (ofwords yh yl) =
      (if Int.eq xh yh then Int.ltu xl yl else Int.ltu xh yh)

def decompose_leuStatement : Prop :=
  ∀ xh xl yh yl : Int.int,
    (! (ltu (ofwords yh yl) (ofwords xh xl))) =
      (if Int.eq xh yh then !(Int.ltu yl xl) else Int.ltu xh yh)

def decompose_ltStatement : Prop :=
  ∀ xh xl yh yl : Int.int,
    lt (ofwords xh xl) (ofwords yh yl) =
      (if Int.eq xh yh then Int.ltu xl yl else Int.lt xh yh)

def decompose_leStatement : Prop :=
  ∀ xh xl yh yl : Int.int,
    (! (lt (ofwords yh yl) (ofwords xh xl))) =
      (if Int.eq xh yh then !(Int.ltu yl xl) else Int.lt xh yh)

/-- `GENAPP-COMPCERT-LIB-INTEGERS-3598-INCLUDE`: `Include Make(Wordsize_64)`. -/
def generatedApplication : WordCore.GeneratedApplication :=
  WordCore.makeGeneratedApplication wordsize

end Int64

abbrev int64 := Int64.int

namespace Wordsize_Ptrofs

def wordsize : Nat :=
  if CompCert4Lean.X86_64.Archi.ptr64 then 64 else 32

end Wordsize_Ptrofs

namespace Ptrofs

def wordsize : Nat := Wordsize_Ptrofs.wordsize
def zwordsize : Z := zOfNat wordsize
def modulus : Z := zTwoPowerNat wordsize
def half_modulus : Z := zTwoPowerNat (wordsize - 1)
def max_unsigned : Z := zSub modulus zOne
def max_signed : Z := zSub half_modulus zOne
def min_signed : Z := zOpp half_modulus

abbrev int := WordCore.Word wordsize

def repr (x : Z) : int := WordCore.repr wordsize x
def unsigned (x : int) : Z := WordCore.unsigned x
def signed (x : int) : Z := WordCore.signed x
def zero : int := WordCore.zero wordsize
def one : int := WordCore.one wordsize
def eq : int → int → Bool := WordCore.eq
def lt : int → int → Bool := WordCore.lt
def ltu : int → int → Bool := WordCore.ltu
def neg : int → int := WordCore.neg
def add : int → int → int := WordCore.add
def sub : int → int → int := WordCore.sub
def mul : int → int → int := WordCore.mul
def divs : int → int → int := WordCore.divs
def divu : int → int → int := WordCore.divu
def and : int → int → int := WordCore.and
def or : int → int → int := WordCore.or
def xor : int → int → int := WordCore.xor
def shl : int → int → int := WordCore.shl
def shru : int → int → int := WordCore.shru
def shr : int → int → int := WordCore.shr
def sign_ext (n : Z) (x : int) : int := WordCore.sign_ext n x
def testbit : int → Z → Bool := WordCore.testbit
def eqm : Z → Z → Prop := WordCore.eqm wordsize

/-! Selected generated members of `Include Make(Wordsize_Ptrofs)` retain their
    exact source propositions; proof discharge remains a later phase. -/
def eqm_repr_eq : Prop :=
  ∀ (x : Z) (y : int), eqm x (unsigned y) → repr x = y

def unsigned_repr_eq : Prop :=
  ∀ x : Z, unsigned (repr x) = zMod x modulus

/-- `GENAPP-COMPCERT-LIB-INTEGERS-4725-INCLUDE`: `Include Make(Wordsize_Ptrofs)`. -/
def generatedApplication : WordCore.GeneratedApplication :=
  WordCore.makeGeneratedApplication wordsize

theorem add_commut_proof_api (x y : int) : add x y = add y x := by
  change WordCore.add x y = WordCore.add y x
  apply WordCore.ext_of_val_eq
  rw [WordCore.add_val, WordCore.add_val, Nat.add_comm]

theorem add_assoc_proof_api (x y z : int) :
    add (add x y) z = add x (add y z) := by
  change WordCore.add (WordCore.add x y) z = WordCore.add x (WordCore.add y z)
  apply WordCore.ext_of_val_eq
  rw [WordCore.add_val, WordCore.add_val, WordCore.add_val, WordCore.add_val]
  rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

theorem sub_add_l_proof_api (x y z : int) :
    sub (add x y) z = add (sub x z) y := by
  change WordCore.sub (WordCore.add x y) z = WordCore.add (WordCore.sub x z) y
  apply WordCore.ext_of_val_eq
  apply Int.ofNat.inj
  rw [WordCore.sub_val_int, WordCore.add_val_int, WordCore.add_val_int,
    WordCore.sub_val_int]
  simp only [Int.emod_sub_emod, Int.sub_emod_emod, Int.emod_add_emod,
    Int.add_emod_emod]
  congr 1
  omega

theorem sub_shifted_proof_api (x y z : int) :
    sub (add x z) (add y z) = sub x y := by
  change WordCore.sub (WordCore.add x z) (WordCore.add y z) = WordCore.sub x y
  apply WordCore.ext_of_val_eq
  apply Int.ofNat.inj
  rw [WordCore.sub_val_int, WordCore.add_val_int, WordCore.add_val_int,
    WordCore.sub_val_int]
  simp only [Int.emod_sub_emod, Int.sub_emod_emod, Int.emod_add_emod,
    Int.add_emod_emod]
  congr 1
  omega

theorem generatedApplication_add_commut
    (x y : generatedApplication.int) :
    generatedApplication.add x y = generatedApplication.add y x := by
  change add x y = add y x
  exact add_commut_proof_api x y

theorem generatedApplication_add_assoc
    (x y z : generatedApplication.int) :
    generatedApplication.add (generatedApplication.add x y) z =
      generatedApplication.add x (generatedApplication.add y z) := by
  change add (add x y) z = add x (add y z)
  exact add_assoc_proof_api x y z

theorem generatedApplication_sub_add_l
    (x y z : generatedApplication.int) :
    generatedApplication.sub (generatedApplication.add x y) z =
      generatedApplication.add (generatedApplication.sub x z) y := by
  change sub (add x y) z = add (sub x z) y
  exact sub_add_l_proof_api x y z

theorem generatedApplication_sub_shifted
    (x y z : generatedApplication.int) :
    generatedApplication.sub (generatedApplication.add x z)
        (generatedApplication.add y z) =
      generatedApplication.sub x y := by
  change sub (add x z) (add y z) = sub x y
  exact sub_shifted_proof_api x y z

def to_int (x : int) : Int.int := Int.repr (unsigned x)
def to_int64 (x : int) : Int64.int := Int64.repr (unsigned x)
def of_int (x : Int.int) : int := repr (Int.unsigned x)
def of_intu : Int.int → int := of_int
def of_ints (x : Int.int) : int := repr (Int.signed x)
def of_int64 (x : Int64.int) : int := repr (Int64.unsigned x)

def agree32 (a : int) (b : Int.int) : Prop :=
  unsigned a = Int.unsigned b

def agree64 (a : int) (b : Int64.int) : Prop :=
  unsigned a = Int64.unsigned b

def modulus_eq32Statement : Prop :=
  CompCert4Lean.X86_64.Archi.ptr64 = false → modulus = Int.modulus

def eqm32Statement : Prop :=
  CompCert4Lean.X86_64.Archi.ptr64 = false →
    ∀ x y : Z, Int.eqm x y ↔ eqm x y

def agree32_reprStatement : Prop :=
  CompCert4Lean.X86_64.Archi.ptr64 = false →
    ∀ i : Z, agree32 (repr i) (Int.repr i)

def agree32_of_intStatement : Prop :=
  CompCert4Lean.X86_64.Archi.ptr64 = false →
    ∀ b : Int.int, agree32 (of_int b) b

def of_int_to_intStatement : Prop :=
  CompCert4Lean.X86_64.Archi.ptr64 = false →
    ∀ n : int, of_int (to_int n) = n

def modulus_eq64Statement : Prop :=
  CompCert4Lean.X86_64.Archi.ptr64 = true → modulus = Int64.modulus

def eqm64Statement : Prop :=
  CompCert4Lean.X86_64.Archi.ptr64 = true →
    ∀ x y : Z, Int64.eqm x y ↔ eqm x y

def agree64_reprStatement : Prop :=
  CompCert4Lean.X86_64.Archi.ptr64 = true →
    ∀ i : Z, agree64 (repr i) (Int64.repr i)

def of_int64_to_int64Statement : Prop :=
  CompCert4Lean.X86_64.Archi.ptr64 = true →
    ∀ n : int, of_int64 (to_int64 n) = n

end Ptrofs

abbrev ptrofs := Ptrofs.int

end CompCert4Lean.Lib.Integers
