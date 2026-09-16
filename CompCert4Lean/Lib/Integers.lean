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
  repr bits (CompCert4Lean.Lib.Zbits.Zzero_ext n (unsigned x))

def sign_ext {bits : Nat} (n : Z) (x : Word bits) : Word bits :=
  let step : (Z → Z) → (Z → Z) :=
    fun rec y =>
      CompCert4Lean.Lib.Zbits.Zshiftin
        (ZArith.BinInt.Z.odd y)
        (rec (ZArith.BinInt.Z.div2 y))
  let base : Z → Z :=
    fun y =>
      if ZArith.BinInt.Z.odd y then
        sumboolSelect (CompCert4Lean.Lib.Coqlib.zlt zZero n) (zOpp zOne) zZero
      else
        zZero
  repr bits
    (ZArith.BinInt.Z.iter (ZArith.BinInt.Z.pred n) step base (unsigned x))

def testbit {bits : Nat} (x : Word bits) : Z → Bool
  | .Zneg _ => false
  | .Z0 => Nat.testBit (natVal x) 0
  | .Zpos p => Nat.testBit (natVal x) (positiveToNat p)

def eqm (bits : Nat) (x y : Z) : Prop :=
  CompCert4Lean.Lib.Zbits.eqmod (zTwoPowerNat bits) x y

def cmp {bits : Nat} (c : comparison) (x y : Word bits) : Bool :=
  match c with
  | .Ceq => eq x y
  | .Cne => !(eq x y)
  | .Clt => lt x y
  | .Cle => !(lt y x)
  | .Cgt => lt y x
  | .Cge => !(lt x y)

def cmpu {bits : Nat} (c : comparison) (x y : Word bits) : Bool :=
  match c with
  | .Ceq => eq x y
  | .Cne => !(eq x y)
  | .Clt => ltu x y
  | .Cle => !(ltu y x)
  | .Cgt => ltu y x
  | .Cge => !(ltu x y)

def unsigned_bitfield_extract {bits : Nat} (pos width : Z) (n : Word bits) : Word bits :=
  zero_ext width (shru n (repr bits pos))

def signed_bitfield_extract {bits : Nat} (pos width : Z) (n : Word bits) : Word bits :=
  sign_ext width (shru n (repr bits pos))

def bitfield_insert {bits : Nat} (pos width : Z) (n p : Word bits) : Word bits :=
  let mask := shl (repr bits (zSub (zTwoP width) zOne)) (repr bits pos)
  or (shl (zero_ext width p) (repr bits pos)) (and n (not mask))

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
  size : int → Z
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
  mods : int → int → int
  divu : int → int → int
  modu : int → int → int
  cmp : comparison → int → int → Bool
  cmpu : comparison → int → int → Bool
  and : int → int → int
  or : int → int → int
  xor : int → int → int
  shl : int → int → int
  shru : int → int → int
  shr : int → int → int
  zero_ext : Z → int → int
  sign_ext : Z → int → int
  unsigned_bitfield_extract : Z → Z → int → int
  signed_bitfield_extract : Z → Z → int → int
  bitfield_insert : Z → Z → int → int → int

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
  size := fun x => CompCert4Lean.Lib.Zbits.Zsize (unsigned x)
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
  mods := mods
  divu := divu
  modu := modu
  cmp := cmp
  cmpu := cmpu
  and := and
  or := or
  xor := xor
  shl := shl
  shru := shru
  shr := shr
  zero_ext := zero_ext
  sign_ext := sign_ext
  unsigned_bitfield_extract := unsigned_bitfield_extract
  signed_bitfield_extract := signed_bitfield_extract
  bitfield_insert := bitfield_insert

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
def size (x : int) : Z := CompCert4Lean.Lib.Zbits.Zsize (unsigned x)
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
def zero_ext (n : Z) (x : int) : int :=
  WordCore.zero_ext n x
def rol : int → int → int := WordCore.rol
def ror : int → int → int := WordCore.ror
def shrx : int → int → int := WordCore.shrx
def testbit : int → Z → Bool := WordCore.testbit
def eqm : Z → Z → Prop := WordCore.eqm wordsize

def is_power2 (x : int) : Option int :=
  match CompCert4Lean.Lib.Zbits.Z_is_power2 (unsigned x) with
  | some i => some (repr i)
  | none => none

def one_bits (x : int) : List int :=
  List.map repr
    (CompCert4Lean.Lib.Zbits.Z_one_bits wordsize (unsigned x) zZero)

def cmp : comparison → int → int → Bool := WordCore.cmp
def cmpu : comparison → int → int → Bool := WordCore.cmpu

def divmodu2 (nhi nlo d : int) : Option (int × int) :=
  match eq_dec d zero with
  | .left _ => none
  | .right _ =>
      let qr := ZArith.BinInt.Z.div_eucl
        (zAdd (zMul (unsigned nhi) modulus) (unsigned nlo)) (unsigned d)
      match CompCert4Lean.Lib.Coqlib.zle qr.1 max_unsigned with
      | .left _ => some (repr qr.1, repr qr.2)
      | .right _ => none

def divmods2 (nhi nlo d : int) : Option (int × int) :=
  match eq_dec d zero with
  | .left _ => none
  | .right _ =>
      let n := zAdd (zMul (signed nhi) modulus) (unsigned nlo)
      let sd := signed d
      let q := zQuot n sd
      let r := zSub n (zMul q sd)
      match CompCert4Lean.Lib.Coqlib.zle min_signed q,
          CompCert4Lean.Lib.Coqlib.zle q max_signed with
      | .left _, .left _ => some (repr q, repr r)
      | _, _ => none

def unsigned_bitfield_extract (pos width : Z) (n : int) : int :=
  WordCore.unsigned_bitfield_extract pos width n

def signed_bitfield_extract (pos width : Z) (n : int) : int :=
  WordCore.signed_bitfield_extract pos width n

def bitfield_insert (pos width : Z) (n p : int) : int :=
  WordCore.bitfield_insert pos width n p

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

def modulus_power : Prop := modulus = zTwoP zwordsize

def half_modulus_pos : Prop := zLt zZero half_modulus

def min_signed_neg : Prop := zLt min_signed zZero

def signed_repr_eq : Prop :=
  ∀ x : Z,
    signed (repr x) =
      zltSelect (zMod x modulus) half_modulus (zMod x modulus)
        (zSub (zMod x modulus) modulus)

def eqm_refl2 : Prop := ∀ x y : Z, x = y → eqm x y

def eqm_trans : Prop :=
  ∀ x y z : Z, eqm x y → eqm y z → eqm x z

def eqm_samerepr : Prop :=
  ∀ x y : Z, eqm x y → repr x = repr y

def eqm_unsigned_repr_r : Prop :=
  ∀ a b : Z, eqm a b → eqm a (unsigned (repr b))

def repr_signed : Prop := ∀ i : int, repr (signed i) = i

def signed_repr : Prop :=
  ∀ z : Z, zLe min_signed z ∧ zLe z max_signed → signed (repr z) = z

def signed_zero : Prop := signed zero = zZero

def signed_mone : Prop := signed mone = zOpp zOne

def one_not_zero : Prop := one ≠ zero

def eq_spec : Prop :=
  ∀ x y : int, if eq x y then x = y else x ≠ y

def eq_true : Prop := ∀ x : int, eq x x = true

def eq_false : Prop := ∀ x y : int, x ≠ y → eq x y = false

def add_signed : Prop :=
  ∀ x y : int, add x y = repr (zAdd (signed x) (signed y))

def add_commut : Prop := ∀ x y : int, add x y = add y x

def add_zero : Prop := ∀ x : int, add x zero = x

def add_zero_l : Prop := ∀ x : int, add zero x = x

def add_assoc : Prop :=
  ∀ x y z : int, add (add x y) z = add x (add y z)

def add_neg_zero : Prop := ∀ x : int, add x (neg x) = zero

def neg_involutive : Prop := ∀ x : int, neg (neg x) = x

def sub_add_opp : Prop :=
  ∀ x y : int, sub x y = add x (neg y)

def sub_idem : Prop := ∀ x : int, sub x x = zero

def sub_add_l : Prop :=
  ∀ x y z : int, sub (add x y) z = add (sub x z) y

def sub_add_r : Prop :=
  ∀ x y z : int, sub x (add y z) = add (sub x z) (neg y)

def mul_commut : Prop := ∀ x y : int, mul x y = mul y x

def mul_zero : Prop := ∀ x : int, mul x zero = zero

def mul_one : Prop := ∀ x : int, mul x one = x

def mul_add_distr_l : Prop :=
  ∀ x y z : int, mul (add x y) z = add (mul x z) (mul y z)

def mul_add_distr_r : Prop :=
  ∀ x y z : int, mul x (add y z) = add (mul x y) (mul x z)

def modu_divu : Prop :=
  ∀ x y : int, y ≠ zero → modu x y = sub x (mul (divu x y) y)

def mods_divs : Prop :=
  ∀ x y : int, mods x y = sub x (mul (divs x y) y)

def divu_one : Prop := ∀ x : int, divu x one = x

def divs_one : Prop :=
  ∀ x : int, zLt zOne zwordsize → divs x one = x

def divmodu2_divu_modu : Prop :=
  ∀ n d : int, d ≠ zero →
    divmodu2 zero n d = some (divu n d, modu n d)

def divmods2_divs_mods : Prop :=
  ∀ n d : int,
    d ≠ zero → n ≠ repr min_signed ∨ d ≠ mone →
      divmods2 (if lt n zero then mone else zero) n d =
        some (divs n d, mods n d)

def bits_one : Prop :=
  ∀ n : Z,
    testbit one n =
      sumboolSelect (CompCert4Lean.Lib.Coqlib.zeq n zZero) true false

def bits_mone : Prop :=
  ∀ i : Z, zLe zZero i ∧ zLt i zwordsize → testbit mone i = true

def bits_signed : Prop :=
  ∀ (x : int) (i : Z), zLe zZero i →
    zTestbit (signed x) i =
      testbit x (zltSelect i zwordsize i (zSub zwordsize zOne))

def bits_not : Prop :=
  ∀ (x : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (not x) i = !(testbit x i)

def and_commut : Prop := ∀ x y : int, and x y = and y x

def and_assoc : Prop :=
  ∀ x y z : int, and (and x y) z = and x (and y z)

def and_zero : Prop := ∀ x : int, and x zero = zero

def and_mone : Prop := ∀ x : int, and x mone = x

def and_idem : Prop := ∀ x : int, and x x = x

def or_commut : Prop := ∀ x y : int, or x y = or y x

def or_assoc : Prop :=
  ∀ x y z : int, or (or x y) z = or x (or y z)

def or_zero : Prop := ∀ x : int, or x zero = x

def or_mone : Prop := ∀ x : int, or x mone = mone

def xor_commut : Prop := ∀ x y : int, xor x y = xor y x

def xor_assoc : Prop :=
  ∀ x y z : int, xor (xor x y) z = xor x (xor y z)

def xor_zero : Prop := ∀ x : int, xor x zero = x

def xor_is_zero : Prop :=
  ∀ x y : int, eq (xor x y) zero = eq x y

def not_involutive : Prop := ∀ x : int, not (not x) = x

def not_or_and_not : Prop :=
  ∀ x y : int, not (or x y) = and (not x) (not y)

def shl_zero : Prop := ∀ x : int, shl x zero = x

def ltu_iwordsize_inv : Prop :=
  ∀ x : int, ltu x iwordsize = true →
    zLe zZero (unsigned x) ∧ zLt (unsigned x) zwordsize

def shl_shl : Prop :=
  ∀ x y z : int,
    ltu y iwordsize = true →
    ltu z iwordsize = true →
    ltu (add y z) iwordsize = true →
      shl (shl x y) z = shl x (add y z)

def shru_zero : Prop := ∀ x : int, shru x zero = x

def shru_shru : Prop :=
  ∀ x y z : int,
    ltu y iwordsize = true →
    ltu z iwordsize = true →
    ltu (add y z) iwordsize = true →
      shru (shru x y) z = shru x (add y z)

def shr_zero : Prop := ∀ x : int, shr x zero = x

def shr_shr : Prop :=
  ∀ x y z : int,
    ltu y iwordsize = true →
    ltu z iwordsize = true →
    ltu (add y z) iwordsize = true →
      shr (shr x y) z = shr x (add y z)

def shru_lt_zero : Prop :=
  ∀ x : int,
    shru x (repr (zSub zwordsize zOne)) =
      if lt x zero then one else zero

def shr_lt_zero : Prop :=
  ∀ x : int,
    shr x (repr (zSub zwordsize zOne)) =
      if lt x zero then mone else zero

def bits_rol : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (rol x y) i = testbit x (zMod (zSub i (unsigned y)) zwordsize)

def bits_ror : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (ror x y) i = testbit x (zMod (zAdd i (unsigned y)) zwordsize)

def ror_rol_neg : Prop :=
  ∀ x y : int, zDivide zwordsize modulus → ror x y = rol x (neg y)

def or_ror : Prop :=
  ∀ x y z : int,
    ltu y iwordsize = true →
    ltu z iwordsize = true →
    add y z = iwordsize →
      ror x z = or (shl x y) (shru x z)

def is_power2_range : Prop :=
  ∀ n logn : int,
    is_power2 n = some logn → ltu logn iwordsize = true

def shl_mul : Prop :=
  ∀ x y : int, shl x y = mul x (shl one y)

def mul_pow2 : Prop :=
  ∀ x n logn : int,
    is_power2 n = some logn → mul x n = shl x logn

def shru_div_two_p : Prop :=
  ∀ x y : int, shru x y = repr (zDiv (unsigned x) (zTwoP (unsigned y)))

def divu_pow2 : Prop :=
  ∀ x n logn : int,
    is_power2 n = some logn → divu x n = shru x logn

def shr_div_two_p : Prop :=
  ∀ x y : int, shr x y = repr (zDiv (signed x) (zTwoP (unsigned y)))

def divs_pow2 : Prop :=
  ∀ x n logn : int,
    is_power2 n = some logn → divs x n = shrx x logn

def modu_and : Prop :=
  ∀ x n logn : int,
    is_power2 n = some logn → modu x n = and x (sub n one)

def shrx_shr : Prop :=
  ∀ x y : int,
    ltu y (repr (zSub zwordsize zOne)) = true →
      shrx x y =
        shr (if lt x zero then add x (sub (shl one y) one) else x) y

def bits_zero_ext : Prop :=
  ∀ (n : Z) (x : int) (i : Z), zLe zZero i →
    testbit (zero_ext n x) i =
      zltSelect i n (testbit x i) false

def bits_sign_ext : Prop :=
  ∀ (n : Z) (x : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (sign_ext n x) i =
      testbit x (zltSelect i n i (zSub n zOne))

def zero_ext_and : Prop :=
  ∀ (n : Z) (x : int), zLe zZero n →
    zero_ext n x = and x (repr (zSub (zTwoP n) zOne))

def sign_ext_widen : Prop :=
  ∀ (x : int) (n n' : Z), zLt zZero n ∧ zLe n n' →
    sign_ext n' (sign_ext n x) = sign_ext n x

def zero_ext_idem : Prop :=
  ∀ (n : Z) (x : int), zLe zZero n →
    zero_ext n (zero_ext n x) = zero_ext n x

def sign_ext_idem : Prop :=
  ∀ (n : Z) (x : int), zLt zZero n →
    sign_ext n (sign_ext n x) = sign_ext n x

def sign_ext_shr_shl : Prop :=
  ∀ (n : Z) (x : int), zLt zZero n ∧ zLe n zwordsize →
    let y := repr (zSub zwordsize n)
    sign_ext n x = shr (shl x y) y

def one_bits_range : Prop :=
  ∀ x i : int, i ∈ one_bits x → ltu i iwordsize = true

def one_bits_decomp : Prop :=
  let rec intOfOneBits : List int → int
    | [] => zero
    | a :: rest => add (shl one a) (intOfOneBits rest)
  ∀ x : int, x = intOfOneBits (one_bits x)

def negate_cmp : Prop :=
  ∀ (c : comparison) (x y : int),
    cmp (negate_comparison c) x y = !(cmp c x y)

def negate_cmpu : Prop :=
  ∀ (c : comparison) (x y : int),
    cmpu (negate_comparison c) x y = !(cmpu c x y)

def swap_cmp : Prop :=
  ∀ (c : comparison) (x y : int),
    cmp (swap_comparison c) x y = cmp c y x

def swap_cmpu : Prop :=
  ∀ (c : comparison) (x y : int),
    cmpu (swap_comparison c) x y = cmpu c y x

def lt_sub_overflow : Prop :=
  ∀ x y : int,
    xor (sub_overflow x y zero) (negative (sub x y)) =
      if lt x y then one else zero

def not_lt : Prop :=
  ∀ x y : int, !(lt y x) = (lt x y || eq x y)

def lt_not : Prop :=
  ∀ x y : int, lt y x = (!(lt x y) && !(eq x y))

def not_ltu : Prop :=
  ∀ x y : int, !(ltu y x) = (ltu x y || eq x y)

def ltu_not : Prop :=
  ∀ x y : int, ltu y x = (!(ltu x y) && !(eq x y))

def bits_size_2 : Prop :=
  ∀ (x : int) (i : Z), zLe (size x) i → testbit x i = false

def size_range : Prop :=
  ∀ x : int, zLe zZero (size x) ∧ zLe (size x) zwordsize

def bits_size_4 : Prop :=
  ∀ (x : int) (n : Z),
    zLe zZero n →
    testbit x (zSub n zOne) = true →
    (∀ i : Z, zLe n i ∧ zLt i zwordsize → testbit x i = false) →
      size x = n

def unsigned_bitfield_extract_by_shifts : Prop :=
  ∀ (pos width : Z) (n : int),
    zLe zZero pos → zLt zZero width → zLe (zAdd pos width) zwordsize →
      unsigned_bitfield_extract pos width n =
        shru (shl n (repr (zSub (zSub zwordsize pos) width)))
          (repr (zSub zwordsize width))

def signed_bitfield_extract_by_shifts : Prop :=
  ∀ (pos width : Z) (n : int),
    zLe zZero pos → zLt zZero width → zLe (zAdd pos width) zwordsize →
      signed_bitfield_extract pos width n =
        shr (shl n (repr (zSub (zSub zwordsize pos) width)))
          (repr (zSub zwordsize width))

def bitfield_insert_alternative : Prop :=
  let bitfieldInsert := fun (pos width : Z) (n p : int) =>
    let mask := shl (repr (zSub (zTwoP width) zOne)) (repr pos)
    or (shl (zero_ext width p) (repr pos)) (and n (not mask))
  ∀ (pos width : Z) (n p : int), zLe zZero width →
    bitfieldInsert pos width n p =
      let mask := shl (repr (zSub (zTwoP width) zOne)) (repr pos)
      or (and (shl p (repr pos)) mask) (and n (not mask))

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
          _root_.Int.not_lt.mpr (_root_.Int.natCast_nonneg _)
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

private theorem ziter_unfold_succ {A : Type} (f : A → A) (x : A) (k : Nat) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.iter
        (zOfNat (k + 1)) f x =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.iter
        (zOfNat k) f (f x) := by
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.iter,
    zOfNat, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
    Int.ofNat_eq_natCast, Int.toNat_natCast]
  rfl

private theorem ziter_commute {A : Type} (f : A → A) (x : A) (k : Nat) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.iter
        (zOfNat k) f (f x) =
      f (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.iter
        (zOfNat k) f x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      rw [ziter_unfold_succ, ziter_unfold_succ]
      rw [ih (f x), ih x]

private theorem ziter_succ {A : Type} (f : A → A) (x : A) (k : Nat) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.iter
        (zOfNat (k + 1)) f x =
      f (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.iter
        (zOfNat k) f x) := by
  rw [ziter_unfold_succ, ziter_commute]

private theorem zdiv2_nat (a : Nat) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div2 (zOfNat a) =
      zOfNat (a / 2) := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div2,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div,
    zOfNat, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change Int.ediv (Int.ofNat a) (Int.ofNat 2) = Int.ofNat (a / 2)
  exact Int.ofNat_ediv_ofNat

private theorem zshiftin_nat (b : Bool) (a : Nat) :
    CompCert4Lean.Lib.Zbits.Zshiftin b (zOfNat a) =
      zOfNat (2 * a + if b then 1 else 0) := by
  cases b <;>
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective <;>
    simp only [CompCert4Lean.Lib.Zbits.Zshiftin,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.double,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.succ_double,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.succ,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
      zOfNat, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
      Bool.false_eq_true, ↓reduceIte]
  · simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat,
      Nat.mul_comm, Nat.add_comm,
      Int.mul_comm]
  · simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat,
      Nat.mul_comm, Nat.add_comm,
      Int.mul_comm, Int.add_comm]

private theorem zNatAbs_nat (a : Nat) :
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zOfNat a)).natAbs = a := by
  have hcast :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zOfNat a) = Int.ofNat a := by
    exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt (Int.ofNat a)
  rw [hcast]
  simp

private theorem zzero_ext_nat (k a : Nat) :
    CompCert4Lean.Lib.Zbits.Zzero_ext (zOfNat k) (zOfNat a) =
      zOfNat (a % (2 ^ k)) := by
  induction k generalizing a with
  | zero =>
      change zOfNat 0 = zOfNat (a % 1)
      rw [Nat.mod_one]
  | succ k ih =>
      have hstep :
          CompCert4Lean.Lib.Zbits.Zzero_ext (zOfNat (k + 1)) (zOfNat a) =
            CompCert4Lean.Lib.Zbits.Zshiftin
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.odd
                (zOfNat a))
              (CompCert4Lean.Lib.Zbits.Zzero_ext (zOfNat k)
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div2
                  (zOfNat a))) := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.iter
            (zOfNat (k + 1))
            (fun rec y =>
              CompCert4Lean.Lib.Zbits.Zshiftin
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.odd y)
                (rec (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div2 y)))
            (fun _ => zZero) (zOfNat a) = _
        rw [ziter_succ]
        rfl
      rw [hstep]
      rw [zdiv2_nat]
      rw [ih]
      rw [zshiftin_nat]
      congr 1
      by_cases h : a % 2 = 0
      · have hodd :
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.odd
                (zOfNat a) = false := by
          unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.odd
          unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
          rw [zNatAbs_nat]
          simp [h]
        rw [hodd]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hmod := Nat.mod_mul (a := 2) (b := 2 ^ k) (x := a)
        simpa [Nat.pow_succ, Nat.add_comm, Nat.mul_comm, h] using hmod.symm
      · have hrem : a % 2 = 1 := by omega
        have hodd :
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.odd
                (zOfNat a) = true := by
          unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.odd
          unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
          rw [zNatAbs_nat]
          simp [hrem]
        rw [hodd]
        simp only [↓reduceIte]
        have hmod := Nat.mod_mul (a := 2) (b := 2 ^ k) (x := a)
        simpa [Nat.pow_succ, Nat.add_comm, Nat.mul_comm, hrem] using hmod.symm

private theorem zzero_ext_nonneg (n : Z) (x : int) (hn : zLe zZero n) :
    CompCert4Lean.Lib.Zbits.Zzero_ext n (unsigned x) =
      zOfNat (x.val % (2 ^ zToNat n)) := by
  have hn' := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Z2Nat.id n hn
  rw [← hn']
  change CompCert4Lean.Lib.Zbits.Zzero_ext (zOfNat (zToNat n)) x.intval = _
  rw [WordCore.intval_eq_zOfNat_val x]
  simpa only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Nat2Z.id] using
    zzero_ext_nat (zToNat n) x.val

private theorem zero_ext_val (n : Z) (x : int) (hn : zLe zZero n) :
    (zero_ext n x).val =
      (x.val % (2 ^ zToNat n)) % (2 ^ wordsize) := by
  unfold zero_ext WordCore.zero_ext
  change (WordCore.repr wordsize
    (CompCert4Lean.Lib.Zbits.Zzero_ext n (unsigned x))).val = _
  rw [zzero_ext_nonneg n x hn]
  change (WordCore.repr wordsize
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (Int.ofNat (x.val % (2 ^ zToNat n))))).val = _
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

theorem unsigned_repr_proof_api (z : Z)
    (hz : zLe zZero z ∧ zLe z max_unsigned) :
    unsigned (repr z) = z := by
  have hznonneg : 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z := hz.1
  have hzlt :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z <
        ((2 ^ wordsize : Nat) : _root_.Int) := by
    have hzmax := hz.2
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ max_unsigned at hzmax
    unfold max_unsigned modulus at hzmax
    rw [WordCore.twoPowerNat_eq_zOfNat_twoPow] at hzmax
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z ≤
      _root_.Int.ofNat (2 ^ wordsize) - 1 at hzmax
    have hzmax' :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z ≤
          ((2 ^ wordsize : Nat) : _root_.Int) - 1 := by
      simpa only [_root_.Int.ofNat_eq_natCast] using hzmax
    omega
  change (WordCore.repr wordsize z).intval = z
  rw [WordCore.intval_eq_zOfNat_val]
  have hval :
      (WordCore.repr wordsize z).val =
        _root_.Int.toNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z %
            ((2 ^ wordsize : Nat) : _root_.Int)) := by
    rw [← CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt_intOfZ z]
    simpa only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] using
      WordCore.val_repr wordsize
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z)
  rw [hval, _root_.Int.emod_eq_of_lt hznonneg hzlt]
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (_root_.Int.ofNat
        (_root_.Int.toNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z))) = z
  calc
    _ = CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z) :=
      congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (_root_.Int.toNat_of_nonneg hznonneg)
    _ = z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt_intOfZ z

theorem zero_ext_mod_proof_api (n : Z) (x : int)
    (hn : zLe zZero n ∧ zLt n zwordsize) :
    unsigned (zero_ext n x) =
      ZArith.BinInt.Z.modulo (unsigned x) (two_p n) := by
  have hnnonneg : 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n := hn.1
  have hnlt : zToNat n < wordsize := by
    change _root_.Int.toNat
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n) < wordsize
    apply (_root_.Int.toNat_lt hnnonneg).2
    have hnltInt := hn.2
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zOfNat wordsize) at hnltInt
    have hnltInt' :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n <
          _root_.Int.ofNat wordsize := by
      simpa only [zOfNat, ZArith.BinInt.Z.of_nat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] using hnltInt
    simpa only [_root_.Int.ofNat_eq_natCast] using hnltInt'
  have hpow : 2 ^ zToNat n ≤ 2 ^ wordsize :=
    Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_of_lt hnlt)
  have hvalLt : x.val % (2 ^ zToNat n) < 2 ^ wordsize :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) hpow
  change (zero_ext n x).intval = _
  rw [WordCore.intval_eq_zOfNat_val, zero_ext_val n x hn.1,
    Nat.mod_eq_of_lt hvalLt, zero_ext_modulo n x hn.1]
  rfl

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
def modulus : Z := zTwoPowerNat wordsize
abbrev int := WordCore.Word wordsize
def repr (x : Z) : int := WordCore.repr wordsize x
def unsigned (x : int) : Z := WordCore.unsigned x
def zero : int := WordCore.zero wordsize

def eqm_samerepr : Prop :=
  ∀ x y : Z, WordCore.eqm wordsize x y → repr x = repr y

def unsigned_range : Prop :=
  ∀ i : int, zLe zZero (unsigned i) ∧ zLt (unsigned i) modulus

theorem unsigned_range_proof_api (i : int) :
    zLe zZero (unsigned i) ∧ zLt (unsigned i) modulus := by
  constructor
  · have h := i.intrange.1
    change (-1 : _root_.Int) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ i.intval at h
    change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ i.intval
    omega
  · exact i.intrange.2

/-- `GENAPP-COMPCERT-LIB-INTEGERS-3582-ASSIGNMENT`: `Make(Wordsize_8)`. -/
def generatedApplication : WordCore.GeneratedApplication :=
  WordCore.makeGeneratedApplication wordsize

end Byte

abbrev int := Int.int
abbrev byte := Byte.int

def int_wordsize_divides_modulusStatement : Prop :=
  zDivide (zOfNat Int.wordsize) Int.modulus

def int_wordsize_divides_modulus : Prop :=
  int_wordsize_divides_modulusStatement

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
def size (x : int) : Z := CompCert4Lean.Lib.Zbits.Zsize (unsigned x)
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
def zero_ext (n : Z) (x : int) : int :=
  WordCore.zero_ext n x
def rol : int → int → int := WordCore.rol
def ror : int → int → int := WordCore.ror
def shrx : int → int → int := WordCore.shrx
def testbit : int → Z → Bool := WordCore.testbit
def eqm : Z → Z → Prop := WordCore.eqm wordsize

def is_power2 (x : int) : Option int :=
  match CompCert4Lean.Lib.Zbits.Z_is_power2 (unsigned x) with
  | some i => some (repr i)
  | none => none

def cmp : comparison → int → int → Bool := WordCore.cmp
def cmpu : comparison → int → int → Bool := WordCore.cmpu

def divmodu2 (nhi nlo d : int) : Option (int × int) :=
  match eq_dec d zero with
  | .left _ => none
  | .right _ =>
      let qr := ZArith.BinInt.Z.div_eucl
        (zAdd (zMul (unsigned nhi) modulus) (unsigned nlo)) (unsigned d)
      match CompCert4Lean.Lib.Coqlib.zle qr.1 max_unsigned with
      | .left _ => some (repr qr.1, repr qr.2)
      | .right _ => none

def divmods2 (nhi nlo d : int) : Option (int × int) :=
  match eq_dec d zero with
  | .left _ => none
  | .right _ =>
      let n := zAdd (zMul (signed nhi) modulus) (unsigned nlo)
      let sd := signed d
      let q := zQuot n sd
      let r := zSub n (zMul q sd)
      match CompCert4Lean.Lib.Coqlib.zle min_signed q,
          CompCert4Lean.Lib.Coqlib.zle q max_signed with
      | .left _, .left _ => some (repr q, repr r)
      | _, _ => none

def unsigned_bitfield_extract (pos width : Z) (n : int) : int :=
  WordCore.unsigned_bitfield_extract pos width n

def signed_bitfield_extract (pos width : Z) (n : int) : int :=
  WordCore.signed_bitfield_extract pos width n

def bitfield_insert (pos width : Z) (n p : int) : int :=
  WordCore.bitfield_insert pos width n p

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

def modulus_power : Prop := modulus = zTwoP zwordsize
def modulus_pos : Prop := zLt zZero modulus
def half_modulus_pos : Prop := zLt zZero half_modulus
def min_signed_neg : Prop := zLt min_signed zZero

def signed_repr_eq : Prop :=
  ∀ x : Z,
    signed (repr x) =
      zltSelect (zMod x modulus) half_modulus (zMod x modulus)
        (zSub (zMod x modulus) modulus)

def eqm_refl2 : Prop := ∀ x y : Z, x = y → eqm x y

def eqm_trans : Prop :=
  ∀ x y z : Z, eqm x y → eqm y z → eqm x z

def eqm_unsigned_repr_r : Prop :=
  ∀ a b : Z, eqm a b → eqm a (unsigned (repr b))

def eqm_signed_unsigned : Prop :=
  ∀ x : int, eqm (signed x) (unsigned x)

def signed_range : Prop :=
  ∀ i : int, zLe min_signed (signed i) ∧ zLe (signed i) max_signed

def repr_signed : Prop := ∀ i : int, repr (signed i) = i
def signed_zero : Prop := signed zero = zZero
def signed_mone : Prop := signed mone = zOpp zOne
def one_not_zero : Prop := one ≠ zero

def eq_spec : Prop :=
  ∀ x y : int, if eq x y then x = y else x ≠ y

def eq_true : Prop := ∀ x : int, eq x x = true
def eq_sym : Prop := ∀ x y : int, eq x y = eq y x

def add_signed : Prop :=
  ∀ x y : int, add x y = repr (zAdd (signed x) (signed y))

def add_commut : Prop := ∀ x y : int, add x y = add y x
def add_zero : Prop := ∀ x : int, add x zero = x
def add_zero_l : Prop := ∀ x : int, add zero x = x

def add_assoc : Prop :=
  ∀ x y z : int, add (add x y) z = add x (add y z)

def neg_involutive : Prop := ∀ x : int, neg (neg x) = x
def sub_zero_l : Prop := ∀ x : int, sub x zero = x

def sub_add_opp : Prop :=
  ∀ x y : int, sub x y = add x (neg y)

def sub_add_l : Prop :=
  ∀ x y z : int, sub (add x y) z = add (sub x z) y

def sub_add_r : Prop :=
  ∀ x y z : int, sub x (add y z) = add (sub x z) (neg y)

def mul_zero : Prop := ∀ x : int, mul x zero = zero

def mul_add_distr_l : Prop :=
  ∀ x y z : int, mul (add x y) z = add (mul x z) (mul y z)

def mul_add_distr_r : Prop :=
  ∀ x y z : int, mul x (add y z) = add (mul x y) (mul x z)

def modu_divu : Prop :=
  ∀ x y : int, y ≠ zero → modu x y = sub x (mul (divu x y) y)

def mods_divs : Prop :=
  ∀ x y : int, mods x y = sub x (mul (divs x y) y)

def divmodu2_divu_modu : Prop :=
  ∀ n d : int, d ≠ zero →
    divmodu2 zero n d = some (divu n d, modu n d)

def divmods2_divs_mods : Prop :=
  ∀ n d : int,
    d ≠ zero → n ≠ repr min_signed ∨ d ≠ mone →
      divmods2 (if lt n zero then mone else zero) n d =
        some (divs n d, mods n d)

def bits_zero : Prop := ∀ i : Z, testbit zero i = false

def bits_mone : Prop :=
  ∀ i : Z, zLe zZero i ∧ zLt i zwordsize → testbit mone i = true

def and_commut : Prop := ∀ x y : int, and x y = and y x

def and_assoc : Prop :=
  ∀ x y z : int, and (and x y) z = and x (and y z)

def and_zero : Prop := ∀ x : int, and x zero = zero
def and_mone : Prop := ∀ x : int, and x mone = x
def and_idem : Prop := ∀ x : int, and x x = x
def or_commut : Prop := ∀ x y : int, or x y = or y x

def or_assoc : Prop :=
  ∀ x y z : int, or (or x y) z = or x (or y z)

def or_zero : Prop := ∀ x : int, or x zero = x
def or_mone : Prop := ∀ x : int, or x mone = mone
def xor_commut : Prop := ∀ x y : int, xor x y = xor y x

def xor_assoc : Prop :=
  ∀ x y z : int, xor (xor x y) z = xor x (xor y z)

def xor_zero : Prop := ∀ x : int, xor x zero = x
def xor_idem : Prop := ∀ x : int, xor x x = zero

def xor_zero_equal : Prop :=
  ∀ x y : int, xor x y = zero → x = y

def not_involutive : Prop := ∀ x : int, not (not x) = x

def not_or_and_not : Prop :=
  ∀ x y : int, not (or x y) = and (not x) (not y)

def shl_zero : Prop := ∀ x : int, shl x zero = x

def ltu_inv : Prop :=
  ∀ x y : int, ltu x y = true →
    zLe zZero (unsigned x) ∧ zLt (unsigned x) (unsigned y)

def shru_zero : Prop := ∀ x : int, shru x zero = x
def shr_zero : Prop := ∀ x : int, shr x zero = x

def shru_lt_zero : Prop :=
  ∀ x : int,
    shru x (repr (zSub zwordsize zOne)) =
      if lt x zero then one else zero

def shr_lt_zero : Prop :=
  ∀ x : int,
    shr x (repr (zSub zwordsize zOne)) =
      if lt x zero then mone else zero

def bits_rol : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (rol x y) i = testbit x (zMod (zSub i (unsigned y)) zwordsize)

def bits_ror : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (ror x y) i = testbit x (zMod (zAdd i (unsigned y)) zwordsize)

def ror_rol_neg : Prop :=
  ∀ x y : int, zDivide zwordsize modulus → ror x y = rol x (neg y)

def modu_and : Prop :=
  ∀ x n logn : int,
    is_power2 n = some logn → modu x n = and x (sub n one)

def bits_zero_ext : Prop :=
  ∀ (n : Z) (x : int) (i : Z), zLe zZero i →
    testbit (zero_ext n x) i = zltSelect i n (testbit x i) false

def negate_cmp : Prop :=
  ∀ (c : comparison) (x y : int),
    cmp (negate_comparison c) x y = !(cmp c x y)

def negate_cmpu : Prop :=
  ∀ (c : comparison) (x y : int),
    cmpu (negate_comparison c) x y = !(cmpu c x y)

def swap_cmp : Prop :=
  ∀ (c : comparison) (x y : int),
    cmp (swap_comparison c) x y = cmp c y x

def swap_cmpu : Prop :=
  ∀ (c : comparison) (x y : int),
    cmpu (swap_comparison c) x y = cmpu c y x

def lt_sub_overflow : Prop :=
  ∀ x y : int,
    xor (sub_overflow x y zero) (negative (sub x y)) =
      if lt x y then one else zero

def not_lt : Prop :=
  ∀ x y : int, !(lt y x) = (lt x y || eq x y)

def lt_not : Prop :=
  ∀ x y : int, lt y x = (!(lt x y) && !(eq x y))

def not_ltu : Prop :=
  ∀ x y : int, !(ltu y x) = (ltu x y || eq x y)

def ltu_not : Prop :=
  ∀ x y : int, ltu y x = (!(ltu x y) && !(eq x y))

def size_range : Prop :=
  ∀ x : int, zLe zZero (size x) ∧ zLe (size x) zwordsize

def bits_size_2 : Prop :=
  ∀ (x : int) (i : Z), zLe (size x) i → testbit x i = false

def bits_size_4 : Prop :=
  ∀ (x : int) (n : Z),
    zLe zZero n →
    testbit x (zSub n zOne) = true →
    (∀ i : Z, zLe n i ∧ zLt i zwordsize → testbit x i = false) →
      size x = n

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

def bits_hiword : Prop := bits_hiwordStatement
def bits_loword : Prop := bits_lowordStatement
def bits_ofwords : Prop := bits_ofwordsStatement
def bits_shl' : Prop := bits_shl'Statement
def bits_shr' : Prop := bits_shr'Statement
def bits_shru' : Prop := bits_shru'Statement
def decompose_and : Prop := decompose_andStatement
def decompose_bitwise_binop : Prop := decompose_bitwise_binopStatement
def decompose_le : Prop := decompose_leStatement
def decompose_leu : Prop := decompose_leuStatement
def decompose_lt : Prop := decompose_ltStatement
def decompose_ltu : Prop := decompose_ltuStatement
def decompose_mul : Prop := decompose_mulStatement
def decompose_or : Prop := decompose_orStatement
def decompose_shl_1 : Prop := decompose_shl_1Statement
def decompose_shl_2 : Prop := decompose_shl_2Statement
def decompose_shr_1 : Prop := decompose_shr_1Statement
def decompose_shr_2 : Prop := decompose_shr_2Statement
def decompose_shru_1 : Prop := decompose_shru_1Statement
def decompose_shru_2 : Prop := decompose_shru_2Statement
def decompose_xor : Prop := decompose_xorStatement
def divu_pow2' : Prop := divu_pow2'Statement
def eqm_mul_2p32 : Prop := eqm_mul_2p32Statement
def hi_ofwords : Prop := hi_ofwordsStatement
def int_ltu_2_inv : Prop := int_ltu_2_invStatement
def is_power2'_correct : Prop := is_power2'_correctStatement
def is_power2'_range : Prop := is_power2'_rangeStatement
def is_power2'_rng : Prop := is_power2'_rngStatement
def lo_ofwords : Prop := lo_ofwordsStatement
def mul_pow2' : Prop := mul_pow2'Statement
def ofwords_add : Prop := ofwords_addStatement
def ofwords_add' : Prop := ofwords_add'Statement
def ofwords_add'' : Prop := ofwords_add''Statement
def ofwords_recompose : Prop := ofwords_recomposeStatement
def one_bits'_decomp : Prop := one_bits'_decompStatement
def one_bits'_range : Prop := one_bits'_rangeStatement
def or_ror' : Prop := or_ror'Statement
def shl'_mul : Prop := shl'_mulStatement
def shl'_mul_two_p : Prop := shl'_mul_two_pStatement
def shl'_one_two_p : Prop := shl'_one_two_pStatement
def shl'_shl' : Prop := shl'_shl'Statement
def shr'_shr' : Prop := shr'_shr'Statement
def shru'_shru' : Prop := shru'_shru'Statement
def shrx'_shr_2 : Prop := shrx'_shr_2Statement
def shrx'_zero : Prop := shrx'_zeroStatement

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
def eq_dec (x y : int) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) :=
  if h : x = y then .left h else .right h
def lt : int → int → Bool := WordCore.lt
def ltu : int → int → Bool := WordCore.ltu
def cmpu (c : comparison) (x y : int) : Bool :=
  match c with
  | .Ceq => eq x y
  | .Cne => !(eq x y)
  | .Clt => ltu x y
  | .Cle => !(ltu y x)
  | .Cgt => ltu y x
  | .Cge => !(ltu x y)
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

def modulus_pos : Prop := zLt zZero modulus
def min_signed_neg : Prop := zLt min_signed zZero

def eqm_unsigned_repr : Prop :=
  ∀ z : Z, eqm z (unsigned (repr z))

def unsigned_range : Prop :=
  ∀ i : int, zLe zZero (unsigned i) ∧ zLt (unsigned i) modulus

def unsigned_range_2 : Prop :=
  ∀ i : int, zLe zZero (unsigned i) ∧ zLe (unsigned i) max_unsigned

def repr_unsigned : Prop := ∀ i : int, repr (unsigned i) = i

def unsigned_repr : Prop :=
  ∀ z : Z, zLe zZero z ∧ zLe z max_unsigned → unsigned (repr z) = z

def signed_repr : Prop :=
  ∀ z : Z, zLe min_signed z ∧ zLe z max_signed → signed (repr z) = z

def unsigned_zero : Prop := unsigned zero = zZero
def unsigned_one : Prop := unsigned one = zOne

def eq_spec : Prop :=
  ∀ x y : int, if eq x y then x = y else x ≠ y

def eq_true : Prop := ∀ x : int, eq x x = true
def eq_false : Prop := ∀ x y : int, x ≠ y → eq x y = false

def add_unsigned : Prop :=
  ∀ x y : int, add x y = repr (zAdd (unsigned x) (unsigned y))

def add_commut : Prop := ∀ x y : int, add x y = add y x
def add_zero : Prop := ∀ x : int, add x zero = x
def add_zero_l : Prop := ∀ x : int, add zero x = x

def add_assoc : Prop :=
  ∀ x y z : int, add (add x y) z = add x (add y z)

def sub_add_opp : Prop :=
  ∀ x y : int, sub x y = add x (neg y)

def sub_add_l : Prop :=
  ∀ x y z : int, sub (add x y) z = add (sub x z) y

def sub_add_r : Prop :=
  ∀ x y z : int, sub x (add y z) = add (sub x z) (neg y)

def sub_shifted : Prop :=
  ∀ x y z : int, sub (add x z) (add y z) = sub x y

def negate_cmpu : Prop :=
  ∀ (c : comparison) (x y : int),
    cmpu (negate_comparison c) x y = !(cmpu c x y)

def swap_cmpu : Prop :=
  ∀ (c : comparison) (x y : int),
    cmpu (swap_comparison c) x y = cmpu c y x

def translate_cmpu : Prop :=
  ∀ (c : comparison) (x y d : int),
    zLe zZero (zAdd (unsigned x) (unsigned d)) ∧
      zLe (zAdd (unsigned x) (unsigned d)) max_unsigned →
    zLe zZero (zAdd (unsigned y) (unsigned d)) ∧
      zLe (zAdd (unsigned y) (unsigned d)) max_unsigned →
      cmpu c (add x d) (add y d) = cmpu c x y

def not_ltu : Prop :=
  ∀ x y : int, !(ltu y x) = (ltu x y || eq x y)

def ltu_not : Prop :=
  ∀ x y : int, ltu y x = (!(ltu x y) && !(eq x y))

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

def agree32_of_int : Prop := agree32_of_intStatement
def agree32_repr : Prop := agree32_reprStatement
def agree64_repr : Prop := agree64_reprStatement
def eqm32 : Prop := eqm32Statement
def eqm64 : Prop := eqm64Statement
def modulus_eq32 : Prop := modulus_eq32Statement
def modulus_eq64 : Prop := modulus_eq64Statement
def of_int64_to_int64 : Prop := of_int64_to_int64Statement
def of_int_to_int : Prop := of_int_to_intStatement

end Ptrofs

abbrev ptrofs := Ptrofs.int

end CompCert4Lean.Lib.Integers

namespace CompCert4Lean.Lib.Integers.Int

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem signed_mone_proof : signed_mone := by
  rfl

theorem shru_zero_proof : shru_zero := by
  intro x
  have hx0 :
      ZArith.BinInt.Z.le
        Numbers.BinNums.Z.Z0 (unsigned x) := by
    have h := x.intrange.1
    change (-1 : Int) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval at h
    change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval
    omega
  have hxlt : ZArith.BinInt.Z.lt (unsigned x) modulus := x.intrange.2
  have hxmax :
      ZArith.BinInt.Z.le (unsigned x) max_unsigned := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval ≤ _
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ modulus - 1
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ modulus at hxlt
    omega
  apply WordCore.ext
  change
    (WordCore.repr wordsize
      (ZArith.BinInt.Z.shiftr (unsigned x) (unsigned zero))).intval = x.intval
  have hz : unsigned zero = Numbers.BinNums.Z.Z0 := by rfl
  rw [hz]
  rw [show ZArith.BinInt.Z.shiftr (unsigned x) Numbers.BinNums.Z.Z0 = unsigned x by
    unfold ZArith.BinInt.Z.shiftr
    change
      (if (0 : Int) ≤ 0 then
          zOfInt ((intOfZ (unsigned x)).ediv (Int.pow 2 (Int.toNat 0)))
        else zOfInt (intOfZ (unsigned x) * Int.pow 2 (-0).toNat)) = unsigned x
    rw [if_pos (by omega)]
    have hp : Int.pow 2 (Int.toNat 0) = 1 := by rfl
    rw [hp]
    exact congrArg zOfInt (Int.ediv_one (intOfZ (unsigned x))) |>.trans
      (zOfInt_intOfZ (unsigned x))]
  change (WordCore.repr wordsize (unsigned x)).intval = x.intval
  have hrepr := unsigned_repr_proof_api (unsigned x) ⟨hx0, hxmax⟩
  exact hrepr

private theorem suffix_val_lt_wordsize (x : int) : x.val < 2 ^ wordsize := by
  have hxnonneg : 0 ≤ intOfZ x.intval := by
    have h := x.intrange.1
    change (-1 : Int) < intOfZ x.intval at h
    omega
  have hxlt : intOfZ x.intval < (Int.ofNat (2 ^ wordsize)) := by
    have h := x.intrange.2
    change intOfZ x.intval < intOfZ (two_power_nat wordsize) at h
    have hp : intOfZ (two_power_nat wordsize) = Int.ofNat (2 ^ wordsize) := by rfl
    rw [hp] at h
    exact h
  have hvalz :
      ZArith.BinInt.Z.of_nat (ZArith.BinInt.Z.to_nat x.intval) = x.intval :=
    ZArith.Znat.Z2Nat.id x.intval (by
      change 0 ≤ intOfZ x.intval
      exact hxnonneg)
  have hint :
      Int.ofNat (ZArith.BinInt.Z.to_nat x.intval) = intOfZ x.intval := by
    have h := congrArg intOfZ hvalz
    simpa only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] using h
  have hnat : ZArith.BinInt.Z.to_nat x.intval = Int.toNat (intOfZ x.intval) := by
    rw [← Int.toNat_of_nonneg hxnonneg] at hint
    exact Int.ofNat.inj hint
  change ZArith.BinInt.Z.to_nat x.intval < 2 ^ wordsize
  rw [hnat]
  exact (Int.toNat_lt hxnonneg).mpr hxlt

private theorem suffix_xor_unsigned (x y : int) :
    unsigned (xor x y) =
      ZArith.BinInt.Z.of_nat (Nat.xor x.val y.val) := by
  have hnlt : Nat.xor x.val y.val < 2 ^ wordsize :=
    Nat.xor_lt_two_pow (suffix_val_lt_wordsize x) (suffix_val_lt_wordsize y)
  have hz0 : ZArith.BinInt.Z.le Numbers.BinNums.Z.Z0
      (ZArith.BinInt.Z.of_nat (Nat.xor x.val y.val)) := by
    change 0 ≤ intOfZ (ZArith.BinInt.Z.of_nat (Nat.xor x.val y.val))
    have hnat : 0 ≤ (Nat.xor x.val y.val : Int) := by omega
    simpa only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt, Int.ofNat_eq_natCast] using hnat
  have hzm : ZArith.BinInt.Z.le
      (ZArith.BinInt.Z.of_nat (Nat.xor x.val y.val)) max_unsigned := by
    change intOfZ (ZArith.BinInt.Z.of_nat (Nat.xor x.val y.val)) ≤ intOfZ max_unsigned
    have hmax : intOfZ max_unsigned = Int.ofNat (2 ^ wordsize) - 1 := by rfl
    rw [hmax]
    simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt, Int.ofNat_eq_natCast]
    omega
  exact unsigned_repr_proof_api
    (ZArith.BinInt.Z.of_nat (Nat.xor x.val y.val)) ⟨hz0, hzm⟩

private theorem suffix_xor_zero_iff_nat (x y : int) :
    xor x y = zero ↔ Nat.xor x.val y.val = 0 := by
  constructor
  · intro h
    have hu := congrArg unsigned h
    rw [suffix_xor_unsigned] at hu
    have hz : unsigned zero = Numbers.BinNums.Z.Z0 := by rfl
    rw [hz] at hu
    have hi := congrArg intOfZ hu
    have hzero : intOfZ Numbers.BinNums.Z.Z0 = (0 : Int) := by rfl
    rw [hzero] at hi
    have hi' : Int.ofNat (Nat.xor x.val y.val) = 0 := by
      simpa only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] using hi
    exact Int.ofNat.inj hi'
  · intro h
    apply WordCore.ext
    change unsigned (xor x y) = unsigned zero
    rw [suffix_xor_unsigned]
    have hz : unsigned zero = Numbers.BinNums.Z.Z0 := by rfl
    rw [hz]
    rw [h]
    rfl

theorem xor_is_zero_proof : xor_is_zero := by
  intro x y
  change decide ((xor x y).intval = zero.intval) = decide (x.intval = y.intval)
  have hiff : (xor x y).intval = zero.intval ↔ x.intval = y.intval := by
    constructor
    · intro h
      have hxy : xor x y = zero := WordCore.ext h
      have hn : Nat.xor x.val y.val = 0 := suffix_xor_zero_iff_nat x y |>.mp hxy
      have hnat : x.val = y.val := by
        apply Nat.eq_of_testBit_eq
        intro i
        have hz : (Nat.xor x.val y.val).testBit i = false := by rw [hn]; simp
        rw [Nat.xor_eq, Nat.testBit_xor] at hz
        by_cases ha : x.val.testBit i = true <;>
          by_cases hb : y.val.testBit i = true <;> simp [ha, hb] at hz ⊢
      have hv : x = y := WordCore.ext_of_val_eq hnat
      exact congrArg (fun q => q.intval) hv
    · intro h
      have hxy : x = y := WordCore.ext h
      have hn : Nat.xor x.val y.val = 0 := by rw [hxy, Nat.xor_eq, Nat.xor_self]
      have hz : xor x y = zero := suffix_xor_zero_iff_nat x y |>.mpr hn
      exact congrArg (fun q => q.intval) hz
  by_cases hp : (xor x y).intval = zero.intval
  · have hq : x.intval = y.intval := hiff.mp hp
    simp [hp, hq]
  · have hq : ¬ x.intval = y.intval := by
      intro hq
      exact hp (hiff.mpr hq)
    simp [hp, hq]

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem suffix_wordcore_neg_val_int (x : int) :
    Int.ofNat (WordCore.neg x).val =
      (-Int.ofNat x.val) % Int.ofNat (2 ^ wordsize) := by
  unfold WordCore.neg
  have hrepr : zOpp (WordCore.unsigned x) =
      zOfInt (-Int.ofNat x.val) := by
    change zOfInt (-intOfZ x.intval) = zOfInt (-Int.ofNat x.val)
    rw [WordCore.intval_eq_zOfNat_val x]
    simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  rw [hrepr, WordCore.val_repr]
  exact Int.toNat_of_nonneg
    (Int.emod_nonneg _ (Int.ne_of_gt
      (Int.natCast_pos.mpr (Nat.two_pow_pos wordsize))))

private theorem suffix_wordcore_mul_val_int (x y : int) :
    Int.ofNat (WordCore.mul x y).val =
      (Int.ofNat x.val * Int.ofNat y.val) % Int.ofNat (2 ^ wordsize) := by
  unfold WordCore.mul
  have hrepr : zMul (WordCore.unsigned x) (WordCore.unsigned y) =
      zOfInt (Int.ofNat x.val * Int.ofNat y.val) := by
    change zOfInt (intOfZ x.intval * intOfZ y.intval) =
      zOfInt (Int.ofNat x.val * Int.ofNat y.val)
    rw [WordCore.intval_eq_zOfNat_val x, WordCore.intval_eq_zOfNat_val y]
    simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  rw [hrepr, WordCore.val_repr]
  exact Int.toNat_of_nonneg
    (Int.emod_nonneg _ (Int.ne_of_gt
      (Int.natCast_pos.mpr (Nat.two_pow_pos wordsize))))

theorem sub_add_opp_proof : sub_add_opp := by
  intro x y
  change WordCore.sub x y = WordCore.add x (WordCore.neg y)
  apply WordCore.ext_of_val_eq
  apply Int.ofNat.inj
  rw [WordCore.sub_val_int, WordCore.add_val_int,
    suffix_wordcore_neg_val_int]
  rw [Int.sub_eq_add_neg, Int.add_emod_emod]

theorem mul_add_distr_r_proof : mul_add_distr_r := by
  intro x y z
  change WordCore.mul x (WordCore.add y z) =
    WordCore.add (WordCore.mul x y) (WordCore.mul x z)
  apply WordCore.ext_of_val_eq
  apply Int.ofNat.inj
  rw [suffix_wordcore_mul_val_int x (WordCore.add y z),
    WordCore.add_val_int y z,
    WordCore.add_val_int (WordCore.mul x y) (WordCore.mul x z),
    suffix_wordcore_mul_val_int x y, suffix_wordcore_mul_val_int x z]
  let m : Int := Int.ofNat (2 ^ wordsize)
  change
    (Int.ofNat x.val * ((Int.ofNat y.val + Int.ofNat z.val) % m)) % m =
      ((Int.ofNat x.val * Int.ofNat y.val) % m +
        (Int.ofNat x.val * Int.ofNat z.val) % m) % m
  calc
    (Int.ofNat x.val * ((Int.ofNat y.val + Int.ofNat z.val) % m)) % m =
        (Int.ofNat x.val % m *
          (((Int.ofNat y.val + Int.ofNat z.val) % m) % m)) % m :=
      Int.mul_emod _ _ _
    _ = (Int.ofNat x.val % m *
          ((Int.ofNat y.val + Int.ofNat z.val) % m)) % m := by
      rw [Int.emod_emod]
    _ = (Int.ofNat x.val * (Int.ofNat y.val + Int.ofNat z.val)) % m :=
      (Int.mul_emod _ _ _).symm
    _ = (Int.ofNat x.val * Int.ofNat y.val +
          Int.ofNat x.val * Int.ofNat z.val) % m := by
      rw [Int.mul_add]
    _ = ((Int.ofNat x.val * Int.ofNat y.val) % m +
          (Int.ofNat x.val * Int.ofNat z.val) % m) % m :=
      Int.add_emod _ _ _

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem shl_zero_proof : shl_zero := by
  intro x
  change WordCore.shl x (WordCore.zero wordsize) = x
  apply WordCore.ext
  change (WordCore.repr wordsize
    (zShiftl (unsigned x) (unsigned (WordCore.zero wordsize)))).intval = x.intval
  have hz : unsigned (WordCore.zero wordsize) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0 := by
    rfl
  rw [hz]
  rw [show zShiftl (unsigned x)
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0 = unsigned x by
    unfold zShiftl CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftl
    rw [show intOfZ Numbers.BinNums.Z.Z0 = 0 by rfl]
    rw [if_pos (by omega)]
    simp only [Int.toNat_zero]
    rw [show Int.pow 2 0 = 1 by rfl]
    simp
    exact zOfInt_intOfZ _]
  change (WordCore.repr wordsize (unsigned x)).intval = x.intval
  have hx0 : ZArith.BinInt.Z.le
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0 (unsigned x) := by
    have h := x.intrange.1
    change (-1 : Int) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval at h
    change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval
    omega
  have hxmax : ZArith.BinInt.Z.le (unsigned x) max_unsigned := by
    have h := x.intrange.2
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ modulus at h
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ max_unsigned
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval ≤
      (2 ^ wordsize : Int) - 1
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval <
      (2 ^ wordsize : Int) at h
    omega
  exact unsigned_repr_proof_api (unsigned x) ⟨hx0, hxmax⟩

theorem swap_cmpu_proof : swap_cmpu := by
  intro c x y
  cases c <;> simp [cmpu, WordCore.cmpu, swap_comparison, WordCore.eq, eq_comm]

private theorem suffix_zshiftr_div (x y : Z)
    (hx : zLe zZero x) (hy : zLe zZero y) :
    zShiftr x y = zDiv x (zTwoP y) := by
  change 0 ≤ intOfZ x at hx
  change 0 ≤ intOfZ y at hy
  have hpow : intOfZ (zTwoP y) =
      Int.pow 2 (Int.toNat (intOfZ y)) := by
    unfold zTwoP two_p CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpower.two_p
    change intOfZ (if intOfZ y < 0 then Numbers.BinNums.Z.Z0 else
      zOfInt (Int.pow (intOfZ (Numbers.BinNums.Z.Zpos (.xO .xH)))
        (Int.toNat (intOfZ y)))) = _
    rw [if_neg (by omega)]
    rw [intOfZ_zOfInt]
    rfl
  apply intOfZ_injective
  simp [zShiftr, zDiv,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftr,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div,
    hx, hy]
  rw [intOfZ_zOfInt, intOfZ_zOfInt]
  rw [hpow]
  change (Int.ediv (intOfZ x) (Int.pow 2 (Int.toNat (intOfZ y)))) =
    (if Int.pow 2 (Int.toNat (intOfZ y)) = 0 then 0
      else if 0 < Int.pow 2 (Int.toNat (intOfZ y)) then
        Int.ediv (intOfZ x) (Int.pow 2 (Int.toNat (intOfZ y)))
      else
        let d := -(Int.pow 2 (Int.toNat (intOfZ y)))
        let q := Int.ediv (intOfZ x) d
        let r := Int.emod (intOfZ x) d
        if r = 0 then -q else -(q + 1))
  have hp : 0 < Int.pow 2 (Int.toNat (intOfZ y)) := by
    exact Int.pow_pos (by omega)
  simp [hp, Int.ne_of_gt hp]

theorem shru_div_two_p_proof : shru_div_two_p := by
  intro x y
  change WordCore.repr wordsize
      (zShiftr (unsigned x) (unsigned y)) =
    WordCore.repr wordsize (zDiv (unsigned x) (zTwoP (unsigned y)))
  have hx : zLe zZero (unsigned x) := by
    have h := x.intrange.1
    change (-1 : Int) < intOfZ x.intval at h
    change 0 ≤ intOfZ x.intval
    omega
  have hy : zLe zZero (unsigned y) := by
    have h := y.intrange.1
    change (-1 : Int) < intOfZ y.intval at h
    change 0 ≤ intOfZ y.intval
    omega
  rw [suffix_zshiftr_div (unsigned x) (unsigned y) hx hy]

theorem eqm_samerepr_proof : eqm_samerepr := by
  intro x y h
  apply WordCore.ext_of_val_eq
  rw [show x = zOfInt (intOfZ x) by exact (zOfInt_intOfZ x).symm,
    show y = zOfInt (intOfZ y) by exact (zOfInt_intOfZ y).symm]
  change (WordCore.repr wordsize (zOfInt (intOfZ x))).val =
    (WordCore.repr wordsize (zOfInt (intOfZ y))).val
  rw [WordCore.val_repr, WordCore.val_repr]
  have hm : intOfZ modulus = (2 ^ wordsize : Int) := by
    unfold modulus
    rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
    rfl
  unfold eqm WordCore.eqm Zbits.eqmod at h
  rcases h with ⟨k, hk⟩
  have hk' := congrArg intOfZ hk
  simp only [zAdd, zMul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
    intOfZ_zOfInt] at hk'
  change intOfZ x = intOfZ k * intOfZ modulus + intOfZ y at hk'
  have hrem : intOfZ x % intOfZ modulus = intOfZ y % intOfZ modulus := by
    rw [hk', Int.add_emod, Int.mul_emod]
    simp
  rw [hm] at hrem
  exact congrArg Int.toNat hrem

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

theorem sub_idem_proof : sub_idem := by
  intro x
  change WordCore.sub x x = WordCore.zero wordsize
  apply WordCore.ext_of_val_eq
  apply Int.ofNat.inj
  rw [WordCore.sub_val_int]
  simp
  rfl

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem suffix_two_p_nonneg (n : Z) (hn : zLe zZero n) :
    zTwoP n = zOfInt (Int.ofNat (2 ^ zToNat n)) := by
  change 0 ≤ intOfZ n at hn
  cases n with
  | Z0 => rfl
  | Zpos exponent =>
      have hexp : ¬(Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat exponent) < 0) := _root_.Int.not_lt.mpr (_root_.Int.natCast_nonneg _)
      simp only [zTwoP, two_p, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpower.two_p, zToNat, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat, CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ, CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat, hexp, if_false]
      apply congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      change (2 : Int) ^ CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat exponent = (2 : Int) ^ CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat exponent
      rfl
  | Zneg exponent =>
      have hpos := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive exponent
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at hn
      omega

private theorem suffix_mask_val (n : Z) (hn : zLe zZero n) :
    (WordCore.repr wordsize (zSub (zTwoP n) zOne)).val = (2 ^ zToNat n - 1) % (2 ^ wordsize) := by
  have htwo := suffix_two_p_nonneg n hn
  have hsub_nat (a b : Nat) (hba : b ≤ a) : zSub (zOfNat a) (zOfNat b) = zOfNat (a - b) := by
    apply intOfZ_injective
    simp only [zSub, ZArith.BinInt.Z.sub, zOfNat, ZArith.BinInt.Z.of_nat, CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    exact (Int.ofNat_sub hba).symm
  have hsub : zSub (zTwoP n) zOne = zOfNat (2 ^ zToNat n - 1) := by
    have hq : 1 ≤ 2 ^ zToNat n := Nat.one_le_two_pow
    have hqrepr : zOfInt (Int.ofNat (2 ^ zToNat n)) = zOfNat (2 ^ zToNat n) := by rfl
    have hOne : zOne = zOfNat 1 := by rfl
    rw [htwo, hqrepr, hOne, hsub_nat _ _ hq]
  rw [hsub]
  change (WordCore.repr wordsize (zOfNat (2 ^ zToNat n - 1))).val = _
  have hznat : zOfNat (2 ^ zToNat n - 1) = zOfInt (Int.ofNat (2 ^ zToNat n - 1)) := by rfl
  rw [hznat, WordCore.val_repr_residue, WordCore.residue_zOfNat]

private theorem suffix_and_val (x y : int) : (WordCore.and x y).val = Nat.land x.val y.val := by
  unfold WordCore.and
  have hz : zOfNat (Nat.land x.val y.val) = zOfInt (Int.ofNat (Nat.land x.val y.val)) := by rfl
  rw [hz, WordCore.val_repr_residue, WordCore.residue_zOfNat]
  exact Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ (WordCore.val_lt y))

private theorem suffix_nat_zero_ext_and (a k w : Nat) (ha : a < 2 ^ w) : (a % (2 ^ k)) % (2 ^ w) = Nat.land a ((2 ^ k - 1) % (2 ^ w)) := by
  by_cases hkw : k ≤ w
  · have hpow : 2 ^ k ≤ 2 ^ w := Nat.pow_le_pow_right Nat.zero_lt_two hkw
    have hklt : 2 ^ k - 1 < 2 ^ w := by omega
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos k)) hpow), Nat.mod_eq_of_lt hklt]
    exact (Nat.and_two_pow_sub_one_eq_mod a k).symm
  · have hwk : w ≤ k := Nat.le_of_not_ge hkw
    have hpow : 2 ^ w ≤ 2 ^ k := Nat.pow_le_pow_right Nat.zero_lt_two hwk
    have h1 : a % (2 ^ k) = a := Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ha hpow)
    have h2 : a % (2 ^ w) = a := Nat.mod_eq_of_lt ha
    rw [h1, h2]
    have hmask : (2 ^ k - 1) % (2 ^ w) = 2 ^ w - 1 := by
      have hpoww : 0 < 2 ^ w := Nat.two_pow_pos w
      have hpowd : 0 < 2 ^ (k - w) := Nat.two_pow_pos _
      have hkpow : 2 ^ k = 2 ^ w * 2 ^ (k - w) := by rw [← Nat.pow_add]; congr 1; omega
      have hdecomp : 2 ^ k - 1 = 2 ^ w * (2 ^ (k - w) - 1) + (2 ^ w - 1) := by
        rw [hkpow, Nat.mul_sub_left_distrib]
        have hmul : 2 ^ w ≤ 2 ^ w * 2 ^ (k - w) := Nat.le_mul_of_pos_right _ hpowd
        omega
      rw [hdecomp, Nat.add_comm, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmask]
    exact (Nat.and_two_pow_sub_one_of_lt_two_pow ha).symm

theorem zero_ext_and_proof : zero_ext_and := by
  intro n x hn
  change WordCore.zero_ext n x = WordCore.and x (WordCore.repr wordsize (zSub (zTwoP n) zOne))
  apply WordCore.ext_of_val_eq
  change (zero_ext n x).val = (WordCore.and x (WordCore.repr wordsize (zSub (zTwoP n) zOne))).val
  rw [zero_ext_val n x hn, suffix_and_val, suffix_mask_val n hn]
  exact suffix_nat_zero_ext_and x.val (zToNat n) wordsize (WordCore.val_lt x)

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

theorem unsigned_repr_wordsize_proof : unsigned_repr_wordsize := by
  unfold unsigned_repr_wordsize iwordsize zwordsize
  apply unsigned_repr_proof_api
  constructor
  · change (0 : Int) ≤ 32
    omega
  · change (32 : Int) ≤ (2 ^ wordsize : Int) - 1
    decide

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem ltu_inv_proof : ltu_inv := by
  intro x y h
  change zltSelect (unsigned x) (unsigned y) true false = true at h
  cases hlt : CompCert4Lean.Lib.Coqlib.zlt (unsigned x) (unsigned y) with
  | left hxy =>
      simp [zltSelect, sumboolSelect, hlt] at h
      constructor
      · have hx := x.intrange.1
        change (-1 : Int) < intOfZ (unsigned x) at hx
        change 0 ≤ intOfZ (unsigned x)
        omega
      · exact hxy
  | right hxy =>
      simp [zltSelect, sumboolSelect, hlt] at h

theorem add_assoc_proof : add_assoc := by
  intro x y z
  change WordCore.add (WordCore.add x y) z = WordCore.add x (WordCore.add y z)
  apply WordCore.ext_of_val_eq
  rw [WordCore.add_val, WordCore.add_val, WordCore.add_val, WordCore.add_val]
  rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

private theorem signed_injective_try {x y : int} (h : signed x = signed y) : x = y := by
  dsimp [signed, WordCore.signed] at h
  simp [zltSelect, sumboolSelect] at h
  split at h <;> split at h
  · apply WordCore.ext
    exact h
  · exfalso
    have hx0 : 0 ≤ intOfZ (unsigned x) := by
      have hx := x.intrange.1
      change (-1 : Int) < intOfZ (unsigned x) at hx
      omega
    have hymod := y.intrange.2
    change intOfZ (unsigned y) < intOfZ modulus at hymod
    change intOfZ (unsigned y) < intOfZ (zTwoPowerNat wordsize) at hymod
    have hh := congrArg intOfZ h
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hh
    have hmod : intOfZ (zTwoPowerNat wordsize) = (2 ^ wordsize : Int) := by
      rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
      rfl
    rw [hmod] at hymod hh
    have hh' : intOfZ (unsigned x) =
        intOfZ (unsigned y) - (2 ^ wordsize : Int) := by
      exact hh
    have hneg : intOfZ (unsigned y) - (2 ^ wordsize : Int) < 0 := by
      omega
    rw [← hh'] at hneg
    exact (Int.not_lt_of_ge hx0 hneg).elim
  · exfalso
    have hy0 : 0 ≤ intOfZ (unsigned y) := by
      have hy := y.intrange.1
      change (-1 : Int) < intOfZ (unsigned y) at hy
      omega
    have hxmod := x.intrange.2
    change intOfZ (unsigned x) < intOfZ modulus at hxmod
    change intOfZ (unsigned x) < intOfZ (zTwoPowerNat wordsize) at hxmod
    have hh := congrArg intOfZ h
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hh
    have hmod : intOfZ (zTwoPowerNat wordsize) = (2 ^ wordsize : Int) := by
      rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
      rfl
    rw [hmod] at hxmod hh
    have hh' : intOfZ (unsigned x) - (2 ^ wordsize : Int) =
        intOfZ (unsigned y) := by
      exact hh
    have hneg : intOfZ (unsigned x) - (2 ^ wordsize : Int) < 0 := by
      omega
    rw [hh'] at hneg
    exact (Int.not_lt_of_ge hy0 hneg).elim
  · have hh := congrArg intOfZ h
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hh
    have hmod : intOfZ (zTwoPowerNat wordsize) = (2 ^ wordsize : Int) := by
      rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
      rfl
    rw [hmod] at hh
    have hu : unsigned x = unsigned y := by
      apply intOfZ_injective
      exact (Int.sub_left_inj _).mp hh
    apply WordCore.ext
    exact hu

theorem lt_not_proof : lt_not := by
  intro x y
  by_cases hxy : x = y
  · subst y
    cases h : CompCert4Lean.Lib.Coqlib.zlt (signed x) (signed x) with
    | left hlt => exact (Int.lt_irrefl _ hlt).elim
    | right hge =>
        change zltSelect (signed x) (signed x) true false =
          (!zltSelect (signed x) (signed x) true false && !eq x x)
        simp only [zltSelect, sumboolSelect]
        rw [h]
        simp [eq, WordCore.eq]
  · have heq : eq x y = false := by
      have hxy' : x.intval ≠ y.intval := by
        intro hval
        apply hxy
        exact WordCore.ext hval
      simp [eq, WordCore.eq, hxy']
    cases h1 : CompCert4Lean.Lib.Coqlib.zlt (signed y) (signed x) with
    | left h1lt =>
        cases h2 : CompCert4Lean.Lib.Coqlib.zlt (signed x) (signed y) with
        | left h2lt => exact (Int.lt_asymm h1lt h2lt).elim
        | right h2ge =>
            change zltSelect (signed y) (signed x) true false =
              (!zltSelect (signed x) (signed y) true false && !eq x y)
            simp only [zltSelect, sumboolSelect]
            rw [h1, h2]
            simp [heq]
    | right h1ge =>
        cases h2 : CompCert4Lean.Lib.Coqlib.zlt (signed x) (signed y) with
        | left h2lt =>
            change zltSelect (signed y) (signed x) true false =
              (!zltSelect (signed x) (signed y) true false && !eq x y)
            simp only [zltSelect, sumboolSelect]
            rw [h1, h2]
            simp [heq]
        | right h2ge =>
            have hs : signed x = signed y := intOfZ_injective
              (Int.le_antisymm h1ge h2ge)
            exact (hxy (signed_injective_try hs)).elim

theorem shru_lt_zero_proof : shru_lt_zero := by
  intro x
  rw [shru_div_two_p_proof]
  have hy : unsigned (repr (zSub zwordsize zOne)) = zSub zwordsize zOne := by
    apply unsigned_repr_proof_api
    constructor
    · change (0 : Int) ≤ 31
      omega
    · change (31 : Int) ≤ (2 ^ wordsize : Int) - 1
      decide
  rw [hy]
  by_cases hlt : lt x zero = true
  · simp [hlt]
    have hn : zLe zZero (zSub zwordsize zOne) := by
      change (0 : Int) ≤ 31
      omega
    have hpow := suffix_two_p_nonneg (zSub zwordsize zOne) hn
    have hnval : zToNat (zSub zwordsize zOne) = wordsize - 1 := by
      decide
    have hpow' : zTwoP (zSub zwordsize zOne) =
        zOfInt (Int.ofNat (2 ^ (wordsize - 1))) := by
      simpa [hnval] using hpow
    rw [hpow']
    have hq : zDiv (unsigned x)
        (zOfInt (Int.ofNat (2 ^ (wordsize - 1)))) = zOne := by
      apply intOfZ_injective
      simp only [zDiv,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div]
      rw [intOfZ_zOfInt]
      change Int.ediv (intOfZ (unsigned x))
          (Int.ofNat (2 ^ (wordsize - 1))) = 1
      have hslt : zLt (signed x) (signed zero) := by
        change zltSelect (signed x) (signed zero) true false = true at hlt
        cases hs : CompCert4Lean.Lib.Coqlib.zlt (signed x) (signed zero) with
        | left hs' => exact hs'
        | right hs' => simp [zltSelect, sumboolSelect, hs] at hlt
      have hz : signed zero = zZero := by
        rfl
      rw [hz] at hslt
      have hxr : intOfZ (unsigned x) ≥ (2 ^ (wordsize - 1) : Int) := by
        cases hx : CompCert4Lean.Lib.Coqlib.zlt (unsigned x) half_modulus with
        | left hx' =>
            exfalso
            have hx0 : 0 ≤ intOfZ (unsigned x) := by
              have h := x.intrange.1
              change (-1 : Int) < intOfZ (unsigned x) at h
              omega
            have hxs : signed x = unsigned x := by
              unfold signed
              dsimp [WordCore.signed]
              simp only [zltSelect, sumboolSelect]
              have hx'' : CompCert4Lean.Lib.Coqlib.zlt
                  (WordCore.unsigned x) (zTwoPowerNat (wordsize - 1)) =
                  Foundation.Logic.Support.Sumbool.left hx' := by
                exact hx
              rw [hx'']
              rfl
            rw [hxs] at hslt
            change intOfZ (unsigned x) < 0 at hslt
            omega
        | right hx' =>
            change intOfZ (unsigned x) ≥ intOfZ half_modulus at hx'
            have hh : intOfZ half_modulus = (2 ^ (wordsize - 1) : Int) := by
              unfold half_modulus
              rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
              rfl
            rw [hh] at hx'
            exact hx'
      have hxmod : intOfZ (unsigned x) < (2 ^ wordsize : Int) := by
        have h := x.intrange.2
        change intOfZ (unsigned x) < intOfZ modulus at h
        have hm : intOfZ modulus = (2 ^ wordsize : Int) := by
          unfold modulus
          rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
          rfl
        rw [hm] at h
        exact h
      have hdpos : (0 : Int) < Int.ofNat (2 ^ (wordsize - 1)) := by
        exact Int.natCast_pos.mpr (Nat.two_pow_pos _)
      have hpowrel : (2 ^ wordsize : Int) =
          2 * Int.ofNat (2 ^ (wordsize - 1)) := by
        decide
      have hqge : (1 : Int) ≤ Int.ediv (intOfZ (unsigned x))
          (Int.ofNat (2 ^ (wordsize - 1))) := by
        apply (Int.le_ediv_iff_mul_le hdpos).2
        simpa using hxr
      have hqlt : Int.ediv (intOfZ (unsigned x))
          (Int.ofNat (2 ^ (wordsize - 1))) < 2 := by
        apply (Int.ediv_lt_iff_lt_mul hdpos).2
        rw [hpowrel] at hxmod
        omega
      omega
    change WordCore.repr wordsize
        (zDiv (unsigned x) (zOfInt (Int.ofNat (2 ^ (wordsize - 1))))) =
      WordCore.repr wordsize zOne
    rw [hq]
  · simp [hlt]
    have hn : zLe zZero (zSub zwordsize zOne) := by
      change (0 : Int) ≤ 31
      omega
    have hpow := suffix_two_p_nonneg (zSub zwordsize zOne) hn
    have hnval : zToNat (zSub zwordsize zOne) = wordsize - 1 := by
      decide
    have hpow' : zTwoP (zSub zwordsize zOne) =
        zOfInt (Int.ofNat (2 ^ (wordsize - 1))) := by
      simpa [hnval] using hpow
    rw [hpow']
    have hq : zDiv (unsigned x)
        (zOfInt (Int.ofNat (2 ^ (wordsize - 1)))) = zZero := by
      apply intOfZ_injective
      simp only [zDiv,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div]
      rw [intOfZ_zOfInt]
      change Int.ediv (intOfZ (unsigned x))
          (Int.ofNat (2 ^ (wordsize - 1))) = 0
      have hsge : zLe zZero (signed x) := by
        have hlt' := hlt
        change ¬(zltSelect (signed x) (signed zero) true false = true) at hlt'
        cases hs : CompCert4Lean.Lib.Coqlib.zlt (signed x) (signed zero) with
        | left hs' => simp [zltSelect, sumboolSelect, hs] at hlt'
        | right hs' =>
            change intOfZ (signed x) ≥ intOfZ (signed zero) at hs'
            have hz : signed zero = zZero := by rfl
            rw [hz] at hs'
            exact hs'
      have hxl : intOfZ (unsigned x) < (2 ^ (wordsize - 1) : Int) := by
        cases hx : CompCert4Lean.Lib.Coqlib.zlt (unsigned x) half_modulus with
        | left hx' =>
            change intOfZ (unsigned x) < intOfZ half_modulus at hx'
            have hh : intOfZ half_modulus = (2 ^ (wordsize - 1) : Int) := by
              unfold half_modulus
              rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
              rfl
            rw [hh] at hx'
            exact hx'
        | right hx' =>
            exfalso
            have hxs : signed x = zSub (unsigned x) modulus := by
              unfold signed WordCore.signed
              simp only [zltSelect, sumboolSelect]
              have hx'' : CompCert4Lean.Lib.Coqlib.zlt
                  (WordCore.unsigned x) (zTwoPowerNat (wordsize - 1)) =
                  Foundation.Logic.Support.Sumbool.right hx' := by
                exact hx
              rw [hx'']
              rfl
            rw [hxs] at hsge
            change intOfZ (zSub (unsigned x) modulus) ≥ 0 at hsge
            have hxmod := x.intrange.2
            change intOfZ (unsigned x) < intOfZ modulus at hxmod
            have hm : intOfZ modulus = (2 ^ wordsize : Int) := by
              unfold modulus
              rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
              rfl
            have hh : intOfZ half_modulus = (2 ^ (wordsize - 1) : Int) := by
              unfold half_modulus
              rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
              rfl
            have hxge : intOfZ (unsigned x) ≥ intOfZ half_modulus := hx'
            rw [hm] at hxmod
            rw [hh] at hxge
            have hsge' := hsge
            simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hsge'
            rw [hm] at hsge'
            omega
      have hx0 : 0 ≤ intOfZ (unsigned x) := by
        have h := x.intrange.1
        change (-1 : Int) < intOfZ (unsigned x) at h
        omega
      exact Int.ediv_eq_zero_of_lt hx0 hxl
    change WordCore.repr wordsize
        (zDiv (unsigned x) (zOfInt (Int.ofNat (2 ^ (wordsize - 1))))) =
      WordCore.repr wordsize zZero
    rw [hq]

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem add_zero_proof : add_zero := by
  intro x
  change WordCore.add x (WordCore.zero wordsize) = x
  apply WordCore.ext_of_val_eq
  rw [WordCore.add_val]
  change (x.val + 0) % (2 ^ wordsize) = x.val
  rw [Nat.add_zero, Nat.mod_eq_of_lt (WordCore.val_lt x)]

theorem eq_sym_proof : eq_sym := by
  intro x y
  change decide (x.intval = y.intval) = decide (y.intval = x.intval)
  by_cases h : x.intval = y.intval
  · simp [h]
  · have h' : ¬ y.intval = x.intval := by
      intro hyx
      exact h hyx.symm
    simp [h, h']

theorem not_ltu_proof : not_ltu := by
  intro x y
  change !(zltSelect (unsigned y) (unsigned x) true false) =
    (zltSelect (unsigned x) (unsigned y) true false ||
      decide (x.intval = y.intval))
  cases hxy : CompCert4Lean.Lib.Coqlib.zlt (unsigned y) (unsigned x) with
  | left hlt =>
      cases hrev : CompCert4Lean.Lib.Coqlib.zlt (unsigned x) (unsigned y) with
      | left hrevlt =>
          exact (Int.lt_asymm hlt hrevlt).elim
      | right hrevge =>
          have hne : x.intval ≠ y.intval := by
            intro heq
            have hlt' : intOfZ (unsigned y) < intOfZ (unsigned x) := hlt
            change intOfZ y.intval < intOfZ x.intval at hlt'
            rw [heq] at hlt'
            exact (Int.lt_irrefl _ hlt').elim
          have heq : eq x y = false := by
            change decide (x.intval = y.intval) = false
            simp [hne]
          simp [zltSelect, sumboolSelect, hxy, hrev, heq, hne]
  | right hge =>
      cases hrev : CompCert4Lean.Lib.Coqlib.zlt (unsigned x) (unsigned y) with
      | left hrevlt =>
          simp [zltSelect, sumboolSelect, hxy, hrev]
      | right hrevge =>
          have hge' : intOfZ (unsigned x) ≤ intOfZ (unsigned y) := by
            change intOfZ (unsigned x) ≤ intOfZ (unsigned y)
            exact hge
          have hrevge' : intOfZ (unsigned y) ≤ intOfZ (unsigned x) := by
            change intOfZ (unsigned y) ≤ intOfZ (unsigned x)
            exact hrevge
          have huv : unsigned y = unsigned x := by
            apply intOfZ_injective
            exact Int.le_antisymm hrevge' hge'
          have heqv : x.intval = y.intval := by
            simpa only [unsigned, WordCore.unsigned] using huv.symm
          have heq : eq x y = true := by
            change decide (x.intval = y.intval) = true
            rw [heqv]
            simp
          simp [zltSelect, sumboolSelect, hxy, hrev, heq, heqv]

theorem and_mone_proof : and_mone := by
  intro x
  apply WordCore.ext_of_val_eq
  change (WordCore.and x (WordCore.mone wordsize)).val = x.val
  rw [suffix_and_val]
  unfold WordCore.mone
  rw [WordCore.val_repr_residue]
  have hz : zOpp zOne = CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (-1) := by
    rfl
  rw [hz, WordCore.residue_zOfInt]
  have hmask : ((-1 : Int) % Int.ofNat (2 ^ wordsize)).toNat =
      2 ^ wordsize - 1 := by
    change ((-1 : Int) % Int.ofNat (2 ^ 32)).toNat = 2 ^ 32 - 1
    decide
  change x.val.land ((-1 % Int.ofNat (2 ^ wordsize)).toNat) = x.val
  rw [hmask]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow (WordCore.val_lt x)

theorem repr_unsigned_proof : repr_unsigned := by
  intro i
  have hnonneg : zLe zZero (unsigned i) := by
    have h := i.intrange.1
    change (-1 : Int) < intOfZ (unsigned i) at h
    change 0 ≤ intOfZ (unsigned i)
    omega
  have hlt : zLt (unsigned i) modulus := i.intrange.2
  have hmax : zLe (unsigned i) max_unsigned := by
    change intOfZ (unsigned i) ≤ intOfZ max_unsigned
    change intOfZ (unsigned i) < intOfZ modulus at hlt
    change intOfZ (unsigned i) < (2 ^ wordsize : Int) at hlt
    change intOfZ (unsigned i) ≤ (2 ^ wordsize : Int) - 1
    omega
  apply WordCore.ext
  exact unsigned_repr_proof_api (unsigned i) ⟨hnonneg, hmax⟩

theorem and_commut_proof : and_commut := by
  intro x y
  apply WordCore.ext_of_val_eq
  change (WordCore.and x y).val = (WordCore.and y x).val
  rw [suffix_and_val, suffix_and_val, Nat.land_eq, Nat.land_eq, Nat.and_comm]

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem suffix_shl_val (x y : int) :
    (WordCore.shl x y).val = (x.val * 2 ^ y.val) % (2 ^ wordsize) := by
  change (WordCore.repr wordsize
    (zShiftl (unsigned x) (unsigned y))).val = _
  have hunsigned (w : int) :
      unsigned w = zOfNat w.val := by
    have hw : zLe zZero (unsigned w) := by
      have h := w.intrange.1
      change (-1 : Int) < intOfZ (unsigned w) at h
      change 0 ≤ intOfZ (unsigned w)
      omega
    exact (ZArith.Znat.Z2Nat.id (unsigned w) hw).symm
  rw [hunsigned x, hunsigned y]
  rw [show zShiftl (zOfNat x.val) (zOfNat y.val) =
      zOfNat (x.val * 2 ^ y.val) by
    unfold zShiftl ZArith.BinInt.Z.shiftl
    simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
      Int.ofNat_eq_natCast, Int.natCast_nonneg, ↓reduceIte]
    rw [Int.natCast_mul, Int.natCast_pow]
    rfl]
  rw [WordCore.val_repr_residue]
  have hz : zOfNat (x.val * 2 ^ y.val) =
      zOfInt (Int.ofNat (x.val * 2 ^ y.val)) := by rfl
  rw [hz, WordCore.residue_zOfNat]

private theorem suffix_shl_and (x m y : int) :
    shl (and x m) y = and (shl x y) (shl m y) := by
  change WordCore.shl (WordCore.and x m) y =
    WordCore.and (WordCore.shl x y) (WordCore.shl m y)
  apply WordCore.ext_of_val_eq
  rw [suffix_shl_val, suffix_and_val]
  rw [suffix_and_val (WordCore.shl x y) (WordCore.shl m y)]
  rw [suffix_shl_val x y, suffix_shl_val m y]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.land_eq]
  rw [Nat.testBit_mod_two_pow]
  rw [Nat.testBit_and]
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq]
  rw [Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
  rw [Nat.testBit_and]
  by_cases hi : i < wordsize
  · by_cases hshift : decide (y.val ≤ i) = true
    · simp [hi, hshift, Bool.and_assoc]
    · simp [hi, hshift, Bool.and_assoc]
  · simp [hi]

theorem bitfield_insert_alternative_proof : bitfield_insert_alternative := by
  dsimp [bitfield_insert_alternative]
  intro pos width n p hwidth
  let mask := shl (repr (zSub (zTwoP width) zOne)) (repr pos)
  change or (shl (zero_ext width p) (repr pos)) (and n (not mask)) =
    or (and (shl p (repr pos)) mask) (and n (not mask))
  rw [zero_ext_and_proof width p hwidth]
  exact congrArg (fun q => or q (and n (not mask)))
    (suffix_shl_and p (repr (zSub (zTwoP width) zOne)) (repr pos))

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem suffix_zshiftr_div_any (x y : Z) (hy : zLe zZero y) :
    zShiftr x y = zDiv x (zTwoP y) := by
  change 0 ≤ intOfZ y at hy
  have hpow : intOfZ (zTwoP y) =
      Int.pow 2 (Int.toNat (intOfZ y)) := by
    unfold zTwoP two_p CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpower.two_p
    change intOfZ (if intOfZ y < 0 then Numbers.BinNums.Z.Z0 else
      zOfInt (Int.pow 2 (Int.toNat (intOfZ y)))) = _
    rw [if_neg (by omega)]
    rw [intOfZ_zOfInt]
  apply intOfZ_injective
  simp [zShiftr, zDiv,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftr,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div, hy]
  rw [intOfZ_zOfInt, intOfZ_zOfInt, hpow]
  change Int.ediv (intOfZ x) (Int.pow 2 (Int.toNat (intOfZ y))) =
    (if Int.pow 2 (Int.toNat (intOfZ y)) = 0 then 0
      else if 0 < Int.pow 2 (Int.toNat (intOfZ y)) then
        Int.ediv (intOfZ x) (Int.pow 2 (Int.toNat (intOfZ y)))
      else
        let d := -(Int.pow 2 (Int.toNat (intOfZ y)))
        let q := Int.ediv (intOfZ x) d
        let r := Int.emod (intOfZ x) d
        if r = 0 then -q else -(q + 1))
  have hp : 0 < Int.pow 2 (Int.toNat (intOfZ y)) := by
    exact Int.pow_pos (by omega)
  simp [hp, Int.ne_of_gt hp]

theorem shr_div_two_p_proof : shr_div_two_p := by
  intro x y
  change WordCore.repr wordsize
      (zShiftr (signed x) (unsigned y)) =
    WordCore.repr wordsize (zDiv (signed x) (zTwoP (unsigned y)))
  have hy : zLe zZero (unsigned y) := by
    have h := y.intrange.1
    change (-1 : Int) < intOfZ y.intval at h
    change 0 ≤ intOfZ y.intval
    omega
  rw [suffix_zshiftr_div_any (signed x) (unsigned y) hy]

private theorem suffix_or_val (x y : int) :
    (WordCore.or x y).val = Nat.lor x.val y.val := by
  unfold WordCore.or
  have hz : zOfNat (Nat.lor x.val y.val) =
      zOfInt (Int.ofNat (Nat.lor x.val y.val)) := by rfl
  rw [hz, WordCore.val_repr_residue, WordCore.residue_zOfNat]
  exact Nat.mod_eq_of_lt
    (Nat.or_lt_two_pow (WordCore.val_lt x) (WordCore.val_lt y))

private theorem suffix_not_val (x : int) :
    (WordCore.not x).val = Nat.xor x.val (2 ^ wordsize - 1) := by
  unfold WordCore.not
  have hz : zOfNat (Nat.xor x.val (2 ^ wordsize - 1)) =
      zOfInt (Int.ofNat (Nat.xor x.val (2 ^ wordsize - 1))) := by rfl
  rw [hz, WordCore.val_repr_residue, WordCore.residue_zOfNat]
  apply Nat.mod_eq_of_lt
  apply Nat.xor_lt_two_pow (WordCore.val_lt x)
  have hpow : 0 < 2 ^ wordsize := Nat.two_pow_pos wordsize
  omega

private theorem suffix_nat_not_or (x y n : Nat)
    (hxlt : x < 2 ^ n) (hylt : y < 2 ^ n) :
    Nat.xor (Nat.lor x y) (2 ^ n - 1) =
      Nat.land (Nat.xor x (2 ^ n - 1)) (Nat.xor y (2 ^ n - 1)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.xor_eq, Nat.lor_eq, Nat.land_eq]
  rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and]
  rw [Nat.testBit_xor, Nat.testBit_xor]
  rw [Nat.testBit_two_pow_sub_one]
  by_cases hi : i < n
  · by_cases hx : x.testBit i = true <;>
      by_cases hy : y.testBit i = true <;> simp [hi, hx, hy]
  · have hni : n ≤ i := Nat.le_of_not_gt hi
    have hpow : 2 ^ n ≤ 2 ^ i :=
      Nat.pow_le_pow_right Nat.zero_lt_two hni
    have hxi : x < 2 ^ i := Nat.lt_of_lt_of_le hxlt hpow
    have hyi : y < 2 ^ i := Nat.lt_of_lt_of_le hylt hpow
    rw [Nat.testBit_lt_two_pow hxi, Nat.testBit_lt_two_pow hyi]
    simp [hi]

theorem not_or_and_not_proof : not_or_and_not := by
  intro x y
  apply WordCore.ext_of_val_eq
  change (WordCore.not (WordCore.or x y)).val =
    (WordCore.and (WordCore.not x) (WordCore.not y)).val
  rw [suffix_not_val, suffix_or_val, suffix_and_val,
    suffix_not_val, suffix_not_val]
  exact suffix_nat_not_or x.val y.val wordsize
    (WordCore.val_lt x) (WordCore.val_lt y)

theorem divu_one_proof : divu_one := by
  intro x
  change WordCore.repr wordsize
      (zDiv (unsigned x) (unsigned one)) = x
  have hone : unsigned one = zOne := by rfl
  rw [hone]
  have hdiv : zDiv (unsigned x) zOne = unsigned x := by
    apply intOfZ_injective
    simp only [zDiv, ZArith.BinInt.Z.div, intOfZ_zOfInt]
    change (intOfZ (unsigned x)).ediv 1 = intOfZ (unsigned x)
    exact Int.ediv_one _
  rw [hdiv]
  exact repr_unsigned_proof x

theorem signed_range_proof : signed_range := by
  intro x
  unfold signed WordCore.signed
  cases hlt : CompCert4Lean.Lib.Coqlib.zlt
      (WordCore.unsigned x) (zTwoPowerNat (wordsize - 1)) with
  | left h =>
      simp only [zltSelect, sumboolSelect, hlt]
      constructor
      · have hx0 : 0 ≤ intOfZ (unsigned x) := by
          have hx := x.intrange.1
          change (-1 : Int) < intOfZ (unsigned x) at hx
          omega
        change intOfZ min_signed ≤ intOfZ (unsigned x)
        change (-2147483648 : Int) ≤ intOfZ (unsigned x)
        omega
      · change intOfZ (unsigned x) ≤ intOfZ max_signed
        change intOfZ (unsigned x) < intOfZ half_modulus at h
        change intOfZ (unsigned x) < (2147483648 : Int) at h
        change intOfZ (unsigned x) ≤ (2147483647 : Int)
        omega
  | right h =>
      simp only [zltSelect, sumboolSelect, hlt]
      have hxlt := x.intrange.2
      change intOfZ (unsigned x) < intOfZ modulus at hxlt
      change intOfZ (unsigned x) < (4294967296 : Int) at hxlt
      change intOfZ half_modulus ≤ intOfZ (unsigned x) at h
      change (2147483648 : Int) ≤ intOfZ (unsigned x) at h
      constructor
      · change intOfZ min_signed ≤ intOfZ (zSub (unsigned x) modulus)
        simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
        change (-2147483648 : Int) ≤
          intOfZ (unsigned x) - (4294967296 : Int)
        omega
      · change intOfZ (zSub (unsigned x) modulus) ≤ intOfZ max_signed
        simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
        change intOfZ (unsigned x) - (4294967296 : Int) ≤
          (2147483647 : Int)
        omega

private theorem suffix_shru_val (x y : int) :
    (shru x y).val = x.val / 2 ^ y.val := by
  unfold shru WordCore.shru
  change (WordCore.repr wordsize
      (ZArith.BinInt.Z.shiftr x.intval y.intval)).val = _
  rw [WordCore.intval_eq_zOfNat_val x, WordCore.intval_eq_zOfNat_val y]
  have hshift : ZArith.BinInt.Z.shiftr (zOfNat x.val) (zOfNat y.val) =
      zOfNat (x.val / 2 ^ y.val) := by
    unfold ZArith.BinInt.Z.shiftr
    simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
      Int.ofNat_eq_natCast, Int.natCast_nonneg, ↓reduceIte,
      Int.toNat_natCast, Int.natCast_pow]
    exact congrArg zOfInt Int.ofNat_ediv_ofNat
  rw [hshift, WordCore.val_repr_residue]
  have hzof : zOfNat (x.val / 2 ^ y.val) =
      zOfInt (Int.ofNat (x.val / 2 ^ y.val)) := by rfl
  rw [hzof, WordCore.residue_zOfNat]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt (Nat.div_le_self x.val _) (WordCore.val_lt x)

private theorem suffix_ltu_iwordsize_val (n : int)
    (h : ltu n iwordsize = true) : n.val < wordsize := by
  have hlt := (ltu_inv_proof n iwordsize h).2
  change ZArith.BinInt.Z.lt n.intval iwordsize.intval at hlt
  rw [WordCore.intval_eq_zOfNat_val n,
    WordCore.intval_eq_zOfNat_val iwordsize] at hlt
  have hi : iwordsize.val = wordsize := rfl
  rw [hi] at hlt
  change intOfZ (ZArith.BinInt.Z.of_nat n.val) <
    intOfZ (ZArith.BinInt.Z.of_nat wordsize) at hlt
  rw [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
    ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hlt
  exact Int.ofNat_lt.mp hlt

theorem shru_shru_proof : shru_shru := by
  intro x y z hy hz _hsum
  have hyv := suffix_ltu_iwordsize_val y hy
  have hzv := suffix_ltu_iwordsize_val z hz
  have hyzlt : y.val + z.val < 2 ^ wordsize := by
    change y.val < 32 at hyv
    change z.val < 32 at hzv
    change y.val + z.val < 2 ^ 32
    omega
  apply WordCore.ext_of_val_eq
  rw [suffix_shru_val, suffix_shru_val, suffix_shru_val]
  change x.val / 2 ^ y.val / 2 ^ z.val =
    x.val / 2 ^ (WordCore.add y z).val
  rw [WordCore.add_val, Nat.mod_eq_of_lt hyzlt]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

private def suffixSignStep : (Z → Z) → Z → Z :=
  fun rec y => CompCert4Lean.Lib.Zbits.Zshiftin
    (ZArith.BinInt.Z.odd y) (rec (ZArith.BinInt.Z.div2 y))

private def suffixSignBase : Z → Z :=
  fun y => if ZArith.BinInt.Z.odd y then zOpp zOne else zZero

private theorem suffix_intOfZ_shiftin (b : Bool) (x : Z) :
    intOfZ (CompCert4Lean.Lib.Zbits.Zshiftin b x) =
      2 * intOfZ x + if b then 1 else 0 := by
  rw [CompCert4Lean.Lib.Zbits.Zshiftin_spec]
  simp only [zAdd, zMul, ZArith.BinInt.Z.add,
    ZArith.BinInt.Z.mul, intOfZ_zOfInt]
  cases b <;> rfl

private theorem suffix_odd_zOfNat (a : Nat) :
    ZArith.BinInt.Z.odd (zOfNat a) = decide (a % 2 = 1) := by
  unfold ZArith.BinInt.Z.odd ZArith.BinInt.Z.even
  rw [zNatAbs_nat]
  have hrange := Nat.mod_lt a (by decide : 0 < 2)
  by_cases h : a % 2 = 1
  · simp [h]
  · have hz : a % 2 = 0 := by omega
    simp [h, hz]

private theorem suffix_sign_iter_nat (k a : Nat) :
    intOfZ (ZArith.BinInt.Z.iter (zOfNat k)
      suffixSignStep suffixSignBase (zOfNat a)) =
      if a % (2 ^ (k + 1)) < 2 ^ k then
        Int.ofNat (a % (2 ^ (k + 1)))
      else
        Int.ofNat (a % (2 ^ (k + 1))) - Int.ofNat (2 ^ (k + 1)) := by
  induction k generalizing a with
  | zero =>
      change intOfZ (suffixSignBase (zOfNat a)) = _
      unfold suffixSignBase
      rw [suffix_odd_zOfNat]
      by_cases h : a % 2 = 1
      · have hr : a % 2 = 1 := h
        simp [suffixSignBase, h, hr]
        rfl
      · have hr : a % 2 = 0 := by omega
        simp [suffixSignBase, h, hr]
        rfl
  | succ k ih =>
      rw [ziter_succ suffixSignStep suffixSignBase k]
      change intOfZ (CompCert4Lean.Lib.Zbits.Zshiftin
        (ZArith.BinInt.Z.odd (zOfNat a))
        (ZArith.BinInt.Z.iter (zOfNat k) suffixSignStep suffixSignBase
          (ZArith.BinInt.Z.div2 (zOfNat a)))) = _
      rw [zdiv2_nat, suffix_intOfZ_shiftin, ih]
      rw [suffix_odd_zOfNat]
      let q := (a / 2) % 2 ^ (k + 1)
      let r := a % 2 ^ (k + 2)
      change 2 * (if q < 2 ^ k then Int.ofNat q
          else Int.ofNat q - Int.ofNat (2 ^ (k + 1))) +
          (if decide (a % 2 = 1) then 1 else 0) =
        if r < 2 ^ (k + 1) then Int.ofNat r
          else Int.ofNat r - Int.ofNat (2 ^ (k + 2))
      have hr : 2 * q + a % 2 = r := by
        have hm := Nat.mod_mul (a := 2) (b := 2 ^ (k + 1)) (x := a)
        simpa [q, r, Nat.pow_succ, Nat.add_comm, Nat.mul_comm,
          Nat.mul_left_comm] using hm.symm
      have hpNat : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
        rw [show k + 2 = (k + 1) + 1 by omega, Nat.pow_succ]
        omega
      have hpInt := congrArg Int.ofNat hpNat
      simp only [Int.ofNat_eq_natCast, Int.natCast_mul] at hpInt
      have hbit : a % 2 = 0 ∨ a % 2 = 1 := by omega
      rcases hbit with hbit | hbit
      · have hodd : decide (a % 2 = 1) = false := by simp [hbit]
        rw [hodd]
        simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hq : q < 2 ^ k
        · have hrl : r < 2 ^ (k + 1) := by
            rw [← hr, hbit]
            simp only [Nat.add_zero]
            omega
          rw [if_pos hq, if_pos hrl]
          have hrInt := congrArg Int.ofNat hr
          simp only [Int.ofNat_eq_natCast, Int.natCast_add,
            Int.natCast_mul] at hrInt
          simp only [Int.ofNat_eq_natCast]
          omega

        · have hrl : ¬ r < 2 ^ (k + 1) := by
            intro hrl
            rw [← hr, hbit] at hrl
            simp only [Nat.add_zero] at hrl
            omega
          rw [if_neg hq, if_neg hrl]
          have hrInt := congrArg Int.ofNat hr
          simp only [Int.ofNat_eq_natCast, Int.natCast_add,
            Int.natCast_mul] at hrInt
          simp only [Int.ofNat_eq_natCast]
          omega
      · have hodd : decide (a % 2 = 1) = true := by simp [hbit]
        rw [hodd]
        simp only [↓reduceIte]
        by_cases hq : q < 2 ^ k
        · have hrl : r < 2 ^ (k + 1) := by
            rw [← hr, hbit]
            omega
          rw [if_pos hq, if_pos hrl]
          have hrInt := congrArg Int.ofNat hr
          simp only [Int.ofNat_eq_natCast, Int.natCast_add,
            Int.natCast_mul] at hrInt
          simp only [Int.ofNat_eq_natCast]
          omega
        · have hrl : ¬ r < 2 ^ (k + 1) := by
            intro hrl
            rw [← hr, hbit] at hrl
            omega
          rw [if_neg hq, if_neg hrl]
          have hrInt := congrArg Int.ofNat hr
          simp only [Int.ofNat_eq_natCast, Int.natCast_add,
            Int.natCast_mul] at hrInt
          simp only [Int.ofNat_eq_natCast]
          omega

private theorem suffix_sign_ext_nat (k : Nat) (x : int) :
    sign_ext (zOfNat (k + 1)) x =
      WordCore.repr wordsize (zOfInt
        (if x.val % (2 ^ (k + 1)) < 2 ^ k then
          Int.ofNat (x.val % (2 ^ (k + 1)))
        else
          Int.ofNat (x.val % (2 ^ (k + 1))) - Int.ofNat (2 ^ (k + 1)))) := by
  have hpred : ZArith.BinInt.Z.pred (zOfNat (k + 1)) = zOfNat k := by
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.pred, ZArith.BinInt.Z.sub,
      intOfZ_zOfInt, zOfNat, ZArith.BinInt.Z.of_nat]
    change Int.ofNat (k + 1) - 1 = Int.ofNat k
    simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_one]
    omega
  have hsel : sumboolSelect
      (CompCert4Lean.Lib.Coqlib.zlt zZero (zOfNat (k + 1)))
      (zOpp zOne) zZero = zOpp zOne := by
    cases hs : CompCert4Lean.Lib.Coqlib.zlt zZero (zOfNat (k + 1)) with
    | left _ => rfl
    | right h =>
        exfalso
        change intOfZ (zOfNat (k + 1)) ≤ 0 at h
        have hz : intOfZ (zOfNat (k + 1)) = Int.ofNat (k + 1) := by
          simpa only [zOfNat, ZArith.BinInt.Z.of_nat] using
            intOfZ_zOfInt (Int.ofNat (k + 1))
        rw [hz] at h
        have hk : 0 < Int.ofNat (k + 1) := by
          rw [Int.ofNat_eq_natCast]
          exact Int.natCast_pos.mpr (by omega)
        exact (Int.not_le_of_gt hk) h
  unfold sign_ext WordCore.sign_ext
  rw [hpred]
  dsimp only
  simp only [hsel]
  unfold WordCore.unsigned
  rw [WordCore.intval_eq_zOfNat_val x]
  change WordCore.repr wordsize
      (ZArith.BinInt.Z.iter (zOfNat k) suffixSignStep suffixSignBase
        (zOfNat x.val)) = _
  apply congrArg (WordCore.repr wordsize)
  apply intOfZ_injective
  rw [intOfZ_zOfInt]
  exact suffix_sign_iter_nat k x.val

private theorem suffix_signed_int (x : int) :
    intOfZ (signed x) =
      if x.val < 2 ^ (wordsize - 1) then Int.ofNat x.val
      else Int.ofNat x.val - Int.ofNat (2 ^ wordsize) := by
  unfold signed WordCore.signed
  cases hlt : CompCert4Lean.Lib.Coqlib.zlt
      (WordCore.unsigned x) (zTwoPowerNat (wordsize - 1)) with
  | left h =>
      simp only [zltSelect, sumboolSelect, hlt]
      have hvlt : x.val < 2 ^ (wordsize - 1) := by
        change intOfZ x.intval < intOfZ (zTwoPowerNat (wordsize - 1)) at h
        rw [WordCore.intval_eq_zOfNat_val x] at h
        have hval : intOfZ (zOfNat x.val) = Int.ofNat x.val := by
          simpa only [zOfNat, ZArith.BinInt.Z.of_nat] using
            intOfZ_zOfInt (Int.ofNat x.val)
        have hpow : intOfZ (zTwoPowerNat (wordsize - 1)) =
            Int.ofNat (2 ^ (wordsize - 1)) := by rfl
        rw [hval, hpow] at h
        exact Int.ofNat_lt.mp h
      rw [if_pos hvlt]
      change intOfZ x.intval = Int.ofNat x.val
      rw [WordCore.intval_eq_zOfNat_val x]
      simpa only [zOfNat, ZArith.BinInt.Z.of_nat] using
        intOfZ_zOfInt (Int.ofNat x.val)
  | right h =>
      simp only [zltSelect, sumboolSelect, hlt]
      have hvge : ¬ x.val < 2 ^ (wordsize - 1) := by
        intro hvlt
        change intOfZ (zTwoPowerNat (wordsize - 1)) ≤ intOfZ x.intval at h
        rw [WordCore.intval_eq_zOfNat_val x] at h
        have hval : intOfZ (zOfNat x.val) = Int.ofNat x.val := by
          simpa only [zOfNat, ZArith.BinInt.Z.of_nat] using
            intOfZ_zOfInt (Int.ofNat x.val)
        have hpow : intOfZ (zTwoPowerNat (wordsize - 1)) =
            Int.ofNat (2 ^ (wordsize - 1)) := by rfl
        rw [hval, hpow] at h
        exact (Int.not_le_of_gt (Int.ofNat_lt.mpr hvlt)) h
      rw [if_neg hvge]
      simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      change intOfZ x.intval - intOfZ (zTwoPowerNat wordsize) = _
      rw [WordCore.intval_eq_zOfNat_val x]
      have hval : intOfZ (zOfNat x.val) = Int.ofNat x.val := by
        simpa only [zOfNat, ZArith.BinInt.Z.of_nat] using
          intOfZ_zOfInt (Int.ofNat x.val)
      have hpow : intOfZ (zTwoPowerNat wordsize) =
          Int.ofNat (2 ^ wordsize) := by rfl
      rw [hval, hpow]

private theorem suffix_shr_shl_nat (k : Nat) (hk : k < 32) (x : int) :
    let y := repr (zOfNat (31 - k))
    shr (shl x y) y =
      WordCore.repr wordsize (zOfInt
        (if x.val % (2 ^ (k + 1)) < 2 ^ k then
          Int.ofNat (x.val % (2 ^ (k + 1)))
        else
          Int.ofNat (x.val % (2 ^ (k + 1))) - Int.ofNat (2 ^ (k + 1)))) := by
  let s := 31 - k
  let y := repr (zOfNat s)
  change shr (shl x y) y = _
  have hks : k + s = 31 := by dsimp [s]; omega
  have hk1s : (k + 1) + s = 32 := by omega
  have hpHalf : 2 ^ 31 = 2 ^ k * 2 ^ s := by
    rw [← Nat.pow_add, hks]
  have hpFull : 2 ^ 32 = 2 ^ (k + 1) * 2 ^ s := by
    rw [← Nat.pow_add, hk1s]
  have hyval : y.val = s := by
    dsimp [y]
    unfold repr
    change (WordCore.repr wordsize (zOfNat s)).val = s
    rw [WordCore.val_repr_residue]
    have hzof : zOfNat s = zOfInt (Int.ofNat s) := by rfl
    rw [hzof, WordCore.residue_zOfNat]
    apply Nat.mod_eq_of_lt
    change s < 2 ^ 32
    dsimp [s]
    omega
  have hyunsigned : unsigned y = zOfNat s := by
    change y.intval = zOfNat s
    rw [WordCore.intval_eq_zOfNat_val y, hyval]
  let r := x.val % 2 ^ (k + 1)
  have hrange : r < 2 ^ (k + 1) := by
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hb : (shl x y).val = r * 2 ^ s := by
    change (WordCore.shl x y).val = _
    rw [suffix_shl_val, hyval]
    change (x.val * 2 ^ s) % 2 ^ 32 = r * 2 ^ s
    rw [hpFull]
    exact Nat.mul_mod_mul_right (2 ^ s) x.val (2 ^ (k + 1))
  change WordCore.repr wordsize
      (zShiftr (signed (shl x y)) (unsigned y)) = _
  apply congrArg (WordCore.repr wordsize)
  apply intOfZ_injective
  rw [hyunsigned, intOfZ_zOfInt]
  unfold zShiftr ZArith.BinInt.Z.shiftr
  simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
    Int.ofNat_eq_natCast, Int.natCast_nonneg, ↓reduceIte,
    Int.toNat_natCast]
  rw [suffix_signed_int, hb]
  change (if r * 2 ^ s < 2 ^ 31 then Int.ofNat (r * 2 ^ s)
      else Int.ofNat (r * 2 ^ s) - Int.ofNat (2 ^ 32)) /
      Int.pow 2 s =
    if r < 2 ^ k then Int.ofNat r
      else Int.ofNat r - Int.ofNat (2 ^ (k + 1))
  have hpowpos : 0 < Int.pow 2 s := Int.pow_pos (by omega)
  have hcastmul (a : Nat) : Int.ofNat (a * 2 ^ s) =
      Int.ofNat a * Int.pow 2 s := by
    calc
      Int.ofNat (a * 2 ^ s) = Int.ofNat a * Int.ofNat (2 ^ s) := by
        exact Int.natCast_mul a (2 ^ s)
      _ = Int.ofNat a * Int.pow 2 s :=
        congrArg (fun q : Int => Int.ofNat a * q) (Int.natCast_pow 2 s)
  have hbInt := hcastmul r
  have hpFullInt : Int.ofNat (2 ^ 32) =
      Int.ofNat (2 ^ (k + 1)) * Int.pow 2 s := by
    calc
      Int.ofNat (2 ^ 32) = Int.ofNat (2 ^ (k + 1) * 2 ^ s) :=
        congrArg Int.ofNat hpFull
      _ = _ := hcastmul (2 ^ (k + 1))
  by_cases hrlt : r < 2 ^ k
  · have hblt : r * 2 ^ s < 2 ^ 31 := by
      rw [hpHalf]
      exact (Nat.mul_lt_mul_right (Nat.two_pow_pos s)).2 hrlt
    rw [if_pos hblt, if_pos hrlt, hbInt]
    exact Int.mul_ediv_cancel _ (Int.ne_of_gt hpowpos)
  · have hrge : 2 ^ k ≤ r := Nat.le_of_not_gt hrlt
    have hbge : 2 ^ 31 ≤ r * 2 ^ s := by
      rw [hpHalf]
      exact Nat.mul_le_mul_right (2 ^ s) hrge
    have hbnlt : ¬ r * 2 ^ s < 2 ^ 31 := Nat.not_lt_of_ge hbge
    rw [if_neg hbnlt, if_neg hrlt, hbInt, hpFullInt, ← Int.sub_mul]
    exact Int.mul_ediv_cancel _ (Int.ne_of_gt hpowpos)

theorem sign_ext_shr_shl_proof : sign_ext_shr_shl := by
  intro n x hn
  have hn0 : zLe zZero n := by
    change 0 ≤ intOfZ n
    have h := hn.1
    change 0 < intOfZ n at h
    exact Int.le_of_lt h
  let m := zToNat n
  have hnrepr : n = zOfNat m := by
    exact (ZArith.Znat.Z2Nat.id n hn0).symm
  have hmpos : 0 < m := by
    have h := hn.1
    rw [hnrepr] at h
    change 0 < intOfZ (zOfNat m) at h
    have hz : intOfZ (zOfNat m) = Int.ofNat m := by
      simpa only [zOfNat, ZArith.BinInt.Z.of_nat] using
        intOfZ_zOfInt (Int.ofNat m)
    rw [hz] at h
    exact Int.ofNat_lt.mp h
  have hmle : m ≤ 32 := by
    have h := hn.2
    rw [hnrepr] at h
    change intOfZ (zOfNat m) ≤ intOfZ zwordsize at h
    have hz : intOfZ (zOfNat m) = Int.ofNat m := by
      simpa only [zOfNat, ZArith.BinInt.Z.of_nat] using
        intOfZ_zOfInt (Int.ofNat m)
    rw [hz] at h
    change Int.ofNat m ≤ 32 at h
    exact Int.ofNat_le.mp h
  let k := m - 1
  have hk : k < 32 := by dsimp [k]; omega
  have hmk : k + 1 = m := by dsimp [k]; omega
  have hnk : n = zOfNat (k + 1) := by rw [hnrepr, hmk]
  have hdiff : zSub zwordsize n = zOfNat (31 - k) := by
    rw [hnk]
    apply intOfZ_injective
    simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    have hw : intOfZ zwordsize = (32 : Int) := by rfl
    have hkz : intOfZ (zOfNat (k + 1)) = Int.ofNat (k + 1) := by
      simpa only [zOfNat, ZArith.BinInt.Z.of_nat] using
        intOfZ_zOfInt (Int.ofNat (k + 1))
    have hrz : intOfZ (zOfNat (31 - k)) = Int.ofNat (31 - k) := by
      simpa only [zOfNat, ZArith.BinInt.Z.of_nat] using
        intOfZ_zOfInt (Int.ofNat (31 - k))
    rw [hw, hkz, hrz]
    simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_one]
    omega
  rw [hdiff, hnk]
  exact (suffix_sign_ext_nat k x).trans (suffix_shr_shl_nat k hk x).symm

theorem bits_one_proof : bits_one := by
  intro n
  cases n with
  | Zneg p =>
      rfl
  | Z0 =>
      rfl
  | Zpos p =>
      unfold testbit one WordCore.testbit
      have hneq : (Numbers.BinNums.Z.Zpos p) ≠ zZero := by
        intro h
        cases h
      cases hz : CompCert4Lean.Lib.Coqlib.zeq
          (Numbers.BinNums.Z.Zpos p) zZero with
      | left heq => exact (hneq heq).elim
      | right hne =>
          simp only [sumboolSelect, hz]
          change Nat.testBit (WordCore.one wordsize).val
              (WordCore.positiveToNat p) = false
          have hone : (WordCore.one wordsize).val = 1 := by
            unfold WordCore.one
            rw [WordCore.val_repr_residue]
            rfl
          rw [hone]
          have hp : 0 < WordCore.positiveToNat p := by
            rw [WordCore.positiveToNat_eq_posToNat]
            exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
          rw [Nat.testBit_lt_two_pow
            (Nat.one_lt_two_pow (Nat.ne_of_gt hp))]

private theorem suffix_mone_val : (WordCore.mone wordsize).val = 2 ^ wordsize - 1 := by
  unfold WordCore.mone
  rw [WordCore.val_repr_residue]
  have hz : zOpp zOne =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (-1) := by
    rfl
  rw [hz, WordCore.residue_zOfInt]
  change ((-1 : Int) % Int.ofNat (2 ^ wordsize)).toNat = 2 ^ wordsize - 1
  decide

theorem bits_mone_proof : bits_mone := by
  intro i hi
  have hmone := suffix_mone_val
  cases i with
  | Zneg p =>
      have h := hi.1
      have hp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      simp only [zLe, ZArith.BinInt.Z.le, intOfZ, posToNat] at h
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at h
      have hpI : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr hp
      have hneg : -Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) < 0 := by
        omega
      exact ((Int.not_lt_of_ge h) hneg).elim
  | Z0 =>
      unfold testbit WordCore.testbit
      change Nat.testBit (WordCore.mone wordsize).val 0 = true
      rw [hmone]
      decide
  | Zpos p =>
      unfold testbit WordCore.testbit
      change Nat.testBit (WordCore.mone wordsize).val
        (WordCore.positiveToNat p) = true
      rw [WordCore.positiveToNat_eq_posToNat]
      rw [hmone]
      have hlt := hi.2
      change intOfZ (Numbers.BinNums.Z.Zpos p) < intOfZ (zOfNat wordsize) at hlt
      simp only [intOfZ, posToNat, zOfNat,
        ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hlt
      have hnat : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p < wordsize :=
        Int.ofNat_lt.mp hlt
      simpa [hnat] using Nat.testBit_two_pow_sub_one wordsize
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)

theorem is_power2_range_proof : is_power2_range := by
  intro n logn hpow
  unfold is_power2 at hpow
  cases hu : unsigned n with
  | Z0 =>
      simp only [CompCert4Lean.Lib.Zbits.Z_is_power2, hu] at hpow
      cases hpow
  | Zneg p =>
      simp only [CompCert4Lean.Lib.Zbits.Z_is_power2, hu] at hpow
      cases hpow
  | Zpos p =>
      cases hp : CompCert4Lean.Lib.Zbits.P_is_power2 p with
      | false =>
          simp only [CompCert4Lean.Lib.Zbits.Z_is_power2, hu, hp] at hpow
          cases hpow
      | true =>
          simp only [CompCert4Lean.Lib.Zbits.Z_is_power2, hu, hp, ↓reduceIte] at hpow
          injection hpow with hlogn
          subst logn
          change ltu (repr (ZArith.BinInt.Z.log2
            (Numbers.BinNums.Z.Zpos p))) iwordsize = true
          have hbound : zLt (unsigned n) modulus := n.intrange.2
          rw [hu] at hbound
          change intOfZ (Numbers.BinNums.Z.Zpos p) < intOfZ modulus at hbound
          unfold modulus at hbound
          rw [WordCore.twoPowerNat_eq_zOfNat_twoPow] at hbound
          simp only [intOfZ, posToNat, zOfNat,
            ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hbound
          have hpbound :
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p <
                2 ^ wordsize := Int.ofNat_lt.mp hbound
          have hpne :
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p ≠ 0 :=
            Nat.ne_of_gt
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p)
          have hlog :
              Nat.log2 (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) <
                wordsize := (Nat.log2_lt hpne).2 hpbound
          have hzlog : ZArith.BinInt.Z.log2 (Numbers.BinNums.Z.Zpos p) =
              zOfInt (Int.ofNat (Nat.log2
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))) := by
            unfold ZArith.BinInt.Z.log2
            have hpcast : intOfZ (Numbers.BinNums.Z.Zpos p) =
                Int.ofNat
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) := by
              rfl
            rw [hpcast]
            have htoNat : Int.toNat
                (Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) =
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p := by
              simp
            rw [htoNat]
          have hzrange :
              zLe zZero (ZArith.BinInt.Z.log2 (Numbers.BinNums.Z.Zpos p)) ∧
                zLe (ZArith.BinInt.Z.log2 (Numbers.BinNums.Z.Zpos p)) max_unsigned := by
            rw [hzlog]
            constructor
            · change (0 : Int) ≤ intOfZ
                (zOfInt (Int.ofNat (Nat.log2
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))))
              rw [intOfZ_zOfInt]
              exact Int.natCast_nonneg _
            · change intOfZ (zOfInt (Int.ofNat (Nat.log2
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)))) ≤
                intOfZ max_unsigned
              rw [intOfZ_zOfInt]
              have hmax : intOfZ max_unsigned =
                  (2 ^ wordsize : Int) - 1 := by
                unfold max_unsigned
                unfold modulus
                rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
                simp only [zSub, ZArith.BinInt.Z.sub, zOfNat,
                  ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
                have hone : intOfZ zOne = (1 : Int) := by rfl
                rw [hone]
                rfl
              rw [hmax]
              have hword : wordsize = 32 := by rfl
              rw [hword] at hlog ⊢
              have hpowcast : (2 ^ 32 : Int) - 1 =
                  Int.ofNat (2 ^ 32 - 1) := by decide
              rw [hpowcast]
              apply Int.ofNat_le.mpr
              omega
          have hrepr := unsigned_repr_proof_api
            (ZArith.BinInt.Z.log2 (Numbers.BinNums.Z.Zpos p)) hzrange
          have hword : unsigned iwordsize = zwordsize := by
            exact unsigned_repr_wordsize_proof
          have hlt : zLt
              (unsigned (repr (ZArith.BinInt.Z.log2 (Numbers.BinNums.Z.Zpos p))))
              (unsigned iwordsize) := by
            rw [hrepr, hword, hzlog]
            change intOfZ (zOfInt (Int.ofNat (Nat.log2
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)))) <
              intOfZ zwordsize
            rw [intOfZ_zOfInt]
            unfold zwordsize
            simp only [zOfNat, ZArith.BinInt.Z.of_nat,
              intOfZ_zOfInt]
            exact Int.ofNat_lt.mpr hlog
          change zltSelect
            (unsigned (repr (ZArith.BinInt.Z.log2 (Numbers.BinNums.Z.Zpos p))))
            (unsigned iwordsize) true false = true
          cases hs : CompCert4Lean.Lib.Coqlib.zlt
              (unsigned (repr (ZArith.BinInt.Z.log2 (Numbers.BinNums.Z.Zpos p))))
              (unsigned iwordsize) with
          | left hslt =>
              simp [zltSelect, sumboolSelect, hs]
          | right hsge =>
              change intOfZ (unsigned iwordsize) ≤
                intOfZ (unsigned
                  (repr (ZArith.BinInt.Z.log2 (Numbers.BinNums.Z.Zpos p)))) at hsge
              change intOfZ (unsigned
                  (repr (ZArith.BinInt.Z.log2 (Numbers.BinNums.Z.Zpos p)))) <
                intOfZ (unsigned iwordsize) at hlt
              exact ((Int.not_lt_of_ge hsge) hlt).elim

theorem sign_ext_idem_proof : sign_ext_idem := by
  intro n x hn
  have hn0 : zLe zZero n := by
    change 0 ≤ intOfZ n
    exact Int.le_of_lt hn
  have hnrepr : n = zOfNat (zToNat n) :=
    (ZArith.Znat.Z2Nat.id n hn0).symm
  let m := zToNat n
  have hmpos : 0 < m := by
    rw [show m = zToNat n by rfl]
    have h := hn
    rw [hnrepr] at h
    change 0 < intOfZ (zOfNat m) at h
    simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at h
    exact Int.ofNat_lt.mp h
  let k := m - 1
  have hmk : k + 1 = m := by dsimp [k]; omega
  have hnk : n = zOfNat (k + 1) := by rw [hnrepr, hmk]
  rw [hnk]
  by_cases hk : k < wordsize
  · have h1 := suffix_sign_ext_nat k x
    have h2 := suffix_sign_ext_nat k (sign_ext (zOfNat (k + 1)) x)
    have hvalmod :
        (sign_ext (zOfNat (k + 1)) x).val % 2 ^ (k + 1) =
          x.val % 2 ^ (k + 1) := by
      rw [h1, WordCore.val_repr]
      by_cases hrlt : x.val % 2 ^ (k + 1) < 2 ^ k
      · rw [if_pos hrlt]
        change Int.toNat
            (Int.ofNat (x.val % 2 ^ (k + 1)) % Int.ofNat (2 ^ wordsize)) %
              2 ^ (k + 1) = x.val % 2 ^ (k + 1)
        have hr32 : x.val % 2 ^ (k + 1) < 2 ^ wordsize := by
          have hk1 : k + 1 ≤ wordsize := by omega
          exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
            (Nat.pow_le_pow_right Nat.zero_lt_two hk1)
        have hmod : Int.ofNat (x.val % 2 ^ (k + 1)) %
            Int.ofNat (2 ^ wordsize) =
              Int.ofNat ((x.val % 2 ^ (k + 1)) % 2 ^ wordsize) := by
          exact (Int.natCast_emod _ _).symm
        rw [hmod, Nat.mod_eq_of_lt hr32]
        change (x.val % 2 ^ (k + 1)) % 2 ^ (k + 1) = x.val % 2 ^ (k + 1)
        exact Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))
      · rw [if_neg hrlt]
        change Int.toNat
            ((Int.ofNat (x.val % 2 ^ (k + 1)) - Int.ofNat (2 ^ (k + 1))) %
              Int.ofNat (2 ^ wordsize)) % 2 ^ (k + 1) =
          x.val % 2 ^ (k + 1)
        have hk1 : k + 1 ≤ wordsize := by omega
        let r : Nat := x.val % 2 ^ (k + 1)
        let mm : Nat := 2 ^ (k + 1)
        let ww : Nat := 2 ^ wordsize
        have hrlt' : r < mm := by
          dsimp [r, mm]
          exact Nat.mod_lt _ (Nat.two_pow_pos _)
        have hmmpos : 0 < mm := Nat.two_pow_pos _
        have hmmle : mm ≤ ww := by
          dsimp [mm, ww]
          exact Nat.pow_le_pow_right Nat.zero_lt_two hk1
        have hwdiv : ww % mm = 0 := by
          have hp : ww = mm * 2 ^ (wordsize - (k + 1)) := by
            dsimp [mm, ww]
            rw [← Nat.pow_add]
            congr 1
            omega
          rw [hp, Nat.mul_mod_right]
        have ht0 : 0 ≤ (ww : Int) - mm + r := by
          have := Int.natCast_nonneg r
          have := Int.natCast_nonneg mm
          have := Int.natCast_nonneg ww
          omega
        have htw : (ww : Int) - mm + r < ww := by
          have := Int.natCast_nonneg r
          have := Int.natCast_nonneg mm
          have := Int.natCast_nonneg ww
          omega
        have hsmod :
            (Int.ofNat r - Int.ofNat mm) % Int.ofNat ww =
              (Int.ofNat ww - Int.ofNat mm + Int.ofNat r) := by
          calc
            (Int.ofNat r - Int.ofNat mm) % Int.ofNat ww =
                ((Int.ofNat r - Int.ofNat mm) + Int.ofNat ww) % Int.ofNat ww := by
                  rw [Int.add_emod_right]
            _ = (Int.ofNat ww - Int.ofNat mm + Int.ofNat r) % Int.ofNat ww := by
              congr 1 <;> omega
            _ = Int.ofNat ww - Int.ofNat mm + Int.ofNat r := by
              exact Int.emod_eq_of_lt ht0 htw
        rw [show x.val % 2 ^ (k + 1) = r by rfl,
          show 2 ^ (k + 1) = mm by rfl,
          show 2 ^ wordsize = ww by rfl, hsmod]
        have htnat : Int.toNat
            (Int.ofNat ww - Int.ofNat mm + Int.ofNat r) = ww - mm + r := by
          have heq : Int.ofNat (ww - mm + r) =
              Int.ofNat ww - Int.ofNat mm + Int.ofNat r := by
            simp only [Int.ofNat_eq_natCast, Int.natCast_add]
            rw [Int.ofNat_sub hmmle]
          rw [← heq]
          exact Int.toNat_natCast _
        rw [htnat]
        have hqpos : 0 < ww / mm := Nat.div_pos (by omega) hmmpos
        have hwmul : mm * (ww / mm) = ww := by
          have hd := Nat.mod_add_div ww mm
          rw [hwdiv] at hd
          omega
        have hdecomp : ww - mm + r = r + mm * (ww / mm - 1) := by
          rw [Nat.mul_sub_left_distrib]
          omega
        rw [hdecomp, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt hrlt']
    have hR :
        WordCore.repr wordsize
            (zOfInt
              (if (sign_ext (zOfNat (k + 1)) x).val % 2 ^ (k + 1) < 2 ^ k then
                Int.ofNat ((sign_ext (zOfNat (k + 1)) x).val % 2 ^ (k + 1))
              else
                Int.ofNat ((sign_ext (zOfNat (k + 1)) x).val % 2 ^ (k + 1)) -
                  Int.ofNat (2 ^ (k + 1)))) =
          WordCore.repr wordsize
            (zOfInt
              (if x.val % 2 ^ (k + 1) < 2 ^ k then
                Int.ofNat (x.val % 2 ^ (k + 1))
              else
                Int.ofNat (x.val % 2 ^ (k + 1)) - Int.ofNat (2 ^ (k + 1)))) := by
      rw [hvalmod]
    exact (h2.trans hR).trans h1.symm
  · have hkge : wordsize ≤ k := Nat.le_of_not_gt hk
    have hxlt : x.val < 2 ^ wordsize := WordCore.val_lt x
    have hpow : 2 ^ wordsize ≤ 2 ^ k :=
      Nat.pow_le_pow_right Nat.zero_lt_two hkge
    have hr : x.val % (2 ^ (k + 1)) = x.val := by
      apply Nat.mod_eq_of_lt
      exact Nat.lt_of_lt_of_le hxlt (Nat.le_trans hpow
        (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_succ k)))
    have hcond : x.val < 2 ^ k := Nat.lt_of_lt_of_le hxlt hpow
    have h1 := suffix_sign_ext_nat k x
    have hsign : sign_ext (zOfNat (k + 1)) x =
        WordCore.repr wordsize (zOfInt (Int.ofNat x.val)) := by
      simpa [hr, hcond] using h1
    have hrepr : WordCore.repr wordsize
        (zOfInt (Int.ofNat x.val)) = x := by
      apply WordCore.ext_of_val_eq
      rw [WordCore.val_repr]
      change Int.toNat (Int.ofNat x.val % Int.ofNat (2 ^ wordsize)) = x.val
      simp only [Int.ofNat_eq_natCast]
      have hbridge := Int.emod_natAbs_of_nonneg
        (x := (x.val : Int)) (n := 2 ^ wordsize)
        (Int.natCast_nonneg _)
      simp only [Int.natAbs_natCast] at hbridge
      rw [← hbridge]
      exact Nat.mod_eq_of_lt (WordCore.val_lt x)
    rw [hrepr] at hsign
    exact congrArg (sign_ext (zOfNat (k + 1))) hsign

theorem add_commut_proof : add_commut := by
  intro x y
  change WordCore.add x y = WordCore.add y x
  apply WordCore.ext_of_val_eq
  rw [WordCore.add_val, WordCore.add_val, Nat.add_comm]

theorem and_assoc_proof : and_assoc := by
  intro x y z
  apply WordCore.ext_of_val_eq
  change (WordCore.and (WordCore.and x y) z).val =
    (WordCore.and x (WordCore.and y z)).val
  rw [suffix_and_val, suffix_and_val, suffix_and_val, suffix_and_val]
  exact Nat.and_assoc _ _ _

theorem wordsize_max_unsigned_proof : wordsize_max_unsigned := by
  change (32 : _root_.Int) ≤ (2 ^ 32 : _root_.Int) - 1
  decide

private theorem suffix_unsigned_repr_eq_exact (x : Z) :
    unsigned (repr x) = zMod x modulus := by
  change (WordCore.repr wordsize x).intval = zMod x modulus
  rw [WordCore.intval_eq_zOfNat_val]
  have hval : (WordCore.repr wordsize x).val =
      _root_.Int.toNat
        (intOfZ x % _root_.Int.ofNat (2 ^ wordsize)) := by
    have h := WordCore.val_repr wordsize (intOfZ x)
    rw [zOfInt_intOfZ x] at h
    simpa only [_root_.Int.ofNat_eq_natCast] using h
  rw [hval]
  apply intOfZ_injective
  have hmpos : (0 : _root_.Int) < intOfZ modulus := by
    change (0 : _root_.Int) < _root_.Int.ofNat (2 ^ wordsize)
    exact _root_.Int.natCast_pos.mpr (Nat.two_pow_pos _)
  have hm : intOfZ modulus = _root_.Int.ofNat (2 ^ wordsize) := by
    rfl
  simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  have hmod : intOfZ (zMod x modulus) =
      intOfZ x % _root_.Int.ofNat (2 ^ wordsize) := by
    have hrange := ZArith.BinInt.Z.modulo_range x modulus (by
      change (0 : _root_.Int) < intOfZ modulus
      exact hmpos)
    have hr0 : (0 : _root_.Int) ≤ intOfZ (zMod x modulus) := hrange.1
    have hrlt : intOfZ (zMod x modulus) < intOfZ modulus := hrange.2
    have hd := ZArith.Zdiv.Z_div_mod_eq_full x modulus
    have hdInt := congrArg intOfZ hd
    simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
      intOfZ_zOfInt] at hdInt
    let q := intOfZ (ZArith.BinInt.Z.div x modulus)
    let r := intOfZ (zMod x modulus)
    let m := intOfZ modulus
    have hcalc : intOfZ x % m = r := by
      calc
        intOfZ x % m = (m * q + r) % m := congrArg (fun a => a % m) hdInt
        _ = (r + q * m) % m := by rw [_root_.Int.add_comm, _root_.Int.mul_comm]
        _ = r % m := _root_.Int.add_mul_emod_self_right r q m
        _ = r := _root_.Int.emod_eq_of_lt hr0 hrlt
    simpa [m, r, hm] using hcalc.symm
  rw [hmod]
  exact _root_.Int.toNat_of_nonneg
    (_root_.Int.emod_nonneg (intOfZ x) (_root_.Int.ne_of_gt hmpos))

theorem signed_repr_eq_proof : signed_repr_eq := by
  intro x
  change zltSelect (unsigned (repr x)) half_modulus
      (unsigned (repr x)) (zSub (unsigned (repr x)) modulus) =
    zltSelect (zMod x modulus) half_modulus (zMod x modulus)
      (zSub (zMod x modulus) modulus)
  rw [suffix_unsigned_repr_eq_exact]

theorem eqm_trans_proof : eqm_trans := by
  intro x y z hxy hyz
  exact CompCert4Lean.Lib.Zbits.eqmod_trans modulus x y z hxy hyz

theorem xor_commut_proof : xor_commut := by
  intro x y
  change WordCore.repr wordsize (zOfNat (Nat.xor x.val y.val)) =
    WordCore.repr wordsize (zOfNat (Nat.xor y.val x.val))
  exact congrArg (fun n : Nat => WordCore.repr wordsize (zOfNat n))
    (Nat.xor_comm x.val y.val)

private theorem suffix_testbit_nat (x : int) (n : Nat) :
    testbit x (zOfNat n) = x.val.testBit n := by
  cases n with
  | zero => rfl
  | succ n =>
      have hp :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat (n + 1)) = n + 1 :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat (Nat.succ_pos n)
      have hz : zOfNat (Nat.succ n) =
          .Zpos (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat (n + 1)) := by
        rfl
      rw [hz]
      simp only [testbit, WordCore.testbit,
        WordCore.positiveToNat_eq_posToNat, hp]

private theorem suffix_ror_val (x y : int) :
    (WordCore.ror x y).val =
      Nat.lor (x.val >>> (y.val % wordsize))
        (x.val <<< (wordsize - (y.val % wordsize))) % (2 ^ wordsize) := by
  unfold WordCore.ror
  dsimp
  rw [WordCore.val_repr_residue]
  exact WordCore.residue_zOfNat _ _

private theorem suffix_ror_bit (x y : int) (i : Nat)
    (hi : i < wordsize) :
    ((WordCore.ror x y).val).testBit i =
      x.val.testBit ((i + y.val) % wordsize) := by
  rw [suffix_ror_val]
  rw [Nat.lor_eq]
  rw [Nat.testBit_mod_two_pow]
  simp only [hi, Bool.true_and]
  let a := y.val % wordsize
  have ha : a < wordsize := Nat.mod_lt _ (by omega)
  have htarget : (i + y.val) % wordsize = (i + a) % wordsize := by
    dsimp [a]
    exact (Nat.add_mod_mod i y.val wordsize).symm
  rw [htarget]
  simp only [decide_true, Bool.true_and]
  dsimp [a] at ⊢
  by_cases hsum : i + a < wordsize
  · have hright : (x.val >>> a).testBit i = x.val.testBit (i + a) := by
      simpa [Nat.add_comm] using
        (Nat.testBit_shiftRight x.val a i)
    have hleft : (x.val <<< (wordsize - a)).testBit i = false := by
      rw [Nat.testBit_shiftLeft]
      simp [show ¬ wordsize - a ≤ i by omega]
    dsimp [a] at hright hleft
    simp only [Nat.testBit_or, hright, hleft, Bool.or_false, decide_true,
      Bool.true_and]
    rw [Nat.mod_eq_of_lt hsum]
  · have hsum' : wordsize ≤ i + a := Nat.le_of_not_gt hsum
    have hright : (x.val >>> a).testBit i = false := by
      rw [Nat.testBit_shiftRight]
      apply Nat.testBit_lt_two_pow
      have hpow : 2 ^ wordsize ≤ 2 ^ (a + i) :=
        Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
      exact Nat.lt_of_lt_of_le (WordCore.val_lt x) hpow
    have hleft : (x.val <<< (wordsize - a)).testBit i =
        x.val.testBit (i + a - wordsize) := by
      rw [Nat.testBit_shiftLeft]
      simp [show wordsize - a ≤ i by omega]
      congr 1 <;> omega
    dsimp [a] at hright hleft
    simp only [Nat.testBit_or, hright, Bool.false_or, hleft, decide_true,
      Bool.true_and]
    rw [Nat.mod_eq_sub_mod hsum']
    have hidx : i + a - wordsize < wordsize := by omega
    rw [Nat.mod_eq_of_lt hidx]

private theorem suffix_zmod_add_nat (i : Nat) (y : int) :
    zMod (zAdd (zOfNat i) (unsigned y)) zwordsize =
      zOfNat ((i + y.val) % wordsize) := by
  have hy : unsigned y = zOfNat y.val := by
    change y.intval = zOfNat y.val
    exact WordCore.intval_eq_zOfNat_val y
  rw [hy]
  apply intOfZ_injective
  simp only [zMod, zAdd, zwordsize, zOfNat,
    ZArith.BinInt.Z.modulo, ZArith.BinInt.Z.add,
    ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  change (if (Int.ofNat wordsize) = 0 then
      Int.ofNat i + Int.ofNat y.val
    else if 0 < Int.ofNat wordsize then
      (Int.ofNat i + Int.ofNat y.val) % Int.ofNat wordsize
    else _) = Int.ofNat ((i + y.val) % wordsize)
  simp [wordsize, Int.natCast_add, Int.natCast_emod]

theorem bits_ror_proof : bits_ror := by
  intro x y i hi
  cases i with
  | Zneg p =>
      exfalso
      have hi0 := hi.1
      change 0 ≤ -(Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) at hi0
      have hp : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p)
      omega
  | Z0 =>
      have hbit := suffix_ror_bit x y 0 (by decide)
      have hmod := suffix_zmod_add_nat 0 y
      have hmod' := hmod
      change zMod (zAdd (.Z0 : Z) (unsigned y)) zwordsize =
        zOfNat ((0 + y.val) % wordsize) at hmod'
      calc
        testbit (ror x y) .Z0 = (WordCore.ror x y).val.testBit 0 := by
          rfl
        _ = x.val.testBit ((0 + y.val) % wordsize) := hbit
        _ = testbit x (zOfNat ((0 + y.val) % wordsize)) :=
          (suffix_testbit_nat x ((0 + y.val) % wordsize)).symm
        _ = testbit x (zMod (zAdd .Z0 (unsigned y)) zwordsize) := by
          rw [hmod']
  | Zpos p =>
      have hkZ := hi.2
      change (Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) : Int) <
        Int.ofNat wordsize at hkZ
      have hk :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p < wordsize :=
        Int.ofNat_lt.mp hkZ
      have hz : zOfNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = .Zpos p := by
        apply intOfZ_injective
        simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
        rfl
      rw [← hz] at hi ⊢
      have hbit := suffix_ror_bit x y
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) hk
      have hmod := suffix_zmod_add_nat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) y
      calc
        testbit (ror x y) (zOfNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) =
            (WordCore.ror x y).val.testBit
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
          suffix_testbit_nat (WordCore.ror x y)
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
        _ = x.val.testBit
            ((CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p + y.val) %
              wordsize) := hbit
        _ = testbit x (zOfNat
            ((CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p + y.val) %
              wordsize)) :=
          (suffix_testbit_nat x _).symm
        _ = testbit x (zMod (zAdd
            (zOfNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))
            (unsigned y)) zwordsize) := by
          rw [hmod]

private theorem suffix_ltu_last_val (y : int)
    (h : ltu y (repr (zSub zwordsize zOne)) = true) : y.val < wordsize - 1 := by
  have hlt := (ltu_inv_proof y (repr (zSub zwordsize zOne)) h).2
  have hrepr : unsigned (repr (zSub zwordsize zOne)) =
      zSub zwordsize zOne := by
    apply unsigned_repr_proof_api
    constructor
    · change (0 : Int) ≤ 31
      omega
    · change (31 : Int) ≤ (2 ^ wordsize : Int) - 1
      decide
  rw [hrepr] at hlt
  change intOfZ y.intval < intOfZ (zSub zwordsize zOne) at hlt
  rw [WordCore.intval_eq_zOfNat_val y] at hlt
  simp only [zSub, ZArith.BinInt.Z.sub, zOfNat,
    ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hlt
  exact Int.ofNat_lt.mp hlt

private theorem suffix_signed_shl_one (y : int)
    (hyv : y.val < wordsize - 1) :
    signed (shl one y) = zTwoP (unsigned y) := by
  have hyunsigned : unsigned y = zOfNat y.val := by
    change y.intval = zOfNat y.val
    exact WordCore.intval_eq_zOfNat_val y
  have hone : (one : int).val = 1 := by rfl
  have hshlval : (shl one y).val = 2 ^ y.val := by
    change (WordCore.shl one y).val = 2 ^ y.val
    rw [suffix_shl_val, hone]
    simp only [Nat.one_mul]
    apply Nat.mod_eq_of_lt
    have hpowle : 2 ^ y.val ≤ 2 ^ (wordsize - 1) := by
      apply Nat.pow_le_pow_right Nat.zero_lt_two
      omega
    have hhalf : 2 ^ (wordsize - 1) < 2 ^ wordsize := by
      change 2 ^ 31 < 2 ^ 32
      decide
    exact Nat.lt_of_le_of_lt hpowle hhalf
  have hsmall : (shl one y).val < 2 ^ (wordsize - 1) := by
    rw [hshlval]
    apply Nat.pow_lt_pow_right
    · decide
    · omega
  have hs := suffix_signed_int (shl one y)
  rw [if_pos hsmall, hshlval] at hs
  have hy0 : zLe zZero (unsigned y) := by
    have h := y.intrange.1
    change (-1 : Int) < intOfZ y.intval at h
    change 0 ≤ intOfZ y.intval
    omega
  have htwo : zTwoP (unsigned y) = zOfInt (Int.ofNat (2 ^ y.val)) := by
    have h := suffix_two_p_nonneg (unsigned y) hy0
    simpa [hyunsigned] using h
  apply intOfZ_injective
  rw [hs, htwo, intOfZ_zOfInt]

private theorem suffix_tdiv_adjust (a b : Int) (hb : 0 < b) :
    a.tdiv b = (if a < 0 then (a + b - 1) / b else a / b) := by
  by_cases ha : 0 ≤ a
  · have hna : ¬ a < 0 := by omega
    rw [if_neg hna, Int.tdiv_eq_ediv_of_nonneg ha]
  · have ha' : a < 0 := by omega
    rw [if_pos ha']
    rw [Int.tdiv_cases]
    simp only [if_neg ha, if_pos (Int.le_of_lt hb)]
    have hq : (-a) / b * b ≤ -a ∧ -a < (-a) / b * b + b :=
      (Int.ediv_eq_iff_of_pos hb).mp rfl
    symm
    apply (Int.ediv_eq_iff_of_pos hb).mpr
    constructor <;> simp only [Int.neg_mul] <;> omega

private theorem suffix_zdiv_pos (a b : Z) (hb : 0 < intOfZ b) :
    zDiv a b = zOfInt (Int.ediv (intOfZ a) (intOfZ b)) := by
  change zOfInt (if intOfZ b = 0 then 0 else if 0 < intOfZ b then
    Int.ediv (intOfZ a) (intOfZ b) else
      let d := -(intOfZ b)
      let q := Int.ediv (intOfZ a) d
      let r := Int.emod (intOfZ a) d
      if r = 0 then -q else -(q + 1)) = _
  simp [Int.ne_of_gt hb, hb]

private theorem suffix_signed_add_shift (x y : int)
    (hyv : y.val < wordsize - 1)
    (hx : intOfZ (signed x) < 0) :
    intOfZ (signed (add x (sub (shl one y) one))) =
      intOfZ (signed x) + Int.ofNat (2 ^ y.val) - 1 := by
  have hshlval : (shl one y).val = 2 ^ y.val := by
    change (WordCore.shl one y).val = 2 ^ y.val
    rw [suffix_shl_val]
    have hone : (one : int).val = 1 := by rfl
    rw [hone, Nat.one_mul]
    apply Nat.mod_eq_of_lt
    have hpowle : 2 ^ y.val ≤ 2 ^ (wordsize - 1) := by
      apply Nat.pow_le_pow_right Nat.zero_lt_two
      omega
    have hhalf : 2 ^ (wordsize - 1) < 2 ^ wordsize := by
      change 2 ^ 31 < 2 ^ 32
      decide
    exact Nat.lt_of_le_of_lt hpowle hhalf
  have hsubval : (sub (shl one y) one).val = 2 ^ y.val - 1 := by
    change (WordCore.sub (shl one y) one).val = 2 ^ y.val - 1
    have hone : (one : int).val = 1 := by rfl
    rw [WordCore.sub_val, hshlval, hone]
    have hpow : 1 ≤ 2 ^ y.val := Nat.one_le_two_pow
    have hlt : 2 ^ y.val - 1 < 2 ^ wordsize := by
      have hpowle : 2 ^ y.val ≤ 2 ^ (wordsize - 1) := by
        apply Nat.pow_le_pow_right Nat.zero_lt_two
        omega
      have hhalf : 2 ^ (wordsize - 1) < 2 ^ wordsize := by
        change 2 ^ 31 < 2 ^ 32
        decide
      omega
    have hge : 2 ^ wordsize ≤ 2 ^ wordsize - 1 + 2 ^ y.val := by
      have hpow : 1 ≤ 2 ^ y.val := Nat.one_le_two_pow
      omega
    rw [Nat.mod_eq_sub_mod hge]
    have heq : 2 ^ wordsize - 1 + 2 ^ y.val - 2 ^ wordsize =
        2 ^ y.val - 1 := by
      rw [show 2 ^ wordsize - 1 + 2 ^ y.val =
          2 ^ wordsize + (2 ^ y.val - 1) by omega]
      rw [Nat.add_sub_cancel_left]
    rw [heq, Nat.mod_eq_of_lt]
    exact hlt
  have haddval : (add x (sub (shl one y) one)).val =
      (x.val + (2 ^ y.val - 1)) % 2 ^ wordsize := by
    change (WordCore.add x (sub (shl one y) one)).val = _
    rw [WordCore.add_val, hsubval]
  have hsx := suffix_signed_int x
  have hst := suffix_signed_int (add x (sub (shl one y) one))
  have hxlt : ¬ x.val < 2 ^ (wordsize - 1) := by
    intro hxl
    rw [hsx, if_pos hxl] at hx
    have hx' : (0 : Int) ≤ Int.ofNat x.val := Int.natCast_nonneg _
    omega
  have hsx' : intOfZ (signed x) =
      Int.ofNat x.val - Int.ofNat (2 ^ wordsize) := by
    rw [hsx, if_neg hxlt]
  have hM : 0 < 2 ^ wordsize := Nat.two_pow_pos _
  have hH : 2 ^ (wordsize - 1) ≤ 2 ^ wordsize := by
    apply Nat.pow_le_pow_right Nat.zero_lt_two
    omega
  have hnlt : 2 ^ y.val - 1 < 2 ^ (wordsize - 1) := by
    change 2 ^ y.val - 1 < 2 ^ 31
    have hpowle : 2 ^ y.val ≤ 2 ^ (wordsize - 1) := by
      apply Nat.pow_le_pow_right Nat.zero_lt_two
      omega
    change 2 ^ y.val ≤ 2 ^ 31 at hpowle
    omega
  have hxval_lt : x.val < 2 ^ wordsize := WordCore.val_lt x
  have hsumlt2 : x.val + (2 ^ y.val - 1) < 2 * 2 ^ wordsize := by
    omega
  by_cases hsum : x.val + (2 ^ y.val - 1) < 2 ^ wordsize
  · have hmod : (x.val + (2 ^ y.val - 1)) % 2 ^ wordsize =
        x.val + (2 ^ y.val - 1) := Nat.mod_eq_of_lt hsum
    have htge : 2 ^ (wordsize - 1) ≤
        x.val + (2 ^ y.val - 1) := by
      have hxge : 2 ^ (wordsize - 1) ≤ x.val := Nat.le_of_not_gt hxlt
      omega
    have hst' : intOfZ (signed (add x (sub (shl one y) one))) =
        Int.ofNat (x.val + (2 ^ y.val - 1)) - Int.ofNat (2 ^ wordsize) := by
      have htge' : ¬ (x.val + (2 ^ y.val - 1)) % 2 ^ wordsize <
          2 ^ (wordsize - 1) := by
        rw [hmod]
        omega
      rw [hst, haddval, if_neg htge', hmod]
    rw [hsx', hst']
    have hcastP : Int.ofNat (2 ^ y.val - 1) =
        Int.ofNat (2 ^ y.val) - 1 := by
      exact Int.ofNat_sub (Nat.one_le_two_pow)
    have hcastsum : Int.ofNat (x.val + (2 ^ y.val - 1)) =
        Int.ofNat x.val + Int.ofNat (2 ^ y.val - 1) := by
      simpa only [Int.ofNat_eq_natCast] using Int.natCast_add x.val (2 ^ y.val - 1)
    rw [hcastsum, hcastP]
    omega
  · have hsumge : 2 ^ wordsize ≤ x.val + (2 ^ y.val - 1) :=
      Nat.le_of_not_gt hsum
    have hsublt : x.val + (2 ^ y.val - 1) - 2 ^ wordsize < 2 ^ wordsize := by
      omega
    have hmod : (x.val + (2 ^ y.val - 1)) % 2 ^ wordsize =
        x.val + (2 ^ y.val - 1) - 2 ^ wordsize := by
      rw [Nat.mod_eq_sub_mod hsumge, Nat.mod_eq_of_lt hsublt]
    have htlt : x.val + (2 ^ y.val - 1) - 2 ^ wordsize <
        2 ^ (wordsize - 1) := by
      have hsublt' : x.val + (2 ^ y.val - 1) - 2 ^ wordsize <
          2 ^ y.val - 1 := by
        omega
      exact Nat.lt_trans hsublt' hnlt
    have hst' : intOfZ (signed (add x (sub (shl one y) one))) =
        Int.ofNat (x.val + (2 ^ y.val - 1) - 2 ^ wordsize) := by
      have htlt' : (x.val + (2 ^ y.val - 1)) % 2 ^ wordsize <
          2 ^ (wordsize - 1) := by
        rw [hmod]
        exact htlt
      rw [hst, haddval, if_pos htlt', hmod]
    rw [hsx', hst']
    have hcastsub : Int.ofNat (x.val + (2 ^ y.val - 1) - 2 ^ wordsize) =
        Int.ofNat (x.val + (2 ^ y.val - 1)) - Int.ofNat (2 ^ wordsize) := by
      exact Int.ofNat_sub hsumge
    have hcastP : Int.ofNat (2 ^ y.val - 1) =
        Int.ofNat (2 ^ y.val) - 1 := by
      exact Int.ofNat_sub (Nat.one_le_two_pow)
    have hcastsum : Int.ofNat (x.val + (2 ^ y.val - 1)) =
        Int.ofNat x.val + Int.ofNat (2 ^ y.val - 1) := by
      simpa only [Int.ofNat_eq_natCast] using Int.natCast_add x.val (2 ^ y.val - 1)
    rw [hcastsub, hcastsum, hcastP]
    omega

theorem shrx_shr_proof : shrx_shr := by
  intro x y hy
  have hyv := suffix_ltu_last_val y hy
  have hy0 : zLe zZero (unsigned y) := by
    have h := y.intrange.1
    change (-1 : Int) < intOfZ y.intval at h
    change 0 ≤ intOfZ y.intval
    omega
  have hpow := suffix_two_p_nonneg (unsigned y) hy0
  have htwo : zTwoP (unsigned y) = zOfInt (Int.ofNat (2 ^ y.val)) := by
    have hyunsigned : unsigned y = zOfNat y.val := by
      change y.intval = zOfNat y.val
      exact WordCore.intval_eq_zOfNat_val y
    simpa [hyunsigned] using hpow
  have hdpos : 0 < intOfZ (zTwoP (unsigned y)) := by
    rw [htwo, intOfZ_zOfInt]
    have htwoInt : (0 : Int) < 2 := by decide
    exact Int.pow_pos htwoInt
  have hs := suffix_signed_shl_one y hyv
  have hdint : intOfZ (zTwoP (unsigned y)) = Int.ofNat (2 ^ y.val) := by
    rw [htwo, intOfZ_zOfInt]
  have hltzero : signed zero = zZero := by rfl
  change WordCore.repr wordsize (zQuot (signed x) (signed (shl one y))) =
    WordCore.repr wordsize
      (zShiftr (signed (if lt x zero = true then
        add x (sub (shl one y) one) else x)) (unsigned y))
  by_cases hlt : lt x zero = true
  · have hneg : intOfZ (signed x) < 0 := by
      change zltSelect (signed x) (signed zero) true false = true at hlt
      cases hz : CompCert4Lean.Lib.Coqlib.zlt (signed x) (signed zero) with
      | left hlt' =>
          change intOfZ (signed x) < intOfZ (signed zero) at hlt'
          rw [hltzero] at hlt'
          exact hlt'
      | right hge =>
          simp [zltSelect, sumboolSelect, hz] at hlt
    have hsigned := suffix_signed_add_shift x y hyv hneg
    have hquot : zQuot (signed x) (zTwoP (unsigned y)) =
        zDiv (signed (add x (sub (shl one y) one)))
          (zTwoP (unsigned y)) := by
      rw [suffix_zdiv_pos _ _ hdpos]
      apply intOfZ_injective
      simp only [zQuot, ZArith.BinInt.Z.quot, intOfZ_zOfInt]
      rw [suffix_tdiv_adjust _ _ hdpos]
      simp only [if_pos hneg]
      rw [hsigned, hdint]
      exact Int.div_def _ _
    simp [hlt]
    rw [hs]
    rw [suffix_zshiftr_div_any _ _ hy0]
    rw [hquot]
  · have hnonneg : 0 ≤ intOfZ (signed x) := by
      have hltfalse : lt x zero = false := by
        cases hxlt : lt x zero with
        | false => simpa using hxlt
        | true => exact (hlt hxlt).elim
      change zltSelect (signed x) (signed zero) true false = false at hltfalse
      cases hz : CompCert4Lean.Lib.Coqlib.zlt (signed x) (signed zero) with
      | left hlt' =>
          simp [zltSelect, sumboolSelect, hz] at hltfalse
      | right hge =>
          change intOfZ (signed zero) ≤ intOfZ (signed x) at hge
          rw [hltzero] at hge
          exact hge
    have hquot : zQuot (signed x) (zTwoP (unsigned y)) =
        zDiv (signed x) (zTwoP (unsigned y)) := by
      rw [suffix_zdiv_pos _ _ hdpos]
      apply intOfZ_injective
      simp only [zQuot, ZArith.BinInt.Z.quot, intOfZ_zOfInt]
      rw [suffix_tdiv_adjust _ _ hdpos]
      rw [if_neg (by omega)]
      exact Int.div_def _ _
    rw [if_neg hlt]
    rw [hs]
    rw [suffix_zshiftr_div_any _ _ hy0]
    rw [hquot]

theorem signed_zero_proof : signed_zero := by
  rfl

theorem bits_above_proof : bits_above := by
  intro x i hi
  cases i with
  | Zneg p =>
      exfalso
      change (32 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hi
      have hp : (0 : Int) ≤ Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_nonneg _
      omega
  | Z0 =>
      exfalso
      change (32 : Int) ≤ 0 at hi
      omega
  | Zpos p =>
      simp only [testbit, WordCore.testbit]
      rw [WordCore.positiveToNat_eq_posToNat]
      change Nat.testBit x.val
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = false
      change intOfZ (zOfNat wordsize) ≤
        intOfZ (Numbers.BinNums.Z.Zpos p) at hi
      simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
        intOfZ, posToNat] at hi
      have hidx : wordsize ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        Int.ofNat_le.mp hi
      have hpow : 2 ^ wordsize ≤
          2 ^ CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        Nat.pow_le_pow_right Nat.zero_lt_two hidx
      have hval : x.val <
          2 ^ CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        Nat.lt_of_lt_of_le (WordCore.val_lt x) hpow
      exact Nat.testBit_lt_two_pow hval

private theorem suffix_modulo_int (a : Z) :
    intOfZ (zMod a modulus) = intOfZ a % (2 ^ wordsize : Int) := by
  have hmpos : (0 : Int) < intOfZ modulus := by
    change (0 : Int) < Int.ofNat (2 ^ wordsize)
    exact Int.natCast_pos.mpr (Nat.two_pow_pos _)
  have hm : intOfZ modulus = (2 ^ wordsize : Int) := by
    rfl
  have hrange := ZArith.BinInt.Z.modulo_range a modulus (by
    change (0 : Int) < intOfZ modulus
    exact hmpos)
  have hr0 : (0 : Int) ≤ intOfZ (zMod a modulus) := hrange.1
  have hrlt : intOfZ (zMod a modulus) < intOfZ modulus := hrange.2
  have hd := ZArith.Zdiv.Z_div_mod_eq_full a modulus
  have hdInt := congrArg intOfZ hd
  simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
    intOfZ_zOfInt] at hdInt
  let q := intOfZ (ZArith.BinInt.Z.div a modulus)
  let r := intOfZ (zMod a modulus)
  let m := intOfZ modulus
  have hcalc : intOfZ a % m = r := by
    calc
      intOfZ a % m = (m * q + r) % m := congrArg (fun v => v % m) hdInt
      _ = (r + q * m) % m := by rw [Int.add_comm, Int.mul_comm]
      _ = r % m := Int.add_mul_emod_self_right r q m
      _ = r := Int.emod_eq_of_lt hr0 hrlt
  simpa [m, r, hm] using hcalc.symm

private theorem suffix_signed_mod (x : int) :
    intOfZ (signed x) % (2 ^ wordsize : Int) =
      intOfZ (unsigned x) % (2 ^ wordsize : Int) := by
  unfold signed WordCore.signed
  cases h : CompCert4Lean.Lib.Coqlib.zlt
      (WordCore.unsigned x) (zTwoPowerNat (wordsize - 1)) with
  | left _ =>
      simp only [zltSelect, sumboolSelect, h]
      rfl
  | right _ =>
      simp only [zltSelect, sumboolSelect, h]
      simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      have hm : intOfZ (zTwoPowerNat wordsize) = (2 ^ wordsize : Int) := by
        rfl
      rw [hm, Int.sub_emod, Int.emod_self, Int.sub_zero, Int.emod_emod]
      rfl

theorem mods_divs_proof : mods_divs := by
  intro x y
  apply WordCore.ext
  change unsigned (mods x y) = unsigned (sub x (mul (divs x y) y))
  change unsigned (repr
      (zSub (signed x) (zMul (zQuot (signed x) (signed y)) (signed y)))) =
    unsigned (repr
      (zSub (unsigned x)
        (unsigned (repr (zMul
          (unsigned (repr (zQuot (signed x) (signed y)))) (unsigned y))))))
  rw [suffix_unsigned_repr_eq_exact, suffix_unsigned_repr_eq_exact]
  rw [suffix_unsigned_repr_eq_exact, suffix_unsigned_repr_eq_exact]
  apply intOfZ_injective
  simp only [zSub, zMul, ZArith.BinInt.Z.sub, ZArith.BinInt.Z.mul,
    intOfZ_zOfInt]
  rw [suffix_modulo_int]
  rw [suffix_modulo_int]
  rw [suffix_modulo_int]
  simp only [intOfZ_zOfInt]
  have hsubL :
      (intOfZ (signed x) - intOfZ (zQuot (signed x) (signed y)) *
          intOfZ (signed y)) %
          (2 ^ wordsize : Int) =
        (intOfZ (signed x) % (2 ^ wordsize : Int) -
          (intOfZ (zQuot (signed x) (signed y)) * intOfZ (signed y)) %
            (2 ^ wordsize : Int)) %
          (2 ^ wordsize : Int) := by
    rw [Int.sub_emod]
  have hsubR :
      (intOfZ (unsigned x) -
          (intOfZ (zMod (zQuot (signed x) (signed y)) modulus) *
            intOfZ (unsigned y)) % (2 ^ wordsize : Int)) %
          (2 ^ wordsize : Int) =
        (intOfZ (unsigned x) % (2 ^ wordsize : Int) -
          (intOfZ (zMod (zQuot (signed x) (signed y)) modulus) *
            intOfZ (unsigned y)) % (2 ^ wordsize : Int)) %
          (2 ^ wordsize : Int) := by
    rw [Int.sub_emod, Int.emod_emod]
  rw [hsubL, hsubR]
  have hsx := suffix_signed_mod x
  have hsy := suffix_signed_mod y
  have hqmod := suffix_modulo_int (zQuot (signed x) (signed y))
  have hprod :
      (intOfZ (zQuot (signed x) (signed y)) * intOfZ (signed y)) %
          (2 ^ wordsize : Int) =
        (intOfZ (zMod (zQuot (signed x) (signed y)) modulus) *
          intOfZ (unsigned y)) % (2 ^ wordsize : Int) := by
    rw [hqmod]
    calc
      (intOfZ (zQuot (signed x) (signed y)) * intOfZ (signed y)) %
          (2 ^ wordsize : Int) =
        (intOfZ (zQuot (signed x) (signed y)) % (2 ^ wordsize : Int) *
          (intOfZ (signed y) % (2 ^ wordsize : Int))) %
            (2 ^ wordsize : Int) := Int.mul_emod _ _ _
      _ = (intOfZ (zQuot (signed x) (signed y)) %
          (2 ^ wordsize : Int) *
          (intOfZ (unsigned y) % (2 ^ wordsize : Int))) %
            (2 ^ wordsize : Int) := by rw [hsy]
      _ = (intOfZ (zQuot (signed x) (signed y)) %
          (2 ^ wordsize : Int) * intOfZ (unsigned y)) %
            (2 ^ wordsize : Int) := by
        calc
          (intOfZ (zQuot (signed x) (signed y)) %
              (2 ^ wordsize : Int) *
              (intOfZ (unsigned y) % (2 ^ wordsize : Int))) %
              (2 ^ wordsize : Int) =
            ((intOfZ (zQuot (signed x) (signed y)) %
                (2 ^ wordsize : Int)) % (2 ^ wordsize : Int) *
              (intOfZ (unsigned y) % (2 ^ wordsize : Int) %
                (2 ^ wordsize : Int))) % (2 ^ wordsize : Int) :=
            Int.mul_emod _ _ _
          _ = (intOfZ (zQuot (signed x) (signed y)) %
              (2 ^ wordsize : Int) *
              (intOfZ (unsigned y) % (2 ^ wordsize : Int))) %
              (2 ^ wordsize : Int) := by
            rw [Int.emod_emod, Int.emod_emod]
          _ = (intOfZ (zQuot (signed x) (signed y)) %
              (2 ^ wordsize : Int) * intOfZ (unsigned y)) %
              (2 ^ wordsize : Int) := by
            simpa only [Int.emod_emod] using
              (Int.mul_emod
                (intOfZ (zQuot (signed x) (signed y)) %
                  (2 ^ wordsize : Int))
                (intOfZ (unsigned y)) (2 ^ wordsize : Int)).symm
  rw [hsx, hprod]
  repeat rw [Int.emod_emod]

private theorem suffix_divmods2_n_eq (n : int) :
    zAdd (zMul (signed (if lt n zero = true then mone else zero)) modulus)
        (unsigned n) = signed n := by
  have hux : intOfZ (unsigned n) = Int.ofNat n.val := by
    change intOfZ n.intval = Int.ofNat n.val
    rw [WordCore.intval_eq_zOfNat_val n]
    simpa only [zOfNat, ZArith.BinInt.Z.of_nat] using
      intOfZ_zOfInt (Int.ofNat n.val)
  have hsx := suffix_signed_int n
  have hM : intOfZ modulus = (2 ^ wordsize : Int) := by
    rfl
  have hcastM : Int.ofNat (2 ^ wordsize) = (2 ^ wordsize : Int) := by
    change Int.ofNat (2 ^ wordsize) = Int.ofNat 2 ^ wordsize
    exact Int.natCast_pow 2 wordsize
  have hcastH : Int.ofNat (2 ^ (wordsize - 1)) =
      (2 ^ (wordsize - 1) : Int) := by
    change Int.ofNat (2 ^ (wordsize - 1)) = Int.ofNat 2 ^ (wordsize - 1)
    exact Int.natCast_pow 2 (wordsize - 1)
  by_cases hlt : lt n zero = true
  · have hneg : intOfZ (signed n) < 0 := by
      change zltSelect (signed n) (signed zero) true false = true at hlt
      cases hz : CompCert4Lean.Lib.Coqlib.zlt (signed n) (signed zero) with
      | left hlt' =>
          change intOfZ (signed n) < intOfZ (signed zero) at hlt'
          have hz0 : signed zero = zZero := by rfl
          rw [hz0] at hlt'
          exact hlt'
      | right hge =>
          simp [zltSelect, sumboolSelect, hz] at hlt
    have hval : ¬ n.val < 2 ^ (wordsize - 1) := by
      intro hv
      have hneg' :
          (if n.val < 2 ^ (wordsize - 1) then Int.ofNat n.val
          else Int.ofNat n.val - Int.ofNat (2 ^ wordsize)) < 0 := by
        simpa only [hsx] using hneg
      rw [hcastM] at hneg'
      simp [hv] at hneg'
      omega
    rw [if_pos hlt]
    apply intOfZ_injective
    simp only [zMul, zAdd, ZArith.BinInt.Z.mul, ZArith.BinInt.Z.add,
      zOpp, ZArith.BinInt.Z.opp, intOfZ_zOfInt]
    rw [hux, hM]
    have hsxval : intOfZ (signed n) =
        Int.ofNat n.val - Int.ofNat (2 ^ wordsize) := by
      simpa only [hsx, if_neg hval]
    rw [hcastM] at hsxval
    have hmone : intOfZ (signed mone) = (-1 : Int) := by
      rfl
    rw [hsxval, hmone]
    clear hsx
    omega
  · have hnonneg : 0 ≤ intOfZ (signed n) := by
      have hltfalse : lt n zero = false := by
        cases hq : lt n zero with
        | false => simpa using hq
        | true => exact (hlt hq).elim
      change zltSelect (signed n) (signed zero) true false = false at hltfalse
      cases hz : CompCert4Lean.Lib.Coqlib.zlt (signed n) (signed zero) with
      | left hlt' =>
          simp [zltSelect, sumboolSelect, hz] at hltfalse
      | right hge =>
          change intOfZ (signed zero) ≤ intOfZ (signed n) at hge
          have hz0 : signed zero = zZero := by rfl
          rw [hz0] at hge
          exact hge
    have hval : n.val < 2 ^ (wordsize - 1) := by
      by_cases hv : n.val < 2 ^ (wordsize - 1)
      · exact hv
      · exfalso
        have hv' : 2 ^ (wordsize - 1) ≤ n.val := Nat.le_of_not_gt hv
        have hvInt : (2 ^ (wordsize - 1) : Int) ≤ Int.ofNat n.val := by
          rw [← hcastH]
          exact (Int.ofNat_le).2 hv'
        have hsxval_neg : intOfZ (signed n) =
            Int.ofNat n.val - Int.ofNat (2 ^ wordsize) := by
          simpa only [hsx, if_neg hv]
        rw [hcastM] at hsxval_neg
        have hnonneg' := hnonneg
        rw [hsxval_neg] at hnonneg'
        have hnlt := WordCore.val_lt n
        have hnltInt : Int.ofNat n.val < (2 ^ wordsize : Int) := by
          rw [← hcastM]
          exact (Int.ofNat_lt).2 hnlt
        have hpow : 2 ^ (wordsize - 1) < 2 ^ wordsize := by
          change 2 ^ 31 < 2 ^ 32
          decide
        clear hsx
        omega
    rw [if_neg hlt]
    apply intOfZ_injective
    simp only [zMul, zAdd, ZArith.BinInt.Z.mul, ZArith.BinInt.Z.add,
      intOfZ_zOfInt]
    rw [hux, hM]
    have hsxval : intOfZ (signed n) = Int.ofNat n.val := by
      simpa only [hsx, if_pos hval]
    have hzero : intOfZ (signed zero) = (0 : Int) := by
      rfl
    rw [hsxval, hzero]
    clear hsx
    omega

private theorem suffix_divmods2_q_bounds (n d : int) (hd : d ≠ zero)
    (hcond : n ≠ repr min_signed ∨ d ≠ mone) :
    zLe min_signed (zQuot (signed n) (signed d)) ∧
      zLe (zQuot (signed n) (signed d)) max_signed := by
  have hD0 : intOfZ (signed d) ≠ 0 := by
    intro hzero
    apply hd
    apply signed_injective_try
    apply intOfZ_injective
    have hz : signed zero = zZero := by rfl
    rw [hz]
    exact hzero
  have hNr := signed_range_proof n
  change (-2147483648 : Int) ≤ intOfZ (signed n) ∧
      intOfZ (signed n) ≤ (2147483647 : Int) at hNr
  have hqeq : intOfZ (zQuot (signed n) (signed d)) =
      Int.tdiv (intOfZ (signed n)) (intOfZ (signed d)) := by
    simp only [zQuot, ZArith.BinInt.Z.quot, intOfZ_zOfInt]
  by_cases hDpos : 0 < intOfZ (signed d)
  · by_cases hNnonneg : 0 ≤ intOfZ (signed n)
    · have hQlo : (0 : Int) ≤ Int.tdiv (intOfZ (signed n)) (intOfZ (signed d)) := by
        exact Int.tdiv_nonneg hNnonneg (Int.le_of_lt hDpos)
      have hQhi : Int.tdiv (intOfZ (signed n)) (intOfZ (signed d)) ≤ (2147483647 : Int) := by
        simpa [hNnonneg] using
          (Int.tdiv_le_of_le_mul (a := intOfZ (signed n))
            (b := (2147483647 : Int)) hDpos (by omega))
      constructor
      · change (-2147483648 : Int) ≤ intOfZ (zQuot (signed n) (signed d))
        rw [hqeq]
        exact Int.le_trans (by omega) hQlo
      · change intOfZ (zQuot (signed n) (signed d)) ≤ (2147483647 : Int)
        rw [hqeq]
        exact hQhi
    · have hNneg : intOfZ (signed n) < 0 := by omega
      have hA0 : 0 ≤ -intOfZ (signed n) := by omega
      have hAhi : -intOfZ (signed n) ≤ (2147483648 : Int) := by omega
      have hQlo' : (-intOfZ (signed n)).tdiv (intOfZ (signed d)) ≤ (2147483648 : Int) := by
        simpa [show intOfZ (signed n) ≤ 0 by omega] using
          (Int.tdiv_le_of_le_mul (a := -intOfZ (signed n))
            (b := (2147483648 : Int)) hDpos (by omega))
      have hQhi' : 0 ≤ (-intOfZ (signed n)).tdiv (intOfZ (signed d)) := by
        exact Int.tdiv_nonneg hA0 (Int.le_of_lt hDpos)
      constructor
      · change (-2147483648 : Int) ≤ intOfZ (zQuot (signed n) (signed d))
        rw [hqeq]
        have hform : Int.tdiv (intOfZ (signed n)) (intOfZ (signed d)) =
            -((-intOfZ (signed n)).tdiv (intOfZ (signed d))) := by
          simpa using (Int.neg_tdiv (-intOfZ (signed n)) (intOfZ (signed d)))
        rw [hform]
        omega
      · change intOfZ (zQuot (signed n) (signed d)) ≤ (2147483647 : Int)
        rw [hqeq]
        have hform : Int.tdiv (intOfZ (signed n)) (intOfZ (signed d)) =
            -((-intOfZ (signed n)).tdiv (intOfZ (signed d))) := by
          simpa using (Int.neg_tdiv (-intOfZ (signed n)) (intOfZ (signed d)))
        rw [hform]
        omega
  · have hDneg : intOfZ (signed d) < 0 := by omega
    let c : Int := -intOfZ (signed d)
    have hcpos : 0 < c := by
      dsimp [c]
      omega
    have hqnegden : Int.tdiv (intOfZ (signed n)) (intOfZ (signed d)) =
        -(Int.tdiv (intOfZ (signed n)) c) := by
      dsimp [c]
      simp [Int.tdiv_neg]
    by_cases hNnonneg : 0 ≤ intOfZ (signed n)
    · have hQlo' : Int.tdiv (intOfZ (signed n)) c ≤ (2147483648 : Int) := by
        simpa [hNnonneg] using
          (Int.tdiv_le_of_le_mul (a := intOfZ (signed n))
            (b := (2147483648 : Int)) hcpos (by omega))
      have hQhi' : 0 ≤ Int.tdiv (intOfZ (signed n)) c := by
        exact Int.tdiv_nonneg hNnonneg (Int.le_of_lt hcpos)
      constructor
      · change (-2147483648 : Int) ≤ intOfZ (zQuot (signed n) (signed d))
        rw [hqeq, hqnegden]
        omega
      · change intOfZ (zQuot (signed n) (signed d)) ≤ (2147483647 : Int)
        rw [hqeq, hqnegden]
        omega
    · have hNneg : intOfZ (signed n) < 0 := by omega
      have hA0 : 0 ≤ -intOfZ (signed n) := by omega
      have hAhi : -intOfZ (signed n) ≤ (2147483648 : Int) := by omega
      have hQlo' : 0 ≤ (-intOfZ (signed n)).tdiv c := by
        exact Int.tdiv_nonneg hA0 (Int.le_of_lt hcpos)
      by_cases hc_one : c = 1
      · have hQeq : (-intOfZ (signed n)).tdiv c = -intOfZ (signed n) := by
          rw [hc_one]
          exact Int.tdiv_one _
        have hQhi : (-intOfZ (signed n)).tdiv c ≤ (2147483647 : Int) := by
          rw [hQeq]
          by_cases hbad : -intOfZ (signed n) ≤ (2147483647 : Int)
          · exact hbad
          · exfalso
            have hNmin : intOfZ (signed n) = (-2147483648 : Int) := by omega
            have hnmin : n = repr min_signed := by
              apply signed_injective_try
              have hsmin : signed (repr min_signed) = min_signed := by
                rw [signed_repr_eq_proof]
                decide
              apply intOfZ_injective
              change intOfZ (signed n) = intOfZ (signed (repr min_signed))
              rw [hNmin, hsmin]
              rfl
            have hDminus : signed d = zOpp zOne := by
              apply intOfZ_injective
              simp only [zOpp, ZArith.BinInt.Z.opp, intOfZ_zOfInt]
              dsimp [c] at hc_one
              have hone : intOfZ zOne = (1 : Int) := by rfl
              rw [hone]
              omega
            have hdminus : d = mone := by
              apply signed_injective_try
              rw [hDminus, signed_mone_proof]
            exact hcond.elim (fun hn => hn hnmin) (fun hd' => hd' hdminus)
        constructor
        · change (-2147483648 : Int) ≤ intOfZ (zQuot (signed n) (signed d))
          rw [hqeq, hqnegden]
          have hform : Int.tdiv (intOfZ (signed n)) c =
              -((-intOfZ (signed n)).tdiv c) := by
            simpa using (Int.neg_tdiv (-intOfZ (signed n)) c)
          rw [hform, hQeq]
          omega
        · change intOfZ (zQuot (signed n) (signed d)) ≤ (2147483647 : Int)
          rw [hqeq, hqnegden]
          have hform : Int.tdiv (intOfZ (signed n)) c =
              -((-intOfZ (signed n)).tdiv c) := by
            simpa using (Int.neg_tdiv (-intOfZ (signed n)) c)
          rw [hform, hQeq]
          omega
      · have hc_two : (2 : Int) ≤ c := by omega
        have hQhi : (-intOfZ (signed n)).tdiv c ≤ (2147483647 : Int) := by
          simpa [show intOfZ (signed n) ≤ 0 by omega] using
            (Int.tdiv_le_of_le_mul (a := -intOfZ (signed n))
              (b := (2147483647 : Int)) hcpos (by omega))
        constructor
        · change (-2147483648 : Int) ≤ intOfZ (zQuot (signed n) (signed d))
          rw [hqeq, hqnegden]
          have hform : Int.tdiv (intOfZ (signed n)) c =
              -((-intOfZ (signed n)).tdiv c) := by
            simpa using (Int.neg_tdiv (-intOfZ (signed n)) c)
          rw [hform]
          omega
        · change intOfZ (zQuot (signed n) (signed d)) ≤ (2147483647 : Int)
          rw [hqeq, hqnegden]
          have hform : Int.tdiv (intOfZ (signed n)) c =
              -((-intOfZ (signed n)).tdiv c) := by
            simpa using (Int.neg_tdiv (-intOfZ (signed n)) c)
          rw [hform]
          omega

theorem divmods2_divs_mods_proof : divmods2_divs_mods := by
  intro n d hd hcond
  unfold divmods2 divs mods
  by_cases hdz : d = zero
  · exact (hd hdz).elim
  · simp [eq_dec, hdz]
    rw [suffix_divmods2_n_eq n]
    have hqb := suffix_divmods2_q_bounds n d hdz hcond
    rcases hqb with ⟨hqbLo, hqbHi⟩
    cases hlo : CompCert4Lean.Lib.Coqlib.zle
        min_signed (zQuot (signed n) (signed d)) with
    | left hlo' =>
        cases hhi : CompCert4Lean.Lib.Coqlib.zle
            (zQuot (signed n) (signed d)) max_signed with
        | left hhi' => rfl
        | right hhi' =>
            exfalso
            change intOfZ max_signed <
                intOfZ (zQuot (signed n) (signed d)) at hhi'
            change intOfZ (zQuot (signed n) (signed d)) ≤ intOfZ max_signed at hqbHi
            omega
    | right hlo' =>
        exfalso
        change intOfZ (zQuot (signed n) (signed d)) < intOfZ min_signed at hlo'
        change intOfZ min_signed ≤ intOfZ (zQuot (signed n) (signed d)) at hqbLo
        omega

theorem bits_zero_proof : bits_zero := by
  intro i
  have hz : zero.val = 0 := by rfl
  cases i with
  | Zneg _ => rfl
  | Z0 =>
      change zero.val.testBit 0 = false
      simp [hz]
  | Zpos p =>
      change zero.val.testBit (WordCore.positiveToNat p) = false
      simp [hz]

theorem swap_cmp_proof : swap_cmp := by
  intro c x y
  cases c <;>
    simp [cmp, WordCore.cmp, swap_comparison, WordCore.eq, eq_comm]

theorem or_zero_proof : or_zero := by
  intro x
  unfold or WordCore.or
  change repr (zOfNat (Nat.lor x.val zero.val)) = x
  rw [show zero.val = 0 by rfl]
  rw [show Nat.lor x.val 0 = x.val by
    simpa only [Nat.lor_eq] using Nat.or_zero x.val]
  rw [show zOfNat x.val = unsigned x by
    exact (WordCore.intval_eq_zOfNat_val x).symm]
  exact repr_unsigned_proof x

private theorem suffix_bits_shru_nat (x y : int) (n : Nat) :
    testbit (shru x y) (zOfNat n) =
      zltSelect (zAdd (zOfNat n) (unsigned y)) zwordsize
        (testbit x (zAdd (zOfNat n) (unsigned y))) false := by
  have hy : unsigned y = zOfNat y.val :=
    WordCore.intval_eq_zOfNat_val y
  have hadd : zAdd (zOfNat n) (unsigned y) = zOfNat (n + y.val) := by
    rw [hy]
    apply intOfZ_injective
    simp only [zAdd, ZArith.BinInt.Z.add, zOfNat,
      ZArith.BinInt.Z.of_nat, intOfZ_zOfInt, Int.ofNat_eq_natCast,
      Int.natCast_add]
  rw [hadd, suffix_testbit_nat, suffix_shru_val]
  rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
  rw [Nat.add_comm y.val n]
  cases hlt : CompCert4Lean.Lib.Coqlib.zlt (zOfNat (n + y.val)) zwordsize with
  | left hlt' =>
      simp only [zltSelect, sumboolSelect, hlt]
      exact (suffix_testbit_nat x (n + y.val)).symm
  | right hlt' =>
      simp only [zltSelect, sumboolSelect, hlt]
      apply Nat.testBit_lt_two_pow
      have hsum : wordsize ≤ n + y.val := by
        change zLe zwordsize (zOfNat (n + y.val)) at hlt'
        change intOfZ zwordsize ≤ intOfZ (zOfNat (n + y.val)) at hlt'
        simp only [zwordsize, zOfNat, ZArith.BinInt.Z.of_nat,
          intOfZ_zOfInt] at hlt'
        exact Int.ofNat_le.mp hlt'
      have hpow : 2 ^ wordsize ≤ 2 ^ (n + y.val) :=
        Nat.pow_le_pow_right Nat.zero_lt_two hsum
      exact Nat.lt_of_lt_of_le (WordCore.val_lt x) hpow

theorem bits_shru_proof : bits_shru := by
  intro x y i hi
  cases i with
  | Zneg p =>
      have h := hi.1
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at h
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpI : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr hp
      omega
  | Z0 =>
      exact suffix_bits_shru_nat x y 0
  | Zpos p =>
      have hz : zOfNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = .Zpos p := by
        exact ZArith.Znat.positive_nat_Z p
      rw [← hz] at hi ⊢
      exact suffix_bits_shru_nat x y
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)

theorem half_modulus_pos_proof : half_modulus_pos := by
  change zLt zZero (zTwoPowerNat (wordsize - 1))
  change (0 : Int) < Int.ofNat (2 ^ (wordsize - 1))
  decide

theorem same_bits_eq_proof : same_bits_eq := by
  intro x y h
  apply WordCore.ext_of_val_eq
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < wordsize
  · have hi0 : zLe zZero (zOfNat i) := by
      change 0 ≤ intOfZ (zOfNat i)
      simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
      exact Int.natCast_nonneg _
    have hil : zLt (zOfNat i) zwordsize := by
      change intOfZ (zOfNat i) < intOfZ (zOfNat wordsize)
      simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
      exact Int.ofNat_lt.mpr (by simpa [wordsize] using hi)
    have hh := h (zOfNat i) ⟨hi0, hil⟩
    rw [suffix_testbit_nat, suffix_testbit_nat] at hh
    exact hh
  · have hle : wordsize ≤ i := Nat.le_of_not_gt hi
    have hpow : 2 ^ wordsize ≤ 2 ^ i :=
      Nat.pow_le_pow_right Nat.zero_lt_two hle
    have hxlt : x.val < 2 ^ i :=
      Nat.lt_of_lt_of_le (WordCore.val_lt x) hpow
    have hylt : y.val < 2 ^ i :=
      Nat.lt_of_lt_of_le (WordCore.val_lt y) hpow
    rw [Nat.testBit_lt_two_pow hxlt, Nat.testBit_lt_two_pow hylt]

theorem ltu_not_proof : ltu_not := by
  intro x y
  change zltSelect (unsigned y) (unsigned x) true false =
    (!zltSelect (unsigned x) (unsigned y) true false &&
      !decide (x.intval = y.intval))
  cases hxy : CompCert4Lean.Lib.Coqlib.zlt (unsigned y) (unsigned x) with
  | left hlt =>
      cases hrev : CompCert4Lean.Lib.Coqlib.zlt (unsigned x) (unsigned y) with
      | left hrevlt =>
          exact (Int.lt_asymm hlt hrevlt).elim
      | right hrevge =>
          have hne : x.intval ≠ y.intval := by
            intro heq
            have hlt' : intOfZ (unsigned y) < intOfZ (unsigned x) := hlt
            change intOfZ y.intval < intOfZ x.intval at hlt'
            rw [heq] at hlt'
            exact (Int.lt_irrefl _ hlt').elim
          simp [zltSelect, sumboolSelect, hxy, hrev, hne]
  | right hge =>
      cases hrev : CompCert4Lean.Lib.Coqlib.zlt (unsigned x) (unsigned y) with
      | left hrevlt =>
          simp [zltSelect, sumboolSelect, hxy, hrev]
      | right hrevge =>
          have hge' : intOfZ (unsigned x) ≤ intOfZ (unsigned y) := by
            exact hge
          have hrevge' : intOfZ (unsigned y) ≤ intOfZ (unsigned x) := by
            exact hrevge
          have huv : unsigned y = unsigned x := by
            apply intOfZ_injective
            exact Int.le_antisymm hrevge' hge'
          have heqv : x.intval = y.intval := by
            simpa only [unsigned, WordCore.unsigned] using huv.symm
          simp [zltSelect, sumboolSelect, hxy, hrev, heqv]

theorem divmodu2_divu_modu_proof : divmodu2_divu_modu := by
  intro n d hd
  unfold divmodu2 divu modu
  by_cases hdz : d = zero
  · exact (hd hdz).elim
  · have hsum :
        zAdd (zMul (unsigned zero) modulus) (unsigned n) = unsigned n := by
      apply intOfZ_injective
      simp only [zAdd, zMul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
        intOfZ_zOfInt]
      have hz : intOfZ (unsigned zero) = (0 : Int) := by rfl
      rw [hz]
      omega
    rw [hsum]
    simp [eq_dec, hdz]
    have hn0 : (0 : Int) ≤ intOfZ (unsigned n) := by
      have hn := n.intrange.1
      change (-1 : Int) < intOfZ n.intval at hn
      change 0 ≤ intOfZ n.intval
      omega
    have hnmax : intOfZ (unsigned n) ≤ intOfZ max_unsigned := by
      have hn := n.intrange.2
      change intOfZ n.intval < intOfZ modulus at hn
      change intOfZ n.intval ≤ intOfZ modulus - 1
      omega
    have hd0 : (0 : Int) ≤ intOfZ (unsigned d) := by
      have hd' := d.intrange.1
      change (-1 : Int) < intOfZ d.intval at hd'
      change 0 ≤ intOfZ d.intval
      omega
    have hdpos : (0 : Int) < intOfZ (unsigned d) := by
      have hdne : intOfZ (unsigned d) ≠ 0 := by
        intro hzero
        apply hd
        apply WordCore.ext
        apply intOfZ_injective
        change intOfZ d.intval = 0 at hzero
        have hz0 : intOfZ zero.intval = 0 := by rfl
        exact hzero.trans hz0.symm
      omega
    have hqbound : zLe (ZArith.BinInt.Z.div_eucl
        (unsigned n) (unsigned d)).1 max_unsigned := by
      have hb := CompCert4Lean.Lib.Coqlib.Zdiv_interval_1
        zZero (zAdd max_unsigned zOne) (unsigned n) (unsigned d)
        (by
          change (0 : Int) ≤ 0
          omega) (by
          change (0 : Int) < intOfZ (zAdd max_unsigned zOne)
          simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
          change (0 : Int) < (2 ^ wordsize : Int)
          exact Int.pow_pos (by omega))
        (by exact hdpos)
        (by
          constructor
          · change intOfZ (zMul zZero (unsigned d)) ≤ intOfZ (unsigned n)
            simp only [zMul, ZArith.BinInt.Z.mul]
            simp only [intOfZ_zOfInt]
            have hz0 : intOfZ zZero = (0 : Int) := by rfl
            rw [hz0, Int.zero_mul]
            exact hn0
          · change intOfZ (unsigned n) < intOfZ
              (zMul (zAdd max_unsigned zOne) (unsigned d))
            have hmax : intOfZ max_unsigned = (2 ^ wordsize : Int) - 1 := by
              rfl
            have hone : intOfZ zOne = (1 : Int) := by rfl
            have hmul : intOfZ (unsigned n) ≤
                ((2 ^ wordsize : Int) - 1) * intOfZ (unsigned d) := by
              have hnd := Int.mul_le_mul_of_nonneg_left
                (show (1 : Int) ≤ intOfZ (unsigned d) by omega) hn0
              have hmaxd := Int.mul_le_mul_of_nonneg_right hnmax hd0
              exact Int.le_trans (by simpa using hnd) (by simpa [hmax] using hmaxd)
            have hstrict : ((2 ^ wordsize : Int) - 1) * intOfZ (unsigned d) <
                (((2 ^ wordsize : Int) - 1) + 1) * intOfZ (unsigned d) := by
              apply Int.mul_lt_mul_of_pos_right _ hdpos
              omega
            have hlt : intOfZ (unsigned n) <
                (((2 ^ wordsize : Int) - 1) + 1) * intOfZ (unsigned d) :=
              Int.lt_of_le_of_lt hmul hstrict
            simpa [zMul, zAdd, ZArith.BinInt.Z.mul,
              ZArith.BinInt.Z.add, intOfZ_zOfInt, hmax, hone] using hlt)
      have hqhi := hb.2
      change intOfZ (ZArith.BinInt.Z.div_eucl
          (unsigned n) (unsigned d)).1 <
        intOfZ (zAdd max_unsigned zOne) at hqhi
      change intOfZ (ZArith.BinInt.Z.div_eucl
          (unsigned n) (unsigned d)).1 ≤ intOfZ max_unsigned
      simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hqhi ⊢
      have hmax : intOfZ max_unsigned = (2 ^ wordsize : Int) - 1 := by
        rfl
      have hone : intOfZ zOne = (1 : Int) := by rfl
      rw [hmax] at hqhi ⊢
      rw [hone] at hqhi
      omega
    cases hle : CompCert4Lean.Lib.Coqlib.zle
        (ZArith.BinInt.Z.div_eucl (unsigned n) (unsigned d)).1 max_unsigned with
    | left hle' =>
        simp [hle, ZArith.BinInt.Z.div_eucl]
        constructor <;> rfl
    | right hle' =>
        exfalso
        exact (Int.not_lt_of_ge hqbound hle').elim

theorem eq_false_proof : eq_false := by
  intro x y hxy
  change decide (x.intval = y.intval) = false
  have hval : x.intval ≠ y.intval := by
    intro h
    exact hxy (WordCore.ext h)
  simp [hval]

theorem negate_cmp_proof : negate_cmp := by
  intro c x y
  cases c <;> simp [cmp, WordCore.cmp, negate_comparison]

theorem eq_signed_proof : eq_signed := by
  intro x y
  change decide (x.intval = y.intval) =
    sumboolSelect (CompCert4Lean.Lib.Coqlib.zeq (signed x) (signed y)) true false
  cases h : CompCert4Lean.Lib.Coqlib.zeq (signed x) (signed y) with
  | left hs =>
      have hxy : x = y := signed_injective_try hs
      subst y
      simp [sumboolSelect]
  | right hs =>
      have hxy : x ≠ y := by
        intro heq
        apply hs
        simpa [heq]
      have hval : x.intval ≠ y.intval := by
        intro hv
        exact hxy (WordCore.ext hv)
      simp [sumboolSelect, hval]

private theorem suffix_xor_val_exact (x y : int) :
    (xor x y).val = Nat.xor x.val y.val := by
  have hu := suffix_xor_unsigned x y
  change (xor x y).intval = zOfNat (Nat.xor x.val y.val) at hu
  rw [WordCore.intval_eq_zOfNat_val] at hu
  have hi := congrArg intOfZ hu
  simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hi
  exact Int.ofNat.inj hi

private theorem suffix_bits_xor_nat (x y : int) (n : Nat) :
    testbit (xor x y) (zOfNat n) =
      Bool.xor (testbit x (zOfNat n)) (testbit y (zOfNat n)) := by
  rw [suffix_testbit_nat, suffix_testbit_nat, suffix_testbit_nat]
  rw [suffix_xor_val_exact, Nat.xor_eq, Nat.testBit_xor]

theorem bits_xor_proof : bits_xor := by
  intro x y i hi
  cases i with
  | Zneg p =>
      have h := hi.1
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at h
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpI : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr hp
      omega
  | Z0 =>
      exact suffix_bits_xor_nat x y 0
  | Zpos p =>
      have hz : zOfNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = .Zpos p := by
        exact ZArith.Znat.positive_nat_Z p
      rw [← hz] at hi ⊢
      exact suffix_bits_xor_nat x y
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)

theorem eq_true_proof : eq_true := by
  intro x
  change decide (x.intval = x.intval) = true
  simp

theorem unsigned_range_2_proof : unsigned_range_2 := by
  intro i
  constructor
  · have h := i.intrange.1
    change (-1 : Int) < intOfZ (unsigned i) at h
    change 0 ≤ intOfZ (unsigned i)
    omega
  · have h := i.intrange.2
    change intOfZ (unsigned i) < intOfZ modulus at h
    change intOfZ (unsigned i) ≤ intOfZ max_unsigned
    change intOfZ (unsigned i) ≤ (2 ^ wordsize : Int) - 1
    change intOfZ (unsigned i) < (2 ^ wordsize : Int) at h
    omega

theorem eqm_signed_unsigned_proof : eqm_signed_unsigned := by
  intro x
  unfold eqm WordCore.eqm signed WordCore.signed
  cases h : CompCert4Lean.Lib.Coqlib.zlt
      (WordCore.unsigned x) (zTwoPowerNat (wordsize - 1)) with
  | left hlt =>
      simp only [zltSelect, sumboolSelect, h]
      exact CompCert4Lean.Lib.Zbits.eqmod_refl modulus (unsigned x)
  | right hge =>
      simp only [zltSelect, sumboolSelect, h]
      unfold CompCert4Lean.Lib.Zbits.eqmod
      refine ⟨zOpp zOne, ?_⟩
      apply intOfZ_injective
      simp only [unsigned, zOne, modulus, ZArith.BinInt.Z.add,
        ZArith.BinInt.Z.mul, ZArith.BinInt.Z.sub,
        ZArith.BinInt.Z.opp, intOfZ_zOfInt]
      have hone : intOfZ (Numbers.BinNums.Z.Zpos xH) = (1 : Int) := by rfl
      rw [hone]
      omega

private theorem suffix_repr_nat_val (a : Nat) (ha : a < 2 ^ wordsize) :
    (WordCore.repr wordsize (zOfInt (Int.ofNat a))).val = a := by
  rw [WordCore.val_repr]
  change Int.toNat (Int.ofNat a % Int.ofNat (2 ^ wordsize)) = a
  simp only [Int.ofNat_eq_natCast]
  have hbridge := Int.emod_natAbs_of_nonneg
    (x := (a : Int)) (n := 2 ^ wordsize) (Int.natCast_nonneg _)
  simp only [Int.natAbs_natCast] at hbridge
  rw [← hbridge, Nat.mod_eq_of_lt ha]

private theorem suffix_repr_testbit_nat (a i : Nat) (hi : i < wordsize) :
    testbit (WordCore.repr wordsize (zOfInt (Int.ofNat a))) (zOfNat i) =
      a.testBit i := by
  rw [suffix_testbit_nat, WordCore.val_repr]
  change (Int.toNat (Int.ofNat a % Int.ofNat (2 ^ wordsize))).testBit i = a.testBit i
  simp only [Int.ofNat_eq_natCast]
  have hbridge := Int.emod_natAbs_of_nonneg
    (x := (a : Int)) (n := 2 ^ wordsize) (Int.natCast_nonneg _)
  simp only [Int.natAbs_natCast] at hbridge
  rw [← hbridge, Nat.testBit_mod_two_pow]
  simp [hi]

private theorem suffix_repr_val_testbit_nat (a i : Nat) (hi : i < wordsize) :
    (WordCore.repr wordsize (zOfInt (Int.ofNat a))).val.testBit i =
      a.testBit i := by
  rw [WordCore.val_repr]
  change (Int.toNat (Int.ofNat a % Int.ofNat (2 ^ wordsize))).testBit i = a.testBit i
  simp only [Int.ofNat_eq_natCast]
  have hbridge := Int.emod_natAbs_of_nonneg
    (x := (a : Int)) (n := 2 ^ wordsize) (Int.natCast_nonneg _)
  simp only [Int.natAbs_natCast] at hbridge
  rw [← hbridge, Nat.testBit_mod_two_pow]
  simp [hi]


private theorem suffix_repr_sub_nat_val (r m : Nat)
    (hrm : r < m) (hmw : m ≤ 2 ^ wordsize) :
    (WordCore.repr wordsize
      (zOfInt (Int.ofNat r - Int.ofNat m))).val =
      2 ^ wordsize - (m - r) := by
  rw [WordCore.val_repr]
  change Int.toNat
      ((Int.ofNat r - Int.ofNat m) % Int.ofNat (2 ^ wordsize)) =
    2 ^ wordsize - (m - r)
  have hsub : (Int.ofNat r - Int.ofNat m) = -Int.ofNat (m - r) := by
    simp only [Int.ofNat_eq_natCast, Int.natCast_sub (Nat.le_of_lt hrm)]
    omega
  rw [hsub, Int.neg_emod_eq_sub_emod]
  have hnonneg : (0 : Int) ≤ Int.ofNat (2 ^ wordsize) - Int.ofNat (m - r) := by
    simp only [Int.ofNat_eq_natCast]
    omega
  have hlt : Int.ofNat (2 ^ wordsize) - Int.ofNat (m - r) <
      Int.ofNat (2 ^ wordsize) := by
    simp only [Int.ofNat_eq_natCast]
    have hmr : 0 < m - r := Nat.sub_pos_of_lt hrm
    omega
  rw [Int.emod_eq_of_lt hnonneg hlt]
  have hmr_le : m - r ≤ 2 ^ wordsize := by omega
  have hcast := Int.ofNat_sub hmr_le
  exact (congrArg Int.toNat hcast).symm.trans (Int.toNat_natCast _)

private theorem suffix_sign_ext_testbit_nat (k : Nat) (x : int) (i : Nat)
    (hi : i < wordsize) :
    testbit (sign_ext (zOfNat (k + 1)) x) (zOfNat i) =
      if i < k + 1 then x.val.testBit i else x.val.testBit k := by
  rw [suffix_testbit_nat, suffix_sign_ext_nat]
  by_cases hr : x.val % 2 ^ (k + 1) < 2 ^ k
  · rw [if_pos hr, suffix_repr_val_testbit_nat]
    rw [Nat.testBit_mod_two_pow]
    by_cases hik : i < k + 1
    · simp [hik]
    · simp [hik]
      have hmod := Nat.testBit_mod_two_pow x.val (k + 1) k
      have hkm : k < k + 1 := by omega
      simp only [hkm, decide_true] at hmod
      have hmod' : (x.val % 2 ^ (k + 1)).testBit k = x.val.testBit k := by
        simpa using hmod
      have hrbit : (x.val % 2 ^ (k + 1)).testBit k = false :=
        Nat.testBit_lt_two_pow (by omega)
      rw [← hmod', hrbit]
    exact hi
  ·
    have hxlt : x.val < 2 ^ wordsize := WordCore.val_lt x
    have hrlt : x.val % 2 ^ (k + 1) < 2 ^ (k + 1) :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    have hkmw : k + 1 ≤ wordsize := by
      by_cases hkmw : k + 1 ≤ wordsize
      · exact hkmw
      · have hkw : wordsize ≤ k := by omega
        have hpow : 2 ^ wordsize ≤ 2 ^ k :=
          Nat.pow_le_pow_right Nat.zero_lt_two hkw
        have hxM : x.val < 2 ^ (k + 1) := by
          exact Nat.lt_of_lt_of_le hxlt
            (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
        have hrx : x.val % 2 ^ (k + 1) = x.val := Nat.mod_eq_of_lt hxM
        have hrge : 2 ^ k ≤ x.val := by
          rw [← hrx]
          exact Nat.le_of_not_gt hr
        omega
    have hmle : 2 ^ (k + 1) ≤ 2 ^ wordsize :=
      Nat.pow_le_pow_right Nat.zero_lt_two hkmw
    have hrepr := suffix_repr_sub_nat_val
      (x.val % 2 ^ (k + 1)) (2 ^ (k + 1)) hrlt hmle
    rw [if_neg hr, hrepr]
    let r := x.val % 2 ^ (k + 1)
    let m := 2 ^ (k + 1)
    let w := 2 ^ wordsize
    have hrm : r < m := by exact hrlt
    have hkm : k < k + 1 := by omega
    have hwm : w = m * 2 ^ (wordsize - (k + 1)) := by
      dsimp [w, m]
      rw [← Nat.pow_add]
      congr 1
      omega
    have hbase : w - m = m * (2 ^ (wordsize - (k + 1)) - 1) := by
      rw [hwm]
      calc
        m * 2 ^ (wordsize - (k + 1)) - m =
            m * 2 ^ (wordsize - (k + 1)) - m * 1 := by rw [Nat.mul_one]
        _ = m * (2 ^ (wordsize - (k + 1)) - 1) :=
          (Nat.mul_sub_left_distrib m (2 ^ (wordsize - (k + 1))) 1).symm
    have hout : (w - (m - r)) % m = r := by
      have hmw : m ≤ w := by exact hmle
      have hdecomp : w - (m - r) = (w - m) + r := by omega
      rw [hdecomp, hbase, Nat.add_mod, Nat.mul_mod_right]
      simp only [Nat.zero_add]
      rw [Nat.mod_mod, Nat.mod_eq_of_lt hrm]
    by_cases hik : i < k + 1
    · have hlow : (w - (m - r)).testBit i = r.testBit i := by
        have hh := Nat.testBit_mod_two_pow (w - (m - r)) (k + 1) i
        simp only [hik, decide_true, true_and] at hh
        rw [hout] at hh
        exact hh.symm
      have hxr := Nat.testBit_mod_two_pow x.val (k + 1) i
      have hxr' : (x.val % 2 ^ (k + 1)).testBit i = x.val.testBit i := by
        simpa [hik] using hxr
      rw [hlow]
      simpa [hik, hxr']
    · have hq : m - r - 1 < 2 ^ i := by
        have hrpos : 0 < r := by
          have hrge : 2 ^ k ≤ r := Nat.le_of_not_gt hr
          omega
        have hpowi : 2 ^ (k + 1) ≤ 2 ^ i :=
          Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_of_not_gt hik)
        exact Nat.lt_of_lt_of_le (by omega) hpowi
      have hqbit : (m - r - 1).testBit i = false :=
        Nat.testBit_lt_two_pow hq
      have hmrpos : 0 < m - r := Nat.sub_pos_of_lt hrm
      have hform : w - (m - r) = 2 ^ wordsize - ((m - r - 1) + 1) := by
        omega
      have hhigh : (w - (m - r)).testBit i = true := by
        have hqW : m - r - 1 < 2 ^ wordsize :=
          Nat.lt_of_lt_of_le hq
            (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_of_lt hi))
        have htb := Nat.testBit_two_pow_sub_succ hqW i
        rw [hform, htb]
        simp [hi, hqbit]
      have hrbit : r.testBit k = true := by
        rw [Nat.testBit_eq_decide_div_mod_eq]
        apply decide_eq_true
        have hdiv := Nat.div_eq_of_lt_le
          (k := 1) (n := 2 ^ k) (m := r) (by omega)
          (by
            rw [show (1 + 1) * 2 ^ k = 2 ^ (k + 1) by
              rw [Nat.pow_succ]
              omega]
            exact hrm)
        rw [hdiv]
      have hxbit : x.val.testBit k = true := by
        have hxr := Nat.testBit_mod_two_pow x.val (k + 1) k
        have hxr' : (x.val % 2 ^ (k + 1)).testBit k = x.val.testBit k := by
          simpa [hkm] using hxr
        rw [← hxr', hrbit]
      rw [hhigh]
      simp [hik, hxbit]

private theorem suffix_zltSelect_nat_index (i n : Nat) (hn : 0 < n) :
    zltSelect (zOfNat i) (zOfNat n) (zOfNat i)
        (zSub (zOfNat n) zOne) =
      if i < n then zOfNat i else zOfNat (n - 1) := by
  have hsub : zSub (zOfNat n) zOne = zOfNat (n - 1) := by
    apply intOfZ_injective
    simp only [zSub, ZArith.BinInt.Z.sub, zOfNat,
      ZArith.BinInt.Z.of_nat, zOne, intOfZ_zOfInt]
    change Int.ofNat n - 1 = Int.ofNat (n - 1)
    simp only [Int.ofNat_eq_natCast]
    omega
  rw [hsub]
  cases hs : CompCert4Lean.Lib.Coqlib.zlt (zOfNat i) (zOfNat n) with
  | left hlt =>
      have hin : i < n := by
        change intOfZ (zOfNat i) < intOfZ (zOfNat n) at hlt
        simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hlt
        exact Int.ofNat_lt.mp hlt
      simp [zltSelect, sumboolSelect, hs, hin]
  | right hge =>
      have hin : ¬ i < n := by
        change intOfZ (zOfNat n) ≤ intOfZ (zOfNat i) at hge
        simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hge
        exact Nat.not_lt.mpr (Int.ofNat_le.mp hge)
      simp [zltSelect, sumboolSelect, hs, hin]

private theorem suffix_sign_ext_testbit_pos_nat (n : Nat) (hn : 0 < n)
    (x : int) (i : Nat) (hi : i < wordsize) :
    testbit (sign_ext (zOfNat n) x) (zOfNat i) =
      testbit x
        (zltSelect (zOfNat i) (zOfNat n) (zOfNat i)
          (zSub (zOfNat n) zOne)) := by
  have hnstep : n = (n - 1) + 1 := by omega
  have hmain := suffix_sign_ext_testbit_nat (n - 1) x i hi
  rw [← hnstep] at hmain
  rw [suffix_zltSelect_nat_index i n hn]
  by_cases hin : i < n
  · simpa [hin, suffix_testbit_nat] using hmain
  · simpa [hin, suffix_testbit_nat] using hmain

private theorem suffix_sign_ext_nonpos (n : Z) (x : int)
    (hn : zLe n zZero) : sign_ext n x = zero := by
  unfold sign_ext WordCore.sign_ext
  have hpred : Int.toNat (intOfZ (ZArith.BinInt.Z.pred n)) = 0 := by
    rw [Int.toNat_eq_zero]
    change intOfZ (ZArith.BinInt.Z.sub n zOne) ≤ 0
    simp only [ZArith.BinInt.Z.sub, zOne, intOfZ_zOfInt]
    have hone : intOfZ (Numbers.BinNums.Z.Zpos xH) = (1 : Int) := by rfl
    rw [hone]
    change intOfZ n ≤ 0 at hn
    omega
  have hsel : sumboolSelect (CompCert4Lean.Lib.Coqlib.zlt zZero n)
      (zOpp zOne) zZero = zZero := by
    cases hs : CompCert4Lean.Lib.Coqlib.zlt zZero n with
    | left hlt =>
        exfalso
        change 0 < intOfZ n at hlt
        change intOfZ n ≤ 0 at hn
        omega
    | right _ => rfl
  simp [ZArith.BinInt.Z.iter, hpred, hsel]
  change WordCore.repr wordsize zZero = zero
  rfl

private theorem suffix_testbit_negative_index (x : int) (j : Z)
    (hj : intOfZ j < 0) : testbit x j = false := by
  cases j with
  | Z0 =>
      change (0 : Int) < 0 at hj
      omega
  | Zpos p =>
      change Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) < 0 at hj
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpI : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr hp
      omega
  | Zneg _ => rfl

private theorem suffix_bits_sign_ext_nat (n : Z) (x : int) (i : Nat)
    (hi : i < wordsize) :
    testbit (sign_ext n x) (zOfNat i) =
      testbit x
        (zltSelect (zOfNat i) n (zOfNat i) (zSub n zOne)) := by
  by_cases hnpos : zLt zZero n
  · have hnnonneg : zLe zZero n := by
      change 0 ≤ intOfZ n
      change 0 < intOfZ n at hnpos
      omega
    have hnrepr : zOfNat (zToNat n) = n :=
      ZArith.Znat.Z2Nat.id n hnnonneg
    have hnNat : 0 < zToNat n := by
      change 0 < Int.toNat (intOfZ n)
      by_cases hz : Int.toNat (intOfZ n) = 0
      · rw [Int.toNat_eq_zero] at hz
        change 0 < intOfZ n at hnpos
        omega
      · exact Nat.pos_of_ne_zero hz
    rw [← hnrepr]
    exact suffix_sign_ext_testbit_pos_nat (zToNat n) hnNat x i hi
  · have hnle : zLe n zZero := by
      change intOfZ n ≤ 0
      change ¬ 0 < intOfZ n at hnpos
      omega
    have hsel : zltSelect (zOfNat i) n (zOfNat i) (zSub n zOne) =
        zSub n zOne := by
      cases hs : CompCert4Lean.Lib.Coqlib.zlt (zOfNat i) n with
      | left hlt =>
          exfalso
          change intOfZ (zOfNat i) < intOfZ n at hlt
          simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hlt
          change intOfZ n ≤ 0 at hnle
          have hi0 : (0 : Int) ≤ Int.ofNat i := Int.natCast_nonneg i
          omega
      | right _ => simp [zltSelect, sumboolSelect, hs]
    have hidxneg : intOfZ (zSub n zOne) < 0 := by
      simp only [zSub, ZArith.BinInt.Z.sub, zOne, intOfZ_zOfInt]
      have hone : intOfZ (Numbers.BinNums.Z.Zpos xH) = (1 : Int) := by rfl
      rw [hone]
      change intOfZ n ≤ 0 at hnle
      omega
    rw [suffix_sign_ext_nonpos n x hnle, hsel]
    rw [suffix_testbit_negative_index x (zSub n zOne) hidxneg]
    rw [suffix_testbit_nat]
    have hz : zero.val = 0 := by rfl
    simp [hz]

theorem bits_sign_ext_proof : bits_sign_ext := by
  intro n x i hi
  cases i with
  | Zneg p =>
      have h := hi.1
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at h
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpI : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr hp
      omega
  | Z0 =>
      exact suffix_bits_sign_ext_nat n x 0 (by decide)
  | Zpos p =>
      have hz : zOfNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = .Zpos p :=
        ZArith.Znat.positive_nat_Z p
      rw [← hz] at hi ⊢
      have hiNat : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p <
          wordsize := by
        have hb := hi.2
        change intOfZ (zOfNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) <
          intOfZ (zOfNat wordsize) at hb
        simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hb
        exact Int.ofNat_lt.mp hb
      exact suffix_bits_sign_ext_nat n x
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) hiNat

theorem mul_add_distr_l_proof : mul_add_distr_l := by
  intro x y z
  change WordCore.mul (WordCore.add x y) z =
    WordCore.add (WordCore.mul x z) (WordCore.mul y z)
  apply WordCore.ext_of_val_eq
  apply Int.ofNat.inj
  rw [suffix_wordcore_mul_val_int (WordCore.add x y) z,
    WordCore.add_val_int x y,
    WordCore.add_val_int (WordCore.mul x z) (WordCore.mul y z),
    suffix_wordcore_mul_val_int x z, suffix_wordcore_mul_val_int y z]
  let m : Int := Int.ofNat (2 ^ wordsize)
  change
    (((Int.ofNat x.val + Int.ofNat y.val) % m) * Int.ofNat z.val) % m =
      ((Int.ofNat x.val * Int.ofNat z.val) % m +
        (Int.ofNat y.val * Int.ofNat z.val) % m) % m
  calc
    (((Int.ofNat x.val + Int.ofNat y.val) % m) * Int.ofNat z.val) % m =
        ((((Int.ofNat x.val + Int.ofNat y.val) % m) % m) *
          (Int.ofNat z.val % m)) % m := Int.mul_emod _ _ _
    _ = (((Int.ofNat x.val + Int.ofNat y.val) % m) *
          (Int.ofNat z.val % m)) % m := by
      rw [Int.emod_emod]
    _ = ((Int.ofNat x.val + Int.ofNat y.val) * Int.ofNat z.val) % m :=
      (Int.mul_emod _ _ _).symm
    _ = (Int.ofNat x.val * Int.ofNat z.val +
          Int.ofNat y.val * Int.ofNat z.val) % m := by
      rw [Int.add_mul]
    _ = ((Int.ofNat x.val * Int.ofNat z.val) % m +
          (Int.ofNat y.val * Int.ofNat z.val) % m) % m :=
      Int.add_emod _ _ _

theorem not_involutive_proof : not_involutive := by
  intro x
  apply WordCore.ext_of_val_eq
  change (WordCore.not (WordCore.not x)).val = x.val
  rw [suffix_not_val, suffix_not_val, Nat.xor_eq, Nat.xor_eq, Nat.xor_assoc,
    Nat.xor_self, Nat.xor_zero]

theorem ltu_iwordsize_inv_proof : ltu_iwordsize_inv := by
  intro x h
  have hx := ltu_inv_proof x iwordsize h
  rw [unsigned_repr_wordsize_proof] at hx
  exact hx

theorem shl_shl_proof : shl_shl := by
  intro x y z hy hz _hyz
  have hyv := suffix_ltu_iwordsize_val y hy
  have hzv := suffix_ltu_iwordsize_val z hz
  have hyzlt : y.val + z.val < 2 ^ wordsize := by
    change y.val < 32 at hyv
    change z.val < 32 at hzv
    change y.val + z.val < 2 ^ 32
    omega
  apply WordCore.ext_of_val_eq
  change (WordCore.shl (WordCore.shl x y) z).val =
    (WordCore.shl x (WordCore.add y z)).val
  rw [suffix_shl_val, suffix_shl_val, suffix_shl_val]
  rw [WordCore.add_val, Nat.mod_eq_of_lt hyzlt]
  rw [Nat.pow_add]
  rw [← Nat.mul_assoc]
  exact Nat.mod_mul_mod _ _ _
