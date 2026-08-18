import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Zbits
import CompCert4Lean.X86_64.Archi

/-!
# Fixed-width CompCert integers

This file provides the definition-translation surface selected from
`compcert.lib.Integers`.  Fixed-width values are represented by `Fin (2^n)`;
the source's proof-carrying range invariant is therefore enforced by the Lean
type.  Proofs assigned to the later proof-migration phase are recorded as
transparent proposition descriptors.
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
private abbrev zQuot := ZArith.BinInt.Z.quot
private abbrev zShiftl := ZArith.BinInt.Z.shiftl
private abbrev zShiftr := ZArith.BinInt.Z.shiftr
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLt := ZArith.BinInt.Z.lt
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

abbrev Ceq : comparison := .Ceq
abbrev Cne : comparison := .Cne
abbrev Clt : comparison := .Clt
abbrev Cle : comparison := .Cle
abbrev Cgt : comparison := .Cgt
abbrev Cge : comparison := .Cge

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

abbrev Word (bits : Nat) := Fin (2 ^ bits)

private def positiveToNat : positive → Nat
  | .xH => 1
  | .xI p => 2 * positiveToNat p + 1
  | .xO p => 2 * positiveToNat p

private def residue (bits : Nat) : Z → Nat
  | .Z0 => 0
  | .Zpos p => positiveToNat p % (2 ^ bits)
  | .Zneg p =>
      let modulus := 2 ^ bits
      let r := positiveToNat p % modulus
      if r = 0 then 0 else modulus - r

def repr (bits : Nat) (x : Z) : Word bits :=
  Fin.ofNat (2 ^ bits) (residue bits x)

def unsigned {bits : Nat} (x : Word bits) : Z :=
  zOfNat x.val

def signed {bits : Nat} (x : Word bits) : Z :=
  let modulus := zTwoPowerNat bits
  let half := zTwoPowerNat (bits - 1)
  let u := unsigned x
  zltSelect u half u (zSub u modulus)

def zero (bits : Nat) : Word bits := repr bits zZero
def one (bits : Nat) : Word bits := repr bits zOne
def mone (bits : Nat) : Word bits := repr bits (zOpp zOne)
def iwordsize (bits : Nat) : Word bits := repr bits (zOfNat bits)

def eq {bits : Nat} (x y : Word bits) : Bool := decide (x = y)
def lt {bits : Nat} (x y : Word bits) : Bool :=
  zltSelect (signed x) (signed y) true false
def ltu {bits : Nat} (x y : Word bits) : Bool :=
  zltSelect (unsigned x) (unsigned y) true false

def neg {bits : Nat} (x : Word bits) : Word bits :=
  repr bits (zOpp (unsigned x))
def add {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zAdd (unsigned x) (unsigned y))
def sub {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zSub (unsigned x) (unsigned y))
def mul {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zMul (unsigned x) (unsigned y))
def divs {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zQuot (signed x) (signed y))
def divu {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zDiv (unsigned x) (unsigned y))

def and {bits : Nat} (x y : Word bits) : Word bits :=
  Fin.ofNat (2 ^ bits) (Nat.land x.val y.val)
def or {bits : Nat} (x y : Word bits) : Word bits :=
  Fin.ofNat (2 ^ bits) (Nat.lor x.val y.val)
def xor {bits : Nat} (x y : Word bits) : Word bits :=
  Fin.ofNat (2 ^ bits) (Nat.xor x.val y.val)
def not {bits : Nat} (x : Word bits) : Word bits :=
  Fin.ofNat (2 ^ bits) (Nat.xor x.val (2 ^ bits - 1))

def shl {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zShiftl (unsigned x) (unsigned y))
def shru {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zShiftr (unsigned x) (unsigned y))
def shr {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zShiftr (signed x) (unsigned y))

def rol {bits : Nat} (x y : Word bits) : Word bits :=
  let amount := if bits = 0 then 0 else y.val % bits
  Fin.ofNat (2 ^ bits)
    (Nat.lor (Nat.shiftLeft x.val amount) (Nat.shiftRight x.val (bits - amount)))

def ror {bits : Nat} (x y : Word bits) : Word bits :=
  let amount := if bits = 0 then 0 else y.val % bits
  Fin.ofNat (2 ^ bits)
    (Nat.lor (Nat.shiftRight x.val amount) (Nat.shiftLeft x.val (bits - amount)))

def shrx {bits : Nat} (x y : Word bits) : Word bits :=
  divs x (shl (one bits) y)

def testbit {bits : Nat} (x : Word bits) : Z → Bool
  | .Zneg _ => false
  | .Z0 => Nat.testBit x.val 0
  | .Zpos p => Nat.testBit x.val (positiveToNat p)

def eqm (bits : Nat) (x y : Z) : Prop :=
  CompCert4Lean.Lib.Zbits.eqmod (zTwoPowerNat bits) x y

end WordCore

namespace Int

def GeneratedApplicationMarker : Type := Unit

def wordsize : Nat := 32
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
def mone : int := WordCore.mone wordsize
def iwordsize : int := WordCore.iwordsize wordsize
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
def not : int → int := WordCore.not
def shl : int → int → int := WordCore.shl
def shru : int → int → int := WordCore.shru
def shr : int → int → int := WordCore.shr
def rol : int → int → int := WordCore.rol
def ror : int → int → int := WordCore.ror
def shrx : int → int → int := WordCore.shrx
def testbit : int → Z → Bool := WordCore.testbit
def eqm : Z → Z → Prop := WordCore.eqm wordsize

end Int

namespace Byte

def GeneratedApplicationMarker : Type := Unit

def wordsize : Nat := 8
abbrev int := WordCore.Word wordsize
def repr (x : Z) : int := WordCore.repr wordsize x

end Byte

abbrev int := Int.int
abbrev byte := Byte.int

def int_wordsize_divides_modulusStatement : Prop :=
  zDivide (zOfNat Int.wordsize) Int.modulus

namespace Int64

def GeneratedApplicationMarker : Type := Unit

def wordsize : Nat := 64
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
def mone : int := WordCore.mone wordsize
def iwordsize : int := WordCore.iwordsize wordsize
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
def not : int → int := WordCore.not
def shl : int → int → int := WordCore.shl
def shru : int → int → int := WordCore.shru
def shr : int → int → int := WordCore.shr
def rol : int → int → int := WordCore.rol
def ror : int → int → int := WordCore.ror
def shrx : int → int → int := WordCore.shrx
def testbit : int → Z → Bool := WordCore.testbit
def eqm : Z → Z → Prop := WordCore.eqm wordsize

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
    !(ltu (ofwords yh yl) (ofwords xh xl)) =
      (if Int.eq xh yh then !(Int.ltu yl xl) else Int.ltu xh yh)

def decompose_ltStatement : Prop :=
  ∀ xh xl yh yl : Int.int,
    lt (ofwords xh xl) (ofwords yh yl) =
      (if Int.eq xh yh then Int.ltu xl yl else Int.lt xh yh)

def decompose_leStatement : Prop :=
  ∀ xh xl yh yl : Int.int,
    !(lt (ofwords yh yl) (ofwords xh xl)) =
      (if Int.eq xh yh then !(Int.ltu yl xl) else Int.lt xh yh)

end Int64

abbrev int64 := Int64.int

namespace Wordsize_Ptrofs

def wordsize : Nat :=
  if CompCert4Lean.X86_64.Archi.ptr64 then 64 else 32

end Wordsize_Ptrofs

namespace Ptrofs

def GeneratedApplicationMarker : Type := Unit

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
def testbit : int → Z → Bool := WordCore.testbit
def eqm : Z → Z → Prop := WordCore.eqm wordsize

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
