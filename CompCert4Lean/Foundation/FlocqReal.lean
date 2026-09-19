import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.Ordered

/-!
# Flocq runtime carrier and exact-real specification boundary

This module owns the checked rational/runtime carrier and the explicit exact
specification boundary selected by RPR-007.  The source-shaped statement
descriptors below remain proof obligations; no theorem proof or exact carrier
implementation is asserted here.
-/

namespace CompCert4Lean.Foundation.FlocqReal

/-- Rational/runtime carrier used by the executable Flocq staging layer. -/
structure OrderedReal where
  value : Rat
deriving DecidableEq, Repr

namespace OrderedReal

def denote (x : OrderedReal) : Rat := x.value

instance : Inhabited OrderedReal := ⟨⟨0⟩⟩
instance : Zero OrderedReal := ⟨⟨0⟩⟩
instance : Neg OrderedReal := ⟨fun x => ⟨-x.value⟩⟩
instance : Add OrderedReal := ⟨fun x y => ⟨x.value + y.value⟩⟩
instance : Sub OrderedReal := ⟨fun x y => ⟨x.value - y.value⟩⟩
instance : Mul OrderedReal := ⟨fun x y => ⟨x.value * y.value⟩⟩
instance : Div OrderedReal := ⟨fun x y => ⟨x.value / y.value⟩⟩
instance : LT OrderedReal := ⟨fun x y => x.value < y.value⟩
instance : LE OrderedReal := ⟨fun x y => x.value ≤ y.value⟩

end OrderedReal

abbrev RuntimeReal := OrderedReal
abbrev RuntimeCarrier := RuntimeReal

/-!
The exact Flocq theorem surface is an interface, rather than a rational
implementation. In particular, `sqrt`, `exp`, and `ln` are supplied by an
injected specification carrier and are never defined by runtime placeholders.
-/

abbrev SourceZ := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z

/-- Operations of one exact-real specification carrier. -/
structure ExactRealSpec where
  carrier : Type
  ofZ : SourceZ → carrier
  zero : carrier
  one : carrier
  neg : carrier → carrier
  add : carrier → carrier → carrier
  mul : carrier → carrier → carrier
  inv : carrier → carrier
  div : carrier → carrier → carrier
  lt : carrier → carrier → Prop
  le : carrier → carrier → Prop
  /-- Source-shaped exact decision procedure used by total real extensions. -/
  lt_dec : ∀ x y,
    _root_.CompCert4Lean.Foundation.Logic.Support.Sumbool
      (lt x y) (¬ lt x y)
  abs : carrier → carrier
  min : carrier → carrier → carrier
  sqrt : carrier → carrier
  exp : carrier → carrier
  ln : carrier → carrier
  up : carrier → SourceZ

abbrev ExactRealCarrier (spec : ExactRealSpec) := spec.carrier

namespace ExactReal

abbrev R (spec : ExactRealSpec) := spec.carrier
abbrev Z := SourceZ

def IZR (spec : ExactRealSpec) : Z → spec.carrier := spec.ofZ
def R0 (spec : ExactRealSpec) : spec.carrier := spec.zero
def Rone (spec : ExactRealSpec) : spec.carrier := spec.one
def Ropp (spec : ExactRealSpec) : spec.carrier → spec.carrier := spec.neg
def Rplus (spec : ExactRealSpec) : spec.carrier → spec.carrier → spec.carrier := spec.add
def Rminus (spec : ExactRealSpec) : spec.carrier → spec.carrier → spec.carrier :=
  fun x y => spec.add x (spec.neg y)
def Rmult (spec : ExactRealSpec) : spec.carrier → spec.carrier → spec.carrier := spec.mul
def Rinv (spec : ExactRealSpec) : spec.carrier → spec.carrier := spec.inv
def Rdiv (spec : ExactRealSpec) : spec.carrier → spec.carrier → spec.carrier := spec.div
def Rlt (spec : ExactRealSpec) : spec.carrier → spec.carrier → Prop := spec.lt
def Rle (spec : ExactRealSpec) : spec.carrier → spec.carrier → Prop := spec.le
def Rge (spec : ExactRealSpec) : spec.carrier → spec.carrier → Prop := fun x y => spec.le y x
def Rgt (spec : ExactRealSpec) : spec.carrier → spec.carrier → Prop := fun x y => spec.lt y x
def Rabs (spec : ExactRealSpec) : spec.carrier → spec.carrier := spec.abs
def Rmin (spec : ExactRealSpec) : spec.carrier → spec.carrier → spec.carrier := spec.min
def Rsqr (spec : ExactRealSpec) : spec.carrier → spec.carrier := fun x => spec.mul x x
def sqrt (spec : ExactRealSpec) (x : spec.carrier) : spec.carrier :=
  match spec.lt_dec x spec.zero with
  | .left _ => spec.zero
  | .right _ => spec.sqrt x
def Rsqrt (spec : ExactRealSpec) : spec.carrier → spec.carrier := spec.sqrt
def exp (spec : ExactRealSpec) : spec.carrier → spec.carrier := spec.exp
def ln (spec : ExactRealSpec) (x : spec.carrier) : spec.carrier :=
  match spec.lt_dec spec.zero x with
  | .left _ => spec.ln x
  | .right _ => spec.zero

def powerNat (spec : ExactRealSpec) (x : spec.carrier) : Nat → spec.carrier
  | 0 => spec.one
  | n + 1 => spec.mul x (powerNat spec x n)

def powerRZ (spec : ExactRealSpec) (x : spec.carrier) : Z → spec.carrier
  | .Z0 => spec.one
  | .Zpos p => powerNat spec x
      (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p)
  | .Zneg p => spec.inv (powerNat spec x
      (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p))
def up (spec : ExactRealSpec) : spec.carrier → Z := spec.up

end ExactReal

/-- Ordered-field laws required of an exact Flocq specification carrier. -/
structure OrderedFieldCertificate (spec : ExactRealSpec) : Prop where
  zero_ne_one : spec.zero ≠ spec.one
  add_zero : ∀ x, spec.add x spec.zero = x
  zero_add : ∀ x, spec.add spec.zero x = x
  add_assoc : ∀ x y z, spec.add (spec.add x y) z = spec.add x (spec.add y z)
  add_comm : ∀ x y, spec.add x y = spec.add y x
  neg_add_cancel : ∀ x, spec.add (spec.neg x) x = spec.zero
  mul_one : ∀ x, spec.mul x spec.one = x
  one_mul : ∀ x, spec.mul spec.one x = x
  mul_assoc : ∀ x y z, spec.mul (spec.mul x y) z = spec.mul x (spec.mul y z)
  mul_comm : ∀ x y, spec.mul x y = spec.mul y x
  mul_zero : ∀ x, spec.mul x spec.zero = spec.zero
  zero_mul : ∀ x, spec.mul spec.zero x = spec.zero
  left_distrib : ∀ x y z,
    spec.mul x (spec.add y z) = spec.add (spec.mul x y) (spec.mul x z)
  inv_mul_cancel : ∀ x, x ≠ spec.zero → spec.mul (spec.inv x) x = spec.one
  div_eq_mul_inv : ∀ x y, spec.div x y = spec.mul x (spec.inv y)
  le_refl : ∀ x, spec.le x x
  le_trans : ∀ x y z, spec.le x y → spec.le y z → spec.le x z
  le_antisymm : ∀ x y, spec.le x y → spec.le y x → x = y
  lt_irrefl : ∀ x, ¬ spec.lt x x
  lt_trans : ∀ x y z, spec.lt x y → spec.lt y z → spec.lt x z
  lt_iff_le_not_le : ∀ x y, spec.lt x y ↔ spec.le x y ∧ ¬ spec.le y x
  add_lt_compat_l : ∀ r r1 r2,
    spec.lt r1 r2 → spec.lt (spec.add r r1) (spec.add r r2)
  mul_lt_compat_l : ∀ r r1 r2,
    spec.lt spec.zero r → spec.lt r1 r2 →
      spec.lt (spec.mul r r1) (spec.mul r r2)

/-- Exact square-root laws required by Flocq theorem consumers. -/
structure SqrtCertificate (spec : ExactRealSpec) : Prop where
  nonnegative : ∀ x, spec.le spec.zero (spec.sqrt x)
  sqr : ∀ x, spec.le spec.zero x → spec.mul (spec.sqrt x) (spec.sqrt x) = x
  monotone : ∀ x y, spec.le spec.zero x → spec.le x y → spec.le (spec.sqrt x) (spec.sqrt y)
  sqrt_sqr : ∀ x, spec.le spec.zero x → spec.sqrt (spec.mul x x) = x

/-- Exact exponential laws required by Flocq theorem consumers. -/
structure ExpCertificate (spec : ExactRealSpec) : Prop where
  zero : spec.exp spec.zero = spec.one
  add : ∀ x y, spec.exp (spec.add x y) = spec.mul (spec.exp x) (spec.exp y)
  strict_monotone : ∀ x y, spec.lt x y → spec.lt (spec.exp x) (spec.exp y)
  positive : ∀ x, spec.lt spec.zero (spec.exp x)

/-- Exact logarithm laws required by Flocq theorem consumers. -/
structure LnCertificate (spec : ExactRealSpec) : Prop where
  exp_ln : ∀ x, spec.lt spec.zero x → spec.exp (spec.ln x) = x
  ln_exp : ∀ x, spec.ln (spec.exp x) = x
  one : spec.ln spec.one = spec.zero

/-! Source-named laws that are consumed across the selected Flocq provider
surface.  These are obligations, not proof shortcuts: proof grinding supplies
their terms after definition migration, but the exact propositions and their
ownership remain part of the canonical context now. -/
structure ExactRealSourceLaws (spec : ExactRealSpec) : Prop where
  ofZ_zero : spec.ofZ
      (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0) = spec.zero
  ofZ_one : spec.ofZ
      (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH) = spec.one
  ofZ_add : ∀ x y,
    spec.ofZ (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add x y) =
      spec.add (spec.ofZ x) (spec.ofZ y)
  ofZ_neg : ∀ x,
    spec.ofZ (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp x) =
      spec.neg (spec.ofZ x)
  sqrt_mult : ∀ x y,
    spec.le spec.zero x → spec.le spec.zero y →
      spec.sqrt (spec.mul x y) = spec.mul (spec.sqrt x) (spec.sqrt y)
  sqrt_strict_positive : ∀ x,
    spec.lt spec.zero x → spec.lt spec.zero (spec.sqrt x)
  exp_opp : ∀ x,
    spec.exp (spec.neg x) = spec.inv (spec.exp x)
  abs_negative : ∀ x,
    spec.lt x spec.zero → spec.abs x = spec.neg x
  abs_nonnegative : ∀ x,
    spec.le spec.zero x → spec.abs x = x
  min_left : ∀ x y, spec.le (spec.min x y) x
  min_right : ∀ x y, spec.le (spec.min x y) y
  min_eq_left : ∀ x y, spec.le x y → spec.min x y = x
  min_eq_right : ∀ x y, spec.le y x → spec.min x y = y
  powerRZ_zero : ∀ x,
    ExactReal.powerRZ spec x
      (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0) = spec.one
  powerRZ_add : ∀ x z1 z2,
    x ≠ spec.zero →
      ExactReal.powerRZ spec x
          (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add z1 z2) =
        spec.mul (ExactReal.powerRZ spec x z1) (ExactReal.powerRZ spec x z2)
  up_gt : ∀ x,
    spec.lt x (spec.ofZ (spec.up x))
  up_gap : ∀ x,
    spec.le
      (ExactReal.Rminus spec (spec.ofZ (spec.up x)) x)
      (spec.ofZ (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH))
  completeness :
    ∀ (E : spec.carrier → Prop),
      (∃ m, ∀ x, E x → spec.le x m) →
      (∃ x, E x) →
      ∃ m, (∀ x, E x → spec.le x m) ∧
        ∀ b, (∀ x, E x → spec.le x b) → spec.le m b

/-- Mandatory proof owner for the exact-real specification boundary. -/
structure ExactRealCertificate (spec : ExactRealSpec) : Prop where
  orderedField : OrderedFieldCertificate spec
  /-- Source `Rdefinitions.total_order_T` trichotomy for exact comparisons. -/
  total_order : ∀ x y, (spec.lt x y ∨ x = y) ∨ spec.lt y x
  sqrt : SqrtCertificate spec
  exp : ExpCertificate spec
  ln : LnCertificate spec
  sourceLaws : ExactRealSourceLaws spec

/-!
The adapter is a relation from the checked runtime carrier into the selected
exact carrier. Its closure and preservation fields are intentionally proof
obligations; no default adapter or certificate is provided here.
-/
structure RuntimeExactAdapter (spec : ExactRealSpec) : Type where
  represented : RuntimeReal → Prop
  embed : (x : RuntimeReal) → represented x → spec.carrier
  runtime_ofZ : SourceZ → RuntimeReal
  ofZ_represents : ∀ z, represented (runtime_ofZ z)
  ofZ_preserved : ∀ z,
    embed (runtime_ofZ z) (ofZ_represents z) = spec.ofZ z
  runtime_zero : RuntimeReal
  zero_represents : represented runtime_zero
  zero_preserved : embed runtime_zero zero_represents = spec.zero
  runtime_one : RuntimeReal
  one_represents : represented runtime_one
  one_preserved : embed runtime_one one_represents = spec.one
  neg_closed : ∀ x, represented x → represented ⟨-x.value⟩
  neg_preserved : ∀ x (hx : represented x),
    embed ⟨-x.value⟩ (neg_closed x hx) = spec.neg (embed x hx)
  add_closed : ∀ x, represented x → ∀ y, represented y → represented ⟨x.value + y.value⟩
  add_preserved : ∀ x (hx : represented x) y (hy : represented y),
    embed ⟨x.value + y.value⟩ (add_closed x hx y hy) =
      spec.add (embed x hx) (embed y hy)
  sub_closed : ∀ x, represented x → ∀ y, represented y → represented ⟨x.value - y.value⟩
  sub_preserved : ∀ x (hx : represented x) y (hy : represented y),
    embed ⟨x.value - y.value⟩ (sub_closed x hx y hy) =
      ExactReal.Rminus spec (embed x hx) (embed y hy)
  mul_closed : ∀ x, represented x → ∀ y, represented y → represented ⟨x.value * y.value⟩
  mul_preserved : ∀ x (hx : represented x) y (hy : represented y),
    embed ⟨x.value * y.value⟩ (mul_closed x hx y hy) =
      spec.mul (embed x hx) (embed y hy)
  inv_closed : ∀ x, represented x → represented ⟨1 / x.value⟩
  inv_preserved : ∀ x (hx : represented x),
    embed ⟨1 / x.value⟩ (inv_closed x hx) = spec.inv (embed x hx)
  div_closed : ∀ x, represented x → ∀ y, represented y → represented ⟨x.value / y.value⟩
  div_preserved : ∀ x (hx : represented x) y (hy : represented y),
    embed ⟨x.value / y.value⟩ (div_closed x hx y hy) =
      spec.div (embed x hx) (embed y hy)
  abs_closed : ∀ x, represented x → represented ⟨if x.value < 0 then -x.value else x.value⟩
  abs_preserved : ∀ x (hx : represented x),
    embed ⟨if x.value < 0 then -x.value else x.value⟩ (abs_closed x hx) =
      spec.abs (embed x hx)
  min_closed : ∀ x, represented x → ∀ y, represented y →
    represented ⟨if x.value ≤ y.value then x.value else y.value⟩
  min_preserved : ∀ x (hx : represented x) y (hy : represented y),
    embed ⟨if x.value ≤ y.value then x.value else y.value⟩ (min_closed x hx y hy) =
      spec.min (embed x hx) (embed y hy)
  runtime_powerRZ : RuntimeReal → SourceZ → RuntimeReal
  powerRZ_closed : ∀ x, represented x → ∀ z, represented (runtime_powerRZ x z)
  powerRZ_preserved : ∀ x (hx : represented x) z,
    embed (runtime_powerRZ x z) (powerRZ_closed x hx z) =
      ExactReal.powerRZ spec (embed x hx) z
  lt_preserved : ∀ x (hx : represented x) y (hy : represented y),
    spec.lt (embed x hx) (embed y hy) ↔ x.value < y.value
  le_preserved : ∀ x (hx : represented x) y (hy : represented y),
    spec.le (embed x hx) (embed y hy) ↔ x.value ≤ y.value
  runtime_up : RuntimeReal → SourceZ
  up_preserved : ∀ x (hx : represented x),
    spec.up (embed x hx) = runtime_up x

namespace RuntimeExactAdapter

/-! The dependent `embed` field is the primitive adapter operation.  Exposing
    it over the represented-value carrier gives theorem-facing consumers one
    stable operation to thread through source/runtime correspondences without
    identifying the two carriers. -/
abbrev Represented (adapter : RuntimeExactAdapter spec) :=
  Subtype adapter.represented

def operation (adapter : RuntimeExactAdapter spec)
    (x : adapter.Represented) : spec.carrier :=
  adapter.embed x.1 x.2

/-! These propositions restate the exact laws at the operation surface.  They
    intentionally carry no proof terms of their own; the existing adapter
    fields remain the proof-grinding obligations. -/
def operation_ofZ (adapter : RuntimeExactAdapter spec) : Prop :=
  ∀ z,
    adapter.operation
        ⟨adapter.runtime_ofZ z, adapter.ofZ_represents z⟩ =
      spec.ofZ z

def operation_mul (adapter : RuntimeExactAdapter spec) : Prop :=
  ∀ (x y : adapter.Represented),
    adapter.operation
        ⟨⟨x.1.value * y.1.value⟩,
          adapter.mul_closed x.1 x.2 y.1 y.2⟩ =
      spec.mul (adapter.operation x) (adapter.operation y)

/-! Generic source-indexed correspondence schema.  SCC-098 instantiates this
    with its canonical exact `F2R` identity and the separately named runtime
    `F2R` operation; the provider does not duplicate either source declaration.
    The existential representation witness is deliberately retained. -/
def operation_correspondence (adapter : RuntimeExactAdapter spec)
    {ι : Type} (runtime : ι → RuntimeReal) (exact : ι → spec.carrier) : Prop :=
  ∀ i, ∃ h : adapter.represented (runtime i),
    adapter.operation ⟨runtime i, h⟩ = exact i

def f2r_correspondence (adapter : RuntimeExactAdapter spec)
    {β : Type}
    (runtimeF2R : β → SourceZ → SourceZ → RuntimeReal)
    (exactF2R : β → SourceZ → SourceZ → spec.carrier) : Prop :=
  ∀ beta m e, ∃ h : adapter.represented (runtimeF2R beta m e),
    adapter.operation ⟨runtimeF2R beta m e, h⟩ = exactF2R beta m e

end RuntimeExactAdapter

/-- Explicit bundle threaded by theorem-facing Flocq consumers. -/
structure ExactRealContext where
  spec : ExactRealSpec
  certificate : ExactRealCertificate spec
  adapter : RuntimeExactAdapter spec

namespace ExactReal

/-- Canonical source-shaped total-order witness for an exact-real context. -/
def total_order_T (ctx : ExactRealContext) (x y : ctx.spec.carrier) :
    _root_.CompCert4Lean.Foundation.Logic.Support.Sumor
      (_root_.CompCert4Lean.Foundation.Logic.Support.Sumbool
        (ctx.spec.lt x y) (x = y))
      (ctx.spec.lt y x) := by
  match ctx.spec.lt_dec x y with
  | .left hxy => exact .inleft (.left hxy)
  | .right hnxy =>
      match ctx.spec.lt_dec y x with
      | .left hyx => exact .inright hyx
      | .right hnyx =>
          exact .inleft (.right (by
            rcases ctx.certificate.total_order x y with hxy | hyx
            · rcases hxy with hlt | heq
              · exact (hnxy hlt).elim
              · exact heq
            · exact (hnyx hyx).elim))

end ExactReal

/-! Proof-bearing source carrier used by `Rsqrt` and related theorem surfaces.
The value and its nonnegativity proposition are retained even though proof
construction is deferred to the proof-grinding phase. -/
structure ExactNonnegReal (ctx : ExactRealContext) where
  nonneg : ctx.spec.carrier
  cond_nonneg : ctx.spec.le ctx.spec.zero nonneg

abbrev RealValue := OrderedReal
abbrev F2RRat := Rat
def F2R (q : F2RRat) : RealValue := ⟨q⟩

namespace Rocq.Coq.Reals

abbrev R := OrderedReal
abbrev Z := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
abbrev positive := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive
abbrev xH : positive := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH
abbrev xO : positive → positive := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.xO
abbrev Z0 : Z := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0
abbrev Zpos : positive → Z := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos

abbrev lt := Nat.lt
abbrev le := Nat.le
abbrev O : Nat := 0

namespace Z
abbrev of_nat := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
abbrev add := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
abbrev sub := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub
abbrev mul := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
abbrev opp := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
abbrev abs := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
abbrev le := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
abbrev lt := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt
end Z

private def zToInt : Z → Int
  | .Z0 => 0
  | .Zpos p => Int.ofNat (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p)
  | .Zneg p => -Int.ofNat (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p)

def IZR (z : Z) : R := ⟨Rat.ofInt (zToInt z)⟩
def INR (n : Nat) : R := ⟨Rat.ofInt (Int.ofNat n)⟩
def R0 : R := ⟨0⟩
def Ropp (x : R) : R := ⟨-x.value⟩
def Rplus (x y : R) : R := ⟨x.value + y.value⟩
def Rminus (x y : R) : R := ⟨x.value - y.value⟩
def Rmult (x y : R) : R := ⟨x.value * y.value⟩
def Rinv (x : R) : R := ⟨1 / x.value⟩
def Rdiv (x y : R) : R := Rmult x (Rinv y)
def Rlt (x y : R) : Prop := x.value < y.value
def Rle (x y : R) : Prop := x.value ≤ y.value
def Rge (x y : R) : Prop := Rle y x
def Rgt (x y : R) : Prop := Rlt y x
def Rsqr (x : R) : R := Rmult x x
def Rabs (x : R) : R := if x.value < R0.value then Ropp x else x
def Rmin (x y : R) : R := if x.value ≤ y.value then x else y
namespace Runtime
def sqrt (x : R) : R := if R0.value ≤ x.value then x else R0
def Rsqrt (x : R) : R := sqrt x
def exp (_ : R) : R := ⟨1⟩
def ln (_ : R) : R := R0
end Runtime
abbrev sqrt := Runtime.sqrt
abbrev Rsqrt := Runtime.Rsqrt
abbrev exp := Runtime.exp
abbrev ln := Runtime.ln
def powerRZ (x : R) (n : Z) : R :=
  match n with
  | .Z0 => ⟨1⟩
  | .Zpos p => ⟨Rat.pow x.value
      (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p)⟩
  | .Zneg p => ⟨1 / Rat.pow x.value
      (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p)⟩

private def strictCeil (q : Rat) : Int :=
  let c := Rat.ceil q
  if Rat.ofInt c = q then c + 1 else c

def up (x : R) : Z :=
  _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (strictCeil x.value)

abbrev Sumbool (A B : Prop) := _root_.CompCert4Lean.Foundation.Logic.Support.Sumbool A B
abbrev Sumor (A : Type) (B : Prop) := _root_.CompCert4Lean.Foundation.Logic.Support.Sumor A B
abbrev ex {A : Type} (P : A → Prop) := ∃ x, P x
abbrev sig {A : Type} (P : A → Prop) := Subtype P
abbrev nonnegreal := R
def is_upper_bound (E : R → Prop) (m : R) : Prop := ∀ x, E x → Rle x m
def bound (E : R → Prop) : Prop := ∃ m, is_upper_bound E m
def is_lub (E : R → Prop) (m : R) : Prop :=
  is_upper_bound E m ∧ ∀ b, is_upper_bound E b → Rle m b

namespace RinvImpl
abbrev Rinv := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rinv
end RinvImpl

namespace RbaseSymbolsImpl
def R : Type := OrderedReal
def R0 : R := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.R0
def Ropp : R → R := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Ropp
end RbaseSymbolsImpl

namespace Rdefinitions
def R : Type := OrderedReal
def R0 : R := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.R0
def Ropp : R → R := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Ropp
namespace RbaseSymbolsImpl
def R : Type := OrderedReal
def R0 : R := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.R0
def Ropp : R → R := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Ropp
end RbaseSymbolsImpl
def IZR : Z → R := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.IZR
def Rdiv : R → R → R := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rdiv
abbrev Rinv := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rinv
def Rminus : R → R → R := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rminus
def up : R → Z := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.up
def total_order_T_type (r1 r2 : R) : Type :=
  Sumor (Sumbool (Rlt r1 r2) (Eq r1 r2)) (Rlt r2 r1)
end Rdefinitions

namespace R_sqrt
def sqrt (ctx : ExactRealContext) (x : ctx.spec.carrier) : ctx.spec.carrier :=
  ExactReal.sqrt ctx.spec x
end R_sqrt

namespace Raxioms
def INR : Nat → R := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.INR
def is_upper_bound : (R → Prop) → R → Prop := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.is_upper_bound
end Raxioms

namespace Rbasic_fun
def Rabs : R → R := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rabs
def Rabs_Rinv_runtime (r : R) (_h : Not (Eq r (IZR Z0))) : Prop :=
  Eq (Rabs (Rinv r)) (Rinv (Rabs r))
def Rmin : R → R → R := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rmin
end Rbasic_fun

namespace Rfunctions
def powerRZ : R → Z → R := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.powerRZ
end Rfunctions

namespace RIneq

namespace Runtime

def Req_dec_T (r1 r2 : R) : Sumbool (Eq r1 r2) (Not (Eq r1 r2)) :=
  if h : r1 = r2 then .left h else .right h

abbrev Req_EM_T := Req_dec_T

end Runtime

/-- Source `Req_dec_T`, constructively derived from the injected exact order. -/
def Req_dec_T (ctx : ExactRealContext) (r1 r2 : ctx.spec.carrier) :
    Sumbool (Eq r1 r2) (Not (Eq r1 r2)) :=
  match ExactReal.total_order_T ctx r1 r2 with
  | .inleft (.left hlt) => .right (by
      intro heq
      subst r2
      exact ctx.certificate.orderedField.lt_irrefl r1 hlt)
  | .inleft (.right heq) => .left heq
  | .inright hgt => .right (by
      intro heq
      subst r2
      exact ctx.certificate.orderedField.lt_irrefl r1 hgt)

abbrev Req_EM_T := Req_dec_T

def IZR_neq (ctx : ExactRealContext) (z1 z2 : Z) (h : z1 ≠ z2) : Prop :=
  Not (Eq (ExactReal.IZR ctx.spec z1) (ExactReal.IZR ctx.spec z2))
def Rinv_involutive_runtime (r : R) (_h : Not (Eq r (IZR Z0))) : Prop :=
  Eq (Rinv (Rinv r)) r
def Rle_Rinv_runtime (x y : R) (_hx : Rlt (IZR Z0) x) (_hy : Rlt (IZR Z0) y)
    (_hxy : Rle x y) : Prop :=
  Rle (Rinv y) (Rinv x)
def Rlt_0_minus (a b : R) : Prop := Rlt (IZR Z0) (Rminus a b)
def Rlt_Rminus (ctx : ExactRealContext) (a b : ctx.spec.carrier)
    (_h : ExactReal.Rlt ctx.spec a b) : Prop :=
  ExactReal.Rlt ctx.spec (ExactReal.R0 ctx.spec)
    (ExactReal.Rminus ctx.spec b a)
def Ropp_inv_permute_runtime (r : R) (_h : Not (Eq r (IZR Z0))) : Prop :=
  Eq (Ropp (Rinv r)) (Rinv (Ropp r))
def Ropp_Ropp_IZR_runtime (n : Z) : Prop := Eq (IZR (Z.opp n)) (Ropp (IZR n))
def Rsqr : R → R := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rsqr
end RIneq

namespace Rpower
def ln (ctx : ExactRealContext) (x : ctx.spec.carrier) : ctx.spec.carrier :=
  ExactReal.ln ctx.spec x
end Rpower

namespace Rtrigo_def
def exp (ctx : ExactRealContext) (x : ctx.spec.carrier) : ctx.spec.carrier :=
  ExactReal.exp ctx.spec x
end Rtrigo_def

end Rocq.Coq.Reals

namespace Rocq.Coq.Reals

/-! The source theorem descriptors below are parameterised by the exact-real
    context.  The runtime aliases above remain available for executable
    staging, but theorem-facing identities must not silently quantify over the
    rational compatibility carrier. -/
section ExactStatements

variable (ctx : ExactRealContext)

local notation "R" => ctx.spec.carrier
local notation "IZR" => ExactReal.IZR ctx.spec
local notation "INR" => fun n : Nat => ExactReal.IZR ctx.spec (Z.of_nat n)
local notation "R0" => ExactReal.R0 ctx.spec
local notation "Ropp" => ExactReal.Ropp ctx.spec
local notation "Rplus" => ExactReal.Rplus ctx.spec
local notation "Rminus" => ExactReal.Rminus ctx.spec
local notation "Rmult" => ExactReal.Rmult ctx.spec
local notation "Rinv" => ExactReal.Rinv ctx.spec
local notation "Rle" => ExactReal.Rle ctx.spec
local notation "Rlt" => ExactReal.Rlt ctx.spec
local notation "Rge" => ExactReal.Rge ctx.spec
local notation "Rgt" => ExactReal.Rgt ctx.spec
local notation "Rabs" => ExactReal.Rabs ctx.spec
local notation "Rmin" => ExactReal.Rmin ctx.spec
local notation "Rsqr" => ExactReal.Rsqr ctx.spec
local notation "sqrt" => ExactReal.sqrt ctx.spec
local notation "exp" => ExactReal.exp ctx.spec
local notation "ln" => ExactReal.ln ctx.spec
local notation "powerRZ" => ExactReal.powerRZ ctx.spec
local notation "up" => ExactReal.up ctx.spec

private def exactIsUpperBound (E : R → Prop) (m : R) : Prop :=
  ∀ x, E x → Rle x m

private def exactBound (E : R → Prop) : Prop :=
  ∃ m, exactIsUpperBound (ctx := ctx) E m

private def exactIsLub (E : R → Prop) (m : R) : Prop :=
  exactIsUpperBound (ctx := ctx) E m ∧
    ∀ b, exactIsUpperBound (ctx := ctx) E b → Rle m b

local notation "bound" => exactBound (ctx := ctx)
local notation "is_lub" => exactIsLub (ctx := ctx)

namespace DiscrR

def IZR_eqStatement : Prop := ∀ (z1 z2 : Z) (_ : Eq z1 z2), Eq (IZR z1) (IZR z2)

end DiscrR

namespace Exp_prop

def exp_plusStatement : Prop := ∀ x y : R, Eq (exp (Rplus x y)) (Rmult (exp x) (exp y))

end Exp_prop

namespace R_Ifp

def tech_upStatement : Prop := ∀ (r : R) (z : Z) (_ : Rlt r (IZR z)) (_ : Rle (IZR z) (Rplus r (IZR (Zpos xH)))), Eq z (up r)

end R_Ifp

namespace R_sqr

def Rsqr_absStatement : Prop := ∀ x : R, Eq (Rsqr x) (Rsqr (Rabs x))
def Rsqr_incr_0Statement : Prop := ∀ (x y : R) (_ : Rle (Rsqr x) (Rsqr y)) (_ : Rle (IZR Z0) x) (_ : Rle (IZR Z0) y), Rle x y
def Rsqr_incrst_0Statement : Prop := ∀ (x y : R) (_ : Rlt (Rsqr x) (Rsqr y)) (_ : Rle (IZR Z0) x) (_ : Rle (IZR Z0) y), Rlt x y
def Rsqr_incrst_1Statement : Prop := ∀ (x y : R) (_ : Rlt x y) (_ : Rle (IZR Z0) x) (_ : Rle (IZR Z0) y), Rlt (Rsqr x) (Rsqr y)
def Rsqr_le_abs_0Statement : Prop := ∀ (x y : R) (_ : Rle (Rsqr x) (Rsqr y)), Rle (Rabs x) (Rabs y)
def Rsqr_lt_abs_0Statement : Prop := ∀ (x y : R) (_ : Rlt (Rsqr x) (Rsqr y)), Rlt (Rabs x) (Rabs y)
def Rsqr_lt_abs_1Statement : Prop := ∀ (x y : R) (_ : Rlt (Rabs x) (Rabs y)), Rlt (Rsqr x) (Rsqr y)
def Rsqr_multStatement : Prop := ∀ x y : R, Eq (Rsqr (Rmult x y)) (Rmult (Rsqr x) (Rsqr y))

end R_sqr

namespace R_sqrt

def Rsqr_sqrtStatement : Prop := ∀ (x : R) (_ : Rle (IZR Z0) x), Eq (Rsqr (sqrt x)) x
def sqrt_lt_1Statement : Prop := ∀ (x y : R) (_ : Rle (IZR Z0) x) (_ : Rle (IZR Z0) y) (_ : Rlt x y), Rlt (sqrt x) (sqrt y)
def sqrt_lt_R0Statement : Prop := ∀ (x : R) (_ : Rlt (IZR Z0) x), Rlt (IZR Z0) (sqrt x)
def sqrt_multStatement : Prop := ∀ (x y : R) (_ : Rle (IZR Z0) x) (_ : Rle (IZR Z0) y), Eq (sqrt (Rmult x y)) (Rmult (sqrt x) (sqrt y))
def sqrt_RsqrStatement : Prop := ∀ (x : R) (_ : Rle (IZR Z0) x), Eq (sqrt (Rsqr x)) x

end R_sqrt

namespace Raxioms

def archimedStatement : Prop := ∀ r : R, And (Rgt (IZR (up r)) r) (Rle (Rminus (IZR (up r)) r) (IZR (Zpos xH)))
def completenessStatement : Type := ∀ (E : ∀ _ : R, Prop) (_ : bound E) (_ : ex (fun x : R => E x)), sig (fun m : R => is_lub E m)
def Rinv_lStatement : Prop := ∀ (r : R) (_ : Not (Eq r (IZR Z0))), Eq (Rmult (Rinv r) r) (IZR (Zpos xH))
def Rlt_transStatement : Prop := ∀ (r1 r2 r3 : R) (_ : Rlt r1 r2) (_ : Rlt r2 r3), Rlt r1 r3
def Rmult_1_lStatement : Prop := ∀ r : R, Eq (Rmult (IZR (Zpos xH)) r) r
def Rmult_assocStatement : Prop := ∀ r1 r2 r3 : R, Eq (Rmult (Rmult r1 r2) r3) (Rmult r1 (Rmult r2 r3))
def Rmult_commStatement : Prop := ∀ r1 r2 : R, Eq (Rmult r1 r2) (Rmult r2 r1)
def Rmult_lt_compat_lStatement : Prop := ∀ (r r1 r2 : R) (_ : Rlt (IZR Z0) r) (_ : Rlt r1 r2), Rlt (Rmult r r1) (Rmult r r2)
def Rplus_0_lStatement : Prop := ∀ r : R, Eq (Rplus (IZR Z0) r) r
def Rplus_assocStatement : Prop := ∀ r1 r2 r3 : R, Eq (Rplus (Rplus r1 r2) r3) (Rplus r1 (Rplus r2 r3))
def Rplus_commStatement : Prop := ∀ r1 r2 : R, Eq (Rplus r1 r2) (Rplus r2 r1)
def Rplus_lt_compat_lStatement : Prop := ∀ (r r1 r2 : R) (_ : Rlt r1 r2), Rlt (Rplus r r1) (Rplus r r2)
def Rplus_opp_rStatement : Prop := ∀ r : R, Eq (Rplus r (Ropp r)) (IZR Z0)

end Raxioms

namespace Rbasic_fun

def Rabs_Rinv (ctx : ExactRealContext)
    (r : ctx.spec.carrier)
    (_h : Not (Eq r (ExactReal.IZR ctx.spec Z0))) : Prop :=
  Eq (ExactReal.Rabs ctx.spec (ExactReal.Rinv ctx.spec r))
    (ExactReal.Rinv ctx.spec (ExactReal.Rabs ctx.spec r))
def abs_IZRStatement : Prop := ∀ z : Z, Eq (IZR (Z.abs z)) (Rabs (IZR z))
def Rabs_def1Statement : Prop := ∀ (x a : R) (_ : Rlt x a) (_ : Rlt (Ropp a) x), Rlt (Rabs x) a
def Rabs_def2Statement : Prop := ∀ (x a : R) (_ : Rlt (Rabs x) a), And (Rlt x a) (Rlt (Ropp a) x)
def Rabs_leStatement : Prop := ∀ (a b : R) (_ : And (Rle (Ropp b) a) (Rle a b)), Rle (Rabs a) b
def Rabs_leftStatement : Prop := ∀ (r : R) (_ : Rlt r (IZR Z0)), Eq (Rabs r) (Ropp r)
def Rabs_left1Statement : Prop := ∀ (a : R) (_ : Rle a (IZR Z0)), Eq (Rabs a) (Ropp a)
def Rabs_minus_symStatement : Prop :=
  ∀ x y : R, Eq (Rabs (Rminus x y)) (Rabs (Rminus y x))
def Rabs_multStatement : Prop := ∀ x y : R, Eq (Rabs (Rmult x y)) (Rmult (Rabs x) (Rabs y))
def Rabs_no_R0Statement : Prop := ∀ (r : R) (_ : Not (Eq r (IZR Z0))), Not (Eq (Rabs r) (IZR Z0))
def Rabs_pos_eqStatement : Prop := ∀ (x : R) (_ : Rle (IZR Z0) x), Eq (Rabs x) x
def Rabs_pos_ltStatement : Prop := ∀ (x : R) (_ : Not (Eq x (IZR Z0))), Rlt (IZR Z0) (Rabs x)
def Rabs_posStatement : Prop := ∀ x : R, Rle (IZR Z0) (Rabs x)
def Rabs_R0Statement : Prop := Eq (Rabs (IZR Z0)) (IZR Z0)
def Rabs_R1Statement : Prop := Eq (Rabs (IZR (Zpos xH))) (IZR (Zpos xH))
def Rabs_rightStatement : Prop := ∀ (r : R) (_ : Rge r (IZR Z0)), Eq (Rabs r) r
def Rabs_RoppStatement : Prop := ∀ x : R, Eq (Rabs (Ropp x)) (Rabs x)
def Rcase_absStatement : Type := ∀ r : R, Sumbool (Rlt r (IZR Z0)) (Rge r (IZR Z0))
def Rmin_commStatement : Prop := ∀ x y : R, Eq (Rmin x y) (Rmin y x)
def Rmin_lStatement : Prop := ∀ x y : R, Rle (Rmin x y) x
def Rmin_rStatement : Prop := ∀ x y : R, Rle (Rmin x y) y

end Rbasic_fun

namespace Rdefinitions

def total_order_T (r1 r2 : R) :
    Sumor (Sumbool (Rlt r1 r2) (Eq r1 r2)) (Rlt r2 r1) :=
  ExactReal.total_order_T ctx r1 r2

def total_order_TStatement : Type := ∀ r1 r2 : R, Sumor (Sumbool (Rlt r1 r2) (Eq r1 r2)) (Rlt r2 r1)

end Rdefinitions

namespace Rfunctions

def powerRZ_addStatement : Prop := ∀ (x : R) (n m : Z) (_ : Not (Eq x (IZR Z0))), Eq (powerRZ x (Z.add n m)) (Rmult (powerRZ x n) (powerRZ x m))
def powerRZ_leStatement : Prop := ∀ (x : R) (z : Z) (_ : Rlt (IZR Z0) x), Rle (IZR Z0) (powerRZ x z)
def powerRZ_ltStatement : Prop := ∀ (x : R) (z : Z) (_ : Rlt (IZR Z0) x), Rlt (IZR Z0) (powerRZ x z)

end Rfunctions

namespace RIneq

def Rinv_involutive (ctx : ExactRealContext)
    (r : ctx.spec.carrier)
    (_h : Not (Eq r (ExactReal.IZR ctx.spec Z0))) : Prop :=
  Eq (ExactReal.Rinv ctx.spec (ExactReal.Rinv ctx.spec r)) r
def Rle_Rinv (ctx : ExactRealContext)
    (x y : ctx.spec.carrier)
    (_hx : ExactReal.Rlt ctx.spec (ExactReal.IZR ctx.spec Z0) x)
    (_hy : ExactReal.Rlt ctx.spec (ExactReal.IZR ctx.spec Z0) y)
    (_hxy : ExactReal.Rle ctx.spec x y) : Prop :=
  ExactReal.Rle ctx.spec (ExactReal.Rinv ctx.spec y) (ExactReal.Rinv ctx.spec x)
def Ropp_inv_permute (ctx : ExactRealContext)
    (r : ctx.spec.carrier)
    (_h : Not (Eq r (ExactReal.IZR ctx.spec Z0))) : Prop :=
  Eq (ExactReal.Ropp ctx.spec (ExactReal.Rinv ctx.spec r))
    (ExactReal.Rinv ctx.spec (ExactReal.Ropp ctx.spec r))
def Ropp_Ropp_IZR (ctx : ExactRealContext) (n : Z) : Prop :=
  Eq (ExactReal.IZR ctx.spec (Z.opp n))
    (ExactReal.Ropp ctx.spec (ExactReal.IZR ctx.spec n))
def Rlt_dec (r1 r2 : R) : Sumbool (Rlt r1 r2) (Not (Rlt r1 r2)) :=
  ctx.spec.lt_dec r1 r2
def Rlt_decStatement : Type :=
  ∀ r1 r2 : R, Sumbool (Rlt r1 r2) (Not (Rlt r1 r2))
def eq_IZRStatement : Prop := ∀ (n m : Z) (_ : Eq (IZR n) (IZR m)), Eq n m
def INR_IZR_INZStatement : Prop := ∀ n : Nat, Eq (INR n) (IZR (Z.of_nat n))
def INR_ltStatement : Prop := ∀ (n m : Nat) (_ : Rlt (INR n) (INR m)), lt n m
def IZR_leStatement : Prop := ∀ (n m : Z) (_ : Z.le n m), Rle (IZR n) (IZR m)
def IZR_ltStatement : Prop := ∀ (n m : Z) (_ : Z.lt n m), Rlt (IZR n) (IZR m)
def le_INRStatement : Prop := ∀ (n m : Nat) (_ : le n m), Rle (INR n) (INR m)
def le_IZRStatement : Prop := ∀ (n m : Z) (_ : Rle (IZR n) (IZR m)), Z.le n m
def lt_0_INRStatement : Prop := ∀ (n : Nat) (_ : lt 0 n), Rlt (IZR Z0) (INR n)
def lt_INRStatement : Prop := ∀ (n m : Nat) (_ : lt n m), Rlt (INR n) (INR m)
def lt_IZRStatement : Prop := ∀ (n m : Z) (_ : Rlt (IZR n) (IZR m)), Z.lt n m
def minus_IZRStatement : Prop := ∀ n m : Z, Eq (IZR (Z.sub n m)) (Rminus (IZR n) (IZR m))
def mult_IZRStatement : Prop := ∀ n m : Z, Eq (IZR (Z.mul n m)) (Rmult (IZR n) (IZR m))
def opp_IZRStatement : Prop := ∀ n : Z, Eq (IZR (Z.opp n)) (Ropp (IZR n))
def plus_IZRStatement : Prop := ∀ n m : Z, Eq (IZR (Z.add n m)) (Rplus (IZR n) (IZR m))
def Req_decStatement : Prop := ∀ r1 r2 : R, Or (Eq r1 r2) (Not (Eq r1 r2))
def Req_geStatement : Prop := ∀ (r1 r2 : R) (_ : Eq r1 r2), Rge r1 r2
def Rge_leStatement : Prop := ∀ (r1 r2 : R) (_ : Rge r1 r2), Rle r2 r1
def Rge_minusStatement : Prop := ∀ (r1 r2 : R) (_ : Rge r1 r2), Rge (Rminus r1 r2) (IZR Z0)
def Rgt_geStatement : Prop := ∀ (r1 r2 : R) (_ : Rgt r1 r2), Rge r1 r2
def Rgt_ltStatement : Prop := ∀ (r1 r2 : R) (_ : Rgt r1 r2), Rlt r2 r1
def Rgt_not_eqStatement : Prop := ∀ (r1 r2 : R) (_ : Rgt r1 r2), Not (Eq r1 r2)
def Rgt_transStatement : Prop := ∀ (r1 r2 r3 : R) (_ : Rgt r1 r2) (_ : Rgt r2 r3), Rgt r1 r3
def Rinv_0_lt_compatStatement : Prop := ∀ (r : R) (_ : Rlt (IZR Z0) r), Rlt (IZR Z0) (Rinv r)
def Rinv_1_lt_contravarStatement : Prop := ∀ (r1 r2 : R) (_ : Rle (IZR (Zpos xH)) r1) (_ : Rlt r1 r2), Rlt (Rinv r2) (Rinv r1)
def Rinv_1Statement : Prop := Eq (Rinv (IZR (Zpos xH))) (IZR (Zpos xH))
def Rinv_lt_contravarStatement : Prop := ∀ (r1 r2 : R) (_ : Rlt (IZR Z0) (Rmult r1 r2)) (_ : Rlt r1 r2), Rlt (Rinv r2) (Rinv r1)
def Rinv_neq_0_compatStatement : Prop := ∀ (r : R) (_ : Not (Eq r (IZR Z0))), Not (Eq (Rinv r) (IZR Z0))
def Rle_0_1Statement : Prop := Rle (IZR Z0) (IZR (Zpos xH))
def Rle_0_sqrStatement : Prop := ∀ r : R, Rle (IZR Z0) (Rsqr r)
def Rle_antisymStatement : Prop := ∀ (r1 r2 : R) (_ : Rle r1 r2) (_ : Rle r2 r1), Eq r1 r2
def Rle_decStatement : Type := ∀ r1 r2 : R, Sumbool (Rle r1 r2) (Not (Rle r1 r2))
def Rle_geStatement : Prop := ∀ (r1 r2 : R) (_ : Rle r1 r2), Rge r2 r1
def Rle_lt_decStatement : Type := ∀ r1 r2 : R, Sumbool (Rle r1 r2) (Rlt r2 r1)
def Rle_lt_or_eq_decStatement : Type := ∀ (r1 r2 : R) (_ : Rle r1 r2), Sumbool (Rlt r1 r2) (Eq r1 r2)
def Rle_lt_transStatement : Prop := ∀ (r1 r2 r3 : R) (_ : Rle r1 r2) (_ : Rlt r2 r3), Rlt r1 r3
def Rle_minusStatement : Prop := ∀ (r1 r2 : R) (_ : Rle r1 r2), Rle (Rminus r1 r2) (IZR Z0)
def Rle_not_ltStatement : Prop := ∀ (r1 r2 : R) (_ : Rle r2 r1), Not (Rlt r1 r2)
def Rle_or_ltStatement : Prop := ∀ r1 r2 : R, Or (Rle r1 r2) (Rlt r2 r1)
def Rle_reflStatement : Prop := ∀ r : R, Rle r r
def Rle_transStatement : Prop := ∀ (r1 r2 r3 : R) (_ : Rle r1 r2) (_ : Rle r2 r3), Rle r1 r3
def Rlt_0_1Statement : Prop := Rlt (IZR Z0) (IZR (Zpos xH))
def Rlt_0_2Statement : Prop := Rlt (IZR Z0) (IZR (Zpos (xO xH)))
def Rlt_0_minusStatement : Prop :=
  ∀ r1 r2 : R, Iff (Rlt (IZR Z0) (Rminus r2 r1)) (Rlt r1 r2)
def Rlt_irreflStatement : Prop := ∀ r : R, Not (Rlt r r)
def Rlt_le_decStatement : Type := ∀ r1 r2 : R, Sumbool (Rlt r1 r2) (Rle r2 r1)
def Rlt_leStatement : Prop := ∀ (r1 r2 : R) (_ : Rlt r1 r2), Rle r1 r2
def Rlt_le_transStatement : Prop := ∀ (r1 r2 r3 : R) (_ : Rlt r1 r2) (_ : Rle r2 r3), Rlt r1 r3
def Rlt_not_eqStatement : Prop := ∀ (r1 r2 : R) (_ : Rlt r1 r2), Not (Eq r1 r2)
def Rlt_not_leStatement : Prop := ∀ (r1 r2 : R) (_ : Rlt r2 r1), Not (Rle r1 r2)
def Rlt_or_leStatement : Prop := ∀ r1 r2 : R, Or (Rlt r1 r2) (Rle r2 r1)
def Rmult_0_lStatement : Prop := ∀ r : R, Eq (Rmult (IZR Z0) r) (IZR Z0)
def Rmult_0_rStatement : Prop := ∀ r : R, Eq (Rmult r (IZR Z0)) (IZR Z0)
def Rmult_1_rStatement : Prop := ∀ r : R, Eq (Rmult r (IZR (Zpos xH))) r
def Rmult_eq_0_compat_rStatement : Prop := ∀ (r1 r2 : R) (_ : Eq r1 (IZR Z0)), Eq (Rmult r1 r2) (IZR Z0)
def Rmult_eq_compat_lStatement : Prop := ∀ (r r1 r2 : R) (_ : Eq r1 r2), Eq (Rmult r r1) (Rmult r r2)
def Rmult_eq_reg_rStatement : Prop := ∀ (r r1 r2 : R) (_ : Eq (Rmult r1 r) (Rmult r2 r)) (_ : Not (Eq r (IZR Z0))), Eq r1 r2
def Rmult_ge_0_gt_0_lt_compatStatement : Prop := ∀ (r1 r2 r3 r4 : R) (_ : Rge r3 (IZR Z0)) (_ : Rgt r2 (IZR Z0)) (_ : Rlt r1 r2) (_ : Rlt r3 r4), Rlt (Rmult r1 r3) (Rmult r2 r4)
def Rmult_integral_contrapositive_currifiedStatement : Prop := ∀ (r1 r2 : R) (_ : Not (Eq r1 (IZR Z0))) (_ : Not (Eq r2 (IZR Z0))), Not (Eq (Rmult r1 r2) (IZR Z0))
def Rmult_integralStatement : Prop := ∀ (r1 r2 : R) (_ : Eq (Rmult r1 r2) (IZR Z0)), Or (Eq r1 (IZR Z0)) (Eq r2 (IZR Z0))
def Rmult_le_compat_lStatement : Prop := ∀ (r r1 r2 : R) (_ : Rle (IZR Z0) r) (_ : Rle r1 r2), Rle (Rmult r r1) (Rmult r r2)
def Rmult_le_compat_rStatement : Prop := ∀ (r r1 r2 : R) (_ : Rle (IZR Z0) r) (_ : Rle r1 r2), Rle (Rmult r1 r) (Rmult r2 r)
def Rmult_le_compatStatement : Prop := ∀ (r1 r2 r3 r4 : R) (_ : Rle (IZR Z0) r1) (_ : Rle (IZR Z0) r3) (_ : Rle r1 r2) (_ : Rle r3 r4), Rle (Rmult r1 r3) (Rmult r2 r4)
def Rmult_le_posStatement : Prop := ∀ (r1 r2 : R) (_ : Rle (IZR Z0) r1) (_ : Rle (IZR Z0) r2), Rle (IZR Z0) (Rmult r1 r2)
def Rmult_le_reg_rStatement : Prop := ∀ (r r1 r2 : R) (_ : Rlt (IZR Z0) r) (_ : Rle (Rmult r1 r) (Rmult r2 r)), Rle r1 r2
def Rmult_lt_0_compatStatement : Prop := ∀ (r1 r2 : R) (_ : Rlt (IZR Z0) r1) (_ : Rlt (IZR Z0) r2), Rlt (IZR Z0) (Rmult r1 r2)
def Rmult_lt_compat_rStatement : Prop := ∀ (r r1 r2 : R) (_ : Rlt (IZR Z0) r) (_ : Rlt r1 r2), Rlt (Rmult r1 r) (Rmult r2 r)
def Rmult_lt_reg_lStatement : Prop := ∀ (r r1 r2 : R) (_ : Rlt (IZR Z0) r) (_ : Rlt (Rmult r r1) (Rmult r r2)), Rlt r1 r2
def Rmult_lt_reg_rStatement : Prop := ∀ (r r1 r2 : R) (_ : Rlt (IZR Z0) r) (_ : Rlt (Rmult r1 r) (Rmult r2 r)), Rlt r1 r2
def Rmult_opp_oppStatement : Prop := ∀ r1 r2 : R, Eq (Rmult (Ropp r1) (Ropp r2)) (Rmult r1 r2)
def Rmult_minus_distr_rStatement : Prop :=
  ∀ r1 r2 r3 : R,
    Eq (Rmult (Rminus r2 r3) r1) (Rminus (Rmult r2 r1) (Rmult r3 r1))
def Rmult_plus_distr_rStatement : Prop := ∀ r1 r2 r3 : R, Eq (Rmult (Rplus r1 r2) r3) (Rplus (Rmult r1 r3) (Rmult r2 r3))
def Rnot_le_ltStatement : Prop := ∀ (r1 r2 : R) (_ : Not (Rle r1 r2)), Rlt r2 r1
def Rnot_lt_leStatement : Prop := ∀ (r1 r2 : R) (_ : Not (Rlt r1 r2)), Rle r2 r1
def Ropp_0_gt_lt_contravarStatement : Prop := ∀ (r : R) (_ : Rgt (IZR Z0) r), Rlt (IZR Z0) (Ropp r)
def Ropp_0Statement : Prop := Eq (Ropp (IZR Z0)) (IZR Z0)
def Ropp_involutiveStatement : Prop := ∀ r : R, Eq (Ropp (Ropp r)) r
def Ropp_le_cancelStatement : Prop := ∀ (r1 r2 : R) (_ : Rle (Ropp r2) (Ropp r1)), Rle r1 r2
def Ropp_le_contravarStatement : Prop := ∀ (r1 r2 : R) (_ : Rle r2 r1), Rle (Ropp r1) (Ropp r2)
def Ropp_lt_cancelStatement : Prop := ∀ (r1 r2 : R) (_ : Rlt (Ropp r2) (Ropp r1)), Rlt r1 r2
def Ropp_lt_contravarStatement : Prop := ∀ (r1 r2 : R) (_ : Rlt r2 r1), Rlt (Ropp r1) (Ropp r2)
def Ropp_lt_gt_0_contravarStatement : Prop := ∀ (r : R) (_ : Rgt r (IZR Z0)), Rlt (Ropp r) (IZR Z0)
def Ropp_minus_distrStatement : Prop := ∀ r1 r2 : R, Eq (Ropp (Rminus r1 r2)) (Rminus r2 r1)
def Ropp_mult_distr_l_reverseStatement : Prop := ∀ r1 r2 : R, Eq (Rmult (Ropp r1) r2) (Ropp (Rmult r1 r2))
def Ropp_mult_distr_r_reverseStatement : Prop := ∀ r1 r2 : R, Eq (Rmult r1 (Ropp r2)) (Ropp (Rmult r1 r2))
def Ropp_plus_distrStatement : Prop := ∀ r1 r2 : R, Eq (Ropp (Rplus r1 r2)) (Rplus (Ropp r1) (Ropp r2))
def Rplus_0_rStatement : Prop := ∀ r : R, Eq (Rplus r (IZR Z0)) r
def Rplus_eq_reg_lStatement : Prop := ∀ (r r1 r2 : R) (_ : Eq (Rplus r r1) (Rplus r r2)), Eq r1 r2
def Rplus_le_compat_lStatement : Prop := ∀ (r r1 r2 : R) (_ : Rle r1 r2), Rle (Rplus r r1) (Rplus r r2)
def Rplus_le_compat_rStatement : Prop := ∀ (r r1 r2 : R) (_ : Rle r1 r2), Rle (Rplus r1 r) (Rplus r2 r)
def Rplus_le_compatStatement : Prop := ∀ (r1 r2 r3 r4 : R) (_ : Rle r1 r2) (_ : Rle r3 r4), Rle (Rplus r1 r3) (Rplus r2 r4)
def Rplus_le_reg_rStatement : Prop := ∀ (r r1 r2 : R) (_ : Rle (Rplus r1 r) (Rplus r2 r)), Rle r1 r2
def Rplus_lt_compat_rStatement : Prop := ∀ (r r1 r2 : R) (_ : Rlt r1 r2), Rlt (Rplus r1 r) (Rplus r2 r)
def Rplus_lt_compatStatement : Prop := ∀ (r1 r2 r3 r4 : R) (_ : Rlt r1 r2) (_ : Rlt r3 r4), Rlt (Rplus r1 r3) (Rplus r2 r4)
def Rplus_lt_reg_lStatement : Prop := ∀ (r r1 r2 : R) (_ : Rlt (Rplus r r1) (Rplus r r2)), Rlt r1 r2
def Rplus_lt_reg_rStatement : Prop := ∀ (r r1 r2 : R) (_ : Rlt (Rplus r1 r) (Rplus r2 r)), Rlt r1 r2
def Rplus_opp_lStatement : Prop := ∀ r : R, Eq (Rplus (Ropp r) r) (IZR Z0)
def Rplus_opp_r_uniqStatement : Prop := ∀ (r1 r2 : R) (_ : Eq (Rplus r1 r2) (IZR Z0)), Eq r2 (Ropp r1)
def S_INRStatement : Prop := ∀ n : Nat, Eq (INR (Nat.succ n)) (Rplus (INR n) (IZR (Zpos xH)))

end RIneq

namespace Rpower

def exp_increasingStatement : Prop := ∀ (x y : R) (_ : Rlt x y), Rlt (exp x) (exp y)
def exp_lnStatement : Prop := ∀ (x : R) (_ : Rlt (IZR Z0) x), Eq (exp (ln x)) x
def exp_lt_invStatement : Prop := ∀ (x y : R) (_ : Rlt (exp x) (exp y)), Rlt x y
def exp_RoppStatement : Prop := ∀ x : R, Eq (exp (Ropp x)) (Rinv (exp x))

end Rpower

namespace Rsqrt_def

def Rsqrt_positivityStatement : Prop :=
  ∀ (ctx : ExactRealContext) (x : ExactNonnegReal ctx),
    ExactReal.Rle ctx.spec (ExactReal.R0 ctx.spec)
      (ExactReal.Rsqrt ctx.spec x.nonneg)

end Rsqrt_def

namespace Rtrigo_def

def exp_0Statement : Prop := Eq (exp (IZR Z0)) (IZR (Zpos xH))

end Rtrigo_def

end ExactStatements
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Rmult_lt_compat_r (ctx : ExactRealContext) :
    Rmult_lt_compat_rStatement ctx := by
  intro r r1 r2 hr h12
  have hzero : ExactReal.IZR ctx.spec Z0 = ctx.spec.zero := by
    exact ctx.certificate.sourceLaws.ofZ_zero
  have hr' : ctx.spec.lt ctx.spec.zero r := by
    rw [← hzero]
    exact hr
  change ctx.spec.lt (ctx.spec.mul r1 r) (ctx.spec.mul r2 r)
  rw [ctx.certificate.orderedField.mul_comm r1 r,
    ctx.certificate.orderedField.mul_comm r2 r]
  exact ctx.certificate.orderedField.mul_lt_compat_l r r1 r2 hr' h12

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

private theorem exact_zero_lt_one (ctx : ExactRealContext) :
    ctx.spec.lt ctx.spec.zero ctx.spec.one := by
  have hz : ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ (ctx.spec.up ctx.spec.zero)) := by
    simpa [ExactReal.R0] using ctx.certificate.sourceLaws.up_gt ctx.spec.zero
  have hg := ctx.certificate.sourceLaws.up_gap ctx.spec.zero
  have hneg0 : ctx.spec.neg ctx.spec.zero = ctx.spec.zero := by
    calc
      ctx.spec.neg ctx.spec.zero =
          ctx.spec.add (ctx.spec.neg ctx.spec.zero) ctx.spec.zero :=
        (ctx.certificate.orderedField.add_zero _).symm
      _ = ctx.spec.zero := ctx.certificate.orderedField.neg_add_cancel _
  have hz0 : ctx.spec.add (ctx.spec.ofZ (ctx.spec.up ctx.spec.zero))
      (ctx.spec.neg ctx.spec.zero) = ctx.spec.ofZ (ctx.spec.up ctx.spec.zero) := by
    rw [hneg0, ctx.certificate.orderedField.add_zero]
  have hg' : ctx.spec.le (ctx.spec.ofZ (ctx.spec.up ctx.spec.zero)) ctx.spec.one := by
    rw [← hz0, ← ctx.certificate.sourceLaws.ofZ_one]
    exact hg
  apply (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
  constructor
  · have hzle := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hz
    exact ctx.certificate.orderedField.le_trans _ _ _ hzle.1 hg'
  · intro h10
    have hzle := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hz
    exact hzle.2 (ctx.certificate.orderedField.le_trans _ _ _ hg' h10)

private theorem posToNat_succ (p : positive) :
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ p) =
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p + 1 := by
  induction p with
  | xH => simp [Numbers.Rocq.Coq.PArith.BinPos.Pos.succ,
      Numbers.Rocq.Coq.posToNat]
  | xI p ih => simp [Numbers.Rocq.Coq.PArith.BinPos.Pos.succ,
      Numbers.Rocq.Coq.posToNat, ih] <;> omega
  | xO p ih => simp [Numbers.Rocq.Coq.PArith.BinPos.Pos.succ,
      Numbers.Rocq.Coq.posToNat]

private theorem zadd_pos_one (p : positive) :
    Z.add (Zpos p) (Zpos xH) = Zpos
      (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ p) := by
  apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add]
  rw [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change Int.ofNat (Numbers.Rocq.Coq.posToNat p) + Int.ofNat 1 =
    Int.ofNat (Numbers.Rocq.Coq.posToNat
      (Numbers.Rocq.Coq.PArith.BinPos.Pos.succ p))
  rw [posToNat_succ]
  simp

private theorem zadd_sub_cancel (n m : Z) :
    Z.add n (Z.sub m n) = m := by
  apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub]
  simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

private theorem exact_IZR_pos (ctx : ExactRealContext) (p : positive) :
    ctx.spec.lt ctx.spec.zero (ExactReal.IZR ctx.spec (Zpos p)) := by
  apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.peano_ind
    (P := fun p => ctx.spec.lt ctx.spec.zero (ExactReal.IZR ctx.spec (Zpos p)))
  · change ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ
      (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH))
    rw [ctx.certificate.sourceLaws.ofZ_one]
    exact exact_zero_lt_one ctx
  · intro p ih
    have h := ctx.certificate.orderedField.add_lt_compat_l
      ctx.spec.one ctx.spec.zero (ExactReal.IZR ctx.spec (Zpos p)) ih
    rw [ctx.certificate.orderedField.add_zero] at h
    rw [← ctx.certificate.orderedField.add_comm] at h
    have h' := ctx.certificate.orderedField.lt_trans
      ctx.spec.zero ctx.spec.one
      (ctx.spec.add (ExactReal.IZR ctx.spec (Zpos p)) ctx.spec.one)
      (exact_zero_lt_one ctx) h
    change ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ
      (Zpos (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ p)))
    rw [← zadd_pos_one, ctx.certificate.sourceLaws.ofZ_add,
      ctx.certificate.sourceLaws.ofZ_one]
    exact h'

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Rle_refl (ctx : ExactRealContext) :
    Rle_reflStatement ctx := by
  intro r
  exact ctx.certificate.orderedField.le_refl r

theorem Rlt_le (ctx : ExactRealContext) :
    Rlt_leStatement ctx := by
  intro r1 r2 h
  exact (ctx.certificate.orderedField.lt_iff_le_not_le r1 r2).mp h |>.1

theorem Rlt_le_trans (ctx : ExactRealContext) :
    Rlt_le_transStatement ctx := by
  intro r1 r2 r3 h12 h23
  apply (ctx.certificate.orderedField.lt_iff_le_not_le r1 r3).mpr
  constructor
  · exact ctx.certificate.orderedField.le_trans r1 r2 r3
      ((ctx.certificate.orderedField.lt_iff_le_not_le r1 r2).mp h12).1 h23
  · intro h31
    apply (ctx.certificate.orderedField.lt_iff_le_not_le r1 r2).mp h12 |>.2
    exact ctx.certificate.orderedField.le_trans r2 r3 r1 h23 h31

private theorem zsub_positive (n m : Z) (h : Z.lt n m) :
    ∃ p : positive, Z.sub m n = Zpos p := by
  have hsum : Z.add n (Z.sub m n) = m := zadd_sub_cancel n m
  change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n <
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m at h
  rw [← hsum] at h
  simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at h
  cases hd : Z.sub m n with
  | Z0 =>
      simp [hd, _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at h
  | Zpos p => exact ⟨p, by simpa using hd⟩
  | Zneg p =>
      rw [hd] at h
      simp [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at h
      have hp := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      omega

theorem IZR_lt (ctx : ExactRealContext) :
    IZR_ltStatement ctx := by
  intro n m hnm
  obtain ⟨p, hp⟩ := zsub_positive n m hnm
  have hpos := exact_IZR_pos ctx p
  have hadd := ctx.certificate.orderedField.add_lt_compat_l
    (ExactReal.IZR ctx.spec n) ctx.spec.zero
    (ExactReal.IZR ctx.spec (Zpos p)) hpos
  rw [ctx.certificate.orderedField.add_zero] at hadd
  rw [← zadd_sub_cancel n m, hp]
  change ctx.spec.lt (ctx.spec.ofZ n) (ctx.spec.ofZ (Z.add n (Zpos p)))
  rw [ctx.certificate.sourceLaws.ofZ_add]
  exact hadd

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

private theorem exact_zopp_pos (p : positive) :
    Z.opp (Zpos p) = _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg p := by
  apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp]
  rw [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  rfl

private theorem exact_zmul_negpos (n : Z) (p : positive) :
    Z.mul n (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg p) =
      Z.opp (Z.mul n (Zpos p)) := by
  rw [← exact_zopp_pos]
  apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp]
  simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
  rw [Int.mul_neg]

private theorem exact_mul_neg_right (ctx : ExactRealContext)
    (x y : ctx.spec.carrier) :
    ctx.spec.mul x (ctx.spec.neg y) = ctx.spec.neg (ctx.spec.mul x y) := by
  have h : ctx.spec.add (ctx.spec.mul x (ctx.spec.neg y)) (ctx.spec.mul x y) =
      ctx.spec.zero := by
    rw [← ctx.certificate.orderedField.left_distrib,
      ctx.certificate.orderedField.neg_add_cancel,
      ctx.certificate.orderedField.mul_zero]
  symm
  calc
    ctx.spec.neg (ctx.spec.mul x y) =
        ctx.spec.add (ctx.spec.neg (ctx.spec.mul x y)) ctx.spec.zero :=
      (ctx.certificate.orderedField.add_zero _).symm
    _ = ctx.spec.add (ctx.spec.neg (ctx.spec.mul x y))
        (ctx.spec.add (ctx.spec.mul x (ctx.spec.neg y)) (ctx.spec.mul x y)) := by
          rw [h]
    _ = ctx.spec.add (ctx.spec.neg (ctx.spec.mul x y))
        (ctx.spec.add (ctx.spec.mul x y) (ctx.spec.mul x (ctx.spec.neg y))) := by
          rw [ctx.certificate.orderedField.add_comm
            (ctx.spec.mul x (ctx.spec.neg y))]
    _ = ctx.spec.add
        (ctx.spec.add (ctx.spec.neg (ctx.spec.mul x y)) (ctx.spec.mul x y))
        (ctx.spec.mul x (ctx.spec.neg y)) := by
          rw [ctx.certificate.orderedField.add_assoc]
    _ = ctx.spec.add ctx.spec.zero (ctx.spec.mul x (ctx.spec.neg y)) := by
          rw [ctx.certificate.orderedField.neg_add_cancel]
    _ = ctx.spec.mul x (ctx.spec.neg y) :=
      ctx.certificate.orderedField.zero_add _

private theorem exact_posToNat_succ (p : positive) :
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ p) =
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p + 1 := by
  induction p with
  | xH => simp [Numbers.Rocq.Coq.PArith.BinPos.Pos.succ,
      Numbers.Rocq.Coq.posToNat]
  | xI p ih => simp [Numbers.Rocq.Coq.PArith.BinPos.Pos.succ,
      Numbers.Rocq.Coq.posToNat, ih] <;> omega
  | xO p ih => simp [Numbers.Rocq.Coq.PArith.BinPos.Pos.succ,
      Numbers.Rocq.Coq.posToNat]

private theorem exact_zadd_pos_one (p : positive) :
    Z.add (Zpos p) (Zpos xH) = Zpos
      (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ p) := by
  apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add]
  rw [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change Int.ofNat (Numbers.Rocq.Coq.posToNat p) + Int.ofNat 1 =
    Int.ofNat (Numbers.Rocq.Coq.posToNat
      (Numbers.Rocq.Coq.PArith.BinPos.Pos.succ p))
  rw [exact_posToNat_succ]
  simp

private theorem exact_mul_IZR_pos (ctx : ExactRealContext) (n : Z) (p : positive) :
    ctx.spec.ofZ (Z.mul n (Zpos p)) =
      ctx.spec.mul (ctx.spec.ofZ n) (ctx.spec.ofZ (Zpos p)) := by
  apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.peano_ind
    (P := fun p => ctx.spec.ofZ (Z.mul n (Zpos p)) =
      ctx.spec.mul (ctx.spec.ofZ n) (ctx.spec.ofZ (Zpos p)))
  · rw [show Z.mul n (Zpos xH) = n by
      apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n * 1 =
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n
      omega,
      ctx.certificate.sourceLaws.ofZ_one,
      ctx.certificate.orderedField.mul_one]
  · intro p ih
    rw [show Z.mul n
        (Zpos (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ p)) =
          Z.add (Z.mul n (Zpos p)) n by
      apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n *
          _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
            (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ p) =
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n *
          _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p +
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n
      rw [exact_posToNat_succ]
      push_cast
      rw [Int.mul_add]
      simp,
      ctx.certificate.sourceLaws.ofZ_add, ih,
      ← exact_zadd_pos_one, ctx.certificate.sourceLaws.ofZ_add,
      ctx.certificate.sourceLaws.ofZ_one,
      ctx.certificate.orderedField.left_distrib,
      ctx.certificate.orderedField.mul_one]

private theorem exact_mul_IZR_negpos (ctx : ExactRealContext) (n : Z) (p : positive) :
    ctx.spec.ofZ (Z.mul n (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg p)) =
      ctx.spec.mul (ctx.spec.ofZ n)
        (ctx.spec.ofZ (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg p)) := by
  rw [exact_zmul_negpos, ctx.certificate.sourceLaws.ofZ_neg]
  rw [← exact_zopp_pos, ctx.certificate.sourceLaws.ofZ_neg]
  rw [exact_mul_neg_right]
  exact congrArg ctx.spec.neg (exact_mul_IZR_pos ctx n p)

private theorem exact_mul_IZR (ctx : ExactRealContext) (n m : Z) :
    ctx.spec.ofZ (Z.mul n m) = ctx.spec.mul (ctx.spec.ofZ n) (ctx.spec.ofZ m) := by
  cases m with
  | Z0 =>
      have hz : Z.mul n Z0 = Z0 := by
        cases n with
        | Z0 => rfl
        | Zpos p =>
            apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
            simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul]
            rw [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
            change Int.ofNat (Numbers.Rocq.Coq.posToNat p) * 0 = 0
            omega
        | Zneg p =>
            apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
            simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul]
            rw [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
            change (-Int.ofNat (Numbers.Rocq.Coq.posToNat p)) * 0 = 0
            omega
      rw [hz, ctx.certificate.sourceLaws.ofZ_zero,
        ctx.certificate.orderedField.mul_zero]
  | Zpos p => exact exact_mul_IZR_pos ctx n p
  | Zneg p => exact exact_mul_IZR_negpos ctx n p

theorem mult_IZR (ctx : ExactRealContext) :
    mult_IZRStatement ctx := by
  intro n m
  exact exact_mul_IZR ctx n m

end RIneq

namespace Raxioms

theorem Rplus_lt_compat_l (ctx : ExactRealContext) :
    Rplus_lt_compat_lStatement ctx := by
  intro r r1 r2 h
  exact ctx.certificate.orderedField.add_lt_compat_l r r1 r2 h

end Raxioms

namespace RIneq

theorem Rmult_lt_0_compat (ctx : ExactRealContext) :
    Rmult_lt_0_compatStatement ctx := by
  intro r1 r2 hr1 hr2
  change ctx.spec.lt (ctx.spec.ofZ Z0) r1 at hr1
  change ctx.spec.lt (ctx.spec.ofZ Z0) r2 at hr2
  rw [ctx.certificate.sourceLaws.ofZ_zero] at hr1 hr2
  have h := ctx.certificate.orderedField.mul_lt_compat_l
    r1 ctx.spec.zero r2 hr1 hr2
  rw [ctx.certificate.orderedField.mul_zero] at h
  change ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.mul r1 r2)
  rw [ctx.certificate.sourceLaws.ofZ_zero]
  exact h

theorem IZR_le (ctx : ExactRealContext) :
    IZR_leStatement ctx := by
  intro n m h
  change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n ≤
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m at h
  rcases Int.lt_or_eq_of_le h with h | h
  · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
      (IZR_lt ctx n m h) |>.1
  · have hnm : n = m := by
      rw [← _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt_intOfZ n,
        ← _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt_intOfZ m, h]
    subst m
    exact ctx.certificate.orderedField.le_refl _

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Rplus_0_r (ctx : ExactRealContext) :
    Rplus_0_rStatement ctx := by
  intro r
  change ctx.spec.add r (ctx.spec.ofZ Z0) = r
  rw [ctx.certificate.sourceLaws.ofZ_zero]
  exact ctx.certificate.orderedField.add_zero r

theorem Rle_lt_trans (ctx : ExactRealContext) :
    Rle_lt_transStatement ctx := by
  intro r1 r2 r3 h12 h23
  have h23' := (ctx.certificate.orderedField.lt_iff_le_not_le r2 r3).mp h23
  apply (ctx.certificate.orderedField.lt_iff_le_not_le r1 r3).mpr
  constructor
  · exact ctx.certificate.orderedField.le_trans r1 r2 r3 h12 h23'.1
  · intro h31
    exact h23'.2 (ctx.certificate.orderedField.le_trans r3 r1 r2 h31 h12)

theorem Rplus_le_compat_l (ctx : ExactRealContext) :
    Rplus_le_compat_lStatement ctx := by
  intro r r1 r2 h12
  rcases ctx.certificate.total_order r1 r2 with h12' | h21
  · rcases h12' with hlt | heq
    · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
        (ctx.certificate.orderedField.add_lt_compat_l r r1 r2 hlt) |>.1
    · subst r2
      exact ctx.certificate.orderedField.le_refl _
  · exact False.elim ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h21 |>.2 h12)

theorem Rmult_le_compat_r (ctx : ExactRealContext) :
    Rmult_le_compat_rStatement ctx := by
  intro r r1 r2 hr h12
  change ctx.spec.le (ctx.spec.ofZ Z0) r at hr
  rw [ctx.certificate.sourceLaws.ofZ_zero] at hr
  rcases ctx.certificate.total_order ctx.spec.zero r with hzr | hrz
  · rcases hzr with hpos | hzero
    · rcases ctx.certificate.total_order r1 r2 with h12' | h21
      · rcases h12' with hlt | heq
        · have hmul : ctx.spec.lt (ctx.spec.mul r r1) (ctx.spec.mul r r2) :=
            ctx.certificate.orderedField.mul_lt_compat_l r r1 r2 hpos hlt
          have hmul' : ctx.spec.lt (ctx.spec.mul r1 r) (ctx.spec.mul r2 r) := by
            rw [ctx.certificate.orderedField.mul_comm r1 r,
              ctx.certificate.orderedField.mul_comm r2 r]
            exact hmul
          exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hmul' |>.1
        · subst r2
          exact ctx.certificate.orderedField.le_refl _
      · exact False.elim ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h21 |>.2 h12)
    · subst r
      change ctx.spec.le (ctx.spec.mul r1 ctx.spec.zero)
        (ctx.spec.mul r2 ctx.spec.zero)
      rw [ctx.certificate.orderedField.mul_zero, ctx.certificate.orderedField.mul_zero]
      exact ctx.certificate.orderedField.le_refl _
  · exact False.elim ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hrz |>.2 hr)

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals

namespace RIneq

theorem Rmult_1_r (ctx : ExactRealContext) :
    Rmult_1_rStatement ctx := by
  intro r
  change ctx.spec.mul r (ctx.spec.ofZ
    (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH)) = r
  rw [ctx.certificate.sourceLaws.ofZ_one]
  exact ctx.certificate.orderedField.mul_one r

theorem plus_IZR (ctx : ExactRealContext) :
    plus_IZRStatement ctx := by
  intro n m
  exact ctx.certificate.sourceLaws.ofZ_add n m

end RIneq

namespace Raxioms

theorem Rmult_1_l (ctx : ExactRealContext) :
    Rmult_1_lStatement ctx := by
  intro r
  change ctx.spec.mul (ctx.spec.ofZ
    (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH)) r = r
  rw [ctx.certificate.sourceLaws.ofZ_one]
  exact ctx.certificate.orderedField.one_mul r

theorem Rlt_trans (ctx : ExactRealContext) :
    Rlt_transStatement ctx := by
  intro r1 r2 r3 h12 h23
  exact ctx.certificate.orderedField.lt_trans r1 r2 r3 h12 h23

end Raxioms
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Rmult_0_l (ctx : ExactRealContext) :
    Rmult_0_lStatement ctx := by
  intro r
  change ctx.spec.mul (ctx.spec.ofZ Z0) r = ctx.spec.ofZ Z0
  rw [ctx.certificate.sourceLaws.ofZ_zero]
  exact ctx.certificate.orderedField.zero_mul r

theorem Rgt_not_eq (ctx : ExactRealContext) :
    Rgt_not_eqStatement ctx := by
  intro r1 r2 hgt heq
  change ctx.spec.lt r2 r1 at hgt
  subst r1
  exact ctx.certificate.orderedField.lt_irrefl r2 hgt

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Rinv_0_lt_compat (ctx : ExactRealContext) :
    Rinv_0_lt_compatStatement ctx := by
  intro r hr
  have hzero : ExactReal.IZR ctx.spec Z0 = ctx.spec.zero :=
    ctx.certificate.sourceLaws.ofZ_zero
  have hr' : ctx.spec.lt ctx.spec.zero r := by
    rw [← hzero]
    exact hr
  have hrne : r ≠ ctx.spec.zero := by
    intro heq
    subst r
    exact ctx.certificate.orderedField.lt_irrefl _ hr'
  have hinv_ne_zero : ctx.spec.inv r ≠ ctx.spec.zero := by
    intro heq
    have hc := ctx.certificate.orderedField.inv_mul_cancel r hrne
    rw [heq, ctx.certificate.orderedField.zero_mul] at hc
    exact ctx.certificate.orderedField.zero_ne_one hc
  have hnonneg : ctx.spec.le ctx.spec.zero (ctx.spec.inv r) := by
    rcases ctx.certificate.total_order ctx.spec.zero (ctx.spec.inv r) with h | h
    · rcases h with hpos | heq
      · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hpos |>.1
      · rw [← heq]
        exact ctx.certificate.orderedField.le_refl _
    · have hmul := ctx.certificate.orderedField.mul_lt_compat_l
        r (ctx.spec.inv r) ctx.spec.zero hr' h
      rw [ctx.certificate.orderedField.mul_zero] at hmul
      have hmul' : ctx.spec.lt (ctx.spec.mul (ctx.spec.inv r) r) ctx.spec.zero := by
        rw [ctx.certificate.orderedField.mul_comm (ctx.spec.inv r) r]
        exact hmul
      rw [ctx.certificate.orderedField.inv_mul_cancel r hrne] at hmul'
      have hbad : ctx.spec.lt ctx.spec.zero ctx.spec.zero :=
        ctx.certificate.orderedField.lt_trans
          ctx.spec.zero ctx.spec.one ctx.spec.zero
          (exact_zero_lt_one ctx) hmul'
      exact (ctx.certificate.orderedField.lt_irrefl _ hbad).elim
  rw [hzero]
  apply (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
  constructor
  · exact hnonneg
  · intro hle
    have heq := ctx.certificate.orderedField.le_antisymm
      ctx.spec.zero (ctx.spec.inv r) hnonneg hle
    exact hinv_ne_zero heq.symm

theorem Rlt_0_minus_proof (ctx : ExactRealContext) :
    Rlt_0_minusStatement ctx := by
  intro r1 r2
  have hzero : ExactReal.IZR ctx.spec Z0 = ctx.spec.zero :=
    ctx.certificate.sourceLaws.ofZ_zero
  constructor
  · intro h
    change ctx.spec.lt (ctx.spec.ofZ Z0)
      (ctx.spec.add r2 (ctx.spec.neg r1)) at h
    have hbase : ctx.spec.lt ctx.spec.zero
        (ctx.spec.add r2 (ctx.spec.neg r1)) := by
      rw [← hzero]
      exact h
    have h' := ctx.certificate.orderedField.add_lt_compat_l
      r1 ctx.spec.zero (ctx.spec.add r2 (ctx.spec.neg r1)) hbase
    rw [ctx.certificate.orderedField.add_zero] at h'
    have hadd : ctx.spec.add r1
        (ctx.spec.add r2 (ctx.spec.neg r1)) = r2 := by
      calc
        ctx.spec.add r1 (ctx.spec.add r2 (ctx.spec.neg r1)) =
            ctx.spec.add (ctx.spec.add r1 r2) (ctx.spec.neg r1) := by
              rw [ctx.certificate.orderedField.add_assoc]
        _ = ctx.spec.add (ctx.spec.add r2 r1) (ctx.spec.neg r1) := by
              rw [ctx.certificate.orderedField.add_comm r1 r2]
        _ = ctx.spec.add r2 (ctx.spec.add r1 (ctx.spec.neg r1)) := by
              rw [← ctx.certificate.orderedField.add_assoc]
        _ = ctx.spec.add r2 ctx.spec.zero := by
              rw [show ctx.spec.add r1 (ctx.spec.neg r1) = ctx.spec.zero by
                rw [ctx.certificate.orderedField.add_comm,
                  ctx.certificate.orderedField.neg_add_cancel]]
        _ = r2 := ctx.certificate.orderedField.add_zero _
    rw [hadd] at h'
    exact h'
  · intro h
    change ctx.spec.lt r1 r2 at h
    have h' : ctx.spec.lt
        (ctx.spec.add (ctx.spec.neg r1) r1)
        (ctx.spec.add (ctx.spec.neg r1) r2) :=
      ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.neg r1) r1 r2 h
    rw [ctx.certificate.orderedField.neg_add_cancel] at h'
    rw [ctx.certificate.orderedField.add_comm (ctx.spec.neg r1) r2] at h'
    change ctx.spec.lt (ctx.spec.ofZ Z0)
      (ctx.spec.add r2 (ctx.spec.neg r1))
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact h'

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals

namespace Raxioms

theorem Rmult_assoc (ctx : ExactRealContext) :
    Rmult_assocStatement ctx := by
  intro r1 r2 r3
  exact ctx.certificate.orderedField.mul_assoc r1 r2 r3

end Raxioms

namespace RIneq

theorem Rlt_irrefl (ctx : ExactRealContext) :
    Rlt_irreflStatement ctx := by
  intro r
  exact ctx.certificate.orderedField.lt_irrefl r

theorem Rplus_lt_reg_l (ctx : ExactRealContext) :
    Rplus_lt_reg_lStatement ctx := by
  intro r r1 r2 h
  have h' := ctx.certificate.orderedField.add_lt_compat_l
    (ctx.spec.neg r) (ctx.spec.add r r1) (ctx.spec.add r r2) h
  rw [← ctx.certificate.orderedField.add_assoc,
    ctx.certificate.orderedField.neg_add_cancel,
    ctx.certificate.orderedField.zero_add,
    ← ctx.certificate.orderedField.add_assoc,
    ctx.certificate.orderedField.neg_add_cancel,
    ctx.certificate.orderedField.zero_add] at h'
  exact h'

theorem Rplus_lt_reg_r (ctx : ExactRealContext) :
    Rplus_lt_reg_rStatement ctx := by
  intro r r1 r2 h
  change ctx.spec.lt (ctx.spec.add r1 r) (ctx.spec.add r2 r) at h
  rw [ctx.certificate.orderedField.add_comm r1 r,
    ctx.certificate.orderedField.add_comm r2 r] at h
  exact Rplus_lt_reg_l ctx r r1 r2 h

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals

namespace Raxioms

theorem Rmult_comm (ctx : ExactRealContext) :
    Rmult_commStatement ctx := by
  intro r1 r2
  change ctx.spec.mul r1 r2 = ctx.spec.mul r2 r1
  exact ctx.certificate.orderedField.mul_comm r1 r2

theorem Rinv_l (ctx : ExactRealContext) :
    Rinv_lStatement ctx := by
  intro r hr
  have hrne : r ≠ ctx.spec.zero := by
    intro hzero
    apply hr
    calc
      r = ctx.spec.zero := hzero
      _ = ctx.spec.ofZ Z0 := ctx.certificate.sourceLaws.ofZ_zero.symm
  change ctx.spec.mul (ctx.spec.inv r) r =
    ctx.spec.ofZ (Zpos xH)
  rw [ctx.certificate.sourceLaws.ofZ_one]
  exact ctx.certificate.orderedField.inv_mul_cancel r hrne

end Raxioms
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Rlt_Rminus_proof :
    ∀ (ctx : ExactRealContext) (a b : ctx.spec.carrier)
      (_h : ExactReal.Rlt ctx.spec a b), Rlt_Rminus ctx a b _h := by
  intro ctx a b h
  change ctx.spec.lt ctx.spec.zero (ctx.spec.add b (ctx.spec.neg a))
  rw [← ctx.certificate.sourceLaws.ofZ_zero]
  exact (Rlt_0_minus_proof ctx a b).mpr h

private theorem flocqReal_Rmult_lt_reg_l (ctx : ExactRealContext)
    (r r1 r2 : ctx.spec.carrier)
    (hr : ctx.spec.lt ctx.spec.zero r)
    (h : ctx.spec.lt (ctx.spec.mul r r1) (ctx.spec.mul r r2)) :
    ctx.spec.lt r1 r2 := by
  have hr0 : ctx.spec.lt (ExactReal.IZR ctx.spec Z0) r := by
    change ctx.spec.lt (ctx.spec.ofZ Z0) r
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hr
  have hinv0 : ctx.spec.lt (ExactReal.IZR ctx.spec Z0) (ctx.spec.inv r) := by
    exact Rinv_0_lt_compat ctx r hr0
  have hinv0' : ctx.spec.lt ctx.spec.zero (ctx.spec.inv r) := by
    rw [← ctx.certificate.sourceLaws.ofZ_zero]
    exact hinv0
  have hrne : r ≠ ctx.spec.zero := by
    intro hzero
    subst r
    exact ctx.certificate.orderedField.lt_irrefl _ hr
  have hmul := ctx.certificate.orderedField.mul_lt_compat_l
    (ctx.spec.inv r) (ctx.spec.mul r r1) (ctx.spec.mul r r2) hinv0' h
  have hleft : ctx.spec.mul (ctx.spec.inv r) (ctx.spec.mul r r1) = r1 := by
    calc
      ctx.spec.mul (ctx.spec.inv r) (ctx.spec.mul r r1) =
          ctx.spec.mul (ctx.spec.mul (ctx.spec.inv r) r) r1 := by
            rw [ctx.certificate.orderedField.mul_assoc]
      _ = ctx.spec.mul ctx.spec.one r1 := by
            rw [ctx.certificate.orderedField.inv_mul_cancel r hrne]
      _ = r1 := ctx.certificate.orderedField.one_mul _
  have hright : ctx.spec.mul (ctx.spec.inv r) (ctx.spec.mul r r2) = r2 := by
    calc
      ctx.spec.mul (ctx.spec.inv r) (ctx.spec.mul r r2) =
          ctx.spec.mul (ctx.spec.mul (ctx.spec.inv r) r) r2 := by
            rw [ctx.certificate.orderedField.mul_assoc]
      _ = ctx.spec.mul ctx.spec.one r2 := by
            rw [ctx.certificate.orderedField.inv_mul_cancel r hrne]
      _ = r2 := ctx.certificate.orderedField.one_mul _
  rw [hleft, hright] at hmul
  exact hmul

theorem Rmult_lt_reg_r (ctx : ExactRealContext) :
    Rmult_lt_reg_rStatement ctx := by
  intro r r1 r2 hr h
  have hr' : ctx.spec.lt ctx.spec.zero r := by
    rw [← ctx.certificate.sourceLaws.ofZ_zero]
    exact hr
  have h' : ctx.spec.lt (ctx.spec.mul r r1) (ctx.spec.mul r r2) := by
    change ctx.spec.lt (ctx.spec.mul r1 r) (ctx.spec.mul r2 r) at h
    rw [ctx.certificate.orderedField.mul_comm r1 r,
      ctx.certificate.orderedField.mul_comm r2 r] at h
    exact h
  exact flocqReal_Rmult_lt_reg_l ctx r r1 r2 hr' h'

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals.Raxioms

theorem Rmult_lt_compat_l :
    ∀ (ctx : ExactRealContext), Rmult_lt_compat_lStatement ctx := by
  intro ctx r r1 r2 hr h12
  have hr' : ctx.spec.lt ctx.spec.zero r := by
    rw [← ctx.certificate.sourceLaws.ofZ_zero]
    exact hr
  exact ctx.certificate.orderedField.mul_lt_compat_l r r1 r2 hr' h12

end Rocq.Coq.Reals.Raxioms
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals.RIneq

theorem Req_dec :
    ∀ (ctx : ExactRealContext), Req_decStatement ctx := by
  intro ctx r1 r2
  rcases ctx.certificate.total_order r1 r2 with h | h
  · rcases h with hlt | heq
    · exact Or.inr (by
        intro heq'
        subst r2
        exact ctx.certificate.orderedField.lt_irrefl _ hlt)
    · exact Or.inl heq
  · exact Or.inr (by
      intro heq'
      subst r2
      exact ctx.certificate.orderedField.lt_irrefl _ h)

end Rocq.Coq.Reals.RIneq
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals.RIneq

theorem Rmult_plus_distr_r (ctx : ExactRealContext) :
    Rmult_plus_distr_rStatement ctx := by
  intro r1 r2 r3
  change ctx.spec.mul (ctx.spec.add r1 r2) r3 =
    ctx.spec.add (ctx.spec.mul r1 r3) (ctx.spec.mul r2 r3)
  calc
    ctx.spec.mul (ctx.spec.add r1 r2) r3 =
        ctx.spec.mul r3 (ctx.spec.add r1 r2) := by
      rw [ctx.certificate.orderedField.mul_comm]
    _ = ctx.spec.add (ctx.spec.mul r3 r1) (ctx.spec.mul r3 r2) :=
      ctx.certificate.orderedField.left_distrib r3 r1 r2
    _ = ctx.spec.add (ctx.spec.mul r1 r3) (ctx.spec.mul r2 r3) := by
      rw [ctx.certificate.orderedField.mul_comm r3 r1,
        ctx.certificate.orderedField.mul_comm r3 r2]

end Rocq.Coq.Reals.RIneq
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Rmult_le_pos (ctx : ExactRealContext) :
    Rmult_le_posStatement ctx := by
  intro r1 r2 h1 h2
  change ctx.spec.le (ctx.spec.ofZ Z0) r1 at h1
  change ctx.spec.le (ctx.spec.ofZ Z0) r2 at h2
  change ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.mul r1 r2)
  rw [ctx.certificate.sourceLaws.ofZ_zero] at h1 h2 ⊢
  rcases ctx.certificate.total_order ctx.spec.zero r1 with h1' | h1'
  · rcases h1' with hpos1 | hzero1
    · rcases ctx.certificate.total_order ctx.spec.zero r2 with h2' | h2'
      · rcases h2' with hpos2 | hzero2
        · have hmul := ctx.certificate.orderedField.mul_lt_compat_l
            r1 ctx.spec.zero r2 hpos1 hpos2
          rw [ctx.certificate.orderedField.mul_zero] at hmul
          exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hmul |>.1
        · subst r2
          rw [ctx.certificate.orderedField.mul_zero]
          exact ctx.certificate.orderedField.le_refl _
      · exact False.elim ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h2' |>.2 h2)
    · subst r1
      rw [ctx.certificate.orderedField.zero_mul]
      exact ctx.certificate.orderedField.le_refl _
  · exact False.elim ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h1' |>.2 h1)

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Rle_0_sqr (ctx : ExactRealContext) :
    Rle_0_sqrStatement ctx := by
  intro r
  change ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.mul r r)
  have neg_mul_right (x y : ctx.spec.carrier) :
      ctx.spec.mul x (ctx.spec.neg y) = ctx.spec.neg (ctx.spec.mul x y) := by
    have hcancel :
        ctx.spec.add (ctx.spec.mul x (ctx.spec.neg y))
            (ctx.spec.mul x y) = ctx.spec.zero := by
      rw [← ctx.certificate.orderedField.left_distrib,
        ctx.certificate.orderedField.neg_add_cancel,
        ctx.certificate.orderedField.mul_zero]
    symm
    calc
      ctx.spec.neg (ctx.spec.mul x y) =
          ctx.spec.add (ctx.spec.neg (ctx.spec.mul x y)) ctx.spec.zero :=
        (ctx.certificate.orderedField.add_zero _).symm
      _ = ctx.spec.add (ctx.spec.neg (ctx.spec.mul x y))
          (ctx.spec.add (ctx.spec.mul x (ctx.spec.neg y)) (ctx.spec.mul x y)) := by
        rw [hcancel]
      _ = ctx.spec.add (ctx.spec.neg (ctx.spec.mul x y))
          (ctx.spec.add (ctx.spec.mul x y) (ctx.spec.mul x (ctx.spec.neg y))) := by
        rw [ctx.certificate.orderedField.add_comm
          (ctx.spec.mul x (ctx.spec.neg y)) (ctx.spec.mul x y)]
      _ = ctx.spec.add
          (ctx.spec.add (ctx.spec.neg (ctx.spec.mul x y)) (ctx.spec.mul x y))
          (ctx.spec.mul x (ctx.spec.neg y)) := by
        rw [ctx.certificate.orderedField.add_assoc]
      _ = ctx.spec.add ctx.spec.zero (ctx.spec.mul x (ctx.spec.neg y)) := by
        rw [ctx.certificate.orderedField.neg_add_cancel]
      _ = ctx.spec.mul x (ctx.spec.neg y) :=
        ctx.certificate.orderedField.zero_add _
  have neg_neg (x : ctx.spec.carrier) :
      ctx.spec.neg (ctx.spec.neg x) = x := by
    calc
      ctx.spec.neg (ctx.spec.neg x) =
          ctx.spec.add (ctx.spec.neg (ctx.spec.neg x)) ctx.spec.zero :=
        (ctx.certificate.orderedField.add_zero _).symm
      _ = ctx.spec.add (ctx.spec.neg (ctx.spec.neg x))
          (ctx.spec.add (ctx.spec.neg x) x) := by
        rw [ctx.certificate.orderedField.neg_add_cancel]
      _ = ctx.spec.add
          (ctx.spec.add (ctx.spec.neg (ctx.spec.neg x)) (ctx.spec.neg x)) x := by
        rw [ctx.certificate.orderedField.add_assoc]
      _ = ctx.spec.add ctx.spec.zero x := by
        rw [ctx.certificate.orderedField.neg_add_cancel]
      _ = x := ctx.certificate.orderedField.zero_add _
  have neg_sqr (r : ctx.spec.carrier) :
      ctx.spec.mul (ctx.spec.neg r) (ctx.spec.neg r) = ctx.spec.mul r r := by
    calc
      ctx.spec.mul (ctx.spec.neg r) (ctx.spec.neg r) =
          ctx.spec.neg (ctx.spec.mul (ctx.spec.neg r) r) :=
        neg_mul_right (ctx.spec.neg r) r
      _ = ctx.spec.neg (ctx.spec.mul r (ctx.spec.neg r)) := by
        rw [ctx.certificate.orderedField.mul_comm]
      _ = ctx.spec.neg (ctx.spec.neg (ctx.spec.mul r r)) := by
        rw [neg_mul_right]
      _ = ctx.spec.mul r r := neg_neg _
  rcases ctx.certificate.total_order ctx.spec.zero r with h | h
  · rcases h with hpos | hzero
    · have hr : ctx.spec.le ctx.spec.zero r :=
        (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hpos |>.1
      have hr0 : ctx.spec.le (ctx.spec.ofZ Z0) r := by
        rw [ctx.certificate.sourceLaws.ofZ_zero]
        exact hr
      exact Rmult_le_pos ctx r r hr0 hr0
    · subst r
      rw [ctx.certificate.sourceLaws.ofZ_zero,
        ctx.certificate.orderedField.zero_mul]
      exact ctx.certificate.orderedField.le_refl _
  · have hposneg : ctx.spec.lt ctx.spec.zero (ctx.spec.neg r) := by
      have h' := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.neg r) r ctx.spec.zero h
      rw [ctx.certificate.orderedField.neg_add_cancel,
        ctx.certificate.orderedField.add_zero] at h'
      exact h'
    have hr : ctx.spec.le ctx.spec.zero (ctx.spec.neg r) :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hposneg |>.1
    have hr0 : ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.neg r) := by
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact hr
    have hs := Rmult_le_pos ctx (ctx.spec.neg r) (ctx.spec.neg r) hr0 hr0
    change ctx.spec.le (ctx.spec.ofZ Z0)
      (ctx.spec.mul (ctx.spec.neg r) (ctx.spec.neg r)) at hs
    rw [neg_sqr] at hs
    exact hs

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace R_sqrt

theorem sqrt_Rsqr :
    ∀ (ctx : ExactRealContext), sqrt_RsqrStatement ctx := by
  intro ctx x hx
  change ExactReal.sqrt ctx.spec (ctx.spec.mul x x) = x
  have hx' : ctx.spec.le ctx.spec.zero x := by
    change ctx.spec.le (ctx.spec.ofZ Z0) x at hx
    rw [ctx.certificate.sourceLaws.ofZ_zero] at hx
    exact hx
  have hsq : ctx.spec.le ctx.spec.zero (ctx.spec.mul x x) := by
    have h :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_0_sqr ctx x
    change ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.mul x x) at h
    rw [ctx.certificate.sourceLaws.ofZ_zero] at h
    exact h
  unfold ExactReal.sqrt
  cases hdec : ctx.spec.lt_dec (ctx.spec.mul x x) ctx.spec.zero with
  | left hlt =>
      exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt).2 hsq |>.elim
  | right _ =>
      exact ctx.certificate.sqrt.sqrt_sqr x hx'

end R_sqrt
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace R_sqrt

theorem Rsqr_sqrt :
    ∀ (ctx : ExactRealContext), Rsqr_sqrtStatement ctx := by
  intro ctx x hx
  change ctx.spec.mul (ExactReal.sqrt ctx.spec x) (ExactReal.sqrt ctx.spec x) = x
  have hx' : ctx.spec.le ctx.spec.zero x := by
    change ctx.spec.le (ctx.spec.ofZ Z0) x at hx
    rw [ctx.certificate.sourceLaws.ofZ_zero] at hx
    exact hx
  unfold ExactReal.sqrt
  cases hdec : ctx.spec.lt_dec x ctx.spec.zero with
  | left hlt =>
      exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt).2 hx' |>.elim
  | right _ =>
      exact ctx.certificate.sqrt.sqr x hx'

end R_sqrt
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace R_sqrt

theorem sqrt_mult :
    ∀ (ctx : ExactRealContext), sqrt_multStatement ctx := by
  intro ctx x y hx hy
  change ExactReal.sqrt ctx.spec (ctx.spec.mul x y) =
    ctx.spec.mul (ExactReal.sqrt ctx.spec x) (ExactReal.sqrt ctx.spec y)
  have hx' : ctx.spec.le ctx.spec.zero x := by
    change ctx.spec.le (ctx.spec.ofZ Z0) x at hx
    rw [ctx.certificate.sourceLaws.ofZ_zero] at hx
    exact hx
  have hy' : ctx.spec.le ctx.spec.zero y := by
    change ctx.spec.le (ctx.spec.ofZ Z0) y at hy
    rw [ctx.certificate.sourceLaws.ofZ_zero] at hy
    exact hy
  have hxy' : ctx.spec.le ctx.spec.zero (ctx.spec.mul x y) := by
    have h := RIneq.Rmult_le_pos ctx x y hx hy
    change ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.mul x y) at h
    rw [ctx.certificate.sourceLaws.ofZ_zero] at h
    exact h
  unfold ExactReal.sqrt
  cases hxydec : ctx.spec.lt_dec (ctx.spec.mul x y) ctx.spec.zero with
  | left hxylt =>
      exact (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxylt).2 hxy').elim
  | right _ =>
      cases hxdec : ctx.spec.lt_dec x ctx.spec.zero with
      | left hxlt =>
          exact (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxlt).2 hx').elim
      | right _ =>
          cases hydec : ctx.spec.lt_dec y ctx.spec.zero with
          | left hylt =>
              exact (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hylt).2 hy').elim
          | right _ =>
              simpa [hxydec, hxdec, hydec] using
                ctx.certificate.sourceLaws.sqrt_mult x y hx' hy'

end R_sqrt
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace DiscrR

theorem IZR_eq :
    ∀ (ctx : ExactRealContext), IZR_eqStatement ctx := by
  intro ctx z1 z2 h
  subst z2
  rfl

end DiscrR
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace Rbasic_fun

theorem Rabs_pos_eq :
    ∀ (ctx : ExactRealContext), Rabs_pos_eqStatement ctx := by
  intro ctx x hx
  change ctx.spec.abs x = x
  change ctx.spec.le (ctx.spec.ofZ Z0) x at hx
  rw [ctx.certificate.sourceLaws.ofZ_zero] at hx
  exact ctx.certificate.sourceLaws.abs_nonnegative x hx

end Rbasic_fun
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace Exp_prop

theorem exp_plus :
    ∀ (ctx : ExactRealContext), exp_plusStatement ctx := by
  intro ctx x y
  change ctx.spec.exp (ctx.spec.add x y) =
    ctx.spec.mul (ctx.spec.exp x) (ctx.spec.exp y)
  exact ctx.certificate.exp.add x y

end Exp_prop
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace R_sqrt

theorem sqrt_lt_1 :
    ∀ (ctx : ExactRealContext), sqrt_lt_1Statement ctx := by
  intro ctx x y hx hy hxy
  change ctx.spec.le (ctx.spec.ofZ Z0) x at hx
  change ctx.spec.le (ctx.spec.ofZ Z0) y at hy
  change ctx.spec.lt x y at hxy
  change ctx.spec.lt (ExactReal.sqrt ctx.spec x)
    (ExactReal.sqrt ctx.spec y)
  rw [ctx.certificate.sourceLaws.ofZ_zero] at hx hy
  have sqrt_eq (z : ctx.spec.carrier) (hz : ctx.spec.le ctx.spec.zero z) :
      ExactReal.sqrt ctx.spec z = ctx.spec.sqrt z := by
    unfold ExactReal.sqrt
    cases hdec : ctx.spec.lt_dec z ctx.spec.zero with
    | left hlt =>
        exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt).2 hz |>.elim
    | right _ => simp [hdec]
  have hrootx := sqrt_eq x hx
  have hrooty := sqrt_eq y hy
  have hxy_le : ctx.spec.le x y :=
    (ctx.certificate.orderedField.lt_iff_le_not_le x y).mp hxy |>.1
  have hle := ctx.certificate.sqrt.monotone x y hx hxy_le
  have hle' : ctx.spec.le (ExactReal.sqrt ctx.spec x)
      (ExactReal.sqrt ctx.spec y) := by
    simpa [hrootx, hrooty] using hle
  apply (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
  refine ⟨hle', ?_⟩
  intro hrev
  have hrev' : ctx.spec.le (ctx.spec.sqrt y) (ctx.spec.sqrt x) := by
    simpa [hrootx, hrooty] using hrev
  have heq : ctx.spec.sqrt x = ctx.spec.sqrt y :=
    ctx.certificate.orderedField.le_antisymm _ _ hle hrev'
  have hsqx := ctx.certificate.sqrt.sqr x hx
  have hsqy := ctx.certificate.sqrt.sqr y hy
  have hxy_eq : x = y := by
    calc
      x = ctx.spec.mul (ctx.spec.sqrt x) (ctx.spec.sqrt x) := hsqx.symm
      _ = ctx.spec.mul (ctx.spec.sqrt y) (ctx.spec.sqrt y) := by rw [heq]
      _ = y := hsqy
  subst y
  exact ctx.certificate.orderedField.lt_irrefl x hxy

end R_sqrt
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Req_ge :
    ∀ (ctx : ExactRealContext), Req_geStatement ctx := by
  intro ctx r1 r2 h
  subst r2
  exact ctx.certificate.orderedField.le_refl r1

theorem Rlt_not_eq :
    ∀ (ctx : ExactRealContext), Rlt_not_eqStatement ctx := by
  intro ctx r1 r2 hlt heq
  subst r2
  exact ctx.certificate.orderedField.lt_irrefl r1 hlt

theorem Rgt_ge :
    ∀ (ctx : ExactRealContext), Rgt_geStatement ctx := by
  intro ctx r1 r2 hgt
  exact (ctx.certificate.orderedField.lt_iff_le_not_le r2 r1).mp hgt |>.1

theorem Rle_ge :
    ∀ (ctx : ExactRealContext), Rle_geStatement ctx := by
  intro ctx r1 r2 hle
  exact hle

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Rge_le : ∀ (ctx : ExactRealContext), Rge_leStatement ctx := by
  intro ctx r1 r2 h
  exact h

theorem Rgt_lt : ∀ (ctx : ExactRealContext), Rgt_ltStatement ctx := by
  intro ctx r1 r2 h
  exact h

theorem Rnot_le_lt : ∀ (ctx : ExactRealContext), Rnot_le_ltStatement ctx := by
  intro ctx r1 r2 hn
  rcases ctx.certificate.total_order r1 r2 with h | h
  · rcases h with hlt | heq
    · exact (hn ((ctx.certificate.orderedField.lt_iff_le_not_le r1 r2).mp hlt).1).elim
    · subst r2
      exact (hn (ctx.certificate.orderedField.le_refl r1)).elim
  · exact (ctx.certificate.orderedField.lt_iff_le_not_le r2 r1).mpr
      ⟨(ctx.certificate.orderedField.lt_iff_le_not_le r2 r1).mp h |>.1, hn⟩

theorem Rnot_lt_le : ∀ (ctx : ExactRealContext), Rnot_lt_leStatement ctx := by
  intro ctx r1 r2 hn
  rcases ctx.certificate.total_order r1 r2 with h | h
  · rcases h with hlt | heq
    · exact (hn hlt).elim
    · subst r2
      exact ctx.certificate.orderedField.le_refl r1
  · exact (ctx.certificate.orderedField.lt_iff_le_not_le r2 r1).mp h |>.1

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Rlt_not_le :
    ∀ (ctx : ExactRealContext), Rlt_not_leStatement ctx := by
  intro ctx r1 r2 hlt hle
  exact ((ctx.certificate.orderedField.lt_iff_le_not_le r2 r1).mp hlt).2 hle

theorem Rle_not_lt :
    ∀ (ctx : ExactRealContext), Rle_not_ltStatement ctx := by
  intro ctx r1 r2 hle hlt
  exact ((ctx.certificate.orderedField.lt_iff_le_not_le r1 r2).mp hlt).2 hle

theorem Rle_antisym :
    ∀ (ctx : ExactRealContext), Rle_antisymStatement ctx := by
  intro ctx r1 r2 h12 h21
  exact ctx.certificate.orderedField.le_antisymm r1 r2 h12 h21

theorem Rle_trans :
    ∀ (ctx : ExactRealContext), Rle_transStatement ctx := by
  intro ctx r1 r2 r3 h12 h23
  exact ctx.certificate.orderedField.le_trans r1 r2 r3 h12 h23

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Rgt_trans :
    ∀ (ctx : ExactRealContext), Rgt_transStatement ctx := by
  intro ctx r1 r2 r3 h12 h23
  exact ctx.certificate.orderedField.lt_trans r3 r2 r1 h23 h12

def Rle_dec :
    ∀ (ctx : ExactRealContext), Rle_decStatement ctx := by
  intro ctx r1 r2
  cases h21 : ctx.spec.lt_dec r2 r1 with
  | left hlt21 =>
      exact .right (by
        intro hle
        exact ((ctx.certificate.orderedField.lt_iff_le_not_le r2 r1).mp hlt21).2 hle)
  | right hn21 =>
      cases h12 : ctx.spec.lt_dec r1 r2 with
      | left hlt12 =>
          exact .left ((ctx.certificate.orderedField.lt_iff_le_not_le r1 r2).mp hlt12 |>.1)
      | right hn12 =>
          exact .left (by
            rcases ctx.certificate.total_order r1 r2 with h | h
            · rcases h with hlt | heq
              · exact (hn12 hlt).elim
              · subst r2
                exact ctx.certificate.orderedField.le_refl r1
            · exact (hn21 h).elim)

def Rlt_le_dec :
    ∀ (ctx : ExactRealContext), Rlt_le_decStatement ctx := by
  intro ctx r1 r2
  cases h12 : ctx.spec.lt_dec r1 r2 with
  | left hlt12 => exact .left hlt12
  | right hn12 =>
      exact .right (by
        rcases ctx.certificate.total_order r1 r2 with h | h
        · rcases h with hlt | heq
          · exact (hn12 hlt).elim
          · subst r2
            exact ctx.certificate.orderedField.le_refl r1
        · exact (ctx.certificate.orderedField.lt_iff_le_not_le r2 r1).mp h |>.1)

def Rle_lt_dec :
    ∀ (ctx : ExactRealContext), Rle_lt_decStatement ctx := by
  intro ctx r1 r2
  cases h21 : ctx.spec.lt_dec r2 r1 with
  | left hlt21 => exact .right hlt21
  | right hn21 =>
      exact .left (by
        rcases ctx.certificate.total_order r1 r2 with h | h
        · rcases h with hlt | heq
          · exact (ctx.certificate.orderedField.lt_iff_le_not_le r1 r2).mp hlt |>.1
          · subst r2
            exact ctx.certificate.orderedField.le_refl r1
        · exact (hn21 h).elim)

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

def Rle_lt_or_eq_dec :
    ∀ (ctx : ExactRealContext), Rle_lt_or_eq_decStatement ctx := by
  intro ctx r1 r2 h12
  cases hdec : ctx.spec.lt_dec r1 r2 with
  | left hlt => exact .left hlt
  | right hnlt =>
      exact .right (by
        rcases ctx.certificate.total_order r1 r2 with h | h
        · rcases h with hlt | heq
          · exact (hnlt hlt).elim
          · exact heq
        · exact (((ctx.certificate.orderedField.lt_iff_le_not_le r2 r1).mp h).2 h12).elim)

theorem Rlt_or_le :
    ∀ (ctx : ExactRealContext), Rlt_or_leStatement ctx := by
  intro ctx r1 r2
  rcases ctx.certificate.total_order r1 r2 with h | h
  · rcases h with hlt | heq
    · exact Or.inl hlt
    · subst r2
      exact Or.inr (ctx.certificate.orderedField.le_refl r1)
  · exact Or.inr ((ctx.certificate.orderedField.lt_iff_le_not_le r2 r1).mp h).1

theorem Rle_or_lt :
    ∀ (ctx : ExactRealContext), Rle_or_ltStatement ctx := by
  intro ctx r1 r2
  rcases ctx.certificate.total_order r1 r2 with h | h
  · rcases h with hlt | heq
    · exact Or.inl ((ctx.certificate.orderedField.lt_iff_le_not_le r1 r2).mp hlt).1
    · subst r2
      exact Or.inl (ctx.certificate.orderedField.le_refl r1)
  · exact Or.inr h

theorem Rplus_opp_l :
    ∀ (ctx : ExactRealContext), Rplus_opp_lStatement ctx := by
  intro ctx r
  change ctx.spec.add (ctx.spec.neg r) r = ctx.spec.ofZ
    (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0)
  rw [ctx.certificate.sourceLaws.ofZ_zero]
  exact ctx.certificate.orderedField.neg_add_cancel r

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Rplus_opp_r_uniq :
    ∀ (ctx : ExactRealContext), Rplus_opp_r_uniqStatement ctx := by
  intro ctx r1 r2 h
  change ctx.spec.add r1 r2 = ctx.spec.ofZ Z0 at h
  have h' : ctx.spec.add (ctx.spec.neg r1) (ctx.spec.add r1 r2) =
      ctx.spec.add (ctx.spec.neg r1) (ctx.spec.ofZ Z0) :=
    congrArg (fun x => ctx.spec.add (ctx.spec.neg r1) x) h
  calc
    r2 = ctx.spec.add ctx.spec.zero r2 :=
      (ctx.certificate.orderedField.zero_add r2).symm
    _ = ctx.spec.add (ctx.spec.add (ctx.spec.neg r1) r1) r2 := by
      rw [ctx.certificate.orderedField.neg_add_cancel]
    _ = ctx.spec.add (ctx.spec.neg r1) (ctx.spec.add r1 r2) := by
      rw [ctx.certificate.orderedField.add_assoc]
    _ = ctx.spec.add (ctx.spec.neg r1) (ctx.spec.ofZ Z0) := h'
    _ = ctx.spec.neg r1 := by
      rw [ctx.certificate.sourceLaws.ofZ_zero,
        ctx.certificate.orderedField.add_zero]

theorem Rplus_eq_reg_l :
    ∀ (ctx : ExactRealContext), Rplus_eq_reg_lStatement ctx := by
  intro ctx r r1 r2 h
  change ctx.spec.add r r1 = ctx.spec.add r r2 at h
  have h' : ctx.spec.add (ctx.spec.neg r) (ctx.spec.add r r1) =
      ctx.spec.add (ctx.spec.neg r) (ctx.spec.add r r2) :=
    congrArg (fun x => ctx.spec.add (ctx.spec.neg r) x) h
  calc
    r1 = ctx.spec.add ctx.spec.zero r1 :=
      (ctx.certificate.orderedField.zero_add r1).symm
    _ = ctx.spec.add (ctx.spec.add (ctx.spec.neg r) r) r1 := by
      rw [ctx.certificate.orderedField.neg_add_cancel]
    _ = ctx.spec.add (ctx.spec.neg r) (ctx.spec.add r r1) := by
      rw [ctx.certificate.orderedField.add_assoc]
    _ = ctx.spec.add (ctx.spec.neg r) (ctx.spec.add r r2) := h'
    _ = ctx.spec.add (ctx.spec.add (ctx.spec.neg r) r) r2 := by
      rw [ctx.certificate.orderedField.add_assoc]
    _ = ctx.spec.add ctx.spec.zero r2 := by
      rw [ctx.certificate.orderedField.neg_add_cancel]
    _ = r2 := ctx.certificate.orderedField.zero_add r2

theorem Ropp_0 :
    ∀ (ctx : ExactRealContext), Ropp_0Statement ctx := by
  intro ctx
  change ctx.spec.neg (ctx.spec.ofZ Z0) = ctx.spec.ofZ Z0
  rw [ctx.certificate.sourceLaws.ofZ_zero]
  calc
    ctx.spec.neg ctx.spec.zero =
        ctx.spec.add (ctx.spec.neg ctx.spec.zero) ctx.spec.zero :=
      (ctx.certificate.orderedField.add_zero _).symm
    _ = ctx.spec.zero := ctx.certificate.orderedField.neg_add_cancel _

theorem Ropp_involutive :
    ∀ (ctx : ExactRealContext), Ropp_involutiveStatement ctx := by
  intro ctx r
  change ctx.spec.neg (ctx.spec.neg r) = r
  have h : ctx.spec.add (ctx.spec.neg r) r = ctx.spec.ofZ Z0 := by
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact ctx.certificate.orderedField.neg_add_cancel r
  exact (Rplus_opp_r_uniq ctx (ctx.spec.neg r) r h).symm

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Rmult_eq_compat_l :
    ∀ (ctx : ExactRealContext), Rmult_eq_compat_lStatement ctx := by
  intro ctx r r1 r2 h
  change ctx.spec.mul r r1 = ctx.spec.mul r r2
  exact congrArg (fun x => ctx.spec.mul r x) h

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Rmult_eq_reg_r :
    ∀ (ctx : ExactRealContext), Rmult_eq_reg_rStatement ctx := by
  intro ctx r r1 r2 hmul hr
  change ctx.spec.mul r1 r = ctx.spec.mul r2 r at hmul
  have hrne : r ≠ ctx.spec.zero := by
    intro hz
    apply hr
    calc
      r = ctx.spec.zero := hz
      _ = ctx.spec.ofZ Z0 := ctx.certificate.sourceLaws.ofZ_zero.symm
  have hmul' :
      ctx.spec.mul (ctx.spec.inv r) (ctx.spec.mul r1 r) =
        ctx.spec.mul (ctx.spec.inv r) (ctx.spec.mul r2 r) :=
    congrArg (fun x => ctx.spec.mul (ctx.spec.inv r) x) hmul
  calc
    r1 = ctx.spec.mul ctx.spec.one r1 :=
      (ctx.certificate.orderedField.one_mul r1).symm
    _ = ctx.spec.mul (ctx.spec.mul (ctx.spec.inv r) r) r1 := by
      rw [ctx.certificate.orderedField.inv_mul_cancel r hrne]
    _ = ctx.spec.mul (ctx.spec.inv r) (ctx.spec.mul r r1) := by
      rw [ctx.certificate.orderedField.mul_assoc]
    _ = ctx.spec.mul (ctx.spec.inv r) (ctx.spec.mul r1 r) := by
      rw [ctx.certificate.orderedField.mul_comm r r1]
    _ = ctx.spec.mul (ctx.spec.inv r) (ctx.spec.mul r2 r) := hmul'
    _ = ctx.spec.mul (ctx.spec.inv r) (ctx.spec.mul r r2) := by
      rw [ctx.certificate.orderedField.mul_comm r2 r]
    _ = ctx.spec.mul (ctx.spec.mul (ctx.spec.inv r) r) r2 := by
      rw [ctx.certificate.orderedField.mul_assoc]
    _ = ctx.spec.mul ctx.spec.one r2 := by
      rw [ctx.certificate.orderedField.inv_mul_cancel r hrne]
    _ = r2 := ctx.certificate.orderedField.one_mul r2

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Rmult_0_r (ctx : ExactRealContext) :
    Rmult_0_rStatement ctx := by
  intro r
  change ctx.spec.mul r (ctx.spec.ofZ Z0) = ctx.spec.ofZ Z0
  rw [ctx.certificate.sourceLaws.ofZ_zero]
  exact ctx.certificate.orderedField.mul_zero r

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Rmult_eq_0_compat_r (ctx : ExactRealContext) :
    Rmult_eq_0_compat_rStatement ctx := by
  intro r1 r2 h
  change ctx.spec.mul r1 r2 = ctx.spec.ofZ Z0
  rw [h]
  change ctx.spec.mul (ctx.spec.ofZ Z0) r2 = ctx.spec.ofZ Z0
  rw [ctx.certificate.sourceLaws.ofZ_zero]
  exact ctx.certificate.orderedField.zero_mul r2

private theorem exact_mul_neg_right_suffix (ctx : ExactRealContext)
    (x y : ctx.spec.carrier) :
    ctx.spec.mul x (ctx.spec.neg y) = ctx.spec.neg (ctx.spec.mul x y) := by
  have h : ctx.spec.add (ctx.spec.mul x (ctx.spec.neg y)) (ctx.spec.mul x y) =
      ctx.spec.zero := by
    rw [← ctx.certificate.orderedField.left_distrib,
      ctx.certificate.orderedField.neg_add_cancel,
      ctx.certificate.orderedField.mul_zero]
  symm
  calc
    ctx.spec.neg (ctx.spec.mul x y) =
        ctx.spec.add (ctx.spec.neg (ctx.spec.mul x y)) ctx.spec.zero :=
      (ctx.certificate.orderedField.add_zero _).symm
    _ = ctx.spec.add (ctx.spec.neg (ctx.spec.mul x y))
        (ctx.spec.add (ctx.spec.mul x (ctx.spec.neg y)) (ctx.spec.mul x y)) := by
          rw [h]
    _ = ctx.spec.add (ctx.spec.neg (ctx.spec.mul x y))
        (ctx.spec.add (ctx.spec.mul x y) (ctx.spec.mul x (ctx.spec.neg y))) := by
          rw [ctx.certificate.orderedField.add_comm
            (ctx.spec.mul x (ctx.spec.neg y))]
    _ = ctx.spec.add
        (ctx.spec.add (ctx.spec.neg (ctx.spec.mul x y)) (ctx.spec.mul x y))
        (ctx.spec.mul x (ctx.spec.neg y)) := by
          rw [ctx.certificate.orderedField.add_assoc]
    _ = ctx.spec.add ctx.spec.zero (ctx.spec.mul x (ctx.spec.neg y)) := by
          rw [ctx.certificate.orderedField.neg_add_cancel]
    _ = ctx.spec.mul x (ctx.spec.neg y) :=
      ctx.certificate.orderedField.zero_add _

theorem Rmult_integral (ctx : ExactRealContext) :
    Rmult_integralStatement ctx := by
  intro r1 r2 h
  change ctx.spec.mul r1 r2 = ctx.spec.ofZ Z0 at h
  by_cases h1 : r1 = ctx.spec.ofZ Z0
  · exact Or.inl h1
  · right
    have h1' : r1 ≠ ctx.spec.zero := by
      intro hz
      apply h1
      calc
        r1 = ctx.spec.zero := hz
        _ = ctx.spec.ofZ Z0 := ctx.certificate.sourceLaws.ofZ_zero.symm
    have hmul := congrArg (fun x => ctx.spec.mul (ctx.spec.inv r1) x) h
    calc
      r2 = ctx.spec.mul ctx.spec.one r2 :=
        (ctx.certificate.orderedField.one_mul r2).symm
      _ = ctx.spec.mul (ctx.spec.mul (ctx.spec.inv r1) r1) r2 := by
        rw [ctx.certificate.orderedField.inv_mul_cancel r1 h1']
      _ = ctx.spec.mul (ctx.spec.inv r1) (ctx.spec.mul r1 r2) := by
        rw [ctx.certificate.orderedField.mul_assoc]
      _ = ctx.spec.mul (ctx.spec.inv r1) (ctx.spec.ofZ Z0) := hmul
      _ = ctx.spec.mul (ctx.spec.inv r1) ctx.spec.zero := by
        rw [ctx.certificate.sourceLaws.ofZ_zero]
      _ = ctx.spec.zero := ctx.certificate.orderedField.mul_zero _
      _ = ctx.spec.ofZ Z0 := ctx.certificate.sourceLaws.ofZ_zero.symm

theorem Rmult_integral_contrapositive_currified (ctx : ExactRealContext) :
    Rmult_integral_contrapositive_currifiedStatement ctx := by
  intro r1 r2 h1 h2 hmul
  change ctx.spec.mul r1 r2 = ctx.spec.ofZ Z0 at hmul
  rcases Rmult_integral ctx r1 r2 hmul with hzero | hzero
  · exact h1 hzero
  · exact h2 hzero

theorem Ropp_mult_distr_l_reverse (ctx : ExactRealContext) :
    Ropp_mult_distr_l_reverseStatement ctx := by
  intro r1 r2
  change ctx.spec.mul (ctx.spec.neg r1) r2 =
    ctx.spec.neg (ctx.spec.mul r1 r2)
  calc
    ctx.spec.mul (ctx.spec.neg r1) r2 =
        ctx.spec.mul r2 (ctx.spec.neg r1) :=
      ctx.certificate.orderedField.mul_comm _ _
    _ = ctx.spec.neg (ctx.spec.mul r2 r1) := by
      exact exact_mul_neg_right_suffix ctx r2 r1
    _ = ctx.spec.neg (ctx.spec.mul r1 r2) := by
      rw [ctx.certificate.orderedField.mul_comm r2 r1]

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

private theorem exact_neg_add_suffix (ctx : ExactRealContext)
    (x y : ctx.spec.carrier) :
    ctx.spec.neg (ctx.spec.add x y) =
      ctx.spec.add (ctx.spec.neg x) (ctx.spec.neg y) := by
  have hzero :
      ctx.spec.add (ctx.spec.add x y)
          (ctx.spec.add (ctx.spec.neg x) (ctx.spec.neg y)) =
        ctx.spec.ofZ Z0 := by
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    calc
      ctx.spec.add (ctx.spec.add x y)
          (ctx.spec.add (ctx.spec.neg x) (ctx.spec.neg y)) =
          ctx.spec.add x
            (ctx.spec.add y (ctx.spec.add (ctx.spec.neg x) (ctx.spec.neg y))) :=
              ctx.certificate.orderedField.add_assoc x y _
      _ = ctx.spec.add x
            (ctx.spec.add (ctx.spec.add y (ctx.spec.neg x)) (ctx.spec.neg y)) := by
              exact congrArg (fun z => ctx.spec.add x z)
                (ctx.certificate.orderedField.add_assoc y
                  (ctx.spec.neg x) (ctx.spec.neg y)).symm
      _ = ctx.spec.add x
            (ctx.spec.add (ctx.spec.add (ctx.spec.neg x) y) (ctx.spec.neg y)) := by
              exact congrArg (fun z => ctx.spec.add x
                (ctx.spec.add z (ctx.spec.neg y)))
                (ctx.certificate.orderedField.add_comm y (ctx.spec.neg x))
      _ = ctx.spec.add x
            (ctx.spec.add (ctx.spec.neg x)
              (ctx.spec.add y (ctx.spec.neg y))) := by
              exact congrArg (fun z => ctx.spec.add x z)
                (ctx.certificate.orderedField.add_assoc
                  (ctx.spec.neg x) y (ctx.spec.neg y))
      _ = ctx.spec.add
            (ctx.spec.add x (ctx.spec.neg x))
              (ctx.spec.add y (ctx.spec.neg y)) := by
              exact (ctx.certificate.orderedField.add_assoc x
                (ctx.spec.neg x) (ctx.spec.add y (ctx.spec.neg y))).symm
      _ = ctx.spec.add
            (ctx.spec.add (ctx.spec.neg x) x)
              (ctx.spec.add (ctx.spec.neg y) y) := by
              rw [ctx.certificate.orderedField.add_comm x (ctx.spec.neg x),
                ctx.certificate.orderedField.add_comm y (ctx.spec.neg y)]
      _ = ctx.spec.add ctx.spec.zero ctx.spec.zero := by
              rw [ctx.certificate.orderedField.neg_add_cancel,
                ctx.certificate.orderedField.neg_add_cancel]
      _ = ctx.spec.zero := ctx.certificate.orderedField.zero_add _
  exact (Rplus_opp_r_uniq ctx
    (ctx.spec.add x y)
    (ctx.spec.add (ctx.spec.neg x) (ctx.spec.neg y)) hzero).symm

theorem Rmult_opp_opp :
    ∀ (ctx : ExactRealContext), Rmult_opp_oppStatement ctx := by
  intro ctx r1 r2
  change ctx.spec.mul (ctx.spec.neg r1) (ctx.spec.neg r2) =
    ctx.spec.mul r1 r2
  calc
    ctx.spec.mul (ctx.spec.neg r1) (ctx.spec.neg r2) =
        ctx.spec.neg (ctx.spec.mul (ctx.spec.neg r1) r2) := by
      exact exact_mul_neg_right_suffix ctx (ctx.spec.neg r1) r2
    _ = ctx.spec.neg (ctx.spec.neg (ctx.spec.mul r1 r2)) := by
      exact congrArg ctx.spec.neg (Ropp_mult_distr_l_reverse ctx r1 r2)
    _ = ctx.spec.mul r1 r2 := by
      exact Ropp_involutive ctx (ctx.spec.mul r1 r2)

theorem Ropp_mult_distr_r_reverse :
    ∀ (ctx : ExactRealContext), Ropp_mult_distr_r_reverseStatement ctx := by
  intro ctx r1 r2
  change ctx.spec.mul r1 (ctx.spec.neg r2) =
    ctx.spec.neg (ctx.spec.mul r1 r2)
  exact exact_mul_neg_right_suffix ctx r1 r2

theorem Ropp_minus_distr :
    ∀ (ctx : ExactRealContext), Ropp_minus_distrStatement ctx := by
  intro ctx r1 r2
  change ctx.spec.neg (ctx.spec.add r1 (ctx.spec.neg r2)) =
    ctx.spec.add r2 (ctx.spec.neg r1)
  rw [exact_neg_add_suffix ctx r1 (ctx.spec.neg r2)]
  have hinv := Ropp_involutive ctx r2
  change ctx.spec.neg (ctx.spec.neg r2) = r2 at hinv
  rw [hinv]
  exact ctx.certificate.orderedField.add_comm _ _

theorem Rmult_minus_distr_r :
    ∀ (ctx : ExactRealContext), Rmult_minus_distr_rStatement ctx := by
  intro ctx r1 r2 r3
  change ctx.spec.mul (ctx.spec.add r2 (ctx.spec.neg r3)) r1 =
    ctx.spec.add (ctx.spec.mul r2 r1)
      (ctx.spec.neg (ctx.spec.mul r3 r1))
  calc
    ctx.spec.mul (ctx.spec.add r2 (ctx.spec.neg r3)) r1 =
        ctx.spec.mul r1 (ctx.spec.add r2 (ctx.spec.neg r3)) := by
      rw [ctx.certificate.orderedField.mul_comm]
    _ = ctx.spec.add (ctx.spec.mul r1 r2)
        (ctx.spec.mul r1 (ctx.spec.neg r3)) :=
      ctx.certificate.orderedField.left_distrib r1 r2 (ctx.spec.neg r3)
    _ = ctx.spec.add (ctx.spec.mul r2 r1)
        (ctx.spec.mul r1 (ctx.spec.neg r3)) := by
      rw [ctx.certificate.orderedField.mul_comm r1 r2]
    _ = ctx.spec.add (ctx.spec.mul r2 r1)
        (ctx.spec.neg (ctx.spec.mul r1 r3)) := by
      rw [exact_mul_neg_right_suffix ctx r1 r3]
    _ = ctx.spec.add (ctx.spec.mul r2 r1)
        (ctx.spec.neg (ctx.spec.mul r3 r1)) := by
      rw [ctx.certificate.orderedField.mul_comm r1 r3]

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Rinv_1 :
    ∀ (ctx : ExactRealContext), Rinv_1Statement ctx := by
  intro ctx
  change ctx.spec.inv (ctx.spec.ofZ
    (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH)) =
    ctx.spec.ofZ
      (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH)
  rw [ctx.certificate.sourceLaws.ofZ_one]
  have hone_ne_zero : ctx.spec.one ≠ ctx.spec.zero := by
    intro h
    exact ctx.certificate.orderedField.zero_ne_one h.symm
  calc
    ctx.spec.inv ctx.spec.one =
        ctx.spec.mul (ctx.spec.inv ctx.spec.one) ctx.spec.one :=
      (ctx.certificate.orderedField.mul_one _).symm
    _ = ctx.spec.one :=
      ctx.certificate.orderedField.inv_mul_cancel ctx.spec.one hone_ne_zero

theorem Rinv_neq_0_compat :
    ∀ (ctx : ExactRealContext), Rinv_neq_0_compatStatement ctx := by
  intro ctx r hr hzero
  change ctx.spec.inv r = ctx.spec.ofZ
    (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0) at hzero
  have hrne : r ≠ ctx.spec.zero := by
    intro heq
    apply hr
    calc
      r = ctx.spec.zero := heq
      _ = ctx.spec.ofZ
          (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0) :=
        ctx.certificate.sourceLaws.ofZ_zero.symm
  have hmul := ctx.certificate.orderedField.inv_mul_cancel r hrne
  rw [hzero, ctx.certificate.sourceLaws.ofZ_zero,
    ctx.certificate.orderedField.zero_mul] at hmul
  exact ctx.certificate.orderedField.zero_ne_one hmul

theorem Rplus_lt_compat_r :
    ∀ (ctx : ExactRealContext), Rplus_lt_compat_rStatement ctx := by
  intro ctx r r1 r2 h
  change ctx.spec.lt (ctx.spec.add r1 r) (ctx.spec.add r2 r)
  rw [ctx.certificate.orderedField.add_comm r1 r,
    ctx.certificate.orderedField.add_comm r2 r]
  exact ctx.certificate.orderedField.add_lt_compat_l r r1 r2 h

theorem Rplus_le_compat_r :
    ∀ (ctx : ExactRealContext), Rplus_le_compat_rStatement ctx := by
  intro ctx r r1 r2 h
  change ctx.spec.le (ctx.spec.add r1 r) (ctx.spec.add r2 r)
  rw [ctx.certificate.orderedField.add_comm r1 r,
    ctx.certificate.orderedField.add_comm r2 r]
  exact Rplus_le_compat_l ctx r r1 r2 h

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Rplus_lt_compat :
    ∀ (ctx : ExactRealContext), Rplus_lt_compatStatement ctx := by
  intro ctx r1 r2 r3 r4 h12 h34
  change ctx.spec.lt (ctx.spec.add r1 r3) (ctx.spec.add r2 r4)
  have h34' : ctx.spec.lt (ctx.spec.add r1 r3) (ctx.spec.add r1 r4) :=
    ctx.certificate.orderedField.add_lt_compat_l r1 r3 r4 h34
  have h12' : ctx.spec.lt (ctx.spec.add r1 r4) (ctx.spec.add r2 r4) := by
    rw [ctx.certificate.orderedField.add_comm r1 r4,
      ctx.certificate.orderedField.add_comm r2 r4]
    exact ctx.certificate.orderedField.add_lt_compat_l r4 r1 r2 h12
  exact ctx.certificate.orderedField.lt_trans _ _ _ h34' h12'

theorem Rplus_le_compat :
    ∀ (ctx : ExactRealContext), Rplus_le_compatStatement ctx := by
  intro ctx r1 r2 r3 r4 h12 h34
  change ctx.spec.le (ctx.spec.add r1 r3) (ctx.spec.add r2 r4)
  have h34' : ctx.spec.le (ctx.spec.add r1 r3) (ctx.spec.add r1 r4) :=
    Rplus_le_compat_l ctx r1 r3 r4 h34
  have h12' : ctx.spec.le (ctx.spec.add r1 r4) (ctx.spec.add r2 r4) := by
    rw [ctx.certificate.orderedField.add_comm r1 r4,
      ctx.certificate.orderedField.add_comm r2 r4]
    exact Rplus_le_compat_l ctx r4 r1 r2 h12
  exact ctx.certificate.orderedField.le_trans _ _ _ h34' h12'

theorem Rplus_le_reg_r :
    ∀ (ctx : ExactRealContext), Rplus_le_reg_rStatement ctx := by
  intro ctx r r1 r2 h
  change ctx.spec.le (ctx.spec.add r1 r) (ctx.spec.add r2 r) at h
  have h' :
      ctx.spec.le
        (ctx.spec.add (ctx.spec.neg r) (ctx.spec.add r1 r))
        (ctx.spec.add (ctx.spec.neg r) (ctx.spec.add r2 r)) :=
    Rplus_le_compat_l ctx (ctx.spec.neg r) (ctx.spec.add r1 r)
      (ctx.spec.add r2 r) h
  have hleft :
      ctx.spec.add (ctx.spec.neg r) (ctx.spec.add r1 r) = r1 := by
    calc
      ctx.spec.add (ctx.spec.neg r) (ctx.spec.add r1 r) =
          ctx.spec.add (ctx.spec.add (ctx.spec.neg r) r) r1 := by
            rw [ctx.certificate.orderedField.add_comm r1 r,
              ← ctx.certificate.orderedField.add_assoc]
      _ = ctx.spec.add ctx.spec.zero r1 := by
            rw [ctx.certificate.orderedField.neg_add_cancel]
      _ = r1 := ctx.certificate.orderedField.zero_add _
  have hright :
      ctx.spec.add (ctx.spec.neg r) (ctx.spec.add r2 r) = r2 := by
    calc
      ctx.spec.add (ctx.spec.neg r) (ctx.spec.add r2 r) =
          ctx.spec.add (ctx.spec.add (ctx.spec.neg r) r) r2 := by
            rw [ctx.certificate.orderedField.add_comm r2 r,
              ← ctx.certificate.orderedField.add_assoc]
      _ = ctx.spec.add ctx.spec.zero r2 := by
            rw [ctx.certificate.orderedField.neg_add_cancel]
      _ = r2 := ctx.certificate.orderedField.zero_add _
  rw [hleft, hright] at h'
  exact h'

theorem Ropp_lt_contravar :
    ∀ (ctx : ExactRealContext), Ropp_lt_contravarStatement ctx := by
  intro ctx r1 r2 h
  change ctx.spec.lt (ctx.spec.neg r1) (ctx.spec.neg r2)
  apply Rplus_lt_reg_r ctx (ctx.spec.add r1 r2)
      (ctx.spec.neg r1) (ctx.spec.neg r2)
  have hleft :
      ctx.spec.add (ctx.spec.neg r1) (ctx.spec.add r1 r2) = r2 := by
    calc
      ctx.spec.add (ctx.spec.neg r1) (ctx.spec.add r1 r2) =
          ctx.spec.add (ctx.spec.add (ctx.spec.neg r1) r1) r2 := by
            rw [← ctx.certificate.orderedField.add_assoc]
      _ = ctx.spec.add ctx.spec.zero r2 := by
            rw [ctx.certificate.orderedField.neg_add_cancel]
      _ = r2 := ctx.certificate.orderedField.zero_add _
  have hright :
      ctx.spec.add (ctx.spec.neg r2) (ctx.spec.add r1 r2) = r1 := by
    calc
      ctx.spec.add (ctx.spec.neg r2) (ctx.spec.add r1 r2) =
          ctx.spec.add (ctx.spec.neg r2) (ctx.spec.add r2 r1) := by
            rw [ctx.certificate.orderedField.add_comm r1 r2]
      _ = ctx.spec.add (ctx.spec.add (ctx.spec.neg r2) r2) r1 := by
            rw [← ctx.certificate.orderedField.add_assoc]
      _ = ctx.spec.add ctx.spec.zero r1 := by
            rw [ctx.certificate.orderedField.neg_add_cancel]
      _ = r1 := ctx.certificate.orderedField.zero_add _
  change ctx.spec.lt
    (ctx.spec.add (ctx.spec.neg r1) (ctx.spec.add r1 r2))
    (ctx.spec.add (ctx.spec.neg r2) (ctx.spec.add r1 r2))
  rw [hleft, hright]
  exact h

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Ropp_le_contravar :
    ∀ (ctx : ExactRealContext), Ropp_le_contravarStatement ctx := by
  intro ctx r1 r2 h
  change ctx.spec.le r2 r1 at h
  change ctx.spec.le (ctx.spec.neg r1) (ctx.spec.neg r2)
  rcases ctx.certificate.total_order (ctx.spec.neg r1) (ctx.spec.neg r2) with h' | h'
  · rcases h' with hlt | heq
    · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt |>.1
    · rw [heq]
      exact ctx.certificate.orderedField.le_refl _
  · have hlt : ctx.spec.lt r1 r2 := by
      have hneg := Ropp_lt_contravar ctx (ctx.spec.neg r1) (ctx.spec.neg r2) h'
      have hri1 : ctx.spec.neg (ctx.spec.neg r1) = r1 := by
        change ctx.spec.neg (ctx.spec.neg r1) = r1
        exact Ropp_involutive ctx r1
      have hri2 : ctx.spec.neg (ctx.spec.neg r2) = r2 := by
        change ctx.spec.neg (ctx.spec.neg r2) = r2
        exact Ropp_involutive ctx r2
      change ctx.spec.lt
        (ctx.spec.neg (ctx.spec.neg r1))
        (ctx.spec.neg (ctx.spec.neg r2)) at hneg
      rw [hri1, hri2] at hneg
      exact hneg
    exact (((ctx.certificate.orderedField.lt_iff_le_not_le r1 r2).mp hlt).2 h).elim

theorem Ropp_lt_cancel :
    ∀ (ctx : ExactRealContext), Ropp_lt_cancelStatement ctx := by
  intro ctx r1 r2 h
  change ctx.spec.lt (ctx.spec.neg r2) (ctx.spec.neg r1) at h
  have h' := Ropp_lt_contravar ctx (ctx.spec.neg r1) (ctx.spec.neg r2) h
  have hri1 : ctx.spec.neg (ctx.spec.neg r1) = r1 := by
    change ctx.spec.neg (ctx.spec.neg r1) = r1
    exact Ropp_involutive ctx r1
  have hri2 : ctx.spec.neg (ctx.spec.neg r2) = r2 := by
    change ctx.spec.neg (ctx.spec.neg r2) = r2
    exact Ropp_involutive ctx r2
  change ctx.spec.lt
    (ctx.spec.neg (ctx.spec.neg r1))
    (ctx.spec.neg (ctx.spec.neg r2)) at h'
  rw [hri1, hri2] at h'
  exact h'

theorem Ropp_0_gt_lt_contravar :
    ∀ (ctx : ExactRealContext), Ropp_0_gt_lt_contravarStatement ctx := by
  intro ctx r h
  change ctx.spec.lt r (ctx.spec.ofZ Z0) at h
  change ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.neg r)
  have h' := Ropp_lt_contravar ctx (ctx.spec.ofZ Z0) r h
  have hzero : ctx.spec.neg (ctx.spec.ofZ Z0) = ctx.spec.ofZ Z0 := by
    change ctx.spec.neg (ctx.spec.ofZ Z0) = ctx.spec.ofZ Z0
    exact Ropp_0 ctx
  change ctx.spec.lt
    (ctx.spec.neg (ctx.spec.ofZ Z0)) (ctx.spec.neg r) at h'
  rw [hzero] at h'
  exact h'

theorem Ropp_lt_gt_0_contravar :
    ∀ (ctx : ExactRealContext), Ropp_lt_gt_0_contravarStatement ctx := by
  intro ctx r h
  change ctx.spec.lt (ctx.spec.ofZ Z0) r at h
  change ctx.spec.lt (ctx.spec.neg r) (ctx.spec.ofZ Z0)
  have h' := Ropp_lt_contravar ctx r (ctx.spec.ofZ Z0) h
  have hzero : ctx.spec.neg (ctx.spec.ofZ Z0) = ctx.spec.ofZ Z0 := by
    change ctx.spec.neg (ctx.spec.ofZ Z0) = ctx.spec.ofZ Z0
    exact Ropp_0 ctx
  change ctx.spec.lt
    (ctx.spec.neg r) (ctx.spec.neg (ctx.spec.ofZ Z0)) at h'
  rw [hzero] at h'
  exact h'

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Ropp_le_cancel :
    ∀ (ctx : ExactRealContext), Ropp_le_cancelStatement ctx := by
  intro ctx r1 r2 h
  change ctx.spec.le (ctx.spec.neg r2) (ctx.spec.neg r1) at h
  have h' := Ropp_le_contravar ctx (ctx.spec.neg r1) (ctx.spec.neg r2) h
  change ctx.spec.le
    (ctx.spec.neg (ctx.spec.neg r1))
    (ctx.spec.neg (ctx.spec.neg r2)) at h'
  have hri1 : ctx.spec.neg (ctx.spec.neg r1) = r1 := by
    change ctx.spec.neg (ctx.spec.neg r1) = r1
    exact Ropp_involutive ctx r1
  have hri2 : ctx.spec.neg (ctx.spec.neg r2) = r2 := by
    change ctx.spec.neg (ctx.spec.neg r2) = r2
    exact Ropp_involutive ctx r2
  rw [hri1, hri2] at h'
  exact h'

theorem Rmult_le_compat_l :
    ∀ (ctx : ExactRealContext), Rmult_le_compat_lStatement ctx := by
  intro ctx r r1 r2 hr h12
  have h := Rmult_le_compat_r ctx r r1 r2 hr h12
  change ctx.spec.le (ctx.spec.mul r1 r) (ctx.spec.mul r2 r) at h
  change ctx.spec.le (ctx.spec.mul r r1) (ctx.spec.mul r r2)
  rw [ctx.certificate.orderedField.mul_comm r r1,
    ctx.certificate.orderedField.mul_comm r r2]
  exact h

theorem Rmult_le_compat :
    ∀ (ctx : ExactRealContext), Rmult_le_compatStatement ctx := by
  intro ctx r1 r2 r3 r4 h1 h3 h12 h34
  change ctx.spec.le (ctx.spec.ofZ Z0) r1 at h1
  change ctx.spec.le (ctx.spec.ofZ Z0) r3 at h3
  have h1' : ctx.spec.le ctx.spec.zero r1 := by
    rw [← ctx.certificate.sourceLaws.ofZ_zero]
    exact h1
  have h3' : ctx.spec.le ctx.spec.zero r3 := by
    rw [← ctx.certificate.sourceLaws.ofZ_zero]
    exact h3
  have h2 : ctx.spec.le ctx.spec.zero r2 :=
    ctx.certificate.orderedField.le_trans _ r1 r2 h1' h12
  have h2z : ctx.spec.le (ctx.spec.ofZ Z0) r2 := by
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact h2
  have hleft := Rmult_le_compat_r ctx r3 r1 r2 h3 h12
  have hright := Rmult_le_compat_l ctx r2 r3 r4 h2z h34
  change ctx.spec.le (ctx.spec.mul r1 r3) (ctx.spec.mul r2 r3) at hleft
  change ctx.spec.le (ctx.spec.mul r2 r3) (ctx.spec.mul r2 r4) at hright
  change ctx.spec.le (ctx.spec.mul r1 r3) (ctx.spec.mul r2 r4)
  exact ctx.certificate.orderedField.le_trans _ _ _ hleft hright

theorem Rmult_ge_0_gt_0_lt_compat :
    ∀ (ctx : ExactRealContext), Rmult_ge_0_gt_0_lt_compatStatement ctx := by
  intro ctx r1 r2 r3 r4 h3 h2 h12 h34
  change ctx.spec.le (ctx.spec.ofZ Z0) r3 at h3
  change ctx.spec.lt (ctx.spec.ofZ Z0) r2 at h2
  have h3' : ctx.spec.le ctx.spec.zero r3 := by
    rw [← ctx.certificate.sourceLaws.ofZ_zero]
    exact h3
  have h2' : ctx.spec.lt ctx.spec.zero r2 := by
    rw [← ctx.certificate.sourceLaws.ofZ_zero]
    exact h2
  have h12le : ctx.spec.le r1 r2 :=
    (ctx.certificate.orderedField.lt_iff_le_not_le r1 r2).mp h12 |>.1
  have hleft := Rmult_le_compat_r ctx r3 r1 r2 h3 h12le
  have hright : ctx.spec.lt (ctx.spec.mul r2 r3) (ctx.spec.mul r2 r4) :=
    ctx.certificate.orderedField.mul_lt_compat_l r2 r3 r4 h2' h34
  change ctx.spec.le (ctx.spec.mul r1 r3) (ctx.spec.mul r2 r3) at hleft
  change ctx.spec.lt (ctx.spec.mul r1 r3) (ctx.spec.mul r2 r4)
  exact Rle_lt_trans ctx _ _ _ hleft hright

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Rlt_0_1 :
    ∀ (ctx : ExactRealContext), Rlt_0_1Statement ctx := by
  intro ctx
  change ctx.spec.lt (ctx.spec.ofZ Z0)
    (ctx.spec.ofZ (Zpos xH))
  rw [ctx.certificate.sourceLaws.ofZ_zero,
    ctx.certificate.sourceLaws.ofZ_one]
  exact exact_zero_lt_one ctx

theorem Rle_0_1 :
    ∀ (ctx : ExactRealContext), Rle_0_1Statement ctx := by
  intro ctx
  change ctx.spec.le (ctx.spec.ofZ Z0)
    (ctx.spec.ofZ (Zpos xH))
  rw [ctx.certificate.sourceLaws.ofZ_zero,
    ctx.certificate.sourceLaws.ofZ_one]
  exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
    (exact_zero_lt_one ctx) |>.1

theorem Rmult_lt_reg_l :
    ∀ (ctx : ExactRealContext), Rmult_lt_reg_lStatement ctx := by
  intro ctx r r1 r2 hr h
  change ctx.spec.lt (ctx.spec.ofZ Z0) r at hr
  change ctx.spec.lt (ctx.spec.mul r r1) (ctx.spec.mul r r2) at h
  have hr' : ctx.spec.lt ctx.spec.zero r := by
    rw [← ctx.certificate.sourceLaws.ofZ_zero]
    exact hr
  exact flocqReal_Rmult_lt_reg_l ctx r r1 r2 hr' h

theorem Rmult_le_reg_r :
    ∀ (ctx : ExactRealContext), Rmult_le_reg_rStatement ctx := by
  intro ctx r r1 r2 hr h
  change ctx.spec.lt (ctx.spec.ofZ Z0) r at hr
  change ctx.spec.le (ctx.spec.mul r1 r) (ctx.spec.mul r2 r) at h
  rcases ctx.certificate.total_order r1 r2 with h12 | h21
  · rcases h12 with hlt | heq
    · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt |>.1
    · rw [heq]
      exact ctx.certificate.orderedField.le_refl _
  · have hprod : ctx.spec.lt (ctx.spec.mul r2 r) (ctx.spec.mul r1 r) :=
      Rmult_lt_compat_r ctx r r2 r1 hr h21
    exact False.elim ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
      hprod |>.2 h)

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Rle_minus :
    ∀ (ctx : ExactRealContext), Rle_minusStatement ctx := by
  intro ctx r1 r2 h
  change ctx.spec.le
    (ctx.spec.add r1 (ctx.spec.neg r2)) (ctx.spec.ofZ Z0)
  have h' := Rplus_le_compat_l ctx (ctx.spec.neg r2) r1 r2 h
  change ctx.spec.le
    (ctx.spec.add (ctx.spec.neg r2) r1)
    (ctx.spec.add (ctx.spec.neg r2) r2) at h'
  rw [ctx.certificate.orderedField.add_comm (ctx.spec.neg r2) r1,
    ctx.certificate.orderedField.neg_add_cancel] at h'
  rw [ctx.certificate.sourceLaws.ofZ_zero]
  exact h'

theorem Rge_minus :
    ∀ (ctx : ExactRealContext), Rge_minusStatement ctx := by
  intro ctx r1 r2 h
  change ctx.spec.le (ctx.spec.ofZ Z0)
    (ctx.spec.add r1 (ctx.spec.neg r2))
  have h' := Rplus_le_compat_l ctx (ctx.spec.neg r2) r2 r1 h
  change ctx.spec.le
    (ctx.spec.add (ctx.spec.neg r2) r2)
    (ctx.spec.add (ctx.spec.neg r2) r1) at h'
  rw [ctx.certificate.orderedField.neg_add_cancel,
    ctx.certificate.orderedField.add_comm (ctx.spec.neg r2) r1] at h'
  rw [ctx.certificate.sourceLaws.ofZ_zero]
  exact h'

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

private theorem flocqReal_Rinv_0_lt_contravar
    (ctx : ExactRealContext)
    (r1 r2 : ctx.spec.carrier)
    (hr1 : ctx.spec.lt ctx.spec.zero r1)
    (h12 : ctx.spec.lt r1 r2) :
    ctx.spec.lt (ctx.spec.inv r2) (ctx.spec.inv r1) := by
  have hr2 : ctx.spec.lt ctx.spec.zero r2 :=
    ctx.certificate.orderedField.lt_trans _ _ _ hr1 h12
  have hr1ne : r1 ≠ ctx.spec.zero := by
    intro hz
    subst r1
    exact ctx.certificate.orderedField.lt_irrefl _ hr1
  have hr2ne : r2 ≠ ctx.spec.zero := by
    intro hz
    subst r2
    exact ctx.certificate.orderedField.lt_irrefl _ hr2
  have hr1src : ctx.spec.lt (ctx.spec.ofZ Z0) r1 := by
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hr1
  have hr2src : ctx.spec.lt (ctx.spec.ofZ Z0) r2 := by
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hr2
  have hinv1src : ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.inv r1) :=
    Rinv_0_lt_compat ctx r1 hr1src
  have hinv1 : ctx.spec.lt ctx.spec.zero (ctx.spec.inv r1) := by
    rw [← ctx.certificate.sourceLaws.ofZ_zero]
    exact hinv1src
  have hmul : ctx.spec.lt
      (ctx.spec.mul (ctx.spec.inv r1) r1)
      (ctx.spec.mul (ctx.spec.inv r1) r2) :=
    ctx.certificate.orderedField.mul_lt_compat_l
      (ctx.spec.inv r1) r1 r2 hinv1 h12
  have hmul' : ctx.spec.lt
      (ctx.spec.mul r1 (ctx.spec.inv r1))
      (ctx.spec.mul r2 (ctx.spec.inv r1)) := by
    rw [ctx.certificate.orderedField.mul_comm r1 (ctx.spec.inv r1),
      ctx.certificate.orderedField.mul_comm r2 (ctx.spec.inv r1)]
    exact hmul
  have hleft : ctx.spec.mul r1 (ctx.spec.inv r1) = ctx.spec.one := by
    rw [ctx.certificate.orderedField.mul_comm r1 (ctx.spec.inv r1),
      ctx.certificate.orderedField.inv_mul_cancel r1 hr1ne]
  rw [hleft] at hmul'
  have hright : ctx.spec.mul r2 (ctx.spec.inv r2) = ctx.spec.one := by
    rw [ctx.certificate.orderedField.mul_comm r2 (ctx.spec.inv r2),
      ctx.certificate.orderedField.inv_mul_cancel r2 hr2ne]
  have hmul'' : ctx.spec.lt
      (ctx.spec.mul r2 (ctx.spec.inv r2))
      (ctx.spec.mul r2 (ctx.spec.inv r1)) := by
    rw [hright]
    exact hmul'
  exact Rmult_lt_reg_l ctx r2 (ctx.spec.inv r2) (ctx.spec.inv r1)
    hr2src hmul''

theorem Rinv_1_lt_contravar :
    ∀ (ctx : ExactRealContext), Rinv_1_lt_contravarStatement ctx := by
  intro ctx r1 r2 hr1 h12
  change ctx.spec.le (ctx.spec.ofZ
    (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos xH)) r1 at hr1
  change ctx.spec.lt r1 r2 at h12
  change ctx.spec.lt (ctx.spec.inv r2) (ctx.spec.inv r1)
  rw [ctx.certificate.sourceLaws.ofZ_one] at hr1
  have hpos : ctx.spec.lt ctx.spec.zero r1 :=
    Rlt_le_trans ctx ctx.spec.zero ctx.spec.one r1
      (exact_zero_lt_one ctx) hr1
  exact flocqReal_Rinv_0_lt_contravar ctx r1 r2 hpos h12

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

private theorem flocqReal_mul_eq_mul_right_cancel
    (ctx : ExactRealContext)
    (a b r : ctx.spec.carrier)
    (hr : r ≠ ctx.spec.zero)
    (h : ctx.spec.mul a r = ctx.spec.mul b r) :
    a = b := by
  have h' := congrArg (fun x => ctx.spec.mul (ctx.spec.inv r) x) h
  calc
    a = ctx.spec.mul ctx.spec.one a :=
      (ctx.certificate.orderedField.one_mul a).symm
    _ = ctx.spec.mul (ctx.spec.mul (ctx.spec.inv r) r) a := by
      rw [ctx.certificate.orderedField.inv_mul_cancel r hr]
    _ = ctx.spec.mul (ctx.spec.inv r) (ctx.spec.mul r a) := by
      rw [ctx.certificate.orderedField.mul_assoc]
    _ = ctx.spec.mul (ctx.spec.inv r) (ctx.spec.mul a r) := by
      rw [ctx.certificate.orderedField.mul_comm r a]
    _ = ctx.spec.mul (ctx.spec.inv r) (ctx.spec.mul b r) := h'
    _ = ctx.spec.mul (ctx.spec.inv r) (ctx.spec.mul r b) := by
      rw [ctx.certificate.orderedField.mul_comm b r]
    _ = ctx.spec.mul (ctx.spec.mul (ctx.spec.inv r) r) b := by
      rw [ctx.certificate.orderedField.mul_assoc]
    _ = ctx.spec.mul ctx.spec.one b := by
      rw [ctx.certificate.orderedField.inv_mul_cancel r hr]
    _ = b := ctx.certificate.orderedField.one_mul b

private theorem flocqReal_inv_neg
    (ctx : ExactRealContext)
    (r : ctx.spec.carrier)
    (hr : r ≠ ctx.spec.zero) :
    ctx.spec.inv (ctx.spec.neg r) = ctx.spec.neg (ctx.spec.inv r) := by
  have hzero : ctx.spec.neg ctx.spec.zero = ctx.spec.zero := by
    calc
      ctx.spec.neg ctx.spec.zero =
          ctx.spec.add (ctx.spec.neg ctx.spec.zero) ctx.spec.zero :=
        (ctx.certificate.orderedField.add_zero _).symm
      _ = ctx.spec.zero := ctx.certificate.orderedField.neg_add_cancel _
  have hneg : ctx.spec.neg r ≠ ctx.spec.zero := by
    intro hz
    apply hr
    have hz' := congrArg ctx.spec.neg hz
    have hnn : ctx.spec.neg (ctx.spec.neg r) = r := by
      exact Ropp_involutive ctx r
    rw [hnn, hzero] at hz'
    exact hz'
  have hnegmul :
      ctx.spec.mul (ctx.spec.neg (ctx.spec.inv r)) (ctx.spec.neg r) =
        ctx.spec.mul (ctx.spec.inv r) r := by
    exact Rmult_opp_opp ctx (ctx.spec.inv r) r
  apply flocqReal_mul_eq_mul_right_cancel ctx
    (ctx.spec.inv (ctx.spec.neg r)) (ctx.spec.neg (ctx.spec.inv r))
    (ctx.spec.neg r) hneg
  calc
    ctx.spec.mul (ctx.spec.inv (ctx.spec.neg r)) (ctx.spec.neg r) =
        ctx.spec.one := ctx.certificate.orderedField.inv_mul_cancel
          (ctx.spec.neg r) hneg
    _ = ctx.spec.mul (ctx.spec.neg (ctx.spec.inv r)) (ctx.spec.neg r) := by
      rw [hnegmul, ctx.certificate.orderedField.inv_mul_cancel r hr]

theorem Rinv_lt_contravar :
    ∀ (ctx : ExactRealContext), Rinv_lt_contravarStatement ctx := by
  intro ctx r1 r2 hprod h12
  change ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.mul r1 r2) at hprod
  change ctx.spec.lt r1 r2 at h12
  change ctx.spec.lt (ctx.spec.inv r2) (ctx.spec.inv r1)
  rw [ctx.certificate.sourceLaws.ofZ_zero] at hprod
  rcases ctx.certificate.total_order ctx.spec.zero r1 with h1 | h1
  · rcases h1 with hpos1 | hzero1
    · have hpos2 : ctx.spec.lt ctx.spec.zero r2 :=
        ctx.certificate.orderedField.lt_trans _ _ _ hpos1 h12
      have hpos1src : ctx.spec.lt (ctx.spec.ofZ Z0) r1 := by
        rw [ctx.certificate.sourceLaws.ofZ_zero]
        exact hpos1
      exact flocqReal_Rinv_0_lt_contravar ctx r1 r2 hpos1 h12
    · subst r1
      rw [ctx.certificate.orderedField.zero_mul] at hprod
      exact (ctx.certificate.orderedField.lt_irrefl _ hprod).elim
  · rcases ctx.certificate.total_order ctx.spec.zero r2 with h2 | h2
    · rcases h2 with hpos2 | hzero2
      · have hnegprod : ctx.spec.lt
            (ctx.spec.mul r1 r2) ctx.spec.zero := by
          have hmul := ctx.certificate.orderedField.mul_lt_compat_l
            r2 r1 ctx.spec.zero hpos2 h1
          rw [ctx.certificate.orderedField.mul_zero] at hmul
          rw [ctx.certificate.orderedField.mul_comm r1 r2]
          exact hmul
        exact (ctx.certificate.orderedField.lt_irrefl _
          (ctx.certificate.orderedField.lt_trans _ _ _ hprod hnegprod)).elim
      · subst r2
        rw [ctx.certificate.orderedField.mul_zero] at hprod
        exact (ctx.certificate.orderedField.lt_irrefl _ hprod).elim
    · have hpos_neg1src : ctx.spec.lt (ctx.spec.ofZ Z0)
          (ctx.spec.neg r1) :=
        Ropp_0_gt_lt_contravar ctx r1 (by
          change ctx.spec.lt r1 (ctx.spec.ofZ Z0)
          rw [ctx.certificate.sourceLaws.ofZ_zero]
          exact h1)
      have hpos_neg2src : ctx.spec.lt (ctx.spec.ofZ Z0)
          (ctx.spec.neg r2) :=
        Ropp_0_gt_lt_contravar ctx r2 (by
          change ctx.spec.lt r2 (ctx.spec.ofZ Z0)
          rw [ctx.certificate.sourceLaws.ofZ_zero]
          exact h2)
      have hpos_neg1 : ctx.spec.lt ctx.spec.zero (ctx.spec.neg r1) := by
        rw [← ctx.certificate.sourceLaws.ofZ_zero]
        exact hpos_neg1src
      have hpos_neg2 : ctx.spec.lt ctx.spec.zero (ctx.spec.neg r2) := by
        rw [← ctx.certificate.sourceLaws.ofZ_zero]
        exact hpos_neg2src
      have hneg12src := Ropp_lt_contravar ctx r2 r1 h12
      change ctx.spec.lt (ctx.spec.neg r2) (ctx.spec.neg r1) at hneg12src
      have hinvneg := flocqReal_Rinv_0_lt_contravar ctx
        (ctx.spec.neg r2) (ctx.spec.neg r1) hpos_neg2 hneg12src
      have hr1ne : r1 ≠ ctx.spec.zero := by
        intro hz
        subst r1
        exact ctx.certificate.orderedField.lt_irrefl _ h1
      have hr2ne : r2 ≠ ctx.spec.zero := by
        intro hz
        subst r2
        exact ctx.certificate.orderedField.lt_irrefl _ h2
      rw [flocqReal_inv_neg ctx r1 hr1ne,
        flocqReal_inv_neg ctx r2 hr2ne] at hinvneg
      exact Ropp_lt_cancel ctx (ctx.spec.inv r2) (ctx.spec.inv r1) hinvneg

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

private theorem flocqReal_zero_lt_one (ctx : ExactRealContext) :
    ctx.spec.lt ctx.spec.zero ctx.spec.one := by
  have hz : ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ (ctx.spec.up ctx.spec.zero)) := by
    simpa [ExactReal.R0] using ctx.certificate.sourceLaws.up_gt ctx.spec.zero
  have hg := ctx.certificate.sourceLaws.up_gap ctx.spec.zero
  have hneg0 : ctx.spec.neg ctx.spec.zero = ctx.spec.zero := by
    calc
      ctx.spec.neg ctx.spec.zero =
          ctx.spec.add (ctx.spec.neg ctx.spec.zero) ctx.spec.zero :=
        (ctx.certificate.orderedField.add_zero _).symm
      _ = ctx.spec.zero := ctx.certificate.orderedField.neg_add_cancel _
  have hz0 : ctx.spec.add (ctx.spec.ofZ (ctx.spec.up ctx.spec.zero))
      (ctx.spec.neg ctx.spec.zero) = ctx.spec.ofZ (ctx.spec.up ctx.spec.zero) := by
    rw [hneg0, ctx.certificate.orderedField.add_zero]
  have hg' : ctx.spec.le (ctx.spec.ofZ (ctx.spec.up ctx.spec.zero)) ctx.spec.one := by
    rw [← hz0, ← ctx.certificate.sourceLaws.ofZ_one]
    exact hg
  apply (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
  constructor
  · have hzle := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hz
    exact ctx.certificate.orderedField.le_trans _ _ _ hzle.1 hg'
  · intro h10
    have hzle := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hz
    exact hzle.2 (ctx.certificate.orderedField.le_trans _ _ _ hg' h10)

theorem Rlt_0_2 :
    ∀ (ctx : ExactRealContext), Rlt_0_2Statement ctx := by
  intro ctx
  change ctx.spec.lt (ctx.spec.ofZ Z0)
    (ctx.spec.ofZ (Zpos (xO xH)))
  have hZ : Z.add (Zpos xH) (Zpos xH) = Zpos (xO xH) := by
    apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add]
    rw [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change (1 : Int) + 1 = Int.ofNat
      (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (xO xH))
    simp [Numbers.Rocq.Coq.posToNat]
  rw [ctx.certificate.sourceLaws.ofZ_zero, ← hZ,
    ctx.certificate.sourceLaws.ofZ_add,
    ctx.certificate.sourceLaws.ofZ_one]
  have h01 := flocqReal_zero_lt_one ctx
  have h11 := ctx.certificate.orderedField.add_lt_compat_l
    ctx.spec.one ctx.spec.zero ctx.spec.one h01
  rw [ctx.certificate.orderedField.add_zero] at h11
  exact ctx.certificate.orderedField.lt_trans _ _ _ h01 h11

private theorem flocqReal_zof_nat_succ (n : Nat) :
    Z.of_nat (Nat.succ n) = Z.add (Z.of_nat n) (Zpos xH) := by
  apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat (Nat.succ n))) =
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat n)) +
          _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos xH)))
  simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change Int.ofNat (Nat.succ n) =
    Int.ofNat n + _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos xH)
  simp [Numbers.Rocq.Coq.intOfZ, Numbers.Rocq.Coq.posToNat]

theorem S_INR :
    ∀ (ctx : ExactRealContext), S_INRStatement ctx := by
  intro ctx n
  change ctx.spec.ofZ (Z.of_nat (Nat.succ n)) =
    ctx.spec.add (ctx.spec.ofZ (Z.of_nat n))
      (ctx.spec.ofZ (Zpos xH))
  rw [flocqReal_zof_nat_succ]
  exact ctx.certificate.sourceLaws.ofZ_add _ _

private theorem flocqReal_zof_nat_zero : Z.of_nat 0 = Z0 := by
  rfl

theorem lt_0_INR :
    ∀ (ctx : ExactRealContext), lt_0_INRStatement ctx := by
  intro ctx n
  induction n with
  | zero =>
      intro hn
      change 0 < 0 at hn
      exact (Nat.lt_irrefl 0 hn).elim
  | succ n ih =>
      intro hn
      change ctx.spec.lt (ctx.spec.ofZ Z0)
        (ctx.spec.ofZ (Z.of_nat (Nat.succ n)))
      rw [flocqReal_zof_nat_succ,
        ctx.certificate.sourceLaws.ofZ_add,
        ctx.certificate.sourceLaws.ofZ_zero,
        ctx.certificate.sourceLaws.ofZ_one]
      by_cases hnzero : n = 0
      · subst n
        rw [flocqReal_zof_nat_zero,
          ctx.certificate.sourceLaws.ofZ_zero,
          ctx.certificate.orderedField.zero_add]
        exact flocqReal_zero_lt_one ctx
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero
        have hin := ih hnpos
        have hin' : ctx.spec.lt ctx.spec.zero
            (ctx.spec.ofZ (Z.of_nat n)) := by
          rw [← ctx.certificate.sourceLaws.ofZ_zero]
          exact hin
        have hstep := ctx.certificate.orderedField.add_lt_compat_l
          (ctx.spec.ofZ (Z.of_nat n)) ctx.spec.zero ctx.spec.one
          (flocqReal_zero_lt_one ctx)
        rw [ctx.certificate.orderedField.add_zero] at hstep
        exact ctx.certificate.orderedField.lt_trans _ _ _ hin' hstep

theorem lt_INR :
    ∀ (ctx : ExactRealContext), lt_INRStatement ctx := by
  intro ctx n
  induction n with
  | zero =>
      intro m hnm
      exact lt_0_INR ctx m hnm
  | succ n ih =>
      intro m hnm
      cases m with
      | zero =>
          exfalso
          change Nat.succ n < 0 at hnm
          omega
      | succ m =>
          have hnm' : n < m := Nat.succ_lt_succ_iff.mp hnm
          have hin := ih m hnm'
          change ctx.spec.lt (ctx.spec.ofZ (Z.of_nat (Nat.succ n)))
            (ctx.spec.ofZ (Z.of_nat (Nat.succ m)))
          rw [flocqReal_zof_nat_succ, flocqReal_zof_nat_succ,
            ctx.certificate.sourceLaws.ofZ_add,
            ctx.certificate.sourceLaws.ofZ_add,
            ctx.certificate.sourceLaws.ofZ_one]
          have hres := Rplus_lt_compat_r ctx (ctx.spec.ofZ (Zpos xH))
            (ctx.spec.ofZ (Z.of_nat n))
            (ctx.spec.ofZ (Z.of_nat m)) hin
          rw [ctx.certificate.sourceLaws.ofZ_one] at hres
          change ctx.spec.lt
            (ctx.spec.add (ctx.spec.ofZ (Z.of_nat n)) ctx.spec.one)
            (ctx.spec.add (ctx.spec.ofZ (Z.of_nat m)) ctx.spec.one) at hres
          exact hres

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem INR_lt :
    ∀ (ctx : ExactRealContext), INR_ltStatement ctx := by
  intro ctx n m hnm
  rcases Nat.lt_trichotomy n m with hlt | heq | hgt
  · exact hlt
  · subst m
    exact (ctx.certificate.orderedField.lt_irrefl _ hnm).elim
  · have hmn := lt_INR ctx m n hgt
    exact (ctx.certificate.orderedField.lt_irrefl _
      (ctx.certificate.orderedField.lt_trans _ _ _ hnm hmn)).elim

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem le_INR :
    ∀ (ctx : ExactRealContext), le_INRStatement ctx := by
  intro ctx n m hnm
  rcases Nat.lt_or_eq_of_le hnm with hlt | heq
  · have hlt' := lt_INR ctx n m hlt
    exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt' |>.1
  · subst m
    exact ctx.certificate.orderedField.le_refl _

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem INR_IZR_INZ :
    ∀ (ctx : ExactRealContext), INR_IZR_INZStatement ctx := by
  intro ctx n
  rfl

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem opp_IZR :
    ∀ (ctx : ExactRealContext), opp_IZRStatement ctx := by
  intro ctx n
  exact ctx.certificate.sourceLaws.ofZ_neg n

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

private theorem flocqReal_zsub_eq_add_opp (n m : Z) :
    Z.sub n m = Z.add n (Z.opp m) := by
  apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

theorem minus_IZR :
    ∀ (ctx : ExactRealContext), minus_IZRStatement ctx := by
  intro ctx n m
  change ctx.spec.ofZ (Z.sub n m) =
    ctx.spec.add (ctx.spec.ofZ n) (ctx.spec.neg (ctx.spec.ofZ m))
  rw [flocqReal_zsub_eq_add_opp,
    ctx.certificate.sourceLaws.ofZ_add,
    ctx.certificate.sourceLaws.ofZ_neg]

theorem lt_IZR :
    ∀ (ctx : ExactRealContext), lt_IZRStatement ctx := by
  intro ctx n m h
  change ctx.spec.lt (ctx.spec.ofZ n) (ctx.spec.ofZ m) at h
  change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n <
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m
  by_cases hnm :
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n <
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m
  · exact hnm
  · by_cases hmn :
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m <
          _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n
    · have hmn' := IZR_lt ctx m n hmn
      exact (ctx.certificate.orderedField.lt_irrefl _
        (ctx.certificate.orderedField.lt_trans _ _ _ h hmn')).elim
    · have heq :
          _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n =
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m :=
        Int.le_antisymm (Int.le_of_not_gt hmn) (Int.le_of_not_gt hnm)
      have hnm' : n = m :=
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective heq
      subst m
      exact (ctx.certificate.orderedField.lt_irrefl _ h).elim

theorem eq_IZR :
    ∀ (ctx : ExactRealContext), eq_IZRStatement ctx := by
  intro ctx n m h
  change ctx.spec.ofZ n = ctx.spec.ofZ m at h
  by_cases hnm :
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n <
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m
  · have hlt := IZR_lt ctx n m hnm
    change ctx.spec.lt (ctx.spec.ofZ n) (ctx.spec.ofZ m) at hlt
    rw [h] at hlt
    exact (ctx.certificate.orderedField.lt_irrefl _ hlt).elim
  · by_cases hmn :
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m <
          _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n
    · have hlt := IZR_lt ctx m n hmn
      change ctx.spec.lt (ctx.spec.ofZ m) (ctx.spec.ofZ n) at hlt
      rw [h] at hlt
      exact (ctx.certificate.orderedField.lt_irrefl _ hlt).elim
    · have heq :
          _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n =
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m :=
        Int.le_antisymm (Int.le_of_not_gt hmn) (Int.le_of_not_gt hnm)
      exact _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective heq

theorem le_IZR :
    ∀ (ctx : ExactRealContext), le_IZRStatement ctx := by
  intro ctx n m h
  change ctx.spec.le (ctx.spec.ofZ n) (ctx.spec.ofZ m) at h
  change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n ≤
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m
  by_cases hnm :
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n ≤
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m
  · exact hnm
  · have hmn :
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m <
          _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n :=
      Int.lt_of_not_ge hnm
    have hlt := IZR_lt ctx m n hmn
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt).2 h |>.elim

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem IZR_neq_proof :
    ∀ (ctx : ExactRealContext) (z1 z2 : Z) (h : z1 ≠ z2),
      IZR_neq ctx z1 z2 h := by
  intro ctx z1 z2 h heq
  exact h (eq_IZR ctx z1 z2 heq)

theorem Rinv_involutive_proof :
    ∀ (ctx : ExactRealContext) (r : ctx.spec.carrier)
      (_h : ¬r = ExactReal.IZR ctx.spec Z0),
      Rinv_involutive ctx r _h := by
  intro ctx r h
  have hrne : r ≠ ctx.spec.zero := by
    intro hz
    apply h
    calc
      r = ctx.spec.zero := hz
      _ = ExactReal.IZR ctx.spec Z0 :=
        ctx.certificate.sourceLaws.ofZ_zero.symm
  have hinvr : ctx.spec.inv r ≠ ctx.spec.zero := by
    intro hz
    have hinvr_src := Rinv_neq_0_compat ctx r h
    apply hinvr_src
    calc
      ctx.spec.inv r = ctx.spec.zero := hz
      _ = ExactReal.IZR ctx.spec Z0 :=
        ctx.certificate.sourceLaws.ofZ_zero.symm
  have hinvr_src : ¬(ctx.spec.inv r = ExactReal.IZR ctx.spec Z0) :=
    Rinv_neq_0_compat ctx r h
  apply Rmult_eq_reg_r ctx (ctx.spec.inv r)
    (ctx.spec.inv (ctx.spec.inv r)) r
  · have hleft := Raxioms.Rinv_l ctx (ctx.spec.inv r) (by
      intro hz
      exact hinvr_src hz)
    have hright := Raxioms.Rinv_l ctx r h
    have hleft' : ctx.spec.mul (ctx.spec.inv (ctx.spec.inv r))
        (ctx.spec.inv r) = ctx.spec.one := by
      simpa [ExactReal.Rmult, ExactReal.Rinv, ExactReal.IZR,
        ctx.certificate.sourceLaws.ofZ_one] using hleft
    have hright' : ctx.spec.mul r (ctx.spec.inv r) = ctx.spec.one := by
      calc
        ctx.spec.mul r (ctx.spec.inv r) =
            ctx.spec.mul (ctx.spec.inv r) r :=
          ctx.certificate.orderedField.mul_comm r (ctx.spec.inv r)
        _ = ctx.spec.one := by
          simpa [ExactReal.Rmult, ExactReal.Rinv, ExactReal.IZR,
            ctx.certificate.sourceLaws.ofZ_one] using hright
    change ctx.spec.mul (ctx.spec.inv (ctx.spec.inv r)) (ctx.spec.inv r) =
      ctx.spec.mul r (ctx.spec.inv r)
    rw [hleft', hright']
  · exact hinvr_src

theorem Ropp_inv_permute_proof :
    ∀ (ctx : ExactRealContext) (r : ctx.spec.carrier)
      (_h : ¬r = ExactReal.IZR ctx.spec Z0),
      Ropp_inv_permute ctx r _h := by
  intro ctx r h
  have hrne : r ≠ ctx.spec.zero := by
    intro hz
    apply h
    calc
      r = ctx.spec.zero := hz
      _ = ExactReal.IZR ctx.spec Z0 :=
        ctx.certificate.sourceLaws.ofZ_zero.symm
  change ctx.spec.neg (ctx.spec.inv r) =
    ctx.spec.inv (ctx.spec.neg r)
  exact (flocqReal_inv_neg ctx r hrne).symm

theorem Rle_Rinv_proof :
    ∀ (ctx : ExactRealContext) (x y : ctx.spec.carrier)
      (_hx : ExactReal.Rlt ctx.spec (ExactReal.IZR ctx.spec Z0) x)
      (_hy : ExactReal.Rlt ctx.spec (ExactReal.IZR ctx.spec Z0) y)
      (_hxy : ExactReal.Rle ctx.spec x y),
      Rle_Rinv ctx x y _hx _hy _hxy := by
  intro ctx x y hx hy hxy
  change ctx.spec.lt (ctx.spec.ofZ Z0) x at hx
  change ctx.spec.lt (ctx.spec.ofZ Z0) y at hy
  change ctx.spec.le x y at hxy
  change ctx.spec.le (ctx.spec.inv y) (ctx.spec.inv x)
  rcases ctx.certificate.total_order x y with h | h
  · rcases h with hlt | heq
    · have hprod : ctx.spec.lt (ctx.spec.ofZ Z0)
          (ctx.spec.mul x y) := Rmult_lt_0_compat ctx x y hx hy
      have hinv := Rinv_lt_contravar ctx x y hprod hlt
      change ctx.spec.lt (ctx.spec.inv y) (ctx.spec.inv x) at hinv
      exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hinv |>.1
    · subst y
      exact ctx.certificate.orderedField.le_refl _
  · have hcontra : ¬ctx.spec.lt y x := by
      intro hyx
      exact (ctx.certificate.orderedField.lt_iff_le_not_le y x).mp hyx |>.2 hxy
    exact (hcontra h).elim

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals

namespace R_sqr

theorem Rsqr_mult :
    ∀ (ctx : ExactRealContext), Rsqr_multStatement ctx := by
  intro ctx x y
  change ctx.spec.mul (ctx.spec.mul x y) (ctx.spec.mul x y) =
    ctx.spec.mul (ctx.spec.mul x x) (ctx.spec.mul y y)
  calc
    ctx.spec.mul (ctx.spec.mul x y) (ctx.spec.mul x y) =
        ctx.spec.mul x (ctx.spec.mul y (ctx.spec.mul x y)) := by
          rw [ctx.certificate.orderedField.mul_assoc]
    _ = ctx.spec.mul x (ctx.spec.mul (ctx.spec.mul y x) y) := by
          rw [ctx.certificate.orderedField.mul_assoc]
    _ = ctx.spec.mul x (ctx.spec.mul (ctx.spec.mul x y) y) := by
          rw [ctx.certificate.orderedField.mul_comm y x]
    _ = ctx.spec.mul x (ctx.spec.mul x (ctx.spec.mul y y)) := by
          rw [ctx.certificate.orderedField.mul_assoc]
    _ = ctx.spec.mul (ctx.spec.mul x x) (ctx.spec.mul y y) := by
          rw [ctx.certificate.orderedField.mul_assoc]

private theorem sqr_lt_of_lt (ctx : ExactRealContext)
    (y x : ctx.spec.carrier)
    (hy : ctx.spec.le (ctx.spec.ofZ Z0) y)
    (hyx : ctx.spec.lt y x) :
    ctx.spec.lt (ctx.spec.mul y y) (ctx.spec.mul x x) := by
  have hy0 : ctx.spec.le ctx.spec.zero y := by
    rw [← ctx.certificate.sourceLaws.ofZ_zero]
    exact hy
  have hyx_le : ctx.spec.le y x :=
    (ctx.certificate.orderedField.lt_iff_le_not_le y x).mp hyx |>.1
  have h0x0 : ctx.spec.lt ctx.spec.zero x := by
    apply (ctx.certificate.orderedField.lt_iff_le_not_le
      ctx.spec.zero x).mpr
    constructor
    · exact ctx.certificate.orderedField.le_trans _ _ _ hy0 hyx_le
    · intro hx0
      have hyeq : y = ctx.spec.zero := by
        apply ctx.certificate.orderedField.le_antisymm y ctx.spec.zero
        · exact ctx.certificate.orderedField.le_trans _ _ _ hyx_le hx0
        · exact hy0
      subst y
      have hxeq : x = ctx.spec.zero :=
        ctx.certificate.orderedField.le_antisymm _ _ hx0
          (ctx.certificate.orderedField.le_trans _ _ _ hy0 hyx_le)
      subst x
      exact ctx.certificate.orderedField.lt_irrefl _ hyx
  have h0x : ctx.spec.lt (ctx.spec.ofZ Z0) x := by
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact h0x0
  have hle :=
    _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
      ctx y y x hy hyx_le
  have hlt :=
    _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Raxioms.Rmult_lt_compat_l
      ctx x y x h0x hyx
  change ctx.spec.le (ctx.spec.mul y y) (ctx.spec.mul x y) at hle
  change ctx.spec.lt (ctx.spec.mul x y) (ctx.spec.mul x x) at hlt
  exact _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
    ctx _ _ _ hle hlt

theorem Rsqr_incr_0 :
    ∀ (ctx : ExactRealContext), Rsqr_incr_0Statement ctx := by
  intro ctx x y hxy hx hy
  change ctx.spec.le (ctx.spec.mul x x) (ctx.spec.mul y y) at hxy
  change ctx.spec.le (ctx.spec.ofZ Z0) x at hx
  change ctx.spec.le (ctx.spec.ofZ Z0) y at hy
  rcases ctx.certificate.total_order x y with h | h
  · rcases h with hlt | heq
    · exact (ctx.certificate.orderedField.lt_iff_le_not_le x y).mp hlt |>.1
    · rw [heq]
      exact ctx.certificate.orderedField.le_refl _
  · have hs := sqr_lt_of_lt ctx y x hy h
    exact False.elim (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hs).2 hxy)

theorem Rsqr_incrst_0 :
    ∀ (ctx : ExactRealContext), Rsqr_incrst_0Statement ctx := by
  intro ctx x y hxy hx hy
  change ctx.spec.lt (ctx.spec.mul x x) (ctx.spec.mul y y) at hxy
  change ctx.spec.le (ctx.spec.ofZ Z0) x at hx
  change ctx.spec.le (ctx.spec.ofZ Z0) y at hy
  rcases ctx.certificate.total_order x y with h | h
  · rcases h with hlt | heq
    · exact hlt
    · subst y
      exact (ctx.certificate.orderedField.lt_irrefl _ hxy).elim
  · have hs := sqr_lt_of_lt ctx y x hy h
    exact (ctx.certificate.orderedField.lt_irrefl _
      (ctx.certificate.orderedField.lt_trans _ _ _ hxy hs)).elim

end R_sqr

end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace R_Ifp

theorem tech_up :
    ∀ (ctx : ExactRealContext), tech_upStatement ctx := by
  intro ctx r z hr hz
  change ctx.spec.lt r (ctx.spec.ofZ z) at hr
  change ctx.spec.le (ctx.spec.ofZ z)
    (ctx.spec.add r (ctx.spec.ofZ (Zpos xH))) at hz
  have ofZ_succ (n : Z) :
      ctx.spec.ofZ (Z.add n (Zpos xH)) =
        ctx.spec.add (ctx.spec.ofZ n) (ctx.spec.ofZ (Zpos xH)) :=
    ctx.certificate.sourceLaws.ofZ_add n (Zpos xH)
  have hup_le :
      ctx.spec.le (ctx.spec.ofZ (ctx.spec.up r))
        (ctx.spec.add r (ctx.spec.ofZ (Zpos xH))) := by
    have h := ctx.certificate.sourceLaws.up_gap r
    have h' :=
      _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_le_compat_l
        ctx r (ctx.spec.add (ctx.spec.ofZ (ctx.spec.up r)) (ctx.spec.neg r))
        (ctx.spec.ofZ (Zpos xH)) h
    have hcancel :
        ctx.spec.add r
            (ctx.spec.add (ctx.spec.ofZ (ctx.spec.up r)) (ctx.spec.neg r)) =
          ctx.spec.ofZ (ctx.spec.up r) := by
      calc
        ctx.spec.add r
            (ctx.spec.add (ctx.spec.ofZ (ctx.spec.up r)) (ctx.spec.neg r)) =
            ctx.spec.add (ctx.spec.add r (ctx.spec.ofZ (ctx.spec.up r)))
              (ctx.spec.neg r) := by
                rw [ctx.certificate.orderedField.add_assoc]
        _ = ctx.spec.add (ctx.spec.add (ctx.spec.ofZ (ctx.spec.up r)) r)
              (ctx.spec.neg r) := by
                rw [ctx.certificate.orderedField.add_comm r]
        _ = ctx.spec.add (ctx.spec.ofZ (ctx.spec.up r))
              (ctx.spec.add r (ctx.spec.neg r)) := by
                rw [← ctx.certificate.orderedField.add_assoc]
        _ = ctx.spec.add (ctx.spec.ofZ (ctx.spec.up r)) ctx.spec.zero := by
                rw [show ctx.spec.add r (ctx.spec.neg r) = ctx.spec.zero by
                  rw [ctx.certificate.orderedField.add_comm,
                    ctx.certificate.orderedField.neg_add_cancel]]
        _ = ctx.spec.ofZ (ctx.spec.up r) :=
          ctx.certificate.orderedField.add_zero _
    change ctx.spec.le
      (ctx.spec.add r
        (ctx.spec.add (ctx.spec.ofZ (ctx.spec.up r)) (ctx.spec.neg r)))
      (ctx.spec.add r (ctx.spec.ofZ (Zpos xH))) at h'
    rw [hcancel] at h'
    exact h'
  rcases Int.lt_trichotomy
      (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z)
      (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (ctx.spec.up r)) with
    hzu | heq | huz
  · have hsucc : Z.le (Z.add z (Zpos xH)) (ctx.spec.up r) :=
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zorder.Zlt_le_succ
        z (ctx.spec.up r) hzu
    have hsucc' :=
      _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_le ctx
        (Z.add z (Zpos xH)) (ctx.spec.up r) hsucc
    have hplus :=
      _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Raxioms.Rplus_lt_compat_l
        ctx (ctx.spec.ofZ (Zpos xH)) r (ctx.spec.ofZ z) hr
    change ctx.spec.lt
      (ctx.spec.add (ctx.spec.ofZ (Zpos xH)) r)
      (ctx.spec.add (ctx.spec.ofZ (Zpos xH)) (ctx.spec.ofZ z)) at hplus
    rw [ctx.certificate.orderedField.add_comm _ r,
      ctx.certificate.orderedField.add_comm _ (ctx.spec.ofZ z)] at hplus
    rw [← ofZ_succ] at hplus
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hplus).2
      (ctx.certificate.orderedField.le_trans _ _ _ hsucc' hup_le) |>.elim
  · exact _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective heq
  · have hsucc : Z.le (Z.add (ctx.spec.up r) (Zpos xH)) z :=
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zorder.Zlt_le_succ
        (ctx.spec.up r) z huz
    have hsucc' :=
      _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_le ctx
        (Z.add (ctx.spec.up r) (Zpos xH)) z hsucc
    have hplus :=
      _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Raxioms.Rplus_lt_compat_l
        ctx (ctx.spec.ofZ (Zpos xH)) r (ctx.spec.ofZ (ctx.spec.up r))
        (ctx.certificate.sourceLaws.up_gt r)
    change ctx.spec.lt
      (ctx.spec.add (ctx.spec.ofZ (Zpos xH)) r)
      (ctx.spec.add (ctx.spec.ofZ (Zpos xH)) (ctx.spec.ofZ (ctx.spec.up r))) at hplus
    rw [ctx.certificate.orderedField.add_comm _ r,
      ctx.certificate.orderedField.add_comm _ (ctx.spec.ofZ (ctx.spec.up r))] at hplus
    rw [← ofZ_succ] at hplus
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hplus).2
      (ctx.certificate.orderedField.le_trans _ _ _ hsucc' hz) |>.elim

end R_Ifp
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace R_sqr

private theorem rsqr_abs_nonnegative (ctx : ExactRealContext)
    (x : ctx.spec.carrier) :
    ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.abs x) := by
  rcases ctx.certificate.total_order ctx.spec.zero x with hx | hx
  · have hx0 : ctx.spec.le ctx.spec.zero x := by
      rcases hx with hlt | heq
      · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt |>.1
      · rw [heq]
        exact ctx.certificate.orderedField.le_refl _
    rw [ctx.certificate.sourceLaws.abs_nonnegative x hx0,
      ctx.certificate.sourceLaws.ofZ_zero]
    exact hx0
  · rw [ctx.certificate.sourceLaws.abs_negative x hx]
    have hpos :=
      _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_0_gt_lt_contravar
        ctx x (by
          change ctx.spec.lt x (ctx.spec.ofZ Z0)
          rw [ctx.certificate.sourceLaws.ofZ_zero]
          exact hx)
    exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hpos |>.1

theorem Rsqr_incrst_1 :
    ∀ (ctx : ExactRealContext), Rsqr_incrst_1Statement ctx := by
  intro ctx x y hxy hx _hy
  change ctx.spec.lt (ctx.spec.mul x x) (ctx.spec.mul y y)
  exact sqr_lt_of_lt ctx x y hx hxy

theorem Rsqr_abs :
    ∀ (ctx : ExactRealContext), Rsqr_absStatement ctx := by
  intro ctx x
  change ctx.spec.mul x x =
    ctx.spec.mul (ctx.spec.abs x) (ctx.spec.abs x)
  rcases ctx.certificate.total_order ctx.spec.zero x with hx | hx
  · have hx0 : ctx.spec.le ctx.spec.zero x := by
      rcases hx with hlt | heq
      · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt |>.1
      · rw [heq]
        exact ctx.certificate.orderedField.le_refl _
    rw [ctx.certificate.sourceLaws.abs_nonnegative x hx0]
  · rw [ctx.certificate.sourceLaws.abs_negative x hx]
    exact (_root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_opp_opp
      ctx x x).symm

theorem Rsqr_le_abs_0 :
    ∀ (ctx : ExactRealContext), Rsqr_le_abs_0Statement ctx := by
  intro ctx x y hxy
  have hsquares :
      ctx.spec.le
        (ctx.spec.mul (ctx.spec.abs x) (ctx.spec.abs x))
        (ctx.spec.mul (ctx.spec.abs y) (ctx.spec.abs y)) := by
    change ctx.spec.le (ctx.spec.mul x x) (ctx.spec.mul y y) at hxy
    have hx := Rsqr_abs ctx x
    have hy := Rsqr_abs ctx y
    change ctx.spec.mul x x =
      ctx.spec.mul (ctx.spec.abs x) (ctx.spec.abs x) at hx
    change ctx.spec.mul y y =
      ctx.spec.mul (ctx.spec.abs y) (ctx.spec.abs y) at hy
    rw [← hx, ← hy]
    exact hxy
  exact Rsqr_incr_0 ctx (ctx.spec.abs x) (ctx.spec.abs y) hsquares
    (rsqr_abs_nonnegative ctx x) (rsqr_abs_nonnegative ctx y)

theorem Rsqr_lt_abs_0 :
    ∀ (ctx : ExactRealContext), Rsqr_lt_abs_0Statement ctx := by
  intro ctx x y hxy
  have hsquares :
      ctx.spec.lt
        (ctx.spec.mul (ctx.spec.abs x) (ctx.spec.abs x))
        (ctx.spec.mul (ctx.spec.abs y) (ctx.spec.abs y)) := by
    change ctx.spec.lt (ctx.spec.mul x x) (ctx.spec.mul y y) at hxy
    have hx := Rsqr_abs ctx x
    have hy := Rsqr_abs ctx y
    change ctx.spec.mul x x =
      ctx.spec.mul (ctx.spec.abs x) (ctx.spec.abs x) at hx
    change ctx.spec.mul y y =
      ctx.spec.mul (ctx.spec.abs y) (ctx.spec.abs y) at hy
    rw [← hx, ← hy]
    exact hxy
  exact Rsqr_incrst_0 ctx (ctx.spec.abs x) (ctx.spec.abs y) hsquares
    (rsqr_abs_nonnegative ctx x) (rsqr_abs_nonnegative ctx y)

end R_sqr
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace R_sqr

theorem Rsqr_lt_abs_1 :
    ∀ (ctx : ExactRealContext), Rsqr_lt_abs_1Statement ctx := by
  intro ctx x y hxy
  change ctx.spec.lt (ctx.spec.abs x) (ctx.spec.abs y) at hxy
  have hx : ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.abs x) := by
    exact rsqr_abs_nonnegative ctx x
  have hy : ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.abs y) := by
    exact rsqr_abs_nonnegative ctx y
  have hs := Rsqr_incrst_1 ctx (ctx.spec.abs x) (ctx.spec.abs y) hxy hx hy
  change ctx.spec.lt (ctx.spec.mul x x) (ctx.spec.mul y y)
  have hxs := Rsqr_abs ctx x
  have hys := Rsqr_abs ctx y
  change ctx.spec.mul x x =
    ctx.spec.mul (ctx.spec.abs x) (ctx.spec.abs x) at hxs
  change ctx.spec.mul y y =
    ctx.spec.mul (ctx.spec.abs y) (ctx.spec.abs y) at hys
  rw [hxs, hys]
  exact hs

end R_sqr
end Rocq.Coq.Reals

namespace Rocq.Coq.Reals
namespace R_sqrt

theorem sqrt_lt_R0 :
    ∀ (ctx : ExactRealContext), sqrt_lt_R0Statement ctx := by
  intro ctx x hx
  change ctx.spec.lt (ctx.spec.ofZ Z0) x at hx
  change ctx.spec.lt (ctx.spec.ofZ Z0) (ExactReal.sqrt ctx.spec x)
  rw [ctx.certificate.sourceLaws.ofZ_zero] at hx ⊢
  unfold ExactReal.sqrt
  cases hdec : ctx.spec.lt_dec x ctx.spec.zero with
  | left hlt =>
      exact (ctx.certificate.orderedField.lt_irrefl x
        (ctx.certificate.orderedField.lt_trans x ctx.spec.zero x hlt hx)).elim
  | right _ =>
      simpa [hdec] using ctx.certificate.sourceLaws.sqrt_strict_positive x hx

end R_sqrt
end Rocq.Coq.Reals

namespace Rocq.Coq.Reals
namespace Raxioms

theorem Rplus_comm :
    ∀ (ctx : ExactRealContext), Rplus_commStatement ctx := by
  intro ctx r1 r2
  change ctx.spec.add r1 r2 = ctx.spec.add r2 r1
  exact ctx.certificate.orderedField.add_comm r1 r2

theorem Rplus_assoc :
    ∀ (ctx : ExactRealContext), Rplus_assocStatement ctx := by
  intro ctx r1 r2 r3
  change ctx.spec.add (ctx.spec.add r1 r2) r3 =
    ctx.spec.add r1 (ctx.spec.add r2 r3)
  exact ctx.certificate.orderedField.add_assoc r1 r2 r3

end Raxioms
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace Raxioms

theorem Rplus_opp_r :
    ∀ (ctx : ExactRealContext), Rplus_opp_rStatement ctx := by
  intro ctx r
  change ctx.spec.add r (ctx.spec.neg r) = ctx.spec.ofZ
    (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0)
  rw [ctx.certificate.sourceLaws.ofZ_zero,
    ctx.certificate.orderedField.add_comm]
  exact ctx.certificate.orderedField.neg_add_cancel r

theorem Rplus_0_l :
    ∀ (ctx : ExactRealContext), Rplus_0_lStatement ctx := by
  intro ctx r
  change ctx.spec.add (ctx.spec.ofZ
    (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0)) r = r
  rw [ctx.certificate.sourceLaws.ofZ_zero]
  exact ctx.certificate.orderedField.zero_add r

theorem archimed :
    ∀ (ctx : ExactRealContext), archimedStatement ctx := by
  intro ctx r
  change And
    (ctx.spec.lt r (ctx.spec.ofZ (ctx.spec.up r)))
    (ctx.spec.le
      (ExactReal.Rminus ctx.spec (ctx.spec.ofZ (ctx.spec.up r)) r)
      (ctx.spec.ofZ
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos
          _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH)))
  exact ⟨ctx.certificate.sourceLaws.up_gt r,
    ctx.certificate.sourceLaws.up_gap r⟩

noncomputable def completeness :
    (ctx : ExactRealContext) → completenessStatement ctx := by
  intro ctx E hbound hex
  change (∃ m, (∀ x, E x → ctx.spec.le x m)) at hbound
  change (∃ x, E x) at hex
  let hres := ctx.certificate.sourceLaws.completeness E hbound hex
  exact ⟨Classical.choose hres, Classical.choose_spec hres⟩

end Raxioms
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace Rbasic_fun

theorem Rmin_l :
    ∀ (ctx : ExactRealContext), Rmin_lStatement ctx := by
  intro ctx x y
  change ctx.spec.le (ctx.spec.min x y) x
  exact ctx.certificate.sourceLaws.min_left x y

theorem Rmin_r :
    ∀ (ctx : ExactRealContext), Rmin_rStatement ctx := by
  intro ctx x y
  change ctx.spec.le (ctx.spec.min x y) y
  exact ctx.certificate.sourceLaws.min_right x y

theorem Rmin_comm :
    ∀ (ctx : ExactRealContext), Rmin_commStatement ctx := by
  intro ctx x y
  change ctx.spec.min x y = ctx.spec.min y x
  rcases ctx.certificate.total_order x y with hxy | hyx
  · rcases hxy with hlt | heq
    · have hle : ctx.spec.le x y :=
        (ctx.certificate.orderedField.lt_iff_le_not_le x y).mp hlt |>.1
      rw [ctx.certificate.sourceLaws.min_eq_left x y hle,
        ctx.certificate.sourceLaws.min_eq_right y x hle]
    · subst y
      rfl
  · have hle : ctx.spec.le y x :=
      (ctx.certificate.orderedField.lt_iff_le_not_le y x).mp hyx |>.1
    rw [ctx.certificate.sourceLaws.min_eq_right x y hle,
      ctx.certificate.sourceLaws.min_eq_left y x hle]

def Rcase_abs :
    ∀ (ctx : ExactRealContext), Rcase_absStatement ctx := by
  intro ctx r
  cases hdec : ctx.spec.lt_dec r ctx.spec.zero with
  | left hlt =>
      exact .left (by
        change ctx.spec.lt r (ctx.spec.ofZ Z0)
        rw [ctx.certificate.sourceLaws.ofZ_zero]
        exact hlt)
  | right hnlt =>
      apply Logic.Support.Sumbool.right
      change ctx.spec.le (ctx.spec.ofZ Z0) r
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      rcases ctx.certificate.total_order ctx.spec.zero r with h | h
      · rcases h with hlt | heq
        · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt |>.1
        · subst r
          exact ctx.certificate.orderedField.le_refl _
      · exact (hnlt h).elim

end Rbasic_fun
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace Rbasic_fun

theorem Rabs_R0 :
    ∀ (ctx : ExactRealContext), Rabs_R0Statement ctx := by
  intro ctx
  change ctx.spec.abs (ctx.spec.ofZ Z0) = ctx.spec.ofZ Z0
  rw [ctx.certificate.sourceLaws.ofZ_zero]
  exact ctx.certificate.sourceLaws.abs_nonnegative _
    (ctx.certificate.orderedField.le_refl _)

theorem Rabs_R1 :
    ∀ (ctx : ExactRealContext), Rabs_R1Statement ctx := by
  intro ctx
  change ctx.spec.abs (ctx.spec.ofZ (Zpos xH)) = ctx.spec.ofZ (Zpos xH)
  rw [ctx.certificate.sourceLaws.ofZ_one]
  have h01 : ctx.spec.le ctx.spec.zero ctx.spec.one := by
    have hz : ctx.spec.lt ctx.spec.zero
        (ctx.spec.ofZ (ctx.spec.up ctx.spec.zero)) := by
      simpa [ExactReal.R0] using
        ctx.certificate.sourceLaws.up_gt ctx.spec.zero
    have hg := ctx.certificate.sourceLaws.up_gap ctx.spec.zero
    have hneg0 : ctx.spec.neg ctx.spec.zero = ctx.spec.zero := by
      calc
        ctx.spec.neg ctx.spec.zero =
            ctx.spec.add (ctx.spec.neg ctx.spec.zero) ctx.spec.zero :=
          (ctx.certificate.orderedField.add_zero _).symm
        _ = ctx.spec.zero :=
          ctx.certificate.orderedField.neg_add_cancel _
    have hz0 : ctx.spec.add (ctx.spec.ofZ (ctx.spec.up ctx.spec.zero))
        (ctx.spec.neg ctx.spec.zero) =
        ctx.spec.ofZ (ctx.spec.up ctx.spec.zero) := by
      rw [hneg0, ctx.certificate.orderedField.add_zero]
    have hg' : ctx.spec.le (ctx.spec.ofZ (ctx.spec.up ctx.spec.zero))
        ctx.spec.one := by
      rw [← hz0, ← ctx.certificate.sourceLaws.ofZ_one]
      exact hg
    have h01lt : ctx.spec.lt ctx.spec.zero ctx.spec.one := by
      apply (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
      constructor
      · exact ctx.certificate.orderedField.le_trans _ _ _
          ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hz).1 hg'
      · intro h10
        exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hz).2
          (ctx.certificate.orderedField.le_trans _ _ _ hg' h10)
    exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h01lt |>.1
  exact ctx.certificate.sourceLaws.abs_nonnegative _ h01

theorem Rabs_left :
    ∀ (ctx : ExactRealContext), Rabs_leftStatement ctx := by
  intro ctx r hr
  change ctx.spec.abs r = ctx.spec.neg r
  have hr' : ctx.spec.lt r ctx.spec.zero := by
    rw [← ctx.certificate.sourceLaws.ofZ_zero]
    exact hr
  exact ctx.certificate.sourceLaws.abs_negative r hr'

theorem Rabs_no_R0 :
    ∀ (ctx : ExactRealContext), Rabs_no_R0Statement ctx := by
  intro ctx r hne
  have hzero : ctx.spec.ofZ Z0 = ctx.spec.zero :=
    ctx.certificate.sourceLaws.ofZ_zero
  have hne' : r ≠ ctx.spec.zero := by
    intro hr0
    apply hne
    exact hr0.trans hzero.symm
  have neg_ne_zero : ctx.spec.neg r ≠ ctx.spec.zero := by
    intro hneg
    have hsum := ctx.certificate.orderedField.neg_add_cancel r
    rw [hneg, ctx.certificate.orderedField.zero_add] at hsum
    exact hne' hsum
  intro habs
  rcases ctx.certificate.total_order r ctx.spec.zero with h | h
  · rcases h with hlt | heq
    · have habs' := ctx.certificate.sourceLaws.abs_negative r hlt
      apply neg_ne_zero
      calc
        ctx.spec.neg r = ctx.spec.abs r := habs'.symm
        _ = ctx.spec.ofZ Z0 := habs
        _ = ctx.spec.zero := hzero
    · exact hne' heq
  · have hle : ctx.spec.le ctx.spec.zero r :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1
    have habs' := ctx.certificate.sourceLaws.abs_nonnegative r hle
    apply hne'
    exact habs'.symm.trans (habs.trans hzero)

end Rbasic_fun
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace Rbasic_fun

theorem Rabs_right :
    ∀ (ctx : ExactRealContext), Rabs_rightStatement ctx := by
  intro ctx r hr
  change ctx.spec.abs r = r
  change ctx.spec.le (ctx.spec.ofZ Z0) r at hr
  rw [ctx.certificate.sourceLaws.ofZ_zero] at hr
  exact ctx.certificate.sourceLaws.abs_nonnegative r hr

theorem Rabs_left1 :
    ∀ (ctx : ExactRealContext), Rabs_left1Statement ctx := by
  intro ctx a ha
  change ctx.spec.abs a = ctx.spec.neg a
  change ctx.spec.le a (ctx.spec.ofZ Z0) at ha
  rw [ctx.certificate.sourceLaws.ofZ_zero] at ha
  rcases ctx.certificate.total_order a ctx.spec.zero with h | h
  · rcases h with hlt | heq
    · exact ctx.certificate.sourceLaws.abs_negative a hlt
    · subst a
      calc
        ctx.spec.abs ctx.spec.zero = ctx.spec.zero :=
          ctx.certificate.sourceLaws.abs_nonnegative _
            (ctx.certificate.orderedField.le_refl _)
        _ = ctx.spec.neg ctx.spec.zero := by
          have hz := RIneq.Ropp_0 ctx
          change ctx.spec.neg (ctx.spec.ofZ Z0) = ctx.spec.ofZ Z0 at hz
          rw [ctx.certificate.sourceLaws.ofZ_zero] at hz
          exact hz.symm
  · exact False.elim (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h).2 ha)

theorem Rabs_pos :
    ∀ (ctx : ExactRealContext), Rabs_posStatement ctx := by
  intro ctx x
  change ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.abs x)
  rw [ctx.certificate.sourceLaws.ofZ_zero]
  rcases ctx.certificate.total_order x ctx.spec.zero with h | h
  · rcases h with hlt | heq
    · have hlt' : ctx.spec.lt x (ctx.spec.ofZ Z0) := by
        rw [ctx.certificate.sourceLaws.ofZ_zero]
        exact hlt
      have hneg := RIneq.Ropp_0_gt_lt_contravar ctx x hlt'
      have hneg_le : ctx.spec.le ctx.spec.zero (ctx.spec.neg x) := by
        have hneg_le' :=
          (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hneg |>.1
        change ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.neg x) at hneg_le'
        rw [ctx.certificate.sourceLaws.ofZ_zero] at hneg_le'
        exact hneg_le'
      rw [ctx.certificate.sourceLaws.abs_negative x hlt]
      exact hneg_le
    · subst x
      rw [ctx.certificate.sourceLaws.abs_nonnegative _
        (ctx.certificate.orderedField.le_refl _)]
      exact ctx.certificate.orderedField.le_refl _
  · have hx : ctx.spec.le ctx.spec.zero x :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1
    rw [ctx.certificate.sourceLaws.abs_nonnegative x hx]
    exact hx

theorem Rabs_le :
    ∀ (ctx : ExactRealContext), Rabs_leStatement ctx := by
  intro ctx a b hab
  rcases hab with ⟨hab1, hab2⟩
  change ctx.spec.le (ctx.spec.neg b) a at hab1
  change ctx.spec.le a b at hab2
  rcases ctx.certificate.total_order a ctx.spec.zero with h | h
  · rcases h with hlt | heq
    · change ctx.spec.le (ctx.spec.abs a) b
      rw [ctx.certificate.sourceLaws.abs_negative a hlt]
      have hneg := RIneq.Ropp_le_contravar ctx a (ctx.spec.neg b) hab1
      have hneg' : ctx.spec.le (ctx.spec.neg a) b := by
        change ctx.spec.le (ctx.spec.neg a)
          (ctx.spec.neg (ctx.spec.neg b)) at hneg
        have hri := RIneq.Ropp_involutive ctx b
        change ctx.spec.neg (ctx.spec.neg b) = b at hri
        rw [hri] at hneg
        exact hneg
      exact hneg'
    · subst a
      change ctx.spec.le (ctx.spec.abs ctx.spec.zero) b
      rw [ctx.certificate.sourceLaws.abs_nonnegative _
        (ctx.certificate.orderedField.le_refl _)]
      exact hab2
  · have ha : ctx.spec.le ctx.spec.zero a :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1
    change ctx.spec.le (ctx.spec.abs a) b
    rw [ctx.certificate.sourceLaws.abs_nonnegative a ha]
    exact hab2

end Rbasic_fun
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace Rbasic_fun

theorem Rabs_pos_lt :
    ∀ (ctx : ExactRealContext), Rabs_pos_ltStatement ctx := by
  intro ctx x hne
  change ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.abs x)
  rw [ctx.certificate.sourceLaws.ofZ_zero]
  apply (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
  constructor
  · have hpos := Rabs_pos ctx x
    change ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.abs x) at hpos
    rw [ctx.certificate.sourceLaws.ofZ_zero] at hpos
    exact hpos
  · intro hzero
    have hnonneg : ctx.spec.le ctx.spec.zero (ctx.spec.abs x) := by
      have hpos := Rabs_pos ctx x
      change ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.abs x) at hpos
      rw [ctx.certificate.sourceLaws.ofZ_zero] at hpos
      exact hpos
    have heq : ctx.spec.abs x = ctx.spec.zero :=
      ctx.certificate.orderedField.le_antisymm _ _ hzero hnonneg
    apply (Rabs_no_R0 ctx x hne)
    exact heq.trans ctx.certificate.sourceLaws.ofZ_zero.symm

end Rbasic_fun
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace Rbasic_fun

private theorem exact_abs_neg_suffix (ctx : ExactRealContext)
    (z : ctx.spec.carrier) :
    ctx.spec.abs (ctx.spec.neg z) = ctx.spec.abs z := by
  rcases ctx.certificate.total_order z ctx.spec.zero with hz | hz
  · rcases hz with hzneg | hzero
    · have hpos : ctx.spec.lt ctx.spec.zero (ctx.spec.neg z) :=
        by
          have hzneg' : ctx.spec.lt z (ctx.spec.ofZ Z0) := by
            rw [ctx.certificate.sourceLaws.ofZ_zero]
            exact hzneg
          have hpos' := RIneq.Ropp_0_gt_lt_contravar ctx z hzneg'
          change ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.neg z) at hpos'
          rw [ctx.certificate.sourceLaws.ofZ_zero] at hpos'
          exact hpos'
      have hposle : ctx.spec.le ctx.spec.zero (ctx.spec.neg z) :=
        (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hpos |>.1
      rw [ctx.certificate.sourceLaws.abs_nonnegative _ hposle,
        ctx.certificate.sourceLaws.abs_negative z hzneg]
    · subst z
      have hzero' : ctx.spec.neg ctx.spec.zero = ctx.spec.zero := by
        calc
          ctx.spec.neg ctx.spec.zero = ctx.spec.neg (ctx.spec.ofZ Z0) := by
            rw [ctx.certificate.sourceLaws.ofZ_zero]
          _ = ctx.spec.ofZ Z0 := by
            exact RIneq.Ropp_0 ctx
          _ = ctx.spec.zero := ctx.certificate.sourceLaws.ofZ_zero
      rw [hzero']
  · have hneg : ctx.spec.lt (ctx.spec.neg z) ctx.spec.zero :=
      by
        have hz' : ctx.spec.lt (ctx.spec.ofZ Z0) z := by
          rw [ctx.certificate.sourceLaws.ofZ_zero]
          exact hz
        have hneg' := RIneq.Ropp_lt_gt_0_contravar ctx z hz'
        change ctx.spec.lt (ctx.spec.neg z) (ctx.spec.ofZ Z0) at hneg'
        rw [ctx.certificate.sourceLaws.ofZ_zero] at hneg'
        exact hneg'
    have hzle : ctx.spec.le ctx.spec.zero z :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hz |>.1
    rw [ctx.certificate.sourceLaws.abs_negative _ hneg,
      ctx.certificate.sourceLaws.abs_nonnegative _ hzle]
    exact by
      have hri := RIneq.Ropp_involutive ctx z
      change ctx.spec.neg (ctx.spec.neg z) = z at hri
      exact hri

theorem Rabs_minus_sym :
    ∀ (ctx : ExactRealContext), Rabs_minus_symStatement ctx := by
  intro ctx x y
  change ctx.spec.abs (ctx.spec.add x (ctx.spec.neg y)) =
    ctx.spec.abs (ctx.spec.add y (ctx.spec.neg x))
  have hminus :
      ctx.spec.neg (ctx.spec.add x (ctx.spec.neg y)) =
        ctx.spec.add y (ctx.spec.neg x) :=
    RIneq.Ropp_minus_distr ctx x y
  rw [← hminus, exact_abs_neg_suffix]

end Rbasic_fun
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace Rbasic_fun

theorem Rabs_mult :
    ∀ (ctx : ExactRealContext), Rabs_multStatement ctx := by
  intro ctx x y
  change ctx.spec.abs (ctx.spec.mul x y) =
    ctx.spec.mul (ctx.spec.abs x) (ctx.spec.abs y)
  rcases ctx.certificate.total_order x ctx.spec.zero with hx | hx
  · rcases hx with hxneg | hxzero
    · rcases ctx.certificate.total_order y ctx.spec.zero with hy | hy
      · rcases hy with hyneg | hyzero
        · have hnx : ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.neg x) := by
            have hxneg' : ctx.spec.lt x (ctx.spec.ofZ Z0) := by
              rw [ctx.certificate.sourceLaws.ofZ_zero]
              exact hxneg
            exact RIneq.Ropp_0_gt_lt_contravar ctx x hxneg'
          have hny : ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.neg y) := by
            have hyneg' : ctx.spec.lt y (ctx.spec.ofZ Z0) := by
              rw [ctx.certificate.sourceLaws.ofZ_zero]
              exact hyneg
            exact RIneq.Ropp_0_gt_lt_contravar ctx y hyneg'
          have hprod : ctx.spec.lt ctx.spec.zero (ctx.spec.mul x y) := by
            have h := RIneq.Rmult_lt_0_compat ctx (ctx.spec.neg x)
              (ctx.spec.neg y) hnx hny
            change ctx.spec.lt (ctx.spec.ofZ Z0)
              (ctx.spec.mul (ctx.spec.neg x) (ctx.spec.neg y)) at h
            have hnegneg : ctx.spec.mul (ctx.spec.neg x) (ctx.spec.neg y) =
                ctx.spec.mul x y := by
              change ExactReal.Rmult ctx.spec
                (ExactReal.Ropp ctx.spec x) (ExactReal.Ropp ctx.spec y) =
                ExactReal.Rmult ctx.spec x y
              exact RIneq.Rmult_opp_opp ctx x y
            rw [ctx.certificate.sourceLaws.ofZ_zero, hnegneg] at h
            exact h
          have hprodle : ctx.spec.le ctx.spec.zero (ctx.spec.mul x y) :=
            (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hprod |>.1
          have hnegneg : ctx.spec.mul (ctx.spec.neg x) (ctx.spec.neg y) =
              ctx.spec.mul x y := by
            change ExactReal.Rmult ctx.spec
              (ExactReal.Ropp ctx.spec x) (ExactReal.Ropp ctx.spec y) =
              ExactReal.Rmult ctx.spec x y
            exact RIneq.Rmult_opp_opp ctx x y
          rw [ctx.certificate.sourceLaws.abs_nonnegative _ hprodle,
            ctx.certificate.sourceLaws.abs_negative x hxneg,
            ctx.certificate.sourceLaws.abs_negative y hyneg,
            hnegneg.symm]
        · subst y
          rw [ctx.certificate.orderedField.mul_zero,
            ctx.certificate.sourceLaws.abs_nonnegative _
              (ctx.certificate.orderedField.le_refl _),
            ctx.certificate.orderedField.mul_zero]
      · have hypos : ctx.spec.lt ctx.spec.zero y := hy
        have hy_nonneg : ctx.spec.le ctx.spec.zero y :=
          (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hypos |>.1
        have hypos' : ctx.spec.lt (ctx.spec.ofZ Z0) y := by
          rw [ctx.certificate.sourceLaws.ofZ_zero]
          exact hypos
        have hprod : ctx.spec.lt (ctx.spec.mul x y) ctx.spec.zero := by
          have hxneg' : ctx.spec.lt x (ctx.spec.ofZ Z0) := by
            rw [ctx.certificate.sourceLaws.ofZ_zero]
            exact hxneg
          have h := RIneq.Rmult_lt_compat_r ctx y x (ctx.spec.ofZ Z0)
            hypos' hxneg'
          change ctx.spec.lt (ctx.spec.mul x y)
            (ctx.spec.mul (ctx.spec.ofZ Z0) y) at h
          rw [ctx.certificate.sourceLaws.ofZ_zero,
            ctx.certificate.orderedField.zero_mul] at h
          exact h
        have hnegleft : ctx.spec.mul (ctx.spec.neg x) y =
            ctx.spec.neg (ctx.spec.mul x y) := by
          change ExactReal.Rmult ctx.spec (ExactReal.Ropp ctx.spec x) y =
            ExactReal.Ropp ctx.spec (ExactReal.Rmult ctx.spec x y)
          exact RIneq.Ropp_mult_distr_l_reverse ctx x y
        rw [ctx.certificate.sourceLaws.abs_negative _ hprod,
          ctx.certificate.sourceLaws.abs_negative x hxneg,
          ctx.certificate.sourceLaws.abs_nonnegative _ hy_nonneg,
          hnegleft.symm]
    · subst x
      rw [ctx.certificate.orderedField.zero_mul,
        ctx.certificate.sourceLaws.abs_nonnegative _
          (ctx.certificate.orderedField.le_refl _),
        ctx.certificate.orderedField.zero_mul]
  · have hxpos : ctx.spec.lt ctx.spec.zero x := hx
    have hx_nonneg : ctx.spec.le ctx.spec.zero x :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxpos |>.1
    have hxpos' : ctx.spec.lt (ctx.spec.ofZ Z0) x := by
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact hxpos
    rcases ctx.certificate.total_order y ctx.spec.zero with hy | hy
    · rcases hy with hyneg | hyzero
      · have hprod : ctx.spec.lt (ctx.spec.mul x y) ctx.spec.zero := by
          have hyneg' : ctx.spec.lt y (ctx.spec.ofZ Z0) := by
            rw [ctx.certificate.sourceLaws.ofZ_zero]
            exact hyneg
          have h := Raxioms.Rmult_lt_compat_l ctx x y (ctx.spec.ofZ Z0)
            hxpos' hyneg'
          change ctx.spec.lt (ctx.spec.mul x y)
            (ctx.spec.mul x (ctx.spec.ofZ Z0)) at h
          rw [ctx.certificate.sourceLaws.ofZ_zero,
            ctx.certificate.orderedField.mul_zero] at h
          exact h
        have hnegright : ctx.spec.mul x (ctx.spec.neg y) =
            ctx.spec.neg (ctx.spec.mul x y) := by
          change ExactReal.Rmult ctx.spec x (ExactReal.Ropp ctx.spec y) =
            ExactReal.Ropp ctx.spec (ExactReal.Rmult ctx.spec x y)
          exact RIneq.Ropp_mult_distr_r_reverse ctx x y
        rw [ctx.certificate.sourceLaws.abs_negative _ hprod,
          ctx.certificate.sourceLaws.abs_nonnegative _ hx_nonneg,
          ctx.certificate.sourceLaws.abs_negative y hyneg,
          hnegright.symm]
      · subst y
        rw [ctx.certificate.orderedField.mul_zero,
          ctx.certificate.sourceLaws.abs_nonnegative _ hx_nonneg,
          ctx.certificate.sourceLaws.abs_nonnegative _
            (ctx.certificate.orderedField.le_refl _),
          ctx.certificate.orderedField.mul_zero]
    · have hypos : ctx.spec.lt ctx.spec.zero y := hy
      have hy_nonneg : ctx.spec.le ctx.spec.zero y :=
        (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hypos |>.1
      have hypos' : ctx.spec.lt (ctx.spec.ofZ Z0) y := by
        rw [ctx.certificate.sourceLaws.ofZ_zero]
        exact hypos
      have hprod : ctx.spec.lt ctx.spec.zero (ctx.spec.mul x y) := by
        have h := RIneq.Rmult_lt_0_compat ctx x y hxpos' hypos'
        change ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.mul x y) at h
        rw [ctx.certificate.sourceLaws.ofZ_zero] at h
        exact h
      have hprodle : ctx.spec.le ctx.spec.zero (ctx.spec.mul x y) :=
        (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hprod |>.1
      rw [ctx.certificate.sourceLaws.abs_nonnegative _ hprodle,
        ctx.certificate.sourceLaws.abs_nonnegative _ hx_nonneg,
        ctx.certificate.sourceLaws.abs_nonnegative _ hy_nonneg]

end Rbasic_fun
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace Rbasic_fun

theorem Rabs_Rinv_proof :
    ∀ (ctx : ExactRealContext) (r : ctx.spec.carrier)
      (_h : ¬r = ExactReal.IZR ctx.spec Z0),
      Rabs_Rinv ctx r _h := by
  intro ctx r h
  change ctx.spec.abs (ctx.spec.inv r) =
    ctx.spec.inv (ctx.spec.abs r)
  have hzero : ExactReal.IZR ctx.spec Z0 = ctx.spec.zero :=
    ctx.certificate.sourceLaws.ofZ_zero
  have hrne : r ≠ ctx.spec.zero := by
    intro hr0
    apply h
    exact hr0.trans hzero.symm
  have habs_r_ne : ctx.spec.abs r ≠ ctx.spec.zero := by
    intro habs0
    have habs0' := Rabs_no_R0 ctx r h
    apply habs0'
    exact habs0.trans hzero.symm
  have hinvl : ctx.spec.mul (ctx.spec.inv r) r = ctx.spec.one := by
    have h' := Raxioms.Rinv_l ctx r h
    change ctx.spec.mul (ctx.spec.inv r) r =
      ctx.spec.ofZ
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos
          _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH) at h'
    rw [ctx.certificate.sourceLaws.ofZ_one] at h'
    exact h'
  have hzero_le_one : ctx.spec.le ctx.spec.zero ctx.spec.one := by
    have h01 := RIneq.Rle_0_1 ctx
    change ctx.spec.le (ctx.spec.ofZ Z0)
      (ctx.spec.ofZ (Zpos xH)) at h01
    rw [ctx.certificate.sourceLaws.ofZ_zero,
      ctx.certificate.sourceLaws.ofZ_one] at h01
    exact h01
  have habs_one : ctx.spec.abs ctx.spec.one = ctx.spec.one :=
    ctx.certificate.sourceLaws.abs_nonnegative _ hzero_le_one
  have hmul :
      ctx.spec.mul (ctx.spec.abs (ctx.spec.inv r)) (ctx.spec.abs r) =
        ctx.spec.one := by
    have habsmul :
        ctx.spec.abs (ctx.spec.mul (ctx.spec.inv r) r) =
          ctx.spec.mul (ctx.spec.abs (ctx.spec.inv r)) (ctx.spec.abs r) := by
      simpa [ExactReal.Rabs, ExactReal.Rmult] using
        (Rabs_mult ctx (ctx.spec.inv r) r)
    rw [← habsmul, hinvl, habs_one]
  have hinv_abs :
      ctx.spec.mul (ctx.spec.inv (ctx.spec.abs r)) (ctx.spec.abs r) =
        ctx.spec.one :=
    ctx.certificate.orderedField.inv_mul_cancel _ habs_r_ne
  apply RIneq.Rmult_eq_reg_r ctx (ctx.spec.abs r)
  · change ctx.spec.mul (ctx.spec.abs (ctx.spec.inv r)) (ctx.spec.abs r) =
      ctx.spec.mul (ctx.spec.inv (ctx.spec.abs r)) (ctx.spec.abs r)
    rw [hmul, hinv_abs]
  · exact Rabs_no_R0 ctx r h

end Rbasic_fun
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace Rbasic_fun

theorem Rabs_Ropp :
    ∀ (ctx : ExactRealContext), Rabs_RoppStatement ctx := by
  intro ctx x
  exact exact_abs_neg_suffix ctx x

theorem Rabs_def1 :
    ∀ (ctx : ExactRealContext), Rabs_def1Statement ctx := by
  intro ctx x a hxa hax
  change ctx.spec.lt x a at hxa
  change ctx.spec.lt (ctx.spec.neg a) x at hax
  change ctx.spec.lt (ctx.spec.abs x) a
  rcases ctx.certificate.total_order x ctx.spec.zero with hx | hx
  · rcases hx with hxneg | hxzero
    · rw [ctx.certificate.sourceLaws.abs_negative x hxneg]
      have h := RIneq.Ropp_lt_contravar ctx x (ctx.spec.neg a) hax
      change ctx.spec.lt (ctx.spec.neg x)
        (ctx.spec.neg (ctx.spec.neg a)) at h
      rw [show ctx.spec.neg (ctx.spec.neg a) = a by
        exact RIneq.Ropp_involutive ctx a] at h
      exact h
    · subst x
      rw [ctx.certificate.sourceLaws.abs_nonnegative _
        (ctx.certificate.orderedField.le_refl _)]
      exact hxa
  · have hxle : ctx.spec.le ctx.spec.zero x :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hx |>.1
    rw [ctx.certificate.sourceLaws.abs_nonnegative x hxle]
    exact hxa

theorem Rabs_def2 :
    ∀ (ctx : ExactRealContext), Rabs_def2Statement ctx := by
  intro ctx x a habs
  change ctx.spec.lt (ctx.spec.abs x) a at habs
  change And (ctx.spec.lt x a) (ctx.spec.lt (ctx.spec.neg a) x)
  rcases ctx.certificate.total_order x ctx.spec.zero with hx | hx
  · rcases hx with hxneg | hxzero
    · have hnegx : ctx.spec.lt (ctx.spec.neg x) a := by
        rw [← ctx.certificate.sourceLaws.abs_negative x hxneg]
        exact habs
      have hzero_negx : ctx.spec.lt ctx.spec.zero (ctx.spec.neg x) := by
        have h := RIneq.Ropp_0_gt_lt_contravar ctx x (by
          change ctx.spec.lt x (ctx.spec.ofZ Z0)
          rw [ctx.certificate.sourceLaws.ofZ_zero]
          exact hxneg)
        change ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.neg x) at h
        rw [ctx.certificate.sourceLaws.ofZ_zero] at h
        exact h
      have hzero_a : ctx.spec.lt ctx.spec.zero a :=
        ctx.certificate.orderedField.lt_trans _ _ _ hzero_negx hnegx
      constructor
      · exact ctx.certificate.orderedField.lt_trans _ _ _ hxneg hzero_a
      · have h := RIneq.Ropp_lt_contravar ctx a (ctx.spec.neg x) hnegx
        change ctx.spec.lt (ctx.spec.neg a)
          (ctx.spec.neg (ctx.spec.neg x)) at h
        rw [show ctx.spec.neg (ctx.spec.neg x) = x by
          exact RIneq.Ropp_involutive ctx x] at h
        exact h
    · subst x
      have hzero_a : ctx.spec.lt ctx.spec.zero a := by
        rw [ctx.certificate.sourceLaws.abs_nonnegative _
          (ctx.certificate.orderedField.le_refl _)] at habs
        exact habs
      constructor
      · exact hzero_a
      · have h := RIneq.Ropp_lt_gt_0_contravar ctx a (by
          change ctx.spec.lt (ctx.spec.ofZ Z0) a
          rw [ctx.certificate.sourceLaws.ofZ_zero]
          exact hzero_a)
        change ctx.spec.lt (ctx.spec.neg a) (ctx.spec.ofZ Z0) at h
        rw [ctx.certificate.sourceLaws.ofZ_zero] at h
        exact h
  · have hxle : ctx.spec.le ctx.spec.zero x :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hx |>.1
    have hxa : ctx.spec.lt x a := by
      rw [← ctx.certificate.sourceLaws.abs_nonnegative x hxle]
      exact habs
    have hzero_a : ctx.spec.lt ctx.spec.zero a :=
      ctx.certificate.orderedField.lt_trans _ _ _ hx hxa
    constructor
    · exact hxa
    · have hnega : ctx.spec.lt (ctx.spec.neg a) ctx.spec.zero := by
        have h := RIneq.Ropp_lt_gt_0_contravar ctx a (by
          change ctx.spec.lt (ctx.spec.ofZ Z0) a
          rw [ctx.certificate.sourceLaws.ofZ_zero]
          exact hzero_a)
        change ctx.spec.lt (ctx.spec.neg a) (ctx.spec.ofZ Z0) at h
        rw [ctx.certificate.sourceLaws.ofZ_zero] at h
        exact h
      exact ctx.certificate.orderedField.lt_trans _ _ _ hnega hx

private theorem flocqReal_zabs_zero_suffix :
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
      (Z0 : Z) = Z0 := by
  apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  rfl

private theorem flocqReal_zabs_pos_suffix
    (p : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) :
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
      (.Zpos p) = (.Zpos p : Z) := by
  apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
        (.Zpos p)) =
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (.Zpos p)
  unfold _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
  rw [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  simp [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]

private theorem flocqReal_zabs_neg_suffix
    (p : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) :
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
      (.Zneg p) = (.Zpos p : Z) := by
  apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
        (.Zneg p)) =
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (.Zpos p)
  unfold _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
  rw [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  simp [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]

private theorem flocqReal_zopp_pos_suffix
    (p : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) :
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
      (.Zpos p) = (.Zneg p : Z) := by
  apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  unfold _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
  rw [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  simp [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]

theorem abs_IZR :
    ∀ (ctx : ExactRealContext), abs_IZRStatement ctx := by
  intro ctx z
  cases z with
  | Z0 =>
      change ctx.spec.ofZ
          (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
            Z0) = ctx.spec.abs (ctx.spec.ofZ Z0)
      rw [flocqReal_zabs_zero_suffix]
      rw [ctx.certificate.sourceLaws.ofZ_zero,
        ctx.certificate.sourceLaws.abs_nonnegative]
      exact ctx.certificate.orderedField.le_refl _
  | Zpos p =>
      change ctx.spec.ofZ
          (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
            (.Zpos p)) = ctx.spec.abs (ctx.spec.ofZ (.Zpos p))
      rw [flocqReal_zabs_pos_suffix]
      have hp := RIneq.IZR_le ctx Z0 (.Zpos p)
        (Int.natCast_nonneg
          (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))
      change ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.ofZ (.Zpos p)) at hp
      rw [ctx.certificate.sourceLaws.ofZ_zero] at hp
      exact (ctx.certificate.sourceLaws.abs_nonnegative _ hp).symm
  | Zneg p =>
      change ctx.spec.ofZ
          (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
            (.Zneg p)) = ctx.spec.abs (ctx.spec.ofZ (.Zneg p))
      rw [flocqReal_zabs_neg_suffix]
      have hneg := ctx.certificate.sourceLaws.ofZ_neg (.Zpos p)
      rw [flocqReal_zopp_pos_suffix] at hneg
      rw [hneg]
      have habs := Rabs_Ropp ctx (ctx.spec.ofZ (.Zpos p))
      change ctx.spec.abs (ctx.spec.neg (ctx.spec.ofZ (.Zpos p))) =
        ctx.spec.abs (ctx.spec.ofZ (.Zpos p)) at habs
      rw [habs]
      have hp := RIneq.IZR_le ctx Z0 (.Zpos p)
        (Int.natCast_nonneg
          (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))
      change ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.ofZ (.Zpos p)) at hp
      rw [ctx.certificate.sourceLaws.ofZ_zero] at hp
      exact (ctx.certificate.sourceLaws.abs_nonnegative _ hp).symm

end Rbasic_fun
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace Rfunctions

theorem powerRZ_add :
    ∀ (ctx : ExactRealContext), powerRZ_addStatement ctx := by
  intro ctx x n m h
  change ExactReal.powerRZ ctx.spec x (Z.add n m) =
    ctx.spec.mul (ExactReal.powerRZ ctx.spec x n)
      (ExactReal.powerRZ ctx.spec x m)
  have hx : x ≠ ctx.spec.zero := by
    intro hx0
    apply h
    change x = ctx.spec.ofZ Z0
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hx0
  exact ctx.certificate.sourceLaws.powerRZ_add x n m hx

end Rfunctions
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace Rpower

theorem exp_increasing :
    ∀ (ctx : ExactRealContext), exp_increasingStatement ctx := by
  intro ctx x y hxy
  exact ctx.certificate.exp.strict_monotone x y hxy

end Rpower
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace Rfunctions

private theorem powerRZ_mul_pos_suffix
    (ctx : ExactRealContext) (a b : ctx.spec.carrier)
    (ha : ctx.spec.lt ctx.spec.zero a)
    (hb : ctx.spec.lt ctx.spec.zero b) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.mul a b) := by
  have h := ctx.certificate.orderedField.mul_lt_compat_l a
    ctx.spec.zero b ha hb
  rw [ctx.certificate.orderedField.mul_zero] at h
  exact h

private theorem powerRZ_one_pos_suffix (ctx : ExactRealContext) :
    ctx.spec.lt ctx.spec.zero ctx.spec.one := by
  have h := RIneq.Rlt_0_1 ctx
  change ctx.spec.lt (ctx.spec.ofZ Z0)
    (ctx.spec.ofZ (Zpos xH)) at h
  rw [ctx.certificate.sourceLaws.ofZ_zero,
    ctx.certificate.sourceLaws.ofZ_one] at h
  exact h

private theorem powerRZ_inv_pos_suffix
    (ctx : ExactRealContext) (a : ctx.spec.carrier)
    (ha : ctx.spec.lt ctx.spec.zero a) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.inv a) := by
  have ha' : ctx.spec.lt (ctx.spec.ofZ Z0) a := by
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact ha
  have h := RIneq.Rinv_0_lt_compat ctx a ha'
  change ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.inv a) at h
  rw [ctx.certificate.sourceLaws.ofZ_zero] at h
  exact h

private theorem powerNat_pos_suffix
    (ctx : ExactRealContext) (x : ctx.spec.carrier)
    (hx : ctx.spec.lt ctx.spec.zero x) :
    ∀ n : Nat, ctx.spec.lt ctx.spec.zero (ExactReal.powerNat ctx.spec x n) := by
  intro n
  induction n with
  | zero =>
      exact powerRZ_one_pos_suffix ctx
  | succ n ih =>
      unfold ExactReal.powerNat
      exact powerRZ_mul_pos_suffix ctx x
        (ExactReal.powerNat ctx.spec x n) hx ih

theorem powerRZ_lt :
    ∀ (ctx : ExactRealContext), powerRZ_ltStatement ctx := by
  intro ctx x z hx
  have hx' : ctx.spec.lt ctx.spec.zero x := by
    change ctx.spec.lt (ctx.spec.ofZ Z0) x at hx
    rw [ctx.certificate.sourceLaws.ofZ_zero] at hx
    exact hx
  change ctx.spec.lt (ctx.spec.ofZ Z0) (ExactReal.powerRZ ctx.spec x z)
  rw [ctx.certificate.sourceLaws.ofZ_zero]
  cases z with
  | Z0 =>
      exact powerRZ_one_pos_suffix ctx
  | Zpos p =>
      exact powerNat_pos_suffix ctx x hx' _
  | Zneg p =>
      exact powerRZ_inv_pos_suffix ctx _
        (powerNat_pos_suffix ctx x hx' _)

theorem powerRZ_le :
    ∀ (ctx : ExactRealContext), powerRZ_leStatement ctx := by
  intro ctx x z hx
  have hlt := powerRZ_lt ctx x z hx
  have hlt' : ctx.spec.lt ctx.spec.zero
      (ExactReal.powerRZ ctx.spec x z) := by
    change ctx.spec.lt (ctx.spec.ofZ Z0)
      (ExactReal.powerRZ ctx.spec x z) at hlt
    rw [ctx.certificate.sourceLaws.ofZ_zero] at hlt
    exact hlt
  change ctx.spec.le (ctx.spec.ofZ Z0) (ExactReal.powerRZ ctx.spec x z)
  rw [ctx.certificate.sourceLaws.ofZ_zero]
  exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt' |>.1

end Rfunctions
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace Rpower

theorem exp_lt_inv :
    ∀ (ctx : ExactRealContext), exp_lt_invStatement ctx := by
  intro ctx x y hxy
  rcases ctx.certificate.total_order x y with h | h
  · rcases h with hlt | heq
    · exact hlt
    · subst y
      exact (ctx.certificate.orderedField.lt_irrefl _ hxy).elim
  · have hyx : ctx.spec.lt (ctx.spec.exp y) (ctx.spec.exp x) :=
      ctx.certificate.exp.strict_monotone y x h
    exact (ctx.certificate.orderedField.lt_irrefl _
      (ctx.certificate.orderedField.lt_trans _ _ _ hxy hyx)).elim

theorem exp_ln :
    ∀ (ctx : ExactRealContext), exp_lnStatement ctx := by
  intro ctx x hx
  change ctx.spec.exp (ExactReal.ln ctx.spec x) = x
  have hx' : ctx.spec.lt ctx.spec.zero x := by
    change ctx.spec.lt (ctx.spec.ofZ Z0) x at hx
    rw [ctx.certificate.sourceLaws.ofZ_zero] at hx
    exact hx
  unfold ExactReal.ln
  cases hdec : ctx.spec.lt_dec ctx.spec.zero x with
  | left _ =>
      simpa [hdec] using ctx.certificate.ln.exp_ln x hx'
  | right hnot =>
      exact (hnot hx').elim

theorem exp_Ropp :
    ∀ (ctx : ExactRealContext), exp_RoppStatement ctx := by
  intro ctx x
  change ctx.spec.exp (ctx.spec.neg x) = ctx.spec.inv (ctx.spec.exp x)
  exact ctx.certificate.sourceLaws.exp_opp x

end Rpower
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace Rsqrt_def

theorem Rsqrt_positivity :
    Rsqrt_positivityStatement := by
  intro ctx x
  exact ctx.certificate.sqrt.nonnegative x.nonneg

end Rsqrt_def
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace Rtrigo_def

theorem exp_0 :
    ∀ (ctx : ExactRealContext), exp_0Statement ctx := by
  intro ctx
  change ctx.spec.exp (ctx.spec.ofZ Z0) =
    ctx.spec.ofZ (Zpos xH)
  rw [ctx.certificate.sourceLaws.ofZ_zero,
    ctx.certificate.exp.zero,
    ctx.certificate.sourceLaws.ofZ_one]

end Rtrigo_def
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal

namespace CompCert4Lean.Foundation.FlocqReal
namespace Rocq.Coq.Reals
namespace RIneq

theorem Ropp_plus_distr :
    ∀ (ctx : ExactRealContext), Ropp_plus_distrStatement ctx := by
  intro ctx r1 r2
  change ctx.spec.neg (ctx.spec.add r1 r2) =
    ctx.spec.add (ctx.spec.neg r1) (ctx.spec.neg r2)
  exact exact_neg_add_suffix ctx r1 r2

end RIneq
end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal
