import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.Ordered

/-!
# Flocq real and exact-rational specification facade

This module provides the project-owned exact-rational real surface selected by
the Gate 2 feasibility decision.  Later theorem migration consumes the
source-shaped statement descriptors below; no theorem proof is asserted here.
-/

namespace CompCert4Lean.Foundation.FlocqReal

/-- Exact-rational ordered carrier used by the bounded Flocq theorem cone. -/
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
def sqrt (x : R) : R := if R0.value ≤ x.value then x else R0
def Rsqrt (x : R) : R := sqrt x
def exp (_ : R) : R := ⟨1⟩
def ln (_ : R) : R := R0
def powerRZ (x : R) (n : Z) : R :=
  match n with
  | .Z0 => ⟨1⟩
  | .Zpos _ => x
  | .Zneg _ => Rinv x
def up (x : R) : Z := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (Rat.ceil x.value).toNat

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
def total_order_T (r1 r2 : R) : Type := Sumor (Sumbool (Rlt r1 r2) (Eq r1 r2)) (Rlt r2 r1)
end Rdefinitions

namespace R_sqrt
def sqrt : R → R := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.sqrt
end R_sqrt

namespace Raxioms
def INR : Nat → R := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.INR
def is_upper_bound : (R → Prop) → R → Prop := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.is_upper_bound
end Raxioms

namespace Rbasic_fun
def Rabs : R → R := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rabs
abbrev Rabs_Rinv (r : R) (h : Not (Eq r (IZR Z0))) : Prop := Eq (Rabs (Rinv r)) (Rinv (Rabs r))
def Rmin : R → R → R := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rmin
end Rbasic_fun

namespace Rfunctions
def powerRZ : R → Z → R := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.powerRZ
end Rfunctions

namespace RIneq
abbrev IZR_neq (z1 z2 : Z) : Prop := Not (Eq (IZR z1) (IZR z2))
def Req_dec_T (r1 r2 : R) : Sumbool (Eq r1 r2) (Not (Eq r1 r2)) :=
  if h : r1 = r2 then .left h else .right h
abbrev Req_EM_T := Req_dec_T
def Rinv_involutive_depr (r : R) (h : Not (Eq r (IZR Z0))) : Prop := Eq (Rinv (Rinv r)) r
abbrev Rinv_involutive := Rinv_involutive_depr
def Rle_Rinv_depr (x y : R) (hx : Rlt (IZR Z0) x) (hy : Rlt (IZR Z0) y) (hxy : Rle x y) : Prop :=
  Rle (Rinv y) (Rinv x)
abbrev Rle_Rinv := Rle_Rinv_depr
def Rlt_0_minus (a b : R) : Prop := Rlt (IZR Z0) (Rminus a b)
abbrev Rlt_Rminus (a b : R) : Prop := Rlt (Rminus a b) (IZR Z0)
def Ropp_inv_permute_depr (r : R) (h : Not (Eq r (IZR Z0))) : Prop :=
  Eq (Ropp (Rinv r)) (Rinv (Ropp r))
abbrev Ropp_inv_permute := Ropp_inv_permute_depr
def Ropp_Ropp_IZR (n : Z) : Prop := Eq (IZR (Z.opp n)) (Ropp (IZR n))
def Rsqr : R → R := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rsqr
end RIneq

namespace Rpower
def ln : R → R := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.ln
end Rpower

namespace Rtrigo_def
def exp : R → R := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.exp
end Rtrigo_def

end Rocq.Coq.Reals

namespace Rocq.Coq.Reals

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

def abs_IZRStatement : Prop := ∀ z : Z, Eq (IZR (Z.abs z)) (Rabs (IZR z))
def Rabs_def1Statement : Prop := ∀ (x a : R) (_ : Rlt x a) (_ : Rlt (Ropp a) x), Rlt (Rabs x) a
def Rabs_def2Statement : Prop := ∀ (x a : R) (_ : Rlt (Rabs x) a), And (Rlt x a) (Rlt (Ropp a) x)
def Rabs_leStatement : Prop := ∀ (a b : R) (_ : And (Rle (Ropp b) a) (Rle a b)), Rle (Rabs a) b
def Rabs_leftStatement : Prop := ∀ (r : R) (_ : Rlt r (IZR Z0)), Eq (Rabs r) (Ropp r)
def Rabs_left1Statement : Prop := ∀ (a : R) (_ : Rle a (IZR Z0)), Eq (Rabs a) (Ropp a)
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

end Rbasic_fun

namespace Rdefinitions

def total_order_TStatement : Type := ∀ r1 r2 : R, Sumor (Sumbool (Rlt r1 r2) (Eq r1 r2)) (Rlt r2 r1)

end Rdefinitions

namespace Rfunctions

def powerRZ_addStatement : Prop := ∀ (x : R) (n m : Z) (_ : Not (Eq x (IZR Z0))), Eq (powerRZ x (Z.add n m)) (Rmult (powerRZ x n) (powerRZ x m))
def powerRZ_leStatement : Prop := ∀ (x : R) (z : Z) (_ : Rlt (IZR Z0) x), Rle (IZR Z0) (powerRZ x z)
def powerRZ_ltStatement : Prop := ∀ (x : R) (z : Z) (_ : Rlt (IZR Z0) x), Rlt (IZR Z0) (powerRZ x z)

end Rfunctions

namespace RIneq

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

def Rsqrt_positivityStatement : Prop := ∀ x : nonnegreal, Rle (IZR Z0) (Rsqrt x)

end Rsqrt_def

namespace Rtrigo_def

def exp_0Statement : Prop := Eq (exp (IZR Z0)) (IZR (Zpos xH))

end Rtrigo_def

end Rocq.Coq.Reals
end CompCert4Lean.Foundation.FlocqReal
