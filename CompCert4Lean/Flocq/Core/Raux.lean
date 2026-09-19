import CompCert4Lean.Flocq.Core.Zaux

/-!
# Flocq real auxiliary definitions

This module contains the executable and statement-descriptor surfaces selected
from `Flocq.Core.Raux`.  Proof-heavy declarations are represented by their
source-shaped proposition descriptors for later proof migration.
-/

namespace CompCert4Lean.Flocq.Core.Raux

/-!
The executable surface is deliberately carried by the checked rational
carrier.  The exact surface below is parameterised by an injected context;
there is no ambient exact-real instance.
-/
abbrev RuntimeReal := CompCert4Lean.Foundation.FlocqReal.RuntimeReal
abbrev RuntimeCarrier := CompCert4Lean.Foundation.FlocqReal.RuntimeCarrier
abbrev ExactRealSpec := CompCert4Lean.Foundation.FlocqReal.ExactRealSpec
abbrev ExactRealContext := CompCert4Lean.Foundation.FlocqReal.ExactRealContext
abbrev ExactRealCertificate := CompCert4Lean.Foundation.FlocqReal.ExactRealCertificate
abbrev RuntimeExactAdapter := CompCert4Lean.Foundation.FlocqReal.RuntimeExactAdapter

abbrev R := RuntimeReal
abbrev Z := CompCert4Lean.Flocq.Core.Zaux.Z
abbrev positive := CompCert4Lean.Flocq.Core.Zaux.positive
abbrev comparison := CompCert4Lean.Flocq.Core.Zaux.comparison
abbrev Lt : comparison := CompCert4Lean.Flocq.Core.Zaux.Lt
abbrev Eq : comparison := CompCert4Lean.Flocq.Core.Zaux.Eq
abbrev Gt : comparison := CompCert4Lean.Flocq.Core.Zaux.Gt
abbrev Z0 : Z := CompCert4Lean.Flocq.Core.Zaux.Z0
abbrev xH : positive := CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH
abbrev xO : positive → positive := CompCert4Lean.Foundation.Numbers.Rocq.Coq.xO
abbrev Zpos : positive → Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
abbrev Zneg : positive → Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg
abbrev Zadd := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
abbrev Zsub := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub
abbrev Zopp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
abbrev Zabs := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
abbrev Zdiv := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div
abbrev Zdiv2 := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div2
abbrev Zpower := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower
abbrev Zpower_pos := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower_pos
abbrev Zcompare := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.compare
abbrev Zlt := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt
abbrev Zle := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
abbrev IZR := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.IZR
abbrev R0 := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.R0
abbrev Ropp := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Ropp
abbrev Rplus := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rplus
abbrev Rmult := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rmult
abbrev Rabs := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rabs
abbrev Rminus := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rminus
abbrev Rdiv := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rdiv
abbrev Rinv := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rinv
abbrev Rlt := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rlt
abbrev Rle := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rle
abbrev Rge := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rge
abbrev Rgt := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rgt
abbrev Rmin := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rmin
abbrev Rsqr := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rsqr
/- Runtime-only compatibility operations. Exact theorem consumers must use an
   explicit `Foundation.FlocqReal.ExactRealSpec` and certificate. -/
abbrev sqrt := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Runtime.sqrt
abbrev exp := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Runtime.exp
abbrev ln := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Runtime.ln
abbrev powerRZ := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.powerRZ
abbrev up := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.up
abbrev radix := CompCert4Lean.Flocq.Core.Zaux.radix
abbrev cond_Zopp := CompCert4Lean.Flocq.Core.Zaux.cond_Zopp
abbrev bool_eqb := CompCert4Lean.Foundation.Logic.Rocq.Coq.Bool.Bool.eqb
abbrev Sumor := CompCert4Lean.Foundation.Logic.Support.Sumor
abbrev Rone : R := ⟨1⟩
abbrev Rtwo : R := ⟨2⟩
abbrev Rhalf : R := Rdiv Rone Rtwo

/-! Exact specification-facing operations.  These are adapters over the
injected `ExactRealContext`; none of the operations below falls back to the
rational/runtime compatibility definitions above. -/
namespace Exact

abbrev Context := ExactRealContext
abbrev Spec := ExactRealSpec
abbrev R (ctx : Context) := ctx.spec.carrier
abbrev Z := CompCert4Lean.Flocq.Core.Raux.Z

def IZR (ctx : Context) (z : Z) : R ctx :=
  CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR ctx.spec z
def R0 (ctx : Context) : R ctx :=
  CompCert4Lean.Foundation.FlocqReal.ExactReal.R0 ctx.spec
def Rone (ctx : Context) : R ctx :=
  CompCert4Lean.Foundation.FlocqReal.ExactReal.Rone ctx.spec
def Ropp (ctx : Context) (x : R ctx) : R ctx :=
  CompCert4Lean.Foundation.FlocqReal.ExactReal.Ropp ctx.spec x
def Rplus (ctx : Context) (x y : R ctx) : R ctx :=
  CompCert4Lean.Foundation.FlocqReal.ExactReal.Rplus ctx.spec x y
def Rminus (ctx : Context) (x y : R ctx) : R ctx :=
  CompCert4Lean.Foundation.FlocqReal.ExactReal.Rminus ctx.spec x y
def Rmult (ctx : Context) (x y : R ctx) : R ctx :=
  CompCert4Lean.Foundation.FlocqReal.ExactReal.Rmult ctx.spec x y
def Rinv (ctx : Context) (x : R ctx) : R ctx :=
  CompCert4Lean.Foundation.FlocqReal.ExactReal.Rinv ctx.spec x
def Rdiv (ctx : Context) (x y : R ctx) : R ctx :=
  CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv ctx.spec x y
def Rlt (ctx : Context) (x y : R ctx) : Prop :=
  CompCert4Lean.Foundation.FlocqReal.ExactReal.Rlt ctx.spec x y
def Rle (ctx : Context) (x y : R ctx) : Prop :=
  CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle ctx.spec x y
def Rge (ctx : Context) (x y : R ctx) : Prop := Rle ctx y x
def Rgt (ctx : Context) (x y : R ctx) : Prop := Rlt ctx y x
def Rabs (ctx : Context) (x : R ctx) : R ctx :=
  CompCert4Lean.Foundation.FlocqReal.ExactReal.Rabs ctx.spec x
def Rmin (ctx : Context) (x y : R ctx) : R ctx :=
  CompCert4Lean.Foundation.FlocqReal.ExactReal.Rmin ctx.spec x y
def Rsqr (ctx : Context) (x : R ctx) : R ctx := Rmult ctx x x
def sqrt (ctx : Context) (x : R ctx) : R ctx :=
  CompCert4Lean.Foundation.FlocqReal.ExactReal.sqrt ctx.spec x
def exp (ctx : Context) (x : R ctx) : R ctx :=
  CompCert4Lean.Foundation.FlocqReal.ExactReal.exp ctx.spec x
def ln (ctx : Context) (x : R ctx) : R ctx :=
  CompCert4Lean.Foundation.FlocqReal.ExactReal.ln ctx.spec x
def powerRZ (ctx : Context) (x : R ctx) (z : Z) : R ctx :=
  CompCert4Lean.Foundation.FlocqReal.ExactReal.powerRZ ctx.spec x z
def up (ctx : Context) (x : R ctx) : Z :=
  CompCert4Lean.Foundation.FlocqReal.ExactReal.up ctx.spec x
def Rtwo (ctx : Context) : R ctx := Rplus ctx (Rone ctx) (Rone ctx)
def Rhalf (ctx : Context) : R ctx := Rdiv ctx (Rone ctx) (Rtwo ctx)
def cond_Ropp (ctx : Context) (b : Bool) (m : R ctx) : R ctx :=
  if b then Ropp ctx m else m

noncomputable def Rcompare (ctx : Context) (x y : R ctx) : comparison :=
  match CompCert4Lean.Foundation.FlocqReal.ExactReal.total_order_T ctx x y with
  | .inleft (.left _) => Lt
  | .inleft (.right _) => Eq
  | .inright _ => Gt

inductive Rcompare_prop (ctx : Context) (x y : R ctx) : comparison → Prop where
  | Rcompare_Lt_ : Rlt ctx x y → Rcompare_prop ctx x y Lt
  | Rcompare_Eq_ : x = y → Rcompare_prop ctx x y Eq
  | Rcompare_Gt_ : Rlt ctx y x → Rcompare_prop ctx x y Gt

inductive Rle_bool_prop (ctx : Context) (x y : R ctx) : Bool → Prop where
  | Rle_bool_true_ : Rle ctx x y → Rle_bool_prop ctx x y true
  | Rle_bool_false_ : Rlt ctx y x → Rle_bool_prop ctx x y false

inductive Rlt_bool_prop (ctx : Context) (x y : R ctx) : Bool → Prop where
  | Rlt_bool_true_ : Rlt ctx x y → Rlt_bool_prop ctx x y true
  | Rlt_bool_false_ : Rle ctx y x → Rlt_bool_prop ctx x y false

inductive Req_bool_prop (ctx : Context) (x y : R ctx) : Bool → Prop where
  | Req_bool_true_ : x = y → Req_bool_prop ctx x y true
  | Req_bool_false_ : x ≠ y → Req_bool_prop ctx x y false

noncomputable def Rle_bool (ctx : Context) (x y : R ctx) : Bool :=
  match Rcompare ctx x y with
  | .Gt => false
  | _ => true

noncomputable def Rlt_bool (ctx : Context) (x y : R ctx) : Bool :=
  match Rcompare ctx x y with
  | .Lt => true
  | _ => false

noncomputable def Req_bool (ctx : Context) (x y : R ctx) : Bool :=
  match Rcompare ctx x y with
  | .Eq => true
  | _ => false

def Zfloor (ctx : Context) (x : R ctx) : Z := Zsub (up ctx x) (Zpos xH)
def Zceil (ctx : Context) (x : R ctx) : Z := Zopp (Zfloor ctx (Ropp ctx x))
noncomputable def Ztrunc (ctx : Context) (x : R ctx) : Z :=
  if Rlt_bool ctx x (R0 ctx) then Zceil ctx x else Zfloor ctx x
noncomputable def Zaway (ctx : Context) (x : R ctx) : Z :=
  if Rlt_bool ctx x (R0 ctx) then Zfloor ctx x else Zceil ctx x

def bpow (ctx : Context) (r : radix) (e : Z) : R ctx :=
  match e with
  | .Zpos p => IZR ctx (Zpower_pos r p)
  | .Zneg p => Rinv ctx (IZR ctx (Zpower_pos r p))
  | .Z0 => Rone ctx

/- The executable magnitude algorithm remains runtime-only.  An exact theorem
   consumer supplies its source-shaped magnitude witness explicitly, together
   with the invariant that later proof grinding must discharge. -/
structure MagnitudeValue (ctx : Context) (r : radix) (x : R ctx) where
  mag_val : Z
  mag_bound : x ≠ R0 ctx →
    Rle ctx (bpow ctx r (Zsub mag_val (Zpos xH))) (Rabs ctx x) ∧
      Rlt ctx (Rabs ctx x) (bpow ctx r mag_val)

structure Magnitude (ctx : Context) where
  value : ∀ (r : radix) (x : R ctx), MagnitudeValue ctx r x

abbrev mag (m : Magnitude ctx) (r : radix) (x : R ctx) : MagnitudeValue ctx r x :=
  m.value r x

end Exact

private structure FirstNat (P : Nat → Prop) where
  val : Nat
  property : P val
  minimal : ∀ k, k < val → ¬ P k

private def firstNat (P : Nat → Prop) [DecidablePred P] :
    ∀ bound, P bound → FirstNat P
  | 0, h => ⟨0, h, by omega⟩
  | bound + 1, h =>
      if h0 : P 0 then
        ⟨0, h0, by omega⟩
      else
        let next := firstNat (fun k => P (k + 1)) bound h
        ⟨next.val + 1, next.property, by
          intro k hk
          cases k with
          | zero => simpa using h0
          | succ k =>
              exact next.minimal k (by omega)⟩

private def radixNat (r : radix) : Nat :=
  Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val)

private theorem radixNat_ge_two (r : radix) : 2 ≤ radixNat r := by
  have hr := r.radix_prop
  change (if (2 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val
    then true else false) = true at hr
  have hbase : (2 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val := by
    simpa using hr
  simp [radixNat]
  omega

private def highMagnitude (b n d : Nat) (hb : 1 < b) (hd : 0 < d) :
    FirstNat (fun k => n < d * b ^ k) :=
  firstNat (fun k => n < d * b ^ k) n <|
    Nat.lt_of_lt_of_le (Nat.lt_pow_self hb) (Nat.le_mul_of_pos_left _ hd)

private def lowMagnitude (b n d : Nat) (hb : 1 < b) (hn : 0 < n) :
    FirstNat (fun k => d ≤ n * b ^ (k + 1)) :=
  firstNat (fun k => d ≤ n * b ^ (k + 1)) d <|
    Nat.le_trans (Nat.le_of_lt (Nat.lt_pow_self hb)) <|
      Nat.le_trans (Nat.le_of_lt (Nat.pow_lt_pow_succ hb))
        (Nat.le_mul_of_pos_left _ hn)

private theorem orderedReal_ext {x y : R} (h : x.value = y.value) : x = y := by
  cases x
  cases y
  cases h
  rfl

private theorem Rabs_value_eq_abs (x : R) : (Rabs x).value = x.value.abs := by
  change (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rabs x).value = x.value.abs
  unfold CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rabs
  simp only [CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.R0,
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Ropp]
  unfold Rat.abs
  by_cases h : x.value < 0
  · simp [h, Rat.not_le.mpr h]
  · simp [h, Rat.not_lt.mp h]

private theorem Rabs_value_ne_zero (x : R) (hx : x ≠ R0) : (Rabs x).value ≠ 0 := by
  rw [Rabs_value_eq_abs]
  intro h
  apply hx
  apply orderedReal_ext
  change x.value = (0 : Rat)
  exact Rat.abs_eq_zero_iff.mp h

def Rcompare (x y : R) : comparison :=
  let order :
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rdefinitions.total_order_T_type x y :=
    if hxy : x.value < y.value then
      .inleft (.left hxy)
    else if heq : x.value = y.value then
      .inleft (.right (orderedReal_ext heq))
    else
      .inright (Rat.lt_of_le_of_ne (Rat.not_lt.mp hxy) (fun hyx => heq hyx.symm))
  match order with
  | .inleft (.left _) => Lt
  | .inleft (.right _) => Eq
  | .inright _ => Gt

inductive Rcompare_prop (x y : R) : comparison → Prop where
  | Rcompare_Lt_ : Rlt x y → Rcompare_prop x y Lt
  | Rcompare_Eq_ : x = y → Rcompare_prop x y Eq
  | Rcompare_Gt_ : Rlt y x → Rcompare_prop x y Gt

def Rle_bool (x y : R) : Bool :=
  match Rcompare x y with
  | .Gt => false
  | _ => true

inductive Rle_bool_prop (x y : R) : Bool → Prop where
  | Rle_bool_true_ : Rle x y → Rle_bool_prop x y true
  | Rle_bool_false_ : Rlt y x → Rle_bool_prop x y false

def Rlt_bool (x y : R) : Bool :=
  match Rcompare x y with
  | .Lt => true
  | _ => false

inductive Rlt_bool_prop (x y : R) : Bool → Prop where
  | Rlt_bool_true_ : Rlt x y → Rlt_bool_prop x y true
  | Rlt_bool_false_ : Rle y x → Rlt_bool_prop x y false

def Req_bool (x y : R) : Bool :=
  match Rcompare x y with
  | .Eq => true
  | _ => false

inductive Req_bool_prop (x y : R) : Bool → Prop where
  | Req_bool_true_ : x = y → Req_bool_prop x y true
  | Req_bool_false_ : x ≠ y → Req_bool_prop x y false

def Zfloor (x : R) : Z := Zsub (up x) (Zpos xH)

def Zceil (x : R) : Z := Zopp (Zfloor (Ropp x))

def Ztrunc (x : R) : Z := if Rlt_bool x R0 then Zceil x else Zfloor x

def Zaway (x : R) : Z := if Rlt_bool x R0 then Zfloor x else Zceil x

def bpow (r : radix) (e : Z) : R :=
  match e with
  | .Zpos p => IZR (Zpower_pos r p)
  | .Zneg p => Rinv (IZR (Zpower_pos r p))
  | .Z0 => ⟨1⟩

private theorem IZR_value (z : Z) :
    (IZR z).value = Rat.ofInt (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z) := by
  cases z <;> rfl

private theorem bpow_value (r : radix) (e : Z) :
    (bpow r e).value =
      Rat.ofInt (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val) ^
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e) := by
  cases e with
  | Z0 =>
      change (1 : Rat) =
        Rat.ofInt (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val) ^ (0 : Int)
      exact (Rat.zpow_zero _).symm
  | Zpos p =>
      change (IZR (Zpower_pos r p)).value =
        Rat.ofInt (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val) ^
          (Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))
      rw [IZR_value]
      simp only [Zpower_pos,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow_pos,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      exact (Rat.intCast_pow _ _).trans (Rat.zpow_natCast _ _).symm
  | Zneg p =>
      change 1 / (IZR (Zpower_pos r p)).value =
        Rat.ofInt (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val) ^
          (-(Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)))
      rw [IZR_value]
      simp only [Zpower_pos,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow_pos,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      calc
        1 / Rat.ofInt
            (Int.pow (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val)
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) =
            (Rat.ofInt
              (Int.pow (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val)
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)))⁻¹ := by
                  simp [Rat.div_def]
        _ = (Rat.ofInt (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val) ^
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))⁻¹ := by
                exact congrArg Inv.inv (Rat.intCast_pow _ _)
        _ = (Rat.ofInt (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val) ^
              (Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)))⁻¹ := by
                exact congrArg Inv.inv (Rat.zpow_natCast _ _).symm
        _ = Rat.ofInt (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val) ^
              (-(Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))) :=
                (Rat.zpow_neg _ _).symm

private theorem radixRat_eq (r : radix) :
    Rat.ofInt (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val) =
      (radixNat r : Rat) := by
  have hnonneg : 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val := by
    have := radixNat_ge_two r
    have hr := r.radix_prop
    change (if (2 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val
      then true else false) = true at hr
    simpa using (show (0 : Int) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val by
        have : (2 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val := by
          simpa using hr
        omega)
  change Rat.ofInt (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val) =
    Rat.ofInt (Int.ofNat (radixNat r))
  congr 1
  exact (Int.toNat_of_nonneg hnonneg).symm

private theorem bpow_zOfInt_value (r : radix) (i : Int) :
    (bpow r (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt i)).value =
      (radixNat r : Rat) ^ i := by
  rw [bpow_value, CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt, radixRat_eq]

private theorem zsub_zOfInt_one (i : Int) :
    Zsub (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt i) (Zpos xH) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (i - 1) := by
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt i) - 1) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (i - 1)
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]

private theorem neg_ofNat_sub_one (n : Nat) :
    -(Int.ofNat n) - 1 = -(Int.ofNat (n + 1)) := by
  have hadd : Int.ofNat (n + 1) = Int.ofNat n + 1 := by
    exact (Int.ofNat_add_ofNat n 1).symm
  rw [hadd]
  omega

private theorem natPow_le_rat_iff (a : Rat) (ha : 0 ≤ a) (b k : Nat) :
    (b : Rat) ^ k ≤ a ↔ b ^ k * a.den ≤ a.num.natAbs := by
  rw [Rat.le_iff]
  simp only [Rat.num_pow, Rat.den_pow, Rat.num_natCast, Rat.den_natCast,
    Int.natCast_pow, Nat.one_pow]
  have hnum : (a.num.natAbs : Int) = a.num :=
    Int.natAbs_of_nonneg (Rat.num_nonneg.mpr ha)
  rw [← hnum]
  norm_cast
  simp

private theorem rat_lt_natPow_iff (a : Rat) (ha : 0 ≤ a) (b k : Nat) :
    a < (b : Rat) ^ k ↔ a.num.natAbs < a.den * b ^ k := by
  rw [Rat.lt_iff]
  simp only [Rat.num_pow, Rat.den_pow, Rat.num_natCast, Rat.den_natCast,
    Int.natCast_pow, Nat.one_pow]
  have hnum : (a.num.natAbs : Int) = a.num :=
    Int.natAbs_of_nonneg (Rat.num_nonneg.mpr ha)
  rw [← hnum]
  norm_cast
  simp [Nat.mul_comm]

private theorem invNatPow_le_rat_iff (a : Rat) (ha : 0 ≤ a) (b k : Nat)
    (hb : 0 < b) :
    (b : Rat) ^ (-(Int.ofNat k)) ≤ a ↔ a.den ≤ a.num.natAbs * b ^ k := by
  rw [Rat.zpow_neg]
  change ((b : Rat) ^ k)⁻¹ ≤ a ↔ a.den ≤ a.num.natAbs * b ^ k
  rw [Rat.le_iff]
  have hpow : 0 < b ^ k := Nat.pow_pos hb
  have hbne : b ≠ 0 := Nat.ne_of_gt hb
  have hpowNatNe : b ^ k ≠ 0 := Nat.ne_of_gt hpow
  have hpowInt : 0 < (b ^ k : Int) := by exact_mod_cast hpow
  have hpowNe : (b ^ k : Int) ≠ 0 := Int.ne_of_gt hpowInt
  have hnum : (a.num.natAbs : Int) = a.num :=
    Int.natAbs_of_nonneg (Rat.num_nonneg.mpr ha)
  simp only [Rat.num_inv, Rat.den_inv, Rat.num_pow, Rat.den_pow,
    Rat.num_natCast, Rat.den_natCast, Int.natCast_pow, Nat.one_pow]
  rw [Int.sign_eq_one_of_pos hpowInt]
  simp only [if_neg hpowNe, Int.natAbs_of_nonneg (Int.le_of_lt hpowInt),
    Int.one_mul, Int.natCast_one]
  rw [← hnum]
  norm_cast
  simp [hbne]

private theorem rat_lt_invNatPow_iff (a : Rat) (ha : 0 ≤ a) (b k : Nat)
    (hb : 0 < b) :
    a < (b : Rat) ^ (-(Int.ofNat k)) ↔ a.num.natAbs * b ^ k < a.den := by
  rw [Rat.zpow_neg]
  change a < ((b : Rat) ^ k)⁻¹ ↔ a.num.natAbs * b ^ k < a.den
  rw [Rat.lt_iff]
  have hpow : 0 < b ^ k := Nat.pow_pos hb
  have hbne : b ≠ 0 := Nat.ne_of_gt hb
  have hpowNatNe : b ^ k ≠ 0 := Nat.ne_of_gt hpow
  have hpowInt : 0 < (b ^ k : Int) := by exact_mod_cast hpow
  have hpowNe : (b ^ k : Int) ≠ 0 := Int.ne_of_gt hpowInt
  have hnum : (a.num.natAbs : Int) = a.num :=
    Int.natAbs_of_nonneg (Rat.num_nonneg.mpr ha)
  simp only [Rat.num_inv, Rat.den_inv, Rat.num_pow, Rat.den_pow,
    Rat.num_natCast, Rat.den_natCast, Int.natCast_pow, Nat.one_pow]
  rw [Int.sign_eq_one_of_pos hpowInt]
  simp only [if_neg hpowNe, Int.natAbs_of_nonneg (Int.le_of_lt hpowInt),
    Int.one_mul, Int.natCast_one]
  rw [← hnum]
  norm_cast
  simp [hbne]

structure mag_prop (r : radix) (x : R) where
  mag_val : Z
  mag_bound : x ≠ R0 →
    Rle (bpow r (Zsub mag_val (Zpos xH))) (Rabs x) ∧
      Rlt (Rabs x) (bpow r mag_val)

instance {r : radix} {x : R} (m : mag_prop r x) : CoeDep (mag_prop r x) m Z :=
  ⟨m.mag_val⟩

export mag_prop (mag_val)

def mag (r : radix) (x : R) : mag_prop r x :=
  let a := (Rabs x).value
  if hx0 : x = R0 then
    { mag_val := Zpos xH
      mag_bound := by intro hx; exact (hx hx0).elim }
  else
    have ha : 0 ≤ a := by
      dsimp [a]
      rw [Rabs_value_eq_abs]
      exact Rat.abs_nonneg
    have hane : a ≠ 0 := by
      dsimp [a]
      exact Rabs_value_ne_zero x hx0
    have hn : 0 < a.num.natAbs := Int.natAbs_pos.mpr <| by
      intro hnum
      apply hane
      exact Rat.num_eq_zero.mp hnum
    let b := radixNat r
    have hb : 1 < b := by
      dsimp [b]
      have := radixNat_ge_two r
      omega
    if hlarge : a.den ≤ a.num.natAbs then
      let q := highMagnitude b a.num.natAbs a.den hb a.den_pos
      { mag_val := CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat q.val)
        mag_bound := by
          intro _
          have hkpos : 0 < q.val := by
            apply Nat.pos_of_ne_zero
            intro hk0
            have hp := q.property
            simp [hk0] at hp
            omega
          have hlower : a.den * b ^ (q.val - 1) ≤ a.num.natAbs :=
            Nat.le_of_not_gt (q.minimal (q.val - 1) (by omega))
          constructor
          · change (bpow r (Zsub
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat q.val))
                (Zpos xH))).value ≤ a
            rw [zsub_zOfInt_one, bpow_zOfInt_value]
            have hi : Int.ofNat q.val - 1 = Int.ofNat (q.val - 1) := by
              symm
              exact Int.ofNat_sub (by omega : 1 ≤ q.val)
            rw [hi]
            change (b : Rat) ^ (q.val - 1) ≤ a
            exact (natPow_le_rat_iff a ha b (q.val - 1)).2 (by
              simpa [Nat.mul_comm] using hlower)
          · change a < (bpow r
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat q.val))).value
            rw [bpow_zOfInt_value]
            change a < (b : Rat) ^ q.val
            exact (rat_lt_natPow_iff a ha b q.val).2 q.property }
    else
      let q := lowMagnitude b a.num.natAbs a.den hb hn
      { mag_val := CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (-(Int.ofNat q.val))
        mag_bound := by
          intro _
          have hsmall : a.num.natAbs < a.den := Nat.lt_of_not_ge hlarge
          have hupper : a.num.natAbs * b ^ q.val < a.den := by
            cases hq : q.val with
            | zero => simpa [hq] using hsmall
            | succ k =>
                have hm := q.minimal k (by omega)
                have hm' : ¬a.den ≤ a.num.natAbs * b ^ (k + 1) := by
                  simpa [hq] using hm
                simpa [hq] using Nat.lt_of_not_ge hm'
          constructor
          · change (bpow r (Zsub
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (-(Int.ofNat q.val)))
                (Zpos xH))).value ≤ a
            rw [zsub_zOfInt_one, bpow_zOfInt_value]
            have hi : -(Int.ofNat q.val) - 1 = -(Int.ofNat (q.val + 1)) :=
              neg_ofNat_sub_one q.val
            rw [hi]
            exact (invNatPow_le_rat_iff a ha b (q.val + 1) (by omega)).2 q.property
          · change a < (bpow r
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (-(Int.ofNat q.val)))).value
            rw [bpow_zOfInt_value]
            exact (rat_lt_invNatPow_iff a ha b q.val (by omega)).2 hupper }

/-! The executable magnitude remains a runtime support operation.  The
    source-shaped exact magnitude is owned by `Exact.Magnitude`; this seam
    records the adapter obligation that later proof grinding must discharge
    for their magnitude projections to correspond. -/
def mag_runtime_exact_correspondence
    (ctx : Exact.Context) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (r : radix) (x : R),
    ∃ h : ctx.adapter.represented x,
      (Exact.mag magnitude r
        (ctx.adapter.operation ⟨x, h⟩)).mag_val =
        (mag r x).mag_val

def cond_Ropp (b : Bool) (m : R) : R := if b then Ropp m else m

noncomputable def LPO_min (P : Nat → Prop) (decideP : ∀ n, P n ∨ ¬ P n) :
    Sumor (Subtype (fun n => P n ∧ ∀ i, i < n → ¬ P i)) (∀ n, ¬ P n) := by
  classical
  have _decision_at_zero : P 0 ∨ ¬ P 0 := decideP 0
  by_cases h : ∃ n, P n
  · let first := firstNat P (Classical.choose h) (Classical.choose_spec h)
    exact .inleft ⟨first.val, first.property, first.minimal⟩
  · exact .inright (fun n hn => h ⟨n, hn⟩)

noncomputable def LPO (P : Nat → Prop) (decideP : ∀ n, P n ∨ ¬ P n) :
    Sumor (Subtype P) (∀ n, ¬ P n) :=
  match LPO_min P decideP with
  | .inleft witness => .inleft ⟨witness.val, witness.property.1⟩
  | .inright h => .inright h

private theorem zOfNat_toNat_eq_of_nonneg (z : Z)
    (h : 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
      (Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z)) = z := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
    Int.toNat_of_nonneg h]

private theorem zOppOfNat_toNat_neg_eq_of_neg (z : Z)
    (h : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z < 0) :
    Zopp (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
      (Int.toNat (-CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z))) = z := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp [Zopp, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
    Int.toNat_of_nonneg (Int.neg_nonneg.mpr (Int.le_of_lt h))]

noncomputable def LPO_Z (P : Z → Prop) (decideP : ∀ z, P z ∨ ¬ P z) :
    Sumor (Subtype P) (∀ z, ¬ P z) :=
  match LPO
      (fun n => P (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n))
      (fun n =>
        decideP (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)) with
  | .inleft witness =>
      .inleft
        ⟨CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat witness.val,
          witness.property⟩
  | .inright nonnegative =>
      match LPO
          (fun n => P (Zopp
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)))
          (fun n => decideP (Zopp
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n))) with
      | .inleft witness =>
          .inleft
            ⟨Zopp
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat witness.val),
              witness.property⟩
      | .inright negative => .inright (by
          intro z hz
          by_cases hsign : 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z
          · apply nonnegative (Int.toNat
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z))
            rw [zOfNat_toNat_eq_of_nonneg z hsign]
            exact hz
          · apply negative (Int.toNat
                (-CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z))
            rw [zOppOfNat_toNat_neg_eq_of_neg z (Int.lt_of_not_ge hsign)]
            exact hz)

/-! Exact source proposition descriptors for later proof migration. -/

section ExactStatements

variable (ctx : ExactRealContext)
variable (m : Exact.Magnitude ctx)

local notation "R" => Exact.R ctx
local notation "IZR" => Exact.IZR ctx
local notation "R0" => Exact.R0 ctx
local notation "Rone" => Exact.Rone ctx
local notation "Rtwo" => Exact.Rtwo ctx
local notation "Rhalf" => Exact.Rhalf ctx
local notation "Ropp" => Exact.Ropp ctx
local notation "Rplus" => Exact.Rplus ctx
local notation "Rminus" => Exact.Rminus ctx
local notation "Rmult" => Exact.Rmult ctx
local notation "Rdiv" => Exact.Rdiv ctx
local notation "Rinv" => Exact.Rinv ctx
local notation "Rlt" => Exact.Rlt ctx
local notation "Rle" => Exact.Rle ctx
local notation "Rge" => Exact.Rge ctx
local notation "Rgt" => Exact.Rgt ctx
local notation "Rabs" => Exact.Rabs ctx
local notation "Rmin" => Exact.Rmin ctx
local notation "Rsqr" => Exact.Rsqr ctx
local notation "sqrt" => Exact.sqrt ctx
local notation "exp" => Exact.exp ctx
local notation "ln" => Exact.ln ctx
local notation "powerRZ" => Exact.powerRZ ctx
local notation "up" => Exact.up ctx
local notation "cond_Ropp" => Exact.cond_Ropp ctx
local notation "Rcompare" => Exact.Rcompare ctx
local notation "Rcompare_prop" => Exact.Rcompare_prop ctx
local notation "Rle_bool" => Exact.Rle_bool ctx
local notation "Rle_bool_prop" => Exact.Rle_bool_prop ctx
local notation "Rlt_bool" => Exact.Rlt_bool ctx
local notation "Rlt_bool_prop" => Exact.Rlt_bool_prop ctx
local notation "Req_bool" => Exact.Req_bool ctx
local notation "Req_bool_prop" => Exact.Req_bool_prop ctx
local notation "Zfloor" => Exact.Zfloor ctx
local notation "Zceil" => Exact.Zceil ctx
local notation "Ztrunc" => Exact.Ztrunc ctx
local notation "Zaway" => Exact.Zaway ctx
local notation "bpow" => Exact.bpow ctx
local notation "mag" => Exact.mag m
local notation "mag_val" => Exact.MagnitudeValue.mag_val

def IZR_Zpower_posStatement : Prop :=
  ∀ (n : Z) (m : positive),
    IZR (Zpower_pos n m) = powerRZ (IZR n) (Zpos m)

def IZR_ZpowerStatement : Prop :=
  ∀ (r : radix) (e : Z), Zle Z0 e → IZR (Zpower r e) = bpow r e

def IZR_cond_ZoppStatement : Prop :=
  ∀ (b : Bool) (m : Z), IZR (cond_Zopp b m) = cond_Ropp b (IZR m)

def LPO_minStatement : Type :=
  ∀ P : Nat → Prop, (∀ n, P n ∨ ¬ P n) →
    Sumor (Subtype (fun n => P n ∧ ∀ i, i < n → ¬ P i)) (∀ n, ¬ P n)

def LPOStatement : Type :=
  ∀ P : Nat → Prop, (∀ n, P n ∨ ¬ P n) →
    Sumor (Subtype P) (∀ n, ¬ P n)

def LPO_ZStatement : Type :=
  ∀ P : Z → Prop, (∀ n, P n ∨ ¬ P n) →
    Sumor (Subtype P) (∀ n, ¬ P n)

def Rabs_ltStatement : Prop :=
  ∀ x y : R, (Rlt (Ropp y) x ∧ Rlt x y) → Rlt (Rabs x) y

def Rabs_lt_invStatement : Prop :=
  ∀ x y : R, Rlt (Rabs x) y → Rlt (Ropp y) x ∧ Rlt x y

def Rcompare_specStatement : Prop :=
  ∀ x y : R, Rcompare_prop x y (Rcompare x y)

def Rcompare_LtStatement : Prop :=
  ∀ x y : R, Rlt x y → Rcompare x y = Lt

def Rcompare_Lt_invStatement : Prop :=
  ∀ x y : R, Rcompare x y = Lt → Rlt x y

def Rcompare_not_LtStatement : Prop :=
  ∀ x y : R, Rle y x → Rcompare x y ≠ Lt

def Rcompare_not_Lt_invStatement : Prop :=
  ∀ x y : R, Rcompare x y ≠ Lt → Rle y x

def Rcompare_EqStatement : Prop :=
  ∀ x y : R, x = y → Rcompare x y = Eq

def Rcompare_Eq_invStatement : Prop :=
  ∀ x y : R, Rcompare x y = Eq → x = y

def Rcompare_GtStatement : Prop :=
  ∀ x y : R, Rlt y x → Rcompare x y = Gt

def Rcompare_Gt_invStatement : Prop :=
  ∀ x y : R, Rcompare x y = Gt → Rlt y x

def Rcompare_IZRStatement : Prop :=
  ∀ x y : Z, Rcompare (IZR x) (IZR y) = Zcompare x y

def Rcompare_symStatement : Prop :=
  ∀ x y : R, Rcompare x y = CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp (Rcompare y x)

def Rcompare_oppStatement : Prop :=
  ∀ x y : R, Rcompare (Ropp x) (Ropp y) = Rcompare y x

def Rcompare_plus_rStatement : Prop :=
  ∀ z x y : R, Rcompare (Rplus x z) (Rplus y z) = Rcompare x y

def Rcompare_plus_lStatement : Prop :=
  ∀ z x y : R, Rcompare (Rplus z x) (Rplus z y) = Rcompare x y

def Rcompare_mult_rStatement : Prop :=
  ∀ z x y : R, Rlt R0 z → Rcompare (Rmult x z) (Rmult y z) = Rcompare x y

def Rcompare_mult_lStatement : Prop :=
  ∀ z x y : R, Rlt R0 z → Rcompare (Rmult z x) (Rmult z y) = Rcompare x y

def Rcompare_half_lStatement : Prop :=
  ∀ x y : R, Rcompare (Rdiv x Rtwo) y = Rcompare x (Rmult Rtwo y)

def Rcompare_half_rStatement : Prop :=
  ∀ x y : R, Rcompare x (Rdiv y Rtwo) = Rcompare (Rmult Rtwo x) y

def Rcompare_sqrStatement : Prop :=
  ∀ x y : R, Rcompare (Rmult x x) (Rmult y y) = Rcompare (Rabs x) (Rabs y)

def Rcompare_floor_ceil_middleStatement : Prop :=
  ∀ x : R, IZR (Zfloor x) ≠ x →
    Rcompare (Rminus x (IZR (Zfloor x))) Rhalf =
      Rcompare (Rminus x (IZR (Zfloor x))) (Rminus (IZR (Zceil x)) x)

def Rcompare_ceil_floor_middleStatement : Prop :=
  ∀ x : R, IZR (Zfloor x) ≠ x →
    Rcompare (Rminus (IZR (Zceil x)) x) Rhalf =
      Rcompare (Rminus (IZR (Zceil x)) x) (Rminus x (IZR (Zfloor x)))

def Req_bool_specStatement : Prop :=
  ∀ x y : R, Req_bool_prop x y (Req_bool x y)

def Rle_0_minusStatement : Prop :=
  ∀ x y : R, Rle x y → Rle R0 (Rminus y x)

def Rinv_leStatement : Prop :=
  ∀ x y : R, Rlt R0 x → Rle x y → Rle (Rinv y) (Rinv x)

def Rle_bool_specStatement : Prop :=
  ∀ x y : R, Rle_bool_prop x y (Rle_bool x y)

def Rle_bool_trueStatement : Prop :=
  ∀ x y : R, Rle x y → Rle_bool x y = true

def Rle_bool_falseStatement : Prop :=
  ∀ x y : R, Rlt y x → Rle_bool x y = false

def Rlt_bool_specStatement : Prop :=
  ∀ x y : R, Rlt_bool_prop x y (Rlt_bool x y)

def negb_Rlt_boolStatement : Prop :=
  ∀ x y : R, Bool.not (Rle_bool x y) = Rlt_bool y x

def Rlt_bool_trueStatement : Prop :=
  ∀ x y : R, Rlt x y → Rlt_bool x y = true

def Rlt_bool_falseStatement : Prop :=
  ∀ x y : R, Rle y x → Rlt_bool x y = false

def Zfloor_lbStatement : Prop :=
  ∀ x : R, Rle (IZR (Zfloor x)) x

def Zfloor_ubStatement : Prop :=
  ∀ x : R, Rlt x (Rplus (IZR (Zfloor x)) Rone)

def Zfloor_lubStatement : Prop :=
  ∀ (n : Z) (x : R), Rle (IZR n) x → Zle n (Zfloor x)

def Zfloor_impStatement : Prop :=
  ∀ (n : Z) (x : R),
    Rle (IZR n) x ∧ Rlt x (IZR (Zadd n (Zpos xH))) → Zfloor x = n

def Zfloor_IZRStatement : Prop :=
  ∀ n : Z, Zfloor (IZR n) = n

def Zfloor_leStatement : Prop :=
  ∀ x y : R, Rle x y → Zle (Zfloor x) (Zfloor y)

def Zceil_ubStatement : Prop :=
  ∀ x : R, Rle x (IZR (Zceil x))

def Zceil_glbStatement : Prop :=
  ∀ (n : Z) (x : R), Rle x (IZR n) → Zle (Zceil x) n

def Zceil_impStatement : Prop :=
  ∀ (n : Z) (x : R),
    Rlt (IZR (Zsub n (Zpos xH))) x ∧ Rle x (IZR n) → Zceil x = n

def Zceil_IZRStatement : Prop :=
  ∀ n : Z, Zceil (IZR n) = n

def Zceil_leStatement : Prop :=
  ∀ x y : R, Rle x y → Zle (Zceil x) (Zceil y)

def Zceil_floor_neqStatement : Prop :=
  ∀ x : R, IZR (Zfloor x) ≠ x → Zceil x = Zadd (Zfloor x) (Zpos xH)

def Ztrunc_IZRStatement : Prop :=
  ∀ n : Z, Ztrunc (IZR n) = n

def Ztrunc_floorStatement : Prop :=
  ∀ x : R, Rle R0 x → Ztrunc x = Zfloor x

def Ztrunc_ceilStatement : Prop :=
  ∀ x : R, Rle x R0 → Ztrunc x = Zceil x

def Ztrunc_oppStatement : Prop :=
  ∀ x : R, Ztrunc (Ropp x) = Zopp (Ztrunc x)

def Ztrunc_absStatement : Prop :=
  ∀ x : R, Ztrunc (Rabs x) = Zabs (Ztrunc x)

def Zfloor_divStatement : Prop :=
  ∀ (x y : Z), y ≠ Z0 → Zfloor (Rdiv (IZR x) (IZR y)) = Zdiv x y

def Zaway_ceilStatement : Prop :=
  ∀ x : R, Rle R0 x → Zaway x = Zceil x

def Zaway_floorStatement : Prop :=
  ∀ x : R, Rle x R0 → Zaway x = Zfloor x

def Zaway_oppStatement : Prop :=
  ∀ x : R, Zaway (Ropp x) = Zopp (Zaway x)

def radix_posStatement : Prop :=
  ∀ r : radix, Rlt R0 (IZR r)

def bpow_powerRZStatement : Prop :=
  ∀ (r : radix) (e : Z), bpow r e = powerRZ (IZR r) e

def bpow_ge_0Statement : Prop :=
  ∀ (r : radix) (e : Z), Rle R0 (bpow r e)

def bpow_gt_0Statement : Prop :=
  ∀ (r : radix) (e : Z), Rlt R0 (bpow r e)

def bpow_plusStatement : Prop :=
  ∀ (r : radix) (e1 e2 : Z),
    bpow r (Zadd e1 e2) = Rmult (bpow r e1) (bpow r e2)

def bpow_oppStatement : Prop :=
  ∀ (r : radix) (e : Z), bpow r (Zopp e) = Rinv (bpow r e)

def bpow_expStatement : Prop :=
  ∀ (r : radix) (e : Z),
    bpow r e = exp (Rmult (IZR e) (ln (IZR r)))

def bpow_ltStatement : Prop :=
  ∀ (r : radix) (e1 e2 : Z), Zlt e1 e2 → Rlt (bpow r e1) (bpow r e2)

def lt_bpowStatement : Prop :=
  ∀ (r : radix) (e1 e2 : Z), Rlt (bpow r e1) (bpow r e2) → Zlt e1 e2

def bpow_leStatement : Prop :=
  ∀ (r : radix) (e1 e2 : Z), Zle e1 e2 → Rle (bpow r e1) (bpow r e2)

def le_bpowStatement : Prop :=
  ∀ (r : radix) (e1 e2 : Z), Rle (bpow r e1) (bpow r e2) → Zle e1 e2

def bpow_lt_bpowStatement : Prop :=
  ∀ (r : radix) (e1 e2 : Z),
    Rlt (bpow r (Zsub e1 (Zpos xH))) (bpow r e2) → Zle e1 e2

def bpow_uniqueStatement : Prop :=
  ∀ (r : radix) (x : R) (e1 e2 : Z),
    (Rle (bpow r (Zsub e1 (Zpos xH))) x ∧ Rlt x (bpow r e1)) →
    (Rle (bpow r (Zsub e2 (Zpos xH))) x ∧ Rlt x (bpow r e2)) → e1 = e2

def mag_uniqueStatement : Prop :=
  ∀ (r : radix) (x : R) (e : Z),
    (Rle (bpow r (Zsub e (Zpos xH))) (Rabs x) ∧ Rlt (Rabs x) (bpow r e)) →
    mag_val (mag r x) = e

def mag_oppStatement : Prop :=
  ∀ (r : radix) (x : R), mag_val (mag r (Ropp x)) = mag_val (mag r x)

def mag_absStatement : Prop :=
  ∀ (r : radix) (x : R), mag_val (mag r (Rabs x)) = mag_val (mag r x)

def mag_unique_posStatement : Prop :=
  ∀ (r : radix) (x : R) (e : Z),
    (Rle (bpow r (Zsub e (Zpos xH))) x ∧ Rlt x (bpow r e)) →
    mag_val (mag r x) = e

def mag_le_absStatement : Prop :=
  ∀ (r : radix) (x y : R), x ≠ R0 → Rle (Rabs x) (Rabs y) →
    Zle (mag_val (mag r x)) (mag_val (mag r y))

def mag_leStatement : Prop :=
  ∀ (r : radix) (x y : R), Rlt R0 x → Rle x y →
    Zle (mag_val (mag r x)) (mag_val (mag r y))

def lt_magStatement : Prop :=
  ∀ (r : radix) (x y : R), Rlt R0 y →
    Zlt (mag_val (mag r x)) (mag_val (mag r y)) → Rlt x y

def mag_bpowStatement : Prop :=
  ∀ (r : radix) (e : Z), mag_val (mag r (bpow r e)) = Zadd e (Zpos xH)

def mag_mult_bpowStatement : Prop :=
  ∀ (r : radix) (x : R) (e : Z), x ≠ R0 →
    mag_val (mag r (Rmult x (bpow r e))) = Zadd (mag_val (mag r x)) e

def mag_le_bpowStatement : Prop :=
  ∀ (r : radix) (x : R) (e : Z), x ≠ R0 → Rlt (Rabs x) (bpow r e) →
    Zle (mag_val (mag r x)) e

def mag_gt_bpowStatement : Prop :=
  ∀ (r : radix) (x : R) (e : Z), Rle (bpow r e) (Rabs x) →
    Zlt e (mag_val (mag r x))

def mag_ge_bpowStatement : Prop :=
  ∀ (r : radix) (x : R) (e : Z), Rle (bpow r (Zsub e (Zpos xH))) (Rabs x) →
    Zle e (mag_val (mag r x))

def mag_le_ZpowerStatement : Prop :=
  ∀ (r : radix) (m e : Z), m ≠ Z0 → Zlt (Zabs m) (Zpower r e) →
    Zle (mag_val (mag r (IZR m))) e

def mag_divStatement : Prop :=
  ∀ (r : radix) (x y : R), x ≠ R0 → y ≠ R0 →
    Zle (Zsub (mag_val (mag r x)) (mag_val (mag r y)))
      (mag_val (mag r (Rdiv x y))) ∧
    Zle (mag_val (mag r (Rdiv x y)))
      (Zadd (Zsub (mag_val (mag r x)) (mag_val (mag r y))) (Zpos xH))

def mag_sqrtStatement : Prop :=
  ∀ (r : radix) (x : R), Rlt R0 x →
    mag_val (mag r (sqrt x)) = Zdiv2 (Zadd (mag_val (mag r x)) (Zpos xH))

def exp_leStatement : Prop :=
  ∀ x y : R, Rle x y → Rle (exp x) (exp y)

def eqb_symStatement : Prop :=
  ∀ x y : Bool, bool_eqb x y = bool_eqb y x

def eqb_trueStatement : Prop :=
  ∀ x y : Bool, x = y → bool_eqb x y = true

def abs_cond_RoppStatement : Prop :=
  ∀ (b : Bool) (m : R), Rabs (cond_Ropp b m) = Rabs m

def cond_Ropp_mult_lStatement : Prop :=
  ∀ (b : Bool) (x y : R),
    cond_Ropp b (Rmult x y) = Rmult (cond_Ropp b x) y

def sqrt_ge_0Statement : Prop :=
  ∀ x : R, Rle R0 (sqrt x)

def Req_bool_falseStatement : Prop :=
  ∀ x y : R, x ≠ y → Req_bool x y = false

def Req_bool_trueStatement : Prop :=
  ∀ x y : R, x = y → Req_bool x y = true

def Rmin_compareStatement : Prop :=
  ∀ x y : R,
    Rmin x y = match Rcompare x y with
      | .Lt => x
      | .Eq => x
      | .Gt => y

def Rmult_min_distr_rStatement : Prop :=
  ∀ (r r1 r2 : R),
    Rle R0 r →
      Rmult (Rmin r1 r2) r = Rmin (Rmult r1 r) (Rmult r2 r)

def Rmult_neq_compat_rStatement : Prop :=
  ∀ (r1 r2 r3 : R), r1 ≠ R0 → r2 ≠ r3 → Rmult r2 r1 ≠ Rmult r3 r1

def bpow_injStatement : Prop :=
  ∀ (r : radix) (e1 e2 : Z), bpow r e1 = bpow r e2 → e1 = e2

end ExactStatements

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem sqrt_ge_0 (ctx : ExactRealContext) : sqrt_ge_0Statement ctx := by
  intro x
  change ctx.spec.le ctx.spec.zero
    (CompCert4Lean.Foundation.FlocqReal.ExactReal.sqrt ctx.spec x)
  unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.sqrt
  split
  · exact ctx.certificate.orderedField.le_refl ctx.spec.zero
  · exact ctx.certificate.sqrt.nonnegative x

theorem Req_bool_true (ctx : ExactRealContext) : Req_bool_trueStatement ctx := by
  intro x y hxy
  subst y
  change Exact.Req_bool ctx x x = true
  cases hdec : ctx.spec.lt_dec x x with
  | left hlt => exact (ctx.certificate.orderedField.lt_irrefl x hlt).elim
  | right _ =>
      simp [Exact.Req_bool, Exact.Rcompare,
        CompCert4Lean.Foundation.FlocqReal.ExactReal.total_order_T, hdec]

private theorem exact_zero_lt_one_aux (ctx : ExactRealContext) :
    ctx.spec.lt ctx.spec.zero ctx.spec.one := by
  rcases ctx.certificate.total_order ctx.spec.zero ctx.spec.one with h | h
  · rcases h with hlt | heq
    · exact hlt
    · exact (ctx.certificate.orderedField.zero_ne_one heq).elim
  · have hzero_lt_neg : ctx.spec.lt ctx.spec.zero (ctx.spec.neg ctx.spec.one) := by
      have hadd := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.neg ctx.spec.one) ctx.spec.one ctx.spec.zero h
      rw [ctx.certificate.orderedField.neg_add_cancel,
        ctx.certificate.orderedField.add_zero] at hadd
      exact hadd
    have hneg_lt_zero := ctx.certificate.orderedField.mul_lt_compat_l
      (ctx.spec.neg ctx.spec.one) ctx.spec.one ctx.spec.zero hzero_lt_neg h
    rw [ctx.certificate.orderedField.mul_one,
      ctx.certificate.orderedField.mul_zero] at hneg_lt_zero
    exact (ctx.certificate.orderedField.lt_irrefl ctx.spec.zero
      (ctx.certificate.orderedField.lt_trans ctx.spec.zero (ctx.spec.neg ctx.spec.one)
        ctx.spec.zero hzero_lt_neg hneg_lt_zero)).elim

private theorem exact_Rcompare_lt_aux (ctx : ExactRealContext)
    {x y : ctx.spec.carrier} (hxy : ctx.spec.lt x y) :
    Exact.Rcompare ctx x y = Lt := by
  unfold Exact.Rcompare
  unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.total_order_T
  cases hdec : ctx.spec.lt_dec x y with
  | left _ => rfl
  | right hnxy => exact (hnxy hxy).elim

private theorem exact_Rcompare_eq_aux (ctx : ExactRealContext)
    {x y : ctx.spec.carrier} (hxy : x = y) :
    Exact.Rcompare ctx x y = Eq := by
  subst y
  cases hdec : ctx.spec.lt_dec x x with
  | left hlt => exact (ctx.certificate.orderedField.lt_irrefl x hlt).elim
  | right _ =>
      simp [Exact.Rcompare,
        CompCert4Lean.Foundation.FlocqReal.ExactReal.total_order_T, hdec]

private theorem exact_Rcompare_gt_aux (ctx : ExactRealContext)
    {x y : ctx.spec.carrier} (hyx : ctx.spec.lt y x) :
    Exact.Rcompare ctx x y = Gt := by
  have hnxy : ¬ctx.spec.lt x y := by
    intro hxy
    exact ctx.certificate.orderedField.lt_irrefl x
      (ctx.certificate.orderedField.lt_trans x y x hxy hyx)
  unfold Exact.Rcompare
  unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.total_order_T
  cases hxy : ctx.spec.lt_dec x y with
  | left hlt => exact (hnxy hlt).elim
  | right _ =>
      cases hyx_dec : ctx.spec.lt_dec y x with
      | left _ => rfl
      | right hnyx => exact (hnyx hyx).elim

private theorem exact_Rcompare_mul_pos_right_aux (ctx : ExactRealContext)
    (z x y : ctx.spec.carrier) (hz : ctx.spec.lt ctx.spec.zero z) :
    Exact.Rcompare ctx (ctx.spec.mul x z) (ctx.spec.mul y z) =
      Exact.Rcompare ctx x y := by
  rcases ctx.certificate.total_order x y with h | h
  · rcases h with hlt | heq
    · have hmul := ctx.certificate.orderedField.mul_lt_compat_l z x y hz hlt
      rw [ctx.certificate.orderedField.mul_comm z x,
        ctx.certificate.orderedField.mul_comm z y] at hmul
      rw [exact_Rcompare_lt_aux ctx hmul, exact_Rcompare_lt_aux ctx hlt]
    · subst y
      rw [exact_Rcompare_eq_aux ctx rfl, exact_Rcompare_eq_aux ctx rfl]
  · have hmul := ctx.certificate.orderedField.mul_lt_compat_l z y x hz h
    rw [ctx.certificate.orderedField.mul_comm z y,
      ctx.certificate.orderedField.mul_comm z x] at hmul
    rw [exact_Rcompare_gt_aux ctx hmul, exact_Rcompare_gt_aux ctx h]

theorem Rcompare_half_r (ctx : ExactRealContext) : Rcompare_half_rStatement ctx := by
  intro x y
  change Exact.Rcompare ctx x (ctx.spec.div y (ctx.spec.add ctx.spec.one ctx.spec.one)) =
    Exact.Rcompare ctx (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one) x) y
  have hone_pos := exact_zero_lt_one_aux ctx
  have hone_lt_two := ctx.certificate.orderedField.add_lt_compat_l ctx.spec.one
    ctx.spec.zero ctx.spec.one hone_pos
  rw [ctx.certificate.orderedField.add_zero] at hone_lt_two
  have htwo_pos := ctx.certificate.orderedField.lt_trans ctx.spec.zero ctx.spec.one
    (ctx.spec.add ctx.spec.one ctx.spec.one) hone_pos hone_lt_two
  have htwo_ne : ctx.spec.add ctx.spec.one ctx.spec.one ≠ ctx.spec.zero := by
    intro heq
    rw [heq] at htwo_pos
    exact ctx.certificate.orderedField.lt_irrefl ctx.spec.zero htwo_pos
  have hdivmul :
      ctx.spec.mul (ctx.spec.div y (ctx.spec.add ctx.spec.one ctx.spec.one))
          (ctx.spec.add ctx.spec.one ctx.spec.one) = y := by
    rw [ctx.certificate.orderedField.div_eq_mul_inv,
      ctx.certificate.orderedField.mul_assoc,
      ctx.certificate.orderedField.inv_mul_cancel _ htwo_ne,
      ctx.certificate.orderedField.mul_one]
  have hcmp := exact_Rcompare_mul_pos_right_aux ctx
    (ctx.spec.add ctx.spec.one ctx.spec.one) x
    (ctx.spec.div y (ctx.spec.add ctx.spec.one ctx.spec.one)) htwo_pos
  calc
    Exact.Rcompare ctx x (ctx.spec.div y (ctx.spec.add ctx.spec.one ctx.spec.one)) =
        Exact.Rcompare ctx
          (ctx.spec.mul x (ctx.spec.add ctx.spec.one ctx.spec.one))
          (ctx.spec.mul (ctx.spec.div y (ctx.spec.add ctx.spec.one ctx.spec.one))
            (ctx.spec.add ctx.spec.one ctx.spec.one)) := hcmp.symm
    _ = Exact.Rcompare ctx
          (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one) x) y := by
      rw [ctx.certificate.orderedField.mul_comm x,
        hdivmul]

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

private theorem exact_IZR_ofNat_pos_aux (ctx : ExactRealContext) :
    ∀ n : Nat, ctx.spec.lt ctx.spec.zero
      (CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR ctx.spec
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (n + 1))) := by
  intro n
  induction n with
  | zero =>
      have honez :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1 =
            Zpos xH := by
        rfl
      have hone := exact_zero_lt_one_aux ctx
      change ctx.spec.lt ctx.spec.zero
        (ctx.spec.ofZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1))
      rw [honez, ctx.certificate.sourceLaws.ofZ_one]
      exact hone
  | succ n ih =>
      have hzn :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (n + 2) =
            Zadd (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (n + 1))
              (Zpos xH) := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add]
        repeat rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        have hone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos xH) = 1 := rfl
        rw [hone]
        change Int.ofNat (n + 2) = Int.ofNat (n + 1) + Int.ofNat 1
        calc
          Int.ofNat (n + 2) = Int.ofNat ((n + 1) + 1) := by congr 1 <;> omega
          _ = Int.ofNat (n + 1) + Int.ofNat 1 := Int.ofNat_add_ofNat _ _ |>.symm
      change ctx.spec.lt ctx.spec.zero
        (ctx.spec.ofZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (n + 2)))
      rw [hzn, ctx.certificate.sourceLaws.ofZ_add,
        ctx.certificate.sourceLaws.ofZ_one]
      have hone := exact_zero_lt_one_aux ctx
      have h := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.ofZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (n + 1)))
        ctx.spec.zero ctx.spec.one hone
      rw [ctx.certificate.orderedField.add_zero] at h
      exact ctx.certificate.orderedField.lt_trans _ _ _ ih h

private theorem exact_radix_pos_aux (ctx : ExactRealContext) (r : radix) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ r.radix_val) := by
  have hradix := r.radix_prop
  have hr : (2 : Int) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val := by
    change (if
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.xO
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH)) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val then true else false) = true at hradix
    have : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.xO
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH)) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val := by
      simpa using hradix
    simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat] using this
  have hnotzero : r.radix_val ≠ Z0 := by
    intro h
    rw [h] at hr
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at hr
  cases hval : r.radix_val with
  | Z0 => exact (hnotzero hval).elim
  | Zneg p =>
      rw [hval] at hr
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at hr
      omega
  | Zpos p =>
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hrepr :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p =
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) := by
        exact (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt_intOfZ _).symm
      change ctx.spec.lt ctx.spec.zero
        (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))
      rw [hrepr]
      have hp' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p - 1 + 1 =
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p := by omega
      rw [← hp']
      exact exact_IZR_ofNat_pos_aux ctx
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p - 1)

private theorem exact_IZR_pos_aux (ctx : ExactRealContext) (z : Z)
    (hz : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ z) := by
  have hn : 0 < Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z) := by
    apply (Int.ofNat_lt).mp
    rw [Int.toNat_of_nonneg (Int.le_of_lt hz)]
    simpa using hz
  have hrepr :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z)) = z := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat]
    exact (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt _).trans
      (Int.toNat_of_nonneg (Int.le_of_lt hz))
  rw [← hrepr]
  have hstep : Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z) - 1 + 1 =
      Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z) := by
    omega
  rw [← hstep]
  exact exact_IZR_ofNat_pos_aux ctx
    (Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z) - 1)

private theorem radix_int_ge_two_aux (r : radix) : (2 : Int) ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val := by
  have hradix := r.radix_prop
  change (if
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.xO
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH)) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val then true else false) = true at hradix
  have : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.xO
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH)) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val := by
    simpa using hradix
  simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat] using this

private theorem exact_Zpower_pos_aux (ctx : ExactRealContext) (r : radix) (p : positive) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ (Zpower_pos r.radix_val p)) := by
  apply exact_IZR_pos_aux
  change 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (Int.pow (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)))
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  apply Int.pow_pos
  exact Int.lt_of_lt_of_le (by omega) (radix_int_ge_two_aux r)

private theorem exact_inv_pos_aux (ctx : ExactRealContext) {x : ctx.spec.carrier}
    (hx : ctx.spec.lt ctx.spec.zero x) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.inv x) := by
  have hxne : x ≠ ctx.spec.zero := by
    intro h
    rw [h] at hx
    exact ctx.certificate.orderedField.lt_irrefl ctx.spec.zero hx
  rcases ctx.certificate.total_order ctx.spec.zero (ctx.spec.inv x) with h | h
  · rcases h with hpos | hzero
    · exact hpos
    · have hinv : ctx.spec.mul (ctx.spec.inv x) x = ctx.spec.one :=
        ctx.certificate.orderedField.inv_mul_cancel x hxne
      rw [← hzero, ctx.certificate.orderedField.zero_mul] at hinv
      exact (ctx.certificate.orderedField.zero_ne_one hinv).elim
  · have hmul := ctx.certificate.orderedField.mul_lt_compat_l x
      (ctx.spec.inv x) ctx.spec.zero hx h
    rw [ctx.certificate.orderedField.mul_comm x (ctx.spec.inv x),
      ctx.certificate.orderedField.inv_mul_cancel x hxne,
      ctx.certificate.orderedField.mul_zero] at hmul
    have hone := exact_zero_lt_one_aux ctx
    exact (ctx.certificate.orderedField.lt_irrefl ctx.spec.zero
      (ctx.certificate.orderedField.lt_trans ctx.spec.zero ctx.spec.one
        ctx.spec.zero hone hmul)).elim

theorem bpow_gt_0 (ctx : ExactRealContext) : bpow_gt_0Statement ctx := by
  intro r e
  cases e with
  | Z0 =>
      change ctx.spec.lt ctx.spec.zero ctx.spec.one
      exact exact_zero_lt_one_aux ctx
  | Zpos p =>
      change ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ (Zpower_pos r.radix_val p))
      exact exact_Zpower_pos_aux ctx r p
  | Zneg p =>
      change ctx.spec.lt ctx.spec.zero (ctx.spec.inv (ctx.spec.ofZ (Zpower_pos r.radix_val p)))
      exact exact_inv_pos_aux ctx (exact_Zpower_pos_aux ctx r p)

theorem bpow_ge_0 (ctx : ExactRealContext) : bpow_ge_0Statement ctx := by
  intro r e
  exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp
    (bpow_gt_0 ctx r e)).1

private theorem exact_ofZ_lt_aux (ctx : ExactRealContext) {x y : Z}
    (hxy : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y) :
    ctx.spec.lt (ctx.spec.ofZ x) (ctx.spec.ofZ y) := by
  let d := Zsub y x
  have hsum : y = Zadd x d := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [d, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    omega
  have hd : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d := by
    simp only [d, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    omega
  have hdpos := exact_IZR_pos_aux ctx d hd
  rw [hsum, ctx.certificate.sourceLaws.ofZ_add]
  have hadd := ctx.certificate.orderedField.add_lt_compat_l
    (ctx.spec.ofZ x) ctx.spec.zero (ctx.spec.ofZ d) hdpos
  rw [ctx.certificate.orderedField.add_zero] at hadd
  exact hadd

theorem Rcompare_IZR (ctx : ExactRealContext) : Rcompare_IZRStatement ctx := by
  intro x y
  change Exact.Rcompare ctx (ctx.spec.ofZ x) (ctx.spec.ofZ y) = Zcompare x y
  by_cases hxy : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y
  · rw [exact_Rcompare_lt_aux ctx (exact_ofZ_lt_aux ctx hxy)]
    change Lt = (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y then Lt else
      if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y then Eq else Gt)
    rw [if_pos hxy]
  by_cases hyx : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x
  · rw [exact_Rcompare_gt_aux ctx (exact_ofZ_lt_aux ctx hyx)]
    change Gt = (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y then Lt else
      if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y then Eq else Gt)
    rw [if_neg hxy, if_neg (by omega)]
  · have heq : x = y := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      omega
    subst y
    rw [exact_Rcompare_eq_aux ctx rfl]
    change Eq = (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x then Lt else
      if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x then Eq else Gt)
    rw [if_neg hxy, if_pos rfl]

private theorem exact_neg_mul_neg_aux (ctx : ExactRealContext) (x : ctx.spec.carrier) :
    ctx.spec.mul (ctx.spec.neg x) (ctx.spec.neg x) = ctx.spec.mul x x := by
  have h1 := ctx.certificate.orderedField.left_distrib
    (ctx.spec.neg x) (ctx.spec.neg x) x
  rw [ctx.certificate.orderedField.neg_add_cancel,
    ctx.certificate.orderedField.mul_zero] at h1
  have h2 := ctx.certificate.orderedField.left_distrib
    x (ctx.spec.neg x) x
  rw [ctx.certificate.orderedField.neg_add_cancel,
    ctx.certificate.orderedField.mul_zero,
    ctx.certificate.orderedField.mul_comm x (ctx.spec.neg x)] at h2
  calc
    ctx.spec.mul (ctx.spec.neg x) (ctx.spec.neg x) =
        ctx.spec.add (ctx.spec.mul (ctx.spec.neg x) (ctx.spec.neg x)) ctx.spec.zero :=
      (ctx.certificate.orderedField.add_zero _).symm
    _ = ctx.spec.add (ctx.spec.mul (ctx.spec.neg x) (ctx.spec.neg x))
        (ctx.spec.add (ctx.spec.mul (ctx.spec.neg x) x) (ctx.spec.mul x x)) := by rw [h2]
    _ = ctx.spec.add
        (ctx.spec.add (ctx.spec.mul (ctx.spec.neg x) (ctx.spec.neg x))
          (ctx.spec.mul (ctx.spec.neg x) x)) (ctx.spec.mul x x) := by
      rw [ctx.certificate.orderedField.add_assoc]
    _ = ctx.spec.add ctx.spec.zero (ctx.spec.mul x x) := by rw [h1]
    _ = ctx.spec.mul x x := ctx.certificate.orderedField.zero_add _

private theorem exact_sq_abs_eq_aux (ctx : ExactRealContext) (x : ctx.spec.carrier) :
    ctx.spec.mul x x = ctx.spec.mul (ctx.spec.abs x) (ctx.spec.abs x) := by
  rcases ctx.certificate.total_order x ctx.spec.zero with h | h
  · rcases h with hneg | hzero
    · rw [ctx.certificate.sourceLaws.abs_negative x hneg,
        exact_neg_mul_neg_aux ctx x]
    · have hle : ctx.spec.le ctx.spec.zero x := by
        rw [hzero]
        exact ctx.certificate.orderedField.le_refl _
      rw [ctx.certificate.sourceLaws.abs_nonnegative x hle]
  · have hle : ctx.spec.le ctx.spec.zero x :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp h).1
    rw [ctx.certificate.sourceLaws.abs_nonnegative x hle]

private theorem exact_abs_nonneg_aux (ctx : ExactRealContext) (x : ctx.spec.carrier) :
    ctx.spec.le ctx.spec.zero (ctx.spec.abs x) := by
  rcases ctx.certificate.total_order x ctx.spec.zero with h | h
  · rcases h with hneg | hzero
    · rw [ctx.certificate.sourceLaws.abs_negative x hneg]
      rcases ctx.certificate.total_order ctx.spec.zero (ctx.spec.neg x) with h' | h'
      · rcases h' with h' | h'
        · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp h').1
        · rw [← h']
          exact ctx.certificate.orderedField.le_refl _
      · have hsum := ctx.certificate.orderedField.add_lt_compat_l x
          (ctx.spec.neg x) ctx.spec.zero h'
        rw [ctx.certificate.orderedField.add_comm x,
          ctx.certificate.orderedField.neg_add_cancel,
          ctx.certificate.orderedField.add_zero] at hsum
        exact (ctx.certificate.orderedField.lt_irrefl x
          (ctx.certificate.orderedField.lt_trans x ctx.spec.zero x hneg hsum)).elim
    · subst x
      rw [ctx.certificate.sourceLaws.abs_nonnegative _
        (ctx.certificate.orderedField.le_refl _)]
      exact ctx.certificate.orderedField.le_refl _
  · have hle : ctx.spec.le ctx.spec.zero x :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp h).1
    rw [ctx.certificate.sourceLaws.abs_nonnegative x hle]
    exact hle

private theorem exact_sq_lt_of_abs_lt_aux (ctx : ExactRealContext)
    {a b : ctx.spec.carrier} (ha : ctx.spec.le ctx.spec.zero a)
    (hb : ctx.spec.le ctx.spec.zero b) (hab : ctx.spec.lt a b) :
    ctx.spec.lt (ctx.spec.mul a a) (ctx.spec.mul b b) := by
  rcases ctx.certificate.total_order ctx.spec.zero a with h | h
  · rcases h with h | h
    · have hbpos := ctx.certificate.orderedField.lt_trans _ _ _ h hab
      have hmul1 := ctx.certificate.orderedField.mul_lt_compat_l a a b h hab
      have hmul2 := ctx.certificate.orderedField.mul_lt_compat_l b a b hbpos hab
      rw [ctx.certificate.orderedField.mul_comm b a] at hmul2
      exact ctx.certificate.orderedField.lt_trans _ _ _ hmul1 hmul2
    · have hbpos : ctx.spec.lt ctx.spec.zero b := by
        rw [← h] at hab
        exact hab
      have hmul := ctx.certificate.orderedField.mul_lt_compat_l b
        ctx.spec.zero b hbpos hbpos
      rw [ctx.certificate.orderedField.mul_zero] at hmul
      rw [← h, ctx.certificate.orderedField.zero_mul]
      exact hmul
  · have hnot : ¬ ctx.spec.le ctx.spec.zero a :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp h).2
    exact (hnot ha).elim

theorem Rcompare_sqr (ctx : ExactRealContext) : Rcompare_sqrStatement ctx := by
  intro x y
  change Exact.Rcompare ctx (ctx.spec.mul x x) (ctx.spec.mul y y) =
    Exact.Rcompare ctx (ctx.spec.abs x) (ctx.spec.abs y)
  have hx := exact_sq_abs_eq_aux ctx x
  have hy := exact_sq_abs_eq_aux ctx y
  rw [hx, hy]
  rcases ctx.certificate.total_order (ctx.spec.abs x) (ctx.spec.abs y) with h | h
  · rcases h with hlt | heq
    · rw [exact_Rcompare_lt_aux ctx
          (exact_sq_lt_of_abs_lt_aux ctx (exact_abs_nonneg_aux ctx x)
            (exact_abs_nonneg_aux ctx y) hlt),
        exact_Rcompare_lt_aux ctx hlt]
    · rw [heq, exact_Rcompare_eq_aux ctx rfl, exact_Rcompare_eq_aux ctx rfl]
  · rw [exact_Rcompare_gt_aux ctx
        (exact_sq_lt_of_abs_lt_aux ctx (exact_abs_nonneg_aux ctx y)
          (exact_abs_nonneg_aux ctx x) h),
      exact_Rcompare_gt_aux ctx h]

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem IZR_Zpower (ctx : ExactRealContext) : IZR_ZpowerStatement ctx := by
  intro r e he
  cases e with
  | Z0 =>
      change ctx.spec.ofZ (Zpower r.radix_val Z0) = ctx.spec.one
      unfold Zpower CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow]
      have h : ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 < 0 := by
        simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
      rw [if_neg h]
      have hpow :
          ((CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val).pow
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0).toNat) = (1 : Int) := by
        have hz : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 = (0 : Int) := rfl
        rw [hz]
        exact Int.pow_zero _
      rw [hpow]
      change ctx.spec.ofZ (Zpos xH) = ctx.spec.one
      exact ctx.certificate.sourceLaws.ofZ_one
  | Zpos p =>
      change ctx.spec.ofZ (Zpower r.radix_val (Zpos p)) =
        ctx.spec.ofZ (Zpower_pos r.radix_val p)
      rfl
  | Zneg p =>
      exfalso
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zneg p) at he
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at he
      have hp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      omega

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

private theorem pg_posToNat_succ (p : positive) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ p) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p + 1 := by
  induction p with
  | xH => simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
  | xI p ih => simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat, ih] <;> omega
  | xO p ih => simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]

private theorem pg_zpower_pos_succ (z : Z) (p : positive) :
    Zpower_pos z
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ p) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
        (Zpower_pos z p) z := by
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (Int.pow (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ p))) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zpower_pos z p) * CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z)
  rw [pg_posToNat_succ]
  congr 1
  rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p + 1 =
      Nat.succ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) by omega]
  simp only [Zpower_pos,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow_pos,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  exact Int.pow_succ _ _

private theorem pg_zpower_pos_one (z : Z) : Zpower_pos z xH = z := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [Zpower_pos,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow_pos,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat]
  change (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z).pow 1 = _
  exact Int.pow_one _

private theorem pg_bpow_pos (ctx : ExactRealContext) (r : radix) (p : positive) :
    Exact.IZR ctx (Zpower_pos r.radix_val p) =
      Exact.powerRZ ctx (Exact.IZR ctx r.radix_val) (Zpos p) := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.peano_ind
    (P := fun p => Exact.IZR ctx (Zpower_pos r.radix_val p) =
      Exact.powerRZ ctx (Exact.IZR ctx r.radix_val) (Zpos p))
  · rw [pg_zpower_pos_one]
    change Exact.IZR ctx r.radix_val =
      ctx.spec.mul (Exact.IZR ctx r.radix_val) ctx.spec.one
    exact (ctx.certificate.orderedField.mul_one _).symm
  · intro p ih
    change Exact.IZR ctx
        (Zpower_pos r.radix_val
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ p)) =
      CompCert4Lean.Foundation.FlocqReal.ExactReal.powerNat ctx.spec
        (Exact.IZR ctx r.radix_val)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ p))
    rw [pg_zpower_pos_succ]
    have hmul :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR ctx
        (Zpower_pos r.radix_val p) r.radix_val
    rw [show Exact.IZR ctx
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
          (Zpower_pos r.radix_val p) r.radix_val) =
        ctx.spec.mul (Exact.IZR ctx (Zpower_pos r.radix_val p))
          (Exact.IZR ctx r.radix_val) by exact hmul]
    rw [ih, pg_posToNat_succ]
    rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p + 1 =
        Nat.succ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) by omega]
    change ctx.spec.mul
        (CompCert4Lean.Foundation.FlocqReal.ExactReal.powerNat ctx.spec
          (Exact.IZR ctx r.radix_val)
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))
        (Exact.IZR ctx r.radix_val) =
      ctx.spec.mul (Exact.IZR ctx r.radix_val)
        (CompCert4Lean.Foundation.FlocqReal.ExactReal.powerNat ctx.spec
          (Exact.IZR ctx r.radix_val)
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))
    rw [ctx.certificate.orderedField.mul_comm]

private theorem pg_bpow_powerRZ (ctx : ExactRealContext) (r : radix) (e : Z) :
    Exact.bpow ctx r e = Exact.powerRZ ctx (Exact.IZR ctx r.radix_val) e := by
  cases e with
  | Z0 => rfl
  | Zpos p =>
      change Exact.IZR ctx (Zpower_pos r.radix_val p) = _
      exact pg_bpow_pos ctx r p
  | Zneg p =>
      change Exact.Rinv ctx (Exact.IZR ctx (Zpower_pos r.radix_val p)) =
        Exact.Rinv ctx (Exact.powerRZ ctx (Exact.IZR ctx r.radix_val) (Zpos p))
      exact congrArg (Exact.Rinv ctx) (pg_bpow_pos ctx r p)

theorem bpow_plus (ctx : ExactRealContext) : bpow_plusStatement ctx := by
  intro r e1 e2
  rw [pg_bpow_powerRZ ctx r (Zadd e1 e2),
    pg_bpow_powerRZ ctx r e1, pg_bpow_powerRZ ctx r e2]
  apply ctx.certificate.sourceLaws.powerRZ_add
  intro hzero
  have hpos := bpow_gt_0 ctx r (Zpos xH)
  change ctx.spec.lt ctx.spec.zero
      (ctx.spec.ofZ (Zpower_pos r.radix_val xH)) at hpos
  rw [pg_zpower_pos_one] at hpos
  change ctx.spec.ofZ r.radix_val = ctx.spec.zero at hzero
  rw [hzero] at hpos
  exact (ctx.certificate.orderedField.lt_irrefl _ hpos).elim

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Rle_0_minus (ctx : ExactRealContext) : Rle_0_minusStatement ctx := by
  intro x y hxy
  rcases ctx.certificate.total_order x y with h | hyx
  · rcases h with hlt | heq
    · have hlt' :=
        (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_0_minus_proof
          ctx x y).2 hlt
      have hle := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt' |>.1
      have hzero : ctx.spec.ofZ Z0 = ctx.spec.zero :=
        ctx.certificate.sourceLaws.ofZ_zero
      change ctx.spec.le (ctx.spec.ofZ Z0)
        (ctx.spec.add y (ctx.spec.neg x)) at hle
      rw [hzero] at hle
      change ctx.spec.le ctx.spec.zero
        (ctx.spec.add y (ctx.spec.neg x))
      exact hle
    · subst y
      change ctx.spec.le ctx.spec.zero
        (ctx.spec.add x (ctx.spec.neg x))
      rw [show ctx.spec.add x (ctx.spec.neg x) = ctx.spec.zero by
        rw [ctx.certificate.orderedField.add_comm,
          ctx.certificate.orderedField.neg_add_cancel]]
      exact ctx.certificate.orderedField.le_refl _
  · exact False.elim ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hyx |>.2 hxy)

theorem Rmult_neq_compat_r (ctx : ExactRealContext) :
    Rmult_neq_compat_rStatement ctx := by
  intro r1 r2 r3 hr1 h23 hmul
  apply h23
  change r1 ≠ ctx.spec.zero at hr1
  change ctx.spec.mul r2 r1 = ctx.spec.mul r3 r1 at hmul
  have hr1' : r1 ≠ ctx.spec.zero := by
    exact hr1
  have hinv := ctx.certificate.orderedField.inv_mul_cancel r1 hr1'
  have hmul' := congrArg (ctx.spec.mul (ctx.spec.inv r1)) hmul
  calc
    r2 = ctx.spec.mul r2 ctx.spec.one :=
      (ctx.certificate.orderedField.mul_one r2).symm
    _ = ctx.spec.mul r2 (ctx.spec.mul (ctx.spec.inv r1) r1) := by rw [hinv]
    _ = ctx.spec.mul (ctx.spec.mul r2 (ctx.spec.inv r1)) r1 := by
      rw [ctx.certificate.orderedField.mul_assoc]
    _ = ctx.spec.mul (ctx.spec.mul (ctx.spec.inv r1) r2) r1 := by
      rw [ctx.certificate.orderedField.mul_comm r2 (ctx.spec.inv r1)]
    _ = ctx.spec.mul (ctx.spec.inv r1) (ctx.spec.mul r2 r1) := by
      rw [ctx.certificate.orderedField.mul_assoc]
    _ = ctx.spec.mul (ctx.spec.inv r1) (ctx.spec.mul r3 r1) := hmul'
    _ = ctx.spec.mul (ctx.spec.mul (ctx.spec.inv r1) r3) r1 := by
      rw [ctx.certificate.orderedField.mul_assoc]
    _ = ctx.spec.mul (ctx.spec.mul r3 (ctx.spec.inv r1)) r1 := by
      rw [ctx.certificate.orderedField.mul_comm (ctx.spec.inv r1) r3]
    _ = ctx.spec.mul r3 (ctx.spec.mul (ctx.spec.inv r1) r1) := by
      rw [ctx.certificate.orderedField.mul_assoc]
    _ = ctx.spec.mul r3 ctx.spec.one := by rw [hinv]
    _ = r3 := ctx.certificate.orderedField.mul_one r3

theorem Rmult_min_distr_r (ctx : ExactRealContext) :
    Rmult_min_distr_rStatement ctx := by
  intro r r1 r2 hr
  change ctx.spec.le ctx.spec.zero r at hr
  have hr0 : ctx.spec.le (ctx.spec.ofZ Z0) r := by
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hr
  change ctx.spec.mul (ctx.spec.min r1 r2) r =
    ctx.spec.min (ctx.spec.mul r1 r) (ctx.spec.mul r2 r)
  rcases ctx.certificate.total_order r1 r2 with h | h21
  · rcases h with h12 | heq
    · have h12le : ctx.spec.le r1 r2 :=
        (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h12 |>.1
      have hmul : ctx.spec.le (ctx.spec.mul r1 r) (ctx.spec.mul r2 r) :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
          ctx r r1 r2 hr0 h12le
      rw [ctx.certificate.sourceLaws.min_eq_left _ _ h12le,
        ctx.certificate.sourceLaws.min_eq_left _ _ hmul]
    · subst r2
      rw [ctx.certificate.sourceLaws.min_eq_left _ _
          (ctx.certificate.orderedField.le_refl _),
        ctx.certificate.sourceLaws.min_eq_left _ _
          (ctx.certificate.orderedField.le_refl _)]
  · have h21le : ctx.spec.le r2 r1 :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h21 |>.1
    have hmul : ctx.spec.le (ctx.spec.mul r2 r) (ctx.spec.mul r1 r) :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
        ctx r r2 r1 hr0 h21le
    rw [ctx.certificate.sourceLaws.min_eq_right _ _ h21le,
      ctx.certificate.sourceLaws.min_eq_right _ _ hmul]

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

private theorem pg_int_pow_gt_one (a : Int) (ha : (2 : Int) ≤ a) :
    ∀ n : Nat, 0 < n → (1 : Int) < a ^ n := by
  intro n hn
  cases n with
  | zero => omega
  | succ n =>
      have hapos : 0 < a := by omega
      have hpow_one_all : ∀ k : Nat, (1 : Int) ≤ a ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
            rw [Int.pow_succ]
            have hmul := Int.mul_le_mul_of_nonneg_right ih (Int.le_of_lt hapos)
            have haone : (1 : Int) ≤ a := by omega
            have hmul' : (1 : Int) * a ≤ a ^ k * a := by
              simpa using hmul
            have hmul'' : a ≤ a ^ k * a := by
              simpa only [Int.one_mul] using hmul'
            exact Int.le_trans haone hmul''
      have hpow_one : (1 : Int) ≤ a ^ n := hpow_one_all n
      rw [Int.pow_succ]
      have hmul := Int.mul_le_mul_of_nonneg_right hpow_one (Int.le_of_lt hapos)
      have haone : (1 : Int) < a := by omega
      have hmul' : (1 : Int) * a ≤ a ^ n * a := by
        simpa using hmul
      have hmul'' : a ≤ a ^ n * a := by simpa using hmul'
      exact Int.lt_of_lt_of_le haone hmul''

private theorem pg_radix_int_ge_two (r : radix) :
    (2 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val := by
  have hr := r.radix_prop
  change (if (2 : Int) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val then true else false) = true at hr
  simpa using hr

private theorem pg_bpow_pos_gt_one (ctx : ExactRealContext) (r : radix)
    {e : Z} (he : Zlt Z0 e) :
    ctx.spec.lt (ctx.spec.one) (Exact.bpow ctx r e) := by
  cases e with
  | Z0 => change (0 : Int) < 0 at he; omega
  | Zneg p =>
      change (0 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zneg p) at he
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at he
      omega
  | Zpos p =>
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpow : (1 : Int) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zpower_pos r.radix_val p) := by
        simp only [Zpower_pos,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow_pos,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        exact pg_int_pow_gt_one _ (pg_radix_int_ge_two r) _ hp
      have h := exact_ofZ_lt_aux ctx (x := Zpos xH)
        (y := Zpower_pos r.radix_val p) (by
          change (1 : Int) <
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Zpower_pos r.radix_val p)
          exact hpow)
      change ctx.spec.lt (ctx.spec.ofZ (Zpos xH))
        (ctx.spec.ofZ (Zpower_pos r.radix_val p)) at h
      rw [ctx.certificate.sourceLaws.ofZ_one] at h
      exact h

private theorem pg_zadd_sub_cancel (a b : Z) :
    Zadd a (Zsub b a) = b := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

private theorem pg_bpow_lt (ctx : ExactRealContext) (r : radix)
    {e1 e2 : Z} (h : Zlt e1 e2) :
    Exact.Rlt ctx (Exact.bpow ctx r e1) (Exact.bpow ctx r e2) := by
  let d := Zsub e2 e1
  have hd : Zlt Z0 d := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d
    simp only [d,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 -
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 at h
    omega
  have hsum : Zadd e1 d = e2 := by
    exact pg_zadd_sub_cancel e1 e2
  have hmul : Exact.bpow ctx r e2 =
      ctx.spec.mul (Exact.bpow ctx r e1) (Exact.bpow ctx r d) := by
    rw [← hsum, bpow_plus]
    rfl
  have hpos : Exact.Rlt ctx (ctx.spec.zero) (Exact.bpow ctx r e1) :=
    bpow_gt_0 ctx r e1
  have hone : Exact.Rlt ctx (ctx.spec.one) (Exact.bpow ctx r d) :=
    pg_bpow_pos_gt_one ctx r hd
  have hpos' : Exact.Rlt ctx (Exact.IZR ctx Z0) (Exact.bpow ctx r e1) := by
    change ctx.spec.lt (ctx.spec.ofZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0))
      (Exact.bpow ctx r e1)
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hpos
  have hmul' :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_compat_r
      ctx (Exact.bpow ctx r e1) (ctx.spec.one) (Exact.bpow ctx r d) hpos' hone
  change ctx.spec.lt
    (ctx.spec.mul ctx.spec.one (Exact.bpow ctx r e1))
    (ctx.spec.mul (Exact.bpow ctx r d) (Exact.bpow ctx r e1)) at hmul'
  rw [ctx.certificate.orderedField.mul_comm (ctx.spec.one) _,
    ctx.certificate.orderedField.mul_one,
    ctx.certificate.orderedField.mul_comm _ (Exact.bpow ctx r e1)] at hmul'
  rw [← hmul] at hmul'
  exact hmul'

private theorem pg_exact_sqrt_of_pos (ctx : ExactRealContext)
    {x : Exact.R ctx} (hx : Exact.Rlt ctx (ctx.spec.zero) x) :
    Exact.sqrt ctx x = ctx.spec.sqrt x := by
  unfold Exact.sqrt
  unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.sqrt
  cases hdec : ctx.spec.lt_dec x ctx.spec.zero with
  | left hneg =>
      have hfalse := ctx.certificate.orderedField.lt_irrefl ctx.spec.zero
        (ctx.certificate.orderedField.lt_trans _ _ _ hx hneg)
      exact hfalse.elim
  | right _ => rfl

private theorem pg_exact_sqrt_pos (ctx : ExactRealContext)
    {x : Exact.R ctx} (hx : Exact.Rlt ctx (ctx.spec.zero) x) :
    Exact.Rlt ctx (ctx.spec.zero) (Exact.sqrt ctx x) := by
  rw [pg_exact_sqrt_of_pos ctx hx]
  exact ctx.certificate.sourceLaws.sqrt_strict_positive x hx

private theorem pg_exact_sqrt_sq (ctx : ExactRealContext)
    {x : Exact.R ctx} (hx : Exact.Rlt ctx (ctx.spec.zero) x) :
    ctx.spec.mul (Exact.sqrt ctx x) (Exact.sqrt ctx x) = x := by
  rw [pg_exact_sqrt_of_pos ctx hx]
  have hle : ctx.spec.le ctx.spec.zero x :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp hx).1
  exact ctx.certificate.sqrt.sqr x hle

private theorem pg_exact_abs_of_nonneg (ctx : ExactRealContext)
    {x : Exact.R ctx} (hx : Exact.Rle ctx (ctx.spec.zero) x) :
    Exact.Rabs ctx x = x := by
  change ctx.spec.abs x = x
  exact ctx.certificate.sourceLaws.abs_nonnegative x hx

private theorem pg_exact_mul_le_r (ctx : ExactRealContext)
    {r x y : Exact.R ctx} (hr : Exact.Rle ctx (ctx.spec.zero) r)
    (hxy : Exact.Rle ctx x y) :
    Exact.Rle ctx (ctx.spec.mul x r) (ctx.spec.mul y r) := by
  have hr' : Exact.Rle ctx (Exact.IZR ctx Z0) r := by
    change ctx.spec.le (ctx.spec.ofZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0)) r
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hr
  have h :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
      ctx r x y hr' hxy
  change ctx.spec.le (ctx.spec.mul x r) (ctx.spec.mul y r) at h
  exact h

private theorem pg_exact_mul_lt_r (ctx : ExactRealContext)
    {r x y : Exact.R ctx} (hr : Exact.Rlt ctx (ctx.spec.zero) r)
    (hxy : Exact.Rlt ctx x y) :
    Exact.Rlt ctx (ctx.spec.mul x r) (ctx.spec.mul y r) := by
  have hr' : Exact.Rlt ctx (Exact.IZR ctx Z0) r := by
    change ctx.spec.lt (ctx.spec.ofZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0)) r
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hr
  have h :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_compat_r
      ctx r x y hr' hxy
  change ctx.spec.lt (ctx.spec.mul x r) (ctx.spec.mul y r) at h
  exact h

private theorem pg_exact_self_le (ctx : ExactRealContext)
    {a b : Exact.R ctx} (ha : Exact.Rle ctx (ctx.spec.zero) a)
    (hab : Exact.Rle ctx a b) :
    Exact.Rle ctx (ctx.spec.mul a a) (ctx.spec.mul b b) := by
  have hb : Exact.Rle ctx (ctx.spec.zero) b :=
    ctx.certificate.orderedField.le_trans _ _ _ ha hab
  have h1 := pg_exact_mul_le_r ctx (r := a) (x := a) (y := b) ha hab
  have h2 := pg_exact_mul_le_r ctx (r := b) (x := a) (y := b) hb hab
  rw [ctx.certificate.orderedField.mul_comm b a] at h1
  exact ctx.certificate.orderedField.le_trans _ _ _ h1 h2

private theorem pg_exact_self_lt (ctx : ExactRealContext)
    {a b : Exact.R ctx} (ha : Exact.Rlt ctx (ctx.spec.zero) a)
    (hab : Exact.Rlt ctx a b) :
    Exact.Rlt ctx (ctx.spec.mul a a) (ctx.spec.mul b b) := by
  have hb : Exact.Rlt ctx (ctx.spec.zero) b :=
    ctx.certificate.orderedField.lt_trans _ _ _ ha hab
  have h1 := pg_exact_mul_lt_r ctx (r := a) (x := a) (y := b) ha hab
  have h2 := pg_exact_mul_lt_r ctx (r := b) (x := a) (y := b) hb hab
  rw [ctx.certificate.orderedField.mul_comm b a] at h1
  exact ctx.certificate.orderedField.lt_trans _ _ _ h1 h2

private theorem pg_bpow_lt_imp_exp_lt (ctx : ExactRealContext) (r : radix)
    {a b : Z} (h : Exact.Rlt ctx (Exact.bpow ctx r a) (Exact.bpow ctx r b)) :
    Zlt a b := by
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b
  by_cases hablt :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b
  · exact hablt
  · have hle : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a := by omega
    rcases Int.lt_or_eq_of_le hle with hba | heq
    · have hp := pg_bpow_lt ctx r (show Zlt b a by exact hba)
      exact (ctx.certificate.orderedField.lt_irrefl _
        (ctx.certificate.orderedField.lt_trans _ _ _ hp h)).elim
    · have hab : a = b := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        exact heq.symm
      subst b
      exact (ctx.certificate.orderedField.lt_irrefl _ h).elim

private theorem pg_div2_int (z : Z) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zdiv2 z) =
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z).ediv 2 := by
  let d : Z := Zpos (xO xH)
  have heq := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Z_div_mod_eq_full z d
  have hrem := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Z_mod_lt z d (by
    dsimp [d]
    change (0 : Int) < 2
    omega)
  have heq' := congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ heq
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at heq'
  have h0 := hrem.1
  have h2 := hrem.2
  change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo z d) at h0
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo z d) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d at h2
  have hd : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d = 2 := by
    dsimp [d]
    rfl
  rw [hd] at heq' h2
  have hdiv := Int.ediv_mul_add_emod
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z) 2
  change (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z).ediv 2 * 2 +
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z) % 2 =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z at hdiv
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div z d) = _
  omega

theorem mag_sqrt :
    ∀ (ctx : ExactRealContext) (m : Exact.Magnitude ctx),
      mag_sqrtStatement ctx m := by
  intro ctx m r x hx
  let e : Z := (Exact.mag m r x).mag_val
  let s : Z := (Exact.mag m r (Exact.sqrt ctx x)).mag_val
  have hxne : x ≠ Exact.R0 ctx := by
    intro hzero
    rw [hzero] at hx
    exact (ctx.certificate.orderedField.lt_irrefl _ hx).elim
  have hspos := pg_exact_sqrt_pos ctx hx
  have hsne : Exact.sqrt ctx x ≠ Exact.R0 ctx := by
    intro hzero
    rw [hzero] at hspos
    exact (ctx.certificate.orderedField.lt_irrefl _ hspos).elim
  have he := (Exact.mag m r x).mag_bound hxne
  have hs := (Exact.mag m r (Exact.sqrt ctx x)).mag_bound hsne
  change Exact.Rle ctx (Exact.bpow ctx r (Zsub e (Zpos xH)))
      (Exact.Rabs ctx x) ∧
    Exact.Rlt ctx (Exact.Rabs ctx x) (Exact.bpow ctx r e) at he
  change Exact.Rle ctx (Exact.bpow ctx r (Zsub s (Zpos xH)))
      (Exact.Rabs ctx (Exact.sqrt ctx x)) ∧
    Exact.Rlt ctx (Exact.Rabs ctx (Exact.sqrt ctx x)) (Exact.bpow ctx r s) at hs
  have hxle : Exact.Rle ctx (ctx.spec.zero) x :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp hx).1
  have hsqrtle : Exact.Rle ctx (ctx.spec.zero) (Exact.sqrt ctx x) :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp hspos).1
  have habsx := pg_exact_abs_of_nonneg ctx hxle
  have habss := pg_exact_abs_of_nonneg ctx hsqrtle
  rw [habsx] at he
  rw [habss] at hs
  have hlow_nonneg : Exact.Rle ctx (ctx.spec.zero)
      (Exact.bpow ctx r (Zsub s (Zpos xH))) := by
    have h := bpow_ge_0 ctx r (Zsub s (Zpos xH))
    change ctx.spec.le ctx.spec.zero
      (Exact.bpow ctx r (Zsub s (Zpos xH))) at h
    exact h
  have hlow_sq := pg_exact_self_le ctx hlow_nonneg hs.1
  have hlow_sq' : Exact.Rle ctx
      (ctx.spec.mul (Exact.bpow ctx r (Zsub s (Zpos xH)))
        (Exact.bpow ctx r (Zsub s (Zpos xH)))) x := by
    rw [pg_exact_sqrt_sq ctx hx] at hlow_sq
    exact hlow_sq
  have hleft : Exact.Rle ctx
      (Exact.bpow ctx r (Zadd (Zsub s (Zpos xH)) (Zsub s (Zpos xH)))) x := by
    rw [bpow_plus]
    exact hlow_sq'
  have huppos : Exact.Rlt ctx (ctx.spec.zero) (Exact.bpow ctx r s) :=
    bpow_gt_0 ctx r s
  have hupp_sq := pg_exact_self_lt ctx hspos hs.2
  have hupp_sq' : Exact.Rlt ctx x
      (ctx.spec.mul (Exact.bpow ctx r s) (Exact.bpow ctx r s)) := by
    rw [pg_exact_sqrt_sq ctx hx] at hupp_sq
    exact hupp_sq
  have hright : Exact.Rlt ctx x
      (Exact.bpow ctx r (Zadd s s)) := by
    rw [bpow_plus]
    exact hupp_sq'
  have hleft_lt : Exact.Rlt ctx
      (Exact.bpow ctx r (Zadd (Zsub s (Zpos xH)) (Zsub s (Zpos xH))))
      (Exact.bpow ctx r e) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
      ctx _ _ _ hleft he.2
  have hright_lt : Exact.Rlt ctx (Exact.bpow ctx r (Zsub e (Zpos xH)))
      (Exact.bpow ctx r (Zadd s s)) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
      ctx _ _ _ he.1 hright
  have hzleft : Zlt (Zadd (Zsub s (Zpos xH)) (Zsub s (Zpos xH))) e :=
    pg_bpow_lt_imp_exp_lt ctx r hleft_lt
  have hzright : Zlt (Zsub e (Zpos xH)) (Zadd s s) :=
    pg_bpow_lt_imp_exp_lt ctx r hright_lt
  have harith :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ s =
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Zadd e (Zpos xH))).ediv 2 := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (Zadd (Zsub s (Zpos xH)) (Zsub s (Zpos xH))) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e at hzleft
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hzleft
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (Zsub e (Zpos xH)) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd s s) at hzright
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hzright
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ s =
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zadd e (Zpos xH))).ediv 2
    have headd : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zadd e (Zpos xH)) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e + 1 := by
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      rfl
    rw [headd]
    have hxH : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos xH) = 1 := rfl
    rw [hxH] at hzleft hzright
    have hdiv := Int.ediv_mul_add_emod
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e + 1) 2
    change (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e + 1).ediv 2 * 2 +
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e + 1) % 2 =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e + 1 at hdiv
    have hrem0 := Int.emod_nonneg
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e + 1)
      (by omega : (2 : Int) ≠ 0)
    have hrem2 := Int.emod_lt
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e + 1)
      (by omega : (2 : Int) ≠ 0)
    omega
  have hfinal : s = Zdiv2 (Zadd e (Zpos xH)) := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    exact harith.trans (pg_div2_int (Zadd e (Zpos xH))).symm
  simpa [e, s] using hfinal

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem exp_le : ∀ (ctx : ExactRealContext), exp_leStatement ctx := by
  intro ctx x y hxy
  by_cases hyx : Exact.Rle ctx y x
  · have hxy' : x = y := ctx.certificate.orderedField.le_antisymm _ _ hxy hyx
    subst y
    exact ctx.certificate.orderedField.le_refl _
  · have hlt : Exact.Rlt ctx x y :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).2 ⟨hxy, hyx⟩
    have hs := ctx.certificate.exp.strict_monotone x y hlt
    exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).1 hs |>.1

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Rinv_le : ∀ (ctx : ExactRealContext), Rinv_leStatement ctx := by
  intro ctx x y hx hxy
  change ctx.spec.lt ctx.spec.zero x at hx
  change ctx.spec.le x y at hxy
  have hxle : ctx.spec.le ctx.spec.zero x :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hx |>.1
  have hxnot : ¬ctx.spec.le x ctx.spec.zero :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hx |>.2
  have hyle : ctx.spec.le ctx.spec.zero y :=
    ctx.certificate.orderedField.le_trans _ _ _ hxle hxy
  have hynot : ¬ctx.spec.le y ctx.spec.zero := by
    intro hyx
    exact hxnot (ctx.certificate.orderedField.le_trans _ _ _ hxy hyx)
  have hy : ctx.spec.lt ctx.spec.zero y :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr ⟨hyle, hynot⟩
  have hxne : x ≠ ctx.spec.zero := by
    intro hzero
    subst x
    exact ctx.certificate.orderedField.lt_irrefl _ hx
  have hyne : y ≠ ctx.spec.zero := by
    intro hzero
    subst y
    exact ctx.certificate.orderedField.lt_irrefl _ hy
  have hx_ofZ : ctx.spec.lt (ctx.spec.ofZ Z0) x := by
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hx
  have hinvx_ofZ : ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.inv x) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rinv_0_lt_compat
      ctx x hx_ofZ
  have hinvx : ctx.spec.lt ctx.spec.zero (ctx.spec.inv x) := by
    rw [← ctx.certificate.sourceLaws.ofZ_zero]
    exact hinvx_ofZ
  change ctx.spec.le (ctx.spec.inv y) (ctx.spec.inv x)
  rcases ctx.certificate.total_order (ctx.spec.inv y) (ctx.spec.inv x) with h | h
  · rcases h with hlt | heq
    · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt |>.1
    · rw [heq]
      exact ctx.certificate.orderedField.le_refl _
  · have hinvxy : ctx.spec.lt (ctx.spec.inv x) (ctx.spec.inv y) := h
    have hmul_lt := ctx.certificate.orderedField.mul_lt_compat_l
      y (ctx.spec.inv x) (ctx.spec.inv y) hy hinvxy
    have hmul_eq : ctx.spec.mul y (ctx.spec.inv y) = ctx.spec.one := by
      rw [ctx.certificate.orderedField.mul_comm y (ctx.spec.inv y),
        ctx.certificate.orderedField.inv_mul_cancel y hyne]
    have hmul_lt_one : ctx.spec.lt
        (ctx.spec.mul y (ctx.spec.inv x)) ctx.spec.one := by
      rw [← hmul_eq]
      exact hmul_lt
    have hmul_le : ctx.spec.le
        (ctx.spec.mul x (ctx.spec.inv x)) (ctx.spec.mul y (ctx.spec.inv x)) := by
      rcases ctx.certificate.total_order x y with hxy' | hyx'
      · rcases hxy' with hlt | heq
        · have hmul := ctx.certificate.orderedField.mul_lt_compat_l
            (ctx.spec.inv x) x y hinvx hlt
          have hmul' : ctx.spec.lt
              (ctx.spec.mul x (ctx.spec.inv x))
              (ctx.spec.mul y (ctx.spec.inv x)) := by
            rw [ctx.certificate.orderedField.mul_comm x (ctx.spec.inv x),
              ctx.certificate.orderedField.mul_comm y (ctx.spec.inv x)]
            exact hmul
          exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hmul' |>.1
        · subst y
          exact ctx.certificate.orderedField.le_refl _
      · exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hyx').2 hxy |>.elim
    rw [ctx.certificate.orderedField.mul_comm x (ctx.spec.inv x),
      ctx.certificate.orderedField.inv_mul_cancel x hxne] at hmul_le
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hmul_lt_one).2 hmul_le |>.elim

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

private theorem pg_neg_neg (ctx : ExactRealContext) (x : ctx.spec.carrier) :
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

private theorem pg_neg_lt_of_neg_lt (ctx : ExactRealContext)
    {a b : ctx.spec.carrier} (h : ctx.spec.lt (ctx.spec.neg b) a) :
    ctx.spec.lt (ctx.spec.neg a) b := by
  rcases ctx.certificate.total_order (ctx.spec.neg a) b with hab | hba
  · rcases hab with hab | heq
    · exact hab
    · subst b
      rw [pg_neg_neg ctx a] at h
      exact (ctx.certificate.orderedField.lt_irrefl _ h).elim
  · have hleft := ctx.certificate.orderedField.add_lt_compat_l
      a b (ctx.spec.neg a) hba
    rw [ctx.certificate.orderedField.add_comm a (ctx.spec.neg a),
      ctx.certificate.orderedField.neg_add_cancel] at hleft
    have hright := ctx.certificate.orderedField.add_lt_compat_l
      b (ctx.spec.neg b) a h
    rw [ctx.certificate.orderedField.add_comm b (ctx.spec.neg b),
      ctx.certificate.orderedField.neg_add_cancel,
      ctx.certificate.orderedField.add_comm b a] at hright
    exact (ctx.certificate.orderedField.lt_irrefl _
      (ctx.certificate.orderedField.lt_trans _ _ _ hright hleft)).elim

theorem Rabs_lt : ∀ (ctx : ExactRealContext), Rabs_ltStatement ctx := by
  intro ctx x y hxy
  change ctx.spec.lt (ctx.spec.abs x) y
  rcases ctx.certificate.total_order x ctx.spec.zero with hx | hx
  · rcases hx with hxneg | hxeq
    · rw [ctx.certificate.sourceLaws.abs_negative x hxneg]
      exact pg_neg_lt_of_neg_lt ctx hxy.1
    · subst x
      rw [ctx.certificate.sourceLaws.abs_nonnegative _
        (ctx.certificate.orderedField.le_refl _)]
      exact hxy.2
  · have hxle : ctx.spec.le ctx.spec.zero x :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp hx).1
    rw [ctx.certificate.sourceLaws.abs_nonnegative x hxle]
    exact hxy.2

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

private theorem pg_lt_of_lt_of_le (ctx : ExactRealContext)
    {a b c : ctx.spec.carrier} (hab : ctx.spec.lt a b)
    (hbc : ctx.spec.le b c) : ctx.spec.lt a c := by
  apply (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
  constructor
  · exact ctx.certificate.orderedField.le_trans _ _ _
      ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hab).1 hbc
  · intro hca
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hab).2
      (ctx.certificate.orderedField.le_trans _ _ _ hbc hca)

theorem Rabs_lt_inv : ∀ (ctx : ExactRealContext), Rabs_lt_invStatement ctx := by
  intro ctx x y hxy
  change ctx.spec.lt (ctx.spec.abs x) y at hxy
  rcases ctx.certificate.total_order x ctx.spec.zero with hx | hx
  · rcases hx with hxneg | hxeq
    · have habs : ctx.spec.abs x = ctx.spec.neg x :=
        ctx.certificate.sourceLaws.abs_negative x hxneg
      have hneg : ctx.spec.lt (ctx.spec.neg y) x := by
        exact pg_neg_lt_of_neg_lt ctx (by simpa [habs] using hxy)
      have hxle0 : ctx.spec.le x ctx.spec.zero :=
        (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxneg |>.1
      have hnegx : ctx.spec.lt ctx.spec.zero (ctx.spec.neg x) := by
        have h := ctx.certificate.orderedField.add_lt_compat_l
          (ctx.spec.neg x) x ctx.spec.zero hxneg
        rw [ctx.certificate.orderedField.neg_add_cancel,
          ctx.certificate.orderedField.add_zero] at h
        exact h
      have hx_abs : ctx.spec.le x (ctx.spec.abs x) := by
        rw [habs]
        exact ctx.certificate.orderedField.le_trans _ _ _ hxle0
          ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hnegx).1
      have hsecond : ctx.spec.lt x y := by
        apply (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
        constructor
        · exact ctx.certificate.orderedField.le_trans _ _ _ hx_abs
            ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxy).1
        · intro hyx
          exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxy).2
            (ctx.certificate.orderedField.le_trans _ _ _ hyx hx_abs)
      exact ⟨hneg, hsecond⟩
    · subst x
      have habs : ctx.spec.abs ctx.spec.zero = ctx.spec.zero :=
        ctx.certificate.sourceLaws.abs_nonnegative _
          (ctx.certificate.orderedField.le_refl _)
      have hzero_y : ctx.spec.lt ctx.spec.zero y := by
        simpa [habs] using hxy
      have hneg_y : ctx.spec.lt (ctx.spec.neg y) ctx.spec.zero := by
        have h := ctx.certificate.orderedField.add_lt_compat_l
          (ctx.spec.neg y) ctx.spec.zero y hzero_y
        rw [ctx.certificate.orderedField.add_zero,
          ctx.certificate.orderedField.neg_add_cancel] at h
        exact h
      exact ⟨hneg_y, hzero_y⟩
  · have hxle : ctx.spec.le ctx.spec.zero x :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp hx).1
    have habs : ctx.spec.abs x = x :=
      ctx.certificate.sourceLaws.abs_nonnegative x hxle
    have hnonneg_abs : ctx.spec.le ctx.spec.zero (ctx.spec.abs x) := by
      rw [habs]
      exact hxle
    have hxy_le : ctx.spec.le (ctx.spec.abs x) y :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxy |>.1
    have hypos : ctx.spec.lt ctx.spec.zero y := by
      apply (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
      constructor
      · exact ctx.certificate.orderedField.le_trans _ _ _ hnonneg_abs hxy_le
      · intro hy0
        exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxy |>.2
          (ctx.certificate.orderedField.le_trans _ _ _ hy0 hnonneg_abs)
    have hneg_y : ctx.spec.lt (ctx.spec.neg y) ctx.spec.zero := by
      have h := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.neg y) ctx.spec.zero y hypos
      rw [ctx.certificate.orderedField.add_zero,
        ctx.certificate.orderedField.neg_add_cancel] at h
      exact h
    have hfirst : ctx.spec.lt (ctx.spec.neg y) x := by
      apply pg_lt_of_lt_of_le ctx hneg_y hxle
    have hsecond : ctx.spec.lt x y := by
      simpa [habs] using hxy
    exact ⟨hfirst, hsecond⟩

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Rcompare_spec (ctx : ExactRealContext) : Rcompare_specStatement ctx := by
  intro x y
  change Exact.Rcompare_prop ctx x y (Exact.Rcompare ctx x y)
  rcases ctx.certificate.total_order x y with hxy | hyx
  · rcases hxy with hlt | heq
    · rw [exact_Rcompare_lt_aux ctx hlt]
      exact Exact.Rcompare_prop.Rcompare_Lt_ hlt
    · subst y
      rw [exact_Rcompare_eq_aux ctx rfl]
      exact Exact.Rcompare_prop.Rcompare_Eq_ rfl
  · rw [exact_Rcompare_gt_aux ctx hyx]
    exact Exact.Rcompare_prop.Rcompare_Gt_ hyx

theorem Rcompare_Lt (ctx : ExactRealContext) : Rcompare_LtStatement ctx := by
  intro x y hxy
  exact exact_Rcompare_lt_aux ctx hxy

theorem Rcompare_Lt_inv (ctx : ExactRealContext) : Rcompare_Lt_invStatement ctx := by
  intro x y hcmp
  have hspec := Rcompare_spec ctx x y
  rw [hcmp] at hspec
  cases hspec with
  | Rcompare_Lt_ hlt => exact hlt

theorem Rcompare_not_Lt (ctx : ExactRealContext) : Rcompare_not_LtStatement ctx := by
  intro x y hyx hcmp
  have hlt : ctx.spec.lt x y := Rcompare_Lt_inv ctx x y hcmp
  exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt).2 hyx

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Rcompare_not_Lt_inv (ctx : ExactRealContext) :
    Rcompare_not_Lt_invStatement ctx := by
  intro x y hcmp
  rcases ctx.certificate.total_order x y with hxy | hyx
  · rcases hxy with hlt | heq
    · exact (hcmp (Rcompare_Lt ctx x y hlt)).elim
    · subst y
      exact ctx.certificate.orderedField.le_refl _
  · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hyx |>.1

theorem Rcompare_Eq (ctx : ExactRealContext) :
    Rcompare_EqStatement ctx := by
  intro x y hxy
  subst y
  exact exact_Rcompare_eq_aux ctx rfl

theorem Rcompare_Eq_inv (ctx : ExactRealContext) :
    Rcompare_Eq_invStatement ctx := by
  intro x y hcmp
  have hspec := Rcompare_spec ctx x y
  rw [hcmp] at hspec
  cases hspec with
  | Rcompare_Eq_ heq => exact heq

theorem Rcompare_Gt (ctx : ExactRealContext) :
    Rcompare_GtStatement ctx := by
  intro x y hyx
  exact exact_Rcompare_gt_aux ctx hyx

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Rcompare_Gt_inv (ctx : ExactRealContext) :
    Rcompare_Gt_invStatement ctx := by
  intro x y hcmp
  have hspec := Rcompare_spec ctx x y
  rw [hcmp] at hspec
  cases hspec with
  | Rcompare_Gt_ hyx => exact hyx

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Rcompare_sym (ctx : ExactRealContext) :
    Rcompare_symStatement ctx := by
  intro x y
  rcases ctx.certificate.total_order y x with hyx | hxy
  · rcases hyx with hyx | heq
    · rw [exact_Rcompare_gt_aux ctx hyx,
        exact_Rcompare_lt_aux ctx hyx]
      rfl
    · subst y
      rw [exact_Rcompare_eq_aux ctx rfl]
      rfl
  · rw [exact_Rcompare_lt_aux ctx hxy, exact_Rcompare_gt_aux ctx hxy]
    rfl

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

/-! Negation reverses the exact strict order. -/
private theorem exact_neg_lt_neg_iff (ctx : ExactRealContext)
    {x y : ctx.spec.carrier} :
    ctx.spec.lt (ctx.spec.neg x) (ctx.spec.neg y) ↔ ctx.spec.lt y x := by
  constructor
  · intro h
    have h1 := ctx.certificate.orderedField.add_lt_compat_l
      x (ctx.spec.neg x) (ctx.spec.neg y) h
    have hx0 : ctx.spec.add x (ctx.spec.neg x) = ctx.spec.zero := by
      rw [ctx.certificate.orderedField.add_comm,
        ctx.certificate.orderedField.neg_add_cancel]
    rw [hx0] at h1
    have h2 := ctx.certificate.orderedField.add_lt_compat_l
      y ctx.spec.zero (ctx.spec.add x (ctx.spec.neg y)) h1
    rw [ctx.certificate.orderedField.add_zero] at h2
    have hyx : ctx.spec.add y (ctx.spec.add x (ctx.spec.neg y)) = x := by
      calc
        ctx.spec.add y (ctx.spec.add x (ctx.spec.neg y)) =
            ctx.spec.add (ctx.spec.add y x) (ctx.spec.neg y) := by
              rw [ctx.certificate.orderedField.add_assoc]
        _ = ctx.spec.add (ctx.spec.add x y) (ctx.spec.neg y) := by
              rw [ctx.certificate.orderedField.add_comm y x]
        _ = ctx.spec.add x (ctx.spec.add y (ctx.spec.neg y)) := by
              rw [← ctx.certificate.orderedField.add_assoc]
        _ = ctx.spec.add x ctx.spec.zero := by
              rw [show ctx.spec.add y (ctx.spec.neg y) = ctx.spec.zero by
                rw [ctx.certificate.orderedField.add_comm,
                  ctx.certificate.orderedField.neg_add_cancel]]
        _ = x := ctx.certificate.orderedField.add_zero _
    rw [hyx] at h2
    exact h2
  · intro h
    have h1 := ctx.certificate.orderedField.add_lt_compat_l
      (ctx.spec.neg y) y x h
    rw [ctx.certificate.orderedField.neg_add_cancel] at h1
    have h2 := ctx.certificate.orderedField.add_lt_compat_l
      (ctx.spec.neg x) ctx.spec.zero (ctx.spec.add (ctx.spec.neg y) x) h1
    rw [ctx.certificate.orderedField.add_zero] at h2
    have hxy : ctx.spec.add (ctx.spec.neg x)
        (ctx.spec.add (ctx.spec.neg y) x) = ctx.spec.neg y := by
      calc
        ctx.spec.add (ctx.spec.neg x)
            (ctx.spec.add (ctx.spec.neg y) x) =
            ctx.spec.add (ctx.spec.add (ctx.spec.neg x) (ctx.spec.neg y)) x := by
              rw [ctx.certificate.orderedField.add_assoc]
        _ = ctx.spec.add (ctx.spec.add (ctx.spec.neg y) (ctx.spec.neg x)) x := by
              rw [ctx.certificate.orderedField.add_comm
                (ctx.spec.neg x) (ctx.spec.neg y)]
        _ = ctx.spec.add (ctx.spec.neg y)
            (ctx.spec.add (ctx.spec.neg x) x) := by
              rw [← ctx.certificate.orderedField.add_assoc]
        _ = ctx.spec.add (ctx.spec.neg y) ctx.spec.zero := by
              rw [ctx.certificate.orderedField.neg_add_cancel]
        _ = ctx.spec.neg y := ctx.certificate.orderedField.add_zero _
    rw [hxy] at h2
    exact h2

theorem Rcompare_opp (ctx : ExactRealContext) :
    Rcompare_oppStatement ctx := by
  intro x y
  rcases ctx.certificate.total_order y x with hyx | hxy
  · rcases hyx with hyx | heq
    ·
      have hneg := exact_neg_lt_neg_iff ctx |>.2 hyx
      rw [Rcompare_Lt ctx (Exact.Ropp ctx x) (Exact.Ropp ctx y) hneg,
        Rcompare_Lt ctx y x hyx]
    · subst y
      rw [Rcompare_Eq ctx (Exact.Ropp ctx x) (Exact.Ropp ctx x) rfl,
        Rcompare_Eq ctx x x rfl]
  ·
      have hneg := exact_neg_lt_neg_iff ctx |>.2 hxy
      rw [Rcompare_Gt ctx (Exact.Ropp ctx x) (Exact.Ropp ctx y) hneg,
        Rcompare_Gt ctx y x hxy]

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Rcompare_plus_r (ctx : ExactRealContext) :
    Rcompare_plus_rStatement ctx := by
  intro z x y
  rcases ctx.certificate.total_order x y with hxy | hyx
  · rcases hxy with hlt | heq
    · have hplus := ctx.certificate.orderedField.add_lt_compat_l z x y hlt
      rw [ctx.certificate.orderedField.add_comm z x,
        ctx.certificate.orderedField.add_comm z y] at hplus
      rw [Rcompare_Lt ctx (Exact.Rplus ctx x z) (Exact.Rplus ctx y z) hplus,
        Rcompare_Lt ctx x y hlt]
    · subst y
      rw [Rcompare_Eq ctx (Exact.Rplus ctx x z) (Exact.Rplus ctx x z) rfl,
        Rcompare_Eq ctx x x rfl]
  · have hplus := ctx.certificate.orderedField.add_lt_compat_l z y x hyx
    rw [ctx.certificate.orderedField.add_comm z y,
      ctx.certificate.orderedField.add_comm z x] at hplus
    rw [Rcompare_Gt ctx (Exact.Rplus ctx x z) (Exact.Rplus ctx y z) hplus,
      Rcompare_Gt ctx x y hyx]

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux
theorem Rcompare_plus_l (ctx : ExactRealContext) : Rcompare_plus_lStatement ctx := by
  intro z x y
  change Exact.Rcompare ctx (ctx.spec.add z x) (ctx.spec.add z y) = _
  rw [ctx.certificate.orderedField.add_comm z x, ctx.certificate.orderedField.add_comm z y]
  exact Rcompare_plus_r ctx z x y
theorem Rcompare_mult_r (ctx : ExactRealContext) : Rcompare_mult_rStatement ctx := by
  intro z x y hz
  exact exact_Rcompare_mul_pos_right_aux ctx z x y hz
theorem Rcompare_mult_l (ctx : ExactRealContext) : Rcompare_mult_lStatement ctx := by
  intro z x y hz
  change Exact.Rcompare ctx (ctx.spec.mul z x) (ctx.spec.mul z y) = _
  rw [ctx.certificate.orderedField.mul_comm z x, ctx.certificate.orderedField.mul_comm z y]
  exact Rcompare_mult_r ctx z x y hz
end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Rmin_compare (ctx : ExactRealContext) :
    Rmin_compareStatement ctx := by
  intro x y
  change ctx.spec.min x y = _
  rcases ctx.certificate.total_order x y with hxy | hyx
  · rcases hxy with hlt | heq
    · have hle : ctx.spec.le x y :=
        (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt |>.1
      rw [ctx.certificate.sourceLaws.min_eq_left _ _ hle,
        Rcompare_Lt ctx x y hlt]
    · subst y
      rw [ctx.certificate.sourceLaws.min_eq_left _ _
          (ctx.certificate.orderedField.le_refl _),
        Rcompare_Eq ctx x x rfl]
  · have hle : ctx.spec.le y x :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hyx |>.1
    rw [ctx.certificate.sourceLaws.min_eq_right _ _ hle,
      Rcompare_Gt ctx x y hyx]

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Rle_bool_spec (ctx : ExactRealContext) :
    Rle_bool_specStatement ctx := by
  intro x y
  change Exact.Rle_bool_prop ctx x y (Exact.Rle_bool ctx x y)
  unfold Exact.Rle_bool
  rcases ctx.certificate.total_order x y with hxy | hyx
  · rcases hxy with hlt | heq
    · have hle : ctx.spec.le x y :=
        (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt |>.1
      rw [Rcompare_Lt ctx x y hlt]
      exact Exact.Rle_bool_prop.Rle_bool_true_ hle
    · subst y
      rw [Rcompare_Eq ctx x x rfl]
      exact Exact.Rle_bool_prop.Rle_bool_true_
        (ctx.certificate.orderedField.le_refl x)
  · rw [Rcompare_Gt ctx x y hyx]
    exact Exact.Rle_bool_prop.Rle_bool_false_ hyx

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Rle_bool_true (ctx : ExactRealContext) :
    Rle_bool_trueStatement ctx := by
  intro x y hxy
  change Exact.Rle_bool ctx x y = true
  unfold Exact.Rle_bool
  rcases ctx.certificate.total_order x y with hxy' | hyx
  · rcases hxy' with hlt | heq
    · rw [Rcompare_Lt ctx x y hlt]
    · subst y
      rw [Rcompare_Eq ctx x x rfl]
  · exact False.elim
      (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hyx).2 hxy)

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Rle_bool_false (ctx : ExactRealContext) :
    Rle_bool_falseStatement ctx := by
  intro x y hxy
  change Exact.Rle_bool ctx x y = false
  unfold Exact.Rle_bool
  rw [Rcompare_Gt ctx x y hxy]

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Rlt_bool_spec (ctx : ExactRealContext) :
    Rlt_bool_specStatement ctx := by
  intro x y
  change Exact.Rlt_bool_prop ctx x y (Exact.Rlt_bool ctx x y)
  unfold Exact.Rlt_bool
  rcases ctx.certificate.total_order x y with hxy | hyx
  · rcases hxy with hlt | heq
    · rw [Rcompare_Lt ctx x y hlt]
      exact Exact.Rlt_bool_prop.Rlt_bool_true_ hlt
    · subst y
      rw [Rcompare_Eq ctx x x rfl]
      exact Exact.Rlt_bool_prop.Rlt_bool_false_
        (ctx.certificate.orderedField.le_refl x)
  · rw [Rcompare_Gt ctx x y hyx]
    exact Exact.Rlt_bool_prop.Rlt_bool_false_
      ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hyx |>.1)

theorem negb_Rlt_bool (ctx : ExactRealContext) :
    negb_Rlt_boolStatement ctx := by
  intro x y
  unfold Exact.Rle_bool Exact.Rlt_bool
  rw [Rcompare_sym ctx x y]
  cases h : Exact.Rcompare ctx y x <;> rfl

theorem Rlt_bool_true (ctx : ExactRealContext) :
    Rlt_bool_trueStatement ctx := by
  intro x y hxy
  change Exact.Rlt_bool ctx x y = true
  unfold Exact.Rlt_bool
  rw [Rcompare_Lt ctx x y hxy]

theorem Rlt_bool_false (ctx : ExactRealContext) :
    Rlt_bool_falseStatement ctx := by
  intro x y hxy
  rw [← negb_Rlt_bool ctx y x, Rle_bool_true ctx y x hxy]
  rfl

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Req_bool_spec (ctx : ExactRealContext) :
    Req_bool_specStatement ctx := by
  intro x y
  rcases ctx.certificate.total_order x y with hxy | hyx
  · rcases hxy with hlt | heq
    · unfold Exact.Req_bool
      unfold Exact.Rcompare
      unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.total_order_T
      cases hdec : ctx.spec.lt_dec x y with
      | left _ =>
          exact Exact.Req_bool_prop.Req_bool_false_ (by
            intro heq'
            subst y
            exact ctx.certificate.orderedField.lt_irrefl x hlt)
      | right hn => exact (hn hlt).elim
    · unfold Exact.Req_bool
      unfold Exact.Rcompare
      unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.total_order_T
      cases hdec : ctx.spec.lt_dec x y with
      | left hlt => exact (ctx.certificate.orderedField.lt_irrefl x (by simpa [heq] using hlt)).elim
      | right _ =>
          cases hdec' : ctx.spec.lt_dec y x with
          | left hlt => exact (ctx.certificate.orderedField.lt_irrefl x (by simpa [heq] using hlt)).elim
          | right _ => exact Exact.Req_bool_prop.Req_bool_true_ heq
  · unfold Exact.Req_bool
    unfold Exact.Rcompare
    unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.total_order_T
    cases hdec : ctx.spec.lt_dec x y with
    | left hlt => exact (ctx.certificate.orderedField.lt_irrefl x (by
          exact ctx.certificate.orderedField.lt_trans _ _ _ hlt hyx)).elim
    | right _ =>
        cases hdec' : ctx.spec.lt_dec y x with
        | left _ =>
            exact Exact.Req_bool_prop.Req_bool_false_ (by
              intro heq
              subst y
              exact ctx.certificate.orderedField.lt_irrefl x hyx)
        | right hn => exact (hn hyx).elim

theorem Req_bool_false (ctx : ExactRealContext) :
    Req_bool_falseStatement ctx := by
  intro x y hxy
  unfold Exact.Req_bool
  cases hcmp : Exact.Rcompare ctx x y with
  | Lt => rfl
  | Gt => rfl
  | Eq =>
      have hs := Req_bool_spec ctx x y
      unfold Exact.Req_bool at hs
      rw [hcmp] at hs
      cases hs with
      | Req_bool_true_ heq => exact (hxy heq).elim

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Zfloor_lb (ctx : ExactRealContext) :
    Zfloor_lbStatement ctx := by
  intro x
  unfold Exact.Zfloor
  have hg := ctx.certificate.sourceLaws.up_gap x
  rw [CompCert4Lean.Foundation.FlocqReal.ExactReal.Rminus] at hg
  rw [ctx.certificate.sourceLaws.ofZ_one] at hg
  have h := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_le_compat_l
      ctx x (ctx.spec.add (ctx.spec.ofZ (ctx.spec.up x)) (ctx.spec.neg x)) ctx.spec.one hg
  change ctx.spec.le (ctx.spec.add x
      (ctx.spec.add (ctx.spec.ofZ (ctx.spec.up x)) (ctx.spec.neg x)))
      (ctx.spec.add x ctx.spec.one) at h
  have hux : ctx.spec.le (ctx.spec.ofZ (ctx.spec.up x))
      (ctx.spec.add x ctx.spec.one) := by
    rw [← ctx.certificate.orderedField.add_assoc,
      ctx.certificate.orderedField.add_comm x (ctx.spec.ofZ (ctx.spec.up x)),
      ctx.certificate.orderedField.add_assoc,
      ctx.certificate.orderedField.add_comm x (ctx.spec.neg x),
      ctx.certificate.orderedField.neg_add_cancel,
      ctx.certificate.orderedField.add_zero] at h
    exact h
  have htarget := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_le_compat_l
      ctx (ctx.spec.neg ctx.spec.one) (ctx.spec.ofZ (ctx.spec.up x))
        (ctx.spec.add x ctx.spec.one) hux
  change ctx.spec.le (ctx.spec.add (ctx.spec.neg ctx.spec.one)
      (ctx.spec.ofZ (ctx.spec.up x)))
      (ctx.spec.add (ctx.spec.neg ctx.spec.one)
      (ctx.spec.add x ctx.spec.one)) at htarget
  rw [← ctx.certificate.orderedField.add_assoc,
      ctx.certificate.orderedField.add_comm (ctx.spec.neg ctx.spec.one) x,
      ctx.certificate.orderedField.add_assoc,
      ctx.certificate.orderedField.neg_add_cancel,
      ctx.certificate.orderedField.add_zero] at htarget
  rw [ctx.certificate.orderedField.add_comm (ctx.spec.neg ctx.spec.one)
      (ctx.spec.ofZ (ctx.spec.up x))] at htarget
  change ctx.spec.le
    (ctx.spec.ofZ (Zsub (ctx.spec.up x) (Zpos xH))) x
  change ctx.spec.le
    (ctx.spec.ofZ (Zadd (ctx.spec.up x) (Zopp (Zpos xH)))) x
  rw [ctx.certificate.sourceLaws.ofZ_add,
      ctx.certificate.sourceLaws.ofZ_neg,
      ctx.certificate.sourceLaws.ofZ_one]
  exact htarget

theorem Zfloor_ub (ctx : ExactRealContext) :
    Zfloor_ubStatement ctx := by
  intro x
  unfold Exact.Zfloor
  have hgt := ctx.certificate.sourceLaws.up_gt x
  change ctx.spec.lt x
    (ctx.spec.add (ctx.spec.ofZ (Zsub (ctx.spec.up x) (Zpos xH))) ctx.spec.one)
  change ctx.spec.lt x
    (ctx.spec.add (ctx.spec.ofZ (Zadd (ctx.spec.up x) (Zopp (Zpos xH)))) ctx.spec.one)
  rw [ctx.certificate.sourceLaws.ofZ_add,
      ctx.certificate.sourceLaws.ofZ_neg,
      ctx.certificate.sourceLaws.ofZ_one,
      ctx.certificate.orderedField.add_assoc,
      ctx.certificate.orderedField.neg_add_cancel,
      ctx.certificate.orderedField.add_zero]
  exact hgt

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

private theorem pg_lt_IZR (ctx : ExactRealContext) {n m : Z}
    (h : Exact.Rlt ctx (Exact.IZR ctx n) (Exact.IZR ctx m)) : Zlt n m := by
  change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n <
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m
  by_cases hnm :
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n <
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m
  · exact hnm
  · have hle : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m ≤
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n :=
      Int.le_of_not_gt hnm
    rcases Int.lt_or_eq_of_le hle with hlt | heq
    · have hreal :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt
          ctx m n hlt
      exact False.elim ((ctx.certificate.orderedField.lt_irrefl _)
        (ctx.certificate.orderedField.lt_trans _ _ _ hreal h))
    · have heq' :
          _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n =
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m :=
        heq.symm
      have hnmEq : n = m :=
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective heq'
      subst m
      exact False.elim ((ctx.certificate.orderedField.lt_irrefl _ h))

theorem Zfloor_lub (ctx : ExactRealContext) :
    Zfloor_lubStatement ctx := by
  intro n x hnx
  have hreal : Exact.Rlt ctx (Exact.IZR ctx n)
      (Exact.IZR ctx (Zadd (Exact.Zfloor ctx x) (Zpos xH))) := by
    change ctx.spec.lt (ctx.spec.ofZ n)
      (ctx.spec.ofZ (Zadd (Exact.Zfloor ctx x) (Zpos xH)))
    rw [ctx.certificate.sourceLaws.ofZ_add,
      ctx.certificate.sourceLaws.ofZ_one]
    exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
      ctx _ _ _ hnx (Zfloor_ub ctx x)
  have hlt := pg_lt_IZR ctx hreal
  change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n ≤
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Exact.Zfloor ctx x)
  change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n <
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (Zadd (Exact.Zfloor ctx x) (Zpos xH)) at hlt
  simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hlt
  change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n <
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Exact.Zfloor ctx x) + 1 at hlt
  omega

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Zfloor_imp (ctx : ExactRealContext) :
    Zfloor_impStatement ctx := by
  intro n x hnx
  have hnle := Zfloor_lub ctx n x hnx.1
  have hreal := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
    ctx _ _ _ (Zfloor_lb ctx x) hnx.2
  have hlt := pg_lt_IZR ctx hreal
  have hfle :
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Exact.Zfloor ctx x) ≤
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n := by
    change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Exact.Zfloor ctx x) <
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zadd n (Zpos xH)) at hlt
    simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hlt
    change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Exact.Zfloor ctx x) <
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n + 1 at hlt
    omega
  apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (Exact.Zfloor ctx x) =
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n
  change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n ≤
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Exact.Zfloor ctx x) at hnle
  omega

theorem Zfloor_IZR (ctx : ExactRealContext) :
    Zfloor_IZRStatement ctx := by
  intro n
  apply Zfloor_imp ctx n (Exact.IZR ctx n)
  constructor
  · exact ctx.certificate.orderedField.le_refl _
  · change ctx.spec.lt (ctx.spec.ofZ n)
      (ctx.spec.ofZ (Zadd n (Zpos xH)))
    rw [ctx.certificate.sourceLaws.ofZ_add,
      ctx.certificate.sourceLaws.ofZ_one]
    have h := ctx.certificate.orderedField.add_lt_compat_l
      (ctx.spec.ofZ n) ctx.spec.zero ctx.spec.one
      (exact_zero_lt_one_aux ctx)
    rw [ctx.certificate.orderedField.add_zero] at h
    exact h

theorem Zfloor_le (ctx : ExactRealContext) :
    Zfloor_leStatement ctx := by
  intro x y hxy
  apply Zfloor_lub ctx (Exact.Zfloor ctx x) y
  exact ctx.certificate.orderedField.le_trans _ _ _ (Zfloor_lb ctx x) hxy

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Zceil_ub (ctx : ExactRealContext) :
    Zceil_ubStatement ctx := by
  intro x
  unfold Exact.Zceil
  change ctx.spec.le x
      (ctx.spec.ofZ (Zopp (Exact.Zfloor ctx (Exact.Ropp ctx x))))
  rw [ctx.certificate.sourceLaws.ofZ_neg]
  have hfloor := Zfloor_lb ctx (Exact.Ropp ctx x)
  change ctx.spec.le (Exact.IZR ctx (Exact.Zfloor ctx (Exact.Ropp ctx x)))
      (Exact.Ropp ctx x) at hfloor
  have le_of_eq : ∀ {a b : ctx.spec.carrier}, a = b → ctx.spec.le a b := by
    intro a b hab
    cases hab
    exact ctx.certificate.orderedField.le_refl _
  rcases ctx.certificate.total_order x
      (Exact.Ropp ctx (Exact.IZR ctx (Exact.Zfloor ctx (Exact.Ropp ctx x)))) with h | h
  · rcases h with hlt | heq
    · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt |>.1
    · exact le_of_eq heq
  · have hneg := pg_neg_lt_of_neg_lt ctx h
    exact False.elim (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hneg).2 hfloor)

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

private theorem pg_zopp_zopp (z : Z) : Zopp (Zopp z) = z := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zopp (Zopp z)) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z
  simp only [Zopp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

private theorem pg_neg_le_contravar (ctx : ExactRealContext)
    {x y : ctx.spec.carrier} (h : ctx.spec.le x y) :
    ctx.spec.le (ctx.spec.neg y) (ctx.spec.neg x) := by
  rcases ctx.certificate.total_order (ctx.spec.neg y) (ctx.spec.neg x) with hab | hba
  · rcases hab with hlt | heq
    · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt |>.1
    · rw [heq]
      exact ctx.certificate.orderedField.le_refl _
  · have hyx : ctx.spec.lt y x :=
      (exact_neg_lt_neg_iff ctx).mp hba
    exact (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hyx).2 h).elim

theorem Zceil_glb (ctx : ExactRealContext) :
    Zceil_glbStatement ctx := by
  intro n x hnx
  unfold Exact.Zceil
  apply CompCert4Lean.Flocq.Core.Zaux.Zopp_le_cancel
  change Zle (Zopp n)
    (Zopp (Zopp (Exact.Zfloor ctx (Exact.Ropp ctx x))))
  rw [pg_zopp_zopp]
  apply Zfloor_lub ctx (Zopp n) (Exact.Ropp ctx x)
  change ctx.spec.le (ctx.spec.ofZ (Zopp n)) (Exact.Ropp ctx x)
  rw [ctx.certificate.sourceLaws.ofZ_neg]
  exact pg_neg_le_contravar ctx hnx

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Zceil_imp (ctx : ExactRealContext) :
    Zceil_impStatement ctx := by
  intro n x hnx
  unfold Exact.Zceil
  have hfloor : Exact.Zfloor ctx (Exact.Ropp ctx x) = Zopp n := by
    apply Zfloor_imp ctx (Zopp n) (Exact.Ropp ctx x)
    constructor
    · change ctx.spec.le (ctx.spec.ofZ (Zopp n)) (Exact.Ropp ctx x)
      rw [ctx.certificate.sourceLaws.ofZ_neg]
      exact pg_neg_le_contravar ctx hnx.2
    · change ctx.spec.lt (Exact.Ropp ctx x)
        (ctx.spec.ofZ (Zadd (Zopp n) (Zpos xH)))
      rw [ctx.certificate.sourceLaws.ofZ_add,
        ctx.certificate.sourceLaws.ofZ_neg,
        ctx.certificate.sourceLaws.ofZ_one]
      have hneg := (exact_neg_lt_neg_iff ctx).2 hnx.1
      change ctx.spec.lt (ctx.spec.neg x)
        (ctx.spec.neg (ctx.spec.ofZ (Zsub n (Zpos xH)))) at hneg
      change ctx.spec.lt (ctx.spec.neg x)
        (ctx.spec.neg (ctx.spec.ofZ (Zadd n (Zopp (Zpos xH))))) at hneg
      rw [ctx.certificate.sourceLaws.ofZ_add,
        ctx.certificate.sourceLaws.ofZ_neg,
        ctx.certificate.sourceLaws.ofZ_one] at hneg
      have hrewrite :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_minus_distr
          ctx (ctx.spec.ofZ n) ctx.spec.one
      change ctx.spec.neg (ctx.spec.add (ctx.spec.ofZ n)
          (ctx.spec.neg ctx.spec.one)) =
        ctx.spec.add ctx.spec.one (ctx.spec.neg (ctx.spec.ofZ n)) at hrewrite
      rw [hrewrite] at hneg
      rw [ctx.certificate.orderedField.add_comm] at hneg
      exact hneg
  rw [hfloor]
  exact pg_zopp_zopp n

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Zceil_IZR (ctx : ExactRealContext) :
    Zceil_IZRStatement ctx := by
  intro n
  unfold Exact.Zceil
  change Zopp (Exact.Zfloor ctx (Exact.Ropp ctx (Exact.IZR ctx n))) = n
  rw [show Exact.Ropp ctx (Exact.IZR ctx n) = Exact.IZR ctx (Zopp n) by
    change ctx.spec.neg (ctx.spec.ofZ n) = ctx.spec.ofZ (Zopp n)
    exact (ctx.certificate.sourceLaws.ofZ_neg n).symm]
  rw [Zfloor_IZR]
  exact pg_zopp_zopp n

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Zceil_le (ctx : ExactRealContext) :
    Zceil_leStatement ctx := by
  intro x y hxy
  apply Zceil_glb ctx (Exact.Zceil ctx y) x
  exact ctx.certificate.orderedField.le_trans _ _ _ hxy (Zceil_ub ctx y)

theorem Ztrunc_IZR (ctx : ExactRealContext) :
    Ztrunc_IZRStatement ctx := by
  intro n
  unfold Exact.Ztrunc
  cases h : Exact.Rlt_bool ctx (Exact.IZR ctx n) (Exact.R0 ctx) with
  | false => exact Zfloor_IZR ctx n
  | true => exact Zceil_IZR ctx n

theorem Ztrunc_floor (ctx : ExactRealContext) :
    Ztrunc_floorStatement ctx := by
  intro x hx
  unfold Exact.Ztrunc
  have hb := Rlt_bool_false ctx x (Exact.R0 ctx) hx
  simp [hb]

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

private theorem pg_zsub_zadd_one_cancel (a : Z) :
    Zsub (Zadd a (Zpos xH)) (Zpos xH) = a := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [Zsub, Zadd,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

theorem Zceil_floor_neq (ctx : ExactRealContext) :
    Zceil_floor_neqStatement ctx := by
  intro x hneq
  apply Zceil_imp ctx (Zadd (Exact.Zfloor ctx x) (Zpos xH)) x
  constructor
  · change ctx.spec.lt
      (ctx.spec.ofZ
        (Zsub (Zadd (Exact.Zfloor ctx x) (Zpos xH)) (Zpos xH))) x
    rw [pg_zsub_zadd_one_cancel]
    have hfloor := Zfloor_lb ctx x
    change ctx.spec.ofZ (Exact.Zfloor ctx x) ≠ x at hneq
    have hnot : ¬ ctx.spec.le x (ctx.spec.ofZ (Exact.Zfloor ctx x)) := by
      intro hle
      apply hneq
      exact ctx.certificate.orderedField.le_antisymm _ _ hfloor hle
    exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
      ⟨hfloor, hnot⟩
  · change ctx.spec.le x
      (ctx.spec.ofZ (Zadd (Exact.Zfloor ctx x) (Zpos xH)))
    rw [ctx.certificate.sourceLaws.ofZ_add,
      ctx.certificate.sourceLaws.ofZ_one]
    exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
      (Zfloor_ub ctx x) |>.1

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Ztrunc_ceil (ctx : ExactRealContext) :
    Ztrunc_ceilStatement ctx := by
  intro x hx
  unfold Exact.Ztrunc
  cases h : Exact.Rlt_bool ctx x (Exact.R0 ctx) with
  | true => simp [h]
  | false =>
      have hspec := Rlt_bool_spec ctx x (Exact.R0 ctx)
      rw [h] at hspec
      cases hspec with
      | Rlt_bool_false_ hnot =>
          have hzero : Exact.IZR ctx Z0 = Exact.R0 ctx := by
            exact ctx.certificate.sourceLaws.ofZ_zero
          have hx0 : x = Exact.IZR ctx Z0 := by
            apply ctx.certificate.orderedField.le_antisymm
            · rw [hzero]
              exact hx
            · rw [hzero]
              exact hnot
          rw [hx0]
          have hf : Exact.Zfloor ctx (Exact.IZR ctx Z0) = Z0 :=
            Zfloor_IZR ctx Z0
          have hc : Exact.Zceil ctx (Exact.IZR ctx Z0) = Z0 :=
            Zceil_IZR ctx Z0
          rw [hf, hc]
          simp

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Zaway_ceil (ctx : ExactRealContext) :
    Zaway_ceilStatement ctx := by
  intro x hx
  unfold Exact.Zaway
  have hb := Rlt_bool_false ctx x (Exact.R0 ctx) hx
  simp [hb]

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Zaway_floor (ctx : ExactRealContext) :
    Zaway_floorStatement ctx := by
  intro x hx
  unfold Exact.Zaway
  cases h : Exact.Rlt_bool ctx x (Exact.R0 ctx) with
  | true => simp [h]
  | false =>
      have hspec := Rlt_bool_spec ctx x (Exact.R0 ctx)
      rw [h] at hspec
      cases hspec with
      | Rlt_bool_false_ hzero_le =>
          have hzero : Exact.IZR ctx Z0 = Exact.R0 ctx :=
            ctx.certificate.sourceLaws.ofZ_zero
          have hx0 : x = Exact.IZR ctx Z0 := by
            apply ctx.certificate.orderedField.le_antisymm
            · rw [hzero]
              exact hx
            · rw [hzero]
              exact hzero_le
          rw [hx0, Zfloor_IZR ctx Z0, Zceil_IZR ctx Z0]
          simp

theorem Zaway_opp (ctx : ExactRealContext) :
    Zaway_oppStatement ctx := by
  intro x
  cases h : Exact.Rlt_bool ctx x (Exact.R0 ctx) with
  | true =>
      have hspec := Rlt_bool_spec ctx x (Exact.R0 ctx)
      rw [h] at hspec
      cases hspec with
      | Rlt_bool_true_ hx =>
          have hxle : ctx.spec.le x ctx.spec.zero :=
            (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hx |>.1
          have hnonneg : ctx.spec.le ctx.spec.zero (ctx.spec.neg x) := by
            have hneg := pg_neg_le_contravar ctx hxle
            rw [show ctx.spec.neg ctx.spec.zero = ctx.spec.zero by
              calc
                ctx.spec.neg ctx.spec.zero =
                    ctx.spec.add (ctx.spec.neg ctx.spec.zero) ctx.spec.zero :=
                  (ctx.certificate.orderedField.add_zero _).symm
                _ = ctx.spec.zero :=
                  ctx.certificate.orderedField.neg_add_cancel _] at hneg
            exact hneg
          rw [Zaway_ceil ctx (Exact.Ropp ctx x) hnonneg]
          change Zopp (Exact.Zfloor ctx (Exact.Ropp ctx (Exact.Ropp ctx x))) =
            Zopp (Exact.Zaway ctx x)
          rw [show Exact.Ropp ctx (Exact.Ropp ctx x) = x by
            exact pg_neg_neg ctx x]
          unfold Exact.Zaway
          simp [h]
  | false =>
      have hspec := Rlt_bool_spec ctx x (Exact.R0 ctx)
      rw [h] at hspec
      cases hspec with
      | Rlt_bool_false_ hx =>
          have hnonpos : ctx.spec.le (ctx.spec.neg x) ctx.spec.zero := by
            have hneg := pg_neg_le_contravar ctx hx
            change ctx.spec.le (ctx.spec.neg x)
              (ctx.spec.neg ctx.spec.zero) at hneg
            rw [show ctx.spec.neg ctx.spec.zero = ctx.spec.zero by
              calc
                ctx.spec.neg ctx.spec.zero =
                    ctx.spec.add (ctx.spec.neg ctx.spec.zero) ctx.spec.zero :=
                  (ctx.certificate.orderedField.add_zero _).symm
                _ = ctx.spec.zero :=
                  ctx.certificate.orderedField.neg_add_cancel _] at hneg
            exact hneg
          rw [Zaway_floor ctx (Exact.Ropp ctx x) hnonpos]
          unfold Exact.Zaway
          simp [h]
          unfold Exact.Zceil
          rw [pg_zopp_zopp]

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

private theorem pg_middle_half_add_half (ctx : ExactRealContext) :
    ctx.spec.add (Exact.Rhalf ctx) (Exact.Rhalf ctx) = ctx.spec.one := by
  have hone_pos := exact_zero_lt_one_aux ctx
  have hone_lt_two := ctx.certificate.orderedField.add_lt_compat_l ctx.spec.one
    ctx.spec.zero ctx.spec.one hone_pos
  rw [ctx.certificate.orderedField.add_zero] at hone_lt_two
  have htwo_pos := ctx.certificate.orderedField.lt_trans ctx.spec.zero ctx.spec.one
    (ctx.spec.add ctx.spec.one ctx.spec.one) hone_pos hone_lt_two
  have htwo_ne : ctx.spec.add ctx.spec.one ctx.spec.one ≠ ctx.spec.zero := by
    intro heq
    rw [heq] at htwo_pos
    exact ctx.certificate.orderedField.lt_irrefl ctx.spec.zero htwo_pos
  change ctx.spec.add
    (ctx.spec.div ctx.spec.one (ctx.spec.add ctx.spec.one ctx.spec.one))
    (ctx.spec.div ctx.spec.one (ctx.spec.add ctx.spec.one ctx.spec.one)) =
      ctx.spec.one
  rw [ctx.certificate.orderedField.div_eq_mul_inv,
    ctx.certificate.orderedField.one_mul]
  calc
    ctx.spec.add
        (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))
        (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)) =
      ctx.spec.add
        (ctx.spec.mul (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))
          ctx.spec.one)
        (ctx.spec.mul (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))
          ctx.spec.one) := by
            rw [ctx.certificate.orderedField.mul_one]
    _ = ctx.spec.mul
        (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))
        (ctx.spec.add ctx.spec.one ctx.spec.one) :=
      (ctx.certificate.orderedField.left_distrib
        (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))
        ctx.spec.one ctx.spec.one).symm
    _ = ctx.spec.one :=
      ctx.certificate.orderedField.inv_mul_cancel _ htwo_ne

private theorem pg_middle_complement_sum (ctx : ExactRealContext)
    (x f : ctx.spec.carrier) :
    ctx.spec.add (ctx.spec.add x (ctx.spec.neg f))
        (ctx.spec.add (ctx.spec.add f ctx.spec.one) (ctx.spec.neg x)) =
      ctx.spec.one := by
  calc
    ctx.spec.add (ctx.spec.add x (ctx.spec.neg f))
        (ctx.spec.add (ctx.spec.add f ctx.spec.one) (ctx.spec.neg x)) =
      ctx.spec.add x
        (ctx.spec.add (ctx.spec.neg f)
          (ctx.spec.add (ctx.spec.add f ctx.spec.one) (ctx.spec.neg x))) :=
      ctx.certificate.orderedField.add_assoc _ _ _
    _ = ctx.spec.add x
        (ctx.spec.add
          (ctx.spec.add (ctx.spec.neg f) (ctx.spec.add f ctx.spec.one))
          (ctx.spec.neg x)) := by
      apply congrArg (fun t => ctx.spec.add x t)
      exact (ctx.certificate.orderedField.add_assoc
        (ctx.spec.neg f) (ctx.spec.add f ctx.spec.one) (ctx.spec.neg x)).symm
    _ = ctx.spec.add x
        (ctx.spec.add
          (ctx.spec.add (ctx.spec.add (ctx.spec.neg f) f) ctx.spec.one)
          (ctx.spec.neg x)) := by
      apply congrArg (fun t => ctx.spec.add x
        (ctx.spec.add t (ctx.spec.neg x)))
      exact (ctx.certificate.orderedField.add_assoc
        (ctx.spec.neg f) f ctx.spec.one).symm
    _ = ctx.spec.add x
        (ctx.spec.add ctx.spec.one (ctx.spec.neg x)) := by
      rw [ctx.certificate.orderedField.neg_add_cancel,
        ctx.certificate.orderedField.zero_add]
    _ = ctx.spec.add (ctx.spec.add x ctx.spec.one) (ctx.spec.neg x) := by
      rw [ctx.certificate.orderedField.add_assoc]
    _ = ctx.spec.add (ctx.spec.add ctx.spec.one x) (ctx.spec.neg x) := by
      rw [ctx.certificate.orderedField.add_comm x ctx.spec.one]
    _ = ctx.spec.add ctx.spec.one (ctx.spec.add x (ctx.spec.neg x)) :=
      ctx.certificate.orderedField.add_assoc _ _ _
    _ = ctx.spec.add ctx.spec.one ctx.spec.zero := by
      rw [ctx.certificate.orderedField.add_comm x (ctx.spec.neg x),
        ctx.certificate.orderedField.neg_add_cancel]
    _ = ctx.spec.one := ctx.certificate.orderedField.add_zero _

private theorem pg_Rcompare_middle_of_complement (ctx : ExactRealContext)
    (a b : ctx.spec.carrier)
    (hsum : ctx.spec.add a b = ctx.spec.one) :
    Exact.Rcompare ctx a (Exact.Rhalf ctx) = Exact.Rcompare ctx a b := by
  have hhalf := pg_middle_half_add_half ctx
  rcases ctx.certificate.total_order a (Exact.Rhalf ctx) with h | hgt
  · rcases h with hlt | heq
    ·
      have h1 := ctx.certificate.orderedField.add_lt_compat_l a a
        (Exact.Rhalf ctx) hlt
      have h2 := ctx.certificate.orderedField.add_lt_compat_l
        (Exact.Rhalf ctx) a (Exact.Rhalf ctx) hlt
      rw [ctx.certificate.orderedField.add_comm (Exact.Rhalf ctx) a] at h2
      have hab_add := ctx.certificate.orderedField.lt_trans _ _ _ h1 h2
      rw [hhalf, ← hsum] at hab_add
      have hab :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_lt_reg_l
          ctx a a b hab_add
      rw [Rcompare_Lt ctx a (Exact.Rhalf ctx) hlt,
        Rcompare_Lt ctx a b hab]
    ·
      have haa : ctx.spec.add a a = ctx.spec.one := by
        rw [heq]
        exact hhalf
      have hab :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_eq_reg_l
          ctx a a b (haa.trans hsum.symm)
      rw [Rcompare_Eq ctx a (Exact.Rhalf ctx) heq,
        Rcompare_Eq ctx a b hab]
  ·
      have h1 := ctx.certificate.orderedField.add_lt_compat_l
        (Exact.Rhalf ctx) (Exact.Rhalf ctx) a hgt
      have h2 := ctx.certificate.orderedField.add_lt_compat_l a
        (Exact.Rhalf ctx) a hgt
      rw [ctx.certificate.orderedField.add_comm a (Exact.Rhalf ctx)] at h2
      have hba_add := ctx.certificate.orderedField.lt_trans _ _ _ h1 h2
      rw [hhalf, ← hsum] at hba_add
      have hba :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_lt_reg_l
          ctx a b a hba_add
      rw [Rcompare_Gt ctx a (Exact.Rhalf ctx) hgt,
        Rcompare_Gt ctx a b hba]

theorem Rcompare_floor_ceil_middle (ctx : ExactRealContext) :
    Rcompare_floor_ceil_middleStatement ctx := by
  intro x hx
  have hceil := Zceil_floor_neq ctx x hx
  have hsum :
      ctx.spec.add
        (ctx.spec.add x (ctx.spec.neg (ctx.spec.ofZ (Exact.Zfloor ctx x))))
        (ctx.spec.add (ctx.spec.ofZ (Exact.Zceil ctx x)) (ctx.spec.neg x)) =
      ctx.spec.one := by
    rw [hceil, ctx.certificate.sourceLaws.ofZ_add,
      ctx.certificate.sourceLaws.ofZ_one]
    exact pg_middle_complement_sum ctx x (ctx.spec.ofZ (Exact.Zfloor ctx x))
  exact pg_Rcompare_middle_of_complement ctx
    (Exact.Rminus ctx x (Exact.IZR ctx (Exact.Zfloor ctx x)))
    (Exact.Rminus ctx (Exact.IZR ctx (Exact.Zceil ctx x)) x) hsum

theorem Rcompare_ceil_floor_middle (ctx : ExactRealContext) :
    Rcompare_ceil_floor_middleStatement ctx := by
  intro x hx
  have hceil := Zceil_floor_neq ctx x hx
  have hsum :
      ctx.spec.add
        (ctx.spec.add x (ctx.spec.neg (ctx.spec.ofZ (Exact.Zfloor ctx x))))
        (ctx.spec.add (ctx.spec.ofZ (Exact.Zceil ctx x)) (ctx.spec.neg x)) =
      ctx.spec.one := by
    rw [hceil, ctx.certificate.sourceLaws.ofZ_add,
      ctx.certificate.sourceLaws.ofZ_one]
    exact pg_middle_complement_sum ctx x (ctx.spec.ofZ (Exact.Zfloor ctx x))
  have hsum' :
      ctx.spec.add
        (ctx.spec.add (ctx.spec.ofZ (Exact.Zceil ctx x)) (ctx.spec.neg x))
        (ctx.spec.add x (ctx.spec.neg (ctx.spec.ofZ (Exact.Zfloor ctx x)))) =
      ctx.spec.one :=
    (ctx.certificate.orderedField.add_comm _ _).trans hsum
  exact pg_Rcompare_middle_of_complement ctx
    (Exact.Rminus ctx (Exact.IZR ctx (Exact.Zceil ctx x)) x)
    (Exact.Rminus ctx x (Exact.IZR ctx (Exact.Zfloor ctx x))) hsum'

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem radix_pos (ctx : ExactRealContext) :
    radix_posStatement ctx := by
  intro r
  change ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ r.radix_val)
  exact exact_radix_pos_aux ctx r

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem IZR_Zpower_pos (ctx : ExactRealContext) : IZR_Zpower_posStatement ctx := by
  intro n m
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.peano_ind
    (P := fun m => Exact.IZR ctx (Zpower_pos n m) =
      Exact.powerRZ ctx (Exact.IZR ctx n) (Zpos m))
  · rw [pg_zpower_pos_one]
    change Exact.IZR ctx n = ctx.spec.mul (Exact.IZR ctx n) ctx.spec.one
    exact (ctx.certificate.orderedField.mul_one _).symm
  · intro m ih
    change Exact.IZR ctx
        (Zpower_pos n
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ m)) =
      CompCert4Lean.Foundation.FlocqReal.ExactReal.powerNat ctx.spec
        (Exact.IZR ctx n)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ m))
    rw [pg_zpower_pos_succ]
    have hmul :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR ctx
        (Zpower_pos n m) n
    rw [show Exact.IZR ctx
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
          (Zpower_pos n m) n) =
        ctx.spec.mul (Exact.IZR ctx (Zpower_pos n m))
          (Exact.IZR ctx n) by exact hmul]
    rw [ih, pg_posToNat_succ]
    rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m + 1 =
        Nat.succ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m) by omega]
    change ctx.spec.mul
        (CompCert4Lean.Foundation.FlocqReal.ExactReal.powerNat ctx.spec
          (Exact.IZR ctx n)
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m))
        (Exact.IZR ctx n) =
      ctx.spec.mul (Exact.IZR ctx n)
        (CompCert4Lean.Foundation.FlocqReal.ExactReal.powerNat ctx.spec
          (Exact.IZR ctx n)
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m))
    rw [ctx.certificate.orderedField.mul_comm]

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem bpow_powerRZ (ctx : ExactRealContext) :
    bpow_powerRZStatement ctx := by
  intro r e
  exact pg_bpow_powerRZ ctx r e

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem bpow_opp (ctx : ExactRealContext) : bpow_oppStatement ctx := by
  intro r e
  cases e with
  | Z0 =>
      change ctx.spec.one = ctx.spec.inv ctx.spec.one
      have hone : ctx.spec.one ≠ ctx.spec.zero := by
        intro h
        exact ctx.certificate.orderedField.zero_ne_one h.symm
      calc
        ctx.spec.one = ctx.spec.mul (ctx.spec.inv ctx.spec.one) ctx.spec.one :=
          (ctx.certificate.orderedField.inv_mul_cancel ctx.spec.one hone).symm
        _ = ctx.spec.inv ctx.spec.one :=
          ctx.certificate.orderedField.mul_one _
  | Zpos p =>
      have hz : Zopp (Zpos p) = Zneg p := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [Zopp,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        rfl
      rw [hz]
      rfl
  | Zneg p =>
      have hz : Zopp (Zneg p) = Zpos p := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [Zopp,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
      rw [hz]
      change ctx.spec.ofZ (Zpower_pos r.radix_val p) =
        ctx.spec.inv (ctx.spec.inv (ctx.spec.ofZ (Zpower_pos r.radix_val p)))
      have hxpos := bpow_gt_0 ctx r (Zpos p)
      change ctx.spec.lt ctx.spec.zero
        (ctx.spec.ofZ (Zpower_pos r.radix_val p)) at hxpos
      have hx0 : ctx.spec.ofZ (Zpower_pos r.radix_val p) ≠
          Exact.IZR ctx Z0 := by
        intro h
        change ctx.spec.ofZ (Zpower_pos r.radix_val p) = ctx.spec.ofZ Z0 at h
        rw [ctx.certificate.sourceLaws.ofZ_zero] at h
        rw [h] at hxpos
        exact ctx.certificate.orderedField.lt_irrefl _ hxpos
      exact (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rinv_involutive_proof
        ctx (ctx.spec.ofZ (Zpower_pos r.radix_val p)) hx0).symm

theorem bpow_lt (ctx : ExactRealContext) : bpow_ltStatement ctx := by
  intro r e1 e2 h
  exact pg_bpow_lt ctx r h

theorem bpow_le (ctx : ExactRealContext) : bpow_leStatement ctx := by
  intro r e1 e2 h
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 at h
  rcases Int.lt_or_eq_of_le h with hlt | heq
  · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
      (pg_bpow_lt ctx r (show Zlt e1 e2 by exact hlt)) |>.1
  · have he : e1 = e2 :=
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective heq
    subst e2
    exact ctx.certificate.orderedField.le_refl _

theorem le_bpow (ctx : ExactRealContext) : le_bpowStatement ctx := by
  intro r e1 e2 h
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2
  apply Int.le_of_not_gt
  intro hlt
  have hp := pg_bpow_lt ctx r (show Zlt e2 e1 by exact hlt)
  exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hp).2 h

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem bpow_inj : ∀ (ctx : ExactRealContext), bpow_injStatement ctx := by
  intro ctx r e1 e2 h
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  by_cases heq :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2
  · exact heq
  · rcases Int.lt_or_gt_of_ne heq with h12 | h21
    · have hp := bpow_lt ctx r e1 e2 (show Zlt e1 e2 by exact h12)
      rw [h] at hp
      exact (ctx.certificate.orderedField.lt_irrefl _ hp).elim
    · have hp := bpow_lt ctx r e2 e1 (show Zlt e2 e1 by exact h21)
      rw [h] at hp
      exact (ctx.certificate.orderedField.lt_irrefl _ hp).elim

theorem bpow_lt_bpow :
    ∀ (ctx : ExactRealContext), bpow_lt_bpowStatement ctx := by
  intro ctx r e1 e2 h
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2
  apply Int.le_of_not_gt
  intro hgt
  have hle : Zle e2 (Zsub e1 (Zpos xH)) := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zsub e1 (Zpos xH))
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 - 1
    omega
  have hp := bpow_le ctx r e2 (Zsub e1 (Zpos xH)) hle
  exact (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h).2 hp).elim

theorem bpow_unique :
    ∀ (ctx : ExactRealContext), bpow_uniqueStatement ctx := by
  intro ctx r x e1 e2 h1 h2
  have h12 : Zle e1 e2 :=
    bpow_lt_bpow ctx r e1 e2
      (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
        ctx _ _ _ h1.1 h2.2)
  have h21 : Zle e2 e1 :=
    bpow_lt_bpow ctx r e2 e1
      (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
        ctx _ _ _ h2.1 h1.2)
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 at h12
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 at h21
  omega

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

private theorem pg_exact_ln_of_pos_suffix (ctx : ExactRealContext)
    {x : Exact.R ctx} (hx : Exact.Rlt ctx (ctx.spec.zero) x) :
    Exact.ln ctx x = ctx.spec.ln x := by
  unfold Exact.ln
  cases hdec : ctx.spec.lt_dec ctx.spec.zero x with
  | left _ => simp [CompCert4Lean.Foundation.FlocqReal.ExactReal.ln, hdec]
  | right hnon => exact (hnon hx).elim

private theorem pg_bpow_exp_pos_suffix (ctx : ExactRealContext) (r : radix) :
    ∀ p : positive,
      Exact.IZR ctx (Zpower_pos r.radix_val p) =
        ctx.spec.exp (ctx.spec.mul
          (Exact.IZR ctx (Zpos p))
          (ctx.spec.ln (Exact.IZR ctx r.radix_val))) := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.peano_ind
    (P := fun p => Exact.IZR ctx (Zpower_pos r.radix_val p) =
      ctx.spec.exp (ctx.spec.mul
        (Exact.IZR ctx (Zpos p))
        (ctx.spec.ln (Exact.IZR ctx r.radix_val))))
  · rw [pg_zpower_pos_one]
    have hrpos : Exact.Rlt ctx (ctx.spec.zero)
        (Exact.IZR ctx r.radix_val) := radix_pos ctx r
    have hbase := ctx.certificate.ln.exp_ln
      (Exact.IZR ctx r.radix_val) hrpos
    change ctx.spec.ofZ r.radix_val =
      ctx.spec.exp (ctx.spec.mul
        (ctx.spec.ofZ (Zpos xH))
        (ctx.spec.ln (ctx.spec.ofZ r.radix_val)))
    rw [ctx.certificate.sourceLaws.ofZ_one,
      ctx.certificate.orderedField.one_mul]
    exact hbase.symm
  · intro p ih
    have hz : Zpos (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ p) =
        Zadd (Zpos p) (Zpos xH) := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      change Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ p)) =
        Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) + 1
      rw [pg_posToNat_succ]
      simpa using
        (Int.ofNat_add_ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) 1).symm
    have harg :
        ctx.spec.add
            (ctx.spec.mul (Exact.IZR ctx (Zpos p))
              (ctx.spec.ln (Exact.IZR ctx r.radix_val)))
            (ctx.spec.ln (Exact.IZR ctx r.radix_val)) =
          ctx.spec.mul
            (Exact.IZR ctx
              (Zpos (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ p)))
            (ctx.spec.ln (Exact.IZR ctx r.radix_val)) := by
      have hpone : Exact.IZR ctx
          (Zpos (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ p)) =
          ctx.spec.add (Exact.IZR ctx (Zpos p)) ctx.spec.one := by
        rw [hz]
        change ctx.spec.ofZ (Zadd (Zpos p) (Zpos xH)) =
          ctx.spec.add (ctx.spec.ofZ (Zpos p)) ctx.spec.one
        rw [ctx.certificate.sourceLaws.ofZ_add,
          ctx.certificate.sourceLaws.ofZ_one]
      calc
        ctx.spec.add
            (ctx.spec.mul (Exact.IZR ctx (Zpos p))
              (ctx.spec.ln (Exact.IZR ctx r.radix_val)))
            (ctx.spec.ln (Exact.IZR ctx r.radix_val)) =
            ctx.spec.add
              (ctx.spec.mul (ctx.spec.ln (Exact.IZR ctx r.radix_val))
                (Exact.IZR ctx (Zpos p)))
              (ctx.spec.mul (ctx.spec.ln (Exact.IZR ctx r.radix_val))
                ctx.spec.one) := by
          rw [ctx.certificate.orderedField.mul_comm,
            ctx.certificate.orderedField.mul_comm,
            ctx.certificate.orderedField.mul_one]
        _ = ctx.spec.mul
              (ctx.spec.add (Exact.IZR ctx (Zpos p)) ctx.spec.one)
              (ctx.spec.ln (Exact.IZR ctx r.radix_val)) := by
          rw [← ctx.certificate.orderedField.left_distrib,
            ctx.certificate.orderedField.mul_comm]
        _ = ctx.spec.mul
            (Exact.IZR ctx
              (Zpos (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ p)))
            (ctx.spec.ln (Exact.IZR ctx r.radix_val)) := by
          rw [hpone]
    change Exact.IZR ctx
        (Zpower_pos r.radix_val
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ p)) =
      ctx.spec.exp (ctx.spec.mul
        (Exact.IZR ctx
          (Zpos (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ p)))
        (ctx.spec.ln (Exact.IZR ctx r.radix_val)))
    rw [pg_zpower_pos_succ]
    have hmul :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR ctx
        (Zpower_pos r.radix_val p) r.radix_val
    rw [show Exact.IZR ctx
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
          (Zpower_pos r.radix_val p) r.radix_val) =
        ctx.spec.mul (Exact.IZR ctx (Zpower_pos r.radix_val p))
          (Exact.IZR ctx r.radix_val) by exact hmul]
    rw [ih]
    have hrpos : Exact.Rlt ctx (ctx.spec.zero)
        (Exact.IZR ctx r.radix_val) := radix_pos ctx r
    have hbase := ctx.certificate.ln.exp_ln
      (Exact.IZR ctx r.radix_val) hrpos
    calc
      ctx.spec.mul
          (ctx.spec.exp (ctx.spec.mul (Exact.IZR ctx (Zpos p))
            (ctx.spec.ln (Exact.IZR ctx r.radix_val))))
          (Exact.IZR ctx r.radix_val) =
          ctx.spec.mul
            (ctx.spec.exp (ctx.spec.mul (Exact.IZR ctx (Zpos p))
              (ctx.spec.ln (Exact.IZR ctx r.radix_val))))
            (ctx.spec.exp (ctx.spec.ln (Exact.IZR ctx r.radix_val))) := by
        rw [hbase]
      _ = ctx.spec.exp
          (ctx.spec.add (ctx.spec.mul (Exact.IZR ctx (Zpos p))
            (ctx.spec.ln (Exact.IZR ctx r.radix_val)))
            (ctx.spec.ln (Exact.IZR ctx r.radix_val))) :=
        (ctx.certificate.exp.add _ _).symm
      _ = ctx.spec.exp
          (ctx.spec.mul
            (Exact.IZR ctx
              (Zpos (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.succ p)))
            (ctx.spec.ln (Exact.IZR ctx r.radix_val))) := by
        rw [harg]

theorem bpow_exp :
    ∀ (ctx : ExactRealContext), bpow_expStatement ctx := by
  intro ctx r e
  cases e with
  | Z0 =>
      have hrpos : Exact.Rlt ctx (ctx.spec.zero)
          (Exact.IZR ctx r.radix_val) := radix_pos ctx r
      have hln := pg_exact_ln_of_pos_suffix ctx hrpos
      change Exact.Rone ctx =
        ctx.spec.exp (ctx.spec.mul
          (Exact.IZR ctx Z0) (Exact.ln ctx (Exact.IZR ctx r.radix_val)))
      rw [hln]
      change ctx.spec.one =
        ctx.spec.exp (ctx.spec.mul
          (ctx.spec.ofZ Z0) (ctx.spec.ln (ctx.spec.ofZ r.radix_val)))
      rw [ctx.certificate.sourceLaws.ofZ_zero,
        ctx.certificate.orderedField.zero_mul,
        ctx.certificate.exp.zero]
  | Zpos p =>
      change Exact.IZR ctx (Zpower_pos r.radix_val p) = _
      rw [pg_exact_ln_of_pos_suffix ctx (radix_pos ctx r)]
      exact pg_bpow_exp_pos_suffix ctx r p
  | Zneg p =>
      simp only [Exact.bpow, Exact.exp, Exact.Rmult]
      rw [pg_exact_ln_of_pos_suffix ctx (radix_pos ctx r)]
      change ctx.spec.inv (Exact.IZR ctx (Zpower_pos r.radix_val p)) =
        ctx.spec.exp (ctx.spec.mul
          (Exact.IZR ctx (Zneg p)) (ctx.spec.ln (Exact.IZR ctx r.radix_val)))
      rw [pg_bpow_exp_pos_suffix ctx r p]
      have hz : Zneg p = Zopp (Zpos p) := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [Zopp,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        rfl
      rw [hz]
      change ctx.spec.inv (ctx.spec.exp (ctx.spec.mul
          (Exact.IZR ctx (Zpos p))
          (ctx.spec.ln (Exact.IZR ctx r.radix_val)))) =
        ctx.spec.exp (ctx.spec.mul
          (ctx.spec.ofZ (Zopp (Zpos p)))
          (ctx.spec.ln (Exact.IZR ctx r.radix_val)))
      rw [ctx.certificate.sourceLaws.ofZ_neg]
      have hnegmul :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_mult_distr_l_reverse
          ctx (ctx.spec.ofZ (Zpos p)) (ctx.spec.ln (Exact.IZR ctx r.radix_val))
      have hnegmul' :
          ctx.spec.mul (ctx.spec.neg (ctx.spec.ofZ (Zpos p)))
              (ctx.spec.ln (Exact.IZR ctx r.radix_val)) =
            ctx.spec.neg (ctx.spec.mul (ctx.spec.ofZ (Zpos p))
              (ctx.spec.ln (Exact.IZR ctx r.radix_val))) := by
        exact hnegmul
      rw [hnegmul']
      rw [ctx.certificate.sourceLaws.exp_opp]
      change ctx.spec.inv (ctx.spec.exp (ctx.spec.mul
          (ctx.spec.ofZ (Zpos p))
          (ctx.spec.ln (Exact.IZR ctx r.radix_val)))) =
        ctx.spec.inv (ctx.spec.exp (ctx.spec.mul
          (ctx.spec.ofZ (Zpos p))
          (ctx.spec.ln (Exact.IZR ctx r.radix_val))))
      rfl

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

private theorem pg_worker_neg_zero (ctx : ExactRealContext) :
    Exact.Ropp ctx (Exact.R0 ctx) = Exact.R0 ctx := by
  change ctx.spec.neg ctx.spec.zero = ctx.spec.zero
  have h := ctx.certificate.orderedField.neg_add_cancel ctx.spec.zero
  rw [ctx.certificate.orderedField.add_zero] at h
  exact h

private theorem pg_worker_neg_neg (ctx : ExactRealContext) (x : Exact.R ctx) :
    Exact.Ropp ctx (Exact.Ropp ctx x) = x := by
  change ctx.spec.neg (ctx.spec.neg x) = x
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

private theorem pg_worker_abs_opp (ctx : ExactRealContext) (x : Exact.R ctx) :
    Exact.Rabs ctx (Exact.Ropp ctx x) = Exact.Rabs ctx x := by
  change ctx.spec.abs (ctx.spec.neg x) = ctx.spec.abs x
  rcases ctx.certificate.total_order x ctx.spec.zero with h | h
  · rcases h with hlt | heq
    · have hneg : ctx.spec.le ctx.spec.zero (ctx.spec.neg x) := by
        have hh := ctx.certificate.orderedField.add_lt_compat_l
          (ctx.spec.neg x) x ctx.spec.zero hlt
        rw [ctx.certificate.orderedField.neg_add_cancel,
          ctx.certificate.orderedField.add_zero] at hh
        exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hh |>.1
      rw [ctx.certificate.sourceLaws.abs_nonnegative _ hneg,
        ctx.certificate.sourceLaws.abs_negative x hlt]
    · subst x
      exact congrArg (fun z => ctx.spec.abs z) (pg_worker_neg_zero ctx)
  · have hneglt : ctx.spec.lt (ctx.spec.neg x) ctx.spec.zero := by
      have hh := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.neg x) ctx.spec.zero x h
      rw [ctx.certificate.orderedField.neg_add_cancel,
        ctx.certificate.orderedField.add_zero] at hh
      exact hh
    calc
      ctx.spec.abs (ctx.spec.neg x) = ctx.spec.neg (ctx.spec.neg x) :=
        ctx.certificate.sourceLaws.abs_negative _ hneglt
      _ = x := pg_worker_neg_neg ctx x
      _ = ctx.spec.abs x :=
        (ctx.certificate.sourceLaws.abs_nonnegative _
          ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1)).symm

private theorem pg_worker_abs_nonneg (ctx : ExactRealContext) (x : Exact.R ctx) :
    ctx.spec.le ctx.spec.zero (ctx.spec.abs x) := by
  rcases ctx.certificate.total_order x ctx.spec.zero with h | h
  · rcases h with hlt | heq
    · rw [ctx.certificate.sourceLaws.abs_negative x hlt]
      have hh := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.neg x) x ctx.spec.zero hlt
      rw [ctx.certificate.orderedField.neg_add_cancel,
        ctx.certificate.orderedField.add_zero] at hh
      exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hh |>.1
    · subst x
      rw [ctx.certificate.sourceLaws.abs_nonnegative _
        (ctx.certificate.orderedField.le_refl _)]
      exact ctx.certificate.orderedField.le_refl _
  · have hle := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1
    rw [ctx.certificate.sourceLaws.abs_nonnegative x hle]
    exact hle

theorem mag_unique :
    ∀ (ctx : ExactRealContext) (m : Exact.Magnitude ctx),
      mag_uniqueStatement ctx m := by
  intro ctx m r x e h
  by_cases hx : x = Exact.R0 ctx
  · subst x
    have habs : Exact.Rabs ctx (Exact.R0 ctx) = Exact.R0 ctx := by
      change ctx.spec.abs ctx.spec.zero = ctx.spec.zero
      exact ctx.certificate.sourceLaws.abs_nonnegative _
        (ctx.certificate.orderedField.le_refl _)
    rw [habs] at h
    have hpos := bpow_gt_0 ctx r (Zsub e (Zpos xH))
    have hnot := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hpos |>.2
    exact (hnot h.1).elim
  · have hm := (Exact.mag m r x).mag_bound hx
    exact bpow_unique ctx r (Exact.Rabs ctx x)
      (Exact.mag m r x).mag_val e hm h

theorem mag_opp :
    ∀ (ctx : ExactRealContext) (m : Exact.Magnitude ctx),
      mag_oppStatement ctx m := by
  intro ctx m r x
  by_cases hx : x = Exact.R0 ctx
  · subst x
    rw [pg_worker_neg_zero]
  · have hm := (Exact.mag m r x).mag_bound hx
    have habs := pg_worker_abs_opp ctx x
    have h' :
        Exact.Rle ctx
            (Exact.bpow ctx r
              (Zsub (Exact.mag m r x).mag_val (Zpos xH)))
            (Exact.Rabs ctx (Exact.Ropp ctx x)) ∧
          Exact.Rlt ctx (Exact.Rabs ctx (Exact.Ropp ctx x))
            (Exact.bpow ctx r (Exact.mag m r x).mag_val) := by
      simpa only [habs] using hm
    exact mag_unique ctx m r (Exact.Ropp ctx x)
      (Exact.mag m r x).mag_val h'

theorem mag_abs :
    ∀ (ctx : ExactRealContext) (m : Exact.Magnitude ctx),
      mag_absStatement ctx m := by
  intro ctx m r x
  by_cases hx : x = Exact.R0 ctx
  · subst x
    have habs : Exact.Rabs ctx (Exact.R0 ctx) = Exact.R0 ctx := by
      change ctx.spec.abs ctx.spec.zero = ctx.spec.zero
      exact ctx.certificate.sourceLaws.abs_nonnegative _
        (ctx.certificate.orderedField.le_refl _)
    rw [habs]
  · have hm := (Exact.mag m r x).mag_bound hx
    have habsn : Exact.Rabs ctx (Exact.Rabs ctx x) = Exact.Rabs ctx x := by
      change ctx.spec.abs (ctx.spec.abs x) = ctx.spec.abs x
      exact ctx.certificate.sourceLaws.abs_nonnegative _
        (pg_worker_abs_nonneg ctx x)
    have h' :
        Exact.Rle ctx
            (Exact.bpow ctx r
              (Zsub (Exact.mag m r x).mag_val (Zpos xH)))
            (Exact.Rabs ctx (Exact.Rabs ctx x)) ∧
          Exact.Rlt ctx (Exact.Rabs ctx (Exact.Rabs ctx x))
            (Exact.bpow ctx r (Exact.mag m r x).mag_val) := by
      simpa only [habsn] using hm
    exact mag_unique ctx m r (Exact.Rabs ctx x)
      (Exact.mag m r x).mag_val h'

theorem mag_unique_pos :
    ∀ (ctx : ExactRealContext) (m : Exact.Magnitude ctx),
      mag_unique_posStatement ctx m := by
  intro ctx m r x e h
  have hnonneg : Exact.Rle ctx (ctx.spec.zero) x := by
    have hpow : Exact.Rle ctx (ctx.spec.zero)
        (Exact.bpow ctx r (Zsub e (Zpos xH))) :=
      bpow_ge_0 ctx r (Zsub e (Zpos xH))
    exact ctx.certificate.orderedField.le_trans _ _ _ hpow h.1
  have habs : Exact.Rabs ctx x = x := by
    change ctx.spec.abs x = x
    exact ctx.certificate.sourceLaws.abs_nonnegative x hnonneg
  apply mag_unique ctx m r x e
  rw [habs]
  exact h

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

private theorem pg_worker_abs_ne_zero (ctx : ExactRealContext) {x : Exact.R ctx}
    (hx : x ≠ Exact.R0 ctx) : Exact.Rabs ctx x ≠ Exact.R0 ctx := by
  change ctx.spec.abs x ≠ ctx.spec.zero
  rcases ctx.certificate.total_order x ctx.spec.zero with h | h
  · rcases h with hlt | heq
    · rw [ctx.certificate.sourceLaws.abs_negative x hlt]
      have hneg : ctx.spec.neg x ≠ ctx.spec.zero := by
        intro hn
        have hsum := congrArg (fun z => ctx.spec.add x z) hn
        rw [ctx.certificate.orderedField.add_comm x,
          ctx.certificate.orderedField.neg_add_cancel,
          ctx.certificate.orderedField.add_zero] at hsum
        exact hx hsum.symm
      exact hneg
    · exact (hx heq).elim
  · have hle := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1
    rw [ctx.certificate.sourceLaws.abs_nonnegative x hle]
    exact hx

theorem mag_le_abs :
    ∀ (ctx : ExactRealContext) (m : Exact.Magnitude ctx),
      mag_le_absStatement ctx m := by
  intro ctx m r x y hx hxy
  have hy : y ≠ Exact.R0 ctx := by
    intro hy0
    subst y
    have hzero : Exact.Rabs ctx (Exact.R0 ctx) = Exact.R0 ctx := by
      change ctx.spec.abs ctx.spec.zero = ctx.spec.zero
      exact ctx.certificate.sourceLaws.abs_nonnegative _
        (ctx.certificate.orderedField.le_refl _)
    have haxle : Exact.Rle ctx (Exact.Rabs ctx x) (Exact.R0 ctx) := by
      simpa only [hzero] using hxy
    have haxzero : Exact.Rabs ctx x = Exact.R0 ctx := by
      apply ctx.certificate.orderedField.le_antisymm _ _ haxle
      exact pg_worker_abs_nonneg ctx x
    exact (pg_worker_abs_ne_zero ctx hx) haxzero
  have hxmag := (Exact.mag m r x).mag_bound hx
  have hymag := (Exact.mag m r y).mag_bound hy
  apply bpow_lt_bpow ctx r
  exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
    ctx _ _ _ hxmag.1
    (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
      ctx _ _ _ hxy hymag.2)

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem mag_le :
    ∀ (ctx : ExactRealContext) (m : Exact.Magnitude ctx),
      mag_leStatement ctx m := by
  intro ctx m r x y hx hxy
  have hx0 : x ≠ Exact.R0 ctx := by
    intro hxz
    subst x
    exact (ctx.certificate.orderedField.lt_irrefl _ hx).elim
  have hxle : Exact.Rle ctx (ctx.spec.zero) x :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hx |>.1
  have hyle : Exact.Rle ctx (ctx.spec.zero) y :=
    ctx.certificate.orderedField.le_trans _ _ _ hxle hxy
  have habsx : Exact.Rabs ctx x = x := by
    change ctx.spec.abs x = x
    exact ctx.certificate.sourceLaws.abs_nonnegative x hxle
  have habsy : Exact.Rabs ctx y = y := by
    change ctx.spec.abs y = y
    exact ctx.certificate.sourceLaws.abs_nonnegative y hyle
  apply mag_le_abs ctx m r x y hx0
  simpa only [habsx, habsy] using hxy

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem lt_mag :
    ∀ (ctx : ExactRealContext) (m : Exact.Magnitude ctx),
      lt_magStatement ctx m := by
  intro ctx m r x y hy hmag
  by_cases hxle : Exact.Rle ctx x (ctx.spec.zero)
  · exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
      ctx _ _ _ hxle hy
  · have hxpos : Exact.Rlt ctx (ctx.spec.zero) x := by
      rcases ctx.certificate.total_order ctx.spec.zero x with h | h
      · rcases h with hlt | heq
        · exact hlt
        · exact (hxle (by rw [heq]; exact
              ctx.certificate.orderedField.le_refl _)).elim
      · exact (hxle ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h).1).elim
    have hx0 : x ≠ Exact.R0 ctx := by
      intro hxz
      subst x
      exact (ctx.certificate.orderedField.lt_irrefl _ hxpos).elim
    have hy0 : y ≠ Exact.R0 ctx := by
      intro hyz
      subst y
      exact (ctx.certificate.orderedField.lt_irrefl _ hy).elim
    have hxle0 : Exact.Rle ctx (ctx.spec.zero) x :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxpos |>.1
    have hyle0 : Exact.Rle ctx (ctx.spec.zero) y :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hy |>.1
    have habsx : Exact.Rabs ctx x = x := by
      change ctx.spec.abs x = x
      exact ctx.certificate.sourceLaws.abs_nonnegative x hxle0
    have habsy : Exact.Rabs ctx y = y := by
      change ctx.spec.abs y = y
      exact ctx.certificate.sourceLaws.abs_nonnegative y hyle0
    have hxm := (Exact.mag m r x).mag_bound hx0
    have hym := (Exact.mag m r y).mag_bound hy0
    have hexle : Zle (Exact.mag m r x).mag_val
        (Zsub (Exact.mag m r y).mag_val (Zpos xH)) := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Exact.mag m r x).mag_val ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Zsub (Exact.mag m r y).mag_val (Zpos xH))
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Exact.mag m r x).mag_val ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Exact.mag m r y).mag_val - 1
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Exact.mag m r x).mag_val <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Exact.mag m r y).mag_val at hmag
      omega
    have hpow := bpow_le ctx r (Exact.mag m r x).mag_val
      (Zsub (Exact.mag m r y).mag_val (Zpos xH)) hexle
    have hupper : Exact.Rlt ctx x
        (Exact.bpow ctx r (Exact.mag m r x).mag_val) := by
      simpa only [habsx] using hxm.2
    have hlower : Exact.Rle ctx
        (Exact.bpow ctx r (Zsub (Exact.mag m r y).mag_val (Zpos xH))) y := by
      simpa only [habsy] using hym.1
    exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
      ctx _ _ _ hupper
      (ctx.certificate.orderedField.le_trans _ _ _ hpow hlower)

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem mag_bpow :
    ∀ (ctx : ExactRealContext) (m : Exact.Magnitude ctx),
      mag_bpowStatement ctx m := by
  intro ctx m r e
  have habs : Exact.Rabs ctx (Exact.bpow ctx r e) = Exact.bpow ctx r e := by
    change ctx.spec.abs (Exact.bpow ctx r e) = Exact.bpow ctx r e
    exact ctx.certificate.sourceLaws.abs_nonnegative _ (bpow_ge_0 ctx r e)
  have hz : Zsub (Zadd e (Zpos xH)) (Zpos xH) = e := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    omega
  have hlt : Exact.Rlt ctx (Exact.bpow ctx r e)
      (Exact.bpow ctx r (Zadd e (Zpos xH))) := by
    apply bpow_lt ctx r
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd e (Zpos xH))
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    have hone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos xH) = 1 := rfl
    rw [hone]
    omega
  apply mag_unique ctx m r (Exact.bpow ctx r e) (Zadd e (Zpos xH))
  constructor
  · rw [hz, habs]
    exact ctx.certificate.orderedField.le_refl _
  · rw [habs]
    exact hlt

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem mag_le_bpow :
    ∀ (ctx : ExactRealContext) (m : Exact.Magnitude ctx),
      mag_le_bpowStatement ctx m := by
  intro ctx m r x e hx hlt
  have hm := (Exact.mag m r x).mag_bound hx
  apply bpow_lt_bpow ctx r (Exact.mag m r x).mag_val e
  exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
    ctx _ _ _ hm.1 hlt

theorem mag_gt_bpow :
    ∀ (ctx : ExactRealContext) (m : Exact.Magnitude ctx),
      mag_gt_bpowStatement ctx m := by
  intro ctx m r x e h
  have hx : x ≠ Exact.R0 ctx := by
    intro hx
    subst x
    have habs : Exact.Rabs ctx (Exact.R0 ctx) = Exact.R0 ctx := by
      change ctx.spec.abs ctx.spec.zero = ctx.spec.zero
      exact ctx.certificate.sourceLaws.abs_nonnegative _
        (ctx.certificate.orderedField.le_refl _)
    have hle : Exact.Rle ctx (Exact.bpow ctx r e) (Exact.R0 ctx) := by
      simpa only [habs] using h
    have hp := bpow_gt_0 ctx r e
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hp).2 hle
  have hm := (Exact.mag m r x).mag_bound hx
  have hp : Exact.Rlt ctx (Exact.bpow ctx r e)
      (Exact.bpow ctx r (Exact.mag m r x).mag_val) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
      ctx _ _ _ h hm.2
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (Exact.mag m r x).mag_val
  apply Int.lt_of_not_ge
  intro hge
  have hpow := bpow_le ctx r (Exact.mag m r x).mag_val e
    (show Zle (Exact.mag m r x).mag_val e by exact hge)
  exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hp).2 hpow

theorem mag_ge_bpow :
    ∀ (ctx : ExactRealContext) (m : Exact.Magnitude ctx),
      mag_ge_bpowStatement ctx m := by
  intro ctx m r x e h
  by_cases hlt : Exact.Rlt ctx (Exact.Rabs ctx x) (Exact.bpow ctx r e)
  · have heq := mag_unique ctx m r x e ⟨h, hlt⟩
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Exact.mag m r x).mag_val
    rw [heq]
    exact Int.le_refl _
  · have hre : Exact.Rle ctx (Exact.bpow ctx r e) (Exact.Rabs ctx x) := by
      rcases ctx.certificate.total_order (Exact.Rabs ctx x)
          (Exact.bpow ctx r e) with hab | hba
      · rcases hab with hablt | habeq
        · exact (hlt hablt).elim
        · rw [habeq]
          exact ctx.certificate.orderedField.le_refl _
      · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hba |>.1
    have hgt := mag_gt_bpow ctx m r x e hre
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Exact.mag m r x).mag_val
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Exact.mag m r x).mag_val at hgt
    omega

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

private theorem pg_abs_mul_bpow_suffix (ctx : ExactRealContext)
    (r : radix) (x : Exact.R ctx) (e : Z) :
    Exact.Rabs ctx (Exact.Rmult ctx x (Exact.bpow ctx r e)) =
      Exact.Rmult ctx (Exact.Rabs ctx x) (Exact.bpow ctx r e) := by
  have hp : Exact.Rlt ctx (Exact.R0 ctx) (Exact.bpow ctx r e) :=
    bpow_gt_0 ctx r e
  rcases ctx.certificate.total_order x (Exact.R0 ctx) with hx | hx
  · rcases hx with hneg | heq
    · have hmul : Exact.Rlt ctx
          (Exact.Rmult ctx x (Exact.bpow ctx r e)) (Exact.R0 ctx) := by
        have h := ctx.certificate.orderedField.mul_lt_compat_l
          (Exact.bpow ctx r e) x (Exact.R0 ctx) hp hneg
        change ctx.spec.lt
          (ctx.spec.mul (Exact.bpow ctx r e) x)
          (ctx.spec.mul (Exact.bpow ctx r e) ctx.spec.zero) at h
        rw [ctx.certificate.orderedField.mul_zero,
          ctx.certificate.orderedField.mul_comm (Exact.bpow ctx r e) x] at h
        exact h
      change ctx.spec.lt (ctx.spec.mul x (Exact.bpow ctx r e))
        ctx.spec.zero at hmul
      change ctx.spec.abs (ctx.spec.mul x (Exact.bpow ctx r e)) =
        ctx.spec.mul (ctx.spec.abs x) (Exact.bpow ctx r e)
      rw [ctx.certificate.sourceLaws.abs_negative _ hmul,
        ctx.certificate.sourceLaws.abs_negative x hneg]
      exact
        (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_mult_distr_l_reverse
          ctx x (Exact.bpow ctx r e)).symm
    · subst x
      have habs : ctx.spec.abs ctx.spec.zero = ctx.spec.zero :=
        ctx.certificate.sourceLaws.abs_nonnegative _
          (ctx.certificate.orderedField.le_refl _)
      change ctx.spec.abs (ctx.spec.mul ctx.spec.zero (Exact.bpow ctx r e)) =
        ctx.spec.mul (ctx.spec.abs ctx.spec.zero) (Exact.bpow ctx r e)
      rw [habs, ctx.certificate.orderedField.mul_comm ctx.spec.zero,
        ctx.certificate.orderedField.mul_zero]
      exact habs
  · have hxle : Exact.Rle ctx (Exact.R0 ctx) x :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hx |>.1
    have hmul : Exact.Rlt ctx (Exact.R0 ctx)
        (Exact.Rmult ctx x (Exact.bpow ctx r e)) := by
      have h := ctx.certificate.orderedField.mul_lt_compat_l
        (Exact.bpow ctx r e) (Exact.R0 ctx) x hp hx
      change ctx.spec.lt
        (ctx.spec.mul (Exact.bpow ctx r e) ctx.spec.zero)
        (ctx.spec.mul (Exact.bpow ctx r e) x) at h
      rw [ctx.certificate.orderedField.mul_zero,
        ctx.certificate.orderedField.mul_comm (Exact.bpow ctx r e) x] at h
      exact h
    have hmulle : Exact.Rle ctx (Exact.R0 ctx)
        (Exact.Rmult ctx x (Exact.bpow ctx r e)) :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hmul |>.1
    change ctx.spec.le ctx.spec.zero
      (ctx.spec.mul x (Exact.bpow ctx r e)) at hmulle
    change ctx.spec.abs (ctx.spec.mul x (Exact.bpow ctx r e)) =
      ctx.spec.mul (ctx.spec.abs x) (Exact.bpow ctx r e)
    rw [ctx.certificate.sourceLaws.abs_nonnegative _ hmulle,
      ctx.certificate.sourceLaws.abs_nonnegative x hxle]

theorem mag_mult_bpow :
    ∀ (ctx : ExactRealContext) (m : Exact.Magnitude ctx),
      mag_mult_bpowStatement ctx m := by
  intro ctx m r x e hx
  let mx := (Exact.mag m r x).mag_val
  have hm := (Exact.mag m r x).mag_bound hx
  have habs := pg_abs_mul_bpow_suffix ctx r x e
  have hp0 : Exact.Rle ctx (Exact.IZR ctx Z0) (Exact.bpow ctx r e) := by
    change ctx.spec.le (ctx.spec.ofZ Z0) (Exact.bpow ctx r e)
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact bpow_ge_0 ctx r e
  have hp : Exact.Rlt ctx (Exact.IZR ctx Z0) (Exact.bpow ctx r e) := by
    change ctx.spec.lt (ctx.spec.ofZ Z0) (Exact.bpow ctx r e)
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact bpow_gt_0 ctx r e
  have hlower : Exact.Rle ctx
      (Exact.Rmult ctx (Exact.bpow ctx r (Zsub mx (Zpos xH)))
        (Exact.bpow ctx r e))
      (Exact.Rmult ctx (Exact.Rabs ctx x) (Exact.bpow ctx r e)) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
      ctx (Exact.bpow ctx r e)
        (Exact.bpow ctx r (Zsub mx (Zpos xH))) (Exact.Rabs ctx x) hp0 hm.1
  have hupper : Exact.Rlt ctx
      (Exact.Rmult ctx (Exact.Rabs ctx x) (Exact.bpow ctx r e))
      (Exact.Rmult ctx (Exact.bpow ctx r mx) (Exact.bpow ctx r e)) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_compat_r
      ctx (Exact.bpow ctx r e) (Exact.Rabs ctx x)
        (Exact.bpow ctx r mx) hp hm.2
  have hz : Zsub (Zadd mx e) (Zpos xH) =
      Zadd (Zsub mx (Zpos xH)) e := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    omega
  apply mag_unique ctx m r (Exact.Rmult ctx x (Exact.bpow ctx r e))
    (Zadd mx e)
  rw [habs, hz, bpow_plus ctx r (Zsub mx (Zpos xH)) e,
    bpow_plus ctx r mx e]
  exact ⟨hlower, hupper⟩

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem eqb_sym : eqb_symStatement := by
  intro x y
  cases x <;> cases y <;> rfl

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem eqb_true : eqb_trueStatement := by
  intro x y h
  exact (CompCert4Lean.Foundation.Logic.Rocq.Coq.Bool.Bool.eqb_true_iff x y).2 h

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem IZR_cond_Zopp :
    ∀ (ctx : ExactRealContext), IZR_cond_ZoppStatement ctx := by
  intro ctx b m
  cases b with
  | false => rfl
  | true => exact ctx.certificate.sourceLaws.ofZ_neg m

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem abs_cond_Ropp :
    ∀ (ctx : ExactRealContext), abs_cond_RoppStatement ctx := by
  intro ctx b m
  cases b with
  | false => rfl
  | true =>
      change ctx.spec.abs (ctx.spec.neg m) = ctx.spec.abs m
      exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rbasic_fun.Rabs_Ropp
        ctx m

theorem cond_Ropp_mult_l :
    ∀ (ctx : ExactRealContext), cond_Ropp_mult_lStatement ctx := by
  intro ctx b x y
  cases b with
  | false => rfl
  | true =>
      change ctx.spec.neg (ctx.spec.mul x y) =
        ctx.spec.mul (ctx.spec.neg x) y
      exact (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_mult_distr_l_reverse
        ctx x y).symm

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem lt_bpow (ctx : ExactRealContext) : lt_bpowStatement ctx := by
  intro r e1 e2 h
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2
  apply Int.lt_of_not_ge
  intro hle
  have hp := bpow_le ctx r e2 e1 (show Zle e2 e1 by exact hle)
  exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h).2 hp

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem mag_le_Zpower :
    ∀ (ctx : ExactRealContext) (m : Exact.Magnitude ctx),
      mag_le_ZpowerStatement ctx m := by
  intro ctx m r z e hz hpow
  have hne : Exact.IZR ctx z ≠ Exact.R0 ctx := by
    intro hzero
    have hi :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_neq_proof
        ctx z Z0 hz
    apply hi
    calc
      Exact.IZR ctx z = Exact.R0 ctx := hzero
      _ = Exact.IZR ctx Z0 := ctx.certificate.sourceLaws.ofZ_zero.symm
  have hlt : Exact.Rlt ctx (Exact.Rabs ctx (Exact.IZR ctx z))
      (Exact.bpow ctx r e) := by
    have habs :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rbasic_fun.abs_IZR
        ctx z
    have habs' : ctx.spec.ofZ (Zabs z) = ctx.spec.abs (ctx.spec.ofZ z) := habs
    cases e with
    | Z0 =>
        have he : Zle Z0 (.Z0 : Z) := by
          change (0 : Int) ≤ 0
          omega
        have hp := IZR_Zpower ctx r (.Z0 : Z) he
        have hp' : ctx.spec.ofZ (Zpower r.radix_val (.Z0 : Z)) = Exact.bpow ctx r (.Z0 : Z) := hp
        have hi :=
          CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt
            ctx (Zabs z) (Zpower r.radix_val (.Z0 : Z)) hpow
        change ctx.spec.lt (ctx.spec.abs (ctx.spec.ofZ z))
          (Exact.bpow ctx r (.Z0 : Z))
        rw [← habs', ← hp']
        exact hi
    | Zpos p =>
        have he : Zle Z0 (.Zpos p : Z) := by
          change (0 : Int) ≤ _
          simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
        have hp := IZR_Zpower ctx r (.Zpos p) he
        have hp' : ctx.spec.ofZ (Zpower r.radix_val (.Zpos p)) = Exact.bpow ctx r (.Zpos p) := hp
        have hi :=
          CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt
            ctx (Zabs z) (Zpower r.radix_val (.Zpos p)) hpow
        change ctx.spec.lt (ctx.spec.abs (ctx.spec.ofZ z))
          (Exact.bpow ctx r (.Zpos p))
        rw [← habs', ← hp']
        exact hi
    | Zneg p =>
        exfalso
        have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
        cases z with
        | Z0 =>
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zabs (.Z0 : Z)) <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (Zpower r.radix_val (.Zneg p)) at hpow
            simp only [Zabs,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs,
              Zpower,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hpow
            simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ, hp] at hpow
        | Zpos q =>
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zabs (.Zpos q)) <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (Zpower r.radix_val (.Zneg p)) at hpow
            simp only [Zabs,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs,
              Zpower,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hpow
            simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ, hp] at hpow
            omega
        | Zneg q =>
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zabs (.Zneg q)) <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (Zpower r.radix_val (.Zneg p)) at hpow
            simp only [Zabs,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs,
              Zpower,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hpow
            simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ, hp] at hpow
            omega
  exact mag_le_bpow ctx m r (Exact.IZR ctx z) e hne hlt

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Rcompare_half_l (ctx : ExactRealContext) : Rcompare_half_lStatement ctx := by
  intro x y
  calc
    Exact.Rcompare ctx (Exact.Rdiv ctx x (Exact.Rtwo ctx)) y =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp
          (Exact.Rcompare ctx y (Exact.Rdiv ctx x (Exact.Rtwo ctx))) :=
      Rcompare_sym ctx _ _
    _ = CompCert4Lean.Foundation.Numbers.Rocq.Coq.CompOpp
          (Exact.Rcompare ctx (Exact.Rmult ctx (Exact.Rtwo ctx) y) x) :=
      congrArg _ (Rcompare_half_r ctx y x)
    _ = Exact.Rcompare ctx x (Exact.Rmult ctx (Exact.Rtwo ctx) y) :=
      (Rcompare_sym ctx _ _).symm

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Ztrunc_opp (ctx : ExactRealContext) :
    Ztrunc_oppStatement ctx := by
  intro x
  cases h : Exact.Rlt_bool ctx x (Exact.R0 ctx) with
  | true =>
      have hspec := Rlt_bool_spec ctx x (Exact.R0 ctx)
      rw [h] at hspec
      cases hspec with
      | Rlt_bool_true_ hx =>
          have hxle : ctx.spec.le x ctx.spec.zero :=
            (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hx |>.1
          have hneg_nonneg : ctx.spec.le ctx.spec.zero (ctx.spec.neg x) := by
            have hneg := pg_neg_le_contravar ctx hxle
            rw [show ctx.spec.neg ctx.spec.zero = ctx.spec.zero by
              calc
                ctx.spec.neg ctx.spec.zero =
                    ctx.spec.add (ctx.spec.neg ctx.spec.zero) ctx.spec.zero :=
                  (ctx.certificate.orderedField.add_zero _).symm
                _ = ctx.spec.zero :=
                  ctx.certificate.orderedField.neg_add_cancel _] at hneg
            exact hneg
          rw [Ztrunc_floor ctx (Exact.Ropp ctx x) hneg_nonneg]
          rw [Ztrunc_ceil ctx x hxle]
          unfold Exact.Zceil
          rw [pg_zopp_zopp]
  | false =>
      have hspec := Rlt_bool_spec ctx x (Exact.R0 ctx)
      rw [h] at hspec
      cases hspec with
      | Rlt_bool_false_ hx =>
          have hneg_nonpos : ctx.spec.le (ctx.spec.neg x) ctx.spec.zero := by
            have hneg := pg_neg_le_contravar ctx hx
            change ctx.spec.le (ctx.spec.neg x)
              (ctx.spec.neg ctx.spec.zero) at hneg
            rw [show ctx.spec.neg ctx.spec.zero = ctx.spec.zero by
              calc
                ctx.spec.neg ctx.spec.zero =
                    ctx.spec.add (ctx.spec.neg ctx.spec.zero) ctx.spec.zero :=
                  (ctx.certificate.orderedField.add_zero _).symm
                _ = ctx.spec.zero :=
                  ctx.certificate.orderedField.neg_add_cancel _] at hneg
            exact hneg
          rw [Ztrunc_ceil ctx (Exact.Ropp ctx x) hneg_nonpos]
          unfold Exact.Zceil
          rw [show Exact.Ropp ctx (Exact.Ropp ctx x) = x by
            exact pg_neg_neg ctx x]
          rw [Ztrunc_floor ctx x hx]

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

theorem Ztrunc_abs (ctx : ExactRealContext) : Ztrunc_absStatement ctx := by
  intro x
  rw [Ztrunc_floor ctx (Exact.Rabs ctx x) (pg_worker_abs_nonneg ctx x)]
  cases h : Exact.Rlt_bool ctx x (Exact.R0 ctx) with
  | true =>
      have hspec := Rlt_bool_spec ctx x (Exact.R0 ctx)
      rw [h] at hspec
      cases hspec with
      | Rlt_bool_true_ hx =>
          have hxle : ctx.spec.le x ctx.spec.zero :=
            (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hx |>.1
          have hz : Zle (Exact.Zceil ctx x) Z0 := by
            apply Zceil_glb ctx Z0 x
            change ctx.spec.le x (ctx.spec.ofZ Z0)
            rw [ctx.certificate.sourceLaws.ofZ_zero]
            exact hxle
          rw [show Exact.Rabs ctx x = Exact.Ropp ctx x from
            ctx.certificate.sourceLaws.abs_negative x hx]
          rw [Ztrunc_ceil ctx x hxle]
          have habs : Zabs (Exact.Zceil ctx x) = Zopp (Exact.Zceil ctx x) :=
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs_neq _ hz
          rw [habs]
          unfold Exact.Zceil
          rw [pg_zopp_zopp]
  | false =>
      have hspec := Rlt_bool_spec ctx x (Exact.R0 ctx)
      rw [h] at hspec
      cases hspec with
      | Rlt_bool_false_ hx =>
          have hz : Zle Z0 (Exact.Zfloor ctx x) := by
            apply Zfloor_lub ctx Z0 x
            change ctx.spec.le (ctx.spec.ofZ Z0) x
            rw [ctx.certificate.sourceLaws.ofZ_zero]
            exact hx
          rw [show Exact.Rabs ctx x = x from
            ctx.certificate.sourceLaws.abs_nonnegative x hx]
          rw [Ztrunc_floor ctx x hx]
          exact (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs_eq _ hz).symm

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

private theorem pg_Zfloor_div_decomp (ctx : ExactRealContext)
    (x y : Z) (hy : y ≠ Z0) :
    Exact.Rdiv ctx (Exact.IZR ctx x) (Exact.IZR ctx y) =
      Exact.Rplus ctx (Exact.IZR ctx (Zdiv x y))
        (Exact.Rdiv ctx (Exact.IZR ctx (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y))
          (Exact.IZR ctx y)) := by
  have hxy := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Z_div_mod_eq_full x y
  have hmul := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR
    ctx y (Zdiv x y)
  change ctx.spec.ofZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul y (Zdiv x y)) =
    ctx.spec.mul (ctx.spec.ofZ y) (ctx.spec.ofZ (Zdiv x y)) at hmul
  have hadd := ctx.certificate.sourceLaws.ofZ_add
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul y (Zdiv x y))
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y)
  have hxyR : Exact.IZR ctx x =
      Exact.Rplus ctx (Exact.IZR ctx (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul y (Zdiv x y)))
        (Exact.IZR ctx (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y)) := by
    calc
      Exact.IZR ctx x = Exact.IZR ctx
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul y (Zdiv x y))
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y)) := congrArg _ hxy
      _ = _ := by
        change ctx.spec.ofZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul y (Zdiv x y))
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y)) = _
        rw [ctx.certificate.sourceLaws.ofZ_add]
        rfl
  unfold Exact.Rdiv
  unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv
  change ctx.spec.div (Exact.IZR ctx x) (Exact.IZR ctx y) =
    ctx.spec.add (Exact.IZR ctx (Zdiv x y))
      (ctx.spec.div (Exact.IZR ctx
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y))
        (Exact.IZR ctx y))
  rw [ctx.certificate.orderedField.div_eq_mul_inv,
    ctx.certificate.orderedField.div_eq_mul_inv]
  unfold Exact.Rplus at hxyR
  unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rplus at hxyR
  rw [hxyR]
  rw [ctx.certificate.orderedField.mul_comm
      (ctx.spec.add
        (Exact.IZR ctx (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul y (Zdiv x y)))
        (Exact.IZR ctx (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y)))
      (ctx.spec.inv (Exact.IZR ctx y))]
  rw [ctx.certificate.orderedField.left_distrib]
  unfold Exact.IZR at ⊢
  unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR at ⊢
  rw [hmul]
  rw [← ctx.certificate.orderedField.mul_assoc]
  have hyR : ctx.spec.ofZ y ≠ ctx.spec.zero := by
    intro hz
    apply hy
    apply _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.eq_IZR ctx y Z0
    calc
      ctx.spec.ofZ y = ctx.spec.zero := hz
      _ = ctx.spec.ofZ Z0 := ctx.certificate.sourceLaws.ofZ_zero.symm
  have hinv : ctx.spec.mul (ctx.spec.inv (ctx.spec.ofZ y))
      (ctx.spec.ofZ y) = ctx.spec.one := by
    exact ctx.certificate.orderedField.inv_mul_cancel _ hyR
  rw [hinv, ctx.certificate.orderedField.one_mul]
  rw [ctx.certificate.orderedField.mul_comm
      (ctx.spec.inv (ctx.spec.ofZ y))
      (ctx.spec.ofZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y))]

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

private theorem pg_Zfloor_div_remainder_pos (ctx : ExactRealContext)
    (r y : Z) (hy : Zlt Z0 y)
    (hr : Zle Z0 r) (hry : Zlt r y) :
    Exact.Rle ctx (Exact.R0 ctx)
        (Exact.Rdiv ctx (Exact.IZR ctx r) (Exact.IZR ctx y)) ∧
      Exact.Rlt ctx (Exact.Rdiv ctx (Exact.IZR ctx r) (Exact.IZR ctx y))
        (Exact.Rone ctx) := by
  have hy0 := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt ctx Z0 y hy
  have hr0 := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_le ctx Z0 r hr
  have hry' := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt ctx r y hry
  have hinv0 := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rinv_0_lt_compat ctx
    (Exact.IZR ctx y) hy0
  have hr0' : ctx.spec.le ctx.spec.zero (ctx.spec.ofZ r) := by
    change ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.ofZ r) at hr0
    rw [ctx.certificate.sourceLaws.ofZ_zero] at hr0
    exact hr0
  have hinv0' : ctx.spec.le ctx.spec.zero (ctx.spec.inv (ctx.spec.ofZ y)) := by
    have h : ctx.spec.lt ctx.spec.zero (ctx.spec.inv (ctx.spec.ofZ y)) := by
      change ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.inv (ctx.spec.ofZ y)) at hinv0
      rw [ctx.certificate.sourceLaws.ofZ_zero] at hinv0
      exact hinv0
    exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1
  have hinv0le := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le
    ctx (Exact.IZR ctx Z0) (Exact.Rinv ctx (Exact.IZR ctx y)) hinv0
  have hnon : Exact.Rle ctx (Exact.R0 ctx)
      (Exact.Rmult ctx (Exact.IZR ctx r) (Exact.Rinv ctx (Exact.IZR ctx y))) := by
    unfold Exact.Rle Exact.R0 Exact.Rmult Exact.IZR Exact.Rinv
    unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle
      CompCert4Lean.Foundation.FlocqReal.ExactReal.R0
      CompCert4Lean.Foundation.FlocqReal.ExactReal.Rmult
      CompCert4Lean.Foundation.FlocqReal.ExactReal.Rinv
      CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR
    have h := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_pos
      ctx (Exact.IZR ctx r) (Exact.Rinv ctx (Exact.IZR ctx y)) hr0 hinv0le
    change ctx.spec.le (ctx.spec.ofZ Z0)
      (ctx.spec.mul (ctx.spec.ofZ r) (ctx.spec.inv (ctx.spec.ofZ y))) at h
    rw [ctx.certificate.sourceLaws.ofZ_zero] at h
    exact h
  have hyne : y ≠ Z0 := by
    intro he
    subst y
    change (0 : Int) < 0 at hy
    omega
  have hprod : Exact.Rmult ctx
      (Exact.Rdiv ctx (Exact.IZR ctx r) (Exact.IZR ctx y))
      (Exact.IZR ctx y) = Exact.IZR ctx r := by
    unfold Exact.Rmult Exact.IZR Exact.Rdiv
    unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rmult
      CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR
      CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv
    rw [ctx.certificate.orderedField.div_eq_mul_inv]
    change ctx.spec.mul (ctx.spec.mul (ctx.spec.ofZ r)
      (ctx.spec.inv (ctx.spec.ofZ y))) (ctx.spec.ofZ y) = ctx.spec.ofZ r
    rw [ctx.certificate.orderedField.mul_assoc]
    have hyR : ctx.spec.ofZ y ≠ ctx.spec.zero := by
      intro hz
      apply hyne
      apply _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.eq_IZR ctx y Z0
      calc
        ctx.spec.ofZ y = ctx.spec.zero := hz
        _ = ctx.spec.ofZ Z0 := ctx.certificate.sourceLaws.ofZ_zero.symm
    rw [ctx.certificate.orderedField.inv_mul_cancel _ hyR,
      ctx.certificate.orderedField.mul_one]
  have hlt : Exact.Rlt ctx
      (Exact.Rdiv ctx (Exact.IZR ctx r) (Exact.IZR ctx y))
      (Exact.IZR ctx (Zpos xH)) := by
    apply _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_reg_r
      ctx (Exact.IZR ctx y) _ _ hy0
    have hprod' := hprod
    unfold Exact.Rmult Exact.IZR Exact.Rdiv at hprod'
    unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rmult
      CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR
      CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv at hprod'
    rw [ctx.certificate.orderedField.div_eq_mul_inv] at hprod'
    unfold Exact.Rdiv Exact.IZR at ⊢
    unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rmult at ⊢
    unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv
      CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR at ⊢
    rw [ctx.certificate.orderedField.div_eq_mul_inv]
    rw [hprod']
    rw [ctx.certificate.sourceLaws.ofZ_one,
      ctx.certificate.orderedField.one_mul]
    change ctx.spec.lt (ctx.spec.ofZ r) (ctx.spec.ofZ y) at hry'
    exact hry'
  constructor
  · unfold Exact.Rle Exact.R0 Exact.Rdiv Exact.IZR
    unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle
      CompCert4Lean.Foundation.FlocqReal.ExactReal.R0
      CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv
      CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR
    rw [ctx.certificate.orderedField.div_eq_mul_inv]
    exact hnon
  · unfold Exact.Rlt Exact.Rone Exact.Rdiv Exact.IZR
    unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rlt
      CompCert4Lean.Foundation.FlocqReal.ExactReal.Rone
      CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv
      CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR
    rw [ctx.certificate.orderedField.div_eq_mul_inv]
    have hlt' := hlt
    unfold Exact.Rlt Exact.Rdiv Exact.IZR at hlt'
    unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rlt
      CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv
      CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR at hlt'
    rw [ctx.certificate.orderedField.div_eq_mul_inv] at hlt'
    rw [ctx.certificate.sourceLaws.ofZ_one] at hlt'
    exact hlt'

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

private theorem pg_Zmod_bounds_neg (x y : Z) (hy : Zlt y Z0) :
    Zlt y (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y) ∧
      Zle (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y) Z0 := by
  have hopp : ∀ z : Z,
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zopp z) =
        -_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z := by
    intro z
    cases z <;>
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] <;>
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
  have hyn : Zlt Z0 (Zopp y) := by
    change (0 : Int) <
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zopp y)
    rw [hopp]
    change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y < 0 at hy
    omega
  have hm := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Z_mod_lt
    (Zopp x) (Zopp y) hyn
  have hrel := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Zmod_opp_opp x y
  have hm0 := hm.1
  have hm1 := hm.2
  change 0 ≤ _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo (Zopp x) (Zopp y)) at hm0
  change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo (Zopp x) (Zopp y)) <
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zopp y) at hm1
  have hrel' :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y =
        Zopp (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo (Zopp x) (Zopp y)) := by
    calc
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y =
          Zopp (Zopp (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y)) :=
        (pg_zopp_zopp _).symm
      _ = Zopp (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo (Zopp x) (Zopp y)) := by
        exact (congrArg Zopp hrel).symm
  constructor
  · change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y <
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y)
    rw [hrel', hopp]
    change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y <
      -_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo (Zopp x) (Zopp y))
    change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zopp y) >
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo (Zopp x) (Zopp y)) at hm1
    rw [hopp y] at hm1
    omega
  · change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y) ≤ 0
    rw [hrel', hopp]
    change -_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo (Zopp x) (Zopp y)) ≤ 0
    omega

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

private theorem pg_div_opp_opp (ctx : ExactRealContext) (r y : Z) (hy : y ≠ Z0) :
    Exact.Rdiv ctx (Exact.IZR ctx (Zopp r)) (Exact.IZR ctx (Zopp y)) =
      Exact.Rdiv ctx (Exact.IZR ctx r) (Exact.IZR ctx y) := by
  have hyR : Exact.IZR ctx y ≠ Exact.R0 ctx := by
    intro hz
    apply hy
    apply _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.eq_IZR ctx y Z0
    calc
      Exact.IZR ctx y = Exact.R0 ctx := hz
      _ = Exact.IZR ctx Z0 := by
        change ctx.spec.zero = ctx.spec.ofZ Z0
        exact ctx.certificate.sourceLaws.ofZ_zero.symm
  unfold Exact.Rdiv Exact.IZR
  unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv
    CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR
  rw [ctx.certificate.orderedField.div_eq_mul_inv,
    ctx.certificate.orderedField.div_eq_mul_inv]
  rw [ctx.certificate.sourceLaws.ofZ_neg,
    ctx.certificate.sourceLaws.ofZ_neg]
  have hinv : ctx.spec.inv (ctx.spec.neg (ctx.spec.ofZ y)) =
      ctx.spec.neg (ctx.spec.inv (ctx.spec.ofZ y)) := by
    have h := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_inv_permute_proof
      ctx (ctx.spec.ofZ y) (by
        intro hz
        apply hyR
        change ctx.spec.ofZ y = ctx.spec.zero
        exact hz.trans ctx.certificate.sourceLaws.ofZ_zero)
    exact h.symm
  rw [hinv]
  have hmul := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_opp_opp
    ctx (ctx.spec.ofZ r) (ctx.spec.inv (ctx.spec.ofZ y))
  exact hmul

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

private theorem pg_Zfloor_div_remainder_neg (ctx : ExactRealContext)
    (r y : Z) (hy : Zlt y Z0)
    (hry : Zlt y r) (hr : Zle r Z0) :
    Exact.Rle ctx (Exact.R0 ctx)
        (Exact.Rdiv ctx (Exact.IZR ctx r) (Exact.IZR ctx y)) ∧
      Exact.Rlt ctx (Exact.Rdiv ctx (Exact.IZR ctx r) (Exact.IZR ctx y))
        (Exact.Rone ctx) := by
  have hopp : ∀ z : Z,
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zopp z) =
        -_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z := by
    intro z
    cases z <;>
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] <;>
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
  have hypos : Zlt Z0 (Zopp y) := by
    change (0 : Int) < _
    rw [hopp]
    change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y < 0 at hy
    omega
  have hrpos : Zle Z0 (Zopp r) := by
    change (0 : Int) ≤ _
    rw [hopp]
    change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r ≤ 0 at hr
    omega
  have hrrpos : Zlt (Zopp r) (Zopp y) := by
    change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zopp r) <
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zopp y)
    rw [hopp, hopp]
    change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y <
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r at hry
    omega
  have hp := pg_Zfloor_div_remainder_pos ctx (Zopp r) (Zopp y)
    hypos hrpos hrrpos
  have hyne : y ≠ Z0 := by
    intro he
    subst y
    change (0 : Int) < 0 at hy
    omega
  rw [pg_div_opp_opp ctx r y hyne] at hp
  exact hp

end CompCert4Lean.Flocq.Core.Raux

namespace CompCert4Lean.Flocq.Core.Raux

private theorem pg_add_le (ctx : ExactRealContext) (q : Z)
    (d : ctx.spec.carrier) (hd : ctx.spec.le ctx.spec.zero d) :
    ctx.spec.le (ctx.spec.ofZ q) (ctx.spec.add (ctx.spec.ofZ q) d) := by
  have hd' : Exact.Rle ctx (Exact.R0 ctx) d := by
    unfold Exact.Rle Exact.R0
    unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle
      CompCert4Lean.Foundation.FlocqReal.ExactReal.R0
    exact hd
  have h := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_le_compat_l
    ctx (Exact.IZR ctx q) (Exact.R0 ctx) d hd'
  unfold Exact.IZR Exact.R0 at h
  unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle
    CompCert4Lean.Foundation.FlocqReal.ExactReal.R0 at h
  unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rplus
    CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR at h
  rw [ctx.certificate.orderedField.add_zero] at h
  change ctx.spec.le (ctx.spec.ofZ q)
    (ctx.spec.add (ctx.spec.ofZ q) d) at h
  exact h

private theorem pg_add_lt (ctx : ExactRealContext) (q : Z)
    (d : ctx.spec.carrier) (hd : ctx.spec.lt d ctx.spec.one) :
    ctx.spec.lt (ctx.spec.add (ctx.spec.ofZ q) d)
      (ctx.spec.add (ctx.spec.ofZ q) ctx.spec.one) := by
  have h := _root_.CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Raxioms.Rplus_lt_compat_l
    ctx (Exact.IZR ctx q) d (Exact.Rone ctx) hd
  unfold Exact.IZR Exact.Rone at h
  unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rplus
    CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR
    CompCert4Lean.Foundation.FlocqReal.ExactReal.Rone at h
  change ctx.spec.lt (ctx.spec.add (ctx.spec.ofZ q) d)
    (ctx.spec.add (ctx.spec.ofZ q) ctx.spec.one) at h
  exact h

theorem Zfloor_div :
    ∀ (ctx : ExactRealContext), Zfloor_divStatement ctx := by
  intro ctx x y hy
  by_cases hypos : Zlt Z0 y
  · have hm := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Z_mod_lt x y hypos
    have hd := pg_Zfloor_div_remainder_pos ctx
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y) y
      hypos hm.1 hm.2
    have hdecomp := pg_Zfloor_div_decomp ctx x y hy
    have hdle := hd.1
    have hdlt := hd.2
    unfold Exact.Rle Exact.R0 Exact.Rdiv Exact.IZR at hdle
    unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle
      CompCert4Lean.Foundation.FlocqReal.ExactReal.R0
      CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv
      CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR at hdle
    unfold Exact.Rlt Exact.Rone Exact.Rdiv Exact.IZR at hdlt
    unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rlt
      CompCert4Lean.Foundation.FlocqReal.ExactReal.Rone
      CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv
      CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR at hdlt
    have hlower := pg_add_le ctx (Zdiv x y)
      (ctx.spec.div (ctx.spec.ofZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y))
        (ctx.spec.ofZ y)) hdle
    have hupper := pg_add_lt ctx (Zdiv x y)
      (ctx.spec.div (ctx.spec.ofZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y))
        (ctx.spec.ofZ y)) hdlt
    apply Zfloor_imp ctx (Zdiv x y)
    constructor
    · rw [hdecomp]
      exact hlower
    · rw [hdecomp]
      unfold Exact.Rlt Exact.Rplus Exact.Rdiv Exact.IZR
      unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rlt
        CompCert4Lean.Foundation.FlocqReal.ExactReal.Rplus
        CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv
        CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR
      rw [ctx.certificate.sourceLaws.ofZ_add,
        ctx.certificate.sourceLaws.ofZ_one]
      exact hupper
  · have hyneg : Zlt y Z0 := by
      change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y < 0
      by_cases hpos : (0 : Int) <
          _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y
      · exact False.elim (hypos hpos)
      · have hzero :
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y ≠ 0 := by
          intro hz
          apply hy
          apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
          exact hz
        omega
    have hm := pg_Zmod_bounds_neg x y hyneg
    have hd := pg_Zfloor_div_remainder_neg ctx
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y) y
      hyneg hm.1 hm.2
    have hdecomp := pg_Zfloor_div_decomp ctx x y hy
    have hdle := hd.1
    have hdlt := hd.2
    unfold Exact.Rle Exact.R0 Exact.Rdiv Exact.IZR at hdle
    unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle
      CompCert4Lean.Foundation.FlocqReal.ExactReal.R0
      CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv
      CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR at hdle
    unfold Exact.Rlt Exact.Rone Exact.Rdiv Exact.IZR at hdlt
    unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rlt
      CompCert4Lean.Foundation.FlocqReal.ExactReal.Rone
      CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv
      CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR at hdlt
    have hlower := pg_add_le ctx (Zdiv x y)
      (ctx.spec.div (ctx.spec.ofZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y))
        (ctx.spec.ofZ y)) hdle
    have hupper := pg_add_lt ctx (Zdiv x y)
      (ctx.spec.div (ctx.spec.ofZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y))
        (ctx.spec.ofZ y)) hdlt
    apply Zfloor_imp ctx (Zdiv x y)
    constructor
    · rw [hdecomp]
      exact hlower
    · rw [hdecomp]
      unfold Exact.Rlt Exact.Rplus Exact.Rdiv Exact.IZR
      unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rlt
        CompCert4Lean.Foundation.FlocqReal.ExactReal.Rplus
        CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv
        CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR
      rw [ctx.certificate.sourceLaws.ofZ_add,
        ctx.certificate.sourceLaws.ofZ_one]
      exact hupper

end CompCert4Lean.Flocq.Core.Raux
