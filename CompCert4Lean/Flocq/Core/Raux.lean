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
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rdefinitions.total_order_T x y :=
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

def cond_Ropp (b : Bool) (m : R) : R := if b then Ropp m else m

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
