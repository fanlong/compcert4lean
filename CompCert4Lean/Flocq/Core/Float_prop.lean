import CompCert4Lean.Flocq.Core.Defs
import CompCert4Lean.Flocq.Core.Digits

/-!
# Basic properties of Flocq floating-point formats

This module provides the executable abbreviation selected from
`Flocq.Core.Float_prop`. Proof-heavy source declarations are represented by
their exact proposition descriptors for the later proof-migration phase.
-/

namespace CompCert4Lean.Flocq.Core.Float_prop

abbrev R := CompCert4Lean.Flocq.Core.Raux.R
abbrev Z := CompCert4Lean.Flocq.Core.Zaux.Z
abbrev radix := CompCert4Lean.Flocq.Core.Zaux.radix

abbrev Z0 : Z := CompCert4Lean.Flocq.Core.Zaux.Z0
abbrev Zone : Z := CompCert4Lean.Flocq.Core.Zaux.Zone

abbrev Zadd := CompCert4Lean.Flocq.Core.Zaux.Zadd
abbrev Zsub := CompCert4Lean.Flocq.Core.Zaux.Zsub
abbrev Zmul := CompCert4Lean.Flocq.Core.Zaux.Zmul
abbrev Zopp := CompCert4Lean.Flocq.Core.Zaux.Zopp
abbrev Zabs := CompCert4Lean.Flocq.Core.Zaux.Zabs
abbrev Zpower := CompCert4Lean.Flocq.Core.Zaux.Zpower
abbrev Zcompare := CompCert4Lean.Flocq.Core.Zaux.Zcompare
abbrev Zlt := CompCert4Lean.Flocq.Core.Zaux.Zlt
abbrev Zle := CompCert4Lean.Flocq.Core.Zaux.Zle

abbrev IZR := CompCert4Lean.Flocq.Core.Raux.IZR
abbrev R0 : R := CompCert4Lean.Flocq.Core.Raux.R0
abbrev Ropp := CompCert4Lean.Flocq.Core.Raux.Ropp
abbrev Rabs := CompCert4Lean.Flocq.Core.Raux.Rabs
abbrev Rlt := CompCert4Lean.Flocq.Core.Raux.Rlt
abbrev Rle := CompCert4Lean.Flocq.Core.Raux.Rle
abbrev Rcompare := CompCert4Lean.Flocq.Core.Raux.Rcompare
abbrev cond_Ropp := CompCert4Lean.Flocq.Core.Raux.cond_Ropp
abbrev mag := CompCert4Lean.Flocq.Core.Raux.mag

abbrev cond_Zopp := CompCert4Lean.Flocq.Core.Zaux.cond_Zopp
abbrev Zdigits := CompCert4Lean.Flocq.Core.Digits.Zdigits

abbrev float := CompCert4Lean.Flocq.Core.Defs.float
abbrev Float (beta : radix) (m e : Z) : float beta :=
  CompCert4Lean.Flocq.Core.Defs.float.mk m e
abbrev Fnum {beta : radix} (f : float beta) : Z :=
  CompCert4Lean.Flocq.Core.Defs.Fnum f
abbrev F2R {beta : radix} (f : float beta) : R :=
  CompCert4Lean.Flocq.Core.Defs.F2R f

abbrev bpow (beta : radix) (e : Z) : R :=
  CompCert4Lean.Flocq.Core.Raux.bpow beta e

/-! Theorem-facing interpretation over the explicit exact-real context. -/

abbrev ExactRealContext := CompCert4Lean.Flocq.Core.Raux.ExactRealContext

namespace Exact

abbrev Context := ExactRealContext
abbrev Magnitude (ctx : Context) := CompCert4Lean.Flocq.Core.Raux.Exact.Magnitude ctx
abbrev R (ctx : Context) := CompCert4Lean.Flocq.Core.Raux.Exact.R ctx

abbrev IZR (ctx : Context) : Z → R ctx := CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx
abbrev R0 (ctx : Context) : R ctx := CompCert4Lean.Flocq.Core.Raux.Exact.R0 ctx
abbrev Ropp (ctx : Context) : R ctx → R ctx := CompCert4Lean.Flocq.Core.Raux.Exact.Ropp ctx
abbrev Rabs (ctx : Context) : R ctx → R ctx := CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx
abbrev Rlt (ctx : Context) : R ctx → R ctx → Prop := CompCert4Lean.Flocq.Core.Raux.Exact.Rlt ctx
abbrev Rle (ctx : Context) : R ctx → R ctx → Prop := CompCert4Lean.Flocq.Core.Raux.Exact.Rle ctx
noncomputable abbrev Rcompare (ctx : Context) : R ctx → R ctx →
    CompCert4Lean.Flocq.Core.Zaux.comparison :=
  CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx
abbrev cond_Ropp (ctx : Context) (b : Bool) (x : R ctx) : R ctx :=
  CompCert4Lean.Flocq.Core.Raux.Exact.cond_Ropp ctx b x
abbrev bpow (ctx : Context) : radix → Z → R ctx :=
  CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx

abbrev F2R (ctx : Context) {beta : radix} (f : float beta) : R ctx :=
  CompCert4Lean.Flocq.Core.Defs.Exact.F2R ctx f

abbrev mag (magnitude : Magnitude ctx) (beta : radix) (x : R ctx) : Z :=
  (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_val

end Exact

/-! Exact source proposition descriptors for later proof migration. -/

def Rcompare_F2RStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (e m1 m2 : Z),
    Exact.Rcompare ctx (Exact.F2R ctx (Float beta m1 e)) (Exact.F2R ctx (Float beta m2 e)) =
      Zcompare m1 m2

def le_F2RStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (e m1 m2 : Z),
    Exact.Rle ctx (Exact.F2R ctx (Float beta m1 e)) (Exact.F2R ctx (Float beta m2 e)) →
      Zle m1 m2

def F2R_leStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (m1 m2 e : Z),
    Zle m1 m2 →
      Exact.Rle ctx (Exact.F2R ctx (Float beta m1 e)) (Exact.F2R ctx (Float beta m2 e))

def lt_F2RStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (e m1 m2 : Z),
    Exact.Rlt ctx (Exact.F2R ctx (Float beta m1 e)) (Exact.F2R ctx (Float beta m2 e)) →
      Zlt m1 m2

def F2R_ltStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (e m1 m2 : Z),
    Zlt m1 m2 →
      Exact.Rlt ctx (Exact.F2R ctx (Float beta m1 e)) (Exact.F2R ctx (Float beta m2 e))

def F2R_eqStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (e m1 m2 : Z),
    m1 = m2 →
      Exact.F2R ctx (Float beta m1 e) = Exact.F2R ctx (Float beta m2 e)

def eq_F2RStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (e m1 m2 : Z),
    Exact.F2R ctx (Float beta m1 e) = Exact.F2R ctx (Float beta m2 e) →
      m1 = m2

def F2R_ZabsStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (m e : Z),
    Exact.F2R ctx (Float beta (Zabs m) e) = Exact.Rabs ctx (Exact.F2R ctx (Float beta m e))

def F2R_ZoppStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (m e : Z),
    Exact.F2R ctx (Float beta (Zopp m) e) = Exact.Ropp ctx (Exact.F2R ctx (Float beta m e))

def F2R_cond_ZoppStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (b : Bool) (m e : Z),
    Exact.F2R ctx (Float beta (cond_Zopp b m) e) =
      Exact.cond_Ropp ctx b (Exact.F2R ctx (Float beta m e))

def F2R_0Statement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (e : Z),
    Exact.F2R ctx (Float beta Z0 e) = Exact.R0 ctx

def eq_0_F2RStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (m e : Z),
    Exact.F2R ctx (Float beta m e) = Exact.R0 ctx →
      m = Z0

def ge_0_F2RStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (m e : Z),
    Exact.Rle ctx (Exact.R0 ctx) (Exact.F2R ctx (Float beta m e)) →
      Zle Z0 m

def le_0_F2RStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (m e : Z),
    Exact.Rle ctx (Exact.F2R ctx (Float beta m e)) (Exact.R0 ctx) →
      Zle m Z0

def gt_0_F2RStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (m e : Z),
    Exact.Rlt ctx (Exact.R0 ctx) (Exact.F2R ctx (Float beta m e)) →
      Zlt Z0 m

def lt_0_F2RStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (m e : Z),
    Exact.Rlt ctx (Exact.F2R ctx (Float beta m e)) (Exact.R0 ctx) →
      Zlt m Z0

def F2R_ge_0Statement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (f : float beta),
    Zle Z0 (Fnum f) →
      Exact.Rle ctx (Exact.R0 ctx) (Exact.F2R ctx f)

def F2R_le_0Statement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (f : float beta),
    Zle (Fnum f) Z0 →
      Exact.Rle ctx (Exact.F2R ctx f) (Exact.R0 ctx)

def F2R_gt_0Statement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (f : float beta),
    Zlt Z0 (Fnum f) →
      Exact.Rlt ctx (Exact.R0 ctx) (Exact.F2R ctx f)

def F2R_lt_0Statement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (f : float beta),
    Zlt (Fnum f) Z0 →
      Exact.Rlt ctx (Exact.F2R ctx f) (Exact.R0 ctx)

def F2R_neq_0Statement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (f : float beta),
    Fnum f ≠ Z0 →
      Exact.F2R ctx f ≠ Exact.R0 ctx

def F2R_bpowStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (e : Z),
    Exact.F2R ctx (Float beta Zone e) = Exact.bpow ctx beta e

def bpow_le_F2RStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (m e : Z),
    Zlt Z0 m →
      Exact.Rle ctx (Exact.bpow ctx beta e) (Exact.F2R ctx (Float beta m e))

def F2R_p1_le_bpowStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (m e1 e2 : Z),
    Zlt Z0 m →
      Exact.Rlt ctx (Exact.F2R ctx (Float beta m e1)) (Exact.bpow ctx beta e2) →
        Exact.Rle ctx (Exact.F2R ctx (Float beta (Zadd m Zone) e1)) (Exact.bpow ctx beta e2)

def F2R_change_expStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (e' m e : Z),
    Zle e' e →
      Exact.F2R ctx (Float beta m e) =
        Exact.F2R ctx (Float beta (Zmul m (Zpower (beta : Z) (Zsub e e'))) e')

def mag_F2R_boundsStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (beta : radix) (x : Exact.R ctx) (m e : Z),
    Zlt Z0 m →
      (Exact.Rle ctx (Exact.F2R ctx (Float beta m e)) x ∧
        Exact.Rlt ctx x (Exact.F2R ctx (Float beta (Zadd m Zone) e))) →
        Exact.mag magnitude beta x = Exact.mag magnitude beta (Exact.F2R ctx (Float beta m e))

def mag_F2RStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (beta : radix) (m e : Z),
    m ≠ Z0 →
      Exact.mag magnitude beta (Exact.F2R ctx (Float beta m e)) =
        Zadd (Exact.mag magnitude beta (Exact.IZR ctx m)) e

def Zdigits_magStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (beta : radix) (n : Z),
    n ≠ Z0 →
      Zdigits beta n = Exact.mag magnitude beta (Exact.IZR ctx n)

def mag_F2R_ZdigitsStatement (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (beta : radix) (m e : Z),
    m ≠ Z0 →
      Exact.mag magnitude beta (Exact.F2R ctx (Float beta m e)) =
        Zadd (Zdigits beta m) e

def mag_F2R_bounds_ZdigitsStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (beta : radix) (x : Exact.R ctx) (m e : Z),
    Zlt Z0 m →
      (Exact.Rle ctx (Exact.F2R ctx (Float beta m e)) x ∧
        Exact.Rlt ctx x (Exact.F2R ctx (Float beta (Zadd m Zone) e))) →
        Exact.mag magnitude beta x = Zadd (Zdigits beta m) e

def bpow_le_F2R_m1Statement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (m e1 e2 : Z),
    Zlt Zone m →
      Exact.Rlt ctx (Exact.bpow ctx beta e2) (Exact.F2R ctx (Float beta m e1)) →
        Exact.Rle ctx (Exact.bpow ctx beta e2) (Exact.F2R ctx (Float beta (Zsub m Zone) e1))

end CompCert4Lean.Flocq.Core.Float_prop

namespace CompCert4Lean.Flocq.Core.Float_prop

private abbrev Pos := CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive
private abbrev xH' := CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH
private abbrev xO' := CompCert4Lean.Foundation.Numbers.Rocq.Coq.xO
private abbrev xI' := CompCert4Lean.Foundation.Numbers.Rocq.Coq.xI
private abbrev Zpos' := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
private abbrev intOfZ := CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ

private theorem fp_one_pos (ctx : ExactRealContext) :
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

private theorem fp_zpos_xO (p : Pos) :
    Zadd (Zpos' p) (Zpos' p) = Zpos' (xO' p) := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
    (intOfZ (Zpos' p) + intOfZ (Zpos' p))) = intOfZ (Zpos' (xO' p))
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) +
    Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) =
      Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (xO' p))
  rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (xO' p) =
      2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p by rfl]
  simp only [Int.ofNat_eq_coe]
  omega

private theorem fp_zpos_xI (p : Pos) :
    Zadd (Zpos' (xO' p)) (Zpos' xH') = Zpos' (xI' p) := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
    (intOfZ (Zpos' (xO' p)) + intOfZ (Zpos' xH'))) = intOfZ (Zpos' (xI' p))
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (xO' p)) +
    Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat xH') =
      Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (xI' p))
  rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (xO' p) =
      2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p by rfl,
      show CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat xH' = 1 by rfl,
      show CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (xI' p) =
      2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p + 1 by rfl]
  simp only [Int.ofNat_eq_coe]
  omega

private theorem fp_add_pos (ctx : ExactRealContext) {x y : ctx.spec.carrier}
    (hx : ctx.spec.lt ctx.spec.zero x) (hy : ctx.spec.lt ctx.spec.zero y) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.add x y) := by
  have h := ctx.certificate.orderedField.add_lt_compat_l x ctx.spec.zero y hy
  rw [ctx.certificate.orderedField.add_zero] at h
  exact ctx.certificate.orderedField.lt_trans ctx.spec.zero x (ctx.spec.add x y) hx h

private theorem fp_izr_pos (ctx : ExactRealContext) (p : Pos) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ (Zpos' p)) := by
  induction p with
  | xH => exact ctx.certificate.sourceLaws.ofZ_one ▸ fp_one_pos ctx
  | xO p ih =>
    rw [← fp_zpos_xO, ctx.certificate.sourceLaws.ofZ_add]
    exact fp_add_pos ctx ih ih
  | xI p ih =>
    rw [← fp_zpos_xI, ctx.certificate.sourceLaws.ofZ_add]
    rw [← fp_zpos_xO, ctx.certificate.sourceLaws.ofZ_add]
    rw [ctx.certificate.sourceLaws.ofZ_one]
    exact fp_add_pos ctx (fp_add_pos ctx ih ih) (fp_one_pos ctx)

private theorem fp_izr_pos_of_int (ctx : ExactRealContext) (z : Z)
    (hz : 0 < intOfZ z) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ z) := by
  cases z with
  | Z0 => exfalso; change (0 : Int) < 0 at hz; omega
  | Zneg p =>
      exfalso
      change (0 : Int) < -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hz
      have hp : 0 <= Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.ofNat_nonneg _
      omega
  | Zpos p => exact fp_izr_pos ctx p

private theorem fp_inv_pos (ctx : ExactRealContext) {x : ctx.spec.carrier}
    (hx : ctx.spec.lt ctx.spec.zero x) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.inv x) := by
  have hx0 : x ≠ ctx.spec.zero := by
    intro hz
    rw [hz] at hx
    exact (ctx.certificate.orderedField.lt_irrefl _ hx).elim
  rcases ctx.certificate.total_order ctx.spec.zero (ctx.spec.inv x) with h | h
  · rcases h with hlt | heq
    · exact hlt
    · have hmul := ctx.certificate.orderedField.inv_mul_cancel x hx0
      rw [← heq, ctx.certificate.orderedField.zero_mul] at hmul
      exact (ctx.certificate.orderedField.zero_ne_one hmul).elim
  · have hm := ctx.certificate.orderedField.mul_lt_compat_l x
        (ctx.spec.inv x) ctx.spec.zero hx h
    rw [ctx.certificate.orderedField.mul_comm x (ctx.spec.inv x),
      ctx.certificate.orderedField.inv_mul_cancel x hx0,
      ctx.certificate.orderedField.mul_zero] at hm
    exact (ctx.certificate.orderedField.lt_irrefl ctx.spec.one
      (ctx.certificate.orderedField.lt_trans ctx.spec.one ctx.spec.zero ctx.spec.one hm
        (fp_one_pos ctx))).elim

private theorem fp_bpow_pos (ctx : ExactRealContext) (r : radix) (e : Z) :
    ctx.spec.lt ctx.spec.zero (Exact.bpow ctx r e) := by
  have hrint : (2 : Int) ≤ intOfZ r.radix_val := by
    have h := r.radix_prop
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.leb
      (Zpos' (xO' xH')) r.radix_val = true at h
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.leb] at h
    exact h
  have hrpos : 0 < intOfZ r.radix_val := by omega
  cases e with
  | Z0 =>
      change ctx.spec.lt ctx.spec.zero ctx.spec.one
      exact fp_one_pos ctx
  | Zpos p =>
      change ctx.spec.lt ctx.spec.zero
        (ctx.spec.ofZ (CompCert4Lean.Flocq.Core.Zaux.Zpower_pos r.radix_val p))
      apply fp_izr_pos_of_int ctx
      change 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (Int.pow (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val)
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p)))
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      exact Int.pow_pos hrpos
  | Zneg p =>
      change ctx.spec.lt ctx.spec.zero
        (ctx.spec.inv (ctx.spec.ofZ
          (CompCert4Lean.Flocq.Core.Zaux.Zpower_pos r.radix_val p)))
      apply fp_inv_pos ctx
      apply fp_izr_pos_of_int ctx
      change 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (Int.pow (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val)
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p)))
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      exact Int.pow_pos hrpos

theorem F2R_gt_0 (ctx : ExactRealContext) : F2R_gt_0Statement ctx := by
  intro beta f hf
  cases f with
  | Float m e =>
      change ctx.spec.lt ctx.spec.zero
        (ctx.spec.mul (ctx.spec.ofZ m) (Exact.bpow ctx _ e))
      have hm : ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ m) := by
        apply fp_izr_pos_of_int ctx m
        exact hf
      have hmul := ctx.certificate.orderedField.mul_lt_compat_l
        (Exact.bpow ctx beta e) ctx.spec.zero (ctx.spec.ofZ m)
          (fp_bpow_pos ctx beta e) hm
      rw [ctx.certificate.orderedField.mul_zero,
        ctx.certificate.orderedField.mul_comm (Exact.bpow ctx beta e)] at hmul
      exact hmul

end CompCert4Lean.Flocq.Core.Float_prop

namespace CompCert4Lean.Flocq.Core.Float_prop

private theorem fp2_rcompare_lt (ctx : ExactRealContext)
    {x y : ctx.spec.carrier} (hxy : ctx.spec.lt x y) :
    Exact.Rcompare ctx x y = CompCert4Lean.Flocq.Core.Zaux.Lt := by
  cases hdec : ctx.spec.lt_dec x y with
  | left _ =>
      simp [CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare,
        CompCert4Lean.Foundation.FlocqReal.ExactReal.total_order_T, hdec]
  | right hnxy => exact (hnxy hxy).elim

private theorem fp2_rcompare_eq (ctx : ExactRealContext)
    {x y : ctx.spec.carrier} (hxy : x = y) :
    Exact.Rcompare ctx x y = CompCert4Lean.Flocq.Core.Zaux.Eq := by
  subst y
  cases hdec : ctx.spec.lt_dec x x with
  | left hlt => exact (ctx.certificate.orderedField.lt_irrefl x hlt).elim
  | right _ =>
      simp [CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare,
        CompCert4Lean.Foundation.FlocqReal.ExactReal.total_order_T, hdec]

private theorem fp2_rcompare_gt (ctx : ExactRealContext)
    {x y : ctx.spec.carrier} (hyx : ctx.spec.lt y x) :
    Exact.Rcompare ctx x y = CompCert4Lean.Flocq.Core.Zaux.Gt := by
  have hnxy : ¬ctx.spec.lt x y := by
    intro hxy
    exact ctx.certificate.orderedField.lt_irrefl x
      (ctx.certificate.orderedField.lt_trans x y x hxy hyx)
  cases hxy : ctx.spec.lt_dec x y with
  | left hlt => exact (hnxy hlt).elim
  | right _ =>
      cases hyx_dec : ctx.spec.lt_dec y x with
      | left _ =>
          simp [CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare,
            CompCert4Lean.Foundation.FlocqReal.ExactReal.total_order_T, hxy, hyx_dec]
      | right hnyx => exact (hnyx hyx).elim

private theorem fp2_rcompare_mul_pos_right (ctx : ExactRealContext)
    (z x y : ctx.spec.carrier) (hz : ctx.spec.lt ctx.spec.zero z) :
    Exact.Rcompare ctx (ctx.spec.mul x z) (ctx.spec.mul y z) =
      Exact.Rcompare ctx x y := by
  rcases ctx.certificate.total_order x y with h | h
  · rcases h with hlt | heq
    · have hmul := ctx.certificate.orderedField.mul_lt_compat_l z x y hz hlt
      rw [ctx.certificate.orderedField.mul_comm z x,
        ctx.certificate.orderedField.mul_comm z y] at hmul
      rw [fp2_rcompare_lt ctx hmul, fp2_rcompare_lt ctx hlt]
    · subst y
      rw [fp2_rcompare_eq ctx rfl, fp2_rcompare_eq ctx rfl]
  · have hmul := ctx.certificate.orderedField.mul_lt_compat_l z y x hz h
    rw [ctx.certificate.orderedField.mul_comm z y,
      ctx.certificate.orderedField.mul_comm z x] at hmul
    rw [fp2_rcompare_gt ctx hmul, fp2_rcompare_gt ctx h]

private theorem fp2_ofZ_lt (ctx : ExactRealContext) {x y : Z}
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
  have hdpos := fp_izr_pos_of_int ctx d hd
  rw [hsum, ctx.certificate.sourceLaws.ofZ_add]
  have hadd := ctx.certificate.orderedField.add_lt_compat_l
    (ctx.spec.ofZ x) ctx.spec.zero (ctx.spec.ofZ d) hdpos
  rw [ctx.certificate.orderedField.add_zero] at hadd
  exact hadd

private theorem fp2_rcompare_IZR (ctx : ExactRealContext) (x y : Z) :
    Exact.Rcompare ctx (Exact.IZR ctx x) (Exact.IZR ctx y) = Zcompare x y := by
  change Exact.Rcompare ctx (ctx.spec.ofZ x) (ctx.spec.ofZ y) = Zcompare x y
  by_cases hxy : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y
  · rw [fp2_rcompare_lt ctx (fp2_ofZ_lt ctx hxy)]
    change CompCert4Lean.Flocq.Core.Zaux.Lt =
      (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y then
        CompCert4Lean.Flocq.Core.Zaux.Lt else
      if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y then
        CompCert4Lean.Flocq.Core.Zaux.Eq else CompCert4Lean.Flocq.Core.Zaux.Gt)
    rw [if_pos hxy]
  by_cases hyx : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x
  · rw [fp2_rcompare_gt ctx (fp2_ofZ_lt ctx hyx)]
    change CompCert4Lean.Flocq.Core.Zaux.Gt =
      (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y then
        CompCert4Lean.Flocq.Core.Zaux.Lt else
      if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y then
        CompCert4Lean.Flocq.Core.Zaux.Eq else CompCert4Lean.Flocq.Core.Zaux.Gt)
    rw [if_neg hxy, if_neg (by omega)]
  · have heq : x = y := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      omega
    subst y
    rw [fp2_rcompare_eq ctx rfl]
    change CompCert4Lean.Flocq.Core.Zaux.Eq =
      (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x then
        CompCert4Lean.Flocq.Core.Zaux.Lt else
      if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x then
        CompCert4Lean.Flocq.Core.Zaux.Eq else CompCert4Lean.Flocq.Core.Zaux.Gt)
    rw [if_neg hxy, if_pos rfl]

theorem Rcompare_F2R (ctx : ExactRealContext) : Rcompare_F2RStatement ctx := by
  intro beta e m1 m2
  change Exact.Rcompare ctx
    (ctx.spec.mul (ctx.spec.ofZ m1) (Exact.bpow ctx beta e))
    (ctx.spec.mul (ctx.spec.ofZ m2) (Exact.bpow ctx beta e)) = Zcompare m1 m2
  rw [fp2_rcompare_mul_pos_right ctx (Exact.bpow ctx beta e)
    (ctx.spec.ofZ m1) (ctx.spec.ofZ m2) (fp_bpow_pos ctx beta e)]
  exact fp2_rcompare_IZR ctx m1 m2

end CompCert4Lean.Flocq.Core.Float_prop

namespace CompCert4Lean.Flocq.Core.Float_prop

theorem F2R_le (ctx : ExactRealContext) : F2R_leStatement ctx := by
  intro beta m1 m2 e h12
  change ctx.spec.le
    (ctx.spec.mul (ctx.spec.ofZ m1) (Exact.bpow ctx beta e))
    (ctx.spec.mul (ctx.spec.ofZ m2) (Exact.bpow ctx beta e))
  have hz : ctx.spec.le ctx.spec.zero (Exact.bpow ctx beta e) := by
    simpa [CompCert4Lean.Flocq.Core.Raux.Exact.Rle,
      CompCert4Lean.Flocq.Core.Raux.Exact.R0,
      CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle,
      CompCert4Lean.Foundation.FlocqReal.ExactReal.R0] using
      (CompCert4Lean.Flocq.Core.Raux.bpow_ge_0 ctx beta e)
  have hz' : CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle ctx.spec
      (CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR ctx.spec Z0)
      (Exact.bpow ctx beta e) := by
    simpa [CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle,
      CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR,
      ctx.certificate.sourceLaws.ofZ_zero] using hz
  have hm :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_le
      ctx m1 m2 h12
  change ctx.spec.le (ctx.spec.ofZ m1) (ctx.spec.ofZ m2) at hm
  exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
    ctx (Exact.bpow ctx beta e) (ctx.spec.ofZ m1) (ctx.spec.ofZ m2) hz' hm

end CompCert4Lean.Flocq.Core.Float_prop

namespace CompCert4Lean.Flocq.Core.Float_prop

private theorem fp_float_mul_lt_of_int_lt (ctx : ExactRealContext)
    (beta : radix) (e m1 m2 : Z)
    (h12 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m1 <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m2) :
    ctx.spec.lt
      (ctx.spec.mul (ctx.spec.ofZ m1) (Exact.bpow ctx beta e))
      (ctx.spec.mul (ctx.spec.ofZ m2) (Exact.bpow ctx beta e)) := by
  have hz : ctx.spec.lt ctx.spec.zero (Exact.bpow ctx beta e) := by
    simpa [CompCert4Lean.Flocq.Core.Raux.Exact.Rlt,
      CompCert4Lean.Flocq.Core.Raux.Exact.R0,
      CompCert4Lean.Foundation.FlocqReal.ExactReal.Rlt,
      CompCert4Lean.Foundation.FlocqReal.ExactReal.R0] using
      (CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta e)
  have hm :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt
      ctx m1 m2 h12
  change ctx.spec.lt (ctx.spec.ofZ m1) (ctx.spec.ofZ m2) at hm
  have hmul := ctx.certificate.orderedField.mul_lt_compat_l
    (Exact.bpow ctx beta e) (ctx.spec.ofZ m1) (ctx.spec.ofZ m2) hz hm
  rw [ctx.certificate.orderedField.mul_comm (Exact.bpow ctx beta e) (ctx.spec.ofZ m1),
    ctx.certificate.orderedField.mul_comm (Exact.bpow ctx beta e) (ctx.spec.ofZ m2)] at hmul
  exact hmul

theorem le_F2R (ctx : ExactRealContext) : le_F2RStatement ctx := by
  intro beta e m1 m2 h
  change ctx.spec.le
    (ctx.spec.mul (ctx.spec.ofZ m1) (Exact.bpow ctx beta e))
    (ctx.spec.mul (ctx.spec.ofZ m2) (Exact.bpow ctx beta e)) at h
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m1 ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m2
  by_cases hle : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m1 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m2
  · exact hle
  · have h21 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m2 <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m1 := by omega
    have hmul := fp_float_mul_lt_of_int_lt ctx beta e m2 m1 h21
    exact False.elim (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hmul).2 h)

theorem lt_F2R (ctx : ExactRealContext) : lt_F2RStatement ctx := by
  intro beta e m1 m2 h
  change ctx.spec.lt
    (ctx.spec.mul (ctx.spec.ofZ m1) (Exact.bpow ctx beta e))
    (ctx.spec.mul (ctx.spec.ofZ m2) (Exact.bpow ctx beta e)) at h
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m1 <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m2
  by_cases hlt : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m1 <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m2
  · exact hlt
  · have h21le : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m2 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m1 := by omega
    rcases Int.lt_or_eq_of_le h21le with h21 | heq
    · have hmul := fp_float_mul_lt_of_int_lt ctx beta e m2 m1 h21
      exact False.elim (ctx.certificate.orderedField.lt_irrefl _
        (ctx.certificate.orderedField.lt_trans _ _ _ h hmul))
    · have hm : m1 = m2 := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        exact heq.symm
      subst m2
      exact False.elim (ctx.certificate.orderedField.lt_irrefl _ h)

theorem F2R_lt (ctx : ExactRealContext) : F2R_ltStatement ctx := by
  intro beta e m1 m2 h12
  change ctx.spec.lt
    (ctx.spec.mul (ctx.spec.ofZ m1) (Exact.bpow ctx beta e))
    (ctx.spec.mul (ctx.spec.ofZ m2) (Exact.bpow ctx beta e))
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m1 <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m2 at h12
  exact fp_float_mul_lt_of_int_lt ctx beta e m1 m2 h12

end CompCert4Lean.Flocq.Core.Float_prop

namespace CompCert4Lean.Flocq.Core.Float_prop

theorem F2R_eq : ∀ (ctx : ExactRealContext), F2R_eqStatement ctx := by
  intro ctx beta e m1 m2 h
  subst m2
  rfl

theorem eq_F2R : ∀ (ctx : ExactRealContext), eq_F2RStatement ctx := by
  intro ctx beta e m1 m2 h
  change ctx.spec.mul (ctx.spec.ofZ m1) (Exact.bpow ctx beta e) =
    ctx.spec.mul (ctx.spec.ofZ m2) (Exact.bpow ctx beta e) at h
  have h12 : Zle m1 m2 := by
    apply le_F2R ctx beta e m1 m2
    change ctx.spec.le
      (ctx.spec.mul (ctx.spec.ofZ m1) (Exact.bpow ctx beta e))
      (ctx.spec.mul (ctx.spec.ofZ m2) (Exact.bpow ctx beta e))
    rw [h]
    exact ctx.certificate.orderedField.le_refl _
  have h21 : Zle m2 m1 := by
    apply le_F2R ctx beta e m2 m1
    change ctx.spec.le
      (ctx.spec.mul (ctx.spec.ofZ m2) (Exact.bpow ctx beta e))
      (ctx.spec.mul (ctx.spec.ofZ m1) (Exact.bpow ctx beta e))
    rw [h]
    exact ctx.certificate.orderedField.le_refl _
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m1 =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m2
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m1 ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m2 at h12
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m2 ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m1 at h21
  omega

private theorem fp_mul_neg_left (ctx : ExactRealContext)
    (x y : ctx.spec.carrier) :
    ctx.spec.mul (ctx.spec.neg x) y =
      ctx.spec.neg (ctx.spec.mul x y) := by
  have h : ctx.spec.add (ctx.spec.mul (ctx.spec.neg x) y)
      (ctx.spec.mul x y) = ctx.spec.zero := by
    rw [ctx.certificate.orderedField.mul_comm (ctx.spec.neg x) y,
      ctx.certificate.orderedField.mul_comm x y,
      ← ctx.certificate.orderedField.left_distrib,
      ctx.certificate.orderedField.neg_add_cancel,
      ctx.certificate.orderedField.mul_zero]
  symm
  calc
    ctx.spec.neg (ctx.spec.mul x y) =
        ctx.spec.add (ctx.spec.neg (ctx.spec.mul x y)) ctx.spec.zero :=
      (ctx.certificate.orderedField.add_zero _).symm
    _ = ctx.spec.add (ctx.spec.neg (ctx.spec.mul x y))
        (ctx.spec.add (ctx.spec.mul (ctx.spec.neg x) y)
          (ctx.spec.mul x y)) := by rw [h]
    _ = ctx.spec.add (ctx.spec.neg (ctx.spec.mul x y))
        (ctx.spec.add (ctx.spec.mul x y)
          (ctx.spec.mul (ctx.spec.neg x) y)) := by
      rw [ctx.certificate.orderedField.add_comm
        (ctx.spec.mul (ctx.spec.neg x) y)]
    _ = ctx.spec.add
        (ctx.spec.add (ctx.spec.neg (ctx.spec.mul x y))
          (ctx.spec.mul x y))
        (ctx.spec.mul (ctx.spec.neg x) y) := by
      rw [ctx.certificate.orderedField.add_assoc]
    _ = ctx.spec.add ctx.spec.zero
        (ctx.spec.mul (ctx.spec.neg x) y) := by
      rw [ctx.certificate.orderedField.neg_add_cancel]
    _ = ctx.spec.mul (ctx.spec.neg x) y :=
      ctx.certificate.orderedField.zero_add _

theorem F2R_Zopp : ∀ (ctx : ExactRealContext), F2R_ZoppStatement ctx := by
  intro ctx beta m e
  change ctx.spec.mul (ctx.spec.ofZ (Zopp m)) (Exact.bpow ctx beta e) =
    ctx.spec.neg (ctx.spec.mul (ctx.spec.ofZ m) (Exact.bpow ctx beta e))
  rw [ctx.certificate.sourceLaws.ofZ_neg]
  exact fp_mul_neg_left ctx _ _

private theorem fp_neg_lt_zero (ctx : ExactRealContext)
    (x : ctx.spec.carrier) (hx : ctx.spec.lt ctx.spec.zero x) :
    ctx.spec.lt (ctx.spec.neg x) ctx.spec.zero := by
  have h := ctx.certificate.orderedField.add_lt_compat_l
    (ctx.spec.neg x) ctx.spec.zero x hx
  rw [ctx.certificate.orderedField.neg_add_cancel,
    ctx.certificate.orderedField.add_zero] at h
  exact h

private theorem fp_neg_neg (ctx : ExactRealContext) (x : ctx.spec.carrier) :
    ctx.spec.neg (ctx.spec.neg x) = x := by
  calc
    ctx.spec.neg (ctx.spec.neg x) =
        ctx.spec.add (ctx.spec.neg (ctx.spec.neg x)) ctx.spec.zero :=
      (ctx.certificate.orderedField.add_zero _).symm
    _ = ctx.spec.add (ctx.spec.neg (ctx.spec.neg x))
        (ctx.spec.add x (ctx.spec.neg x)) := by
      rw [ctx.certificate.orderedField.add_comm x (ctx.spec.neg x),
        ctx.certificate.orderedField.neg_add_cancel]
    _ = ctx.spec.add
        (ctx.spec.add (ctx.spec.neg (ctx.spec.neg x)) (ctx.spec.neg x)) x := by
      rw [ctx.certificate.orderedField.add_comm x (ctx.spec.neg x)]
      exact (ctx.certificate.orderedField.add_assoc _ _ _).symm
    _ = ctx.spec.add ctx.spec.zero x := by
      rw [ctx.certificate.orderedField.neg_add_cancel]
    _ = x := ctx.certificate.orderedField.zero_add _

private theorem fp_mul_pos (ctx : ExactRealContext) {x y : ctx.spec.carrier}
    (hx : ctx.spec.lt ctx.spec.zero x) (hy : ctx.spec.lt ctx.spec.zero y) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.mul x y) := by
  have h := ctx.certificate.orderedField.mul_lt_compat_l x ctx.spec.zero y hx hy
  rw [ctx.certificate.orderedField.mul_zero] at h
  exact h

private theorem fp_zneg_eq (p : Pos) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg p =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p) := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  rfl

private theorem fp_zabs_pos (p : Pos) :
    Zabs (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p)) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p)
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]

private theorem fp_zabs_neg (p : Pos) :
    Zabs (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg p) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg p)) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p)
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]

theorem F2R_Zabs : ∀ (ctx : ExactRealContext), F2R_ZabsStatement ctx := by
  intro ctx beta m e
  cases m with
  | Z0 =>
      change ctx.spec.mul (ctx.spec.ofZ Z0) (Exact.bpow ctx beta e) =
        ctx.spec.abs (ctx.spec.mul (ctx.spec.ofZ Z0) (Exact.bpow ctx beta e))
      rw [ctx.certificate.sourceLaws.ofZ_zero,
        ctx.certificate.orderedField.zero_mul]
      exact (ctx.certificate.sourceLaws.abs_nonnegative ctx.spec.zero
        (ctx.certificate.orderedField.le_refl ctx.spec.zero)).symm
  | Zpos p =>
      rw [fp_zabs_pos]
      change ctx.spec.mul (ctx.spec.ofZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))
          (Exact.bpow ctx beta e) =
        ctx.spec.abs (ctx.spec.mul (ctx.spec.ofZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))
          (Exact.bpow ctx beta e))
      have hle := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
        (fp_mul_pos ctx (fp_izr_pos ctx p) (fp_bpow_pos ctx beta e))
      exact (ctx.certificate.sourceLaws.abs_nonnegative _ hle.1).symm
  | Zneg p =>
      rw [fp_zabs_neg]
      change ctx.spec.mul (ctx.spec.ofZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))
          (Exact.bpow ctx beta e) =
        ctx.spec.abs (ctx.spec.mul (ctx.spec.ofZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg p))
          (Exact.bpow ctx beta e))
      have hpos := fp_mul_pos ctx (fp_izr_pos ctx p) (fp_bpow_pos ctx beta e)
      have hneg : ctx.spec.mul (ctx.spec.ofZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg p))
          (Exact.bpow ctx beta e) =
        ctx.spec.neg (ctx.spec.mul (ctx.spec.ofZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))
          (Exact.bpow ctx beta e)) := by
        rw [fp_zneg_eq, ctx.certificate.sourceLaws.ofZ_neg]
        exact fp_mul_neg_left ctx _ _
      calc
        ctx.spec.mul (ctx.spec.ofZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))
            (Exact.bpow ctx beta e) =
          ctx.spec.neg (ctx.spec.neg (ctx.spec.mul (ctx.spec.ofZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))
            (Exact.bpow ctx beta e))) := (fp_neg_neg ctx _).symm
        _ = ctx.spec.abs (ctx.spec.neg (ctx.spec.mul (ctx.spec.ofZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))
            (Exact.bpow ctx beta e))) :=
          (ctx.certificate.sourceLaws.abs_negative _
            (fp_neg_lt_zero ctx _ hpos)).symm
        _ = ctx.spec.abs (ctx.spec.mul (ctx.spec.ofZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg p))
            (Exact.bpow ctx beta e)) := congrArg ctx.spec.abs hneg.symm

end CompCert4Lean.Flocq.Core.Float_prop

namespace CompCert4Lean.Flocq.Core.Float_prop

theorem F2R_cond_Zopp : ∀ (ctx : ExactRealContext), F2R_cond_ZoppStatement ctx := by
  intro ctx beta b m e
  cases b with
  | false =>
      rfl
  | true =>
      change ctx.spec.mul (ctx.spec.ofZ (Zopp m)) (Exact.bpow ctx beta e) =
        ctx.spec.neg (ctx.spec.mul (ctx.spec.ofZ m) (Exact.bpow ctx beta e))
      rw [ctx.certificate.sourceLaws.ofZ_neg]
      exact fp_mul_neg_left ctx _ _

end CompCert4Lean.Flocq.Core.Float_prop
