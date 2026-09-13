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

namespace CompCert4Lean.Flocq.Core.Float_prop

theorem F2R_0 : ∀ (ctx : ExactRealContext), F2R_0Statement ctx := by
  intro ctx beta e
  change ctx.spec.mul (ctx.spec.ofZ Z0) (Exact.bpow ctx beta e) = ctx.spec.zero
  rw [ctx.certificate.sourceLaws.ofZ_zero,
    ctx.certificate.orderedField.zero_mul]

end CompCert4Lean.Flocq.Core.Float_prop

namespace CompCert4Lean.Flocq.Core.Float_prop

theorem eq_0_F2R : ∀ (ctx : ExactRealContext), eq_0_F2RStatement ctx := by
  intro ctx beta m e h
  apply eq_F2R ctx beta e m Z0
  rw [F2R_0 ctx beta e]
  exact h

end CompCert4Lean.Flocq.Core.Float_prop

namespace CompCert4Lean.Flocq.Core.Float_prop

theorem ge_0_F2R : ∀ (ctx : ExactRealContext), ge_0_F2RStatement ctx := by
  intro ctx beta m e h
  apply le_F2R ctx beta e Z0 m
  rw [F2R_0 ctx beta e]
  exact h

end CompCert4Lean.Flocq.Core.Float_prop

namespace CompCert4Lean.Flocq.Core.Float_prop

theorem le_0_F2R : ∀ (ctx : ExactRealContext), le_0_F2RStatement ctx := by
  intro ctx beta m e h
  apply le_F2R ctx beta e m Z0
  rw [F2R_0 ctx beta e]
  exact h

theorem gt_0_F2R : ∀ (ctx : ExactRealContext), gt_0_F2RStatement ctx := by
  intro ctx beta m e h
  apply lt_F2R ctx beta e Z0 m
  rw [F2R_0 ctx beta e]
  exact h

theorem lt_0_F2R : ∀ (ctx : ExactRealContext), lt_0_F2RStatement ctx := by
  intro ctx beta m e h
  apply lt_F2R ctx beta e m Z0
  rw [F2R_0 ctx beta e]
  exact h

theorem F2R_ge_0 : ∀ (ctx : ExactRealContext), F2R_ge_0Statement ctx := by
  intro ctx beta f hf
  cases f with
  | Float m e =>
      rw [← F2R_0 ctx beta e]
      apply F2R_le ctx beta Z0 m e
      exact hf

end CompCert4Lean.Flocq.Core.Float_prop

namespace CompCert4Lean.Flocq.Core.Float_prop

theorem F2R_le_0 : ∀ (ctx : ExactRealContext), F2R_le_0Statement ctx := by
  intro ctx beta f hf
  cases f with
  | Float m e =>
      rw [← F2R_0 ctx beta e]
      apply F2R_le ctx beta m Z0 e
      exact hf

theorem F2R_lt_0 : ∀ (ctx : ExactRealContext), F2R_lt_0Statement ctx := by
  intro ctx beta f hf
  cases f with
  | Float m e =>
      rw [← F2R_0 ctx beta e]
      apply F2R_lt ctx beta e m Z0
      exact hf

theorem F2R_neq_0 : ∀ (ctx : ExactRealContext), F2R_neq_0Statement ctx := by
  intro ctx beta f hf hzero
  apply hf
  cases f with
  | Float m e =>
      apply eq_0_F2R ctx beta m e
      exact hzero

theorem F2R_bpow : ∀ (ctx : ExactRealContext), F2R_bpowStatement ctx := by
  intro ctx beta e
  change ctx.spec.mul (ctx.spec.ofZ Zone) (Exact.bpow ctx beta e) =
    Exact.bpow ctx beta e
  rw [ctx.certificate.sourceLaws.ofZ_one,
    ctx.certificate.orderedField.one_mul]

end CompCert4Lean.Flocq.Core.Float_prop

namespace CompCert4Lean.Flocq.Core.Float_prop

private abbrev fpZneg := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg
private abbrev fpZpowerPos :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower_pos

private theorem fp_zadd_sub_cancel (a b : Z) :
    Zadd (Zsub b a) a = b := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

private theorem fp_zadd_sub_cancel' (a b : Z) :
    Zadd a (Zsub b a) = b := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

theorem F2R_change_exp : ∀ (ctx : ExactRealContext), F2R_change_expStatement ctx := by
  intro ctx beta e' m e he
  change ctx.spec.mul (ctx.spec.ofZ m) (Exact.bpow ctx beta e) =
    ctx.spec.mul (ctx.spec.ofZ (Zmul m (Zpower (beta : Z) (Zsub e e'))))
      (Exact.bpow ctx beta e')
  have hnonneg : Zle Z0 (Zsub e e') := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub e e')
    simp only [Zsub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change (0 : Int) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e -
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e'
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e' ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e at he
    omega
  have hp := CompCert4Lean.Flocq.Core.Raux.IZR_Zpower ctx beta (Zsub e e') hnonneg
  have hm := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR
    ctx m (Zpower (beta : Z) (Zsub e e'))
  have hm' : ctx.spec.ofZ (Zmul m (Zpower (beta : Z) (Zsub e e'))) =
      ctx.spec.mul (ctx.spec.ofZ m)
        (ctx.spec.ofZ (Zpower (beta : Z) (Zsub e e'))) := by
    change ctx.spec.ofZ
        (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Z.mul m
          (Zpower (beta : Z) (Zsub e e'))) =
      ctx.spec.mul (ctx.spec.ofZ m)
        (ctx.spec.ofZ (Zpower (beta : Z) (Zsub e e')))
    exact hm
  have hp' : ctx.spec.ofZ (Zpower (beta : Z) (Zsub e e')) =
      Exact.bpow ctx beta (Zsub e e') := by
    change ctx.spec.ofZ (Zpower (beta : Z) (Zsub e e')) =
      Exact.bpow ctx beta (Zsub e e') at hp
    exact hp
  change ctx.spec.mul (ctx.spec.ofZ m) (Exact.bpow ctx beta e) =
    ctx.spec.mul (ctx.spec.ofZ (Zmul m (Zpower (beta : Z) (Zsub e e'))))
      (Exact.bpow ctx beta e')
  rw [hm', hp']
  rw [ctx.certificate.orderedField.mul_assoc]
  have hbplus := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta (Zsub e e') e'
  change Exact.bpow ctx beta (Zadd (Zsub e e') e') =
      ctx.spec.mul (Exact.bpow ctx beta (Zsub e e')) (Exact.bpow ctx beta e') at hbplus
  rw [← hbplus]
  rw [fp_zadd_sub_cancel e' e]

end CompCert4Lean.Flocq.Core.Float_prop

namespace CompCert4Lean.Flocq.Core.Float_prop

theorem bpow_le_F2R : ∀ (ctx : ExactRealContext), bpow_le_F2RStatement ctx := by
  intro ctx beta m e hm
  rw [← F2R_bpow ctx beta e]
  apply F2R_le ctx beta Zone m e
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m
  change (1 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m at hm
  change (0 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m at hm
  omega

end CompCert4Lean.Flocq.Core.Float_prop

namespace CompCert4Lean.Flocq.Core.Float_prop

private theorem fp_int_pow_gt_one (a : Int) (ha : (2 : Int) ≤ a) :
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
            have hmul' : (1 : Int) * a ≤ a ^ k * a := by simpa using hmul
            have hmul'' : a ≤ a ^ k * a := by simpa only [Int.one_mul] using hmul'
            exact Int.le_trans haone hmul''
      have hpow_one : (1 : Int) ≤ a ^ n := hpow_one_all n
      rw [Int.pow_succ]
      have hmul := Int.mul_le_mul_of_nonneg_right hpow_one (Int.le_of_lt hapos)
      have haone : (1 : Int) < a := by omega
      have hmul' : (1 : Int) * a ≤ a ^ n * a := by simpa using hmul
      have hmul'' : a ≤ a ^ n * a := by simpa using hmul'
      exact Int.lt_of_lt_of_le haone hmul''

private theorem fp_radix_int_ge_two (r : radix) :
    (2 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val := by
  have hr := r.radix_prop
  change (if (2 : Int) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val then true else false) = true at hr
  simpa using hr

private theorem fp_bpow_gt_one (ctx : ExactRealContext) (r : radix)
    {e : Z} (he : Zlt Z0 e) :
    ctx.spec.lt ctx.spec.one (Exact.bpow ctx r e) := by
  cases e with
  | Z0 => change (0 : Int) < 0 at he; omega
  | Zneg p =>
      change (0 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fpZneg p) at he
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at he
      omega
  | Zpos p =>
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpow : (1 : Int) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (fpZpowerPos r.radix_val p) := by
        simp only [fpZpowerPos,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow_pos,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        exact fp_int_pow_gt_one _ (fp_radix_int_ge_two r) _ hp
      have h := fp2_ofZ_lt ctx (x := Zone)
        (y := fpZpowerPos r.radix_val p) (by
          change (1 : Int) <
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (fpZpowerPos r.radix_val p)
          exact hpow)
      change ctx.spec.lt (ctx.spec.ofZ Zone)
        (ctx.spec.ofZ (fpZpowerPos r.radix_val p)) at h
      rw [ctx.certificate.sourceLaws.ofZ_one] at h
      exact h

private theorem fp_bpow_lt (ctx : ExactRealContext) (r : radix)
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
  have hsum : Zadd e1 d = e2 := by exact fp_zadd_sub_cancel' e1 e2
  have hmul : Exact.bpow ctx r e2 =
      ctx.spec.mul (Exact.bpow ctx r e1) (Exact.bpow ctx r d) := by
    rw [← hsum]
    exact CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx r e1 d
  have hpos : Exact.Rlt ctx (ctx.spec.zero) (Exact.bpow ctx r e1) :=
    CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx r e1
  have hone : Exact.Rlt ctx (ctx.spec.one) (Exact.bpow ctx r d) :=
    fp_bpow_gt_one ctx r hd
  have hpos' : Exact.Rlt ctx (Exact.IZR ctx Z0) (Exact.bpow ctx r e1) := by
    change ctx.spec.lt (ctx.spec.ofZ Z0) (Exact.bpow ctx r e1)
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

private theorem fp_bpow_lt_imp_exp_lt (ctx : ExactRealContext) (r : radix)
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
    · have hp := fp_bpow_lt ctx r (show Zlt b a by exact hba)
      exact (ctx.certificate.orderedField.lt_irrefl _
        (ctx.certificate.orderedField.lt_trans _ _ _ hp h)).elim
    · have hab : a = b := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        exact heq.symm
      subst b
      exact (ctx.certificate.orderedField.lt_irrefl _ h).elim

private theorem fp_ofZ_lt_of_real_lt (ctx : ExactRealContext) {x y : Z}
    (h : ctx.spec.lt (ctx.spec.ofZ x) (ctx.spec.ofZ y)) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y := by
  by_cases hxy : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y
  · exact hxy
  · have hyx : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x := by omega
    rcases Int.lt_or_eq_of_le hyx with hyx | heq
    · have hrev := fp2_ofZ_lt ctx hyx
      exact (ctx.certificate.orderedField.lt_irrefl _
        (ctx.certificate.orderedField.lt_trans _ _ _ h hrev)).elim
    · have heq' : x = y := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        exact heq.symm
      subst y
      exact (ctx.certificate.orderedField.lt_irrefl _ h).elim

theorem bpow_le_F2R_m1 : ∀ (ctx : ExactRealContext), bpow_le_F2R_m1Statement ctx := by
  intro ctx beta m e1 e2 hm h
  have hmpos : Zlt Z0 (Zsub m Zone) := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub m Zone)
    simp only [Zsub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change (0 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m - 1
    change (1 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m at hm
    omega
  by_cases he : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2
  · let d := Zsub e2 e1
    have hd : Zle Z0 d := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d
      simp only [d, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      change (0 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 -
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1
      omega
    have hsum : Zadd e1 d = e2 := by exact fp_zadd_sub_cancel' e1 e2
    have hdecomp : Exact.bpow ctx beta e2 =
        ctx.spec.mul (Exact.bpow ctx beta d) (Exact.bpow ctx beta e1) := by
      rw [← hsum]
      have hbp := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta e1 d
      change Exact.bpow ctx beta (Zadd e1 d) =
        ctx.spec.mul (Exact.bpow ctx beta e1) (Exact.bpow ctx beta d) at hbp
      calc
        Exact.bpow ctx beta (Zadd e1 d) =
            ctx.spec.mul (Exact.bpow ctx beta e1) (Exact.bpow ctx beta d) := hbp
        _ = ctx.spec.mul (Exact.bpow ctx beta d) (Exact.bpow ctx beta e1) :=
          ctx.certificate.orderedField.mul_comm _ _
    have h' : ctx.spec.lt
          (ctx.spec.mul (Exact.bpow ctx beta d) (Exact.bpow ctx beta e1))
          (ctx.spec.mul (ctx.spec.ofZ m) (Exact.bpow ctx beta e1)) := by
      rw [← hdecomp]
      exact h
    have hpos' : Exact.Rlt ctx (Exact.IZR ctx Z0) (Exact.bpow ctx beta e1) := by
      change ctx.spec.lt (ctx.spec.ofZ Z0) (Exact.bpow ctx beta e1)
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta e1
    have hd_lt_m : ctx.spec.lt (Exact.bpow ctx beta d) (ctx.spec.ofZ m) :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_reg_r
        ctx (Exact.bpow ctx beta e1) (Exact.bpow ctx beta d) (ctx.spec.ofZ m)
        hpos' h'
    have hp := CompCert4Lean.Flocq.Core.Raux.IZR_Zpower ctx beta d hd
    have hp' : ctx.spec.ofZ (Zpower (beta : Z) d) =
        Exact.bpow ctx beta d := by
      change ctx.spec.ofZ (Zpower (beta : Z) d) = Exact.bpow ctx beta d
      exact hp
    have hpow_lt : ctx.spec.lt (ctx.spec.ofZ (Zpower (beta : Z) d))
        (ctx.spec.ofZ m) := by
      rw [hp']
      exact hd_lt_m
    have hpow_int := fp_ofZ_lt_of_real_lt ctx hpow_lt
    have hpow_le : Zle (Zpower (beta : Z) d) (Zsub m Zone) := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Zpower (beta : Z) d) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub m Zone)
      simp only [Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Zpower (beta : Z) d) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m - 1
      omega
    have hpow_le' : ctx.spec.le (Exact.bpow ctx beta d)
        (ctx.spec.ofZ (Zsub m Zone)) := by
      rw [← hp']
      exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_le
        ctx _ _ hpow_le
    change ctx.spec.le (Exact.bpow ctx beta e2)
      (ctx.spec.mul (ctx.spec.ofZ (Zsub m Zone))
        (Exact.bpow ctx beta e1))
    rw [hdecomp]
    have hnonneg : ctx.spec.le (ctx.spec.ofZ Z0)
        (Exact.bpow ctx beta e1) := by
      change ctx.spec.le (ctx.spec.ofZ Z0) (Exact.bpow ctx beta e1)
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
        (CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta e1) |>.1
    exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
      ctx (Exact.bpow ctx beta e1) (Exact.bpow ctx beta d)
        (ctx.spec.ofZ (Zsub m Zone))
      hnonneg hpow_le'
  · have h21 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 := by omega
    have hpow : Exact.Rle ctx (Exact.bpow ctx beta e2)
        (Exact.bpow ctx beta e1) := by
      exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le
        ctx _ _ (fp_bpow_lt ctx beta h21)
    have hbase := bpow_le_F2R ctx beta (Zsub m Zone) e1 hmpos
    exact ctx.certificate.orderedField.le_trans _ _ _ hpow hbase

theorem F2R_p1_le_bpow : ∀ (ctx : ExactRealContext), F2R_p1_le_bpowStatement ctx := by
  intro ctx beta m e1 e2 hm h
  have hbase := bpow_le_F2R ctx beta m e1 hm
  have hltpow : Exact.Rlt ctx (Exact.bpow ctx beta e1) (Exact.bpow ctx beta e2) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
      ctx (Exact.bpow ctx beta e1) (Exact.F2R ctx (Float beta m e1))
      (Exact.bpow ctx beta e2) hbase h
  have he12 : Zle e1 e2 := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2
    have hnot : ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 := by
      intro h21
      have hp := fp_bpow_lt ctx beta (show Zlt e2 e1 by exact h21)
      exact (ctx.certificate.orderedField.lt_irrefl _
        (ctx.certificate.orderedField.lt_trans _ _ _ hp hltpow)).elim
    omega
  let d := Zsub e2 e1
  have hd_nonneg : Zle Z0 d := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d
    simp only [d, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change (0 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 -
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 at he12
    omega
  have hsum : Zadd e1 d = e2 := by exact fp_zadd_sub_cancel' e1 e2
  have hbdecomp : Exact.bpow ctx beta e2 =
      ctx.spec.mul (Exact.bpow ctx beta d) (Exact.bpow ctx beta e1) := by
    rw [← hsum]
    have hbp := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta e1 d
    change Exact.bpow ctx beta (Zadd e1 d) =
      ctx.spec.mul (Exact.bpow ctx beta e1) (Exact.bpow ctx beta d) at hbp
    calc
      Exact.bpow ctx beta (Zadd e1 d) =
          ctx.spec.mul (Exact.bpow ctx beta e1) (Exact.bpow ctx beta d) := hbp
      _ = ctx.spec.mul (Exact.bpow ctx beta d) (Exact.bpow ctx beta e1) :=
        ctx.certificate.orderedField.mul_comm _ _
  have hcancel : ctx.spec.lt (ctx.spec.ofZ m) (Exact.bpow ctx beta d) := by
    change ctx.spec.lt (ctx.spec.mul (ctx.spec.ofZ m) (Exact.bpow ctx beta e1))
      (Exact.bpow ctx beta e2) at h
    rw [hbdecomp] at h
    have hpos' : Exact.Rlt ctx (Exact.IZR ctx Z0) (Exact.bpow ctx beta e1) := by
      change ctx.spec.lt (ctx.spec.ofZ Z0) (Exact.bpow ctx beta e1)
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta e1
    exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_reg_r
      ctx (Exact.bpow ctx beta e1) (ctx.spec.ofZ m) (Exact.bpow ctx beta d)
      hpos' h
  change ctx.spec.le (ctx.spec.mul (ctx.spec.ofZ (Zadd m Zone)) (Exact.bpow ctx beta e1))
    (Exact.bpow ctx beta e2)
  rw [hbdecomp]
  apply CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
    ctx (Exact.bpow ctx beta e1) (ctx.spec.ofZ (Zadd m Zone))
      (Exact.bpow ctx beta d)
  · have hnonneg : Exact.Rle ctx (Exact.IZR ctx Z0)
        (Exact.bpow ctx beta e1) := by
      change ctx.spec.le (ctx.spec.ofZ Z0) (Exact.bpow ctx beta e1)
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
        (CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta e1) |>.1
    exact hnonneg
  have hp := CompCert4Lean.Flocq.Core.Raux.IZR_Zpower ctx beta d hd_nonneg
  have hp' : Exact.bpow ctx beta d = ctx.spec.ofZ (Zpower (beta : Z) d) := by
    change Exact.bpow ctx beta d = ctx.spec.ofZ (Zpower (beta : Z) d)
    exact hp.symm
  change ctx.spec.le (ctx.spec.ofZ (Zadd m Zone)) (Exact.bpow ctx beta d)
  rw [hp']
  apply CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_le ctx
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd m Zone) ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpower (beta : Z) d)
  simp only [Zadd,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m + 1 ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpower (beta : Z) d)
  have hcancel' : ctx.spec.lt (ctx.spec.ofZ m)
      (ctx.spec.ofZ (Zpower (beta : Z) d)) := by
    rw [← hp']
    exact hcancel
  have hmi : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpower (beta : Z) d) := by
    by_cases hlt : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpower (beta : Z) d)
    · exact hlt
    · have hle : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Zpower (beta : Z) d) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m := by omega
      rcases Int.lt_or_eq_of_le hle with hrev | heq
      · have hcontra := fp2_ofZ_lt ctx hrev
        exact (ctx.certificate.orderedField.lt_irrefl _
          (ctx.certificate.orderedField.lt_trans _ _ _ hcontra hcancel')).elim
      · have heq' : m = Zpower (beta : Z) d := by
          apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
          exact heq.symm
        subst m
        exact (ctx.certificate.orderedField.lt_irrefl _ hcancel').elim
  omega

end CompCert4Lean.Flocq.Core.Float_prop

namespace CompCert4Lean.Flocq.Core.Float_prop

private theorem pg_fp_zadd_sub_cancel (a b : Z) :
    Zadd (Zsub b a) a = b := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

private theorem pg_fp_zadd_sub_cancel' (a b : Z) :
    Zadd a (Zsub b a) = b := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

private theorem pg_fp_int_pow_gt_one (a : Int) (ha : (2 : Int) ≤ a) :
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
            have hmul' : (1 : Int) * a ≤ a ^ k * a := by simpa using hmul
            have hmul'' : a ≤ a ^ k * a := by simpa only [Int.one_mul] using hmul'
            exact Int.le_trans haone hmul''
      have hpow_one : (1 : Int) ≤ a ^ n := hpow_one_all n
      rw [Int.pow_succ]
      have hmul := Int.mul_le_mul_of_nonneg_right hpow_one (Int.le_of_lt hapos)
      have haone : (1 : Int) < a := by omega
      have hmul' : (1 : Int) * a ≤ a ^ n * a := by simpa using hmul
      have hmul'' : a ≤ a ^ n * a := by simpa using hmul'
      exact Int.lt_of_lt_of_le haone hmul''

private theorem pg_fp_bpow_gt_one (ctx : ExactRealContext) (r : radix)
    {e : Z} (he : Zlt Z0 e) :
    ctx.spec.lt ctx.spec.one (Exact.bpow ctx r e) := by
  cases e with
  | Z0 => change (0 : Int) < 0 at he; omega
  | Zneg p =>
      change (0 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg p) at he
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at he
      omega
  | Zpos p =>
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hr : (2 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val := by
        have h := r.radix_prop
        change (if (2 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val then true else false) = true at h
        simpa using h
      have hpow : (1 : Int) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower_pos r.radix_val p) := by
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower_pos,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow_pos,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        exact pg_fp_int_pow_gt_one _ hr _ hp
      have h := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt
        ctx Zone (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower_pos r.radix_val p)
        hpow
      change ctx.spec.lt (ctx.spec.ofZ Zone)
        (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower_pos r.radix_val p)) at h
      rw [ctx.certificate.sourceLaws.ofZ_one] at h
      exact h

private theorem pg_fp_bpow_lt (ctx : ExactRealContext) (r : radix)
    {e1 e2 : Z} (h : Zlt e1 e2) :
    Exact.Rlt ctx (Exact.bpow ctx r e1) (Exact.bpow ctx r e2) := by
  let d := Zsub e2 e1
  have hd : Zlt Z0 d := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d
    simp only [d, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 -
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 at h
    omega
  have hsum : Zadd e1 d = e2 := pg_fp_zadd_sub_cancel' e1 e2
  have hmul : Exact.bpow ctx r e2 =
      ctx.spec.mul (Exact.bpow ctx r e1) (Exact.bpow ctx r d) := by
    rw [← hsum]
    exact CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx r e1 d
  have hpos := CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx r e1
  have hone := pg_fp_bpow_gt_one ctx r hd
  have hpos' : Exact.Rlt ctx (Exact.IZR ctx Z0) (Exact.bpow ctx r e1) := by
    change ctx.spec.lt (ctx.spec.ofZ Z0) (Exact.bpow ctx r e1)
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hpos
  have hmul' :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_compat_r
      ctx (Exact.bpow ctx r e1) (ctx.spec.one) (Exact.bpow ctx r d) hpos' hone
  change ctx.spec.lt (ctx.spec.mul ctx.spec.one (Exact.bpow ctx r e1))
    (ctx.spec.mul (Exact.bpow ctx r d) (Exact.bpow ctx r e1)) at hmul'
  rw [ctx.certificate.orderedField.mul_comm ctx.spec.one _,
    ctx.certificate.orderedField.mul_one,
    ctx.certificate.orderedField.mul_comm _ (Exact.bpow ctx r e1)] at hmul'
  rw [← hmul] at hmul'
  exact hmul'

private theorem pg_float_prop_bpow_le (ctx : ExactRealContext) (r : radix)
    {e1 e2 : Z} (h : Zle e1 e2) :
    ctx.spec.le (Exact.bpow ctx r e1) (Exact.bpow ctx r e2) := by
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 at h
  rcases Int.lt_or_eq_of_le h with hlt | heq
  · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
      (pg_fp_bpow_lt ctx r (show Zlt e1 e2 by exact hlt)) |>.1
  · have heq' : e1 = e2 := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      exact heq
    subst e2
    exact ctx.certificate.orderedField.le_refl _

private theorem pg_digits_correct :
    CompCert4Lean.Flocq.Core.Digits.Zdigits_correctStatement := by
  intro beta n
  let d := Zdigits beta n
  constructor
  · apply CompCert4Lean.Flocq.Core.Digits.Zpower_le_Zdigits
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub d Zone) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d
    simp only [Zsub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d - 1 <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d
    omega
  · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zabs n) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpower (beta : Z) d)
    by_cases hlt : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zabs n) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpower (beta : Z) d)
    · exact hlt
    · have hle : Zle (Zpower (beta : Z) d) (Zabs n) := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zpower (beta : Z) d) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zabs n)
        exact Int.le_of_not_gt hlt
      have hd := CompCert4Lean.Flocq.Core.Digits.Zdigits_gt_Zpower beta d n hle
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d at hd
      exact (Int.lt_irrefl _ hd).elim

private theorem pg_zabs_zero : Zabs (Z0 : Z) = Z0 := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  rfl

private theorem pg_zabs_pos (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) :
    Zabs (.Zpos p) = (.Zpos p : Z) := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs (.Zpos p)) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (.Zpos p)
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]

private theorem pg_zabs_neg (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) :
    Zabs (.Zneg p) = (.Zpos p : Z) := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs (.Zneg p)) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (.Zpos p)
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]

private theorem pg_abs_IZR (ctx : ExactRealContext) (n : Z) :
    Exact.IZR ctx (Zabs n) = Exact.Rabs ctx (Exact.IZR ctx n) := by
  cases n with
  | Z0 =>
      rw [pg_zabs_zero]
      dsimp [Exact.IZR, Exact.Rabs]
      unfold CompCert4Lean.Flocq.Core.Raux.Exact.IZR
        CompCert4Lean.Flocq.Core.Raux.Exact.Rabs
      unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR
        CompCert4Lean.Foundation.FlocqReal.ExactReal.Rabs
      change ctx.spec.ofZ Z0 = ctx.spec.abs (ctx.spec.ofZ Z0)
      rw [ctx.certificate.sourceLaws.ofZ_zero,
        ctx.certificate.sourceLaws.abs_nonnegative]
      exact ctx.certificate.orderedField.le_refl _
  | Zpos p =>
      rw [pg_zabs_pos]
      dsimp [Exact.IZR, Exact.Rabs]
      unfold CompCert4Lean.Flocq.Core.Raux.Exact.IZR
        CompCert4Lean.Flocq.Core.Raux.Exact.Rabs
      unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR
        CompCert4Lean.Foundation.FlocqReal.ExactReal.Rabs
      change ctx.spec.ofZ (.Zpos p) = ctx.spec.abs (ctx.spec.ofZ (.Zpos p))
      rw [ctx.certificate.sourceLaws.abs_nonnegative]
      have hppos := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpint : (0 : Int) ≤ Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_nonneg _
      have hp := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_le
        ctx Z0 (.Zpos p) hpint
      change ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.ofZ (.Zpos p)) at hp
      rw [ctx.certificate.sourceLaws.ofZ_zero] at hp
      exact hp
  | Zneg p =>
      rw [pg_zabs_neg]
      dsimp [Exact.IZR, Exact.Rabs]
      unfold CompCert4Lean.Flocq.Core.Raux.Exact.IZR
        CompCert4Lean.Flocq.Core.Raux.Exact.Rabs
      unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR
        CompCert4Lean.Foundation.FlocqReal.ExactReal.Rabs
      change ctx.spec.ofZ (.Zpos p) = ctx.spec.abs (ctx.spec.ofZ (.Zneg p))
      have hppos := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpint : (-Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) : Int) < 0 := by
        have hpos : (0 : Int) < Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
          Int.natCast_pos.mpr hppos
        omega
      have hn := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt
        ctx (.Zneg p) Z0 hpint
      change ctx.spec.lt (ctx.spec.ofZ (.Zneg p)) (ctx.spec.ofZ Z0) at hn
      rw [ctx.certificate.sourceLaws.ofZ_zero] at hn
      rw [ctx.certificate.sourceLaws.abs_negative _ hn]
      have hneg := ctx.certificate.sourceLaws.ofZ_neg (.Zpos p)
      have hopp : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
          (.Zpos p) = (.Zneg p) := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
        rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
      rw [hopp] at hneg
      rw [hneg]
      have hnn : ∀ y : ctx.spec.carrier, ctx.spec.neg (ctx.spec.neg y) = y := by
        intro y
        calc
          ctx.spec.neg (ctx.spec.neg y) =
              ctx.spec.add (ctx.spec.neg (ctx.spec.neg y)) ctx.spec.zero :=
            (ctx.certificate.orderedField.add_zero _).symm
          _ = ctx.spec.add (ctx.spec.neg (ctx.spec.neg y))
              (ctx.spec.add (ctx.spec.neg y) y) := by
            rw [ctx.certificate.orderedField.neg_add_cancel]
          _ = ctx.spec.add
              (ctx.spec.add (ctx.spec.neg (ctx.spec.neg y)) (ctx.spec.neg y)) y := by
            rw [ctx.certificate.orderedField.add_assoc]
          _ = ctx.spec.add ctx.spec.zero y := by
            rw [ctx.certificate.orderedField.neg_add_cancel]
          _ = y := ctx.certificate.orderedField.zero_add _
      exact (hnn _).symm

private theorem pg_IZR_ne_zero (ctx : ExactRealContext) {n : Z} (hn : n ≠ Z0) :
    Exact.IZR ctx n ≠ Exact.R0 ctx := by
  cases n with
  | Z0 => exact (hn rfl).elim
  | Zpos p =>
      intro hz
      have hppos := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpint : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr hppos
      have hp := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt
        ctx Z0 (.Zpos p) hpint
      change ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.ofZ (.Zpos p)) at hp
      have hz' : ctx.spec.ofZ (.Zpos p) = ctx.spec.zero := by exact hz
      rw [ctx.certificate.sourceLaws.ofZ_zero, hz'] at hp
      exact (ctx.certificate.orderedField.lt_irrefl _ hp).elim

  | Zneg p =>
      intro hz
      have hppos := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpint : (-Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) : Int) < 0 := by
        have hpos : (0 : Int) < Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
          Int.natCast_pos.mpr hppos
        omega
      have hp := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt
        ctx (.Zneg p) Z0 hpint
      change ctx.spec.lt (ctx.spec.ofZ (.Zneg p)) (ctx.spec.ofZ Z0) at hp
      have hz' : ctx.spec.ofZ (.Zneg p) = ctx.spec.zero := by exact hz
      rw [ctx.certificate.sourceLaws.ofZ_zero, hz'] at hp
      exact (ctx.certificate.orderedField.lt_irrefl _ hp).elim

private theorem pg_digits_mag_unique (ctx : ExactRealContext) (r : radix)
    (x : Exact.R ctx) {e1 e2 : Z}
    (h1 : ctx.spec.le (Exact.bpow ctx r (Zsub e1 Zone)) (ctx.spec.abs x) ∧
      ctx.spec.lt (ctx.spec.abs x) (Exact.bpow ctx r e1))
    (h2 : ctx.spec.le (Exact.bpow ctx r (Zsub e2 Zone)) (ctx.spec.abs x) ∧
      ctx.spec.lt (ctx.spec.abs x) (Exact.bpow ctx r e2)) : e1 = e2 := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  by_cases hEq : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2
  · exact hEq
  · rcases Int.lt_or_gt_of_ne hEq with h12 | h21
    · have hleexp : Zle e1 (Zsub e2 Zone) := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub e2 Zone)
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 - 1
        omega
      have hp := pg_float_prop_bpow_le ctx r hleexp
      have hmid :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
          ctx _ _ _ h2.1 h1.2
      have hnot := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hmid |>.2
      exact (hnot hp).elim
    · have hleexp : Zle e2 (Zsub e1 Zone) := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub e1 Zone)
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 - 1
        omega
      have hp := pg_float_prop_bpow_le ctx r hleexp
      have hmid :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
          ctx _ _ _ h1.1 h2.2
      have hnot := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hmid |>.2
      exact (hnot hp).elim
theorem Zdigits_mag : ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
    Zdigits_magStatement ctx magnitude := by
  intro ctx magnitude beta n hn
  let d := Zdigits beta n
  have hc := pg_digits_correct beta n
  have hdpos := CompCert4Lean.Flocq.Core.Digits.Zdigits_gt_0 beta n hn
  have hdzero : Zle Z0 d := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zdigits beta n) at hdpos
    exact Int.le_of_lt hdpos
  have hds : Zle Z0 (Zsub d Zone) := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub d Zone)
    simp only [Zsub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change (0 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d - 1
    change (0 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d at hdpos
    omega
  have hpl := CompCert4Lean.Flocq.Core.Raux.IZR_Zpower ctx beta (Zsub d Zone) hds
  have hpu := CompCert4Lean.Flocq.Core.Raux.IZR_Zpower ctx beta d hdzero
  change ctx.spec.ofZ (Zpower (beta : Z) (Zsub d Zone)) =
      Exact.bpow ctx beta (Zsub d Zone) at hpl
  change ctx.spec.ofZ (Zpower (beta : Z) d) =
      Exact.bpow ctx beta d at hpu
  have hlow := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_le
    ctx (Zpower (beta : Z) (Zsub d Zone)) (Zabs n) hc.1
  have hupp := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt
    ctx (Zabs n) (Zpower (beta : Z) d) hc.2
  change ctx.spec.le (ctx.spec.ofZ (Zpower (beta : Z) (Zsub d Zone)))
      (ctx.spec.ofZ (Zabs n)) at hlow
  change ctx.spec.lt (ctx.spec.ofZ (Zabs n))
      (ctx.spec.ofZ (Zpower (beta : Z) d)) at hupp
  rw [hpl] at hlow
  rw [hpu] at hupp
  have habs := pg_abs_IZR ctx n
  change ctx.spec.ofZ (Zabs n) = ctx.spec.abs (ctx.spec.ofZ n) at habs
  rw [habs] at hlow hupp
  let mv := CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta (Exact.IZR ctx n)
  have hmv := mv.mag_bound (pg_IZR_ne_zero ctx hn)
  change ctx.spec.le (Exact.bpow ctx beta (Zsub mv.mag_val Zone))
      (ctx.spec.abs (Exact.IZR ctx n)) ∧
    ctx.spec.lt (ctx.spec.abs (Exact.IZR ctx n)) (Exact.bpow ctx beta mv.mag_val) at hmv
  have heq := pg_digits_mag_unique ctx beta (Exact.IZR ctx n) hmv
    (show ctx.spec.le (Exact.bpow ctx beta (Zsub d Zone))
        (ctx.spec.abs (Exact.IZR ctx n)) ∧
      ctx.spec.lt (ctx.spec.abs (Exact.IZR ctx n)) (Exact.bpow ctx beta d) from
      ⟨hlow, hupp⟩)
  change mv.mag_val = d at heq
  change Zdigits beta n =
    (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta
      (Exact.IZR ctx n)).mag_val
  exact heq.symm

private theorem pg_mul_neg_right (ctx : ExactRealContext)
    (x y : ctx.spec.carrier) :
    ctx.spec.mul x (ctx.spec.neg y) = ctx.spec.neg (ctx.spec.mul x y) := by
  have h : ctx.spec.add (ctx.spec.mul x (ctx.spec.neg y))
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
    _ = ctx.spec.mul x (ctx.spec.neg y) := ctx.certificate.orderedField.zero_add _

private theorem pg_abs_mul_pos (ctx : ExactRealContext) {x z : ctx.spec.carrier}
    (hz : ctx.spec.lt ctx.spec.zero z) :
    ctx.spec.abs (ctx.spec.mul x z) = ctx.spec.mul (ctx.spec.abs x) z := by
  rcases ctx.certificate.total_order x ctx.spec.zero with hx | hx
  · rcases hx with hneg | hzero
    · have hprod := ctx.certificate.orderedField.mul_lt_compat_l z x
        ctx.spec.zero hz hneg
      rw [ctx.certificate.orderedField.mul_zero,
        ctx.certificate.orderedField.mul_comm z x] at hprod
      rw [ctx.certificate.sourceLaws.abs_negative _ hprod,
        ctx.certificate.sourceLaws.abs_negative x hneg]
      have hmul := pg_mul_neg_right ctx z x
      calc
        ctx.spec.neg (ctx.spec.mul x z) =
            ctx.spec.neg (ctx.spec.mul z x) := by
              rw [ctx.certificate.orderedField.mul_comm x z]
        _ = ctx.spec.mul z (ctx.spec.neg x) := hmul.symm
        _ = ctx.spec.mul (ctx.spec.neg x) z :=
              ctx.certificate.orderedField.mul_comm _ _
    · subst x
      have hzeroabs : ctx.spec.abs ctx.spec.zero = ctx.spec.zero :=
        ctx.certificate.sourceLaws.abs_nonnegative _
          (ctx.certificate.orderedField.le_refl _)
      rw [ctx.certificate.orderedField.zero_mul, hzeroabs,
        ctx.certificate.orderedField.zero_mul]
  · have hxle : ctx.spec.le ctx.spec.zero x :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hx |>.1
    have hprodlt : ctx.spec.lt ctx.spec.zero (ctx.spec.mul x z) := by
      have hmul := ctx.certificate.orderedField.mul_lt_compat_l z
        ctx.spec.zero x hz hx
      rw [ctx.certificate.orderedField.mul_zero,
        ctx.certificate.orderedField.mul_comm z x] at hmul
      exact hmul
    rw [ctx.certificate.sourceLaws.abs_nonnegative _
          ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hprodlt).1,
      ctx.certificate.sourceLaws.abs_nonnegative _ hxle]

private theorem pg_zsub_add_zone (a e : Z) :
    Zsub (Zadd a e) Zone = Zadd (Zsub a Zone) e := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

private theorem pg_mag_mult_bpow (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) (beta : radix)
    (x : Exact.R ctx) (e : Z) (hx : x ≠ Exact.R0 ctx) :
    (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta
      (ctx.spec.mul x (Exact.bpow ctx beta e))).mag_val =
      Zadd (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_val e := by
  let mv := CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x
  have hmv := mv.mag_bound hx
  change ctx.spec.le (Exact.bpow ctx beta (Zsub mv.mag_val Zone))
      (ctx.spec.abs x) ∧
    ctx.spec.lt (ctx.spec.abs x) (Exact.bpow ctx beta mv.mag_val) at hmv
  have hz := CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta e
  have hzle : ctx.spec.le ctx.spec.zero (Exact.bpow ctx beta e) :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hz |>.1
  have hmulabs := pg_abs_mul_pos ctx (x := x)
    (z := Exact.bpow ctx beta e) hz
  let y := ctx.spec.mul x (Exact.bpow ctx beta e)
  have hlowmul : ctx.spec.le
      (ctx.spec.mul (Exact.bpow ctx beta (Zsub mv.mag_val Zone))
        (Exact.bpow ctx beta e))
      (ctx.spec.mul (ctx.spec.abs x) (Exact.bpow ctx beta e)) := by
    have hzle' : CompCert4Lean.Flocq.Core.Raux.Exact.Rle ctx
        (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx Z0)
        (Exact.bpow ctx beta e) := by
      change ctx.spec.le (ctx.spec.ofZ Z0) (Exact.bpow ctx beta e)
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact hzle
    have hlowmul' :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
        ctx (Exact.bpow ctx beta e)
        (Exact.bpow ctx beta (Zsub mv.mag_val Zone)) (ctx.spec.abs x)
        hzle' hmv.1
    change ctx.spec.le
      (ctx.spec.mul (Exact.bpow ctx beta (Zsub mv.mag_val Zone))
        (Exact.bpow ctx beta e))
      (ctx.spec.mul (ctx.spec.abs x) (Exact.bpow ctx beta e)) at hlowmul'
    exact hlowmul'
  have huppmul : ctx.spec.lt
      (ctx.spec.mul (ctx.spec.abs x) (Exact.bpow ctx beta e))
      (ctx.spec.mul (Exact.bpow ctx beta mv.mag_val)
        (Exact.bpow ctx beta e)) := by
    have hz' : CompCert4Lean.Flocq.Core.Raux.Exact.Rlt ctx
        (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx Z0)
        (Exact.bpow ctx beta e) := by
      change ctx.spec.lt (ctx.spec.ofZ Z0) (Exact.bpow ctx beta e)
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact hz
    have hlt :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_compat_r
        ctx (Exact.bpow ctx beta e) (ctx.spec.abs x)
        (Exact.bpow ctx beta mv.mag_val) hz' hmv.2
    change ctx.spec.lt
      (ctx.spec.mul (ctx.spec.abs x) (Exact.bpow ctx beta e))
      (ctx.spec.mul (Exact.bpow ctx beta mv.mag_val)
        (Exact.bpow ctx beta e)) at hlt
    exact hlt
  have hlowpow := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta
      (Zsub mv.mag_val Zone) e
  have huppow := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta mv.mag_val e
  have hlowpow' : Exact.bpow ctx beta (Zadd (Zsub mv.mag_val Zone) e) =
      ctx.spec.mul (Exact.bpow ctx beta (Zsub mv.mag_val Zone))
        (Exact.bpow ctx beta e) := by
    change Exact.bpow ctx beta (Zadd (Zsub mv.mag_val Zone) e) =
      ctx.spec.mul (Exact.bpow ctx beta (Zsub mv.mag_val Zone))
        (Exact.bpow ctx beta e)
    exact hlowpow
  have huppow' : Exact.bpow ctx beta (Zadd mv.mag_val e) =
      ctx.spec.mul (Exact.bpow ctx beta mv.mag_val)
        (Exact.bpow ctx beta e) := by
    change Exact.bpow ctx beta (Zadd mv.mag_val e) =
      ctx.spec.mul (Exact.bpow ctx beta mv.mag_val)
        (Exact.bpow ctx beta e)
    exact huppow
  have hlowexp := pg_zsub_add_zone mv.mag_val e
  have hlow : ctx.spec.le
      (Exact.bpow ctx beta (Zsub (Zadd mv.mag_val e) Zone))
      (ctx.spec.abs y) := by
    rw [hlowexp]
    change ctx.spec.le
      (Exact.bpow ctx beta (Zadd (Zsub mv.mag_val Zone) e))
      (ctx.spec.abs (ctx.spec.mul x (Exact.bpow ctx beta e)))
    rw [hmulabs]
    rw [hlowpow']
    exact hlowmul
  have hupp : ctx.spec.lt (ctx.spec.abs y)
      (Exact.bpow ctx beta (Zadd mv.mag_val e)) := by
    change ctx.spec.lt
      (ctx.spec.abs (ctx.spec.mul x (Exact.bpow ctx beta e)))
      (Exact.bpow ctx beta (Zadd mv.mag_val e))
    rw [hmulabs]
    rw [huppow']
    exact huppmul
  have hyx : y ≠ Exact.R0 ctx := by
    intro hy
    have hzne : Exact.bpow ctx beta e ≠ ctx.spec.zero := by
      intro hz0
      have hz' : ctx.spec.lt ctx.spec.zero (Exact.bpow ctx beta e) := by
        exact hz
      rw [hz0] at hz'
      exact (ctx.certificate.orderedField.lt_irrefl _ hz').elim
    have hzinv : ctx.spec.mul (Exact.bpow ctx beta e)
        (ctx.spec.inv (Exact.bpow ctx beta e)) = ctx.spec.one := by
      rw [ctx.certificate.orderedField.mul_comm]
      exact ctx.certificate.orderedField.inv_mul_cancel _ hzne
    have hmul := congrArg (fun t =>
      ctx.spec.mul t (ctx.spec.inv (Exact.bpow ctx beta e))) hy
    change ctx.spec.mul y (ctx.spec.inv (Exact.bpow ctx beta e)) =
      ctx.spec.mul (ctx.spec.zero) (ctx.spec.inv (Exact.bpow ctx beta e)) at hmul
    rw [show y = ctx.spec.mul x (Exact.bpow ctx beta e) by rfl,
      ctx.certificate.orderedField.mul_assoc, hzinv,
      ctx.certificate.orderedField.mul_one,
      ctx.certificate.orderedField.zero_mul] at hmul
    exact hx hmul
  have hmy := (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta y).mag_bound hyx
  change ctx.spec.le _ (ctx.spec.abs y) ∧ ctx.spec.lt (ctx.spec.abs y) _ at hmy
  have heq := pg_digits_mag_unique ctx beta y hmy ⟨hlow, hupp⟩
  exact heq

private theorem pg_float_prop_mag_unique (ctx : ExactRealContext) (r : radix)
    (x : Exact.R ctx) {e1 e2 : Z}
    (h1 : ctx.spec.le (Exact.bpow ctx r (Zsub e1 Zone)) (ctx.spec.abs x) ∧
      ctx.spec.lt (ctx.spec.abs x) (Exact.bpow ctx r e1))
    (h2 : ctx.spec.le (Exact.bpow ctx r (Zsub e2 Zone)) (ctx.spec.abs x) ∧
      ctx.spec.lt (ctx.spec.abs x) (Exact.bpow ctx r e2)) : e1 = e2 := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  by_cases hEq : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2
  · exact hEq
  · rcases Int.lt_or_gt_of_ne hEq with h12 | h21
    · have hleexp : Zle e1 (Zsub e2 Zone) := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub e2 Zone)
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 - 1
        omega
      have hp := pg_float_prop_bpow_le ctx r hleexp
      have hmid :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
          ctx _ _ _ h2.1 h1.2
      have hnot := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hmid |>.2
      exact (hnot hp).elim
    · have hleexp : Zle e2 (Zsub e1 Zone) := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub e1 Zone)
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 - 1
        omega
      have hp := pg_float_prop_bpow_le ctx r hleexp
      have hmid :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
          ctx _ _ _ h1.1 h2.2
      have hnot := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hmid |>.2
      exact (hnot hp).elim

theorem mag_F2R_bounds : ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
    mag_F2R_boundsStatement ctx magnitude := by
  intro ctx magnitude beta x m e hm hbounds
  change ctx.spec.le (Exact.F2R ctx (Float beta m e)) x ∧
      ctx.spec.lt x (Exact.F2R ctx (Float beta (Zadd m Zone) e)) at hbounds
  let f := Exact.F2R ctx (Float beta m e)
  change ctx.spec.le f x ∧
      ctx.spec.lt x (Exact.F2R ctx (Float beta (Zadd m Zone) e)) at hbounds
  have hfne : f ≠ Exact.R0 ctx := by
    intro hz
    have hpos := F2R_gt_0 ctx beta (Float beta m e) hm
    have hz' : Exact.F2R ctx (Float beta m e) = Exact.R0 ctx := by
      simpa [f] using hz
    rw [hz'] at hpos
    exact (ctx.certificate.orderedField.lt_irrefl _ hpos).elim
  let mf := CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta f
  have hfm := mf.mag_bound hfne
  change ctx.spec.le (Exact.bpow ctx beta (Zsub mf.mag_val Zone))
      (ctx.spec.abs f) ∧
    ctx.spec.lt (ctx.spec.abs f) (Exact.bpow ctx beta mf.mag_val) at hfm
  have hxne : x ≠ Exact.R0 ctx := by
    intro hz
    rw [hz] at hbounds
    have hpos := F2R_gt_0 ctx beta (Float beta m e) hm
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hpos).2 hbounds.1
  have hfpos : Exact.Rlt ctx (Exact.R0 ctx) f := by
    exact F2R_gt_0 ctx beta (Float beta m e) hm
  have hxpos : Exact.Rlt ctx (Exact.R0 ctx) x :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
      ctx _ _ _ hfpos hbounds.1
  have hfabs : Exact.Rabs ctx f = f := by
    change ctx.spec.abs f = f
    exact ctx.certificate.sourceLaws.abs_nonnegative f
      ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hfpos).1
  have hfabs' : ctx.spec.abs f = f := by exact hfabs
  have hxabs : Exact.Rabs ctx x = x := by
    change ctx.spec.abs x = x
    exact ctx.certificate.sourceLaws.abs_nonnegative x
      ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxpos).1
  have hxabs' : ctx.spec.abs x = x := by exact hxabs
  have hfm_upper : ctx.spec.lt f (Exact.bpow ctx beta mf.mag_val) := by
    have hh : ctx.spec.lt (Exact.Rabs ctx f)
        (Exact.bpow ctx beta mf.mag_val) := hfm.2
    rw [hfabs] at hh
    exact hh
  have hupper := F2R_p1_le_bpow ctx beta m e mf.mag_val hm hfm_upper
  have hupper' : ctx.spec.lt x
      (Exact.bpow ctx beta mf.mag_val) := by
    exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
      ctx _ _ _ hbounds.2 hupper
  have hxf : ctx.spec.le
      (Exact.bpow ctx beta (Zsub mf.mag_val Zone)) (ctx.spec.abs x) ∧
      ctx.spec.lt (ctx.spec.abs x) (Exact.bpow ctx beta mf.mag_val) := by
    have hxm' : ctx.spec.le
        (Exact.bpow ctx beta (Zsub mf.mag_val Zone)) x := by
      have hfm1 : ctx.spec.le (Exact.bpow ctx beta (Zsub mf.mag_val Zone)) f := by
        exact Eq.mp (congrArg (fun y : ctx.spec.carrier =>
          ctx.spec.le (Exact.bpow ctx beta (Zsub mf.mag_val Zone)) y) hfabs') hfm.1
      exact ctx.certificate.orderedField.le_trans _ _ _ hfm1
        hbounds.1
    have hxm_abs : ctx.spec.le
        (Exact.bpow ctx beta (Zsub mf.mag_val Zone)) (ctx.spec.abs x) := by
      exact Eq.mpr (congrArg (fun y : ctx.spec.carrier =>
        ctx.spec.le (Exact.bpow ctx beta (Zsub mf.mag_val Zone)) y) hxabs') hxm'
    have hupper_abs : ctx.spec.lt (ctx.spec.abs x)
        (Exact.bpow ctx beta mf.mag_val) := by
      exact Eq.mpr (congrArg (fun y : ctx.spec.carrier =>
        ctx.spec.lt y (Exact.bpow ctx beta mf.mag_val)) hxabs') hupper'
    exact And.intro hxm_abs hupper_abs
  have hxm := (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_bound hxne
  change ctx.spec.le _ (ctx.spec.abs x) ∧ ctx.spec.lt (ctx.spec.abs x) _ at hxm
  have heq := pg_float_prop_mag_unique ctx beta x hxm hxf
  change (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_val = mf.mag_val at heq
  simpa [f, mf] using heq

end CompCert4Lean.Flocq.Core.Float_prop

namespace CompCert4Lean.Flocq.Core.Float_prop

theorem mag_F2R_bounds_Zdigits : ∀ (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx),
    mag_F2R_bounds_ZdigitsStatement ctx magnitude := by
  intro ctx magnitude beta x m e hm hbounds
  have hmne : m ≠ Z0 := by
    intro hm0
    subst m
    change (0 : Int) < 0 at hm
    omega
  have hbound := mag_F2R_bounds ctx magnitude beta x m e hm hbounds
  calc
    Exact.mag magnitude beta x =
        Exact.mag magnitude beta (Exact.F2R ctx (Float beta m e)) := hbound
    _ = Zadd (Zdigits beta m) e := by
      change (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta
        (ctx.spec.mul (ctx.spec.ofZ m) (Exact.bpow ctx beta e))).mag_val = _
      rw [pg_mag_mult_bpow ctx magnitude beta (ctx.spec.ofZ m) e
        (pg_IZR_ne_zero ctx hmne)]
      have hd := Zdigits_mag ctx magnitude beta m hmne
      change Zdigits beta m =
        (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta
          (Exact.IZR ctx m)).mag_val at hd
      exact congrArg (fun d => Zadd d e) hd.symm

end CompCert4Lean.Flocq.Core.Float_prop
