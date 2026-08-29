import CompCert4Lean.Flocq.Core.Generic_fmt
import CompCert4Lean.Flocq.Core.FLX
import CompCert4Lean.Flocq.Core.Ulp

/-!
# Floating-point format with gradual underflow

This module contains the selected definition surface from `Flocq.Core.FLT`.
The remaining source declarations are outside this packet's formal roots.
-/

namespace CompCert4Lean.Flocq.Core.FLT

abbrev R := CompCert4Lean.Flocq.Core.Raux.R
abbrev Z := CompCert4Lean.Flocq.Core.Zaux.Z
abbrev radix := CompCert4Lean.Flocq.Core.Zaux.radix
abbrev float := CompCert4Lean.Flocq.Core.Defs.float
abbrev Fnum {beta : radix} (f : float beta) : Z :=
  CompCert4Lean.Flocq.Core.Defs.Fnum f
abbrev Fexp {beta : radix} (f : float beta) : Z :=
  CompCert4Lean.Flocq.Core.Defs.Fexp f
abbrev F2R {beta : radix} (f : float beta) : R :=
  CompCert4Lean.Flocq.Core.Defs.F2R f
abbrev Zabs := CompCert4Lean.Flocq.Core.Zaux.Zabs
abbrev Zadd := CompCert4Lean.Flocq.Core.Zaux.Zadd
abbrev Zle := CompCert4Lean.Flocq.Core.Zaux.Zle
abbrev Zlt := CompCert4Lean.Flocq.Core.Zaux.Zlt
abbrev Zmax := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max
abbrev Zpower := CompCert4Lean.Flocq.Core.Zaux.Zpower
abbrev Zsub := CompCert4Lean.Flocq.Core.Zaux.Zsub
abbrev Zone := CompCert4Lean.Flocq.Core.Zaux.Zone
abbrev Prec_gt_0 := CompCert4Lean.Flocq.Core.FLX.Prec_gt_0
private abbrev intOfZ := CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
private abbrev zOfInt := CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
abbrev Valid_exp := CompCert4Lean.Flocq.Core.Generic_fmt.Valid_exp
abbrev Monotone_exp := CompCert4Lean.Flocq.Core.Generic_fmt.Monotone_exp
abbrev generic_format := CompCert4Lean.Flocq.Core.Generic_fmt.generic_format
abbrev bpow := CompCert4Lean.Flocq.Core.Raux.bpow
abbrev Rlt := CompCert4Lean.Flocq.Core.Raux.Rlt

def FLT_exp (emin prec e : Z) : Z := Zmax (Zsub e prec) emin

instance FLT_exp_valid (emin prec : Z) [Prec_gt_0 prec] : Valid_exp (FLT_exp emin prec) where
  valid_exp := by
    have zsub_int : ∀ a b : Z, intOfZ (Zsub a b) = intOfZ a - intOfZ b := by
      intro a b
      change intOfZ (zOfInt (intOfZ a - intOfZ b)) = _
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    have zadd_int : ∀ a b : Z, intOfZ (Zadd a b) = intOfZ a + intOfZ b := by
      intro a b
      change intOfZ (zOfInt (intOfZ a + intOfZ b)) = _
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    have zone_int : intOfZ Zone = 1 := by
      change Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.xH) = 1
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
    have hp : 0 < intOfZ prec := by
      exact CompCert4Lean.Flocq.Core.FLX.prec_gt_0 prec
    have exp_succ_le : ∀ e : Z, intOfZ (Zsub (Zadd e Zone) prec) ≤ intOfZ e := by
      intro e
      rw [zsub_int, zadd_int, zone_int]
      omega
    have exp_emin_le : ∀ e : Z, intOfZ emin ≤ intOfZ (FLT_exp emin prec e) := by
      intro e
      change intOfZ emin ≤ intOfZ (Zmax (Zsub e prec) emin)
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max]
      by_cases h : intOfZ (Zsub e prec) ≤ intOfZ emin
      · simp only [if_pos h]
        exact Int.le_refl _
      · simp only [if_neg h]
        omega
    have exp_succ_bound : ∀ e : Z, intOfZ emin ≤ intOfZ e →
        intOfZ (FLT_exp emin prec (Zadd e Zone)) ≤ intOfZ e := by
      intro e he
      change intOfZ (Zmax (Zsub (Zadd e Zone) prec) emin) ≤ intOfZ e
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max]
      by_cases h : intOfZ (Zsub (Zadd e Zone) prec) ≤ intOfZ emin
      · simp only [if_pos h]
        exact he
      · simp only [if_neg h]
        exact exp_succ_le e
    intro k
    constructor
    · intro h
      change intOfZ (FLT_exp emin prec k) < intOfZ k at h
      change intOfZ (FLT_exp emin prec (Zadd k Zone)) ≤ intOfZ k
      simp only [FLT_exp, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max] at h ⊢
      simp only [zsub_int, zadd_int, zone_int] at h ⊢
      by_cases hke : intOfZ k - intOfZ prec ≤ intOfZ emin
      · simp only [if_pos hke] at h
        by_cases hnext : intOfZ k + 1 - intOfZ prec ≤ intOfZ emin
        · simp only [if_pos hnext]
          omega
        · simp only [if_neg hnext]
          have hnext_sub : intOfZ (Zsub (Zadd k Zone) prec) =
              intOfZ k + 1 - intOfZ prec := by
            rw [zsub_int, zadd_int, zone_int]
          rw [hnext_sub]
          omega
      · simp only [if_neg hke] at h
        by_cases hnext : intOfZ k + 1 - intOfZ prec ≤ intOfZ emin
        · simp only [if_pos hnext]
          omega
        · simp only [if_neg hnext]
          have hnext_sub : intOfZ (Zsub (Zadd k Zone) prec) =
              intOfZ k + 1 - intOfZ prec := by
            rw [zsub_int, zadd_int, zone_int]
          rw [hnext_sub]
          omega
    · intro h
      constructor
      · change intOfZ (FLT_exp emin prec (Zadd (FLT_exp emin prec k) Zone)) ≤
          intOfZ (FLT_exp emin prec k)
        exact exp_succ_bound (FLT_exp emin prec k) (exp_emin_le k)
      · intro l hl
        change FLT_exp emin prec l = FLT_exp emin prec k
        have hk : intOfZ k ≤ intOfZ (FLT_exp emin prec k) := h
        have hke : intOfZ (Zsub k prec) ≤ intOfZ emin := by
          by_cases hke : intOfZ (Zsub k prec) ≤ intOfZ emin
          · exact hke
          · have hgt : intOfZ emin < intOfZ (Zsub k prec) := Int.lt_of_not_ge hke
            have hmax : intOfZ (FLT_exp emin prec k) = intOfZ (Zsub k prec) := by
              change intOfZ (Zmax (Zsub k prec) emin) = _
              simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max,
                if_neg hke]
            have hk' := hk
            rw [hmax] at hk'
            have hk_sub := zsub_int k prec
            rw [hk_sub] at hk'
            exfalso
            omega
        have hmax : intOfZ (FLT_exp emin prec k) = intOfZ emin := by
          change intOfZ (Zmax (Zsub k prec) emin) = _
          simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max,
            if_pos hke]
        have hl' : intOfZ l ≤ intOfZ emin := by
          rw [← hmax]
          exact hl
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        change intOfZ (FLT_exp emin prec l) = intOfZ (FLT_exp emin prec k)
        have hlmax : intOfZ (FLT_exp emin prec l) = intOfZ emin := by
          change intOfZ (Zmax (Zsub l prec) emin) = _
          simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max]
          by_cases hle : intOfZ (Zsub l prec) ≤ intOfZ emin
          · simp only [if_pos hle]
          · simp only [if_neg hle]
            have hl_sub := zsub_int l prec
            rw [hl_sub] at hle
            exfalso
            omega
        exact hlmax.trans hmax.symm

instance FLT_exp_monotone (emin prec : Z) : Monotone_exp (FLT_exp emin prec) where
  monotone_exp := by
    intro ex ey h
    change intOfZ ex ≤ intOfZ ey at h
    change intOfZ (FLT_exp emin prec ex) ≤ intOfZ (FLT_exp emin prec ey)
    have hsub : intOfZ (Zsub ex prec) ≤ intOfZ (Zsub ey prec) := by
      change intOfZ (zOfInt (intOfZ ex - intOfZ prec)) ≤
        intOfZ (zOfInt (intOfZ ey - intOfZ prec))
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      omega
    simp only [FLT_exp, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max]
    by_cases hxe : intOfZ (Zsub ex prec) ≤ intOfZ emin
    · simp only [if_pos hxe]
      by_cases hye : intOfZ (Zsub ey prec) ≤ intOfZ emin
      · simp only [if_pos hye]
        exact Int.le_refl _
      · simp only [if_neg hye]
        omega
    · simp only [if_neg hxe]
      by_cases hye : intOfZ (Zsub ey prec) ≤ intOfZ emin
      · simp only [if_pos hye]
        omega
      · simp only [if_neg hye]
        exact hsub

abbrev ExactRealContext := CompCert4Lean.Flocq.Core.Generic_fmt.ExactRealContext

namespace Exact

abbrev Context := ExactRealContext
abbrev R (ctx : Context) := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R ctx
abbrev F2R (ctx : Context) {beta : radix} (f : float beta) : R ctx :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx f
abbrev Magnitude (ctx : Context) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Magnitude ctx
abbrev generic_format := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.generic_format
abbrev bpow := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.bpow
abbrev R0 := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R0
abbrev Rabs := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rabs
abbrev Rlt := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rlt

end Exact

inductive FLT_format (ctx : ExactRealContext) :
    radix → Z → Z → Exact.R ctx → Prop where
  | FLT_spec (beta : radix) (emin prec : Z) (x : Exact.R ctx)
      (f : float beta) :
      x = Exact.F2R ctx f →
      Zlt (Zabs (Fnum f)) (Zpower beta prec) →
      Zle emin (Fexp f) →
      FLT_format ctx beta emin prec x

export FLT_format (FLT_spec)

def generic_format_FLTStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (beta : radix) (emin prec : Z) (x : Exact.R ctx),
    FLT_format ctx beta emin prec x →
      Exact.generic_format ctx magnitude beta (FLT_exp emin prec) x

def generic_format_FLT_bpowStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (beta : radix) (emin prec : Z) [Prec_gt_0 prec] (e : Z),
    Zle emin e →
      Exact.generic_format ctx magnitude beta (FLT_exp emin prec)
        (Exact.bpow ctx beta e)

def ulp_FLT_0Statement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (beta : radix) (emin prec : Z) [Prec_gt_0 prec],
    CompCert4Lean.Flocq.Core.Ulp.Exact.ulp ctx magnitude beta (FLT_exp emin prec)
        (CompCert4Lean.Flocq.Core.Ulp.Exact.R0 ctx) =
      Exact.bpow ctx beta emin

def ulp_FLT_smallStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (beta : radix) (emin prec : Z) [Prec_gt_0 prec] (x : Exact.R ctx),
    Exact.Rlt ctx (Exact.Rabs ctx x) (Exact.bpow ctx beta (Zadd emin prec)) →
      CompCert4Lean.Flocq.Core.Ulp.Exact.ulp ctx magnitude beta (FLT_exp emin prec) x =
        Exact.bpow ctx beta emin

end CompCert4Lean.Flocq.Core.FLT
