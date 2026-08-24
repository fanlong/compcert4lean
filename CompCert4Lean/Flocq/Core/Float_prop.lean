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
