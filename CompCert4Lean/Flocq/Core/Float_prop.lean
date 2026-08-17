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

/-! Exact source proposition descriptors for later proof migration. -/

def Rcompare_F2RStatement : Prop :=
  ∀ (beta : radix) (e m1 m2 : Z),
    Rcompare (F2R (Float beta m1 e)) (F2R (Float beta m2 e)) =
      Zcompare m1 m2

def le_F2RStatement : Prop :=
  ∀ (beta : radix) (e m1 m2 : Z),
    Rle (F2R (Float beta m1 e)) (F2R (Float beta m2 e)) →
      Zle m1 m2

def F2R_leStatement : Prop :=
  ∀ (beta : radix) (m1 m2 e : Z),
    Zle m1 m2 →
      Rle (F2R (Float beta m1 e)) (F2R (Float beta m2 e))

def lt_F2RStatement : Prop :=
  ∀ (beta : radix) (e m1 m2 : Z),
    Rlt (F2R (Float beta m1 e)) (F2R (Float beta m2 e)) →
      Zlt m1 m2

def F2R_ltStatement : Prop :=
  ∀ (beta : radix) (e m1 m2 : Z),
    Zlt m1 m2 →
      Rlt (F2R (Float beta m1 e)) (F2R (Float beta m2 e))

def F2R_eqStatement : Prop :=
  ∀ (beta : radix) (e m1 m2 : Z),
    m1 = m2 →
      F2R (Float beta m1 e) = F2R (Float beta m2 e)

def eq_F2RStatement : Prop :=
  ∀ (beta : radix) (e m1 m2 : Z),
    F2R (Float beta m1 e) = F2R (Float beta m2 e) →
      m1 = m2

def F2R_ZabsStatement : Prop :=
  ∀ (beta : radix) (m e : Z),
    F2R (Float beta (Zabs m) e) = Rabs (F2R (Float beta m e))

def F2R_ZoppStatement : Prop :=
  ∀ (beta : radix) (m e : Z),
    F2R (Float beta (Zopp m) e) = Ropp (F2R (Float beta m e))

def F2R_cond_ZoppStatement : Prop :=
  ∀ (beta : radix) (b : Bool) (m e : Z),
    F2R (Float beta (cond_Zopp b m) e) =
      cond_Ropp b (F2R (Float beta m e))

def F2R_0Statement : Prop :=
  ∀ (beta : radix) (e : Z),
    F2R (Float beta Z0 e) = R0

def eq_0_F2RStatement : Prop :=
  ∀ (beta : radix) (m e : Z),
    F2R (Float beta m e) = R0 →
      m = Z0

def ge_0_F2RStatement : Prop :=
  ∀ (beta : radix) (m e : Z),
    Rle R0 (F2R (Float beta m e)) →
      Zle Z0 m

def le_0_F2RStatement : Prop :=
  ∀ (beta : radix) (m e : Z),
    Rle (F2R (Float beta m e)) R0 →
      Zle m Z0

def gt_0_F2RStatement : Prop :=
  ∀ (beta : radix) (m e : Z),
    Rlt R0 (F2R (Float beta m e)) →
      Zlt Z0 m

def lt_0_F2RStatement : Prop :=
  ∀ (beta : radix) (m e : Z),
    Rlt (F2R (Float beta m e)) R0 →
      Zlt m Z0

def F2R_ge_0Statement : Prop :=
  ∀ (beta : radix) (f : float beta),
    Zle Z0 (Fnum f) →
      Rle R0 (F2R f)

def F2R_le_0Statement : Prop :=
  ∀ (beta : radix) (f : float beta),
    Zle (Fnum f) Z0 →
      Rle (F2R f) R0

def F2R_gt_0Statement : Prop :=
  ∀ (beta : radix) (f : float beta),
    Zlt Z0 (Fnum f) →
      Rlt R0 (F2R f)

def F2R_lt_0Statement : Prop :=
  ∀ (beta : radix) (f : float beta),
    Zlt (Fnum f) Z0 →
      Rlt (F2R f) R0

def F2R_neq_0Statement : Prop :=
  ∀ (beta : radix) (f : float beta),
    Fnum f ≠ Z0 →
      F2R f ≠ R0

def F2R_bpowStatement : Prop :=
  ∀ (beta : radix) (e : Z),
    F2R (Float beta Zone e) = bpow beta e

def bpow_le_F2RStatement : Prop :=
  ∀ (beta : radix) (m e : Z),
    Zlt Z0 m →
      Rle (bpow beta e) (F2R (Float beta m e))

def F2R_p1_le_bpowStatement : Prop :=
  ∀ (beta : radix) (m e1 e2 : Z),
    Zlt Z0 m →
      Rlt (F2R (Float beta m e1)) (bpow beta e2) →
        Rle (F2R (Float beta (Zadd m Zone) e1)) (bpow beta e2)

def F2R_change_expStatement : Prop :=
  ∀ (beta : radix) (e' m e : Z),
    Zle e' e →
      F2R (Float beta m e) =
        F2R (Float beta (Zmul m (Zpower (beta : Z) (Zsub e e'))) e')

def mag_F2R_boundsStatement : Prop :=
  ∀ (beta : radix) (x : R) (m e : Z),
    Zlt Z0 m →
      (Rle (F2R (Float beta m e)) x ∧
        Rlt x (F2R (Float beta (Zadd m Zone) e))) →
        (mag beta x : Z) = (mag beta (F2R (Float beta m e)) : Z)

def mag_F2RStatement : Prop :=
  ∀ (beta : radix) (m e : Z),
    m ≠ Z0 →
      (mag beta (F2R (Float beta m e)) : Z) =
        Zadd (mag beta (IZR m) : Z) e

def Zdigits_magStatement : Prop :=
  ∀ (beta : radix) (n : Z),
    n ≠ Z0 →
      Zdigits beta n = (mag beta (IZR n) : Z)

def mag_F2R_ZdigitsStatement : Prop :=
  ∀ (beta : radix) (m e : Z),
    m ≠ Z0 →
      (mag beta (F2R (Float beta m e)) : Z) =
        Zadd (Zdigits beta m) e

def mag_F2R_bounds_ZdigitsStatement : Prop :=
  ∀ (beta : radix) (x : R) (m e : Z),
    Zlt Z0 m →
      (Rle (F2R (Float beta m e)) x ∧
        Rlt x (F2R (Float beta (Zadd m Zone) e))) →
        (mag beta x : Z) = Zadd (Zdigits beta m) e

end CompCert4Lean.Flocq.Core.Float_prop
