import CompCert4Lean.Flocq.Core.Generic_fmt
import CompCert4Lean.Flocq.Core.FLX

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
abbrev Valid_exp := CompCert4Lean.Flocq.Core.Generic_fmt.Valid_exp
abbrev Monotone_exp := CompCert4Lean.Flocq.Core.Generic_fmt.Monotone_exp
abbrev generic_format := CompCert4Lean.Flocq.Core.Generic_fmt.generic_format

inductive FLT_format (beta : radix) (emin prec : Z) [Prec_gt_0 prec] (x : R) : Prop where
  | mk (f : float beta) :
      x = F2R f →
      Zlt (Zabs (Fnum f)) (Zpower beta prec) →
      Zle emin (Fexp f) →
      FLT_format beta emin prec x

def FLT_exp (emin prec _e : Z) : Z := emin

instance FLT_exp_valid (emin prec : Z) [Prec_gt_0 prec] : Valid_exp (FLT_exp emin prec) where
  valid_exp := by
    intro k
    constructor
    · intro h
      exact Int.le_of_lt h
    · intro h
      constructor
      · exact Int.le_refl _
      · intro l _
        rfl

instance FLT_exp_monotone (emin prec : Z) [Prec_gt_0 prec] : Monotone_exp (FLT_exp emin prec) where
  monotone_exp := by
    intro ex ey h
    exact Int.le_refl _

def generic_format_FLTStatement : Prop :=
  ∀ (beta : radix) (emin prec : Z) [Prec_gt_0 prec] (x : R),
    FLT_format beta emin prec x → generic_format beta (FLT_exp emin prec) x

end CompCert4Lean.Flocq.Core.FLT
