import CompCert4Lean.Flocq.Core.Zaux

/-!
# Floating-point format without underflow

This module contains the selected definition surface from `Flocq.Core.FLX`.
The remaining source declarations are outside this packet's formal roots.
-/

namespace CompCert4Lean.Flocq.Core.FLX

abbrev Z := CompCert4Lean.Flocq.Core.Zaux.Z
abbrev Z0 : Z := CompCert4Lean.Flocq.Core.Zaux.Z0
abbrev Zlt := CompCert4Lean.Flocq.Core.Zaux.Zlt

/-! The source `Class Prec_gt_0` elaborates to the transparent proposition
    `Zlt Z0 prec`, rather than to a nominal one-field record.  Keep that
    source-facing boundary transparent; the separately named adapter below is
    only for Lean consumers that want typeclass synthesis. -/
def Prec_gt_0 (prec : Z) : Prop := Zlt Z0 prec

/-! Internal typeclass convenience for definitions that use synthesized
    precision hypotheses.  Its field stores the canonical source proposition;
    it is not the public `Prec_gt_0` representation. -/
class Prec_gt_0Class (prec : Z) : Prop where
  proof : Prec_gt_0 prec

def Prec_gt_0Class.of {prec : Z} (h : Prec_gt_0 prec) : Prec_gt_0Class prec :=
  { proof := h }

abbrev prec_gt_0 (prec : Z) {h : Prec_gt_0 prec} : Zlt Z0 prec := h

abbrev prec_gt_0_of_class (prec : Z) [h : Prec_gt_0Class prec] : Zlt Z0 prec :=
  prec_gt_0 prec (h := h.proof)

end CompCert4Lean.Flocq.Core.FLX
