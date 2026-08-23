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

class Prec_gt_0 (prec : Z) : Prop where
  prec_gt_0 : Zlt Z0 prec

export Prec_gt_0 (prec_gt_0)

end CompCert4Lean.Flocq.Core.FLX
