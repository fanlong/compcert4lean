import CompCert4Lean.Flocq.Core.Zaux
import Lean.Elab.Command

/-!
# Floating-point format without underflow

This module contains the selected definition surface from `Flocq.Core.FLX`.
The remaining source declarations are outside this packet's formal roots.
-/

open Lean Elab Command

namespace CompCert4Lean.Flocq.Core.FLX

abbrev Z := CompCert4Lean.Flocq.Core.Zaux.Z
abbrev Z0 : Z := CompCert4Lean.Flocq.Core.Zaux.Z0
abbrev Zlt := CompCert4Lean.Flocq.Core.Zaux.Zlt

/-! The source `Class Prec_gt_0` elaborates to the transparent proposition
    `Zlt Z0 prec`, rather than to a nominal one-field record. -/
def Prec_gt_0 (prec : Z) : Prop := Zlt Z0 prec

/-! Lean only accepts inductive declarations and axioms through the public
    `[class]` attribute, while Rocq's source class is a transparent
    proposition.  Register the existing transparent constant directly in the
    class environment; this changes elaboration metadata only and preserves
    the source proposition and reduction behavior. -/
run_cmd
  let env ← getEnv
  let env := Lean.classExtension.addEntry env {
    name := ``CompCert4Lean.Flocq.Core.FLX.Prec_gt_0
    outParams := #[]
    outLevelParams := #[]
  }
  modifyEnv fun _ => env

abbrev prec_gt_0 (prec : Z) [h : Prec_gt_0 prec] : Zlt Z0 prec := h

end CompCert4Lean.Flocq.Core.FLX
