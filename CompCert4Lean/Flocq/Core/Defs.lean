import CompCert4Lean.Flocq.Core.Raux

/-!
# Basic Flocq definitions

This module contains the executable definition surfaces selected from
`Flocq.Core.Defs`.  The source-facing names are retained while the numerical
operations are supplied by the checked Flocq real and Rocq standard-library
facades.
-/

namespace CompCert4Lean.Flocq.Core.Defs

abbrev R := CompCert4Lean.Flocq.Core.Raux.R
abbrev Z := CompCert4Lean.Flocq.Core.Raux.Z
abbrev radix := CompCert4Lean.Flocq.Core.Raux.radix
abbrev IZR := CompCert4Lean.Flocq.Core.Raux.IZR
abbrev bpow := CompCert4Lean.Flocq.Core.Raux.bpow
abbrev Rmult := CompCert4Lean.Flocq.Core.Raux.Rmult
abbrev Rle := CompCert4Lean.Flocq.Core.Raux.Rle

structure float (beta : radix) where
  Fnum : Z
  Fexp : Z

export float (Fnum Fexp)

def F2R {beta : radix} (f : float beta) : R :=
  Rmult (IZR (Fnum f)) (bpow beta (Fexp f))

def round_pred_monotone (P : R → R → Prop) : Prop :=
  ∀ x y f g, P x f → P y g → Rle x y → Rle f g

def Rnd_DN_pt (F : R → Prop) (x f : R) : Prop :=
  F f ∧ Rle f x ∧ ∀ g : R, F g → Rle g x → Rle g f

def Rnd_UP_pt (F : R → Prop) (x f : R) : Prop :=
  F f ∧ Rle x f ∧ ∀ g : R, F g → Rle x g → Rle f g

end CompCert4Lean.Flocq.Core.Defs
