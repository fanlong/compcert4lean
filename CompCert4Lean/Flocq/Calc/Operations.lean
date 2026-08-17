import CompCert4Lean.Flocq.Core.Defs

/-!
# Basic operations on Flocq floats

This module contains the executable definitions selected from
`Flocq.Calc.Operations`.  The source theorem declarations are retained as
exact proposition descriptors for the later proof-migration phase.
-/

namespace CompCert4Lean.Flocq.Calc.Operations

abbrev R := CompCert4Lean.Flocq.Core.Defs.R
abbrev Z := CompCert4Lean.Flocq.Core.Defs.Z
abbrev radix := CompCert4Lean.Flocq.Core.Defs.radix
abbrev float := CompCert4Lean.Flocq.Core.Defs.float
abbrev Float (beta : radix) (m e : Z) : float beta :=
  CompCert4Lean.Flocq.Core.Defs.float.mk m e
abbrev Fnum {beta : radix} (f : float beta) : Z :=
  CompCert4Lean.Flocq.Core.Defs.Fnum f
abbrev Fexp {beta : radix} (f : float beta) : Z :=
  CompCert4Lean.Flocq.Core.Defs.Fexp f
abbrev IZR := CompCert4Lean.Flocq.Core.Defs.IZR
abbrev F2R {beta : radix} (f : float beta) : R :=
  CompCert4Lean.Flocq.Core.Defs.F2R f

abbrev Zadd := CompCert4Lean.Flocq.Core.Zaux.Zadd
abbrev Zsub := CompCert4Lean.Flocq.Core.Zaux.Zsub
abbrev Zmul := CompCert4Lean.Flocq.Core.Zaux.Zmul
abbrev Zopp := CompCert4Lean.Flocq.Core.Zaux.Zopp
abbrev Zabs := CompCert4Lean.Flocq.Core.Zaux.Zabs
abbrev Zle_bool := CompCert4Lean.Flocq.Core.Zaux.Zle_bool
abbrev Zpower := CompCert4Lean.Flocq.Core.Zaux.Zpower
abbrev Zmin := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.min
abbrev Rplus := CompCert4Lean.Flocq.Core.Raux.Rplus
abbrev Rmult := CompCert4Lean.Flocq.Core.Raux.Rmult
abbrev Ropp := CompCert4Lean.Flocq.Core.Raux.Ropp
abbrev Rabs := CompCert4Lean.Flocq.Core.Raux.Rabs

def Falign (f1 f2 : float beta) : (Z × Z) × Z :=
  match f1, f2 with
  | ⟨m1, e1⟩, ⟨m2, e2⟩ =>
      if Zle_bool e1 e2 then
        ((m1, Zmul m2 (Zpower (beta : Z) (Zsub e2 e1))), e1)
      else
        ((Zmul m1 (Zpower (beta : Z) (Zsub e1 e2)), m2), e2)

def Fopp {beta : radix} (f1 : float beta) : float beta :=
  match f1 with
  | ⟨m1, e1⟩ => Float beta (Zopp m1) e1

def Fabs {beta : radix} (f1 : float beta) : float beta :=
  match f1 with
  | ⟨m1, e1⟩ => Float beta (Zabs m1) e1

def Fplus {beta : radix} (f1 f2 : float beta) : float beta :=
  let ((m1, m2), e) := Falign f1 f2
  Float beta (Zadd m1 m2) e

def Fmult {beta : radix} (f1 f2 : float beta) : float beta :=
  match f1, f2 with
  | ⟨m1, e1⟩, ⟨m2, e2⟩ => Float beta (Zmul m1 m2) (Zadd e1 e2)

/-! Exact source proposition descriptors for later proof migration. -/

def Falign_specStatement : Prop :=
  ∀ (beta : radix) (f1 f2 : float beta),
    let ((m1, m2), e) := Falign f1 f2
    F2R f1 = F2R (Float beta m1 e) ∧
      F2R f2 = F2R (Float beta m2 e)

def Falign_spec_expStatement : Prop :=
  ∀ (beta : radix) (f1 f2 : float beta),
    (Falign f1 f2).2 = Zmin (Fexp f1) (Fexp f2)

def F2R_oppStatement : Prop :=
  ∀ (beta : radix) (f1 : float beta),
    F2R (Fopp f1) = Ropp (F2R f1)

def F2R_absStatement : Prop :=
  ∀ (beta : radix) (f1 : float beta),
    F2R (Fabs f1) = Rabs (F2R f1)

def F2R_plusStatement : Prop :=
  ∀ (beta : radix) (f1 f2 : float beta),
    F2R (Fplus f1 f2) = Rplus (F2R f1) (F2R f2)

def Fexp_FplusStatement : Prop :=
  ∀ (beta : radix) (f1 f2 : float beta),
    Fexp (Fplus f1 f2) = Zmin (Fexp f1) (Fexp f2)

def F2R_multStatement : Prop :=
  ∀ (beta : radix) (f1 f2 : float beta),
    F2R (Fmult f1 f2) = Rmult (F2R f1) (F2R f2)

end CompCert4Lean.Flocq.Calc.Operations
