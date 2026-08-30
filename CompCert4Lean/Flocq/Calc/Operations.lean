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
  CompCert4Lean.Flocq.Core.Defs.Float beta m e
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

abbrev ExactRealContext := CompCert4Lean.Flocq.Core.Raux.ExactRealContext

namespace Exact

abbrev F2R := CompCert4Lean.Flocq.Core.Defs.Exact.F2R
abbrev Ropp := CompCert4Lean.Flocq.Core.Raux.Exact.Ropp
abbrev Rabs := CompCert4Lean.Flocq.Core.Raux.Exact.Rabs
abbrev Rplus := CompCert4Lean.Flocq.Core.Raux.Exact.Rplus
abbrev Rmult := CompCert4Lean.Flocq.Core.Raux.Exact.Rmult

end Exact

def Falign (f1 f2 : float beta) : (Z × Z) × Z :=
  match f1, f2 with
  | CompCert4Lean.Flocq.Core.Defs.Float _ m1 e1,
      CompCert4Lean.Flocq.Core.Defs.Float _ m2 e2 =>
      if Zle_bool e1 e2 then
        ((m1, Zmul m2 (Zpower (beta : Z) (Zsub e2 e1))), e1)
      else
        ((Zmul m1 (Zpower (beta : Z) (Zsub e1 e2)), m2), e2)

def Fopp {beta : radix} (f1 : float beta) : float beta :=
  match f1 with
  | CompCert4Lean.Flocq.Core.Defs.Float _ m1 e1 => Float beta (Zopp m1) e1

def Fabs {beta : radix} (f1 : float beta) : float beta :=
  match f1 with
  | CompCert4Lean.Flocq.Core.Defs.Float _ m1 e1 => Float beta (Zabs m1) e1

def Fplus {beta : radix} (f1 f2 : float beta) : float beta :=
  let ((m1, m2), e) := Falign f1 f2
  Float beta (Zadd m1 m2) e

def Fmult {beta : radix} (f1 f2 : float beta) : float beta :=
  match f1, f2 with
  | CompCert4Lean.Flocq.Core.Defs.Float _ m1 e1,
      CompCert4Lean.Flocq.Core.Defs.Float _ m2 e2 =>
      Float beta (Zmul m1 m2) (Zadd e1 e2)

/-! Exact source proposition descriptors for later proof migration. -/

def Falign_specStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (f1 f2 : float beta),
    let ((m1, m2), e) := Falign f1 f2
    Exact.F2R ctx f1 = Exact.F2R ctx (Float beta m1 e) ∧
      Exact.F2R ctx f2 = Exact.F2R ctx (Float beta m2 e)

def Falign_spec_expStatement : Prop :=
  ∀ (beta : radix) (f1 f2 : float beta),
    (Falign f1 f2).2 = Zmin (Fexp f1) (Fexp f2)

def F2R_oppStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (f1 : float beta),
    Exact.F2R ctx (Fopp f1) = Exact.Ropp ctx (Exact.F2R ctx f1)

def F2R_absStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (f1 : float beta),
    Exact.F2R ctx (Fabs f1) = Exact.Rabs ctx (Exact.F2R ctx f1)

def F2R_plusStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (f1 f2 : float beta),
    Exact.F2R ctx (Fplus f1 f2) =
      Exact.Rplus ctx (Exact.F2R ctx f1) (Exact.F2R ctx f2)

def Fexp_FplusStatement : Prop :=
  ∀ (beta : radix) (f1 f2 : float beta),
    Fexp (Fplus f1 f2) = Zmin (Fexp f1) (Fexp f2)

def F2R_multStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (f1 f2 : float beta),
    Exact.F2R ctx (Fmult f1 f2) =
      Exact.Rmult ctx (Exact.F2R ctx f1) (Exact.F2R ctx f2)

end CompCert4Lean.Flocq.Calc.Operations
