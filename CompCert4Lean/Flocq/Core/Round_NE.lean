import CompCert4Lean.Flocq.Core.Generic_fmt

/-!
# Rounding to nearest, ties to even

This module contains the definition surfaces selected from
`Flocq.Core.Round_NE`.  Runtime rounding remains on the checked rational
carrier, while theorem-facing predicates and descriptors use the explicit
exact-real context and magnitude witness selected by RPR-007.
-/

namespace CompCert4Lean.Flocq.Core.Round_NE

open CompCert4Lean.Flocq.Core

abbrev R := Raux.R
abbrev Z := Raux.Z
abbrev radix := Raux.radix
abbrev Zeven := Zaux.Zeven
abbrev Zone : Z := Zaux.Zone
abbrev Zadd := Zaux.Zadd
abbrev Zle := Zaux.Zle
abbrev Zlt := Zaux.Zlt
abbrev Ropp := Raux.Ropp
abbrev Rabs := Raux.Rabs
abbrev Valid_exp := Generic_fmt.Valid_exp
abbrev round := Generic_fmt.round
abbrev Znearest := Generic_fmt.Znearest

abbrev ZnearestE (x : R) : Z :=
  Znearest (fun m => Bool.not (Zeven m)) x

class Exists_NE (beta : radix) (fexp : Z → Z) : Prop where
  exists_NE :
    Zeven (beta : Z) = false ∨
      ∀ e : Z,
        (Zlt (fexp e) e → Zlt (fexp (Zadd e Zone)) e) ∧
          (Zle e (fexp e) → fexp (Zadd (fexp e) Zone) = fexp e)

def exists_NE (beta : radix) (fexp : Z → Z)
    [exists_NE_ : Exists_NE beta fexp] :
    Zeven (beta : Z) = false ∨
      ∀ e : Z,
        (Zlt (fexp e) e → Zlt (fexp (Zadd e Zone)) e) ∧
          (Zle e (fexp e) → fexp (Zadd (fexp e) Zone) = fexp e) :=
  exists_NE_.exists_NE

/-! The source computational notation above remains a runtime operation.  The
exact counterpart below is used only by theorem and specification surfaces. -/

abbrev ExactRealContext := Generic_fmt.ExactRealContext
abbrev ExactMagnitude (ctx : ExactRealContext) := Generic_fmt.Exact.Magnitude ctx

namespace Exact

abbrev R (ctx : ExactRealContext) := Generic_fmt.Exact.R ctx
abbrev F2R (ctx : ExactRealContext) {beta : radix} (f : Defs.float beta) : R ctx :=
  Generic_fmt.Exact.F2R ctx f
abbrev R0 (ctx : ExactRealContext) := Generic_fmt.Exact.R0 ctx
abbrev Ropp (ctx : ExactRealContext) := Generic_fmt.Exact.Ropp ctx
abbrev Rabs (ctx : ExactRealContext) := Generic_fmt.Exact.Rabs ctx
abbrev Rlt (ctx : ExactRealContext) := Generic_fmt.Exact.Rlt ctx
abbrev bpow (ctx : ExactRealContext) := Generic_fmt.Exact.bpow ctx
abbrev canonical (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx) :=
  Generic_fmt.Exact.canonical ctx magnitude
abbrev format (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx) :=
  Generic_fmt.Exact.generic_format ctx magnitude
abbrev round (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx) :=
  Generic_fmt.Exact.round ctx magnitude
abbrev Zfloor (ctx : ExactRealContext) := Generic_fmt.Exact.Zfloor ctx
abbrev Zceil (ctx : ExactRealContext) := Generic_fmt.Exact.Zceil ctx

noncomputable abbrev ZnearestE (ctx : ExactRealContext) (x : R ctx) : Z :=
  Generic_fmt.Exact.Znearest ctx (fun m => Bool.not (Zeven m)) x

end Exact

/-! Source-local theorem notation is exposed on the exact carrier. -/

abbrev bpow (ctx : ExactRealContext) := Exact.bpow ctx
abbrev canonical (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx) :=
  Exact.canonical ctx magnitude
abbrev format (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx) :=
  Exact.format ctx magnitude

/-! Checked runtime compatibility surfaces remain available without being used
by the exact predicates or theorem descriptors below. -/

namespace Runtime

abbrev bpow (beta : radix) (e : Z) : R := Raux.bpow beta e
abbrev canonical (beta : radix) (fexp : Z → Z) (f : Defs.float beta) : Prop :=
  Generic_fmt.canonical beta fexp f
abbrev format (beta : radix) (fexp : Z → Z) : R → Prop :=
  Generic_fmt.generic_format beta fexp
abbrev ZnearestE := CompCert4Lean.Flocq.Core.Round_NE.ZnearestE

end Runtime

def DN_UP_parity_pos_prop (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (fexp : Z → Z) : Prop :=
  ∀ (x : Exact.R ctx) (xd xu : Defs.float beta),
    Exact.Rlt ctx (Exact.R0 ctx) x →
      ¬ format ctx magnitude beta fexp x →
      canonical ctx magnitude beta fexp xd →
      canonical ctx magnitude beta fexp xu →
      Exact.F2R ctx xd =
        Exact.round ctx magnitude beta fexp (Exact.Zfloor ctx) x →
      Exact.F2R ctx xu =
        Exact.round ctx magnitude beta fexp (Exact.Zceil ctx) x →
      Zeven (Defs.Fnum xu) = Bool.not (Zeven (Defs.Fnum xd))

def DN_UP_parity_prop (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (fexp : Z → Z) : Prop :=
  ∀ (x : Exact.R ctx) (xd xu : Defs.float beta),
    ¬ format ctx magnitude beta fexp x →
      canonical ctx magnitude beta fexp xd →
      canonical ctx magnitude beta fexp xu →
      Exact.F2R ctx xd =
        Exact.round ctx magnitude beta fexp (Exact.Zfloor ctx) x →
      Exact.F2R ctx xu =
        Exact.round ctx magnitude beta fexp (Exact.Zceil ctx) x →
      Zeven (Defs.Fnum xu) = Bool.not (Zeven (Defs.Fnum xd))

/-! Exact source proposition descriptors for later proof migration. -/

def round_NE_oppStatement (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx) : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (x : Exact.R ctx),
    Exact.round ctx magnitude beta fexp (Exact.ZnearestE ctx) (Exact.Ropp ctx x) =
      Exact.Ropp ctx
        (Exact.round ctx magnitude beta fexp (Exact.ZnearestE ctx) x)

def round_NE_absStatement (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx) : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp → ∀ x : Exact.R ctx,
    Exact.round ctx magnitude beta fexp (Exact.ZnearestE ctx) (Exact.Rabs ctx x) =
      Exact.Rabs ctx
        (Exact.round ctx magnitude beta fexp (Exact.ZnearestE ctx) x)

def DN_UP_parity_auxStatement (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx) : Prop :=
  ∀ (beta : radix) (fexp : Z → Z),
    DN_UP_parity_pos_prop ctx magnitude beta fexp →
      DN_UP_parity_prop ctx magnitude beta fexp

def DN_UP_parity_genericStatement (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx) : Prop :=
  ∀ (beta : radix) (fexp : Z → Z),
    Valid_exp fexp → Exists_NE beta fexp →
      DN_UP_parity_prop ctx magnitude beta fexp

def DN_UP_parity_generic_posStatement (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx) : Prop :=
  ∀ (beta : radix) (fexp : Z → Z),
    Valid_exp fexp → Exists_NE beta fexp →
      DN_UP_parity_pos_prop ctx magnitude beta fexp

end CompCert4Lean.Flocq.Core.Round_NE
