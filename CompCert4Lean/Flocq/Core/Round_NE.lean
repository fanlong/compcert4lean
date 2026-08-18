import CompCert4Lean.Flocq.Core.Generic_fmt

/-!
# Rounding to nearest, ties to even

This module contains the definition surfaces selected from
`Flocq.Core.Round_NE`.  The two proof-bearing declarations assigned to a later
phase are represented by exact proposition descriptors.
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

/-! Exact source proposition descriptors for later proof migration. -/

def round_NE_oppStatement : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ x,
    round beta fexp ZnearestE (Ropp x) =
      Ropp (round beta fexp ZnearestE x)

def round_NE_absStatement : Prop :=
  ∀ beta fexp, Valid_exp fexp → ∀ x,
    round beta fexp ZnearestE (Rabs x) =
      Rabs (round beta fexp ZnearestE x)

end CompCert4Lean.Flocq.Core.Round_NE
