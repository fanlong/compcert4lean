import CompCert4Lean.Flocq.Core.Generic_fmt
import CompCert4Lean.Flocq.Core.Round_NE
import CompCert4Lean.Flocq.Core.Round_pred
import CompCert4Lean.Flocq.Core.Ulp

/-!
# Fixed-point format

This module contains the definition-bearing surface selected from
`Flocq.Core.FIX`.  Proof-bearing source declarations are represented by
source-named proposition descriptors for the later proof phase.
-/

namespace CompCert4Lean.Flocq.Core.FIX

abbrev R := CompCert4Lean.Flocq.Core.Raux.R
abbrev Z := CompCert4Lean.Flocq.Core.Zaux.Z
abbrev radix := CompCert4Lean.Flocq.Core.Zaux.radix
abbrev float := CompCert4Lean.Flocq.Core.Defs.float
abbrev Fexp {beta : radix} (f : float beta) : Z :=
  CompCert4Lean.Flocq.Core.Defs.Fexp f
abbrev F2R {beta : radix} (f : float beta) : R :=
  CompCert4Lean.Flocq.Core.Defs.F2R f
abbrev generic_format := CompCert4Lean.Flocq.Core.Generic_fmt.generic_format
abbrev Valid_exp := CompCert4Lean.Flocq.Core.Generic_fmt.Valid_exp
abbrev Monotone_exp := CompCert4Lean.Flocq.Core.Generic_fmt.Monotone_exp
abbrev round := CompCert4Lean.Flocq.Core.Generic_fmt.round
abbrev radix2 := CompCert4Lean.Flocq.Core.Zaux.radix2
abbrev satisfies_any := CompCert4Lean.Flocq.Core.Round_pred.satisfies_any
abbrev Exists_NE := CompCert4Lean.Flocq.Core.Round_NE.Exists_NE
abbrev Zlt := CompCert4Lean.Flocq.Core.Zaux.Zlt
abbrev Zle := CompCert4Lean.Flocq.Core.Zaux.Zle
abbrev Zadd := CompCert4Lean.Flocq.Core.Zaux.Zadd
abbrev Zone := CompCert4Lean.Flocq.Core.Zaux.Zone
abbrev Z0 := CompCert4Lean.Flocq.Core.Zaux.Z0
abbrev IZR := CompCert4Lean.Flocq.Core.Raux.IZR

def bpow (beta : radix) (e : Z) : R :=
  CompCert4Lean.Flocq.Core.Raux.bpow beta e

inductive FIX_format : radix → Z → R → Prop where
  | FIX_spec (beta : radix) (emin : Z) (x : R) (f : float beta) :
      x = F2R f → Fexp f = emin → FIX_format beta emin x

export FIX_format (FIX_spec)

abbrev ExactRealContext := CompCert4Lean.Flocq.Core.Generic_fmt.ExactRealContext

namespace Exact

inductive FIX_format (ctx : ExactRealContext) (beta : radix) (emin : Z)
    (x : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R ctx) : Prop where
  | FIX_spec (f : float beta) :
      x = CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx f →
        Fexp f = emin → FIX_format ctx beta emin x

export FIX_format (FIX_spec)

end Exact

def FIX_exp (emin : Z) (e : Z) : Z := emin

instance FIX_exp_valid (emin : Z) : Valid_exp (FIX_exp emin) where
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

def generic_format_FIXStatement (ctx : ExactRealContext)
    (magnitude : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Magnitude ctx) : Prop :=
  ∀ (beta : radix) (emin : Z)
    (x : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R ctx),
    Exact.FIX_format ctx beta emin x →
      CompCert4Lean.Flocq.Core.Generic_fmt.Exact.generic_format
        ctx magnitude beta (FIX_exp emin) x

def FIX_format_genericStatement (ctx : ExactRealContext)
    (magnitude : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Magnitude ctx) : Prop :=
  ∀ (beta : radix) (emin : Z)
    (x : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R ctx),
    CompCert4Lean.Flocq.Core.Generic_fmt.Exact.generic_format
        ctx magnitude beta (FIX_exp emin) x →
      Exact.FIX_format ctx beta emin x

def FIX_format_satisfies_anyStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (emin : Z),
    CompCert4Lean.Flocq.Core.Round_pred.satisfies_any ctx
      (Exact.FIX_format ctx beta emin)

instance FIX_exp_monotone (emin : Z) : Monotone_exp (FIX_exp emin) where
  monotone_exp := by
    intro ex ey _
    exact Int.le_refl _

def ulp_FIXStatement (ctx : ExactRealContext)
    (magnitude : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Magnitude ctx) : Prop :=
  ∀ (beta : radix) (emin : Z)
    (x : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R ctx),
    CompCert4Lean.Flocq.Core.Ulp.Exact.ulp
        ctx magnitude beta (FIX_exp emin) x =
      CompCert4Lean.Flocq.Core.Generic_fmt.Exact.bpow ctx beta emin

instance exists_NE_FIX (beta : radix) (emin : Z) : Exists_NE beta (FIX_exp emin) :=
  ⟨Or.inr (fun e => by
    constructor
    · intro h
      exact h
    · intro _
      rfl)⟩

def round_FIX_IZRStatement (ctx : ExactRealContext)
    (magnitude : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Magnitude ctx) : Prop :=
  ∀ (f : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R ctx → Z)
    (x : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R ctx),
    CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
        ctx magnitude radix2 (FIX_exp Z0) f x =
      CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx (f x)

end CompCert4Lean.Flocq.Core.FIX
