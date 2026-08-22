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

inductive FIX_format (beta : radix) (emin : Z) (x : R) : Prop where
  | FIX_spec (f : float beta) :
      x = F2R f → Fexp f = emin → FIX_format beta emin x

export FIX_format (FIX_spec)

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

def generic_format_FIXStatement : Prop :=
  ∀ (beta : radix) (emin : Z) (x : R),
    FIX_format beta emin x → generic_format beta (FIX_exp emin) x

def FIX_format_genericStatement : Prop :=
  ∀ (beta : radix) (emin : Z) (x : R),
    generic_format beta (FIX_exp emin) x → FIX_format beta emin x

def FIX_format_satisfies_anyStatement : Prop :=
  ∀ (beta : radix) (emin : Z), satisfies_any (FIX_format beta emin)

instance FIX_exp_monotone (emin : Z) : Monotone_exp (FIX_exp emin) where
  monotone_exp := by
    intro ex ey _
    exact Int.le_refl _

def ulp_FIXStatement : Prop :=
  ∀ (beta : radix) (emin : Z) (x : R),
    CompCert4Lean.Flocq.Core.Ulp.ulp beta (FIX_exp emin) x = bpow beta emin

instance exists_NE_FIX (beta : radix) (emin : Z) : Exists_NE beta (FIX_exp emin) where
  exists_NE := Or.inr (fun e => by
    constructor
    · intro h
      exact h
    · intro _
      rfl)

def round_FIX_IZRStatement : Prop :=
  ∀ (f : R → Z) (x : R),
    round radix2 (FIX_exp Z0) f x = IZR (f x)

def FIX_format_ind (beta : radix) (emin : Z) (x : R) (P : Prop)
    (step : ∀ (f : float beta), x = F2R f → Fexp f = emin → P)
    (h : FIX_format beta emin x) : P :=
  match h with
  | .FIX_spec f hxf hfe => step f hxf hfe

end CompCert4Lean.Flocq.Core.FIX
