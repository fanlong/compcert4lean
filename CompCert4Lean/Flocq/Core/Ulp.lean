import CompCert4Lean.Flocq.Core.Generic_fmt

/-!
# Unit in the last place

This module contains the definition-bearing surface selected from
`Flocq.Core.Ulp`.  The four proof-bearing declarations assigned to the later
proof phase are represented by exact proposition descriptors below.
-/

namespace CompCert4Lean.Flocq.Core.Ulp

abbrev R := CompCert4Lean.Flocq.Core.Raux.R
abbrev Z := CompCert4Lean.Flocq.Core.Zaux.Z
abbrev radix := CompCert4Lean.Flocq.Core.Zaux.radix
abbrev Z0 := CompCert4Lean.Flocq.Core.Zaux.Z0
abbrev Zle := CompCert4Lean.Flocq.Core.Zaux.Zle
abbrev IZR := CompCert4Lean.Flocq.Core.Raux.IZR
abbrev R0 := CompCert4Lean.Flocq.Core.Raux.R0
abbrev Rabs := CompCert4Lean.Flocq.Core.Raux.Rabs
abbrev Rminus := CompCert4Lean.Flocq.Core.Raux.Rminus
abbrev Rlt := CompCert4Lean.Flocq.Core.Raux.Rlt
abbrev Req_bool := CompCert4Lean.Flocq.Core.Raux.Req_bool
abbrev cexp := CompCert4Lean.Flocq.Core.Generic_fmt.cexp
abbrev generic_format := CompCert4Lean.Flocq.Core.Generic_fmt.generic_format
abbrev round := CompCert4Lean.Flocq.Core.Generic_fmt.round
abbrev Valid_exp := CompCert4Lean.Flocq.Core.Generic_fmt.Valid_exp
abbrev Valid_rnd := CompCert4Lean.Flocq.Core.Generic_fmt.Valid_rnd
abbrev Zceil := CompCert4Lean.Flocq.Core.Raux.Zceil
abbrev Zfloor := CompCert4Lean.Flocq.Core.Raux.Zfloor
abbrev Sumor := CompCert4Lean.Foundation.Logic.Support.Sumor

/- The source notation is a local abbreviation for the provider's bpow. -/
def bpow (beta : radix) (e : Z) : R :=
  CompCert4Lean.Flocq.Core.Raux.bpow beta e

/- LPO_Z is a classical Rocq specification primitive.  This local adapter
   keeps that source boundary explicit while preserving the selected
   `negligible_exp` definition without introducing an extra project assumption. -/
private noncomputable def lpo_Z (P : Z → Prop) :
    Sumor (Subtype P) (∀ z, ¬ P z) := by
  classical
  by_cases h : ∃ z, P z
  · exact .inleft ⟨Classical.choose h, Classical.choose_spec h⟩
  · exact .inright (fun z hz => h ⟨z, hz⟩)

noncomputable def negligible_exp (fexp : Z → Z) : Option Z :=
  match lpo_Z (fun z => Zle z (fexp z)) with
  | .inleft witness => some witness.val
  | .inright _ => none

noncomputable def ulp (beta : radix) (fexp : Z → Z) (x : R) : R :=
  match Req_bool x R0 with
  | true =>
      match negligible_exp fexp with
      | some n => bpow beta (fexp n)
      | none => R0
  | false => bpow beta (cexp beta fexp x)

def F (beta : radix) (fexp : Z → Z) (x : R) : Prop :=
  generic_format beta fexp x

/-! Exact source proposition descriptors for the later proof phase. -/

def Z_le_dec_auxStatement : Prop :=
  ∀ (x y : Z), Zle x y ∨ ¬ Zle x y

def ulp_neq_0Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (x : R),
    x ≠ R0 →
      ulp beta fexp x = bpow beta (cexp beta fexp x)

def round_UP_DN_ulpStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (x : R),
    ¬ generic_format beta fexp x →
      round beta fexp Zceil x =
        CompCert4Lean.Flocq.Core.Raux.Rplus
          (round beta fexp Zfloor x) (ulp beta fexp x)

def error_lt_ulpStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z),
    Valid_exp fexp →
      ∀ (rnd : R → Z),
        Valid_rnd rnd →
          ∀ (x : R), x ≠ R0 →
            Rlt
              (Rabs (Rminus (round beta fexp rnd x) x))
              (ulp beta fexp x)

end CompCert4Lean.Flocq.Core.Ulp
