import CompCert4Lean.Flocq.Core.Generic_fmt

/-!
# Sterbenz conditions for exact subtraction

This module carries the exact-real definitions selected from
`Flocq.Prop.Sterbenz`.  The proof-bearing source declarations are represented
by exact proposition descriptors for the later proof-migration phase.
-/

namespace CompCert4Lean.Flocq.Prop.Sterbenz

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.Core.Generic_fmt

abbrev Z := CompCert4Lean.Flocq.Core.Raux.Z
abbrev radix := CompCert4Lean.Flocq.Core.Raux.radix
abbrev ExactRealContext := CompCert4Lean.Flocq.Core.Generic_fmt.ExactRealContext
abbrev ExactMagnitude (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Magnitude ctx
abbrev ExactR (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R ctx

abbrev Zmin := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.min

abbrev bpow (ctx : ExactRealContext) (beta : radix) (e : Z) : ExactR ctx :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.bpow ctx beta e

abbrev format (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (fexp : Z → Z) : ExactR ctx → Prop :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.generic_format ctx magnitude beta fexp

section ExactSpecification

variable (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)

local notation "R" => ExactR ctx
local notation "Rplus" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rplus ctx
local notation "Rminus" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rminus ctx
local notation "Rmult" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rmult ctx
local notation "Rabs" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rabs ctx
local notation "Rmin" => CompCert4Lean.Flocq.Core.Raux.Exact.Rmin ctx
local notation "Rtwo" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rtwo ctx
local notation "Rle" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rle ctx
local notation "bpow" => bpow ctx
local notation "format" => format ctx magnitude
local notation "mag" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.mag magnitude

def generic_format_plusStatement : Prop :=
  ∀ beta fexp, Valid_exp fexp → Monotone_exp fexp →
    ∀ x y, format beta fexp x → format beta fexp y →
      Rle (Rabs (Rplus x y))
        (bpow beta (Zmin (mag beta x) (mag beta y))) →
          format beta fexp (Rplus x y)

def generic_format_plus_weakStatement : Prop :=
  ∀ beta fexp, Valid_exp fexp → Monotone_exp fexp →
    ∀ x y, format beta fexp x → format beta fexp y →
      Rle (Rabs (Rplus x y)) (Rmin (Rabs x) (Rabs y)) →
        format beta fexp (Rplus x y)

def sterbenz_auxStatement : Prop :=
  ∀ beta fexp, Valid_exp fexp → Monotone_exp fexp →
    ∀ x y, format beta fexp x → format beta fexp y →
      (Rle y x ∧ Rle x (Rmult Rtwo y)) →
        format beta fexp (Rminus x y)

end ExactSpecification

end CompCert4Lean.Flocq.Prop.Sterbenz
