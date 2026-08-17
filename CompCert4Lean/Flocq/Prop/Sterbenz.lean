import CompCert4Lean.Flocq.Core.Generic_fmt

/-!
# Sterbenz conditions for exact subtraction

This module carries the executable abbreviations selected from
`Flocq.Prop.Sterbenz`.  The proof-bearing source declarations are represented
by exact proposition descriptors for the later proof-migration phase.
-/

namespace CompCert4Lean.Flocq.Prop.Sterbenz

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.Core.Generic_fmt

abbrev R := CompCert4Lean.Flocq.Core.Raux.R
abbrev Z := CompCert4Lean.Flocq.Core.Raux.Z
abbrev radix := CompCert4Lean.Flocq.Core.Raux.radix

abbrev Zmin := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.min
abbrev Rmin := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rmin
abbrev Rplus := CompCert4Lean.Flocq.Core.Raux.Rplus
abbrev Rminus := CompCert4Lean.Flocq.Core.Raux.Rminus
abbrev Rmult := CompCert4Lean.Flocq.Core.Raux.Rmult
abbrev Rabs := CompCert4Lean.Flocq.Core.Raux.Rabs
abbrev Rtwo := CompCert4Lean.Flocq.Core.Raux.Rtwo
abbrev Rle := CompCert4Lean.Flocq.Core.Raux.Rle

abbrev bpow (beta : radix) (e : Z) : R :=
  CompCert4Lean.Flocq.Core.Raux.bpow beta e

abbrev format (beta : radix) (fexp : Z → Z) : R → Prop :=
  CompCert4Lean.Flocq.Core.Generic_fmt.generic_format beta fexp

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

end CompCert4Lean.Flocq.Prop.Sterbenz
