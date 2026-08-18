import CompCert4Lean.Flocq.Core.Core

/-!
# Relative rounding error

This module preserves the executable local `bpow` surface from
`Flocq.Prop.Relative`.  The proof-bearing declarations assigned to the later
proof phase are represented by exact source-shaped proposition descriptors.
-/

namespace CompCert4Lean.Flocq.Prop.Relative

abbrev R := CompCert4Lean.Flocq.Core.Raux.R
abbrev Z := CompCert4Lean.Flocq.Core.Raux.Z
abbrev radix := CompCert4Lean.Flocq.Core.Raux.radix

abbrev Valid_exp := CompCert4Lean.Flocq.Core.Generic_fmt.Valid_exp
abbrev Valid_rnd := CompCert4Lean.Flocq.Core.Generic_fmt.Valid_rnd
abbrev round := CompCert4Lean.Flocq.Core.Generic_fmt.round
abbrev FLT_exp := CompCert4Lean.Flocq.Core.FLT.FLT_exp

abbrev Z0 := CompCert4Lean.Flocq.Core.Zaux.Z0
abbrev Zone := CompCert4Lean.Flocq.Core.Zaux.Zone
abbrev Zadd := CompCert4Lean.Flocq.Core.Zaux.Zadd
abbrev Zsub := CompCert4Lean.Flocq.Core.Zaux.Zsub
abbrev Zopp := CompCert4Lean.Flocq.Core.Zaux.Zopp
abbrev Zle := CompCert4Lean.Flocq.Core.Zaux.Zle
abbrev Zlt := CompCert4Lean.Flocq.Core.Zaux.Zlt

abbrev R0 := CompCert4Lean.Flocq.Core.Raux.R0
abbrev Rone := CompCert4Lean.Flocq.Core.Raux.Rone
abbrev Rplus := CompCert4Lean.Flocq.Core.Raux.Rplus
abbrev Rminus := CompCert4Lean.Flocq.Core.Raux.Rminus
abbrev Rmult := CompCert4Lean.Flocq.Core.Raux.Rmult
abbrev Rabs := CompCert4Lean.Flocq.Core.Raux.Rabs
abbrev Rlt := CompCert4Lean.Flocq.Core.Raux.Rlt
abbrev Rle := CompCert4Lean.Flocq.Core.Raux.Rle

abbrev bpow (beta : radix) (e : Z) : R :=
  CompCert4Lean.Flocq.Core.Raux.bpow beta e

def relative_error_lt_conversionStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (rnd : R → Z),
    Valid_rnd rnd →
      ∀ (x b : R),
        Rlt R0 b →
          (x ≠ R0 →
            Rlt
              (Rabs (Rminus (round beta fexp rnd x) x))
              (Rmult b (Rabs x))) →
            ∃ eps : R,
              Rlt (Rabs eps) b ∧
                round beta fexp rnd x = Rmult x (Rplus Rone eps)

def relative_errorStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z),
    Valid_exp fexp →
      ∀ (emin p : Z),
        (∀ k : Z, Zlt emin k → Zle p (Zsub k (fexp k))) →
          ∀ (rnd : R → Z),
            Valid_rnd rnd →
              ∀ (x : R),
                Rle (bpow beta emin) (Rabs x) →
                  Rlt
                    (Rabs (Rminus (round beta fexp rnd x) x))
                    (Rmult (bpow beta (Zadd (Zopp p) Zone)) (Rabs x))

def relative_error_FLT_auxStatement : Prop :=
  ∀ (emin prec k : Z),
    Zlt (Zsub (Zadd emin prec) Zone) k →
      Zle prec (Zsub k (FLT_exp emin prec k))

def relative_error_FLTStatement : Prop :=
  ∀ (beta : radix) (emin prec : Z),
    Zlt Z0 prec →
      ∀ (rnd : R → Z),
        Valid_rnd rnd →
          ∀ (x : R),
            Rle (bpow beta (Zsub (Zadd emin prec) Zone)) (Rabs x) →
              Rlt
                (Rabs (Rminus (round beta (FLT_exp emin prec) rnd x) x))
                (Rmult
                  (bpow beta (Zadd (Zopp prec) Zone))
                  (Rabs x))

def relative_error_FLT_exStatement : Prop :=
  ∀ (beta : radix) (emin prec : Z),
    Zlt Z0 prec →
      ∀ (rnd : R → Z),
        Valid_rnd rnd →
          ∀ (x : R),
            Rle (bpow beta (Zsub (Zadd emin prec) Zone)) (Rabs x) →
              ∃ eps : R,
                Rlt (Rabs eps) (bpow beta (Zadd (Zopp prec) Zone)) ∧
                  round beta (FLT_exp emin prec) rnd x =
                    Rmult x (Rplus Rone eps)

end CompCert4Lean.Flocq.Prop.Relative
