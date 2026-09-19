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

namespace CompCert4Lean.Flocq.Core.FIX

theorem FIX_format_generic (ctx : ExactRealContext)
    (magnitude : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Magnitude ctx) :
    FIX_format_genericStatement ctx magnitude := by
  intro beta emin x hgeneric
  unfold CompCert4Lean.Flocq.Core.Generic_fmt.Exact.generic_format at hgeneric
  refine Exact.FIX_spec (CompCert4Lean.Flocq.Core.Defs.Float beta
    (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa ctx magnitude beta (FIX_exp emin) x))
    emin) ?_ rfl
  simpa [FIX_exp, CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp] using hgeneric

theorem ulp_FIX (ctx : ExactRealContext)
    (magnitude : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Magnitude ctx) :
    ulp_FIXStatement ctx magnitude := by
  intro beta emin x
  cases hreq : CompCert4Lean.Flocq.Core.Ulp.Exact.Req_bool ctx x
      (CompCert4Lean.Flocq.Core.Ulp.Exact.R0 ctx) with
  | false =>
      simp [CompCert4Lean.Flocq.Core.Ulp.Exact.ulp, hreq,
        CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp, FIX_exp]
  | true =>
      rw [CompCert4Lean.Flocq.Core.Ulp.Exact.ulp, hreq]
      cases hnegligible : CompCert4Lean.Flocq.Core.Ulp.negligible_exp (FIX_exp emin) with
      | some n =>
          simp [FIX_exp]
      | none =>
          have hspec := CompCert4Lean.Flocq.Core.Ulp.negligible_exp_spec (FIX_exp emin)
          rw [hnegligible] at hspec
          cases hspec with
          | negligible_None hall =>
              have hlt := hall emin
              change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emin <
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emin at hlt
              exact (Int.lt_irrefl _ hlt).elim

end CompCert4Lean.Flocq.Core.FIX

namespace CompCert4Lean.Flocq.Core.FIX

theorem round_FIX_IZR (ctx : ExactRealContext)
    (magnitude : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Magnitude ctx) :
    round_FIX_IZRStatement ctx magnitude := by
  intro f x
  unfold CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
    CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
    CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp FIX_exp
  have hscaled :
      CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rmult ctx x
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.bpow ctx radix2
            (CompCert4Lean.Flocq.Core.Zaux.Zopp Z0)) = x := by
    change ctx.spec.mul x ctx.spec.one = x
    exact ctx.certificate.orderedField.mul_one _
  rw [hscaled]
  change ctx.spec.mul (ctx.spec.ofZ (f x)) ctx.spec.one = ctx.spec.ofZ (f x)
  exact ctx.certificate.orderedField.mul_one _

end CompCert4Lean.Flocq.Core.FIX

namespace CompCert4Lean.Flocq.Core.FIX

theorem generic_format_FIX (ctx : ExactRealContext)
    (magnitude : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Magnitude ctx) :
    generic_format_FIXStatement ctx magnitude := by
  intro beta emin x hfix
  cases hfix with
  | FIX_spec f hx he =>
      subst x
      apply CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_canonical
        ctx magnitude beta (FIX_exp emin) f
      unfold CompCert4Lean.Flocq.Core.Generic_fmt.Exact.canonical
      change Fexp f = emin
      exact he

end CompCert4Lean.Flocq.Core.FIX
