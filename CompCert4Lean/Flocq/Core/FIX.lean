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
namespace CompCert4Lean.Flocq.Core.FIX

private abbrev fix_Zopp := CompCert4Lean.Flocq.Core.Zaux.Zopp

private theorem fix_zsub_add_opp (a b : Z) :
    CompCert4Lean.Flocq.Core.Zaux.Zsub a b =
      CompCert4Lean.Flocq.Core.Zaux.Zadd a (fix_Zopp b) := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Flocq.Core.Zaux.Zsub a b) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Flocq.Core.Zaux.Zadd a
        (CompCert4Lean.Flocq.Core.Zaux.Zopp b))
  simp only [CompCert4Lean.Flocq.Core.Zaux.Zsub,
    CompCert4Lean.Flocq.Core.Zaux.Zadd,
    fix_Zopp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

private theorem fix_ofZ_sub (ctx : ExactRealContext) (a b : Z) :
    ctx.spec.ofZ (CompCert4Lean.Flocq.Core.Zaux.Zsub a b) =
      ctx.spec.add (ctx.spec.ofZ a) (ctx.spec.neg (ctx.spec.ofZ b)) := by
  rw [fix_zsub_add_opp, ctx.certificate.sourceLaws.ofZ_add,
    ctx.certificate.sourceLaws.ofZ_neg]

private theorem fix_ofZ_succ_sub (ctx : ExactRealContext) (u : Z) :
    ctx.spec.ofZ u =
      ctx.spec.add
        (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub
          u CompCert4Lean.Flocq.Core.Zaux.Zone))
        ctx.spec.one := by
  have h : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub u
        CompCert4Lean.Flocq.Core.Zaux.Zone)
      CompCert4Lean.Flocq.Core.Zaux.Zone = u := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub u
            CompCert4Lean.Flocq.Core.Zaux.Zone)
          CompCert4Lean.Flocq.Core.Zaux.Zone) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ u
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ u - 1 + 1 =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ u
    omega
  calc
    ctx.spec.ofZ u = ctx.spec.ofZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub u
            CompCert4Lean.Flocq.Core.Zaux.Zone)
          CompCert4Lean.Flocq.Core.Zaux.Zone) := congrArg ctx.spec.ofZ h.symm
    _ = ctx.spec.add
        (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub u
          CompCert4Lean.Flocq.Core.Zaux.Zone))
        (ctx.spec.ofZ CompCert4Lean.Flocq.Core.Zaux.Zone) :=
      ctx.certificate.sourceLaws.ofZ_add _ _
    _ = ctx.spec.add
        (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub u
          CompCert4Lean.Flocq.Core.Zaux.Zone)) ctx.spec.one := by
      rw [show ctx.spec.ofZ CompCert4Lean.Flocq.Core.Zaux.Zone = ctx.spec.one from
        ctx.certificate.sourceLaws.ofZ_one]

private theorem fix_mul_le_of_pos (ctx : ExactRealContext)
    {p a b : ctx.spec.carrier} (hp : ctx.spec.lt ctx.spec.zero p)
    (hab : ctx.spec.le a b) :
    ctx.spec.le (ctx.spec.mul p a) (ctx.spec.mul p b) := by
  rcases ctx.certificate.total_order a b with h | h
  · rcases h with hlt | heq
    · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
        (ctx.certificate.orderedField.mul_lt_compat_l p a b hp hlt) |>.1
    · rw [heq]
      exact ctx.certificate.orderedField.le_refl _
  · exact False.elim (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h).2 hab)

private theorem fix_zero_lt_one (ctx : ExactRealContext) :
    ctx.spec.lt ctx.spec.zero ctx.spec.one := by
  rcases ctx.certificate.total_order ctx.spec.zero ctx.spec.one with h | h
  · rcases h with h | h
    · exact h
    · exact (ctx.certificate.orderedField.zero_ne_one h).elim
  · have hzero_lt_neg : ctx.spec.lt ctx.spec.zero (ctx.spec.neg ctx.spec.one) := by
      have hadd := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.neg ctx.spec.one) ctx.spec.one ctx.spec.zero h
      rw [ctx.certificate.orderedField.neg_add_cancel,
        ctx.certificate.orderedField.add_zero] at hadd
      exact hadd
    have hneg_lt_zero := ctx.certificate.orderedField.mul_lt_compat_l
      (ctx.spec.neg ctx.spec.one) ctx.spec.one ctx.spec.zero hzero_lt_neg h
    rw [ctx.certificate.orderedField.mul_one,
      ctx.certificate.orderedField.mul_zero] at hneg_lt_zero
    exact (ctx.certificate.orderedField.lt_irrefl ctx.spec.zero
      (ctx.certificate.orderedField.lt_trans ctx.spec.zero
        (ctx.spec.neg ctx.spec.one) ctx.spec.zero hzero_lt_neg hneg_lt_zero)).elim

private theorem fix_add_left_cancel (ctx : ExactRealContext)
    (p q r : ctx.spec.carrier)
    (h : ctx.spec.add p q = ctx.spec.add p r) : q = r := by
  have h' := congrArg (fun z => ctx.spec.add (ctx.spec.neg p) z) h
  have hl : ctx.spec.add (ctx.spec.neg p) (ctx.spec.add p q) = q := by
    rw [← ctx.certificate.orderedField.add_assoc,
      ctx.certificate.orderedField.neg_add_cancel,
      ctx.certificate.orderedField.zero_add]
  have hr : ctx.spec.add (ctx.spec.neg p) (ctx.spec.add p r) = r := by
    rw [← ctx.certificate.orderedField.add_assoc,
      ctx.certificate.orderedField.neg_add_cancel,
      ctx.certificate.orderedField.zero_add]
  exact hl.symm.trans (h'.trans hr)

private theorem fix_neg_mul (ctx : ExactRealContext) (a b : ctx.spec.carrier) :
    ctx.spec.neg (ctx.spec.mul a b) =
      ctx.spec.mul (ctx.spec.neg a) b := by
  apply fix_add_left_cancel ctx (ctx.spec.mul a b)
  calc
    ctx.spec.add (ctx.spec.mul a b) (ctx.spec.neg (ctx.spec.mul a b)) =
        ctx.spec.add (ctx.spec.neg (ctx.spec.mul a b)) (ctx.spec.mul a b) :=
      ctx.certificate.orderedField.add_comm _ _
    _ = ctx.spec.zero := ctx.certificate.orderedField.neg_add_cancel _
    _ = ctx.spec.add (ctx.spec.mul a b) (ctx.spec.mul (ctx.spec.neg a) b) := by
      calc
        ctx.spec.zero = ctx.spec.mul b ctx.spec.zero :=
          (ctx.certificate.orderedField.mul_zero _).symm
        _ = ctx.spec.mul b (ctx.spec.add (ctx.spec.neg a) a) := by
          rw [ctx.certificate.orderedField.neg_add_cancel]
        _ = ctx.spec.add (ctx.spec.mul b (ctx.spec.neg a))
              (ctx.spec.mul b a) := ctx.certificate.orderedField.left_distrib _ _ _
        _ = ctx.spec.add (ctx.spec.mul a b) (ctx.spec.mul (ctx.spec.neg a) b) := by
          rw [ctx.certificate.orderedField.mul_comm b (ctx.spec.neg a),
            ctx.certificate.orderedField.mul_comm b a,
            ctx.certificate.orderedField.add_comm]

private theorem fix_inv_pos (ctx : ExactRealContext) {p : ctx.spec.carrier}
    (hp : ctx.spec.lt ctx.spec.zero p) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.inv p) := by
  have hpne : p ≠ ctx.spec.zero := by
    intro h
    rw [h] at hp
    exact ctx.certificate.orderedField.lt_irrefl _ hp
  rcases ctx.certificate.total_order ctx.spec.zero (ctx.spec.inv p) with h | h
  · rcases h with hpos | hzero
    · exact hpos
    · have hi := ctx.certificate.orderedField.inv_mul_cancel p hpne
      rw [← hzero, ctx.certificate.orderedField.zero_mul] at hi
      exact (ctx.certificate.orderedField.zero_ne_one hi).elim
  · have hmul := ctx.certificate.orderedField.mul_lt_compat_l p
      (ctx.spec.inv p) ctx.spec.zero hp h
    rw [ctx.certificate.orderedField.mul_comm p (ctx.spec.inv p),
      ctx.certificate.orderedField.inv_mul_cancel p hpne,
      ctx.certificate.orderedField.mul_zero] at hmul
    exact (ctx.certificate.orderedField.lt_irrefl _
      (ctx.certificate.orderedField.lt_trans _ _ _
        (fix_zero_lt_one ctx) hmul)).elim

private theorem fix_format_satisfies_any_core (ctx : ExactRealContext) :
    FIX_format_satisfies_anyStatement ctx := by
  intro beta emin
  apply CompCert4Lean.Flocq.Core.Round_pred.satisfies_any.Satisfies_any
    (Exact.FIX_format ctx beta emin)
  · refine Exact.FIX_spec (CompCert4Lean.Flocq.Core.Defs.Float beta Z0 emin) ?_ rfl
    change ctx.spec.zero = ctx.spec.mul (ctx.spec.ofZ Z0)
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta emin)
    rw [ctx.certificate.sourceLaws.ofZ_zero,
      ctx.certificate.orderedField.zero_mul]
  · intro x hx
    rcases hx with ⟨f, hxf, hef⟩
    cases f with
    | Float m e =>
        refine Exact.FIX_spec (CompCert4Lean.Flocq.Core.Defs.Float beta (fix_Zopp m) e) ?_ hef
        change ctx.spec.neg x = ctx.spec.mul (ctx.spec.ofZ (fix_Zopp m))
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e)
        change x = ctx.spec.mul (ctx.spec.ofZ m)
          (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e) at hxf
        rw [ctx.certificate.sourceLaws.ofZ_neg]
        calc
          ctx.spec.neg x = ctx.spec.neg
              (ctx.spec.mul (ctx.spec.ofZ m)
                (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e)) := by rw [hxf]
          _ = ctx.spec.mul (ctx.spec.neg (ctx.spec.ofZ m))
              (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e) :=
            fix_neg_mul ctx _ _
  · intro x
    let p := CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta emin
    let q := ctx.spec.mul x (ctx.spec.inv p)
    let u := ctx.spec.up q
    let n := CompCert4Lean.Flocq.Core.Zaux.Zsub u Zone
    have hp : ctx.spec.lt ctx.spec.zero p := by
      exact CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta emin
    have hpne : p ≠ ctx.spec.zero := by
      intro h
      rw [h] at hp
      exact ctx.certificate.orderedField.lt_irrefl _ hp
    have hqp : ctx.spec.mul q p = x := by
      dsimp [q]
      calc
        ctx.spec.mul (ctx.spec.mul x (ctx.spec.inv p)) p =
            ctx.spec.mul x (ctx.spec.mul (ctx.spec.inv p) p) :=
          ctx.certificate.orderedField.mul_assoc _ _ _
        _ = ctx.spec.mul x ctx.spec.one := by
          rw [ctx.certificate.orderedField.inv_mul_cancel p hpne]
        _ = x := ctx.certificate.orderedField.mul_one _
    have hfloor : ctx.spec.le (ctx.spec.ofZ n) q := by
      have hgap := ctx.certificate.sourceLaws.up_gap q
      have hgood : ctx.spec.le
          (ctx.spec.add (ctx.spec.ofZ u) (ctx.spec.neg q)) ctx.spec.one := by
        change ctx.spec.le (ctx.spec.add (ctx.spec.ofZ u) (ctx.spec.neg q)) ctx.spec.one
        change ctx.spec.le (ctx.spec.add (ctx.spec.ofZ u) (ctx.spec.neg q))
          (ctx.spec.ofZ CompCert4Lean.Flocq.Core.Zaux.Zone) at hgap
        simpa [ctx.certificate.sourceLaws.ofZ_one] using hgap
      by_cases hle : ctx.spec.le (ctx.spec.ofZ n) q
      · exact hle
      · have hnq : ctx.spec.lt q (ctx.spec.ofZ n) := by
          rcases ctx.certificate.total_order q (ctx.spec.ofZ n) with h | h
          · rcases h with hlt | heq
            · exact hlt
            · exact (hle (by rw [heq]; exact ctx.certificate.orderedField.le_refl _)).elim
          · exact (hle ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h).1).elim
        have hplus := ctx.certificate.orderedField.add_lt_compat_l
          ctx.spec.one q (ctx.spec.ofZ n) hnq
        have hu_eq : ctx.spec.ofZ u = ctx.spec.add (ctx.spec.ofZ n) ctx.spec.one := by
          simpa [n] using fix_ofZ_succ_sub ctx u
        have hplus' : ctx.spec.lt
            (ctx.spec.add q ctx.spec.one) (ctx.spec.ofZ u) := by
          rw [hu_eq]
          rw [ctx.certificate.orderedField.add_comm q ctx.spec.one]
          rw [ctx.certificate.orderedField.add_comm (ctx.spec.ofZ n) ctx.spec.one]
          simpa [n] using hplus
        have hdiff := ctx.certificate.orderedField.add_lt_compat_l
          (ctx.spec.neg q) (ctx.spec.add q ctx.spec.one) (ctx.spec.ofZ u) hplus'
        rw [← ctx.certificate.orderedField.add_assoc,
          ctx.certificate.orderedField.neg_add_cancel,
          ctx.certificate.orderedField.zero_add] at hdiff
        have hgood' : ctx.spec.le
            (ctx.spec.add (ctx.spec.neg q) (ctx.spec.ofZ u)) ctx.spec.one := by
          rw [ctx.certificate.orderedField.add_comm]
          exact hgood
        exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hdiff |>.2 hgood' |>.elim
    have hdn : ctx.spec.le (ctx.spec.mul (ctx.spec.ofZ n) p) x := by
      have hmulle : ctx.spec.le (ctx.spec.mul (ctx.spec.ofZ n) p)
          (ctx.spec.mul q p) := by
        exact (by
          simpa [ctx.certificate.orderedField.mul_comm] using
            fix_mul_le_of_pos ctx hp hfloor)
      rw [hqp] at hmulle
      exact hmulle
    have hformat : Exact.FIX_format ctx beta emin
        (ctx.spec.mul (ctx.spec.ofZ n) p) := by
      refine Exact.FIX_spec (CompCert4Lean.Flocq.Core.Defs.Float beta n emin) ?_ rfl
      rfl
    refine ⟨ctx.spec.mul (ctx.spec.ofZ n) p, hformat, hdn, ?_⟩
    intro g hg hgx
    rcases hg with ⟨f, hgf, hef⟩
    cases f with
    | Float m e =>
        have heme : e = emin := hef
        subst e
        have hgm : ctx.spec.le (ctx.spec.ofZ m) q := by
          have hmul : ctx.spec.le
              (ctx.spec.mul (ctx.spec.inv p) g)
              (ctx.spec.mul (ctx.spec.inv p) (ctx.spec.mul q p)) := by
            apply fix_mul_le_of_pos ctx (fix_inv_pos ctx hp)
            rw [hqp]
            exact hgx
          rw [hgf] at hmul
          change ctx.spec.le
            (ctx.spec.mul (ctx.spec.inv p)
              (ctx.spec.mul (ctx.spec.ofZ m) p))
            (ctx.spec.mul (ctx.spec.inv p) (ctx.spec.mul q p)) at hmul
          have hleft : ctx.spec.mul (ctx.spec.inv p)
              (ctx.spec.mul (ctx.spec.ofZ m) p) = ctx.spec.ofZ m := by
            calc
              ctx.spec.mul (ctx.spec.inv p)
                  (ctx.spec.mul (ctx.spec.ofZ m) p) =
                  ctx.spec.mul (ctx.spec.inv p)
                    (ctx.spec.mul p (ctx.spec.ofZ m)) := by
                rw [ctx.certificate.orderedField.mul_comm
                  (ctx.spec.ofZ m) p]
              _ = ctx.spec.mul
                    (ctx.spec.mul (ctx.spec.inv p) p) (ctx.spec.ofZ m) := by
                rw [ctx.certificate.orderedField.mul_assoc]
              _ = ctx.spec.ofZ m := by
                rw [ctx.certificate.orderedField.inv_mul_cancel p hpne,
                  ctx.certificate.orderedField.one_mul]
          have hright : ctx.spec.mul (ctx.spec.inv p)
              (ctx.spec.mul q p) = q := by
            calc
              ctx.spec.mul (ctx.spec.inv p) (ctx.spec.mul q p) =
                  ctx.spec.mul (ctx.spec.inv p) (ctx.spec.mul p q) := by
                rw [ctx.certificate.orderedField.mul_comm q p]
              _ = ctx.spec.mul
                    (ctx.spec.mul (ctx.spec.inv p) p) q := by
                rw [ctx.certificate.orderedField.mul_assoc]
              _ = q := by
                rw [ctx.certificate.orderedField.inv_mul_cancel p hpne,
                  ctx.certificate.orderedField.one_mul]
          rw [hleft, hright] at hmul
          exact hmul
        have hmn : CompCert4Lean.Flocq.Core.Zaux.Zle m n := by
          by_cases hmn : CompCert4Lean.Flocq.Core.Zaux.Zle m n
          · exact hmn
          · exfalso
            have hnm : CompCert4Lean.Flocq.Core.Zaux.Zlt n m := by
              change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n <
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m
              change ¬ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m ≤
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n) at hmn
              omega
            have hunm : CompCert4Lean.Flocq.Core.Zaux.Zle u m := by
              change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ u ≤
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m
              change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                  (CompCert4Lean.Flocq.Core.Zaux.Zsub u Zone) <
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m at hnm
              simp only [CompCert4Lean.Flocq.Core.Zaux.Zsub,
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hnm
              change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ u - 1 <
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m at hnm
              omega
            have huq := ctx.certificate.sourceLaws.up_gt q
            have hmq :=
              CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_le
                ctx u m hunm
            exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp huq |>.2
              (ctx.certificate.orderedField.le_trans _ _ _ hmq hgm)
        have hmn' :=
          CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_le
            ctx m n hmn
        have hmul := fix_mul_le_of_pos ctx hp hmn'
        have hmul' : ctx.spec.le
            (ctx.spec.mul (ctx.spec.ofZ m) p)
            (ctx.spec.mul (ctx.spec.ofZ n) p) := by
          change ctx.spec.le
            (ctx.spec.mul p (ctx.spec.ofZ m))
            (ctx.spec.mul p (ctx.spec.ofZ n)) at hmul
          simpa [ctx.certificate.orderedField.mul_comm] using hmul
        rw [hgf]
        change ctx.spec.le
          (ctx.spec.mul (ctx.spec.ofZ m) p)
          (ctx.spec.mul (ctx.spec.ofZ n) p)
        exact hmul'

theorem FIX_format_satisfies_any (ctx : ExactRealContext) :
    FIX_format_satisfies_anyStatement ctx := fix_format_satisfies_any_core ctx

end CompCert4Lean.Flocq.Core.FIX
