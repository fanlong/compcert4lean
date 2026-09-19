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

namespace CompCert4Lean.Flocq.Core.Round_NE
theorem DN_UP_parity_aux :
    ∀ ctx magnitude, DN_UP_parity_auxStatement ctx magnitude := by
  intro ctx magnitude beta fexp hpos x xd xu
  intro hformat hx_d hx_u hxd hxu
  have hnegzero : Exact.Ropp ctx (Exact.R0 ctx) = Exact.R0 ctx := by
    change ctx.spec.neg ctx.spec.zero = ctx.spec.zero
    have h := ctx.certificate.orderedField.neg_add_cancel ctx.spec.zero
    rw [ctx.certificate.orderedField.add_zero] at h
    exact h
  have hnegneg : ∀ y : Exact.R ctx, Exact.Ropp ctx (Exact.Ropp ctx y) = y := by
    intro y
    change ctx.spec.neg (ctx.spec.neg y) = y
    calc
      ctx.spec.neg (ctx.spec.neg y) =
          ctx.spec.add (ctx.spec.neg (ctx.spec.neg y)) ctx.spec.zero :=
        (ctx.certificate.orderedField.add_zero _).symm
      _ = ctx.spec.add (ctx.spec.neg (ctx.spec.neg y))
          (ctx.spec.add (ctx.spec.neg y) y) := by
        rw [ctx.certificate.orderedField.neg_add_cancel]
      _ = ctx.spec.add
          (ctx.spec.add (ctx.spec.neg (ctx.spec.neg y)) (ctx.spec.neg y)) y := by
        rw [ctx.certificate.orderedField.add_assoc]
      _ = ctx.spec.add ctx.spec.zero y := by
        rw [ctx.certificate.orderedField.neg_add_cancel]
      _ = y := ctx.certificate.orderedField.zero_add _
  have hzero : format ctx magnitude beta fexp (Exact.R0 ctx) := by
    change Exact.R0 ctx = Exact.F2R ctx (Defs.float.Float beta
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp
          (Exact.R0 ctx)))
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp
        (Exact.R0 ctx)))
    rw [CompCert4Lean.Flocq.Core.Generic_fmt.scaled_mantissa_0
      ctx magnitude beta fexp]
    have hz : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx (Exact.R0 ctx) = Zaux.Z0 := by
      rw [show Exact.R0 ctx = CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx Zaux.Z0 by
        exact ctx.certificate.sourceLaws.ofZ_zero.symm]
      exact CompCert4Lean.Flocq.Core.Raux.Ztrunc_IZR ctx Zaux.Z0
    rw [hz]
    exact (CompCert4Lean.Flocq.Core.Float_prop.F2R_0 ctx beta _).symm
  rcases ctx.certificate.total_order (Exact.R0 ctx) x with hx | hx
  · rcases hx with hxpos | hxeq
    · exact hpos x xd xu hxpos hformat hx_d hx_u hxd hxu
    · subst x
      exact (hformat hzero).elim
  · have hxpos : Exact.Rlt ctx (Exact.R0 ctx) (Exact.Ropp ctx x) := by
      have h := ctx.certificate.orderedField.add_lt_compat_l
        (Exact.Ropp ctx x) x (Exact.R0 ctx) hx
      change ctx.spec.lt (ctx.spec.add (ctx.spec.neg x) x)
        (ctx.spec.add (ctx.spec.neg x) ctx.spec.zero) at h
      rw [ctx.certificate.orderedField.neg_add_cancel,
        ctx.certificate.orderedField.add_zero] at h
      exact h
    have hformat' : ¬ format ctx magnitude beta fexp (Exact.Ropp ctx x) := by
      intro h
      apply hformat
      have hh := CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_opp
        ctx magnitude beta fexp (Exact.Ropp ctx x) h
      simpa only [hnegneg x] using hh
    have hcanon_opp : ∀ (m e : Z),
        canonical ctx magnitude beta fexp (Defs.float.Float beta m e) →
          canonical ctx magnitude beta fexp (Defs.float.Float beta (Zaux.Zopp m) e) := by
      intro m e hc
      unfold canonical at hc ⊢
      change e = CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp
        (Exact.F2R ctx (Defs.float.Float beta (Zaux.Zopp m) e))
      have hf := CompCert4Lean.Flocq.Core.Float_prop.F2R_Zopp ctx beta m e
      change Exact.F2R ctx (Defs.float.Float beta (Zaux.Zopp m) e) =
        Exact.Ropp ctx (Exact.F2R ctx (Defs.float.Float beta m e)) at hf
      have hce : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp
          (Exact.Ropp ctx (Exact.F2R ctx (Defs.float.Float beta m e))) =
          CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp
            (Exact.F2R ctx (Defs.float.Float beta m e)) := by
        unfold CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp
        exact congrArg fexp
          (CompCert4Lean.Flocq.Core.Raux.mag_opp ctx magnitude beta
            (Exact.F2R ctx (Defs.float.Float beta m e)))
      rw [hf, hce]
      exact hc
    cases xd with
    | Float md ed =>
      cases xu with
      | Float mu eu =>
        have hcd := hcanon_opp mu eu hx_u
        have hcu := hcanon_opp md ed hx_d
        have hxd' : Exact.F2R ctx (Defs.float.Float beta (Zaux.Zopp mu) eu) =
            Exact.round ctx magnitude beta fexp (Exact.Zfloor ctx) (Exact.Ropp ctx x) := by
          have hr := CompCert4Lean.Flocq.Core.Generic_fmt.round_opp
            ctx magnitude beta fexp (Exact.Zfloor ctx) x
          have hfd : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zrnd_opp ctx (Exact.Zfloor ctx) = Exact.Zceil ctx := by
            funext y
            rfl
          rw [hfd] at hr
          calc
            Exact.F2R ctx (Defs.float.Float beta (Zaux.Zopp mu) eu) =
                Exact.Ropp ctx (Exact.F2R ctx (Defs.float.Float beta mu eu)) :=
              CompCert4Lean.Flocq.Core.Float_prop.F2R_Zopp ctx beta mu eu
            _ = Exact.Ropp ctx (Exact.round ctx magnitude beta fexp
                (Exact.Zceil ctx) x) := by rw [hxu]
            _ = Exact.round ctx magnitude beta fexp (Exact.Zfloor ctx)
                (Exact.Ropp ctx x) := hr.symm
        have hxu' : Exact.F2R ctx (Defs.float.Float beta (Zaux.Zopp md) ed) =
            Exact.round ctx magnitude beta fexp (Exact.Zceil ctx) (Exact.Ropp ctx x) := by
          have hr := CompCert4Lean.Flocq.Core.Generic_fmt.round_UP_opp
            ctx magnitude beta fexp x
          calc
            Exact.F2R ctx (Defs.float.Float beta (Zaux.Zopp md) ed) =
                Exact.Ropp ctx (Exact.F2R ctx (Defs.float.Float beta md ed)) :=
              CompCert4Lean.Flocq.Core.Float_prop.F2R_Zopp ctx beta md ed
            _ = Exact.Ropp ctx (Exact.round ctx magnitude beta fexp
                (Exact.Zfloor ctx) x) := by rw [hxd]
            _ = Exact.round ctx magnitude beta fexp (Exact.Zceil ctx)
                (Exact.Ropp ctx x) := hr.symm
        have hp := hpos (Exact.Ropp ctx x)
          (Defs.float.Float beta (Zaux.Zopp mu) eu)
          (Defs.float.Float beta (Zaux.Zopp md) ed)
          hxpos hformat' hcd hcu hxd' hxu'
        have hp2 := congrArg Bool.not hp.symm
        simp only [Defs.Fnum] at hp2 ⊢
        change Bool.not (Bool.not (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp mu))) =
          Bool.not (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp md)) at hp2
        rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even_opp md,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even_opp mu] at hp2
        simpa only [Bool.not_not] using hp2

end CompCert4Lean.Flocq.Core.Round_NE

namespace CompCert4Lean.Flocq.Core.Round_NE

open CompCert4Lean.Flocq.Core

theorem round_NE_opp :
    ∀ (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx),
      round_NE_oppStatement ctx magnitude := by
  intro ctx magnitude beta fexp x
  have hchoice :
      (fun t : Z => Bool.not (Bool.not (Zeven (Zaux.Zopp (Zadd t Zone))))) =
        (fun t : Z => Bool.not (Zeven t)) := by
    funext t
    simp only [Bool.not_not]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add t Zone)) =
      Bool.not (Zeven t)
    rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even_opp,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even_add]
    change CompCert4Lean.Foundation.Logic.Rocq.Coq.Bool.Bool.eqb
      (Zeven t) false = Bool.not (Zeven t)
    cases Zeven t <;> rfl
  have h := Generic_fmt.round_N_opp ctx magnitude beta fexp
    (fun t => Bool.not (Zeven t)) x
  rw [hchoice] at h
  exact h

end CompCert4Lean.Flocq.Core.Round_NE

namespace CompCert4Lean.Flocq.Core.Round_NE

theorem round_NE_abs :
    ∀ ctx magnitude, round_NE_absStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x
  have hround_nonpos : ∀ y : Exact.R ctx, ctx.spec.le y ctx.spec.zero →
      Generic_fmt.Exact.Rle ctx (Exact.round ctx magnitude beta fexp (Exact.ZnearestE ctx) y)
        (Exact.R0 ctx) := by
    intro y hy
    have hpow : Generic_fmt.Exact.Rle ctx (Generic_fmt.Exact.IZR ctx Zaux.Z0)
        (Exact.bpow ctx beta
          (Zaux.Zopp (Generic_fmt.Exact.cexp ctx magnitude beta fexp y))) := by
      change ctx.spec.le (ctx.spec.ofZ Zaux.Z0)
        (Exact.bpow ctx beta
          (Zaux.Zopp (Generic_fmt.Exact.cexp ctx magnitude beta fexp y)))
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact CompCert4Lean.Flocq.Core.Raux.bpow_ge_0 ctx beta _
    have hmul :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
        ctx (Exact.bpow ctx beta
          (Zaux.Zopp (Generic_fmt.Exact.cexp ctx magnitude beta fexp y)))
        y ctx.spec.zero hpow hy
    have hscaled : ctx.spec.le
        (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp y) ctx.spec.zero := by
      change ctx.spec.le
        (ctx.spec.mul y (Exact.bpow ctx beta
          (Zaux.Zopp (Generic_fmt.Exact.cexp ctx magnitude beta fexp y))))
        (ctx.spec.mul ctx.spec.zero (Exact.bpow ctx beta
          (Zaux.Zopp (Generic_fmt.Exact.cexp ctx magnitude beta fexp y)))) at hmul
      rw [ctx.certificate.orderedField.zero_mul] at hmul
      exact hmul
    have hn := Generic_fmt.Znearest_le_ceil ctx
      (fun m => Bool.not (Zeven m))
      (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp y)
    have hc := CompCert4Lean.Flocq.Core.Raux.Zceil_le ctx
      (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp y)
      (Exact.R0 ctx) hscaled
    have hz : Exact.Zceil ctx (Exact.R0 ctx) = Zaux.Z0 := by
      rw [show Exact.R0 ctx = Generic_fmt.Exact.IZR ctx Zaux.Z0 by
        exact ctx.certificate.sourceLaws.ofZ_zero.symm]
      exact CompCert4Lean.Flocq.Core.Raux.Zceil_IZR ctx Zaux.Z0
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Exact.Zceil ctx
          (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp y)) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Exact.Zceil ctx (Exact.R0 ctx)) at hc
    have hc0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Exact.Zceil ctx (Exact.R0 ctx)) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zaux.Z0 :=
      congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hz
    rw [hc0] at hc
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Generic_fmt.Exact.Znearest ctx (fun m => Bool.not (Zeven m))
          (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp y)) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Exact.Zceil ctx
          (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp y)) at hn
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Exact.Zceil ctx
          (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp y)) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zaux.Z0 at hc
    have hnear : Zle
        (Generic_fmt.Exact.Znearest ctx (fun m => Bool.not (Zeven m))
          (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp y)) Zaux.Z0 := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Generic_fmt.Exact.Znearest ctx (fun m => Bool.not (Zeven m))
            (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp y)) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zaux.Z0
      omega
    unfold Exact.round
    have hf := CompCert4Lean.Flocq.Core.Float_prop.F2R_le ctx beta
      (Generic_fmt.Exact.Znearest ctx (fun m => Bool.not (Zeven m))
        (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp y)) Zaux.Z0
      (Generic_fmt.Exact.cexp ctx magnitude beta fexp y) hnear
    rw [CompCert4Lean.Flocq.Core.Float_prop.F2R_0 ctx beta] at hf
    exact hf
  have hround_nonneg : ∀ y : Exact.R ctx, ctx.spec.le ctx.spec.zero y →
      Generic_fmt.Exact.Rle ctx (Exact.R0 ctx)
        (Exact.round ctx magnitude beta fexp (Exact.ZnearestE ctx) y) := by
    intro y hy
    have hpow : Generic_fmt.Exact.Rle ctx (Generic_fmt.Exact.IZR ctx Zaux.Z0)
        (Exact.bpow ctx beta
          (Zaux.Zopp (Generic_fmt.Exact.cexp ctx magnitude beta fexp y))) := by
      change ctx.spec.le (ctx.spec.ofZ Zaux.Z0)
        (Exact.bpow ctx beta
          (Zaux.Zopp (Generic_fmt.Exact.cexp ctx magnitude beta fexp y)))
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact CompCert4Lean.Flocq.Core.Raux.bpow_ge_0 ctx beta _
    have hmul :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
        ctx (Exact.bpow ctx beta
          (Zaux.Zopp (Generic_fmt.Exact.cexp ctx magnitude beta fexp y)))
        ctx.spec.zero y hpow hy
    have hscaled : ctx.spec.le ctx.spec.zero
        (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp y) := by
      change ctx.spec.le
        (ctx.spec.mul ctx.spec.zero (Exact.bpow ctx beta
          (Zaux.Zopp (Generic_fmt.Exact.cexp ctx magnitude beta fexp y))))
        (ctx.spec.mul y (Exact.bpow ctx beta
          (Zaux.Zopp (Generic_fmt.Exact.cexp ctx magnitude beta fexp y)))) at hmul
      rw [ctx.certificate.orderedField.zero_mul] at hmul
      exact hmul
    have hn := Generic_fmt.Znearest_ge_floor ctx
      (fun m => Bool.not (Zeven m))
      (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp y)
    have hc := CompCert4Lean.Flocq.Core.Raux.Zfloor_le ctx (Exact.R0 ctx)
      (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp y) hscaled
    have hz : Exact.Zfloor ctx (Exact.R0 ctx) = Zaux.Z0 := by
      rw [show Exact.R0 ctx = Generic_fmt.Exact.IZR ctx Zaux.Z0 by
        exact ctx.certificate.sourceLaws.ofZ_zero.symm]
      exact CompCert4Lean.Flocq.Core.Raux.Zfloor_IZR ctx Zaux.Z0
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Exact.Zfloor ctx (Exact.R0 ctx)) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Exact.Zfloor ctx
          (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp y)) at hc
    have hc0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Exact.Zfloor ctx (Exact.R0 ctx)) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zaux.Z0 :=
      congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hz
    rw [hc0] at hc
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zaux.Z0 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Exact.Zfloor ctx
          (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp y)) at hc
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Exact.Zfloor ctx
          (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp y)) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Generic_fmt.Exact.Znearest ctx (fun m => Bool.not (Zeven m))
          (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp y)) at hn
    have hnear : Zle Zaux.Z0
        (Generic_fmt.Exact.Znearest ctx (fun m => Bool.not (Zeven m))
          (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp y)) := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zaux.Z0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Generic_fmt.Exact.Znearest ctx (fun m => Bool.not (Zeven m))
            (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp y))
      omega
    unfold Exact.round
    have hf := CompCert4Lean.Flocq.Core.Float_prop.F2R_le ctx beta Zaux.Z0
      (Generic_fmt.Exact.Znearest ctx (fun m => Bool.not (Zeven m))
        (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp y))
      (Generic_fmt.Exact.cexp ctx magnitude beta fexp y) hnear
    rw [CompCert4Lean.Flocq.Core.Float_prop.F2R_0 ctx beta] at hf
    exact hf
  have hzero : Exact.Rabs ctx (Exact.R0 ctx) = Exact.R0 ctx := by
    exact ctx.certificate.sourceLaws.abs_nonnegative _
      (ctx.certificate.orderedField.le_refl _)
  have hnear_zero : Generic_fmt.Exact.Znearest ctx (fun m => Bool.not (Zeven m))
      (Exact.R0 ctx) = Zaux.Z0 := by
    rw [show Exact.R0 ctx = Generic_fmt.Exact.IZR ctx Zaux.Z0 by
      exact ctx.certificate.sourceLaws.ofZ_zero.symm]
    rcases Generic_fmt.Znearest_DN_or_UP ctx (fun m => Bool.not (Zeven m))
      (Generic_fmt.Exact.IZR ctx Zaux.Z0) with h | h
    · rw [h]
      exact CompCert4Lean.Flocq.Core.Raux.Zfloor_IZR ctx Zaux.Z0
    · rw [h]
      exact CompCert4Lean.Flocq.Core.Raux.Zceil_IZR ctx Zaux.Z0
  have hround_zero :
      Exact.round ctx magnitude beta fexp (Exact.ZnearestE ctx) (Exact.R0 ctx) =
        Exact.R0 ctx := by
    unfold Exact.round
    change Generic_fmt.Exact.F2R ctx
        (Defs.float.Float beta
          (Generic_fmt.Exact.Znearest ctx (fun m => Bool.not (Zeven m))
            (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp (Exact.R0 ctx)))
          (Generic_fmt.Exact.cexp ctx magnitude beta fexp (Exact.R0 ctx))) =
      Exact.R0 ctx
    rw [Generic_fmt.scaled_mantissa_0 ctx magnitude beta fexp, hnear_zero]
    exact CompCert4Lean.Flocq.Core.Float_prop.F2R_0 ctx beta _
  rcases ctx.certificate.total_order x (Exact.R0 ctx) with hx | hx
  · rcases hx with hxlt | hxeq
    · have hxle : Generic_fmt.Exact.Rle ctx x (Exact.R0 ctx) :=
        (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxlt |>.1
      have hxle' : CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle ctx.spec x
          (Generic_fmt.Exact.IZR ctx Zaux.Z0) := by
        change ctx.spec.le x (ctx.spec.ofZ Zaux.Z0)
        rw [ctx.certificate.sourceLaws.ofZ_zero]
        exact hxle
      have habsx : Exact.Rabs ctx x = Exact.Ropp ctx x :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rbasic_fun.Rabs_left1
          ctx x hxle'
      have hroundopp := round_NE_opp ctx magnitude beta fexp x
      have hroundle := hround_nonpos x hxle
      have hroundle' : CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle ctx.spec
          (Exact.round ctx magnitude beta fexp (Exact.ZnearestE ctx) x)
          (Generic_fmt.Exact.IZR ctx Zaux.Z0) := by
        change ctx.spec.le
          (Exact.round ctx magnitude beta fexp (Exact.ZnearestE ctx) x)
          (ctx.spec.ofZ Zaux.Z0)
        rw [ctx.certificate.sourceLaws.ofZ_zero]
        exact hroundle
      calc
        Exact.round ctx magnitude beta fexp (Exact.ZnearestE ctx)
            (Exact.Rabs ctx x) =
            Exact.round ctx magnitude beta fexp (Exact.ZnearestE ctx)
              (Exact.Ropp ctx x) := by rw [habsx]
        _ = Exact.Ropp ctx
            (Exact.round ctx magnitude beta fexp (Exact.ZnearestE ctx) x) := hroundopp
        _ = Exact.Rabs ctx
          (Exact.round ctx magnitude beta fexp (Exact.ZnearestE ctx) x) :=
          (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rbasic_fun.Rabs_left1
            ctx _ hroundle').symm
    · subst x
      rw [hzero, hround_zero, hzero]
  · have hxle : Generic_fmt.Exact.Rle ctx (Exact.R0 ctx) x :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hx |>.1
    have hxle' : CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle ctx.spec
        (Generic_fmt.Exact.IZR ctx Zaux.Z0) x := by
      change ctx.spec.le (ctx.spec.ofZ Zaux.Z0) x
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact hxle
    have habsx : Exact.Rabs ctx x = x :=
      ctx.certificate.sourceLaws.abs_nonnegative x hxle
    have hroundge := hround_nonneg x hxle
    have hroundge' : CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle ctx.spec
        (Generic_fmt.Exact.IZR ctx Zaux.Z0)
        (Exact.round ctx magnitude beta fexp (Exact.ZnearestE ctx) x) := by
      change ctx.spec.le (ctx.spec.ofZ Zaux.Z0)
        (Exact.round ctx magnitude beta fexp (Exact.ZnearestE ctx) x)
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact hroundge
    have habsr : Exact.Rabs ctx
        (Exact.round ctx magnitude beta fexp (Exact.ZnearestE ctx) x) =
      Exact.round ctx magnitude beta fexp (Exact.ZnearestE ctx) x :=
      ctx.certificate.sourceLaws.abs_nonnegative _ hroundge
    rw [habsx, habsr]

end CompCert4Lean.Flocq.Core.Round_NE
