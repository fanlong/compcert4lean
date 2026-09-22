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

namespace CompCert4Lean.Flocq.Core.Round_NE

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals

private theorem parity_sub_nonneg (left right : Z) (bound : Zle left right) :
    Zaux.Zle Zaux.Z0 (Zaux.Zsub right left) := by
  change intOfZ left ≤ intOfZ right at bound
  change (0 : Int) ≤ intOfZ (Zaux.Zsub right left)
  simp only [Zaux.Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
  omega

private theorem parity_sub_pos (left right : Z) (bound : Zlt left right) :
    Zaux.Zlt Zaux.Z0 (Zaux.Zsub right left) := by
  change intOfZ left < intOfZ right at bound
  change (0 : Int) < intOfZ (Zaux.Zsub right left)
  simp only [Zaux.Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
  omega

private theorem parity_successor (mantissa : Z) :
    Zeven (Zadd mantissa Zone) = Bool.not (Zeven mantissa) := by
  have addition := ZArith.BinInt.Z.even_add mantissa Zone
  change Zeven (Zadd mantissa Zone) =
    CompCert4Lean.Foundation.Logic.Rocq.Coq.Bool.Bool.eqb (Zeven mantissa) false at addition
  rw [addition]
  cases Zeven mantissa <;> rfl

private theorem parity_power_representation (ctx : ExactRealContext) (beta : radix)
    (exponent target : Z) (bound : Zle target exponent) :
    Exact.F2R ctx (Defs.float.Float beta
      (Zaux.Zpower (beta : Z) (Zaux.Zsub exponent target)) target) =
        Exact.bpow ctx beta exponent := by
  have change_exp := Float_prop.F2R_change_exp ctx beta target Zone exponent bound
  change Exact.F2R ctx (Defs.float.Float beta Zone exponent) =
    Exact.F2R ctx (Defs.float.Float beta
      (Zaux.Zmul Zone (Zaux.Zpower (beta : Z) (Zaux.Zsub exponent target))) target) at change_exp
  have one_mul : Zaux.Zmul Zone
      (Zaux.Zpower (beta : Z) (Zaux.Zsub exponent target)) =
        Zaux.Zpower (beta : Z) (Zaux.Zsub exponent target) := by
    apply intOfZ_injective
    simp only [Zaux.Zmul, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    change 1 * _ = _
    omega
  rw [one_mul] at change_exp
  exact change_exp.symm.trans (Float_prop.F2R_bpow ctx beta exponent)

private theorem parity_canonical_power (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx) (beta : radix) (fexp : Z → Z)
    (exponent : Z) (value : Defs.float beta)
    (canonical_value : canonical ctx magnitude beta fexp value)
    (value_eq : Exact.F2R ctx value = Exact.bpow ctx beta exponent)
    (bound : Zle (fexp (Zadd exponent Zone)) exponent) :
    Defs.Fnum value = Zaux.Zpower (beta : Z)
      (Zaux.Zsub exponent (fexp (Zadd exponent Zone))) := by
  rcases value with ⟨mantissa, storedExponent⟩
  change storedExponent = fexp
    (Generic_fmt.Exact.mag magnitude beta
      (Exact.F2R ctx (Defs.float.Float beta mantissa storedExponent))) at canonical_value
  have power_mag : Generic_fmt.Exact.mag magnitude beta (Exact.bpow ctx beta exponent) =
      Zadd exponent Zone := Raux.mag_bpow ctx magnitude beta exponent
  rw [value_eq, power_mag] at canonical_value
  subst storedExponent
  exact Float_prop.eq_F2R ctx beta (fexp (Zadd exponent Zone)) mantissa _
    (value_eq.trans (parity_power_representation ctx beta exponent _ bound).symm)

theorem DN_UP_parity_generic_pos :
    ∀ ctx magnitude, DN_UP_parity_generic_posStatement ctx magnitude := by
  intro ctx magnitude beta fexp valid nearest value lower upper
    positive not_format canonical_lower canonical_upper lower_round upper_round
  rcases lower with ⟨lowerMantissa, lowerExponent⟩
  rcases upper with ⟨upperMantissa, upperExponent⟩
  change Zeven upperMantissa = Bool.not (Zeven lowerMantissa)
  let exponent := Generic_fmt.Exact.mag magnitude beta value
  have nonzero : value ≠ Exact.R0 ctx := by
    intro equality
    rw [equality] at positive
    exact ctx.certificate.orderedField.lt_irrefl _ positive
  have nonnegative := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp positive |>.1
  have bounds := (Raux.Exact.mag magnitude beta value).mag_bound nonzero
  change Generic_fmt.Exact.Rle ctx (Exact.bpow ctx beta (Zaux.Zsub exponent Zone))
      (Exact.Rabs ctx value) ∧
    Exact.Rlt ctx (Exact.Rabs ctx value) (Exact.bpow ctx beta exponent) at bounds
  have abs_value : Exact.Rabs ctx value = value :=
    ctx.certificate.sourceLaws.abs_nonnegative value nonnegative
  rw [abs_value] at bounds
  change Generic_fmt.Exact.Rle ctx (Exact.bpow ctx beta (Zaux.Zsub exponent Zone)) value ∧
    Exact.Rlt ctx value (Exact.bpow ctx beta exponent) at bounds
  by_cases small : Zle exponent (fexp exponent)
  · have lower_zero : lowerMantissa = Zaux.Z0 :=
      Float_prop.eq_0_F2R ctx beta lowerMantissa lowerExponent
        (lower_round.trans (Generic_fmt.round_DN_small_pos ctx magnitude beta fexp
          value exponent bounds small))
    have exponent_bound := ((valid.valid_exp exponent).2 small).1
    have upper_power := parity_canonical_power ctx magnitude beta fexp (fexp exponent)
      (Defs.float.Float beta upperMantissa upperExponent) canonical_upper
      (upper_round.trans (Generic_fmt.round_UP_small_pos ctx magnitude beta fexp
        value exponent bounds small)) exponent_bound
    change upperMantissa = _ at upper_power
    rw [lower_zero, upper_power]
    change Zeven (Zaux.Zpower (beta : Z)
      (Zaux.Zsub (fexp exponent) (fexp (Zadd (fexp exponent) Zone)))) = false
    rcases nearest.exists_NE with odd | stable
    · exact Zaux.Zeven_Zpower_odd _ _ (parity_sub_nonneg _ _ exponent_bound) odd
    · rw [(stable exponent).2 small]
      have difference : Zaux.Zsub (fexp exponent) (fexp exponent) = Zaux.Z0 := by
        apply intOfZ_injective
        simp only [Zaux.Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
        change _ - _ = 0
        omega
      rw [difference]
      have power_zero : Zaux.Zpower (beta : Z) Zaux.Z0 = Zone := by
        apply intOfZ_injective
        change intOfZ (zOfInt (Int.pow (intOfZ (beta : Z)) 0)) = 1
        rw [intOfZ_zOfInt]
        cases intOfZ (beta : Z) <;> simp [Int.pow]
      rw [power_zero]
      rfl
  · have large : Zlt (fexp exponent) exponent := by
      change ¬ intOfZ exponent ≤ intOfZ (fexp exponent) at small
      change intOfZ (fexp exponent) < intOfZ exponent
      omega
    have valid_floor : Generic_fmt.Exact.Valid_rnd ctx (Exact.Zfloor ctx) :=
      ⟨Raux.Zfloor_le ctx, Raux.Zfloor_IZR ctx⟩
    have valid_ceil : Generic_fmt.Exact.Valid_rnd ctx (Exact.Zceil ctx) :=
      ⟨Raux.Zceil_le ctx, Raux.Zceil_IZR ctx⟩
    have lower_bounds := Generic_fmt.round_bounded_large_pos ctx magnitude beta fexp
      (Exact.Zfloor ctx) valid_floor value exponent large bounds
    have upper_bounds := Generic_fmt.round_bounded_large_pos ctx magnitude beta fexp
      (Exact.Zceil ctx) valid_ceil value exponent large bounds
    have lower_le := (Generic_fmt.round_DN_pt ctx magnitude beta fexp valid value).2.1
    have value_le := (Generic_fmt.round_UP_pt ctx magnitude beta fexp valid value).2.1
    have lower_mag : Generic_fmt.Exact.mag magnitude beta
        (Exact.round ctx magnitude beta fexp (Exact.Zfloor ctx) value) = exponent :=
      Raux.mag_unique_pos ctx magnitude beta
        (Exact.round ctx magnitude beta fexp (Exact.Zfloor ctx) value) exponent
        ⟨lower_bounds.1, RIneq.Rle_lt_trans ctx _ _ _ lower_le bounds.2⟩
    change lowerExponent = fexp
      (Generic_fmt.Exact.mag magnitude beta
        (Exact.F2R ctx (Defs.float.Float beta lowerMantissa lowerExponent))) at canonical_lower
    rw [lower_round, lower_mag] at canonical_lower
    subst lowerExponent
    have lower_mantissa : lowerMantissa = Exact.Zfloor ctx
        (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp value) :=
      Float_prop.eq_F2R ctx beta (fexp exponent) _ _ lower_round
    have ceil_floor : Exact.Zceil ctx
        (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp value) =
        Zadd (Exact.Zfloor ctx
          (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp value)) Zone := by
      apply Raux.Zceil_floor_neq ctx
      intro scaled_eq
      change Generic_fmt.Exact.IZR ctx (Exact.Zfloor ctx
          (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp value)) =
        Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp value at scaled_eq
      have rounded_eq :
          Exact.round ctx magnitude beta fexp (Exact.Zfloor ctx) value = value := by
        change Generic_fmt.Exact.Rmult ctx
          (Generic_fmt.Exact.IZR ctx (Exact.Zfloor ctx
            (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp value)))
          (Exact.bpow ctx beta (Generic_fmt.Exact.cexp ctx magnitude beta fexp value)) = value
        rw [scaled_eq]
        exact Generic_fmt.scaled_mantissa_mult_bpow ctx magnitude beta fexp value
      apply not_format
      rw [← rounded_eq]
      exact (Generic_fmt.round_DN_pt ctx magnitude beta fexp valid value).1
    by_cases boundary : Exact.round ctx magnitude beta fexp (Exact.Zceil ctx) value =
        Exact.bpow ctx beta exponent
    · have upper_exponent_bound := (valid.valid_exp exponent).1 large
      have upper_power := parity_canonical_power ctx magnitude beta fexp exponent
        (Defs.float.Float beta upperMantissa upperExponent) canonical_upper
        (upper_round.trans boundary) upper_exponent_bound
      have lower_exponent_bound : Zle (fexp exponent) exponent := by
        change intOfZ (fexp exponent) < intOfZ exponent at large
        change intOfZ (fexp exponent) ≤ intOfZ exponent
        omega
      have ceiling_power : Exact.Zceil ctx
          (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp value) =
          Zaux.Zpower (beta : Z) (Zaux.Zsub exponent (fexp exponent)) :=
        Float_prop.eq_F2R ctx beta (fexp exponent) _ _
          (boundary.trans
            (parity_power_representation ctx beta exponent _ lower_exponent_bound).symm)
      have next_power : Zadd lowerMantissa Zone =
          Zaux.Zpower (beta : Z) (Zaux.Zsub exponent (fexp exponent)) := by
        rw [lower_mantissa, ← ceil_floor]
        exact ceiling_power
      have lower_parity := parity_successor lowerMantissa
      rw [next_power] at lower_parity
      change upperMantissa = _ at upper_power
      rw [upper_power, ← lower_parity]
      rcases nearest.exists_NE with odd | stable
      · exact (Zaux.Zeven_Zpower_odd _ _
          (parity_sub_nonneg _ _ upper_exponent_bound) odd).trans
          (Zaux.Zeven_Zpower_odd _ _
          (parity_sub_nonneg _ _ lower_exponent_bound) odd).symm
      · exact (ZArith.BinInt.Z.even_pow _ _
          (parity_sub_pos _ _ ((stable exponent).1 large))).trans
          (ZArith.BinInt.Z.even_pow _ _ (parity_sub_pos _ _ large)).symm
    · have upper_lt : Exact.Rlt ctx
          (Exact.round ctx magnitude beta fexp (Exact.Zceil ctx) value)
          (Exact.bpow ctx beta exponent) := by
        apply (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
        refine ⟨upper_bounds.2, ?_⟩
        intro reverse
        exact boundary (ctx.certificate.orderedField.le_antisymm _ _ upper_bounds.2 reverse)
      have upper_mag : Generic_fmt.Exact.mag magnitude beta
          (Exact.round ctx magnitude beta fexp (Exact.Zceil ctx) value) = exponent :=
        Raux.mag_unique_pos ctx magnitude beta
          (Exact.round ctx magnitude beta fexp (Exact.Zceil ctx) value) exponent
          ⟨ctx.certificate.orderedField.le_trans _ _ _ bounds.1 value_le, upper_lt⟩
      change upperExponent = fexp
        (Generic_fmt.Exact.mag magnitude beta
          (Exact.F2R ctx (Defs.float.Float beta upperMantissa upperExponent))) at canonical_upper
      rw [upper_round, upper_mag] at canonical_upper
      subst upperExponent
      have upper_mantissa : upperMantissa = Exact.Zceil ctx
          (Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp value) :=
        Float_prop.eq_F2R ctx beta (fexp exponent) _ _ upper_round
      rw [upper_mantissa, ceil_floor, ← lower_mantissa]
      exact parity_successor lowerMantissa

end CompCert4Lean.Flocq.Core.Round_NE

namespace CompCert4Lean.Flocq.Core.Round_NE

theorem DN_UP_parity_generic :
    ∀ ctx magnitude, DN_UP_parity_genericStatement ctx magnitude := by
  intro ctx magnitude beta fexp valid nearest
  exact DN_UP_parity_aux ctx magnitude beta fexp
    (DN_UP_parity_generic_pos ctx magnitude beta fexp valid nearest)

end CompCert4Lean.Flocq.Core.Round_NE
