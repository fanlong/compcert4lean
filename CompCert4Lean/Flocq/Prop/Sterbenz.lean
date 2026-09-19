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

namespace CompCert4Lean.Flocq.Prop.Sterbenz

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.Core.Generic_fmt

private theorem sterbenz_generic_format_zero (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx) (beta : radix) (fexp : Z → Z) :
    Exact.generic_format ctx magnitude beta fexp (Exact.R0 ctx) := by
  unfold Exact.generic_format
  rw [scaled_mantissa_0 ctx magnitude beta fexp]
  have hz : Exact.Ztrunc ctx (Exact.R0 ctx) = Z0 := by
    rw [show Exact.R0 ctx = Exact.IZR ctx Z0 by
      exact ctx.certificate.sourceLaws.ofZ_zero.symm]
    exact CompCert4Lean.Flocq.Core.Raux.Ztrunc_IZR ctx Z0
  rw [hz]
  exact (CompCert4Lean.Flocq.Core.Float_prop.F2R_0 ctx beta
    (Exact.cexp ctx magnitude beta fexp (Exact.R0 ctx))).symm

private theorem sterbenz_generic_format_F2R (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx) (beta : radix) (fexp : Z → Z)
    (x : ExactR ctx) (f : float beta) (hfx : Exact.F2R ctx f = x)
    (hx : x = Exact.R0 ctx ∨
      Zle (Exact.cexp ctx magnitude beta fexp x) (Fexp f)) :
    Exact.generic_format ctx magnitude beta fexp x := by
  rcases hx with hx0 | hle
  · rw [hx0]
    exact sterbenz_generic_format_zero ctx magnitude beta fexp
  · cases f with
    | Float m e =>
        let e' := Exact.cexp ctx magnitude beta fexp x
        let m' := Zmul m
          (CompCert4Lean.Flocq.Core.Raux.Zpower (beta : Z)
            (Zsub e e'))
        have hchange :
            Exact.F2R ctx (Float beta m e) =
              Exact.F2R ctx (Float beta m' e') := by
          dsimp [m', e']
          exact CompCert4Lean.Flocq.Core.Float_prop.F2R_change_exp ctx
            beta e' m e hle
        have hxe : Exact.F2R ctx (Float beta m' e') = x := by
          exact hchange.symm.trans hfx
        have hcanon : Exact.canonical ctx magnitude beta fexp
            (Float beta m' e') := by
          unfold Exact.canonical
          change e' = Exact.cexp ctx magnitude beta fexp
            (Exact.F2R ctx (Float beta m' e'))
          rw [hxe]
        rw [← hxe]
        exact generic_format_canonical ctx magnitude beta fexp
          (Float beta m' e') hcanon

private theorem sterbenz_f2r_plus (ctx : ExactRealContext) (beta : radix)
    (m1 e1 m2 e2 : Z) :
    ∃ (m e : Z), e = Zmin e1 e2 ∧
      Exact.F2R ctx (Float beta m e) =
        Exact.Rplus ctx (Exact.F2R ctx (Float beta m1 e1))
          (Exact.F2R ctx (Float beta m2 e2)) := by
  by_cases hle : Zle e1 e2
  · let k := Zmul m2
      (CompCert4Lean.Flocq.Core.Raux.Zpower (beta : Z) (Zsub e2 e1))
    have hchange := CompCert4Lean.Flocq.Core.Float_prop.F2R_change_exp
      ctx beta e1 m2 e2 hle
    have hchange' :
        ctx.spec.mul (ctx.spec.ofZ m2)
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2) =
          ctx.spec.mul (ctx.spec.ofZ k)
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1) := by
      change Exact.F2R ctx (Float beta m2 e2) =
        Exact.F2R ctx (Float beta k e1) at hchange
      exact hchange
    refine ⟨Zadd m1 k, e1, ?_, ?_⟩
    · exact (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.min_l
        e1 e2 hle).symm
    · change ctx.spec.mul (ctx.spec.ofZ (Zadd m1 k))
          (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1) =
        ctx.spec.add
          (ctx.spec.mul (ctx.spec.ofZ m1)
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1))
          (ctx.spec.mul (ctx.spec.ofZ m2)
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2))
      rw [ctx.certificate.sourceLaws.ofZ_add]
      calc
        ctx.spec.mul (ctx.spec.add (ctx.spec.ofZ m1) (ctx.spec.ofZ k))
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1) =
          ctx.spec.mul (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1)
            (ctx.spec.add (ctx.spec.ofZ m1) (ctx.spec.ofZ k)) :=
          ctx.certificate.orderedField.mul_comm _ _
        _ = ctx.spec.add
            (ctx.spec.mul (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1)
              (ctx.spec.ofZ m1))
            (ctx.spec.mul (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1)
              (ctx.spec.ofZ k)) :=
          ctx.certificate.orderedField.left_distrib _ _ _
        _ = ctx.spec.add
            (ctx.spec.mul (ctx.spec.ofZ m1)
              (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1))
            (ctx.spec.mul (ctx.spec.ofZ m2)
              (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2)) := by
          rw [ctx.certificate.orderedField.mul_comm
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1)
            (ctx.spec.ofZ m1)]
          rw [ctx.certificate.orderedField.mul_comm
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1)
            (ctx.spec.ofZ k)]
          exact congrArg
            (fun t => ctx.spec.add
              (ctx.spec.mul (ctx.spec.ofZ m1)
                (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1)) t)
            hchange'.symm

  · have hle : Zle e2 e1 := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1
      change ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 at hle
      exact Int.le_of_lt (Int.lt_of_not_ge hle)
    let k := Zmul m1
      (CompCert4Lean.Flocq.Core.Raux.Zpower (beta : Z) (Zsub e1 e2))
    have hchange := CompCert4Lean.Flocq.Core.Float_prop.F2R_change_exp
      ctx beta e2 m1 e1 hle
    have hchange' :
        ctx.spec.mul (ctx.spec.ofZ m1)
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1) =
          ctx.spec.mul (ctx.spec.ofZ k)
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2) := by
      change Exact.F2R ctx (Float beta m1 e1) =
        Exact.F2R ctx (Float beta k e2) at hchange
      exact hchange
    refine ⟨Zadd k m2, e2, ?_, ?_⟩
    · exact (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.min_r
        e1 e2 hle).symm
    · change ctx.spec.mul (ctx.spec.ofZ (Zadd k m2))
          (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2) =
        ctx.spec.add
          (ctx.spec.mul (ctx.spec.ofZ m1)
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1))
          (ctx.spec.mul (ctx.spec.ofZ m2)
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2))
      rw [ctx.certificate.sourceLaws.ofZ_add]
      calc
        ctx.spec.mul (ctx.spec.add (ctx.spec.ofZ k) (ctx.spec.ofZ m2))
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2) =
          ctx.spec.mul (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2)
            (ctx.spec.add (ctx.spec.ofZ k) (ctx.spec.ofZ m2)) :=
          ctx.certificate.orderedField.mul_comm _ _
        _ = ctx.spec.add
            (ctx.spec.mul (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2)
              (ctx.spec.ofZ k))
            (ctx.spec.mul (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2)
              (ctx.spec.ofZ m2)) :=
          ctx.certificate.orderedField.left_distrib _ _ _
        _ = ctx.spec.add
            (ctx.spec.mul (ctx.spec.ofZ m1)
              (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1))
            (ctx.spec.mul (ctx.spec.ofZ m2)
              (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2)) := by
          rw [ctx.certificate.orderedField.mul_comm
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2)
            (ctx.spec.ofZ k)]
          rw [ctx.certificate.orderedField.mul_comm
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2)
            (ctx.spec.ofZ m2)]
          exact congrArg
            (fun t => ctx.spec.add t
              (ctx.spec.mul (ctx.spec.ofZ m2)
                (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2)))
            hchange'.symm

private theorem sterbenz_neg_neg (ctx : ExactRealContext) (x : ExactR ctx) :
    Exact.Ropp ctx (Exact.Ropp ctx x) = x := by
  change ctx.spec.neg (ctx.spec.neg x) = x
  calc
    ctx.spec.neg (ctx.spec.neg x) =
        ctx.spec.add (ctx.spec.neg (ctx.spec.neg x)) ctx.spec.zero :=
      (ctx.certificate.orderedField.add_zero _).symm
    _ = ctx.spec.add (ctx.spec.neg (ctx.spec.neg x))
        (ctx.spec.add (ctx.spec.neg x) x) := by
      rw [ctx.certificate.orderedField.neg_add_cancel]
    _ = ctx.spec.add
        (ctx.spec.add (ctx.spec.neg (ctx.spec.neg x)) (ctx.spec.neg x)) x := by
      rw [ctx.certificate.orderedField.add_assoc]
    _ = ctx.spec.add ctx.spec.zero x := by
      rw [ctx.certificate.orderedField.neg_add_cancel]
    _ = x := ctx.certificate.orderedField.zero_add _

private theorem sterbenz_generic_format_abs_inv (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx) (beta : radix) (fexp : Z → Z)
    (x : ExactR ctx)
    (hx : Exact.generic_format ctx magnitude beta fexp (Exact.Rabs ctx x)) :
    Exact.generic_format ctx magnitude beta fexp x := by
  rcases ctx.certificate.total_order x (ctx.spec.zero) with h | h
  · rcases h with hxneg | hzero
    · have habs := ctx.certificate.sourceLaws.abs_negative x hxneg
      have hneg := generic_format_opp ctx magnitude beta fexp
        (Exact.Rabs ctx x) hx
      have harg : Exact.Ropp ctx (Exact.Rabs ctx x) = x := by
        change ctx.spec.neg (ctx.spec.abs x) = x
        rw [habs]
        exact sterbenz_neg_neg ctx x
      rw [harg] at hneg
      exact hneg
    · subst x
      have harg : Exact.Rabs ctx (ctx.spec.zero) = ctx.spec.zero := by
        exact ctx.certificate.sourceLaws.abs_nonnegative _
          (ctx.certificate.orderedField.le_refl _)
      rw [harg] at hx
      exact hx
  · have hxle : ctx.spec.le ctx.spec.zero x :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1
    have harg : Exact.Rabs ctx x = x := by
      change ctx.spec.abs x = x
      exact ctx.certificate.sourceLaws.abs_nonnegative x hxle
    rw [harg] at hx
    exact hx

private theorem sterbenz_abs_ne_zero (ctx : ExactRealContext) {x : ExactR ctx}
    (hx : x ≠ Exact.R0 ctx) : Exact.Rabs ctx x ≠ Exact.R0 ctx := by
  intro hz
  rcases ctx.certificate.total_order x ctx.spec.zero with h | h
  · rcases h with hlt | heq
    · have habs := ctx.certificate.sourceLaws.abs_negative x hlt
      change ctx.spec.abs x = ctx.spec.zero at hz
      rw [habs] at hz
      have hsum := congrArg (fun z => ctx.spec.add x z) hz
      rw [ctx.certificate.orderedField.add_comm x,
        ctx.certificate.orderedField.neg_add_cancel,
        ctx.certificate.orderedField.add_zero] at hsum
      exact hx hsum.symm
    · exact hx heq
  · have hxle : ctx.spec.le ctx.spec.zero x :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1
    have habs := ctx.certificate.sourceLaws.abs_nonnegative x hxle
    change ctx.spec.abs x = ctx.spec.zero at hz
    rw [habs] at hz
    exact hx hz

private theorem sterbenz_abs_nonneg (ctx : ExactRealContext) (x : ExactR ctx) :
    Exact.Rle ctx (Exact.R0 ctx) (Exact.Rabs ctx x) := by
  change ctx.spec.le ctx.spec.zero (ctx.spec.abs x)
  rcases ctx.certificate.total_order x ctx.spec.zero with h | h
  · rcases h with hneg | hzero
    · rw [ctx.certificate.sourceLaws.abs_negative x hneg]
      rcases ctx.certificate.total_order ctx.spec.zero (ctx.spec.neg x) with h' | h'
      · rcases h' with h' | h'
        · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp h').1
        · rw [← h']
          exact ctx.certificate.orderedField.le_refl _
      · have hsum := ctx.certificate.orderedField.add_lt_compat_l x
          (ctx.spec.neg x) ctx.spec.zero h'
        rw [ctx.certificate.orderedField.add_comm x,
          ctx.certificate.orderedField.neg_add_cancel,
          ctx.certificate.orderedField.add_zero] at hsum
        exact (ctx.certificate.orderedField.lt_irrefl x
          (ctx.certificate.orderedField.lt_trans x ctx.spec.zero x hneg hsum)).elim
    · subst x
      rw [ctx.certificate.sourceLaws.abs_nonnegative _
        (ctx.certificate.orderedField.le_refl _)]
      exact ctx.certificate.orderedField.le_refl _
  · have hle : ctx.spec.le ctx.spec.zero x :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _ |>.mp h).1
    rw [ctx.certificate.sourceLaws.abs_nonnegative x hle]
    exact hle

private theorem sterbenz_mag_generic_gt (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx) (beta : radix) (fexp : Z → Z)
    (hvalid : Valid_exp fexp) (x : ExactR ctx) (hx0 : x ≠ Exact.R0 ctx)
    (hformat : Exact.generic_format ctx magnitude beta fexp x) :
    Zlt (Exact.cexp ctx magnitude beta fexp x)
      (Exact.mag magnitude beta x) := by
  have habs_fmt := generic_format_abs ctx magnitude beta fexp x hformat
  have habs0 := sterbenz_abs_ne_zero (ctx := ctx) hx0
  have hce_abs :
      Exact.cexp ctx magnitude beta fexp (Exact.Rabs ctx x) =
        Exact.cexp ctx magnitude beta fexp x := by
    unfold Exact.cexp
    change fexp
      (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta
        (Exact.Rabs ctx x)).mag_val =
      fexp
        (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_val
    exact congrArg fexp
      (CompCert4Lean.Flocq.Core.Raux.mag_abs ctx magnitude beta x)
  unfold Exact.generic_format at habs_fmt
  let m := Exact.Ztrunc ctx
    (Exact.scaled_mantissa ctx magnitude beta fexp (Exact.Rabs ctx x))
  have habs_fmt' : Exact.Rabs ctx x =
      Exact.F2R ctx (Float beta m
        (Exact.cexp ctx magnitude beta fexp x)) := by
    simpa [m, hce_abs] using habs_fmt
  have hm0 : m ≠ Z0 := by
    intro hm
    have htmp := habs_fmt'
    rw [hm] at htmp
    change Exact.Rabs ctx x = Exact.F2R ctx
      (Float beta Z0 (Exact.cexp ctx magnitude beta fexp x)) at htmp
    have hzero : Exact.F2R ctx
        (Float beta Z0 (Exact.cexp ctx magnitude beta fexp x)) =
        Exact.R0 ctx := by
      change CompCert4Lean.Flocq.Core.Raux.Exact.Rmult ctx
        (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx Z0)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta
          (Exact.cexp ctx magnitude beta fexp x)) =
        CompCert4Lean.Flocq.Core.Raux.Exact.R0 ctx
      exact CompCert4Lean.Flocq.Core.Float_prop.F2R_0 ctx beta
        (Exact.cexp ctx magnitude beta fexp x)
    rw [hzero] at htmp
    exact habs0 htmp
  have hmle : Zle Z0 m := by
    have hnonneg : Exact.Rle ctx (Exact.R0 ctx) (Exact.Rabs ctx x) :=
      sterbenz_abs_nonneg ctx x
    have hnonneg' : Exact.Rle ctx (Exact.R0 ctx)
        (Exact.F2R ctx (Float beta m
          (Exact.cexp ctx magnitude beta fexp x))) := by
      rw [← habs_fmt']
      exact hnonneg
    exact CompCert4Lean.Flocq.Core.Float_prop.ge_0_F2R ctx beta m
      (Exact.cexp ctx magnitude beta fexp x) hnonneg'
  have hmpos : Zlt Z0 m := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m
    have hmle' : (0 : Int) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m := by
      have hz0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 =
          (0 : Int) := rfl
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m at hmle
      rw [hz0] at hmle
      exact hmle
    have hmne' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m ≠ 0 := by
      intro hmz
      apply hm0
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      have hz0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 =
          (0 : Int) := rfl
      rw [← hz0] at hmz
      exact hmz
    have hz0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 =
        (0 : Int) := rfl
    rw [hz0]
    omega
  have hpow := CompCert4Lean.Flocq.Core.Float_prop.bpow_le_F2R ctx beta m
    (Exact.cexp ctx magnitude beta fexp x) hmpos
  have hpow' : Exact.Rle ctx
      (Exact.bpow ctx beta (Exact.cexp ctx magnitude beta fexp x))
      (Exact.Rabs ctx x) := by
    simpa only [habs_fmt'] using hpow
  have hpow'' : CompCert4Lean.Flocq.Core.Raux.Exact.Rle ctx
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta
        (Exact.cexp ctx magnitude beta fexp x))
      (CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x) := by
    exact hpow'
  have hgt := CompCert4Lean.Flocq.Core.Raux.mag_gt_bpow ctx magnitude beta
    x (Exact.cexp ctx magnitude beta fexp x) hpow'
  exact hgt

private theorem sterbenz_generic_format_bpow (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx) (beta : radix) (fexp : Z → Z) (e : Z)
    (h : Zle (fexp (Zadd e Zone)) e) :
    Exact.generic_format ctx magnitude beta fexp (Exact.bpow ctx beta e) := by
  have hmag := CompCert4Lean.Flocq.Core.Raux.mag_bpow ctx magnitude beta e
  have hc : Exact.cexp ctx magnitude beta fexp
      (Exact.bpow ctx beta e) = fexp (Zadd e Zone) := by
    unfold Exact.cexp
    change fexp
      (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e)).mag_val = _
    exact congrArg fexp hmag
  apply sterbenz_generic_format_F2R ctx magnitude beta fexp
    (Exact.bpow ctx beta e) (Float beta Zone e)
  · exact CompCert4Lean.Flocq.Core.Float_prop.F2R_bpow ctx beta e
  · right
    rw [hc]
    exact h

theorem generic_format_plus :
    ∀ ctx magnitude, generic_format_plusStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid hmono x y hfx hfy hxy
  by_cases hsum0 : Exact.Rplus ctx x y = Exact.R0 ctx
  · rw [hsum0]
    exact sterbenz_generic_format_zero ctx magnitude beta fexp
  by_cases hx0 : x = Exact.R0 ctx
  · subst x
    change Exact.generic_format ctx magnitude beta fexp
      (ctx.spec.add ctx.spec.zero y)
    rw [ctx.certificate.orderedField.zero_add]
    exact hfy
  by_cases hy0 : y = Exact.R0 ctx
  · subst y
    change Exact.generic_format ctx magnitude beta fexp
      (ctx.spec.add x ctx.spec.zero)
    rw [ctx.certificate.orderedField.add_zero]
    exact hfx
  let ex := Exact.mag magnitude beta x
  let ey := Exact.mag magnitude beta y
  have hfx' : x = Exact.F2R ctx (Float beta
      (Exact.Ztrunc ctx (Exact.scaled_mantissa ctx magnitude beta fexp x))
      (fexp ex)) := by
    change x = Exact.F2R ctx (Float beta
      (Exact.Ztrunc ctx (Exact.scaled_mantissa ctx magnitude beta fexp x))
      (Exact.cexp ctx magnitude beta fexp x)) at hfx
    simpa [ex, Exact.cexp] using hfx
  have hfy' : y = Exact.F2R ctx (Float beta
      (Exact.Ztrunc ctx (Exact.scaled_mantissa ctx magnitude beta fexp y))
      (fexp ey)) := by
    change y = Exact.F2R ctx (Float beta
      (Exact.Ztrunc ctx (Exact.scaled_mantissa ctx magnitude beta fexp y))
      (Exact.cexp ctx magnitude beta fexp y)) at hfy
    simpa [ey, Exact.cexp] using hfy
  obtain ⟨mxy, exy, hexy, hplus⟩ := sterbenz_f2r_plus ctx beta
    (Exact.Ztrunc ctx (Exact.scaled_mantissa ctx magnitude beta fexp x))
      (fexp ex)
    (Exact.Ztrunc ctx (Exact.scaled_mantissa ctx magnitude beta fexp y))
      (fexp ey)
  have hfeq : Zmin (fexp ex) (fexp ey) = fexp (Zmin ex ey) := by
    rcases CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zmin.Zmin_spec
        ex ey with h | h
    · calc
        Zmin (fexp ex) (fexp ey) = fexp ex :=
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.min_l
            (fexp ex) (fexp ey) (hmono.monotone_exp _ _ h.1)
        _ = fexp (Zmin ex ey) := congrArg fexp h.2.symm
    · calc
        Zmin (fexp ex) (fexp ey) = fexp ey :=
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.min_r
            (fexp ex) (fexp ey) (hmono.monotone_exp _ _ (by
              have hlt : Zlt ey ex :=
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.gt_lt
                  ex ey h.1
              change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ey ≤
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex
              change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ey <
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex at hlt
              exact Int.le_of_lt hlt))
        _ = fexp (Zmin ex ey) := congrArg fexp h.2.symm
  have hexyeq : exy = fexp (Zmin ex ey) := hexy.trans hfeq
  have hplus' : Exact.F2R ctx (Float beta mxy (fexp (Zmin ex ey))) =
      Exact.Rplus ctx x y := by
    have hp : Exact.F2R ctx (Float beta mxy (fexp (Zmin ex ey))) =
        Exact.Rplus ctx
          (Exact.F2R ctx (Float beta
            (Exact.Ztrunc ctx
              (Exact.scaled_mantissa ctx magnitude beta fexp x)) (fexp ex)))
          (Exact.F2R ctx (Float beta
            (Exact.Ztrunc ctx
              (Exact.scaled_mantissa ctx magnitude beta fexp y)) (fexp ey))) := by
      simpa [hexyeq] using hplus
    calc
      Exact.F2R ctx (Float beta mxy (fexp (Zmin ex ey))) =
          Exact.Rplus ctx
            (Exact.F2R ctx (Float beta
              (Exact.Ztrunc ctx
                (Exact.scaled_mantissa ctx magnitude beta fexp x))
              (fexp ex)))
            (Exact.F2R ctx (Float beta
              (Exact.Ztrunc ctx
                (Exact.scaled_mantissa ctx magnitude beta fexp y))
              (fexp ey))) := hp
      _ = Exact.Rplus ctx x y := by rw [← hfx', ← hfy']
  let emin := Zmin ex ey
  by_cases hlt : Exact.Rlt ctx (Exact.Rabs ctx (Exact.Rplus ctx x y))
      (Exact.bpow ctx beta emin)
  · have hmagle := CompCert4Lean.Flocq.Core.Raux.mag_le_bpow ctx magnitude
      beta (Exact.Rplus ctx x y) emin hsum0 hlt
    have hce : Zle (Exact.cexp ctx magnitude beta fexp (Exact.Rplus ctx x y))
        (fexp emin) := by
      unfold Exact.cexp
      exact hmono.monotone_exp _ _ hmagle
    apply sterbenz_generic_format_F2R ctx magnitude beta fexp
      (Exact.Rplus ctx x y) (Float beta mxy (fexp emin))
    · exact hplus'
    · right
      exact hce
  · have habseq : Exact.Rabs ctx (Exact.Rplus ctx x y) =
        Exact.bpow ctx beta emin := by
      apply ctx.certificate.orderedField.le_antisymm _ _ hxy
      rcases ctx.certificate.total_order
          (Exact.Rabs ctx (Exact.Rplus ctx x y))
          (Exact.bpow ctx beta emin) with h | h
      · rcases h with hlt' | heq
        · exact (hlt hlt').elim
        · rw [heq]
          exact ctx.certificate.orderedField.le_refl _
      · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1
    have hsmall' : Zlt (fexp (Zmin ex ey)) (Zmin ex ey) := by
      rcases CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zmin.Zmin_spec
          ex ey with h | h
      · have hg := sterbenz_mag_generic_gt ctx magnitude beta fexp hvalid x
          hx0 hfx
        have hg' : Zlt (fexp ex) ex := by
          simpa [ex, Exact.cexp] using hg
        have hmin : Zmin ex ey = ex := h.2
        simpa only [hmin] using hg'
      · have hg := sterbenz_mag_generic_gt ctx magnitude beta fexp hvalid y
          hy0 hfy
        have hg' : Zlt (fexp ey) ey := by
          simpa [ey, Exact.cexp] using hg
        have hmin : Zmin ex ey = ey := h.2
        simpa only [hmin] using hg'
    have hsmall : Zlt (fexp emin) emin := by simpa [emin] using hsmall'
    have hpow : Zle (fexp (Zadd emin Zone)) emin :=
      (hvalid.valid_exp emin).1 hsmall
    apply sterbenz_generic_format_abs_inv ctx magnitude beta fexp
      (Exact.Rplus ctx x y)
    rw [habseq]
    exact sterbenz_generic_format_bpow ctx magnitude beta fexp emin hpow

end CompCert4Lean.Flocq.Prop.Sterbenz

namespace CompCert4Lean.Flocq.Prop.Sterbenz

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.Core.Generic_fmt

theorem generic_format_plus_weak :
    ∀ (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx),
      generic_format_plus_weakStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid hmono x y hfx hfy hxy
  by_cases hx0 : x = Exact.R0 ctx
  · subst x
    change Exact.generic_format ctx magnitude beta fexp
      (ctx.spec.add ctx.spec.zero y)
    rw [ctx.certificate.orderedField.zero_add]
    exact hfy
  by_cases hy0 : y = Exact.R0 ctx
  · subst y
    change Exact.generic_format ctx magnitude beta fexp
      (ctx.spec.add x ctx.spec.zero)
    rw [ctx.certificate.orderedField.add_zero]
    exact hfx
  apply generic_format_plus ctx magnitude beta fexp hvalid hmono x y hfx hfy
  apply ctx.certificate.orderedField.le_trans _ _ _ hxy
  rcases CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zmin.Zmin_spec
      (Exact.mag magnitude beta x) (Exact.mag magnitude beta y) with h | h
  · have hmin : Zmin (Exact.mag magnitude beta x)
        (Exact.mag magnitude beta y) = Exact.mag magnitude beta x := h.2
    rw [hmin]
    apply ctx.certificate.orderedField.le_trans _ _ _
      (ctx.certificate.sourceLaws.min_left _ _)
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
      ((magnitude.value beta x).mag_bound hx0).2).1
  · have hmin : Zmin (Exact.mag magnitude beta x)
        (Exact.mag magnitude beta y) = Exact.mag magnitude beta y := h.2
    rw [hmin]
    apply ctx.certificate.orderedField.le_trans _ _ _
      (ctx.certificate.sourceLaws.min_right _ _)
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
      ((magnitude.value beta y).mag_bound hy0).2).1

end CompCert4Lean.Flocq.Prop.Sterbenz
