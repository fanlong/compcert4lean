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

abbrev ExactRealContext :=
  CompCert4Lean.Flocq.Core.Generic_fmt.ExactRealContext
abbrev ExactMagnitude (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Magnitude ctx
abbrev ExactR (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R ctx

section ExactSpecification

variable (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)

local notation "R" => ExactR ctx
local notation "R0" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R0 ctx
local notation "Rone" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rone ctx
local notation "Rplus" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rplus ctx
local notation "Rminus" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rminus ctx
local notation "Rmult" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rmult ctx
local notation "Rabs" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rabs ctx
local notation "Rlt" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rlt ctx
local notation "Rle" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rle ctx
local notation "bpow" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.bpow ctx
local notation "round" =>
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round ctx magnitude
local notation "Valid_rnd" =>
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Valid_rnd ctx

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

end ExactSpecification

end CompCert4Lean.Flocq.Prop.Relative

namespace CompCert4Lean.Flocq.Prop.Relative

theorem relative_error_FLT_aux : relative_error_FLT_auxStatement := by
  intro emin prec k h
  change
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zsub k (FLT_exp emin prec k))
  change
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (Zsub (Zadd emin prec) Zone) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ k at h
  have intOfZ_sub : ∀ a b : Z,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub a b) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a -
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
    intro a b
    change
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            a - CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b)) = _
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  have intOfZ_add : ∀ a b : Z,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd a b) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a +
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
    intro a b
    change
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a +
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b)) = _
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  have intOfZ_one : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = 1 := by
    rfl
  have intOfZ_FLT_sub : ∀ a b : Z,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Flocq.Core.FLT.Zsub a b) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a -
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
    intro a b
    change
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a -
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b)) = _
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  simp only [intOfZ_sub, intOfZ_add, intOfZ_one,
    CompCert4Lean.Flocq.Core.FLT.FLT_exp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max] at h ⊢
  split
  · omega
  · rw [intOfZ_FLT_sub]
    omega

end CompCert4Lean.Flocq.Prop.Relative
namespace CompCert4Lean.Flocq.Prop.Relative

private theorem pg_zero_lt_one (ctx : ExactRealContext) :
    ctx.spec.lt ctx.spec.zero ctx.spec.one := by
  rcases ctx.certificate.total_order ctx.spec.zero ctx.spec.one with h | h
  · rcases h with h | h
    · exact h
    · exact (ctx.certificate.orderedField.zero_ne_one h).elim
  · have hn : ctx.spec.lt ctx.spec.zero (ctx.spec.neg ctx.spec.one) := by
      have h' := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.neg ctx.spec.one) ctx.spec.one ctx.spec.zero h
      rw [ctx.certificate.orderedField.neg_add_cancel,
        ctx.certificate.orderedField.add_zero] at h'
      exact h'
    have h' := ctx.certificate.orderedField.mul_lt_compat_l
      (ctx.spec.neg ctx.spec.one) ctx.spec.one ctx.spec.zero hn h
    rw [ctx.certificate.orderedField.mul_one,
      ctx.certificate.orderedField.mul_zero] at h'
    exact (ctx.certificate.orderedField.lt_irrefl ctx.spec.zero
      (ctx.certificate.orderedField.lt_trans ctx.spec.zero
        (ctx.spec.neg ctx.spec.one) ctx.spec.zero hn h')).elim

private theorem pg_neg_neg (ctx : ExactRealContext) (x : ctx.spec.carrier) :
    ctx.spec.neg (ctx.spec.neg x) = x := by
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

private theorem pg_neg_mul (ctx : ExactRealContext) (x y : ctx.spec.carrier) :
    ctx.spec.mul (ctx.spec.neg x) y = ctx.spec.neg (ctx.spec.mul x y) := by
  have hsum : ctx.spec.add (ctx.spec.mul (ctx.spec.neg x) y)
      (ctx.spec.mul x y) = ctx.spec.zero := by
    calc
      ctx.spec.add (ctx.spec.mul (ctx.spec.neg x) y) (ctx.spec.mul x y) =
          ctx.spec.add (ctx.spec.mul y (ctx.spec.neg x)) (ctx.spec.mul y x) := by
            rw [ctx.certificate.orderedField.mul_comm (ctx.spec.neg x) y,
              ctx.certificate.orderedField.mul_comm x y]
      _ = ctx.spec.mul y (ctx.spec.add (ctx.spec.neg x) x) :=
        (ctx.certificate.orderedField.left_distrib y (ctx.spec.neg x) x).symm
      _ = ctx.spec.mul y ctx.spec.zero := by
        rw [ctx.certificate.orderedField.neg_add_cancel]
      _ = ctx.spec.zero := ctx.certificate.orderedField.mul_zero _
  calc
    ctx.spec.mul (ctx.spec.neg x) y =
        ctx.spec.add (ctx.spec.mul (ctx.spec.neg x) y) ctx.spec.zero :=
      (ctx.certificate.orderedField.add_zero _).symm
    _ = ctx.spec.add (ctx.spec.mul (ctx.spec.neg x) y)
        (ctx.spec.add (ctx.spec.neg (ctx.spec.mul x y)) (ctx.spec.mul x y)) := by
      rw [ctx.certificate.orderedField.neg_add_cancel]
    _ = ctx.spec.add (ctx.spec.mul (ctx.spec.neg x) y)
        (ctx.spec.add (ctx.spec.mul x y) (ctx.spec.neg (ctx.spec.mul x y))) := by
      exact congrArg (ctx.spec.add (ctx.spec.mul (ctx.spec.neg x) y))
        (ctx.certificate.orderedField.add_comm _ _)
    _ = ctx.spec.add
        (ctx.spec.add (ctx.spec.mul (ctx.spec.neg x) y) (ctx.spec.mul x y))
        (ctx.spec.neg (ctx.spec.mul x y)) :=
      (ctx.certificate.orderedField.add_assoc _ _ _).symm
    _ = ctx.spec.add ctx.spec.zero (ctx.spec.neg (ctx.spec.mul x y)) := by
      rw [hsum]
    _ = ctx.spec.neg (ctx.spec.mul x y) := ctx.certificate.orderedField.zero_add _

private theorem pg_mul_neg (ctx : ExactRealContext) (x y : ctx.spec.carrier) :
    ctx.spec.mul x (ctx.spec.neg y) = ctx.spec.neg (ctx.spec.mul x y) := by
  rw [ctx.certificate.orderedField.mul_comm,
    pg_neg_mul ctx y x,
    ctx.certificate.orderedField.mul_comm]

private theorem pg_neg_pos (ctx : ExactRealContext) {x : ctx.spec.carrier}
    (hx : ctx.spec.lt x ctx.spec.zero) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.neg x) := by
  have h := ctx.certificate.orderedField.add_lt_compat_l
    (ctx.spec.neg x) x ctx.spec.zero hx
  rw [ctx.certificate.orderedField.neg_add_cancel,
    ctx.certificate.orderedField.add_zero] at h
  exact h

private theorem pg_pos_neg (ctx : ExactRealContext) {x : ctx.spec.carrier}
    (hx : ctx.spec.lt ctx.spec.zero x) :
    ctx.spec.lt (ctx.spec.neg x) ctx.spec.zero := by
  have h := ctx.certificate.orderedField.add_lt_compat_l
    (ctx.spec.neg x) ctx.spec.zero x hx
  rw [ctx.certificate.orderedField.add_zero,
    ctx.certificate.orderedField.neg_add_cancel] at h
  exact h

private theorem pg_abs_nonneg (ctx : ExactRealContext) (x : ctx.spec.carrier) :
    ctx.spec.le ctx.spec.zero (ctx.spec.abs x) := by
  rcases ctx.certificate.total_order x ctx.spec.zero with h | h
  · rcases h with hneg | hzero
    · rw [ctx.certificate.sourceLaws.abs_negative x hneg]
      exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
        (pg_neg_pos ctx hneg) |>.1
    · subst x
      rw [ctx.certificate.sourceLaws.abs_nonnegative _
        (ctx.certificate.orderedField.le_refl _)]
      exact ctx.certificate.orderedField.le_refl _
  · rw [ctx.certificate.sourceLaws.abs_nonnegative x
      ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h).1]
    exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1

private theorem pg_abs_pos (ctx : ExactRealContext) {x : ctx.spec.carrier}
    (hx : x ≠ ctx.spec.zero) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.abs x) := by
  rcases ctx.certificate.total_order x ctx.spec.zero with h | h
  · rcases h with hneg | hzero
    · rw [ctx.certificate.sourceLaws.abs_negative x hneg]
      exact pg_neg_pos ctx hneg
    · exact (hx hzero).elim
  · rw [ctx.certificate.sourceLaws.abs_nonnegative x
      ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h).1]
    exact h

private theorem pg_abs_neg (ctx : ExactRealContext) (x : ctx.spec.carrier) :
    ctx.spec.abs (ctx.spec.neg x) = ctx.spec.abs x := by
  rcases ctx.certificate.total_order x ctx.spec.zero with h | h
  · rcases h with hneg | hzero
    · rw [ctx.certificate.sourceLaws.abs_negative x hneg,
        ctx.certificate.sourceLaws.abs_nonnegative (ctx.spec.neg x)
          ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
            (pg_neg_pos ctx hneg)).1]
    · subst x
      have hz : ctx.spec.neg ctx.spec.zero = ctx.spec.zero := by
        calc
          ctx.spec.neg ctx.spec.zero =
              ctx.spec.add (ctx.spec.neg ctx.spec.zero) ctx.spec.zero :=
            (ctx.certificate.orderedField.add_zero _).symm
          _ = ctx.spec.zero := ctx.certificate.orderedField.neg_add_cancel _
      rw [hz]
  · have hpos : ctx.spec.lt (ctx.spec.neg x) ctx.spec.zero := by
      have h' := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.neg x) ctx.spec.zero x h
      rw [ctx.certificate.orderedField.add_zero,
        ctx.certificate.orderedField.neg_add_cancel] at h'
      exact h'
    rw [ctx.certificate.sourceLaws.abs_negative _ hpos,
      pg_neg_neg ctx,
      ctx.certificate.sourceLaws.abs_nonnegative x
        ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h).1]

private theorem pg_add_neg_cancel (ctx : ExactRealContext) (x : ctx.spec.carrier) :
    ctx.spec.add x (ctx.spec.neg x) = ctx.spec.zero := by
  rw [ctx.certificate.orderedField.add_comm,
    ctx.certificate.orderedField.neg_add_cancel]

private theorem pg_sub_add (ctx : ExactRealContext) (a x : ctx.spec.carrier) :
    ctx.spec.add x (ctx.spec.add a (ctx.spec.neg x)) = a := by
  calc
    ctx.spec.add x (ctx.spec.add a (ctx.spec.neg x)) =
        ctx.spec.add (ctx.spec.add x a) (ctx.spec.neg x) :=
      (ctx.certificate.orderedField.add_assoc _ _ _).symm
    _ = ctx.spec.add (ctx.spec.add a x) (ctx.spec.neg x) := by
      rw [ctx.certificate.orderedField.add_comm x a]
    _ = ctx.spec.add a (ctx.spec.add x (ctx.spec.neg x)) :=
      ctx.certificate.orderedField.add_assoc _ _ _
    _ = ctx.spec.add a ctx.spec.zero := by
      rw [pg_add_neg_cancel ctx]
    _ = a := ctx.certificate.orderedField.add_zero _

private theorem pg_mul_sub_inv (ctx : ExactRealContext)
    {a x : ctx.spec.carrier} (hx : x ≠ ctx.spec.zero) :
    ctx.spec.mul x
        (ctx.spec.mul (ctx.spec.add a (ctx.spec.neg x)) (ctx.spec.inv x)) =
      ctx.spec.add a (ctx.spec.neg x) := by
  have hi : ctx.spec.mul x (ctx.spec.inv x) = ctx.spec.one := by
    rw [ctx.certificate.orderedField.mul_comm]
    exact ctx.certificate.orderedField.inv_mul_cancel x hx
  calc
    ctx.spec.mul x
        (ctx.spec.mul (ctx.spec.add a (ctx.spec.neg x)) (ctx.spec.inv x)) =
        ctx.spec.mul
          (ctx.spec.mul x (ctx.spec.add a (ctx.spec.neg x)))
          (ctx.spec.inv x) :=
      (ctx.certificate.orderedField.mul_assoc _ _ _).symm
    _ = ctx.spec.mul
          (ctx.spec.mul (ctx.spec.add a (ctx.spec.neg x)) x)
          (ctx.spec.inv x) := by
      rw [ctx.certificate.orderedField.mul_comm x]
    _ = ctx.spec.mul
          (ctx.spec.add a (ctx.spec.neg x))
          (ctx.spec.mul x (ctx.spec.inv x)) := by
      rw [ctx.certificate.orderedField.mul_assoc]
    _ = ctx.spec.add a (ctx.spec.neg x) := by rw [hi, ctx.certificate.orderedField.mul_one]

private theorem pg_mul_lt_r (ctx : ExactRealContext) {r a b : ctx.spec.carrier}
    (hr : ctx.spec.lt ctx.spec.zero r) (hab : ctx.spec.lt a b) :
    ctx.spec.lt (ctx.spec.mul a r) (ctx.spec.mul b r) := by
  rw [ctx.certificate.orderedField.mul_comm a r,
    ctx.certificate.orderedField.mul_comm b r]
  exact ctx.certificate.orderedField.mul_lt_compat_l r a b hr hab

private theorem pg_abs_mul (ctx : ExactRealContext) (x y : ctx.spec.carrier) :
    ctx.spec.abs (ctx.spec.mul x y) =
      ctx.spec.mul (ctx.spec.abs x) (ctx.spec.abs y) := by
  have split : ∀ z : ctx.spec.carrier,
      z = ctx.spec.zero ∨ ctx.spec.lt ctx.spec.zero z ∨
        ctx.spec.lt z ctx.spec.zero := by
    intro z
    rcases ctx.certificate.total_order ctx.spec.zero z with h | h
    · rcases h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
  rcases split x with hx0 | hxpos | hxneg
  · rw [hx0, ctx.certificate.orderedField.zero_mul,
      ctx.certificate.sourceLaws.abs_nonnegative _
        (ctx.certificate.orderedField.le_refl _),
      ctx.certificate.orderedField.zero_mul]
  · rcases split y with hy0 | hypos | hyneg
    · rw [hy0, ctx.certificate.orderedField.mul_zero,
        ctx.certificate.sourceLaws.abs_nonnegative _
          (ctx.certificate.orderedField.le_refl _),
        ctx.certificate.orderedField.mul_zero]
    · have hprod := ctx.certificate.orderedField.mul_lt_compat_l x
          ctx.spec.zero y hxpos hypos
      rw [ctx.certificate.orderedField.mul_zero] at hprod
      rw [ctx.certificate.sourceLaws.abs_nonnegative _
          ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hprod).1,
        ctx.certificate.sourceLaws.abs_nonnegative x
          ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxpos).1,
        ctx.certificate.sourceLaws.abs_nonnegative y
          ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hypos).1]
    · have hprod := ctx.certificate.orderedField.mul_lt_compat_l x
          y ctx.spec.zero hxpos hyneg
      rw [ctx.certificate.orderedField.mul_zero] at hprod
      rw [ctx.certificate.sourceLaws.abs_negative _ hprod,
        ctx.certificate.sourceLaws.abs_nonnegative x
          ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxpos).1,
        ctx.certificate.sourceLaws.abs_negative y hyneg,
        pg_mul_neg ctx x y]
  · rcases split y with hy0 | hypos | hyneg
    · rw [hy0, ctx.certificate.orderedField.mul_zero,
        ctx.certificate.sourceLaws.abs_nonnegative _
          (ctx.certificate.orderedField.le_refl _),
        ctx.certificate.orderedField.mul_zero]
    · have hprod := ctx.certificate.orderedField.mul_lt_compat_l y
          x ctx.spec.zero hypos hxneg
      rw [ctx.certificate.orderedField.mul_comm y x,
        ctx.certificate.orderedField.mul_zero] at hprod
      rw [ctx.certificate.sourceLaws.abs_negative _ hprod,
        ctx.certificate.sourceLaws.abs_negative x hxneg,
        ctx.certificate.sourceLaws.abs_nonnegative y
          ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hypos).1,
        pg_neg_mul ctx x y]
    · have hprod0 := ctx.certificate.orderedField.mul_lt_compat_l
          (ctx.spec.neg x) ctx.spec.zero (ctx.spec.neg y)
          (pg_neg_pos ctx hxneg) (pg_neg_pos ctx hyneg)
      rw [ctx.certificate.orderedField.mul_zero] at hprod0
      have hnegneg : ctx.spec.mul (ctx.spec.neg x) (ctx.spec.neg y) =
          ctx.spec.mul x y := by
        calc
          ctx.spec.mul (ctx.spec.neg x) (ctx.spec.neg y) =
              ctx.spec.neg (ctx.spec.mul (ctx.spec.neg x) y) :=
            pg_mul_neg ctx (ctx.spec.neg x) y
          _ = ctx.spec.neg (ctx.spec.neg (ctx.spec.mul x y)) := by
            rw [pg_neg_mul ctx x y]
          _ = ctx.spec.mul x y := pg_neg_neg ctx _
      have hprod : ctx.spec.lt ctx.spec.zero (ctx.spec.mul x y) := by
        rw [← hnegneg]
        exact hprod0
      rw [ctx.certificate.sourceLaws.abs_nonnegative _
          ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hprod).1,
        ctx.certificate.sourceLaws.abs_negative x hxneg,
        ctx.certificate.sourceLaws.abs_negative y hyneg,
        hnegneg]

private theorem pg_abs_inv_mul (ctx : ExactRealContext) {x : ctx.spec.carrier}
    (hx : x ≠ ctx.spec.zero) :
    ctx.spec.mul (ctx.spec.abs (ctx.spec.inv x)) (ctx.spec.abs x) = ctx.spec.one := by
  have hi : ctx.spec.mul (ctx.spec.inv x) x = ctx.spec.one :=
    ctx.certificate.orderedField.inv_mul_cancel x hx
  calc
    ctx.spec.mul (ctx.spec.abs (ctx.spec.inv x)) (ctx.spec.abs x) =
        ctx.spec.abs (ctx.spec.mul (ctx.spec.inv x) x) :=
      (pg_abs_mul ctx (ctx.spec.inv x) x).symm
    _ = ctx.spec.abs ctx.spec.one := congrArg ctx.spec.abs hi
    _ = ctx.spec.one := by
      rw [ctx.certificate.sourceLaws.abs_nonnegative _
        ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
          (pg_zero_lt_one ctx)).1]

private theorem pg_eps_abs_bound (ctx : ExactRealContext) {d x b : ctx.spec.carrier}
    (hx : x ≠ ctx.spec.zero)
    (hd : ctx.spec.lt (ctx.spec.abs d)
      (ctx.spec.mul b (ctx.spec.abs x))) :
    ctx.spec.lt (ctx.spec.abs (ctx.spec.mul d (ctx.spec.inv x))) b := by
  have hi0 : ctx.spec.lt ctx.spec.zero (ctx.spec.abs (ctx.spec.inv x)) := by
    apply pg_abs_pos ctx
    intro hi
    have hmul := ctx.certificate.orderedField.inv_mul_cancel x hx
    rw [hi, ctx.certificate.orderedField.zero_mul] at hmul
    exact (ctx.certificate.orderedField.zero_ne_one hmul).elim
  have hm := pg_mul_lt_r ctx hi0 hd
  have hm' : ctx.spec.lt
      (ctx.spec.abs (ctx.spec.mul d (ctx.spec.inv x)))
      (ctx.spec.mul (ctx.spec.mul b (ctx.spec.abs x))
        (ctx.spec.abs (ctx.spec.inv x))) := by
    rw [pg_abs_mul ctx]
    exact hm
  have hright : ctx.spec.mul
      (ctx.spec.abs (ctx.spec.inv x))
      (ctx.spec.mul b (ctx.spec.abs x)) = b := by
    calc
      ctx.spec.mul (ctx.spec.abs (ctx.spec.inv x))
          (ctx.spec.mul b (ctx.spec.abs x)) =
          ctx.spec.mul b
            (ctx.spec.mul (ctx.spec.abs (ctx.spec.inv x))
              (ctx.spec.abs x)) := by
        calc
          ctx.spec.mul (ctx.spec.abs (ctx.spec.inv x))
              (ctx.spec.mul b (ctx.spec.abs x)) =
              ctx.spec.mul
                (ctx.spec.mul (ctx.spec.abs (ctx.spec.inv x)) b)
                (ctx.spec.abs x) :=
            (ctx.certificate.orderedField.mul_assoc _ _ _).symm
          _ = ctx.spec.mul
                (ctx.spec.mul b (ctx.spec.abs (ctx.spec.inv x)))
                (ctx.spec.abs x) := by
            rw [ctx.certificate.orderedField.mul_comm
              (ctx.spec.abs (ctx.spec.inv x)) b]
          _ = ctx.spec.mul b
                (ctx.spec.mul (ctx.spec.abs (ctx.spec.inv x))
                  (ctx.spec.abs x)) :=
            ctx.certificate.orderedField.mul_assoc _ _ _
      _ = ctx.spec.mul b ctx.spec.one := by
        rw [pg_abs_inv_mul ctx hx]
      _ = b := ctx.certificate.orderedField.mul_one _
  have hright' : ctx.spec.mul
      (ctx.spec.mul b (ctx.spec.abs x))
      (ctx.spec.abs (ctx.spec.inv x)) = b := by
    rw [ctx.certificate.orderedField.mul_comm]
    exact hright
  rw [hright'] at hm'
  exact hm'

private theorem pg_round_zero (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (fexp : Z → Z)
    (rnd : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R ctx → Z)
    (hrnd : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Valid_rnd ctx rnd) :
    CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round ctx magnitude beta fexp rnd
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R0 ctx) =
      CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R0 ctx := by
  unfold CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
    CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
    CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp
  have hs : ctx.spec.mul ctx.spec.zero
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.bpow ctx beta
        (CompCert4Lean.Flocq.Core.Raux.Zopp
          (fexp (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.mag magnitude beta ctx.spec.zero)))) =
      ctx.spec.zero := by
    exact ctx.certificate.orderedField.zero_mul _
  have hr : rnd (ctx.spec.zero) = Z0 := by
    rw [← ctx.certificate.sourceLaws.ofZ_zero]
    exact hrnd.Zrnd_IZR Z0
  have hr' : rnd (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R0 ctx) = Z0 := by
    change rnd ctx.spec.zero = Z0
    exact hr
  have hscaled :
      CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rmult ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R0 ctx)
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.bpow ctx beta
            (CompCert4Lean.Flocq.Core.Raux.Zopp
              (fexp (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.mag magnitude beta
                (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R0 ctx))))) =
        CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R0 ctx := by
    change ctx.spec.mul ctx.spec.zero
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.bpow ctx beta
      (CompCert4Lean.Flocq.Core.Raux.Zopp
          (fexp (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.mag magnitude beta
            ctx.spec.zero)))) = ctx.spec.zero
    exact ctx.certificate.orderedField.zero_mul _
  rw [hscaled, hr']
  change ctx.spec.mul (ctx.spec.ofZ Z0)
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.bpow ctx beta
        (fexp (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.mag magnitude beta
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R0 ctx)))) = ctx.spec.zero
  rw [ctx.certificate.sourceLaws.ofZ_zero,
    ctx.certificate.orderedField.zero_mul]

theorem relative_error_lt_conversion :
    ∀ (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx),
      relative_error_lt_conversionStatement ctx magnitude := by
  intro ctx magnitude beta fexp rnd hrnd x b hb hxb
  by_cases hx : x = CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R0 ctx
  · subst x
    refine ⟨CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R0 ctx, ?_, ?_⟩
    · change ctx.spec.lt (ctx.spec.abs ctx.spec.zero) b
      rw [ctx.certificate.sourceLaws.abs_nonnegative _
        (ctx.certificate.orderedField.le_refl _)]
      exact hb
    · rw [pg_round_zero ctx magnitude beta fexp rnd hrnd]
      change ctx.spec.zero =
        ctx.spec.mul ctx.spec.zero (ctx.spec.add ctx.spec.one ctx.spec.zero)
      rw [ctx.certificate.orderedField.zero_mul]
  · let d := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rminus ctx
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round ctx magnitude beta fexp rnd x) x
    let eps := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rmult ctx d
      (CompCert4Lean.Flocq.Core.Raux.Exact.Rinv ctx x)
    have heps :
        ctx.spec.lt (ctx.spec.abs eps) b := by
      dsimp [eps, d]
      apply pg_eps_abs_bound ctx hx
      exact hxb hx
    have heq :
        CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round ctx magnitude beta fexp rnd x =
          CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rmult ctx x
            (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rplus ctx
              (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rone ctx) eps) := by
      dsimp [eps, d]
      have hi : ctx.spec.mul x (ctx.spec.inv x) = ctx.spec.one := by
        rw [ctx.certificate.orderedField.mul_comm]
        exact ctx.certificate.orderedField.inv_mul_cancel x hx
      have halg :
          ctx.spec.mul x
            (ctx.spec.add ctx.spec.one
              (ctx.spec.mul
                (ctx.spec.add
                  (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
                    ctx magnitude beta fexp rnd x)
                  (ctx.spec.neg x))
                (ctx.spec.inv x))) =
            CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
              ctx magnitude beta fexp rnd x := by
       calc
        ctx.spec.mul x
            (ctx.spec.add ctx.spec.one
              (ctx.spec.mul
                (ctx.spec.add
                  (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
                    ctx magnitude beta fexp rnd x)
                  (ctx.spec.neg x))
                (ctx.spec.inv x))) =
            ctx.spec.add (ctx.spec.mul x ctx.spec.one)
              (ctx.spec.mul x
                (ctx.spec.mul
                  (ctx.spec.add
                    (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
                      ctx magnitude beta fexp rnd x)
                    (ctx.spec.neg x))
                  (ctx.spec.inv x))) :=
          ctx.certificate.orderedField.left_distrib _ _ _
        _ = ctx.spec.add x
              (ctx.spec.mul x
                (ctx.spec.mul
                  (ctx.spec.add
                    (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
                      ctx magnitude beta fexp rnd x)
                    (ctx.spec.neg x))
                  (ctx.spec.inv x))) := by
          rw [ctx.certificate.orderedField.mul_one]
        _ = ctx.spec.add x
              (ctx.spec.mul
                (ctx.spec.mul
                  (ctx.spec.add
                    (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
                      ctx magnitude beta fexp rnd x)
                    (ctx.spec.neg x)) x)
                (ctx.spec.inv x)) := by
          rw [← ctx.certificate.orderedField.mul_assoc,
            ctx.certificate.orderedField.mul_comm x]
        _ = ctx.spec.add x
              (ctx.spec.mul
                (ctx.spec.add
                  (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
                    ctx magnitude beta fexp rnd x)
                  (ctx.spec.neg x))
                (ctx.spec.mul x (ctx.spec.inv x))) := by
          rw [ctx.certificate.orderedField.mul_assoc]
        _ = ctx.spec.add x
              (ctx.spec.add
                (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
                  ctx magnitude beta fexp rnd x)
                (ctx.spec.neg x)) := by
          rw [hi, ctx.certificate.orderedField.mul_one]
        _ = CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
              ctx magnitude beta fexp rnd x := by
          exact pg_sub_add ctx _ _
      exact halg.symm

    exact ⟨eps, heps, heq⟩

end CompCert4Lean.Flocq.Prop.Relative

namespace CompCert4Lean.Flocq.Prop.Relative

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals

private theorem pg_flt_floor_error (ctx : ExactRealContext) (x : ExactR ctx) :
    ctx.spec.lt
      (ctx.spec.abs (ctx.spec.add x (ctx.spec.neg (ctx.spec.ofZ (Raux.Exact.Zfloor ctx x)))))
      ctx.spec.one := by
  let n := ctx.spec.ofZ (Raux.Exact.Zfloor ctx x)
  have hnonneg : ctx.spec.le ctx.spec.zero (ctx.spec.add x (ctx.spec.neg n)) := by
    have h := RIneq.Rplus_le_compat_l ctx (ctx.spec.neg n) n x
      (Raux.Zfloor_lb ctx x)
    change ctx.spec.le (ctx.spec.add (ctx.spec.neg n) n)
      (ctx.spec.add (ctx.spec.neg n) x) at h
    rw [ctx.certificate.orderedField.neg_add_cancel,
      ctx.certificate.orderedField.add_comm (ctx.spec.neg n) x] at h
    exact h
  have h := ctx.certificate.orderedField.add_lt_compat_l
    (ctx.spec.neg n) x (ctx.spec.add n ctx.spec.one) (Raux.Zfloor_ub ctx x)
  rw [← ctx.certificate.orderedField.add_assoc,
    ctx.certificate.orderedField.neg_add_cancel,
    ctx.certificate.orderedField.zero_add,
    ctx.certificate.orderedField.add_comm (ctx.spec.neg n) x] at h
  rw [ctx.certificate.sourceLaws.abs_nonnegative _ hnonneg]
  exact h

private theorem pg_flt_integer_error (ctx : ExactRealContext)
    (rnd : ExactR ctx → Z) (hrnd : Generic_fmt.Exact.Valid_rnd ctx rnd)
    (x : ExactR ctx) :
    ctx.spec.lt (ctx.spec.abs (ctx.spec.add (ctx.spec.ofZ (rnd x)) (ctx.spec.neg x)))
      ctx.spec.one := by
  rcases Generic_fmt.Zrnd_DN_or_UP ctx rnd hrnd x with h | h
  · rw [h]
    have hs := Rbasic_fun.Rabs_minus_sym ctx (ctx.spec.ofZ (Raux.Exact.Zfloor ctx x)) x
    change ctx.spec.abs (ctx.spec.add (ctx.spec.ofZ (Raux.Exact.Zfloor ctx x))
        (ctx.spec.neg x)) =
      ctx.spec.abs (ctx.spec.add x (ctx.spec.neg (ctx.spec.ofZ (Raux.Exact.Zfloor ctx x)))) at hs
    rw [hs]
    exact pg_flt_floor_error ctx x
  · rw [h]
    change ctx.spec.lt
      (ctx.spec.abs (ctx.spec.add
        (ctx.spec.ofZ (Zopp (Raux.Exact.Zfloor ctx (ctx.spec.neg x))))
        (ctx.spec.neg x))) ctx.spec.one
    rw [ctx.certificate.sourceLaws.ofZ_neg,
      ctx.certificate.orderedField.add_comm]
    exact pg_flt_floor_error ctx (ctx.spec.neg x)

private theorem pg_flt_round_error (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx) (beta : radix) (fexp : Z → Z)
    (rnd : ExactR ctx → Z) (hrnd : Generic_fmt.Exact.Valid_rnd ctx rnd)
    (x : ExactR ctx) :
    ctx.spec.lt
      (ctx.spec.abs (ctx.spec.add (Generic_fmt.Exact.round ctx magnitude beta fexp rnd x)
        (ctx.spec.neg x)))
      (Generic_fmt.Exact.bpow ctx beta (Generic_fmt.Exact.cexp ctx magnitude beta fexp x)) := by
  let m := Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp x
  let u := Generic_fmt.Exact.bpow ctx beta (Generic_fmt.Exact.cexp ctx magnitude beta fexp x)
  have hscale : ctx.spec.mul m u = x :=
    Generic_fmt.scaled_mantissa_mult_bpow ctx magnitude beta fexp x
  have hu : ctx.spec.lt ctx.spec.zero u := Raux.bpow_gt_0 ctx beta _
  have habsu : ctx.spec.abs u = u :=
    ctx.certificate.sourceLaws.abs_nonnegative u
      ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hu).1
  have hdiff : ctx.spec.add (Generic_fmt.Exact.round ctx magnitude beta fexp rnd x)
      (ctx.spec.neg x) =
      ctx.spec.mul (ctx.spec.add (ctx.spec.ofZ (rnd m)) (ctx.spec.neg m)) u := by
    have hd := RIneq.Rmult_minus_distr_r ctx u (ctx.spec.ofZ (rnd m)) m
    change ctx.spec.mul (ctx.spec.add (ctx.spec.ofZ (rnd m)) (ctx.spec.neg m)) u =
      ctx.spec.add (ctx.spec.mul (ctx.spec.ofZ (rnd m)) u)
        (ctx.spec.neg (ctx.spec.mul m u)) at hd
    rw [hscale] at hd
    exact hd.symm
  rw [hdiff, pg_abs_mul ctx, habsu]
  have h := pg_mul_lt_r ctx hu (pg_flt_integer_error ctx rnd hrnd m)
  rw [ctx.certificate.orderedField.one_mul] at h
  exact h

end CompCert4Lean.Flocq.Prop.Relative

namespace CompCert4Lean.Flocq.Prop.Relative

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals

theorem relative_error_FLT :
    ∀ (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx),
      relative_error_FLTStatement ctx magnitude := by
  intro ctx magnitude beta emin prec _hp rnd hrnd x hx
  have hx0 : x ≠ ctx.spec.zero := by
    intro hz
    have hx' := hx
    change ctx.spec.le (Generic_fmt.Exact.bpow ctx beta (Zsub (Zadd emin prec) Zone))
      (ctx.spec.abs x) at hx'
    rw [hz, ctx.certificate.sourceLaws.abs_nonnegative _
      (ctx.certificate.orderedField.le_refl _)] at hx'
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
      (Raux.bpow_gt_0 ctx beta (Zsub (Zadd emin prec) Zone))).2 hx'
  let e := Generic_fmt.Exact.mag magnitude beta x
  have hmag := (magnitude.value beta x).mag_bound hx0
  have he : Zlt (Zsub (Zadd emin prec) Zone) e :=
    Raux.lt_bpow ctx beta _ _ (RIneq.Rle_lt_trans ctx _ _ _ hx hmag.2)
  have heaux := relative_error_FLT_aux emin prec e he
  have hexp : Zle (FLT_exp emin prec e)
      (Zadd (Zadd (Zopp prec) Zone) (Zsub e Zone)) := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub e (FLT_exp emin prec e)) at heaux
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (FLT_exp emin prec e) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zadd (Zadd (Zopp prec) Zone) (Zsub e Zone))
    simp only [Zadd, Zsub, Zopp,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at heaux ⊢
    omega
  have hpow := Raux.bpow_le ctx beta _ _ hexp
  rw [Raux.bpow_plus ctx beta (Zadd (Zopp prec) Zone) (Zsub e Zone)] at hpow
  have hpos : ctx.spec.le (ctx.spec.ofZ Z0)
      (Generic_fmt.Exact.bpow ctx beta (Zadd (Zopp prec) Zone)) := by
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
      (Raux.bpow_gt_0 ctx beta (Zadd (Zopp prec) Zone))).1
  have hprod := RIneq.Rmult_le_compat_l ctx
    (Generic_fmt.Exact.bpow ctx beta (Zadd (Zopp prec) Zone)) _ _ hpos hmag.1
  exact RIneq.Rlt_le_trans ctx _ _ _
    (pg_flt_round_error ctx magnitude beta (FLT_exp emin prec) rnd hrnd x)
    (ctx.certificate.orderedField.le_trans _ _ _ hpow hprod)

end CompCert4Lean.Flocq.Prop.Relative

namespace CompCert4Lean.Flocq.Prop.Relative

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals

theorem relative_error_FLT_ex :
    ∀ (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx),
      relative_error_FLT_exStatement ctx magnitude := by
  intro ctx magnitude beta emin prec hp rnd hrnd x hx
  apply relative_error_lt_conversion ctx magnitude beta
    (FLT_exp emin prec) rnd hrnd x
    (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.bpow ctx beta
      (Zadd (Zopp prec) Zone))
  · exact Raux.bpow_gt_0 ctx beta _
  · intro _
    exact relative_error_FLT ctx magnitude beta emin prec hp rnd hrnd x hx

end CompCert4Lean.Flocq.Prop.Relative
