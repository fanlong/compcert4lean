import CompCert4Lean.Flocq.Core.Defs

/-!
# Basic operations on Flocq floats

This module contains the executable definitions selected from
`Flocq.Calc.Operations`.  The source theorem declarations are retained as
exact proposition descriptors for the later proof-migration phase.
-/

namespace CompCert4Lean.Flocq.Calc.Operations

abbrev R := CompCert4Lean.Flocq.Core.Defs.R
abbrev Z := CompCert4Lean.Flocq.Core.Defs.Z
abbrev radix := CompCert4Lean.Flocq.Core.Defs.radix
abbrev float := CompCert4Lean.Flocq.Core.Defs.float
abbrev Float (beta : radix) (m e : Z) : float beta :=
  CompCert4Lean.Flocq.Core.Defs.Float beta m e
abbrev Fnum {beta : radix} (f : float beta) : Z :=
  CompCert4Lean.Flocq.Core.Defs.Fnum f
abbrev Fexp {beta : radix} (f : float beta) : Z :=
  CompCert4Lean.Flocq.Core.Defs.Fexp f
abbrev IZR := CompCert4Lean.Flocq.Core.Defs.IZR
abbrev F2R {beta : radix} (f : float beta) : R :=
  CompCert4Lean.Flocq.Core.Defs.F2R f

abbrev Zadd := CompCert4Lean.Flocq.Core.Zaux.Zadd
abbrev Zsub := CompCert4Lean.Flocq.Core.Zaux.Zsub
abbrev Zmul := CompCert4Lean.Flocq.Core.Zaux.Zmul
abbrev Zopp := CompCert4Lean.Flocq.Core.Zaux.Zopp
abbrev Zabs := CompCert4Lean.Flocq.Core.Zaux.Zabs
abbrev Zle_bool := CompCert4Lean.Flocq.Core.Zaux.Zle_bool
abbrev Zpower := CompCert4Lean.Flocq.Core.Zaux.Zpower
abbrev Zmin := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.min
abbrev Rplus := CompCert4Lean.Flocq.Core.Raux.Rplus
abbrev Rmult := CompCert4Lean.Flocq.Core.Raux.Rmult
abbrev Ropp := CompCert4Lean.Flocq.Core.Raux.Ropp
abbrev Rabs := CompCert4Lean.Flocq.Core.Raux.Rabs

abbrev ExactRealContext := CompCert4Lean.Flocq.Core.Raux.ExactRealContext

namespace Exact

abbrev F2R := CompCert4Lean.Flocq.Core.Defs.Exact.F2R
abbrev Ropp := CompCert4Lean.Flocq.Core.Raux.Exact.Ropp
abbrev Rabs := CompCert4Lean.Flocq.Core.Raux.Exact.Rabs
abbrev Rplus := CompCert4Lean.Flocq.Core.Raux.Exact.Rplus
abbrev Rmult := CompCert4Lean.Flocq.Core.Raux.Exact.Rmult

end Exact

def Falign (f1 f2 : float beta) : (Z × Z) × Z :=
  match f1, f2 with
  | CompCert4Lean.Flocq.Core.Defs.Float _ m1 e1,
      CompCert4Lean.Flocq.Core.Defs.Float _ m2 e2 =>
      if Zle_bool e1 e2 then
        ((m1, Zmul m2 (Zpower (beta : Z) (Zsub e2 e1))), e1)
      else
        ((Zmul m1 (Zpower (beta : Z) (Zsub e1 e2)), m2), e2)

def Fopp {beta : radix} (f1 : float beta) : float beta :=
  match f1 with
  | CompCert4Lean.Flocq.Core.Defs.Float _ m1 e1 => Float beta (Zopp m1) e1

def Fabs {beta : radix} (f1 : float beta) : float beta :=
  match f1 with
  | CompCert4Lean.Flocq.Core.Defs.Float _ m1 e1 => Float beta (Zabs m1) e1

def Fplus {beta : radix} (f1 f2 : float beta) : float beta :=
  let ((m1, m2), e) := Falign f1 f2
  Float beta (Zadd m1 m2) e

def Fmult {beta : radix} (f1 f2 : float beta) : float beta :=
  match f1, f2 with
  | CompCert4Lean.Flocq.Core.Defs.Float _ m1 e1,
      CompCert4Lean.Flocq.Core.Defs.Float _ m2 e2 =>
      Float beta (Zmul m1 m2) (Zadd e1 e2)

/-! Exact source proposition descriptors for later proof migration. -/

def Falign_specStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (f1 f2 : float beta),
    let ((m1, m2), e) := Falign f1 f2
    Exact.F2R ctx f1 = Exact.F2R ctx (Float beta m1 e) ∧
      Exact.F2R ctx f2 = Exact.F2R ctx (Float beta m2 e)

def Falign_spec_expStatement : Prop :=
  ∀ (beta : radix) (f1 f2 : float beta),
    (Falign f1 f2).2 = Zmin (Fexp f1) (Fexp f2)

def F2R_oppStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (f1 : float beta),
    Exact.F2R ctx (Fopp f1) = Exact.Ropp ctx (Exact.F2R ctx f1)

def F2R_absStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (f1 : float beta),
    Exact.F2R ctx (Fabs f1) = Exact.Rabs ctx (Exact.F2R ctx f1)

def F2R_plusStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (f1 f2 : float beta),
    Exact.F2R ctx (Fplus f1 f2) =
      Exact.Rplus ctx (Exact.F2R ctx f1) (Exact.F2R ctx f2)

def Fexp_FplusStatement : Prop :=
  ∀ (beta : radix) (f1 f2 : float beta),
    Fexp (Fplus f1 f2) = Zmin (Fexp f1) (Fexp f2)

def F2R_multStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (f1 f2 : float beta),
    Exact.F2R ctx (Fmult f1 f2) =
      Exact.Rmult ctx (Exact.F2R ctx f1) (Exact.F2R ctx f2)

end CompCert4Lean.Flocq.Calc.Operations

namespace CompCert4Lean.Flocq.Calc.Operations

private theorem f2r_zofnat_succ (n : Nat) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat (Nat.succ n)) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat n))
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH) := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  rfl

private theorem f2r_one_pos (ctx : ExactRealContext) :
    ctx.spec.lt ctx.spec.zero ctx.spec.one := by
  rcases ctx.certificate.total_order ctx.spec.zero ctx.spec.one with h | h
  · rcases h with hlt | heq
    · exact hlt
    · exact (ctx.certificate.orderedField.zero_ne_one heq).elim
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

private theorem f2r_add_pos (ctx : ExactRealContext) {x y : ctx.spec.carrier}
    (hx : ctx.spec.lt ctx.spec.zero x) (hy : ctx.spec.lt ctx.spec.zero y) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.add x y) := by
  have h := ctx.certificate.orderedField.add_lt_compat_l y ctx.spec.zero x hx
  rw [ctx.certificate.orderedField.add_zero,
    ctx.certificate.orderedField.add_comm y x] at h
  exact ctx.certificate.orderedField.lt_trans ctx.spec.zero y
    (ctx.spec.add x y) hy h

private theorem f2r_ofZ_nat_pos (ctx : ExactRealContext) (n : Nat) (hn : 0 < n) :
    ctx.spec.lt ctx.spec.zero
      (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat n))) := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      change ctx.spec.lt ctx.spec.zero
        (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH))
      rw [ctx.certificate.sourceLaws.ofZ_one]
      exact f2r_one_pos ctx
    | succ n =>
      rw [f2r_zofnat_succ, ctx.certificate.sourceLaws.ofZ_add]
      apply f2r_add_pos ctx (ih (Nat.succ_pos _))
      rw [ctx.certificate.sourceLaws.ofZ_one]
      exact f2r_one_pos ctx

private theorem f2r_ofZ_int_pos (ctx : ExactRealContext) (i : Int) (hi : 0 < i) :
    ctx.spec.lt ctx.spec.zero
      (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt i)) := by
  have hnonneg : 0 ≤ i := by omega
  have hnat : 0 < i.toNat := by omega
  have h := f2r_ofZ_nat_pos ctx i.toNat hnat
  have heq : Int.ofNat i.toNat = i := Int.toNat_of_nonneg hnonneg
  rw [heq] at h
  exact h

private theorem f2r_ofZ_pos (ctx : ExactRealContext)
    (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) :
    ctx.spec.lt ctx.spec.zero
      (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos p)) := by
  have hp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
  have h := f2r_ofZ_nat_pos ctx
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) hp
  have hz : CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos p := by
    simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] using
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt_intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos p)
  rw [hz] at h
  exact h

private theorem f2r_neg_lt_zero (ctx : ExactRealContext) (x : ctx.spec.carrier)
    (hx : ctx.spec.lt ctx.spec.zero x) :
    ctx.spec.lt (ctx.spec.neg x) ctx.spec.zero := by
  have h := ctx.certificate.orderedField.add_lt_compat_l
    (ctx.spec.neg x) ctx.spec.zero x hx
  rw [ctx.certificate.orderedField.neg_add_cancel,
    ctx.certificate.orderedField.add_zero] at h
  exact h

private theorem f2r_neg_neg (ctx : ExactRealContext) (x : ctx.spec.carrier) :
    ctx.spec.neg (ctx.spec.neg x) = x := by
  calc
    ctx.spec.neg (ctx.spec.neg x) =
        ctx.spec.add (ctx.spec.neg (ctx.spec.neg x)) ctx.spec.zero :=
      (ctx.certificate.orderedField.add_zero _).symm
    _ = ctx.spec.add (ctx.spec.neg (ctx.spec.neg x))
        (ctx.spec.add x (ctx.spec.neg x)) := by
      rw [ctx.certificate.orderedField.add_comm x (ctx.spec.neg x),
        ctx.certificate.orderedField.neg_add_cancel]
    _ = ctx.spec.add
        (ctx.spec.add (ctx.spec.neg (ctx.spec.neg x)) (ctx.spec.neg x)) x := by
      rw [ctx.certificate.orderedField.add_comm x (ctx.spec.neg x)]
      exact (ctx.certificate.orderedField.add_assoc _ _ _).symm
    _ = ctx.spec.add ctx.spec.zero x := by
      rw [ctx.certificate.orderedField.neg_add_cancel]
    _ = x := ctx.certificate.orderedField.zero_add _

private theorem f2r_mul_pos (ctx : ExactRealContext) {x y : ctx.spec.carrier}
    (hx : ctx.spec.lt ctx.spec.zero x) (hy : ctx.spec.lt ctx.spec.zero y) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.mul x y) := by
  have h := ctx.certificate.orderedField.mul_lt_compat_l x ctx.spec.zero y hx hy
  rw [ctx.certificate.orderedField.mul_zero] at h
  exact h

private theorem f2r_inv_pos (ctx : ExactRealContext) (x : ctx.spec.carrier)
    (hx : ctx.spec.lt ctx.spec.zero x) : ctx.spec.lt ctx.spec.zero (ctx.spec.inv x) := by
  rcases ctx.certificate.total_order ctx.spec.zero (ctx.spec.inv x) with h | h
  · rcases h with hlt | heq
    · exact hlt
    · have hx0 : x ≠ ctx.spec.zero := by
        intro heq
        rw [heq] at hx
        exact ctx.certificate.orderedField.lt_irrefl _ hx
      have hmul := ctx.certificate.orderedField.inv_mul_cancel x hx0
      rw [← heq, ctx.certificate.orderedField.zero_mul] at hmul
      exact (ctx.certificate.orderedField.zero_ne_one hmul).elim
  · have hmul := ctx.certificate.orderedField.mul_lt_compat_l x
      (ctx.spec.inv x) ctx.spec.zero hx h
    rw [ctx.certificate.orderedField.mul_comm x (ctx.spec.inv x),
      ctx.certificate.orderedField.inv_mul_cancel] at hmul
    · rw [ctx.certificate.orderedField.mul_zero] at hmul
      exact (ctx.certificate.orderedField.lt_irrefl ctx.spec.zero
        (ctx.certificate.orderedField.lt_trans ctx.spec.zero ctx.spec.one
          ctx.spec.zero (f2r_one_pos ctx) hmul)).elim
    · intro hx0
      rw [hx0] at hx
      exact ctx.certificate.orderedField.lt_irrefl _ hx

private theorem f2r_pow_pos (r : radix)
    (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) :
    0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val ^
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p := by
  have hr := r.radix_prop
  change (if (2 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val
    then true else false) = true at hr
  have hbase : (2 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val := by
    simpa using hr
  apply Int.pow_pos
  omega

private theorem f2r_bpow_pos (ctx : ExactRealContext) (r : radix) (e : Z) :
    ctx.spec.lt ctx.spec.zero
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx r e) := by
  cases e with
  | Z0 =>
    change ctx.spec.lt ctx.spec.zero ctx.spec.one
    exact f2r_one_pos ctx
  | Zpos p =>
    change ctx.spec.lt ctx.spec.zero
      (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val ^
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)))
    exact f2r_ofZ_int_pos ctx _ (f2r_pow_pos r p)
  | Zneg p =>
    change ctx.spec.lt ctx.spec.zero (ctx.spec.inv (ctx.spec.ofZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val ^
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))))
    apply f2r_inv_pos ctx
    exact f2r_ofZ_int_pos ctx _ (f2r_pow_pos r p)

private theorem f2r_zneg_eq
    (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zneg p =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos p) := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  rfl

private theorem f2r_zabs_pos
    (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) :
    Zabs (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos p) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos p := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos p)) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos p)
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]

private theorem f2r_zabs_neg
    (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) :
    Zabs (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zneg p) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos p := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zneg p)) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos p)
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]

private theorem f2r_neg_mul_abs (ctx : ExactRealContext) (x y : ctx.spec.carrier) :
    ctx.spec.mul (ctx.spec.neg x) y = ctx.spec.neg (ctx.spec.mul x y) := by
  have hsum : ctx.spec.add (ctx.spec.mul (ctx.spec.neg x) y) (ctx.spec.mul x y) =
      ctx.spec.zero := by
    calc
      ctx.spec.add (ctx.spec.mul (ctx.spec.neg x) y) (ctx.spec.mul x y) =
          ctx.spec.add (ctx.spec.mul y (ctx.spec.neg x)) (ctx.spec.mul y x) := by
            rw [ctx.certificate.orderedField.mul_comm (ctx.spec.neg x) y,
              ctx.certificate.orderedField.mul_comm x y]
      _ = ctx.spec.mul y (ctx.spec.add (ctx.spec.neg x) x) :=
        (ctx.certificate.orderedField.left_distrib y (ctx.spec.neg x) x).symm
      _ = ctx.spec.mul y ctx.spec.zero := by
        rw [ctx.certificate.orderedField.neg_add_cancel]
      _ = ctx.spec.zero := ctx.certificate.orderedField.mul_zero y
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

theorem F2R_abs (ctx : ExactRealContext) : F2R_absStatement ctx := by
  intro beta f
  rcases f with ⟨m, e⟩
  cases m with
  | Z0 =>
    simp only [Fabs]
    change ctx.spec.mul (ctx.spec.ofZ
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e) =
      ctx.spec.abs (ctx.spec.mul (ctx.spec.ofZ
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e))
    rw [ctx.certificate.sourceLaws.ofZ_zero,
      ctx.certificate.orderedField.zero_mul]
    exact (ctx.certificate.sourceLaws.abs_nonnegative ctx.spec.zero
      (ctx.certificate.orderedField.le_refl ctx.spec.zero)).symm
  | Zpos p =>
    simp only [Fabs]
    rw [f2r_zabs_pos]
    change ctx.spec.mul (ctx.spec.ofZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos p))
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e) =
      ctx.spec.abs (ctx.spec.mul (ctx.spec.ofZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos p))
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e))
    have hle := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
      (f2r_mul_pos ctx (f2r_ofZ_pos ctx p) (f2r_bpow_pos ctx beta e))
    exact (ctx.certificate.sourceLaws.abs_nonnegative _ hle.1).symm
  | Zneg p =>
    simp only [Fabs]
    rw [f2r_zabs_neg]
    change ctx.spec.mul (ctx.spec.ofZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos p))
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e) =
      ctx.spec.abs (ctx.spec.mul (ctx.spec.ofZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zneg p))
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e))
    have hpos := f2r_mul_pos ctx (f2r_ofZ_pos ctx p) (f2r_bpow_pos ctx beta e)
    have hneg : ctx.spec.mul (ctx.spec.ofZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zneg p))
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e) =
        ctx.spec.neg (ctx.spec.mul (ctx.spec.ofZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos p))
          (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e)) := by
      rw [f2r_zneg_eq, ctx.certificate.sourceLaws.ofZ_neg]
      exact f2r_neg_mul_abs ctx _ _
    calc
      ctx.spec.mul (ctx.spec.ofZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos p))
          (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e) =
          ctx.spec.neg (ctx.spec.neg (ctx.spec.mul (ctx.spec.ofZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos p))
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e))) :=
        (f2r_neg_neg ctx _).symm
      _ = ctx.spec.abs (ctx.spec.neg (ctx.spec.mul (ctx.spec.ofZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos p))
          (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e))) :=
        (ctx.certificate.sourceLaws.abs_negative _
          (f2r_neg_lt_zero ctx _ hpos)).symm
      _ = ctx.spec.abs (ctx.spec.mul (ctx.spec.ofZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zneg p))
          (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e)) :=
        congrArg ctx.spec.abs hneg.symm

end CompCert4Lean.Flocq.Calc.Operations

namespace CompCert4Lean.Flocq.Calc.Operations

theorem Falign_spec_exp : Falign_spec_expStatement := by
  intro beta f1 f2
  rcases f1 with ⟨m1, e1⟩
  rcases f2 with ⟨m2, e2⟩
  simp only [Falign]
  split <;> simp [CompCert4Lean.Flocq.Core.Defs.Fexp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.leb,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.min] at * <;> omega

private theorem f2r_neg_mul (ctx : ExactRealContext) (x y : ctx.spec.carrier) :
    ctx.spec.mul (ctx.spec.neg x) y = ctx.spec.neg (ctx.spec.mul x y) := by
  have hsum : ctx.spec.add (ctx.spec.mul (ctx.spec.neg x) y) (ctx.spec.mul x y) = ctx.spec.zero := by
    calc
      ctx.spec.add (ctx.spec.mul (ctx.spec.neg x) y) (ctx.spec.mul x y) =
          ctx.spec.add (ctx.spec.mul y (ctx.spec.neg x)) (ctx.spec.mul y x) := by
            rw [ctx.certificate.orderedField.mul_comm (ctx.spec.neg x) y,
              ctx.certificate.orderedField.mul_comm x y]
      _ = ctx.spec.mul y (ctx.spec.add (ctx.spec.neg x) x) :=
        (ctx.certificate.orderedField.left_distrib y (ctx.spec.neg x) x).symm
      _ = ctx.spec.mul y ctx.spec.zero := by
        rw [ctx.certificate.orderedField.neg_add_cancel]
      _ = ctx.spec.zero := ctx.certificate.orderedField.mul_zero y
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

theorem F2R_opp (ctx : ExactRealContext) : F2R_oppStatement ctx := by
  intro beta f
  rcases f with ⟨m, e⟩
  change ctx.spec.mul (ctx.spec.ofZ (Zopp m))
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e) =
    ctx.spec.neg (ctx.spec.mul (ctx.spec.ofZ m)
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e))
  rw [ctx.certificate.sourceLaws.ofZ_neg]
  exact f2r_neg_mul ctx _ _

end CompCert4Lean.Flocq.Calc.Operations

namespace CompCert4Lean.Flocq.Calc.Operations

theorem Fexp_Fplus : Fexp_FplusStatement := by
  intro beta f1 f2
  change (Falign f1 f2).2 = Zmin (Fexp f1) (Fexp f2)
  exact Falign_spec_exp beta f1 f2

end CompCert4Lean.Flocq.Calc.Operations

namespace CompCert4Lean.Flocq.Calc.Operations

theorem F2R_mult (ctx : ExactRealContext) : F2R_multStatement ctx := by
  intro beta f1 f2
  rcases f1 with ⟨m1, e1⟩
  rcases f2 with ⟨m2, e2⟩
  change ctx.spec.mul (ctx.spec.ofZ (Zmul m1 m2))
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Zadd e1 e2)) =
    ctx.spec.mul
      (ctx.spec.mul (ctx.spec.ofZ m1)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1))
      (ctx.spec.mul (ctx.spec.ofZ m2)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2))
  change ctx.spec.mul
      (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx (Zmul m1 m2))
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Zadd e1 e2)) =
    ctx.spec.mul
      (ctx.spec.mul (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx m1)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1))
      (ctx.spec.mul (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx m2)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2))
  have hmul :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR ctx m1 m2
  have hpow := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta e1 e2
  have hmul' :
      CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx (Zmul m1 m2) =
        ctx.spec.mul (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx m1)
          (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx m2) := by
    exact hmul
  rw [hmul', hpow]
  calc
    ctx.spec.mul
        (ctx.spec.mul (ctx.spec.ofZ m1) (ctx.spec.ofZ m2))
        (ctx.spec.mul
          (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1)
          (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2)) =
        ctx.spec.mul (ctx.spec.ofZ m1)
          (ctx.spec.mul (ctx.spec.ofZ m2)
            (ctx.spec.mul
              (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1)
              (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2))) :=
      ctx.certificate.orderedField.mul_assoc _ _ _
    _ = ctx.spec.mul (ctx.spec.ofZ m1)
          (ctx.spec.mul
            (ctx.spec.mul (ctx.spec.ofZ m2)
              (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1))
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2)) := by
      exact congrArg (ctx.spec.mul (ctx.spec.ofZ m1))
        (ctx.certificate.orderedField.mul_assoc _ _ _).symm
    _ = ctx.spec.mul
          (ctx.spec.ofZ m1)
          (ctx.spec.mul
            (ctx.spec.mul
              (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1)
              (ctx.spec.ofZ m2))
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2)) := by
      exact congrArg (ctx.spec.mul (ctx.spec.ofZ m1))
        (congrArg (fun t => ctx.spec.mul t
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2))
          (ctx.certificate.orderedField.mul_comm _ _))
    _ = ctx.spec.mul
          (ctx.spec.mul (ctx.spec.ofZ m1)
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1))
          (ctx.spec.mul (ctx.spec.ofZ m2)
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2)) := by
      calc
        ctx.spec.mul (ctx.spec.ofZ m1)
            (ctx.spec.mul
              (ctx.spec.mul
                (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1)
                (ctx.spec.ofZ m2))
              (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2)) =
            ctx.spec.mul (ctx.spec.ofZ m1)
              (ctx.spec.mul
                (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e1)
                (ctx.spec.mul (ctx.spec.ofZ m2)
                  (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e2))) := by
          rw [ctx.certificate.orderedField.mul_assoc]
        _ = _ := (ctx.certificate.orderedField.mul_assoc _ _ _).symm

end CompCert4Lean.Flocq.Calc.Operations
