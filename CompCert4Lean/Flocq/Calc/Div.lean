import CompCert4Lean.Flocq.Calc.Bracket

/-!
# Floating-point division helpers

This module translates the executable definitions selected from
`Flocq.Calc.Div`.  The two source proofs assigned to the later proof phase
are retained as exact proposition descriptors.
-/

namespace CompCert4Lean.Flocq.Calc.Div

abbrev R := CompCert4Lean.Flocq.Core.Float_prop.R
abbrev Z := CompCert4Lean.Flocq.Core.Float_prop.Z
abbrev radix := CompCert4Lean.Flocq.Core.Float_prop.radix
abbrev location := CompCert4Lean.Flocq.Calc.Bracket.location

abbrev Z0 : Z := CompCert4Lean.Flocq.Core.Float_prop.Z0
abbrev Zone : Z := CompCert4Lean.Flocq.Core.Float_prop.Zone
abbrev Zadd := CompCert4Lean.Flocq.Core.Float_prop.Zadd
abbrev Zsub := CompCert4Lean.Flocq.Core.Zaux.Zsub
abbrev Zmul := CompCert4Lean.Flocq.Core.Float_prop.Zmul
abbrev Zdiv_eucl :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl
abbrev Zdigits := CompCert4Lean.Flocq.Core.Float_prop.Zdigits
abbrev Zle := CompCert4Lean.Flocq.Core.Float_prop.Zle
abbrev Zle_bool := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zle_bool
abbrev Zlt := CompCert4Lean.Flocq.Core.Float_prop.Zlt
abbrev Zpower := CompCert4Lean.Flocq.Core.Float_prop.Zpower

abbrev IZR := CompCert4Lean.Flocq.Core.Float_prop.IZR
abbrev Rdiv := CompCert4Lean.Flocq.Core.Raux.Rdiv
abbrev float := CompCert4Lean.Flocq.Core.Float_prop.float
abbrev Float (beta : radix) (m e : Z) : float beta :=
  CompCert4Lean.Flocq.Core.Float_prop.Float beta m e
abbrev F2R {beta : radix} (f : float beta) : R :=
  CompCert4Lean.Flocq.Core.Float_prop.F2R f
abbrev mag := CompCert4Lean.Flocq.Core.Float_prop.mag
abbrev mag_prop := CompCert4Lean.Flocq.Core.Raux.mag_prop
abbrev mag_val {beta : radix} {x : R} (m : mag_prop beta x) : Z :=
  CompCert4Lean.Flocq.Core.Raux.mag_val m
abbrev inbetween_float := CompCert4Lean.Flocq.Calc.Bracket.inbetween_float
abbrev new_location := CompCert4Lean.Flocq.Calc.Bracket.new_location
abbrev loc_Exact := CompCert4Lean.Flocq.Calc.Bracket.loc_Exact

abbrev ExactRealContext := CompCert4Lean.Flocq.Calc.Bracket.ExactRealContext

namespace Exact

abbrev F2R := CompCert4Lean.Flocq.Calc.Bracket.F2R
abbrev Rdiv := CompCert4Lean.Flocq.Calc.Bracket.Rdiv
abbrev Magnitude := CompCert4Lean.Flocq.Core.Float_prop.Exact.Magnitude
abbrev bpow (ctx : ExactRealContext) (beta : radix) (e : Z) :
    CompCert4Lean.Flocq.Core.Float_prop.Exact.R ctx :=
  CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e
abbrev mag (ctx : ExactRealContext) (magnitude : Magnitude ctx) (beta : radix)
    (x : CompCert4Lean.Flocq.Core.Float_prop.Exact.R ctx) : Z :=
  CompCert4Lean.Flocq.Core.Float_prop.Exact.mag magnitude beta x

end Exact

/- The source notation `bpow e` is theorem-facing here.  Under RPR-007 the
   mapped identity names the injected exact-real carrier explicitly; the
   runtime/rational carrier remains confined to executable surfaces. -/
abbrev bpow (ctx : ExactRealContext) (beta : radix) (e : Z) :
    CompCert4Lean.Flocq.Core.Float_prop.Exact.R ctx :=
  CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e

def Fdiv_core (beta : radix) (m1 e1 m2 e2 e : Z) : Z × location :=
  let (m1', m2') :=
    if Zle_bool e (Zsub e1 e2) then
      (Zmul m1 (Zpower (beta : Z) (Zsub (Zsub e1 e2) e)), m2)
    else
      (m1, Zmul m2 (Zpower (beta : Z) (Zsub e (Zsub e1 e2))))
  let (q, r) := Zdiv_eucl m1' m2'
  (q, new_location m2' r loc_Exact)

/-! Exact source proposition descriptors for later proof migration.

The explicit `ctx` and (for magnitude) `magnitude` arguments are the
RPR-007 carrier/certificate seam.  The proposition after those arguments is
source-shaped; no extra computational premise is introduced, and construction
of the exact-real laws and magnitude invariant remains a proof-grinding duty.
-/

def mag_div_F2RStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (beta : radix) (m1 e1 m2 e2 : Z),
    Zlt Z0 m1 →
      Zlt Z0 m2 →
        let e :=
          Zsub
            (Zadd (Zdigits beta m1) e1)
            (Zadd (Zdigits beta m2) e2)
        Zle e
            (Exact.mag ctx magnitude beta
              (Exact.Rdiv ctx
                (Exact.F2R ctx (Float beta m1 e1))
                (Exact.F2R ctx (Float beta m2 e2)))) ∧
          Zle
            (Exact.mag ctx magnitude beta
              (Exact.Rdiv ctx
                (Exact.F2R ctx (Float beta m1 e1))
                (Exact.F2R ctx (Float beta m2 e2))))
            (Zadd e Zone)

def Fdiv_core_correctStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (m1 e1 m2 e2 e : Z),
      Zlt Z0 m1 →
      Zlt Z0 m2 →
        let (m, l) := Fdiv_core beta m1 e1 m2 e2 e
        inbetween_float ctx beta m e
          (Exact.Rdiv ctx
            (Exact.F2R ctx (Float beta m1 e1))
            (Exact.F2R ctx (Float beta m2 e2))) l

end CompCert4Lean.Flocq.Calc.Div

namespace CompCert4Lean.Flocq.Calc.Div

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.Calc
open CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals

private theorem div_iadd (a b : Z) :
    intOfZ (Zadd a b) = intOfZ a + intOfZ b :=
  intOfZ_zOfInt _

private theorem div_isub (a b : Z) :
    intOfZ (Zsub a b) = intOfZ a - intOfZ b :=
  intOfZ_zOfInt _

private theorem div_imul (a b : Z) :
    intOfZ (Zmul a b) = intOfZ a * intOfZ b :=
  intOfZ_zOfInt _

private theorem div_izero : intOfZ Z0 = 0 := rfl
private theorem div_ione : intOfZ Zone = 1 := rfl
private theorem div_itwo : intOfZ Zaux.Ztwo = 2 := rfl

private theorem div_compare (a b : Z) :
    Zaux.Zcompare a b =
      (if intOfZ a < intOfZ b then Zaux.Lt
       else if intOfZ a = intOfZ b then Zaux.Eq else Zaux.Gt) := rfl

private theorem div_new_location (b r : Z) :
    new_location b r loc_Exact =
      if r = Z0 then loc_Exact
      else Bracket.loc_Inexact (Zaux.Zcompare (Zmul Zaux.Ztwo r) b) := by
  by_cases hr : r = Z0
  · subst r
    simp [new_location, Bracket.new_location, Bracket.new_location_even,
      Bracket.new_location_odd, ZArith.Zbool.Zeq_bool]
  · have hz : Zaux.Zeq_bool r Z0 = false := by
      simp [Zaux.Zeq_bool, ZArith.Zbool.Zeq_bool, hr]
    rw [if_neg hr]
    unfold new_location Bracket.new_location
    split
    · simp only [Bracket.new_location_even, hz, Bool.false_eq_true, if_false]
      cases hc : Zaux.Zcompare (Zmul Zaux.Ztwo r) b <;> simp only [hc] <;> rfl
    · rename_i heven
      have heven' : Zaux.Zeven b = false := Bool.eq_false_iff.mpr heven
      obtain ⟨p, hp⟩ := Zaux.Zeven_ex b
      rw [heven'] at hp
      have hip := congrArg intOfZ hp
      simp only [Bool.false_eq_true, if_false, div_iadd, div_imul, div_itwo] at hip
      change intOfZ b = 2 * intOfZ p + 1 at hip
      have hne : 2 * intOfZ r ≠ intOfZ b := by omega
      simp only [Bracket.new_location_odd, hz, Bool.false_eq_true, if_false,
        div_compare, div_iadd, div_imul, div_itwo, div_ione]
      by_cases hlt : 2 * intOfZ r < intOfZ b
      · rw [if_pos hlt]
        by_cases hlt' : 2 * intOfZ r + 1 < intOfZ b
        · simp [hlt']
        · have heq : 2 * intOfZ r + 1 = intOfZ b := by omega
          simp [heq]
      · have hlt' : ¬ 2 * intOfZ r + 1 < intOfZ b := by omega
        have hne' : 2 * intOfZ r + 1 ≠ intOfZ b := by omega
        simp [hlt, hne, hlt', hne']

private theorem div_integer_between (ctx : ExactRealContext) (d b r : Z)
    (hr : Zle Z0 r) (hrb : Zlt r b) :
    Bracket.inbetween ctx (ctx.spec.ofZ d) (ctx.spec.ofZ (Zadd d b))
      (ctx.spec.ofZ (Zadd d r)) (new_location b r loc_Exact) := by
  rw [div_new_location]
  by_cases hr0 : r = Z0
  · rw [if_pos hr0, hr0]
    apply Bracket.inbetween_Exact
    change ctx.spec.ofZ (Zadd d Z0) = ctx.spec.ofZ d
    rw [ctx.certificate.sourceLaws.ofZ_add,
      ctx.certificate.sourceLaws.ofZ_zero, ctx.certificate.orderedField.add_zero]
  · rw [if_neg hr0]
    apply Bracket.inbetween_Inexact
    · constructor
      · apply RIneq.IZR_lt ctx
        change intOfZ d < intOfZ (Zadd d r)
        rw [div_iadd]
        have hpos : 0 < intOfZ r := by
          change 0 ≤ intOfZ r at hr
          have hn : intOfZ r ≠ 0 := fun h => hr0 (intOfZ_injective h)
          omega
        omega
      · apply RIneq.IZR_lt ctx
        change intOfZ (Zadd d r) < intOfZ (Zadd d b)
        simp only [div_iadd]
        change intOfZ r < intOfZ b at hrb
        omega
    · change Raux.Exact.Rcompare ctx (ctx.spec.ofZ (Zadd d r))
          (Raux.Exact.Rdiv ctx (ctx.spec.add (ctx.spec.ofZ d) (ctx.spec.ofZ (Zadd d b)))
            (Raux.Exact.Rtwo ctx)) = _
      rw [Raux.Rcompare_half_r ctx]
      have htwo : ctx.spec.ofZ Zaux.Ztwo =
          ctx.spec.add ctx.spec.one ctx.spec.one := by
        rw [show Zaux.Ztwo = Zadd Zone Zone by rfl,
          ctx.certificate.sourceLaws.ofZ_add, ctx.certificate.sourceLaws.ofZ_one]
      change Raux.Exact.Rcompare ctx
          (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
            (ctx.spec.ofZ (Zadd d r)))
          (ctx.spec.add (ctx.spec.ofZ d) (ctx.spec.ofZ (Zadd d b))) = _
      have hm : ctx.spec.ofZ (Zmul Zaux.Ztwo (Zadd d r)) =
          ctx.spec.mul (ctx.spec.ofZ Zaux.Ztwo) (ctx.spec.ofZ (Zadd d r)) :=
        RIneq.mult_IZR ctx _ _
      rw [← htwo, ← ctx.certificate.sourceLaws.ofZ_add, ← hm]
      exact (Raux.Rcompare_IZR ctx _ _).trans (by
        simp only [div_compare, div_imul, div_iadd, div_itwo]
        have hlt : 2 * (intOfZ d + intOfZ r) < intOfZ d + (intOfZ d + intOfZ b) ↔
            2 * intOfZ r < intOfZ b := by omega
        have heq : 2 * (intOfZ d + intOfZ r) = intOfZ d + (intOfZ d + intOfZ b) ↔
            2 * intOfZ r = intOfZ b := by omega
        simp only [hlt, heq])

private theorem div_ofZ_ne_zero (ctx : ExactRealContext) (b : Z)
    (hb : Zlt Z0 b) : ctx.spec.ofZ b ≠ ctx.spec.zero := by
  have hp : ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.ofZ b) := RIneq.IZR_lt ctx _ _ hb
  rw [ctx.certificate.sourceLaws.ofZ_zero] at hp
  intro h
  rw [h] at hp
  exact ctx.certificate.orderedField.lt_irrefl _ hp

private theorem div_mul_left_comm (ctx : ExactRealContext) (x y z : ctx.spec.carrier) :
    ctx.spec.mul x (ctx.spec.mul y z) = ctx.spec.mul y (ctx.spec.mul x z) := by
  rw [← ctx.certificate.orderedField.mul_assoc,
    ctx.certificate.orderedField.mul_comm x y, ctx.certificate.orderedField.mul_assoc]

private theorem div_mul_inv_cancel (ctx : ExactRealContext) (x y : ctx.spec.carrier)
    (hy : y ≠ ctx.spec.zero) :
    ctx.spec.mul (ctx.spec.mul x y) (ctx.spec.inv y) = x := by
  rw [ctx.certificate.orderedField.mul_assoc,
    ctx.certificate.orderedField.mul_comm y (ctx.spec.inv y),
    ctx.certificate.orderedField.inv_mul_cancel _ hy,
    ctx.certificate.orderedField.mul_one]

private theorem div_div_mul_cancel (ctx : ExactRealContext) (x y : ctx.spec.carrier)
    (hy : y ≠ ctx.spec.zero) :
    ctx.spec.mul (ctx.spec.div x y) y = x := by
  rw [ctx.certificate.orderedField.div_eq_mul_inv,
    ctx.certificate.orderedField.mul_assoc,
    ctx.certificate.orderedField.inv_mul_cancel _ hy,
    ctx.certificate.orderedField.mul_one]

private theorem div_eq_of_mul (ctx : ExactRealContext) (x y z : ctx.spec.carrier)
    (hy : y ≠ ctx.spec.zero) (h : ctx.spec.mul z y = x) : ctx.spec.div x y = z := by
  rw [ctx.certificate.orderedField.div_eq_mul_inv, ← h, div_mul_inv_cancel ctx _ _ hy]

private theorem div_quotient_between (ctx : ExactRealContext) (a b : Z)
    (hb : Zlt Z0 b) :
    let qr := Zdiv_eucl a b
    Bracket.inbetween ctx (ctx.spec.ofZ qr.1) (ctx.spec.ofZ (Zadd qr.1 Zone))
      (ctx.spec.div (ctx.spec.ofZ a) (ctx.spec.ofZ b))
      (new_location b qr.2 loc_Exact) := by
  obtain ⟨hq, hr, hrb⟩ := ZArith.Zdiv.Z_div_mod a b hb
  let q := (Zdiv_eucl a b).1
  let r := (Zdiv_eucl a b).2
  have hbetween := div_integer_between ctx (Zmul b q) b r hr hrb
  have hsum : Zadd (Zmul b q) b = Zmul (Zadd q Zone) b := by
    apply intOfZ_injective
    simp only [div_iadd, div_imul, div_ione, Int.add_mul, Int.one_mul]
    rw [Int.mul_comm (intOfZ b) (intOfZ q)]
  have hq' : Zadd (Zmul b q) r = a := hq.symm
  rw [hq', hsum] at hbetween
  have hbne := div_ofZ_ne_zero ctx b hb
  have hbpos : Bracket.Rlt ctx (Bracket.IZR ctx Z0) (ctx.spec.inv (ctx.spec.ofZ b)) :=
    RIneq.Rinv_0_lt_compat ctx _ (RIneq.IZR_lt ctx _ _ hb)
  have hs := Bracket.inbetween_mult_compat ctx _ _ _ _
    (ctx.spec.inv (ctx.spec.ofZ b)) hbpos hbetween
  have hlow : ctx.spec.mul (ctx.spec.ofZ (Zmul b q)) (ctx.spec.inv (ctx.spec.ofZ b)) =
      ctx.spec.ofZ q := by
    have hm : ctx.spec.ofZ (Zmul b q) = ctx.spec.mul (ctx.spec.ofZ b) (ctx.spec.ofZ q) :=
      RIneq.mult_IZR ctx _ _
    rw [hm, ctx.certificate.orderedField.mul_comm (ctx.spec.ofZ b),
      div_mul_inv_cancel ctx _ _ hbne]
  have hupp : ctx.spec.mul (ctx.spec.ofZ (Zmul (Zadd q Zone) b))
      (ctx.spec.inv (ctx.spec.ofZ b)) = ctx.spec.ofZ (Zadd q Zone) := by
    have hm : ctx.spec.ofZ (Zmul (Zadd q Zone) b) =
        ctx.spec.mul (ctx.spec.ofZ (Zadd q Zone)) (ctx.spec.ofZ b) := RIneq.mult_IZR ctx _ _
    rw [hm, div_mul_inv_cancel ctx _ _ hbne]
  change Bracket.inbetween ctx
    (ctx.spec.mul (ctx.spec.ofZ (Zmul b q)) (ctx.spec.inv (ctx.spec.ofZ b)))
    (ctx.spec.mul (ctx.spec.ofZ (Zmul (Zadd q Zone) b)) (ctx.spec.inv (ctx.spec.ofZ b)))
    (ctx.spec.mul (ctx.spec.ofZ a) (ctx.spec.inv (ctx.spec.ofZ b))) _ at hs
  rw [hlow, hupp, ← ctx.certificate.orderedField.div_eq_mul_inv] at hs
  exact hs

private theorem div_float_quotient (ctx : ExactRealContext) (beta : radix)
    (a b e t : Z) (hb : Zlt Z0 b) :
    Exact.Rdiv ctx (Exact.F2R ctx (Float beta a (Zadd e t)))
        (Exact.F2R ctx (Float beta b t)) =
      ctx.spec.mul (ctx.spec.div (ctx.spec.ofZ a) (ctx.spec.ofZ b)) (bpow ctx beta e) := by
  have hbne := div_ofZ_ne_zero ctx b hb
  have hfpos := Float_prop.F2R_gt_0 ctx beta (Float beta b t) hb
  have hfne : Exact.F2R ctx (Float beta b t) ≠ ctx.spec.zero := by
    have hfpos' : ctx.spec.lt ctx.spec.zero (Exact.F2R ctx (Float beta b t)) := hfpos
    intro h
    rw [h] at hfpos'
    exact ctx.certificate.orderedField.lt_irrefl _ hfpos'
  apply div_eq_of_mul ctx _ _ _ hfne
  change ctx.spec.mul
      (ctx.spec.mul (ctx.spec.div (ctx.spec.ofZ a) (ctx.spec.ofZ b)) (bpow ctx beta e))
      (ctx.spec.mul (ctx.spec.ofZ b) (bpow ctx beta t)) =
    ctx.spec.mul (ctx.spec.ofZ a) (bpow ctx beta (Zadd e t))
  have hp : bpow ctx beta (Zadd e t) =
      ctx.spec.mul (bpow ctx beta e) (bpow ctx beta t) := Raux.bpow_plus ctx beta e t
  rw [hp]
  calc
    _ = ctx.spec.mul
        (ctx.spec.mul (ctx.spec.div (ctx.spec.ofZ a) (ctx.spec.ofZ b)) (ctx.spec.ofZ b))
        (ctx.spec.mul (bpow ctx beta e) (bpow ctx beta t)) := by
      simp only [ctx.certificate.orderedField.mul_assoc,
        ctx.certificate.orderedField.mul_comm, div_mul_left_comm]
    _ = _ := by rw [div_div_mul_cancel ctx _ _ hbne]

private theorem div_scaled_between (ctx : ExactRealContext) (beta : radix)
    (a b e : Z) (hb : Zlt Z0 b) :
    let qr := Zdiv_eucl a b
    inbetween_float ctx beta qr.1 e
      (ctx.spec.mul (ctx.spec.div (ctx.spec.ofZ a) (ctx.spec.ofZ b)) (bpow ctx beta e))
      (new_location b qr.2 loc_Exact) := by
  have hp : Bracket.Rlt ctx (Bracket.IZR ctx Z0) (bpow ctx beta e) := by
    change ctx.spec.lt (ctx.spec.ofZ Z0) (bpow ctx beta e)
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact Raux.bpow_gt_0 ctx beta e
  exact Bracket.inbetween_mult_compat ctx _ _ _ _ (bpow ctx beta e) hp
    (div_quotient_between ctx a b hb)

theorem Fdiv_core_correct :
    ∀ (ctx : ExactRealContext), Fdiv_core_correctStatement ctx := by
  intro ctx beta m1 e1 m2 e2 e _hm1 hm2
  dsimp only [Fdiv_core]
  split
  · rename_i he
    have he' : Zle e (Zsub e1 e2) := (ZArith.BinInt.Z.leb_le _ _).mp he
    have hshift : Zle (Zadd e e2) e1 := by
      change intOfZ (Zadd e e2) ≤ intOfZ e1
      change intOfZ e ≤ intOfZ (Zsub e1 e2) at he'
      simp only [div_iadd, div_isub] at *
      omega
    have hd : Zsub e1 (Zadd e e2) = Zsub (Zsub e1 e2) e := by
      apply intOfZ_injective
      simp only [div_isub, div_iadd]
      omega
    have hf : Exact.F2R ctx (Float beta m1 e1) =
        Exact.F2R ctx (Float beta
          (Zmul m1 (Zpower (beta : Z) (Zsub (Zsub e1 e2) e))) (Zadd e e2)) := by
      simpa only [hd] using
        Float_prop.F2R_change_exp ctx beta (Zadd e e2) m1 e1 hshift
    dsimp only
    rw [hf, div_float_quotient ctx beta _ m2 e e2 hm2]
    exact div_scaled_between ctx beta _ m2 e hm2
  · rename_i he
    have hefalse : Zle_bool e (Zsub e1 e2) = false := Bool.eq_false_iff.mpr he
    have he' : Zlt (Zsub e1 e2) e := (ZArith.BinInt.Z.leb_gt _ _).mp hefalse
    have hshift : Zle (Zsub e1 e) e2 := by
      change intOfZ (Zsub e1 e) ≤ intOfZ e2
      change intOfZ (Zsub e1 e2) < intOfZ e at he'
      simp only [div_isub] at *
      omega
    have hd : Zsub e2 (Zsub e1 e) = Zsub e (Zsub e1 e2) := by
      apply intOfZ_injective
      simp only [div_isub]
      omega
    have hpow : Zle Z0 (Zsub e (Zsub e1 e2)) := by
      change 0 ≤ intOfZ (Zsub e (Zsub e1 e2))
      change intOfZ (Zsub e1 e2) < intOfZ e at he'
      simp only [div_isub] at *
      omega
    have hb : Zlt Z0 (Zmul m2 (Zpower (beta : Z) (Zsub e (Zsub e1 e2)))) := by
      have hp := Zaux.Zpower_gt_0 beta _ hpow
      change 0 < intOfZ (Zmul m2 (Zpower (beta : Z) (Zsub e (Zsub e1 e2))))
      rw [div_imul]
      exact Int.mul_pos hm2 hp
    have hf : Exact.F2R ctx (Float beta m2 e2) =
        Exact.F2R ctx (Float beta
          (Zmul m2 (Zpower (beta : Z) (Zsub e (Zsub e1 e2)))) (Zsub e1 e)) := by
      simpa only [hd] using
        Float_prop.F2R_change_exp ctx beta (Zsub e1 e) m2 e2 hshift
    have heq : e1 = Zadd e (Zsub e1 e) := by
      apply intOfZ_injective
      simp only [div_iadd, div_isub]
      omega
    dsimp only
    rw [hf]
    have hnum : Exact.F2R ctx (Float beta m1 e1) =
        Exact.F2R ctx (Float beta m1 (Zadd e (Zsub e1 e))) :=
      congrArg (fun t => Exact.F2R ctx (Float beta m1 t)) heq
    rw [hnum]
    rw [div_float_quotient ctx beta m1 _ e (Zsub e1 e) hb]
    exact div_scaled_between ctx beta m1 _ e hb

end CompCert4Lean.Flocq.Calc.Div

namespace CompCert4Lean.Flocq.Calc.Div

theorem mag_div_F2R (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) :
    mag_div_F2RStatement ctx magnitude := by
  intro beta mantissa₁ exponent₁ mantissa₂ exponent₂ positive₁ positive₂
  have nonzero₁ : mantissa₁ ≠ Z0 := by
    intro equal
    subst mantissa₁
    change (0 : Int) < 0 at positive₁
    omega
  have nonzero₂ : mantissa₂ ≠ Z0 := by
    intro equal
    subst mantissa₂
    change (0 : Int) < 0 at positive₂
    omega
  have float_nonzero₁ : Exact.F2R ctx (Float beta mantissa₁ exponent₁) ≠ ctx.spec.zero := by
    intro equal
    have positive := CompCert4Lean.Flocq.Core.Float_prop.F2R_gt_0 ctx beta
      (Float beta mantissa₁ exponent₁) positive₁
    change ctx.spec.lt ctx.spec.zero (Exact.F2R ctx (Float beta mantissa₁ exponent₁)) at positive
    rw [equal] at positive
    exact ctx.certificate.orderedField.lt_irrefl _ positive
  have float_nonzero₂ : Exact.F2R ctx (Float beta mantissa₂ exponent₂) ≠ ctx.spec.zero := by
    intro equal
    have positive := CompCert4Lean.Flocq.Core.Float_prop.F2R_gt_0 ctx beta
      (Float beta mantissa₂ exponent₂) positive₂
    change ctx.spec.lt ctx.spec.zero (Exact.F2R ctx (Float beta mantissa₂ exponent₂)) at positive
    rw [equal] at positive
    exact ctx.certificate.orderedField.lt_irrefl _ positive
  have bounds := CompCert4Lean.Flocq.Core.Raux.mag_div ctx magnitude beta
    (Exact.F2R ctx (Float beta mantissa₁ exponent₁))
    (Exact.F2R ctx (Float beta mantissa₂ exponent₂)) float_nonzero₁ float_nonzero₂
  have magnitude₁ := CompCert4Lean.Flocq.Core.Float_prop.mag_F2R_Zdigits
    ctx magnitude beta mantissa₁ exponent₁ nonzero₁
  have magnitude₂ := CompCert4Lean.Flocq.Core.Float_prop.mag_F2R_Zdigits
    ctx magnitude beta mantissa₂ exponent₂ nonzero₂
  change Exact.mag ctx magnitude beta (Exact.F2R ctx (Float beta mantissa₁ exponent₁)) =
    Zadd (Zdigits beta mantissa₁) exponent₁ at magnitude₁
  change Exact.mag ctx magnitude beta (Exact.F2R ctx (Float beta mantissa₂ exponent₂)) =
    Zadd (Zdigits beta mantissa₂) exponent₂ at magnitude₂
  change Zle (Zsub (Exact.mag ctx magnitude beta (Exact.F2R ctx (Float beta mantissa₁ exponent₁)))
      (Exact.mag ctx magnitude beta (Exact.F2R ctx (Float beta mantissa₂ exponent₂)))) _ ∧
    Zle _ (Zadd (Zsub (Exact.mag ctx magnitude beta (Exact.F2R ctx (Float beta mantissa₁ exponent₁)))
      (Exact.mag ctx magnitude beta (Exact.F2R ctx (Float beta mantissa₂ exponent₂)))) Zone) at bounds
  rw [magnitude₁, magnitude₂] at bounds
  exact bounds

end CompCert4Lean.Flocq.Calc.Div
