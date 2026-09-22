import CompCert4Lean.Flocq.Calc.Bracket
import CompCert4Lean.Flocq.Core.Digits
import CompCert4Lean.Flocq.Core.Raux

/-!
# Flocq square-root helpers

This module translates the executable and statement-bearing surface selected
from `Flocq.Calc.Sqrt`.  Proofs assigned to the later proof-migration phase
are represented by exact source-shaped proposition descriptors.
-/

namespace CompCert4Lean.Flocq.Calc.Sqrt

abbrev R := CompCert4Lean.Flocq.Core.Raux.R
abbrev Z := CompCert4Lean.Flocq.Core.Zaux.Z
abbrev radix := CompCert4Lean.Flocq.Core.Zaux.radix
abbrev comparison := CompCert4Lean.Flocq.Core.Zaux.comparison

abbrev Lt : comparison := CompCert4Lean.Flocq.Core.Zaux.Lt
abbrev Eq : comparison := CompCert4Lean.Flocq.Core.Zaux.Eq
abbrev Gt : comparison := CompCert4Lean.Flocq.Core.Zaux.Gt

abbrev Z0 : Z := CompCert4Lean.Flocq.Core.Zaux.Z0
abbrev Zone : Z := CompCert4Lean.Flocq.Core.Zaux.Zone
abbrev Ztwo : Z := CompCert4Lean.Flocq.Core.Zaux.Ztwo
abbrev Zadd := CompCert4Lean.Flocq.Core.Zaux.Zadd
abbrev Zmul := CompCert4Lean.Flocq.Core.Zaux.Zmul
abbrev Zsub := CompCert4Lean.Flocq.Core.Zaux.Zsub
abbrev Zdiv2 := CompCert4Lean.Flocq.Core.Raux.Zdiv2
abbrev Zpower := CompCert4Lean.Flocq.Core.Zaux.Zpower
abbrev Zeq_bool := CompCert4Lean.Flocq.Core.Zaux.Zeq_bool
abbrev Zle_bool := CompCert4Lean.Flocq.Core.Zaux.Zle_bool
abbrev Zle := CompCert4Lean.Flocq.Core.Zaux.Zle
abbrev Zlt := CompCert4Lean.Flocq.Core.Zaux.Zlt
abbrev Zdigits := CompCert4Lean.Flocq.Core.Digits.Zdigits

abbrev IZR := CompCert4Lean.Flocq.Core.Raux.IZR
abbrev sqrt := CompCert4Lean.Flocq.Core.Raux.sqrt
abbrev mag := CompCert4Lean.Flocq.Core.Raux.mag
abbrev bpow := CompCert4Lean.Flocq.Core.Raux.bpow

abbrev location := CompCert4Lean.Flocq.Calc.Bracket.location
abbrev loc_Exact : location := CompCert4Lean.Flocq.Calc.Bracket.loc_Exact
abbrev loc_Inexact (c : comparison) : location :=
  CompCert4Lean.Flocq.Calc.Bracket.loc_Inexact c

abbrev ExactRealContext := CompCert4Lean.Flocq.Calc.Bracket.ExactRealContext

namespace Exact

abbrev Magnitude (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Float_prop.Exact.Magnitude ctx
abbrev F2R := CompCert4Lean.Flocq.Calc.Bracket.F2R
abbrev mag (ctx : ExactRealContext) (magnitude : Magnitude ctx) (beta : radix)
    (x : CompCert4Lean.Flocq.Core.Float_prop.Exact.R ctx) : Z :=
  CompCert4Lean.Flocq.Core.Float_prop.Exact.mag magnitude beta x
abbrev sqrt := CompCert4Lean.Flocq.Core.Raux.Exact.sqrt

end Exact

abbrev float := CompCert4Lean.Flocq.Core.Float_prop.float
abbrev Float (beta : radix) (m e : Z) : float beta :=
  CompCert4Lean.Flocq.Core.Float_prop.Float beta m e
abbrev F2R {beta : radix} (f : float beta) : R :=
  CompCert4Lean.Flocq.Core.Float_prop.F2R f

def Fsqrt_core (beta : radix) (m1 e1 e : Z) : Z × location :=
  let _d1 := Zdigits beta m1
  let m1' := Zmul m1 (Zpower (beta : Z) (Zsub e1 (Zmul Ztwo e)))
  let qr := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sqrtrem m1'
  let q := qr.1
  let r := qr.2
  let l :=
    if Zeq_bool r Z0 then
      loc_Exact
    else
      loc_Inexact (if Zle_bool r q then Lt else Gt)
  (q, l)

/-! Exact source proposition descriptors for later proof migration. -/

def mag_sqrt_F2RStatement (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) : Prop :=
  ∀ (beta : radix) (m1 e1 : Z),
    Zlt Z0 m1 →
      Exact.mag ctx magnitude beta
          (Exact.sqrt ctx (Exact.F2R ctx (Float beta m1 e1))) =
        Zdiv2 (Zadd (Zadd (Zdigits beta m1) e1) Zone)

def Fsqrt_core_correctStatement (ctx : ExactRealContext) : Prop :=
  ∀ (beta : radix) (m1 e1 e : Z),
    Zlt Z0 m1 →
    Zle (Zmul Ztwo e) e1 →
    let (m, l) := Fsqrt_core beta m1 e1 e
    CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx beta m e
      (Exact.sqrt ctx (Exact.F2R ctx (Float beta m1 e1))) l

end CompCert4Lean.Flocq.Calc.Sqrt

namespace CompCert4Lean.Flocq.Calc.Sqrt

theorem mag_sqrt_F2R : ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx),
    mag_sqrt_F2RStatement ctx magnitude := by
  intro ctx magnitude beta m1 e1 hm
  have hpos := CompCert4Lean.Flocq.Core.Float_prop.F2R_gt_0 ctx beta
    (Float beta m1 e1) hm
  have hs := CompCert4Lean.Flocq.Core.Raux.mag_sqrt ctx magnitude beta
    (Exact.F2R ctx (Float beta m1 e1)) hpos
  have hmne : m1 ≠ Z0 := by
    intro hm0
    subst m1
    change (0 : Int) < 0 at hm
    omega
  have hmag :
      (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta
        (Exact.F2R ctx (Float beta m1 e1))).mag_val =
        Zadd (Zdigits beta m1) e1 := by
    exact CompCert4Lean.Flocq.Core.Float_prop.mag_F2R_Zdigits
      ctx magnitude beta m1 e1 hmne
  calc
    Exact.mag ctx magnitude beta
        (Exact.sqrt ctx (Exact.F2R ctx (Float beta m1 e1))) =
        Zdiv2 (Zadd
          (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta
            (Exact.F2R ctx (Float beta m1 e1))).mag_val Zone) := hs
    _ = Zdiv2 (Zadd (Zadd (Zdigits beta m1) e1) Zone) := by
      rw [hmag]

end CompCert4Lean.Flocq.Calc.Sqrt

namespace CompCert4Lean.Flocq.Calc.Sqrt

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals
open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.Calc

private theorem sqrt_int_add (left right : Z) :
    intOfZ (Zadd left right) = intOfZ left + intOfZ right := intOfZ_zOfInt _

private theorem sqrt_int_mul (left right : Z) :
    intOfZ (Zmul left right) = intOfZ left * intOfZ right := intOfZ_zOfInt _

private theorem sqrt_int_sub (left right : Z) :
    intOfZ (Zsub left right) = intOfZ left - intOfZ right := intOfZ_zOfInt _

private theorem sqrt_ofZ_mul (ctx : ExactRealContext) (left right : Z) :
    ctx.spec.ofZ (Zmul left right) = ctx.spec.mul (ctx.spec.ofZ left) (ctx.spec.ofZ right) :=
  RIneq.mult_IZR ctx left right

private theorem sqrt_ofZ_compare (ctx : ExactRealContext) (left right : Z) :
    Raux.Exact.Rcompare ctx (ctx.spec.ofZ left) (ctx.spec.ofZ right) = Zaux.Zcompare left right :=
  Raux.Rcompare_IZR ctx left right

private theorem sqrt_square_lt (ctx : ExactRealContext) (left right : ctx.spec.carrier)
    (squares : ctx.spec.lt (ctx.spec.mul left left) (ctx.spec.mul right right))
    (left_nonnegative : ctx.spec.le ctx.spec.zero left)
    (right_nonnegative : ctx.spec.le ctx.spec.zero right) : ctx.spec.lt left right := by
  apply R_sqr.Rsqr_incrst_0 ctx left right squares
  · change ctx.spec.le (ctx.spec.ofZ Z0) left
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact left_nonnegative
  · change ctx.spec.le (ctx.spec.ofZ Z0) right
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact right_nonnegative

private theorem sqrt_integer_nonnegative (ctx : ExactRealContext) (integer : Z)
    (nonnegative : Zle Z0 integer) : ctx.spec.le ctx.spec.zero (ctx.spec.ofZ integer) := by
  have result := RIneq.IZR_le ctx Z0 integer nonnegative
  change ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.ofZ integer) at result
  simpa only [ctx.certificate.sourceLaws.ofZ_zero] using result

private theorem sqrt_square (ctx : ExactRealContext) (value : ctx.spec.carrier)
    (nonnegative : ctx.spec.le ctx.spec.zero value) :
    ctx.spec.mul (Exact.sqrt ctx value) (Exact.sqrt ctx value) = value := by
  apply R_sqrt.Rsqr_sqrt ctx value
  change ctx.spec.le (ctx.spec.ofZ Z0) value
  simpa only [ctx.certificate.sourceLaws.ofZ_zero] using nonnegative

private theorem sqrt_square_root (ctx : ExactRealContext) (value : ctx.spec.carrier)
    (nonnegative : ctx.spec.le ctx.spec.zero value) :
    Exact.sqrt ctx (ctx.spec.mul value value) = value := by
  apply R_sqrt.sqrt_Rsqr ctx value
  change ctx.spec.le (ctx.spec.ofZ Z0) value
  simpa only [ctx.certificate.sourceLaws.ofZ_zero] using nonnegative

private theorem sqrt_integer_between (ctx : ExactRealContext) (number root remainder : Z)
    (number_nonnegative : Zle Z0 number)
    (decomposition : number = Zadd (Zmul root root) remainder)
    (remainder_nonnegative : Zle Z0 remainder)
    (remainder_bound : Zle remainder (Zmul Ztwo root)) :
    Bracket.inbetween_int ctx root (Exact.sqrt ctx (ctx.spec.ofZ number))
      (if Zeq_bool remainder Z0 then loc_Exact
       else loc_Inexact (if Zle_bool remainder root then Lt else Gt)) := by
  have remainder_lower : (0 : Int) ≤ intOfZ remainder := remainder_nonnegative
  have remainder_upper : intOfZ remainder ≤ 2 * intOfZ root := by
    change intOfZ remainder ≤ intOfZ (Zmul Ztwo root) at remainder_bound
    simpa only [sqrt_int_mul, show intOfZ Ztwo = 2 by rfl] using remainder_bound
  have root_nonnegative : Zle Z0 root := by
    change (0 : Int) ≤ intOfZ root
    omega
  have next_nonnegative : Zle Z0 (Zadd root Zone) := by
    change (0 : Int) ≤ intOfZ (Zadd root Zone)
    rw [sqrt_int_add, show intOfZ Zone = 1 by rfl]
    change (0 : Int) ≤ intOfZ root at root_nonnegative
    omega
  have real_nonnegative := sqrt_integer_nonnegative ctx number number_nonnegative
  have root_real_nonnegative := sqrt_integer_nonnegative ctx root root_nonnegative
  have next_real_nonnegative := sqrt_integer_nonnegative ctx (Zadd root Zone) next_nonnegative
  have square_root_nonnegative : ctx.spec.le ctx.spec.zero
      (Exact.sqrt ctx (ctx.spec.ofZ number)) := Raux.sqrt_ge_0 ctx _
  have square_value := sqrt_square ctx (ctx.spec.ofZ number) real_nonnegative
  have decomposition_int := congrArg intOfZ decomposition
  simp only [sqrt_int_add, sqrt_int_mul] at decomposition_int
  by_cases exact_remainder : remainder = Z0
  · subst remainder
    simp only [Zeq_bool, Zaux.Zeq_bool, ZArith.Zbool.Zeq_bool]
    apply Bracket.inbetween_Exact
    have square_number : number = Zmul root root := by
      apply intOfZ_injective
      rw [sqrt_int_mul]
      change intOfZ number = intOfZ root * intOfZ root + 0 at decomposition_int
      omega
    rw [square_number]
    have real_square : ctx.spec.ofZ (Zmul root root) =
        ctx.spec.mul (ctx.spec.ofZ root) (ctx.spec.ofZ root) := RIneq.mult_IZR ctx _ _
    rw [real_square]
    exact sqrt_square_root ctx _ root_real_nonnegative
  · have remainder_bool : Zeq_bool remainder Z0 = false := by
      simp [Zeq_bool, Zaux.Zeq_bool, ZArith.Zbool.Zeq_bool, exact_remainder]
    rw [remainder_bool]
    apply Bracket.inbetween_Inexact
    · constructor
      · apply sqrt_square_lt ctx
          (ctx.spec.ofZ root) (Exact.sqrt ctx (ctx.spec.ofZ number))
        · change ctx.spec.lt (ctx.spec.mul (ctx.spec.ofZ root) (ctx.spec.ofZ root))
            (ctx.spec.mul (Exact.sqrt ctx (ctx.spec.ofZ number))
              (Exact.sqrt ctx (ctx.spec.ofZ number)))
          rw [square_value, ← sqrt_ofZ_mul ctx root root]
          apply RIneq.IZR_lt ctx
          change intOfZ (Zmul root root) < intOfZ number
          rw [sqrt_int_mul]
          have remainder_ne : intOfZ remainder ≠ 0 := by
            intro equal
            exact exact_remainder (intOfZ_injective equal)
          omega
        · exact root_real_nonnegative
        · exact square_root_nonnegative
      · apply sqrt_square_lt ctx
          (Exact.sqrt ctx (ctx.spec.ofZ number)) (ctx.spec.ofZ (Zadd root Zone))
        · change ctx.spec.lt
            (ctx.spec.mul (Exact.sqrt ctx (ctx.spec.ofZ number))
              (Exact.sqrt ctx (ctx.spec.ofZ number)))
            (ctx.spec.mul (ctx.spec.ofZ (Zadd root Zone)) (ctx.spec.ofZ (Zadd root Zone)))
          rw [square_value, ← sqrt_ofZ_mul ctx (Zadd root Zone) (Zadd root Zone)]
          apply RIneq.IZR_lt ctx
          change intOfZ number < intOfZ (Zmul (Zadd root Zone) (Zadd root Zone))
          simp only [sqrt_int_mul, sqrt_int_add, show intOfZ Zone = 1 by rfl,
            Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one]
          omega
        · exact square_root_nonnegative
        · exact next_real_nonnegative
    · change Raux.Exact.Rcompare ctx (Exact.sqrt ctx (ctx.spec.ofZ number))
        (Raux.Exact.Rdiv ctx (ctx.spec.add (ctx.spec.ofZ root)
          (ctx.spec.ofZ (Zadd root Zone))) (Raux.Exact.Rtwo ctx)) = _
      rw [Raux.Rcompare_half_r ctx]
      have two_real : Raux.Exact.Rtwo ctx = ctx.spec.ofZ Ztwo := by
        rw [show Ztwo = Zadd Zone Zone by rfl, ctx.certificate.sourceLaws.ofZ_add,
          ctx.certificate.sourceLaws.ofZ_one]
        rfl
      rw [two_real, ← ctx.certificate.sourceLaws.ofZ_add]
      let doubled_root := ctx.spec.mul (ctx.spec.ofZ Ztwo)
        (Exact.sqrt ctx (ctx.spec.ofZ number))
      let midpoint_sum := Zadd root (Zadd root Zone)
      have doubled_nonnegative : ctx.spec.le ctx.spec.zero doubled_root := by
        rw [← ctx.certificate.sourceLaws.ofZ_zero]
        apply RIneq.Rmult_le_pos ctx
        · exact RIneq.IZR_le ctx Z0 Ztwo (by change (0 : Int) ≤ 2; omega)
        · change ctx.spec.le (ctx.spec.ofZ Z0) (Exact.sqrt ctx (ctx.spec.ofZ number))
          rw [ctx.certificate.sourceLaws.ofZ_zero]
          exact square_root_nonnegative
      have sum_nonnegative : ctx.spec.le ctx.spec.zero (ctx.spec.ofZ midpoint_sum) := by
        apply sqrt_integer_nonnegative
        change (0 : Int) ≤ intOfZ (Zadd root (Zadd root Zone))
        simp only [sqrt_int_add, show intOfZ Zone = 1 by rfl]
        change (0 : Int) ≤ intOfZ root at root_nonnegative
        omega
      have compare_squares := Raux.Rcompare_sqr ctx doubled_root (ctx.spec.ofZ midpoint_sum)
      change Raux.Exact.Rcompare ctx (ctx.spec.mul doubled_root doubled_root)
          (ctx.spec.mul (ctx.spec.ofZ midpoint_sum) (ctx.spec.ofZ midpoint_sum)) =
        Raux.Exact.Rcompare ctx (ctx.spec.abs doubled_root)
          (ctx.spec.abs (ctx.spec.ofZ midpoint_sum)) at compare_squares
      rw [ctx.certificate.sourceLaws.abs_nonnegative _ doubled_nonnegative,
        ctx.certificate.sourceLaws.abs_nonnegative _ sum_nonnegative] at compare_squares
      change Raux.Exact.Rcompare ctx doubled_root (ctx.spec.ofZ midpoint_sum) = _
      rw [← compare_squares]
      have doubled_square : ctx.spec.mul doubled_root doubled_root =
          ctx.spec.ofZ (Zmul (Zmul Ztwo Ztwo) number) := by
        have product_square := R_sqr.Rsqr_mult ctx (ctx.spec.ofZ Ztwo)
          (Exact.sqrt ctx (ctx.spec.ofZ number))
        change ctx.spec.mul doubled_root doubled_root =
          ctx.spec.mul (ctx.spec.mul (ctx.spec.ofZ Ztwo) (ctx.spec.ofZ Ztwo))
            (ctx.spec.mul (Exact.sqrt ctx (ctx.spec.ofZ number))
              (Exact.sqrt ctx (ctx.spec.ofZ number))) at product_square
        rw [product_square, square_value, ← sqrt_ofZ_mul ctx Ztwo Ztwo,
          ← sqrt_ofZ_mul ctx (Zmul Ztwo Ztwo) number]
      rw [doubled_square, ← sqrt_ofZ_mul ctx midpoint_sum midpoint_sum,
        sqrt_ofZ_compare ctx]
      have square_sum : intOfZ (Zmul midpoint_sum midpoint_sum) =
          4 * (intOfZ root * intOfZ root) + 4 * intOfZ root + 1 := by
        dsimp only [midpoint_sum]
        simp only [sqrt_int_mul, sqrt_int_add, show intOfZ Zone = 1 by rfl,
          Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one]
        omega
      change (if intOfZ (Zmul (Zmul Ztwo Ztwo) number) < intOfZ (Zmul midpoint_sum midpoint_sum)
        then Lt else if intOfZ (Zmul (Zmul Ztwo Ztwo) number) =
          intOfZ (Zmul midpoint_sum midpoint_sum) then Eq else Gt) = _
      rw [square_sum]
      simp only [sqrt_int_mul, show intOfZ Ztwo = 2 by rfl]
      by_cases lower_half : Zle remainder root
      · have location_lower : Zle_bool remainder root = true := Zaux.Zle_bool_true _ _ lower_half
        rw [location_lower]
        have comparison_lower : 2 * 2 * intOfZ number <
            4 * (intOfZ root * intOfZ root) + 4 * intOfZ root + 1 := by
          change intOfZ remainder ≤ intOfZ root at lower_half
          omega
        simp only [comparison_lower, ↓reduceIte]
      · have location_upper : Zle_bool remainder root = false := by
          apply Zaux.Zle_bool_false
          change intOfZ root < intOfZ remainder
          change ¬ intOfZ remainder ≤ intOfZ root at lower_half
          omega
        rw [location_upper]
        have comparison_upper : 4 * (intOfZ root * intOfZ root) + 4 * intOfZ root + 1 <
            2 * 2 * intOfZ number := by
          change ¬ intOfZ remainder ≤ intOfZ root at lower_half
          omega
        have not_lower : ¬ 2 * 2 * intOfZ number <
            4 * (intOfZ root * intOfZ root) + 4 * intOfZ root + 1 := by omega
        have not_equal : 2 * 2 * intOfZ number ≠
            4 * (intOfZ root * intOfZ root) + 4 * intOfZ root + 1 := by omega
        simp only [not_lower, not_equal, Bool.false_eq_true, ↓reduceIte]

theorem Fsqrt_core_correct (ctx : ExactRealContext) : Fsqrt_core_correctStatement ctx := by
  intro beta mantissa input_exponent output_exponent mantissa_positive exponent_bound
  let shifted := Zmul mantissa (Zpower (beta : Z)
    (Zsub input_exponent (Zmul Ztwo output_exponent)))
  have shift_nonnegative : Zle Z0 (Zsub input_exponent (Zmul Ztwo output_exponent)) := by
    change (0 : Int) ≤ intOfZ (Zsub input_exponent (Zmul Ztwo output_exponent))
    rw [sqrt_int_sub]
    change intOfZ (Zmul Ztwo output_exponent) ≤ intOfZ input_exponent at exponent_bound
    omega
  have shifted_nonnegative : Zle Z0 shifted := by
    have power_positive := Zaux.Zpower_gt_0 beta _ shift_nonnegative
    change (0 : Int) ≤ intOfZ (Zmul mantissa
      (Zpower (beta : Z) (Zsub input_exponent (Zmul Ztwo output_exponent))))
    rw [sqrt_int_mul]
    exact Int.le_of_lt (Int.mul_pos mantissa_positive power_positive)
  let scale := Raux.Exact.bpow ctx beta output_exponent
  have scale_positive : ctx.spec.lt ctx.spec.zero scale := Raux.bpow_gt_0 ctx beta _
  have scale_nonnegative : ctx.spec.le ctx.spec.zero scale :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp scale_positive |>.1
  have scale_square_nonnegative : ctx.spec.le ctx.spec.zero (ctx.spec.mul scale scale) := by
    have square := RIneq.Rle_0_sqr ctx scale
    change ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.mul scale scale) at square
    simpa only [ctx.certificate.sourceLaws.ofZ_zero] using square
  have doubled_exponent : Zmul Ztwo output_exponent = Zadd output_exponent output_exponent := by
    apply intOfZ_injective
    simp only [sqrt_int_mul, sqrt_int_add, show intOfZ Ztwo = 2 by rfl]
    omega
  have power_square : Raux.Exact.bpow ctx beta (Zmul Ztwo output_exponent) =
      ctx.spec.mul scale scale := by
    rw [doubled_exponent]
    exact Raux.bpow_plus ctx beta output_exponent output_exponent
  have float_scaled : Exact.F2R ctx (Float beta mantissa input_exponent) =
      ctx.spec.mul (ctx.spec.ofZ shifted) (ctx.spec.mul scale scale) := by
    have changed := Float_prop.F2R_change_exp ctx beta (Zmul Ztwo output_exponent)
      mantissa input_exponent exponent_bound
    change Exact.F2R ctx (Float beta mantissa input_exponent) =
      ctx.spec.mul (ctx.spec.ofZ shifted)
        (Raux.Exact.bpow ctx beta (Zmul Ztwo output_exponent)) at changed
    rw [power_square] at changed
    exact changed
  have square_root_scaled : Exact.sqrt ctx (Exact.F2R ctx (Float beta mantissa input_exponent)) =
      ctx.spec.mul (Exact.sqrt ctx (ctx.spec.ofZ shifted)) scale := by
    rw [float_scaled]
    have product := R_sqrt.sqrt_mult ctx (ctx.spec.ofZ shifted) (ctx.spec.mul scale scale)
      (RIneq.IZR_le ctx Z0 shifted shifted_nonnegative)
      (by
        change ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.mul scale scale)
        rw [ctx.certificate.sourceLaws.ofZ_zero]
        exact scale_square_nonnegative)
    change Exact.sqrt ctx (ctx.spec.mul (ctx.spec.ofZ shifted) (ctx.spec.mul scale scale)) =
      ctx.spec.mul (Exact.sqrt ctx (ctx.spec.ofZ shifted))
        (Exact.sqrt ctx (ctx.spec.mul scale scale)) at product
    rw [product, sqrt_square_root ctx scale scale_nonnegative]
  obtain ⟨decomposition, remainder_nonnegative, remainder_bound⟩ :=
    ZArith.BinInt.Z.sqrtrem_spec shifted shifted_nonnegative
  have between := sqrt_integer_between ctx shifted (ZArith.BinInt.Z.sqrtrem shifted).1
    (ZArith.BinInt.Z.sqrtrem shifted).2 shifted_nonnegative decomposition
    remainder_nonnegative remainder_bound
  have scaled_between := Bracket.inbetween_mult_compat ctx _ _ _ _ scale
    (by
      change ctx.spec.lt (ctx.spec.ofZ Z0) scale
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact scale_positive) between
  change Bracket.inbetween_float ctx beta (ZArith.BinInt.Z.sqrtrem shifted).1 output_exponent
    (Exact.sqrt ctx (Exact.F2R ctx (Float beta mantissa input_exponent)))
    (if Zeq_bool (ZArith.BinInt.Z.sqrtrem shifted).2 Z0 then loc_Exact
     else loc_Inexact (if Zle_bool (ZArith.BinInt.Z.sqrtrem shifted).2
       (ZArith.BinInt.Z.sqrtrem shifted).1 then Lt else Gt))
  rw [square_root_scaled]
  exact scaled_between

end CompCert4Lean.Flocq.Calc.Sqrt
