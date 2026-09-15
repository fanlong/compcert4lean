import CompCert4Lean.Flocq.IEEE754.Binary

/-!
# Additional IEEE-754 operations

This module translates the definition-bearing surface of
`compcert.lib.IEEE754_extra`.  Proof-bearing source declarations assigned to
the later proof phase are recorded as exact proposition descriptors.
-/

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754

abbrev R := Raux.R
abbrev Z := Raux.Z
abbrev positive := Raux.positive
abbrev radix := Raux.radix
abbrev xH : positive := Raux.xH
abbrev xO : positive → positive := Raux.xO
abbrev Z0 : Z := Zaux.Z0
abbrev Zone : Z := Zaux.Zone
abbrev Ztwo : Z := Zaux.Ztwo
abbrev Zpos := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
abbrev Zneg := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg
abbrev Zadd := Zaux.Zadd
abbrev Zsub := Zaux.Zsub
abbrev Zmul := Zaux.Zmul
abbrev Zopp := Zaux.Zopp
abbrev Zabs := Zaux.Zabs
abbrev Zdiv := Raux.Zdiv
abbrev Zpower := Zaux.Zpower
abbrev Zpower_pos := Zaux.Zpower_pos
abbrev Ziter := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.iter
abbrev Zle := Zaux.Zle
abbrev Zlt := Zaux.Zlt
abbrev Zle_bool := Zaux.Zle_bool
abbrev Zlt_bool := Zaux.Zlt_bool
abbrev IZR := Raux.IZR
abbrev R0 : R := Raux.R0
abbrev Rone : R := Raux.Rone
abbrev Rplus := Raux.Rplus
abbrev Rminus := Raux.Rminus
abbrev Rmult := Raux.Rmult
abbrev Rdiv := Raux.Rdiv
abbrev Rinv := Raux.Rinv
abbrev Ropp := Raux.Ropp
abbrev Rabs := Raux.Rabs
abbrev Rlt := Raux.Rlt
abbrev Rle := Raux.Rle
abbrev Rlt_bool := Raux.Rlt_bool
abbrev bpow := Raux.bpow
abbrev Zfloor := Raux.Zfloor
abbrev Ztrunc := Raux.Ztrunc
abbrev generic_format := Generic_fmt.generic_format
abbrev round := Generic_fmt.round
abbrev mode : Type := BinarySingleNaN.mode
abbrev mode_NE : mode := BinarySingleNaN.mode_NE
abbrev round_mode (m : mode) : R → Z := BinarySingleNaN.round_mode m
abbrev Prec_gt_0 := FLX.Prec_gt_0
abbrev Prec_lt_emax := BinarySingleNaN.Prec_lt_emax
abbrev Sumbool (P Q : Prop) : Type := CompCert4Lean.Foundation.Logic.Support.Sumbool P Q

/-! The executable aliases above are retained for the runtime compatibility
    boundary.  All proposition/specification surfaces below use this
    injected exact interpretation. -/
abbrev ExactRealContext := Binary.Exact.Context

namespace Exact

abbrev Context := ExactRealContext
abbrev Magnitude (ctx : Context) := Binary.Exact.Magnitude ctx
abbrev R (ctx : Context) := Binary.Exact.R ctx
abbrev IZR (ctx : Context) := BinarySingleNaN.Exact.IZR ctx
abbrev R0 (ctx : Context) := Binary.Exact.R0 ctx
abbrev Rone (ctx : Context) := Raux.Exact.Rone ctx
abbrev Ropp (ctx : Context) := Binary.Exact.Ropp ctx
abbrev Rplus (ctx : Context) := Binary.Exact.Rplus ctx
abbrev Rminus (ctx : Context) := Binary.Exact.Rminus ctx
abbrev Rmult (ctx : Context) := Binary.Exact.Rmult ctx
abbrev Rdiv (ctx : Context) := Binary.Exact.Rdiv ctx
abbrev Rinv (ctx : Context) := Raux.Exact.Rinv ctx
abbrev Rabs (ctx : Context) := Binary.Exact.Rabs ctx
abbrev Rlt (ctx : Context) := Binary.Exact.Rlt ctx
abbrev Rle (ctx : Context) := Binary.Exact.Rle ctx
noncomputable abbrev Rcompare (ctx : Context) := Binary.Exact.Rcompare ctx
noncomputable abbrev Rlt_bool (ctx : Context) := Binary.Exact.Rlt_bool ctx
abbrev Zfloor (ctx : Context) := BinarySingleNaN.Exact.Zfloor ctx
noncomputable abbrev Ztrunc (ctx : Context) := BinarySingleNaN.Exact.Ztrunc ctx
abbrev bpow (ctx : Context) := Binary.Exact.bpow ctx
abbrev generic_format (magnitude : Magnitude ctx) := Binary.Exact.generic_format magnitude
abbrev round (magnitude : Magnitude ctx) := Binary.Exact.round magnitude
noncomputable abbrev round_mode (ctx : Context) := BinarySingleNaN.Exact.round_mode ctx
abbrev B2R (ctx : Context) {prec emax : Z} (f : Binary.binary_float prec emax) :=
  Binary.Exact.B2R ctx f

end Exact

def emin (prec emax : Z) : Z := Binary.emin0 prec emax

def fexp (prec emax : Z) : Z → Z := Binary.fexp0 prec emax

abbrev binary_float (prec emax : Z) : Type := Binary.binary_float prec emax

abbrev BinaryFloatCertificate {prec emax : Z} :=
  Binary.BinaryFloatCertificate (prec := prec) (emax := emax)

abbrev CertifiedBinaryFloat (prec emax : Z) :=
  Binary.CertifiedBinaryFloat prec emax

abbrev NaNResult (prec emax : Z) :=
  Binary.CertifiedNaNResult prec emax

def keepPrecisionHypotheses
    (P : Prop) [prec_gt_0 : Prec_gt_0 prec]
    [prec_lt_emax : Prec_lt_emax prec emax] : Prop :=
  let _ := prec_gt_0
  let _ := prec_lt_emax
  P

def keepPrecGt (P : Prop) [prec_gt_0 : Prec_gt_0 prec] : Prop :=
  let _ := prec_gt_0
  P

variable {prec emax : Z} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  [Binary.BinaryNormalizeCertificate prec emax]

def is_finite_not_is_nanStatement : Prop :=
  ∀ f : CertifiedBinaryFloat prec emax,
    Binary.is_finite f.1 = true → Binary.is_nan f.1 = false

def is_finite_strict_finiteStatement : Prop :=
  ∀ f : CertifiedBinaryFloat prec emax,
    Binary.is_finite_strict f.1 = true → Binary.is_finite f.1 = true

private def binaryFloatDecidableEq
    (f1 f2 : binary_float prec emax) : Decidable (f1 = f2) := by
  cases f1 <;> cases f2 <;> simp <;> infer_instance

def Beq_dec (f1 f2 : binary_float prec emax) : Sumbool (f1 = f2) (f1 ≠ f2) :=
  match binaryFloatDecidableEq f1 f2 with
  | .isTrue h => .left h
  | .isFalse h => .right h

def integer_representable :
    ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) (n : Z), Prop :=
  fun ctx magnitude n =>
    Zle (Zabs n)
        (Zsub (Zpower Ztwo emax) (Zpower Ztwo (Zsub emax prec))) ∧
      Exact.generic_format magnitude Zaux.radix2 (fexp prec emax) (Exact.IZR ctx n)

def int_upper_bound_eqStatement : Prop :=
  keepPrecisionHypotheses (prec := prec) (emax := emax)
    (Zsub (Zpower Ztwo emax) (Zpower Ztwo (Zsub emax prec)) =
      Zmul (Zsub (Zpower Ztwo prec) Zone) (Zpower Ztwo (Zsub emax prec)))

def integer_representable_n2pStatement : Prop :=
  keepPrecisionHypotheses (prec := prec) (emax := emax)
    (∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) (n p : Z),
      (Zlt (Zopp (Zpower Ztwo prec)) n ∧ Zlt n (Zpower Ztwo prec)) →
      Zle Z0 p → Zle p (Zsub emax prec) →
      integer_representable (prec := prec) (emax := emax) ctx magnitude
        (Zmul n (Zpower Ztwo p)))

def integer_representable_2pStatement : Prop :=
  keepPrecisionHypotheses (prec := prec) (emax := emax)
    (∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) (p : Z),
      (Zle Z0 p ∧ Zle p (Zsub emax Zone)) →
      integer_representable (prec := prec) (emax := emax) ctx magnitude
        (Zpower Ztwo p))

def integer_representable_oppStatement : Prop :=
  ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) (n : Z),
    integer_representable (prec := prec) (emax := emax) ctx magnitude n →
    integer_representable (prec := prec) (emax := emax) ctx magnitude (Zopp n)

def integer_representable_n2p_wideStatement : Prop :=
  keepPrecisionHypotheses (prec := prec) (emax := emax)
    (∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) (n p : Z),
      (Zle (Zopp (Zpower Ztwo prec)) n ∧ Zle n (Zpower Ztwo prec)) →
      Zle Z0 p → Zlt p (Zsub emax prec) →
      integer_representable (prec := prec) (emax := emax) ctx magnitude
        (Zmul n (Zpower Ztwo p)))

def integer_representable_nStatement : Prop :=
  keepPrecisionHypotheses (prec := prec) (emax := emax)
    (∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) (n : Z),
      (Zle (Zopp (Zpower Ztwo prec)) n ∧ Zle n (Zpower Ztwo prec)) →
      integer_representable (prec := prec) (emax := emax) ctx magnitude n)

def round_int_no_overflowStatement : Prop :=
  keepPrecisionHypotheses (prec := prec) (emax := emax)
    (∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) (n : Z),
      Zle (Zabs n)
        (Zsub (Zpower Ztwo emax) (Zpower Ztwo (Zsub emax prec))) →
      Exact.Rlt ctx
        (Exact.Rabs ctx
          (Exact.round magnitude Zaux.radix2 (fexp prec emax)
            (Exact.round_mode ctx mode_NE) (Exact.IZR ctx n)))
        (Exact.bpow ctx Zaux.radix2 emax))

def BofZ (n : Z) [Binary.BinaryNormalizeCertificate prec emax] : binary_float prec emax :=
  Binary.binary_normalize mode_NE n Z0 false

def BofZ_result_obligation [Binary.BinaryNormalizeCertificate prec emax] : Prop :=
  ∀ n : Z, BinaryFloatCertificate (BofZ (prec := prec) (emax := emax) n)

def BofZ_correctStatement : Prop :=
  keepPrecisionHypotheses (prec := prec) (emax := emax)
    (∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) (n : Z),
      if Exact.Rlt_bool ctx
          (Exact.Rabs ctx
            (Exact.round magnitude Zaux.radix2 (fexp prec emax)
              (Exact.round_mode ctx mode_NE) (Exact.IZR ctx n)))
          (Exact.bpow ctx Zaux.radix2 emax) then
        Exact.B2R ctx (BofZ (prec := prec) (emax := emax) n) =
            Exact.round magnitude Zaux.radix2 (fexp prec emax)
              (Exact.round_mode ctx mode_NE) (Exact.IZR ctx n) ∧
          Binary.is_finite (BofZ (prec := prec) (emax := emax) n) = true ∧
          Binary.Bsign (BofZ (prec := prec) (emax := emax) n) = Zlt_bool n Z0
      else
        Binary.B2FF (BofZ (prec := prec) (emax := emax) n) =
          Binary.binary_overflow (prec := prec) (emax := emax) mode_NE (Zlt_bool n Z0))

def BofZ_finiteStatement : Prop :=
  keepPrecisionHypotheses (prec := prec) (emax := emax)
    (∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) (n : Z),
      Zle (Zabs n)
        (Zsub (Zpower Ztwo emax) (Zpower Ztwo (Zsub emax prec))) →
      Exact.B2R ctx (BofZ (prec := prec) (emax := emax) n) =
          Exact.round magnitude Zaux.radix2 (fexp prec emax)
            (Exact.round_mode ctx mode_NE) (Exact.IZR ctx n) ∧
        Binary.is_finite (BofZ (prec := prec) (emax := emax) n) = true ∧
        Binary.Bsign (BofZ (prec := prec) (emax := emax) n) = Zlt_bool n Z0)

def BofZ_representableStatement : Prop :=
  keepPrecisionHypotheses (prec := prec) (emax := emax)
    (∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) (n : Z),
      integer_representable (prec := prec) (emax := emax) ctx magnitude n →
      Exact.B2R ctx (BofZ (prec := prec) (emax := emax) n) = Exact.IZR ctx n ∧
        Binary.is_finite (BofZ (prec := prec) (emax := emax) n) = true ∧
        Binary.Bsign (BofZ (prec := prec) (emax := emax) n) = Zlt_bool n Z0)

def BofZ_exactStatement : Prop :=
  keepPrecisionHypotheses (prec := prec) (emax := emax)
    (∀ (ctx : ExactRealContext) (n : Z),
      (Zle (Zopp (Zpower Ztwo prec)) n ∧ Zle n (Zpower Ztwo prec)) →
      Exact.B2R ctx (BofZ (prec := prec) (emax := emax) n) = Exact.IZR ctx n ∧
        Binary.is_finite (BofZ (prec := prec) (emax := emax) n) = true ∧
        Binary.Bsign (BofZ (prec := prec) (emax := emax) n) = Zlt_bool n Z0)

def BofZ_plusStatement : Prop :=
  ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (nan : binary_float prec emax → binary_float prec emax → NaNResult prec emax)
    (p q : Z),
    integer_representable (prec := prec) (emax := emax) ctx magnitude p →
    integer_representable (prec := prec) (emax := emax) ctx magnitude q →
    Binary.Bplus nan mode_NE
        (BofZ (prec := prec) (emax := emax) p)
        (BofZ (prec := prec) (emax := emax) q) =
      BofZ (prec := prec) (emax := emax) (Zadd p q)

def ZofB (f : binary_float prec emax) : Option Z :=
  match f with
  | .B754_finite s m (.Zpos e) =>
      some (Zmul (Zaux.cond_Zopp s (Zpos m)) (Zpower_pos Ztwo e))
  | .B754_finite s m .Z0 => some (Zaux.cond_Zopp s (Zpos m))
  | .B754_finite s m (.Zneg e) =>
      some (Zaux.cond_Zopp s (Zdiv (Zpos m) (Zpower_pos Ztwo e)))
  | .B754_zero _ => some Z0
  | _ => none

def ZofB_correctStatement : Prop :=
  ∀ f : CertifiedBinaryFloat prec emax,
    ∀ (ctx : ExactRealContext),
    ZofB f.1 =
      if Binary.is_finite f.1 then some (Exact.Ztrunc ctx (Exact.B2R ctx f.1)) else none

def Ztrunc_range_posStatement : Prop :=
  ∀ (ctx : ExactRealContext) (x : Exact.R ctx),
    Zlt Z0 (Exact.Ztrunc ctx x) →
    Exact.Rle ctx (Exact.IZR ctx (Exact.Ztrunc ctx x)) x ∧
      Exact.Rlt ctx x (Exact.IZR ctx (Zadd (Exact.Ztrunc ctx x) Zone))

def Ztrunc_range_zeroStatement : Prop :=
  ∀ (ctx : ExactRealContext) (x : Exact.R ctx),
    Exact.Ztrunc ctx x = Z0 →
    Exact.Rlt ctx (Exact.Ropp ctx (Exact.Rone ctx)) x ∧
      Exact.Rlt ctx x (Exact.Rone ctx)

def ZofB_range_posStatement : Prop :=
  keepPrecisionHypotheses (prec := prec) (emax := emax)
    (∀ (f : CertifiedBinaryFloat prec emax) (n : Z),
      ZofB f.1 = some n → Zlt Z0 n →
      ∀ (ctx : ExactRealContext),
      Exact.Rle ctx (Exact.IZR ctx n) (Exact.B2R ctx f.1) ∧
        Exact.Rlt ctx (Exact.B2R ctx f.1) (Exact.IZR ctx (Zadd n Zone)))

def ZofB_range_zeroStatement : Prop :=
  keepPrecisionHypotheses (prec := prec) (emax := emax)
    (∀ (f : CertifiedBinaryFloat prec emax),
      ZofB f.1 = some Z0 → ∀ (ctx : ExactRealContext),
      Exact.Rlt ctx (Exact.Ropp ctx (Exact.Rone ctx)) (Exact.B2R ctx f.1) ∧
        Exact.Rlt ctx (Exact.B2R ctx f.1) (Exact.Rone ctx))

def ZofB_range_nonnegStatement : Prop :=
  keepPrecisionHypotheses (prec := prec) (emax := emax)
    (∀ (f : CertifiedBinaryFloat prec emax) (n : Z),
      ZofB f.1 = some n → Zle Z0 n →
      ∀ (ctx : ExactRealContext),
      Exact.Rlt ctx (Exact.Ropp ctx (Exact.Rone ctx)) (Exact.B2R ctx f.1) ∧
        Exact.Rlt ctx (Exact.B2R ctx f.1) (Exact.IZR ctx (Zadd n Zone)))

def Zfloor_minusStatement : Prop :=
  ∀ (ctx : ExactRealContext) (x : Exact.R ctx) (n : Z),
    Exact.Zfloor ctx (Exact.Rminus ctx x (Exact.IZR ctx n)) =
      Zsub (Exact.Zfloor ctx x) n

def ZofB_minusStatement : Prop :=
  ∀ (minus_nan : binary_float prec emax → binary_float prec emax → NaNResult prec emax)
    (m : mode) (f : CertifiedBinaryFloat prec emax) (p q : Z),
    ZofB f.1 = some p →
    (Zle Z0 p ∧ Zlt p (Zmul Ztwo q)) →
    Zle q (Zpower Ztwo prec) →
    ∀ (ctx : ExactRealContext),
    Exact.Rle ctx (Exact.IZR ctx q) (Exact.B2R ctx f.1) →
    ZofB (Binary.Bminus minus_nan m f.1
      (BofZ (prec := prec) (emax := emax) q)) = some (Zsub p q)

def ZofB_range (f : binary_float prec emax) (zmin zmax : Z) : Option Z :=
  match ZofB f with
  | none => none
  | some z => if Zle_bool zmin z && Zle_bool z zmax then some z else none

def ZofB_range_correctStatement : Prop :=
  ∀ (f : CertifiedBinaryFloat prec emax) (min max : Z),
    ∀ (ctx : ExactRealContext),
    let n := Exact.Ztrunc ctx (Exact.B2R ctx f.1)
    ZofB_range f.1 min max =
      if Binary.is_finite f.1 && Zle_bool min n && Zle_bool n max then some n else none

def ZofB_range_inversionStatement : Prop :=
  ∀ (f : CertifiedBinaryFloat prec emax) (min max n : Z),
    ZofB_range f.1 min max = some n →
    Zle min n ∧ Zle n max ∧ ZofB f.1 = some n

def ZofB_range_minusStatement : Prop :=
  ∀ (minus_nan : binary_float prec emax → binary_float prec emax → NaNResult prec emax)
    (m : mode) (f : CertifiedBinaryFloat prec emax) (p q : Z),
    ZofB_range f.1 Z0 (Zsub (Zmul Ztwo q) Zone) = some p →
    Zle q (Zpower Ztwo prec) →
    ∀ (ctx : ExactRealContext),
    Exact.Rle ctx (Exact.IZR ctx q) (Exact.B2R ctx f.1) →
    ZofB_range
      (Binary.Bminus minus_nan m f.1
        (BofZ (prec := prec) (emax := emax) q))
      (Zopp q) (Zsub q Zone) = some (Zsub p q)

def Bmult_commutStatement : Prop :=
  ∀ (mult_nan : binary_float prec emax → binary_float prec emax → NaNResult prec emax)
    (m : mode) (x y : CertifiedBinaryFloat prec emax),
    mult_nan x.1 y.1 = mult_nan y.1 x.1 →
    Binary.Bmult mult_nan m x.1 y.1 =
      Binary.Bmult mult_nan m y.1 x.1

def Bmult2_BplusStatement : Prop :=
  ∀ (plus_nan mult_nan : binary_float prec emax → binary_float prec emax → NaNResult prec emax)
    (m : mode) (f : CertifiedBinaryFloat prec emax),
    (∀ x y : CertifiedBinaryFloat prec emax,
      Binary.is_nan x.1 = true → Binary.is_finite y.1 = true →
      plus_nan x.1 x.1 = mult_nan x.1 y.1) →
    Binary.Bplus plus_nan m f.1 f.1 =
      Binary.Bmult mult_nan m f.1
        (BofZ (prec := prec) (emax := emax) Ztwo)

def Bexact_inverse_mantissa : positive :=
  Ziter (Zsub prec Zone) xO xH

def Bexact_inverse_mantissa_valueStatement : Prop :=
  keepPrecGt (prec := prec)
    (Zpos (Bexact_inverse_mantissa (prec := prec)) =
      Zpower Ztwo (Zsub prec Zone))

def Bexact_inverse_mantissa_digits2_posStatement : Prop :=
  keepPrecisionHypotheses (prec := prec) (emax := emax)
    (Zpos (Digits.digits2_pos (Bexact_inverse_mantissa (prec := prec))) = prec)

def bounded_Bexact_inverseStatement : Prop :=
  keepPrecisionHypotheses (prec := prec) (emax := emax)
    (∀ e : Z,
      (Zle (emin prec emax) e ∧ Zle e (Zsub emax prec)) ↔
        Binary.bounded (prec := prec) (emax := emax)
          (Bexact_inverse_mantissa (prec := prec)) e = true)

def Bexact_inverse_obligation_1 : Prop :=
  keepPrecisionHypotheses (prec := prec) (emax := emax)
    (∀ (f : binary_float prec emax) (s : Bool) (m : positive) (e : Z)
      (B : Binary.B754_finiteObligation (prec := prec) (emax := emax) m e)
      (Heq_f : Binary.B754_finite s m e = f),
      m = Bexact_inverse_mantissa (prec := prec) →
      let e' := Zsub (Zopp e) (Zmul (Zsub prec Zone) Ztwo)
      Zle (emin prec emax) e' →
        Binary.B754_finiteObligation (prec := prec) (emax := emax) m e')

def Bexact_inverse_obligation_2Statement : Prop :=
  ∀ (b : Bool),
    let wildcard' := Binary.B754_zero (prec := prec) (emax := emax) b
    ∀ (s : Bool) (m : positive) (e : Z)
      (B : Binary.B754_finiteObligation (prec := prec) (emax := emax) m e),
      Binary.B754_finite s m e ≠ wildcard'

def Bexact_inverse_obligation_3Statement : Prop :=
  ∀ (b : Bool),
    let wildcard' := Binary.B754_infinity (prec := prec) (emax := emax) b
    ∀ (s : Bool) (m : positive) (e : Z)
      (B : Binary.B754_finiteObligation (prec := prec) (emax := emax) m e),
      Binary.B754_finite s m e ≠ wildcard'

def Bexact_inverse_obligation_4Statement : Prop :=
  ∀ (b : Bool) (p : positive)
    (e : Binary.nan_pl (prec := prec) p = true),
    let wildcard' := Binary.B754_nan (prec := prec) (emax := emax) b p
    ∀ (s : Bool) (m : positive) (e0 : Z)
      (B : Binary.B754_finiteObligation (prec := prec) (emax := emax) m e0),
      Binary.B754_finite s m e0 ≠ wildcard'

class Bexact_inverse_certificate (prec emax : Z)
    [Prec_gt_0 prec] [Prec_lt_emax prec emax] : Prop where
  obligation : Bexact_inverse_obligation_1 (prec := prec) (emax := emax)

def Bexact_inverse (f : binary_float prec emax)
    [certificate : Bexact_inverse_certificate prec emax] : Option (binary_float prec emax) :=
  let _ := certificate
  match f with
  | .B754_finite s m e =>
      if _hm : m = Bexact_inverse_mantissa (prec := prec) then
        let e' := Zsub (Zopp e) (Zmul (Zsub prec Zone) Ztwo)
        match _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.ZArith_dec.Z_le_dec
            (emin prec emax) e' with
        | .left _ =>
            match _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.ZArith_dec.Z_le_dec
                e' emax with
            | .left _ => some (Binary.B754_finite s m e')
            | .right _ => none
        | .right _ => none
      else none
  | _ => none

def Bexact_inverse_result_obligation
    [Bexact_inverse_certificate prec emax] : Prop :=
  ∀ (f : CertifiedBinaryFloat prec emax),
    ∀ f', Bexact_inverse (prec := prec) (emax := emax) f.1 = some f' →
      BinaryFloatCertificate f'

def Bexact_inverse_correctStatement : Prop :=
  keepPrecisionHypotheses (prec := prec) (emax := emax)
  (∀ (_certificate : Bexact_inverse_certificate prec emax)
    (f f' : CertifiedBinaryFloat prec emax),
    Bexact_inverse (certificate := _certificate) f.1 = some f'.1 →
    Binary.is_finite_strict f.1 = true ∧
      Binary.is_finite_strict f'.1 = true ∧
      ∀ (ctx : ExactRealContext),
      Exact.B2R ctx f'.1 = Exact.Rinv ctx (Exact.B2R ctx f.1) ∧
      Exact.B2R ctx f.1 ≠ Exact.R0 ctx ∧
      Binary.Bsign f'.1 = Binary.Bsign f.1)

def Bdiv_mult_inverseStatement : Prop :=
  ∀ (_certificate : Bexact_inverse_certificate prec emax)
    (div_nan mult_nan : binary_float prec emax → binary_float prec emax → NaNResult prec emax)
    (m : mode) (x y z : CertifiedBinaryFloat prec emax),
    (∀ a b c : CertifiedBinaryFloat prec emax,
      Binary.is_nan a.1 = true →
      Binary.is_finite b.1 = true → Binary.is_finite c.1 = true →
      div_nan a.1 b.1 = mult_nan a.1 c.1) →
    Bexact_inverse (certificate := _certificate) y.1 = some z.1 →
    Binary.Bdiv div_nan m x.1 y.1 =
      Binary.Bmult mult_nan m x.1 z.1

section Conversions

variable {prec1 emax1 prec2 emax2 : Z}
  [Prec_gt_0 prec1] [Prec_gt_0 prec2]
  [Prec_lt_emax prec1 emax1] [Prec_lt_emax prec2 emax2]
  [Binary.BinaryNormalizeCertificate prec1 emax1]
  [Binary.BinaryNormalizeCertificate prec2 emax2]

def Bconv
    (conv_nan : binary_float prec1 emax1 →
      NaNResult prec2 emax2)
    (md : mode) (f : binary_float prec1 emax1) : binary_float prec2 emax2 :=
  match f with
  | .B754_nan _ _ => Binary.build_nan
      ⟨(conv_nan f).1, (conv_nan f).2.1⟩
  | .B754_infinity s => Binary.B754_infinity s
  | .B754_zero s => Binary.B754_zero s
  | .B754_finite s m e =>
      Binary.binary_normalize md (Zaux.cond_Zopp s (Zpos m)) e s

def Bconv_result_obligation
    [Binary.BinaryNormalizeCertificate prec2 emax2] : Prop :=
  ∀ (conv_nan : binary_float prec1 emax1 → NaNResult prec2 emax2)
    (md : mode) (f : CertifiedBinaryFloat prec1 emax1),
    BinaryFloatCertificate (Bconv conv_nan md f.1)

def Bconv_correctStatement : Prop :=
  ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (conv_nan : binary_float prec1 emax1 → NaNResult prec2 emax2)
    (m : mode) (f : CertifiedBinaryFloat prec1 emax1),
    Binary.is_finite f.1 = true →
    if Exact.Rlt_bool ctx
        (Exact.Rabs ctx
          (Exact.round magnitude Zaux.radix2 (fexp prec2 emax2)
            (Exact.round_mode ctx m) (Exact.B2R ctx f.1)))
        (Exact.bpow ctx Zaux.radix2 emax2) then
      Exact.B2R ctx (Bconv conv_nan m f.1) =
          Exact.round magnitude Zaux.radix2 (fexp prec2 emax2)
            (Exact.round_mode ctx m) (Exact.B2R ctx f.1) ∧
        Binary.is_finite (Bconv conv_nan m f.1) = true ∧
        Binary.Bsign (Bconv conv_nan m f.1) = Binary.Bsign f.1
    else
      Binary.B2FF (Bconv conv_nan m f.1) =
        Binary.binary_overflow (prec := prec2) (emax := emax2) m (Binary.Bsign f.1)

def Bconv_widen_exactStatement : Prop :=
  keepPrecGt (prec := prec1)
  (∀ (ctx : ExactRealContext),
  Zle prec1 prec2 → Zle emax1 emax2 →
  ∀ (conv_nan : binary_float prec1 emax1 → NaNResult prec2 emax2)
    (m : mode) (f : CertifiedBinaryFloat prec1 emax1),
    Binary.is_finite f.1 = true →
    Exact.B2R ctx (Bconv conv_nan m f.1) = Exact.B2R ctx f.1 ∧
      Binary.is_finite (Bconv conv_nan m f.1) = true ∧
      Binary.Bsign (Bconv conv_nan m f.1) = Binary.Bsign f.1)

def Bconv_BofZStatement : Prop :=
  ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (conv_nan : binary_float prec1 emax1 → NaNResult prec2 emax2) (n : Z),
    integer_representable (prec := prec1) (emax := emax1) ctx magnitude n →
    BinaryFloatCertificate (BofZ (prec := prec1) (emax := emax1) n) →
    BinaryFloatCertificate (BofZ (prec := prec2) (emax := emax2) n) →
    Bconv conv_nan mode_NE (BofZ (prec := prec1) (emax := emax1) n) =
      BofZ (prec := prec2) (emax := emax2) n

def ZofB_BconvStatement : Prop :=
  keepPrecGt (prec := prec1)
    (Zle prec1 prec2 → Zle emax1 emax2 →
    ∀ (conv_nan : binary_float prec1 emax1 → NaNResult prec2 emax2)
      (m : mode) (f : CertifiedBinaryFloat prec1 emax1) (n : Z),
      ZofB f.1 = some n → ZofB (Bconv conv_nan m f.1) = some n)

def ZofB_range_BconvStatement : Prop :=
  keepPrecGt (prec := prec1)
    (∀ min1 max1 min2 max2 : Z,
      Zle prec1 prec2 → Zle emax1 emax2 →
      Zle min2 min1 → Zle max1 max2 →
      ∀ (conv_nan : binary_float prec1 emax1 → NaNResult prec2 emax2)
        (m : mode) (f : CertifiedBinaryFloat prec1 emax1) (n : Z),
        ZofB_range f.1 min1 max1 = some n →
        ZofB_range (Bconv conv_nan m f.1) min2 max2 = some n)

end Conversions

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754

private abbrev binary32_prec : Z :=
  _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 24
private abbrev binary32_emax : Z :=
  _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 128

theorem binary32_exact_inverse_certificate_proof :
    ∀ [pgt : Prec_gt_0
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 24)]
      [ple : Prec_lt_emax
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 24)
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 128)],
      Bexact_inverse_certificate
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 24)
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 128) := by
  intro pgt ple
  letI : Prec_gt_0 binary32_prec := pgt
  letI : Prec_lt_emax binary32_prec binary32_emax := ple
  refine ⟨?_⟩
  dsimp [Bexact_inverse_obligation_1, keepPrecisionHypotheses]
  intro f s m e B Heq hm hemin
  subst m
  have hd :
      _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos
          (Bexact_inverse_mantissa (prec := binary32_prec)) =
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat 24 := by
    decide
  have h24 : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ binary32_prec = (24 : Int) := by
    decide
  have h128 : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ binary32_emax = (128 : Int) := by
    decide
  have h1 : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by
    decide
  have h2 : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = (2 : Int) := by
    decide
  have h3 :
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos (.xI .xH)) = (3 : Int) := by
    decide
  have hp24 :
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
            (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat 24)) =
        (24 : Int) := by
    decide
  have hemin_val :
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (emin binary32_prec binary32_emax) = (-149 : Int) := by
    decide
  simp only [Binary.B754_finiteObligation,
    _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.bounded,
    _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.canonical_mantissa,
    _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.emin,
    _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.fexp]
  rw [hd]
  simp [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.leb]
  simp [_root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.zmax,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
    h24, h128, h1, h2, h3, hp24, Binary.B754_finiteObligation,
    _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.bounded,
    _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.canonical_mantissa,
    _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.emin,
    _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.fexp] at B ⊢
  rw [hd] at B
  simp [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.leb,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
    h24, h128, h1, h2, h3, hp24,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp] at B
  have he_lower : (-149 : Int) ≤ _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e := by
    by_cases hgood : (-149 : Int) ≤ _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e
    · exact hgood
    · let hnot := hgood
      have hcancel (x : Int) : 24 + x - 24 = x := by
        rw [Int.add_comm]
        exact Int.add_sub_cancel x 24
      have hcond :
          24 + _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e - 24 ≤ (-149 : Int) := by
        rw [hcancel]
        exact Int.le_of_lt (Int.lt_of_not_ge hnot)
      rw [if_pos hcond] at B
      have hEq := congrArg _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ B.1
      have hEq' : (-149 : Int) = _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e := by
        simpa only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] using hEq
      exact False.elim (hnot (hEq' ▸ Int.le_refl _))
  have hmin0 := hemin
  change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (emin binary32_prec binary32_emax) ≤
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zsub (Zopp e) (Zmul (Zsub binary32_prec Zone) Ztwo)) at hmin0
  simp [_root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.emin,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
    h24, h128, h1, h2, h3, hemin_val] at hmin0
  have hupper : -_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e - 46 ≤ (104 : Int) := by
    have hneg := Int.neg_le_neg he_lower
    have hsub := Int.sub_le_sub_right hneg 46
    have h103 : -_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e - 46 ≤ (103 : Int) := by
      simpa using hsub
    exact Int.le_trans h103 (by decide)
  have hcancel (x : Int) : 24 + x - 24 = x := by
    rw [Int.add_comm]
    exact Int.add_sub_cancel x 24
  by_cases hc :
      24 + (-_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e - 46) - 24 ≤ (-149 : Int)
  · have hc' : -_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e - 46 ≤ (-149 : Int) := by
      calc
        -_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e - 46 =
            24 + (-_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e - 46) - 24 :=
          (hcancel _).symm
        _ ≤ -149 := hc
    have heq : -_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e - 46 = (-149 : Int) :=
      Int.le_antisymm hc' hmin0
    constructor
    · rw [if_pos hc, heq]
    · exact hupper
  · constructor
    · rw [if_neg hc, hcancel]
    · exact hupper

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754

theorem int_upper_bound_eq :
    ∀ {prec emax : Z} [pgt : Prec_gt_0 prec]
      [ple : Prec_lt_emax prec emax],
      int_upper_bound_eqStatement (prec := prec) (emax := emax) := by
  intro prec emax pgt ple
  dsimp [int_upper_bound_eqStatement, keepPrecisionHypotheses]
  have hp : 0 ≤ _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec := by
    exact Int.le_of_lt (show 0 < _ from pgt)
  have he : 0 ≤ _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emax := by
    have hpe : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec <
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emax :=
      (show Zlt prec emax from ple.prec_lt_emax)
    exact Int.le_trans hp (Int.le_of_lt hpe)
  have hsub :
      ∀ x y : Z,
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub x y) =
          _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x -
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y := by
    intro x y
    simp [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  have hpow :
      ∀ x : Z, 0 ≤ _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x →
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpower Ztwo x) =
          Int.pow 2 (Int.toNat (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x)) := by
    intro x hx
    have htwo :
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = (2 : Int) := by
      decide
    have hif : ¬ _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x < 0 := by
      omega
    simp [Zpower, _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow,
      htwo, hif,
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [hsub,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  have hdiff : 0 ≤
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub emax prec) := by
    rw [hsub]
    have hpe : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec ≤
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emax :=
      Int.le_of_lt (show Zlt prec emax from ple.prec_lt_emax)
    omega
  rw [hpow emax he, hpow (Zsub emax prec) hdiff, hpow prec hp]
  have hi :
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emax =
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub emax prec) +
          _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec := by
    rw [hsub]
    omega
  have hnat :
      Int.toNat (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emax) =
        Int.toNat (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub emax prec)) +
          Int.toNat (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec) := by
    rw [hi, Int.toNat_add hdiff hp]
  rw [hnat]
  change (2 : Int) ^
      (Int.toNat (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub emax prec)) +
        Int.toNat (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec)) -
      (2 : Int) ^ Int.toNat (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub emax prec)) =
    ((2 : Int) ^ Int.toNat (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec) -
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone) *
      (2 : Int) ^ Int.toNat (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub emax prec))
  rw [Int.pow_add]
  have hzone :
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by
    decide
  simp [hzone]
  rw [Int.sub_mul]
  simp only [Int.one_mul]
  exact congrArg (fun t : Int => t -
      2 ^ Int.toNat (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub emax prec)))
    (Int.mul_comm _ _)

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754

theorem is_finite_not_is_nan :
    ∀ {prec emax : Z},
      is_finite_not_is_nanStatement (prec := prec) (emax := emax) := by
  intro prec emax f hf
  rcases f with ⟨f, hf_cert⟩
  cases f <;>
    simp [CompCert4Lean.Flocq.IEEE754.Binary.is_finite,
      CompCert4Lean.Flocq.IEEE754.Binary.is_nan] at hf ⊢

theorem is_finite_strict_finite :
    ∀ {prec emax : Z},
      is_finite_strict_finiteStatement (prec := prec) (emax := emax) := by
  intro prec emax f hf
  rcases f with ⟨f, hf_cert⟩
  cases f <;>
    simp [CompCert4Lean.Flocq.IEEE754.Binary.is_finite_strict,
      CompCert4Lean.Flocq.IEEE754.Binary.is_finite] at hf ⊢

private abbrev binary64_prec : Z :=
  _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 53
private abbrev binary64_emax : Z :=
  _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1024

theorem binary64_exact_inverse_certificate_proof :
    ∀ [pgt : Prec_gt_0
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 53)]
      [ple : Prec_lt_emax
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 53)
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1024)],
      Bexact_inverse_certificate
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 53)
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1024) := by
  intro pgt ple
  letI : Prec_gt_0 binary64_prec := pgt
  letI : Prec_lt_emax binary64_prec binary64_emax := ple
  refine ⟨?_⟩
  dsimp [Bexact_inverse_obligation_1, keepPrecisionHypotheses]
  intro f s m e B Heq hm hemin
  subst m
  have hd :
      _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos
          (Bexact_inverse_mantissa (prec := binary64_prec)) =
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat 53 := by
    decide
  have h53 : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ binary64_prec = (53 : Int) := by
    decide
  have h1024 : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ binary64_emax = (1024 : Int) := by
    decide
  have h1 : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by
    decide
  have h2 : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = (2 : Int) := by
    decide
  have h3 :
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos (.xI .xH)) = (3 : Int) := by
    decide
  have hp53 :
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
            (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat 53)) =
        (53 : Int) := by
    decide
  have hemin_val :
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (emin binary64_prec binary64_emax) = (-1074 : Int) := by
    decide
  simp only [CompCert4Lean.Flocq.IEEE754.Binary.B754_finiteObligation,
    _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.bounded,
    _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.canonical_mantissa,
    _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.emin,
    _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.fexp]
  rw [hd]
  simp [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.leb]
  simp [_root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.zmax,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
    h53, h1024, h1, h2, h3, hp53,
    _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.bounded,
    _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.canonical_mantissa,
    _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.emin,
    _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.fexp] at ⊢
  simp only [CompCert4Lean.Flocq.IEEE754.Binary.B754_finiteObligation,
    _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.bounded,
    _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.canonical_mantissa,
    _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.emin,
    _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.fexp] at B
  rw [hd] at B
  simp [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.leb,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
    h53, h1024, h1, h2, h3, hp53,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp] at B
  have he_lower : (-1074 : Int) ≤ _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e := by
    by_cases hgood : (-1074 : Int) ≤ _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e
    · exact hgood
    · let hnot := hgood
      have hcancel (x : Int) : 53 + x - 53 = x := by
        rw [Int.add_comm]
        exact Int.add_sub_cancel x 53
      have hcond :
          53 + _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e - 53 ≤ (-1074 : Int) := by
        rw [hcancel]
        exact Int.le_of_lt (Int.lt_of_not_ge hnot)
      rw [if_pos hcond] at B
      have hEq := congrArg _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ B.1
      have hEq' : (-1074 : Int) = _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e := by
        simpa only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] using hEq
      exact False.elim (hnot (hEq' ▸ Int.le_refl _))
  have hmin0 := hemin
  change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (emin binary64_prec binary64_emax) ≤
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zsub (Zopp e) (Zmul (Zsub binary64_prec Zone) Ztwo)) at hmin0
  simp [_root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.emin,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
    h53, h1024, h1, h2, h3, hemin_val] at hmin0
  have hupper : -_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e - 104 ≤ (971 : Int) := by
    have hneg := Int.neg_le_neg he_lower
    have hsub := Int.sub_le_sub_right hneg 104
    have h970 : -_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e - 104 ≤ (970 : Int) := by
      simpa using hsub
    exact Int.le_trans h970 (by decide)
  have hcancel (x : Int) : 53 + x - 53 = x := by
    rw [Int.add_comm]
    exact Int.add_sub_cancel x 53
  by_cases hc :
      53 + (-_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e - 104) - 53 ≤ (-1074 : Int)
  · have hc' : -_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e - 104 ≤ (-1074 : Int) := by
      calc
        -_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e - 104 =
            53 + (-_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e - 104) - 53 :=
          (hcancel _).symm
        _ ≤ -1074 := hc
    have heq : -_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e - 104 = (-1074 : Int) :=
      Int.le_antisymm hc' hmin0
    constructor
    · rw [if_pos hc, heq]
    · exact hupper
  · constructor
    · rw [if_neg hc, hcancel]
    · exact hupper

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.IEEE754

theorem Bexact_inverse_result_obligation_proof :
    ∀ {prec emax : Z} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
      [Bexact_inverse_certificate prec emax],
      Bexact_inverse_result_obligation (prec := prec) (emax := emax) := by
  intro prec emax hp he certificate f f' hresult
  rcases f with ⟨f, hf⟩
  cases f with
  | B754_zero s => simp [Bexact_inverse] at hresult
  | B754_infinity s => simp [Bexact_inverse] at hresult
  | B754_nan s p => simp [Bexact_inverse] at hresult
  | B754_finite s m e =>
      by_cases hm : m = Bexact_inverse_mantissa (prec := prec)
      · let e' := Zsub (Zopp e) (Zmul (Zsub prec Zone) Ztwo)
        cases hmin :
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.ZArith_dec.Z_le_dec
              (emin prec emax) e' with
        | left hemin =>
            cases hmax :
                _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.ZArith_dec.Z_le_dec
                  e' emax with
            | left hemax =>
                have hout : f' = Binary.B754_finite s m e' := by
                  simpa [Bexact_inverse, hm, e', hmin, hmax] using hresult.symm
                subst f'
                have hbounded :
                    Binary.B754_finiteObligation (prec := prec) (emax := emax) m e' :=
                  certificate.obligation (Binary.B754_finite s m e) s m e hf rfl hm (by
                    simpa [e'] using hemin)
                simpa [Binary.BinaryFloatCertificate, Binary.B2FF, Binary.valid_binary,
                  Binary.B754_finiteObligation] using hbounded
            | right hnmax =>
                simp [Bexact_inverse, hm, e', hmin, hmax] at hresult
        | right hnmin =>
            simp [Bexact_inverse, hm, e', hmin] at hresult
      · simp [Bexact_inverse, hm] at hresult

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

private theorem pg_ieee_zsub_add_opp (a b : Z) : Zsub a b = Zadd a (Zopp b) := by
  apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub a b) =
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd a (Zopp b))
  simp only [Zsub, Zadd, Zopp,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

private theorem pg_ieee_floor_bounds (ctx : ExactRealContext) (x : Exact.R ctx) :
    CompCert4Lean.Flocq.Core.Raux.Exact.Rle ctx
      (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx
        (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx x)) x ∧
      Exact.Rlt ctx x
        (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx
          (Zadd (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx x) Zone)) := by
  let u : Z := ctx.spec.up x
  have hgt : ctx.spec.lt x (ctx.spec.ofZ u) :=
    ctx.certificate.sourceLaws.up_gt x
  have hgap : ctx.spec.le
      (CompCert4Lean.Foundation.FlocqReal.ExactReal.Rminus ctx.spec
        (ctx.spec.ofZ u) x) ctx.spec.one :=
    by
      have h := ctx.certificate.sourceLaws.up_gap x
      rw [ctx.certificate.sourceLaws.ofZ_one] at h
      simpa [u] using h
  have hu : Zadd (Zsub u Zone) Zone = u := by
    apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (Zadd (Zsub u Zone) Zone) = _
    simp only [Zadd, Zsub,
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ u - 1 + 1 = _
    omega
  have hupper : ctx.spec.lt x
      (ctx.spec.ofZ (Zadd (Zsub u Zone) Zone)) := by
    rw [hu]
    exact hgt
  have hlow : ctx.spec.le (ctx.spec.ofZ (Zsub u Zone)) x := by
    by_cases hgood : ctx.spec.le (ctx.spec.ofZ (Zsub u Zone)) x
    · exact hgood
    · exfalso
      let hnot := hgood
      have hlt : ctx.spec.lt x (ctx.spec.ofZ (Zsub u Zone)) := by
        rcases ctx.certificate.total_order x (ctx.spec.ofZ (Zsub u Zone)) with h | h
        · rcases h with h | h
          · exact h
          · exact (hnot (by rw [h]; exact ctx.certificate.orderedField.le_refl _)).elim
        · exact False.elim (hnot
              ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1))
      have h1 := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.ofZ Zone) x (ctx.spec.ofZ (Zsub u Zone)) hlt
      have hz1 : ctx.spec.add (ctx.spec.ofZ Zone)
          (ctx.spec.ofZ (Zsub u Zone)) = ctx.spec.ofZ u := by
        have hus : Zadd Zone (Zsub u Zone) = u := by
          apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
          change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zadd Zone (Zsub u Zone)) = _
          simp only [Zadd, Zsub,
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          omega
        have hz1' := ctx.certificate.sourceLaws.ofZ_add Zone (Zsub u Zone)
        rw [← hz1']
        exact congrArg ctx.spec.ofZ hus
      have hzone : ctx.spec.ofZ Zone = ctx.spec.one := by
        simpa [Zone] using ctx.certificate.sourceLaws.ofZ_one
      rw [hz1, hzone] at h1
      have h1' : ctx.spec.lt (ctx.spec.add (ctx.spec.ofZ Zone) x)
          (ctx.spec.ofZ u) := by
        rw [hzone]
        exact h1
      have h2 := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.neg x) (ctx.spec.add (ctx.spec.ofZ Zone) x)
        (ctx.spec.ofZ u) h1'
      rw [ctx.certificate.orderedField.add_comm (ctx.spec.ofZ Zone) x,
        ← ctx.certificate.orderedField.add_assoc,
        ctx.certificate.orderedField.neg_add_cancel,
        ctx.certificate.orderedField.zero_add,
        hzone] at h2
      rw [ctx.certificate.orderedField.add_comm (ctx.spec.neg x)
        (ctx.spec.ofZ u)] at h2
      have h2' : ctx.spec.lt ctx.spec.one
          (CompCert4Lean.Foundation.FlocqReal.ExactReal.Rminus ctx.spec
            (ctx.spec.ofZ u) x) := by
        simpa [CompCert4Lean.Foundation.FlocqReal.ExactReal.Rminus,
          ctx.certificate.sourceLaws.ofZ_one] using h2
      exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h2').2 hgap
  constructor
  · rw [show CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx x = Zsub u Zone by rfl]
    exact hlow
  · rw [show CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx x = Zsub u Zone by rfl]
    exact hupper

private theorem pg_ieee_rlt_bool_true (ctx : ExactRealContext)
    (x : Exact.R ctx) (h : ctx.spec.lt x ctx.spec.zero) :
    CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x ctx.spec.zero = true := by
  unfold CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool
  unfold CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare
  unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.total_order_T
  cases hdec : ctx.spec.lt_dec x ctx.spec.zero with
  | left _ => simp
  | right hn => exact (hn h).elim

private theorem pg_ieee_rlt_bool_false (ctx : ExactRealContext)
    (x : Exact.R ctx) (h : ctx.spec.le ctx.spec.zero x) :
    CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x ctx.spec.zero = false := by
  have hnot : ¬ ctx.spec.lt x ctx.spec.zero := by
    intro hlt
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt).2 h
  unfold CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool
  unfold CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare
  unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.total_order_T
  cases hdec : ctx.spec.lt_dec x ctx.spec.zero with
  | left hlt => exact (hnot hlt).elim
  | right _ =>
      cases hzero : ctx.spec.lt_dec ctx.spec.zero x with
      | left _ => simp
      | right _ => simp

theorem Ztrunc_range_pos : Ztrunc_range_posStatement := by
  intro ctx x hn
  by_cases hneg : ctx.spec.lt x ctx.spec.zero
  · change Zlt Z0 (CompCert4Lean.Flocq.Core.Raux.Exact.Ztrunc ctx x) at hn
    change Zlt Z0 (if CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x
        ctx.spec.zero = true then
        CompCert4Lean.Flocq.Core.Raux.Exact.Zceil ctx x else
        CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx x) at hn
    rw [pg_ieee_rlt_bool_true ctx x hneg] at hn
    simp only [if_pos rfl] at hn
    have hceil_nonpos : Zle (CompCert4Lean.Flocq.Core.Raux.Exact.Zceil ctx x) Z0 := by
      let y : Exact.R ctx := ctx.spec.neg x
      have hypos : ctx.spec.lt ctx.spec.zero y := by
        have hs := ctx.certificate.orderedField.add_lt_compat_l (ctx.spec.neg x)
          x ctx.spec.zero hneg
        rw [ctx.certificate.orderedField.neg_add_cancel,
          ctx.certificate.orderedField.add_zero] at hs
        exact hs
      have hb := pg_ieee_floor_bounds ctx y
      have hk : Zle Z0 (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx y) := by
        by_cases hkgood : Zle Z0 (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx y)
        · exact hkgood
        · exfalso
          let hk := hkgood
          have hklt : Zlt (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx y) Z0 := by
            change ¬ _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 ≤
              _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx y) at hk
            have hz0int : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 =
                (0 : Int) := by rfl
            rw [hz0int] at hk
            change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx y) < 0
            omega
          have hkplus : Zle
              (Zadd (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx y) Zone) Z0 := by
            change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (Zadd (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx y) Zone) ≤ 0
            simp only [Zadd,
              _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
              _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
            change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx y) + 1 ≤ 0
            change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx y) < 0 at hklt
            omega
          have hle := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_le
            ctx (Zadd (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx y) Zone) Z0 hkplus
          change ctx.spec.le (ctx.spec.ofZ
            (Zadd (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx y) Zone))
              (ctx.spec.ofZ Z0) at hle
          have hz0 : ctx.spec.ofZ Z0 = ctx.spec.zero := by
            simpa [Z0] using ctx.certificate.sourceLaws.ofZ_zero
          rw [hz0] at hle
          have hypos' : ctx.spec.le ctx.spec.zero y :=
            ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hypos).1
          have hley : ctx.spec.le
              (ctx.spec.ofZ
                (Zadd (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx y) Zone)) y :=
            ctx.certificate.orderedField.le_trans _ _ _ hle hypos'
          exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hb.2).2 hley
      unfold CompCert4Lean.Flocq.Core.Raux.Exact.Zceil
      change Zle (Zopp (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx y)) Z0
      change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Zopp (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx y)) ≤ 0
      simp only [Zopp,
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx y) ≥ 0 at hk
      omega
    exfalso
    change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 <
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Flocq.Core.Raux.Exact.Zceil ctx x) at hn
    change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Flocq.Core.Raux.Exact.Zceil ctx x) ≤ 0 at hceil_nonpos
    have hz0int : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 = (0 : Int) := by
      rfl
    rw [hz0int] at hn
    omega
  · have hnonneg : ctx.spec.le ctx.spec.zero x := by
      rcases ctx.certificate.total_order x ctx.spec.zero with h | h
      · rcases h with hlt | heq
        · exact (hneg hlt).elim
        · rw [heq]
          exact ctx.certificate.orderedField.le_refl _
      · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1
    have htrunc : CompCert4Lean.Flocq.Core.Raux.Exact.Ztrunc ctx x =
        CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx x := by
      change (if CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x
          ctx.spec.zero = true then
          CompCert4Lean.Flocq.Core.Raux.Exact.Zceil ctx x else
          CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx x) = _
      simp [pg_ieee_rlt_bool_false ctx x hnonneg]
    unfold CompCert4Lean.Lib.IEEE754_extra.Exact.Rle
      CompCert4Lean.Flocq.IEEE754.Binary.Exact.Rle
      CompCert4Lean.Flocq.IEEE754.BinarySingleNaN.Exact.Rle
      CompCert4Lean.Lib.IEEE754_extra.Exact.Rlt
      CompCert4Lean.Flocq.IEEE754.Binary.Exact.Rlt
      CompCert4Lean.Flocq.IEEE754.BinarySingleNaN.Exact.Rlt
      CompCert4Lean.Lib.IEEE754_extra.Exact.IZR
      CompCert4Lean.Flocq.IEEE754.BinarySingleNaN.Exact.IZR
      CompCert4Lean.Lib.IEEE754_extra.Exact.Ztrunc
      CompCert4Lean.Flocq.IEEE754.BinarySingleNaN.Exact.Ztrunc
    rw [htrunc]
    exact pg_ieee_floor_bounds ctx x

end CompCert4Lean.Lib.IEEE754_extra
namespace CompCert4Lean.Lib.IEEE754_extra
open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754
private theorem local_zdiv_nonneg (x y : Z) (hx : Zlt Z0 x) (hy : Zlt Z0 y) :
    Zle Z0 (Zdiv x y) := by
  let q : Z := Zdiv x y
  let r : Z := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y
  have hdecomp : x = Zadd (Zmul y q) r := by
    simpa [q, r, Zadd, Zmul] using
      (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Z_div_mod_eq_full x y)
  have hrange := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Z_mod_lt x y
    (show _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.gt y Z0 from hy)
  change (0 : Int) ≤ _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zdiv x y)
  by_cases hqgood : Zle Z0 (Zdiv x y)
  · exact hqgood
  · have hq := hqgood
    have hqneg : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q < 0 := by
      change ¬ (0 : Int) ≤ _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q at hq
      exact Int.lt_of_not_ge hq
    have hypos : (0 : Int) < _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y := hy
    have hqle : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q ≤ -1 := by
      have := Int.le_sub_one_of_lt hqneg
      simpa using this
    have hmul_le := Int.mul_le_mul_of_nonneg_left hqle (Int.le_of_lt hypos)
    have hmul_le' : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y *
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q ≤
        -_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y := by
      simpa using hmul_le
    have hrem_lt : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r <
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y := hrange.2
    rw [hdecomp] at hx
    simp only [Zadd, Zmul,
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hx
    change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 <
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y *
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q +
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r)) at hx
    simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hx
    change (0 : Int) < _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y *
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q +
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r at hx
    omega

private theorem local_floor_div (ctx : ExactRealContext) (x y : Z) (hy : Zlt Z0 y) :
    CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx
      (CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv ctx.spec
        (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx x)
        (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx y)) = Zdiv x y := by
  let q : Z := Zdiv x y
  let r : Z := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo x y
  have hdecomp : x = Zadd (Zmul y q) r := by
    simpa [q, r, Zadd, Zmul] using
      (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Z_div_mod_eq_full x y)
  have hrange := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Z_mod_lt x y
    (show _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.gt y Z0 from hy)
  have hq_int : Zle (Zmul y q) x := by
    change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zmul y q) ≤
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x
    rw [hdecomp]
    simp only [Zadd, Zmul,
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    have hr0 : (0 : Int) ≤ _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r := by
      exact hrange.1
    omega
  have hupper_int : Zlt x (Zmul y (Zadd q Zone)) := by
    change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zmul y (Zadd q Zone))
    rw [hdecomp]
    simp only [Zadd, Zmul,
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    simp only [Int.mul_add, _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    have hzone : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by rfl
    rw [hzone]
    have hrlt : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r <
        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y := hrange.2
    have hyi : 0 < _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y := hy
    omega
  have hypos : ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ y) := by
    rw [← ctx.certificate.sourceLaws.ofZ_zero]
    exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt ctx Z0 y hy
  have hyne : ctx.spec.ofZ y ≠ ctx.spec.zero := by
    intro heq
    rw [heq] at hypos
    exact ctx.certificate.orderedField.lt_irrefl _ hypos
  let ratio := CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv ctx.spec
        (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx x)
        (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx y)
  have hmul_ratio : ctx.spec.mul (ctx.spec.ofZ y) ratio = ctx.spec.ofZ x := by
    dsimp [ratio, CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv]
    rw [ctx.certificate.orderedField.div_eq_mul_inv]
    calc
      ctx.spec.mul (ctx.spec.ofZ y)
          (ctx.spec.mul (ctx.spec.ofZ x) (ctx.spec.inv (ctx.spec.ofZ y))) =
          ctx.spec.mul (ctx.spec.ofZ x)
            (ctx.spec.mul (ctx.spec.ofZ y) (ctx.spec.inv (ctx.spec.ofZ y))) := by
              rw [← ctx.certificate.orderedField.mul_assoc,
                ctx.certificate.orderedField.mul_comm (ctx.spec.ofZ y) (ctx.spec.ofZ x),
                ctx.certificate.orderedField.mul_assoc]
      _ = ctx.spec.mul (ctx.spec.ofZ x)
            (ctx.spec.mul (ctx.spec.inv (ctx.spec.ofZ y)) (ctx.spec.ofZ y)) := by
              exact congrArg (fun z => ctx.spec.mul (ctx.spec.ofZ x) z)
                (ctx.certificate.orderedField.mul_comm (ctx.spec.ofZ y) (ctx.spec.inv (ctx.spec.ofZ y)))
      _ = ctx.spec.mul (ctx.spec.ofZ x) ctx.spec.one := by
              rw [ctx.certificate.orderedField.inv_mul_cancel _ hyne]
      _ = ctx.spec.ofZ x := ctx.certificate.orderedField.mul_one _
  have hq_real : ctx.spec.le (ctx.spec.ofZ q) ratio := by
    rcases ctx.certificate.total_order (ctx.spec.ofZ q) ratio with h | h
    · rcases h with h | h
      · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1
      · rw [h]
        exact ctx.certificate.orderedField.le_refl _
    · exfalso
      have hm := ctx.certificate.orderedField.mul_lt_compat_l (ctx.spec.ofZ y)
        ratio (ctx.spec.ofZ q) hypos h
      rw [hmul_ratio] at hm
      have hmq' : ctx.spec.mul (ctx.spec.ofZ y) (ctx.spec.ofZ q) = ctx.spec.ofZ (Zmul y q) := by
        exact (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR ctx y q).symm
      rw [hmq'] at hm
      have hqx := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_le ctx
        (Zmul y q) x hq_int
      change ctx.spec.le (ctx.spec.ofZ (Zmul y q)) (ctx.spec.ofZ x) at hqx
      exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hm).2 hqx
  have hupper_real : ctx.spec.lt ratio (ctx.spec.ofZ (Zadd q Zone)) := by
    rcases ctx.certificate.total_order ratio (ctx.spec.ofZ (Zadd q Zone)) with h | h
    · rcases h with h | h
      · exact h
      · exfalso
        have heqmul := congrArg (fun z => ctx.spec.mul (ctx.spec.ofZ y) z) h
        rw [hmul_ratio] at heqmul
        have hmq' : ctx.spec.mul (ctx.spec.ofZ y) (ctx.spec.ofZ (Zadd q Zone)) =
            ctx.spec.ofZ (Zmul y (Zadd q Zone)) := by
          exact (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR ctx y (Zadd q Zone)).symm
        rw [hmq'] at heqmul
        have hxu := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt ctx x
          (Zmul y (Zadd q Zone)) hupper_int
        change ctx.spec.lt (ctx.spec.ofZ x) (ctx.spec.ofZ (Zmul y (Zadd q Zone))) at hxu
        rw [← heqmul] at hxu
        exact ctx.certificate.orderedField.lt_irrefl _ hxu
    · exfalso
      have hm := ctx.certificate.orderedField.mul_lt_compat_l (ctx.spec.ofZ y)
        (ctx.spec.ofZ (Zadd q Zone)) ratio hypos h
      rw [hmul_ratio] at hm
      have hmq' : ctx.spec.mul (ctx.spec.ofZ y) (ctx.spec.ofZ (Zadd q Zone)) =
          ctx.spec.ofZ (Zmul y (Zadd q Zone)) := by
        exact (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR ctx y (Zadd q Zone)).symm
      rw [hmq'] at hm
      have hxu := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt ctx x
        (Zmul y (Zadd q Zone)) hupper_int
      exact (ctx.certificate.orderedField.lt_irrefl _
        (ctx.certificate.orderedField.lt_trans _ _ _ hxu hm)).elim
  apply CompCert4Lean.Flocq.Core.Raux.Zfloor_imp ctx q ratio
  constructor
  · exact hq_real
  · change ctx.spec.lt ratio (ctx.spec.ofZ (Zadd q (Zpos xH)))
    exact hupper_real

private theorem local_trunc_div (ctx : ExactRealContext) (x y : Z)
    (hx : Zle Z0 x) (hy : Zlt Z0 y) :
    CompCert4Lean.Flocq.Core.Raux.Exact.Ztrunc ctx
      (CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv ctx.spec
        (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx x)
        (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx y)) = Zdiv x y := by
  have hnonneg : ctx.spec.le ctx.spec.zero
      (CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv ctx.spec
        (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx x)
        (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx y)) := by
    change ctx.spec.le ctx.spec.zero
      (ctx.spec.div (ctx.spec.ofZ x) (ctx.spec.ofZ y))
    rw [ctx.certificate.orderedField.div_eq_mul_inv]
    have hxin : ctx.spec.le ctx.spec.zero (ctx.spec.ofZ x) := by
      rw [← ctx.certificate.sourceLaws.ofZ_zero]
      exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_le ctx Z0 x hx
    have hypos : ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ y) := by
      rw [← ctx.certificate.sourceLaws.ofZ_zero]
      exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt ctx Z0 y hy
    have hypos' : CompCert4Lean.Flocq.Core.Raux.Exact.Rlt ctx
        (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx Z0) (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx y) := by
      change ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.ofZ y)
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact hypos
    have hinvle : ctx.spec.le ctx.spec.zero (ctx.spec.inv (ctx.spec.ofZ y)) := by
      have hi := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rinv_0_lt_compat ctx
        (ctx.spec.ofZ y) hypos'
      change ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.inv (ctx.spec.ofZ y)) at hi
      rw [ctx.certificate.sourceLaws.ofZ_zero] at hi
      exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hi |>.1
    have hxin' : CompCert4Lean.Flocq.Core.Raux.Exact.Rle ctx
        (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx Z0) (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx x) := by
      change ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.ofZ x)
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact hxin
    have hinvle' : CompCert4Lean.Flocq.Core.Raux.Exact.Rle ctx
        (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx Z0)
        (CompCert4Lean.Flocq.Core.Raux.Exact.Rinv ctx (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx y)) := by
      change ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.inv (ctx.spec.ofZ y))
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact hinvle
    have hp := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_pos ctx
      (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx x)
      (CompCert4Lean.Flocq.Core.Raux.Exact.Rinv ctx (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx y)) hxin' hinvle'
    change ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.mul (ctx.spec.ofZ x) (ctx.spec.inv (ctx.spec.ofZ y))) at hp
    rw [ctx.certificate.sourceLaws.ofZ_zero] at hp
    exact hp
  unfold CompCert4Lean.Flocq.Core.Raux.Exact.Ztrunc
  have hb0 : CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx
      (CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv ctx.spec
        (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx x)
        (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx y))
      (CompCert4Lean.Flocq.Core.Raux.Exact.R0 ctx) = false := by
    apply CompCert4Lean.Flocq.Core.Raux.Rlt_bool_false ctx
    exact hnonneg
  rw [hb0]
  exact local_floor_div ctx x y hy
theorem ZofB_range_pos {prec emax : Z} [Prec_gt_0 prec] [Prec_lt_emax prec emax] : ZofB_range_posStatement (prec := prec) (emax := emax) := by
  dsimp [ZofB_range_posStatement, keepPrecisionHypotheses]
  intro f n hfn hn ctx
  cases f with
  | mk f hcert =>
    cases f with
    | B754_nan => simp [ZofB] at hfn
    | B754_infinity s => simp [ZofB] at hfn
    | B754_zero s =>
      simp [ZofB] at hfn
      subst n
      change Zlt Z0 Z0 at hn
      change (0 : Int) < 0 at hn
      omega
    | B754_finite s m e =>
      cases e with
      | Z0 =>
        simp [ZofB] at hfn
        cases s with
        | true =>
          rw [← hfn] at hn
          change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 <
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Zaux.cond_Zopp true (Zpos m)) at hn
          simp [Zaux.cond_Zopp, CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.cond_Zopp,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hn
          have hz0 : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 = (0 : Int) := by rfl
          rw [hz0] at hn
          have hmpos : (0 : Int) < _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos m) := by
            simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
            change (0 : Int) < Int.ofNat
              (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m)
            change Int.ofNat 0 < Int.ofNat
              (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m)
            exact Int.ofNat_lt.mpr
              (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive m)
          omega
        | false =>
          simp [Zaux.cond_Zopp, CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.cond_Zopp] at hfn
          subst n
          change Exact.Rle ctx (Exact.IZR ctx (Zpos m))
            (Exact.Rmult ctx (Exact.IZR ctx (Zpos m))
              (Exact.bpow ctx Zaux.radix2 Z0)) ∧
            Exact.Rlt ctx (Exact.Rmult ctx (Exact.IZR ctx (Zpos m))
              (Exact.bpow ctx Zaux.radix2 Z0))
              (Exact.IZR ctx (Zadd (Zpos m) Zone))
          have hbpow : CompCert4Lean.Lib.IEEE754_extra.Exact.bpow ctx
              Zaux.radix2 Z0 = ctx.spec.one := by rfl
          rw [hbpow]
          change ctx.spec.le (ctx.spec.ofZ (Zpos m))
              (ctx.spec.mul (ctx.spec.ofZ (Zpos m)) ctx.spec.one) ∧
            ctx.spec.lt (ctx.spec.mul (ctx.spec.ofZ (Zpos m)) ctx.spec.one)
              (ctx.spec.ofZ (Zadd (Zpos m) Zone))
          rw [ctx.certificate.orderedField.mul_one]
          constructor
          · exact ctx.certificate.orderedField.le_refl _
          · apply CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt ctx
            change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos m) < _
            simp [Zadd, _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
              _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
            have hzone : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by rfl
            rw [hzone]
            omega
      | Zpos p =>
        simp [ZofB] at hfn
        cases s with
        | true =>
          rw [← hfn] at hn
          change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 <
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Zmul (Zaux.cond_Zopp true (Zpos m)) (Zpower_pos Ztwo p)) at hn
          simp [Zaux.cond_Zopp, CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.cond_Zopp,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
            Zmul,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hn
          have hmpos : (0 : Int) < _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos m) := by
            simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
            change (0 : Int) < Int.ofNat
              (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m)
            change Int.ofNat 0 < Int.ofNat
              (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m)
            exact Int.ofNat_lt.mpr
              (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive m)
          have hpbase : Zlt Z0 Ztwo := by
            change (0 : Int) < 2
            decide
          have hpowpos := CompCert4Lean.Flocq.Core.Zaux.Zpower_pos_gt_0 Ztwo p hpbase
          change (0 : Int) < -_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos m) *
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpower_pos Ztwo p) at hn
          have hnegm : -_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos m) < 0 :=
            Int.neg_neg_of_pos hmpos
          have hneg : -_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos m) *
              _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpower_pos Ztwo p) < 0 := by
            exact Int.mul_neg_of_neg_of_pos hnegm hpowpos
          omega
        | false =>
          simp [Zaux.cond_Zopp, CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.cond_Zopp] at hfn
          subst n
          change Exact.Rle ctx (Exact.IZR ctx (Zmul (Zpos m) (Zpower_pos Ztwo p)))
            (Exact.Rmult ctx (Exact.IZR ctx (Zpos m))
              (Exact.bpow ctx Zaux.radix2 (Zpos p))) ∧
            Exact.Rlt ctx (Exact.Rmult ctx (Exact.IZR ctx (Zpos m))
              (Exact.bpow ctx Zaux.radix2 (Zpos p)))
              (Exact.IZR ctx (Zadd (Zmul (Zpos m) (Zpower_pos Ztwo p)) Zone))
          have hbpow : Exact.bpow ctx Zaux.radix2 (Zpos p) =
              Exact.IZR ctx (Zpower_pos Ztwo p) := by rfl
          rw [hbpow]
          change ctx.spec.le (ctx.spec.ofZ (Zmul (Zpos m) (Zpower_pos Ztwo p)))
              (ctx.spec.mul (ctx.spec.ofZ (Zpos m)) (ctx.spec.ofZ (Zpower_pos Ztwo p))) ∧
            ctx.spec.lt (ctx.spec.mul (ctx.spec.ofZ (Zpos m)) (ctx.spec.ofZ (Zpower_pos Ztwo p)))
              (ctx.spec.ofZ (Zadd (Zmul (Zpos m) (Zpower_pos Ztwo p)) Zone))
          have hmul := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR ctx
            (Zpos m) (Zpower_pos Ztwo p)
          change ctx.spec.ofZ (Zmul (Zpos m) (Zpower_pos Ztwo p)) =
            ctx.spec.mul (ctx.spec.ofZ (Zpos m)) (ctx.spec.ofZ (Zpower_pos Ztwo p)) at hmul
          rw [← hmul]
          constructor
          · exact ctx.certificate.orderedField.le_refl _
          · apply CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt ctx
            change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (Zmul (Zpos m) (Zpower_pos Ztwo p)) < _
            simp [Zadd, _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
              _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
            have hzone : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by rfl
            rw [hzone]
            omega
      | Zneg p =>
        simp [ZofB] at hfn
        cases s with
        | true =>
          rw [← hfn] at hn
          change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 <
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Zaux.cond_Zopp true (Zdiv (Zpos m) (Zpower_pos Ztwo p))) at hn
          simp [Zaux.cond_Zopp,
            CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.cond_Zopp,
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hn
          have hmpos : Zlt Z0 (Zpos m) := by
            change (0 : Int) < _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos m)
            simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
            change (0 : Int) < Int.ofNat
              (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m)
            change Int.ofNat 0 < Int.ofNat
              (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m)
            exact Int.ofNat_lt.mpr
              (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive m)
          have hpbase : Zlt Z0 Ztwo := by
            change (0 : Int) < 2
            decide
          have hpowpos := CompCert4Lean.Flocq.Core.Zaux.Zpower_pos_gt_0 Ztwo p hpbase
          have hqnonneg := local_zdiv_nonneg (Zpos m) (Zpower_pos Ztwo p)
            hmpos hpowpos
          change (0 : Int) < -
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Zdiv (Zpos m) (Zpower_pos Ztwo p)) at hn
          change (0 : Int) ≤
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Zdiv (Zpos m) (Zpower_pos Ztwo p)) at hqnonneg
          omega
        | false =>
          simp [Zaux.cond_Zopp,
            CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.cond_Zopp] at hfn
          subst n
          change Exact.Rle ctx (Exact.IZR ctx (Zdiv (Zpos m) (Zpower_pos Ztwo p)))
            (Exact.Rmult ctx (Exact.IZR ctx (Zpos m))
              (Exact.bpow ctx Zaux.radix2 (Zneg p))) ∧
            Exact.Rlt ctx (Exact.Rmult ctx (Exact.IZR ctx (Zpos m))
              (Exact.bpow ctx Zaux.radix2 (Zneg p)))
              (Exact.IZR ctx (Zadd (Zdiv (Zpos m) (Zpower_pos Ztwo p)) Zone))
          have hbpow : Exact.bpow ctx Zaux.radix2 (Zneg p) =
              Exact.Rinv ctx (Exact.IZR ctx (Zpower_pos Ztwo p)) := by rfl
          rw [hbpow]
          change ctx.spec.le (ctx.spec.ofZ (Zdiv (Zpos m) (Zpower_pos Ztwo p)))
              (ctx.spec.mul (ctx.spec.ofZ (Zpos m))
                (ctx.spec.inv (ctx.spec.ofZ (Zpower_pos Ztwo p)))) ∧
            ctx.spec.lt (ctx.spec.mul (ctx.spec.ofZ (Zpos m))
              (ctx.spec.inv (ctx.spec.ofZ (Zpower_pos Ztwo p))))
              (ctx.spec.ofZ (Zadd (Zdiv (Zpos m) (Zpower_pos Ztwo p)) Zone))
          rw [← ctx.certificate.orderedField.div_eq_mul_inv]
          have hmpos : Zlt Z0 (Zpos m) := by
            change (0 : Int) < _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos m)
            simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
            change (0 : Int) < Int.ofNat
              (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m)
            change Int.ofNat 0 < Int.ofNat
              (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m)
            exact Int.ofNat_lt.mpr
              (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive m)
          have hpbase : Zlt Z0 Ztwo := by
            change (0 : Int) < 2
            decide
          have hpowpos := CompCert4Lean.Flocq.Core.Zaux.Zpower_pos_gt_0 Ztwo p hpbase
          have hmle : Zle Z0 (Zpos m) := by
            change (0 : Int) ≤ _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos m)
            exact Int.le_of_lt (by exact hmpos)
          have htrunc : Exact.Ztrunc ctx
              (Exact.Rdiv ctx (Exact.IZR ctx (Zpos m))
                (Exact.IZR ctx (Zpower_pos Ztwo p))) =
              Zdiv (Zpos m) (Zpower_pos Ztwo p) := by
            exact local_trunc_div ctx (Zpos m) (Zpower_pos Ztwo p) hmle hpowpos
          have hpos : Zlt Z0
              (Exact.Ztrunc ctx (Exact.Rdiv ctx (Exact.IZR ctx (Zpos m))
              (Exact.IZR ctx (Zpower_pos Ztwo p)))) := by
            rw [htrunc]
            exact hn
          have hbounds := Ztrunc_range_pos ctx
            (Exact.Rdiv ctx (Exact.IZR ctx (Zpos m))
              (Exact.IZR ctx (Zpower_pos Ztwo p))) hpos
          rw [htrunc] at hbounds
          change ctx.spec.le (ctx.spec.ofZ (Zdiv (Zpos m) (Zpower_pos Ztwo p)))
              (ctx.spec.div (ctx.spec.ofZ (Zpos m))
                (ctx.spec.ofZ (Zpower_pos Ztwo p))) ∧
            ctx.spec.lt (ctx.spec.div (ctx.spec.ofZ (Zpos m))
              (ctx.spec.ofZ (Zpower_pos Ztwo p)))
              (ctx.spec.ofZ (Zadd (Zdiv (Zpos m) (Zpower_pos Ztwo p)) Zone)) at hbounds
          exact hbounds
end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754

private theorem pg_zsub_as_add (a b : Z) :
    Zsub a b = Zadd a (Zopp b) := by
  apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [Zsub, Zadd, Zopp,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

theorem Zfloor_minus : Zfloor_minusStatement := by
  intro ctx x n
  let f := Exact.Zfloor ctx x
  apply CompCert4Lean.Flocq.Core.Raux.Zfloor_imp ctx (Zsub f n)
    (Exact.Rminus ctx x (Exact.IZR ctx n))
  constructor
  · have hf := CompCert4Lean.Flocq.Core.Raux.Zfloor_lb ctx x
    have hsub :
        ctx.spec.ofZ (Zsub f n) =
          ctx.spec.add (ctx.spec.ofZ f) (ctx.spec.neg (ctx.spec.ofZ n)) := by
      rw [pg_zsub_as_add, ctx.certificate.sourceLaws.ofZ_add,
        ctx.certificate.sourceLaws.ofZ_neg]
    change ctx.spec.le (ctx.spec.ofZ (Zsub f n))
      (ctx.spec.add x (ctx.spec.neg (ctx.spec.ofZ n)))
    rw [hsub]
    exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_le_compat_r
      ctx (ctx.spec.neg (ctx.spec.ofZ n)) (ctx.spec.ofZ f) x hf
  · have hf := CompCert4Lean.Flocq.Core.Raux.Zfloor_ub ctx x
    have hlt := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rplus_lt_compat_r
      ctx (ctx.spec.neg (ctx.spec.ofZ n)) x
        (ctx.spec.add (ctx.spec.ofZ f) (ctx.spec.one)) hf
    have hsub :
        ctx.spec.ofZ (Zsub f n) =
          ctx.spec.add (ctx.spec.ofZ f) (ctx.spec.neg (ctx.spec.ofZ n)) := by
      rw [pg_zsub_as_add, ctx.certificate.sourceLaws.ofZ_add,
        ctx.certificate.sourceLaws.ofZ_neg]
    have hone :
        ctx.spec.ofZ (Zadd (Zsub f n) (Zpos xH)) =
          ctx.spec.add (ctx.spec.add (ctx.spec.ofZ f)
            (ctx.spec.neg (ctx.spec.ofZ n))) ctx.spec.one := by
      rw [ctx.certificate.sourceLaws.ofZ_add,
        ctx.certificate.sourceLaws.ofZ_one, hsub]
    change ctx.spec.lt (ctx.spec.add x (ctx.spec.neg (ctx.spec.ofZ n)))
      (ctx.spec.ofZ (Zadd (Zsub f n) (Zpos xH)))
    rw [hone]
    rw [ctx.certificate.orderedField.add_assoc,
      ctx.certificate.orderedField.add_comm
        (ctx.spec.neg (ctx.spec.ofZ n)) (ctx.spec.one),
      ← ctx.certificate.orderedField.add_assoc]
    exact hlt

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

theorem ZofB_range_inversion {prec emax : Z} :
    ZofB_range_inversionStatement (prec := prec) (emax := emax) := by
  intro f min max n h
  unfold ZofB_range at h
  cases hz : ZofB f.1 with
  | none => simp [hz] at h
  | some z =>
    simp [hz] at h
    rcases h with ⟨⟨hmin, hmax⟩, hzn⟩
    subst n
    constructor
    · have hs : CompCert4Lean.Flocq.Core.Zaux.Zle_bool_prop min z true := by
        simpa [hmin] using
          (CompCert4Lean.Flocq.Core.Zaux.Zle_bool_spec min z)
      cases hs with
      | Zle_bool_true_ hle => exact hle
    constructor
    · have hs : CompCert4Lean.Flocq.Core.Zaux.Zle_bool_prop z max true := by
        simpa [hmax] using
          (CompCert4Lean.Flocq.Core.Zaux.Zle_bool_spec z max)
      cases hs with
      | Zle_bool_true_ hle => exact hle
    · rfl

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754

private theorem pg_zadd_comm (a b : Z) : Zadd a b = Zadd b a := by
  apply _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [Zadd,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

theorem Bmult_commut :
    ∀ {prec emax : Z} [pgt : Prec_gt_0 prec]
      [ple : Prec_lt_emax prec emax],
      Bmult_commutStatement (prec := prec) (emax := emax) := by
  intro prec emax pgt ple mult_nan m x y hnan
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  unfold CompCert4Lean.Flocq.IEEE754.Binary.Bmult
  have hnan' := congrArg (fun z : NaNResult prec emax =>
      (⟨z.val, z.property.1⟩ :
        { z : CompCert4Lean.Flocq.IEEE754.Binary.binary_float prec emax //
            CompCert4Lean.Flocq.IEEE754.Binary.is_nan z = true })) hnan
  rw [hnan']
  unfold BinarySingleNaN.Bmult
  cases x <;> cases y <;> simp [CompCert4Lean.Flocq.IEEE754.BinarySingleNaN.B2SF,
    CompCert4Lean.Flocq.IEEE754.Binary.B2BSN,
    CompCert4Lean.Flocq.IEEE754.Binary.BSN2B,
    _root_.CompCert4Lean.Foundation.Logic.Rocq.Coq.Bool.Bool.xorb_comm,
    _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.mul_comm,
    pg_zadd_comm] <;>
    rw [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.mul_comm]

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

private theorem pg_ieee754_ziter_unfold_succ {A : Type} (f : A → A) (x : A) (k : Nat) :
    Ziter (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (k + 1)) f x =
      Ziter (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat k) f (f x) := by
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.iter,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
    Int.ofNat_eq_natCast, Int.toNat_natCast]
  rfl

private theorem pg_ieee754_ziter_commute {A : Type} (f : A → A) (x : A) (k : Nat) :
    Ziter (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat k) f (f x) =
      f (Ziter (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat k) f x) := by
  induction k generalizing x with
  | zero =>
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.iter,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
        Int.ofNat_eq_natCast, Int.toNat_natCast]
      rfl
  | succ k ih =>
      rw [pg_ieee754_ziter_unfold_succ, pg_ieee754_ziter_unfold_succ]
      rw [ih (f x), ih x]

private theorem pg_ieee754_ziter_succ {A : Type} (f : A → A) (x : A) (k : Nat) :
    Ziter (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (k + 1)) f x =
      f (Ziter (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat k) f x) := by
  rw [pg_ieee754_ziter_unfold_succ, pg_ieee754_ziter_commute]

private theorem pg_ieee754_xO_iter (k : Nat) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
      (Ziter (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat k) xO xH) =
        2 ^ k := by
  induction k with
  | zero =>
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat xH = 1
      rfl
  | succ k ih =>
      rw [pg_ieee754_ziter_succ]
      change 2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
          (Ziter (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat k) xO xH) =
        2 ^ (k + 1)
      rw [ih]
      omega

private theorem pg_ieee754_pow_nat (k : Nat) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zpower Ztwo
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat k)) =
      Int.ofNat (2 ^ k) := by
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow Ztwo
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat k)) = _
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
  have hk : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat k) =
        Int.ofNat k := by
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  rw [hk]
  have htwo : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = (2 : Int) := by
    decide
  rw [htwo]
  have hkneg : ¬ (Int.ofNat k) < 0 := by
    exact Int.not_lt_of_ge (Int.natCast_nonneg k)
  simp only [hkneg, ↓reduceIte]
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  rw [show (Int.ofNat k).toNat = k by rfl]
  change Int.pow 2 k = Int.ofNat (2 ^ k)
  exact (Int.natCast_pow 2 k).symm

private theorem pg_ieee754_mantissa_nonneg (n : Z) (hn : Zle Z0 n) :
    Zpos (Ziter n xO xH) = Zpower Ztwo n := by
  have hn_int : (0 : Int) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n := hn
  let k := Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n)
  have hrepr : n =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat k := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat]
    exact (Int.toNat_of_nonneg hn_int).symm
  rw [hrepr]
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
      (Ziter (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat k) xO xH)) = _
  rw [pg_ieee754_xO_iter]
  exact (pg_ieee754_pow_nat k).symm

theorem Bexact_inverse_mantissa_value :
    ∀ {prec : Z} [Prec_gt_0 prec],
      Bexact_inverse_mantissa_valueStatement (prec := prec) := by
  intro prec pgt
  letI : Prec_gt_0 prec := pgt
  dsimp [Bexact_inverse_mantissa_valueStatement, keepPrecGt]
  apply pg_ieee754_mantissa_nonneg
  change (0 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
    (Zsub prec Zone)
  simp only [Zsub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  have hp : Zlt Z0 prec := pgt
  change (0 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec at hp
  have hzone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by
    decide
  rw [hzone]
  omega

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core

private theorem pg_ieee754_posSucc_nat (q : positive) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
        (_root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posSucc q) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q + 1 := by
  induction q with
  | xH => rfl
  | xI q ih =>
      change 2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
          (_root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posSucc q) =
        2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q + 1 + 1
      rw [ih]
      omega
  | xO q ih =>
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (.xI q) =
        2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q + 1
      rfl

private theorem pg_ieee754_digits_xO_iter (k : Nat) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
        (Digits.digits2_pos
          (Ziter (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat k)
            xO xH)) =
      k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pg_ieee754_ziter_succ]
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
          (_root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posSucc
            (Digits.digits2_pos
              (Ziter (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat k)
                xO xH))) =
        k + 1 + 1
      rw [pg_ieee754_posSucc_nat, ih]

theorem Bexact_inverse_mantissa_digits2_pos :
    ∀ {prec emax : Z} [Prec_gt_0 prec] [Prec_lt_emax prec emax],
      Bexact_inverse_mantissa_digits2_posStatement (prec := prec) (emax := emax) := by
  intro prec emax pgt ple
  letI : Prec_gt_0 prec := pgt
  letI : Prec_lt_emax prec emax := ple
  dsimp [Bexact_inverse_mantissa_digits2_posStatement, keepPrecisionHypotheses]
  have hp : Zlt Z0 prec := pgt
  change (0 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec at hp
  let k := Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec - 1)
  have hk_nonneg : (0 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec - 1 := by
    omega
  have hk : Int.ofNat k = CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec - 1 := by
    exact Int.toNat_of_nonneg hk_nonneg
  have hsub : Zsub prec Zone =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat k := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [Zsub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat]
    have hzone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by
      decide
    rw [hzone, hk]
  unfold Bexact_inverse_mantissa
  rw [hsub]
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change Int.ofNat
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
        (Digits.digits2_pos
          (Ziter (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat k)
            xO xH))) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec
  rw [pg_ieee754_digits_xO_iter]
  change (↑(k + 1) : Int) = _
  rw [Int.natCast_add]
  have hprec : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec =
      Int.ofNat k + 1 := by
    omega
  exact hprec.symm

theorem bounded_Bexact_inverse :
    ∀ {prec emax : Z} [Prec_gt_0 prec] [Prec_lt_emax prec emax],
      bounded_Bexact_inverseStatement (prec := prec) (emax := emax) := by
  intro prec emax pgt ple
  letI : Prec_gt_0 prec := pgt
  letI : Prec_lt_emax prec emax := ple
  dsimp [bounded_Bexact_inverseStatement, keepPrecisionHypotheses]
  intro e
  have hd := Bexact_inverse_mantissa_digits2_pos (prec := prec) (emax := emax)
  dsimp [Bexact_inverse_mantissa_digits2_posStatement, keepPrecisionHypotheses] at hd
  change (Zle (emin prec emax) e ∧ Zle e (Zsub emax prec)) ↔
    (_root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.bounded
      prec emax (Bexact_inverse_mantissa (prec := prec)) e = true)
  unfold _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.bounded
  unfold _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.canonical_mantissa
  unfold _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.fexp
  have hd' :
      _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.zpos
          (_root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos
            (Bexact_inverse_mantissa (prec := prec))) = prec := by
    exact hd
  rw [hd']
  let em := _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.emin prec emax
  let up := _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.zsub emax prec
  have hcancel :
      _root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.zsub
          (_root_.CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.zadd prec e) prec = e := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    omega
  rw [hcancel]
  change
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ em ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e ∧
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ up) ↔
      ((decide
          ((if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e ≤
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ em then em else e) = e) &&
        (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ up then true else false)) = true)
  have heq_iff : em = e ↔
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ em =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e := by
    constructor
    · exact fun h => congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ h
    · intro h
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      exact h
  by_cases hmax : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ em <;>
    by_cases hup : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ up <;>
    simp [hmax, hup, heq_iff] <;> omega

theorem Bexact_inverse_obligation_2Statement_proof :
    ∀ {prec emax : Z}, Bexact_inverse_obligation_2Statement (prec := prec) (emax := emax) := by
  simp [Bexact_inverse_obligation_2Statement]

theorem Bexact_inverse_obligation_3Statement_proof :
    ∀ {prec emax : Z}, Bexact_inverse_obligation_3Statement (prec := prec) (emax := emax) := by
  simp [Bexact_inverse_obligation_3Statement]

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

theorem Bexact_inverse_obligation_4Statement_proof :
    ∀ {prec emax : Z}, Bexact_inverse_obligation_4Statement (prec := prec) (emax := emax) := by
  intro prec emax b p hp
  dsimp [Bexact_inverse_obligation_4Statement]
  intro s m e0 hbound heq
  cases heq

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core

/-
theorem Bexact_inverse_correct :
    ∀ {prec emax : Z} [Prec_gt_0 prec] [Prec_lt_emax prec emax],
      Bexact_inverse_correctStatement (prec := prec) (emax := emax) := by
  intro prec emax pgt ple
  letI : Prec_gt_0 prec := pgt
  letI : Prec_lt_emax prec emax := ple
  dsimp [Bexact_inverse_correctStatement, keepPrecisionHypotheses]
  intro certificate f f' hresult
  rcases f with ⟨f, hf⟩
  cases f with
  | B754_zero s => simp [Bexact_inverse] at hresult
  | B754_infinity s => simp [Bexact_inverse] at hresult
  | B754_nan s p => simp [Bexact_inverse] at hresult
  | B754_finite s m e =>
      by_cases hm : m = Bexact_inverse_mantissa (prec := prec)
      · let e' := Zsub (Zopp e) (Zmul (Zsub prec Zone) Ztwo)
        cases hmin :
            _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.ZArith_dec.Z_le_dec
              (emin prec emax) e' with
        | left hemin =>
            cases hmax :
                _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.ZArith_dec.Z_le_dec
                  e' emax with
            | left hemax =>
                have hout : f'.val = CompCert4Lean.Flocq.IEEE754.Binary.B754_finite s m e' := by
                  simpa [Bexact_inverse, hm, e', hmin, hmax] using hresult.symm
                rw [hout]
                refine ⟨rfl, rfl, ?_⟩
                intro ctx
                have hmant : Zpos m = Zpower Ztwo (Zsub prec Zone) := by
                  have h := Bexact_inverse_mantissa_value (prec := prec)
                  dsimp [Bexact_inverse_mantissa_valueStatement, keepPrecGt] at h
                  simpa [hm] using h
                have hpow : Exact.bpow ctx Zaux.radix2 (Zsub prec Zone) =
                    Exact.IZR ctx (Zpos m) := by
                  have hp : Zle Z0 (Zsub prec Zone) := by
                    change (0 : Int) ≤
                      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                        (Zsub prec Zone)
                    simp only [Zsub,
                      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
                      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
                    have hp' := pgt
                    change (0 : Int) <
                      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec at hp'
                    have hzone :
                        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by
                      decide
                    rw [hzone]
                    omega
                  have h := CompCert4Lean.Flocq.Core.Raux.IZR_Zpower ctx Zaux.radix2
                    (Zsub prec Zone) hp
                  calc
                    Exact.bpow ctx Zaux.radix2 (Zsub prec Zone) =
                        Exact.IZR ctx (Zpower Ztwo (Zsub prec Zone)) := h.symm
                    _ = Exact.IZR ctx (Zpos m) := by rw [hmant]
                have hnonzero : Exact.B2R ctx (CompCert4Lean.Flocq.IEEE754.Binary.B754_finite
                      (prec := prec) (emax := emax) s m e) ≠
                    Exact.R0 ctx := by
                  apply CompCert4Lean.Flocq.Core.Float_prop.F2R_neq_0 ctx
                    Zaux.radix2
                  change Zaux.cond_Zopp s (Zpos m) ≠ Z0
                  cases s with
                  | false =>
                      change Zpos m ≠ Z0
                      intro hz
                      have hz' := congrArg
                        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hz
                      simp only [Zpos,
                        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hz'
                      have hmpos :=
                        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive m
                      omega
                  | true =>
                      change Zopp (Zpos m) ≠ Z0
                      intro hz
                      have hz' := congrArg
                        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hz
                      simp only [Zaux.cond_Zopp,
                        CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.cond_Zopp,
                        Zopp,
                        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
                        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hz'
                      have hmpos :=
                        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive m
                      omega
                constructor
                · change Exact.B2R ctx (CompCert4Lean.Flocq.IEEE754.Binary.B754_finite s m e') =
                    Exact.Rinv ctx (Exact.B2R ctx (CompCert4Lean.Flocq.IEEE754.Binary.B754_finite s m e))
                  change Exact.Rmult ctx (Exact.IZR ctx (Zaux.cond_Zopp s (Zpos m)))
                    (Exact.bpow ctx Zaux.radix2 e') = _
                  have hpowopp : ∀ q : Z,
                      Exact.bpow ctx Zaux.radix2 (Zopp q) =
                        Exact.Rinv ctx (Exact.bpow ctx Zaux.radix2 q) := by
                    intro q
                    have hqpos : Exact.Rlt ctx (Exact.R0 ctx)
                        (Exact.bpow ctx Zaux.radix2 q) :=
                      CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx Zaux.radix2 q
                    have hqne : Exact.bpow ctx Zaux.radix2 q ≠ Exact.R0 ctx := by
                      intro hz
                      rw [hz] at hqpos
                      exact ctx.certificate.orderedField.lt_irrefl _ hqpos
                    have hqsum : Zadd q (Zopp q) = Z0 := by
                      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
                      simp only [Zadd, Zopp,
                        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
                        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
                        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
                      change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q +
                        -_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ q = 0
                      omega
                    have hmul_zero :
                        Exact.Rmult ctx (Exact.bpow ctx Zaux.radix2 q)
                            (Exact.bpow ctx Zaux.radix2 (Zopp q)) =
                          Exact.Rone ctx := by
                      change ctx.spec.mul (Exact.bpow ctx Zaux.radix2 q)
                          (Exact.bpow ctx Zaux.radix2 (Zopp q)) = ctx.spec.one
                      have hplus := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx
                        Zaux.radix2 q (Zopp q)
                      change Exact.bpow ctx Zaux.radix2 (Zadd q (Zopp q)) =
                        ctx.spec.mul (Exact.bpow ctx Zaux.radix2 q)
                          (Exact.bpow ctx Zaux.radix2 (Zopp q)) at hplus
                      rw [← hplus, hqsum]
                      rfl
                    have hmul_inv :
                        Exact.Rmult ctx (Exact.bpow ctx Zaux.radix2 q)
                            (Exact.Rinv ctx (Exact.bpow ctx Zaux.radix2 q)) =
                          Exact.Rone ctx := by
                      change ctx.spec.mul (Exact.bpow ctx Zaux.radix2 q)
                          (Exact.Rinv ctx (Exact.bpow ctx Zaux.radix2 q)) = ctx.spec.one
                      calc
                        ctx.spec.mul (Exact.bpow ctx Zaux.radix2 q)
                            (Exact.Rinv ctx (Exact.bpow ctx Zaux.radix2 q)) =
                            ctx.spec.mul (Exact.Rinv ctx (Exact.bpow ctx Zaux.radix2 q))
                              (Exact.bpow ctx Zaux.radix2 q) :=
                                ctx.certificate.orderedField.mul_comm _ _
                        _ = ctx.spec.one :=
                          ctx.certificate.orderedField.inv_mul_cancel _ hqne
                    have hqne0 : Exact.bpow ctx Zaux.radix2 q ≠ Exact.IZR ctx Z0 := by
                      intro hz
                      have hz' : Exact.bpow ctx Zaux.radix2 q = Exact.R0 ctx := by
                        calc
                          Exact.bpow ctx Zaux.radix2 q = Exact.IZR ctx Z0 := hz
                          _ = Exact.R0 ctx := by
                            change ctx.spec.ofZ Z0 = ctx.spec.zero
                            exact ctx.certificate.sourceLaws.ofZ_zero
                      rw [hz'] at hqpos
                      exact ctx.certificate.orderedField.lt_irrefl _ hqpos
                    exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_eq_reg_r
                      ctx (Exact.bpow ctx Zaux.radix2 q)
                      (Exact.bpow ctx Zaux.radix2 (Zopp q))
                      (Exact.Rinv ctx (Exact.bpow ctx Zaux.radix2 q))
                      (by
                        change ctx.spec.mul (Exact.bpow ctx Zaux.radix2 q)
                            (Exact.bpow ctx Zaux.radix2 (Zopp q)) =
                          ctx.spec.mul (Exact.bpow ctx Zaux.radix2 q)
                            (Exact.Rinv ctx (Exact.bpow ctx Zaux.radix2 q))
                        exact hmul_zero.trans hmul_inv.symm) hqne0
                  have hexp : Zadd (Zsub prec Zone) e' =
                      Zopp (Zadd (Zsub prec Zone) e) := by
                    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
                    simp only [Zadd, Zsub, Zopp, Zmul,
                      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
                      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
                      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
                      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
                      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
                    omega
                  have hposid :
                      Exact.Rmult ctx (Exact.IZR ctx (Zpos m))
                          (Exact.bpow ctx Zaux.radix2 e') =
                        Exact.Rinv ctx
                          (Exact.Rmult ctx (Exact.IZR ctx (Zpos m))
                            (Exact.bpow ctx Zaux.radix2 e)) := by
                    rw [← hpow]
                    calc
                      Exact.Rmult ctx (Exact.bpow ctx Zaux.radix2 (Zsub prec Zone))
                          (Exact.bpow ctx Zaux.radix2 e') =
                          Exact.bpow ctx Zaux.radix2 (Zadd (Zsub prec Zone) e') :=
                            (CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx Zaux.radix2
                              (Zsub prec Zone) e').symm
                      _ = Exact.bpow ctx Zaux.radix2
                          (Zopp (Zadd (Zsub prec Zone) e)) := by rw [hexp]
                      _ = Exact.Rinv ctx
                          (Exact.bpow ctx Zaux.radix2 (Zadd (Zsub prec Zone) e)) :=
                            hpowopp _
                      _ = Exact.Rinv ctx
                          (Exact.Rmult ctx (Exact.bpow ctx Zaux.radix2 (Zsub prec Zone))
                            (Exact.bpow ctx Zaux.radix2 e)) := by
                            exact congrArg (Exact.Rinv ctx)
                              (CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx Zaux.radix2
                                (Zsub prec Zone) e)
                  have hposnonzero :
                      Exact.Rmult ctx (Exact.IZR ctx (Zpos m))
                          (Exact.bpow ctx Zaux.radix2 e) ≠ Exact.R0 ctx := by
                    change CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
                      (CompCert4Lean.Flocq.Core.Float_prop.Float Zaux.radix2
                        (Zpos m) e) ≠ Exact.R0 ctx
                    apply CompCert4Lean.Flocq.Core.Float_prop.F2R_neq_0 ctx Zaux.radix2
                    change Zpos m ≠ Z0
                    intro hz
                    have hz' := congrArg
                      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hz
                    simp only [Z0, Zpos,
                      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hz'
                    have hmpos :=
                      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive m
                    omega
                  have hinv_neg : ∀ x : Exact.R ctx, x ≠ Exact.R0 ctx →
                      Exact.Rinv ctx (Exact.Ropp ctx x) =
                        Exact.Ropp ctx (Exact.Rinv ctx x) := by
                    intro x hx
                    change ctx.spec.inv (ctx.spec.neg x) = ctx.spec.neg (ctx.spec.inv x)
                    have hx0 : x ≠ ctx.spec.zero := by
                      intro hz
                      apply hx
                      change x = ctx.spec.zero
                      exact hz
                    have hdouble : ctx.spec.neg (ctx.spec.neg x) = x := by
                      have hdouble' :=
                        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_involutive ctx x
                      change ctx.spec.neg (ctx.spec.neg x) = x at hdouble'
                      exact hdouble'
                    have hnx0 : ctx.spec.neg x ≠ ctx.spec.zero := by
                      intro hz
                      apply hx0
                      calc
                        x = ctx.spec.neg (ctx.spec.neg x) := hdouble.symm
                        _ = ctx.spec.neg ctx.spec.zero := by rw [hz]
                        _ = ctx.spec.zero := by
                          calc
                            ctx.spec.neg ctx.spec.zero =
                                ctx.spec.add (ctx.spec.neg ctx.spec.zero) ctx.spec.zero :=
                                  (ctx.certificate.orderedField.add_zero _).symm
                            _ = ctx.spec.zero :=
                              ctx.certificate.orderedField.neg_add_cancel _
                    have hx_izr : x ≠ Exact.IZR ctx Z0 := by
                      intro hz
                      apply hx
                      calc
                        x = Exact.IZR ctx Z0 := hz
                        _ = Exact.R0 ctx := by
                          change ctx.spec.ofZ Z0 = ctx.spec.zero
                          exact ctx.certificate.sourceLaws.ofZ_zero
                    refine CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_eq_reg_r
                      ctx x (Exact.Rinv ctx (Exact.Ropp ctx x))
                      (Exact.Ropp ctx (Exact.Rinv ctx x)) ?_ hx_izr
                    change ctx.spec.mul (ctx.spec.inv (ctx.spec.neg x)) x =
                      ctx.spec.mul (ctx.spec.neg (ctx.spec.inv x)) x
                    calc
                      ctx.spec.mul (ctx.spec.inv (ctx.spec.neg x)) x =
                          ctx.spec.neg ctx.spec.one := by
                            calc
                              ctx.spec.mul (ctx.spec.inv (ctx.spec.neg x)) x =
                                  ctx.spec.mul (ctx.spec.inv (ctx.spec.neg x))
                                    (ctx.spec.neg (ctx.spec.neg x)) := by
                                      rw [hdouble]
                              _ = ctx.spec.neg
                                  (ctx.spec.mul (ctx.spec.inv (ctx.spec.neg x))
                                    (ctx.spec.neg x)) := by
                                      have h :=
                                        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_mult_distr_r_reverse
                                          ctx (Exact.Rinv ctx (Exact.Ropp ctx x)) (Exact.Ropp ctx x)
                                      change ctx.spec.mul (ctx.spec.inv (ctx.spec.neg x))
                                          (ctx.spec.neg (ctx.spec.neg x)) =
                                        ctx.spec.neg (ctx.spec.mul (ctx.spec.inv (ctx.spec.neg x))
                                          (ctx.spec.neg x)) at h
                                      exact h
                              _ = ctx.spec.neg ctx.spec.one := by
                                  rw [ctx.certificate.orderedField.inv_mul_cancel _ hnx0]
                      _ = ctx.spec.mul (ctx.spec.neg (ctx.spec.inv x)) x := by
                          symm
                          have h :=
                            CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_mult_distr_l_reverse
                              ctx (Exact.Rinv ctx x) x
                          change ctx.spec.mul (ctx.spec.neg (ctx.spec.inv x)) x =
                            ctx.spec.neg (ctx.spec.mul (ctx.spec.inv x) x) at h
                          rw [h, ctx.certificate.orderedField.inv_mul_cancel _ hx0]

                  cases s with
                  | false => exact hposid
                  | true =>
                      change ctx.spec.mul (ctx.spec.ofZ (Zopp (Zpos m)))
                          (Exact.bpow ctx Zaux.radix2 e') =
                        ctx.spec.inv (ctx.spec.mul (ctx.spec.ofZ (Zopp (Zpos m)))
                          (Exact.bpow ctx Zaux.radix2 e))
                      rw [ctx.certificate.sourceLaws.ofZ_neg]
                      calc
                        Exact.Rmult ctx (Exact.Ropp ctx (Exact.IZR ctx (Zpos m)))
                            (Exact.bpow ctx Zaux.radix2 e') =
                            Exact.Ropp ctx (Exact.Rmult ctx (Exact.IZR ctx (Zpos m))
                              (Exact.bpow ctx Zaux.radix2 e')) :=
                              CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_mult_distr_l_reverse
                                ctx _ _
                        _ = Exact.Ropp ctx (Exact.Rinv ctx
                            (Exact.Rmult ctx (Exact.IZR ctx (Zpos m))
                              (Exact.bpow ctx Zaux.radix2 e))) := congrArg _ hposid
                        _ = Exact.Rinv ctx (Exact.Ropp ctx
                            (Exact.Rmult ctx (Exact.IZR ctx (Zpos m))
                              (Exact.bpow ctx Zaux.radix2 e))) :=
                              (hinv_neg _ hposnonzero).symm
                        _ = Exact.Rinv ctx (Exact.Rmult ctx
                            (Exact.Ropp ctx (Exact.IZR ctx (Zpos m)))
                            (Exact.bpow ctx Zaux.radix2 e)) := by
                              congr 1
                              exact (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_mult_distr_l_reverse
                                ctx (Exact.IZR ctx (Zpos m))
                                (Exact.bpow ctx Zaux.radix2 e)).symm
                · exact hnonzero
                · rfl
            | right hnmax => simp [Bexact_inverse, hm, e', hmin, hmax] at hresult
            | right hnmin => simp [Bexact_inverse, hm, e', hmin] at hresult
      · simp [Bexact_inverse, hm] at hresult

end CompCert4Lean.Lib.IEEE754_extra
-/
