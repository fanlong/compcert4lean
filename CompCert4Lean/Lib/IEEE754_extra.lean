import CompCert4Lean.Flocq.IEEE754.Binary
import CompCert4Lean.Flocq.Prop.Sterbenz

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
                      cases m <;> simp [Zpos, Z0] at hz
                  | true =>
                      change Zopp (Zpos m) ≠ Z0
                      intro hz
                      have hopp : ∀ z : Z,
                          _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zopp z) =
                            -_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z := by
                        intro z
                        change _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
                              (-_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z)) = _
                        rw [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
                      have hz' := congrArg
                        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hz
                      rw [hopp] at hz'
                      change -(_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m : Int) = 0 at hz'
                      have hmpos :=
                        _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive m
                      have hmpos' : (0 : Int) < (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m) := by
                        exact_mod_cast hmpos
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
                        change ctx.spec.mul (Exact.bpow ctx Zaux.radix2 (Zopp q))
                            (Exact.bpow ctx Zaux.radix2 q) =
                          ctx.spec.mul (Exact.Rinv ctx (Exact.bpow ctx Zaux.radix2 q))
                            (Exact.bpow ctx Zaux.radix2 q)
                        calc
                          ctx.spec.mul (Exact.bpow ctx Zaux.radix2 (Zopp q))
                              (Exact.bpow ctx Zaux.radix2 q) =
                              ctx.spec.mul (Exact.bpow ctx Zaux.radix2 q)
                                (Exact.bpow ctx Zaux.radix2 (Zopp q)) :=
                            ctx.certificate.orderedField.mul_comm _ _
                          _ = ctx.spec.mul (Exact.bpow ctx Zaux.radix2 q)
                              (Exact.Rinv ctx (Exact.bpow ctx Zaux.radix2 q)) :=
                            hmul_zero.trans hmul_inv.symm
                          _ = ctx.spec.mul (Exact.Rinv ctx (Exact.bpow ctx Zaux.radix2 q))
                              (Exact.bpow ctx Zaux.radix2 q) :=
                            ctx.certificate.orderedField.mul_comm _ _) hqne0
                  have hexp : Zadd (Zsub prec Zone) e' =
                      Zopp (Zadd (Zsub prec Zone) e) := by
                    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
                    dsimp [e']
                    simp only [Zadd, Zsub, Zopp, Zmul,
                      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
                      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
                      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
                      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
                      _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
                    have hzone : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by
                      decide
                    have htwo : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = (2 : Int) := by
                      decide
                    rw [hzone, htwo]
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
                    have hz'' : (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m : Int) = 0 := by
                      exact hz'
                    have hmpos' : (0 : Int) < (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m) := by
                      exact_mod_cast hmpos
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
                · constructor
                  · exact hnonzero
                  · rfl
            | right hnmax => simp [Bexact_inverse, hm, e', hmin, hmax] at hresult
        | right hnmin => simp [Bexact_inverse, hm, e', hmin] at hresult
      · simp [Bexact_inverse, hm] at hresult
end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Foundation.Numbers.Rocq.Coq (intOfZ intOfZ_injective intOfZ_zOfInt)

theorem integer_representable_2p :
    ∀ {prec emax : Z} [pgt : Prec_gt_0 prec]
      [ple : Prec_lt_emax prec emax],
      integer_representable_2pStatement (prec := prec) (emax := emax) := by
  intro prec emax pgt ple ctx magnitude p hp
  have hprec : 0 < intOfZ prec := pgt
  have hpe : intOfZ prec < intOfZ emax := ple.prec_lt_emax
  have hsub (x y : Z) : intOfZ (Zsub x y) = intOfZ x - intOfZ y := by
    simp [Zsub, Zaux.Zsub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub, intOfZ_zOfInt]
  have hadd (x y : Z) : intOfZ (Zadd x y) = intOfZ x + intOfZ y := by
    simp [Zadd, Zaux.Zadd,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add, intOfZ_zOfInt]
  have hone : intOfZ Zone = 1 := rfl
  have hp0 : 0 ≤ intOfZ p := hp.1
  constructor
  · have hpowp := Zaux.Zpower_le Zaux.radix2 p (Zsub emax Zone) hp.2
    have hdiff : Zle (Zsub emax prec) (Zsub emax Zone) := by
      change intOfZ (Zsub emax prec) ≤ intOfZ (Zsub emax Zone)
      rw [hsub, hsub, hone]
      omega
    have hpowdiff := Zaux.Zpower_le Zaux.radix2
      (Zsub emax prec) (Zsub emax Zone) hdiff
    have hnonneg : Zle Z0 (Zsub emax Zone) := by
      change 0 ≤ intOfZ (Zsub emax Zone)
      rw [hsub, hone]
      omega
    have hsum : Zadd (Zsub emax Zone) Zone = emax := by
      apply intOfZ_injective
      rw [hadd, hsub]
      omega
    have hdouble : Zpower Ztwo (Zadd (Zsub emax Zone) Zone) =
        Zmul (Zpower Ztwo (Zsub emax Zone)) (Zpower Ztwo Zone) :=
      Zaux.Zpower_plus Ztwo (Zsub emax Zone) Zone hnonneg
        (show (0 : Int) ≤ 1 by decide)
    rw [hsum] at hdouble
    have htwo : Zpower Ztwo Zone = Ztwo := by decide
    rw [htwo] at hdouble
    have habs : Zabs (Zpower Ztwo p) = Zpower Ztwo p :=
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs_eq
        (Zpower Ztwo p) (Zaux.Zpower_ge_0 Zaux.radix2 p)
    rw [habs]
    change intOfZ (Zpower Ztwo p) ≤
      intOfZ (Zsub (Zpower Ztwo emax) (Zpower Ztwo (Zsub emax prec)))
    rw [hsub, hdouble]
    change intOfZ (Zpower Ztwo p) ≤
      intOfZ (Zaux.Zmul (Zpower Ztwo (Zsub emax Zone)) Ztwo) - _
    simp only [Zaux.Zmul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    have htwoInt : intOfZ Ztwo = 2 := rfl
    rw [htwoInt]
    change intOfZ (Zpower Ztwo p) ≤ intOfZ (Zpower Ztwo (Zsub emax Zone)) at hpowp
    change intOfZ (Zpower Ztwo (Zsub emax prec)) ≤
      intOfZ (Zpower Ztwo (Zsub emax Zone)) at hpowdiff
    omega
  · change Generic_fmt.Exact.generic_format ctx magnitude Zaux.radix2
      (fexp prec emax) (Exact.IZR ctx (Zpower Ztwo p))
    have hizr : Exact.IZR ctx (Zpower Ztwo p) = Exact.bpow ctx Zaux.radix2 p :=
      Raux.IZR_Zpower ctx Zaux.radix2 p hp.1
    rw [hizr]
    apply Generic_fmt.generic_format_bpow ctx magnitude
    change intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max
      (Zsub (Zadd p Zone) prec) (Zsub (Zsub (Zpos (.xI .xH)) emax) prec)) ≤ intOfZ p
    have hthree : intOfZ (Zpos (.xI .xH)) = 3 := rfl
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max]
    split <;> simp only [hsub, hadd, hone, hthree] <;> omega

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core

theorem integer_representable_opp :
    ∀ {prec emax : Z},
      integer_representable_oppStatement (prec := prec) (emax := emax) := by
  intro prec emax ctx magnitude n hn
  constructor
  · change Zle (Zabs (Zopp n)) _
    have habs : Zabs (Zopp n) = Zabs n :=
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs_opp n
    rw [habs]
    exact hn.1
  · change Generic_fmt.Exact.generic_format ctx magnitude Zaux.radix2
      (fexp prec emax) (Exact.IZR ctx (Zopp n))
    have hizr : Exact.IZR ctx (Zopp n) = Exact.Ropp ctx (Exact.IZR ctx n) :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.opp_IZR ctx n
    rw [hizr]
    exact Generic_fmt.generic_format_opp ctx magnitude Zaux.radix2
      (fexp prec emax) (Exact.IZR ctx n) hn.2

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.Numbers.Rocq.Coq (intOfZ intOfZ_injective intOfZ_zOfInt)

theorem integer_representable_n2p_wide :
    ∀ {prec emax : Z} [pgt : Prec_gt_0 prec]
      [ple : Prec_lt_emax prec emax],
      integer_representable_n2p_wideStatement (prec := prec) (emax := emax) := by
  intro prec emax pgt ple ctx magnitude n p hn hp hpmax
  have hprec : 0 < intOfZ prec := pgt
  have hpe : intOfZ prec < intOfZ emax := ple.prec_lt_emax
  have hsub (a b : Z) : intOfZ (Zsub a b) = intOfZ a - intOfZ b := by
    simp [Zsub, Zaux.Zsub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub, intOfZ_zOfInt]
  have hadd (a b : Z) : intOfZ (Zadd a b) = intOfZ a + intOfZ b := by
    simp [Zadd, Zaux.Zadd,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add, intOfZ_zOfInt]
  have hmul (a b : Z) : intOfZ (Zmul a b) = intOfZ a * intOfZ b := by
    simp [Zmul, Zaux.Zmul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul, intOfZ_zOfInt]
  have hopp (a : Z) : intOfZ (Zopp a) = -intOfZ a := by
    simp [Zopp, Zaux.Zopp,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp, intOfZ_zOfInt]
  have habseq (a : Z) (ha : Zle Z0 a) : Zabs a = a :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs_eq a ha
  have habsneg (a : Z) (ha : Zle a Z0) : Zabs a = Zopp a :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs_neq a ha
  have habsmul (a b : Z) : Zabs (Zmul a b) = Zmul (Zabs a) (Zabs b) :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs_mul a b
  have hoppmul (a b : Z) : Zopp (Zmul a b) = Zmul (Zopp a) b :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Zopp_mult_distr_l a b
  have hp0 : 0 ≤ intOfZ p := hp
  have hpmax' : intOfZ p < intOfZ emax - intOfZ prec := by
    change intOfZ p < intOfZ (Zsub emax prec) at hpmax
    simpa only [hsub] using hpmax
  have hpbound : Zle Z0 (Zadd prec p) ∧ Zle (Zadd prec p) (Zsub emax Zone) := by
    change (0 ≤ intOfZ (Zadd prec p)) ∧
      (intOfZ (Zadd prec p) ≤ intOfZ (Zsub emax Zone))
    rw [hadd, hsub]
    have hone : intOfZ Zone = 1 := rfl
    rw [hone]
    omega
  have hpow := Zaux.Zpower_plus Ztwo prec p
    (show Zle Z0 prec from Int.le_of_lt hprec) hp
  have hrepr := integer_representable_2p (prec := prec) (emax := emax)
    ctx magnitude (Zadd prec p) hpbound
  change Zpower Ztwo (Zadd prec p) = Zmul (Zpower Ztwo prec) (Zpower Ztwo p) at hpow
  have hreprMul : integer_representable (prec := prec) (emax := emax) ctx magnitude
      (Zmul (Zpower Ztwo prec) (Zpower Ztwo p)) := hpow ▸ hrepr
  by_cases hnpos : n = Zpower Ztwo prec
  · simpa only [hnpos] using hreprMul
  by_cases hnneg : n = Zopp (Zpower Ztwo prec)
  · rw [hnneg, ← hoppmul]
    exact integer_representable_opp (prec := prec) (emax := emax)
      ctx magnitude _ hreprMul
  have hnlo : -intOfZ (Zpower Ztwo prec) < intOfZ n := by
    have h := hn.1
    change intOfZ (Zopp (Zpower Ztwo prec)) ≤ intOfZ n at h
    rw [hopp] at h
    have hne : intOfZ n ≠ -intOfZ (Zpower Ztwo prec) := by
      intro heq
      apply hnneg
      apply intOfZ_injective
      rw [hopp]
      exact heq
    omega
  have hnhi : intOfZ n < intOfZ (Zpower Ztwo prec) := by
    have h : intOfZ n ≤ intOfZ (Zpower Ztwo prec) := hn.2
    have hne : intOfZ n ≠ intOfZ (Zpower Ztwo prec) := by
      intro heq
      exact hnpos (intOfZ_injective heq)
    omega
  have habslt : intOfZ (Zabs n) < intOfZ (Zpower Ztwo prec) := by
    by_cases hsign : 0 ≤ intOfZ n
    · rw [habseq n hsign]
      exact hnhi
    · rw [habsneg n
        (show intOfZ n ≤ 0 by omega), hopp]
      omega
  have hppos : Zle Z0 (Zpower Ztwo p) := Zaux.Zpower_ge_0 Zaux.radix2 p
  have hpcpos : Zle Z0 (Zpower Ztwo prec) := Zaux.Zpower_ge_0 Zaux.radix2 prec
  constructor
  · have hbound := hreprMul.1
    rw [habsmul,
      habseq _ hpcpos,
      habseq _ hppos] at hbound
    rw [habsmul,
      habseq _ hppos]
    change intOfZ (Zmul (Zabs n) (Zpower Ztwo p)) ≤ _
    rw [hmul]
    apply Int.le_trans (Int.mul_le_mul_of_nonneg_right (Int.le_of_lt habslt) hppos)
    change intOfZ (Zmul (Zpower Ztwo prec) (Zpower Ztwo p)) ≤ _ at hbound
    simpa only [hmul] using hbound
  · change Generic_fmt.Exact.generic_format ctx magnitude Zaux.radix2
      (FLT.FLT_exp (emin prec emax) prec) (Exact.IZR ctx (Zmul n (Zpower Ztwo p)))
    apply FLT.generic_format_FLT ctx magnitude
    apply FLT.FLT_spec _ _ _ _ (Defs.Float Zaux.radix2 n p)
    · change Exact.IZR ctx (Zmul n (Zpower Ztwo p)) =
        Exact.Rmult ctx (Exact.IZR ctx n) (Exact.bpow ctx Zaux.radix2 p)
      have hizr : Exact.IZR ctx (Zpower Ztwo p) = Exact.bpow ctx Zaux.radix2 p :=
        Raux.IZR_Zpower ctx Zaux.radix2 p hp
      rw [← hizr]
      exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR ctx n _
    · exact habslt
    · change intOfZ (Zsub (Zsub (Zpos (.xI .xH)) emax) prec) ≤ intOfZ p
      rw [hsub, hsub]
      have hthree : intOfZ (Zpos (.xI .xH)) = 3 := rfl
      rw [hthree]
      omega

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.Numbers.Rocq.Coq (intOfZ intOfZ_injective intOfZ_zOfInt)

private theorem integer_representable_n_zpower_zero :
    Zpower Ztwo Z0 = Zone := by
  apply intOfZ_injective
  unfold Zpower
  have hcond : ¬ intOfZ (Z0 : Z) < 0 := by simp [intOfZ]
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow, hcond,
    ↓reduceIte]
  rw [intOfZ_zOfInt]
  change (intOfZ Ztwo) ^ (0 : Nat) = intOfZ Zone
  decide

private theorem integer_representable_n_mul_zpower_zero (n : Z) :
    Zmul n (Zpower Ztwo Z0) = n := by
  rw [integer_representable_n_zpower_zero]
  apply intOfZ_injective
  simp [Zmul, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
    intOfZ_zOfInt]
  have hone : intOfZ Zone = 1 := by decide
  rw [hone]
  omega

theorem integer_representable_n :
    ∀ {prec emax : Z} [pgt : Prec_gt_0 prec]
      [ple : Prec_lt_emax prec emax],
      integer_representable_nStatement (prec := prec) (emax := emax) := by
  intro prec emax pgt ple ctx magnitude n hn
  have hprec : 0 < intOfZ prec := pgt
  have hpe : intOfZ prec < intOfZ emax := ple.prec_lt_emax
  have hpzero : Zle Z0 Z0 := by
    change (0 : Int) ≤ 0
    omega
  have hpstrict : Zlt Z0 (Zsub emax prec) := by
    change (0 : Int) < intOfZ (Zsub emax prec)
    simp [Zsub, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      intOfZ_zOfInt]
    omega
  have h := integer_representable_n2p_wide (prec := prec) (emax := emax)
    ctx magnitude n Z0 hn hpzero hpstrict
  rw [integer_representable_n_mul_zpower_zero] at h
  exact h

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra
open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Foundation.Numbers.Rocq.Coq (intOfZ intOfZ_injective intOfZ_zOfInt)

theorem round_int_no_overflow :
    ∀ {prec emax : Z} [pgt : Prec_gt_0 prec]
      [ple : Prec_lt_emax prec emax],
      round_int_no_overflowStatement (prec := prec) (emax := emax) := by
  intro prec emax pgt ple ctx magnitude n hn
  have hvalid : Generic_fmt.Valid_exp (fexp prec emax) := by
    let hcert : Binary.FexpCorrectCertificate prec emax :=
      Binary.fexp_correct_certificate_proof prec emax
    exact hcert.valid
  have hbound : Zle (Zabs n)
      (Zsub (Zpower Ztwo emax) (Zpower Ztwo (Zsub emax prec))) := hn
  have hyfmt : Exact.generic_format magnitude Zaux.radix2 (fexp prec emax)
      (Exact.IZR ctx (Zsub (Zpower Ztwo emax) (Zpower Ztwo (Zsub emax prec)))) := by
    apply FLT.generic_format_FLT ctx magnitude
    apply FLT.FLT_spec _ _ _ _
      (Defs.Float Zaux.radix2
        (Zsub (Zpower Ztwo prec) Zone) (Zsub emax prec))
    · rw [int_upper_bound_eq (prec := prec) (emax := emax)]
      change Exact.IZR ctx
          (Zmul (Zsub (Zpower Ztwo prec) Zone)
            (Zpower Ztwo (Zsub emax prec))) =
        Exact.Rmult ctx (Exact.IZR ctx (Zsub (Zpower Ztwo prec) Zone))
          (Exact.bpow ctx Zaux.radix2 (Zsub emax prec))
      have hp : Zle Z0 (Zsub emax prec) := by
        change (0 : Int) ≤ intOfZ (Zsub emax prec)
        simp [Zsub, Zaux.Zsub, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          intOfZ_zOfInt]
        have hpe : intOfZ prec < intOfZ emax := ple.prec_lt_emax
        omega
      have hizr : Exact.IZR ctx (Zpower Ztwo (Zsub emax prec)) =
          Exact.bpow ctx Zaux.radix2 (Zsub emax prec) :=
        Raux.IZR_Zpower ctx Zaux.radix2 (Zsub emax prec) hp
      rw [← hizr]
      exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR ctx _ _
    · change Zlt
        (Zabs (Zsub (Zpower Ztwo prec) Zone))
        (Zpower Ztwo prec)
      have hpow : Zlt Zone (Zpower Ztwo prec) :=
        Zaux.Zpower_gt_1 Zaux.radix2 prec (show Zlt Z0 prec from pgt)
      have hm : Zle Z0 (Zsub (Zpower Ztwo prec) Zone) := by
        change (0 : Int) ≤ intOfZ (Zsub (Zpower Ztwo prec) Zone)
        simp [Zsub, Zaux.Zsub, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          intOfZ_zOfInt]
        have hpI : (1 : Int) < intOfZ (Zpower Ztwo prec) := hpow
        have hone : intOfZ Zone = (1 : Int) := by decide
        omega
      have habs : Zabs (Zsub (Zpower Ztwo prec) Zone) =
          Zsub (Zpower Ztwo prec) Zone :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs_eq _ hm
      rw [habs]
      change intOfZ (Zsub (Zpower Ztwo prec) Zone) <
        intOfZ (Zpower Ztwo prec)
      simp [Zsub, Zaux.Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      have hpI : (1 : Int) < intOfZ (Zpower Ztwo prec) := hpow
      have hone : intOfZ Zone = (1 : Int) := by decide
      omega
    · change intOfZ (Zsub (Zsub (Zpos (.xI .xH)) emax) prec) ≤
        intOfZ (Zsub emax prec)
      simp [Zsub, Zaux.Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      have hprec : (0 : Int) < intOfZ prec := pgt
      have hpe : intOfZ prec < intOfZ emax := ple.prec_lt_emax
      have hthree : intOfZ (Zpos (.xI .xH)) = (3 : Int) := by decide
      omega
  have hxy : Exact.Rle ctx (Exact.Rabs ctx (Exact.IZR ctx n))
      (Exact.IZR ctx (Zsub (Zpower Ztwo emax) (Zpower Ztwo (Zsub emax prec)))) := by
    have habs : Exact.IZR ctx (Zabs n) = Exact.Rabs ctx (Exact.IZR ctx n) := by
      exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rbasic_fun.abs_IZR ctx n
    rw [← habs]
    exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_le
      ctx _ _ hbound
  have hle : Exact.Rle ctx
      (Exact.round magnitude Zaux.radix2 (fexp prec emax)
        (Exact.round_mode ctx mode_NE) (Exact.Rabs ctx (Exact.IZR ctx n)))
      (Exact.IZR ctx (Zsub (Zpower Ztwo emax) (Zpower Ztwo (Zsub emax prec)))) := by
    change Exact.Rle ctx
      (Generic_fmt.Exact.round ctx magnitude Zaux.radix2 (fexp prec emax)
        (Generic_fmt.Exact.Znearest ctx (fun m => Bool.not (Zaux.Zeven m)))
        (Exact.Rabs ctx (Exact.IZR ctx n)))
      (Exact.IZR ctx (Zsub (Zpower Ztwo emax) (Zpower Ztwo (Zsub emax prec))))
    let sm := Generic_fmt.Exact.scaled_mantissa ctx magnitude Zaux.radix2
      (fexp prec emax) (Exact.Rabs ctx (Exact.IZR ctx n))
    rcases Generic_fmt.Znearest_DN_or_UP ctx (fun m => Bool.not (Zaux.Zeven m)) sm with hfloor | hceil
    · rw [show Generic_fmt.Exact.round ctx magnitude Zaux.radix2 (fexp prec emax)
          (Generic_fmt.Exact.Znearest ctx (fun m => Bool.not (Zaux.Zeven m)))
          (Exact.Rabs ctx (Exact.IZR ctx n)) =
        Generic_fmt.Exact.round ctx magnitude Zaux.radix2 (fexp prec emax)
          (Generic_fmt.Exact.Zfloor ctx) (Exact.Rabs ctx (Exact.IZR ctx n)) by
          unfold sm at hfloor
          unfold Generic_fmt.Exact.round
          rw [hfloor]]
      let hrnd : Generic_fmt.Exact.Valid_rnd ctx (Generic_fmt.Exact.Zfloor ctx) := by
        constructor
        · intro x y hxy'
          exact CompCert4Lean.Flocq.Core.Raux.Zfloor_le ctx x y hxy'
        · intro z
          exact CompCert4Lean.Flocq.Core.Raux.Zfloor_IZR ctx z
      exact Generic_fmt.round_le_generic ctx magnitude Zaux.radix2 (fexp prec emax)
        hvalid (Generic_fmt.Exact.Zfloor ctx) hrnd _ _ hyfmt hxy
    · rw [show Generic_fmt.Exact.round ctx magnitude Zaux.radix2 (fexp prec emax)
          (Generic_fmt.Exact.Znearest ctx (fun m => Bool.not (Zaux.Zeven m)))
          (Exact.Rabs ctx (Exact.IZR ctx n)) =
        Generic_fmt.Exact.round ctx magnitude Zaux.radix2 (fexp prec emax)
          (Generic_fmt.Exact.Zceil ctx) (Exact.Rabs ctx (Exact.IZR ctx n)) by
          unfold sm at hceil
          unfold Generic_fmt.Exact.round
          rw [hceil]]
      let hrnd : Generic_fmt.Exact.Valid_rnd ctx (Generic_fmt.Exact.Zceil ctx) := by
        constructor
        · intro x y hxy'
          exact CompCert4Lean.Flocq.Core.Raux.Zceil_le ctx x y hxy'
        · intro z
          exact CompCert4Lean.Flocq.Core.Raux.Zceil_IZR ctx z
      exact Generic_fmt.round_le_generic ctx magnitude Zaux.radix2 (fexp prec emax)
        hvalid (Generic_fmt.Exact.Zceil ctx) hrnd _ _ hyfmt hxy
  have hlt : Exact.Rlt ctx
      (Exact.IZR ctx (Zsub (Zpower Ztwo emax) (Zpower Ztwo (Zsub emax prec))))
      (Exact.bpow ctx Zaux.radix2 emax) := by
    have hp0 : Zle Z0 (Zsub emax prec) := by
      change (0 : Int) ≤ intOfZ (Zsub emax prec)
      simp [Zsub, Zaux.Zsub, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        intOfZ_zOfInt]
      have hprec : (0 : Int) < intOfZ prec := pgt
      have hpe : intOfZ prec < intOfZ emax := ple.prec_lt_emax
      omega
    have hp : Zlt Z0 (Zpower Ztwo (Zsub emax prec)) :=
      Zaux.Zpower_gt_0 Zaux.radix2 _ hp0
    have hsub : Zlt
        (Zsub (Zpower Ztwo emax) (Zpower Ztwo (Zsub emax prec)))
        (Zpower Ztwo emax) := by
      change intOfZ (Zsub (Zpower Ztwo emax) (Zpower Ztwo (Zsub emax prec))) <
        intOfZ (Zpower Ztwo emax)
      simp [Zsub, Zaux.Zsub, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        intOfZ_zOfInt]
      have hpI : (0 : Int) < intOfZ (Zpower Ztwo (Zsub emax prec)) := hp
      simp [Zsub, Zaux.Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        intOfZ_zOfInt] at hpI ⊢
      omega
    have he0 : Zle Z0 emax := by
      change (0 : Int) ≤ intOfZ emax
      have hprec : (0 : Int) < intOfZ prec := pgt
      have hpe : intOfZ prec < intOfZ emax := ple.prec_lt_emax
      omega
    have hizr : Exact.IZR ctx (Zpower Ztwo emax) =
        Exact.bpow ctx Zaux.radix2 emax :=
      Raux.IZR_Zpower ctx Zaux.radix2 emax he0
    rw [← hizr]
    exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt ctx _ _ hsub
  change Exact.Rlt ctx
    (Generic_fmt.Exact.Rabs ctx
      (Generic_fmt.Exact.round ctx magnitude Zaux.radix2 (fexp prec emax)
        (Generic_fmt.Exact.Znearest ctx (fun m => Bool.not (Zaux.Zeven m)))
        (Exact.IZR ctx n)))
    (Exact.bpow ctx Zaux.radix2 emax)
  have habsround := CompCert4Lean.Flocq.Core.Round_NE.round_NE_abs ctx magnitude
    Zaux.radix2 (fexp prec emax) hvalid (Exact.IZR ctx n)
  change Generic_fmt.Exact.round ctx magnitude Zaux.radix2 (fexp prec emax)
      (Generic_fmt.Exact.Znearest ctx (fun m => Bool.not (Zaux.Zeven m)))
      (Exact.Rabs ctx (Exact.IZR ctx n)) =
    Generic_fmt.Exact.Rabs ctx
      (Generic_fmt.Exact.round ctx magnitude Zaux.radix2 (fexp prec emax)
        (Generic_fmt.Exact.Znearest ctx (fun m => Bool.not (Zaux.Zeven m)))
        (Exact.IZR ctx n)) at habsround
  rw [← habsround]
  exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
    ctx _ _ _ hle hlt
end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Foundation.Numbers.Rocq.Coq (intOfZ intOfZ_injective intOfZ_zOfInt)

private theorem bofz_repr_round_fixed (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) (prec emax : Z) (x : Exact.R ctx)
    (hx : Exact.generic_format magnitude Zaux.radix2 (fexp prec emax) x) :
    Exact.round magnitude Zaux.radix2 (fexp prec emax)
      (Exact.round_mode ctx mode_NE) x = x := by
  change Generic_fmt.Exact.round ctx magnitude Zaux.radix2 (fexp prec emax)
    (Generic_fmt.Exact.Znearest ctx (fun m => Bool.not (Zaux.Zeven m))) x = x
  unfold Generic_fmt.Exact.round
  rw [Generic_fmt.scaled_mantissa_generic ctx magnitude Zaux.radix2
    (fexp prec emax) x hx]
  have hz : ∀ n : Z, Generic_fmt.Exact.Znearest ctx
      (fun m => Bool.not (Zaux.Zeven m)) (Generic_fmt.Exact.IZR ctx n) = n := by
    intro n
    rcases Generic_fmt.Znearest_DN_or_UP ctx (fun m => Bool.not (Zaux.Zeven m))
      (Exact.IZR ctx n) with h | h
    · exact h.trans (Raux.Zfloor_IZR ctx n)
    · exact h.trans (Raux.Zceil_IZR ctx n)
  rw [hz]
  exact hx.symm

private theorem bofz_repr_shr_exponent (mrs : BinarySingleNaN.shr_record)
    (e t : Z) (h : Zle e t) :
    (BinarySingleNaN.shr mrs e (Zsub t e)).2 = t := by
  have hi : intOfZ e ≤ intOfZ t := h
  cases hn : Zsub t e with
  | Z0 =>
    change e = t
    apply intOfZ_injective
    have hh := congrArg intOfZ hn
    simp only [Zsub, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      intOfZ_zOfInt] at hh
    change intOfZ t - intOfZ e = 0 at hh
    omega
  | Zpos p =>
    change Zadd e (Zpos p) = t
    have hh := congrArg intOfZ hn
    apply intOfZ_injective
    simp only [Zadd, Zsub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hh ⊢
    change intOfZ t - intOfZ e = intOfZ (Zpos p) at hh
    omega
  | Zneg p =>
    have hh := congrArg intOfZ hn
    simp only [Zsub, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      intOfZ_zOfInt] at hh
    change intOfZ t - intOfZ e =
      -Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hh
    have hp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
    simp only [Int.ofNat_eq_natCast] at hh
    omega


private theorem bofz_repr_shift_exact (ctx : ExactRealContext)
    (magnitude : Exact.Magnitude ctx) (prec emax : Z) (m : positive) (e : Z)
    (he : Zle e (fexp prec emax (Zadd (Digits.Zdigits Zaux.radix2 (Zpos m)) e)))
    (hx : Exact.generic_format magnitude Zaux.radix2 (fexp prec emax)
      (Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos m) e))) :
    ∃ (p : positive) (er : Z),
      BinarySingleNaN.shr_fexp (prec := prec) (emax := emax)
        (Zpos m) e BinarySingleNaN.loc_Exact =
          (BinarySingleNaN.shr_record_of_loc (Zpos p) BinarySingleNaN.loc_Exact, er) ∧
      Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos p) er) =
        Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos m) e) ∧
      Generic_fmt.Exact.canonical ctx magnitude Zaux.radix2 (fexp prec emax)
        (Defs.Float Zaux.radix2 (Zpos p) er) := by
  let x := Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos m) e)
  let t := fexp prec emax (Zadd (Digits.Zdigits Zaux.radix2 (Zpos m)) e)
  have hm0 : Zlt Z0 (Zpos m) := by
    change (0 : Int) < Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m)
    exact Int.natCast_pos.mpr (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive m)
  have hxpos : Exact.Rlt ctx (Exact.R0 ctx) x :=
    Float_prop.F2R_gt_0 ctx Zaux.radix2 (Defs.Float Zaux.radix2 (Zpos m) e) hm0
  have hce : Generic_fmt.Exact.cexp ctx magnitude Zaux.radix2 (fexp prec emax) x = t := by
    change fexp prec emax (Float_prop.Exact.mag magnitude Zaux.radix2 x) = t
    rw [Float_prop.mag_F2R_Zdigits ctx magnitude Zaux.radix2 (Zpos m) e (by intro h; cases h)]
  have hsdef : BinarySingleNaN.shr_fexp (prec := prec) (emax := emax)
      (Zpos m) e BinarySingleNaN.loc_Exact =
      BinarySingleNaN.shr (BinarySingleNaN.shr_record_of_loc (Zpos m)
        BinarySingleNaN.loc_Exact) e (Zsub t e) := by
    change CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shr
      (BinarySingleNaN.shr_record_of_loc (Zpos m) BinarySingleNaN.loc_Exact) e
      (Zsub (fexp prec emax (Zadd (Zpos (Digits.digits2_pos m)) e)) e) = _
    have hd := Digits.Zpos_digits2_pos m
    change Zpos (Digits.digits2_pos m) = Digits.Zdigits Zaux.radix2 (Zpos m) at hd
    rw [hd]
  generalize hs : BinarySingleNaN.shr_fexp
    (prec := prec) (emax := emax) (Zpos m) e BinarySingleNaN.loc_Exact = pair
  rcases pair with ⟨sr, er⟩
  have her : er = t := by
    have h := bofz_repr_shr_exponent
      (BinarySingleNaN.shr_record_of_loc (Zpos m) BinarySingleNaN.loc_Exact) e t he
    rw [← hsdef, hs] at h
    exact h
  have hb := BinarySingleNaN.inbetween_shr ctx x (Zpos m) e
    BinarySingleNaN.loc_Exact (Zsub t e) (show Zle Z0 (Zpos m) from Int.le_of_lt hm0)
    (CompCert4Lean.Flocq.Calc.Bracket.inbetween_Exact rfl)
  change CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx Zaux.radix2
    (BinarySingleNaN.shr_m (BinarySingleNaN.shr
      (BinarySingleNaN.shr_record_of_loc (Zpos m) BinarySingleNaN.loc_Exact) e (Zsub t e)).1)
    (BinarySingleNaN.shr
      (BinarySingleNaN.shr_record_of_loc (Zpos m) BinarySingleNaN.loc_Exact) e (Zsub t e)).2
    x (BinarySingleNaN.loc_of_shr_record (BinarySingleNaN.shr
      (BinarySingleNaN.shr_record_of_loc (Zpos m) BinarySingleNaN.loc_Exact) e (Zsub t e)).1) at hb
  rw [← hsdef, hs] at hb
  dsimp only at hb
  rw [her] at hb
  have hfmt := hx
  change x = Generic_fmt.Exact.F2R ctx
    (Generic_fmt.Float Zaux.radix2
      (Generic_fmt.Exact.Ztrunc ctx
        (Generic_fmt.Exact.scaled_mantissa ctx magnitude Zaux.radix2 (fexp prec emax) x))
      (Generic_fmt.Exact.cexp ctx magnitude Zaux.radix2 (fexp prec emax) x)) at hfmt
  rw [hce] at hfmt
  have hu := CompCert4Lean.Flocq.Calc.Bracket.inbetween_float_unique ctx Zaux.radix2 x t
    (BinarySingleNaN.shr_m sr) (BinarySingleNaN.loc_of_shr_record sr)
    (Generic_fmt.Exact.Ztrunc ctx
      (Generic_fmt.Exact.scaled_mantissa ctx magnitude Zaux.radix2 (fexp prec emax) x))
    BinarySingleNaN.loc_Exact hb
    (CompCert4Lean.Flocq.Calc.Bracket.inbetween_Exact hfmt)
  have hval : Defs.Exact.F2R ctx
      (Defs.Float Zaux.radix2 (BinarySingleNaN.shr_m sr) er) = x := by
    rw [her, hu.1]
    exact hfmt.symm
  have hp0 : Zlt Z0 (BinarySingleNaN.shr_m sr) :=
    Float_prop.gt_0_F2R ctx Zaux.radix2 (BinarySingleNaN.shr_m sr) er
      (by
        change Exact.Rlt ctx (Exact.R0 ctx)
          (Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (BinarySingleNaN.shr_m sr) er))
        rw [hval]
        exact hxpos)
  have hpos : ∃ p : positive, BinarySingleNaN.shr_m sr = Zpos p := by
    cases hm : BinarySingleNaN.shr_m sr with
    | Z0 => rw [hm] at hp0; exact False.elim ((Int.lt_irrefl 0) hp0)
    | Zpos p => exact ⟨p, rfl⟩
    | Zneg p =>
      rw [hm] at hp0
      change (0 : Int) < -Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hp0
      have hnonneg := Int.ofNat_zero_le (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
      simp only [Int.ofNat_eq_natCast] at hp0
      omega
  obtain ⟨p, hp⟩ := hpos
  have hrec : sr = BinarySingleNaN.shr_record_of_loc
      (BinarySingleNaN.shr_m sr) BinarySingleNaN.loc_Exact := by
    have hl := hu.2
    rcases sr with ⟨m, r, s⟩
    cases r <;> cases s <;> cases hl <;> rfl
  refine ⟨p, er, ?_, ?_, ?_⟩
  · rw [hp] at hrec
    rw [hrec]
  · rw [hp] at hval
    exact hval
  · change er = Generic_fmt.Exact.cexp ctx magnitude Zaux.radix2 (fexp prec emax)
      (Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos p) er))
    rw [hp] at hval
    rw [hval, hce]
    exact her


private theorem bofz_repr_round_aux_exact {prec emax : Z}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (sx : Bool) (m : positive) (e : Z)
    (he : Zle e (fexp prec emax (Zadd (Digits.Zdigits Zaux.radix2 (Zpos m)) e)))
    (hx : Exact.generic_format magnitude Zaux.radix2 (fexp prec emax)
      (Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos m) e)))
    (hlt : Exact.Rlt ctx
      (Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos m) e))
      (Exact.bpow ctx Zaux.radix2 emax)) :
    ∃ (p : positive) (er : Z),
      BinarySingleNaN.binary_round_aux (prec := prec) (emax := emax)
        mode_NE sx (Zpos m) e BinarySingleNaN.loc_Exact =
          BinarySingleNaN.S754_finite sx p er ∧
      Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos p) er) =
        Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos m) e) := by
  obtain ⟨p, er, hs, hv, hc⟩ := bofz_repr_shift_exact ctx magnitude prec emax m e he hx
  have hb := BinarySingleNaN.bounded_canonical_lt_emax ctx magnitude p er hc
    (show Exact.Rlt ctx (Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos p) er))
      (Exact.bpow ctx Zaux.radix2 emax) from hv ▸ hlt)
  have hb' : BinarySingleNaN.canonical_mantissa (prec := prec) (emax := emax) p er = true ∧
      Zle_bool er (Zsub emax prec) = true := Bool.and_eq_true_iff.mp hb
  have hcan : fexp prec emax (Zadd (Zpos (Digits.digits2_pos p)) er) = er :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool_eq _ _ hb'.1
  have hs2 : BinarySingleNaN.shr_fexp (prec := prec) (emax := emax)
      (Zpos p) er BinarySingleNaN.loc_Exact =
        (BinarySingleNaN.shr_record_of_loc (Zpos p) BinarySingleNaN.loc_Exact, er) := by
    change BinarySingleNaN.shr
      (BinarySingleNaN.shr_record_of_loc (Zpos p) BinarySingleNaN.loc_Exact) er
      (Zsub (fexp prec emax (Zadd (Zpos (Digits.digits2_pos p)) er)) er) = _
    have hz : Zsub er er = Z0 := by
      apply intOfZ_injective
      change intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (intOfZ er - intOfZ er)) = 0
      rw [intOfZ_zOfInt]
      omega
    rw [hcan, hz]
    rfl
  refine ⟨p, er, ?_, hv⟩
  unfold BinarySingleNaN.binary_round_aux
  rw [hs]
  change (match BinarySingleNaN.shr_m
      (BinarySingleNaN.shr_fexp (prec := prec) (emax := emax)
        (Zpos p) er BinarySingleNaN.loc_Exact).1 with
    | .Z0 => BinarySingleNaN.S754_zero sx
    | .Zpos q => BinarySingleNaN.binary_fit_aux (prec := prec) (emax := emax)
        mode_NE sx q (BinarySingleNaN.shr_fexp (prec := prec) (emax := emax)
          (Zpos p) er BinarySingleNaN.loc_Exact).2
    | .Zneg _ => BinarySingleNaN.S754_nan) = _
  rw [hs2]
  change BinarySingleNaN.binary_fit_aux (prec := prec) (emax := emax) mode_NE sx p er = _
  unfold BinarySingleNaN.binary_fit_aux
  rw [show BinarySingleNaN.Zle_bool er (BinarySingleNaN.Zsub emax prec) = true from hb'.2]
  rfl

private theorem bofz_repr_binary_round_exact {prec emax : Z}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (sx : Bool) (m : positive) (e : Z)
    (hx : Exact.generic_format magnitude Zaux.radix2 (fexp prec emax)
      (Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos m) e)))
    (hlt : Exact.Rlt ctx
      (Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos m) e))
      (Exact.bpow ctx Zaux.radix2 emax)) :
    ∃ (p : positive) (er : Z),
      BinarySingleNaN.binary_round (prec := prec) (emax := emax) mode_NE sx m e =
          BinarySingleNaN.S754_finite sx p er ∧
      Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos p) er) =
        Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos m) e) := by
  have ha := BinarySingleNaN.shl_align_fexp_correct (prec := prec) (emax := emax) ctx m e
  generalize hs : BinarySingleNaN.shl_align_fexp (prec := prec) (emax := emax) m e = pair
  rcases pair with ⟨ma, ea⟩
  rw [hs] at ha
  dsimp only at ha
  have hv : Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos m) e) =
      Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos ma) ea) := ha.1
  obtain ⟨p, er, hr, hv'⟩ := bofz_repr_round_aux_exact ctx magnitude sx ma ea ha.2
    (hv ▸ hx) (hv ▸ hlt)
  refine ⟨p, er, ?_, hv'.trans hv.symm⟩
  unfold BinarySingleNaN.binary_round
  rw [hs]
  exact hr


private theorem bofz_repr_positive_round {prec emax : Z}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (sx : Bool) (m : positive)
    (hx : integer_representable (prec := prec) (emax := emax) ctx magnitude (Zpos m)) :
    ∃ (p : positive) (er : Z),
      BinarySingleNaN.binary_round (prec := prec) (emax := emax) mode_NE sx m Z0 =
        BinarySingleNaN.S754_finite sx p er ∧
      Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos p) er) = Exact.IZR ctx (Zpos m) := by
  have hf : Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos m) Z0) =
      Exact.IZR ctx (Zpos m) := ctx.certificate.orderedField.mul_one _
  have hround := bofz_repr_round_fixed ctx magnitude prec emax (Exact.IZR ctx (Zpos m)) hx.2
  have hlt := round_int_no_overflow (prec := prec) (emax := emax) ctx magnitude (Zpos m) hx.1
  change Exact.Rlt ctx
    (Exact.Rabs ctx (Exact.round magnitude Zaux.radix2 (fexp prec emax)
      (Exact.round_mode ctx mode_NE) (Exact.IZR ctx (Zpos m))))
    (Exact.bpow ctx Zaux.radix2 emax) at hlt
  rw [hround] at hlt
  have habs : Exact.IZR ctx (Zpos m) = Exact.Rabs ctx (Exact.IZR ctx (Zpos m)) := by
    have h := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.Rbasic_fun.abs_IZR ctx (Zpos m)
    have hm : Zle Z0 (Zpos m) := Int.natCast_nonneg _
    have hz : Zabs (Zpos m) = Zpos m :=
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs_eq _ hm
    change Exact.IZR ctx (Zabs (Zpos m)) = Exact.Rabs ctx (Exact.IZR ctx (Zpos m)) at h
    rw [hz] at h
    exact h
  rw [← habs] at hlt
  obtain ⟨p, er, hr, hv⟩ := bofz_repr_binary_round_exact ctx magnitude sx m Z0
    (hf.symm ▸ hx.2) (hf.symm ▸ hlt)
  exact ⟨p, er, hr, hv.trans hf⟩

private theorem bofz_repr_lift_finite {prec emax : Z}
    (x : BinarySingleNaN.binary_float prec emax) (h : BinarySingleNaN.is_nan x = false)
    (s : Bool) (p : positive) (e : Z) (hx : x = BinarySingleNaN.B754_finite s p e) :
    Binary.BSN2B' x h = Binary.B754_finite s p e := by
  cases hx
  rfl

theorem BofZ_representable :
    ∀ {prec emax : Z} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
      [Binary.BinaryNormalizeCertificate prec emax],
      BofZ_representableStatement (prec := prec) (emax := emax) := by
  intro prec emax pgt ple cert ctx magnitude n hn
  cases n with
  | Z0 =>
    refine ⟨?_, rfl, rfl⟩
    exact ctx.certificate.sourceLaws.ofZ_zero.symm
  | Zpos m =>
    obtain ⟨p, er, hr, hv⟩ := bofz_repr_positive_round ctx magnitude false m hn
    have hb : BofZ (prec := prec) (emax := emax) (Zpos m) =
        Binary.B754_finite false p er := by
      apply bofz_repr_lift_finite
      change BinarySingleNaN.SF2B (prec := prec) (emax := emax)
        (BinarySingleNaN.binary_round (prec := prec) (emax := emax) mode_NE false m Z0) = _
      rw [hr]
      rfl
    change Exact.B2R ctx (BofZ (prec := prec) (emax := emax) (Zpos m)) =
      Exact.IZR ctx (Zpos m) ∧
      Binary.is_finite (BofZ (prec := prec) (emax := emax) (Zpos m)) = true ∧
      Binary.Bsign (BofZ (prec := prec) (emax := emax) (Zpos m)) = Zlt_bool (Zpos m) Z0
    rw [hb]
    refine ⟨hv, rfl, ?_⟩
    change false = (if Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m) < 0
      then true else false)
    simp
  | Zneg m =>
    have hop : Zopp (Zneg m) = Zpos m := by
      apply intOfZ_injective
      simp only [Zopp, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
        intOfZ_zOfInt]
      change -(-Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m)) =
        Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m)
      omega
    have hn' : integer_representable (prec := prec) (emax := emax) ctx magnitude (Zpos m) := by
      have h := integer_representable_opp (prec := prec) (emax := emax) ctx magnitude (Zneg m) hn
      rw [hop] at h
      exact h
    obtain ⟨p, er, hr, hv⟩ := bofz_repr_positive_round ctx magnitude true m hn'
    have hb : BofZ (prec := prec) (emax := emax) (Zneg m) =
        Binary.B754_finite true p er := by
      apply bofz_repr_lift_finite
      change BinarySingleNaN.SF2B (prec := prec) (emax := emax)
        (BinarySingleNaN.binary_round (prec := prec) (emax := emax) mode_NE true m Z0) = _
      rw [hr]
      rfl
    change Exact.B2R ctx (BofZ (prec := prec) (emax := emax) (Zneg m)) =
      Exact.IZR ctx (Zneg m) ∧
      Binary.is_finite (BofZ (prec := prec) (emax := emax) (Zneg m)) = true ∧
      Binary.Bsign (BofZ (prec := prec) (emax := emax) (Zneg m)) = Zlt_bool (Zneg m) Z0
    rw [hb]
    refine ⟨?_, rfl, ?_⟩
    · change Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zopp (Zpos p)) er) =
        Exact.IZR ctx (Zneg m)
      have hf : Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zopp (Zpos p)) er) =
          Exact.Ropp ctx (Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos p) er)) :=
        Float_prop.F2R_Zopp ctx Zaux.radix2 (Zpos p) er
      rw [hf, hv]
      have hop' : Zopp (Zpos m) = Zneg m := by
        apply intOfZ_injective
        simp only [Zopp, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
          intOfZ_zOfInt]
        rfl
      have hizr : Exact.IZR ctx (Zopp (Zpos m)) = Exact.Ropp ctx (Exact.IZR ctx (Zpos m)) :=
        CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.opp_IZR ctx (Zpos m)
      rw [hop'] at hizr
      exact hizr.symm
    · change true = (if -Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m) < 0
        then true else false)
      have hp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive m
      simp only [Int.ofNat_eq_natCast]
      have hlt : -(Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m)) < 0 := by
        simp only [Int.ofNat_eq_natCast]
        omega
      simp only [Int.ofNat_eq_natCast] at hlt
      simp [hlt, hp]

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra
open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754

theorem ZofB_correct :
    ∀ {prec emax : Z}, ZofB_correctStatement (prec := prec) (emax := emax) := by
  intro prec emax f ctx
  cases f with
  | mk f hcert =>
    cases f with
    | B754_nan => simp [ZofB, Binary.is_finite]
    | B754_infinity s => simp [ZofB, Binary.is_finite]
    | B754_zero s =>
      simp only [ZofB, Binary.is_finite, Bool.false_eq_true, ↓reduceIte,
        Option.some.injEq]
      change Z0 = Exact.Ztrunc ctx (Exact.R0 ctx)
      have hz : Exact.R0 ctx = Exact.IZR ctx Z0 := by
        change ctx.spec.zero = ctx.spec.ofZ Z0
        exact ctx.certificate.sourceLaws.ofZ_zero.symm
      rw [hz]
      change Z0 = CompCert4Lean.Flocq.Core.Raux.Exact.Ztrunc ctx
        (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx Z0)
      rw [CompCert4Lean.Flocq.Core.Raux.Ztrunc_IZR ctx]
    | B754_finite s m e =>
      cases e with
      | Z0 =>
        simp only [ZofB, Binary.is_finite, ↓reduceIte,
          Option.some.injEq]
        change Zaux.cond_Zopp s (Zpos m) =
          Exact.Ztrunc ctx (CompCert4Lean.Flocq.IEEE754.Binary.Exact.F2R ctx
            (CompCert4Lean.Flocq.Core.Defs.Float Zaux.radix2
              (Zaux.cond_Zopp s (Zpos m)) Z0))
        have hF : CompCert4Lean.Flocq.IEEE754.Binary.Exact.F2R ctx
            (CompCert4Lean.Flocq.Core.Defs.Float Zaux.radix2
              (Zaux.cond_Zopp s (Zpos m)) Z0) =
            Exact.IZR ctx (Zaux.cond_Zopp s (Zpos m)) := by
          change ctx.spec.mul
              (ctx.spec.ofZ (Zaux.cond_Zopp s (Zpos m)))
              (Exact.bpow ctx Zaux.radix2 Z0) =
              ctx.spec.ofZ (Zaux.cond_Zopp s (Zpos m))
          rw [show Exact.bpow ctx Zaux.radix2 Z0 = ctx.spec.one by rfl,
            ctx.certificate.orderedField.mul_one]
        rw [hF]
        change Zaux.cond_Zopp s (Zpos m) =
          CompCert4Lean.Flocq.Core.Raux.Exact.Ztrunc ctx
            (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx
              (Zaux.cond_Zopp s (Zpos m)))
        rw [CompCert4Lean.Flocq.Core.Raux.Ztrunc_IZR ctx]
      | Zpos p =>
        simp only [ZofB, Binary.is_finite, ↓reduceIte,
          Option.some.injEq]
        change Zmul (Zaux.cond_Zopp s (Zpos m)) (Zpower_pos Ztwo p) =
          Exact.Ztrunc ctx (CompCert4Lean.Flocq.IEEE754.Binary.Exact.F2R ctx
            (CompCert4Lean.Flocq.Core.Defs.Float Zaux.radix2
              (Zaux.cond_Zopp s (Zpos m)) (Zpos p)))
        have hbpow : Exact.bpow ctx Zaux.radix2 (Zpos p) =
            Exact.IZR ctx (Zpower_pos Ztwo p) := by rfl
        have hF : CompCert4Lean.Flocq.IEEE754.Binary.Exact.F2R ctx
            (CompCert4Lean.Flocq.Core.Defs.Float Zaux.radix2
              (Zaux.cond_Zopp s (Zpos m)) (Zpos p)) =
            Exact.IZR ctx
              (Zmul (Zaux.cond_Zopp s (Zpos m)) (Zpower_pos Ztwo p)) := by
          change ctx.spec.mul
              (ctx.spec.ofZ (Zaux.cond_Zopp s (Zpos m)))
              (Exact.bpow ctx Zaux.radix2 (Zpos p)) = _
          rw [hbpow]
          exact (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR
            ctx (Zaux.cond_Zopp s (Zpos m)) (Zpower_pos Ztwo p)).symm
        rw [hF]
        change Zmul (Zaux.cond_Zopp s (Zpos m)) (Zpower_pos Ztwo p) =
          CompCert4Lean.Flocq.Core.Raux.Exact.Ztrunc ctx
            (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx
              (Zmul (Zaux.cond_Zopp s (Zpos m)) (Zpower_pos Ztwo p)))
        rw [CompCert4Lean.Flocq.Core.Raux.Ztrunc_IZR ctx]
      | Zneg p =>
        simp only [ZofB, Binary.is_finite, ↓reduceIte,
          Option.some.injEq]
        cases s with
        | false =>
          change Zdiv (Zpos m) (Zpower_pos Ztwo p) =
            Exact.Ztrunc ctx (CompCert4Lean.Flocq.IEEE754.Binary.Exact.F2R ctx
              (CompCert4Lean.Flocq.Core.Defs.Float Zaux.radix2
                (Zpos m) (Zneg p)))
          change Zdiv (Zpos m) (Zpower_pos Ztwo p) =
            Exact.Ztrunc ctx
              (ctx.spec.mul (ctx.spec.ofZ (Zpos m))
                (Exact.bpow ctx Zaux.radix2 (Zneg p)))
          change Zdiv (Zpos m) (Zpower_pos Ztwo p) =
            Exact.Ztrunc ctx
              (ctx.spec.mul (ctx.spec.ofZ (Zpos m))
                (ctx.spec.inv (ctx.spec.ofZ (Zpower_pos Ztwo p))))
          have hmpos : Zlt Z0 (Zpos m) := by
            change (0 : Int) <
              _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos m)
            simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
            change (0 : Int) < Int.ofNat
              (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m)
            exact Int.ofNat_lt.mpr
              (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive m)
          have hmle : Zle Z0 (Zpos m) := Int.le_of_lt hmpos
          have hpbase : Zlt Z0 Ztwo := by
            change (0 : Int) < 2
            decide
          have hpowpos := CompCert4Lean.Flocq.Core.Zaux.Zpower_pos_gt_0 Ztwo p hpbase
          rw [← ctx.certificate.orderedField.div_eq_mul_inv]
          exact (local_trunc_div ctx (Zpos m) (Zpower_pos Ztwo p) hmle hpowpos).symm
        | true =>
          change Zaux.cond_Zopp true (Zdiv (Zpos m) (Zpower_pos Ztwo p)) =
            Exact.Ztrunc ctx (CompCert4Lean.Flocq.IEEE754.Binary.Exact.B2R ctx
              (Binary.B754_finite true m (Zneg p)))
          change Zaux.cond_Zopp true (Zdiv (Zpos m) (Zpower_pos Ztwo p)) =
            Exact.Ztrunc ctx (CompCert4Lean.Flocq.IEEE754.Binary.Exact.F2R ctx
              (CompCert4Lean.Flocq.Core.Defs.Float Zaux.radix2
                (Zaux.cond_Zopp true (Zpos m)) (Zneg p)))
          have hFpos : CompCert4Lean.Flocq.IEEE754.Binary.Exact.F2R ctx
              (CompCert4Lean.Flocq.Core.Defs.Float Zaux.radix2 (Zpos m) (Zneg p)) =
              CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv ctx.spec
                (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx (Zpos m))
                (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx (Zpower_pos Ztwo p)) := by
            change ctx.spec.mul (ctx.spec.ofZ (Zpos m))
              (Exact.bpow ctx Zaux.radix2 (Zneg p)) = _
            change ctx.spec.mul (ctx.spec.ofZ (Zpos m))
              (ctx.spec.inv (ctx.spec.ofZ (Zpower_pos Ztwo p))) = _
            rw [← ctx.certificate.orderedField.div_eq_mul_inv]
            rfl
          have hF : CompCert4Lean.Flocq.IEEE754.Binary.Exact.F2R ctx
              (CompCert4Lean.Flocq.Core.Defs.Float Zaux.radix2
                (Zaux.cond_Zopp true (Zpos m)) (Zneg p)) =
              CompCert4Lean.Foundation.FlocqReal.ExactReal.Ropp ctx.spec
                (CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv ctx.spec
                  (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx (Zpos m))
                  (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx (Zpower_pos Ztwo p))) := by
            change ctx.spec.mul
                (ctx.spec.ofZ (Zaux.cond_Zopp true (Zpos m)))
                (Exact.bpow ctx Zaux.radix2 (Zneg p)) = _
            rw [show Zaux.cond_Zopp true (Zpos m) = Zopp (Zpos m) by rfl,
              ctx.certificate.sourceLaws.ofZ_neg]
            rw [← hFpos]
            exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Ropp_mult_distr_l_reverse
              ctx (ctx.spec.ofZ (Zpos m)) (Exact.bpow ctx Zaux.radix2 (Zneg p))
          rw [hF]
          change Zaux.cond_Zopp true (Zdiv (Zpos m) (Zpower_pos Ztwo p)) =
            CompCert4Lean.Flocq.Core.Raux.Exact.Ztrunc ctx
              (CompCert4Lean.Flocq.Core.Raux.Exact.Ropp ctx
                (CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv ctx.spec
                  (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx (Zpos m))
                  (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx (Zpower_pos Ztwo p))))
          rw [CompCert4Lean.Flocq.Core.Raux.Ztrunc_opp ctx]
          have hmpos : Zlt Z0 (Zpos m) := by
            change (0 : Int) <
              _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpos m)
            simp only [_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
            change (0 : Int) < Int.ofNat
              (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat m)
            exact Int.ofNat_lt.mpr
              (_root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive m)
          have hmle : Zle Z0 (Zpos m) := Int.le_of_lt hmpos
          have hpbase : Zlt Z0 Ztwo := by
            change (0 : Int) < 2
            decide
          have hpowpos := CompCert4Lean.Flocq.Core.Zaux.Zpower_pos_gt_0 Ztwo p hpbase
          rw [local_trunc_div ctx (Zpos m) (Zpower_pos Ztwo p) hmle hpowpos]
          rfl

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754

theorem ZofB_range_correct :
    ∀ {prec emax : Z}, ZofB_range_correctStatement (prec := prec) (emax := emax) := by
  intro prec emax f min max ctx
  dsimp [ZofB_range_correctStatement]
  unfold ZofB_range
  have hz := ZofB_correct (prec := prec) (emax := emax) f ctx
  rw [hz]
  cases hfin : Binary.is_finite f.1 with
  | false => simp [hfin]
  | true => simp [hfin]

end CompCert4Lean.Lib.IEEE754_extra
namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.Numbers.Rocq.Coq (intOfZ intOfZ_injective intOfZ_zOfInt)

theorem integer_representable_n2p :
    ∀ {prec emax : Z} [pgt : Prec_gt_0 prec]
      [ple : Prec_lt_emax prec emax],
      integer_representable_n2pStatement (prec := prec) (emax := emax) := by
  intro prec emax pgt ple ctx magnitude n p hn hp hpmax
  have hprec : 0 < intOfZ prec := pgt
  have hpe : intOfZ prec < intOfZ emax := ple.prec_lt_emax
  have hsub (a b : Z) : intOfZ (Zsub a b) = intOfZ a - intOfZ b := by
    simp [Zsub, Zaux.Zsub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub, intOfZ_zOfInt]
  have hadd (a b : Z) : intOfZ (Zadd a b) = intOfZ a + intOfZ b := by
    simp [Zadd, Zaux.Zadd,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add, intOfZ_zOfInt]
  have hmul (a b : Z) : intOfZ (Zmul a b) = intOfZ a * intOfZ b := by
    simp [Zmul, Zaux.Zmul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul, intOfZ_zOfInt]
  have hopp (a : Z) : intOfZ (Zopp a) = -intOfZ a := by
    simp [Zopp, Zaux.Zopp,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp, intOfZ_zOfInt]
  have habseq (a : Z) (ha : Zle Z0 a) : Zabs a = a :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs_eq a ha
  have habsneg (a : Z) (ha : Zle a Z0) : Zabs a = Zopp a :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs_neq a ha
  have habsmul (a b : Z) : Zabs (Zmul a b) = Zmul (Zabs a) (Zabs b) :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs_mul a b
  have hp0 : 0 ≤ intOfZ p := hp
  have hpmax' : intOfZ p ≤ intOfZ emax - intOfZ prec := by
    change intOfZ p ≤ intOfZ (Zsub emax prec) at hpmax
    simpa only [hsub] using hpmax
  have hdiff_nonneg : Zle Z0 (Zsub emax prec) := by
    change (0 : Int) ≤ intOfZ (Zsub emax prec)
    rw [hsub]
    omega
  have hsum : Zadd (Zsub emax prec) prec = emax := by
    apply intOfZ_injective
    rw [hadd, hsub]
    omega
  have hpow :
      Zpower Ztwo emax =
        Zmul (Zpower Ztwo (Zsub emax prec)) (Zpower Ztwo prec) := by
    have h := Zaux.Zpower_plus Ztwo (Zsub emax prec) prec
      hdiff_nonneg (Int.le_of_lt hprec)
    change Zpower Ztwo (Zadd (Zsub emax prec) prec) =
      Zmul (Zpower Ztwo (Zsub emax prec)) (Zpower Ztwo prec) at h
    rw [hsum] at h
    exact h
  have hpow_le : Zle (Zpower Ztwo p) (Zpower Ztwo (Zsub emax prec)) :=
    Zaux.Zpower_le Zaux.radix2 p (Zsub emax prec) hpmax
  have hpowp_nonneg : Zle Z0 (Zpower Ztwo p) :=
    Zaux.Zpower_ge_0 Zaux.radix2 p
  have hpowprec_nonneg : Zle Z0 (Zpower Ztwo prec) :=
    Zaux.Zpower_ge_0 Zaux.radix2 prec
  have hpowprec_gt_one : Zlt Zone (Zpower Ztwo prec) :=
    Zaux.Zpower_gt_1 Zaux.radix2 prec (show Zlt Z0 prec from pgt)
  have hA_lt : intOfZ (Zabs n) < intOfZ (Zpower Ztwo prec) := by
    have hnlo : -intOfZ (Zpower Ztwo prec) < intOfZ n := by
      have h := hn.1
      change intOfZ (Zopp (Zpower Ztwo prec)) < intOfZ n at h
      rw [hopp] at h
      omega
    have hnhi : intOfZ n < intOfZ (Zpower Ztwo prec) := by
      have h := hn.2
      change intOfZ n < intOfZ (Zpower Ztwo prec) at h
      omega
    by_cases hsign : 0 ≤ intOfZ n
    · rw [habseq n hsign]
      exact hnhi
    · rw [habsneg n (show intOfZ n ≤ 0 by omega), hopp]
      omega
  have hA_le : intOfZ (Zabs n) ≤ intOfZ (Zsub (Zpower Ztwo prec) Zone) := by
    rw [hsub]
    have hone : intOfZ Zone = 1 := rfl
    rw [hone]
    omega
  have hCminus_nonneg : (0 : Int) ≤ intOfZ (Zsub (Zpower Ztwo prec) Zone) := by
    rw [hsub]
    have hone : intOfZ Zone = 1 := rfl
    rw [hone]
    have hpowgt : (1 : Int) < intOfZ (Zpower Ztwo prec) := hpowprec_gt_one
    omega
  have hupper :
      intOfZ (Zsub (Zpower Ztwo prec) Zone) * intOfZ (Zpower Ztwo (Zsub emax prec)) =
        intOfZ (Zsub (Zpower Ztwo emax) (Zpower Ztwo (Zsub emax prec))) := by
    rw [hsub, hsub, hpow, hmul]
    have hone : intOfZ Zone = 1 := rfl
    rw [hone]
    rw [Int.sub_mul]
    simp only [Int.one_mul]
    rw [Int.mul_comm]
  constructor
  · rw [habsmul, habseq _ hpowp_nonneg]
    change intOfZ (Zmul (Zabs n) (Zpower Ztwo p)) ≤
      intOfZ (Zsub (Zpower Ztwo emax) (Zpower Ztwo (Zsub emax prec)))
    rw [hmul, hsub]
    have hstep1 :=
      Int.mul_le_mul_of_nonneg_right hA_le
        (show (0 : Int) ≤ intOfZ (Zpower Ztwo p) from hpowp_nonneg)
    have hstep2 :=
      Int.mul_le_mul_of_nonneg_left hpow_le hCminus_nonneg
    have hchain : intOfZ (Zabs n) * intOfZ (Zpower Ztwo p) ≤
        intOfZ (Zsub (Zpower Ztwo prec) Zone) *
          intOfZ (Zpower Ztwo (Zsub emax prec)) :=
      Int.le_trans hstep1 hstep2
    rw [hupper] at hchain
    simpa only [hsub] using hchain
  · change Generic_fmt.Exact.generic_format ctx magnitude Zaux.radix2
      (FLT.FLT_exp (emin prec emax) prec) (Exact.IZR ctx (Zmul n (Zpower Ztwo p)))
    apply FLT.generic_format_FLT ctx magnitude
    apply FLT.FLT_spec _ _ _ _ (Defs.Float Zaux.radix2 n p)
    · change Exact.IZR ctx (Zmul n (Zpower Ztwo p)) =
        Exact.Rmult ctx (Exact.IZR ctx n) (Exact.bpow ctx Zaux.radix2 p)
      have hizr : Exact.IZR ctx (Zpower Ztwo p) = Exact.bpow ctx Zaux.radix2 p :=
        Raux.IZR_Zpower ctx Zaux.radix2 p hp
      rw [← hizr]
      exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR ctx n _
    · exact hA_lt
    · change intOfZ (Zsub (Zsub (Zpos (.xI .xH)) emax) prec) ≤ intOfZ p
      rw [hsub, hsub]
      have hthree : intOfZ (Zpos (.xI .xH)) = 3 := rfl
      rw [hthree]
      omega

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals

theorem Ztrunc_range_zero : Ztrunc_range_zeroStatement := by
  intro ctx value hzero
  have habs : ctx.spec.le ctx.spec.zero (ctx.spec.abs value) := by
    have hbound := Rbasic_fun.Rabs_pos ctx value
    change ctx.spec.le (ctx.spec.ofZ Z0) (ctx.spec.abs value) at hbound
    simpa only [ctx.certificate.sourceLaws.ofZ_zero] using hbound
  have hfloor : Raux.Exact.Zfloor ctx (ctx.spec.abs value) = Z0 := by
    rw [← Raux.Ztrunc_floor ctx _ habs]
    change Raux.Exact.Ztrunc ctx (Raux.Exact.Rabs ctx value) = Z0
    rw [Raux.Ztrunc_abs ctx value]
    change Zabs (Exact.Ztrunc ctx value) = Z0
    rw [hzero]
    rfl
  have hupper := Raux.Zfloor_ub ctx (ctx.spec.abs value)
  change ctx.spec.lt (ctx.spec.abs value)
    (ctx.spec.add (ctx.spec.ofZ (Raux.Exact.Zfloor ctx (ctx.spec.abs value)))
      ctx.spec.one) at hupper
  rw [hfloor, ctx.certificate.sourceLaws.ofZ_zero,
    ctx.certificate.orderedField.zero_add] at hupper
  obtain ⟨hhigh, hlow⟩ := Rbasic_fun.Rabs_def2 ctx value ctx.spec.one hupper
  exact ⟨hlow, hhigh⟩

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

theorem ZofB_range_zero :
    ∀ {prec emax : Z} [Prec_gt_0 prec] [Prec_lt_emax prec emax],
      ZofB_range_zeroStatement (prec := prec) (emax := emax) := by
  intro prec emax precision_gt precision_lt value hzero ctx
  apply Ztrunc_range_zero ctx (Exact.B2R ctx value.1)
  have hcorrect := ZofB_correct value ctx
  rw [hzero] at hcorrect
  split at hcorrect
  · exact (Option.some.inj hcorrect).symm
  · contradiction

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Foundation.Numbers.Rocq.Coq (intOfZ intOfZ_injective)
open CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals

theorem ZofB_range_nonneg :
    ∀ {prec emax : Z} [Prec_gt_0 prec] [Prec_lt_emax prec emax],
      ZofB_range_nonnegStatement (prec := prec) (emax := emax) := by
  intro prec emax precision_gt precision_lt value integer hconvert hnonneg ctx
  by_cases hzero : integer = Z0
  · subst integer
    have hbound := ZofB_range_zero value hconvert ctx
    refine ⟨hbound.1, ?_⟩
    change ctx.spec.lt _ (ctx.spec.ofZ Zone)
    rw [ctx.certificate.sourceLaws.ofZ_one]
    exact hbound.2
  · have hpositive : Zlt Z0 integer := by
      change (0 : Int) < intOfZ integer
      change (0 : Int) ≤ intOfZ integer at hnonneg
      have hne : intOfZ integer ≠ 0 := by
        intro hint
        exact hzero (intOfZ_injective hint)
      omega
    have hbound := ZofB_range_pos value integer hconvert hpositive ctx
    have hlower : ctx.spec.lt (ctx.spec.neg ctx.spec.one) (ctx.spec.ofZ integer) := by
      have hnegative : Zlt (Zopp Zone) integer := by
        change (-1 : Int) < intOfZ integer
        change (0 : Int) ≤ intOfZ integer at hnonneg
        omega
      have hreal := RIneq.IZR_lt ctx (Zopp Zone) integer hnegative
      change ctx.spec.lt (ctx.spec.ofZ (Zopp Zone)) (ctx.spec.ofZ integer) at hreal
      rw [ctx.certificate.sourceLaws.ofZ_neg, ctx.certificate.sourceLaws.ofZ_one] at hreal
      exact hreal
    exact ⟨RIneq.Rlt_le_trans ctx _ _ _ hlower hbound.1, hbound.2⟩

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem ieee_manual_add_int (left right : Z) :
    intOfZ (Zadd left right) = intOfZ left + intOfZ right := intOfZ_zOfInt _

private theorem ieee_manual_sub_int (left right : Z) :
    intOfZ (Zsub left right) = intOfZ left - intOfZ right := intOfZ_zOfInt _

private theorem ieee_manual_fexp_int (precision maximum exponent : Z) :
    intOfZ (fexp precision maximum exponent) =
      max (intOfZ exponent - intOfZ precision) (3 - intOfZ maximum - intOfZ precision) := by
  change intOfZ (if intOfZ (Zsub exponent precision) ≤
    intOfZ (Zsub (Zsub (Zpos (.xI .xH)) maximum) precision)
    then Zsub (Zsub (Zpos (.xI .xH)) maximum) precision else Zsub exponent precision) = _
  split <;> simp only [ieee_manual_sub_int,
    show intOfZ (Zpos (.xI .xH)) = 3 from rfl] at * <;> omega

private theorem ieee_manual_digits_nat (mantissa : positive) :
    posToNat (Digits.digits2_pos mantissa) = Nat.log2 (posToNat mantissa) + 1 := by
  have hsucc (value : positive) :
      posToNat (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posSucc value) =
        posToNat value + 1 := PArith.BinPos.Pos.posToNat_succ value
  induction mantissa with
  | xH => decide
  | xO mantissa induction_hypothesis =>
    change posToNat (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posSucc
      (Digits.digits2_pos mantissa)) = Nat.log2 (2 * posToNat mantissa) + 1
    rw [hsucc, induction_hypothesis, Nat.log2_two_mul (Nat.ne_of_gt (posToNat_positive mantissa))]
  | xI mantissa induction_hypothesis =>
    change posToNat (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.posSucc
      (Digits.digits2_pos mantissa)) = Nat.log2 (2 * posToNat mantissa + 1) + 1
    rw [hsucc, induction_hypothesis, Nat.log2_def (2 * posToNat mantissa + 1)]
    have hpositive := posToNat_positive mantissa
    rw [if_pos (by omega)]
    have hdivide : (2 * posToNat mantissa + 1) / 2 = posToNat mantissa := by omega
    rw [hdivide]

private theorem ieee_manual_log2_shift (mantissa amount : Nat) (hpositive : 0 < mantissa) :
    Nat.log2 (mantissa * 2 ^ amount) = Nat.log2 mantissa + amount := by
  apply (Nat.log2_eq_iff (Nat.ne_of_gt (Nat.mul_pos hpositive (Nat.two_pow_pos amount)))).2
  have hlower := Nat.log2_self_le (Nat.ne_of_gt hpositive)
  have hupper := (Nat.log2_lt (Nat.ne_of_gt hpositive)).1 (Nat.lt_succ_self (Nat.log2 mantissa))
  constructor
  · rw [Nat.pow_add]
    exact Nat.mul_le_mul_right (2 ^ amount) hlower
  · rw [show Nat.log2 mantissa + amount + 1 = (Nat.log2 mantissa + 1) + amount by omega,
      Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right hupper (Nat.two_pow_pos amount)

private theorem ieee_manual_shift_digits (amount mantissa : positive) :
    intOfZ (Zpos (Digits.digits2_pos
      (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos amount mantissa))) =
      intOfZ (Zpos (Digits.digits2_pos mantissa)) + intOfZ (Zpos amount) := by
  change (posToNat (Digits.digits2_pos
      (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos amount mantissa)) : Int) =
    (posToNat (Digits.digits2_pos mantissa) : Int) + (posToNat amount : Int)
  rw [ieee_manual_digits_nat, ieee_manual_digits_nat]
  unfold CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos
    ZArith.Zpower.shift_pos PArith.BinPos.Pos.shiftl_nat
  rw [posToNat_posOfNat (Nat.mul_pos (posToNat_positive mantissa) (Nat.two_pow_pos _))]
  rw [ieee_manual_log2_shift _ _ (posToNat_positive mantissa)]
  simp only [PArith.BinPos.Pos.to_nat, Int.natCast_add]
  omega

private theorem ieee_manual_align_magnitude (precision maximum : Z) (mantissa : positive) (exponent : Z) :
    let aligned := BinarySingleNaN.shl_align_fexp (prec := precision) (emax := maximum) mantissa exponent
    Zadd (Zpos (Digits.digits2_pos aligned.1)) aligned.2 =
      Zadd (Zpos (Digits.digits2_pos mantissa)) exponent := by
  let target := fexp precision maximum (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent)
  change Zadd (Zpos (Digits.digits2_pos (BinarySingleNaN.shl_align mantissa exponent target).1))
    (BinarySingleNaN.shl_align mantissa exponent target).2 = _
  change (let aligned := match Zsub target exponent with
    | .Zneg amount => (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos amount mantissa, target)
    | _ => (mantissa, exponent)
    ; Zadd (Zpos (Digits.digits2_pos aligned.1)) aligned.2) = _
  cases hdifference : Zsub target exponent with
  | Z0 => rfl
  | Zpos amount => rfl
  | Zneg amount =>
    apply intOfZ_injective
    change intOfZ (Zadd (Zpos (Digits.digits2_pos
      (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos amount mantissa))) target) = _
    rw [ieee_manual_add_int, ieee_manual_add_int, ieee_manual_shift_digits]
    have hdifference_int := congrArg intOfZ hdifference
    rw [ieee_manual_sub_int] at hdifference_int
    change intOfZ target - intOfZ exponent = -(posToNat amount : Int) at hdifference_int
    change (posToNat (Digits.digits2_pos mantissa) : Int) + (posToNat amount : Int) +
      intOfZ target = (posToNat (Digits.digits2_pos mantissa) : Int) + intOfZ exponent
    omega

private theorem ieee_manual_round_canonical {prec emax : Z}
    (rounding : mode) (sign : Bool) (mantissa : positive) (exponent : Z)
    (hcanonical : fexp prec emax (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent) = exponent)
    (hbounded : Zle exponent (Zsub emax prec)) :
    BinarySingleNaN.binary_round_aux (prec := prec) (emax := emax) rounding sign
      (Zpos mantissa) exponent BinarySingleNaN.loc_Exact =
        BinarySingleNaN.S754_finite sign mantissa exponent := by
  have hshift : BinarySingleNaN.shr_fexp (prec := prec) (emax := emax)
      (Zpos mantissa) exponent BinarySingleNaN.loc_Exact =
      (BinarySingleNaN.shr_record_of_loc (Zpos mantissa) BinarySingleNaN.loc_Exact, exponent) := by
    change BinarySingleNaN.shr
      (BinarySingleNaN.shr_record_of_loc (Zpos mantissa) BinarySingleNaN.loc_Exact) exponent
      (Zsub (fexp prec emax (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent)) exponent) = _
    rw [hcanonical, show Zsub exponent exponent = Z0 by
      apply intOfZ_injective
      rw [ieee_manual_sub_int]
      change intOfZ exponent - intOfZ exponent = 0
      omega]
    rfl
  have hchoice : BinarySingleNaN.choice_mode rounding sign (Zpos mantissa)
      BinarySingleNaN.loc_Exact = Zpos mantissa := by
    cases rounding <;> cases sign <;> rfl
  unfold BinarySingleNaN.binary_round_aux
  rw [hshift]
  change (match BinarySingleNaN.shr_m (BinarySingleNaN.shr_fexp
    (prec := prec) (emax := emax)
    (BinarySingleNaN.choice_mode rounding sign (Zpos mantissa) BinarySingleNaN.loc_Exact)
    exponent BinarySingleNaN.loc_Exact).1 with
    | .Z0 => BinarySingleNaN.S754_zero sign
    | .Zpos result => BinarySingleNaN.binary_fit_aux (prec := prec) (emax := emax)
      rounding sign result (BinarySingleNaN.shr_fexp (prec := prec) (emax := emax)
        (BinarySingleNaN.choice_mode rounding sign (Zpos mantissa) BinarySingleNaN.loc_Exact)
        exponent BinarySingleNaN.loc_Exact).2
    | .Zneg _ => BinarySingleNaN.S754_nan) = _
  rw [hchoice, hshift]
  change (if Zle_bool exponent (Zsub emax prec) then _ else _) = _
  have htest : Zle_bool exponent (Zsub emax prec) = true := by
    change (if intOfZ exponent ≤ intOfZ (Zsub emax prec) then true else false) = true
    exact if_pos hbounded
  rw [htest]
  rfl

private theorem ieee_manual_round_exact {prec emax : Z}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (ctx : ExactRealContext) (rounding : mode) (sign : Bool)
    (mantissa : positive) (exponent : Z)
    (hsmall : Zle (fexp prec emax (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent)) exponent)
    (hupper : Zle (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent) emax) :
    ∃ result_mantissa result_exponent,
      BinarySingleNaN.binary_round (prec := prec) (emax := emax)
        rounding sign mantissa exponent = BinarySingleNaN.S754_finite sign result_mantissa result_exponent ∧
      Binary.bounded (prec := prec) (emax := emax) result_mantissa result_exponent = true ∧
      Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos result_mantissa) result_exponent) =
        Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos mantissa) exponent) := by
  let target := fexp prec emax (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent)
  have halign := BinarySingleNaN.shl_align_correct' ctx mantissa exponent target hsmall
  have hmagnitude := ieee_manual_align_magnitude prec emax mantissa exponent
  change (match BinarySingleNaN.shl_align_fexp (prec := prec) (emax := emax) mantissa exponent with
    | (result_mantissa, result_exponent) =>
      Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos result_mantissa) target) =
        Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos mantissa) exponent) ∧
      result_exponent = target) at halign
  generalize haligned : BinarySingleNaN.shl_align_fexp
    (prec := prec) (emax := emax) mantissa exponent = aligned
  rcases aligned with ⟨result_mantissa, result_exponent⟩
  rw [haligned] at halign hmagnitude
  dsimp only at halign hmagnitude
  have hcanonical : fexp prec emax
      (Zadd (Zpos (Digits.digits2_pos result_mantissa)) result_exponent) = result_exponent := by
    rw [hmagnitude]
    exact halign.2.symm
  have hbounded : Zle result_exponent (Zsub emax prec) := by
    rw [halign.2]
    change intOfZ target ≤ intOfZ (Zsub emax prec)
    dsimp only [target]
    rw [ieee_manual_fexp_int, ieee_manual_add_int, ieee_manual_sub_int]
    have hprecision : (0 : Int) < intOfZ prec := FLX.prec_gt_0 prec
    have hmaximum : intOfZ prec < intOfZ emax := BinarySingleNaN.prec_lt_emax
    change intOfZ (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent) ≤ intOfZ emax at hupper
    rw [ieee_manual_add_int] at hupper
    omega
  refine ⟨result_mantissa, result_exponent, ?_, ?_, ?_⟩
  · unfold BinarySingleNaN.binary_round
    rw [haligned]
    exact ieee_manual_round_canonical rounding sign result_mantissa result_exponent hcanonical hbounded
  · apply Bool.and_eq_true_iff.mpr
    constructor
    · change (if fexp prec emax (Zadd (Zpos (Digits.digits2_pos result_mantissa)) result_exponent) =
        result_exponent then true else false) = true
      exact if_pos hcanonical
    · change (if intOfZ result_exponent ≤ intOfZ (Zsub emax prec) then true else false) = true
      exact if_pos hbounded
  · rw [halign.2]
    exact halign.1

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem ieee_manual_lift_finite {prec emax : Z}
    (value : BinarySingleNaN.binary_float prec emax) (hnan : BinarySingleNaN.is_nan value = false)
    (sign : Bool) (mantissa : positive) (exponent : Z)
    (hequal : value = BinarySingleNaN.B754_finite sign mantissa exponent) :
    Binary.BSN2B' value hnan = Binary.B754_finite sign mantissa exponent := by
  cases hequal
  rfl

private theorem ieee_manual_widen_finite {prec1 emax1 prec2 emax2 : Z}
    [Prec_gt_0 prec2] [Prec_lt_emax prec2 emax2]
    [Binary.BinaryNormalizeCertificate prec2 emax2]
    (ctx : ExactRealContext) (precision_le : Zle prec1 prec2) (maximum_le : Zle emax1 emax2)
    (rounding : mode) (sign : Bool) (mantissa : positive) (exponent : Z)
    (hvalid : Binary.bounded (prec := prec1) (emax := emax1) mantissa exponent = true) :
    ∃ result_mantissa result_exponent,
      Binary.binary_normalize (prec := prec2) (emax := emax2)
        rounding (Zaux.cond_Zopp sign (Zpos mantissa)) exponent sign =
          Binary.B754_finite sign result_mantissa result_exponent ∧
      Binary.bounded (prec := prec2) (emax := emax2) result_mantissa result_exponent = true ∧
      Defs.Exact.F2R ctx
        (Defs.Float Zaux.radix2 (Zaux.cond_Zopp sign (Zpos result_mantissa)) result_exponent) =
      Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zaux.cond_Zopp sign (Zpos mantissa)) exponent) := by
  have hparts := Bool.and_eq_true_iff.mp hvalid
  have hcanonical : fexp prec1 emax1 (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent) = exponent :=
    ZArith.Zbool.Zeq_bool_eq _ _ hparts.1
  have hbound : Zle exponent (Zsub emax1 prec1) := by
    have hcheck := hparts.2
    change (if intOfZ exponent ≤ intOfZ (Zsub emax1 prec1) then true else false) = true at hcheck
    change intOfZ exponent ≤ intOfZ (Zsub emax1 prec1)
    split at hcheck
    · assumption
    · contradiction
  have hsmall : Zle (fexp prec2 emax2 (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent)) exponent := by
    have hcanonical_int := congrArg intOfZ hcanonical
    rw [ieee_manual_fexp_int, ieee_manual_add_int] at hcanonical_int
    change intOfZ _ ≤ intOfZ _
    rw [ieee_manual_fexp_int, ieee_manual_add_int]
    change intOfZ prec1 ≤ intOfZ prec2 at precision_le
    change intOfZ emax1 ≤ intOfZ emax2 at maximum_le
    omega
  have hupper : Zle (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent) emax2 := by
    have hcanonical_int := congrArg intOfZ hcanonical
    rw [ieee_manual_fexp_int, ieee_manual_add_int] at hcanonical_int
    change intOfZ exponent ≤ intOfZ (Zsub emax1 prec1) at hbound
    rw [ieee_manual_sub_int] at hbound
    change intOfZ emax1 ≤ intOfZ emax2 at maximum_le
    change intOfZ (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent) ≤ intOfZ emax2
    rw [ieee_manual_add_int]
    omega
  obtain ⟨result_mantissa, result_exponent, hround, hresult, hvalue⟩ :=
    ieee_manual_round_exact ctx rounding sign mantissa exponent hsmall hupper
  refine ⟨result_mantissa, result_exponent, ?_, hresult, ?_⟩
  · cases sign with
    | false =>
      unfold Binary.binary_normalize
      apply ieee_manual_lift_finite
      change BinarySingleNaN.SF2B
        (BinarySingleNaN.binary_round (prec := prec2) (emax := emax2) rounding false mantissa exponent) = _
      rw [hround]
      rfl
    | true =>
      have hnegative : Zaux.cond_Zopp true (Zpos mantissa) = Zneg mantissa := by
        apply intOfZ_injective
        change intOfZ (zOfInt (-(posToNat mantissa : Int))) = -(posToNat mantissa : Int)
        exact intOfZ_zOfInt _
      rw [hnegative]
      unfold Binary.binary_normalize
      apply ieee_manual_lift_finite
      change BinarySingleNaN.SF2B
        (BinarySingleNaN.binary_round (prec := prec2) (emax := emax2) rounding true mantissa exponent) = _
      rw [hround]
      rfl
  · cases sign with
    | false => exact hvalue
    | true =>
      change Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zopp (Zpos result_mantissa)) result_exponent) =
        Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zopp (Zpos mantissa)) exponent)
      have hleft : Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zopp (Zpos result_mantissa)) result_exponent) =
          ctx.spec.neg (Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos result_mantissa) result_exponent)) :=
        Float_prop.F2R_Zopp ctx Zaux.radix2 (Zpos result_mantissa) result_exponent
      have hright : Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zopp (Zpos mantissa)) exponent) =
          ctx.spec.neg (Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos mantissa) exponent)) :=
        Float_prop.F2R_Zopp ctx Zaux.radix2 (Zpos mantissa) exponent
      rw [hleft, hright, hvalue]

theorem Bconv_widen_exact :
    ∀ {prec1 emax1 prec2 emax2 : Z} [Prec_gt_0 prec1] [Prec_gt_0 prec2]
      [Prec_lt_emax prec2 emax2] [Binary.BinaryNormalizeCertificate prec2 emax2],
      Bconv_widen_exactStatement (prec1 := prec1) (emax1 := emax1)
        (prec2 := prec2) (emax2 := emax2) := by
  intro prec1 emax1 prec2 emax2 precision1_gt precision2_gt maximum2_gt certificate
    ctx precision_le maximum_le nan rounding value hfinite
  rcases value with ⟨value, hvalid⟩
  cases value with
  | B754_zero sign => exact ⟨rfl, rfl, rfl⟩
  | B754_infinity sign => contradiction
  | B754_nan sign payload => contradiction
  | B754_finite sign mantissa exponent =>
    obtain ⟨result_mantissa, result_exponent, hnormalize, hresult, hvalue⟩ :=
      ieee_manual_widen_finite ctx precision_le maximum_le rounding sign mantissa exponent hvalid
    change Exact.B2R ctx (Binary.binary_normalize rounding (Zaux.cond_Zopp sign (Zpos mantissa)) exponent sign) =
      Exact.B2R ctx (Binary.B754_finite (prec := prec1) (emax := emax1) sign mantissa exponent) ∧
      Binary.is_finite (Binary.binary_normalize rounding (Zaux.cond_Zopp sign (Zpos mantissa)) exponent sign) = true ∧
      Binary.Bsign (Binary.binary_normalize rounding (Zaux.cond_Zopp sign (Zpos mantissa)) exponent sign) = sign
    rw [hnormalize]
    exact ⟨hvalue, rfl, rfl⟩

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private def ieee_manual_nat_trunc (mantissa : Nat) (exponent : Int) : Nat :=
  mantissa * 2 ^ exponent.toNat / 2 ^ (-exponent).toNat

private theorem ieee_manual_nat_trunc_shift (mantissa : Nat) (old_exponent new_exponent : Int)
    (hle : new_exponent ≤ old_exponent) :
    ieee_manual_nat_trunc (mantissa * 2 ^ (old_exponent - new_exponent).toNat) new_exponent =
      ieee_manual_nat_trunc mantissa old_exponent := by
  unfold ieee_manual_nat_trunc
  by_cases hnew : 0 ≤ new_exponent
  · have hold : 0 ≤ old_exponent := by omega
    have hnegative_new : (-new_exponent).toNat = 0 := by omega
    have hnegative_old : (-old_exponent).toNat = 0 := by omega
    rw [hnegative_new, hnegative_old]
    simp only [Nat.pow_zero, Nat.div_one]
    rw [Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  · have hzero_new : new_exponent.toNat = 0 := by omega
    rw [hzero_new]
    simp only [Nat.pow_zero, Nat.mul_one]
    by_cases hold : 0 ≤ old_exponent
    · have hnegative_old : (-old_exponent).toNat = 0 := by omega
      have hsplit : (old_exponent - new_exponent).toNat =
          old_exponent.toNat + (-new_exponent).toNat := by omega
      rw [hsplit, hnegative_old, Nat.pow_add, ← Nat.mul_assoc]
      simp only [Nat.pow_zero, Nat.div_one]
      exact Nat.mul_div_cancel _ (Nat.two_pow_pos _)
    · have hzero_old : old_exponent.toNat = 0 := by omega
      have hsplit : (-new_exponent).toNat =
          (-old_exponent).toNat + (old_exponent - new_exponent).toNat := by omega
      rw [hzero_old, hsplit, Nat.pow_add]
      simp only [Nat.pow_zero, Nat.mul_one]
      exact Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)

private theorem ieee_manual_power_pos_int (amount : positive) :
    intOfZ (Zpower_pos Ztwo amount) = (2 ^ posToNat amount : Nat) := by
  change intOfZ (zOfInt ((2 : Int) ^ posToNat amount)) = _
  rw [intOfZ_zOfInt, Int.natCast_pow]
  rfl

private theorem ieee_manual_zofb_nat {precision maximum : Z}
    (sign : Bool) (mantissa : positive) (exponent : Z) :
    ZofB (Binary.B754_finite (prec := precision) (emax := maximum) sign mantissa exponent) =
      some (Zaux.cond_Zopp sign (zOfInt (ieee_manual_nat_trunc (posToNat mantissa) (intOfZ exponent)))) := by
  cases exponent with
  | Z0 =>
    apply congrArg some
    apply congrArg (Zaux.cond_Zopp sign)
    apply intOfZ_injective
    change (posToNat mantissa : Int) = intOfZ (zOfInt (ieee_manual_nat_trunc (posToNat mantissa) 0))
    simp [ieee_manual_nat_trunc, intOfZ_zOfInt]
  | Zpos amount =>
    apply congrArg some
    apply intOfZ_injective
    have hpositive := posToNat_positive amount
    have hnegative : (-(posToNat amount : Int)).toNat = 0 := by omega
    cases sign <;>
      simp only [Zaux.cond_Zopp, CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.cond_Zopp,
        Bool.false_eq_true, ↓reduceIte,
        Zmul, Zaux.Zmul, ZArith.BinInt.Z.mul, ZArith.BinInt.Z.opp,
        intOfZ_zOfInt, ieee_manual_power_pos_int, ieee_manual_nat_trunc,
        show intOfZ (Zpos amount) = (posToNat amount : Int) from rfl,
        hnegative, Int.toNat_natCast, Nat.pow_zero, Nat.div_one, Int.natCast_mul, Int.neg_mul] <;> rfl
  | Zneg amount =>
    apply congrArg some
    apply congrArg (Zaux.cond_Zopp sign)
    apply intOfZ_injective
    have hpositive : (0 : Int) < intOfZ (Zpower_pos Ztwo amount) := by
      rw [ieee_manual_power_pos_int]
      exact Int.natCast_pos.mpr (Nat.two_pow_pos _)
    have hdivision : intOfZ (Zdiv (Zpos mantissa) (Zpower_pos Ztwo amount)) =
        (posToNat mantissa : Int) / intOfZ (Zpower_pos Ztwo amount) := by
      change intOfZ (zOfInt (if intOfZ (Zpower_pos Ztwo amount) = 0 then 0
        else if 0 < intOfZ (Zpower_pos Ztwo amount) then
          (posToNat mantissa : Int) / intOfZ (Zpower_pos Ztwo amount) else _)) = _
      rw [if_neg (Int.ne_of_gt hpositive), if_pos hpositive, intOfZ_zOfInt]
    rw [hdivision]
    have hnegative : (-(posToNat amount : Int)).toNat = 0 := by omega
    simp only [intOfZ_zOfInt, ieee_manual_power_pos_int, ieee_manual_nat_trunc,
      show intOfZ (Zneg amount) = -(posToNat amount : Int) from rfl,
      hnegative, Int.neg_neg, Int.toNat_natCast, Nat.pow_zero, Nat.mul_one, Int.natCast_ediv]

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem ieee_manual_align_exponent (mantissa : positive) (exponent target : Z)
    (hle : Zle target exponent) :
    (BinarySingleNaN.shl_align mantissa exponent target).2 = target := by
  change (match Zsub target exponent with
    | .Zneg amount => (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos amount mantissa, target)
    | _ => (mantissa, exponent)).2 = target
  cases hdifference : Zsub target exponent with
  | Z0 =>
    apply intOfZ_injective
    have hint := congrArg intOfZ hdifference
    rw [ieee_manual_sub_int] at hint
    change intOfZ target - intOfZ exponent = 0 at hint
    dsimp only
    omega
  | Zpos amount =>
    have hint := congrArg intOfZ hdifference
    rw [ieee_manual_sub_int] at hint
    change intOfZ target - intOfZ exponent = (posToNat amount : Int) at hint
    change intOfZ target ≤ intOfZ exponent at hle
    have hpositive := posToNat_positive amount
    omega
  | Zneg amount => rfl

private theorem ieee_manual_align_trunc (mantissa : positive) (exponent target : Z) :
    let aligned := BinarySingleNaN.shl_align mantissa exponent target
    ieee_manual_nat_trunc (posToNat aligned.1) (intOfZ aligned.2) =
      ieee_manual_nat_trunc (posToNat mantissa) (intOfZ exponent) := by
  change (let aligned := match Zsub target exponent with
    | .Zneg amount => (CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos amount mantissa, target)
    | _ => (mantissa, exponent)
    ; ieee_manual_nat_trunc (posToNat aligned.1) (intOfZ aligned.2)) = _
  cases hdifference : Zsub target exponent with
  | Z0 => rfl
  | Zpos amount => rfl
  | Zneg amount =>
    have hint := congrArg intOfZ hdifference
    rw [ieee_manual_sub_int] at hint
    change intOfZ target - intOfZ exponent = -(posToNat amount : Int) at hint
    have hle : intOfZ target ≤ intOfZ exponent := by omega
    have hamount : PArith.BinPos.Pos.to_nat amount = (intOfZ exponent - intOfZ target).toNat := by
      change posToNat amount = _
      omega
    dsimp only
    unfold CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shiftPos
      ZArith.Zpower.shift_pos PArith.BinPos.Pos.shiftl_nat
    rw [posToNat_posOfNat (Nat.mul_pos (posToNat_positive mantissa) (Nat.two_pow_pos _)), hamount]
    exact ieee_manual_nat_trunc_shift _ _ _ hle

private theorem ieee_manual_widen_core {prec1 emax1 prec2 emax2 : Z}
    [Prec_gt_0 prec2] [Prec_lt_emax prec2 emax2]
    [Binary.BinaryNormalizeCertificate prec2 emax2]
    (precision_le : Zle prec1 prec2) (maximum_le : Zle emax1 emax2)
    (rounding : mode) (sign : Bool) (mantissa : positive) (exponent : Z)
    (hvalid : Binary.bounded (prec := prec1) (emax := emax1) mantissa exponent = true) :
    let aligned := BinarySingleNaN.shl_align_fexp (prec := prec2) (emax := emax2) mantissa exponent
    Binary.binary_normalize (prec := prec2) (emax := emax2)
        rounding (Zaux.cond_Zopp sign (Zpos mantissa)) exponent sign =
      Binary.B754_finite sign aligned.1 aligned.2 := by
  have hparts := Bool.and_eq_true_iff.mp hvalid
  have hcanonical : fexp prec1 emax1 (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent) = exponent :=
    ZArith.Zbool.Zeq_bool_eq _ _ hparts.1
  have hcanonical_int := congrArg intOfZ hcanonical
  rw [ieee_manual_fexp_int, ieee_manual_add_int] at hcanonical_int
  have hbound : intOfZ exponent ≤ intOfZ (Zsub emax1 prec1) := by
    have hcheck := hparts.2
    change (if intOfZ exponent ≤ intOfZ (Zsub emax1 prec1) then true else false) = true at hcheck
    split at hcheck
    · assumption
    · contradiction
  rw [ieee_manual_sub_int] at hbound
  have hprecision : intOfZ prec1 ≤ intOfZ prec2 := precision_le
  have hmaximum : intOfZ emax1 ≤ intOfZ emax2 := maximum_le
  let target := fexp prec2 emax2 (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent)
  have hsmall : Zle target exponent := by
    change intOfZ (fexp prec2 emax2 (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent)) ≤ intOfZ exponent
    rw [ieee_manual_fexp_int, ieee_manual_add_int]
    omega
  have halign := ieee_manual_align_exponent mantissa exponent target hsmall
  change (BinarySingleNaN.shl_align_fexp (prec := prec2) (emax := emax2) mantissa exponent).2 = target at halign
  have hmagnitude := ieee_manual_align_magnitude prec2 emax2 mantissa exponent
  generalize haligned : BinarySingleNaN.shl_align_fexp (prec := prec2) (emax := emax2) mantissa exponent = aligned
  rcases aligned with ⟨result_mantissa, result_exponent⟩
  rw [haligned] at halign hmagnitude
  dsimp only at halign hmagnitude ⊢
  have hresult_canonical : fexp prec2 emax2
      (Zadd (Zpos (Digits.digits2_pos result_mantissa)) result_exponent) = result_exponent := by
    rw [hmagnitude]
    exact halign.symm
  have hresult_bound : Zle result_exponent (Zsub emax2 prec2) := by
    rw [halign]
    change intOfZ (fexp prec2 emax2 (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent)) ≤
      intOfZ (Zsub emax2 prec2)
    rw [ieee_manual_fexp_int, ieee_manual_add_int, ieee_manual_sub_int]
    have hprecision_positive : (0 : Int) < intOfZ prec2 := FLX.prec_gt_0 prec2
    have hmaximum_positive : intOfZ prec2 < intOfZ emax2 := BinarySingleNaN.prec_lt_emax
    omega
  have hround : BinarySingleNaN.binary_round (prec := prec2) (emax := emax2)
      rounding sign mantissa exponent = BinarySingleNaN.S754_finite sign result_mantissa result_exponent := by
    unfold BinarySingleNaN.binary_round
    rw [haligned]
    exact ieee_manual_round_canonical rounding sign result_mantissa result_exponent hresult_canonical hresult_bound
  cases sign with
  | false =>
    unfold Binary.binary_normalize
    apply ieee_manual_lift_finite
    change BinarySingleNaN.SF2B
      (BinarySingleNaN.binary_round (prec := prec2) (emax := emax2) rounding false mantissa exponent) = _
    rw [hround]
    rfl
  | true =>
    have hnegative : Zaux.cond_Zopp true (Zpos mantissa) = Zneg mantissa := by
      apply intOfZ_injective
      change intOfZ (zOfInt (-(posToNat mantissa : Int))) = -(posToNat mantissa : Int)
      exact intOfZ_zOfInt _
    rw [hnegative]
    unfold Binary.binary_normalize
    apply ieee_manual_lift_finite
    change BinarySingleNaN.SF2B
      (BinarySingleNaN.binary_round (prec := prec2) (emax := emax2) rounding true mantissa exponent) = _
    rw [hround]
    rfl

theorem ZofB_Bconv :
    ∀ {prec1 emax1 prec2 emax2 : Z} [Prec_gt_0 prec1] [Prec_gt_0 prec2]
      [Prec_lt_emax prec2 emax2] [Binary.BinaryNormalizeCertificate prec2 emax2],
      ZofB_BconvStatement (prec1 := prec1) (emax1 := emax1) (prec2 := prec2) (emax2 := emax2) := by
  intro prec1 emax1 prec2 emax2 precision1_gt precision2_gt maximum2_gt certificate
    precision_le maximum_le nan rounding value integer hconvert
  rcases value with ⟨value, hvalid⟩
  cases value with
  | B754_zero sign => exact hconvert
  | B754_infinity sign => contradiction
  | B754_nan sign payload => contradiction
  | B754_finite sign mantissa exponent =>
    have hnormalize := ieee_manual_widen_core precision_le maximum_le rounding sign mantissa exponent hvalid
    change ZofB (Binary.binary_normalize rounding (Zaux.cond_Zopp sign (Zpos mantissa)) exponent sign) = some integer
    rw [hnormalize]
    rw [ieee_manual_zofb_nat] at hconvert ⊢
    have htrunc := ieee_manual_align_trunc mantissa exponent
      (fexp prec2 emax2 (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent))
    change ieee_manual_nat_trunc
      (posToNat (BinarySingleNaN.shl_align_fexp (prec := prec2) (emax := emax2) mantissa exponent).1)
      (intOfZ (BinarySingleNaN.shl_align_fexp (prec := prec2) (emax := emax2) mantissa exponent).2) =
        ieee_manual_nat_trunc (posToNat mantissa) (intOfZ exponent) at htrunc
    rw [htrunc]
    exact hconvert

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Foundation.Numbers.Rocq.Coq (intOfZ)

theorem ZofB_range_Bconv :
    ∀ {prec1 emax1 prec2 emax2 : Z} [Prec_gt_0 prec1] [Prec_gt_0 prec2]
      [Prec_lt_emax prec2 emax2] [Binary.BinaryNormalizeCertificate prec2 emax2],
      ZofB_range_BconvStatement (prec1 := prec1) (emax1 := emax1) (prec2 := prec2) (emax2 := emax2) := by
  intro prec1 emax1 prec2 emax2 precision1_gt precision2_gt maximum2_gt certificate
    minimum1 maximum1 minimum2 maximum2 precision_le maximum_le minimum_bound maximum_bound
    nan rounding value integer hconvert
  obtain ⟨hlower, hupper, hvalue⟩ := ZofB_range_inversion value minimum1 maximum1 integer hconvert
  have hconversion := ZofB_Bconv precision_le maximum_le nan rounding value integer hvalue
  have hlower_test : Zle_bool minimum2 integer = true := by
    change (if intOfZ minimum2 ≤ intOfZ integer then true else false) = true
    exact if_pos (Int.le_trans minimum_bound hlower)
  have hupper_test : Zle_bool integer maximum2 = true := by
    change (if intOfZ integer ≤ intOfZ maximum2 then true else false) = true
    exact if_pos (Int.le_trans hupper maximum_bound)
  unfold ZofB_range
  rw [hconversion]
  change (if Zle_bool minimum2 integer && Zle_bool integer maximum2 then some integer else none) = some integer
  rw [hlower_test, hupper_test]
  rfl

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra.ManualValidity

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Flocq.IEEE754.Binary
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private def binary_width : Z → Nat
  | .Z0 => 0
  | .Zpos mantissa | .Zneg mantissa => Digits.digits2_Pnat mantissa + 1

private theorem binary_width_digits (value : Z) :
    intOfZ (Digits.Zdigits2 value) = (binary_width value : Int) := by
  have positiveWidth (mantissa : positive) :
      intOfZ (Zpos (BinarySingleNaN.digits2_pos mantissa)) =
        (Digits.digits2_Pnat mantissa + 1 : Nat) := by
    have digits := congrArg intOfZ ((Digits.Z_of_nat_S_digits2_Pnat mantissa).trans
      (Digits.Zpos_digits2_pos mantissa).symm)
    change intOfZ (zOfInt (Int.ofNat (Digits.digits2_Pnat mantissa + 1))) = _ at digits
    rw [intOfZ_zOfInt] at digits
    exact digits.symm
  cases value with
  | Z0 => rfl
  | Zpos mantissa => exact positiveWidth mantissa
  | Zneg mantissa => exact positiveWidth mantissa

private theorem binary_width_zero (value : Z) : binary_width value = 0 ↔ value = Z0 := by
  cases value <;> simp [binary_width]

private theorem binary_width_shr_one (record : shr_record)
    (nonnegative : Zle Z0 (shr_m record)) :
    binary_width (shr_m (shr_1 record)) = binary_width (shr_m record) - 1 := by
  rcases record with ⟨mantissa, roundBit, stickyBit⟩
  cases mantissa with
  | Z0 => rfl
  | Zpos mantissa =>
      cases mantissa <;> simp [shr_m, shr_1,
        Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shr_1, binary_width, Digits.digits2_Pnat]
  | Zneg mantissa =>
      change (0 : Int) ≤ -(posToNat mantissa : Int) at nonnegative
      have positiveMantissa := posToNat_positive mantissa
      omega

private theorem binary_width_shr_iter (record : shr_record) (count : Nat)
    (nonnegative : Zle Z0 (shr_m record)) :
    Zle Z0 (shr_m (Zaux.iter_nat shr_1 count record)) ∧
      binary_width (shr_m (Zaux.iter_nat shr_1 count record)) =
        binary_width (shr_m record) - count := by
  induction count generalizing record with
  | zero => exact ⟨nonnegative, rfl⟩
  | succ count inductionHypothesis =>
      change Zle Z0 (shr_m (Zaux.iter_nat shr_1 count (shr_1 record))) ∧ _
      have stepNonnegative := (BinarySingleNaN.le_shr1_le record nonnegative).1
      have next := inductionHypothesis (shr_1 record) stepNonnegative
      constructor
      · exact next.1
      · change binary_width (shr_m (Zaux.iter_nat shr_1 count (shr_1 record))) = _
        rw [next.2, binary_width_shr_one record nonnegative]
        omega

private theorem binary_width_monotone (left right : Z)
    (nonnegative : Zle Z0 left) (ordered : Zle left right) :
    binary_width left ≤ binary_width right := by
  apply Classical.byContradiction
  intro reversed
  have digitOrder : Zlt (Digits.Zdigits2 right) (Digits.Zdigits2 left) := by
    change intOfZ _ < intOfZ _
    rw [binary_width_digits, binary_width_digits]
    omega
  rw [Digits.Zdigits2_Zdigits, Digits.Zdigits2_Zdigits] at digitOrder
  have lower := Digits.Zpower_le_Zdigits radix2 (Digits.Zdigits radix2 right) left digitOrder
  have upper := Digits.Zpower_gt_Zdigits radix2 (Digits.Zdigits radix2 right) right
    (by exact Int.le_refl _)
  change intOfZ _ ≤ intOfZ (Zabs left) at lower
  change intOfZ (Zabs right) < intOfZ _ at upper
  change (0 : Int) ≤ intOfZ left at nonnegative
  change intOfZ left ≤ intOfZ right at ordered
  have rightNonnegative : (0 : Int) ≤ intOfZ right := by omega
  have absoluteLeft : intOfZ (Zabs left) = intOfZ left := by
    change intOfZ (zOfInt (intOfZ left).natAbs) = _
    rw [intOfZ_zOfInt]
    exact Int.natAbs_of_nonneg nonnegative
  have absoluteRight : intOfZ (Zabs right) = intOfZ right := by
    change intOfZ (zOfInt (intOfZ right).natAbs) = _
    rw [intOfZ_zOfInt]
    exact Int.natAbs_of_nonneg rightNonnegative
  rw [absoluteLeft] at lower
  rw [absoluteRight] at upper
  omega

private theorem binary_fexp_integer (prec emax exponent : Z) :
    intOfZ (fexp0 prec emax exponent) =
      max (intOfZ exponent - intOfZ prec) (intOfZ (emin0 prec emax)) := by
  change intOfZ (ZArith.BinInt.Z.max (Zsub exponent prec) (emin0 prec emax)) = _
  unfold ZArith.BinInt.Z.max
  split
  · rename_i ordered
    simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] at ordered
    exact (Int.max_eq_right ordered).symm
  · rename_i ordered
    simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] at ordered ⊢
    exact (Int.max_eq_left (by omega)).symm

private theorem binary_shr_fexp_canonical {prec emax : Z} [FLX.Prec_gt_0 prec]
    (mantissa exponent : Z) (position : location)
    (nonnegative : Zle Z0 mantissa)
    (aligned : Zle exponent (fexp0 prec emax (Zadd (Digits.Zdigits2 mantissa) exponent))) :
    let output := BinarySingleNaN.shr_fexp (prec := prec) (emax := emax) mantissa exponent position
    Zle Z0 (shr_m output.1) ∧
      fexp0 prec emax (Zadd (Digits.Zdigits2 (shr_m output.1)) output.2) = output.2 := by
  have positivePrecision := FLX.prec_gt_0 prec
  change (0 : Int) < intOfZ prec at positivePrecision
  have inputDigits := binary_width_digits mantissa
  have inputFormat := binary_fexp_integer prec emax (Zadd (Digits.Zdigits2 mantissa) exponent)
  simp only [Zadd, ZArith.BinInt.Z.add, intOfZ_zOfInt, inputDigits] at inputFormat
  change intOfZ exponent ≤ intOfZ _ at aligned
  have recordMantissa := BinarySingleNaN.shr_m_shr_record_of_loc mantissa position
  change shr_m (shr_record_of_loc mantissa position) = mantissa at recordMantissa
  have recordNonnegative : Zle Z0 (shr_m (shr_record_of_loc mantissa position)) := by
    rw [recordMantissa]
    exact nonnegative
  change
    let output := shr (shr_record_of_loc mantissa position) exponent
      (Zsub (fexp0 prec emax (Zadd (Digits.Zdigits2 mantissa) exponent)) exponent)
    Zle Z0 (shr_m output.1) ∧
      fexp0 prec emax (Zadd (Digits.Zdigits2 (shr_m output.1)) output.2) = output.2
  dsimp only
  cases shiftAmount : Zsub (fexp0 prec emax (Zadd (Digits.Zdigits2 mantissa) exponent)) exponent with
  | Z0 =>
      change Zle Z0 (shr_m (shr_record_of_loc mantissa position)) ∧ _
      constructor
      · exact recordNonnegative
      · change fexp0 prec emax
          (Zadd (Digits.Zdigits2 (shr_m (shr_record_of_loc mantissa position))) exponent) = exponent
        rw [recordMantissa]
        apply intOfZ_injective
        have zeroShift := congrArg intOfZ shiftAmount
        simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] at zeroShift
        change _ - intOfZ exponent = 0 at zeroShift
        omega
  | Zneg count =>
      have negativeShift := congrArg intOfZ shiftAmount
      simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] at negativeShift
      change _ - intOfZ exponent = -(posToNat count : Int) at negativeShift
      have countPositive := posToNat_positive count
      omega
  | Zpos count =>
      have countNonnegative : Zle Z0 (Zpos count) := by
        change (0 : Int) ≤ (posToNat count : Int)
        omega
      have shifted := BinarySingleNaN.shr_nat (shr_record_of_loc mantissa position)
        exponent (Zpos count) countNonnegative
      change shr (shr_record_of_loc mantissa position) exponent (Zpos count) =
        (Zaux.iter_nat shr_1 (posToNat count) (shr_record_of_loc mantissa position),
          Zadd exponent (Zpos count)) at shifted
      rw [shifted]
      have iteration := binary_width_shr_iter (shr_record_of_loc mantissa position)
        (posToNat count) recordNonnegative
      constructor
      · exact iteration.1
      · apply intOfZ_injective
        rw [binary_fexp_integer]
        simp only [Zadd, ZArith.BinInt.Z.add, intOfZ_zOfInt, binary_width_digits]
        have widthOutput := iteration.2
        rw [recordMantissa] at widthOutput
        have positiveShift := congrArg intOfZ shiftAmount
        simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] at positiveShift
        change _ - intOfZ exponent = (posToNat count : Int) at positiveShift
        have outputEquation :
            max ((binary_width mantissa : Int) + intOfZ exponent - intOfZ prec)
                (intOfZ (emin0 prec emax)) - intOfZ exponent = (posToNat count : Int) := by
          rw [← inputFormat]
          simpa only [Zadd, ZArith.BinInt.Z.add, intOfZ_zOfInt, inputDigits] using positiveShift
        change max ((binary_width (shr_m (Zaux.iter_nat shr_1 (posToNat count)
          (shr_record_of_loc mantissa position))) : Int) +
          (intOfZ exponent + (posToNat count : Int)) - intOfZ prec)
          (intOfZ (emin0 prec emax)) = intOfZ exponent + (posToNat count : Int)
        rw [widthOutput]
        simp only [Int.max_def] at outputEquation ⊢
        split at outputEquation <;> split <;> omega

private theorem binary_choice_increases (rounding : BinarySingleNaN.mode)
    (sign : Bool) (mantissa : Z) (position : location) :
    Zle mantissa (BinarySingleNaN.choice_mode rounding sign mantissa position) := by
  have incremented (increment : Bool) :
      Zle mantissa (CompCert4Lean.Flocq.Calc.Round.cond_incr increment mantissa) := by
    cases increment
    · exact Int.le_refl _
    · change intOfZ mantissa ≤ intOfZ (Zadd mantissa Zone)
      simp only [Zadd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
      change intOfZ mantissa ≤ intOfZ mantissa + 1
      omega
  cases rounding with
  | mode_NE => exact incremented _
  | mode_ZR => exact Int.le_refl _
  | mode_DN => exact incremented _
  | mode_UP => exact incremented _
  | mode_NA => exact incremented _

private theorem binary_fexp_mantissa_monotone (prec emax exponent left right : Z)
    (nonnegative : Zle Z0 left) (ordered : Zle left right) :
    Zle (fexp0 prec emax (Zadd (Digits.Zdigits2 left) exponent))
      (fexp0 prec emax (Zadd (Digits.Zdigits2 right) exponent)) := by
  have widthOrder := binary_width_monotone left right nonnegative ordered
  change intOfZ _ ≤ intOfZ _
  rw [binary_fexp_integer, binary_fexp_integer]
  simp only [Zadd, ZArith.BinInt.Z.add, intOfZ_zOfInt, binary_width_digits]
  simp only [Int.max_def]
  split <;> split <;> omega

private theorem binary_round_aux_valid {prec emax : Z}
    [FLX.Prec_gt_0 prec] [BinarySingleNaN.Prec_lt_emax prec emax]
    (rounding : BinarySingleNaN.mode) (sign : Bool) (mantissa exponent : Z)
    (position : location) (nonnegative : Zle Z0 mantissa)
    (aligned : Zle exponent (fexp0 prec emax (Zadd (Digits.Zdigits2 mantissa) exponent))) :
    BinarySingleNaN.valid_binary0 prec emax
      (BinarySingleNaN.binary_round_aux (prec := prec) (emax := emax)
        rounding sign mantissa exponent position) = true := by
  let first := BinarySingleNaN.shr_fexp (prec := prec) (emax := emax) mantissa exponent position
  have firstValid := binary_shr_fexp_canonical (prec := prec) (emax := emax)
    mantissa exponent position nonnegative aligned
  change Zle Z0 (shr_m first.1) ∧
    fexp0 prec emax (Zadd (Digits.Zdigits2 (shr_m first.1)) first.2) = first.2 at firstValid
  let rounded := BinarySingleNaN.choice_mode rounding sign (shr_m first.1) (loc_of_shr_record first.1)
  have increased := binary_choice_increases rounding sign (shr_m first.1) (loc_of_shr_record first.1)
  have roundedNonnegative : Zle Z0 rounded := Int.le_trans firstValid.1 increased
  have roundedAligned : Zle first.2
      (fexp0 prec emax (Zadd (Digits.Zdigits2 rounded) first.2)) := by
    have monotone := binary_fexp_mantissa_monotone prec emax first.2
      (shr_m first.1) rounded firstValid.1 increased
    rw [firstValid.2] at monotone
    exact monotone
  let second := BinarySingleNaN.shr_fexp (prec := prec) (emax := emax) rounded first.2 loc_Exact
  have secondValid := binary_shr_fexp_canonical (prec := prec) (emax := emax)
    rounded first.2 loc_Exact roundedNonnegative roundedAligned
  change Zle Z0 (shr_m second.1) ∧
    fexp0 prec emax (Zadd (Digits.Zdigits2 (shr_m second.1)) second.2) = second.2 at secondValid
  change BinarySingleNaN.valid_binary0 prec emax (match shr_m second.1 with
    | .Z0 => S754_zero sign
    | .Zpos result => BinarySingleNaN.binary_fit_aux (prec := prec) (emax := emax) rounding sign result second.2
    | .Zneg _ => S754_nan) = true
  cases resultMantissa : shr_m second.1 with
  | Z0 => rfl
  | Zneg result => rfl
  | Zpos result =>
      change BinarySingleNaN.valid_binary0 prec emax
        (BinarySingleNaN.binary_fit_aux (prec := prec) (emax := emax)
          rounding sign result second.2) = true
      have canonical := secondValid.2
      rw [resultMantissa] at canonical
      have canonicalBool : canonical_mantissa0 prec emax result second.2 = true := by
        change ZArith.Zbool.Zeq_bool
          (fexp0 prec emax (Zadd (Digits.Zdigits2 (Zpos result)) second.2)) second.2 = true
        rw [canonical]
        simp [ZArith.Zbool.Zeq_bool]
      unfold BinarySingleNaN.binary_fit_aux
      split
      · rename_i exponentBound
        exact Bool.and_eq_true_iff.mpr ⟨canonicalBool, exponentBound⟩
      · exact BinarySingleNaN.binary_overflow_correct rounding sign

private theorem binary_width_shift_nat (mantissa : positive) (count : Nat) :
    binary_width (Zpos (PArith.BinPos.Pos.shiftl_nat mantissa count)) =
      binary_width (Zpos mantissa) + count := by
  induction count with
  | zero => simp [PArith.BinPos.Pos.shiftl_nat, posOfNat_posToNat]
  | succ count inductionHypothesis =>
      have nextShift : PArith.BinPos.Pos.shiftl_nat mantissa (count + 1) =
          .xO (PArith.BinPos.Pos.shiftl_nat mantissa count) := by
        apply posToNat_injective
        change posToNat (posOfNat (posToNat mantissa * 2 ^ (count + 1))) =
          2 * posToNat (posOfNat (posToNat mantissa * 2 ^ count))
        rw [posToNat_posOfNat (Nat.mul_pos (posToNat_positive mantissa) (Nat.two_pow_pos _)),
          posToNat_posOfNat (Nat.mul_pos (posToNat_positive mantissa) (Nat.two_pow_pos _))]
        rw [Nat.pow_succ, ← Nat.mul_assoc]
        omega
      rw [nextShift]
      change binary_width (Zpos (PArith.BinPos.Pos.shiftl_nat mantissa count)) + 1 =
        binary_width (Zpos mantissa) + (count + 1)
      rw [inductionHypothesis]
      omega

private theorem binary_shl_align_aligned (prec emax : Z) (mantissa : positive) (exponent : Z) :
    let output := BinarySingleNaN.shl_align_fexp (prec := prec) (emax := emax) mantissa exponent
    Zle output.2 (fexp0 prec emax (Zadd (Digits.Zdigits2 (Zpos output.1)) output.2)) := by
  let target := fexp0 prec emax (Zadd (Digits.Zdigits2 (Zpos mantissa)) exponent)
  have shape : BinarySingleNaN.shl_align_fexp (prec := prec) (emax := emax) mantissa exponent =
    (match Zsub target exponent with
      | .Zneg count => (ZArith.Zpower.shift_pos count mantissa, target)
      | _ => (mantissa, exponent)) := rfl
  dsimp only
  rw [shape]
  cases shiftAmount : Zsub target exponent with
  | Z0 =>
      change intOfZ exponent ≤ intOfZ target
      have integerShift := congrArg intOfZ shiftAmount
      simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] at integerShift
      change intOfZ target - intOfZ exponent = 0 at integerShift
      omega
  | Zpos count =>
      change intOfZ exponent ≤ intOfZ target
      have integerShift := congrArg intOfZ shiftAmount
      simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] at integerShift
      change intOfZ target - intOfZ exponent = (posToNat count : Int) at integerShift
      omega
  | Zneg count =>
      change Zle target (fexp0 prec emax
        (Zadd (Digits.Zdigits2 (Zpos (ZArith.Zpower.shift_pos count mantissa))) target))
      have preservedMagnitude :
          Zadd (Digits.Zdigits2 (Zpos (ZArith.Zpower.shift_pos count mantissa))) target =
          Zadd (Digits.Zdigits2 (Zpos mantissa)) exponent := by
        apply intOfZ_injective
        simp only [Zadd, ZArith.BinInt.Z.add, intOfZ_zOfInt, binary_width_digits]
        have shiftedWidth := binary_width_shift_nat mantissa (posToNat count)
        change binary_width (Zpos (ZArith.Zpower.shift_pos count mantissa)) =
          binary_width (Zpos mantissa) + posToNat count at shiftedWidth
        rw [shiftedWidth]
        have integerShift := congrArg intOfZ shiftAmount
        simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] at integerShift
        change intOfZ target - intOfZ exponent = -(posToNat count : Int) at integerShift
        omega
      rw [preservedMagnitude]
      exact Int.le_refl _

private theorem binary_round_valid {prec emax : Z}
    [FLX.Prec_gt_0 prec] [BinarySingleNaN.Prec_lt_emax prec emax]
    (rounding : BinarySingleNaN.mode) (sign : Bool) (mantissa : positive) (exponent : Z) :
    BinarySingleNaN.valid_binary0 prec emax
      (BinarySingleNaN.binary_round (prec := prec) (emax := emax) rounding sign mantissa exponent) = true := by
  apply binary_round_aux_valid
  · change (0 : Int) ≤ (posToNat _ : Int)
    omega
  · exact binary_shl_align_aligned prec emax mantissa exponent

private theorem binary_single_normalize_valid {prec emax : Z}
    [FLX.Prec_gt_0 prec] [BinarySingleNaN.Prec_lt_emax prec emax]
    (rounding : BinarySingleNaN.mode) (mantissa exponent : Z) (zeroSign : Bool) :
    BinarySingleNaN.BinaryFloatCertificate
      (BinarySingleNaN.binary_normalize (prec := prec) (emax := emax) rounding mantissa exponent zeroSign) := by
  cases mantissa with
  | Z0 => rfl
  | Zpos mantissa =>
      apply BinarySingleNaN.SF2BCertificateStatement_proof
      exact binary_round_valid rounding false mantissa exponent
  | Zneg mantissa =>
      apply BinarySingleNaN.SF2BCertificateStatement_proof
      exact binary_round_valid rounding true mantissa exponent

private theorem ieee_manual_normalize_valid :
    ∀ {prec emax : Z} [FLX.Prec_gt_0 prec] [BinarySingleNaN.Prec_lt_emax prec emax]
      [BinaryNormalizeCertificate prec emax],
      binary_normalize_result_obligation (prec := prec) (emax := emax) := by
  intro prec emax positivePrecision validFormat normalizeCertificate rounding mantissa exponent zeroSign
  exact BSN2B'_result_obligation_proof
    ⟨_, binary_single_normalize_valid rounding mantissa exponent zeroSign⟩
    (normalizeCertificate.is_nan_binary_normalize rounding mantissa exponent zeroSign)

end CompCert4Lean.Lib.IEEE754_extra.ManualValidity

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.IEEE754

theorem BofZ_result_obligation_proof :
    ∀ {prec emax : Z} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
      [Binary.BinaryNormalizeCertificate prec emax],
      BofZ_result_obligation (prec := prec) (emax := emax) := by
  intro prec emax precision_gt maximum_gt certificate integer
  exact ManualValidity.ieee_manual_normalize_valid mode_NE integer Z0 false

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.IEEE754

theorem Bconv_result_obligation_proof :
    ∀ {prec1 emax1 prec2 emax2 : Z} [Prec_gt_0 prec2] [Prec_lt_emax prec2 emax2]
      [Binary.BinaryNormalizeCertificate prec2 emax2],
      Bconv_result_obligation (prec1 := prec1) (emax1 := emax1)
        (prec2 := prec2) (emax2 := emax2) := by
  intro prec1 emax1 prec2 emax2 precision_gt maximum_gt certificate nan rounding value
  rcases value with ⟨value, valid⟩
  cases value with
  | B754_zero sign => rfl
  | B754_infinity sign => rfl
  | B754_nan sign payload =>
      exact Binary.build_nan_result_obligation_proof (nan (.B754_nan sign payload))
  | B754_finite sign mantissa exponent =>
      exact ManualValidity.ieee_manual_normalize_valid rounding
        (CompCert4Lean.Flocq.Core.Zaux.cond_Zopp sign (Zpos mantissa)) exponent sign

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem ieee_manual_integer_power {precision : Z} [Prec_gt_0 precision] :
    intOfZ (Zpower Ztwo precision) = (2 ^ (intOfZ precision).toNat : Nat) := by
  have hprecision : (0 : Int) < intOfZ precision := FLX.prec_gt_0 precision
  change intOfZ (if intOfZ precision < 0 then Z0 else zOfInt ((2 : Int) ^ (intOfZ precision).toNat)) = _
  rw [if_neg (by omega), intOfZ_zOfInt, Int.natCast_pow]
  rfl

private theorem ieee_manual_round_two_power {prec emax : Z}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (ctx : ExactRealContext) (sign : Bool) (mantissa : positive)
    (hboundary : intOfZ (Zpos mantissa) = intOfZ (Zpower Ztwo prec)) :
    ∃ result_mantissa result_exponent,
      BinarySingleNaN.binary_round (prec := prec) (emax := emax) mode_NE sign mantissa Z0 =
        BinarySingleNaN.S754_finite sign result_mantissa result_exponent ∧
      Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos result_mantissa) result_exponent) =
        Exact.IZR ctx (Zpos mantissa) := by
  have hprecision : (0 : Int) < intOfZ prec := FLX.prec_gt_0 prec
  have hmaximum : intOfZ prec < intOfZ emax := BinarySingleNaN.prec_lt_emax
  rw [ieee_manual_integer_power] at hboundary
  let half : positive := posOfNat (2 ^ ((intOfZ prec).toNat - 1))
  have hhalf : posToNat half = 2 ^ ((intOfZ prec).toNat - 1) :=
    posToNat_posOfNat (Nat.two_pow_pos _)
  have hdouble : mantissa = .xO half := by
    apply posToNat_injective
    have hboundary_nat : posToNat mantissa = 2 ^ (intOfZ prec).toNat := by
      change (posToNat mantissa : Int) = _ at hboundary
      exact Int.natCast_inj.mp hboundary
    rw [hboundary_nat]
    change 2 ^ (intOfZ prec).toNat = 2 * posToNat half
    calc
      2 ^ (intOfZ prec).toNat = 2 ^ (((intOfZ prec).toNat - 1) + 1) :=
        congrArg (fun power : Nat => 2 ^ power) (by omega)
      _ = 2 * posToNat half := by rw [Nat.pow_succ, hhalf, Nat.mul_comm]
  have hdigits : intOfZ (Zpos (Digits.digits2_pos half)) = intOfZ prec := by
    change (posToNat (Digits.digits2_pos half) : Int) = intOfZ prec
    rw [ieee_manual_digits_nat, hhalf, Nat.log2_two_pow]
    omega
  have htarget : fexp prec emax (Zadd (Zpos (Digits.digits2_pos mantissa)) Z0) = Zone := by
    apply intOfZ_injective
    rw [ieee_manual_fexp_int, ieee_manual_add_int]
    have hmantissa_digits : intOfZ (Zpos (Digits.digits2_pos mantissa)) = intOfZ prec + 1 := by
      rw [hdouble]
      change (posToNat (Digits.digits2_pos (.xO half)) : Int) = _
      change (posToNat (PArith.BinPos.Pos.succ (Digits.digits2_pos half)) : Int) = _
      rw [PArith.BinPos.Pos.posToNat_succ]
      change (posToNat (Digits.digits2_pos half) : Int) = intOfZ prec at hdigits
      omega
    rw [hmantissa_digits]
    change max (intOfZ prec + 1 + 0 - intOfZ prec) (3 - intOfZ emax - intOfZ prec) = 1
    omega
  have hcanonical : fexp prec emax (Zadd (Zpos (Digits.digits2_pos half)) Zone) = Zone := by
    apply intOfZ_injective
    rw [ieee_manual_fexp_int, ieee_manual_add_int, hdigits]
    change max (intOfZ prec + 1 - intOfZ prec) (3 - intOfZ emax - intOfZ prec) = 1
    omega
  have hfirst : BinarySingleNaN.shr_fexp (prec := prec) (emax := emax)
      (Zpos mantissa) Z0 BinarySingleNaN.loc_Exact =
      (BinarySingleNaN.shr_record_of_loc (Zpos half) BinarySingleNaN.loc_Exact, Zone) := by
    change BinarySingleNaN.shr
      (BinarySingleNaN.shr_record_of_loc (Zpos mantissa) BinarySingleNaN.loc_Exact) Z0
      (Zsub (fexp prec emax (Zadd (Zpos (Digits.digits2_pos mantissa)) Z0)) Z0) = _
    rw [htarget, hdouble]
    rfl
  have hsecond : BinarySingleNaN.shr_fexp (prec := prec) (emax := emax)
      (Zpos half) Zone BinarySingleNaN.loc_Exact =
      (BinarySingleNaN.shr_record_of_loc (Zpos half) BinarySingleNaN.loc_Exact, Zone) := by
    change BinarySingleNaN.shr
      (BinarySingleNaN.shr_record_of_loc (Zpos half) BinarySingleNaN.loc_Exact) Zone
      (Zsub (fexp prec emax (Zadd (Zpos (Digits.digits2_pos half)) Zone)) Zone) = _
    rw [hcanonical]
    rfl
  have halign : BinarySingleNaN.shl_align_fexp (prec := prec) (emax := emax) mantissa Z0 = (mantissa, Z0) := by
    change BinarySingleNaN.shl_align mantissa Z0
      (fexp prec emax (Zadd (Zpos (Digits.digits2_pos mantissa)) Z0)) = _
    rw [htarget]
    rfl
  refine ⟨half, Zone, ?_, ?_⟩
  · unfold BinarySingleNaN.binary_round
    rw [halign]
    dsimp only
    unfold BinarySingleNaN.binary_round_aux
    rw [hfirst]
    change (match BinarySingleNaN.shr_m (BinarySingleNaN.shr_fexp
      (prec := prec) (emax := emax) (Zpos half) Zone BinarySingleNaN.loc_Exact).1 with
      | .Z0 => BinarySingleNaN.S754_zero sign
      | .Zpos result => BinarySingleNaN.binary_fit_aux (prec := prec) (emax := emax)
        mode_NE sign result (BinarySingleNaN.shr_fexp (prec := prec) (emax := emax)
          (Zpos half) Zone BinarySingleNaN.loc_Exact).2
      | .Zneg _ => BinarySingleNaN.S754_nan) = _
    rw [hsecond]
    change (if Zle_bool Zone (Zsub emax prec) then _ else _) = _
    have hbounded : Zle_bool Zone (Zsub emax prec) = true := by
      change (if (1 : Int) ≤ intOfZ (Zsub emax prec) then true else false) = true
      rw [ieee_manual_sub_int]
      exact if_pos (by omega)
    rw [hbounded]
    rfl
  · rw [hdouble]
    change ctx.spec.mul (ctx.spec.ofZ (Zpos half)) (ctx.spec.ofZ Ztwo) = ctx.spec.ofZ (Zpos (.xO half))
    have hproduct : Zmul (Zpos half) Ztwo = Zpos (.xO half) := by
      apply intOfZ_injective
      change intOfZ (zOfInt ((posToNat half : Int) * 2)) = (2 * posToNat half : Nat)
      rw [intOfZ_zOfInt]
      omega
    rw [← hproduct]
    exact (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR ctx (Zpos half) Ztwo).symm

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem ieee_manual_round_bounded_integer {prec emax : Z}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (ctx : ExactRealContext) (sign : Bool) (mantissa : positive)
    (hbound : Zle (Zpos mantissa) (Zpower Ztwo prec)) :
    ∃ result_mantissa result_exponent,
      BinarySingleNaN.binary_round (prec := prec) (emax := emax) mode_NE sign mantissa Z0 =
        BinarySingleNaN.S754_finite sign result_mantissa result_exponent ∧
      Defs.Exact.F2R ctx (Defs.Float Zaux.radix2 (Zpos result_mantissa) result_exponent) =
        Exact.IZR ctx (Zpos mantissa) := by
  by_cases hboundary : intOfZ (Zpos mantissa) = intOfZ (Zpower Ztwo prec)
  · exact ieee_manual_round_two_power ctx sign mantissa hboundary
  have hstrict : Zlt (Zabs (Zpos mantissa)) (Zpower Ztwo prec) := by
    have habsolute : Zabs (Zpos mantissa) = Zpos mantissa :=
      ZArith.BinInt.Z.abs_eq (Zpos mantissa) (Int.natCast_nonneg _)
    rw [habsolute]
    change intOfZ (Zpos mantissa) < intOfZ (Zpower Ztwo prec)
    change intOfZ (Zpos mantissa) ≤ intOfZ (Zpower Ztwo prec) at hbound
    omega
  have hwidth : Zle (Zpos (Digits.digits2_pos mantissa)) prec := by
    change intOfZ (Zpos (Digits.digits2_pos mantissa)) ≤ intOfZ prec
    have hdigits : Zpos (Digits.digits2_pos mantissa) = Digits.Zdigits Zaux.radix2 (Zpos mantissa) :=
      Digits.Zpos_digits2_pos mantissa
    rw [hdigits]
    exact Digits.Zdigits_le_Zpower Zaux.radix2 prec (Zpos mantissa) hstrict
  change intOfZ (Zpos (Digits.digits2_pos mantissa)) ≤ intOfZ prec at hwidth
  have hprecision : (0 : Int) < intOfZ prec := FLX.prec_gt_0 prec
  have hmaximum : intOfZ prec < intOfZ emax := BinarySingleNaN.prec_lt_emax
  have hsmall : Zle (fexp prec emax (Zadd (Zpos (Digits.digits2_pos mantissa)) Z0)) Z0 := by
    change intOfZ _ ≤ 0
    rw [ieee_manual_fexp_int, ieee_manual_add_int]
    change max (intOfZ (Zpos (Digits.digits2_pos mantissa)) + 0 - intOfZ prec)
      (3 - intOfZ emax - intOfZ prec) ≤ 0
    omega
  have hupper : Zle (Zadd (Zpos (Digits.digits2_pos mantissa)) Z0) emax := by
    change intOfZ _ ≤ intOfZ emax
    rw [ieee_manual_add_int]
    change intOfZ (Zpos (Digits.digits2_pos mantissa)) + 0 ≤ intOfZ emax
    omega
  obtain ⟨result_mantissa, result_exponent, hround, _, hvalue⟩ :=
    ieee_manual_round_exact ctx mode_NE sign mantissa Z0 hsmall hupper
  refine ⟨result_mantissa, result_exponent, hround, hvalue.trans ?_⟩
  exact ctx.certificate.orderedField.mul_one _

theorem BofZ_exact :
    ∀ {prec emax : Z} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
      [Binary.BinaryNormalizeCertificate prec emax],
      BofZ_exactStatement (prec := prec) (emax := emax) := by
  intro prec emax precision_gt maximum_gt certificate ctx integer bounds
  cases integer with
  | Z0 =>
      refine ⟨?_, rfl, rfl⟩
      exact ctx.certificate.sourceLaws.ofZ_zero.symm
  | Zpos mantissa =>
      obtain ⟨result_mantissa, result_exponent, hround, hvalue⟩ :=
        ieee_manual_round_bounded_integer (prec := prec) (emax := emax) ctx false mantissa bounds.2
      have hnormalized : BofZ (prec := prec) (emax := emax) (Zpos mantissa) =
          Binary.B754_finite false result_mantissa result_exponent := by
        apply ieee_manual_lift_finite
        change BinarySingleNaN.SF2B (prec := prec) (emax := emax)
          (BinarySingleNaN.binary_round (prec := prec) (emax := emax) mode_NE false mantissa Z0) = _
        rw [hround]
        rfl
      change Exact.B2R ctx (BofZ (prec := prec) (emax := emax) (Zpos mantissa)) =
          Exact.IZR ctx (Zpos mantissa) ∧
        Binary.is_finite (BofZ (prec := prec) (emax := emax) (Zpos mantissa)) = true ∧
        Binary.Bsign (BofZ (prec := prec) (emax := emax) (Zpos mantissa)) = Zlt_bool (Zpos mantissa) Z0
      rw [hnormalized]
      refine ⟨hvalue, rfl, ?_⟩
      change false = (if (posToNat mantissa : Int) < 0 then true else false)
      simp
  | Zneg mantissa =>
      have hbound : Zle (Zpos mantissa) (Zpower Ztwo prec) := by
        have hlower := bounds.1
        change intOfZ (Zopp (Zpower Ztwo prec)) ≤ -(posToNat mantissa : Int) at hlower
        simp only [Zopp, ZArith.BinInt.Z.opp, intOfZ_zOfInt] at hlower
        change (posToNat mantissa : Int) ≤ intOfZ (Zpower Ztwo prec)
        omega
      obtain ⟨result_mantissa, result_exponent, hround, hvalue⟩ :=
        ieee_manual_round_bounded_integer (prec := prec) (emax := emax) ctx true mantissa hbound
      have hnormalized : BofZ (prec := prec) (emax := emax) (Zneg mantissa) =
          Binary.B754_finite true result_mantissa result_exponent := by
        apply ieee_manual_lift_finite
        change BinarySingleNaN.SF2B (prec := prec) (emax := emax)
          (BinarySingleNaN.binary_round (prec := prec) (emax := emax) mode_NE true mantissa Z0) = _
        rw [hround]
        rfl
      change Exact.B2R ctx (BofZ (prec := prec) (emax := emax) (Zneg mantissa)) =
          Exact.IZR ctx (Zneg mantissa) ∧
        Binary.is_finite (BofZ (prec := prec) (emax := emax) (Zneg mantissa)) = true ∧
        Binary.Bsign (BofZ (prec := prec) (emax := emax) (Zneg mantissa)) = Zlt_bool (Zneg mantissa) Z0
      rw [hnormalized]
      refine ⟨?_, rfl, ?_⟩
      · change Defs.Exact.F2R ctx
          (Defs.Float Zaux.radix2 (Zopp (Zpos result_mantissa)) result_exponent) =
          Exact.IZR ctx (Zneg mantissa)
        have hnegative : Defs.Exact.F2R ctx
            (Defs.Float Zaux.radix2 (Zopp (Zpos result_mantissa)) result_exponent) =
            Exact.Ropp ctx (Defs.Exact.F2R ctx
              (Defs.Float Zaux.radix2 (Zpos result_mantissa) result_exponent)) :=
          Float_prop.F2R_Zopp ctx Zaux.radix2 (Zpos result_mantissa) result_exponent
        rw [hnegative, hvalue]
        have hopp : Zopp (Zpos mantissa) = Zneg mantissa := by
          apply intOfZ_injective
          simp only [Zopp, ZArith.BinInt.Z.opp, intOfZ_zOfInt]
          rfl
        have hcast : Exact.IZR ctx (Zopp (Zpos mantissa)) =
            Exact.Ropp ctx (Exact.IZR ctx (Zpos mantissa)) :=
          CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.opp_IZR ctx (Zpos mantissa)
        rw [hopp] at hcast
        exact hcast.symm
      · change true = (if -(posToNat mantissa : Int) < 0 then true else false)
        rw [if_pos (by have hpositive := posToNat_positive mantissa; omega)]

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN.IEEEManualRounding

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private def manual_shift_encoding (record : shr_record) : Int :=
  2 * intOfZ (shr_m record) + if shr_r record then 1 else 0

private theorem manual_shift_encoding_step (record : shr_record)
    (nonnegative : Zle Z0 (shr_m record)) :
    manual_shift_encoding (shr_1 record) = manual_shift_encoding record / 2 := by
  rcases record with ⟨mantissa, rounding, sticky⟩
  cases mantissa with
  | Z0 => cases rounding <;> rfl
  | Zpos mantissa =>
      cases mantissa <;> cases rounding <;>
        simp [manual_shift_encoding, shr_1, Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shr_1,
          shr_m, shr_r, intOfZ, posToNat] <;> omega
  | Zneg mantissa =>
      change (0 : Int) ≤ -(posToNat mantissa : Int) at nonnegative
      have positive := posToNat_positive mantissa
      omega

private theorem manual_shift_sticky_step (record : shr_record)
    (nonnegative : Zle Z0 (shr_m record)) :
    (shr_1 record).shr_s = false ↔
      manual_shift_encoding record % 2 = 0 ∧ record.shr_s = false := by
  rcases record with ⟨mantissa, rounding, sticky⟩
  cases mantissa with
  | Z0 => cases rounding <;> cases sticky <;> decide
  | Zpos mantissa =>
      cases mantissa <;> cases rounding <;> cases sticky <;>
        simp [manual_shift_encoding, shr_1, Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shr_1,
          shr_m, shr_r, intOfZ, posToNat] <;> omega
  | Zneg mantissa =>
      change (0 : Int) ≤ -(posToNat mantissa : Int) at nonnegative
      have positive := posToNat_positive mantissa
      omega

private theorem manual_mod_product (value divisor : Int) :
    value % (divisor * 2) = 0 ↔ value % divisor = 0 ∧ value / divisor % 2 = 0 := by
  constructor
  · intro divisible
    have productDivides := Int.dvd_of_emod_eq_zero divisible
    exact ⟨Int.emod_eq_zero_of_dvd (Int.dvd_trans (Int.dvd_mul_right divisor 2) productDivides),
      Int.emod_eq_zero_of_dvd (Int.dvd_ediv_of_mul_dvd productDivides)⟩
  · rintro ⟨first, second⟩
    exact Int.emod_eq_zero_of_dvd (Int.mul_dvd_of_dvd_ediv
      (Int.dvd_of_emod_eq_zero first) (Int.dvd_of_emod_eq_zero second))

private theorem manual_iter_encoding (count : Nat) (record : shr_record)
    (nonnegative : Zle Z0 (shr_m record)) :
    Zle Z0 (shr_m (Zaux.iter_nat shr_1 count record)) ∧
      manual_shift_encoding (Zaux.iter_nat shr_1 count record) =
        manual_shift_encoding record / (2 : Int) ^ count ∧
      ((Zaux.iter_nat shr_1 count record).shr_s = false ↔
        manual_shift_encoding record % (2 : Int) ^ count = 0 ∧ record.shr_s = false) := by
  induction count with
  | zero => simpa [Zaux.iter_nat] using nonnegative
  | succ count induction =>
      have iteration : Zaux.iter_nat shr_1 (count + 1) record =
          shr_1 (Zaux.iter_nat shr_1 count record) :=
        Zaux.iter_nat_S shr_1 count record
      rw [iteration]
      refine ⟨(le_shr1_le _ induction.1).1, ?_, ?_⟩
      · rw [manual_shift_encoding_step _ induction.1, induction.2.1]
        rw [Int.ediv_ediv_of_nonneg (Int.pow_nonneg (by decide)), Int.pow_succ]
      · rw [manual_shift_sticky_step _ induction.1, induction.2.1, induction.2.2,
          Int.pow_succ, manual_mod_product]
        simp only [and_assoc, and_left_comm]

private theorem manual_record_ext (first second : shr_record)
    (encoding : manual_shift_encoding first = manual_shift_encoding second)
    (sticky : first.shr_s = false ↔ second.shr_s = false) : first = second := by
  rcases first with ⟨firstMantissa, firstRound, firstSticky⟩
  rcases second with ⟨secondMantissa, secondRound, secondSticky⟩
  have stickyEqual : firstSticky = secondSticky := by
    cases firstSticky <;> cases secondSticky <;> simp_all
  subst secondSticky
  change 2 * intOfZ firstMantissa + (if firstRound then 1 else 0) =
    2 * intOfZ secondMantissa + (if secondRound then 1 else 0) at encoding
  cases firstRound <;> cases secondRound <;> simp only [Bool.false_eq_true, if_false, if_true] at encoding
  · have mantissaEqual : firstMantissa = secondMantissa := intOfZ_injective (by omega)
    subst secondMantissa
    rfl
  · omega
  · omega
  · have mantissaEqual : firstMantissa = secondMantissa := intOfZ_injective (by omega)
    subst secondMantissa
    rfl

private def manual_location (half remainder : Int) (rounding sticky : Bool) : location :=
  if remainder = 0 then
    if rounding || sticky then loc_Inexact Lt else loc_Exact
  else if remainder < half then loc_Inexact Lt
  else if remainder = half then
    if rounding || sticky then loc_Inexact Gt else loc_Inexact Eq
  else loc_Inexact Gt

private theorem manual_location_formula (half remainder : Int)
    (mantissa : Z) (rounding sticky : Bool) :
    new_location (zOfInt (2 * half)) (zOfInt remainder)
      (loc_of_shr_record ⟨mantissa, rounding, sticky⟩) =
      manual_location half remainder rounding sticky := by
  have even : Calc.Bracket.Zeven (zOfInt (2 * half)) = true := by
    change decide (Int.natAbs (intOfZ (zOfInt (2 * half))) % 2 = 0) = true
    simp [intOfZ_zOfInt, Int.natAbs_mul, Nat.mul_mod]
  have zeroEquivalence : zOfInt remainder = (Z0 : Z) ↔ remainder = 0 := by
    constructor
    · intro equal
      have equality := congrArg intOfZ equal
      rw [intOfZ_zOfInt] at equality
      exact equality
    · intro equal
      subst remainder
      rfl
  have comparisonValue : Calc.Bracket.Zcompare
      (Calc.Bracket.Zmul Calc.Bracket.Ztwo (zOfInt remainder)) (zOfInt (2 * half)) =
      if remainder < half then Lt else if remainder = half then Eq else Gt := by
    change (if intOfZ (zOfInt (2 * intOfZ (zOfInt remainder))) < intOfZ (zOfInt (2 * half)) then Lt
      else if intOfZ (zOfInt (2 * intOfZ (zOfInt remainder))) = intOfZ (zOfInt (2 * half)) then Eq else Gt) = _
    simp only [intOfZ_zOfInt]
    have less : 2 * remainder < 2 * half ↔ remainder < half := by omega
    have equal : 2 * remainder = 2 * half ↔ remainder = half := by omega
    simp only [less, equal]
  unfold new_location Calc.Bracket.new_location
  rw [even]
  simp only [if_true]
  unfold Calc.Bracket.new_location_even
  rw [comparisonValue]
  simp only [Calc.Bracket.Zeq_bool, Zaux.Zeq_bool, ZArith.Zbool.Zeq_bool,
    zeroEquivalence, decide_eq_true_eq]
  by_cases zero : remainder = 0 <;> by_cases less : remainder < half <;>
    by_cases equal : remainder = half <;> cases rounding <;> cases sticky <;>
    simp [manual_location, zero, less, equal, loc_of_shr_record,
      Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.loc_of_shr_record]

private theorem manual_encoded_division (mantissa divisor bit : Int)
    (nonzero : divisor ≠ 0) :
    (2 * mantissa + bit) / divisor =
        2 * (mantissa / divisor) + (2 * (mantissa % divisor) + bit) / divisor ∧
      (2 * mantissa + bit) % divisor = (2 * (mantissa % divisor) + bit) % divisor := by
  have decomposition : 2 * mantissa + bit =
      (2 * (mantissa % divisor) + bit) + divisor * (2 * (mantissa / divisor)) := by
    calc
      2 * mantissa + bit = 2 * (mantissa % divisor + divisor * (mantissa / divisor)) + bit :=
        congrArg (fun value => 2 * value + bit) (Int.emod_add_mul_ediv mantissa divisor).symm
      _ = _ := by
        simp only [Int.mul_add, Int.mul_left_comm 2 divisor]
        omega
  rw [decomposition, Int.add_mul_ediv_left _ _ nonzero, Int.add_mul_emod_self_left]
  exact ⟨Int.add_comm _ _, rfl⟩

private theorem manual_result_encoding (mantissa half : Int) (positive : 0 < half)
    (rounding sticky : Bool) :
    let result := shr_record_of_loc (zOfInt (mantissa / (2 * half)))
      (manual_location half (mantissa % (2 * half)) rounding sticky)
    manual_shift_encoding result =
        (2 * mantissa + if rounding then 1 else 0) / (2 * half) ∧
      (result.shr_s = false ↔
        (2 * mantissa + if rounding then 1 else 0) % (2 * half) = 0 ∧ sticky = false) := by
  let remainder := mantissa % (2 * half)
  let bit : Int := if rounding then 1 else 0
  have bitBounds : 0 ≤ bit ∧ bit ≤ 1 := by cases rounding <;> decide
  have divisorPositive : 0 < 2 * half := by omega
  have divisorNonzero : 2 * half ≠ 0 := by omega
  have halfNonzero : half ≠ 0 := by omega
  have lower : 0 ≤ remainder := Int.emod_nonneg _ divisorNonzero
  have upper : remainder < 2 * half := Int.emod_lt_of_pos _ divisorPositive
  have division := manual_encoded_division mantissa (2 * half) bit divisorNonzero
  have residual :
      ((2 * remainder + bit) / (2 * half) = if remainder < half then 0 else 1) ∧
      ((2 * remainder + bit) % (2 * half) =
        if remainder < half then 2 * remainder + bit else 2 * remainder + bit - 2 * half) := by
    by_cases less : remainder < half
    · simp only [less, if_true]
      exact (Int.ediv_emod_unique divisorPositive).mpr ⟨by omega, by omega, by omega⟩
    · simp only [less, if_false]
      exact (Int.ediv_emod_unique divisorPositive).mpr ⟨by omega, by omega, by omega⟩
  have quotientValue := division.1.trans (congrArg (fun value => 2 * (mantissa / (2 * half)) + value) residual.1)
  have remainderValue := division.2.trans residual.2
  dsimp only
  change manual_shift_encoding (shr_record_of_loc (zOfInt (mantissa / (2 * half)))
      (manual_location half remainder rounding sticky)) = (2 * mantissa + bit) / (2 * half) ∧
    ((shr_record_of_loc (zOfInt (mantissa / (2 * half)))
      (manual_location half remainder rounding sticky)).shr_s = false ↔
      (2 * mantissa + bit) % (2 * half) = 0 ∧ sticky = false)
  rw [quotientValue, remainderValue]
  by_cases zero : remainder = 0 <;> by_cases less : remainder < half <;>
    by_cases equal : remainder = half <;>
    cases rounding <;> cases sticky <;>
    simp [manual_location, zero, less, equal, halfNonzero, manual_shift_encoding, shr_record_of_loc,
      Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.shr_record_of_loc,
      shr_m, shr_r, intOfZ_zOfInt, bit] <;> omega

private theorem manual_source_div (mantissa : Z) (divisor : Int) (positive : 0 < divisor) :
    Raux.Zdiv mantissa (zOfInt divisor) = zOfInt (intOfZ mantissa / divisor) := by
  change zOfInt (if intOfZ (zOfInt divisor) = 0 then 0
    else if 0 < intOfZ (zOfInt divisor) then intOfZ mantissa / intOfZ (zOfInt divisor)
    else _) = _
  simp only [intOfZ_zOfInt, positive, Int.ne_of_gt positive, if_false, if_true]

private theorem manual_source_mod (mantissa : Z) (divisor : Int) (positive : 0 < divisor) :
    ZArith.Zdiv.Zmod mantissa (zOfInt divisor) = zOfInt (intOfZ mantissa % divisor) := by
  change zOfInt (if intOfZ (zOfInt divisor) = 0 then intOfZ mantissa
    else if 0 < intOfZ (zOfInt divisor) then intOfZ mantissa % intOfZ (zOfInt divisor)
    else _) = _
  simp only [intOfZ_zOfInt, positive, Int.ne_of_gt positive, if_false, if_true]

private theorem manual_iter_record (count : Nat) (positiveCount : 0 < count)
    (record : shr_record) (nonnegative : Zle Z0 (shr_m record)) :
    Zaux.iter_nat shr_1 count record =
      shr_record_of_loc (Raux.Zdiv (shr_m record) (zOfInt ((2 : Int) ^ count)))
        (new_location (zOfInt ((2 : Int) ^ count))
          (ZArith.Zdiv.Zmod (shr_m record) (zOfInt ((2 : Int) ^ count)))
          (loc_of_shr_record record)) := by
  cases count with
  | zero => omega
  | succ count =>
      have invariant := manual_iter_encoding (count + 1) record nonnegative
      rcases record with ⟨mantissa, rounding, sticky⟩
      have powerPositive : 0 < (2 : Int) ^ count := Int.pow_pos (by decide)
      have powerRewrite : (2 : Int) ^ (count + 1) = 2 * 2 ^ count := by
        rw [Int.pow_succ, Int.mul_comm]
      have result := manual_result_encoding (intOfZ mantissa) (2 ^ count) powerPositive rounding sticky
      simp only [powerRewrite] at invariant ⊢
      change Zaux.iter_nat shr_1 (count + 1) ⟨mantissa, rounding, sticky⟩ =
        shr_record_of_loc (Raux.Zdiv mantissa (zOfInt (2 * 2 ^ count)))
          (new_location (zOfInt (2 * 2 ^ count))
            (ZArith.Zdiv.Zmod mantissa (zOfInt (2 * 2 ^ count)))
            (loc_of_shr_record ⟨mantissa, rounding, sticky⟩))
      rw [manual_source_div _ _ (by omega), manual_source_mod _ _ (by omega), manual_location_formula]
      apply manual_record_ext
      · exact invariant.2.1.trans result.1.symm
      · exact invariant.2.2.trans result.2.symm

private theorem manual_shr_truncate (mantissa exponent count : Z) (place : location)
    (nonnegative : Zle Z0 mantissa) :
    shr (shr_record_of_loc mantissa place) exponent count =
      if Zlt_bool Z0 count then
        (shr_record_of_loc (Raux.Zdiv mantissa (Zpower (radix2 : Z) count))
          (new_location (Zpower (radix2 : Z) count)
            (ZArith.Zdiv.Zmod mantissa (Zpower (radix2 : Z) count)) place), Zadd exponent count)
      else (shr_record_of_loc mantissa place, exponent) := by
  cases count with
  | Z0 => rfl
  | Zneg count =>
      have positive := posToNat_positive count
      have comparison : Zlt_bool Z0 (Zneg count) = false := by
        change (if (0 : Int) < -(posToNat count : Int) then true else false) = false
        simp [show ¬ (0 : Int) < -(posToNat count : Int) by omega]
      rw [comparison]
      rfl
  | Zpos count =>
      have positive := posToNat_positive count
      have comparison : Zlt_bool Z0 (Zpos count) = true := by
        change (if (0 : Int) < (posToNat count : Int) then true else false) = true
        simp [positive]
      rw [comparison]
      have countNonnegative : Zle Z0 (Zpos count) := by
        change (0 : Int) ≤ (posToNat count : Int)
        omega
      rw [shr_nat _ _ _ countNonnegative]
      change (Zaux.iter_nat shr_1 (posToNat count) (shr_record_of_loc mantissa place),
        Zadd exponent (Zpos count)) = _
      have recordNonnegative : Zle Z0 (shr_m (shr_record_of_loc mantissa place)) := by
        rw [shr_m_shr_record_of_loc]
        exact nonnegative
      rw [manual_iter_record _ positive _ recordNonnegative, shr_m_shr_record_of_loc,
        loc_of_shr_record_of_loc]
      have powerValue : Zpower (radix2 : Z) (Zpos count) = zOfInt ((2 : Int) ^ posToNat count) := by
        change (if (posToNat count : Int) < 0 then Z0
          else zOfInt ((2 : Int) ^ Int.toNat (posToNat count : Int))) = _
        rw [if_neg (by omega)]
        rfl
      rw [powerValue]
      rfl

private theorem ieee_shr_fexp_truncate :
    ∀ {prec emax : Z} [Core.FLX.Prec_gt_0 prec],
      shr_fexp_truncateStatement (prec := prec) (emax := emax) := by
  intro prec emax precision mantissa exponent place nonnegative
  change shr (shr_record_of_loc mantissa place) exponent
      (Zsub (fexp0 prec emax (Zadd (Digits.Zdigits2 mantissa) exponent)) exponent) = _
  rw [Digits.Zdigits2_Zdigits]
  rw [manual_shr_truncate _ _ _ _ nonnegative]
  unfold truncate Calc.Round.truncate
  dsimp only
  simp only [Calc.Round.Zsub, Zsub, Calc.Round.Zadd, Zadd,
    Calc.Round.Zdigits, Zdigits, Calc.Round.Zlt_bool, Zlt_bool,
    Calc.Round.Z0, Z0, fexp, Digits.radix2, radix2]
  split <;> rename_i condition <;>
    simp only [condition, if_true, if_false, Calc.Round.truncate_aux]

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN.IEEEManualRounding

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN.IEEEManualRounding

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals

private theorem manual_choice_correct (ctx : ExactRealContext) (rounding : mode)
    (value : Exact.R ctx) (mantissa : Z) (place : location)
    (bracket : Calc.Bracket.inbetween_int ctx mantissa (Exact.Rabs ctx value) place) :
    Exact.round_mode ctx rounding value =
      cond_Zopp (Exact.Rlt_bool ctx value (Exact.R0 ctx))
        (choice_mode rounding (Exact.Rlt_bool ctx value (Exact.R0 ctx)) mantissa place) := by
  cases rounding
  · have nearest := Calc.Round.inbetween_int_N_sign ctx
      (fun integer => !Zeven integer) value mantissa place bracket
    have parity : Zeven (Zopp (Zadd mantissa Zone)) = !Zeven mantissa := by
      change ZArith.BinInt.Z.even (ZArith.BinInt.Z.opp
        (ZArith.BinInt.Z.add mantissa Zone)) = _
      rw [ZArith.BinInt.Z.even_opp, ZArith.BinInt.Z.even_add]
      change CompCert4Lean.Foundation.Logic.Rocq.Coq.Bool.Bool.eqb (Zeven mantissa) false = _
      cases Zeven mantissa <;> rfl
    change Exact.round_mode ctx mode_NE value =
      cond_Zopp (Exact.Rlt_bool ctx value (Exact.R0 ctx))
        (cond_incr (round_N
          (if Exact.Rlt_bool ctx value (Exact.R0 ctx) then
            !(!(Zeven (Zopp (Zadd mantissa Zone)))) else !Zeven mantissa) place) mantissa)
      at nearest
    rw [parity] at nearest
    simpa only [Bool.not_not, ite_self, choice_mode] using nearest
  · exact Calc.Round.inbetween_int_ZR_sign ctx value mantissa place bracket
  · exact Calc.Round.inbetween_int_DN_sign ctx value mantissa place bracket
  · exact Calc.Round.inbetween_int_UP_sign ctx value mantissa place bracket
  · exact Calc.Round.inbetween_int_NA_sign ctx value mantissa place bracket

private theorem manual_choice_ge (rounding : mode) (sign : Bool)
    (mantissa : Z) (place : location) :
    Zle mantissa (choice_mode rounding sign mantissa place) := by
  have increased : Zle mantissa (Zadd mantissa Zone) := by
    change intOfZ mantissa ≤ intOfZ (ZArith.BinInt.Z.add mantissa Zone)
    simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
    change intOfZ mantissa ≤ intOfZ mantissa + 1
    omega
  cases rounding <;> simp only [choice_mode, cond_incr, Calc.Round.cond_incr]
  all_goals first | exact Int.le_refl _ | split <;> first | exact increased | exact Int.le_refl _

private theorem manual_bracket_nonnegative (ctx : ExactRealContext)
    (value : Exact.R ctx) (mantissa exponent : Z) (place : location)
    (nonnegative : Exact.Rle ctx (Exact.R0 ctx) value)
    (bracket : Calc.Bracket.inbetween_float ctx radix2 mantissa exponent value place) :
    Zle Z0 mantissa := by
  have bound := (Calc.Bracket.inbetween_float_bounds ctx radix2 value
    mantissa exponent place bracket).2
  have positive := RIneq.Rle_lt_trans ctx _ _ _ nonnegative bound
  have integerPositive := Float_prop.gt_0_F2R ctx radix2 (Zadd mantissa Zone) exponent positive
  change (0 : Int) < intOfZ (ZArith.BinInt.Z.add mantissa Zone) at integerPositive
  simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt] at integerPositive
  change (0 : Int) ≤ intOfZ mantissa
  change (0 : Int) < intOfZ mantissa + 1 at integerPositive
  omega

private theorem manual_abs_positive (ctx : ExactRealContext) (value : Exact.R ctx)
    (nonzero : value ≠ Exact.R0 ctx) :
    Exact.Rlt ctx (Exact.R0 ctx) (Exact.Rabs ctx value) := by
  have nonzero' : value ≠ ctx.spec.ofZ Z0 := by
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact nonzero
  have positive := Rbasic_fun.Rabs_pos_lt ctx value nonzero'
  change ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.abs value) at positive
  rw [ctx.certificate.sourceLaws.ofZ_zero] at positive
  exact positive

private theorem manual_signed_absolute (ctx : ExactRealContext) (sign : Bool)
    (mantissa exponent : Z) (nonnegative : Zle Z0 mantissa) :
    Exact.Rabs ctx (Exact.F2R ctx (Float radix2 (cond_Zopp sign mantissa) exponent)) =
      Exact.F2R ctx (Float radix2 mantissa exponent) := by
  have absolute : Zabs mantissa = mantissa := by
    apply intOfZ_injective
    change intOfZ (zOfInt (intOfZ mantissa).natAbs) = intOfZ mantissa
    rw [intOfZ_zOfInt]
    exact Int.natAbs_of_nonneg nonnegative
  have signed : Zabs (cond_Zopp sign mantissa) = mantissa :=
    (Zaux.abs_cond_Zopp sign mantissa).trans absolute
  have identity : Exact.F2R ctx (Float radix2 (Zabs (cond_Zopp sign mantissa)) exponent) =
      Exact.Rabs ctx (Exact.F2R ctx (Float radix2 (cond_Zopp sign mantissa) exponent)) :=
    Float_prop.F2R_Zabs ctx radix2 (cond_Zopp sign mantissa) exponent
  rw [signed] at identity
  exact identity.symm

private theorem manual_cexp_float (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (exponentFunction : Z → Z) (mantissa exponent : Z) (nonzero : mantissa ≠ Z0) :
    Exact.cexp magnitude radix2 exponentFunction
      (Exact.F2R ctx (Float radix2 mantissa exponent)) =
      exponentFunction (Zadd (Zdigits radix2 mantissa) exponent) := by
  change exponentFunction (Float_prop.Exact.mag magnitude radix2
    (Float_prop.Exact.F2R ctx (Float radix2 mantissa exponent))) = _
  rw [Float_prop.mag_F2R_Zdigits ctx magnitude radix2 mantissa exponent nonzero]

private theorem manual_canonical_mantissa {prec emax : Z}
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (mantissa : positive) (exponent : Z)
    (canonical : exponent = Exact.cexp magnitude radix2 (fexp (prec := prec) (emax := emax))
      (Exact.F2R ctx (Float radix2 (Zpos mantissa) exponent))) :
    canonical_mantissa (prec := prec) (emax := emax) mantissa exponent = true := by
  rw [manual_cexp_float ctx magnitude _ _ _ (by intro impossible; cases impossible)] at canonical
  change Zeq_bool (fexp0 prec emax
    (Zadd (Digits.Zpos (Digits.digits2_pos mantissa)) exponent)) exponent = true
  rw [Digits.Zpos_digits2_pos]
  apply Zaux.Zeq_bool_true
  exact canonical.symm

private theorem manual_signed_float_eq (ctx : ExactRealContext) (sign : Bool)
    (first firstExp second secondExp : Z)
    (same : Exact.F2R ctx (Float radix2 first firstExp) =
      Exact.F2R ctx (Float radix2 second secondExp)) :
    Exact.F2R ctx (Float radix2 (cond_Zopp sign first) firstExp) =
      Exact.F2R ctx (Float radix2 (cond_Zopp sign second) secondExp) := by
  change Float_prop.Exact.F2R ctx (Float radix2 (cond_Zopp sign first) firstExp) =
    Float_prop.Exact.F2R ctx (Float radix2 (cond_Zopp sign second) secondExp)
  rw [Float_prop.F2R_cond_Zopp, Float_prop.F2R_cond_Zopp]
  exact congrArg (Raux.Exact.cond_Ropp ctx sign) same

private theorem ieee_round_aux_correct :
    ∀ {prec emax : Z} (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
      [FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax],
      binary_round_aux_correct'Statement (prec := prec) (emax := emax) ctx magnitude := by
  intro prec emax ctx magnitude precision exponentLimit rounding value mantissa exponent place
    nonzero bracket exponentBound
  have validExp : Valid_exp (fexp (prec := prec) (emax := emax)) :=
    FLT.FLT_exp_valid (emin (prec := prec) (emax := emax)) prec (h := precision)
  have validRound := valid_rnd_round_mode_proof ctx rounding
  have absPositive := manual_abs_positive ctx value nonzero
  have absNonnegative := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp absPositive |>.1
  have mantissaNonnegative := manual_bracket_nonnegative ctx _ _ _ _ absNonnegative bracket
  have absExponent : Exact.cexp magnitude radix2 (fexp (prec := prec) (emax := emax))
      (Exact.Rabs ctx value) = Exact.cexp magnitude radix2 (fexp (prec := prec) (emax := emax)) value :=
    Generic_fmt.cexp_abs ctx magnitude radix2 _ value
  have absExponentBound : Zle exponent
      (Exact.cexp magnitude radix2 (fexp (prec := prec) (emax := emax)) (Exact.Rabs ctx value)) := by
    rw [absExponent]
    exact exponentBound
  have firstData := Calc.Round.truncate_correct_partial' ctx magnitude radix2
    (fexp (prec := prec) (emax := emax)) validExp (Exact.Rabs ctx value)
    mantissa exponent place absPositive bracket absExponentBound
  have firstRound := Calc.Round.round_trunc_sign_any_correct' ctx magnitude radix2
    (fexp (prec := prec) (emax := emax)) validExp (Exact.round_mode ctx rounding)
    validRound (choice_mode rounding) (manual_choice_correct ctx rounding)
    value mantissa exponent place bracket (Or.inl exponentBound)
  have firstShift := ieee_shr_fexp_truncate (prec := prec) (emax := emax)
    mantissa exponent place mantissaNonnegative
  dsimp only at firstShift
  rcases firstTrunc : Calc.Round.truncate radix2 (fexp (prec := prec) (emax := emax))
      ((mantissa, exponent), place) with ⟨⟨firstMantissa, firstExp⟩, firstPlace⟩
  rw [firstTrunc] at firstData firstRound firstShift
  dsimp only at firstData firstRound firstShift
  have firstExponent : firstExp = Exact.cexp magnitude radix2
      (fexp (prec := prec) (emax := emax)) value := firstData.2.trans absExponent
  have firstNonnegative := manual_bracket_nonnegative ctx _ _ _ _ absNonnegative firstData.1
  let selected := choice_mode rounding (Exact.Rlt_bool ctx value (Exact.R0 ctx)) firstMantissa firstPlace
  have selectedNonnegative : Zle Z0 selected :=
    Int.le_trans firstNonnegative (manual_choice_ge rounding _ firstMantissa firstPlace)
  have roundedValue : Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
      (Exact.round_mode ctx rounding) value =
      Exact.F2R ctx (Float radix2 (cond_Zopp (Exact.Rlt_bool ctx value (Exact.R0 ctx)) selected) firstExp) :=
    firstRound
  have absoluteValue : Exact.Rabs ctx
      (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
        (Exact.round_mode ctx rounding) value) = Exact.F2R ctx (Float radix2 selected firstExp) := by
    rw [roundedValue]
    exact manual_signed_absolute ctx _ _ _ selectedNonnegative
  have secondShift := ieee_shr_fexp_truncate (prec := prec) (emax := emax)
    selected firstExp loc_Exact selectedNonnegative
  dsimp only at secondShift
  unfold binary_round_aux
  rw [firstShift]
  dsimp only
  rw [shr_m_shr_record_of_loc, loc_of_shr_record_of_loc]
  change valid_binary (prec := prec) (emax := emax)
      (let result := shr_fexp (prec := prec) (emax := emax) selected firstExp loc_Exact
       match shr_m result.1 with
       | .Z0 => S754_zero (Exact.Rlt_bool ctx value (Exact.R0 ctx))
       | .Zpos positiveMantissa => binary_fit_aux (prec := prec) (emax := emax)
           rounding (Exact.Rlt_bool ctx value (Exact.R0 ctx)) positiveMantissa result.2
       | .Zneg _ => S754_nan) = true ∧ _
  rw [secondShift]
  have absoluteZero : Exact.Rabs ctx (Exact.R0 ctx) = Exact.R0 ctx :=
    ctx.certificate.sourceLaws.abs_nonnegative _ (ctx.certificate.orderedField.le_refl _)
  cases selectedEq : selected with
  | Z0 =>
      rw [selectedEq] at secondShift roundedValue absoluteValue
      have zeroTrunc := Calc.Round.truncate_0 radix2 (fexp (prec := prec) (emax := emax)) firstExp loc_Exact
      rcases secondTrunc : Calc.Round.truncate radix2 (fexp (prec := prec) (emax := emax))
          ((Z0, firstExp), loc_Exact) with ⟨⟨secondMantissa, secondExp⟩, secondPlace⟩
      rw [secondTrunc] at zeroTrunc
      dsimp only at zeroTrunc
      subst secondMantissa
      have signedZero : cond_Zopp (Exact.Rlt_bool ctx value (Exact.R0 ctx)) Z0 = Z0 := by
        cases Exact.Rlt_bool ctx value (Exact.R0 ctx) <;> rfl
      rw [signedZero] at roundedValue
      have zeroValue : Exact.F2R ctx (Float radix2 Z0 firstExp) = Exact.R0 ctx :=
        Float_prop.F2R_0 ctx radix2 firstExp
      rw [zeroValue] at roundedValue
      rw [roundedValue, absoluteZero]
      have small : Exact.Rlt_bool ctx (Exact.R0 ctx) (Exact.bpow ctx radix2 emax) = true :=
        Raux.Rlt_bool_true ctx _ _ (Raux.bpow_gt_0 ctx radix2 emax)
      simp only [small, if_true]
      cases secondPlace with
      | loc_Exact => exact ⟨rfl, rfl, rfl, rfl⟩
      | loc_Inexact comparison => cases comparison <;> exact ⟨rfl, rfl, rfl, rfl⟩
  | Zpos selectedMantissa =>
      rw [selectedEq] at roundedValue absoluteValue secondShift
      have selectedNotZero : Zpos selectedMantissa ≠ Z0 := by intro impossible; cases impossible
      have signedNotZero : cond_Zopp (Exact.Rlt_bool ctx value (Exact.R0 ctx))
          (Zpos selectedMantissa) ≠ Z0 := by
        intro impossible
        have absolute := Zaux.abs_cond_Zopp (Exact.Rlt_bool ctx value (Exact.R0 ctx))
          (Zpos selectedMantissa)
        change Zabs (cond_Zopp _ (Zpos selectedMantissa)) = Zabs (Zpos selectedMantissa) at absolute
        rw [impossible] at absolute
        have integerEq := congrArg intOfZ absolute
        change intOfZ (zOfInt (intOfZ Z0).natAbs) =
          intOfZ (zOfInt (intOfZ (Zpos selectedMantissa)).natAbs) at integerEq
        simp only [intOfZ_zOfInt] at integerEq
        change (0 : Int) = (posToNat selectedMantissa : Int) at integerEq
        have positive := posToNat_positive selectedMantissa
        omega
      have roundedNonzero : Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx rounding) value ≠ Exact.R0 ctx := by
        rw [roundedValue]
        exact Float_prop.F2R_neq_0 ctx radix2 _ signedNotZero
      have roundedExponent : Exact.cexp magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.Rabs ctx (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
            (Exact.round_mode ctx rounding) value)) =
          Exact.cexp magnitude radix2 (fexp (prec := prec) (emax := emax))
            (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
              (Exact.round_mode ctx rounding) value) :=
        Generic_fmt.cexp_abs ctx magnitude radix2 _ _
      have selectedExponent : Zle firstExp (fexp (prec := prec) (emax := emax)
          (Zadd (Zdigits radix2 (Zpos selectedMantissa)) firstExp)) := by
        rw [← manual_cexp_float ctx magnitude (fexp (prec := prec) (emax := emax))
          (Zpos selectedMantissa) firstExp selectedNotZero,
          ← absoluteValue, roundedExponent, firstExponent]
        exact Generic_fmt.cexp_round_ge ctx magnitude radix2 _ validExp
          (FLT.FLT_exp_monotone (emin (prec := prec) (emax := emax)) prec)
          _ validRound value roundedNonzero
      have formatted : Exact.generic_format magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.F2R ctx (Float radix2 (Zpos selectedMantissa) firstExp)) := by
        rw [← absoluteValue]
        exact Generic_fmt.generic_format_abs ctx magnitude radix2 _ _
          (Generic_fmt.generic_format_round ctx magnitude radix2 _ validExp _ validRound value)
      have secondData := Calc.Round.truncate_correct_format ctx magnitude radix2
        (fexp (prec := prec) (emax := emax)) (Zpos selectedMantissa) firstExp
        selectedNotZero formatted selectedExponent
      rcases secondTrunc : Calc.Round.truncate radix2 (fexp (prec := prec) (emax := emax))
          ((Zpos selectedMantissa, firstExp), loc_Exact) with ⟨⟨secondMantissa, secondExp⟩, secondPlace⟩
      rw [secondTrunc] at secondData
      dsimp only at secondData
      have secondPositive : Zlt Z0 secondMantissa := by
        apply Float_prop.gt_0_F2R ctx radix2 secondMantissa secondExp
        have sameValue : Float_prop.Exact.F2R ctx (Float radix2 secondMantissa secondExp) =
            Float_prop.Exact.F2R ctx (Float radix2 (Zpos selectedMantissa) firstExp) :=
          secondData.1.symm
        rw [sameValue]
        exact Float_prop.F2R_gt_0 ctx radix2 _
          (Int.natCast_pos.mpr (posToNat_positive selectedMantissa))
      cases secondMantissa with
      | Z0 => exact False.elim (Int.lt_irrefl 0 secondPositive)
      | Zneg negativeMantissa =>
          change (0 : Int) < -(posToNat negativeMantissa : Int) at secondPositive
          omega
      | Zpos positiveMantissa =>
          have canonical : secondExp = Exact.cexp magnitude radix2
              (fexp (prec := prec) (emax := emax))
              (Exact.F2R ctx (Float radix2 (Zpos positiveMantissa) secondExp)) :=
            secondData.2.trans (congrArg (Exact.cexp magnitude radix2
              (fexp (prec := prec) (emax := emax))) secondData.1)
          have resultValue := roundedValue.trans (manual_signed_float_eq ctx _ _ _ _ _ secondData.1)
          have fitted := binary_fit_aux_correct (prec := prec) (emax := emax) ctx rounding
            (Exact.Rlt_bool ctx value (Exact.R0 ctx)) positiveMantissa secondExp
            (manual_canonical_mantissa ctx magnitude positiveMantissa secondExp canonical)
          dsimp only [Exact.SF2R] at fitted
          rw [← resultValue] at fitted
          cases secondPlace with
          | loc_Exact => exact fitted
          | loc_Inexact comparison => cases comparison <;> exact fitted
  | Zneg negativeMantissa =>
      rw [selectedEq] at selectedNonnegative
      change (0 : Int) ≤ -(posToNat negativeMantissa : Int) at selectedNonnegative
      have positive := posToNat_positive negativeMantissa
      omega

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN.IEEEManualRounding

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN.IEEEManualRounding

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals

private theorem ieee_signed_nonzero (ctx : ExactRealContext) (sign : Bool)
    (mantissa : positive) (exponent : Z) :
    Exact.F2R ctx (Float radix2 (cond_Zopp sign (Zpos mantissa)) exponent) ≠ Exact.R0 ctx := by
  apply Float_prop.F2R_neq_0 ctx radix2
  cases sign with
  | false => intro impossible; cases impossible
  | true =>
      intro impossible
      have integerEq := congrArg intOfZ impossible
      change intOfZ (zOfInt (-(posToNat mantissa : Int))) = 0 at integerEq
      rw [intOfZ_zOfInt] at integerEq
      have positive := posToNat_positive mantissa
      omega

private theorem ieee_float_sign (ctx : ExactRealContext) (sign : Bool)
    (mantissa : positive) (exponent : Z) :
    Exact.Rlt_bool ctx (Exact.F2R ctx (Float radix2 (cond_Zopp sign (Zpos mantissa)) exponent))
      (Exact.R0 ctx) = sign := by
  cases sign with
  | false =>
      apply Raux.Rlt_bool_false ctx
      apply RIneq.Rlt_le ctx
      exact Float_prop.F2R_gt_0 ctx radix2 _
        (Int.natCast_pos.mpr (posToNat_positive mantissa))
  | true =>
      apply Raux.Rlt_bool_true ctx
      apply Float_prop.F2R_lt_0 ctx radix2
      change intOfZ (zOfInt (-(posToNat mantissa : Int))) < 0
      rw [intOfZ_zOfInt]
      have positive := posToNat_positive mantissa
      omega

private theorem ieee_round_correct :
    ∀ {prec emax : Z} (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
      [FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax],
      binary_round_correctStatement (prec := prec) (emax := emax) ctx magnitude := by
  intro prec emax ctx magnitude precision maximum rounding sign mantissa exponent
  let value := Exact.F2R ctx (Float radix2 (cond_Zopp sign (Zpos mantissa)) exponent)
  have nonzero := ieee_signed_nonzero ctx sign mantissa exponent
  have signValue := ieee_float_sign ctx sign mantissa exponent
  have absoluteValue := manual_signed_absolute ctx sign (Zpos mantissa) exponent (Int.natCast_nonneg _)
  have aligned := shl_align_fexp_correct (prec := prec) (emax := emax) ctx mantissa exponent
  rcases alignment : shl_align_fexp (prec := prec) (emax := emax) mantissa exponent with
    ⟨alignedMantissa, alignedExponent⟩
  rw [alignment] at aligned
  dsimp only at aligned
  have bracket : Calc.Bracket.inbetween_float ctx radix2 (Zpos alignedMantissa) alignedExponent
      (Exact.Rabs ctx value) loc_Exact :=
    Calc.Bracket.inbetween_Exact (absoluteValue.trans aligned.1)
  have exponentValue : Exact.cexp magnitude radix2 (fexp (prec := prec) (emax := emax)) value =
      fexp (prec := prec) (emax := emax) (Zadd (Zdigits radix2 (Zpos alignedMantissa)) alignedExponent) := by
    calc
      _ = Exact.cexp magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.Rabs ctx value) := (Generic_fmt.cexp_abs ctx magnitude radix2 _ value).symm
      _ = _ := by
        change Exact.cexp magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.Rabs ctx (Exact.F2R ctx (Float radix2 (cond_Zopp sign (Zpos mantissa)) exponent))) = _
        rw [absoluteValue, aligned.1]
        exact manual_cexp_float ctx magnitude _ _ _ (by intro impossible; cases impossible)
  have exponentBound : Zle alignedExponent
      (Exact.cexp magnitude radix2 (fexp (prec := prec) (emax := emax)) value) := by
    rw [exponentValue]
    exact aligned.2
  have result := ieee_round_aux_correct ctx magnitude rounding value (Zpos alignedMantissa)
    alignedExponent loc_Exact nonzero bracket exponentBound
  change Exact.Rlt_bool ctx value (Exact.R0 ctx) = sign at signValue
  dsimp only at result
  rw [signValue] at result
  unfold binary_round
  rw [alignment]
  exact result

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN.IEEEManualRounding

namespace CompCert4Lean.Flocq.IEEE754.BinarySingleNaN.IEEEManualRounding

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem ieee_lift_spectrum {prec emax : Z} (ctx : ExactRealContext)
    (raw : binary_float prec emax) (notNan : is_nan raw = false)
    (spectrum : spec_float) (same : raw = SF2B spectrum) :
    Binary.Exact.B2R ctx (Binary.BSN2B' raw notNan) = Exact.SF2R ctx radix2 spectrum ∧
      Binary.is_finite (Binary.BSN2B' raw notNan) = is_finite_SF spectrum ∧
      Binary.Bsign (Binary.BSN2B' raw notNan) = sign_SF spectrum ∧
      Binary.B2FF (Binary.BSN2B' raw notNan) = Binary.SF2FF spectrum := by
  cases same
  cases spectrum with
  | S754_nan => cases notNan
  | S754_zero sign => exact ⟨rfl, rfl, rfl, rfl⟩
  | S754_infinity sign => exact ⟨rfl, rfl, rfl, rfl⟩
  | S754_finite sign mantissa exponent => exact ⟨rfl, rfl, rfl, rfl⟩

private theorem ieee_normalize_signed {prec emax : Z}
    [FLX.Prec_gt_0 prec] [Prec_lt_emax prec emax]
    [certificate : Binary.BinaryNormalizeCertificate prec emax]
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (rounding : mode) (sign : Bool) (mantissa : positive) (exponent : Z) (zeroSign : Bool) :
    let value := Exact.F2R ctx (Float radix2 (cond_Zopp sign (Zpos mantissa)) exponent)
    let result := Binary.binary_normalize (prec := prec) (emax := emax)
      rounding (cond_Zopp sign (Zpos mantissa)) exponent zeroSign
    if Exact.Rlt_bool ctx
        (Exact.Rabs ctx (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx rounding) value)) (Exact.bpow ctx radix2 emax) then
      Binary.Exact.B2R ctx result = Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
          (Exact.round_mode ctx rounding) value ∧
        Binary.is_finite result = true ∧ Binary.Bsign result = sign
    else Binary.B2FF result = Binary.binary_overflow (prec := prec) (emax := emax) rounding sign := by
  have rounded := ieee_round_correct (prec := prec) (emax := emax) ctx magnitude
    rounding sign mantissa exponent
  have rawEqual : binary_normalize (prec := prec) (emax := emax) rounding
      (cond_Zopp sign (Zpos mantissa)) exponent zeroSign =
      SF2B (binary_round (prec := prec) (emax := emax) rounding sign mantissa exponent) := by
    cases sign with
    | false => rfl
    | true =>
        have negative : cond_Zopp true (Zpos mantissa) = Zneg mantissa := by
          apply intOfZ_injective
          change intOfZ (zOfInt (-(posToNat mantissa : Int))) = -(posToNat mantissa : Int)
          exact intOfZ_zOfInt _
        rw [negative]
        rfl
  have fields := ieee_lift_spectrum ctx _
    (certificate.is_nan_binary_normalize rounding (cond_Zopp sign (Zpos mantissa)) exponent zeroSign)
    _ rawEqual
  dsimp only at rounded ⊢
  by_cases small : Exact.Rlt_bool ctx
      (Exact.Rabs ctx (Exact.round magnitude radix2 (fexp (prec := prec) (emax := emax))
        (Exact.round_mode ctx rounding)
        (Exact.F2R ctx (Float radix2 (cond_Zopp sign (Zpos mantissa)) exponent))))
      (Exact.bpow ctx radix2 emax) = true
  · rw [if_pos small] at rounded ⊢
    exact ⟨fields.1.trans rounded.2.1, fields.2.1.trans rounded.2.2.1,
      fields.2.2.1.trans rounded.2.2.2⟩
  · rw [if_neg small] at rounded ⊢
    exact fields.2.2.2.trans (congrArg Binary.SF2FF rounded.2)

end CompCert4Lean.Flocq.IEEE754.BinarySingleNaN.IEEEManualRounding

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem BofZ_correct :
    ∀ {prec emax : Z} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
      [Binary.BinaryNormalizeCertificate prec emax],
      BofZ_correctStatement (prec := prec) (emax := emax) := by
  intro prec emax precision maximum certificate ctx magnitude integer
  cases integer with
  | Z0 =>
      have roundZero : Exact.round magnitude Zaux.radix2 (fexp prec emax)
          (Exact.round_mode ctx mode_NE) (Exact.IZR ctx Z0) = Exact.R0 ctx := by
        have zeroCast : Exact.IZR ctx Z0 = Exact.R0 ctx := ctx.certificate.sourceLaws.ofZ_zero
        rw [zeroCast]
        exact Generic_fmt.round_0 ctx magnitude Zaux.radix2 (fexp prec emax)
          (Exact.round_mode ctx mode_NE) (BinarySingleNaN.valid_rnd_round_mode_proof ctx mode_NE)
      rw [roundZero]
      have absoluteZero : Exact.Rabs ctx (Exact.R0 ctx) = Exact.R0 ctx :=
        ctx.certificate.sourceLaws.abs_nonnegative _ (ctx.certificate.orderedField.le_refl _)
      rw [absoluteZero]
      have small : Exact.Rlt_bool ctx (Exact.R0 ctx) (Exact.bpow ctx Zaux.radix2 emax) = true :=
        Raux.Rlt_bool_true ctx _ _ (Raux.bpow_gt_0 ctx Zaux.radix2 emax)
      rw [small]
      exact ⟨rfl, rfl, rfl⟩
  | Zpos mantissa =>
      have result := BinarySingleNaN.IEEEManualRounding.ieee_normalize_signed
        (prec := prec) (emax := emax) ctx magnitude mode_NE false mantissa Z0 false
      dsimp only at result
      have realValue : BinarySingleNaN.Exact.F2R ctx
          (BinarySingleNaN.Float Zaux.radix2 (Zaux.cond_Zopp false (Zpos mantissa)) Z0) =
          Exact.IZR ctx (Zpos mantissa) := ctx.certificate.orderedField.mul_one _
      rw [realValue] at result
      have integerSign : Zlt_bool (Zpos mantissa) Z0 = false := by
        change (if (posToNat mantissa : Int) < 0 then true else false) = false
        simp
      rw [integerSign]
      exact result
  | Zneg mantissa =>
      have result := BinarySingleNaN.IEEEManualRounding.ieee_normalize_signed
        (prec := prec) (emax := emax) ctx magnitude mode_NE true mantissa Z0 false
      dsimp only at result
      have negative : BinarySingleNaN.cond_Zopp true (BinarySingleNaN.Zpos mantissa) = Zneg mantissa := by
        apply intOfZ_injective
        change intOfZ (zOfInt (-(posToNat mantissa : Int))) = -(posToNat mantissa : Int)
        exact intOfZ_zOfInt _
      rw [negative] at result
      have realValue : BinarySingleNaN.Exact.F2R ctx
          (BinarySingleNaN.Float Zaux.radix2 (Zneg mantissa) Z0) =
          Exact.IZR ctx (Zneg mantissa) := ctx.certificate.orderedField.mul_one _
      rw [realValue] at result
      have integerSign : Zlt_bool (Zneg mantissa) Z0 = true := by
        change (if -(posToNat mantissa : Int) < 0 then true else false) = true
        exact if_pos (by have positive := posToNat_positive mantissa; omega)
      rw [integerSign]
      exact result

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754

theorem BofZ_finite :
    ∀ {prec emax : Z} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
      [Binary.BinaryNormalizeCertificate prec emax],
      BofZ_finiteStatement (prec := prec) (emax := emax) := by
  intro prec emax precision maximum certificate ctx magnitude integer bound
  have result := BofZ_correct (prec := prec) (emax := emax) ctx magnitude integer
  have noOverflow := round_int_no_overflow (prec := prec) (emax := emax)
    ctx magnitude integer bound
  have small : Exact.Rlt_bool ctx
      (Exact.Rabs ctx (Exact.round magnitude Zaux.radix2 (fexp prec emax)
        (Exact.round_mode ctx mode_NE) (Exact.IZR ctx integer)))
      (Exact.bpow ctx Zaux.radix2 emax) = true :=
    Raux.Rlt_bool_true ctx _ _ noOverflow
  rw [small] at result
  exact result

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754

theorem Bconv_correct :
    ∀ {prec1 emax1 prec2 emax2 : Z}
      [Prec_gt_0 prec2] [Prec_lt_emax prec2 emax2]
      [Binary.BinaryNormalizeCertificate prec2 emax2],
      Bconv_correctStatement (prec1 := prec1) (emax1 := emax1)
        (prec2 := prec2) (emax2 := emax2) := by
  intro prec1 emax1 prec2 emax2 precision2 maximum2 certificate
    ctx magnitude nan rounding value finite
  rcases value with ⟨value, valid⟩
  cases value with
  | B754_nan sign payload => cases finite
  | B754_infinity sign => cases finite
  | B754_zero sign =>
      change (if Exact.Rlt_bool ctx
        (Exact.Rabs ctx (Exact.round magnitude Zaux.radix2 (fexp prec2 emax2)
          (Exact.round_mode ctx rounding) (Exact.R0 ctx)))
        (Exact.bpow ctx Zaux.radix2 emax2) then _ else _)
      have roundZero : Exact.round magnitude Zaux.radix2 (fexp prec2 emax2)
          (Exact.round_mode ctx rounding) (Exact.R0 ctx) = Exact.R0 ctx :=
        Generic_fmt.round_0 ctx magnitude Zaux.radix2 (fexp prec2 emax2)
          (Exact.round_mode ctx rounding) (BinarySingleNaN.valid_rnd_round_mode_proof ctx rounding)
      rw [roundZero]
      have absoluteZero : Exact.Rabs ctx (Exact.R0 ctx) = Exact.R0 ctx :=
        ctx.certificate.sourceLaws.abs_nonnegative _ (ctx.certificate.orderedField.le_refl _)
      have small : Exact.Rlt_bool ctx (Exact.R0 ctx)
          (Exact.bpow ctx Zaux.radix2 emax2) = true :=
        Raux.Rlt_bool_true ctx _ _ (Raux.bpow_gt_0 ctx Zaux.radix2 emax2)
      rw [absoluteZero, small]
      exact ⟨roundZero.symm, rfl, rfl⟩
  | B754_finite sign mantissa exponent =>
      exact BinarySingleNaN.IEEEManualRounding.ieee_normalize_signed
        (prec := prec2) (emax := emax2) ctx magnitude rounding sign mantissa exponent sign

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754

theorem Bconv_BofZ :
    ∀ {prec1 emax1 prec2 emax2 : Z}
      [Prec_gt_0 prec1] [Prec_gt_0 prec2]
      [Prec_lt_emax prec1 emax1] [Prec_lt_emax prec2 emax2]
      [Binary.BinaryNormalizeCertificate prec1 emax1]
      [Binary.BinaryNormalizeCertificate prec2 emax2],
      Bconv_BofZStatement (prec1 := prec1) (emax1 := emax1)
        (prec2 := prec2) (emax2 := emax2) := by
  intro prec1 emax1 prec2 emax2 precision1 precision2 maximum1 maximum2 certificate1 certificate2
    ctx magnitude nan integer representable sourceValid targetValid
  have source := BofZ_representable (prec := prec1) (emax := emax1)
    ctx magnitude integer representable
  have conversion := Bconv_correct (prec1 := prec1) (emax1 := emax1)
    (prec2 := prec2) (emax2 := emax2) ctx magnitude nan mode_NE
    ⟨BofZ integer, sourceValid⟩ source.2.1
  have target := BofZ_correct (prec := prec2) (emax := emax2) ctx magnitude integer
  dsimp only at conversion target
  rw [source.1] at conversion
  by_cases small : Exact.Rlt_bool ctx
      (Exact.Rabs ctx (Exact.round magnitude Zaux.radix2 (fexp prec2 emax2)
        (Exact.round_mode ctx mode_NE) (Exact.IZR ctx integer)))
      (Exact.bpow ctx Zaux.radix2 emax2) = true
  · rw [if_pos small] at conversion target
    exact Binary.B2R_Bsign_inj ctx
      ⟨_, Bconv_result_obligation_proof nan mode_NE ⟨_, sourceValid⟩⟩
      ⟨_, targetValid⟩ conversion.2.1 target.2.1
      (conversion.1.trans target.1.symm)
      (conversion.2.2.trans (source.2.2.trans target.2.2.symm))
  · rw [if_neg small] at conversion target
    apply Binary.B2FF_inj
      ⟨_, Bconv_result_obligation_proof nan mode_NE ⟨_, sourceValid⟩⟩ ⟨_, targetValid⟩
    exact conversion.trans ((congrArg (Binary.binary_overflow mode_NE) source.2.2).trans target.symm)

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem ieee_lift_non_nan {prec emax : Z}
    (nan : {value : binary_float prec emax // Binary.is_nan value = true})
    (value : BinarySingleNaN.binary_float prec emax)
    (notNan : BinarySingleNaN.is_nan value = false) :
    Binary.BSN2B nan value = Binary.BSN2B' value notNan := by
  cases value <;> first | rfl | cases notNan

private theorem ieee_integer_sign (ctx : ExactRealContext) (integer : Z) :
    (match Exact.Rcompare ctx (Exact.IZR ctx integer) (Exact.R0 ctx) with
      | .Eq => false | .Lt => true | .Gt => false) = Zlt_bool integer Z0 := by
  have zero : Exact.IZR ctx Z0 = Exact.R0 ctx := ctx.certificate.sourceLaws.ofZ_zero
  have comparison : Exact.Rcompare ctx (Exact.IZR ctx integer) (Exact.IZR ctx Z0) =
      Raux.Zcompare integer Z0 := Raux.Rcompare_IZR ctx integer Z0
  rw [← zero, comparison]
  change (match (if intOfZ integer < 0 then Raux.Lt else
      if intOfZ integer = 0 then Raux.Eq else Raux.Gt) with
      | .Eq => false | .Lt => true | .Gt => false) =
    (if intOfZ integer < 0 then true else false)
  by_cases negative : intOfZ integer < 0
  · simp [negative]
  · by_cases zeroInteger : intOfZ integer = 0 <;> simp [negative, zeroInteger]

private theorem ieee_normalize_integer {prec emax : Z}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    [Binary.BinaryNormalizeCertificate prec emax]
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (mantissa exponent integer : Z)
    (value : Binary.Exact.F2R ctx (Binary.Float Zaux.radix2 mantissa exponent) =
      Exact.IZR ctx integer) :
    Binary.binary_normalize (prec := prec) (emax := emax) mode_NE mantissa exponent false =
      BofZ integer := by
  have normalized := Binary.binary_normalize_correct (prec := prec) (emax := emax)
    ctx magnitude mode_NE mantissa exponent false
  have target := BofZ_correct (prec := prec) (emax := emax) ctx magnitude integer
  dsimp only at normalized target
  rw [value] at normalized
  change (if Exact.Rlt_bool ctx
    (Exact.Rabs ctx (Exact.round magnitude Zaux.radix2 (fexp prec emax)
      (Exact.round_mode ctx mode_NE) (Exact.IZR ctx integer)))
    (Exact.bpow ctx Zaux.radix2 emax) then _ else _) at normalized
  have sign : (match Binary.Exact.Rcompare ctx (Exact.IZR ctx integer) (Binary.Exact.R0 ctx) with
      | .Eq => false | .Lt => true | .Gt => false) = Zlt_bool integer Z0 :=
    ieee_integer_sign ctx integer
  have negative : Binary.Exact.Rlt_bool ctx (Exact.IZR ctx integer) (Binary.Exact.R0 ctx) =
      Zlt_bool integer Z0 := by
    change (match Exact.Rcompare ctx (Exact.IZR ctx integer) (Exact.R0 ctx) with
      | .Lt => true | _ => false) = _
    cases comparison : Exact.Rcompare ctx (Exact.IZR ctx integer) (Exact.R0 ctx) <;>
      simpa only [comparison] using sign
  by_cases small : Exact.Rlt_bool ctx
      (Exact.Rabs ctx (Exact.round magnitude Zaux.radix2 (fexp prec emax)
        (Exact.round_mode ctx mode_NE) (Exact.IZR ctx integer)))
      (Exact.bpow ctx Zaux.radix2 emax) = true
  · rw [if_pos small] at normalized target
    exact Binary.B2R_Bsign_inj ctx
      ⟨_, Binary.binary_normalize_result_obligation_proof mode_NE mantissa exponent false⟩
      ⟨_, BofZ_result_obligation_proof integer⟩ normalized.2.1 target.2.1
      (normalized.1.trans target.1.symm)
      (normalized.2.2.trans (sign.trans target.2.2.symm))
  · rw [if_neg small] at normalized target
    exact Binary.B2FF_inj
      ⟨_, Binary.binary_normalize_result_obligation_proof mode_NE mantissa exponent false⟩
      ⟨_, BofZ_result_obligation_proof integer⟩
      (normalized.trans ((congrArg (Binary.binary_overflow mode_NE) negative).trans target.symm))

theorem BofZ_plus :
    ∀ {prec emax : Z} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
      [Binary.BinaryNormalizeCertificate prec emax],
      BofZ_plusStatement (prec := prec) (emax := emax) := by
  intro prec emax precision maximum certificate ctx magnitude nan leftInteger rightInteger
    leftRepresentable rightRepresentable
  have left := BofZ_representable (prec := prec) (emax := emax)
    ctx magnitude leftInteger leftRepresentable
  have right := BofZ_representable (prec := prec) (emax := emax)
    ctx magnitude rightInteger rightRepresentable
  have zeroInteger (integer : Z) (value : Exact.R0 ctx = Exact.IZR ctx integer) : integer = Z0 :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.eq_IZR ctx integer Z0
      (value.symm.trans ctx.certificate.sourceLaws.ofZ_zero.symm)
  have addZero (integer : Z) : Zadd integer Z0 = integer := by
    apply intOfZ_injective
    change intOfZ (zOfInt (intOfZ integer + 0)) = intOfZ integer
    simp [intOfZ_zOfInt]
  have zeroAdd (integer : Z) : Zadd Z0 integer = integer := by
    apply intOfZ_injective
    change intOfZ (zOfInt (0 + intOfZ integer)) = intOfZ integer
    simp [intOfZ_zOfInt]
  generalize leftEquation : BofZ (prec := prec) (emax := emax) leftInteger = leftValue at left ⊢
  generalize rightEquation : BofZ (prec := prec) (emax := emax) rightInteger = rightValue at right ⊢
  cases leftValue with
  | B754_nan sign payload => cases left.2.1
  | B754_infinity sign => cases left.2.1
  | B754_zero sign =>
      have integerZero := zeroInteger leftInteger left.1
      subst leftInteger
      have signFalse : sign = false := left.2.2
      subst sign
      rw [zeroAdd]
      cases rightValue with
      | B754_nan sign payload => cases right.2.1
      | B754_infinity sign => cases right.2.1
      | B754_zero sign =>
          have integerZero := zeroInteger rightInteger right.1
          subst rightInteger
          have signFalse : sign = false := right.2.2
          subst sign
          rfl
      | B754_finite sign mantissa exponent => exact rightEquation.symm
  | B754_finite signLeft mantissaLeft exponentLeft =>
      cases rightValue with
      | B754_nan sign payload => cases right.2.1
      | B754_infinity sign => cases right.2.1
      | B754_zero sign =>
          have integerZero := zeroInteger rightInteger right.1
          subst rightInteger
          have signFalse : sign = false := right.2.2
          subst sign
          rw [addZero]
          exact leftEquation.symm
      | B754_finite signRight mantissaRight exponentRight =>
          let exponent := ZArith.BinInt.Z.min exponentLeft exponentRight
          let mantissa := BinarySingleNaN.Fplus_naive signLeft mantissaLeft exponentLeft
            signRight mantissaRight exponentRight exponent
          change Binary.BSN2B _ (BinarySingleNaN.binary_normalize mode_NE mantissa exponent false) = _
          rw [ieee_lift_non_nan _ _
            (certificate.is_nan_binary_normalize mode_NE mantissa exponent false)]
          change Binary.binary_normalize mode_NE mantissa exponent false = _
          apply ieee_normalize_integer ctx magnitude
          have boundLeft : Zle exponent exponentLeft := by
            change intOfZ (ZArith.BinInt.Z.min exponentLeft exponentRight) ≤ intOfZ exponentLeft
            unfold ZArith.BinInt.Z.min
            split <;> omega
          have boundRight : Zle exponent exponentRight := by
            change intOfZ (ZArith.BinInt.Z.min exponentLeft exponentRight) ≤ intOfZ exponentRight
            unfold ZArith.BinInt.Z.min
            split <;> omega
          have sum := BinarySingleNaN.Fplus_naive_correct ctx signLeft mantissaLeft exponentLeft
            signRight mantissaRight exponentRight exponent boundLeft boundRight
          exact sum.trans ((congrArg (fun value => Exact.Rplus ctx value
            (Exact.B2R ctx (.B754_finite signRight mantissaRight exponentRight))) left.1).trans
            ((congrArg (Exact.Rplus ctx (Exact.IZR ctx leftInteger)) right.1).trans
            (ctx.certificate.sourceLaws.ofZ_add leftInteger rightInteger).symm))

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals

private theorem ieee_magnitude_exists (ctx : ExactRealContext) : Nonempty (Exact.Magnitude ctx) := by
  classical
  refine ⟨{ value := fun beta value => ?_ }⟩
  by_cases zero : value = Exact.R0 ctx
  · exact ⟨Z0, fun nonzero => False.elim (nonzero zero)⟩
  have basePositive : ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ beta.radix_val) :=
    Raux.radix_pos ctx beta
  have baseLarge : ctx.spec.lt ctx.spec.one (ctx.spec.ofZ beta.radix_val) := by
    have bound := RIneq.IZR_lt ctx Zone beta.radix_val (Zaux.radix_gt_1 beta)
    change ctx.spec.lt (ctx.spec.ofZ Zone) (ctx.spec.ofZ beta.radix_val) at bound
    rw [ctx.certificate.sourceLaws.ofZ_one] at bound
    exact bound
  let logarithm := ctx.spec.ln (ctx.spec.ofZ beta.radix_val)
  have logPositive : ctx.spec.lt ctx.spec.zero logarithm := by
    rcases ctx.certificate.total_order logarithm ctx.spec.zero with (less | equal) | greater
    · have bound := Raux.exp_le ctx logarithm ctx.spec.zero (RIneq.Rlt_le ctx _ _ less)
      change ctx.spec.le (ctx.spec.exp logarithm) (ctx.spec.exp ctx.spec.zero) at bound
      rw [ctx.certificate.exp.zero] at bound
      change ctx.spec.le (ctx.spec.exp (ctx.spec.ln (ctx.spec.ofZ beta.radix_val))) _ at bound
      rw [ctx.certificate.ln.exp_ln _ basePositive] at bound
      exact False.elim ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp baseLarge |>.2 bound)
    · have contradiction := ctx.certificate.ln.exp_ln (ctx.spec.ofZ beta.radix_val) basePositive
      change ctx.spec.exp logarithm = _ at contradiction
      rw [equal, ctx.certificate.exp.zero] at contradiction
      rw [← contradiction] at baseLarge
      exact False.elim (ctx.certificate.orderedField.lt_irrefl _ baseLarge)
    · exact greater
  have logNonzero : logarithm ≠ ctx.spec.zero := by
    intro equal
    rw [equal] at logPositive
    exact ctx.certificate.orderedField.lt_irrefl _ logPositive
  have absPositive : ctx.spec.lt ctx.spec.zero (ctx.spec.abs value) := by
    have bound := Rbasic_fun.Rabs_pos_lt ctx value (fun equal =>
      zero (equal.trans ctx.certificate.sourceLaws.ofZ_zero))
    change ctx.spec.lt (ctx.spec.ofZ Z0) (ctx.spec.abs value) at bound
    rw [ctx.certificate.sourceLaws.ofZ_zero] at bound
    exact bound
  let ratio := ctx.spec.mul (ctx.spec.ln (ctx.spec.abs value)) (ctx.spec.inv logarithm)
  let lower := Exact.Zfloor ctx ratio
  let exponent := Zadd lower Zone
  have product : ctx.spec.mul ratio logarithm = ctx.spec.ln (ctx.spec.abs value) := by
    dsimp only [ratio]
    rw [ctx.certificate.orderedField.mul_assoc,
      ctx.certificate.orderedField.inv_mul_cancel _ logNonzero,
      ctx.certificate.orderedField.mul_one]
  have logPositiveCast : ctx.spec.lt (ctx.spec.ofZ Z0) logarithm := by
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact logPositive
  have lowerBound := RIneq.Rmult_le_compat_r ctx logarithm (Exact.IZR ctx lower) ratio
    (RIneq.Rlt_le ctx _ _ logPositiveCast) (Raux.Zfloor_lb ctx ratio)
  have floorUpper : ctx.spec.lt ratio (ctx.spec.ofZ exponent) := by
    have result := Raux.Zfloor_ub ctx ratio
    change ctx.spec.lt ratio (ctx.spec.add (ctx.spec.ofZ lower) ctx.spec.one) at result
    change ctx.spec.lt ratio (ctx.spec.ofZ (Zadd lower Zone))
    rw [ctx.certificate.sourceLaws.ofZ_add, ctx.certificate.sourceLaws.ofZ_one]
    exact result
  have upperBound := RIneq.Rmult_lt_compat_r ctx logarithm ratio (Exact.IZR ctx exponent)
    logPositiveCast floorUpper
  change ctx.spec.le (ctx.spec.mul (ctx.spec.ofZ lower) logarithm)
    (ctx.spec.mul ratio logarithm) at lowerBound
  change ctx.spec.lt (ctx.spec.mul ratio logarithm)
    (ctx.spec.mul (ctx.spec.ofZ exponent) logarithm) at upperBound
  rw [product] at lowerBound upperBound
  have realLog : Raux.Exact.ln ctx (Exact.IZR ctx beta.radix_val) = logarithm := by
    change CompCert4Lean.Foundation.FlocqReal.ExactReal.ln ctx.spec
      (ctx.spec.ofZ beta.radix_val) = _
    unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.ln
    cases decision : ctx.spec.lt_dec ctx.spec.zero (ctx.spec.ofZ beta.radix_val) with
    | left proof => rfl
    | right proof => exact False.elim (proof basePositive)
  have power (powerExponent : Z) : Exact.bpow ctx beta powerExponent =
      ctx.spec.exp (ctx.spec.mul (ctx.spec.ofZ powerExponent) logarithm) := by
    have equation := Raux.bpow_exp ctx beta powerExponent
    change Exact.bpow ctx beta powerExponent =
      ctx.spec.exp (ctx.spec.mul (ctx.spec.ofZ powerExponent)
        (Raux.Exact.ln ctx (Exact.IZR ctx beta.radix_val))) at equation
    rw [realLog] at equation
    exact equation
  refine ⟨exponent, fun _ => ⟨?_, ?_⟩⟩
  · have predecessor : Zsub exponent Zone = lower := by
      apply intOfZ_injective
      simp only [exponent, Zadd, Zsub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      omega
    change ctx.spec.le (Exact.bpow ctx beta (Zsub exponent Zone)) (ctx.spec.abs value)
    rw [predecessor, power]
    have result := Raux.exp_le ctx _ _ lowerBound
    change ctx.spec.le _ (ctx.spec.exp (ctx.spec.ln (ctx.spec.abs value))) at result
    rw [ctx.certificate.ln.exp_ln _ absPositive] at result
    exact result
  · change ctx.spec.lt (ctx.spec.abs value) (Exact.bpow ctx beta exponent)
    rw [power]
    have result := ctx.certificate.exp.strict_monotone _ _ upperBound
    rw [ctx.certificate.ln.exp_ln _ absPositive] at result
    exact result

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals

private theorem ieee_subtract_finite {prec emax : Z}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    [certificate : Binary.BinaryNormalizeCertificate prec emax]
    (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (nan : binary_float prec emax → binary_float prec emax → NaNResult prec emax)
    (rounding : mode) (sign : Bool) (mantissaLeft : positive) (exponentLeft : Z)
    (mantissaRight : positive) (exponentRight : Z)
    (exactDifference : Exact.generic_format magnitude Zaux.radix2 (fexp prec emax)
      (Exact.Rminus ctx
        (Exact.B2R ctx (Binary.B754_finite sign mantissaLeft exponentLeft : binary_float prec emax))
        (Exact.B2R ctx (Binary.B754_finite false mantissaRight exponentRight : binary_float prec emax))))
    (smallDifference : Exact.Rlt ctx
      (Exact.Rabs ctx (Exact.Rminus ctx
        (Exact.B2R ctx (Binary.B754_finite sign mantissaLeft exponentLeft : binary_float prec emax))
        (Exact.B2R ctx (Binary.B754_finite false mantissaRight exponentRight : binary_float prec emax))))
      (Exact.bpow ctx Zaux.radix2 emax)) :
    Exact.B2R ctx (Binary.Bminus nan rounding
      (.B754_finite sign mantissaLeft exponentLeft)
      (.B754_finite false mantissaRight exponentRight)) =
      Exact.Rminus ctx
        (Exact.B2R ctx (Binary.B754_finite sign mantissaLeft exponentLeft : binary_float prec emax))
        (Exact.B2R ctx (Binary.B754_finite false mantissaRight exponentRight : binary_float prec emax)) ∧
    Binary.is_finite (Binary.Bminus nan rounding
      (.B754_finite sign mantissaLeft exponentLeft)
      (.B754_finite false mantissaRight exponentRight)) = true := by
  let exponent := ZArith.BinInt.Z.min exponentLeft exponentRight
  let mantissa := BinarySingleNaN.Fplus_naive sign mantissaLeft exponentLeft
    true mantissaRight exponentRight exponent
  let zeroSign := match rounding with | .mode_DN => true | _ => false
  have boundLeft : Zle exponent exponentLeft := by
    change intOfZ (ZArith.BinInt.Z.min exponentLeft exponentRight) ≤ intOfZ exponentLeft
    unfold ZArith.BinInt.Z.min
    split <;> omega
  have boundRight : Zle exponent exponentRight := by
    change intOfZ (ZArith.BinInt.Z.min exponentLeft exponentRight) ≤ intOfZ exponentRight
    unfold ZArith.BinInt.Z.min
    split <;> omega
  have encoding : Binary.Exact.F2R ctx (Binary.Float Zaux.radix2 mantissa exponent) =
      Exact.Rminus ctx
        (Exact.B2R ctx (Binary.B754_finite sign mantissaLeft exponentLeft : binary_float prec emax))
        (Exact.B2R ctx (Binary.B754_finite false mantissaRight exponentRight : binary_float prec emax)) := by
    have sum := BinarySingleNaN.Fplus_naive_correct ctx sign mantissaLeft exponentLeft
      true mantissaRight exponentRight exponent boundLeft boundRight
    dsimp only at sum
    exact sum.trans (congrArg (Exact.Rplus ctx _) (Float_prop.F2R_Zopp ctx Zaux.radix2
      (Zpos mantissaRight) exponentRight))
  have normalized := Binary.binary_normalize_correct (prec := prec) (emax := emax)
    ctx magnitude rounding mantissa exponent zeroSign
  dsimp only at normalized
  rw [encoding] at normalized
  have roundExact : Exact.round magnitude Zaux.radix2 (fexp prec emax)
      (Exact.round_mode ctx rounding)
      (Exact.Rminus ctx
        (Exact.B2R ctx (Binary.B754_finite sign mantissaLeft exponentLeft : binary_float prec emax))
        (Exact.B2R ctx (Binary.B754_finite false mantissaRight exponentRight : binary_float prec emax))) =
      Exact.Rminus ctx
        (Exact.B2R ctx (Binary.B754_finite sign mantissaLeft exponentLeft : binary_float prec emax))
        (Exact.B2R ctx (Binary.B754_finite false mantissaRight exponentRight : binary_float prec emax)) :=
    Generic_fmt.round_generic ctx magnitude Zaux.radix2 (fexp prec emax)
      (Exact.round_mode ctx rounding) (BinarySingleNaN.valid_rnd_round_mode_proof ctx rounding)
      _ exactDifference
  change (if Exact.Rlt_bool ctx
    (Exact.Rabs ctx (Exact.round magnitude Zaux.radix2 (fexp prec emax)
      (Exact.round_mode ctx rounding) _)) (Exact.bpow ctx Zaux.radix2 emax) then _ else _) at normalized
  rw [roundExact] at normalized
  have small : Exact.Rlt_bool ctx
      (Exact.Rabs ctx (Exact.Rminus ctx
        (Exact.B2R ctx (Binary.B754_finite sign mantissaLeft exponentLeft : binary_float prec emax))
        (Exact.B2R ctx (Binary.B754_finite false mantissaRight exponentRight : binary_float prec emax))))
      (Exact.bpow ctx Zaux.radix2 emax) = true := Raux.Rlt_bool_true ctx _ _ smallDifference
  rw [small] at normalized
  have operation : Binary.Bminus nan rounding
      (.B754_finite sign mantissaLeft exponentLeft) (.B754_finite false mantissaRight exponentRight) =
      Binary.binary_normalize rounding mantissa exponent zeroSign :=
    ieee_lift_non_nan _ _ (certificate.is_nan_binary_normalize rounding mantissa exponent zeroSign)
  rw [operation]
  exact ⟨normalized.1.trans roundExact, normalized.2.1⟩

theorem ZofB_minus :
    ∀ {prec emax : Z} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
      [Binary.BinaryNormalizeCertificate prec emax],
      ZofB_minusStatement (prec := prec) (emax := emax) := by
  intro prec emax precision maximum certificate nan rounding value integer offset converted range
    offsetBound ctx below
  classical
  let magnitude := Classical.choice (ieee_magnitude_exists ctx)
  have integerNonnegative : 0 ≤ intOfZ integer := range.1
  have integerBound : intOfZ integer < 2 * intOfZ offset := by
    have bound := range.2
    change intOfZ integer < intOfZ (Zmul Ztwo offset) at bound
    simp only [Zmul, ZArith.BinInt.Z.mul, intOfZ_zOfInt] at bound
    exact bound
  have offsetPositive : Zlt Z0 offset := by
    change 0 < intOfZ offset
    omega
  have offsetBounds : Zle (Zopp (Zpower Ztwo prec)) offset ∧ Zle offset (Zpower Ztwo prec) := by
    refine ⟨?_, offsetBound⟩
    change intOfZ (Zopp (Zpower Ztwo prec)) ≤ intOfZ offset
    simp only [Zopp, ZArith.BinInt.Z.opp, intOfZ_zOfInt]
    change intOfZ offset ≤ intOfZ (Zpower Ztwo prec) at offsetBound
    change 0 < intOfZ offset at offsetPositive
    omega
  have offsetValue := BofZ_exact (prec := prec) (emax := emax) ctx offset offsetBounds
  have castZero : Exact.IZR ctx Z0 = Exact.R0 ctx := ctx.certificate.sourceLaws.ofZ_zero
  have offsetRealPositive : Exact.Rlt ctx (Exact.R0 ctx) (Exact.IZR ctx offset) := by
    have positive := RIneq.IZR_lt ctx Z0 offset offsetPositive
    change Exact.Rlt ctx (Exact.IZR ctx Z0) (Exact.IZR ctx offset) at positive
    rw [castZero] at positive
    exact positive
  have valuePositive : Exact.Rlt ctx (Exact.R0 ctx) (Exact.B2R ctx value.1) :=
    RIneq.Rlt_le_trans ctx _ _ _ offsetRealPositive below
  have valueNonnegative : Exact.Rle ctx (Exact.R0 ctx) (Exact.B2R ctx value.1) :=
    RIneq.Rlt_le ctx _ _ valuePositive
  have finite : Binary.is_finite value.1 = true := by
    rcases value with ⟨value, valid⟩
    cases value <;> first | rfl | cases converted
  have upperInteger : Zle (Zadd integer Zone) (Zmul Ztwo offset) := by
    change intOfZ (Zadd integer Zone) ≤ intOfZ (Zmul Ztwo offset)
    simp only [Zadd, Zmul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    change intOfZ integer + 1 ≤ 2 * intOfZ offset
    omega
  have twice : Exact.IZR ctx (Zmul Ztwo offset) =
      Exact.Rplus ctx (Exact.IZR ctx offset) (Exact.IZR ctx offset) := by
    have twiceInteger : Zmul Ztwo offset = Zadd offset offset := by
      apply intOfZ_injective
      simp only [Zadd, Zmul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
      change 2 * intOfZ offset = intOfZ offset + intOfZ offset
      omega
    rw [twiceInteger]
    exact ctx.certificate.sourceLaws.ofZ_add offset offset
  have upper : Exact.Rlt ctx (Exact.B2R ctx value.1)
      (Exact.Rplus ctx (Exact.IZR ctx offset) (Exact.IZR ctx offset)) := by
    have result := RIneq.Rlt_le_trans ctx _ _ _
      (ZofB_range_nonneg value integer converted range.1 ctx).2
      (RIneq.IZR_le ctx _ _ upperInteger)
    change Exact.Rlt ctx (Exact.B2R ctx value.1) (Exact.IZR ctx (Zmul Ztwo offset)) at result
    rw [twice] at result
    exact result
  have differenceNonnegative : Exact.Rle ctx (Exact.R0 ctx)
      (Exact.Rminus ctx (Exact.B2R ctx value.1) (Exact.IZR ctx offset)) := by
    have result := RIneq.Rge_minus ctx (Exact.B2R ctx value.1) (Exact.IZR ctx offset) below
    change Exact.Rle ctx (Exact.IZR ctx Z0) _ at result
    rw [castZero] at result
    exact result
  have differenceSmall : Exact.Rlt ctx
      (Exact.Rminus ctx (Exact.B2R ctx value.1) (Exact.IZR ctx offset)) (Exact.IZR ctx offset) := by
    have result := RIneq.Rplus_lt_compat_r ctx (Exact.Ropp ctx (Exact.IZR ctx offset)) _ _ upper
    change ctx.spec.lt (ctx.spec.add _ (ctx.spec.neg (ctx.spec.ofZ offset)))
      (ctx.spec.add (ctx.spec.add (ctx.spec.ofZ offset) (ctx.spec.ofZ offset))
        (ctx.spec.neg (ctx.spec.ofZ offset))) at result
    rw [ctx.certificate.orderedField.add_assoc,
      ctx.certificate.orderedField.add_comm (ctx.spec.ofZ offset) (ctx.spec.neg (ctx.spec.ofZ offset)),
      ctx.certificate.orderedField.neg_add_cancel, ctx.certificate.orderedField.add_zero] at result
    exact result
  have powerBound : Exact.Rlt ctx (Exact.IZR ctx offset) (Exact.bpow ctx Zaux.radix2 emax) := by
    have precisionNonnegative : Zle Z0 prec := by
      have positive : 0 < intOfZ prec := precision
      change 0 ≤ intOfZ prec
      omega
    have power : Exact.IZR ctx (Zpower Ztwo prec) = Exact.bpow ctx Zaux.radix2 prec :=
      Raux.IZR_Zpower ctx Zaux.radix2 prec precisionNonnegative
    have bound := RIneq.IZR_le ctx offset (Zpower Ztwo prec) offsetBound
    change Exact.Rle ctx (Exact.IZR ctx offset) (Exact.IZR ctx (Zpower Ztwo prec)) at bound
    rw [power] at bound
    exact RIneq.Rle_lt_trans ctx _ _ _ bound
      (Raux.bpow_lt ctx Zaux.radix2 prec emax maximum.prec_lt_emax)
  have absoluteSmall : Exact.Rlt ctx
      (Exact.Rabs ctx (Exact.Rminus ctx (Exact.B2R ctx value.1) (Exact.IZR ctx offset)))
      (Exact.bpow ctx Zaux.radix2 emax) := by
    have absolute : Exact.Rabs ctx (Exact.Rminus ctx (Exact.B2R ctx value.1) (Exact.IZR ctx offset)) =
        Exact.Rminus ctx (Exact.B2R ctx value.1) (Exact.IZR ctx offset) :=
      ctx.certificate.sourceLaws.abs_nonnegative _ differenceNonnegative
    rw [absolute]
    exact ctx.certificate.orderedField.lt_trans _ _ _ differenceSmall powerBound
  have exactDifference : Exact.generic_format magnitude Zaux.radix2 (fexp prec emax)
      (Exact.Rminus ctx (Exact.B2R ctx value.1) (Exact.IZR ctx offset)) := by
    apply CompCert4Lean.Flocq.Prop.Sterbenz.sterbenz_aux ctx magnitude Zaux.radix2 (fexp prec emax)
      (FLT.FLT_exp_valid (emin prec emax) prec (h := precision))
      (FLT.FLT_exp_monotone (emin prec emax) prec)
    · exact Binary.generic_format_B2R ctx magnitude value
    · exact (integer_representable_n (prec := prec) (emax := emax) ctx magnitude offset offsetBounds).2
    · refine ⟨below, ?_⟩
      have twiceReal : Generic_fmt.Exact.Rmult ctx (Generic_fmt.Exact.Rtwo ctx) (Exact.IZR ctx offset) =
          Exact.Rplus ctx (Exact.IZR ctx offset) (Exact.IZR ctx offset) := by
        change ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one) (ctx.spec.ofZ offset) = _
        rw [ctx.certificate.orderedField.mul_comm, ctx.certificate.orderedField.left_distrib,
          ctx.certificate.orderedField.mul_one]
        rfl
      rw [twiceReal]
      exact RIneq.Rlt_le ctx _ _ upper
  have subtraction : Exact.B2R ctx (Binary.Bminus nan rounding value.1 (BofZ offset)) =
      Exact.Rminus ctx (Exact.B2R ctx value.1) (Exact.IZR ctx offset) ∧
      Binary.is_finite (Binary.Bminus nan rounding value.1 (BofZ offset)) = true := by
    rcases value with ⟨value, valid⟩
    cases value with
    | B754_zero sign => exact False.elim (ctx.certificate.orderedField.lt_irrefl _ valuePositive)
    | B754_infinity sign => cases converted
    | B754_nan sign payload => cases converted
    | B754_finite sign mantissa exponent =>
        generalize equation : BofZ (prec := prec) (emax := emax) offset = offsetFloat at offsetValue ⊢
        cases offsetFloat with
        | B754_zero sign =>
            have zeroValue : Exact.R0 ctx = Exact.IZR ctx offset := offsetValue.1
            rw [← zeroValue] at offsetRealPositive
            exact False.elim (ctx.certificate.orderedField.lt_irrefl _ offsetRealPositive)
        | B754_infinity sign => cases offsetValue.2.1
        | B754_nan sign payload => cases offsetValue.2.1
        | B754_finite offsetSign offsetMantissa offsetExponent =>
            have signFalse : offsetSign = false := by
              have negative : Zlt_bool offset Z0 = false := by
                change (if intOfZ offset < 0 then true else false) = false
                have positive : 0 < intOfZ offset := offsetPositive
                exact if_neg (by omega)
              exact offsetValue.2.2.trans negative
            subst offsetSign
            have format := exactDifference
            have bound := absoluteSmall
            rw [← offsetValue.1] at format bound
            have result := ieee_subtract_finite ctx magnitude nan rounding sign mantissa exponent
              offsetMantissa offsetExponent format bound
            rw [offsetValue.1] at result
            exact result
  have original := ZofB_correct value ctx
  change ZofB value.1 = (if Binary.is_finite value.1 then
    some (Exact.Ztrunc ctx (Exact.B2R ctx value.1)) else none) at original
  rw [finite] at original
  have originalTruncation : Exact.Ztrunc ctx (Exact.B2R ctx value.1) = integer :=
    Option.some.inj (original.symm.trans converted)
  have truncation : Exact.Ztrunc ctx (Exact.Rminus ctx (Exact.B2R ctx value.1) (Exact.IZR ctx offset)) =
      Zsub integer offset := by
    have differenceFloor : Exact.Ztrunc ctx
        (Exact.Rminus ctx (Exact.B2R ctx value.1) (Exact.IZR ctx offset)) =
        Exact.Zfloor ctx (Exact.Rminus ctx (Exact.B2R ctx value.1) (Exact.IZR ctx offset)) :=
      Raux.Ztrunc_floor ctx _ differenceNonnegative
    have originalFloor : Exact.Ztrunc ctx (Exact.B2R ctx value.1) =
        Exact.Zfloor ctx (Exact.B2R ctx value.1) := Raux.Ztrunc_floor ctx _ valueNonnegative
    rw [differenceFloor, Zfloor_minus ctx, ← originalFloor, originalTruncation]
  have result := ZofB_correct
    ⟨_, Binary.Bminus_result_obligation_proof nan rounding value
      ⟨_, BofZ_result_obligation_proof offset⟩⟩ ctx
  change ZofB (Binary.Bminus nan rounding value.1 (BofZ offset)) =
    (if Binary.is_finite (Binary.Bminus nan rounding value.1 (BofZ offset)) then
      some (Exact.Ztrunc ctx (Exact.B2R ctx (Binary.Bminus nan rounding value.1 (BofZ offset))))
      else none) at result
  rw [subtraction.2, subtraction.1, truncation] at result
  exact result

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem ZofB_range_minus :
    ∀ {prec emax : Z} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
      [Binary.BinaryNormalizeCertificate prec emax],
      ZofB_range_minusStatement (prec := prec) (emax := emax) := by
  intro prec emax precision maximum certificate nan rounding value integer offset converted bound ctx below
  obtain ⟨lower, upper, convertedInteger⟩ :=
    ZofB_range_inversion value Z0 (Zsub (Zmul Ztwo offset) Zone) integer converted
  have upperStrict : Zlt integer (Zmul Ztwo offset) := by
    change intOfZ integer ≤ intOfZ (Zsub (Zmul Ztwo offset) Zone) at upper
    simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] at upper
    change intOfZ integer < intOfZ (Zmul Ztwo offset)
    change intOfZ integer ≤ intOfZ (Zmul Ztwo offset) - 1 at upper
    omega
  have subtracted := ZofB_minus nan rounding value integer offset convertedInteger
    ⟨lower, upperStrict⟩ bound ctx below
  have lowerTest : Zle_bool (Zopp offset) (Zsub integer offset) = true := by
    change (if intOfZ (Zopp offset) ≤ intOfZ (Zsub integer offset) then true else false) = true
    apply if_pos
    simp only [Zopp, Zsub, ZArith.BinInt.Z.opp, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    change 0 ≤ intOfZ integer at lower
    omega
  have upperTest : Zle_bool (Zsub integer offset) (Zsub offset Zone) = true := by
    change (if intOfZ (Zsub integer offset) ≤ intOfZ (Zsub offset Zone) then true else false) = true
    apply if_pos
    simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    change intOfZ integer ≤ intOfZ (Zsub (Zmul Ztwo offset) Zone) at upper
    simp only [Zsub, Zmul, ZArith.BinInt.Z.sub, ZArith.BinInt.Z.mul, intOfZ_zOfInt] at upper
    change intOfZ integer ≤ 2 * intOfZ offset - 1 at upper
    change intOfZ integer - intOfZ offset ≤ intOfZ offset - 1
    omega
  unfold ZofB_range
  rw [subtracted]
  change (if Zle_bool (Zopp offset) (Zsub integer offset) &&
    Zle_bool (Zsub integer offset) (Zsub offset Zone) then some (Zsub integer offset) else none) = _
  rw [lowerTest, upperTest]
  rfl

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Flocq.IEEE754.BinarySingleNaN.IEEEManualRounding

private theorem ieee_scaled_iteration (base scaled : positive) (count shift : Nat)
    (scale : posToNat scaled = posToNat base * 2 ^ shift) :
    Zaux.iter_nat BinarySingleNaN.shr_1 (count + shift)
      (BinarySingleNaN.shr_record_of_loc (Zpos scaled) BinarySingleNaN.loc_Exact) =
    Zaux.iter_nat BinarySingleNaN.shr_1 count
      (BinarySingleNaN.shr_record_of_loc (Zpos base) BinarySingleNaN.loc_Exact) := by
  have scaledResult := manual_iter_encoding (count + shift)
    (BinarySingleNaN.shr_record_of_loc (Zpos scaled) BinarySingleNaN.loc_Exact)
    (Int.natCast_nonneg (posToNat scaled))
  have baseResult := manual_iter_encoding count
    (BinarySingleNaN.shr_record_of_loc (Zpos base) BinarySingleNaN.loc_Exact)
    (Int.natCast_nonneg (posToNat base))
  have integerScale : (posToNat scaled : Int) = (posToNat base : Int) * (2 : Int) ^ shift := by
    rw [scale, Int.natCast_mul, Int.natCast_pow]
    rfl
  have powerPositive : 0 < (2 : Int) ^ shift := Int.pow_pos (by decide)
  have encoding : manual_shift_encoding
      (BinarySingleNaN.shr_record_of_loc (Zpos scaled) BinarySingleNaN.loc_Exact) =
      manual_shift_encoding
        (BinarySingleNaN.shr_record_of_loc (Zpos base) BinarySingleNaN.loc_Exact) * (2 : Int) ^ shift := by
    change 2 * (posToNat scaled : Int) + 0 = (2 * (posToNat base : Int) + 0) * (2 : Int) ^ shift
    rw [integerScale]
    simp only [Int.add_zero, Int.mul_assoc]
  apply manual_record_ext
  · rw [scaledResult.2.1, baseResult.2.1, encoding, Int.pow_add]
    exact Int.mul_ediv_mul_of_pos_left _ _ powerPositive
  · rw [scaledResult.2.2, baseResult.2.2, encoding, Int.pow_add]
    simp only [← Int.dvd_iff_emod_eq_zero,
      Int.mul_dvd_mul_iff_right (Int.ne_of_gt powerPositive)]
    rfl

private theorem ieee_shr_fexp_scaled (prec emax : Z)
    (base scaled : positive) (baseExponent scaledExponent : Z) (shift : Nat)
    (scale : posToNat scaled = posToNat base * 2 ^ shift)
    (exponents : intOfZ baseExponent = intOfZ scaledExponent + shift)
    (aligned : Zle baseExponent
      (fexp prec emax (Zadd (Zpos (Digits.digits2_pos base)) baseExponent))) :
    BinarySingleNaN.shr_fexp (prec := prec) (emax := emax)
        (Zpos scaled) scaledExponent BinarySingleNaN.loc_Exact =
      BinarySingleNaN.shr_fexp (prec := prec) (emax := emax)
        (Zpos base) baseExponent BinarySingleNaN.loc_Exact := by
  have width : Zadd (Zpos (Digits.digits2_pos scaled)) scaledExponent =
      Zadd (Zpos (Digits.digits2_pos base)) baseExponent := by
    apply intOfZ_injective
    simp only [ieee_manual_add_int]
    change (posToNat (Digits.digits2_pos scaled) : Int) + intOfZ scaledExponent =
      (posToNat (Digits.digits2_pos base) : Int) + intOfZ baseExponent
    rw [ieee_manual_digits_nat, ieee_manual_digits_nat, scale,
      ieee_manual_log2_shift _ _ (posToNat_positive base)]
    omega
  let target := fexp prec emax (Zadd (Zpos (Digits.digits2_pos base)) baseExponent)
  have baseNonnegative : Zle Z0 (Zsub target baseExponent) := by
    change 0 ≤ intOfZ (Zsub target baseExponent)
    rw [ieee_manual_sub_int]
    exact Int.sub_nonneg_of_le aligned
  have scaledNonnegative : Zle Z0 (Zsub target scaledExponent) := by
    change 0 ≤ intOfZ (Zsub target scaledExponent)
    rw [ieee_manual_sub_int]
    change intOfZ baseExponent ≤ intOfZ target at aligned
    omega
  change BinarySingleNaN.shr _ scaledExponent
      (Zsub (fexp prec emax (Zadd (Zpos (Digits.digits2_pos scaled)) scaledExponent)) scaledExponent) =
    BinarySingleNaN.shr _ baseExponent (Zsub target baseExponent)
  rw [width]
  rw [BinarySingleNaN.shr_nat _ _ _ scaledNonnegative,
    BinarySingleNaN.shr_nat _ _ _ baseNonnegative]
  apply Prod.ext
  · have count : ZArith.BinInt.Z.to_nat (Zsub target scaledExponent) =
        ZArith.BinInt.Z.to_nat (Zsub target baseExponent) + shift := by
      change (intOfZ (Zsub target scaledExponent)).toNat =
        (intOfZ (Zsub target baseExponent)).toNat + shift
      rw [ieee_manual_sub_int, ieee_manual_sub_int]
      change intOfZ baseExponent ≤ intOfZ target at aligned
      omega
    dsimp only
    rw [count]
    exact ieee_scaled_iteration base scaled _ shift scale
  · apply intOfZ_injective
    simp only [ieee_manual_add_int, ieee_manual_sub_int]
    omega

private theorem ieee_round_aux_scaled (prec emax : Z)
    (rounding : mode) (sign : Bool)
    (base scaled : positive) (baseExponent scaledExponent : Z) (shift : Nat)
    (scale : posToNat scaled = posToNat base * 2 ^ shift)
    (exponents : intOfZ baseExponent = intOfZ scaledExponent + shift)
    (aligned : Zle baseExponent
      (fexp prec emax (Zadd (Zpos (Digits.digits2_pos base)) baseExponent))) :
    BinarySingleNaN.binary_round_aux (prec := prec) (emax := emax) rounding sign
      (Zpos scaled) scaledExponent BinarySingleNaN.loc_Exact =
    BinarySingleNaN.binary_round_aux (prec := prec) (emax := emax) rounding sign
      (Zpos base) baseExponent BinarySingleNaN.loc_Exact := by
  unfold BinarySingleNaN.binary_round_aux
  rw [ieee_shr_fexp_scaled prec emax base scaled baseExponent scaledExponent shift scale exponents aligned]

private theorem ieee_round_aligned (prec emax : Z) (rounding : mode) (sign : Bool)
    (mantissa : positive) (exponent : Z)
    (aligned : Zle exponent (fexp prec emax (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent))) :
    BinarySingleNaN.binary_round (prec := prec) (emax := emax) rounding sign mantissa exponent =
      BinarySingleNaN.binary_round_aux (prec := prec) (emax := emax)
        rounding sign (Zpos mantissa) exponent BinarySingleNaN.loc_Exact := by
  have alignment : BinarySingleNaN.shl_align_fexp (prec := prec) (emax := emax) mantissa exponent =
      (mantissa, exponent) := by
    change (match Zsub (fexp prec emax (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent)) exponent with
      | .Zneg amount => _ | _ => _) = _
    cases difference : Zsub (fexp prec emax (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent)) exponent with
    | Z0 => rfl
    | Zpos amount => rfl
    | Zneg amount =>
        have integerDifference := congrArg intOfZ difference
        rw [ieee_manual_sub_int] at integerDifference
        change _ = -(posToNat amount : Int) at integerDifference
        have positive := posToNat_positive amount
        change intOfZ exponent ≤ intOfZ _ at aligned
        omega
  unfold BinarySingleNaN.binary_round
  rw [alignment]

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem ieee_align_nat (mantissa : positive) (exponent target : Z)
    (ordered : Zle target exponent) :
    posToNat (BinarySingleNaN.shl_align mantissa exponent target).1 =
      posToNat mantissa * 2 ^ (intOfZ exponent - intOfZ target).toNat := by
  change posToNat (match Zsub target exponent with
    | .Zneg amount => (ZArith.Zpower.shift_pos amount mantissa, target)
    | _ => (mantissa, exponent)).1 = _
  cases difference : Zsub target exponent with
  | Z0 =>
      have integerDifference := congrArg intOfZ difference
      rw [ieee_manual_sub_int] at integerDifference
      change _ = 0 at integerDifference
      rw [show intOfZ exponent - intOfZ target = 0 by omega]
      simp
  | Zpos amount =>
      have integerDifference := congrArg intOfZ difference
      rw [ieee_manual_sub_int] at integerDifference
      change _ = (posToNat amount : Int) at integerDifference
      have positive := posToNat_positive amount
      change intOfZ target ≤ intOfZ exponent at ordered
      omega
  | Zneg amount =>
      have integerDifference := congrArg intOfZ difference
      rw [ieee_manual_sub_int] at integerDifference
      change _ = -(posToNat amount : Int) at integerDifference
      change posToNat (posOfNat (posToNat mantissa * 2 ^ posToNat amount)) = _
      rw [posToNat_posOfNat (Nat.mul_pos (posToNat_positive mantissa) (Nat.two_pow_pos _))]
      congr 2
      omega

private theorem ieee_bofz_two {prec emax : Z}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    [Binary.BinaryNormalizeCertificate prec emax] :
    BofZ (prec := prec) (emax := emax) Ztwo =
      Binary.B754_finite false (posOfNat (2 ^ ((intOfZ prec).toNat - 1))) (Zsub Ztwo prec) := by
  have precision : 0 < intOfZ prec := FLX.prec_gt_0 prec
  have maximum : intOfZ prec < intOfZ emax := BinarySingleNaN.prec_lt_emax
  let mantissa := posOfNat (2 ^ ((intOfZ prec).toNat - 1))
  let exponent := Zsub Ztwo prec
  have mantissaValue : posToNat mantissa = 2 ^ ((intOfZ prec).toNat - 1) :=
    posToNat_posOfNat (Nat.two_pow_pos _)
  have exponentValue : intOfZ exponent = 2 - intOfZ prec := ieee_manual_sub_int Ztwo prec
  have target : fexp prec emax (Zadd (Zpos (Digits.digits2_pos (.xO .xH))) Z0) = exponent := by
    apply intOfZ_injective
    rw [ieee_manual_fexp_int, ieee_manual_add_int, exponentValue]
    change max (2 + 0 - intOfZ prec) (3 - intOfZ emax - intOfZ prec) = 2 - intOfZ prec
    omega
  have canonical : fexp prec emax (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent) = exponent := by
    apply intOfZ_injective
    rw [ieee_manual_fexp_int, ieee_manual_add_int, exponentValue]
    change max ((posToNat (Digits.digits2_pos mantissa) : Int) + (2 - intOfZ prec) - intOfZ prec)
      (3 - intOfZ emax - intOfZ prec) = 2 - intOfZ prec
    rw [ieee_manual_digits_nat, mantissaValue, Nat.log2_two_pow]
    omega
  have bounded : Zle exponent (Zsub emax prec) := by
    change intOfZ exponent ≤ intOfZ (Zsub emax prec)
    rw [exponentValue, ieee_manual_sub_int]
    omega
  have rounded : BinarySingleNaN.binary_round (prec := prec) (emax := emax)
      mode_NE false (.xO .xH) Z0 = BinarySingleNaN.S754_finite false mantissa exponent := by
    by_cases oneBit : intOfZ prec = 1
    · have mantissaOne : mantissa = .xH := by
        apply posToNat_injective
        rw [mantissaValue, oneBit]
        rfl
      have exponentOne : exponent = Zone := by
        apply intOfZ_injective
        rw [exponentValue, oneBit]
        rfl
      have alignment : BinarySingleNaN.shl_align_fexp (prec := prec) (emax := emax) (.xO .xH) Z0 =
          (.xO .xH, Z0) := by
        change BinarySingleNaN.shl_align (.xO .xH) Z0
          (fexp prec emax (Zadd (Zpos (Digits.digits2_pos (.xO .xH))) Z0)) = _
        rw [target, exponentOne]
        rfl
      have first : BinarySingleNaN.shr_fexp (prec := prec) (emax := emax)
          (Zpos (.xO .xH)) Z0 BinarySingleNaN.loc_Exact =
          (BinarySingleNaN.shr_record_of_loc (Zpos mantissa) BinarySingleNaN.loc_Exact, exponent) := by
        change BinarySingleNaN.shr _ Z0
          (Zsub (fexp prec emax (Zadd (Zpos (Digits.digits2_pos (.xO .xH))) Z0)) Z0) = _
        rw [target, exponentOne, mantissaOne]
        rfl
      have second : BinarySingleNaN.shr_fexp (prec := prec) (emax := emax)
          (Zpos mantissa) exponent BinarySingleNaN.loc_Exact =
          (BinarySingleNaN.shr_record_of_loc (Zpos mantissa) BinarySingleNaN.loc_Exact, exponent) := by
        change BinarySingleNaN.shr _ exponent
          (Zsub (fexp prec emax (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent)) exponent) = _
        rw [canonical, show Zsub exponent exponent = Z0 by
          apply intOfZ_injective
          rw [ieee_manual_sub_int]
          change intOfZ exponent - intOfZ exponent = 0
          omega]
        rfl
      unfold BinarySingleNaN.binary_round
      rw [alignment]
      dsimp only
      unfold BinarySingleNaN.binary_round_aux
      rw [first]
      change (match BinarySingleNaN.shr_m (BinarySingleNaN.shr_fexp (prec := prec) (emax := emax)
          (Zpos mantissa) exponent BinarySingleNaN.loc_Exact).1 with
        | .Z0 => BinarySingleNaN.S754_zero false
        | .Zpos result => BinarySingleNaN.binary_fit_aux (prec := prec) (emax := emax)
          mode_NE false result (BinarySingleNaN.shr_fexp (prec := prec) (emax := emax)
            (Zpos mantissa) exponent BinarySingleNaN.loc_Exact).2
        | .Zneg _ => BinarySingleNaN.S754_nan) = _
      rw [second]
      change (if Zle_bool exponent (Zsub emax prec) then _ else _) = _
      have test : Zle_bool exponent (Zsub emax prec) = true := if_pos bounded
      rw [test]
      rfl
    · have exponentNonpositive : Zle exponent Z0 := by
        change intOfZ exponent ≤ 0
        rw [exponentValue]
        omega
      have alignment : BinarySingleNaN.shl_align_fexp (prec := prec) (emax := emax) (.xO .xH) Z0 =
          (mantissa, exponent) := by
        change BinarySingleNaN.shl_align (.xO .xH) Z0
          (fexp prec emax (Zadd (Zpos (Digits.digits2_pos (.xO .xH))) Z0)) = _
        rw [target]
        apply Prod.ext
        · apply posToNat_injective
          rw [ieee_align_nat _ _ _ exponentNonpositive, mantissaValue, exponentValue]
          change 2 * 2 ^ (0 - (2 - intOfZ prec)).toNat = 2 ^ ((intOfZ prec).toNat - 1)
          have power : (intOfZ prec).toNat - 1 = (0 - (2 - intOfZ prec)).toNat + 1 := by omega
          rw [power, Nat.pow_succ, Nat.mul_comm]
        · exact ieee_manual_align_exponent _ _ _ exponentNonpositive
      unfold BinarySingleNaN.binary_round
      rw [alignment]
      exact ieee_manual_round_canonical mode_NE false mantissa exponent canonical bounded
  apply ieee_manual_lift_finite
  change BinarySingleNaN.SF2B (BinarySingleNaN.binary_round mode_NE false (.xO .xH) Z0) = _
  rw [rounded]
  rfl

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem ieee_double_mult_round {prec emax : Z}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (rounding : mode) (sign : Bool) (mantissa : positive) (exponent : Z)
    (valid : Binary.bounded (prec := prec) (emax := emax) mantissa exponent = true) :
    BinarySingleNaN.binary_round_aux (prec := prec) (emax := emax) rounding sign
      (Zpos (PArith.BinPos.Pos.mul mantissa (posOfNat (2 ^ ((intOfZ prec).toNat - 1)))))
      (Zadd exponent (Zsub Ztwo prec)) BinarySingleNaN.loc_Exact =
    BinarySingleNaN.binary_round_aux (prec := prec) (emax := emax) rounding sign
      (Zpos (.xO mantissa)) exponent BinarySingleNaN.loc_Exact := by
  have precision : 0 < intOfZ prec := FLX.prec_gt_0 prec
  have canonical : fexp prec emax (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent) = exponent :=
    ZArith.Zbool.Zeq_bool_eq _ _ (Bool.and_eq_true_iff.mp valid).1
  have doubleDigits : intOfZ (Zpos (Digits.digits2_pos (.xO mantissa))) =
      intOfZ (Zpos (Digits.digits2_pos mantissa)) + 1 := by
    change (posToNat (PArith.BinPos.Pos.succ (Digits.digits2_pos mantissa)) : Int) = _
    rw [PArith.BinPos.Pos.posToNat_succ]
    rfl
  have aligned : Zle exponent (fexp prec emax (Zadd (Zpos (Digits.digits2_pos (.xO mantissa))) exponent)) := by
    have previous := congrArg intOfZ canonical
    rw [ieee_manual_fexp_int, ieee_manual_add_int] at previous
    change intOfZ exponent ≤ intOfZ _
    rw [ieee_manual_fexp_int, ieee_manual_add_int, doubleDigits]
    omega
  by_cases oneBit : intOfZ prec = 1
  · have oneMantissa : posOfNat (2 ^ ((intOfZ prec).toNat - 1)) = .xH := by rw [oneBit]; rfl
    have product : PArith.BinPos.Pos.mul mantissa .xH = mantissa := by
      apply posToNat_injective
      change posToNat (posOfNat (posToNat mantissa * 1)) = posToNat mantissa
      rw [Nat.mul_one, posToNat_posOfNat (posToNat_positive mantissa)]
    have exponentOne : Zsub Ztwo prec = Zone := by
      apply intOfZ_injective
      rw [ieee_manual_sub_int, oneBit]
      rfl
    rw [oneMantissa, product, exponentOne]
    have alignedOne : Zle (Zadd exponent Zone)
        (fexp prec emax (Zadd (Zpos (Digits.digits2_pos mantissa)) (Zadd exponent Zone))) := by
      change intOfZ (Zadd exponent Zone) ≤ intOfZ _
      rw [ieee_manual_fexp_int, ieee_manual_add_int, ieee_manual_add_int, oneBit]
      simp only [ieee_manual_add_int]
      have digitsPositive := posToNat_positive (Digits.digits2_pos mantissa)
      change intOfZ exponent + 1 ≤
        max ((posToNat (Digits.digits2_pos mantissa) : Int) + (intOfZ exponent + 1) - 1)
          (3 - intOfZ emax - 1)
      omega
    exact (ieee_round_aux_scaled prec emax rounding sign mantissa (.xO mantissa)
      (Zadd exponent Zone) exponent 1 (by change 2 * posToNat mantissa = posToNat mantissa * 2; omega)
      (by rw [ieee_manual_add_int]; rfl) alignedOne).symm
  · apply ieee_round_aux_scaled prec emax rounding sign (.xO mantissa)
      (PArith.BinPos.Pos.mul mantissa (posOfNat (2 ^ ((intOfZ prec).toNat - 1))))
      exponent (Zadd exponent (Zsub Ztwo prec)) ((intOfZ prec).toNat - 2)
    · have product : posToNat (PArith.BinPos.Pos.mul mantissa
          (posOfNat (2 ^ ((intOfZ prec).toNat - 1)))) =
          posToNat mantissa * 2 ^ ((intOfZ prec).toNat - 1) := by
        change posToNat (posOfNat (posToNat mantissa * posToNat (posOfNat _))) = _
        rw [posToNat_posOfNat (Nat.mul_pos (posToNat_positive mantissa)
          (posToNat_positive _)), posToNat_posOfNat (Nat.two_pow_pos _)]
      rw [product]
      have power : (intOfZ prec).toNat - 1 = ((intOfZ prec).toNat - 2) + 1 := by omega
      rw [power, Nat.pow_succ]
      change posToNat mantissa * (2 ^ ((intOfZ prec).toNat - 2) * 2) =
        (2 * posToNat mantissa) * 2 ^ ((intOfZ prec).toNat - 2)
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    · rw [ieee_manual_add_int, ieee_manual_sub_int]
      change intOfZ exponent = intOfZ exponent + (2 - intOfZ prec) + _
      omega
    · exact aligned

theorem Bmult2_Bplus :
    ∀ {prec emax : Z} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
      [Binary.BinaryNormalizeCertificate prec emax],
      Bmult2_BplusStatement (prec := prec) (emax := emax) := by
  intro prec emax precision maximum certificate plusNan multNan rounding value sameNan
  have two := ieee_bofz_two (prec := prec) (emax := emax)
  have twoValid := BofZ_result_obligation_proof (prec := prec) (emax := emax) Ztwo
  have twoFinite : Binary.is_finite (BofZ (prec := prec) (emax := emax) Ztwo) = true := by
    rw [two]
    rfl
  rcases value with ⟨value, valid⟩
  cases value with
  | B754_zero sign => rw [two]; cases sign <;> cases rounding <;> rfl
  | B754_infinity sign => rw [two]; cases sign <;> rfl
  | B754_nan sign payload =>
      have providers := sameNan ⟨.B754_nan sign payload, valid⟩ ⟨_, twoValid⟩ rfl twoFinite
      dsimp only at providers
      change Binary.BSN2B _ BinarySingleNaN.B754_nan = _
      unfold Binary.Bmult
      rw [two]
      change Binary.build_nan ⟨(plusNan (.B754_nan sign payload) (.B754_nan sign payload)).1, _⟩ =
        Binary.build_nan ⟨(multNan (.B754_nan sign payload)
          (.B754_finite false (posOfNat (2 ^ ((intOfZ prec).toNat - 1))) (Zsub Ztwo prec))).1, _⟩
      rw [two] at providers
      exact congrArg (fun result : NaNResult prec emax => Binary.build_nan ⟨result.1, result.2.1⟩) providers
  | B754_finite sign mantissa exponent =>
      have sameExponent : ZArith.BinInt.Z.min exponent exponent = exponent := if_pos (Int.le_refl _)
      have sameAlignment : BinarySingleNaN.shl_align mantissa exponent exponent = (mantissa, exponent) := by
        change (match Zsub exponent exponent with | .Zneg _ => _ | _ => _) = _
        rw [show Zsub exponent exponent = Z0 by
          apply intOfZ_injective
          rw [ieee_manual_sub_int]
          change intOfZ exponent - intOfZ exponent = 0
          omega]
      have doubleMantissa : BinarySingleNaN.Fplus_naive sign mantissa exponent sign mantissa exponent exponent =
          Zaux.cond_Zopp sign (Zpos (.xO mantissa)) := by
        change Zadd (Zaux.cond_Zopp sign (Zpos (BinarySingleNaN.shl_align mantissa exponent exponent).1))
          (Zaux.cond_Zopp sign (Zpos (BinarySingleNaN.shl_align mantissa exponent exponent).1)) = _
        rw [sameAlignment]
        apply intOfZ_injective
        cases sign with
        | false =>
            change intOfZ (zOfInt ((posToNat mantissa : Int) + posToNat mantissa)) =
              ((2 * posToNat mantissa : Nat) : Int)
            rw [intOfZ_zOfInt]
            omega
        | true =>
            change intOfZ (zOfInt (intOfZ (zOfInt (-(posToNat mantissa : Int))) +
              intOfZ (zOfInt (-(posToNat mantissa : Int))))) =
              intOfZ (zOfInt (-((2 * posToNat mantissa : Nat) : Int)))
            simp only [intOfZ_zOfInt]
            omega
      have doubleDigits : intOfZ (Zpos (Digits.digits2_pos (.xO mantissa))) =
          intOfZ (Zpos (Digits.digits2_pos mantissa)) + 1 := by
        change (posToNat (PArith.BinPos.Pos.succ (Digits.digits2_pos mantissa)) : Int) = _
        rw [PArith.BinPos.Pos.posToNat_succ]
        rfl
      have canonical : fexp prec emax (Zadd (Zpos (Digits.digits2_pos mantissa)) exponent) = exponent :=
        ZArith.Zbool.Zeq_bool_eq _ _ (Bool.and_eq_true_iff.mp valid).1
      have aligned : Zle exponent (fexp prec emax (Zadd (Zpos (Digits.digits2_pos (.xO mantissa))) exponent)) := by
        have previous := congrArg intOfZ canonical
        rw [ieee_manual_fexp_int, ieee_manual_add_int] at previous
        change intOfZ exponent ≤ intOfZ _
        rw [ieee_manual_fexp_int, ieee_manual_add_int, doubleDigits]
        omega
      have normalized : BinarySingleNaN.binary_normalize (prec := prec) (emax := emax) rounding
          (Zaux.cond_Zopp sign (Zpos (.xO mantissa))) exponent
          (match rounding with | .mode_DN => true | _ => false) =
          BinarySingleNaN.SF2B (BinarySingleNaN.binary_round (prec := prec) (emax := emax)
            rounding sign (.xO mantissa) exponent) := by
        cases sign with
        | false => rfl
        | true =>
            have negative : Zaux.cond_Zopp true (Zpos (.xO mantissa)) = Zneg (.xO mantissa) := by
              apply intOfZ_injective
              exact intOfZ_zOfInt _
            rw [negative]
            rfl
      have plusRaw : BinarySingleNaN.Bplus (prec := prec) (emax := emax) rounding
          (.B754_finite sign mantissa exponent) (.B754_finite sign mantissa exponent) =
          BinarySingleNaN.SF2B (BinarySingleNaN.binary_round_aux (prec := prec) (emax := emax)
            rounding sign (Zpos (.xO mantissa)) exponent BinarySingleNaN.loc_Exact) := by
        change BinarySingleNaN.binary_normalize rounding
          (BinarySingleNaN.Fplus_naive sign mantissa exponent sign mantissa exponent
            (ZArith.BinInt.Z.min exponent exponent)) (ZArith.BinInt.Z.min exponent exponent) _ = _
        rw [sameExponent, doubleMantissa]
        exact normalized.trans (congrArg (BinarySingleNaN.SF2B (prec := prec) (emax := emax))
          (ieee_round_aligned prec emax rounding sign _ _ aligned))
      have multRaw : BinarySingleNaN.Bmult (prec := prec) (emax := emax) rounding
          (.B754_finite sign mantissa exponent)
          (.B754_finite false (posOfNat (2 ^ ((intOfZ prec).toNat - 1))) (Zsub Ztwo prec)) =
          BinarySingleNaN.SF2B (BinarySingleNaN.binary_round_aux (prec := prec) (emax := emax)
            rounding sign (Zpos (.xO mantissa)) exponent BinarySingleNaN.loc_Exact) := by
        unfold BinarySingleNaN.Bmult
        simp only [Bool.xor_false]
        rw [ieee_double_mult_round rounding sign mantissa exponent valid]
      have notNan : BinarySingleNaN.is_nan
          (BinarySingleNaN.Bplus (prec := prec) (emax := emax) rounding
            (.B754_finite sign mantissa exponent) (.B754_finite sign mantissa exponent)) = false :=
        certificate.is_nan_binary_normalize rounding _ _ _
      rw [plusRaw] at notNan
      rw [two]
      unfold Binary.Bplus Binary.Bmult
      change Binary.BSN2B _ (BinarySingleNaN.Bplus rounding
        (.B754_finite sign mantissa exponent) (.B754_finite sign mantissa exponent)) =
        Binary.BSN2B _ (BinarySingleNaN.Bmult rounding (.B754_finite sign mantissa exponent)
          (.B754_finite false (posOfNat (2 ^ ((intOfZ prec).toNat - 1))) (Zsub Ztwo prec)))
      rw [plusRaw, multRaw]
      rw [ieee_lift_non_nan _ _ notNan, ieee_lift_non_nan _ _ notNan]

end CompCert4Lean.Lib.IEEE754_extra

namespace CompCert4Lean.Lib.IEEE754_extra

open CompCert4Lean.Flocq.Core
open CompCert4Lean.Flocq.IEEE754
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Flocq.IEEE754.BinarySingleNaN.IEEEManualRounding
open ManualValidity
open CompCert4Lean.Flocq

private theorem ieee_record_reconstruct (record : BinarySingleNaN.shr_record) :
    BinarySingleNaN.shr_record_of_loc (BinarySingleNaN.shr_m record)
      (BinarySingleNaN.loc_of_shr_record record) = record := by
  rcases record with ⟨mantissa, rounding, sticky⟩
  cases rounding <;> cases sticky <;> rfl

private theorem ieee_shr_fexp_partial {prec emax : Z} [Prec_gt_0 prec]
    (mantissa exponent intermediate : Z) (position : BinarySingleNaN.location) (count : Nat)
    (nonnegative : Zle Z0 mantissa)
    (exponents : intOfZ intermediate = intOfZ exponent + count)
    (bounded : Zle intermediate (fexp prec emax (Zadd (Digits.Zdigits2 mantissa) exponent))) :
    let record := Zaux.iter_nat BinarySingleNaN.shr_1 count
      (BinarySingleNaN.shr_record_of_loc mantissa position)
    BinarySingleNaN.shr_fexp (prec := prec) (emax := emax)
        (BinarySingleNaN.shr_m record) intermediate (BinarySingleNaN.loc_of_shr_record record) =
      BinarySingleNaN.shr_fexp (prec := prec) (emax := emax) mantissa exponent position := by
  let record := Zaux.iter_nat BinarySingleNaN.shr_1 count
    (BinarySingleNaN.shr_record_of_loc mantissa position)
  let target := fexp prec emax (Zadd (Digits.Zdigits2 mantissa) exponent)
  have recordMantissa : Binary.shr_m (BinarySingleNaN.shr_record_of_loc mantissa position) = mantissa :=
    BinarySingleNaN.shr_m_shr_record_of_loc mantissa position
  have width := binary_width_shr_iter (BinarySingleNaN.shr_record_of_loc mantissa position)
    count (by rw [recordMantissa]; exact nonnegative)
  rw [recordMantissa] at width
  have precision := FLX.prec_gt_0 prec
  change 0 < intOfZ prec at precision
  have targetValue : intOfZ target =
      max ((binary_width mantissa : Int) + intOfZ exponent - intOfZ prec)
        (3 - intOfZ emax - intOfZ prec) := by
    rw [ieee_manual_fexp_int, ieee_manual_add_int, binary_width_digits]
  have targetSame : fexp prec emax (Zadd (Digits.Zdigits2 (BinarySingleNaN.shr_m record)) intermediate) =
      target := by
    apply intOfZ_injective
    rw [ieee_manual_fexp_int, ieee_manual_add_int, binary_width_digits, targetValue]
    change max ((binary_width (BinarySingleNaN.shr_m record) : Int) + intOfZ intermediate -
      intOfZ prec) (3 - intOfZ emax - intOfZ prec) = _
    rw [show binary_width (BinarySingleNaN.shr_m record) = binary_width mantissa - count from width.2]
    change intOfZ intermediate ≤ intOfZ target at bounded
    rw [targetValue] at bounded
    omega
  have afterNonnegative : Zle Z0 (Zsub target intermediate) := by
    change 0 ≤ intOfZ (Zsub target intermediate)
    rw [ieee_manual_sub_int]
    exact Int.sub_nonneg_of_le bounded
  have beforeNonnegative : Zle Z0 (Zsub target exponent) := by
    change 0 ≤ intOfZ (Zsub target exponent)
    rw [ieee_manual_sub_int]
    change intOfZ intermediate ≤ intOfZ target at bounded
    omega
  change BinarySingleNaN.shr (BinarySingleNaN.shr_record_of_loc (BinarySingleNaN.shr_m record)
    (BinarySingleNaN.loc_of_shr_record record)) intermediate
    (Zsub (fexp prec emax (Zadd (Digits.Zdigits2 (BinarySingleNaN.shr_m record)) intermediate)) intermediate) =
    BinarySingleNaN.shr (BinarySingleNaN.shr_record_of_loc mantissa position) exponent (Zsub target exponent)
  rw [ieee_record_reconstruct, targetSame, BinarySingleNaN.shr_nat _ _ _ afterNonnegative,
    BinarySingleNaN.shr_nat _ _ _ beforeNonnegative]
  apply Prod.ext
  · have counts : ZArith.BinInt.Z.to_nat (Zsub target exponent) =
        ZArith.BinInt.Z.to_nat (Zsub target intermediate) + count := by
      change (intOfZ (Zsub target exponent)).toNat =
        (intOfZ (Zsub target intermediate)).toNat + count
      rw [ieee_manual_sub_int, ieee_manual_sub_int]
      change intOfZ intermediate ≤ intOfZ target at bounded
      omega
    dsimp only
    rw [counts, Zaux.iter_nat_plus]
  · apply intOfZ_injective
    simp only [ieee_manual_add_int, ieee_manual_sub_int]
    omega

private theorem ieee_binary_new_location (divisor remainder : Z) :
    Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.new_location divisor remainder =
      Calc.Bracket.new_location divisor remainder BinarySingleNaN.loc_Exact := by
  unfold Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.new_location Calc.Bracket.new_location
  split
  · change (if ZArith.Zbool.Zeq_bool remainder Z0 then BinarySingleNaN.loc_Exact
      else BinarySingleNaN.loc_Inexact (ZArith.BinInt.Z.compare (Zmul Ztwo remainder) divisor)) =
      (if ZArith.Zbool.Zeq_bool remainder Z0 then BinarySingleNaN.loc_Exact else BinarySingleNaN.loc_Inexact
        (match ZArith.BinInt.Z.compare (Zmul Ztwo remainder) divisor with | .Lt => .Lt | .Eq => .Eq | .Gt => .Gt))
    split
    · rfl
    · cases ZArith.BinInt.Z.compare (Zmul Ztwo remainder) divisor <;> rfl
  · unfold Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.new_location_odd Calc.Bracket.new_location_odd
    split
    · rfl
    · change BinarySingleNaN.loc_Inexact
          (match ZArith.BinInt.Z.compare (Zadd (Zmul Ztwo remainder) Zone) divisor with
          | .Eq => .Lt | choice => choice) =
        BinarySingleNaN.loc_Inexact
          (match ZArith.BinInt.Z.compare (Zadd (Zmul Ztwo remainder) Zone) divisor with
          | .Lt => .Lt | .Eq => .Lt | .Gt => .Gt)
      cases ZArith.BinInt.Z.compare (Zadd (Zmul Ztwo remainder) Zone) divisor <;> rfl

private theorem ieee_division_record (mantissa : positive) (count : Nat) :
    BinarySingleNaN.shr_record_of_loc
      (ZArith.BinInt.Z.div (Zpos mantissa) (zOfInt ((2 : Int) ^ count)))
      (Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.new_location (zOfInt ((2 : Int) ^ count))
        (ZArith.BinInt.Z.modulo (Zpos mantissa) (zOfInt ((2 : Int) ^ count)))) =
      Zaux.iter_nat BinarySingleNaN.shr_1 count
        (BinarySingleNaN.shr_record_of_loc (Zpos mantissa) BinarySingleNaN.loc_Exact) := by
  rw [ieee_binary_new_location]
  cases count with
  | zero =>
      rw [show (2 : Int) ^ 0 = 1 from rfl]
      have quotient : ZArith.BinInt.Z.div (Zpos mantissa) (zOfInt 1) = Zpos mantissa := by
        exact (manual_source_div (Zpos mantissa) 1 (by decide)).trans
          (by rw [Int.ediv_one, zOfInt_intOfZ])
      have remainder : ZArith.BinInt.Z.modulo (Zpos mantissa) (zOfInt 1) = Z0 := by
        exact (manual_source_mod (Zpos mantissa) 1 (by decide)).trans
          (by rw [Int.emod_one]; rfl)
      rw [quotient, remainder]
      rfl
  | succ count =>
      exact (manual_iter_record (count + 1) (by omega)
        (BinarySingleNaN.shr_record_of_loc (Zpos mantissa) BinarySingleNaN.loc_Exact)
        (Int.natCast_nonneg _)).symm

private theorem ieee_shr_fexp_common (prec emax : Z)
    (base left right : positive) (leftExponent rightExponent : Z)
    (leftShift rightShift : Nat)
    (leftScale : posToNat left = posToNat base * 2 ^ leftShift)
    (rightScale : posToNat right = posToNat base * 2 ^ rightShift)
    (exponents : intOfZ leftExponent + leftShift = intOfZ rightExponent + rightShift)
    (leftAligned : Zle leftExponent
      (fexp prec emax (Zadd (Zpos (Digits.digits2_pos left)) leftExponent)))
    (rightAligned : Zle rightExponent
      (fexp prec emax (Zadd (Zpos (Digits.digits2_pos right)) rightExponent))) :
    BinarySingleNaN.shr_fexp (prec := prec) (emax := emax)
        (Zpos left) leftExponent BinarySingleNaN.loc_Exact =
      BinarySingleNaN.shr_fexp (prec := prec) (emax := emax)
        (Zpos right) rightExponent BinarySingleNaN.loc_Exact := by
  let common := posOfNat (posToNat base * 2 ^ (leftShift + rightShift))
  let commonExponent := zOfInt (intOfZ leftExponent - rightShift)
  have commonValue : posToNat common = posToNat base * 2 ^ (leftShift + rightShift) :=
    posToNat_posOfNat (Nat.mul_pos (posToNat_positive base) (Nat.two_pow_pos _))
  have leftEquality := ieee_shr_fexp_scaled prec emax left common leftExponent commonExponent rightShift
    (by rw [commonValue, leftScale, Nat.pow_add, Nat.mul_assoc])
    (by change _ = intOfZ (zOfInt _) + _; rw [intOfZ_zOfInt]; omega) leftAligned
  have rightEquality := ieee_shr_fexp_scaled prec emax right common rightExponent commonExponent leftShift
    (by rw [commonValue, rightScale, Nat.pow_add]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm])
    (by change _ = intOfZ (zOfInt _) + _; rw [intOfZ_zOfInt]; omega) rightAligned
  exact leftEquality.symm.trans rightEquality

private theorem ieee_scaled_digits (base scaled : positive) (shift : Nat)
    (scale : posToNat scaled = posToNat base * 2 ^ shift) :
    intOfZ (Digits.Zdigits2 (Zpos scaled)) = intOfZ (Digits.Zdigits2 (Zpos base)) + shift := by
  change (posToNat (Digits.digits2_pos scaled) : Int) =
    (posToNat (Digits.digits2_pos base) : Int) + shift
  rw [ieee_manual_digits_nat, ieee_manual_digits_nat, scale,
    ieee_manual_log2_shift _ _ (posToNat_positive base)]
  omega

private theorem ieee_inverse_round {prec emax : Z} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (rounding : mode) (sign : Bool) (mantissa : positive) (exponent divisorExponent : Z) :
    let divisor := Bexact_inverse_mantissa (prec := prec)
    let result := BinarySingleNaN.SFdiv_core_binary prec emax
      (Zpos mantissa) exponent (Zpos divisor) divisorExponent
    BinarySingleNaN.binary_round_aux (prec := prec) (emax := emax)
        rounding sign result.1.1 result.1.2 result.2 =
      BinarySingleNaN.binary_round_aux (prec := prec) (emax := emax) rounding sign
        (Zpos (PArith.BinPos.Pos.mul mantissa divisor))
        (Zadd exponent (Zsub (Zopp divisorExponent) (Zmul (Zsub prec Zone) Ztwo)))
        BinarySingleNaN.loc_Exact := by
  let divisor := Bexact_inverse_mantissa (prec := prec)
  let half := (intOfZ prec - 1).toNat
  have precision := FLX.prec_gt_0 prec
  change 0 < intOfZ prec at precision
  have halfValue : (half : Int) = intOfZ prec - 1 := by omega
  have divisorValue : Zpos divisor = zOfInt ((2 : Int) ^ half) := by
    have value := Bexact_inverse_mantissa_value (prec := prec)
    change Zpos divisor = Zpower Ztwo (Zsub prec Zone) at value
    rw [value]
    change (if intOfZ (Zsub prec Zone) < 0 then Z0
      else zOfInt ((2 : Int) ^ (intOfZ (Zsub prec Zone)).toNat)) = _
    rw [ieee_manual_sub_int]
    change (if intOfZ prec - 1 < 0 then Z0 else zOfInt ((2 : Int) ^ half)) = _
    rw [if_neg (by omega)]
  have divisorScale : posToNat divisor = 2 ^ half := by
    have value := congrArg intOfZ divisorValue
    rw [intOfZ_zOfInt] at value
    change (posToNat divisor : Int) = (2 : Int) ^ half at value
    exact_mod_cast value
  have divisorDigits : Digits.Zdigits2 (Zpos divisor) = prec :=
    Bexact_inverse_mantissa_digits2_pos (prec := prec) (emax := emax)
  let delta := Zsub exponent divisorExponent
  let magnitude := Zsub (Zadd (Digits.Zdigits2 (Zpos mantissa)) exponent)
    (Zadd (Digits.Zdigits2 (Zpos divisor)) divisorExponent)
  let divisionExponent := ZArith.BinInt.Z.min (fexp prec emax magnitude) delta
  have deltaValue : intOfZ delta = intOfZ exponent - intOfZ divisorExponent := ieee_manual_sub_int _ _
  have divisionValue : intOfZ divisionExponent =
      min (max (intOfZ (Digits.Zdigits2 (Zpos mantissa)) + intOfZ delta - 2 * intOfZ prec)
        (3 - intOfZ emax - intOfZ prec)) (intOfZ delta) := by
    have minimum (left right : Z) : intOfZ (ZArith.BinInt.Z.min left right) = min (intOfZ left) (intOfZ right) := by
      unfold ZArith.BinInt.Z.min
      split <;> omega
    rw [minimum, ieee_manual_fexp_int]
    dsimp only [magnitude]
    rw [ieee_manual_sub_int, ieee_manual_add_int, ieee_manual_add_int, divisorDigits]
    congr 2
    omega
  let shift := (intOfZ delta - intOfZ divisionExponent).toNat
  have shiftValue : (shift : Int) = intOfZ delta - intOfZ divisionExponent := by
    rw [divisionValue]
    dsimp only [shift]
    rw [divisionValue]
    omega
  let shifted := posOfNat (posToNat mantissa * 2 ^ shift)
  have shiftedScale : posToNat shifted = posToNat mantissa * 2 ^ shift :=
    posToNat_posOfNat (Nat.mul_pos (posToNat_positive mantissa) (Nat.two_pow_pos _))
  let shiftedExponent := zOfInt (intOfZ divisionExponent - half)
  have shiftedExponentValue : intOfZ shiftedExponent = intOfZ divisionExponent - half := intOfZ_zOfInt _
  let product := PArith.BinPos.Pos.mul mantissa divisor
  let productExponent := Zadd exponent (Zsub (Zopp divisorExponent) (Zmul (Zsub prec Zone) Ztwo))
  have productExponentValue : intOfZ productExponent = intOfZ delta - 2 * half := by
    simp only [productExponent, Zadd, Zsub, Zopp, Zmul, ZArith.BinInt.Z.add,
      ZArith.BinInt.Z.sub, ZArith.BinInt.Z.opp, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    change intOfZ exponent + (-intOfZ divisorExponent - (intOfZ prec - 1) * 2) = _
    omega
  have productScale : posToNat product = posToNat mantissa * 2 ^ half := by
    change posToNat (posOfNat (posToNat mantissa * posToNat divisor)) = _
    rw [posToNat_posOfNat (Nat.mul_pos (posToNat_positive _) (posToNat_positive _)), divisorScale]
  have shiftedDigits := ieee_scaled_digits mantissa shifted shift shiftedScale
  have productDigits := ieee_scaled_digits mantissa product half productScale
  have mantissaDigitsPositive : 0 < intOfZ (Digits.Zdigits2 (Zpos mantissa)) :=
    Int.natCast_pos.mpr (posToNat_positive _)
  have divisionBelow : Zle divisionExponent
      (fexp prec emax (Zadd (Digits.Zdigits2 (Zpos shifted)) shiftedExponent)) := by
    change intOfZ divisionExponent ≤ intOfZ _
    rw [ieee_manual_fexp_int, ieee_manual_add_int, shiftedDigits, shiftedExponentValue]
    rw [divisionValue] at shiftValue ⊢
    omega
  have shiftedAligned : Zle shiftedExponent
      (fexp prec emax (Zadd (Digits.Zdigits2 (Zpos shifted)) shiftedExponent)) := by
    change intOfZ shiftedExponent ≤ intOfZ _
    exact Int.le_trans (by rw [shiftedExponentValue]; omega) divisionBelow
  have productAligned : Zle productExponent
      (fexp prec emax (Zadd (Digits.Zdigits2 (Zpos product)) productExponent)) := by
    change intOfZ productExponent ≤ intOfZ _
    rw [ieee_manual_fexp_int, ieee_manual_add_int (Digits.Zdigits2 (Zpos product)) productExponent,
      productDigits, productExponentValue]
    omega
  have common := ieee_shr_fexp_common prec emax mantissa shifted product shiftedExponent productExponent
    shift half shiftedScale productScale (by rw [shiftedExponentValue, productExponentValue]; omega)
    shiftedAligned productAligned
  have partialShift := ieee_shr_fexp_partial (prec := prec) (emax := emax)
    (Zpos shifted) shiftedExponent divisionExponent BinarySingleNaN.loc_Exact half
    (Int.natCast_nonneg _) (by rw [shiftedExponentValue]; omega) divisionBelow
  have shiftInput : (match Zsub delta divisionExponent with
      | .Zpos _ => ZArith.BinInt.Z.shiftl (Zpos mantissa) (Zsub delta divisionExponent)
      | .Z0 => Zpos mantissa
      | .Zneg _ => Z0) = Zpos shifted := by
    have amountValue : intOfZ (Zsub delta divisionExponent) = (shift : Int) := by
      rw [ieee_manual_sub_int]
      omega
    cases amount : Zsub delta divisionExponent with
    | Z0 =>
        have zero : shift = 0 := by rw [amount] at amountValue; change 0 = _ at amountValue; omega
        apply intOfZ_injective
        change (posToNat mantissa : Int) = (posToNat shifted : Int)
        rw [shiftedScale, zero, Nat.pow_zero, Nat.mul_one]
    | Zpos count =>
        rw [amount] at amountValue
        change (posToNat count : Int) = (shift : Int) at amountValue
        change (if 0 ≤ (posToNat count : Int)
          then zOfInt ((posToNat mantissa : Int) * (2 : Int) ^ posToNat count)
          else _) = Zpos shifted
        rw [if_pos (Int.natCast_nonneg _)]
        apply intOfZ_injective
        rw [intOfZ_zOfInt]
        change _ = (posToNat shifted : Int)
        rw [shiftedScale, show posToNat count = shift by omega, Int.natCast_mul, Int.natCast_pow]
        rfl
    | Zneg count =>
        rw [amount] at amountValue
        change -(posToNat count : Int) = (shift : Int) at amountValue
        have positive := posToNat_positive count
        omega
  have core : BinarySingleNaN.SFdiv_core_binary prec emax
      (Zpos mantissa) exponent (Zpos divisor) divisorExponent =
      ((ZArith.BinInt.Z.div (Zpos shifted) (zOfInt ((2 : Int) ^ half)), divisionExponent),
        Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.new_location (zOfInt ((2 : Int) ^ half))
          (ZArith.BinInt.Z.modulo (Zpos shifted) (zOfInt ((2 : Int) ^ half)))) := by
    change (((ZArith.BinInt.Z.div_eucl
      (match Zsub delta divisionExponent with
        | .Zpos _ => ZArith.BinInt.Z.shiftl (Zpos mantissa) (Zsub delta divisionExponent)
        | .Z0 => Zpos mantissa | .Zneg _ => Z0) (Zpos divisor)).1, divisionExponent),
      Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.new_location (Zpos divisor)
        (ZArith.BinInt.Z.div_eucl
          (match Zsub delta divisionExponent with
            | .Zpos _ => ZArith.BinInt.Z.shiftl (Zpos mantissa) (Zsub delta divisionExponent)
            | .Z0 => Zpos mantissa | .Zneg _ => Z0) (Zpos divisor)).2) = _
    rw [shiftInput, divisorValue]
    rfl
  let quotient := ZArith.BinInt.Z.div (Zpos shifted) (zOfInt ((2 : Int) ^ half))
  let location := Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.new_location (zOfInt ((2 : Int) ^ half))
    (ZArith.BinInt.Z.modulo (Zpos shifted) (zOfInt ((2 : Int) ^ half)))
  have divisionRecord : BinarySingleNaN.shr_record_of_loc quotient location =
      Zaux.iter_nat BinarySingleNaN.shr_1 half
        (BinarySingleNaN.shr_record_of_loc (Zpos shifted) BinarySingleNaN.loc_Exact) :=
    ieee_division_record shifted half
  dsimp only at partialShift
  rw [← divisionRecord, BinarySingleNaN.shr_m_shr_record_of_loc,
    BinarySingleNaN.loc_of_shr_record_of_loc] at partialShift
  change BinarySingleNaN.binary_round_aux rounding sign
    (BinarySingleNaN.SFdiv_core_binary prec emax (Zpos mantissa) exponent (Zpos divisor) divisorExponent).1.1
    (BinarySingleNaN.SFdiv_core_binary prec emax (Zpos mantissa) exponent (Zpos divisor) divisorExponent).1.2
    (BinarySingleNaN.SFdiv_core_binary prec emax (Zpos mantissa) exponent (Zpos divisor) divisorExponent).2 = _
  rw [core]
  change BinarySingleNaN.binary_round_aux rounding sign quotient divisionExponent location =
    BinarySingleNaN.binary_round_aux rounding sign (Zpos product) productExponent BinarySingleNaN.loc_Exact
  unfold BinarySingleNaN.binary_round_aux
  rw [partialShift, common]

private theorem ieee_round_aux_non_nan (prec emax : Z)
    (rounding : mode) (sign : Bool) (mantissa exponent : Z) (position : BinarySingleNaN.location)
    (nonnegative : Zle Z0 mantissa) :
    BinarySingleNaN.is_nan (BinarySingleNaN.SF2B (prec := prec) (emax := emax)
      (BinarySingleNaN.binary_round_aux (prec := prec) (emax := emax)
        rounding sign mantissa exponent position)) = false := by
  have shiftNonnegative (value power : Z) (place : BinarySingleNaN.location)
      (positive : Zle Z0 value) :
      Zle Z0 (BinarySingleNaN.shr_m
        (BinarySingleNaN.shr_fexp (prec := prec) (emax := emax) value power place).1) := by
    have recordMantissa : BinarySingleNaN.shr_m (BinarySingleNaN.shr_record_of_loc value place) = value :=
      BinarySingleNaN.shr_m_shr_record_of_loc value place
    change Zle Z0 (BinarySingleNaN.shr_m (BinarySingleNaN.shr
      (BinarySingleNaN.shr_record_of_loc value place) power
      (Zsub (fexp prec emax (Zadd (Digits.Zdigits2 value) power)) power)).1)
    cases amount : Zsub (fexp prec emax (Zadd (Digits.Zdigits2 value) power)) power with
    | Z0 =>
        change Zle Z0 (BinarySingleNaN.shr_m (BinarySingleNaN.shr_record_of_loc value place))
        rw [recordMantissa]
        exact positive
    | Zneg count =>
        change Zle Z0 (BinarySingleNaN.shr_m (BinarySingleNaN.shr_record_of_loc value place))
        rw [recordMantissa]
        exact positive
    | Zpos count =>
        rw [BinarySingleNaN.shr_nat _ _ (Zpos count) (Int.natCast_nonneg _)]
        exact (binary_width_shr_iter (BinarySingleNaN.shr_record_of_loc value place) (posToNat count)
          (by change Zle Z0 (BinarySingleNaN.shr_m _); rw [recordMantissa]; exact positive)).1
  let first := BinarySingleNaN.shr_fexp (prec := prec) (emax := emax) mantissa exponent position
  have firstNonnegative := shiftNonnegative mantissa exponent position nonnegative
  let chosen := BinarySingleNaN.choice_mode rounding sign
    (BinarySingleNaN.shr_m first.1) (BinarySingleNaN.loc_of_shr_record first.1)
  have chosenNonnegative : Zle Z0 chosen :=
    Int.le_trans firstNonnegative (binary_choice_increases rounding sign _ _)
  let second := BinarySingleNaN.shr_fexp (prec := prec) (emax := emax)
    chosen first.2 BinarySingleNaN.loc_Exact
  have secondNonnegative := shiftNonnegative chosen first.2 BinarySingleNaN.loc_Exact chosenNonnegative
  change BinarySingleNaN.is_nan (BinarySingleNaN.SF2B
    (match BinarySingleNaN.shr_m second.1 with
      | .Z0 => .S754_zero sign
      | .Zpos result => BinarySingleNaN.binary_fit_aux (prec := prec) (emax := emax) rounding sign result second.2
      | .Zneg _ => .S754_nan)) = false
  cases resultValue : BinarySingleNaN.shr_m second.1 with
  | Z0 => rfl
  | Zpos resultMantissa =>
      change BinarySingleNaN.is_nan (BinarySingleNaN.SF2B
        (BinarySingleNaN.binary_fit_aux (prec := prec) (emax := emax) rounding sign resultMantissa second.2)) = false
      unfold BinarySingleNaN.binary_fit_aux
      split
      · rfl
      · unfold BinarySingleNaN.binary_overflow
        split <;> rfl
  | Zneg resultMantissa =>
      change Zle Z0 (BinarySingleNaN.shr_m second.1) at secondNonnegative
      rw [resultValue] at secondNonnegative
      change 0 ≤ -(posToNat resultMantissa : Int) at secondNonnegative
      have positive := posToNat_positive resultMantissa
      omega

theorem Bdiv_mult_inverse :
    ∀ {prec emax : Z} [Prec_gt_0 prec] [Prec_lt_emax prec emax],
      Bdiv_mult_inverseStatement (prec := prec) (emax := emax) := by
  intro prec emax precision maximum certificate divNan multNan rounding numerator denominator inverse sameNan found
  rcases denominator with ⟨denominator, denominatorValid⟩
  rcases inverse with ⟨inverse, inverseValid⟩
  cases denominator with
  | B754_zero sign => simp [Bexact_inverse] at found
  | B754_infinity sign => simp [Bexact_inverse] at found
  | B754_nan sign payload => simp [Bexact_inverse] at found
  | B754_finite sign mantissa exponent =>
      by_cases correctMantissa : mantissa = Bexact_inverse_mantissa (prec := prec)
      · let inverseExponent := Zsub (Zopp exponent) (Zmul (Zsub prec Zone) Ztwo)
        cases lower : ZArith.ZArith_dec.Z_le_dec (emin prec emax) inverseExponent with
        | right below => simp [Bexact_inverse, correctMantissa, inverseExponent, lower] at found
        | left lowerBound =>
            cases upper : ZArith.ZArith_dec.Z_le_dec inverseExponent emax with
            | right above => simp [Bexact_inverse, correctMantissa, inverseExponent, lower, upper] at found
            | left upperBound =>
                have inverseValue : inverse = Binary.B754_finite sign mantissa inverseExponent := by
                  simpa [Bexact_inverse, correctMantissa, inverseExponent, lower, upper] using found.symm
                subst inverse
                subst mantissa
                rcases numerator with ⟨numerator, numeratorValid⟩
                cases numerator with
                | B754_zero numeratorSign => rfl
                | B754_infinity numeratorSign => rfl
                | B754_nan numeratorSign payload =>
                    have providers := sameNan ⟨.B754_nan numeratorSign payload, numeratorValid⟩
                      ⟨.B754_finite sign (Bexact_inverse_mantissa (prec := prec)) exponent, denominatorValid⟩
                      ⟨.B754_finite sign (Bexact_inverse_mantissa (prec := prec)) inverseExponent, inverseValid⟩
                      rfl rfl rfl
                    exact congrArg (fun result : NaNResult prec emax => Binary.build_nan ⟨result.1, result.2.1⟩)
                      providers
                | B754_finite numeratorSign numeratorMantissa numeratorExponent =>
                    have rounded := ieee_inverse_round (prec := prec) (emax := emax)
                      rounding (numeratorSign ^^ sign) numeratorMantissa numeratorExponent exponent
                    dsimp only at rounded
                    unfold Binary.Bdiv Binary.Bmult
                    change Binary.BSN2B _ (BinarySingleNaN.SF2B
                      (BinarySingleNaN.binary_round_aux rounding (numeratorSign ^^ sign)
                        (BinarySingleNaN.SFdiv_core_binary prec emax (Zpos numeratorMantissa) numeratorExponent
                          (Zpos (Bexact_inverse_mantissa (prec := prec))) exponent).1.1
                        (BinarySingleNaN.SFdiv_core_binary prec emax (Zpos numeratorMantissa) numeratorExponent
                          (Zpos (Bexact_inverse_mantissa (prec := prec))) exponent).1.2
                        (BinarySingleNaN.SFdiv_core_binary prec emax (Zpos numeratorMantissa) numeratorExponent
                          (Zpos (Bexact_inverse_mantissa (prec := prec))) exponent).2)) =
                      Binary.BSN2B _ (BinarySingleNaN.SF2B
                        (BinarySingleNaN.binary_round_aux rounding (numeratorSign ^^ sign)
                          (Zpos (PArith.BinPos.Pos.mul numeratorMantissa (Bexact_inverse_mantissa (prec := prec))))
                          (Zadd numeratorExponent inverseExponent) BinarySingleNaN.loc_Exact))
                    rw [rounded]
                    have notNan := ieee_round_aux_non_nan prec emax rounding (numeratorSign ^^ sign)
                      (Zpos (PArith.BinPos.Pos.mul numeratorMantissa (Bexact_inverse_mantissa (prec := prec))))
                      (Zadd numeratorExponent inverseExponent) BinarySingleNaN.loc_Exact (Int.natCast_nonneg _)
                    rw [ieee_lift_non_nan _ _ notNan, ieee_lift_non_nan _ _ notNan]
      · simp [Bexact_inverse, correctMantissa] at found

end CompCert4Lean.Lib.IEEE754_extra
