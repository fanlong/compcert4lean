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

abbrev NaNResult (prec emax : Z) :=
  { x : binary_float prec emax // Binary.is_nan x = true ∧ BinaryFloatCertificate x }

def dropNaNCertificate
    (nan : binary_float prec emax → binary_float prec emax → NaNResult prec emax)
    (x y : binary_float prec emax) :
    { x : binary_float prec emax // Binary.is_nan x = true } :=
  ⟨(nan x y).1, (nan x y).2.1⟩

def dropUnaryNaNCertificate
    {precIn emaxIn precOut emaxOut : Z}
    (nan : binary_float precIn emaxIn → NaNResult precOut emaxOut)
    (x : binary_float precIn emaxIn) :
    { x : binary_float precOut emaxOut // Binary.is_nan x = true } :=
  ⟨(nan x).1, (nan x).2.1⟩

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
  keepPrecisionHypotheses (prec := prec) (emax := emax)
    (∀ f : binary_float prec emax,
      BinaryFloatCertificate f → Binary.is_finite f = true → Binary.is_nan f = false)

def is_finite_strict_finiteStatement : Prop :=
  keepPrecisionHypotheses (prec := prec) (emax := emax)
    (∀ f : binary_float prec emax,
      BinaryFloatCertificate f →
      Binary.is_finite_strict f = true → Binary.is_finite f = true)

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
  keepPrecisionHypotheses (prec := prec) (emax := emax)
    (∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx) (n : Z),
      integer_representable (prec := prec) (emax := emax) ctx magnitude n →
      integer_representable (prec := prec) (emax := emax) ctx magnitude (Zopp n))

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
    Binary.Bplus (dropNaNCertificate nan) mode_NE
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
  ∀ f : binary_float prec emax,
    BinaryFloatCertificate f →
    ∀ (ctx : ExactRealContext),
    ZofB f =
      if Binary.is_finite f then some (Exact.Ztrunc ctx (Exact.B2R ctx f)) else none

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
    (∀ (f : binary_float prec emax) (n : Z),
      BinaryFloatCertificate f →
      ZofB f = some n → Zlt Z0 n →
      ∀ (ctx : ExactRealContext),
      Exact.Rle ctx (Exact.IZR ctx n) (Exact.B2R ctx f) ∧
        Exact.Rlt ctx (Exact.B2R ctx f) (Exact.IZR ctx (Zadd n Zone)))

def ZofB_range_zeroStatement : Prop :=
  keepPrecisionHypotheses (prec := prec) (emax := emax)
    (∀ (f : binary_float prec emax), BinaryFloatCertificate f →
      ZofB f = some Z0 → ∀ (ctx : ExactRealContext),
      Exact.Rlt ctx (Exact.Ropp ctx (Exact.Rone ctx)) (Exact.B2R ctx f) ∧
        Exact.Rlt ctx (Exact.B2R ctx f) (Exact.Rone ctx))

def ZofB_range_nonnegStatement : Prop :=
  keepPrecisionHypotheses (prec := prec) (emax := emax)
    (∀ (f : binary_float prec emax) (n : Z),
      BinaryFloatCertificate f →
      ZofB f = some n → Zle Z0 n →
      ∀ (ctx : ExactRealContext),
      Exact.Rlt ctx (Exact.Ropp ctx (Exact.Rone ctx)) (Exact.B2R ctx f) ∧
        Exact.Rlt ctx (Exact.B2R ctx f) (Exact.IZR ctx (Zadd n Zone)))

def Zfloor_minusStatement : Prop :=
  ∀ (ctx : ExactRealContext) (x : Exact.R ctx) (n : Z),
    Exact.Zfloor ctx (Exact.Rminus ctx x (Exact.IZR ctx n)) =
      Zsub (Exact.Zfloor ctx x) n

def ZofB_minusStatement : Prop :=
  ∀ (minus_nan : binary_float prec emax → binary_float prec emax → NaNResult prec emax)
    (m : mode) (f : binary_float prec emax) (p q : Z),
    BinaryFloatCertificate f →
    ZofB f = some p →
    (Zle Z0 p ∧ Zlt p (Zmul Ztwo q)) →
    Zle q (Zpower Ztwo prec) →
    ∀ (ctx : ExactRealContext),
    Exact.Rle ctx (Exact.IZR ctx q) (Exact.B2R ctx f) →
    ZofB (Binary.Bminus (dropNaNCertificate minus_nan) m f
      (BofZ (prec := prec) (emax := emax) q)) = some (Zsub p q)

def ZofB_range (f : binary_float prec emax) (zmin zmax : Z) : Option Z :=
  match ZofB f with
  | none => none
  | some z => if Zle_bool zmin z && Zle_bool z zmax then some z else none

def ZofB_range_correctStatement : Prop :=
  ∀ (f : binary_float prec emax) (min max : Z),
    BinaryFloatCertificate f →
    ∀ (ctx : ExactRealContext),
    let n := Exact.Ztrunc ctx (Exact.B2R ctx f)
    ZofB_range f min max =
      if Binary.is_finite f && Zle_bool min n && Zle_bool n max then some n else none

def ZofB_range_inversionStatement : Prop :=
  ∀ (f : binary_float prec emax) (min max n : Z),
    BinaryFloatCertificate f →
    ZofB_range f min max = some n →
    Zle min n ∧ Zle n max ∧ ZofB f = some n

def ZofB_range_minusStatement : Prop :=
  ∀ (minus_nan : binary_float prec emax → binary_float prec emax → NaNResult prec emax)
    (m : mode) (f : binary_float prec emax) (p q : Z),
    BinaryFloatCertificate f →
    ZofB_range f Z0 (Zsub (Zmul Ztwo q) Zone) = some p →
    Zle q (Zpower Ztwo prec) →
    ∀ (ctx : ExactRealContext),
    Exact.Rle ctx (Exact.IZR ctx q) (Exact.B2R ctx f) →
    ZofB_range
      (Binary.Bminus (dropNaNCertificate minus_nan) m f
        (BofZ (prec := prec) (emax := emax) q))
      (Zopp q) (Zsub q Zone) = some (Zsub p q)

def Bmult_commutStatement : Prop :=
  ∀ (mult_nan : binary_float prec emax → binary_float prec emax → NaNResult prec emax)
    (m : mode) (x y : binary_float prec emax),
    BinaryFloatCertificate x → BinaryFloatCertificate y →
    mult_nan x y = mult_nan y x →
    Binary.Bmult (dropNaNCertificate mult_nan) m x y =
      Binary.Bmult (dropNaNCertificate mult_nan) m y x

def Bmult2_BplusStatement : Prop :=
  ∀ (plus_nan mult_nan : binary_float prec emax → binary_float prec emax → NaNResult prec emax)
    (m : mode) (f : binary_float prec emax),
    BinaryFloatCertificate f →
    (∀ x y : binary_float prec emax,
      BinaryFloatCertificate x → BinaryFloatCertificate y →
      Binary.is_nan x = true → Binary.is_finite y = true →
      plus_nan x x = mult_nan x y) →
    Binary.Bplus (dropNaNCertificate plus_nan) m f f =
      Binary.Bmult (dropNaNCertificate mult_nan) m f
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
  ∀ (f : binary_float prec emax), BinaryFloatCertificate f →
    ∀ f', Bexact_inverse (prec := prec) (emax := emax) f = some f' →
      BinaryFloatCertificate f'

def Bexact_inverse_correctStatement : Prop :=
  keepPrecisionHypotheses (prec := prec) (emax := emax)
  (∀ (_certificate : Bexact_inverse_certificate prec emax)
    (f f' : binary_float prec emax),
    BinaryFloatCertificate f → BinaryFloatCertificate f' →
    Bexact_inverse (certificate := _certificate) f = some f' →
    Binary.is_finite_strict f = true ∧
      Binary.is_finite_strict f' = true ∧
      ∀ (ctx : ExactRealContext),
      Exact.B2R ctx f' = Exact.Rinv ctx (Exact.B2R ctx f) ∧
      Exact.B2R ctx f ≠ Exact.R0 ctx ∧
      Binary.Bsign f' = Binary.Bsign f)

def Bdiv_mult_inverseStatement : Prop :=
  ∀ (_certificate : Bexact_inverse_certificate prec emax)
    (div_nan mult_nan : binary_float prec emax → binary_float prec emax → NaNResult prec emax)
    (m : mode) (x y z : binary_float prec emax),
    BinaryFloatCertificate x → BinaryFloatCertificate y → BinaryFloatCertificate z →
    (∀ a b c : binary_float prec emax,
      BinaryFloatCertificate a → BinaryFloatCertificate b → BinaryFloatCertificate c →
      Binary.is_nan a = true →
      Binary.is_finite b = true → Binary.is_finite c = true →
      div_nan a b = mult_nan a c) →
    Bexact_inverse (certificate := _certificate) y = some z →
    Binary.Bdiv (dropNaNCertificate div_nan) m x y =
      Binary.Bmult (dropNaNCertificate mult_nan) m x z

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
  | .B754_nan _ _ => Binary.build_nan (dropUnaryNaNCertificate conv_nan f)
  | .B754_infinity s => Binary.B754_infinity s
  | .B754_zero s => Binary.B754_zero s
  | .B754_finite s m e =>
      Binary.binary_normalize md (Zaux.cond_Zopp s (Zpos m)) e s

def Bconv_result_obligation
    [Binary.BinaryNormalizeCertificate prec2 emax2] : Prop :=
  ∀ (conv_nan : binary_float prec1 emax1 → NaNResult prec2 emax2)
    (md : mode) (f : binary_float prec1 emax1),
    BinaryFloatCertificate f →
    BinaryFloatCertificate (Bconv conv_nan md f)

def Bconv_correctStatement : Prop :=
  ∀ (ctx : ExactRealContext) (magnitude : Exact.Magnitude ctx)
    (conv_nan : binary_float prec1 emax1 → NaNResult prec2 emax2)
    (m : mode) (f : binary_float prec1 emax1),
    BinaryFloatCertificate f →
    Binary.is_finite f = true →
    if Exact.Rlt_bool ctx
        (Exact.Rabs ctx
          (Exact.round magnitude Zaux.radix2 (fexp prec2 emax2)
            (Exact.round_mode ctx m) (Exact.B2R ctx f)))
        (Exact.bpow ctx Zaux.radix2 emax2) then
      Exact.B2R ctx (Bconv conv_nan m f) =
          Exact.round magnitude Zaux.radix2 (fexp prec2 emax2)
            (Exact.round_mode ctx m) (Exact.B2R ctx f) ∧
        Binary.is_finite (Bconv conv_nan m f) = true ∧
        Binary.Bsign (Bconv conv_nan m f) = Binary.Bsign f
    else
      Binary.B2FF (Bconv conv_nan m f) =
        Binary.binary_overflow (prec := prec2) (emax := emax2) m (Binary.Bsign f)

def Bconv_widen_exactStatement : Prop :=
  keepPrecGt (prec := prec1)
  (∀ (ctx : ExactRealContext),
  Zle prec1 prec2 → Zle emax1 emax2 →
  ∀ (conv_nan : binary_float prec1 emax1 → NaNResult prec2 emax2)
    (m : mode) (f : binary_float prec1 emax1),
    BinaryFloatCertificate f → BinaryFloatCertificate (Bconv conv_nan m f) →
    Binary.is_finite f = true →
    Exact.B2R ctx (Bconv conv_nan m f) = Exact.B2R ctx f ∧
      Binary.is_finite (Bconv conv_nan m f) = true ∧
      Binary.Bsign (Bconv conv_nan m f) = Binary.Bsign f)

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
      (m : mode) (f : binary_float prec1 emax1) (n : Z),
      BinaryFloatCertificate f → BinaryFloatCertificate (Bconv conv_nan m f) →
      ZofB f = some n → ZofB (Bconv conv_nan m f) = some n)

def ZofB_range_BconvStatement : Prop :=
  keepPrecGt (prec := prec1)
    (∀ min1 max1 min2 max2 : Z,
      Zle prec1 prec2 → Zle emax1 emax2 →
      Zle min2 min1 → Zle max1 max2 →
      ∀ (conv_nan : binary_float prec1 emax1 → NaNResult prec2 emax2)
        (m : mode) (f : binary_float prec1 emax1) (n : Z),
        BinaryFloatCertificate f → BinaryFloatCertificate (Bconv conv_nan m f) →
        ZofB_range f min1 max1 = some n →
        ZofB_range (Bconv conv_nan m f) min2 max2 = some n)

end Conversions

end CompCert4Lean.Lib.IEEE754_extra
