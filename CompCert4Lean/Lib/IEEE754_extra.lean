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

def emin (prec emax : Z) : Z := Binary.emin0 prec emax

def fexp (prec emax : Z) : Z → Z := Binary.fexp0 prec emax

abbrev binary_float (prec emax : Z) : Type := Binary.binary_float prec emax

variable {prec emax : Z} [Prec_gt_0 prec] [Prec_lt_emax prec emax]

def is_finite_not_is_nanStatement : Prop :=
  ∀ f : binary_float prec emax, Binary.is_finite f = true → Binary.is_nan f = false

def is_finite_strict_finiteStatement : Prop :=
  ∀ f : binary_float prec emax,
    Binary.is_finite_strict f = true → Binary.is_finite f = true

private def binaryFloatDecidableEq
    (f1 f2 : binary_float prec emax) : Decidable (f1 = f2) := by
  cases f1 <;> cases f2 <;> simp <;> infer_instance

def Beq_dec (f1 f2 : binary_float prec emax) : Sumbool (f1 = f2) (f1 ≠ f2) :=
  match binaryFloatDecidableEq f1 f2 with
  | .isTrue h => .left h
  | .isFalse h => .right h

def integer_representable (n : Z) : Prop :=
  Zle (Zabs n)
      (Zsub (Zpower Ztwo emax) (Zpower Ztwo (Zsub emax prec))) ∧
    generic_format Zaux.radix2 (fexp prec emax) (IZR n)

def int_upper_bound_eqStatement : Prop :=
  Zsub (Zpower Ztwo emax) (Zpower Ztwo (Zsub emax prec)) =
    Zmul (Zsub (Zpower Ztwo prec) Zone) (Zpower Ztwo (Zsub emax prec))

def integer_representable_n2pStatement : Prop :=
  ∀ n p : Z,
    (Zlt (Zopp (Zpower Ztwo prec)) n ∧ Zlt n (Zpower Ztwo prec)) →
    Zle Z0 p → Zle p (Zsub emax prec) →
    integer_representable (prec := prec) (emax := emax)
      (Zmul n (Zpower Ztwo p))

def integer_representable_2pStatement : Prop :=
  ∀ p : Z,
    (Zle Z0 p ∧ Zle p (Zsub emax Zone)) →
    integer_representable (prec := prec) (emax := emax) (Zpower Ztwo p)

def integer_representable_oppStatement : Prop :=
  ∀ n : Z,
    integer_representable (prec := prec) (emax := emax) n →
    integer_representable (prec := prec) (emax := emax) (Zopp n)

def integer_representable_n2p_wideStatement : Prop :=
  ∀ n p : Z,
    (Zle (Zopp (Zpower Ztwo prec)) n ∧ Zle n (Zpower Ztwo prec)) →
    Zle Z0 p → Zlt p (Zsub emax prec) →
    integer_representable (prec := prec) (emax := emax)
      (Zmul n (Zpower Ztwo p))

def integer_representable_nStatement : Prop :=
  ∀ n : Z,
    (Zle (Zopp (Zpower Ztwo prec)) n ∧ Zle n (Zpower Ztwo prec)) →
    integer_representable (prec := prec) (emax := emax) n

def round_int_no_overflowStatement : Prop :=
  ∀ n : Z,
    Zle (Zabs n)
      (Zsub (Zpower Ztwo emax) (Zpower Ztwo (Zsub emax prec))) →
    Rlt
      (Rabs (round Zaux.radix2 (fexp prec emax) (round_mode mode_NE) (IZR n)))
      (bpow Zaux.radix2 emax)

def BofZ (n : Z) : binary_float prec emax :=
  Binary.binary_normalize mode_NE n Z0 false

def BofZ_correctStatement : Prop :=
  ∀ n : Z,
    if Rlt_bool
        (Rabs (round Zaux.radix2 (fexp prec emax) (round_mode mode_NE) (IZR n)))
        (bpow Zaux.radix2 emax) then
      Binary.B2R (BofZ (prec := prec) (emax := emax) n) =
          round Zaux.radix2 (fexp prec emax) (round_mode mode_NE) (IZR n) ∧
        Binary.is_finite (BofZ (prec := prec) (emax := emax) n) = true ∧
        Binary.Bsign (BofZ (prec := prec) (emax := emax) n) = Zlt_bool n Z0
    else
      Binary.B2FF (BofZ (prec := prec) (emax := emax) n) =
        Binary.binary_overflow (prec := prec) (emax := emax) mode_NE (Zlt_bool n Z0)

def BofZ_finiteStatement : Prop :=
  ∀ n : Z,
    Zle (Zabs n)
      (Zsub (Zpower Ztwo emax) (Zpower Ztwo (Zsub emax prec))) →
    Binary.B2R (BofZ (prec := prec) (emax := emax) n) =
        round Zaux.radix2 (fexp prec emax) (round_mode mode_NE) (IZR n) ∧
      Binary.is_finite (BofZ (prec := prec) (emax := emax) n) = true ∧
      Binary.Bsign (BofZ (prec := prec) (emax := emax) n) = Zlt_bool n Z0

def BofZ_representableStatement : Prop :=
  ∀ n : Z,
    integer_representable (prec := prec) (emax := emax) n →
    Binary.B2R (BofZ (prec := prec) (emax := emax) n) = IZR n ∧
      Binary.is_finite (BofZ (prec := prec) (emax := emax) n) = true ∧
      Binary.Bsign (BofZ (prec := prec) (emax := emax) n) = Zlt_bool n Z0

def BofZ_exactStatement : Prop :=
  ∀ n : Z,
    (Zle (Zopp (Zpower Ztwo prec)) n ∧ Zle n (Zpower Ztwo prec)) →
    Binary.B2R (BofZ (prec := prec) (emax := emax) n) = IZR n ∧
      Binary.is_finite (BofZ (prec := prec) (emax := emax) n) = true ∧
      Binary.Bsign (BofZ (prec := prec) (emax := emax) n) = Zlt_bool n Z0

def BofZ_plusStatement : Prop :=
  ∀ (nan : binary_float prec emax → binary_float prec emax →
      { x : binary_float prec emax // Binary.is_nan x = true }) (p q : Z),
    integer_representable (prec := prec) (emax := emax) p →
    integer_representable (prec := prec) (emax := emax) q →
    Binary.Bplus nan mode_NE
        (BofZ (prec := prec) (emax := emax) p)
        (BofZ (prec := prec) (emax := emax) q) =
      BofZ (prec := prec) (emax := emax) (Zadd p q)

def ZofB (f : binary_float prec emax) : Option Z :=
  match f with
  | .B754_finite s m (.Zpos e) _ =>
      some (Zmul (Zaux.cond_Zopp s (Zpos m)) (Zpower_pos Ztwo e))
  | .B754_finite s m .Z0 _ => some (Zaux.cond_Zopp s (Zpos m))
  | .B754_finite s m (.Zneg e) _ =>
      some (Zaux.cond_Zopp s (Zdiv (Zpos m) (Zpower_pos Ztwo e)))
  | .B754_zero _ => some Z0
  | _ => none

def ZofB_correctStatement : Prop :=
  ∀ f : binary_float prec emax,
    ZofB f =
      if Binary.is_finite f then some (Ztrunc (Binary.B2R f)) else none

def Ztrunc_range_posStatement : Prop :=
  ∀ x : R, Zlt Z0 (Ztrunc x) →
    Rle (IZR (Ztrunc x)) x ∧ Rlt x (IZR (Zadd (Ztrunc x) Zone))

def Ztrunc_range_zeroStatement : Prop :=
  ∀ x : R, Ztrunc x = Z0 →
    Rlt (Ropp Rone) x ∧ Rlt x Rone

def ZofB_range_posStatement : Prop :=
  ∀ (f : binary_float prec emax) (n : Z),
    ZofB f = some n → Zlt Z0 n →
    Rle (IZR n) (Binary.B2R f) ∧
      Rlt (Binary.B2R f) (IZR (Zadd n Zone))

def ZofB_range_zeroStatement : Prop :=
  ∀ f : binary_float prec emax, ZofB f = some Z0 →
    Rlt (Ropp Rone) (Binary.B2R f) ∧ Rlt (Binary.B2R f) Rone

def ZofB_range_nonnegStatement : Prop :=
  ∀ (f : binary_float prec emax) (n : Z),
    ZofB f = some n → Zle Z0 n →
    Rlt (Ropp Rone) (Binary.B2R f) ∧
      Rlt (Binary.B2R f) (IZR (Zadd n Zone))

def Zfloor_minusStatement : Prop :=
  ∀ (x : R) (n : Z),
    Zfloor (Rminus x (IZR n)) = Zsub (Zfloor x) n

def ZofB_minusStatement : Prop :=
  ∀ (minus_nan : binary_float prec emax → binary_float prec emax →
      { x : binary_float prec emax // Binary.is_nan x = true })
    (m : mode) (f : binary_float prec emax) (p q : Z),
    ZofB f = some p →
    (Zle Z0 p ∧ Zlt p (Zmul Ztwo q)) →
    Zle q (Zpower Ztwo prec) →
    Rle (IZR q) (Binary.B2R f) →
    ZofB (Binary.Bminus minus_nan m f
      (BofZ (prec := prec) (emax := emax) q)) = some (Zsub p q)

def ZofB_range (f : binary_float prec emax) (zmin zmax : Z) : Option Z :=
  match ZofB f with
  | none => none
  | some z => if Zle_bool zmin z && Zle_bool z zmax then some z else none

def ZofB_range_correctStatement : Prop :=
  ∀ (f : binary_float prec emax) (min max : Z),
    let n := Ztrunc (Binary.B2R f)
    ZofB_range f min max =
      if Binary.is_finite f && Zle_bool min n && Zle_bool n max then some n else none

def ZofB_range_inversionStatement : Prop :=
  ∀ (f : binary_float prec emax) (min max n : Z),
    ZofB_range f min max = some n →
    Zle min n ∧ Zle n max ∧ ZofB f = some n

def ZofB_range_minusStatement : Prop :=
  ∀ (minus_nan : binary_float prec emax → binary_float prec emax →
      { x : binary_float prec emax // Binary.is_nan x = true })
    (m : mode) (f : binary_float prec emax) (p q : Z),
    ZofB_range f Z0 (Zsub (Zmul Ztwo q) Zone) = some p →
    Zle q (Zpower Ztwo prec) →
    Rle (IZR q) (Binary.B2R f) →
    ZofB_range
      (Binary.Bminus minus_nan m f (BofZ (prec := prec) (emax := emax) q))
      (Zopp q) (Zsub q Zone) = some (Zsub p q)

def Bmult_commutStatement : Prop :=
  ∀ (mult_nan : binary_float prec emax → binary_float prec emax →
      { x : binary_float prec emax // Binary.is_nan x = true })
    (m : mode) (x y : binary_float prec emax),
    mult_nan x y = mult_nan y x →
    Binary.Bmult mult_nan m x y = Binary.Bmult mult_nan m y x

def Bmult2_BplusStatement : Prop :=
  ∀ (plus_nan mult_nan : binary_float prec emax → binary_float prec emax →
      { x : binary_float prec emax // Binary.is_nan x = true })
    (m : mode) (f : binary_float prec emax),
    (∀ x y : binary_float prec emax,
      Binary.is_nan x = true → Binary.is_finite y = true →
      plus_nan x x = mult_nan x y) →
    Binary.Bplus plus_nan m f f =
      Binary.Bmult mult_nan m f (BofZ (prec := prec) (emax := emax) Ztwo)

def Bexact_inverse_mantissa : positive :=
  Ziter (Zsub prec Zone) xO xH

def Bexact_inverse_mantissa_valueStatement : Prop :=
  Zpos (Bexact_inverse_mantissa (prec := prec)) =
    Zpower Ztwo (Zsub prec Zone)

def Bexact_inverse_mantissa_digits2_posStatement : Prop :=
  Zpos (Digits.digits2_pos (Bexact_inverse_mantissa (prec := prec))) = prec

def bounded_Bexact_inverseStatement : Prop :=
  ∀ e : Z,
    (Zle (emin prec emax) e ∧ Zle e (Zsub emax prec)) ↔
      Binary.bounded (prec := prec) (emax := emax)
        (Bexact_inverse_mantissa (prec := prec)) e = true

def Bexact_inverse (f : binary_float prec emax) : Option (binary_float prec emax) :=
  match f with
  | .B754_finite s m e _ =>
      if _hm : m = Bexact_inverse_mantissa (prec := prec) then
        let e' := Zsub (Zopp e) (Zmul (Zsub prec Zone) Ztwo)
        match _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.ZArith_dec.Z_le_dec
            (emin prec emax) e' with
        | .left _ =>
            match _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.ZArith_dec.Z_le_dec
                e' emax with
            | .left _ =>
                match hbounded : Binary.bounded (prec := prec) (emax := emax) m e' with
                | true => some (Binary.B754_finite s m e' hbounded)
                | false => none
            | .right _ => none
        | .right _ => none
      else none
  | _ => none

def Bexact_inverse_correctStatement : Prop :=
  ∀ f f' : binary_float prec emax,
    Bexact_inverse f = some f' →
    Binary.is_finite_strict f = true ∧
      Binary.is_finite_strict f' = true ∧
      Binary.B2R f' = Rinv (Binary.B2R f) ∧
      Binary.B2R f ≠ R0 ∧
      Binary.Bsign f' = Binary.Bsign f

def Bdiv_mult_inverseStatement : Prop :=
  ∀ (div_nan mult_nan : binary_float prec emax → binary_float prec emax →
      { x : binary_float prec emax // Binary.is_nan x = true })
    (m : mode) (x y z : binary_float prec emax),
    (∀ a b c : binary_float prec emax,
      Binary.is_nan a = true →
      Binary.is_finite b = true → Binary.is_finite c = true →
      div_nan a b = mult_nan a c) →
    Bexact_inverse y = some z →
    Binary.Bdiv div_nan m x y = Binary.Bmult mult_nan m x z

section Conversions

variable {prec1 emax1 prec2 emax2 : Z}
  [Prec_gt_0 prec1] [Prec_gt_0 prec2]
  [Prec_lt_emax prec1 emax1] [Prec_lt_emax prec2 emax2]

def Bconv
    (conv_nan : binary_float prec1 emax1 →
      { x : binary_float prec2 emax2 // Binary.is_nan x = true })
    (md : mode) (f : binary_float prec1 emax1) : binary_float prec2 emax2 :=
  match f with
  | .B754_nan _ _ _ => Binary.build_nan (conv_nan f)
  | .B754_infinity s => Binary.B754_infinity s
  | .B754_zero s => Binary.B754_zero s
  | .B754_finite s m e _ =>
      Binary.binary_normalize md (Zaux.cond_Zopp s (Zpos m)) e s

def Bconv_correctStatement : Prop :=
  ∀ (conv_nan : binary_float prec1 emax1 →
      { x : binary_float prec2 emax2 // Binary.is_nan x = true })
    (m : mode) (f : binary_float prec1 emax1),
    Binary.is_finite f = true →
    if Rlt_bool
        (Rabs (round Zaux.radix2 (fexp prec2 emax2) (round_mode m) (Binary.B2R f)))
        (bpow Zaux.radix2 emax2) then
      Binary.B2R (Bconv conv_nan m f) =
          round Zaux.radix2 (fexp prec2 emax2) (round_mode m) (Binary.B2R f) ∧
        Binary.is_finite (Bconv conv_nan m f) = true ∧
        Binary.Bsign (Bconv conv_nan m f) = Binary.Bsign f
    else
      Binary.B2FF (Bconv conv_nan m f) =
        Binary.binary_overflow (prec := prec2) (emax := emax2) m (Binary.Bsign f)

def Bconv_widen_exactStatement : Prop :=
  Zle prec1 prec2 → Zle emax1 emax2 →
  ∀ (conv_nan : binary_float prec1 emax1 →
      { x : binary_float prec2 emax2 // Binary.is_nan x = true })
    (m : mode) (f : binary_float prec1 emax1),
    Binary.is_finite f = true →
    Binary.B2R (Bconv conv_nan m f) = Binary.B2R f ∧
      Binary.is_finite (Bconv conv_nan m f) = true ∧
      Binary.Bsign (Bconv conv_nan m f) = Binary.Bsign f

def Bconv_BofZStatement : Prop :=
  ∀ (conv_nan : binary_float prec1 emax1 →
      { x : binary_float prec2 emax2 // Binary.is_nan x = true }) (n : Z),
    integer_representable (prec := prec1) (emax := emax1) n →
    Bconv conv_nan mode_NE (BofZ (prec := prec1) (emax := emax1) n) =
      BofZ (prec := prec2) (emax := emax2) n

def ZofB_BconvStatement : Prop :=
  Zle prec1 prec2 → Zle emax1 emax2 →
  ∀ (conv_nan : binary_float prec1 emax1 →
      { x : binary_float prec2 emax2 // Binary.is_nan x = true })
    (m : mode) (f : binary_float prec1 emax1) (n : Z),
    ZofB f = some n → ZofB (Bconv conv_nan m f) = some n

def ZofB_range_BconvStatement : Prop :=
  ∀ min1 max1 min2 max2 : Z,
    Zle prec1 prec2 → Zle emax1 emax2 →
    Zle min2 min1 → Zle max1 max2 →
    ∀ (conv_nan : binary_float prec1 emax1 →
        { x : binary_float prec2 emax2 // Binary.is_nan x = true })
      (m : mode) (f : binary_float prec1 emax1) (n : Z),
      ZofB_range f min1 max1 = some n →
      ZofB_range (Bconv conv_nan m f) min2 max2 = some n

end Conversions

end CompCert4Lean.Lib.IEEE754_extra
