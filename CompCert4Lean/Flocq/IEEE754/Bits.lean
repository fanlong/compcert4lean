import CompCert4Lean.Flocq.IEEE754.Binary

/-!
# IEEE-754 bit encodings

This is the definition-translation surface for `Flocq.IEEE754.Bits`.
Proof-bearing source declarations in this packet are represented by exact
source-shaped proposition descriptors below.
-/

namespace CompCert4Lean.Flocq.IEEE754.Bits

open CompCert4Lean.Flocq.Core

abbrev Z := Zaux.Z
abbrev positive := Zaux.positive
abbrev Z0 : Z := Zaux.Z0
abbrev Zone : Z := Zaux.Zone
abbrev Ztwo : Z := Zaux.Ztwo
abbrev Zpos := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
abbrev Zadd := Zaux.Zadd
abbrev Zsub := Zaux.Zsub
abbrev Zmul := Zaux.Zmul
abbrev Zdiv := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div
abbrev Zmod := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo
abbrev Zshiftl := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftl
abbrev Zeq_bool := Zaux.Zeq_bool
abbrev Zle := Zaux.Zle
abbrev Zlt := Zaux.Zlt
abbrev Zle_bool := Zaux.Zle_bool
abbrev Zpower := Zaux.Zpower
abbrev Z_of_nat := _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat

abbrev prec (mw : Z) : Z := Zadd mw Zone
abbrev emax (ew : Z) : Z := Zpower Ztwo (Zsub ew Zone)

abbrev emin (mw ew : Z) : Z :=
  BinarySingleNaN.emin0 (prec mw) (emax ew)

abbrev binary_float (_mw _ew : Z) : Type := Binary.binary_float

def join_bits (mw ew : Z) (s : Bool) (m e : Z) : Z :=
  Zadd (Zshiftl (Zadd (if s then Zpower Ztwo ew else Z0) e) mw) m

def split_bits (mw ew x : Z) : (Bool × Z) × Z :=
  let mm := Zpower Ztwo mw
  let em := Zpower Ztwo ew
  ((Zle_bool (Zmul mm em) x, Zmod x mm), Zmod (Zdiv x mm) em)

def bits_of_binary_float (mw ew : Z) (x : binary_float mw ew) : Z :=
  match x with
  | .B754_zero sx => join_bits mw ew sx Z0 Z0
  | .B754_infinity sx =>
      join_bits mw ew sx Z0 (Zsub (Zpower Ztwo ew) Zone)
  | .B754_nan sx plx _ =>
      join_bits mw ew sx (Zpos plx) (Zsub (Zpower Ztwo ew) Zone)
  | .B754_finite sx mx ex _ =>
      let m := Zsub (Zpos mx) (Zpower Ztwo mw)
      if Zle_bool Z0 m then
        join_bits mw ew sx m (Zadd (Zsub ex (emin mw ew)) Zone)
      else
        join_bits mw ew sx (Zpos mx) Z0

def split_bits_of_binary_float (mw ew : Z)
    (x : binary_float mw ew) : (Bool × Z) × Z :=
  match x with
  | .B754_zero sx => ((sx, Z0), Z0)
  | .B754_infinity sx =>
      ((sx, Z0), Zsub (Zpower Ztwo ew) Zone)
  | .B754_nan sx plx _ =>
      ((sx, Zpos plx), Zsub (Zpower Ztwo ew) Zone)
  | .B754_finite sx mx ex _ =>
      let m := Zsub (Zpos mx) (Zpower Ztwo mw)
      if Zle_bool Z0 m then
        ((sx, m), Zadd (Zsub ex (emin mw ew)) Zone)
      else
        ((sx, Zpos mx), Z0)

def binary_float_of_bits_aux (mw ew x : Z) :=
  let ((sx, mx), ex) := split_bits mw ew x
  if Zeq_bool ex Z0 then
    match mx with
    | .Z0 => Binary.F754_zero sx
    | .Zpos px => Binary.F754_finite sx px (emin mw ew)
    | .Zneg _ => Binary.F754_nan false .xH
  else if Zeq_bool ex (Zsub (Zpower Ztwo ew) Zone) then
    match mx with
    | .Z0 => Binary.F754_infinity sx
    | .Zpos plx => Binary.F754_nan sx plx
    | .Zneg _ => Binary.F754_nan false .xH
  else
    match Zadd mx (Zpower Ztwo mw) with
    | .Zpos px => Binary.F754_finite sx px (Zsub (Zadd ex (emin mw ew)) Zone)
    | _ => Binary.F754_nan false .xH

def binary_float_of_bits (mw ew : Z)
    (_Hmw : Zlt Z0 mw) (_Hew : Zlt Z0 ew)
    (_Hmax : Zlt (prec mw) (emax ew))
    (x : Z) : binary_float mw ew :=
  let y := binary_float_of_bits_aux mw ew x
  if h : Binary.valid_binary (prec := prec mw) (emax := emax ew) y = true then
    Binary.FF2B y h
  else
    Binary.B754_zero false

/-! Exact source proposition descriptors for later proof migration. -/

def join_bits_rangeStatement : Prop :=
  ∀ (mw ew : Z) (s : Bool) (m e : Z),
    (Zle Z0 m ∧ Zlt m (Zpower Ztwo mw)) →
    (Zle Z0 e ∧ Zlt e (Zpower Ztwo ew)) →
    Zle Z0 (join_bits mw ew s m e) ∧
      Zlt (join_bits mw ew s m e)
        (Zpower Ztwo (Zadd (Zadd mw ew) Zone))

def split_join_bitsStatement : Prop :=
  ∀ (mw ew : Z) (s : Bool) (m e : Z),
    (Zle Z0 m ∧ Zlt m (Zpower Ztwo mw)) →
    (Zle Z0 e ∧ Zlt e (Zpower Ztwo ew)) →
    split_bits mw ew (join_bits mw ew s m e) = ((s, m), e)

def split_bits_of_binary_float_correctStatement : Prop :=
  ∀ (mw ew : Z), Zlt Z0 mw → Zlt Z0 ew →
    ∀ x : binary_float mw ew,
    split_bits mw ew (bits_of_binary_float mw ew x) =
      split_bits_of_binary_float mw ew x

def bits_of_binary_float_rangeStatement : Prop :=
  ∀ (mw ew : Z), Zlt Z0 mw → Zlt Z0 ew →
    ∀ x : binary_float mw ew,
    Zle Z0 (bits_of_binary_float mw ew x) ∧
      Zlt (bits_of_binary_float mw ew x)
        (Zpower Ztwo (Zadd (Zadd mw ew) Zone))

def binary_float_of_bits_aux_correctStatement : Prop :=
  ∀ (mw ew : Z), Zlt Z0 mw → Zlt Z0 ew →
    Zlt (prec mw) (emax ew) → ∀ x : Z,
    Binary.valid_binary (prec := prec mw) (emax := emax ew)
      (binary_float_of_bits_aux mw ew x) = true

def binary_float_of_bits_of_binary_floatStatement : Prop :=
  ∀ (mw ew : Z) (Hmw : Zlt Z0 mw) (Hew : Zlt Z0 ew)
    (Hmax : Zlt (prec mw) (emax ew)) (x : binary_float mw ew),
    binary_float_of_bits mw ew Hmw Hew Hmax (bits_of_binary_float mw ew x) = x

private abbrev z8 : Z := Z_of_nat 8
private abbrev z11 : Z := Z_of_nat 11
private abbrev z23 : Z := Z_of_nat 23
private abbrev z52 : Z := Z_of_nat 52

private def z23_gt_0 : Zlt Z0 z23 := by
  change (0 : Int) < 23
  decide

private def z8_gt_0 : Zlt Z0 z8 := by
  change (0 : Int) < 8
  decide

private def z23_format : Zlt (prec z23) (emax z8) := by
  change (24 : Int) < 128
  decide

private def z52_gt_0 : Zlt Z0 z52 := by
  change (0 : Int) < 52
  decide

private def z11_gt_0 : Zlt Z0 z11 := by
  change (0 : Int) < 11
  decide

private def z52_format : Zlt (prec z52) (emax z11) := by
  change (53 : Int) < 1024
  decide

def binary32 : Type := binary_float z23 z8

def b32_of_bits (x : Z) : binary32 :=
  binary_float_of_bits z23 z8 z23_gt_0 z8_gt_0 z23_format x

def bits_of_b32 (x : binary32) : Z :=
  bits_of_binary_float z23 z8 x

def binary64 : Type := binary_float z52 z11

def b64_of_bits (x : Z) : binary64 :=
  binary_float_of_bits z52 z11 z52_gt_0 z11_gt_0 z52_format x

def bits_of_b64 (x : binary64) : Z :=
  bits_of_binary_float z52 z11 x

end CompCert4Lean.Flocq.IEEE754.Bits
