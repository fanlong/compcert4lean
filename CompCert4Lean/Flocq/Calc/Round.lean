import CompCert4Lean.Flocq.Calc.Bracket
import CompCert4Lean.Flocq.Core.Digits
import CompCert4Lean.Flocq.Core.Generic_fmt
import CompCert4Lean.Flocq.Core.Round_NE

/-!
# Floating-point rounding helpers

This module contains the executable definitions selected from
`Flocq.Calc.Round`.  Proof-bearing declarations are represented by exact
source-shaped proposition descriptors for the later proof-migration phase.
-/

namespace CompCert4Lean.Flocq.Calc.Round

abbrev R := CompCert4Lean.Flocq.Core.Raux.R
abbrev Z := CompCert4Lean.Flocq.Core.Zaux.Z
abbrev radix := CompCert4Lean.Flocq.Core.Zaux.radix
abbrev comparison := CompCert4Lean.Flocq.Core.Zaux.comparison

abbrev Lt : comparison := CompCert4Lean.Flocq.Core.Zaux.Lt
abbrev Eq : comparison := CompCert4Lean.Flocq.Core.Zaux.Eq
abbrev Gt : comparison := CompCert4Lean.Flocq.Core.Zaux.Gt

abbrev Z0 : Z := CompCert4Lean.Flocq.Core.Zaux.Z0
abbrev Zone : Z := CompCert4Lean.Flocq.Core.Zaux.Zone
abbrev Zadd := CompCert4Lean.Flocq.Core.Zaux.Zadd
abbrev Zsub := CompCert4Lean.Flocq.Core.Zaux.Zsub
abbrev Zmul := CompCert4Lean.Flocq.Core.Zaux.Zmul
abbrev Zopp := CompCert4Lean.Flocq.Core.Zaux.Zopp
abbrev Zdiv := CompCert4Lean.Flocq.Core.Raux.Zdiv
abbrev Zmod := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Zmod
abbrev Zpower := CompCert4Lean.Flocq.Core.Zaux.Zpower
abbrev Zeven := CompCert4Lean.Flocq.Core.Zaux.Zeven
abbrev Zle := CompCert4Lean.Flocq.Core.Zaux.Zle
abbrev Zle_bool := CompCert4Lean.Flocq.Core.Zaux.Zle_bool
abbrev Zlt := CompCert4Lean.Flocq.Core.Zaux.Zlt
abbrev Zlt_bool := CompCert4Lean.Flocq.Core.Zaux.Zlt_bool
abbrev Zdigits := CompCert4Lean.Flocq.Core.Digits.Zdigits

abbrev IZR := CompCert4Lean.Flocq.Core.Raux.IZR
abbrev R0 := CompCert4Lean.Flocq.Core.Raux.R0
abbrev Rabs := CompCert4Lean.Flocq.Core.Raux.Rabs
abbrev Rlt := CompCert4Lean.Flocq.Core.Raux.Rlt
abbrev Rle := CompCert4Lean.Flocq.Core.Raux.Rle
abbrev Rlt_bool := CompCert4Lean.Flocq.Core.Raux.Rlt_bool

abbrev location := CompCert4Lean.Flocq.Calc.Bracket.location
abbrev loc_Exact : location := CompCert4Lean.Flocq.Calc.Bracket.loc_Exact
abbrev loc_Inexact (c : comparison) : location :=
  CompCert4Lean.Flocq.Calc.Bracket.loc_Inexact c

abbrev float := CompCert4Lean.Flocq.Core.Defs.float
abbrev Float (beta : radix) (m e : Z) : float beta :=
  CompCert4Lean.Flocq.Core.Defs.float.mk m e
abbrev Fnum {beta : radix} (f : float beta) : Z :=
  CompCert4Lean.Flocq.Core.Defs.Fnum f
abbrev Fexp {beta : radix} (f : float beta) : Z :=
  CompCert4Lean.Flocq.Core.Defs.Fexp f
abbrev F2R {beta : radix} (f : float beta) : R :=
  CompCert4Lean.Flocq.Core.Defs.F2R f

abbrev Valid_exp := CompCert4Lean.Flocq.Core.Generic_fmt.Valid_exp
abbrev Valid_rnd := CompCert4Lean.Flocq.Core.Generic_fmt.Valid_rnd
abbrev bpow (beta : radix) (e : Z) : R :=
  CompCert4Lean.Flocq.Core.Raux.bpow beta e
abbrev cexp := CompCert4Lean.Flocq.Core.Generic_fmt.cexp
abbrev generic_format := CompCert4Lean.Flocq.Core.Generic_fmt.generic_format
abbrev scaled_mantissa := CompCert4Lean.Flocq.Core.Generic_fmt.scaled_mantissa
abbrev round := CompCert4Lean.Flocq.Core.Generic_fmt.round
abbrev Zfloor := CompCert4Lean.Flocq.Core.Raux.Zfloor
abbrev Zceil := CompCert4Lean.Flocq.Core.Raux.Zceil
abbrev Ztrunc := CompCert4Lean.Flocq.Core.Raux.Ztrunc
abbrev Znearest := CompCert4Lean.Flocq.Core.Generic_fmt.Znearest
abbrev ZnearestA := CompCert4Lean.Flocq.Core.Generic_fmt.ZnearestA
abbrev ZnearestE := CompCert4Lean.Flocq.Core.Round_NE.ZnearestE
abbrev cond_Zopp := CompCert4Lean.Flocq.Core.Zaux.cond_Zopp
abbrev inbetween_float := CompCert4Lean.Flocq.Calc.Bracket.inbetween_float
abbrev inbetween_int := CompCert4Lean.Flocq.Calc.Bracket.inbetween_int
abbrev new_location := CompCert4Lean.Flocq.Calc.Bracket.new_location

abbrev format (beta : radix) (fexp : Z → Z) (x : R) : Prop :=
  generic_format beta fexp x

def cond_incr (b : Bool) (m : Z) : Z :=
  if b then Zadd m Zone else m

def round_sign_DN (s : Bool) (l : location) : Bool :=
  match l with
  | .loc_Exact => false
  | .loc_Inexact _ => s

def round_sign_UP (s : Bool) (l : location) : Bool :=
  match l with
  | .loc_Exact => false
  | .loc_Inexact _ => Bool.not s

def round_N (p : Bool) (l : location) : Bool :=
  match l with
  | .loc_Exact => false
  | .loc_Inexact c =>
      match c with
      | .Lt => false
      | .Eq => p
      | .Gt => true

def truncate_aux (beta : radix) (t : (Z × Z) × location) (k : Z) : (Z × Z) × location :=
  let ((m, e), l) := t
  let p := Zpower (beta : Z) k
  ((Zdiv m p, Zadd e k), new_location p (Zmod m p) l)

def truncate (beta : radix) (fexp : Z → Z) (t : (Z × Z) × location) : (Z × Z) × location :=
  let ((m, e), l) := t
  let k := Zsub (fexp (Zadd (Zdigits beta m) e)) e
  if Zlt_bool Z0 k then truncate_aux beta t k else t

/-! Exact source proposition descriptors for later proof migration. -/

def cexp_inbetween_floatStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (x : R) (m e : Z) (l : location),
      Rlt R0 x →
      inbetween_float beta m e x l →
      (Zle e (cexp beta fexp x) ∨
        Zle e (fexp (Zadd (Zdigits beta m) e))) →
      cexp beta fexp x = fexp (Zadd (Zdigits beta m) e)

def cexp_inbetween_float_loc_ExactStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (x : R) (m e : Z) (l : location),
      Rle R0 x →
      inbetween_float beta m e x l →
      ((Zle e (cexp beta fexp x) ∨ l = loc_Exact) ↔
        (Zle e (fexp (Zadd (Zdigits beta m) e)) ∨ l = loc_Exact))

def inbetween_float_round_signStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (rnd : R → Z)
      (choice : Bool → Z → location → Z),
    Valid_exp fexp →
      (∀ (x : R) (m : Z) (l : location),
        inbetween_int m (Rabs x) l →
          rnd x = cond_Zopp (Rlt_bool x R0)
            (choice (Rlt_bool x R0) m l)) →
      ∀ (x : R) (m : Z) (l : location),
        let e := cexp beta fexp x
        inbetween_float beta m e (Rabs x) l →
          round beta fexp rnd x =
            F2R (Float beta
              (cond_Zopp (Rlt_bool x R0)
                (choice (Rlt_bool x R0) m l)) e)

def inbetween_int_DN_signStatement : Prop :=
  ∀ (x : R) (m : Z) (l : location),
    inbetween_int m (Rabs x) l →
      Zfloor x = cond_Zopp (Rlt_bool x R0)
        (cond_incr (round_sign_DN (Rlt_bool x R0) l) m)

def inbetween_int_UP_signStatement : Prop :=
  ∀ (x : R) (m : Z) (l : location),
    inbetween_int m (Rabs x) l →
      Zceil x = cond_Zopp (Rlt_bool x R0)
        (cond_incr (round_sign_UP (Rlt_bool x R0) l) m)

def inbetween_int_ZR_signStatement : Prop :=
  ∀ (x : R) (m : Z) (l : location),
    inbetween_int m (Rabs x) l →
      Ztrunc x = cond_Zopp (Rlt_bool x R0) m

def inbetween_int_N_signStatement : Prop :=
  ∀ (choice : Z → Bool) (x : R) (m : Z) (l : location),
    inbetween_int m (Rabs x) l →
      Znearest choice x =
        cond_Zopp (Rlt_bool x R0)
          (cond_incr
            (round_N
              (if Rlt_bool x R0 then
                Bool.not (choice (Zopp (Zadd m Zone)))
               else choice m)
              l)
            m)

def inbetween_int_NE_signStatement : Prop :=
  ∀ (x : R) (m : Z) (l : location),
    inbetween_int m (Rabs x) l →
      ZnearestE x = cond_Zopp (Rlt_bool x R0)
        (cond_incr (round_N (Bool.not (Zeven m)) l) m)

def inbetween_int_NA_signStatement : Prop :=
  ∀ (x : R) (m : Z) (l : location),
    inbetween_int m (Rabs x) l →
      ZnearestA x = cond_Zopp (Rlt_bool x R0)
        (cond_incr (round_N true l) m)

def truncate_0Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (e : Z) (l : location),
    let ((m', e'), l') := truncate beta fexp ((Z0, e), l)
    m' = Z0

def truncate_correct_formatStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (m e : Z), Valid_exp fexp →
    m ≠ Z0 →
      let x := F2R (Float beta m e)
      generic_format beta fexp x →
      Zle e (fexp (Zadd (Zdigits beta m) e)) →
      let ((m', e'), l') := truncate beta fexp ((m, e), loc_Exact)
      x = F2R (Float beta m' e') ∧
        e' = cexp beta fexp x

def truncate_correct_partial'Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (x : R) (m e : Z) (l : location),
    Valid_exp fexp →
      Rlt R0 x →
      inbetween_float beta m e x l →
      Zle e (cexp beta fexp x) →
      let ((m', e'), l') := truncate beta fexp ((m, e), l)
      inbetween_float beta m' e' x l' ∧
        e' = cexp beta fexp x

def truncate_correct_partialStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (x : R) (m e : Z) (l : location),
    Valid_exp fexp →
      Rlt R0 x →
      inbetween_float beta m e x l →
      Zle e (fexp (Zadd (Zdigits beta m) e)) →
      let ((m', e'), l') := truncate beta fexp ((m, e), l)
      inbetween_float beta m' e' x l' ∧
        e' = cexp beta fexp x

def truncate_correct'Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (x : R) (m e : Z) (l : location),
    Valid_exp fexp →
      Rle R0 x →
      inbetween_float beta m e x l →
      (Zle e (cexp beta fexp x) ∨ l = loc_Exact) →
      let ((m', e'), l') := truncate beta fexp ((m, e), l)
      inbetween_float beta m' e' x l' ∧
        (e' = cexp beta fexp x ∨
          (l' = loc_Exact ∧ generic_format beta fexp x))

def truncate_correctStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (x : R) (m e : Z) (l : location),
    Valid_exp fexp →
      Rle R0 x →
      inbetween_float beta m e x l →
      (Zle e (fexp (Zadd (Zdigits beta m) e)) ∨ l = loc_Exact) →
      let ((m', e'), l') := truncate beta fexp ((m, e), l)
      inbetween_float beta m' e' x l' ∧
        (e' = cexp beta fexp x ∨
          (l' = loc_Exact ∧ generic_format beta fexp x))

def round_sign_any_correctStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (rnd : R → Z)
      (choice : Bool → Z → location → Z),
    Valid_exp fexp →
      Valid_rnd rnd →
      (∀ (x : R) (m : Z) (l : location),
        inbetween_int m (Rabs x) l →
          rnd x = cond_Zopp (Rlt_bool x R0)
            (choice (Rlt_bool x R0) m l)) →
      ∀ (x : R) (m e : Z) (l : location),
        inbetween_float beta m e (Rabs x) l →
        (e = cexp beta fexp x ∨
          (l = loc_Exact ∧ generic_format beta fexp x)) →
        round beta fexp rnd x =
          F2R (Float beta
            (cond_Zopp (Rlt_bool x R0)
              (choice (Rlt_bool x R0) m l)) e)

def round_trunc_sign_any_correct'Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (rnd : R → Z)
      (choice : Bool → Z → location → Z),
    Valid_exp fexp →
      Valid_rnd rnd →
      (∀ (x : R) (m : Z) (l : location),
        inbetween_int m (Rabs x) l →
          rnd x = cond_Zopp (Rlt_bool x R0)
            (choice (Rlt_bool x R0) m l)) →
      ∀ (x : R) (m e : Z) (l : location),
        inbetween_float beta m e (Rabs x) l →
        (Zle e (cexp beta fexp x) ∨ l = loc_Exact) →
        let ((m', e'), l') := truncate beta fexp ((m, e), l)
        round beta fexp rnd x =
          F2R (Float beta
            (cond_Zopp (Rlt_bool x R0)
              (choice (Rlt_bool x R0) m' l')) e')

def round_trunc_sign_any_correctStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (rnd : R → Z)
      (choice : Bool → Z → location → Z),
    Valid_exp fexp →
      Valid_rnd rnd →
      (∀ (x : R) (m : Z) (l : location),
        inbetween_int m (Rabs x) l →
          rnd x = cond_Zopp (Rlt_bool x R0)
            (choice (Rlt_bool x R0) m l)) →
      ∀ (x : R) (m e : Z) (l : location),
        inbetween_float beta m e (Rabs x) l →
        (Zle e (fexp (Zadd (Zdigits beta m) e)) ∨ l = loc_Exact) →
        let ((m', e'), l') := truncate beta fexp ((m, e), l)
        round beta fexp rnd x =
          F2R (Float beta
            (cond_Zopp (Rlt_bool x R0)
              (choice (Rlt_bool x R0) m' l')) e')

end CompCert4Lean.Flocq.Calc.Round
