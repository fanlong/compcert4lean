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

abbrev ExactRealContext := CompCert4Lean.Flocq.Calc.Bracket.ExactRealContext
abbrev ExactR (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Calc.Bracket.R ctx
abbrev ExactMagnitude (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Magnitude ctx

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

section ExactSpecification

variable (ctx : ExactRealContext)
variable (magnitude : ExactMagnitude ctx)

local notation "ER" => ExactR ctx
local notation "ER0" => CompCert4Lean.Flocq.Calc.Bracket.R0 ctx
local notation "ERabs" => CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx
local notation "ERlt" => CompCert4Lean.Flocq.Calc.Bracket.Rlt ctx
local notation "ERle" => CompCert4Lean.Flocq.Calc.Bracket.Rle ctx
local notation "ERlt_bool" => CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx
local notation "EZfloor" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx
local notation "EZceil" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx
local notation "EZtrunc" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx
local notation "EZnearest" => CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Znearest ctx
local notation "EZnearestE" =>
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Znearest ctx
    (fun m => Bool.not (Zeven m))
local notation "EZnearestA" =>
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Znearest ctx
    (fun m => Zle_bool Z0 m)
local notation "Ecexp" =>
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude
local notation "Egeneric_format" =>
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.generic_format ctx magnitude
local notation "Eround" =>
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round ctx magnitude
local notation "EValid_rnd" =>
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Valid_rnd ctx
local notation "EFloat" => CompCert4Lean.Flocq.Calc.Bracket.Float
local notation "EF2R" => CompCert4Lean.Flocq.Calc.Bracket.F2R ctx

def cexp_inbetween_floatStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (x : ER) (m e : Z) (l : location),
      ERlt ER0 x →
      CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx beta m e x l →
      (Zle e (Ecexp beta fexp x) ∨
        Zle e (fexp (Zadd (Zdigits beta m) e))) →
      Ecexp beta fexp x = fexp (Zadd (Zdigits beta m) e)

def cexp_inbetween_float_loc_ExactStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (x : ER) (m e : Z) (l : location),
      ERle ER0 x →
      CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx beta m e x l →
      ((Zle e (Ecexp beta fexp x) ∨ l = loc_Exact) ↔
        (Zle e (fexp (Zadd (Zdigits beta m) e)) ∨ l = loc_Exact))

def inbetween_float_round_signStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (rnd : ER → Z)
      (choice : Bool → Z → location → Z),
      (∀ (x : ER) (m : Z) (l : location),
        CompCert4Lean.Flocq.Calc.Bracket.inbetween_int ctx m (ERabs x) l →
          rnd x = cond_Zopp (ERlt_bool x ER0)
            (choice (ERlt_bool x ER0) m l)) →
      ∀ (x : ER) (m : Z) (l : location),
        let e := Ecexp beta fexp x
        CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx beta m e (ERabs x) l →
          Eround beta fexp rnd x =
            EF2R (EFloat beta
              (cond_Zopp (ERlt_bool x ER0)
                (choice (ERlt_bool x ER0) m l)) e)

def inbetween_int_DN_signStatement : Prop :=
  ∀ (x : ER) (m : Z) (l : location),
    CompCert4Lean.Flocq.Calc.Bracket.inbetween_int ctx m (ERabs x) l →
      EZfloor x = cond_Zopp (ERlt_bool x ER0)
        (cond_incr (round_sign_DN (ERlt_bool x ER0) l) m)

def inbetween_int_UP_signStatement : Prop :=
  ∀ (x : ER) (m : Z) (l : location),
    CompCert4Lean.Flocq.Calc.Bracket.inbetween_int ctx m (ERabs x) l →
      EZceil x = cond_Zopp (ERlt_bool x ER0)
        (cond_incr (round_sign_UP (ERlt_bool x ER0) l) m)

def inbetween_int_ZR_signStatement : Prop :=
  ∀ (x : ER) (m : Z) (l : location),
    CompCert4Lean.Flocq.Calc.Bracket.inbetween_int ctx m (ERabs x) l →
      EZtrunc x = cond_Zopp (ERlt_bool x ER0) m

def inbetween_int_N_signStatement : Prop :=
  ∀ (choice : Z → Bool) (x : ER) (m : Z) (l : location),
    CompCert4Lean.Flocq.Calc.Bracket.inbetween_int ctx m (ERabs x) l →
      EZnearest choice x =
        cond_Zopp (ERlt_bool x ER0)
          (cond_incr
            (round_N
              (if ERlt_bool x ER0 then
                Bool.not (choice (Zopp (Zadd m Zone)))
               else choice m)
              l)
            m)

def inbetween_int_NE_signStatement : Prop :=
  ∀ (x : ER) (m : Z) (l : location),
    CompCert4Lean.Flocq.Calc.Bracket.inbetween_int ctx m (ERabs x) l →
      EZnearestE x = cond_Zopp (ERlt_bool x ER0)
        (cond_incr (round_N (Bool.not (Zeven m)) l) m)

def inbetween_int_NA_signStatement : Prop :=
  ∀ (x : ER) (m : Z) (l : location),
    CompCert4Lean.Flocq.Calc.Bracket.inbetween_int ctx m (ERabs x) l →
      EZnearestA x = cond_Zopp (ERlt_bool x ER0)
        (cond_incr (round_N true l) m)

def truncate_0Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (e : Z) (l : location),
    let ((m', e'), l') := truncate beta fexp ((Z0, e), l)
    m' = Z0

def truncate_correct_formatStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (m e : Z),
    m ≠ Z0 →
      let x := EF2R (EFloat beta m e)
      Egeneric_format beta fexp x →
      Zle e (fexp (Zadd (Zdigits beta m) e)) →
      let ((m', e'), l') := truncate beta fexp ((m, e), loc_Exact)
      x = EF2R (EFloat beta m' e') ∧
        e' = Ecexp beta fexp x

def truncate_correct_partial'Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (x : ER) (m e : Z) (l : location),
      ERlt ER0 x →
      CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx beta m e x l →
      Zle e (Ecexp beta fexp x) →
      let ((m', e'), l') := truncate beta fexp ((m, e), l)
      CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx beta m' e' x l' ∧
        e' = Ecexp beta fexp x

def truncate_correct_partialStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (x : ER) (m e : Z) (l : location),
      ERlt ER0 x →
      CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx beta m e x l →
      Zle e (fexp (Zadd (Zdigits beta m) e)) →
      let ((m', e'), l') := truncate beta fexp ((m, e), l)
      CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx beta m' e' x l' ∧
        e' = Ecexp beta fexp x

def truncate_correct'Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (x : ER) (m e : Z) (l : location),
      ERle ER0 x →
      CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx beta m e x l →
      (Zle e (Ecexp beta fexp x) ∨ l = loc_Exact) →
      let ((m', e'), l') := truncate beta fexp ((m, e), l)
      CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx beta m' e' x l' ∧
        (e' = Ecexp beta fexp x ∨
          (l' = loc_Exact ∧ Egeneric_format beta fexp x))

def truncate_correctStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (x : ER) (m e : Z) (l : location),
      ERle ER0 x →
      CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx beta m e x l →
      (Zle e (fexp (Zadd (Zdigits beta m) e)) ∨ l = loc_Exact) →
      let ((m', e'), l') := truncate beta fexp ((m, e), l)
      CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx beta m' e' x l' ∧
        (e' = Ecexp beta fexp x ∨
          (l' = loc_Exact ∧ Egeneric_format beta fexp x))

def round_sign_any_correctStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (rnd : ER → Z),
    EValid_rnd rnd →
    ∀ (choice : Bool → Z → location → Z),
      (∀ (x : ER) (m : Z) (l : location),
        CompCert4Lean.Flocq.Calc.Bracket.inbetween_int ctx m (ERabs x) l →
          rnd x = cond_Zopp (ERlt_bool x ER0)
            (choice (ERlt_bool x ER0) m l)) →
      ∀ (x : ER) (m e : Z) (l : location),
        CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx beta m e (ERabs x) l →
        (e = Ecexp beta fexp x ∨
          (l = loc_Exact ∧ Egeneric_format beta fexp x)) →
        Eround beta fexp rnd x =
          EF2R (EFloat beta
            (cond_Zopp (ERlt_bool x ER0)
              (choice (ERlt_bool x ER0) m l)) e)

def round_trunc_sign_any_correct'Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (rnd : ER → Z), EValid_rnd rnd →
      ∀ (choice : Bool → Z → location → Z),
        (∀ (x : ER) (m : Z) (l : location),
        CompCert4Lean.Flocq.Calc.Bracket.inbetween_int ctx m (ERabs x) l →
          rnd x = cond_Zopp (ERlt_bool x ER0)
            (choice (ERlt_bool x ER0) m l)) →
      ∀ (x : ER) (m e : Z) (l : location),
        CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx beta m e (ERabs x) l →
        (Zle e (Ecexp beta fexp x) ∨ l = loc_Exact) →
        let ((m', e'), l') := truncate beta fexp ((m, e), l)
        Eround beta fexp rnd x =
          EF2R (EFloat beta
            (cond_Zopp (ERlt_bool x ER0)
              (choice (ERlt_bool x ER0) m' l')) e')

def round_trunc_sign_any_correctStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (rnd : ER → Z), EValid_rnd rnd →
      ∀ (choice : Bool → Z → location → Z),
        (∀ (x : ER) (m : Z) (l : location),
        CompCert4Lean.Flocq.Calc.Bracket.inbetween_int ctx m (ERabs x) l →
          rnd x = cond_Zopp (ERlt_bool x ER0)
            (choice (ERlt_bool x ER0) m l)) →
      ∀ (x : ER) (m e : Z) (l : location),
        CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx beta m e (ERabs x) l →
        (Zle e (fexp (Zadd (Zdigits beta m) e)) ∨ l = loc_Exact) →
        let ((m', e'), l') := truncate beta fexp ((m, e), l)
        Eround beta fexp rnd x =
          EF2R (EFloat beta
            (cond_Zopp (ERlt_bool x ER0)
              (choice (ERlt_bool x ER0) m' l')) e')

end ExactSpecification

end CompCert4Lean.Flocq.Calc.Round
