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

namespace CompCert4Lean.Flocq.Calc.Round

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem pg_zero_lt_one (ctx : ExactRealContext) :
    ctx.spec.lt ctx.spec.zero ctx.spec.one := by
  rcases ctx.certificate.total_order ctx.spec.zero ctx.spec.one with h | h
  · rcases h with h | h
    · exact h
    · exact (ctx.certificate.orderedField.zero_ne_one h).elim
  · have hzero_lt_neg : ctx.spec.lt ctx.spec.zero (ctx.spec.neg ctx.spec.one) := by
      have hadd := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.neg ctx.spec.one) ctx.spec.one ctx.spec.zero h
      rw [ctx.certificate.orderedField.neg_add_cancel,
        ctx.certificate.orderedField.add_zero] at hadd
      exact hadd
    have hneg_lt_zero := ctx.certificate.orderedField.mul_lt_compat_l
      (ctx.spec.neg ctx.spec.one) ctx.spec.one ctx.spec.zero hzero_lt_neg h
    rw [ctx.certificate.orderedField.mul_one,
      ctx.certificate.orderedField.mul_zero] at hneg_lt_zero
    exact (ctx.certificate.orderedField.lt_irrefl ctx.spec.zero
      (ctx.certificate.orderedField.lt_trans ctx.spec.zero
        (ctx.spec.neg ctx.spec.one) ctx.spec.zero hzero_lt_neg hneg_lt_zero)).elim

private theorem pg_zpos_xo (p : positive) :
    Zpos (xO p) = Zadd (Zpos p) (Zpos p) := by
  apply intOfZ_injective
  simp only [Zadd,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    intOfZ_zOfInt]
  simp [intOfZ, CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
  omega

private theorem pg_zpos_xi (p : positive) :
    Zpos (xI p) = Zadd (Zadd (Zpos p) (Zpos p)) Zone := by
  apply intOfZ_injective
  simp only [Zadd,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    intOfZ_zOfInt]
  simp [intOfZ, CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
  omega

private theorem pg_zsub_eq_add_opp (a b : Z) :
    Zsub a b = Zadd a (Zopp b) := by
  apply intOfZ_injective
  change intOfZ (Zsub a b) = intOfZ (Zadd a (Zopp b))
  simp only [Zsub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    Zadd,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    Zopp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
    intOfZ_zOfInt]
  omega

private theorem pg_izr_pos (ctx : ExactRealContext) (p : positive) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ (Zpos p)) := by
  induction p with
  | xH =>
      rw [ctx.certificate.sourceLaws.ofZ_one]
      exact pg_zero_lt_one ctx
  | xO p ih =>
      rw [pg_zpos_xo, ctx.certificate.sourceLaws.ofZ_add]
      have h := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.ofZ (Zpos p)) ctx.spec.zero (ctx.spec.ofZ (Zpos p)) ih
      rw [ctx.certificate.orderedField.add_zero] at h
      exact ctx.certificate.orderedField.lt_trans ctx.spec.zero
        (ctx.spec.ofZ (Zpos p)) _ ih h
  | xI p ih =>
      rw [pg_zpos_xi, ctx.certificate.sourceLaws.ofZ_add,
        ctx.certificate.sourceLaws.ofZ_add, ctx.certificate.sourceLaws.ofZ_one]
      have h := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.ofZ (Zpos p)) ctx.spec.zero (ctx.spec.ofZ (Zpos p)) ih
      rw [ctx.certificate.orderedField.add_zero] at h
      have hdouble := ctx.certificate.orderedField.lt_trans ctx.spec.zero
        (ctx.spec.ofZ (Zpos p)) _ ih h
      have hplusone := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.add (ctx.spec.ofZ (Zpos p)) (ctx.spec.ofZ (Zpos p)))
        ctx.spec.zero ctx.spec.one (pg_zero_lt_one ctx)
      rw [ctx.certificate.orderedField.add_zero] at hplusone
      exact ctx.certificate.orderedField.lt_trans ctx.spec.zero _ _ hdouble hplusone

private theorem pg_izr_nonneg (ctx : ExactRealContext) (z : Z) (hz : Zle Z0 z) :
    ctx.spec.le ctx.spec.zero (ctx.spec.ofZ z) := by
  cases z with
  | Z0 =>
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact ctx.certificate.orderedField.le_refl _
  | Zpos p =>
      exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
        (pg_izr_pos ctx p) |>.1
  | Zneg p =>
      change 0 <= -Int.ofNat (posToNat p) at hz
      have hp := posToNat_positive p
      have hpq : (0 : Int) < Int.ofNat (posToNat p) := by
        exact Int.ofNat_lt.mpr hp
      omega

private theorem pg_izr_le (ctx : ExactRealContext) (a b : Z) (hab : Zle a b) :
    ctx.spec.le (ctx.spec.ofZ a) (ctx.spec.ofZ b) := by
  have hsub : Zle Z0 (Zsub b a) := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub b a)
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      intOfZ_zOfInt]
    change (0 : Int) <= intOfZ b - intOfZ a
    change intOfZ a <= intOfZ b at hab
    omega
  have hnonneg := pg_izr_nonneg ctx (Zsub b a) hsub
  rw [pg_zsub_eq_add_opp, ctx.certificate.sourceLaws.ofZ_add,
    ctx.certificate.sourceLaws.ofZ_neg] at hnonneg
  by_cases hle : ctx.spec.le (ctx.spec.ofZ a) (ctx.spec.ofZ b)
  · exact hle
  · exfalso
    rcases ctx.certificate.total_order (ctx.spec.ofZ a) (ctx.spec.ofZ b) with h | h
    · rcases h with hlt | heq
      · exact hle ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt).1
      · exact hle (by rw [heq]; exact ctx.certificate.orderedField.le_refl _)
    · have hdiff := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.neg (ctx.spec.ofZ a)) (ctx.spec.ofZ b) (ctx.spec.ofZ a) h
      rw [ctx.certificate.orderedField.neg_add_cancel] at hdiff
      rw [ctx.certificate.orderedField.add_comm] at hdiff
      exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hdiff).2 hnonneg

private theorem pg_izr_pos_z (ctx : ExactRealContext) (z : Z) (hz : Zlt Z0 z) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ z) := by
  cases z with
  | Z0 =>
      change (0 : Int) < 0 at hz
      omega
  | Zpos p => exact pg_izr_pos ctx p
  | Zneg p =>
      change (0 : Int) < -Int.ofNat (posToNat p) at hz
      have hp := posToNat_positive p
      have hpq : (0 : Int) < Int.ofNat (posToNat p) := by
        exact Int.ofNat_lt.mpr hp
      omega

private theorem pg_izr_lt (ctx : ExactRealContext) (a b : Z) (hab : Zlt a b) :
    ctx.spec.lt (ctx.spec.ofZ a) (ctx.spec.ofZ b) := by
  have hsub : Zlt Z0 (Zsub b a) := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub b a)
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      intOfZ_zOfInt]
    change (0 : Int) < intOfZ b - intOfZ a
    change intOfZ a < intOfZ b at hab
    omega
  have hpos := pg_izr_pos_z ctx (Zsub b a) hsub
  rw [pg_zsub_eq_add_opp, ctx.certificate.sourceLaws.ofZ_add,
    ctx.certificate.sourceLaws.ofZ_neg] at hpos
  have hadd := ctx.certificate.orderedField.add_lt_compat_l
    (ctx.spec.ofZ a) ctx.spec.zero
    (ctx.spec.add (ctx.spec.ofZ b) (ctx.spec.neg (ctx.spec.ofZ a))) hpos
  rw [ctx.certificate.orderedField.add_zero,
    <- ctx.certificate.orderedField.add_assoc,
    ctx.certificate.orderedField.add_comm (ctx.spec.ofZ a) (ctx.spec.ofZ b),
    ctx.certificate.orderedField.add_assoc,
    ctx.certificate.orderedField.add_comm (ctx.spec.ofZ a)
      (ctx.spec.neg (ctx.spec.ofZ a)),
    ctx.certificate.orderedField.neg_add_cancel,
    ctx.certificate.orderedField.add_zero] at hadd
  exact hadd

private theorem pg_izr_le_inv (ctx : ExactRealContext) (a b : Z)
    (h : ctx.spec.le (ctx.spec.ofZ a) (ctx.spec.ofZ b)) : Zle a b := by
  change intOfZ a <= intOfZ b
  by_cases hab : intOfZ a <= intOfZ b
  · exact hab
  · exfalso
    have hba : Zlt b a := by
      change intOfZ b < intOfZ a
      omega
    have hreal := pg_izr_lt ctx b a hba
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hreal).2 h

private theorem pg_izr_lt_inv (ctx : ExactRealContext) (a b : Z)
    (h : ctx.spec.lt (ctx.spec.ofZ a) (ctx.spec.ofZ b)) : Zlt a b := by
  by_cases hab : Zlt a b
  · exact hab
  · exfalso
    have hba : Zle b a := by
      change intOfZ b <= intOfZ a
      change ¬(intOfZ a < intOfZ b) at hab
      omega
    have hreal := pg_izr_le ctx b a hba
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h).2 hreal

private theorem pg_up_izr (ctx : ExactRealContext) (n : Z) :
    ctx.spec.up (ctx.spec.ofZ n) = Zadd n Zone := by
  let u := ctx.spec.up (ctx.spec.ofZ n)
  have hgt : Zlt n u :=
    pg_izr_lt_inv ctx n u (ctx.certificate.sourceLaws.up_gt (ctx.spec.ofZ n))
  have hgap : Zle (Zsub u n) Zone := by
    apply pg_izr_le_inv ctx
    rw [pg_zsub_eq_add_opp, ctx.certificate.sourceLaws.ofZ_add,
      ctx.certificate.sourceLaws.ofZ_neg]
    exact ctx.certificate.sourceLaws.up_gap (ctx.spec.ofZ n)
  apply intOfZ_injective
  change intOfZ (ctx.spec.up (ctx.spec.ofZ n)) = intOfZ (Zadd n Zone)
  simp only [Zadd,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    intOfZ_zOfInt]
  change intOfZ n < intOfZ u at hgt
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub u n)
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH) at hgap
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    intOfZ_zOfInt] at hgap
  change intOfZ (ctx.spec.up (ctx.spec.ofZ n)) = intOfZ n + 1
  change intOfZ u - intOfZ n <= 1 at hgap
  dsimp [u] at hgt hgap
  omega

private theorem pg_floor_izr (ctx : ExactRealContext) (n : Z) :
    CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx (ctx.spec.ofZ n) = n := by
  unfold CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor
  change Zsub (ctx.spec.up (ctx.spec.ofZ n)) Zone = n
  rw [pg_up_izr]
  apply intOfZ_injective
  change intOfZ (Zsub (Zadd n Zone) (Zpos xH)) = intOfZ n
  simp only [Zsub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    Zadd,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    intOfZ_zOfInt]
  change intOfZ n + 1 - 1 = intOfZ n
  omega

private theorem pg_rlt_bool_true (ctx : ExactRealContext) (x : ctx.spec.carrier)
    (h : ctx.spec.lt x ctx.spec.zero) :
    CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x ctx.spec.zero = true := by
  unfold CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool
  unfold CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare
  unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.total_order_T
  cases hdec : ctx.spec.lt_dec x ctx.spec.zero with
  | left _ => simp
  | right hn => exact (hn h).elim

private theorem pg_rlt_bool_false (ctx : ExactRealContext) (x : ctx.spec.carrier)
    (h : ctx.spec.le ctx.spec.zero x) :
    CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x ctx.spec.zero = false := by
  have hnot : ¬ctx.spec.lt x ctx.spec.zero := by
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

private theorem pg_le_lt_trans (ctx : ExactRealContext) (a b c : ctx.spec.carrier)
    (hab : ctx.spec.le a b) (hbc : ctx.spec.lt b c) : ctx.spec.lt a c := by
  apply (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
  constructor
  · exact ctx.certificate.orderedField.le_trans _ _ _ hab
      ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hbc).1
  · intro hca
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hbc).2
      (ctx.certificate.orderedField.le_trans _ _ _ hca hab)

private theorem pg_lt_le_trans (ctx : ExactRealContext) (a b c : ctx.spec.carrier)
    (hab : ctx.spec.lt a b) (hbc : ctx.spec.le b c) : ctx.spec.lt a c := by
  apply (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
  constructor
  · exact ctx.certificate.orderedField.le_trans _ _ _
      ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hab).1 hbc
  · intro hca
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hab).2
      (ctx.certificate.orderedField.le_trans _ _ _ hbc hca)

private theorem pg_floor_imp (ctx : ExactRealContext) (n : Z) (x : ctx.spec.carrier)
    (hl : ctx.spec.le (ctx.spec.ofZ n) x)
    (hu : ctx.spec.lt x (ctx.spec.ofZ (Zadd n Zone))) :
    CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx x = n := by
  let u := ctx.spec.up x
  have hnu : Zlt n u :=
    pg_izr_lt_inv ctx n u
      (pg_le_lt_trans ctx (ctx.spec.ofZ n) x (ctx.spec.ofZ u) hl
        (ctx.certificate.sourceLaws.up_gt x))
  have hgap : ctx.spec.le (ctx.spec.add (ctx.spec.ofZ u) (ctx.spec.neg x)) ctx.spec.one := by
    change ctx.spec.le
      (CompCert4Lean.Flocq.Core.Raux.Exact.Rminus ctx (ctx.spec.ofZ u) x) _
    rw [<- ctx.certificate.sourceLaws.ofZ_one]
    exact ctx.certificate.sourceLaws.up_gap x
  have hule : Zle u (Zadd n Zone) := by
    by_cases hle : Zle u (Zadd n Zone)
    · exact hle
    · exfalso
      have hku : Zlt (Zadd n Zone) u := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt
          (Zadd n Zone) u
        simp only [Zadd,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          intOfZ_zOfInt]
        change intOfZ n + 1 < intOfZ u
        change ¬CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
          u (Zadd n Zone) at hle
        simp only [Zadd,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          intOfZ_zOfInt] at hle
        change ¬(intOfZ u <= intOfZ n + 1) at hle
        omega
      have hkplus : Zle (Zadd (Zadd n Zone) Zone) u := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
          (Zadd (Zadd n Zone) Zone) u
        simp only [Zadd,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          intOfZ_zOfInt]
        have hone : intOfZ Zone = 1 := rfl
        rw [hone]
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt
          (Zadd n Zone) u at hku
        simp only [Zadd,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          intOfZ_zOfInt] at hku
        rw [hone] at hku
        omega
      have hxle := pg_izr_le ctx _ _ hkplus
      have hxplus : ctx.spec.lt (ctx.spec.add x ctx.spec.one)
          (ctx.spec.ofZ (Zadd (Zadd n Zone) Zone)) := by
        have h := ctx.certificate.orderedField.add_lt_compat_l ctx.spec.one x
          (ctx.spec.ofZ (Zadd n Zone)) hu
        rw [ctx.certificate.orderedField.add_comm ctx.spec.one x] at h
        have hcast : ctx.spec.ofZ (Zadd (Zadd n Zone) Zone) =
            ctx.spec.add (ctx.spec.ofZ (Zadd n Zone)) ctx.spec.one := by
          rw [ctx.certificate.sourceLaws.ofZ_add,
            ctx.certificate.sourceLaws.ofZ_one]
        rw [hcast]
        rw [ctx.certificate.orderedField.add_comm ctx.spec.one
          (ctx.spec.ofZ (Zadd n Zone))] at h
        exact h
      have hxltu := pg_lt_le_trans ctx _ _ _ hxplus hxle
      have huupper : ctx.spec.le (ctx.spec.ofZ u) (ctx.spec.add x ctx.spec.one) := by
        by_cases hleu : ctx.spec.le (ctx.spec.ofZ u) (ctx.spec.add x ctx.spec.one)
        · exact hleu
        · exfalso
          rcases ctx.certificate.total_order (ctx.spec.ofZ u) (ctx.spec.add x ctx.spec.one) with h | h
          · rcases h with hlt | heq
            · exact hleu ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt).1
            · exact hleu (by rw [heq]; exact ctx.certificate.orderedField.le_refl _)
          · have hshift := ctx.certificate.orderedField.add_lt_compat_l
              (ctx.spec.neg x) (ctx.spec.add x ctx.spec.one) (ctx.spec.ofZ u) h
            rw [<- ctx.certificate.orderedField.add_assoc,
              ctx.certificate.orderedField.neg_add_cancel,
              ctx.certificate.orderedField.zero_add,
              ctx.certificate.orderedField.add_comm (ctx.spec.neg x) (ctx.spec.ofZ u)] at hshift
            exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hshift).2 hgap
      exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxltu).2 huupper
  have hu_eq : u = Zadd n Zone := by
    apply intOfZ_injective
    change intOfZ u = intOfZ (Zadd n Zone)
    simp only [Zadd,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      intOfZ_zOfInt]
    have hone : intOfZ Zone = 1 := rfl
    rw [hone]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
      u (Zadd n Zone) at hule
    simp only [Zadd,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      intOfZ_zOfInt] at hule
    rw [hone] at hule
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt n u at hnu
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt] at hnu
    omega
  unfold CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor
  change Zsub u Zone = n
  rw [hu_eq]
  apply intOfZ_injective
  change intOfZ (Zsub (Zadd n Zone) Zone) = intOfZ n
  simp only [Zsub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    Zadd,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    intOfZ_zOfInt]
  change intOfZ n + 1 - 1 = intOfZ n
  omega

private theorem pg_neg_neg (ctx : ExactRealContext) (x : ctx.spec.carrier) :
    ctx.spec.neg (ctx.spec.neg x) = x := by
  calc
    ctx.spec.neg (ctx.spec.neg x) =
        ctx.spec.add (ctx.spec.neg (ctx.spec.neg x)) ctx.spec.zero :=
      (ctx.certificate.orderedField.add_zero _).symm
    _ = ctx.spec.add (ctx.spec.neg (ctx.spec.neg x)) (ctx.spec.add (ctx.spec.neg x) x) := by
      rw [ctx.certificate.orderedField.neg_add_cancel]
    _ = ctx.spec.add (ctx.spec.add (ctx.spec.neg (ctx.spec.neg x)) (ctx.spec.neg x)) x := by
      rw [ctx.certificate.orderedField.add_assoc]
    _ = ctx.spec.add ctx.spec.zero x := by
      rw [ctx.certificate.orderedField.neg_add_cancel]
    _ = x := ctx.certificate.orderedField.zero_add _

private theorem pg_neg_lt_swap (ctx : ExactRealContext) (x y : ctx.spec.carrier)
    (h : ctx.spec.lt (ctx.spec.neg x) y) : ctx.spec.lt (ctx.spec.neg y) x := by
  have h1 := ctx.certificate.orderedField.add_lt_compat_l x (ctx.spec.neg x) y h
  rw [ctx.certificate.orderedField.add_comm x (ctx.spec.neg x),
    ctx.certificate.orderedField.neg_add_cancel] at h1
  have h2 := ctx.certificate.orderedField.add_lt_compat_l
    (ctx.spec.neg y) ctx.spec.zero (ctx.spec.add x y) h1
  rw [ctx.certificate.orderedField.add_zero] at h2
  rw [<- ctx.certificate.orderedField.add_assoc,
    ctx.certificate.orderedField.add_comm (ctx.spec.neg y) x,
    ctx.certificate.orderedField.add_assoc,
    ctx.certificate.orderedField.neg_add_cancel,
    ctx.certificate.orderedField.add_zero] at h2
  exact h2

theorem inbetween_int_DN_sign (ctx : ExactRealContext) :
    inbetween_int_DN_signStatement ctx := by
  intro x m l hx
  change CompCert4Lean.Flocq.Calc.Bracket.inbetween_int ctx m
    (CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x) l at hx
  change CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx x =
    cond_Zopp (CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x ctx.spec.zero)
      (cond_incr
        (round_sign_DN (CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x ctx.spec.zero) l) m)
  by_cases hneg : ctx.spec.lt x ctx.spec.zero
  · have hbool := pg_rlt_bool_true ctx x hneg
    rw [hbool]
    have habs : CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x = ctx.spec.neg x :=
      ctx.certificate.sourceLaws.abs_negative x hneg
    cases hx with
    | inbetween_Exact h =>
        simp [cond_Zopp, round_sign_DN, cond_incr]
        have hxval : x = ctx.spec.neg (ctx.spec.ofZ m) := by
          calc
            x = ctx.spec.neg (ctx.spec.neg x) := (pg_neg_neg ctx x).symm
            _ = ctx.spec.neg (CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x) := by rw [habs]
            _ = ctx.spec.neg (ctx.spec.ofZ m) := congrArg ctx.spec.neg (by
              change CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x = ctx.spec.ofZ m
              exact h)
        rw [hxval, <- ctx.certificate.sourceLaws.ofZ_neg]
        exact pg_floor_izr ctx (Zopp m)
    | inbetween_Inexact c hbounds hmiddle =>
        simp [cond_Zopp, round_sign_DN, cond_incr]
        change CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx x = Zopp (Zadd m Zone)
        have hstrict := pg_neg_lt_swap ctx x (ctx.spec.ofZ (Zadd m Zone)) (by
          change ctx.spec.lt (ctx.spec.neg x) (ctx.spec.ofZ (Zadd m Zone))
          rw [<- habs]
          exact hbounds.2)
        have hlower : ctx.spec.le (ctx.spec.ofZ (Zopp (Zadd m Zone))) x := by
          rw [ctx.certificate.sourceLaws.ofZ_neg]
          exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hstrict |>.1
        have hpre : ctx.spec.lt (ctx.spec.neg (ctx.spec.neg (ctx.spec.ofZ m)))
            (ctx.spec.neg x) := by
          rw [pg_neg_neg]
          change ctx.spec.lt (ctx.spec.ofZ m) (ctx.spec.neg x)
          rw [<- habs]
          exact hbounds.1
        have hupper0 := pg_neg_lt_swap ctx (ctx.spec.neg (ctx.spec.ofZ m)) (ctx.spec.neg x) hpre
        have hupper1 : ctx.spec.lt x (ctx.spec.ofZ (Zopp m)) := by
          rw [pg_neg_neg] at hupper0
          rw [<- ctx.certificate.sourceLaws.ofZ_neg] at hupper0
          exact hupper0
        have htarget : Zadd (Zopp (Zadd m Zone)) Zone = Zopp m := by
          apply intOfZ_injective
          change intOfZ (Zadd (Zopp (Zadd m Zone)) Zone) = intOfZ (Zopp m)
          simp only [Zadd,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
            Zopp,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
            intOfZ_zOfInt]
          have hone : intOfZ Zone = 1 := rfl
          rw [hone]
          omega
        have hupper : ctx.spec.lt x
            (ctx.spec.ofZ (Zadd (Zopp (Zadd m Zone)) Zone)) := by
          rw [htarget]
          exact hupper1
        exact pg_floor_imp ctx (Zopp (Zadd m Zone)) x hlower hupper
  · have hnonneg : ctx.spec.le ctx.spec.zero x := by
      rcases ctx.certificate.total_order x ctx.spec.zero with h | h
      · rcases h with hlt | heq
        · exact (hneg hlt).elim
        · rw [heq]
          exact ctx.certificate.orderedField.le_refl _
      · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1
    have hbool := pg_rlt_bool_false ctx x hnonneg
    rw [hbool]
    have habs : CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x = x :=
      ctx.certificate.sourceLaws.abs_nonnegative x hnonneg
    cases hx with
    | inbetween_Exact h =>
        simp [cond_Zopp, round_sign_DN, cond_incr]
        rw [habs] at h
        change x = ctx.spec.ofZ m at h
        rw [h]
        exact pg_floor_izr ctx m
    | inbetween_Inexact c hbounds hmiddle =>
        simp [cond_Zopp, round_sign_DN, cond_incr]
        rw [habs] at hbounds
        exact pg_floor_imp ctx m x
          ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hbounds.1).1 hbounds.2

end CompCert4Lean.Flocq.Calc.Round

namespace CompCert4Lean.Flocq.Calc.Round

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem pg_zopp_zopp (n : Z) : Zopp (Zopp n) = n := by
  apply intOfZ_injective
  change intOfZ (Zopp (Zopp n)) = intOfZ n
  simp only [Zopp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
    intOfZ_zOfInt]
  omega

private theorem pg_neg_le_swap (ctx : ExactRealContext)
    (a b : ctx.spec.carrier) (h : ctx.spec.le a b) :
    ctx.spec.le (ctx.spec.neg b) (ctx.spec.neg a) := by
  rcases ctx.certificate.total_order (ctx.spec.neg b) (ctx.spec.neg a) with h' | h'
  · rcases h' with hlt | heq
    · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt |>.1
    · rw [heq]
      exact ctx.certificate.orderedField.le_refl _
  · have hltba0 := pg_neg_lt_swap ctx a (ctx.spec.neg b) h'
    have hltba : ctx.spec.lt b a := by
      rw [pg_neg_neg] at hltba0
      exact hltba0
    exact (((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hltba).2 h).elim

private theorem pg_ceil_izr (ctx : ExactRealContext) (n : Z) :
    CompCert4Lean.Flocq.Core.Raux.Exact.Zceil ctx (ctx.spec.ofZ n) = n := by
  unfold CompCert4Lean.Flocq.Core.Raux.Exact.Zceil
  change Zopp (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx
    (ctx.spec.neg (ctx.spec.ofZ n))) = n
  rw [← ctx.certificate.sourceLaws.ofZ_neg, pg_floor_izr, pg_zopp_zopp]

private theorem pg_ceil_imp (ctx : ExactRealContext) (n : Z) (x : ctx.spec.carrier)
    (hl : ctx.spec.lt (ctx.spec.ofZ (Zsub n Zone)) x)
    (hu : ctx.spec.le x (ctx.spec.ofZ n)) :
    CompCert4Lean.Flocq.Core.Raux.Exact.Zceil ctx x = n := by
  have hlow : ctx.spec.le (ctx.spec.ofZ (Zopp n)) (ctx.spec.neg x) := by
    rw [ctx.certificate.sourceLaws.ofZ_neg]
    exact pg_neg_le_swap ctx x (ctx.spec.ofZ n) hu
  have hupper : ctx.spec.lt (ctx.spec.neg x)
      (ctx.spec.ofZ (Zadd (Zopp n) Zone)) := by
    have hneg := pg_neg_lt_swap ctx (ctx.spec.neg (ctx.spec.ofZ (Zsub n Zone))) x (by
      rw [pg_neg_neg]
      exact hl)
    rw [← ctx.certificate.sourceLaws.ofZ_neg] at hneg
    have htarget : Zopp (Zsub n Zone) = Zadd (Zopp n) Zone := by
      apply intOfZ_injective
      change intOfZ (Zopp (Zsub n Zone)) = intOfZ (Zadd (Zopp n) Zone)
      simp only [Zopp, Zsub, Zadd,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        intOfZ_zOfInt]
      have hone : intOfZ Zone = 1 := rfl
      rw [hone]
      omega
    change ctx.spec.lt (ctx.spec.neg x)
      (ctx.spec.ofZ (Zopp (Zsub n Zone))) at hneg
    rw [htarget] at hneg
    exact hneg
  unfold CompCert4Lean.Flocq.Core.Raux.Exact.Zceil
  change Zopp (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx
    (ctx.spec.neg x)) = n
  rw [pg_floor_imp ctx (Zopp n) (ctx.spec.neg x) hlow hupper,
    pg_zopp_zopp]

theorem inbetween_int_UP_sign (ctx : ExactRealContext) :
    inbetween_int_UP_signStatement ctx := by
  intro x m l hx
  change CompCert4Lean.Flocq.Calc.Bracket.inbetween_int ctx m
    (CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x) l at hx
  change CompCert4Lean.Flocq.Core.Raux.Exact.Zceil ctx x =
    cond_Zopp (CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x ctx.spec.zero)
      (cond_incr
        (round_sign_UP (CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x ctx.spec.zero) l) m)
  by_cases hneg : ctx.spec.lt x ctx.spec.zero
  · have hbool := pg_rlt_bool_true ctx x hneg
    rw [hbool]
    have habs : CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x = ctx.spec.neg x :=
      ctx.certificate.sourceLaws.abs_negative x hneg
    cases hx with
    | inbetween_Exact h =>
        simp [cond_Zopp, round_sign_UP, cond_incr]
        have hxval : x = ctx.spec.neg (ctx.spec.ofZ m) := by
          calc
            x = ctx.spec.neg (ctx.spec.neg x) := (pg_neg_neg ctx x).symm
            _ = ctx.spec.neg (CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x) := by rw [habs]
            _ = ctx.spec.neg (ctx.spec.ofZ m) := congrArg ctx.spec.neg (by
              change CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x = ctx.spec.ofZ m
              exact h)
        rw [hxval, ← ctx.certificate.sourceLaws.ofZ_neg]
        exact pg_ceil_izr ctx (Zopp m)
    | inbetween_Inexact c hbounds hmiddle =>
        simp [cond_Zopp, round_sign_UP, cond_incr]
        change CompCert4Lean.Flocq.Core.Raux.Exact.Zceil ctx x = Zopp m
        have hstrict := pg_neg_lt_swap ctx x (ctx.spec.ofZ (Zadd m Zone)) (by
          change ctx.spec.lt (ctx.spec.neg x) (ctx.spec.ofZ (Zadd m Zone))
          rw [← habs]
          exact hbounds.2)
        have hlower : ctx.spec.lt (ctx.spec.ofZ (Zsub (Zopp m) Zone)) x := by
          rw [← ctx.certificate.sourceLaws.ofZ_neg] at hstrict
          have htarget : Zopp (Zadd m Zone) = Zsub (Zopp m) Zone := by
            apply intOfZ_injective
            change intOfZ (Zopp (Zadd m Zone)) = intOfZ (Zsub (Zopp m) Zone)
            simp only [Zopp, Zsub, Zadd,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
              intOfZ_zOfInt]
            omega
          change ctx.spec.lt (ctx.spec.ofZ (Zopp (Zadd m Zone))) x at hstrict
          rw [htarget] at hstrict
          exact hstrict
        have hupper : ctx.spec.le x (ctx.spec.ofZ (Zopp m)) := by
          have hpre : ctx.spec.lt (ctx.spec.ofZ m) (ctx.spec.neg x) := by
            rw [← habs]
            exact hbounds.1
          have hupper0 := pg_neg_lt_swap ctx (ctx.spec.neg (ctx.spec.ofZ m))
            (ctx.spec.neg x) (by
              rw [pg_neg_neg]
              exact hpre)
          rw [pg_neg_neg] at hupper0
          rw [← ctx.certificate.sourceLaws.ofZ_neg] at hupper0
          exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hupper0 |>.1
        exact pg_ceil_imp ctx (Zopp m) x hlower hupper
  · have hnonneg : ctx.spec.le ctx.spec.zero x := by
      rcases ctx.certificate.total_order x ctx.spec.zero with h | h
      · rcases h with hlt | heq
        · exact (hneg hlt).elim
        · rw [heq]
          exact ctx.certificate.orderedField.le_refl _
      · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1
    have hbool := pg_rlt_bool_false ctx x hnonneg
    rw [hbool]
    have habs : CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x = x :=
      ctx.certificate.sourceLaws.abs_nonnegative x hnonneg
    cases hx with
    | inbetween_Exact h =>
        simp [cond_Zopp, round_sign_UP, cond_incr]
        rw [habs] at h
        change x = ctx.spec.ofZ m at h
        rw [h]
        exact pg_ceil_izr ctx m
    | inbetween_Inexact c hbounds hmiddle =>
        simp [cond_Zopp, round_sign_UP, cond_incr]
        rw [habs] at hbounds
        have hsub : Zsub (Zadd m Zone) Zone = m := by
          apply intOfZ_injective
          change intOfZ (Zsub (Zadd m Zone) Zone) = intOfZ m
          simp only [Zsub, Zadd,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
            intOfZ_zOfInt]
          have hone : intOfZ Zone = 1 := rfl
          rw [hone]
          omega
        exact pg_ceil_imp ctx (Zadd m Zone) x
          (by
            change ctx.spec.lt (ctx.spec.ofZ (Zsub (Zadd m Zone) Zone)) x
            rw [hsub]
            exact hbounds.1)
          (by
            change ctx.spec.le x (ctx.spec.ofZ (Zadd m Zone))
            exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hbounds.2 |>.1)

end CompCert4Lean.Flocq.Calc.Round

namespace CompCert4Lean.Flocq.Calc.Round

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem inbetween_int_ZR_sign (ctx : ExactRealContext) :
    inbetween_int_ZR_signStatement ctx := by
  intro x m l hx
  change CompCert4Lean.Flocq.Calc.Bracket.inbetween_int ctx m
    (CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x) l at hx
  change CompCert4Lean.Flocq.Core.Raux.Exact.Ztrunc ctx x =
    cond_Zopp (CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x ctx.spec.zero) m
  by_cases hneg : ctx.spec.lt x ctx.spec.zero
  · have hbool := pg_rlt_bool_true ctx x hneg
    have hbool0 : CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x
        (CompCert4Lean.Flocq.Core.Raux.Exact.R0 ctx) = true := by
      simpa [CompCert4Lean.Flocq.Core.Raux.Exact.R0,
        CompCert4Lean.Foundation.FlocqReal.ExactReal.R0] using hbool
    unfold CompCert4Lean.Flocq.Core.Raux.Exact.Ztrunc
    rw [hbool0]
    simp [cond_Zopp, hbool]
    have habs : CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x = ctx.spec.neg x :=
      ctx.certificate.sourceLaws.abs_negative x hneg
    cases hx with
    | inbetween_Exact h =>
        have hxval : x = ctx.spec.neg (ctx.spec.ofZ m) := by
          calc
            x = ctx.spec.neg (ctx.spec.neg x) := (pg_neg_neg ctx x).symm
            _ = ctx.spec.neg (CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x) := by rw [habs]
            _ = ctx.spec.neg (ctx.spec.ofZ m) := congrArg ctx.spec.neg (by
              change CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x = ctx.spec.ofZ m
              exact h)
        rw [hxval, ← ctx.certificate.sourceLaws.ofZ_neg]
        exact pg_ceil_izr ctx (Zopp m)
    | inbetween_Inexact c hbounds hmiddle =>
        have hstrict := pg_neg_lt_swap ctx x (ctx.spec.ofZ (Zadd m Zone)) (by
          change ctx.spec.lt (ctx.spec.neg x) (ctx.spec.ofZ (Zadd m Zone))
          rw [← habs]
          exact hbounds.2)
        have hlower : ctx.spec.lt (ctx.spec.ofZ (Zsub (Zopp m) Zone)) x := by
          rw [← ctx.certificate.sourceLaws.ofZ_neg] at hstrict
          have htarget : Zopp (Zadd m Zone) = Zsub (Zopp m) Zone := by
            apply intOfZ_injective
            change intOfZ (Zopp (Zadd m Zone)) = intOfZ (Zsub (Zopp m) Zone)
            simp only [Zopp, Zsub, Zadd,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
              intOfZ_zOfInt]
            omega
          change ctx.spec.lt (ctx.spec.ofZ (Zopp (Zadd m Zone))) x at hstrict
          rw [htarget] at hstrict
          exact hstrict
        have hupper : ctx.spec.le x (ctx.spec.ofZ (Zopp m)) := by
          have hpre : ctx.spec.lt (ctx.spec.ofZ m) (ctx.spec.neg x) := by
            rw [← habs]
            exact hbounds.1
          have hupper0 := pg_neg_lt_swap ctx (ctx.spec.neg (ctx.spec.ofZ m))
            (ctx.spec.neg x) (by
              rw [pg_neg_neg]
              exact hpre)
          rw [pg_neg_neg] at hupper0
          rw [← ctx.certificate.sourceLaws.ofZ_neg] at hupper0
          exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hupper0 |>.1
        exact pg_ceil_imp ctx (Zopp m) x hlower hupper
  · have hnonneg : ctx.spec.le ctx.spec.zero x := by
      rcases ctx.certificate.total_order x ctx.spec.zero with h | h
      · rcases h with hlt | heq
        · exact (hneg hlt).elim
        · rw [heq]
          exact ctx.certificate.orderedField.le_refl _
      · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1
    have hbool := pg_rlt_bool_false ctx x hnonneg
    have hbool0 : CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x
        (CompCert4Lean.Flocq.Core.Raux.Exact.R0 ctx) = false := by
      simpa [CompCert4Lean.Flocq.Core.Raux.Exact.R0,
        CompCert4Lean.Foundation.FlocqReal.ExactReal.R0] using hbool
    unfold CompCert4Lean.Flocq.Core.Raux.Exact.Ztrunc
    rw [hbool0]
    simp [cond_Zopp, hbool]
    have habs : CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x = x :=
      ctx.certificate.sourceLaws.abs_nonnegative x hnonneg
    cases hx with
    | inbetween_Exact h =>
        rw [habs] at h
        change x = ctx.spec.ofZ m at h
        rw [h]
        exact pg_floor_izr ctx m
    | inbetween_Inexact c hbounds hmiddle =>
        rw [habs] at hbounds
        exact pg_floor_imp ctx m x
          ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hbounds.1).1 hbounds.2

end CompCert4Lean.Flocq.Calc.Round

namespace CompCert4Lean.Flocq.Calc.Round

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem pg_zdiv_zero (p : Z) (hp : Zlt Z0 p) : Zdiv Z0 p = Z0 := by
  have hmod : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo Z0 p = Z0 := by
    exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mod_small
      Z0 p ⟨by simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le], hp⟩
  have hdivmod :=
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Z_div_mod_eq_full Z0 p
  rw [hmod] at hdivmod
  apply intOfZ_injective
  change intOfZ (Zdiv Z0 p) = intOfZ Z0
  have hprod : intOfZ p * intOfZ (Zdiv Z0 p) = 0 := by
    have hdivmod_int := congrArg intOfZ hdivmod
    simp only [Zadd, Zmul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hdivmod_int
    have hzero : intOfZ Z0 = (0 : Int) := rfl
    change intOfZ p * intOfZ (Zdiv Z0 p) = 0
    rw [hzero] at hdivmod_int
    simpa using hdivmod_int.symm
  have hp0 : intOfZ p ≠ 0 := by
    change ¬ intOfZ p = 0
    intro hp0
    have : ¬ (intOfZ p > 0) := by omega
    exact this hp
  have hz : intOfZ (Zdiv Z0 p) = 0 := by
    exact (Int.mul_eq_zero.mp hprod).resolve_left hp0
  simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] using hz

theorem truncate_0 : truncate_0Statement := by
  intro beta fexp e l
  unfold truncate
  dsimp
  split
  · dsimp [truncate_aux,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div]
    by_cases hp : Zpower beta.radix_val
        (Zsub (fexp (Zadd (Zdigits beta Z0) e)) e) = Z0
    · rw [hp]
      rfl
    · apply pg_zdiv_zero
      have hnonneg := CompCert4Lean.Flocq.Core.Zaux.Zpower_ge_0 beta
        (Zsub (fexp (Zadd (Zdigits beta Z0) e)) e)
      change (0 : Int) ≤ intOfZ (Zpower beta.radix_val
        (Zsub (fexp (Zadd (Zdigits beta Z0) e)) e)) at hnonneg
      change (0 : Int) < intOfZ (Zpower beta.radix_val
        (Zsub (fexp (Zadd (Zdigits beta Z0) e)) e))
      have hne : intOfZ (Zpower beta.radix_val
          (Zsub (fexp (Zadd (Zdigits beta Z0) e)) e)) ≠ 0 := by
        intro hz
        apply hp
        apply intOfZ_injective
        simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] using hz
      omega
  · rfl

end CompCert4Lean.Flocq.Calc.Round

namespace CompCert4Lean.Flocq.Calc.Round

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem pg_rcompare_lt (ctx : ExactRealContext)
    {x y : ctx.spec.carrier} (hxy : ctx.spec.lt x y) :
    CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx x y = Lt := by
  unfold CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare
  unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.total_order_T
  cases hdec : ctx.spec.lt_dec x y with
  | left _ => rfl
  | right hnxy => exact (hnxy hxy).elim

private theorem pg_rcompare_eq (ctx : ExactRealContext)
    {x y : ctx.spec.carrier} (hxy : x = y) :
    CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx x y = Eq := by
  subst y
  cases hdec : ctx.spec.lt_dec x x with
  | left hlt => exact (ctx.certificate.orderedField.lt_irrefl x hlt).elim
  | right _ =>
      simp [CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare,
        CompCert4Lean.Foundation.FlocqReal.ExactReal.total_order_T, hdec]

private theorem pg_rcompare_gt (ctx : ExactRealContext)
    {x y : ctx.spec.carrier} (hyx : ctx.spec.lt y x) :
    CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx x y = Gt := by
  have hnxy : ¬ctx.spec.lt x y := by
    intro hxy
    exact ctx.certificate.orderedField.lt_irrefl x
      (ctx.certificate.orderedField.lt_trans x y x hxy hyx)
  unfold CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare
  unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.total_order_T
  cases hxy : ctx.spec.lt_dec x y with
  | left hlt => exact (hnxy hlt).elim
  | right _ =>
      cases hyx_dec : ctx.spec.lt_dec y x with
      | left _ => rfl
      | right hnyx => exact (hnyx hyx).elim

end CompCert4Lean.Flocq.Calc.Round
