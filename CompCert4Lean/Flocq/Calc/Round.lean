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

namespace CompCert4Lean.Flocq.Calc.Round

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem pg_zopp_add_zero (e : Z) : Zadd (Zopp e) e = Z0 := by
  apply intOfZ_injective
  simp only [Zadd, Zopp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
    intOfZ_zOfInt]
  change -intOfZ e + intOfZ e = 0
  omega

private theorem pg_scaled_mantissa_mult_bpow (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx) (beta : radix) (fexp : Z → Z)
    (x : ExactR ctx) :
    CompCert4Lean.Flocq.Core.Raux.Exact.Rmult ctx
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp x)
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.bpow ctx beta
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x)) = x := by
  change ctx.spec.mul
      (ctx.spec.mul x
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta
          (Zopp (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x))))
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x)) = x
  rw [ctx.certificate.orderedField.mul_assoc]
  have hp := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta
    (Zopp (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x))
    (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x)
  have hp' : ctx.spec.mul
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta
        (Zopp (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x)))
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x)) =
      CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta Z0 := by
    change CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta
        (Zadd (Zopp (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x))
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x)) =
      ctx.spec.mul
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta
          (Zopp (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x)))
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x)) at hp
    rw [pg_zopp_add_zero] at hp
    exact hp.symm
  rw [hp']
  change ctx.spec.mul x ctx.spec.one = x
  rw [ctx.certificate.orderedField.mul_one]

private theorem pg_neg_mul_right (ctx : ExactRealContext)
    (x s : ctx.spec.carrier) :
    ctx.spec.mul (ctx.spec.neg x) s = ctx.spec.neg (ctx.spec.mul x s) := by
  have hsum : ctx.spec.add
      (ctx.spec.mul (ctx.spec.neg x) s) (ctx.spec.mul x s) = ctx.spec.zero := by
    calc
      ctx.spec.add (ctx.spec.mul (ctx.spec.neg x) s) (ctx.spec.mul x s) =
          ctx.spec.mul s (ctx.spec.add (ctx.spec.neg x) x) := by
            rw [ctx.certificate.orderedField.mul_comm (ctx.spec.neg x) s,
              ctx.certificate.orderedField.mul_comm x s,
              ← ctx.certificate.orderedField.left_distrib]
      _ = ctx.spec.mul s ctx.spec.zero := by
        rw [ctx.certificate.orderedField.neg_add_cancel]
      _ = ctx.spec.zero := ctx.certificate.orderedField.mul_zero _
  calc
    ctx.spec.mul (ctx.spec.neg x) s =
        ctx.spec.add (ctx.spec.mul (ctx.spec.neg x) s) ctx.spec.zero :=
      (ctx.certificate.orderedField.add_zero _).symm
    _ = ctx.spec.add (ctx.spec.mul (ctx.spec.neg x) s)
        (ctx.spec.add (ctx.spec.mul x s) (ctx.spec.neg (ctx.spec.mul x s))) := by
      congr 1
      rw [ctx.certificate.orderedField.add_comm]
      exact (ctx.certificate.orderedField.neg_add_cancel _).symm
    _ = ctx.spec.add
        (ctx.spec.add (ctx.spec.mul (ctx.spec.neg x) s) (ctx.spec.mul x s))
        (ctx.spec.neg (ctx.spec.mul x s)) := by
      rw [ctx.certificate.orderedField.add_assoc]
    _ = ctx.spec.neg (ctx.spec.mul x s) := by rw [hsum, ctx.certificate.orderedField.zero_add]

private theorem pg_f2r_mul_bpow_neg (ctx : ExactRealContext) (beta : radix)
    (m e : Z) :
    ctx.spec.mul
      (CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
        (CompCert4Lean.Flocq.Calc.Bracket.Float beta m e))
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Zopp e)) =
      ctx.spec.ofZ m := by
  change ctx.spec.mul
      (ctx.spec.mul (ctx.spec.ofZ m)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e))
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Zopp e)) = ctx.spec.ofZ m
  rw [ctx.certificate.orderedField.mul_assoc]
  have hp := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta (Zopp e) e
  have hp' : ctx.spec.mul
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e)
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Zopp e)) =
      CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta Z0 := by
    rw [ctx.certificate.orderedField.mul_comm]
    change CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta
        (Zadd (Zopp e) e) = _ at hp
    rw [pg_zopp_add_zero] at hp
    exact hp.symm
  rw [hp']
  change ctx.spec.mul (ctx.spec.ofZ m) ctx.spec.one = ctx.spec.ofZ m
  rw [ctx.certificate.orderedField.mul_one]

private theorem pg_abs_mul_pos (ctx : ExactRealContext)
    (x s : ctx.spec.carrier) (hs : ctx.spec.lt ctx.spec.zero s) :
    ctx.spec.abs (ctx.spec.mul x s) =
      ctx.spec.mul (ctx.spec.abs x) s := by
  rcases ctx.certificate.total_order x ctx.spec.zero with h | h
  · rcases h with hneg | heq
    · have hxs : ctx.spec.lt (ctx.spec.mul x s) ctx.spec.zero := by
        have h' := ctx.certificate.orderedField.mul_lt_compat_l s x
          ctx.spec.zero hs hneg
        rw [ctx.certificate.orderedField.mul_comm s x,
          ctx.certificate.orderedField.mul_zero] at h'
        exact h'
      rw [ctx.certificate.sourceLaws.abs_negative _ hxs,
        ctx.certificate.sourceLaws.abs_negative _ hneg]
      exact (pg_neg_mul_right ctx x s).symm
    · subst x
      rw [ctx.certificate.sourceLaws.abs_nonnegative _
        (ctx.certificate.orderedField.le_refl _),
        ctx.certificate.orderedField.zero_mul,
        ctx.certificate.sourceLaws.abs_nonnegative _
          (ctx.certificate.orderedField.le_refl _)]
  · have hpos : ctx.spec.lt ctx.spec.zero x := h
    have hxs : ctx.spec.lt ctx.spec.zero (ctx.spec.mul x s) := by
      have h' := ctx.certificate.orderedField.mul_lt_compat_l s
        ctx.spec.zero x hs hpos
      rw [ctx.certificate.orderedField.mul_zero,
        ctx.certificate.orderedField.mul_comm s x] at h'
      exact h'
    have hxle := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hpos |>.1
    have hxsle := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxs |>.1
    rw [ctx.certificate.sourceLaws.abs_nonnegative _ hxsle,
      ctx.certificate.sourceLaws.abs_nonnegative _ hxle]

private theorem pg_inbetween_int_scaled (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx) (beta : radix) (fexp : Z → Z)
    (x : ExactR ctx) (m e : Z) (l : location)
    (hbetween : CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx beta m e
      (CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x) l)
    (he : e = CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x) :
    CompCert4Lean.Flocq.Calc.Bracket.inbetween_int ctx m
      (CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp x)) l := by
  have hs : ctx.spec.lt ctx.spec.zero
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Zopp e)) := by
    exact CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta (Zopp e)
  have hmul1 := pg_f2r_mul_bpow_neg ctx beta m e
  have hmul2 := pg_f2r_mul_bpow_neg ctx beta (Zadd m Zone) e
  have hs' : CompCert4Lean.Flocq.Calc.Bracket.Rlt ctx
      (CompCert4Lean.Flocq.Calc.Bracket.IZR ctx Z0)
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Zopp e)) := by
    change ctx.spec.lt (ctx.spec.ofZ Z0)
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Zopp e))
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hs
  have htrans := CompCert4Lean.Flocq.Calc.Bracket.inbetween_mult_compat ctx
    (CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
      (CompCert4Lean.Flocq.Calc.Bracket.Float beta m e))
    (CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
      (CompCert4Lean.Flocq.Calc.Bracket.Float beta (Zadd m Zone) e))
    (CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x) l
    (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Zopp e)) hs' hbetween
  have hmul1' : CompCert4Lean.Flocq.Calc.Bracket.Rmult ctx
      (CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
        (CompCert4Lean.Flocq.Calc.Bracket.Float beta m e))
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Zopp e)) =
      ctx.spec.ofZ m := hmul1
  have hmul2' : CompCert4Lean.Flocq.Calc.Bracket.Rmult ctx
      (CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
        (CompCert4Lean.Flocq.Calc.Bracket.Float beta (Zadd m Zone) e))
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Zopp e)) =
      ctx.spec.ofZ (Zadd m Zone) := hmul2
  rw [hmul1', hmul2'] at htrans
  have habs : CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp x) =
      CompCert4Lean.Flocq.Calc.Bracket.Rmult ctx
        (CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Zopp e)) := by
    unfold CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
    rw [← he]
    change ctx.spec.abs (ctx.spec.mul x
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Zopp e))) =
      ctx.spec.mul (ctx.spec.abs x)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Zopp e))
    exact pg_abs_mul_pos ctx x _ hs
  rw [habs]
  simpa [CompCert4Lean.Flocq.Calc.Bracket.inbetween_int,
    CompCert4Lean.Flocq.Calc.Bracket.IZR,
    CompCert4Lean.Flocq.Core.Float_prop.Exact.IZR,
    CompCert4Lean.Flocq.Core.Raux.Exact.IZR,
    CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR] using htrans

private theorem pg_rlt_bool_scaled (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx) (beta : radix) (fexp : Z → Z)
    (x : ExactR ctx) :
    CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp x)
      ctx.spec.zero =
    CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x ctx.spec.zero := by
  let e := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x
  let s := CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Zopp e)
  have hs : ctx.spec.lt ctx.spec.zero s := by
    exact CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta (Zopp e)
  have hzero : CompCert4Lean.Flocq.Core.Raux.Exact.R0 ctx = ctx.spec.zero := rfl
  rcases ctx.certificate.total_order x ctx.spec.zero with h | h
  · rcases h with hneg | heq
    · have hscaled : ctx.spec.lt
          (ctx.spec.mul x s) ctx.spec.zero := by
        have hh := ctx.certificate.orderedField.mul_lt_compat_l s x
          ctx.spec.zero hs hneg
        rw [ctx.certificate.orderedField.mul_comm s x,
          ctx.certificate.orderedField.mul_zero] at hh
        exact hh
      have hb1 := pg_rlt_bool_true ctx x hneg
      have hb2 := pg_rlt_bool_true ctx
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp x)
        (by simpa [e, s,
          CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa,
          CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rmult,
          CompCert4Lean.Flocq.Core.Raux.Exact.Rmult,
          CompCert4Lean.Foundation.FlocqReal.ExactReal.Rmult] using hscaled)
      exact hb2.trans hb1.symm
    · subst x
      have hb1 := pg_rlt_bool_false ctx ctx.spec.zero
        (ctx.certificate.orderedField.le_refl _)
      have hb2 : ctx.spec.le ctx.spec.zero
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp ctx.spec.zero) := by
        unfold CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
        change ctx.spec.le ctx.spec.zero
          (ctx.spec.mul ctx.spec.zero
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta
              (Zopp (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp ctx.spec.zero))))
        rw [ctx.certificate.orderedField.zero_mul]
        exact ctx.certificate.orderedField.le_refl _
      have hb3 := pg_rlt_bool_false ctx
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp ctx.spec.zero) hb2
      exact hb3.trans hb1.symm
  · have hpos : ctx.spec.lt ctx.spec.zero x := h
    have hscaled : ctx.spec.lt ctx.spec.zero
        (ctx.spec.mul x s) := by
      have hh := ctx.certificate.orderedField.mul_lt_compat_l s
        ctx.spec.zero x hs hpos
      rw [ctx.certificate.orderedField.mul_zero,
        ctx.certificate.orderedField.mul_comm s x] at hh
      exact hh
    have hxle := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hpos |>.1
    have hscle := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hscaled |>.1
    have hb1 := pg_rlt_bool_false ctx x hxle
    have hb2 := pg_rlt_bool_false ctx
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp x)
      (by simpa [e, s,
        CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa,
        CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rmult,
        CompCert4Lean.Flocq.Core.Raux.Exact.Rmult,
        CompCert4Lean.Foundation.FlocqReal.ExactReal.Rmult] using hscle)
    exact hb2.trans hb1.symm

private theorem pg_scaled_mantissa_generic
    (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (fexp : Z → Z) (x : ExactR ctx)
    (hformat : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.generic_format
      ctx magnitude beta fexp x) :
    CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp x =
      CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx
        (CompCert4Lean.Flocq.Core.Raux.Exact.Ztrunc ctx
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp x)) := by
  let k := CompCert4Lean.Flocq.Core.Raux.Exact.Ztrunc ctx
    (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp x)
  let e := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x
  have hformat' : x = CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
      (CompCert4Lean.Flocq.Calc.Bracket.Float beta k e) := by
    simpa [k, e, CompCert4Lean.Flocq.Core.Generic_fmt.Exact.generic_format] using hformat
  change ctx.spec.mul x
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Zopp e)) =
    CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx k
  rw [hformat']
  change ctx.spec.mul
      (CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
        (CompCert4Lean.Flocq.Calc.Bracket.Float beta k e))
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Zopp e)) =
    CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx k
  exact pg_f2r_mul_bpow_neg ctx beta k e

private theorem pg_round_generic
    (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (fexp : Z → Z) (rnd : ExactR ctx → Z)
    (hrnd : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Valid_rnd ctx rnd)
    (x : ExactR ctx)
    (hformat : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.generic_format
      ctx magnitude beta fexp x) :
    CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round ctx magnitude beta fexp rnd x = x := by
  let k := CompCert4Lean.Flocq.Core.Raux.Exact.Ztrunc ctx
    (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp x)
  let e := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x
  have hformat' : x = CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
      (CompCert4Lean.Flocq.Calc.Bracket.Float beta k e) := by
    simpa [k, e, CompCert4Lean.Flocq.Core.Generic_fmt.Exact.generic_format] using hformat
  unfold CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
  have hsm := pg_scaled_mantissa_generic ctx magnitude beta fexp x hformat
  change CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
      (CompCert4Lean.Flocq.Calc.Bracket.Float beta
        (rnd (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp x)) e) = x
  rw [hsm]
  rw [hrnd.Zrnd_IZR]
  exact hformat'.symm

private theorem pg_neg_lt_zero_of_pos (ctx : ExactRealContext)
    {x : ctx.spec.carrier} (hx : ctx.spec.lt ctx.spec.zero x) :
    ctx.spec.lt (ctx.spec.neg x) ctx.spec.zero := by
  have h := ctx.certificate.orderedField.add_lt_compat_l
    (ctx.spec.neg x) ctx.spec.zero x hx
  rw [ctx.certificate.orderedField.add_zero] at h
  rw [ctx.certificate.orderedField.neg_add_cancel] at h
  exact h

private theorem pg_abs_pos_of_neg (ctx : ExactRealContext)
    {x : ctx.spec.carrier} (hx : ctx.spec.lt x ctx.spec.zero) :
    ctx.spec.lt ctx.spec.zero (ctx.spec.abs x) := by
  rw [ctx.certificate.sourceLaws.abs_negative x hx]
  have h := ctx.certificate.orderedField.add_lt_compat_l
    (ctx.spec.neg x) x ctx.spec.zero hx
  rw [ctx.certificate.orderedField.neg_add_cancel,
    ctx.certificate.orderedField.add_zero] at h
  exact h

private theorem pg_round_sign_exact
    (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (fexp : Z → Z) (rnd : ExactR ctx → Z)
    (choice : Bool → Z → location → Z)
    (hrnd : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Valid_rnd ctx rnd)
    (hchoice : ∀ (x : ExactR ctx) (m : Z) (l : location),
      CompCert4Lean.Flocq.Calc.Bracket.inbetween_int ctx m
          (CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x) l →
        rnd x = cond_Zopp
          (CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x ctx.spec.zero)
          (choice
            (CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x ctx.spec.zero) m l))
    (x : ExactR ctx) (m e : Z)
    (habs : CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x =
      CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
        (CompCert4Lean.Flocq.Calc.Bracket.Float beta m e))
    (hformat : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.generic_format
      ctx magnitude beta fexp x) :
    CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round ctx magnitude beta fexp rnd x =
      CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
        (CompCert4Lean.Flocq.Calc.Bracket.Float beta
          (cond_Zopp (CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x ctx.spec.zero)
            (choice (CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x ctx.spec.zero)
              m CompCert4Lean.Flocq.Calc.Bracket.loc_Exact)) e) := by
  have hround := pg_round_generic ctx magnitude beta fexp rnd hrnd x hformat
  change ctx.spec.abs x = CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
    (CompCert4Lean.Flocq.Core.Float_prop.Float beta m e) at habs
  rcases ctx.certificate.total_order x ctx.spec.zero with h | h
  · rcases h with hneg | hzero
    · have hposabs := pg_abs_pos_of_neg ctx hneg
      have hposf : ctx.spec.lt ctx.spec.zero
          (CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
            (CompCert4Lean.Flocq.Calc.Bracket.Float beta m e)) := by
        change ctx.spec.lt ctx.spec.zero
          (CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
            (CompCert4Lean.Flocq.Core.Float_prop.Float beta m e))
        rw [← habs]
        exact hposabs
      have hmpos := CompCert4Lean.Flocq.Core.Float_prop.gt_0_F2R ctx beta m e hposf
      have hmposR : ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ m) :=
        pg_izr_pos_z ctx m hmpos
      have hmnegR : ctx.spec.lt (ctx.spec.ofZ (Zopp m)) ctx.spec.zero := by
        rw [ctx.certificate.sourceLaws.ofZ_neg]
        exact pg_neg_lt_zero_of_pos ctx hmposR
      have hcm : choice true m CompCert4Lean.Flocq.Calc.Bracket.loc_Exact = m := by
        have htmp : CompCert4Lean.Flocq.Calc.Bracket.inbetween_int ctx m
            (CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx
              (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx (Zopp m)))
            CompCert4Lean.Flocq.Calc.Bracket.loc_Exact := by
          apply CompCert4Lean.Flocq.Calc.Bracket.inbetween_Exact
          change ctx.spec.abs (ctx.spec.ofZ (Zopp m)) = ctx.spec.ofZ m
          rw [ctx.certificate.sourceLaws.abs_negative _ hmnegR,
            ctx.certificate.sourceLaws.ofZ_neg]
          exact pg_neg_neg ctx (ctx.spec.ofZ m)
        have hh := hchoice (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx (Zopp m)) m
          CompCert4Lean.Flocq.Calc.Bracket.loc_Exact htmp
        have hb : CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx
            (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx (Zopp m)) ctx.spec.zero = true := by
          apply pg_rlt_bool_true ctx
          change ctx.spec.lt (ctx.spec.ofZ (Zopp m)) ctx.spec.zero
          exact hmnegR
        rw [hb] at hh
        rw [hrnd.Zrnd_IZR] at hh
        have hh' : Zopp m = Zopp
            (choice true m CompCert4Lean.Flocq.Calc.Bracket.loc_Exact) := by
          have hcond : cond_Zopp true
              (choice true m CompCert4Lean.Flocq.Calc.Bracket.loc_Exact) =
              Zopp (choice true m CompCert4Lean.Flocq.Calc.Bracket.loc_Exact) := by
            unfold cond_Zopp CompCert4Lean.Flocq.Core.Zaux.cond_Zopp
            rfl
          rw [hcond] at hh
          exact hh
        have hi := congrArg intOfZ hh'
        simp only [Zopp,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
          intOfZ_zOfInt] at hi
        exact (by
          apply intOfZ_injective
          change intOfZ (choice true m CompCert4Lean.Flocq.Calc.Bracket.loc_Exact) =
            intOfZ m
          omega)
      rw [hround]
      have hb : CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x ctx.spec.zero = true :=
        pg_rlt_bool_true ctx x hneg
      rw [hb, hcm]
      simp [cond_Zopp]
      change x = CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
        (CompCert4Lean.Flocq.Core.Float_prop.Float beta (Zopp m) e)
      rw [CompCert4Lean.Flocq.Core.Float_prop.F2R_Zopp]
      rw [← habs]
      rw [ctx.certificate.sourceLaws.abs_negative x hneg]
      exact (pg_neg_neg ctx x).symm
    · subst x
      have hfzero : CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
          (CompCert4Lean.Flocq.Core.Float_prop.Float beta m e) =
          CompCert4Lean.Flocq.Core.Float_prop.Exact.R0 ctx := by
        change CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
          (CompCert4Lean.Flocq.Core.Float_prop.Float beta m e) = ctx.spec.zero
        rw [← habs]
        change ctx.spec.abs ctx.spec.zero = ctx.spec.zero
        exact ctx.certificate.sourceLaws.abs_nonnegative _
          (ctx.certificate.orderedField.le_refl _)
      have hmzero := CompCert4Lean.Flocq.Core.Float_prop.eq_0_F2R ctx beta m e hfzero
      subst m
      have hb : CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx
          (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx Z0) ctx.spec.zero = false := by
        apply pg_rlt_bool_false ctx
        change ctx.spec.le ctx.spec.zero (ctx.spec.ofZ Z0)
        rw [ctx.certificate.sourceLaws.ofZ_zero]
        exact ctx.certificate.orderedField.le_refl _
      have hcm : choice false Z0 CompCert4Lean.Flocq.Calc.Bracket.loc_Exact = Z0 := by
        have hh := hchoice (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx Z0) Z0
          CompCert4Lean.Flocq.Calc.Bracket.loc_Exact (by
            apply CompCert4Lean.Flocq.Calc.Bracket.inbetween_Exact
            change ctx.spec.abs (ctx.spec.ofZ Z0) = ctx.spec.ofZ Z0
            rw [ctx.certificate.sourceLaws.ofZ_zero]
            exact ctx.certificate.sourceLaws.abs_nonnegative _
              (ctx.certificate.orderedField.le_refl _))
        rw [hb, hrnd.Zrnd_IZR] at hh
        have hh' : Z0 = cond_Zopp false
            (choice false Z0 CompCert4Lean.Flocq.Calc.Bracket.loc_Exact) := by
          simpa using hh
        rw [show cond_Zopp false
            (choice false Z0 CompCert4Lean.Flocq.Calc.Bracket.loc_Exact) =
            choice false Z0 CompCert4Lean.Flocq.Calc.Bracket.loc_Exact by
              unfold cond_Zopp CompCert4Lean.Flocq.Core.Zaux.cond_Zopp
              rfl] at hh'
        exact hh'.symm
      have hbzero : CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx
          ctx.spec.zero ctx.spec.zero = false := by
        apply pg_rlt_bool_false ctx
        exact ctx.certificate.orderedField.le_refl _
      rw [hround, hbzero, hcm]
      simp [cond_Zopp]
      change ctx.spec.zero = CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
        (CompCert4Lean.Flocq.Core.Float_prop.Float beta Z0 e)
      rw [CompCert4Lean.Flocq.Core.Float_prop.F2R_0]
      exact rfl
  · have hpos := h
    have hle := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hpos |>.1
    have hposf : ctx.spec.lt ctx.spec.zero
        (CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
          (CompCert4Lean.Flocq.Calc.Bracket.Float beta m e)) := by
      change ctx.spec.lt ctx.spec.zero
        (CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
          (CompCert4Lean.Flocq.Core.Float_prop.Float beta m e))
      rw [← habs]
      change ctx.spec.lt ctx.spec.zero (ctx.spec.abs x)
      rw [ctx.certificate.sourceLaws.abs_nonnegative x hle]
      exact hpos
    have hmnonneg := CompCert4Lean.Flocq.Core.Float_prop.ge_0_F2R ctx beta m e
      ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hposf |>.1)
    have hmnonnegR : ctx.spec.le ctx.spec.zero (ctx.spec.ofZ m) := by
      have hh := pg_izr_le ctx Z0 m hmnonneg
      rw [ctx.certificate.sourceLaws.ofZ_zero] at hh
      exact hh
    have hcm : choice false m CompCert4Lean.Flocq.Calc.Bracket.loc_Exact = m := by
      have hh := hchoice (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx m) m
        CompCert4Lean.Flocq.Calc.Bracket.loc_Exact (by
          apply CompCert4Lean.Flocq.Calc.Bracket.inbetween_Exact
          change ctx.spec.abs (ctx.spec.ofZ m) = ctx.spec.ofZ m
          exact ctx.certificate.sourceLaws.abs_nonnegative _ hmnonnegR)
      have hb' : CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx
          (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx m) ctx.spec.zero = false := by
        apply pg_rlt_bool_false ctx
        change ctx.spec.le ctx.spec.zero (ctx.spec.ofZ m)
        exact hmnonnegR
      rw [hb', hrnd.Zrnd_IZR] at hh
      have hh' : m = cond_Zopp false
          (choice false m CompCert4Lean.Flocq.Calc.Bracket.loc_Exact) := by
        simpa using hh
      rw [show cond_Zopp false
          (choice false m CompCert4Lean.Flocq.Calc.Bracket.loc_Exact) =
          choice false m CompCert4Lean.Flocq.Calc.Bracket.loc_Exact by
            unfold cond_Zopp CompCert4Lean.Flocq.Core.Zaux.cond_Zopp
            rfl] at hh'
      exact hh'.symm
    rw [hround]
    have hb := pg_rlt_bool_false ctx x hle
    rw [hb, hcm]
    simp [cond_Zopp]
    change x = CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
      (CompCert4Lean.Flocq.Calc.Bracket.Float beta m e)
    exact (ctx.certificate.sourceLaws.abs_nonnegative x hle).symm.trans habs

private theorem pg_round_sign_he (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx) (beta : radix) (fexp : Z → Z)
    (rnd : ExactR ctx → Z) (choice : Bool → Z → location → Z)
    (hrnd : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Valid_rnd ctx rnd)
    (hchoice : ∀ (x : ExactR ctx) (m : Z) (l : location),
      CompCert4Lean.Flocq.Calc.Bracket.inbetween_int ctx m
          (CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x) l →
        rnd x = cond_Zopp
          (CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x ctx.spec.zero)
          (choice
            (CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x ctx.spec.zero) m l))
    (x : ExactR ctx) (m e : Z) (l : location)
    (hbetween : CompCert4Lean.Flocq.Calc.Bracket.inbetween_float ctx beta m e
      (CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x) l)
    (he : e = CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x) :
    CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round ctx magnitude beta fexp rnd x =
      CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
        (CompCert4Lean.Flocq.Calc.Bracket.Float beta
          (cond_Zopp (CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x ctx.spec.zero)
            (choice (CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x ctx.spec.zero) m l)) e) := by
  unfold CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
  rw [he]
  apply congrArg (fun z : Z =>
    CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
      (CompCert4Lean.Flocq.Calc.Bracket.Float beta z
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x)))
  rw [← pg_rlt_bool_scaled ctx magnitude beta fexp x]
  apply hchoice
  exact pg_inbetween_int_scaled ctx magnitude beta fexp x m e l hbetween he

theorem round_sign_any_correct : ∀ (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx),
    round_sign_any_correctStatement ctx magnitude := by
  intro ctx magnitude beta fexp rnd hrnd choice hchoice x m e l hbetween hcase
  rcases hcase with he | ⟨hloc, hformat⟩
  · exact pg_round_sign_he ctx magnitude beta fexp rnd choice hrnd hchoice
      x m e l hbetween he
  · subst l
    cases hbetween with
    | inbetween_Exact habs =>
        exact pg_round_sign_exact ctx magnitude beta fexp rnd choice hrnd hchoice
          x m e habs hformat

end CompCert4Lean.Flocq.Calc.Round

namespace CompCert4Lean.Flocq.Calc.Round
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem cexp_inbetween_float : ∀ (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx),
    cexp_inbetween_floatStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x m e l hx hbetween he
  unfold CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp
  have hb := CompCert4Lean.Flocq.Calc.Bracket.inbetween_float_bounds ctx
    beta x m e l hbetween
  have hupperpos : ctx.spec.lt ctx.spec.zero
      (CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
        (CompCert4Lean.Flocq.Calc.Bracket.Float beta (Zadd m Zone) e)) := by
    exact ctx.certificate.orderedField.lt_trans _ _ _ hx hb.2
  have hmsucc : Zlt Z0 (Zadd m Zone) := by
    exact CompCert4Lean.Flocq.Core.Float_prop.gt_0_F2R ctx beta
      (Zadd m Zone) e hupperpos
  have hm : Zle Z0 m := by
    change (0 : Int) ≤ intOfZ m
    change (0 : Int) < intOfZ (Zadd m Zone) at hmsucc
    simp only [Zadd,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      intOfZ_zOfInt] at hmsucc
    have hone : intOfZ Zone = (1 : Int) := by rfl
    rw [hone] at hmsucc
    change (0 : Int) < intOfZ m + 1 at hmsucc
    omega
  rcases show Or (Zlt Z0 m) (m = Z0) from by
    change Or ((0 : Int) < intOfZ m) (m = Z0)
    by_cases hm0 : m = Z0
    · exact Or.inr hm0
    · left
      have hm' : (0 : Int) ≤ intOfZ m := by
        change (0 : Int) ≤ intOfZ m at hm
        exact hm
      have : ¬ (intOfZ m ≤ (0 : Int)) := by
        intro hle
        have : intOfZ m = 0 := by omega
        apply hm0
        apply intOfZ_injective
        change intOfZ m = 0
        exact this
      omega
    with hmpos | hmzero
  · have hmag := CompCert4Lean.Flocq.Core.Float_prop.mag_F2R_bounds_Zdigits
      ctx magnitude beta x m e hmpos hb
    change fexp ((CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_val) =
      fexp (Zadd (Zdigits beta m) e)
    have hmag' : (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_val =
        Zadd (Zdigits beta m) e := by exact hmag
    rw [hmag']
  
  · subst m
    have hxne : x ≠ ctx.spec.zero := by
      intro hx0
      rw [hx0] at hx
      exact (ctx.certificate.orderedField.lt_irrefl _ hx).elim
    have habsx : ctx.spec.abs x = x :=
      ctx.certificate.sourceLaws.abs_nonnegative x
        ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hx).1
    have hbpow : ctx.spec.lt (ctx.spec.abs x)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e) := by
      rw [habsx]
      have hbupper := hb.2
      change ctx.spec.lt x
          (CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
            (CompCert4Lean.Flocq.Calc.Bracket.Float beta
              (CompCert4Lean.Flocq.Calc.Bracket.Zadd Z0
                CompCert4Lean.Flocq.Calc.Bracket.Zone) e)) at hbupper
      have hzadd : CompCert4Lean.Flocq.Calc.Bracket.Zadd Z0
          CompCert4Lean.Flocq.Calc.Bracket.Zone =
          CompCert4Lean.Flocq.Calc.Bracket.Zone := by
        apply intOfZ_injective
        change intOfZ (Zadd Z0 Zone) = intOfZ Zone
        simp only [Zadd,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          intOfZ_zOfInt]
        have hz0 : intOfZ Z0 = 0 := by rfl
        rw [hz0]
        omega
      rw [hzadd] at hbupper
      change ctx.spec.lt x
        (CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
          (CompCert4Lean.Flocq.Core.Float_prop.Float beta Zone e)) at hbupper
      rw [CompCert4Lean.Flocq.Core.Float_prop.F2R_bpow] at hbupper
      exact hbupper
    have hmag : Zle
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.mag magnitude beta x) e := by
      exact CompCert4Lean.Flocq.Core.Raux.mag_le_bpow ctx magnitude beta x e hxne hbpow
    have hzdigits : Zdigits beta Z0 = Z0 := by rfl
    have hzadd : Zadd Z0 e = e := by
      apply intOfZ_injective
      change intOfZ (Zadd Z0 e) = intOfZ e
      simp only [Zadd,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        intOfZ_zOfInt]
      have hz0 : intOfZ Z0 = 0 := by rfl
      rw [hz0]
      omega
    rcases he with he1 | he2
    · have hle : Zle
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.mag magnitude beta x)
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x) := by
        change Zle
          (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_val
          (fexp (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_val)
        exact (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le_trans
          _ _ _ hmag he1)
      have heq := (hvalid.valid_exp
        ((CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_val)).2 hle
      have heq' := heq.2 e
      have hele : Zle e
          (fexp ((CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_val)) := by
        exact he1
      have hres := heq' he1
      have hmag_eq : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.mag magnitude beta x =
          (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_val := by rfl
      rw [hmag_eq]
      have hzright : Zadd (Zdigits beta Z0) e = e := by
        simpa [hzdigits] using hzadd
      rw [hzright]
      exact hres.symm
    · have he2' : Zle e (fexp e) := by
        simpa [hzdigits, hzadd] using he2
      have hle : Zle
          (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_val
          (fexp e) := by
        exact (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le_trans
          _ _ _ hmag he2')
      have heq := (hvalid.valid_exp e).2 he2' 
      have hres := heq.2 _ hle
      have hmag_eq : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.mag magnitude beta x =
          (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_val := by rfl
      rw [hmag_eq]
      have hzright : Zadd (Zdigits beta Z0) e = e := by
        simpa [hzdigits] using hzadd
      rw [hzright]
      exact hres
end CompCert4Lean.Flocq.Calc.Round

namespace CompCert4Lean.Flocq.Calc.Round

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem cexp_inbetween_float_loc_Exact : ∀ (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx),
    cexp_inbetween_float_loc_ExactStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x m e l hx hbetween
  classical
  by_cases hx0 : x = ctx.spec.zero
  · subst x
    cases hbetween with
    | inbetween_Exact h =>
        exact ⟨fun _ => Or.inr rfl, fun _ => Or.inr rfl⟩
    | inbetween_Inexact c hbounds hmiddle =>
        have hmneg := CompCert4Lean.Flocq.Core.Float_prop.lt_0_F2R
          ctx beta m e hbounds.1
        have hmpos := CompCert4Lean.Flocq.Core.Float_prop.gt_0_F2R
          ctx beta (Zadd m Zone) e hbounds.2
        change intOfZ m < (0 : Int) at hmneg
        change (0 : Int) < intOfZ (Zadd m Zone) at hmpos
        simp only [Zadd,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          intOfZ_zOfInt] at hmpos
        have hone : intOfZ Zone = (1 : Int) := rfl
        rw [hone] at hmpos
        omega
  · have hxpos : ctx.spec.lt ctx.spec.zero x := by
      apply (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
      exact ⟨hx, fun h => hx0 (ctx.certificate.orderedField.le_antisymm _ _ h hx)⟩
    constructor
    · intro h
      rcases h with he | hl
      · left
        have heq := cexp_inbetween_float ctx magnitude beta fexp hvalid
          x m e l hxpos hbetween (Or.inl he)
        rw [← heq]
        exact he
      · exact Or.inr hl
    · intro h
      rcases h with he | hl
      · left
        have heq := cexp_inbetween_float ctx magnitude beta fexp hvalid
          x m e l hxpos hbetween (Or.inr he)
        rw [heq]
        exact he
      · exact Or.inr hl

end CompCert4Lean.Flocq.Calc.Round

namespace CompCert4Lean.Flocq.Calc.Round

theorem inbetween_float_round_sign : ∀ (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx),
    inbetween_float_round_signStatement ctx magnitude := by
  intro ctx magnitude beta fexp rnd choice hchoice x m l e hbetween
  unfold CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
  apply congrArg (fun z : Z =>
    CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
      (CompCert4Lean.Flocq.Calc.Bracket.Float beta z
        (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x)))
  dsimp only [CompCert4Lean.Flocq.Calc.Bracket.R0,
    CompCert4Lean.Flocq.Core.Raux.Exact.R0,
    CompCert4Lean.Foundation.FlocqReal.ExactReal.R0]
  rw [← pg_rlt_bool_scaled ctx magnitude beta fexp x]
  apply hchoice
  exact pg_inbetween_int_scaled ctx magnitude beta fexp x m _ l hbetween rfl

end CompCert4Lean.Flocq.Calc.Round

namespace CompCert4Lean.Flocq.Calc.Round

open CompCert4Lean.Flocq.Core.Generic_fmt

private theorem pg_N_sign_nearest_opp (ctx : ExactRealContext)
    (choice : Z → Bool) (x : Exact.R ctx) :
    Exact.Znearest ctx choice (Exact.Ropp ctx x) =
      Zopp (Exact.Znearest ctx
        (fun t => Bool.not (choice (Zopp (Zadd t Zone)))) x) := by
  have hnearest_izr : ∀ (ch : Z → Bool) (n : Z),
      Exact.Znearest ctx ch (Exact.IZR ctx n) = n := by
    intro ch n
    rcases Znearest_DN_or_UP ctx ch (Exact.IZR ctx n) with hfloor | hceil
    ·
      calc
        Exact.Znearest ctx ch (Exact.IZR ctx n) =
            Exact.Zfloor ctx (Exact.IZR ctx n) := hfloor
        _ = n := CompCert4Lean.Flocq.Core.Raux.Zfloor_IZR ctx n
    ·
      calc
        Exact.Znearest ctx ch (Exact.IZR ctx n) =
            Exact.Zceil ctx (Exact.IZR ctx n) := hceil
        _ = n := CompCert4Lean.Flocq.Core.Raux.Zceil_IZR ctx n
  by_cases hx : Exact.IZR ctx (Exact.Zfloor ctx x) = x
  · have hnegizr : Exact.Ropp ctx (Exact.IZR ctx (Exact.Zfloor ctx x)) =
        Exact.IZR ctx (Zopp (Exact.Zfloor ctx x)) := by
      change ctx.spec.neg (ctx.spec.ofZ (Exact.Zfloor ctx x)) =
        ctx.spec.ofZ (Zopp (Exact.Zfloor ctx x))
      exact (ctx.certificate.sourceLaws.ofZ_neg _).symm
    calc
      Exact.Znearest ctx choice (Exact.Ropp ctx x) =
          Exact.Znearest ctx choice
            (Exact.IZR ctx (Zopp (Exact.Zfloor ctx x))) := by
        have harg : Exact.Ropp ctx x =
            Exact.IZR ctx (Zopp (Exact.Zfloor ctx x)) := by
          exact (congrArg (Exact.Ropp ctx) hx.symm).trans hnegizr
        rw [harg]
      _ = Zopp (Exact.Zfloor ctx x) := hnearest_izr choice _
      _ = Zopp (Exact.Znearest ctx
          (fun t => Bool.not (choice (Zopp (Zadd t Zone)))) x) := by
        have hnearx : Exact.Znearest ctx
            (fun t => Bool.not (choice (Zopp (Zadd t Zone)))) x =
            Exact.Zfloor ctx x := by
          calc
            Exact.Znearest ctx
                (fun t => Bool.not (choice (Zopp (Zadd t Zone)))) x =
                Exact.Znearest ctx
                  (fun t => Bool.not (choice (Zopp (Zadd t Zone))))
                  (Exact.IZR ctx (Exact.Zfloor ctx x)) := by
              exact congrArg (Exact.Znearest ctx
                (fun t => Bool.not (choice (Zopp (Zadd t Zone))))) hx.symm
            _ = Exact.Zfloor ctx x := hnearest_izr _ _
        exact congrArg Zopp hnearx.symm
  · have hceil : Exact.Zceil ctx x = Zadd (Exact.Zfloor ctx x) Zone :=
      CompCert4Lean.Flocq.Core.Raux.Zceil_floor_neq ctx x hx
    have hfloor_opp : Exact.Zfloor ctx (Exact.Ropp ctx x) =
        Zopp (Exact.Zceil ctx x) := by
      unfold Exact.Zceil
      exact (pg_zopp_zopp _).symm
    have hceil_opp : Exact.Zceil ctx (Exact.Ropp ctx x) =
        Zopp (Exact.Zfloor ctx x) := by
      change Zopp (Exact.Zfloor ctx (Exact.Ropp ctx (Exact.Ropp ctx x))) =
        Zopp (Exact.Zfloor ctx x)
      have hnn : Exact.Ropp ctx (Exact.Ropp ctx x) = x := pg_neg_neg ctx x
      rw [hnn]
    have hdiff : Exact.Rminus ctx (Exact.Ropp ctx x)
        (Exact.IZR ctx (Exact.Zfloor ctx (Exact.Ropp ctx x))) =
        Exact.Rminus ctx (Exact.IZR ctx (Exact.Zceil ctx x)) x := by
      rw [hfloor_opp]
      change ctx.spec.add (ctx.spec.neg x)
          (ctx.spec.neg (ctx.spec.ofZ (Zopp (Exact.Zceil ctx x)))) =
        ctx.spec.add (ctx.spec.ofZ (Exact.Zceil ctx x)) (ctx.spec.neg x)
      rw [ctx.certificate.sourceLaws.ofZ_neg]
      change ctx.spec.add (ctx.spec.neg x)
          (ctx.spec.neg (ctx.spec.neg (ctx.spec.ofZ (Exact.Zceil ctx x)))) =
        ctx.spec.add (ctx.spec.ofZ (Exact.Zceil ctx x)) (ctx.spec.neg x)
      have hnn : ctx.spec.neg (ctx.spec.neg (ctx.spec.ofZ (Exact.Zceil ctx x))) =
          ctx.spec.ofZ (Exact.Zceil ctx x) := pg_neg_neg ctx _
      rw [hnn]
      exact ctx.certificate.orderedField.add_comm _ _
    have hcmp_ceil :
        Exact.Rcompare ctx (Exact.Rminus ctx
          (Exact.IZR ctx (Exact.Zceil ctx x)) x)
          (Exact.Rdiv ctx (Exact.Rone ctx) (Exact.Rtwo ctx)) =
        Exact.Rcompare ctx (Exact.Rminus ctx
          (Exact.IZR ctx (Exact.Zceil ctx x)) x)
          (Exact.Rminus ctx x (Exact.IZR ctx (Exact.Zfloor ctx x))) := by
      simpa [CompCert4Lean.Flocq.Core.Raux.Exact.Rhalf] using
        (CompCert4Lean.Flocq.Core.Raux.Rcompare_ceil_floor_middle ctx x hx)
    have hcmp_floor :
        Exact.Rcompare ctx (Exact.Rminus ctx x
          (Exact.IZR ctx (Exact.Zfloor ctx x)))
          (Exact.Rdiv ctx (Exact.Rone ctx) (Exact.Rtwo ctx)) =
        Exact.Rcompare ctx (Exact.Rminus ctx x
          (Exact.IZR ctx (Exact.Zfloor ctx x)))
          (Exact.Rminus ctx (Exact.IZR ctx (Exact.Zceil ctx x)) x) := by
      simpa [CompCert4Lean.Flocq.Core.Raux.Exact.Rhalf] using
        (CompCert4Lean.Flocq.Core.Raux.Rcompare_floor_ceil_middle ctx x hx)
    have hcmp_sym := CompCert4Lean.Flocq.Core.Raux.Rcompare_sym ctx
      (Exact.Rminus ctx (Exact.IZR ctx (Exact.Zceil ctx x)) x)
      (Exact.Rminus ctx x (Exact.IZR ctx (Exact.Zfloor ctx x)))
    unfold Exact.Znearest
    rw [hdiff, hcmp_ceil, hcmp_floor]
    cases hcmp : Exact.Rcompare ctx
        (Exact.Rminus ctx (Exact.IZR ctx (Exact.Zceil ctx x)) x)
        (Exact.Rminus ctx x (Exact.IZR ctx (Exact.Zfloor ctx x))) with
    | Lt =>
        have hcmpR : CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx
            (Exact.Rminus ctx (Exact.IZR ctx (Exact.Zceil ctx x)) x)
            (Exact.Rminus ctx x (Exact.IZR ctx (Exact.Zfloor ctx x))) = .Lt := hcmp
        have hcmp' : CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx
            (Exact.Rminus ctx x (Exact.IZR ctx (Exact.Zfloor ctx x)))
            (Exact.Rminus ctx (Exact.IZR ctx (Exact.Zceil ctx x)) x) =
            .Gt := by
          have hh := hcmp_sym
          rw [hcmpR] at hh
          cases hrev : CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx
              (Exact.Rminus ctx x (Exact.IZR ctx (Exact.Zfloor ctx x)))
              (Exact.Rminus ctx (Exact.IZR ctx (Exact.Zceil ctx x)) x) with
          | Lt => simp [hrev,
              CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.CompOpp] at hh
          | Eq => simp [hrev,
              CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.CompOpp] at hh
          | Gt => simp [hrev]
        have hcmp'' : Exact.Rcompare ctx
            (Exact.Rminus ctx x (Exact.IZR ctx (Exact.Zfloor ctx x)))
            (Exact.Rminus ctx (Exact.IZR ctx (Exact.Zceil ctx x)) x) = .Gt := hcmp'
        rw [hcmp'']
        simp [hfloor_opp, hceil_opp, hceil, pg_zopp_zopp]
    | Eq =>
        have hcmpR : CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx
            (Exact.Rminus ctx (Exact.IZR ctx (Exact.Zceil ctx x)) x)
            (Exact.Rminus ctx x (Exact.IZR ctx (Exact.Zfloor ctx x))) = .Eq := hcmp
        have hcmp' : CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx
            (Exact.Rminus ctx x (Exact.IZR ctx (Exact.Zfloor ctx x)))
            (Exact.Rminus ctx (Exact.IZR ctx (Exact.Zceil ctx x)) x) =
            .Eq := by
          have hh := hcmp_sym
          rw [hcmpR] at hh
          cases hrev : CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx
              (Exact.Rminus ctx x (Exact.IZR ctx (Exact.Zfloor ctx x)))
              (Exact.Rminus ctx (Exact.IZR ctx (Exact.Zceil ctx x)) x) with
          | Lt => simp [hrev,
              CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.CompOpp] at hh
          | Eq => simp [hrev]
          | Gt => simp [hrev,
              CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.CompOpp] at hh
        have hcmp'' : Exact.Rcompare ctx
            (Exact.Rminus ctx x (Exact.IZR ctx (Exact.Zfloor ctx x)))
            (Exact.Rminus ctx (Exact.IZR ctx (Exact.Zceil ctx x)) x) = .Eq := hcmp'
        rw [hcmp'']
        by_cases hc : choice (Zopp (Zadd (Exact.Zfloor ctx x) Zone))
        · simp [hc, hfloor_opp, hceil_opp, hceil, pg_zopp_zopp]
        · simp [hc, hfloor_opp, hceil_opp, hceil, pg_zopp_zopp]
    | Gt =>
        have hcmpR : CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx
            (Exact.Rminus ctx (Exact.IZR ctx (Exact.Zceil ctx x)) x)
            (Exact.Rminus ctx x (Exact.IZR ctx (Exact.Zfloor ctx x))) = .Gt := hcmp
        have hcmp' : CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx
            (Exact.Rminus ctx x (Exact.IZR ctx (Exact.Zfloor ctx x)))
            (Exact.Rminus ctx (Exact.IZR ctx (Exact.Zceil ctx x)) x) =
            .Lt := by
          have hh := hcmp_sym
          rw [hcmpR] at hh
          cases hrev : CompCert4Lean.Flocq.Core.Raux.Exact.Rcompare ctx
              (Exact.Rminus ctx x (Exact.IZR ctx (Exact.Zfloor ctx x)))
              (Exact.Rminus ctx (Exact.IZR ctx (Exact.Zceil ctx x)) x) with
          | Lt => simp [hrev]
          | Eq => simp [hrev,
              CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.CompOpp] at hh
          | Gt => simp [hrev,
              CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes.CompOpp] at hh
        have hcmp'' : Exact.Rcompare ctx
            (Exact.Rminus ctx x (Exact.IZR ctx (Exact.Zfloor ctx x)))
            (Exact.Rminus ctx (Exact.IZR ctx (Exact.Zceil ctx x)) x) = .Lt := hcmp'
        rw [hcmp'']
        simp [hfloor_opp, hceil_opp, hceil, pg_zopp_zopp]


private theorem pg_N_sign_midpoint (ctx : ExactRealContext) (m : Z) :
    CompCert4Lean.Flocq.Calc.Bracket.Rdiv ctx
      (CompCert4Lean.Flocq.Calc.Bracket.Rplus ctx (ctx.spec.ofZ m)
        (ctx.spec.ofZ (Zadd m Zone)))
      (CompCert4Lean.Flocq.Calc.Bracket.Rtwo ctx) =
    ctx.spec.add (ctx.spec.ofZ m)
      (Exact.Rdiv ctx (Exact.Rone ctx) (Exact.Rtwo ctx)) := by
  have h := CompCert4Lean.Flocq.Calc.Bracket.middle_range ctx
    (ctx.spec.ofZ m) ctx.spec.one Zone
  change ctx.spec.div
      (ctx.spec.add (ctx.spec.ofZ m)
        (ctx.spec.add (ctx.spec.ofZ m)
          (ctx.spec.mul (ctx.spec.ofZ Zone) ctx.spec.one)))
      (ctx.spec.add ctx.spec.one ctx.spec.one) =
    ctx.spec.add (ctx.spec.ofZ m)
      (ctx.spec.mul (ctx.spec.div (ctx.spec.ofZ Zone)
        (ctx.spec.add ctx.spec.one ctx.spec.one)) ctx.spec.one) at h
  simp only [ctx.certificate.sourceLaws.ofZ_one,
    ctx.certificate.orderedField.mul_one] at h
  change ctx.spec.div
      (ctx.spec.add (ctx.spec.ofZ m) (ctx.spec.ofZ (Zadd m Zone)))
      (ctx.spec.add ctx.spec.one ctx.spec.one) =
    ctx.spec.add (ctx.spec.ofZ m)
      (ctx.spec.div ctx.spec.one (ctx.spec.add ctx.spec.one ctx.spec.one))
  rw [ctx.certificate.sourceLaws.ofZ_add, ctx.certificate.sourceLaws.ofZ_one]
  exact h

private theorem pg_N_sign_unsigned (ctx : ExactRealContext)
    (choice : Z → Bool) (x : ExactR ctx) (m : Z) (l : location)
    (hx : CompCert4Lean.Flocq.Calc.Bracket.inbetween_int ctx m x l) :
    Exact.Znearest ctx choice x = cond_incr (round_N (choice m) l) m := by
  cases hx with
  | inbetween_Exact h =>
      change x = ctx.spec.ofZ m at h
      rw [h]
      rcases Znearest_DN_or_UP ctx choice (ctx.spec.ofZ m) with hd | hu
      · simpa only [round_N, cond_incr, Bool.false_eq_true, if_false,
          pg_floor_izr] using hd
      · simpa only [round_N, cond_incr, Bool.false_eq_true, if_false,
          pg_ceil_izr] using hu
  | inbetween_Inexact c hbounds hmiddle =>
      have hfloor : Exact.Zfloor ctx x = m :=
        pg_floor_imp ctx m x
          ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hbounds.1).1
          hbounds.2
      have hneq : Exact.IZR ctx (Exact.Zfloor ctx x) ≠ x := by
        rw [hfloor]
        intro heq
        have hlt := hbounds.1
        change ctx.spec.lt (ctx.spec.ofZ m) x at hlt
        change ctx.spec.ofZ m = x at heq
        rw [heq] at hlt
        exact ctx.certificate.orderedField.lt_irrefl _ hlt
      have hceil : Exact.Zceil ctx x = Zadd m Zone := by
        calc
          Exact.Zceil ctx x = Zadd (Exact.Zfloor ctx x) Zone :=
            CompCert4Lean.Flocq.Core.Raux.Zceil_floor_neq ctx x hneq
          _ = Zadd m Zone := by rw [hfloor]
      have hmid := pg_N_sign_midpoint ctx m
      have hshift := CompCert4Lean.Flocq.Core.Raux.Rcompare_plus_r ctx
        (ctx.spec.neg (ctx.spec.ofZ m)) x
        (ctx.spec.add (ctx.spec.ofZ m)
          (Exact.Rdiv ctx (Exact.Rone ctx) (Exact.Rtwo ctx)))
      have hcancel : ctx.spec.add
          (ctx.spec.add (ctx.spec.ofZ m)
            (Exact.Rdiv ctx (Exact.Rone ctx) (Exact.Rtwo ctx)))
          (ctx.spec.neg (ctx.spec.ofZ m)) =
          Exact.Rdiv ctx (Exact.Rone ctx) (Exact.Rtwo ctx) := by
        rw [ctx.certificate.orderedField.add_comm (ctx.spec.ofZ m),
          ctx.certificate.orderedField.add_assoc,
          ctx.certificate.orderedField.add_comm (ctx.spec.ofZ m)
            (ctx.spec.neg (ctx.spec.ofZ m)),
          ctx.certificate.orderedField.neg_add_cancel,
          ctx.certificate.orderedField.add_zero]
      change Exact.Rcompare ctx
          (ctx.spec.add x (ctx.spec.neg (ctx.spec.ofZ m)))
          (ctx.spec.add (ctx.spec.add (ctx.spec.ofZ m)
            (Exact.Rdiv ctx (Exact.Rone ctx) (Exact.Rtwo ctx)))
            (ctx.spec.neg (ctx.spec.ofZ m))) =
        Exact.Rcompare ctx x
          (ctx.spec.add (ctx.spec.ofZ m)
            (Exact.Rdiv ctx (Exact.Rone ctx) (Exact.Rtwo ctx))) at hshift
      rw [hcancel] at hshift
      have hcmp : Exact.Rcompare ctx (Exact.Rminus ctx x (Exact.IZR ctx m))
          (Exact.Rdiv ctx (Exact.Rone ctx) (Exact.Rtwo ctx)) = c := by
        have hcmp0 : Exact.Rcompare ctx
            (ctx.spec.add x (ctx.spec.neg (ctx.spec.ofZ m)))
            (Exact.Rdiv ctx (Exact.Rone ctx) (Exact.Rtwo ctx)) = c := by
          rw [hshift, ← hmid]
          exact hmiddle
        exact hcmp0
      unfold Exact.Znearest
      rw [hfloor, hceil, hcmp]
      cases c <;> cases choice m <;> rfl

theorem inbetween_int_N_sign (ctx : ExactRealContext) :
    inbetween_int_N_signStatement ctx := by
  intro choice x m l hx
  change Exact.Znearest ctx choice x =
    cond_Zopp (CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x ctx.spec.zero)
      (cond_incr (round_N
        (if CompCert4Lean.Flocq.Core.Raux.Exact.Rlt_bool ctx x ctx.spec.zero then
          Bool.not (choice (Zopp (Zadd m Zone))) else choice m) l) m)
  change CompCert4Lean.Flocq.Calc.Bracket.inbetween_int ctx m
    (CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x) l at hx
  by_cases hneg : ctx.spec.lt x ctx.spec.zero
  · have hbool := pg_rlt_bool_true ctx x hneg
    rw [hbool]
    have habs : CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x = ctx.spec.neg x :=
      ctx.certificate.sourceLaws.abs_negative x hneg
    have hbase := pg_N_sign_unsigned ctx
      (fun z => Bool.not (choice (Zopp (Zadd z Zone))))
      (ctx.spec.neg x) m l (by simpa [habs] using hx)
    have hopp := pg_N_sign_nearest_opp ctx choice (ctx.spec.neg x)
    change Exact.Znearest ctx choice (ctx.spec.neg (ctx.spec.neg x)) = _ at hopp
    rw [pg_neg_neg ctx x] at hopp
    change Exact.Znearest ctx choice x =
      Zopp (cond_incr (round_N (Bool.not (choice (Zopp (Zadd m Zone)))) l) m)
    exact hopp.trans (congrArg Zopp hbase)
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
    have hbase := pg_N_sign_unsigned ctx choice x m l (by simpa [habs] using hx)
    exact hbase

end CompCert4Lean.Flocq.Calc.Round

namespace CompCert4Lean.Flocq.Calc.Round

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem inbetween_int_NA_sign (ctx : ExactRealContext) :
    inbetween_int_NA_signStatement ctx := by
  intro x m l hx
  change CompCert4Lean.Flocq.Calc.Bracket.inbetween_int ctx m
    (CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x) l at hx
  have hdu : ctx.spec.lt (ctx.spec.ofZ m)
      (ctx.spec.ofZ (Zadd m Zone)) := by
    rw [ctx.certificate.sourceLaws.ofZ_add,
      ctx.certificate.sourceLaws.ofZ_one]
    have h01 : ctx.spec.lt ctx.spec.zero ctx.spec.one := by
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
        exact (ctx.certificate.orderedField.lt_irrefl _
          (ctx.certificate.orderedField.lt_trans _ _ _ hzero_lt_neg hneg_lt_zero)).elim
    have hstep := ctx.certificate.orderedField.add_lt_compat_l
      (ctx.spec.ofZ m) ctx.spec.zero ctx.spec.one h01
    rw [ctx.certificate.orderedField.add_zero] at hstep
    exact hstep
  have hbounds := CompCert4Lean.Flocq.Calc.Bracket.inbetween_bounds ctx
    (ctx.spec.ofZ m) (ctx.spec.ofZ (Zadd m Zone)) hdu
    (CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x) l hx
  have hnonneg : ctx.spec.le ctx.spec.zero
      (CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx x) := by
    change ctx.spec.le ctx.spec.zero (ctx.spec.abs x)
    rcases ctx.certificate.total_order x ctx.spec.zero with h | h
    · rcases h with hlt | heq
      · rw [ctx.certificate.sourceLaws.abs_negative x hlt]
        have hadd := ctx.certificate.orderedField.add_lt_compat_l
          (ctx.spec.neg x) x ctx.spec.zero hlt
        rw [ctx.certificate.orderedField.neg_add_cancel,
          ctx.certificate.orderedField.add_zero] at hadd
        exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hadd |>.1
      · subst x
        rw [ctx.certificate.sourceLaws.abs_nonnegative _
          (ctx.certificate.orderedField.le_refl _)]
        exact ctx.certificate.orderedField.le_refl _
    · have hle := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1
      rw [ctx.certificate.sourceLaws.abs_nonnegative x hle]
      exact hle
  have hupperpos : ctx.spec.lt ctx.spec.zero
      (ctx.spec.ofZ (Zadd m Zone)) := by
    apply (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
    constructor
    · exact ctx.certificate.orderedField.le_trans _ _ _ hnonneg
        ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hbounds.2 |>.1)
    · intro hcontra
      exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hbounds.2).2
        (ctx.certificate.orderedField.le_trans _ _ _ hcontra hnonneg)
  have hupperpos' : ctx.spec.lt (ctx.spec.ofZ Z0)
      (ctx.spec.ofZ (Zadd m Zone)) := by
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hupperpos
  have hmsucc : Zlt Z0 (Zadd m Zone) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.lt_IZR ctx
      Z0 (Zadd m Zone) hupperpos'
  have hm : Zle Z0 m := by
    change (0 : Int) ≤ intOfZ m
    change (0 : Int) < intOfZ (Zadd m Zone) at hmsucc
    simp only [Zadd,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      intOfZ_zOfInt] at hmsucc
    have hone : intOfZ Zone = (1 : Int) := by rfl
    rw [hone] at hmsucc
    change (0 : Int) < intOfZ m + 1 at hmsucc
    omega
  have hchoice_m : Zle_bool Z0 m = true :=
    CompCert4Lean.Flocq.Core.Zaux.Zle_bool_true Z0 m hm
  have hneg : Zlt (Zopp (Zadd m Zone)) Z0 := by
    have hm' : (0 : Int) ≤ intOfZ m := by
      change (0 : Int) ≤ intOfZ m at hm
      exact hm
    change intOfZ (Zopp (Zadd m Zone)) < (0 : Int)
    simp only [Zopp,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
      intOfZ_zOfInt]
    simp only [Zadd,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      intOfZ_zOfInt]
    have hone : intOfZ Zone = (1 : Int) := by rfl
    rw [hone]
    omega
  have hchoice_neg : Zle_bool Z0 (Zopp (Zadd m Zone)) = false :=
    CompCert4Lean.Flocq.Core.Zaux.Zle_bool_false Z0
      (Zopp (Zadd m Zone)) hneg
  change CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Znearest ctx
    (fun z => Zle_bool Z0 z) x = _
  have hbase := inbetween_int_N_sign ctx
    (fun z => Zle_bool Z0 z) x m l hx
  rw [hchoice_m, hchoice_neg] at hbase
  simpa using hbase

end CompCert4Lean.Flocq.Calc.Round

namespace CompCert4Lean.Flocq.Calc.Round
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem truncate_correct_format : ∀ (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx),
    truncate_correct_formatStatement ctx magnitude := by
  intro ctx magnitude beta fexp m e hm
  dsimp
  intro hfmt he
  let x := CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
    (CompCert4Lean.Flocq.Calc.Bracket.Float beta m e)
  have hcexp : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x =
      fexp (Zadd (Zdigits beta m) e) := by
    unfold CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp
    apply congrArg fexp
    change CompCert4Lean.Flocq.Core.Float_prop.Exact.mag magnitude beta x = _
    dsimp [x]
    exact CompCert4Lean.Flocq.Core.Float_prop.mag_F2R_Zdigits ctx magnitude beta m e hm
  let E := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x
  let k := Zsub E e
  let p := Zpower (beta : Z) k
  let q := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ztrunc ctx
    (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa ctx magnitude beta fexp x)
  have heE : Zle e E := by
    change Zle e (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x)
    rw [hcexp]
    exact he
  have hknonneg : Zle Z0 k := by
    change (0 : Int) ≤ intOfZ (Zsub E e)
    simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    change intOfZ e ≤ intOfZ E at heE
    omega
  have hp : Zlt Z0 p := CompCert4Lean.Flocq.Core.Zaux.Zpower_gt_0 beta k hknonneg
  have hcanon : x = CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
      (CompCert4Lean.Flocq.Calc.Bracket.Float beta q E) := hfmt
  have hchange := CompCert4Lean.Flocq.Core.Float_prop.F2R_change_exp ctx beta e q E heE
  have hmm : m = Zmul q p :=
    CompCert4Lean.Flocq.Core.Float_prop.eq_F2R ctx beta e m (Zmul q p)
      (hcanon.trans hchange)
  have hquot : q = Zdiv m p := by
    apply ZArith.Zdiv.Zdiv_unique_full m p q Z0
    · exact Or.inl ⟨Int.le_refl 0, hp⟩
    · rw [hmm]
      apply intOfZ_injective
      simp only [Zmul, ZArith.BinInt.Z.mul, ZArith.BinInt.Z.add, intOfZ_zOfInt]
      change intOfZ q * intOfZ p = intOfZ p * intOfZ q + 0
      rw [Int.add_zero, Int.mul_comm]
  have headd : Zadd e k = E := by
    apply intOfZ_injective
    change intOfZ (Zadd e (Zsub E e)) = intOfZ E
    simp only [Zadd, Zsub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    omega
  unfold truncate
  dsimp
  rw [← hcexp]
  split
  · dsimp [truncate_aux]
    change x = CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
      (CompCert4Lean.Flocq.Calc.Bracket.Float beta (Zdiv m p) (Zadd e k)) ∧
      Zadd e k = E
    rw [headd, ← hquot]
    exact ⟨hcanon, rfl⟩
  · rename_i hk
    have hkle : Zle k Z0 := by
      change intOfZ k ≤ intOfZ Z0
      apply Int.le_of_not_gt
      intro hpos
      exact hk (CompCert4Lean.Flocq.Core.Zaux.Zlt_bool_true Z0 k hpos)
    have heq : e = E := by
      apply intOfZ_injective
      change intOfZ k ≤ (0 : Int) at hkle
      change (0 : Int) ≤ intOfZ k at hknonneg
      have hi := congrArg intOfZ headd
      simp only [Zadd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hi
      omega
    exact ⟨rfl, heq⟩

end CompCert4Lean.Flocq.Calc.Round

namespace CompCert4Lean.Flocq.Calc.Round
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem truncate_correct_partial' : ∀ (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx),
    truncate_correct_partial'Statement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x m e l hx hbetween he
  have hcexp : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x =
      fexp (Zadd (Zdigits beta m) e) := by
    exact cexp_inbetween_float ctx magnitude beta fexp hvalid x m e l hx hbetween (Or.inl he)
  unfold truncate
  dsimp
  rw [← hcexp]
  split
  · rename_i hk
    constructor
    · apply CompCert4Lean.Flocq.Calc.Bracket.inbetween_float_new_location ctx
      exact (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zlt_is_lt_bool Z0 _).mpr hk
      exact hbetween
    · dsimp [truncate_aux]
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp only [Zadd, Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      omega
  · rename_i hk
    have hnot : ¬ Zlt Z0 (Zsub (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x) e) := by
      intro hpos
      have htrue := CompCert4Lean.Flocq.Core.Zaux.Zlt_bool_true Z0
        (Zsub (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x) e) hpos
      exact hk htrue
    have hkle : Zle (Zsub (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x) e) Z0 := by
      change intOfZ (Zsub (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x) e) ≤ (0 : Int)
      apply Int.le_of_not_gt
      exact hnot
    constructor
    · exact hbetween
    · apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      change intOfZ e = intOfZ (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x)
      change intOfZ e ≤ intOfZ (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x) at he
      change intOfZ (Zsub (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x) e) ≤ intOfZ Z0 at hkle
      simp only [Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hkle
      have hz0 : intOfZ Z0 = (0 : Int) := by rfl
      rw [hz0] at hkle
      omega

end CompCert4Lean.Flocq.Calc.Round

namespace CompCert4Lean.Flocq.Calc.Round
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem truncate_correct_partial : ∀ (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx),
    truncate_correct_partialStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x m e l hx hbetween he
  have hcexp := cexp_inbetween_float ctx magnitude beta fexp hvalid x m e l hx hbetween
    (Or.inr he)
  have he' : Zle e (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp
      ctx magnitude beta fexp x) := by
    rw [hcexp]
    exact he
  exact truncate_correct_partial' ctx magnitude beta fexp hvalid x m e l hx hbetween he'

end CompCert4Lean.Flocq.Calc.Round

namespace CompCert4Lean.Flocq.Calc.Round
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem truncate_correct' : ∀ (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx),
    truncate_correct'Statement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x m e l hx hbetween hcase
  rcases ctx.certificate.total_order x ctx.spec.zero with hneg | hpos
  · rcases hneg with hlt | heq
    · have hnot : ¬ ctx.spec.le ctx.spec.zero x :=
        (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt |>.2
      exact (hnot hx).elim
    · subst x
      have hb := CompCert4Lean.Flocq.Calc.Bracket.inbetween_float_bounds
        ctx beta ctx.spec.zero m e l hbetween
      have hmneg : Zle m Z0 := by
        apply CompCert4Lean.Flocq.Core.Float_prop.le_0_F2R ctx beta m e
        exact hb.1
      have hmpos : Zlt Z0 (Zadd m Zone) := by
        apply CompCert4Lean.Flocq.Core.Float_prop.gt_0_F2R ctx beta (Zadd m Zone) e
        exact hb.2
      have hm : m = Z0 := by
        apply intOfZ_injective
        change intOfZ m = (0 : Int)
        change intOfZ m ≤ (0 : Int) at hmneg
        change (0 : Int) < intOfZ (Zadd m Zone) at hmpos
        simp only [Zadd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hmpos
        have hone : intOfZ Zone = (1 : Int) := by rfl
        rw [hone] at hmpos
        omega
      subst m
      cases hbetween with
      | inbetween_Exact hzero =>
          unfold truncate
          dsimp
          split
          · rename_i hk
            dsimp [truncate_aux]
            have hzdiv : Zdiv Z0 (Zpower (beta : Z)
                (Zsub (fexp (Zadd (Zdigits beta Z0) e)) e)) = Z0 :=
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Zdiv_0_l _
            have hzmod : Zmod Z0 (Zpower (beta : Z)
                (Zsub (fexp (Zadd (Zdigits beta Z0) e)) e)) = Z0 :=
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Zmod_0_l _
            rw [hzdiv, hzmod]
            have hloc : new_location (Zpower (beta : Z)
                (Zsub (fexp (Zadd (Zdigits beta Z0) e)) e)) Z0 loc_Exact = loc_Exact := by
              change CompCert4Lean.Flocq.Calc.Bracket.new_location
                (Zpower (beta : Z)
                  (Zsub (fexp (Zadd (Zdigits beta Z0) e)) e)) Z0 loc_Exact = loc_Exact
              unfold CompCert4Lean.Flocq.Calc.Bracket.new_location
              have hzeroeq : CompCert4Lean.Flocq.Calc.Bracket.Zeq_bool Z0 Z0 = true := by
                rfl
              split <;> simp [CompCert4Lean.Flocq.Calc.Bracket.new_location_even,
                CompCert4Lean.Flocq.Calc.Bracket.new_location_odd, hzeroeq]
            rw [hloc]
            constructor
            · apply CompCert4Lean.Flocq.Calc.Bracket.inbetween_Exact
              exact (CompCert4Lean.Flocq.Core.Float_prop.F2R_0 ctx beta _).symm
            · right
              refine ⟨rfl, ?_⟩
              exact CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_0 ctx magnitude beta fexp
          · rename_i hk
            constructor
            · apply CompCert4Lean.Flocq.Calc.Bracket.inbetween_Exact
              exact (CompCert4Lean.Flocq.Core.Float_prop.F2R_0 ctx beta e).symm
            · right
              refine ⟨rfl, ?_⟩
              exact CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_0 ctx magnitude beta fexp
      | inbetween_Inexact c hbounds hmiddle =>
          have hfzero : CompCert4Lean.Flocq.Calc.Bracket.F2R ctx
              (CompCert4Lean.Flocq.Calc.Bracket.Float beta Z0 e) = ctx.spec.zero :=
            CompCert4Lean.Flocq.Core.Float_prop.F2R_0 ctx beta e
          rw [hfzero] at hbounds
          have hcontra : ctx.spec.lt ctx.spec.zero ctx.spec.zero := hbounds.1
          exact (ctx.certificate.orderedField.lt_irrefl _ hcontra).elim
  · have hxpos : ctx.spec.lt ctx.spec.zero x := hpos
    rcases hcase with he | hl
    · by_cases hsmall : Zle e (fexp (Zadd (Zdigits beta m) e))
      · have hres := truncate_correct_partial ctx magnitude beta fexp hvalid
          x m e l hxpos hbetween hsmall
        dsimp at hres ⊢
        rcases hres with ⟨hres, he'⟩
        simpa only [] using (show _ from ⟨hres, Or.inl he'⟩)
      · have hres := truncate_correct_partial' ctx magnitude beta fexp hvalid
          x m e l hxpos hbetween he
        dsimp at hres ⊢
        rcases hres with ⟨hres, he'⟩
        simpa only [] using (show _ from ⟨hres, Or.inl he'⟩)
    · by_cases hsmall : Zle e (fexp (Zadd (Zdigits beta m) e))
      · have hres := truncate_correct_partial ctx magnitude beta fexp hvalid
          x m e l hxpos hbetween hsmall
        dsimp at hres ⊢
        rcases hres with ⟨hres, he'⟩
        simpa only [] using (show _ from ⟨hres, Or.inl he'⟩)
      · subst l
        cases hbetween with
        | inbetween_Exact hxeq =>
          unfold truncate
          dsimp
          split
          · rename_i hk
            exfalso
            apply hsmall
            have hk' : Zlt Z0 (Zsub (fexp (Zadd (Zdigits beta m) e)) e) :=
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zlt_is_lt_bool
                Z0 _).mpr hk
            change (0 : Int) < intOfZ (Zsub (fexp (Zadd (Zdigits beta m) e)) e) at hk'
            change intOfZ e ≤ intOfZ (fexp (Zadd (Zdigits beta m) e))
            simp only [Zsub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hk'
            omega
          · rename_i hk
            have hformat : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.generic_format
                ctx magnitude beta fexp x := by
              rw [hxeq]
              apply CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_F2R
              intro hm0
              unfold CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp
              change Zle (fexp ((CompCert4Lean.Flocq.Core.Raux.Exact.mag
                magnitude beta (CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
                  (CompCert4Lean.Flocq.Core.Float_prop.Float beta m e))).mag_val)) e
              have hmag := CompCert4Lean.Flocq.Core.Float_prop.mag_F2R_Zdigits
                ctx magnitude beta m e hm0
              have hmag' : (CompCert4Lean.Flocq.Core.Raux.Exact.mag
                  magnitude beta (CompCert4Lean.Flocq.Core.Float_prop.Exact.F2R ctx
                    (CompCert4Lean.Flocq.Core.Float_prop.Float beta m e))).mag_val =
                    Zadd (Zdigits beta m) e := by
                simpa only [CompCert4Lean.Flocq.Core.Float_prop.Exact.mag,
                  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.mag] using hmag
              rw [hmag']
              change intOfZ (fexp (Zadd (Zdigits beta m) e)) ≤ intOfZ e
              change ¬ intOfZ e ≤ intOfZ (fexp (Zadd (Zdigits beta m) e)) at hsmall
              omega
            exact ⟨CompCert4Lean.Flocq.Calc.Bracket.inbetween_Exact hxeq,
              Or.inr ⟨rfl, hformat⟩⟩

end CompCert4Lean.Flocq.Calc.Round

namespace CompCert4Lean.Flocq.Calc.Round

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem truncate_correct : ∀ (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx),
    truncate_correctStatement ctx magnitude := by
  intro ctx magnitude beta fexp hvalid x m e l hx hbetween hcase
  have hcase' := cexp_inbetween_float_loc_Exact ctx magnitude beta fexp
    hvalid x m e l hx hbetween
  exact truncate_correct' ctx magnitude beta fexp hvalid x m e l hx hbetween
    (hcase'.mpr hcase)

end CompCert4Lean.Flocq.Calc.Round
