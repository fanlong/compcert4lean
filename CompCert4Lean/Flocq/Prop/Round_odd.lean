import CompCert4Lean.Flocq.Calc.Operations
import CompCert4Lean.Flocq.Core.FLT
import CompCert4Lean.Flocq.Core.Generic_fmt
import CompCert4Lean.Flocq.Core.Round_NE

/-!
# Rounding to odd

This module carries the executable definitions selected from
`Flocq.Prop.Round_odd`.  Proof-bearing source declarations are represented by
exact source-shaped proposition descriptors for the later proof-migration
phase.
-/

namespace CompCert4Lean.Flocq.Prop.Round_odd

open CompCert4Lean.Flocq.Core

abbrev R := CompCert4Lean.Flocq.Core.Generic_fmt.R
abbrev Z := CompCert4Lean.Flocq.Core.Generic_fmt.Z
abbrev radix := CompCert4Lean.Flocq.Core.Generic_fmt.radix
abbrev float := CompCert4Lean.Flocq.Core.Generic_fmt.float
abbrev Float (beta : radix) (m e : Z) : float beta :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Float beta m e
abbrev Fnum {beta : radix} (f : float beta) : Z :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Fnum f
abbrev Fexp {beta : radix} (f : float beta) : Z :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Fexp f
abbrev F2R {beta : radix} (f : float beta) : R :=
  CompCert4Lean.Flocq.Core.Generic_fmt.F2R f

abbrev IZR := CompCert4Lean.Flocq.Core.Generic_fmt.IZR
abbrev R0 : R := CompCert4Lean.Flocq.Core.Generic_fmt.R0
abbrev Rtwo : R := CompCert4Lean.Flocq.Core.Generic_fmt.Rtwo
abbrev Ropp := CompCert4Lean.Flocq.Core.Generic_fmt.Ropp
abbrev Rplus := CompCert4Lean.Flocq.Core.Generic_fmt.Rplus
abbrev Rmult := CompCert4Lean.Flocq.Core.Generic_fmt.Rmult
abbrev Rdiv := CompCert4Lean.Flocq.Core.Generic_fmt.Rdiv
abbrev Rlt := CompCert4Lean.Flocq.Core.Generic_fmt.Rlt
abbrev Rle := CompCert4Lean.Flocq.Core.Generic_fmt.Rle

abbrev Zone : Z := CompCert4Lean.Flocq.Core.Generic_fmt.Zone
abbrev Ztwo : Z := CompCert4Lean.Flocq.Core.Zaux.Ztwo
abbrev Zadd := CompCert4Lean.Flocq.Core.Generic_fmt.Zadd
abbrev Zsub := CompCert4Lean.Flocq.Core.Generic_fmt.Zsub
abbrev Zabs := CompCert4Lean.Flocq.Core.Generic_fmt.Zabs
abbrev Zeven := CompCert4Lean.Flocq.Core.Zaux.Zeven
abbrev Zle := CompCert4Lean.Flocq.Core.Generic_fmt.Zle
abbrev Zlt := CompCert4Lean.Flocq.Core.Generic_fmt.Zlt
abbrev radix_val := CompCert4Lean.Flocq.Core.Zaux.radix_val

abbrev Zfloor := CompCert4Lean.Flocq.Core.Generic_fmt.Zfloor
abbrev Zceil := CompCert4Lean.Flocq.Core.Generic_fmt.Zceil
abbrev bpow := CompCert4Lean.Flocq.Core.Generic_fmt.bpow
abbrev mag := CompCert4Lean.Flocq.Core.Generic_fmt.mag
abbrev mag_val (beta : radix) (x : R) : Z :=
  CompCert4Lean.Flocq.Core.Raux.mag_val (mag beta x)

abbrev Valid_exp := CompCert4Lean.Flocq.Core.Generic_fmt.Valid_exp
abbrev Exists_NE := CompCert4Lean.Flocq.Core.Round_NE.Exists_NE
abbrev generic_format := CompCert4Lean.Flocq.Core.Generic_fmt.generic_format
abbrev canonical := CompCert4Lean.Flocq.Core.Generic_fmt.canonical
abbrev cexp := CompCert4Lean.Flocq.Core.Generic_fmt.cexp
abbrev round := CompCert4Lean.Flocq.Core.Generic_fmt.round
abbrev Znearest := CompCert4Lean.Flocq.Core.Generic_fmt.Znearest
abbrev Rnd_DN_pt := CompCert4Lean.Flocq.Core.Generic_fmt.Rnd_DN_pt
abbrev Rnd_UP_pt := CompCert4Lean.Flocq.Core.Generic_fmt.Rnd_UP_pt
abbrev round_pred_monotone := CompCert4Lean.Flocq.Core.Defs.round_pred_monotone
abbrev FLT_exp := CompCert4Lean.Flocq.Core.FLT.FLT_exp

def Zrnd_odd (x : R) : Z :=
  if x = IZR (Zfloor x) then
    Zfloor x
  else if Zeven (Zfloor x) then
    Zceil x
  else
    Zfloor x

def valid_rnd_odd : Prop :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Valid_rnd Zrnd_odd

def Rnd_odd_pt (beta : radix) (fexp : Z → Z) (x f : R) : Prop :=
  generic_format beta fexp f ∧
    (f = x ∨
      ((Rnd_DN_pt (generic_format beta fexp) x f ∨
          Rnd_UP_pt (generic_format beta fexp) x f) ∧
        ∃ g : float beta,
          f = F2R g ∧ canonical beta fexp g ∧ Zeven (Fnum g) = false))

def Rnd_odd (beta : radix) (fexp : Z → Z) (rnd : R → R) : Prop :=
  ∀ x : R, Rnd_odd_pt beta fexp x (rnd x)

abbrev format (beta : radix) (emin prec : Z) : R → Prop :=
  generic_format beta (FLT_exp emin prec)

abbrev round_flt (beta : radix) (emin prec : Z) (choice : Z → Bool) (x : R) : R :=
  round beta (FLT_exp emin prec) (Znearest choice) x

abbrev cexp_flt (beta : radix) (emin prec : Z) (x : R) : Z :=
  cexp beta (FLT_exp emin prec) x

abbrev fexpe (emin prec k : Z) : Z :=
  FLT_exp (Zsub emin k) (Zadd prec k) k

def Zrnd_odd_ZoddStatement : Prop :=
  ∀ x : R, x ≠ IZR (Zfloor x) → Zeven (Zrnd_odd x) = false

def Zfloor_plusStatement : Prop :=
  ∀ (n : Z) (y : R),
    Zfloor (Rplus (IZR n) y) = Zadd n (Zfloor y)

def Zceil_plusStatement : Prop :=
  ∀ (n : Z) (y : R),
    Zceil (Rplus (IZR n) y) = Zadd n (Zceil y)

def Zeven_absStatement : Prop :=
  ∀ z : Z, Zeven (Zabs z) = Zeven z

def Zrnd_odd_plusStatement : Prop :=
  ∀ (x y : R),
    x = IZR (Zfloor x) →
      Zeven (Zfloor x) = true →
        IZR (Zrnd_odd (Rplus x y)) = Rplus x (IZR (Zrnd_odd y))

def Rnd_odd_pt_opp_invStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (x f : R),
    Rnd_odd_pt beta fexp (Ropp x) (Ropp f) →
      Rnd_odd_pt beta fexp x f

def round_odd_oppStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (x : R),
    round beta fexp Zrnd_odd (Ropp x) =
      Ropp (round beta fexp Zrnd_odd x)

def round_odd_ptStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z),
    Valid_exp fexp → Exists_NE beta fexp →
      ∀ x : R, Rnd_odd_pt beta fexp x (round beta fexp Zrnd_odd x)

def Rnd_odd_pt_uniqueStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z),
    Valid_exp fexp → Exists_NE beta fexp →
      ∀ (x f1 f2 : R),
        Rnd_odd_pt beta fexp x f1 →
          Rnd_odd_pt beta fexp x f2 → f1 = f2

def Rnd_odd_pt_monotoneStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z),
    Valid_exp fexp → Exists_NE beta fexp →
      round_pred_monotone (Rnd_odd_pt beta fexp)

def generic_format_fexpe_fexpStatement : Prop :=
  ∀ (beta : radix) (fexp fexpe : Z → Z),
    (∀ e : Z, Zle (fexpe e) (Zsub (fexp e) Ztwo)) →
      ∀ x : R,
        generic_format beta fexp x → generic_format beta fexpe x

def exists_even_fexp_ltStatement : Prop :=
  ∀ (beta : radix), Zeven (radix_val beta) = true →
    ∀ (c : Z → Z) (x : R),
      (∃ f : float beta,
        F2R f = x ∧ Zlt (c (mag_val beta x)) (Fexp f)) →
        ∃ f : float beta,
          F2R f = x ∧ canonical beta c f ∧ Zeven (Fnum f) = true

def d_eqStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (x : R) (d : float beta),
      Rnd_DN_pt (generic_format beta fexp) x (F2R d) →
        F2R d = round beta fexp Zfloor x

def u_eqStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (x : R) (u : float beta),
      Rnd_UP_pt (generic_format beta fexp) x (F2R u) →
        F2R u = round beta fexp Zceil x

def d_ge_0Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (x : R) (d : float beta),
      Rnd_DN_pt (generic_format beta fexp) x (F2R d) →
        Rlt R0 x → Rle R0 (F2R d)

def mag_dStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (x : R) (d : float beta),
      Rnd_DN_pt (generic_format beta fexp) x (F2R d) →
        Rlt R0 (F2R d) →
          mag_val beta (F2R d) = mag_val beta x

def Fexp_dStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (x : R) (d : float beta),
      Rnd_DN_pt (generic_format beta fexp) x (F2R d) →
        canonical beta fexp d →
          Rlt R0 (F2R d) → Fexp d = fexp (mag_val beta x)

def format_bpow_xStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (x : R) (d : float beta),
      Rnd_DN_pt (generic_format beta fexp) x (F2R d) →
        canonical beta fexp d →
          Rlt R0 (F2R d) →
            generic_format beta fexp (bpow beta (mag_val beta x))

def format_bpow_dStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (d : float beta), canonical beta fexp d →
      Rlt R0 (F2R d) →
        generic_format beta fexp
          (bpow beta (mag_val beta (F2R d)))

def d_le_mStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (x : R) (d u : float beta),
    Rnd_DN_pt (generic_format beta fexp) x (F2R d) →
      Rnd_UP_pt (generic_format beta fexp) x (F2R u) →
        Rle (F2R d) (Rdiv (Rplus (F2R d) (F2R u)) Rtwo)

def m_le_uStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (x : R) (d u : float beta),
    Rnd_DN_pt (generic_format beta fexp) x (F2R d) →
      Rnd_UP_pt (generic_format beta fexp) x (F2R u) →
        Rle (Rdiv (Rplus (F2R d) (F2R u)) Rtwo) (F2R u)

def mag_mStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (x : R) (d u : float beta),
      Rnd_DN_pt (generic_format beta fexp) x (F2R d) →
        canonical beta fexp d →
          Rnd_UP_pt (generic_format beta fexp) x (F2R u) →
            Rlt R0 (F2R d) →
              mag_val beta (Rdiv (Rplus (F2R d) (F2R u)) Rtwo) =
                mag_val beta (F2R d)

def mag_m_0Statement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (x : R) (d u : float beta),
      Rnd_DN_pt (generic_format beta fexp) x (F2R d) →
        Rnd_UP_pt (generic_format beta fexp) x (F2R u) →
          Rlt R0 x → R0 = F2R d →
            mag_val beta (Rdiv (Rplus (F2R d) (F2R u)) Rtwo) =
              Zsub (mag_val beta (F2R u)) Zone

def u'_eqStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (x : R) (d u : float beta),
      Rnd_DN_pt (generic_format beta fexp) x (F2R d) →
        canonical beta fexp d →
          Rnd_UP_pt (generic_format beta fexp) x (F2R u) →
            Rlt R0 (F2R d) →
              ∃ f : float beta, F2R f = F2R u ∧ Fexp f = Fexp d

def m_eqStatement : Prop :=
  ∀ (beta : radix), Zeven (radix_val beta) = true →
    ∀ (fexp : Z → Z), Valid_exp fexp →
      ∀ (x : R) (d u : float beta),
        Rnd_DN_pt (generic_format beta fexp) x (F2R d) →
          canonical beta fexp d →
            Rnd_UP_pt (generic_format beta fexp) x (F2R u) →
              Rlt R0 (F2R d) →
                ∃ f : float beta,
                  F2R f = Rdiv (Rplus (F2R d) (F2R u)) Rtwo ∧
                    Fexp f = Zsub (fexp (mag_val beta x)) Zone

def m_eq_0Statement : Prop :=
  ∀ (beta : radix), Zeven (radix_val beta) = true →
    ∀ (fexp : Z → Z) (x : R) (d u : float beta),
      Rnd_UP_pt (generic_format beta fexp) x (F2R u) →
        canonical beta fexp u → R0 = F2R d →
          ∃ f : float beta,
            F2R f = Rdiv (Rplus (F2R d) (F2R u)) Rtwo ∧
              Fexp f = Zsub (fexp (mag_val beta (F2R u))) Zone

def fexp_m_eq_0Statement : Prop :=
  ∀ (beta : radix), Zeven (radix_val beta) = true →
    ∀ (fexp : Z → Z), Valid_exp fexp → Exists_NE beta fexp →
      ∀ (x : R) (d u : float beta),
        Rnd_DN_pt (generic_format beta fexp) x (F2R d) →
          Rnd_UP_pt (generic_format beta fexp) x (F2R u) →
            Rlt R0 x → R0 = F2R d →
              Zlt (fexp (Zsub (mag_val beta (F2R u)) Zone))
                (Zadd (fexp (mag_val beta (F2R u))) Zone)

def FmStatement : Prop :=
  ∀ (beta : radix), Zeven (radix_val beta) = true →
    ∀ (fexp fexpe : Z → Z),
      Valid_exp fexp → Exists_NE beta fexp →
        (∀ e : Z, Zle (fexpe e) (Zsub (fexp e) Ztwo)) →
          ∀ (x : R) (d u : float beta),
            Rnd_DN_pt (generic_format beta fexp) x (F2R d) →
              canonical beta fexp d →
                Rnd_UP_pt (generic_format beta fexp) x (F2R u) →
                  canonical beta fexp u → Rlt R0 x →
                    generic_format beta fexpe
                      (Rdiv (Rplus (F2R d) (F2R u)) Rtwo)

def ZmStatement : Prop :=
  ∀ (beta : radix), Zeven (radix_val beta) = true →
    ∀ (fexp fexpe : Z → Z),
      Valid_exp fexp → Exists_NE beta fexp →
        (∀ e : Z, Zle (fexpe e) (Zsub (fexp e) Ztwo)) →
          ∀ (x : R) (d u : float beta),
            Rnd_DN_pt (generic_format beta fexp) x (F2R d) →
              canonical beta fexp d →
                Rnd_UP_pt (generic_format beta fexp) x (F2R u) →
                  canonical beta fexp u → Rlt R0 x →
                    ∃ g : float beta,
                      F2R g = Rdiv (Rplus (F2R d) (F2R u)) Rtwo ∧
                        canonical beta fexpe g ∧ Zeven (Fnum g) = true

def DN_odd_d_auxStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (x : R) (d u : float beta),
      Rnd_DN_pt (generic_format beta fexp) x (F2R d) →
        Rnd_UP_pt (generic_format beta fexp) x (F2R u) →
          ∀ z : R,
            Rle (F2R d) z ∧ Rlt z (F2R u) →
              Rnd_DN_pt (generic_format beta fexp) z (F2R d)

def UP_odd_d_auxStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z), Valid_exp fexp →
    ∀ (x : R) (d u : float beta),
      Rnd_DN_pt (generic_format beta fexp) x (F2R d) →
        Rnd_UP_pt (generic_format beta fexp) x (F2R u) →
          ∀ z : R,
            Rlt (F2R d) z ∧ Rle z (F2R u) →
              Rnd_UP_pt (generic_format beta fexp) z (F2R u)

def round_N_odd_posStatement : Prop :=
  ∀ (beta : radix), Zeven (radix_val beta) = true →
    ∀ (fexp fexpe : Z → Z),
      Valid_exp fexp → Exists_NE beta fexp →
        Valid_exp fexpe → Exists_NE beta fexpe →
          (∀ e : Z, Zle (fexpe e) (Zsub (fexp e) Ztwo)) →
            ∀ (choice : Z → Bool) (x : R) (d u : float beta),
              Rnd_DN_pt (generic_format beta fexp) x (F2R d) →
                canonical beta fexp d →
                  Rnd_UP_pt (generic_format beta fexp) x (F2R u) →
                    canonical beta fexp u → Rlt R0 x →
                      round beta fexp (Znearest choice)
                          (round beta fexpe Zrnd_odd x) =
                        round beta fexp (Znearest choice) x

def round_N_oddStatement : Prop :=
  ∀ (beta : radix), Zeven (radix_val beta) = true →
    ∀ (fexp fexpe : Z → Z) (choice : Z → Bool),
      Valid_exp fexp → Exists_NE beta fexp →
        Valid_exp fexpe → Exists_NE beta fexpe →
          (∀ e : Z, Zle (fexpe e) (Zsub (fexp e) Ztwo)) →
            ∀ x : R,
              round beta fexp (Znearest choice)
                  (round beta fexpe Zrnd_odd x) =
                round beta fexp (Znearest choice) x

def Zrnd_odd_plus'Statement : Prop :=
  ∀ (beta : radix), Zeven (radix_val beta) = true →
    ∀ (x y : R),
      (∃ (n e : Z),
        x = Rmult (IZR n) (bpow beta e) ∧ Zle Zone e) →
          IZR (Zrnd_odd (Rplus x y)) = Rplus x (IZR (Zrnd_odd y))

def mag_round_oddStatement : Prop :=
  ∀ (beta : radix), Zeven (radix_val beta) = true →
    ∀ (emin prec : Z), Zlt Zone prec →
      ∀ x : R,
        Zlt emin (mag_val beta x) →
          mag_val beta (round beta (FLT_exp emin prec) Zrnd_odd x) =
            mag_val beta x

def fexp_round_oddStatement : Prop :=
  ∀ (beta : radix), Zeven (radix_val beta) = true →
    ∀ (emin prec : Z), Zlt Zone prec →
      ∀ x : R,
        cexp beta (FLT_exp emin prec)
            (round beta (FLT_exp emin prec) Zrnd_odd x) =
          cexp beta (FLT_exp emin prec) x

end CompCert4Lean.Flocq.Prop.Round_odd
