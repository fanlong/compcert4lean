import CompCert4Lean.Flocq.Calc.Operations
import CompCert4Lean.Flocq.Core.FLT
import CompCert4Lean.Flocq.Core.Generic_fmt
import CompCert4Lean.Flocq.Core.Round_NE

/-!
# Rounding to odd

The executable definitions in this module retain the checked runtime carrier
only at the RPR-007 compatibility boundary.  All source propositions and
statement descriptors below use the canonical explicit exact-real context.
Proof-bearing source declarations remain descriptors for the later proof phase.
-/

namespace CompCert4Lean.Flocq.Prop.Round_odd

open CompCert4Lean.Flocq.Core

abbrev Z := CompCert4Lean.Flocq.Core.Generic_fmt.Z
abbrev radix := CompCert4Lean.Flocq.Core.Generic_fmt.radix
abbrev float := CompCert4Lean.Flocq.Core.Generic_fmt.float
abbrev Float (beta : radix) (m e : Z) : float beta :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Float beta m e
abbrev Fnum {beta : radix} (f : float beta) : Z :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Fnum f
abbrev Fexp {beta : radix} (f : float beta) : Z :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Fexp f

abbrev Zone : Z := CompCert4Lean.Flocq.Core.Generic_fmt.Zone
abbrev Ztwo : Z := CompCert4Lean.Flocq.Core.Zaux.Ztwo
abbrev Zadd := CompCert4Lean.Flocq.Core.Generic_fmt.Zadd
abbrev Zsub := CompCert4Lean.Flocq.Core.Generic_fmt.Zsub
abbrev Zabs := CompCert4Lean.Flocq.Core.Generic_fmt.Zabs
abbrev Zeven := CompCert4Lean.Flocq.Core.Zaux.Zeven
abbrev Zle := CompCert4Lean.Flocq.Core.Generic_fmt.Zle
abbrev Zlt := CompCert4Lean.Flocq.Core.Generic_fmt.Zlt
abbrev radix_val := CompCert4Lean.Flocq.Core.Zaux.radix_val

abbrev Valid_exp := CompCert4Lean.Flocq.Core.Generic_fmt.Valid_exp
abbrev Exists_NE := CompCert4Lean.Flocq.Core.Round_NE.Exists_NE
abbrev FLT_exp := CompCert4Lean.Flocq.Core.FLT.FLT_exp

/- The source notation is function-valued: fexpe k is the function
   FLT_exp (emin-k) (prec+k), not its value at k. -/
abbrev fexpe (emin prec k : Z) : Z → Z :=
  FLT_exp (Zsub emin k) (Zadd prec k)

abbrev ExactRealContext :=
  CompCert4Lean.Flocq.Core.Generic_fmt.ExactRealContext

abbrev ExactR (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R ctx
abbrev R (ctx : ExactRealContext) := ExactR ctx
abbrev ExactMagnitude (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Magnitude ctx
abbrev F2R (ctx : ExactRealContext) {beta : radix} (f : float beta) : ExactR ctx :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx f
abbrev IZR (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.IZR ctx
abbrev R0 (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R0 ctx
abbrev Rtwo (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rtwo ctx
abbrev Ropp (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ropp ctx
abbrev Rplus (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rplus ctx
abbrev Rmult (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rmult ctx
abbrev Rdiv (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rdiv ctx
abbrev Rlt (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rlt ctx
abbrev Rle (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Rle ctx
abbrev Zfloor (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zfloor ctx
abbrev Zceil (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Zceil ctx
abbrev bpow (ctx : ExactRealContext) (beta : radix) (e : Z) : ExactR ctx :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.bpow ctx beta e
abbrev mag (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (x : ExactR ctx) : Z :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.mag magnitude beta x
abbrev mag_val (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (x : ExactR ctx) : Z :=
  mag ctx magnitude beta x
abbrev canonical (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (fexp : Z → Z) (f : float beta) : Prop :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.canonical ctx magnitude beta fexp f
abbrev cexp (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (fexp : Z → Z) (x : ExactR ctx) : Z :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp ctx magnitude beta fexp x
abbrev generic_format (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (fexp : Z → Z) (x : ExactR ctx) : Prop :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.generic_format ctx magnitude beta fexp x
abbrev round (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (fexp : Z → Z) (rnd : ExactR ctx → Z) (x : ExactR ctx) : ExactR ctx :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round ctx magnitude beta fexp rnd x
noncomputable abbrev Znearest (ctx : ExactRealContext) (choice : Z → Bool) : ExactR ctx → Z :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Znearest ctx choice
abbrev Valid_rnd (ctx : ExactRealContext) (rnd : ExactR ctx → Z) : Prop :=
  CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Valid_rnd ctx rnd
abbrev Rnd_DN_pt (ctx : ExactRealContext) (F : ExactR ctx → Prop)
    (x f : ExactR ctx) : Prop :=
  CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_DN_pt ctx F x f
abbrev Rnd_UP_pt (ctx : ExactRealContext) (F : ExactR ctx → Prop)
    (x f : ExactR ctx) : Prop :=
  CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_UP_pt ctx F x f
abbrev round_pred_monotone (ctx : ExactRealContext)
    (P : ExactR ctx → ExactR ctx → Prop) : Prop :=
  CompCert4Lean.Flocq.Core.Defs.Exact.round_pred_monotone ctx P

def Zrnd_odd (ctx : ExactRealContext) (x : ExactR ctx) : Z :=
  match CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Req_EM_T
      ctx x (IZR ctx (Zfloor ctx x)) with
  | .left _ => Zfloor ctx x
  | .right _ =>
      if Zeven (Zfloor ctx x) then
        Zceil ctx x
      else
        Zfloor ctx x

class Valid_rnd_odd_Certificate (ctx : ExactRealContext) : Prop where
  odd : Valid_rnd ctx (Zrnd_odd ctx)

/- The proof phase constructs the mandatory exact certificate. -/
instance valid_rnd_odd (ctx : ExactRealContext)
    [certificate : Valid_rnd_odd_Certificate ctx] :
    Valid_rnd ctx (Zrnd_odd ctx) :=
  certificate.odd

def Rnd_odd_pt (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (fexp : Z → Z) (x f : R ctx) : Prop :=
  generic_format ctx magnitude beta fexp f ∧
    (f = x ∨
      ((Rnd_DN_pt ctx (generic_format ctx magnitude beta fexp) x f ∨
          Rnd_UP_pt ctx (generic_format ctx magnitude beta fexp) x f) ∧
        ∃ g : float beta,
          f = F2R ctx g ∧
            canonical ctx magnitude beta fexp g ∧ Zeven (Fnum g) = false))

def Rnd_odd (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (fexp : Z → Z) (rnd : R ctx → R ctx) : Prop :=
  ∀ x : R ctx, Rnd_odd_pt ctx magnitude beta fexp x (rnd x)

abbrev format (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (emin prec : Z) : R ctx → Prop :=
  generic_format ctx magnitude beta (FLT_exp emin prec)

noncomputable abbrev round_flt (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (emin prec : Z) (choice : Z → Bool) (x : R ctx) : R ctx :=
  round ctx magnitude beta (FLT_exp emin prec) (Znearest ctx choice) x

abbrev cexp_flt (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (emin prec : Z) (x : R ctx) : Z :=
  cexp ctx magnitude beta (FLT_exp emin prec) x

namespace Runtime

abbrev R := CompCert4Lean.Flocq.Core.Generic_fmt.R
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
abbrev Zfloor := CompCert4Lean.Flocq.Core.Generic_fmt.Zfloor
abbrev Zceil := CompCert4Lean.Flocq.Core.Generic_fmt.Zceil
abbrev bpow := CompCert4Lean.Flocq.Core.Generic_fmt.bpow
abbrev mag := CompCert4Lean.Flocq.Core.Generic_fmt.mag
abbrev mag_val (beta : radix) (x : R) : Z :=
  CompCert4Lean.Flocq.Core.Raux.mag_val (mag beta x)
abbrev generic_format := CompCert4Lean.Flocq.Core.Generic_fmt.generic_format
abbrev canonical := CompCert4Lean.Flocq.Core.Generic_fmt.canonical
abbrev cexp := CompCert4Lean.Flocq.Core.Generic_fmt.cexp
abbrev round := CompCert4Lean.Flocq.Core.Generic_fmt.round
abbrev Znearest := CompCert4Lean.Flocq.Core.Generic_fmt.Znearest
abbrev Valid_rnd := CompCert4Lean.Flocq.Core.Generic_fmt.Valid_rnd
abbrev Rnd_DN_pt := CompCert4Lean.Flocq.Core.Generic_fmt.Rnd_DN_pt
abbrev Rnd_UP_pt := CompCert4Lean.Flocq.Core.Generic_fmt.Rnd_UP_pt

def Zrnd_odd (x : R) : Z :=
  if x = IZR (Zfloor x) then
    Zfloor x
  else if Zeven (Zfloor x) then
    Zceil x
  else
    Zfloor x

class Valid_rnd_odd_Certificate : Prop where
  odd : Valid_rnd Zrnd_odd

instance valid_rnd_odd [certificate : Valid_rnd_odd_Certificate] :
    Valid_rnd Zrnd_odd :=
  certificate.odd

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

end Runtime

def valid_rnd_oddStatement (ctx : ExactRealContext) : Prop :=
  Valid_rnd ctx (Zrnd_odd ctx)

section ExactSpecification

variable (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)

local notation "R" => R ctx
local notation "F2R" => F2R ctx
local notation "IZR" => IZR ctx
local notation "R0" => R0 ctx
local notation "Rtwo" => Rtwo ctx
local notation "Ropp" => Ropp ctx
local notation "Rplus" => Rplus ctx
local notation "Rmult" => Rmult ctx
local notation "Rdiv" => Rdiv ctx
local notation "Rlt" => Rlt ctx
local notation "Rle" => Rle ctx
local notation "Zfloor" => Zfloor ctx
local notation "Zceil" => Zceil ctx
local notation "bpow" => bpow ctx
local notation "mag_val" => mag_val ctx magnitude
local notation "mag" => mag ctx magnitude
local notation "generic_format" => generic_format ctx magnitude
local notation "canonical" => canonical ctx magnitude
local notation "cexp" => cexp ctx magnitude
local notation "round" => round ctx magnitude
local notation "Znearest" => Znearest ctx
local notation "Rnd_DN_pt" => Rnd_DN_pt ctx
local notation "Rnd_UP_pt" => Rnd_UP_pt ctx
local notation "Rnd_odd_pt" => Rnd_odd_pt ctx magnitude
local notation "round_pred_monotone" => round_pred_monotone ctx

def Zrnd_odd_ZoddStatement : Prop :=
  ∀ x : R, x ≠ IZR (Zfloor x) → Zeven (Zrnd_odd ctx x) = false

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
        IZR (Zrnd_odd ctx (Rplus x y)) =
          Rplus x (IZR (Zrnd_odd ctx y))

def Rnd_odd_pt_opp_invStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (x f : R),
    Rnd_odd_pt beta fexp (Ropp x) (Ropp f) →
      Rnd_odd_pt beta fexp x f

def round_odd_oppStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z) (x : R),
    round beta fexp (Zrnd_odd ctx) (Ropp x) =
      Ropp (round beta fexp (Zrnd_odd ctx) x)

def round_odd_ptStatement : Prop :=
  ∀ (beta : radix) (fexp : Z → Z),
    Valid_exp fexp → Exists_NE beta fexp →
      ∀ x : R,
        Rnd_odd_pt beta fexp x
          (round beta fexp (Zrnd_odd ctx) x)

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
                          (round beta fexpe (Zrnd_odd ctx) x) =
                        round beta fexp (Znearest choice) x

def round_N_oddStatement : Prop :=
  ∀ (beta : radix), Zeven (radix_val beta) = true →
    ∀ (fexp fexpe : Z → Z) (choice : Z → Bool),
      Valid_exp fexp → Exists_NE beta fexp →
        Valid_exp fexpe → Exists_NE beta fexpe →
          (∀ e : Z, Zle (fexpe e) (Zsub (fexp e) Ztwo)) →
            ∀ x : R,
              round beta fexp (Znearest choice)
                  (round beta fexpe (Zrnd_odd ctx) x) =
                round beta fexp (Znearest choice) x

def Zrnd_odd_plus'Statement : Prop :=
  ∀ (beta : radix), Zeven (radix_val beta) = true →
    ∀ (x y : R),
      (∃ (n e : Z),
        x = Rmult (IZR n) (bpow beta e) ∧ Zle Zone e) →
          IZR (Zrnd_odd ctx (Rplus x y)) =
            Rplus x (IZR (Zrnd_odd ctx y))

def mag_round_oddStatement : Prop :=
  ∀ (beta : radix), Zeven (radix_val beta) = true →
    ∀ (emin prec : Z), Zlt Zone prec →
      ∀ x : R,
        Zlt emin (mag_val beta x) →
          mag_val beta
              (round beta (FLT_exp emin prec) (Zrnd_odd ctx) x) =
            mag_val beta x

def fexp_round_oddStatement : Prop :=
  ∀ (beta : radix), Zeven (radix_val beta) = true →
    ∀ (emin prec : Z), Zlt Zone prec →
      ∀ x : R,
        cexp beta (FLT_exp emin prec)
            (round beta (FLT_exp emin prec) (Zrnd_odd ctx) x) =
          cexp beta (FLT_exp emin prec) x

end ExactSpecification

end CompCert4Lean.Flocq.Prop.Round_odd
