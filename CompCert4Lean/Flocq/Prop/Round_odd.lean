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

namespace CompCert4Lean.Flocq.Prop.Round_odd

open CompCert4Lean.Flocq.Core

private theorem round_odd_neg_add_distr (ctx : ExactRealContext) (a b : R ctx) :
    Ropp ctx (Rplus ctx a b) = Rplus ctx (Ropp ctx a) (Ropp ctx b) := by
  change ctx.spec.neg (ctx.spec.add a b) = ctx.spec.add (ctx.spec.neg a) (ctx.spec.neg b)
  have hzero : ctx.spec.add (ctx.spec.add (ctx.spec.neg a) (ctx.spec.neg b))
      (ctx.spec.add a b) = ctx.spec.zero := by
    calc
      ctx.spec.add (ctx.spec.add (ctx.spec.neg a) (ctx.spec.neg b))
          (ctx.spec.add a b) =
          ctx.spec.add (ctx.spec.add (ctx.spec.neg a) a) (ctx.spec.add (ctx.spec.neg b) b) := by
            calc
              ctx.spec.add (ctx.spec.add (ctx.spec.neg a) (ctx.spec.neg b))
                  (ctx.spec.add a b) =
                  ctx.spec.add (ctx.spec.neg a)
                    (ctx.spec.add (ctx.spec.neg b) (ctx.spec.add a b)) := by
                      exact ctx.certificate.orderedField.add_assoc _ _ _
              _ = ctx.spec.add (ctx.spec.neg a)
                    (ctx.spec.add (ctx.spec.add (ctx.spec.neg b) a) b) := by
                      exact congrArg (ctx.spec.add (ctx.spec.neg a))
                        (ctx.certificate.orderedField.add_assoc _ _ _).symm
              _ = ctx.spec.add (ctx.spec.neg a)
                    (ctx.spec.add (ctx.spec.add a (ctx.spec.neg b)) b) := by
                      rw [ctx.certificate.orderedField.add_comm (ctx.spec.neg b) a]
              _ = ctx.spec.add (ctx.spec.neg a)
                    (ctx.spec.add a (ctx.spec.add (ctx.spec.neg b) b)) := by
                      rw [ctx.certificate.orderedField.add_assoc]
              _ = ctx.spec.add (ctx.spec.add (ctx.spec.neg a) a)
                    (ctx.spec.add (ctx.spec.neg b) b) := by
                      rw [← ctx.certificate.orderedField.add_assoc]
      _ = ctx.spec.add ctx.spec.zero ctx.spec.zero := by
        rw [ctx.certificate.orderedField.neg_add_cancel,
          ctx.certificate.orderedField.neg_add_cancel]
      _ = ctx.spec.zero := ctx.certificate.orderedField.zero_add _
  have h : ctx.spec.add (ctx.spec.neg a) (ctx.spec.neg b) =
      ctx.spec.neg (ctx.spec.add a b) := by
    calc
      ctx.spec.add (ctx.spec.neg a) (ctx.spec.neg b) =
          ctx.spec.add (ctx.spec.add (ctx.spec.neg a) (ctx.spec.neg b)) ctx.spec.zero :=
            (ctx.certificate.orderedField.add_zero _).symm
      _ = ctx.spec.add (ctx.spec.add (ctx.spec.neg a) (ctx.spec.neg b))
          (ctx.spec.add (ctx.spec.neg (ctx.spec.add a b)) (ctx.spec.add a b)) := by
            rw [ctx.certificate.orderedField.neg_add_cancel]
      _ = ctx.spec.add
          (ctx.spec.add (ctx.spec.add (ctx.spec.neg a) (ctx.spec.neg b))
            (ctx.spec.neg (ctx.spec.add a b))) (ctx.spec.add a b) := by
            rw [← ctx.certificate.orderedField.add_assoc]
      _ = ctx.spec.add (ctx.spec.add (ctx.spec.neg (ctx.spec.add a b))
          (ctx.spec.add (ctx.spec.neg a) (ctx.spec.neg b))) (ctx.spec.add a b) := by
            rw [ctx.certificate.orderedField.add_comm
              (ctx.spec.add (ctx.spec.neg a) (ctx.spec.neg b))
              (ctx.spec.neg (ctx.spec.add a b))]
      _ = ctx.spec.add (ctx.spec.neg (ctx.spec.add a b))
          (ctx.spec.add (ctx.spec.add (ctx.spec.neg a) (ctx.spec.neg b)) (ctx.spec.add a b)) := by
            rw [ctx.certificate.orderedField.add_assoc]
      _ = ctx.spec.add (ctx.spec.neg (ctx.spec.add a b)) ctx.spec.zero := by rw [hzero]
      _ = ctx.spec.neg (ctx.spec.add a b) := ctx.certificate.orderedField.add_zero _
  exact h.symm

private theorem round_odd_zopp_add_opp (n f : Z) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
      (Zadd (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp n) f) =
      Zadd n (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp f) := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

end CompCert4Lean.Flocq.Prop.Round_odd

namespace CompCert4Lean.Flocq.Prop.Round_odd

open CompCert4Lean.Flocq.Core

private theorem round_odd_zsub_add (a b c : Z) :
    Zsub (Zadd a b) c = Zadd a (Zsub b c) := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

private theorem round_odd_add_le_left (ctx : ExactRealContext) (a b c : R ctx)
    (h : Rle ctx b c) : Rle ctx (Rplus ctx a b) (Rplus ctx a c) := by
  change ctx.spec.le (ctx.spec.add a b) (ctx.spec.add a c)
  rcases ctx.certificate.total_order b c with (hbc | hbc) | hcb
  · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
      (ctx.certificate.orderedField.add_lt_compat_l a b c hbc) |>.1
  · subst c
    exact ctx.certificate.orderedField.le_refl _
  · exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hcb).2 h |>.elim

private theorem round_odd_zero_lt_one (ctx : ExactRealContext) :
    Rlt ctx (R0 ctx) (CompCert4Lean.Flocq.Core.Raux.Exact.Rone ctx) := by
  change ctx.spec.lt ctx.spec.zero ctx.spec.one
  rcases ctx.certificate.total_order ctx.spec.zero ctx.spec.one with (h | h) | h
  · exact h
  · exact (ctx.certificate.orderedField.zero_ne_one h).elim
  · have hpos : ctx.spec.lt ctx.spec.zero (ctx.spec.neg ctx.spec.one) := by
      have h' := ctx.certificate.orderedField.add_lt_compat_l (ctx.spec.neg ctx.spec.one)
        ctx.spec.one ctx.spec.zero h
      simpa [ctx.certificate.orderedField.neg_add_cancel,
        ctx.certificate.orderedField.add_zero] using h'
    have hneg : ctx.spec.lt (ctx.spec.neg ctx.spec.one) ctx.spec.zero := by
      have h' := ctx.certificate.orderedField.mul_lt_compat_l (ctx.spec.neg ctx.spec.one)
        ctx.spec.one ctx.spec.zero hpos h
      simpa [ctx.certificate.orderedField.mul_one,
        ctx.certificate.orderedField.mul_zero] using h'
    exact ((ctx.certificate.orderedField.lt_irrefl _)
      (ctx.certificate.orderedField.lt_trans _ _ _ hpos hneg)).elim

private theorem round_odd_zpos_xO (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos (.xO p) =
      Zadd (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p) := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (.xO p)) =
    Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) +
      Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
  simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
  omega

private theorem round_odd_zpos_xI (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos (.xI p) =
      Zadd (Zadd (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p)) Zone := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (.xI p)) =
    (Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) +
      Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) + 1
  simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
  omega

private theorem round_odd_zpos_positive (ctx : ExactRealContext) :
    ∀ p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive,
      Rlt ctx (R0 ctx) (IZR ctx (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p)) := by
  intro p
  induction p with
  | xH =>
      change ctx.spec.lt ctx.spec.zero
        (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos .xH))
      rw [ctx.certificate.sourceLaws.ofZ_one]
      exact round_odd_zero_lt_one ctx
  | xO p ih =>
      rw [round_odd_zpos_xO]
      change ctx.spec.lt ctx.spec.zero
        (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p)
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p)))
      rw [ctx.certificate.sourceLaws.ofZ_add]
      change ctx.spec.lt ctx.spec.zero
        (ctx.spec.add (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))
          (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p)))
      have h' := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))
        ctx.spec.zero (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p)) ih
      have h' : ctx.spec.lt (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))
          (ctx.spec.add (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))
            (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))) := by
        simpa [ctx.certificate.orderedField.add_zero] using h'
      exact ctx.certificate.orderedField.lt_trans _ _ _ ih h'
  | xI p ih =>
      rw [round_odd_zpos_xI]
      change ctx.spec.lt ctx.spec.zero
        (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p)
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p)) Zone))
      rw [ctx.certificate.sourceLaws.ofZ_add, ctx.certificate.sourceLaws.ofZ_add,
        ctx.certificate.sourceLaws.ofZ_one]
      change ctx.spec.lt ctx.spec.zero
        (ctx.spec.add (ctx.spec.add (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))
          (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))) ctx.spec.one)
      have htwo : ctx.spec.lt ctx.spec.zero
          (ctx.spec.add (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))
            (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))) := by
        have h' := ctx.certificate.orderedField.add_lt_compat_l
          (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))
          ctx.spec.zero (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p)) ih
        have h' : ctx.spec.lt (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))
            (ctx.spec.add (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))
              (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))) := by
          simpa [ctx.certificate.orderedField.add_zero] using h'
        exact ctx.certificate.orderedField.lt_trans _ _ _ ih h'
      have h' := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.add (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))
          (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p)))
        ctx.spec.zero ctx.spec.one (round_odd_zero_lt_one ctx)
      have h' : ctx.spec.lt
          (ctx.spec.add (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))
            (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p)))
          (ctx.spec.add (ctx.spec.add (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))
            (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos p))) ctx.spec.one) := by
        simpa [ctx.certificate.orderedField.add_zero] using h'
      exact ctx.certificate.orderedField.lt_trans _ _ _ htwo h'

private theorem round_odd_izr_nonneg (ctx : ExactRealContext) (z : Z)
    (h : Zle (CompCert4Lean.Flocq.Core.Zaux.Z0) z) : Rle ctx (R0 ctx) (IZR ctx z) := by
  cases z with
  | Z0 =>
      change ctx.spec.le ctx.spec.zero (ctx.spec.ofZ CompCert4Lean.Flocq.Core.Zaux.Z0)
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact ctx.certificate.orderedField.le_refl _
  | Zpos p =>
      exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
        (round_odd_zpos_positive ctx p) |>.1
  | Zneg p =>
      change 0 ≤ -Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at h
      have hp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hp' : (0 : Int) < Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.ofNat_lt.mpr hp
      omega

private theorem round_odd_zadd_sub_cancel (a b : Z) :
    Zadd a (Zsub b a) = b := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

private theorem round_odd_izr_positive (ctx : ExactRealContext) (z : Z)
    (h : Zlt (CompCert4Lean.Flocq.Core.Zaux.Z0) z) : Rlt ctx (R0 ctx) (IZR ctx z) := by
  cases z with
  | Z0 =>
      change 0 < 0 at h
      omega
  | Zpos p => exact round_odd_zpos_positive ctx p
  | Zneg p =>
      change 0 < -Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at h
      have hp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hp' : (0 : Int) < Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.ofNat_lt.mpr hp
      omega

private theorem round_odd_izr_le (ctx : ExactRealContext) (a b : Z)
    (h : Zle a b) : Rle ctx (IZR ctx a) (IZR ctx b) := by
  have hd : Zle (CompCert4Lean.Flocq.Core.Zaux.Z0) (Zsub b a) := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub b a)
    change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub b a)
    rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub b a) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b -
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a by
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b at h
    omega
  have hr := round_odd_add_le_left ctx (IZR ctx a) (R0 ctx) (IZR ctx (Zsub b a))
    (round_odd_izr_nonneg ctx (Zsub b a) hd)
  have hadd : ctx.spec.add (ctx.spec.ofZ a) (ctx.spec.ofZ (Zsub b a)) =
      ctx.spec.ofZ (Zadd a (Zsub b a)) := ctx.certificate.sourceLaws.ofZ_add a (Zsub b a) |>.symm
  change ctx.spec.le (ctx.spec.add (ctx.spec.ofZ a) ctx.spec.zero)
    (ctx.spec.add (ctx.spec.ofZ a) (ctx.spec.ofZ (Zsub b a))) at hr
  rw [hadd, round_odd_zadd_sub_cancel a b] at hr
  change ctx.spec.le (ctx.spec.ofZ a) (ctx.spec.ofZ b)
  simpa [ctx.certificate.orderedField.add_zero] using hr

private theorem round_odd_izr_lt (ctx : ExactRealContext) (a b : Z)
    (h : Zlt a b) : Rlt ctx (IZR ctx a) (IZR ctx b) := by
  have hd : Zlt (CompCert4Lean.Flocq.Core.Zaux.Z0) (Zsub b a) := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0 <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub b a)
    change 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub b a)
    rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub b a) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b -
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a by
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b at h
    omega
  have hr := ctx.certificate.orderedField.add_lt_compat_l (IZR ctx a)
    (R0 ctx) (IZR ctx (Zsub b a)) (round_odd_izr_positive ctx (Zsub b a) hd)
  have hadd : ctx.spec.add (ctx.spec.ofZ a) (ctx.spec.ofZ (Zsub b a)) =
      ctx.spec.ofZ (Zadd a (Zsub b a)) := ctx.certificate.sourceLaws.ofZ_add a (Zsub b a) |>.symm
  change ctx.spec.lt (ctx.spec.add (ctx.spec.ofZ a) ctx.spec.zero)
    (ctx.spec.add (ctx.spec.ofZ a) (ctx.spec.ofZ (Zsub b a))) at hr
  rw [hadd, round_odd_zadd_sub_cancel a b] at hr
  change ctx.spec.lt (ctx.spec.ofZ a) (ctx.spec.ofZ b)
  simpa [ctx.certificate.orderedField.add_zero] using hr

private theorem round_odd_add_le_cancel_right (ctx : ExactRealContext) (a b c : R ctx)
    (h : Rle ctx (Rplus ctx a c) (Rplus ctx b c)) : Rle ctx a b := by
  change ctx.spec.le a b
  rcases ctx.certificate.total_order a b with (hab | hab) | hba
  · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hab |>.1
  · subst b
    exact ctx.certificate.orderedField.le_refl _
  · have h' := ctx.certificate.orderedField.add_lt_compat_l c b a hba
    change ctx.spec.le (ctx.spec.add a c) (ctx.spec.add b c) at h
    have h' : ctx.spec.lt (ctx.spec.add b c) (ctx.spec.add a c) := by
      simpa [ctx.certificate.orderedField.add_comm] using h'
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h').2 h |>.elim

private theorem round_odd_lt_le_trans (ctx : ExactRealContext) (a b c : R ctx)
    (hab : Rlt ctx a b) (hbc : Rle ctx b c) : Rlt ctx a c := by
  change ctx.spec.lt a c
  have hab' : ctx.spec.le a b ∧ ¬ ctx.spec.le b a :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hab
  apply (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
  constructor
  · exact ctx.certificate.orderedField.le_trans _ _ _ hab'.1 hbc
  · intro hca
    exact hab'.2 (ctx.certificate.orderedField.le_trans _ _ _ hbc hca)

private theorem round_odd_add_sub_cancel_right (ctx : ExactRealContext) (x u : R ctx) :
    Rplus ctx x (CompCert4Lean.Flocq.Core.Raux.Exact.Rminus ctx u x) = u := by
  change ctx.spec.add x (ctx.spec.add u (ctx.spec.neg x)) = u
  calc
    ctx.spec.add x (ctx.spec.add u (ctx.spec.neg x)) =
        ctx.spec.add x (ctx.spec.add (ctx.spec.neg x) u) := by
      rw [ctx.certificate.orderedField.add_comm u (ctx.spec.neg x)]
    _ = ctx.spec.add (ctx.spec.add x (ctx.spec.neg x)) u := by
      rw [ctx.certificate.orderedField.add_assoc]
    _ = ctx.spec.add (ctx.spec.add (ctx.spec.neg x) x) u := by
      rw [ctx.certificate.orderedField.add_comm x (ctx.spec.neg x)]
    _ = u := by rw [ctx.certificate.orderedField.neg_add_cancel,
      ctx.certificate.orderedField.zero_add]

private theorem round_odd_zadd_one_le_of_lt (a b : Z) (h : Zlt a b) :
    Zle (Zadd a Zone) b := by
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd a Zone) ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add a
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos .xH)) ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b
  rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add a
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos .xH)) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a + 1 by
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    rfl]
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b at h
  omega

private theorem round_odd_up_le_add_one (ctx : ExactRealContext) (x : R ctx) :
    Rle ctx (IZR ctx (ctx.spec.up x))
      (Rplus ctx x (CompCert4Lean.Flocq.Core.Raux.Exact.Rone ctx)) := by
  have hgap := ctx.certificate.sourceLaws.up_gap x
  have h' : ctx.spec.le
      (ctx.spec.add x (CompCert4Lean.Foundation.FlocqReal.ExactReal.Rminus ctx.spec
        (ctx.spec.ofZ (ctx.spec.up x)) x))
      (ctx.spec.add x (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos .xH))) :=
    round_odd_add_le_left ctx x
      (CompCert4Lean.Foundation.FlocqReal.ExactReal.Rminus ctx.spec
        (ctx.spec.ofZ (ctx.spec.up x)) x)
      (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos .xH)) hgap
  rw [ctx.certificate.sourceLaws.ofZ_one] at h'
  change ctx.spec.le (ctx.spec.add x (ctx.spec.add (ctx.spec.ofZ (ctx.spec.up x)) (ctx.spec.neg x)))
    (ctx.spec.add x ctx.spec.one) at h'
  have hcancel : ctx.spec.add x (ctx.spec.add (ctx.spec.ofZ (ctx.spec.up x)) (ctx.spec.neg x)) =
      ctx.spec.ofZ (ctx.spec.up x) := round_odd_add_sub_cancel_right ctx x (IZR ctx (ctx.spec.up x))
  rw [hcancel] at h'
  exact h'

private theorem round_odd_tech_up (ctx : ExactRealContext) (x : R ctx) (z : Z)
    (hlo : Rlt ctx x (IZR ctx z))
    (hhi : Rle ctx (IZR ctx z)
      (Rplus ctx x (CompCert4Lean.Flocq.Core.Raux.Exact.Rone ctx))) : z = ctx.spec.up x := by
  have h_up_gt := ctx.certificate.sourceLaws.up_gt x
  have h_up_le := round_odd_up_le_add_one ctx x
  have hnot_up_lt_z : ¬ Zlt (ctx.spec.up x) z := by
    intro huz
    have hsucc : Zle (Zadd (ctx.spec.up x) Zone) z :=
      round_odd_zadd_one_le_of_lt (ctx.spec.up x) z huz
    have hsuccR := round_odd_izr_le ctx (Zadd (ctx.spec.up x) Zone) z hsucc
    have hbound := ctx.certificate.orderedField.le_trans _ _ _ hsuccR hhi
    change ctx.spec.le (ctx.spec.ofZ (Zadd (ctx.spec.up x) Zone))
      (ctx.spec.add x ctx.spec.one) at hbound
    change ctx.spec.le (ctx.spec.ofZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add (ctx.spec.up x)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos .xH)))
      (ctx.spec.add x ctx.spec.one) at hbound
    rw [ctx.certificate.sourceLaws.ofZ_add, ctx.certificate.sourceLaws.ofZ_one] at hbound
    have hle := round_odd_add_le_cancel_right ctx (IZR ctx (ctx.spec.up x)) x
      (CompCert4Lean.Flocq.Core.Raux.Exact.Rone ctx) hbound
    change ctx.spec.lt x (ctx.spec.ofZ (ctx.spec.up x)) at h_up_gt
    change ctx.spec.le (ctx.spec.ofZ (ctx.spec.up x)) x at hle
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h_up_gt).2 hle
  have hnot_z_lt_up : ¬ Zlt z (ctx.spec.up x) := by
    intro hzu
    have hsucc : Zle (Zadd z Zone) (ctx.spec.up x) :=
      round_odd_zadd_one_le_of_lt z (ctx.spec.up x) hzu
    have hsuccR := round_odd_izr_le ctx (Zadd z Zone) (ctx.spec.up x) hsucc
    change ctx.spec.le (ctx.spec.ofZ (Zadd z Zone)) (ctx.spec.ofZ (ctx.spec.up x)) at hsuccR
    change ctx.spec.le (ctx.spec.ofZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add z
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos .xH)))
      (ctx.spec.ofZ (ctx.spec.up x)) at hsuccR
    rw [ctx.certificate.sourceLaws.ofZ_add, ctx.certificate.sourceLaws.ofZ_one] at hsuccR
    have hshift := ctx.certificate.orderedField.add_lt_compat_l ctx.spec.one x
      (ctx.spec.ofZ z) hlo
    change ctx.spec.lt (ctx.spec.add ctx.spec.one x)
      (ctx.spec.add ctx.spec.one (ctx.spec.ofZ z)) at hshift
    have hshift' : ctx.spec.lt (ctx.spec.add x ctx.spec.one)
      (ctx.spec.add (ctx.spec.ofZ z) ctx.spec.one) := by
      simpa [ctx.certificate.orderedField.add_comm] using hshift
    have hlt := round_odd_lt_le_trans ctx
      (ctx.spec.add x ctx.spec.one)
      (ctx.spec.add (ctx.spec.ofZ z) ctx.spec.one)
      (ctx.spec.ofZ (ctx.spec.up x)) hshift' hsuccR
    change ctx.spec.le (ctx.spec.ofZ (ctx.spec.up x)) (ctx.spec.add x ctx.spec.one) at h_up_le
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt).2 h_up_le
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (ctx.spec.up x)
  change ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (ctx.spec.up x) <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z at hnot_up_lt_z
  change ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (ctx.spec.up x) at hnot_z_lt_up
  omega

theorem Zfloor_plus (ctx : ExactRealContext) : Zfloor_plusStatement ctx := by
  intro n y
  have hup_y := ctx.certificate.sourceLaws.up_gt y
  have hup_y' : ctx.spec.lt (ctx.spec.add (ctx.spec.ofZ n) y)
      (ctx.spec.add (ctx.spec.ofZ n) (ctx.spec.ofZ (ctx.spec.up y))) := by
    exact ctx.certificate.orderedField.add_lt_compat_l (ctx.spec.ofZ n) y
      (ctx.spec.ofZ (ctx.spec.up y)) hup_y
  have hlo : Rlt ctx (Rplus ctx (IZR ctx n) y)
      (IZR ctx (Zadd n (ctx.spec.up y))) := by
    change ctx.spec.lt (ctx.spec.add (ctx.spec.ofZ n) y)
      (ctx.spec.ofZ (Zadd n (ctx.spec.up y)))
    change ctx.spec.lt (ctx.spec.add (ctx.spec.ofZ n) y)
      (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add n (ctx.spec.up y)))
    rw [ctx.certificate.sourceLaws.ofZ_add]
    exact hup_y'
  have hupper_y := round_odd_up_le_add_one ctx y
  have hupper_y' := round_odd_add_le_left ctx (IZR ctx n)
    (IZR ctx (ctx.spec.up y))
    (Rplus ctx y (CompCert4Lean.Flocq.Core.Raux.Exact.Rone ctx)) hupper_y
  have hhi : Rle ctx (IZR ctx (Zadd n (ctx.spec.up y)))
      (Rplus ctx (Rplus ctx (IZR ctx n) y)
        (CompCert4Lean.Flocq.Core.Raux.Exact.Rone ctx)) := by
    change ctx.spec.le (ctx.spec.ofZ (Zadd n (ctx.spec.up y)))
      (ctx.spec.add (ctx.spec.add (ctx.spec.ofZ n) y) ctx.spec.one)
    change ctx.spec.le (ctx.spec.ofZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add n (ctx.spec.up y)))
      (ctx.spec.add (ctx.spec.add (ctx.spec.ofZ n) y) ctx.spec.one)
    rw [ctx.certificate.sourceLaws.ofZ_add]
    change ctx.spec.le (ctx.spec.add (ctx.spec.ofZ n) (ctx.spec.ofZ (ctx.spec.up y)))
      (ctx.spec.add (ctx.spec.add (ctx.spec.ofZ n) y) ctx.spec.one)
    change ctx.spec.le (ctx.spec.add (ctx.spec.ofZ n) (ctx.spec.ofZ (ctx.spec.up y)))
      (ctx.spec.add (ctx.spec.ofZ n) (ctx.spec.add y ctx.spec.one)) at hupper_y'
    rw [← ctx.certificate.orderedField.add_assoc] at hupper_y'
    exact hupper_y'
  have hup := round_odd_tech_up ctx (Rplus ctx (IZR ctx n) y)
    (Zadd n (ctx.spec.up y)) hlo hhi
  change Zsub (ctx.spec.up (Rplus ctx (IZR ctx n) y)) Zone =
    Zadd n (Zsub (ctx.spec.up y) Zone)
  rw [← hup, round_odd_zsub_add]

end CompCert4Lean.Flocq.Prop.Round_odd

namespace CompCert4Lean.Flocq.Prop.Round_odd

open CompCert4Lean.Flocq.Core

theorem Zceil_plus (ctx : ExactRealContext) : Zceil_plusStatement ctx := by
  intro n y
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
    (Zfloor ctx (Ropp ctx (Rplus ctx (IZR ctx n) y))) =
      Zadd n (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
        (Zfloor ctx (Ropp ctx y)))
  have hneg : Ropp ctx (Rplus ctx (IZR ctx n) y) =
      Rplus ctx (IZR ctx (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp n))
        (Ropp ctx y) := by
    change ctx.spec.neg (ctx.spec.add (ctx.spec.ofZ n) y) =
      ctx.spec.add (ctx.spec.ofZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp n)) (ctx.spec.neg y)
    have hdist := round_odd_neg_add_distr ctx (IZR ctx n) y
    change ctx.spec.neg (ctx.spec.add (ctx.spec.ofZ n) y) =
      ctx.spec.add (ctx.spec.neg (ctx.spec.ofZ n)) (ctx.spec.neg y) at hdist
    rw [hdist]
    rw [ctx.certificate.sourceLaws.ofZ_neg]
  have hfloor := Zfloor_plus ctx
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp n) (Ropp ctx y)
  rw [← hneg] at hfloor
  rw [hfloor, round_odd_zopp_add_opp]

end CompCert4Lean.Flocq.Prop.Round_odd

namespace CompCert4Lean.Flocq.Prop.Round_odd

open CompCert4Lean.Flocq.Core

theorem Zeven_abs : Zeven_absStatement := by
  intro z
  change decide (Int.natAbs
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zabs z)) % 2 = 0) =
    decide (Int.natAbs
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z) % 2 = 0)
  have hz : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zabs z) =
      Int.ofNat (Int.natAbs
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z)) := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs z) = _
    exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt _
  rw [hz]
  simp

end CompCert4Lean.Flocq.Prop.Round_odd
namespace CompCert4Lean.Flocq.Prop.Round_odd
open CompCert4Lean.Flocq.Core
private theorem round_odd_even_zpower_of_even (beta : radix) (e : Z)
    (he : Zlt (CompCert4Lean.Flocq.Core.Zaux.Z0) e)
    (hbeta : Zeven (radix_val beta) = true) :
    Zeven (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) e) = true := by
  cases e with
  | Z0 =>
      change (0 : Int) < 0 at he
      omega
  | Zneg p =>
      change (0 : Int) < -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at he
      have hp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hp' : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) := Int.ofNat_lt.mpr hp
      omega
  | Zpos p =>
      change decide (Int.natAbs
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (radix_val beta)) % 2 = 0) = true at hbeta
      have hmod : Int.natAbs
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (radix_val beta)) % 2 = 0 := by
        simpa using hbeta
      unfold CompCert4Lean.Flocq.Core.Zaux.Zpower
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
      change decide (Int.natAbs (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (Int.pow (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (radix_val beta))
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)))) % 2 = 0) = true
      rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      have hh : Int.natAbs (Int.pow
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (radix_val beta))
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) =
          Int.natAbs (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (radix_val beta)) ^
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) := by
        exact Int.natAbs_pow _ _
      rw [hh, Nat.pow_mod, hmod]
      have hp_nat := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      rw [Nat.zero_pow hp_nat]
      simp


private theorem round_odd_even_mul_right (a b : Z) (hb : Zeven b = true) :
    Zeven (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul a b) = true := by
  change decide (Int.natAbs
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul a b)) % 2 = 0) = true
  have hmul : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul a b) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a *
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  rw [hmul]
  have habs : Int.natAbs (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a *
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b) =
      Int.natAbs (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a) *
        Int.natAbs (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b) := by
    exact Int.natAbs_mul _ _
  rw [habs, Nat.mul_mod]
  change decide (Int.natAbs
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b) % 2 = 0) = true at hb
  have hbmod : Int.natAbs
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b) % 2 = 0 := by
    simpa using hb
  rw [hbmod]
  simp
theorem exists_even_fexp_lt : ∀ (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx),
    exists_even_fexp_ltStatement ctx magnitude := by
  intro ctx magnitude beta hbeta c x hx
  rcases hx with ⟨g, hgx, hge⟩
  let e : Z := Zsub (Fexp g) (c (mag_val ctx magnitude beta x))
  have he : Zlt (CompCert4Lean.Flocq.Core.Zaux.Z0) e := by
    change (0 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e
    dsimp [e]
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change (0 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Fexp g) -
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (c (mag_val ctx magnitude beta x))
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (c (mag_val ctx magnitude beta x)) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Fexp g) at hge
    omega
  have he_nonneg : Zle (CompCert4Lean.Flocq.Core.Zaux.Z0) e := by
    change (0 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e
    dsimp [e]
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change (0 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Fexp g) -
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (c (mag_val ctx magnitude beta x))
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (c (mag_val ctx magnitude beta x)) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Fexp g) at hge
    omega
  have hsum : Zadd e (c (mag_val ctx magnitude beta x)) = Fexp g := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp [e, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  have hf2r : F2R ctx (Float beta
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul (Fnum g)
        (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) e))
      (c (mag_val ctx magnitude beta x))) = x := by
    change ctx.spec.mul
      (ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul (Fnum g)
        (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) e)))
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta
        (c (mag_val ctx magnitude beta x))) = x
    have hmul := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR
      ctx (Fnum g)
        (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) e)
    change ctx.spec.ofZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
        (Fnum g) (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) e)) =
      ctx.spec.mul (ctx.spec.ofZ (Fnum g))
        (ctx.spec.ofZ (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) e)) at hmul
    rw [hmul]
    have hp := CompCert4Lean.Flocq.Core.Raux.IZR_Zpower ctx beta e he_nonneg
    change ctx.spec.ofZ (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) e) =
      CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e at hp
    rw [hp]
    rw [ctx.certificate.orderedField.mul_assoc]
    have hbpow := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta e
      (c (mag_val ctx magnitude beta x))
    change CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta
        (Zadd e (c (mag_val ctx magnitude beta x))) =
      ctx.spec.mul
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta e)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta
          (c (mag_val ctx magnitude beta x))) at hbpow
    rw [← hbpow, hsum]
    change ctx.spec.mul (ctx.spec.ofZ (Fnum g))
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Fexp g)) = x
    simpa [CompCert4Lean.Flocq.Core.Defs.Exact.F2R, CompCert4Lean.Flocq.Core.Raux.Exact.IZR, CompCert4Lean.Flocq.Core.Raux.Exact.Rmult, CompCert4Lean.Foundation.FlocqReal.ExactReal.IZR, CompCert4Lean.Foundation.FlocqReal.ExactReal.Rmult] using hgx
  refine ⟨Float beta
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul (Fnum g)
        (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) e))
      (c (mag_val ctx magnitude beta x)), hf2r, ?_, ?_⟩
  · change c (mag_val ctx magnitude beta x) =
      c (mag_val ctx magnitude beta
        (F2R ctx (Float beta
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul (Fnum g)
            (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) e))
          (c (mag_val ctx magnitude beta x)))))
    rw [hf2r]
  · change Zeven (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul (Fnum g)
      (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) e)) = true
    have hp := round_odd_even_zpower_of_even beta e he hbeta
    exact round_odd_even_mul_right (Fnum g)
      (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) e) hp
end CompCert4Lean.Flocq.Prop.Round_odd

namespace CompCert4Lean.Flocq.Prop.Round_odd

open CompCert4Lean.Flocq.Core

theorem d_le_m : ∀ (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx),
    d_le_mStatement ctx magnitude := by
  intro ctx magnitude beta fexp x d u hd hu
  rcases hd with ⟨_, hdx, _⟩
  rcases hu with ⟨_, hxu, _⟩
  have hdu : Rle ctx (F2R ctx d) (F2R ctx u) :=
    ctx.certificate.orderedField.le_trans _ _ _ hdx hxu
  have hone : ctx.spec.lt ctx.spec.zero ctx.spec.one := by
    exact round_odd_zero_lt_one ctx
  have htwo_pos : ctx.spec.lt ctx.spec.zero
      (ctx.spec.add ctx.spec.one ctx.spec.one) := by
    have hlt := ctx.certificate.orderedField.add_lt_compat_l ctx.spec.one
      ctx.spec.zero ctx.spec.one hone
    rw [ctx.certificate.orderedField.add_zero] at hlt
    exact ctx.certificate.orderedField.lt_trans _ _ _ hone hlt
  have htwo_ne : ctx.spec.add ctx.spec.one ctx.spec.one ≠ ctx.spec.zero := by
    intro hz
    rw [hz] at htwo_pos
    exact (ctx.certificate.orderedField.lt_irrefl _ htwo_pos).elim
  have hadd : ctx.spec.le (ctx.spec.add (F2R ctx d) (F2R ctx d))
      (ctx.spec.add (F2R ctx d) (F2R ctx u)) := by
    exact round_odd_add_le_left ctx (F2R ctx d) (F2R ctx d) (F2R ctx u) hdu
  have hscaled : ctx.spec.le
      (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one) (F2R ctx d))
      (ctx.spec.add (F2R ctx d) (F2R ctx u)) := by
    apply ctx.certificate.orderedField.le_trans _ _ _
      (show ctx.spec.le
          (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one) (F2R ctx d))
          (ctx.spec.add (F2R ctx d) (F2R ctx d)) by
        rw [ctx.certificate.orderedField.mul_comm,
          ctx.certificate.orderedField.left_distrib,
          ctx.certificate.orderedField.mul_one]
        exact ctx.certificate.orderedField.le_refl _)
      hadd
  have hi := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
      (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rinv_0_lt_compat
        ctx (ctx.spec.add ctx.spec.one ctx.spec.one) (by
          change ctx.spec.lt (ctx.spec.ofZ CompCert4Lean.Flocq.Core.Zaux.Z0)
            (ctx.spec.add ctx.spec.one ctx.spec.one)
          rw [ctx.certificate.sourceLaws.ofZ_zero]
          exact htwo_pos)) |>.1
  have hinv_nonneg : ctx.spec.le
      (ctx.spec.ofZ CompCert4Lean.Flocq.Core.Zaux.Z0)
      (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)) := hi
  have hhalf :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
      ctx (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))
      (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one) (F2R ctx d))
      (ctx.spec.add (F2R ctx d) (F2R ctx u)) hinv_nonneg hscaled
  have hleft : ctx.spec.mul
      (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one) (F2R ctx d))
      (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)) = F2R ctx d := by
    calc
      _ = ctx.spec.mul (F2R ctx d)
          (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
            (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))) := by
        rw [ctx.certificate.orderedField.mul_comm
          (ctx.spec.add ctx.spec.one ctx.spec.one) (F2R ctx d),
          ← ctx.certificate.orderedField.mul_assoc]
      _ = ctx.spec.mul (F2R ctx d) ctx.spec.one := by
        rw [ctx.certificate.orderedField.mul_comm
            (ctx.spec.add ctx.spec.one ctx.spec.one)
            (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)),
          ctx.certificate.orderedField.inv_mul_cancel _ htwo_ne]
      _ = F2R ctx d := ctx.certificate.orderedField.mul_one _
  change CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle ctx.spec
    (F2R ctx d)
    (CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv ctx.spec
      (ctx.spec.add (F2R ctx d) (F2R ctx u))
      (ctx.spec.add ctx.spec.one ctx.spec.one))
  unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv
  rw [ctx.certificate.orderedField.div_eq_mul_inv]
  unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle
  have hhalf' : ctx.spec.le
      (ctx.spec.mul (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
        (F2R ctx d)) (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)))
      (ctx.spec.mul (ctx.spec.add (F2R ctx d) (F2R ctx u))
        (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))) := hhalf
  simpa only [hleft] using hhalf'

end CompCert4Lean.Flocq.Prop.Round_odd

namespace CompCert4Lean.Flocq.Prop.Round_odd

open CompCert4Lean.Flocq.Core

theorem m_le_u : ∀ (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx),
    m_le_uStatement ctx magnitude := by
  intro ctx magnitude beta fexp x d u hd hu
  rcases hd with ⟨_, hdx, _⟩
  rcases hu with ⟨_, hxu, _⟩
  have hdu : Rle ctx (F2R ctx d) (F2R ctx u) :=
    ctx.certificate.orderedField.le_trans _ _ _ hdx hxu
  have hone : ctx.spec.lt ctx.spec.zero ctx.spec.one := by
    exact round_odd_zero_lt_one ctx
  have htwo_pos : ctx.spec.lt ctx.spec.zero
      (ctx.spec.add ctx.spec.one ctx.spec.one) := by
    have hlt := ctx.certificate.orderedField.add_lt_compat_l ctx.spec.one
      ctx.spec.zero ctx.spec.one hone
    rw [ctx.certificate.orderedField.add_zero] at hlt
    exact ctx.certificate.orderedField.lt_trans _ _ _ hone hlt
  have htwo_ne : ctx.spec.add ctx.spec.one ctx.spec.one ≠ ctx.spec.zero := by
    intro hz
    rw [hz] at htwo_pos
    exact (ctx.certificate.orderedField.lt_irrefl _ htwo_pos).elim
  have hadd : ctx.spec.le (ctx.spec.add (F2R ctx d) (F2R ctx u))
      (ctx.spec.add (F2R ctx u) (F2R ctx u)) := by
    have hh := round_odd_add_le_left ctx (F2R ctx u) (F2R ctx d) (F2R ctx u) hdu
    change ctx.spec.le (ctx.spec.add (F2R ctx u) (F2R ctx d))
      (ctx.spec.add (F2R ctx u) (F2R ctx u)) at hh
    rw [ctx.certificate.orderedField.add_comm (F2R ctx u) (F2R ctx d)] at hh
    exact hh
  have hscaled : ctx.spec.le (ctx.spec.add (F2R ctx d) (F2R ctx u))
      (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one) (F2R ctx u)) := by
    apply ctx.certificate.orderedField.le_trans _ _ _ hadd
    rw [ctx.certificate.orderedField.mul_comm,
      ctx.certificate.orderedField.left_distrib,
      ctx.certificate.orderedField.mul_one]
    exact ctx.certificate.orderedField.le_refl _
  have hi := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
      (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rinv_0_lt_compat
        ctx (ctx.spec.add ctx.spec.one ctx.spec.one) (by
          change ctx.spec.lt (ctx.spec.ofZ CompCert4Lean.Flocq.Core.Zaux.Z0)
            (ctx.spec.add ctx.spec.one ctx.spec.one)
          rw [ctx.certificate.sourceLaws.ofZ_zero]
          exact htwo_pos)) |>.1
  have hinv_nonneg : ctx.spec.le
      (ctx.spec.ofZ CompCert4Lean.Flocq.Core.Zaux.Z0)
      (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)) := hi
  have hhalf :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
      ctx (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))
      (ctx.spec.add (F2R ctx d) (F2R ctx u))
      (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one) (F2R ctx u))
      hinv_nonneg hscaled
  have hright : ctx.spec.mul
      (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one) (F2R ctx u))
      (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)) = F2R ctx u := by
    calc
      _ = ctx.spec.mul (F2R ctx u)
          (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
            (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))) := by
        rw [ctx.certificate.orderedField.mul_comm
          (ctx.spec.add ctx.spec.one ctx.spec.one) (F2R ctx u),
          ← ctx.certificate.orderedField.mul_assoc]
      _ = ctx.spec.mul (F2R ctx u) ctx.spec.one := by
        rw [ctx.certificate.orderedField.mul_comm
            (ctx.spec.add ctx.spec.one ctx.spec.one)
            (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)),
          ctx.certificate.orderedField.inv_mul_cancel _ htwo_ne]
      _ = F2R ctx u := ctx.certificate.orderedField.mul_one _
  change CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle ctx.spec
    (CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv ctx.spec
      (ctx.spec.add (F2R ctx d) (F2R ctx u))
      (ctx.spec.add ctx.spec.one ctx.spec.one)) (F2R ctx u)
  unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rdiv
  rw [ctx.certificate.orderedField.div_eq_mul_inv]
  unfold CompCert4Lean.Foundation.FlocqReal.ExactReal.Rle
  have hhalf' : ctx.spec.le
      (ctx.spec.mul (ctx.spec.add (F2R ctx d) (F2R ctx u))
        (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one)))
      (ctx.spec.mul (ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one)
        (F2R ctx u)) (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))) := hhalf
  simpa only [hright] using hhalf'

end CompCert4Lean.Flocq.Prop.Round_odd
namespace CompCert4Lean.Flocq.Prop.Round_odd
open CompCert4Lean.Flocq.Core

theorem m_eq_0 : ∀ (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx),
    m_eq_0Statement ctx magnitude := by
  intro ctx magnitude beta hbeta fexp x d u hu hcanon hd0
  obtain ⟨b, hb⟩ := CompCert4Lean.Flocq.Core.Zaux.Zeven_ex (radix_val beta)
  have hb' : radix_val beta = CompCert4Lean.Flocq.Core.Zaux.Zadd
      (CompCert4Lean.Flocq.Core.Zaux.Zmul Ztwo b) CompCert4Lean.Flocq.Core.Zaux.Z0 := by
    simpa [hbeta] using hb
  refine ⟨CompCert4Lean.Flocq.Calc.Operations.Fmult
      (Float beta b (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg .xH)) u, ?_, ?_⟩
  · have hmul := CompCert4Lean.Flocq.Calc.Operations.F2R_mult ctx beta
      (Float beta b (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg .xH)) u
    change CompCert4Lean.Flocq.Calc.Operations.Exact.F2R ctx _ = _
    rw [hmul]
    simp only [CompCert4Lean.Flocq.Calc.Operations.Exact.Rmult,
      CompCert4Lean.Flocq.Calc.Operations.Exact.F2R,
      CompCert4Lean.Flocq.Core.Defs.Exact.F2R,
      CompCert4Lean.Flocq.Core.Defs.Fnum,
      CompCert4Lean.Flocq.Core.Defs.Fexp]
    change CompCert4Lean.Flocq.Core.Raux.Exact.Rmult ctx
      (CompCert4Lean.Flocq.Core.Raux.Exact.Rmult ctx
        (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx b)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg .xH)))
      (CompCert4Lean.Flocq.Core.Raux.Exact.Rmult ctx
        (CompCert4Lean.Flocq.Core.Raux.Exact.IZR ctx (Fnum u))
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Fexp u))) = _
    have hpow : CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg .xH) =
      ctx.spec.inv (ctx.spec.ofZ (radix_val beta)) := by
      have hpow_z : CompCert4Lean.Flocq.Core.Zaux.Zpower_pos
          (radix_val beta) .xH = radix_val beta := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [CompCert4Lean.Flocq.Core.Zaux.Zpower_pos,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow_pos,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        change (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (radix_val beta)).pow 1 = _
        exact Int.pow_one _
      unfold CompCert4Lean.Flocq.Core.Raux.Exact.bpow
      change ctx.spec.inv (ctx.spec.ofZ
        (CompCert4Lean.Flocq.Core.Zaux.Zpower_pos (radix_val beta) .xH)) = _
      rw [hpow_z]
    rw [hpow]
    change ctx.spec.mul
      (ctx.spec.mul (ctx.spec.ofZ b)
        (ctx.spec.inv (ctx.spec.ofZ (radix_val beta))))
      (ctx.spec.mul (ctx.spec.ofZ u.1)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta u.2)) =
      ctx.spec.div
        (ctx.spec.add
          (ctx.spec.mul (ctx.spec.ofZ d.1)
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta d.2))
          (ctx.spec.mul (ctx.spec.ofZ u.1)
            (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta u.2)))
        (ctx.spec.add ctx.spec.one ctx.spec.one)
    have hd0' : ctx.spec.zero =
        ctx.spec.mul (ctx.spec.ofZ d.1)
          (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta d.2) := by
      exact hd0
    rw [← hd0']
    change _ = ctx.spec.div _ _
    rw [ctx.certificate.orderedField.div_eq_mul_inv]
    rw [ctx.certificate.orderedField.zero_add]
    change ctx.spec.mul
      (ctx.spec.mul (ctx.spec.ofZ b)
        (ctx.spec.inv (ctx.spec.ofZ (radix_val beta))))
      (ctx.spec.mul (ctx.spec.ofZ u.1)
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta u.2)) =
      ctx.spec.mul
        (ctx.spec.mul (ctx.spec.ofZ u.1)
          (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta u.2))
        (ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one))
    have hbeta_pos : Rlt ctx (R0 ctx) (IZR ctx (radix_val beta)) := by
      exact round_odd_izr_positive ctx (radix_val beta)
        (CompCert4Lean.Flocq.Core.Zaux.radix_gt_0 beta)
    have hbeta_ne : ctx.spec.ofZ (radix_val beta) ≠ ctx.spec.zero := by
      intro hz
      have hp : ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ (radix_val beta)) := hbeta_pos
      rw [hz] at hp
      exact (ctx.certificate.orderedField.lt_irrefl _ hp).elim
    have hbetaR : ctx.spec.ofZ (radix_val beta) =
        ctx.spec.mul (ctx.spec.ofZ Ztwo) (ctx.spec.ofZ b) := by
      rw [hb', ctx.certificate.sourceLaws.ofZ_add,
        ctx.certificate.sourceLaws.ofZ_zero,
        ctx.certificate.orderedField.add_zero]
      exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR
        ctx Ztwo b
    have hb_ne : ctx.spec.ofZ b ≠ ctx.spec.zero := by
      intro hz
      apply hbeta_ne
      rw [hbetaR, hz, ctx.certificate.orderedField.mul_zero]
    have htwo_pos : ctx.spec.lt ctx.spec.zero
        (ctx.spec.add ctx.spec.one ctx.spec.one) := by
      have h := ctx.certificate.orderedField.add_lt_compat_l ctx.spec.one
        ctx.spec.zero ctx.spec.one (round_odd_zero_lt_one ctx)
      rw [ctx.certificate.orderedField.add_zero] at h
      exact ctx.certificate.orderedField.lt_trans _ _ _
        (round_odd_zero_lt_one ctx) h
    have htwo_ne : ctx.spec.add ctx.spec.one ctx.spec.one ≠ ctx.spec.zero := by
      intro hz
      rw [hz] at htwo_pos
      exact (ctx.certificate.orderedField.lt_irrefl _ htwo_pos).elim
    have htwoR : ctx.spec.ofZ Ztwo =
        ctx.spec.add ctx.spec.one ctx.spec.one := by
      change ctx.spec.ofZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos (.xO .xH)) = _
      rw [round_odd_zpos_xO, ctx.certificate.sourceLaws.ofZ_add,
        ctx.certificate.sourceLaws.ofZ_one]
    have mul_right_cancel : ∀ (x a c : ctx.spec.carrier),
        x ≠ ctx.spec.zero → ctx.spec.mul a x = ctx.spec.mul c x → a = c := by
      intro x a c hx h
      have hh := congrArg (fun z => ctx.spec.mul (ctx.spec.inv x) z) h
      have hl : ctx.spec.mul (ctx.spec.inv x) (ctx.spec.mul a x) = a := by
        calc
          _ = ctx.spec.mul (ctx.spec.mul (ctx.spec.inv x) a) x :=
            (ctx.certificate.orderedField.mul_assoc _ _ _).symm
          _ = ctx.spec.mul (ctx.spec.mul a (ctx.spec.inv x)) x := by
            exact congrArg (fun z => ctx.spec.mul z x)
              (ctx.certificate.orderedField.mul_comm _ _)
          _ = ctx.spec.mul a (ctx.spec.mul (ctx.spec.inv x) x) :=
            ctx.certificate.orderedField.mul_assoc _ _ _
          _ = ctx.spec.mul a ctx.spec.one := by
            rw [ctx.certificate.orderedField.inv_mul_cancel x hx]
          _ = a := ctx.certificate.orderedField.mul_one _
      have hr : ctx.spec.mul (ctx.spec.inv x) (ctx.spec.mul c x) = c := by
        calc
          _ = ctx.spec.mul (ctx.spec.mul (ctx.spec.inv x) c) x :=
            (ctx.certificate.orderedField.mul_assoc _ _ _).symm
          _ = ctx.spec.mul (ctx.spec.mul c (ctx.spec.inv x)) x := by
            exact congrArg (fun z => ctx.spec.mul z x)
              (ctx.certificate.orderedField.mul_comm _ _)
          _ = ctx.spec.mul c (ctx.spec.mul (ctx.spec.inv x) x) :=
            ctx.certificate.orderedField.mul_assoc _ _ _
          _ = ctx.spec.mul c ctx.spec.one := by
            rw [ctx.certificate.orderedField.inv_mul_cancel x hx]
          _ = c := ctx.certificate.orderedField.mul_one _
      exact hl.symm.trans (hh.trans hr)
    have hinvprod : ctx.spec.inv
        (ctx.spec.mul (ctx.spec.ofZ Ztwo) (ctx.spec.ofZ b)) =
        ctx.spec.mul (ctx.spec.inv (ctx.spec.ofZ Ztwo))
          (ctx.spec.inv (ctx.spec.ofZ b)) := by
      have htwo_ofZ_ne : ctx.spec.ofZ Ztwo ≠ ctx.spec.zero := by
        rw [htwoR]
        exact htwo_ne
      apply mul_right_cancel
        (ctx.spec.mul (ctx.spec.ofZ Ztwo) (ctx.spec.ofZ b))
        _ _ (by
          intro hz
          have hp : ctx.spec.lt ctx.spec.zero
              (ctx.spec.ofZ (radix_val beta)) := hbeta_pos
          rw [hbetaR, hz] at hp
          exact (ctx.certificate.orderedField.lt_irrefl _ hp).elim)
      have hprod : ctx.spec.mul
          (ctx.spec.mul (ctx.spec.inv (ctx.spec.ofZ Ztwo))
            (ctx.spec.inv (ctx.spec.ofZ b)))
          (ctx.spec.mul (ctx.spec.ofZ Ztwo) (ctx.spec.ofZ b)) = ctx.spec.one := by
        calc
          _ = ctx.spec.mul (ctx.spec.inv (ctx.spec.ofZ Ztwo))
              (ctx.spec.mul (ctx.spec.inv (ctx.spec.ofZ b))
                (ctx.spec.mul (ctx.spec.ofZ Ztwo) (ctx.spec.ofZ b))) :=
            ctx.certificate.orderedField.mul_assoc _ _ _
          _ = ctx.spec.mul (ctx.spec.inv (ctx.spec.ofZ Ztwo))
              (ctx.spec.mul (ctx.spec.ofZ Ztwo)
                (ctx.spec.mul (ctx.spec.inv (ctx.spec.ofZ b))
                  (ctx.spec.ofZ b))) := by
            congr 1
            calc
              _ = ctx.spec.mul
                  (ctx.spec.mul (ctx.spec.inv (ctx.spec.ofZ b))
                    (ctx.spec.ofZ Ztwo)) (ctx.spec.ofZ b) :=
                (ctx.certificate.orderedField.mul_assoc _ _ _).symm
              _ = ctx.spec.mul
                  (ctx.spec.mul (ctx.spec.ofZ Ztwo)
                    (ctx.spec.inv (ctx.spec.ofZ b))) (ctx.spec.ofZ b) := by
                exact congrArg (fun z => ctx.spec.mul z (ctx.spec.ofZ b))
                  (ctx.certificate.orderedField.mul_comm _ _)
              _ = _ := ctx.certificate.orderedField.mul_assoc _ _ _
          _ = ctx.spec.mul (ctx.spec.inv (ctx.spec.ofZ Ztwo))
              (ctx.spec.mul (ctx.spec.ofZ Ztwo) ctx.spec.one) := by
            rw [ctx.certificate.orderedField.inv_mul_cancel _ hb_ne]
          _ = ctx.spec.one := by
            rw [ctx.certificate.orderedField.mul_one,
              ctx.certificate.orderedField.inv_mul_cancel _ htwo_ofZ_ne]
      calc
        ctx.spec.mul (ctx.spec.inv
            (ctx.spec.mul (ctx.spec.ofZ Ztwo) (ctx.spec.ofZ b)))
            (ctx.spec.mul (ctx.spec.ofZ Ztwo) (ctx.spec.ofZ b)) = ctx.spec.one :=
          ctx.certificate.orderedField.inv_mul_cancel _ (by
            intro hz
            have hp : ctx.spec.lt ctx.spec.zero
                (ctx.spec.ofZ (radix_val beta)) := hbeta_pos
            rw [hbetaR, hz] at hp
            exact (ctx.certificate.orderedField.lt_irrefl _ hp).elim)
        _ = ctx.spec.mul
            (ctx.spec.mul (ctx.spec.inv (ctx.spec.ofZ Ztwo))
              (ctx.spec.inv (ctx.spec.ofZ b)))
            (ctx.spec.mul (ctx.spec.ofZ Ztwo) (ctx.spec.ofZ b)) := hprod.symm
    have hcoef : ctx.spec.mul (ctx.spec.ofZ b)
        (ctx.spec.inv (ctx.spec.ofZ (radix_val beta))) =
        ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one) := by
      calc
        _ = ctx.spec.mul (ctx.spec.ofZ b)
            (ctx.spec.inv (ctx.spec.mul (ctx.spec.ofZ Ztwo) (ctx.spec.ofZ b))) := by
          rw [hbetaR]
        _ = ctx.spec.mul (ctx.spec.ofZ b)
            (ctx.spec.mul (ctx.spec.inv (ctx.spec.ofZ Ztwo))
              (ctx.spec.inv (ctx.spec.ofZ b))) := by rw [hinvprod]
        _ = ctx.spec.mul (ctx.spec.inv (ctx.spec.ofZ Ztwo))
            (ctx.spec.mul (ctx.spec.ofZ b)
              (ctx.spec.inv (ctx.spec.ofZ b))) := by
          calc
            _ = ctx.spec.mul
                (ctx.spec.mul (ctx.spec.ofZ b)
                  (ctx.spec.inv (ctx.spec.ofZ Ztwo)))
                (ctx.spec.inv (ctx.spec.ofZ b)) :=
              (ctx.certificate.orderedField.mul_assoc _ _ _).symm
            _ = ctx.spec.mul
                (ctx.spec.mul (ctx.spec.inv (ctx.spec.ofZ Ztwo))
                  (ctx.spec.ofZ b))
                (ctx.spec.inv (ctx.spec.ofZ b)) := by
              exact congrArg (fun z => ctx.spec.mul z
                  (ctx.spec.inv (ctx.spec.ofZ b)))
                (ctx.certificate.orderedField.mul_comm _ _)
            _ = _ := ctx.certificate.orderedField.mul_assoc _ _ _
        _ = ctx.spec.mul (ctx.spec.inv (ctx.spec.ofZ Ztwo)) ctx.spec.one := by
          rw [ctx.certificate.orderedField.mul_comm
            (ctx.spec.ofZ b) (ctx.spec.inv (ctx.spec.ofZ b)),
            ctx.certificate.orderedField.inv_mul_cancel _ hb_ne]
        _ = ctx.spec.inv (ctx.spec.ofZ Ztwo) := ctx.certificate.orderedField.mul_one _
        _ = ctx.spec.inv (ctx.spec.add ctx.spec.one ctx.spec.one) := by rw [htwoR]
    rw [hcoef]
    exact ctx.certificate.orderedField.mul_comm _ _
  · change CompCert4Lean.Flocq.Core.Defs.Fexp
      (CompCert4Lean.Flocq.Calc.Operations.Fmult
        (Float beta b (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg .xH)) u) = _
    have hu_exp : Fexp u = fexp (mag_val ctx magnitude beta (F2R ctx u)) := by
      exact hcanon
    have hz : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg .xH) (Fexp u) =
        Zsub (fexp (mag_val ctx magnitude beta (F2R ctx u))) Zone := by
      rw [hu_exp]
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      have hzone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = 1 := by decide
      have hone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos .xH) = 1 := by decide
      have hneg : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg .xH) = -1 := by decide
      rw [hzone]
      rw [hneg]
      omega
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg .xH) (Fexp u) = _
    exact hz

end CompCert4Lean.Flocq.Prop.Round_odd

namespace CompCert4Lean.Flocq.Prop.Round_odd

open CompCert4Lean.Flocq.Core

theorem DN_odd_d_aux : ∀ (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx),
    DN_odd_d_auxStatement ctx magnitude := by
  intro ctx magnitude beta fexp _ x d u hd hu z hz
  refine ⟨hd.1, hz.1, ?_⟩
  intro g hg hgz
  rcases CompCert4Lean.Flocq.Core.Round_pred.Rnd_DN_UP_pt_split
      ctx (generic_format ctx magnitude beta fexp) x
      (F2R ctx d) (F2R ctx u) hd hu g hg with hgd | hug
  · exact hgd
  · have huz : Rle ctx (F2R ctx u) z :=
      ctx.certificate.orderedField.le_trans _ _ _ hug hgz
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hz.2).2 huz |>.elim

theorem UP_odd_d_aux : ∀ (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx),
    UP_odd_d_auxStatement ctx magnitude := by
  intro ctx magnitude beta fexp _ x d u hd hu z hz
  refine ⟨hu.1, hz.2, ?_⟩
  intro g hg hzg
  rcases CompCert4Lean.Flocq.Core.Round_pred.Rnd_DN_UP_pt_split
      ctx (generic_format ctx magnitude beta fexp) x
      (F2R ctx d) (F2R ctx u) hd hu g hg with hgd | hug
  · have hzd : Rle ctx z (F2R ctx d) :=
      ctx.certificate.orderedField.le_trans _ _ _ hzg hgd
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hz.1).2 hzd |>.elim
  · exact hug

end CompCert4Lean.Flocq.Prop.Round_odd

namespace CompCert4Lean.Flocq.Prop.Round_odd

open CompCert4Lean.Flocq.Core

private theorem round_odd_generic_format_F2R_aux
    (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (fexp : Z → Z) (x : R ctx) (f : float beta)
    (hfx : F2R ctx f = x)
    (hexp : x ≠ R0 ctx →
      Zle (cexp ctx magnitude beta fexp x) (Fexp f)) :
    generic_format ctx magnitude beta fexp x := by
  by_cases hx : x = R0 ctx
  · rw [hx]
    let f0 : float beta := Float beta CompCert4Lean.Flocq.Core.Zaux.Z0
      (cexp ctx magnitude beta fexp (R0 ctx))
    have hf0 : CompCert4Lean.Flocq.Core.Generic_fmt.Exact.F2R ctx f0 =
        CompCert4Lean.Flocq.Core.Generic_fmt.Exact.R0 ctx := by
      exact CompCert4Lean.Flocq.Core.Float_prop.F2R_0 ctx beta _
    have hformat := CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_canonical
      ctx magnitude beta fexp
      f0
      (CompCert4Lean.Flocq.Core.Generic_fmt.canonical_0
        ctx magnitude beta fexp)
    rw [hf0] at hformat
    exact hformat
  · rcases f with ⟨m, e⟩
    let e' := cexp ctx magnitude beta fexp x
    let f' : float beta := Float beta
      (CompCert4Lean.Flocq.Core.Zaux.Zmul m
        (CompCert4Lean.Flocq.Core.Zaux.Zpower
        (radix_val beta) (Zsub e e'))) e'
    have he : Zle e' e := by
      exact hexp hx
    have hchange := CompCert4Lean.Flocq.Core.Float_prop.F2R_change_exp
      ctx beta e' m e he
    have hf'x : F2R ctx f' = x := by
      exact hchange.symm.trans hfx
    have hcanonical : canonical ctx magnitude beta fexp f' := by
      unfold canonical CompCert4Lean.Flocq.Core.Generic_fmt.Exact.canonical
      change e' = cexp ctx magnitude beta fexp (F2R ctx f')
      rw [hf'x]
    rw [← hf'x]
    exact CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_canonical
      ctx magnitude beta fexp f' hcanonical

private theorem round_odd_bpow_lt_aux (ctx : ExactRealContext) (beta : radix)
    {e1 e2 : Z} (he : Zlt e1 e2) :
    Rlt ctx (bpow ctx beta e1) (bpow ctx beta e2) := by
  let d := Zsub e2 e1
  have hd : Zlt CompCert4Lean.Flocq.Core.Zaux.Z0 d := by
    change (0 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d
    dsimp [d]
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 at he
    omega
  have hd0 : Zle CompCert4Lean.Flocq.Core.Zaux.Z0 d := by
    change (0 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ d
    exact Int.le_of_lt hd
  have hsum : Zadd e1 d = e2 := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [d, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    omega
  have hdpow := CompCert4Lean.Flocq.Core.Zaux.Zpower_gt_1 beta d hd
  have honepow :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.IZR_lt
      ctx Zone (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) d) hdpow
  have hpowR := CompCert4Lean.Flocq.Core.Raux.IZR_Zpower ctx beta d hd0
  have hone : ctx.spec.lt ctx.spec.one (bpow ctx beta d) := by
    change ctx.spec.lt ctx.spec.one
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta d)
    rw [← hpowR, ← ctx.certificate.sourceLaws.ofZ_one]
    exact honepow
  have hpos : ctx.spec.lt ctx.spec.zero (bpow ctx beta e1) :=
    CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta e1
  have hmul := ctx.certificate.orderedField.mul_lt_compat_l
    (bpow ctx beta e1) ctx.spec.one (bpow ctx beta d) hpos hone
  rw [ctx.certificate.orderedField.mul_one] at hmul
  have hplus := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta e1 d
  change bpow ctx beta (Zadd e1 d) =
    ctx.spec.mul (bpow ctx beta e1) (bpow ctx beta d) at hplus
  rw [← hplus, hsum] at hmul
  exact hmul

private theorem round_odd_bpow_le_aux (ctx : ExactRealContext) (beta : radix)
    {e1 e2 : Z} (he : Zle e1 e2) :
    Rle ctx (bpow ctx beta e1) (bpow ctx beta e2) := by
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 at he
  rcases Int.lt_or_eq_of_le he with hlt | heq
  · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp
      (round_odd_bpow_lt_aux ctx beta (show Zlt e1 e2 from hlt)) |>.1
  · have : e1 = e2 :=
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective heq
    subst e2
    exact ctx.certificate.orderedField.le_refl _

private theorem round_odd_mag_unique_aux (ctx : ExactRealContext) (beta : radix)
    (x : R ctx) {e1 e2 : Z}
    (h1 : Rle ctx (bpow ctx beta (Zsub e1 Zone)) (ctx.spec.abs x) ∧
      Rlt ctx (ctx.spec.abs x) (bpow ctx beta e1))
    (h2 : Rle ctx (bpow ctx beta (Zsub e2 Zone)) (ctx.spec.abs x) ∧
      Rlt ctx (ctx.spec.abs x) (bpow ctx beta e2)) : e1 = e2 := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  by_cases heq : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2
  · exact heq
  · rcases Int.lt_or_gt_of_ne heq with h12 | h21
    · have hle : Zle e1 (Zsub e2 Zone) := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub e2 Zone)
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 - 1
        omega
      have hp := round_odd_bpow_le_aux ctx beta hle
      have hbad := ctx.certificate.orderedField.le_trans _ _ _ hp h2.1
      exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h1.2).2 hbad |>.elim
    · have hle : Zle e2 (Zsub e1 Zone) := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub e1 Zone)
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 - 1
        omega
      have hp := round_odd_bpow_le_aux ctx beta hle
      have hbad := ctx.certificate.orderedField.le_trans _ _ _ hp h1.1
      exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h2.2).2 hbad |>.elim

private theorem round_odd_abs_of_nonneg_aux (ctx : ExactRealContext) (x : R ctx)
    (hx : Rle ctx (R0 ctx) x) : ctx.spec.abs x = x := by
  exact ctx.certificate.sourceLaws.abs_nonnegative x hx

private theorem round_odd_mag_eq_of_pos_bounds_aux
    (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx) (beta : radix)
    (x : R ctx) (e : Z) (hx : Rlt ctx (R0 ctx) x)
    (hbounds : Rle ctx (bpow ctx beta (Zsub e Zone)) x ∧
      Rlt ctx x (bpow ctx beta e)) :
    mag_val ctx magnitude beta x = e := by
  have hxne : x ≠ R0 ctx := by
    intro hzero
    rw [hzero] at hx
    exact (ctx.certificate.orderedField.lt_irrefl _ hx).elim
  have hxle : Rle ctx (R0 ctx) x :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hx |>.1
  have habs := round_odd_abs_of_nonneg_aux ctx x hxle
  have hmag := (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_bound hxne
  change Rle ctx (bpow ctx beta
      (Zsub (mag_val ctx magnitude beta x) Zone)) (ctx.spec.abs x) ∧
    Rlt ctx (ctx.spec.abs x) (bpow ctx beta (mag_val ctx magnitude beta x)) at hmag
  have hbounds' : Rle ctx (bpow ctx beta (Zsub e Zone)) (ctx.spec.abs x) ∧
      Rlt ctx (ctx.spec.abs x) (bpow ctx beta e) := by
    simpa only [habs] using hbounds
  exact round_odd_mag_unique_aux ctx beta x hmag hbounds'

private theorem round_odd_mag_bpow_aux
    (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (e : Z) :
    mag_val ctx magnitude beta (bpow ctx beta e) = Zadd e Zone := by
  have hpos := CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta e
  have hsub : Zsub (Zadd e Zone) Zone = e := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e + 1 - 1 =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e
    omega
  apply round_odd_mag_eq_of_pos_bounds_aux ctx magnitude beta
    (bpow ctx beta e) (Zadd e Zone) hpos
  rw [hsub]
  constructor
  · exact ctx.certificate.orderedField.le_refl _
  · apply round_odd_bpow_lt_aux ctx beta
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd e Zone)
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e + 1
    omega

private theorem round_odd_format_bpow_at_mag_aux
    (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (fexp : Z → Z) (hvalid : Valid_exp fexp)
    (d : float beta) (hdpos : Rlt ctx (R0 ctx) (F2R ctx d))
    (hdcanon : canonical ctx magnitude beta fexp d) :
    generic_format ctx magnitude beta fexp
      (bpow ctx beta (mag_val ctx magnitude beta (F2R ctx d))) := by
  let md := mag_val ctx magnitude beta (F2R ctx d)
  have hdne : F2R ctx d ≠ R0 ctx := by
    intro hzero
    rw [hzero] at hdpos
    exact (ctx.certificate.orderedField.lt_irrefl _ hdpos).elim
  have hdle : Rle ctx (R0 ctx) (F2R ctx d) :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hdpos |>.1
  have habs := round_odd_abs_of_nonneg_aux ctx (F2R ctx d) hdle
  have hmbounds := (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta
    (F2R ctx d)).mag_bound hdne
  change Rle ctx (bpow ctx beta (Zsub md Zone)) (ctx.spec.abs (F2R ctx d)) ∧
    Rlt ctx (ctx.spec.abs (F2R ctx d)) (bpow ctx beta md) at hmbounds
  rw [habs] at hmbounds
  have hnum : Zlt CompCert4Lean.Flocq.Core.Zaux.Z0 (Fnum d) := by
    cases d with
    | Float m e =>
        exact CompCert4Lean.Flocq.Core.Float_prop.gt_0_F2R ctx beta m e hdpos
  have hbase : Rle ctx (bpow ctx beta (Fexp d)) (F2R ctx d) :=
    CompCert4Lean.Flocq.Core.Float_prop.bpow_le_F2R ctx beta
      (Fnum d) (Fexp d) hnum
  have hedlt : Zlt (Fexp d) md := by
    by_cases hlt : Zlt (Fexp d) md
    · exact hlt
    · have hle : Zle md (Fexp d) := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ md ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Fexp d)
        change ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Fexp d) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ md at hlt
        omega
      have hp := round_odd_bpow_le_aux ctx beta hle
      have hmd : Rle ctx (bpow ctx beta md) (F2R ctx d) :=
        ctx.certificate.orderedField.le_trans _ _ _ hp hbase
      exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hmbounds.2).2 hmd |>.elim
  have hcanonical : Fexp d = fexp md := by
    exact hdcanon
  have hfnext : Zle (fexp (Zadd md Zone)) md := by
    have hh := (hvalid.valid_exp md).1
    apply hh
    rw [← hcanonical]
    exact hedlt
  change generic_format ctx magnitude beta fexp (bpow ctx beta md)
  apply round_odd_generic_format_F2R_aux ctx magnitude beta fexp
    (bpow ctx beta md) (Float beta Zone md)
  · exact CompCert4Lean.Flocq.Core.Float_prop.F2R_bpow ctx beta md
  · intro _
    change Zle (fexp (mag_val ctx magnitude beta (bpow ctx beta md))) md
    rw [round_odd_mag_bpow_aux ctx magnitude beta md]
    exact hfnext

private theorem round_odd_mag_d_aux
    (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (fexp : Z → Z) (hvalid : Valid_exp fexp)
    (x : R ctx) (d : float beta)
    (hd : Rnd_DN_pt ctx (generic_format ctx magnitude beta fexp) x (F2R ctx d))
    (hcanon : canonical ctx magnitude beta fexp d)
    (hdpos : Rlt ctx (R0 ctx) (F2R ctx d)) :
    mag_val ctx magnitude beta (F2R ctx d) =
      mag_val ctx magnitude beta x := by
  let md := mag_val ctx magnitude beta (F2R ctx d)
  let B := bpow ctx beta md
  have hdne : F2R ctx d ≠ R0 ctx := by
    intro hzero
    rw [hzero] at hdpos
    exact (ctx.certificate.orderedField.lt_irrefl _ hdpos).elim
  have hdle0 : Rle ctx (R0 ctx) (F2R ctx d) :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hdpos |>.1
  have habsd := round_odd_abs_of_nonneg_aux ctx (F2R ctx d) hdle0
  have hdbounds := (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta
    (F2R ctx d)).mag_bound hdne
  change Rle ctx (bpow ctx beta (Zsub md Zone)) (ctx.spec.abs (F2R ctx d)) ∧
    Rlt ctx (ctx.spec.abs (F2R ctx d)) B at hdbounds
  rw [habsd] at hdbounds
  have hformatB : generic_format ctx magnitude beta fexp B := by
    exact round_odd_format_bpow_at_mag_aux ctx magnitude beta fexp hvalid
      d hdpos hcanon
  have hxpos : Rlt ctx (R0 ctx) x :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
      ctx _ _ _ hdpos hd.2.1
  have hxB : Rlt ctx x B := by
    rcases ctx.certificate.total_order x B with h | h
    · rcases h with hlt | heq
      · exact hlt
      · have hBx : Rle ctx B x := by
          rw [heq]
          exact ctx.certificate.orderedField.le_refl _
        have hBd := hd.2.2 B hformatB hBx
        exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hdbounds.2).2 hBd |>.elim
    · have hBx := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1
      have hBd := hd.2.2 B hformatB hBx
      exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hdbounds.2).2 hBd |>.elim
  have hlow : Rle ctx (bpow ctx beta (Zsub md Zone)) x :=
    ctx.certificate.orderedField.le_trans _ _ _ hdbounds.1 hd.2.1
  have hmx := round_odd_mag_eq_of_pos_bounds_aux ctx magnitude beta x md hxpos
    ⟨hlow, hxB⟩
  exact hmx.symm

private theorem round_odd_midpoint_lt_aux (ctx : ExactRealContext)
    (a b c : R ctx) (hac : Rlt ctx a c) (hbc : Rle ctx b c) :
    Rlt ctx (Rdiv ctx (Rplus ctx a b) (Rtwo ctx)) c := by
  have habcb : Rlt ctx (Rplus ctx a b) (Rplus ctx c b) := by
    have h := ctx.certificate.orderedField.add_lt_compat_l b a c hac
    rw [ctx.certificate.orderedField.add_comm b a,
      ctx.certificate.orderedField.add_comm b c] at h
    exact h
  have hcbcc : Rle ctx (Rplus ctx c b) (Rplus ctx c c) :=
    round_odd_add_le_left ctx c b c hbc
  have hsum : Rlt ctx (Rplus ctx a b) (Rplus ctx c c) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
      ctx _ _ _ habcb hcbcc
  have hone := round_odd_zero_lt_one ctx
  have htwo_pos : Rlt ctx (R0 ctx) (Rtwo ctx) := by
    have h := ctx.certificate.orderedField.add_lt_compat_l ctx.spec.one
      ctx.spec.zero ctx.spec.one hone
    rw [ctx.certificate.orderedField.add_zero] at h
    exact ctx.certificate.orderedField.lt_trans _ _ _ hone h
  have htwo_ne : Rtwo ctx ≠ R0 ctx := by
    intro hzero
    rw [hzero] at htwo_pos
    exact (ctx.certificate.orderedField.lt_irrefl _ htwo_pos).elim
  have hinvpos :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rinv_0_lt_compat
      ctx (Rtwo ctx) (by
        change ctx.spec.lt
          (ctx.spec.ofZ CompCert4Lean.Flocq.Core.Zaux.Z0) (Rtwo ctx)
        rw [ctx.certificate.sourceLaws.ofZ_zero]
        exact htwo_pos)
  have hmul :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_compat_r
      ctx (ctx.spec.inv (Rtwo ctx)) (Rplus ctx a b) (Rplus ctx c c)
      hinvpos hsum
  have hright : ctx.spec.mul (Rplus ctx c c) (ctx.spec.inv (Rtwo ctx)) = c := by
    have htwoc : Rplus ctx c c = ctx.spec.mul (Rtwo ctx) c := by
      change ctx.spec.add c c =
        ctx.spec.mul (ctx.spec.add ctx.spec.one ctx.spec.one) c
      rw [ctx.certificate.orderedField.mul_comm,
        ctx.certificate.orderedField.left_distrib,
        ctx.certificate.orderedField.mul_one]
    rw [htwoc]
    calc
      ctx.spec.mul (ctx.spec.mul (Rtwo ctx) c) (ctx.spec.inv (Rtwo ctx)) =
          ctx.spec.mul c (ctx.spec.mul (Rtwo ctx) (ctx.spec.inv (Rtwo ctx))) := by
        rw [ctx.certificate.orderedField.mul_comm (Rtwo ctx) c,
          ← ctx.certificate.orderedField.mul_assoc]
      _ = ctx.spec.mul c ctx.spec.one := by
        rw [ctx.certificate.orderedField.mul_comm (Rtwo ctx),
          ctx.certificate.orderedField.inv_mul_cancel _ htwo_ne]
      _ = c := ctx.certificate.orderedField.mul_one _
  change ctx.spec.lt
    (ctx.spec.div (Rplus ctx a b) (Rtwo ctx)) c
  rw [ctx.certificate.orderedField.div_eq_mul_inv]
  change ctx.spec.lt
    (ctx.spec.mul (Rplus ctx a b) (ctx.spec.inv (Rtwo ctx)))
    (ctx.spec.mul (Rplus ctx c c) (ctx.spec.inv (Rtwo ctx))) at hmul
  rw [hright] at hmul
  exact hmul

private theorem round_odd_mag_m_aux
    (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (fexp : Z → Z) (hvalid : Valid_exp fexp)
    (x : R ctx) (d u : float beta)
    (hd : Rnd_DN_pt ctx (generic_format ctx magnitude beta fexp) x (F2R ctx d))
    (hcanon : canonical ctx magnitude beta fexp d)
    (hu : Rnd_UP_pt ctx (generic_format ctx magnitude beta fexp) x (F2R ctx u))
    (hdpos : Rlt ctx (R0 ctx) (F2R ctx d)) :
    mag_val ctx magnitude beta
        (Rdiv ctx (Rplus ctx (F2R ctx d) (F2R ctx u)) (Rtwo ctx)) =
      mag_val ctx magnitude beta (F2R ctx d) := by
  let md := mag_val ctx magnitude beta (F2R ctx d)
  let B := bpow ctx beta md
  let m := Rdiv ctx (Rplus ctx (F2R ctx d) (F2R ctx u)) (Rtwo ctx)
  have hdne : F2R ctx d ≠ R0 ctx := by
    intro hzero
    rw [hzero] at hdpos
    exact (ctx.certificate.orderedField.lt_irrefl _ hdpos).elim
  have hdle0 : Rle ctx (R0 ctx) (F2R ctx d) :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hdpos |>.1
  have habsd := round_odd_abs_of_nonneg_aux ctx (F2R ctx d) hdle0
  have hdbounds := (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta
    (F2R ctx d)).mag_bound hdne
  change Rle ctx (bpow ctx beta (Zsub md Zone)) (ctx.spec.abs (F2R ctx d)) ∧
    Rlt ctx (ctx.spec.abs (F2R ctx d)) B at hdbounds
  rw [habsd] at hdbounds
  have hformatB : generic_format ctx magnitude beta fexp B := by
    exact round_odd_format_bpow_at_mag_aux ctx magnitude beta fexp hvalid
      d hdpos hcanon
  have hxB : Rlt ctx x B := by
    rcases ctx.certificate.total_order x B with h | h
    · rcases h with hlt | heq
      · exact hlt
      · have hBx : Rle ctx B x := by
          rw [heq]
          exact ctx.certificate.orderedField.le_refl _
        have hBd := hd.2.2 B hformatB hBx
        exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hdbounds.2).2 hBd |>.elim
    · have hBx := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1
      have hBd := hd.2.2 B hformatB hBx
      exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hdbounds.2).2 hBd |>.elim
  have hxBle : Rle ctx x B :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxB |>.1
  have huB : Rle ctx (F2R ctx u) B := hu.2.2 B hformatB hxBle
  have hmle : Rle ctx (F2R ctx d) m := by
    exact d_le_m ctx magnitude beta fexp x d u hd hu
  have hmpos : Rlt ctx (R0 ctx) m :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
      ctx _ _ _ hdpos hmle
  have hmB : Rlt ctx m B :=
    round_odd_midpoint_lt_aux ctx (F2R ctx d) (F2R ctx u) B hdbounds.2 huB
  have hlow : Rle ctx (bpow ctx beta (Zsub md Zone)) m :=
    ctx.certificate.orderedField.le_trans _ _ _ hdbounds.1 hmle
  exact round_odd_mag_eq_of_pos_bounds_aux ctx magnitude beta m md hmpos ⟨hlow, hmB⟩

private theorem round_odd_mul_right_cancel_aux (ctx : ExactRealContext)
    (x a c : R ctx) (hx : x ≠ R0 ctx)
    (h : ctx.spec.mul a x = ctx.spec.mul c x) : a = c := by
  have hh := congrArg (fun z => ctx.spec.mul (ctx.spec.inv x) z) h
  have simplify_left : ∀ y : R ctx,
      ctx.spec.mul (ctx.spec.inv x) (ctx.spec.mul y x) = y := by
    intro y
    calc
      ctx.spec.mul (ctx.spec.inv x) (ctx.spec.mul y x) =
          ctx.spec.mul (ctx.spec.mul (ctx.spec.inv x) y) x :=
        (ctx.certificate.orderedField.mul_assoc _ _ _).symm
      _ = ctx.spec.mul (ctx.spec.mul y (ctx.spec.inv x)) x := by
        exact congrArg (fun z => ctx.spec.mul z x)
          (ctx.certificate.orderedField.mul_comm _ _)
      _ = ctx.spec.mul y (ctx.spec.mul (ctx.spec.inv x) x) :=
        ctx.certificate.orderedField.mul_assoc _ _ _
      _ = ctx.spec.mul y ctx.spec.one := by
        rw [ctx.certificate.orderedField.inv_mul_cancel _ hx]
      _ = y := ctx.certificate.orderedField.mul_one _
  exact (simplify_left a).symm.trans (hh.trans (simplify_left c))

private theorem round_odd_half_coefficient_aux (ctx : ExactRealContext)
    (beta : radix) (b : Z)
    (hb : radix_val beta =
      CompCert4Lean.Flocq.Core.Zaux.Zadd
        (CompCert4Lean.Flocq.Core.Zaux.Zmul Ztwo b)
        CompCert4Lean.Flocq.Core.Zaux.Z0) :
    F2R ctx (Float beta b (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg .xH)) =
      ctx.spec.inv (Rtwo ctx) := by
  have hbetaR : ctx.spec.ofZ (radix_val beta) =
      ctx.spec.mul (ctx.spec.ofZ Ztwo) (ctx.spec.ofZ b) := by
    rw [hb, ctx.certificate.sourceLaws.ofZ_add,
      ctx.certificate.sourceLaws.ofZ_zero,
      ctx.certificate.orderedField.add_zero]
    exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR
      ctx Ztwo b
  have htwoR : ctx.spec.ofZ Ztwo = Rtwo ctx := by
    change ctx.spec.ofZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos (.xO .xH)) =
      ctx.spec.add ctx.spec.one ctx.spec.one
    rw [round_odd_zpos_xO, ctx.certificate.sourceLaws.ofZ_add,
      ctx.certificate.sourceLaws.ofZ_one]
  have hbeta_pos : Rlt ctx (R0 ctx) (IZR ctx (radix_val beta)) :=
    round_odd_izr_positive ctx (radix_val beta)
      (CompCert4Lean.Flocq.Core.Zaux.radix_gt_0 beta)
  have hbeta_ne : ctx.spec.ofZ (radix_val beta) ≠ ctx.spec.zero := by
    intro hzero
    change ctx.spec.lt ctx.spec.zero (ctx.spec.ofZ (radix_val beta)) at hbeta_pos
    rw [hzero] at hbeta_pos
    exact (ctx.certificate.orderedField.lt_irrefl _ hbeta_pos).elim
  have htwo_pos : ctx.spec.lt ctx.spec.zero (Rtwo ctx) := by
    have h := ctx.certificate.orderedField.add_lt_compat_l ctx.spec.one
      ctx.spec.zero ctx.spec.one (round_odd_zero_lt_one ctx)
    rw [ctx.certificate.orderedField.add_zero] at h
    exact ctx.certificate.orderedField.lt_trans _ _ _
      (round_odd_zero_lt_one ctx) h
  have htwo_ne : Rtwo ctx ≠ ctx.spec.zero := by
    intro hzero
    rw [hzero] at htwo_pos
    exact (ctx.certificate.orderedField.lt_irrefl _ htwo_pos).elim
  have hleft : ctx.spec.mul
      (ctx.spec.mul (ctx.spec.ofZ b) (ctx.spec.inv (ctx.spec.ofZ (radix_val beta))))
      (ctx.spec.ofZ (radix_val beta)) = ctx.spec.ofZ b := by
    calc
      _ = ctx.spec.mul (ctx.spec.ofZ b)
          (ctx.spec.mul (ctx.spec.inv (ctx.spec.ofZ (radix_val beta)))
            (ctx.spec.ofZ (radix_val beta))) :=
        ctx.certificate.orderedField.mul_assoc _ _ _
      _ = ctx.spec.mul (ctx.spec.ofZ b) ctx.spec.one := by
        rw [ctx.certificate.orderedField.inv_mul_cancel _ hbeta_ne]
      _ = ctx.spec.ofZ b := ctx.certificate.orderedField.mul_one _
  have hright : ctx.spec.mul (ctx.spec.inv (Rtwo ctx))
      (ctx.spec.ofZ (radix_val beta)) = ctx.spec.ofZ b := by
    rw [hbetaR, htwoR]
    calc
      ctx.spec.mul (ctx.spec.inv (Rtwo ctx))
          (ctx.spec.mul (Rtwo ctx) (ctx.spec.ofZ b)) =
          ctx.spec.mul
            (ctx.spec.mul (ctx.spec.inv (Rtwo ctx)) (Rtwo ctx))
            (ctx.spec.ofZ b) :=
        (ctx.certificate.orderedField.mul_assoc _ _ _).symm
      _ = ctx.spec.mul ctx.spec.one (ctx.spec.ofZ b) := by
        rw [ctx.certificate.orderedField.inv_mul_cancel _ htwo_ne]
      _ = ctx.spec.ofZ b := ctx.certificate.orderedField.one_mul _
  have hcoef : ctx.spec.mul (ctx.spec.ofZ b)
      (ctx.spec.inv (ctx.spec.ofZ (radix_val beta))) =
      ctx.spec.inv (Rtwo ctx) := by
    apply round_odd_mul_right_cancel_aux ctx (ctx.spec.ofZ (radix_val beta))
      _ _ hbeta_ne
    exact hleft.trans hright.symm
  change ctx.spec.mul (ctx.spec.ofZ b)
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg .xH)) = _
  have hpow : CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg .xH) =
      ctx.spec.inv (ctx.spec.ofZ (radix_val beta)) := by
    have hp : CompCert4Lean.Flocq.Core.Zaux.Zpower_pos
        (radix_val beta) .xH = radix_val beta := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp only [CompCert4Lean.Flocq.Core.Zaux.Zpower_pos,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow_pos,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      exact Int.pow_one _
    unfold CompCert4Lean.Flocq.Core.Raux.Exact.bpow
    change ctx.spec.inv (ctx.spec.ofZ
      (CompCert4Lean.Flocq.Core.Zaux.Zpower_pos (radix_val beta) .xH)) = _
    rw [hp]
  rw [hpow]
  exact hcoef

private theorem round_odd_upper_same_exp_aux
    (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (fexp : Z → Z) (hvalid : Valid_exp fexp)
    (x : R ctx) (d u : float beta)
    (hd : Rnd_DN_pt ctx (generic_format ctx magnitude beta fexp) x (F2R ctx d))
    (hdcanon : canonical ctx magnitude beta fexp d)
    (hu : Rnd_UP_pt ctx (generic_format ctx magnitude beta fexp) x (F2R ctx u))
    (hucanon : canonical ctx magnitude beta fexp u)
    (hdpos : Rlt ctx (R0 ctx) (F2R ctx d)) :
    ∃ u' : float beta, F2R ctx u' = F2R ctx u ∧ Fexp u' = Fexp d := by
  let md := mag_val ctx magnitude beta (F2R ctx d)
  let B := bpow ctx beta md
  let dn : float beta := Float beta (Zadd (Fnum d) Zone) (Fexp d)
  have hdne : F2R ctx d ≠ R0 ctx := by
    intro hzero
    rw [hzero] at hdpos
    exact (ctx.certificate.orderedField.lt_irrefl _ hdpos).elim
  have hdle0 : Rle ctx (R0 ctx) (F2R ctx d) :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hdpos |>.1
  have habsd := round_odd_abs_of_nonneg_aux ctx (F2R ctx d) hdle0
  have hdbounds := (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta
    (F2R ctx d)).mag_bound hdne
  change Rle ctx (bpow ctx beta (Zsub md Zone)) (ctx.spec.abs (F2R ctx d)) ∧
    Rlt ctx (ctx.spec.abs (F2R ctx d)) B at hdbounds
  rw [habsd] at hdbounds
  have hnum : Zlt CompCert4Lean.Flocq.Core.Zaux.Z0 (Fnum d) := by
    cases d with
    | Float dm de =>
        exact CompCert4Lean.Flocq.Core.Float_prop.gt_0_F2R ctx beta dm de hdpos
  have hddn : Rlt ctx (F2R ctx d) (F2R ctx dn) := by
    cases d with
    | Float dm de =>
        apply CompCert4Lean.Flocq.Core.Float_prop.F2R_lt ctx beta de dm
          (Zadd dm Zone)
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ dm <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd dm Zone)
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ dm <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ dm + 1
        omega
  have hdnB : Rle ctx (F2R ctx dn) B := by
    exact CompCert4Lean.Flocq.Core.Float_prop.F2R_p1_le_bpow ctx beta
      (Fnum d) (Fexp d) md hnum hdbounds.2
  have hdnpos : Rlt ctx (R0 ctx) (F2R ctx dn) :=
    ctx.certificate.orderedField.lt_trans _ _ _ hdpos hddn
  have hformatB : generic_format ctx magnitude beta fexp B := by
    exact round_odd_format_bpow_at_mag_aux ctx magnitude beta fexp hvalid
      d hdpos hdcanon
  have hformatdn : generic_format ctx magnitude beta fexp (F2R ctx dn) := by
    rcases ctx.certificate.total_order (F2R ctx dn) B with h | h
    · rcases h with hlt | heq
      · have hlow : Rle ctx (bpow ctx beta (Zsub md Zone)) (F2R ctx dn) :=
          ctx.certificate.orderedField.le_trans _ _ _ hdbounds.1
            ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hddn).1
        have hmagdn := round_odd_mag_eq_of_pos_bounds_aux ctx magnitude beta
          (F2R ctx dn) md hdnpos ⟨hlow, hlt⟩
        apply CompCert4Lean.Flocq.Core.Generic_fmt.generic_format_canonical
          ctx magnitude beta fexp dn
        unfold CompCert4Lean.Flocq.Core.Generic_fmt.Exact.canonical
        change Fexp dn = fexp (mag_val ctx magnitude beta (F2R ctx dn))
        rw [hmagdn]
        change Fexp d = fexp md
        exact hdcanon
      · rw [heq]
        exact hformatB
    · have hnot := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.2
      exact (hnot hdnB).elim
  have hxdn : Rle ctx x (F2R ctx dn) := by
    rcases ctx.certificate.total_order x (F2R ctx dn) with h | h
    · rcases h with hlt | heq
      · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt |>.1
      · rw [heq]
        exact ctx.certificate.orderedField.le_refl _
    · have hdnd := hd.2.2 (F2R ctx dn) hformatdn
          ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h).1
      exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hddn).2 hdnd |>.elim
  have hudn : Rle ctx (F2R ctx u) (F2R ctx dn) := hu.2.2 _ hformatdn hxdn
  have hdu : Rle ctx (F2R ctx d) (F2R ctx u) :=
    ctx.certificate.orderedField.le_trans _ _ _ hd.2.1 hu.2.1
  rcases ctx.certificate.total_order (F2R ctx d) (F2R ctx u) with h | h
  · rcases h with hlt | heq
    · have hdnu : Rle ctx (F2R ctx dn) (F2R ctx u) := by
        rcases ctx.certificate.total_order (F2R ctx u) B with huB | hBu
        · rcases huB with huBlt | huBeq
          · have hupos : Rlt ctx (R0 ctx) (F2R ctx u) :=
              ctx.certificate.orderedField.lt_trans _ _ _ hdpos hlt
            have hlow : Rle ctx (bpow ctx beta (Zsub md Zone)) (F2R ctx u) :=
              ctx.certificate.orderedField.le_trans _ _ _ hdbounds.1 hdu
            have hmagu := round_odd_mag_eq_of_pos_bounds_aux ctx magnitude beta
              (F2R ctx u) md hupos ⟨hlow, huBlt⟩
            have hexp : Fexp u = Fexp d := by
              calc
                Fexp u = fexp (mag_val ctx magnitude beta (F2R ctx u)) := hucanon
                _ = fexp md := congrArg fexp hmagu
                _ = Fexp d := hdcanon.symm
            cases d with
            | Float dm de =>
              cases u with
              | Float um ue =>
                change ue = de at hexp
                subst ue
                have hmdu := CompCert4Lean.Flocq.Core.Float_prop.lt_F2R
                  ctx beta de dm um hlt
                have hmle : Zle (Zadd dm Zone) um := by
                  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd dm Zone) ≤
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ um
                  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
                  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ dm + 1 ≤
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ um
                  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ dm <
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ um at hmdu
                  omega
                exact CompCert4Lean.Flocq.Core.Float_prop.F2R_le ctx beta
                  (Zadd dm Zone) um de hmle
          · rw [huBeq]
            exact hdnB
        · have hnot := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hBu |>.2
          have huB : Rle ctx (F2R ctx u) B :=
            ctx.certificate.orderedField.le_trans _ _ _ hudn hdnB
          exact (hnot huB).elim
      have hueq := ctx.certificate.orderedField.le_antisymm _ _ hudn hdnu
      refine ⟨dn, hueq.symm, ?_⟩
      rfl
    · refine ⟨d, heq, rfl⟩
  · have hnot := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.2
    exact (hnot hdu).elim

private theorem round_odd_positive_midpoint_float_aux
    (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (hbeta : Zeven (radix_val beta) = true)
    (fexp : Z → Z) (hvalid : Valid_exp fexp)
    (x : R ctx) (d u : float beta)
    (hd : Rnd_DN_pt ctx (generic_format ctx magnitude beta fexp) x (F2R ctx d))
    (hdcanon : canonical ctx magnitude beta fexp d)
    (hu : Rnd_UP_pt ctx (generic_format ctx magnitude beta fexp) x (F2R ctx u))
    (hucanon : canonical ctx magnitude beta fexp u)
    (hdpos : Rlt ctx (R0 ctx) (F2R ctx d)) :
    ∃ g : float beta,
      F2R ctx g = Rdiv ctx (Rplus ctx (F2R ctx d) (F2R ctx u)) (Rtwo ctx) ∧
      Fexp g = Zsub (fexp (mag_val ctx magnitude beta x)) Zone := by
  obtain ⟨u', hu'value, hu'exp⟩ := round_odd_upper_same_exp_aux
    ctx magnitude beta fexp hvalid x d u hd hdcanon hu hucanon hdpos
  obtain ⟨b, hb⟩ := CompCert4Lean.Flocq.Core.Zaux.Zeven_ex (radix_val beta)
  have hb' : radix_val beta = CompCert4Lean.Flocq.Core.Zaux.Zadd
      (CompCert4Lean.Flocq.Core.Zaux.Zmul Ztwo b)
      CompCert4Lean.Flocq.Core.Zaux.Z0 := by
    simpa [hbeta] using hb
  let half : float beta :=
    Float beta b (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg .xH)
  let s : float beta := CompCert4Lean.Flocq.Calc.Operations.Fplus d u'
  let g : float beta := CompCert4Lean.Flocq.Calc.Operations.Fmult half s
  refine ⟨g, ?_, ?_⟩
  · have hmul := CompCert4Lean.Flocq.Calc.Operations.F2R_mult ctx beta half s
    have hplus := CompCert4Lean.Flocq.Calc.Operations.F2R_plus ctx beta d u'
    have hplus' : F2R ctx s = Rplus ctx (F2R ctx d) (F2R ctx u') := by
      exact hplus
    have hhalf := round_odd_half_coefficient_aux ctx beta b hb'
    calc
      F2R ctx g = Rmult ctx (F2R ctx half) (F2R ctx s) := hmul
      _ = Rmult ctx (ctx.spec.inv (Rtwo ctx))
          (Rplus ctx (F2R ctx d) (F2R ctx u')) := by rw [hhalf, hplus']
      _ = Rmult ctx (ctx.spec.inv (Rtwo ctx))
          (Rplus ctx (F2R ctx d) (F2R ctx u)) := by rw [hu'value]
      _ = Rdiv ctx (Rplus ctx (F2R ctx d) (F2R ctx u)) (Rtwo ctx) := by
        change ctx.spec.mul (ctx.spec.inv (Rtwo ctx))
            (ctx.spec.add (F2R ctx d) (F2R ctx u)) =
          ctx.spec.div (ctx.spec.add (F2R ctx d) (F2R ctx u)) (Rtwo ctx)
        rw [ctx.certificate.orderedField.div_eq_mul_inv,
          ctx.certificate.orderedField.mul_comm]
  · have hs := CompCert4Lean.Flocq.Calc.Operations.Fexp_Fplus beta d u'
    have hmin : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.min
        (Fexp d) (Fexp u') = Fexp d := by
      rw [hu'exp]
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.min]
    have hsexp : Fexp s = Fexp d := by
      exact hs.trans hmin
    have hdxmag := round_odd_mag_d_aux ctx magnitude beta fexp hvalid
      x d hd hdcanon hdpos
    have hdexp : Fexp d = fexp (mag_val ctx magnitude beta x) := by
      calc
        Fexp d = fexp (mag_val ctx magnitude beta (F2R ctx d)) := hdcanon
        _ = fexp (mag_val ctx magnitude beta x) := congrArg fexp hdxmag
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg .xH) (Fexp s) = _
    rw [hsexp, hdexp]
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change (-1 : Int) + CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (fexp (mag_val ctx magnitude beta x)) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (fexp (mag_val ctx magnitude beta x)) - 1
    omega

private theorem round_odd_zero_midpoint_data_aux
    (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (hbeta : Zeven (radix_val beta) = true)
    (fexp : Z → Z) (hvalid : Valid_exp fexp) (hne : Exists_NE beta fexp)
    (x : R ctx) (d u : float beta)
    (hd : Rnd_DN_pt ctx (generic_format ctx magnitude beta fexp) x (F2R ctx d))
    (hu : Rnd_UP_pt ctx (generic_format ctx magnitude beta fexp) x (F2R ctx u))
    (hucanon : canonical ctx magnitude beta fexp u)
    (hxpos : Rlt ctx (R0 ctx) x) (hd0 : R0 ctx = F2R ctx d) :
    ∃ g : float beta,
      F2R ctx g = Rdiv ctx (Rplus ctx (F2R ctx d) (F2R ctx u)) (Rtwo ctx) ∧
      mag_val ctx magnitude beta
          (Rdiv ctx (Rplus ctx (F2R ctx d) (F2R ctx u)) (Rtwo ctx)) =
        fexp (mag_val ctx magnitude beta x) ∧
      fexp (fexp (mag_val ctx magnitude beta x)) =
        fexp (mag_val ctx magnitude beta x) ∧
      Fexp g = Zsub (fexp (mag_val ctx magnitude beta x)) Zone := by
  let ex := mag_val ctx magnitude beta x
  let E := fexp ex
  have hxne : x ≠ R0 ctx := by
    intro hzero
    rw [hzero] at hxpos
    exact (ctx.certificate.orderedField.lt_irrefl _ hxpos).elim
  have hxle0 : Rle ctx (R0 ctx) x :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxpos |>.1
  have habsx := round_odd_abs_of_nonneg_aux ctx x hxle0
  have hxbounds := (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_bound hxne
  change Rle ctx (bpow ctx beta (Zsub ex Zone)) (ctx.spec.abs x) ∧
    Rlt ctx (ctx.spec.abs x) (bpow ctx beta ex) at hxbounds
  rw [habsx] at hxbounds
  have hexE : Zle ex E := by
    by_cases hle : Zle ex E
    · exact hle
    · have hEe : Zle E (Zsub ex Zone) := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ E ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub ex Zone)
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ E ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex - 1
        change ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ ex ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ E at hle
        omega
      let L := bpow ctx beta (Zsub ex Zone)
      have hformatL : generic_format ctx magnitude beta fexp L := by
        apply round_odd_generic_format_F2R_aux ctx magnitude beta fexp L
          (Float beta Zone (Zsub ex Zone))
        · exact CompCert4Lean.Flocq.Core.Float_prop.F2R_bpow ctx beta
            (Zsub ex Zone)
        · intro _
          change Zle
            (fexp (mag_val ctx magnitude beta (bpow ctx beta (Zsub ex Zone))))
            (Zsub ex Zone)
          rw [round_odd_mag_bpow_aux ctx magnitude beta (Zsub ex Zone)]
          have hsum : Zadd (Zsub ex Zone) Zone = ex := by
            apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
            simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
            omega
          rw [hsum]
          exact hEe
      have hLd := hd.2.2 L hformatL hxbounds.1
      have hL0 : Rle ctx L (R0 ctx) := by
        rw [hd0]
        exact hLd
      have hLpos := CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta (Zsub ex Zone)
      exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hLpos).2 hL0 |>.elim
  have hne_law : ∀ e : Z,
      (Zlt (fexp e) e → Zlt (fexp (Zadd e Zone)) e) ∧
      (Zle e (fexp e) → fexp (Zadd (fexp e) Zone) = fexp e) := by
    rcases hne.exists_NE with hodd | hlaw
    · change Zeven (radix_val beta) = false at hodd
      rw [hbeta] at hodd
      exact Bool.noConfusion hodd
    · exact hlaw
  have hfix : fexp (Zadd E Zone) = E := by
    change fexp (Zadd (fexp ex) Zone) = fexp ex
    exact (hne_law ex).2 hexE
  have hplateau : ∀ l : Z, Zle l E → fexp l = E := by
    intro l hl
    exact ((hvalid.valid_exp ex).2 hexE).2 l hl
  let B := bpow ctx beta E
  have hformatB : generic_format ctx magnitude beta fexp B := by
    apply round_odd_generic_format_F2R_aux ctx magnitude beta fexp B
      (Float beta Zone E)
    · exact CompCert4Lean.Flocq.Core.Float_prop.F2R_bpow ctx beta E
    · intro _
      change Zle (fexp (mag_val ctx magnitude beta (bpow ctx beta E))) E
      rw [round_odd_mag_bpow_aux ctx magnitude beta E, hfix]
      exact Int.le_refl _
  have hxB : Rlt ctx x B := by
    have heB := round_odd_bpow_le_aux ctx beta hexE
    exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
      ctx _ _ _ hxbounds.2 heB
  have hxBle : Rle ctx x B :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxB |>.1
  have huB : Rle ctx (F2R ctx u) B := hu.2.2 B hformatB hxBle
  have hupos : Rlt ctx (R0 ctx) (F2R ctx u) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
      ctx _ _ _ hxpos hu.2.1
  have hu_eq_B : F2R ctx u = B := by
    rcases ctx.certificate.total_order (F2R ctx u) B with h | h
    · rcases h with hlt | heq
      · let eu := mag_val ctx magnitude beta (F2R ctx u)
        have hune : F2R ctx u ≠ R0 ctx := by
          intro hzero
          rw [hzero] at hupos
          exact (ctx.certificate.orderedField.lt_irrefl _ hupos).elim
        have hule0 : Rle ctx (R0 ctx) (F2R ctx u) :=
          (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hupos |>.1
        have habsu := round_odd_abs_of_nonneg_aux ctx (F2R ctx u) hule0
        have hubounds := (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta
          (F2R ctx u)).mag_bound hune
        change Rle ctx (bpow ctx beta (Zsub eu Zone)) (ctx.spec.abs (F2R ctx u)) ∧
          Rlt ctx (ctx.spec.abs (F2R ctx u)) (bpow ctx beta eu) at hubounds
        rw [habsu] at hubounds
        have heuE : Zle eu E := by
          by_cases hle : Zle eu E
          · exact hle
          · have hEeu : Zle E (Zsub eu Zone) := by
              change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ E ≤
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub eu Zone)
              simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
              change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ E ≤
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ eu - 1
              change ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ eu ≤
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ E at hle
              omega
            have hp := round_odd_bpow_le_aux ctx beta hEeu
            have hBu := ctx.certificate.orderedField.le_trans _ _ _ hp hubounds.1
            exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt).2 hBu |>.elim
        have huexp : Fexp u = E := by
          calc
            Fexp u = fexp eu := hucanon
            _ = E := hplateau eu heuE
        have hunum : Zlt CompCert4Lean.Flocq.Core.Zaux.Z0 (Fnum u) := by
          cases u with
          | Float um ue =>
              exact CompCert4Lean.Flocq.Core.Float_prop.gt_0_F2R ctx beta um ue hupos
        have hBu : Rle ctx B (F2R ctx u) := by
          cases u with
          | Float um ue =>
              change ue = E at huexp
              subst ue
              exact CompCert4Lean.Flocq.Core.Float_prop.bpow_le_F2R
                ctx beta um E hunum
        exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hlt).2 hBu |>.elim
      · exact heq
    · have hnot := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.2
      exact (hnot huB).elim
  have hmag_u : mag_val ctx magnitude beta (F2R ctx u) = Zadd E Zone := by
    rw [hu_eq_B]
    exact round_odd_mag_bpow_aux ctx magnitude beta E
  let M := Rdiv ctx (Rplus ctx (F2R ctx d) (F2R ctx u)) (Rtwo ctx)
  have hM : M = ctx.spec.mul (ctx.spec.inv (Rtwo ctx)) B := by
    change ctx.spec.div (ctx.spec.add (F2R ctx d) (F2R ctx u)) (Rtwo ctx) = _
    change ctx.spec.zero = F2R ctx d at hd0
    rw [← hd0, hu_eq_B, ctx.certificate.orderedField.zero_add,
      ctx.certificate.orderedField.div_eq_mul_inv,
      ctx.certificate.orderedField.mul_comm]
  have htwo_pos : Rlt ctx (R0 ctx) (Rtwo ctx) := by
    have h := ctx.certificate.orderedField.add_lt_compat_l ctx.spec.one
      ctx.spec.zero ctx.spec.one (round_odd_zero_lt_one ctx)
    rw [ctx.certificate.orderedField.add_zero] at h
    exact ctx.certificate.orderedField.lt_trans _ _ _
      (round_odd_zero_lt_one ctx) h
  have htwo_ne : Rtwo ctx ≠ R0 ctx := by
    intro hzero
    rw [hzero] at htwo_pos
    exact (ctx.certificate.orderedField.lt_irrefl _ htwo_pos).elim
  have hinvpos :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rinv_0_lt_compat
      ctx (Rtwo ctx) (by
        change ctx.spec.lt (ctx.spec.ofZ CompCert4Lean.Flocq.Core.Zaux.Z0) (Rtwo ctx)
        rw [ctx.certificate.sourceLaws.ofZ_zero]
        exact htwo_pos)
  have hMpos : Rlt ctx (R0 ctx) M := by
    rw [hM]
    have hBpos := CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta E
    have hinvpos' : ctx.spec.lt ctx.spec.zero (ctx.spec.inv (Rtwo ctx)) := by
      change ctx.spec.lt (ctx.spec.ofZ CompCert4Lean.Flocq.Core.Zaux.Z0)
        (ctx.spec.inv (Rtwo ctx)) at hinvpos
      rw [ctx.certificate.sourceLaws.ofZ_zero] at hinvpos
      exact hinvpos
    have hm := ctx.certificate.orderedField.mul_lt_compat_l B
      ctx.spec.zero (ctx.spec.inv (Rtwo ctx)) hBpos hinvpos'
    rw [ctx.certificate.orderedField.mul_zero,
      ctx.certificate.orderedField.mul_comm B] at hm
    exact hm
  obtain ⟨b, hb⟩ := CompCert4Lean.Flocq.Core.Zaux.Zeven_ex (radix_val beta)
  have hb' : radix_val beta = CompCert4Lean.Flocq.Core.Zaux.Zadd
      (CompCert4Lean.Flocq.Core.Zaux.Zmul Ztwo b)
      CompCert4Lean.Flocq.Core.Zaux.Z0 := by
    simpa [hbeta] using hb
  have hbpos : Zlt CompCert4Lean.Flocq.Core.Zaux.Z0 b := by
    change (0 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b
    have hr := CompCert4Lean.Flocq.Core.Zaux.radix_gt_0 beta
    change (0 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (radix_val beta) at hr
    have hbint := congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hb'
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hbint
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (radix_val beta) =
      2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b + 0 at hbint
    omega
  let half : float beta :=
    Float beta b (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg .xH)
  let oneE : float beta := Float beta Zone E
  let prod : float beta := CompCert4Lean.Flocq.Calc.Operations.Fmult half oneE
  have hprod_shape : prod = Float beta b (Zsub E Zone) := by
    have hm : CompCert4Lean.Flocq.Core.Zaux.Zmul b Zone = b := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b * 1 =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b
      omega
    have he : CompCert4Lean.Flocq.Core.Zaux.Zadd
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zneg .xH) E = Zsub E Zone := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      change (-1 : Int) + CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ E =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ E - 1
      omega
    simp [prod, half, oneE, CompCert4Lean.Flocq.Calc.Operations.Fmult, hm, he]
  have hprod_value : F2R ctx prod = ctx.spec.mul (ctx.spec.inv (Rtwo ctx)) B := by
    have hmul := CompCert4Lean.Flocq.Calc.Operations.F2R_mult ctx beta half oneE
    have hhalf := round_odd_half_coefficient_aux ctx beta b hb'
    have honeE := CompCert4Lean.Flocq.Core.Float_prop.F2R_bpow ctx beta E
    have honeE' : F2R ctx oneE = B := by
      exact honeE
    calc
      F2R ctx prod = Rmult ctx (F2R ctx half) (F2R ctx oneE) := hmul
      _ = ctx.spec.mul (ctx.spec.inv (Rtwo ctx)) B := by
        change ctx.spec.mul (F2R ctx half) (F2R ctx oneE) = _
        rw [hhalf, honeE']
  have hMlow : Rle ctx (bpow ctx beta (Zsub E Zone)) M := by
    have hp := CompCert4Lean.Flocq.Core.Float_prop.bpow_le_F2R ctx beta
      b (Zsub E Zone) hbpos
    have hprodlow : Rle ctx (bpow ctx beta (Zsub E Zone)) (F2R ctx prod) := by
      rw [hprod_shape]
      exact hp
    rw [hprod_value, ← hM] at hprodlow
    exact hprodlow
  have hone_lt_two : Rlt ctx ctx.spec.one (Rtwo ctx) := by
    have h := ctx.certificate.orderedField.add_lt_compat_l ctx.spec.one
      ctx.spec.zero ctx.spec.one (round_odd_zero_lt_one ctx)
    rw [ctx.certificate.orderedField.add_zero] at h
    exact h
  have hone_ne : ctx.spec.one ≠ ctx.spec.zero :=
    (ctx.certificate.orderedField.zero_ne_one).symm
  have hinv_one : ctx.spec.inv ctx.spec.one = ctx.spec.one := by
    have h := ctx.certificate.orderedField.inv_mul_cancel ctx.spec.one hone_ne
    rw [ctx.certificate.orderedField.mul_one] at h
    exact h
  have hone_le_two : Rle ctx ctx.spec.one (Rtwo ctx) :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hone_lt_two |>.1
  have hinv_le_one : Rle ctx (ctx.spec.inv (Rtwo ctx)) ctx.spec.one := by
    have h := CompCert4Lean.Flocq.Core.Raux.Rinv_le ctx ctx.spec.one
      (Rtwo ctx) (round_odd_zero_lt_one ctx) hone_le_two
    have h' : ctx.spec.le (ctx.spec.inv (Rtwo ctx))
        (ctx.spec.inv ctx.spec.one) := by exact h
    rw [hinv_one] at h'
    exact h'
  have hinv_ne_one : ctx.spec.inv (Rtwo ctx) ≠ ctx.spec.one := by
    intro heq
    have h := congrArg (fun z => ctx.spec.mul z (Rtwo ctx)) heq
    have hleft : ctx.spec.mul (ctx.spec.inv (Rtwo ctx)) (Rtwo ctx) =
        ctx.spec.one := ctx.certificate.orderedField.inv_mul_cancel _ htwo_ne
    have hright : ctx.spec.mul ctx.spec.one (Rtwo ctx) = Rtwo ctx :=
      ctx.certificate.orderedField.one_mul _
    rw [hleft, hright] at h
    exact ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hone_lt_two).2
      (by rw [← h]; exact ctx.certificate.orderedField.le_refl _)
  have hinv_lt_one : Rlt ctx (ctx.spec.inv (Rtwo ctx)) ctx.spec.one := by
    apply (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mpr
    refine ⟨hinv_le_one, ?_⟩
    intro honeinv
    have heq := ctx.certificate.orderedField.le_antisymm _ _ hinv_le_one honeinv
    exact hinv_ne_one heq
  have hMupper : Rlt ctx M B := by
    rw [hM]
    have hBpos := CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta E
    have h := ctx.certificate.orderedField.mul_lt_compat_l B
      (ctx.spec.inv (Rtwo ctx)) ctx.spec.one hBpos hinv_lt_one
    rw [ctx.certificate.orderedField.mul_comm B (ctx.spec.inv (Rtwo ctx)),
      ctx.certificate.orderedField.mul_one] at h
    exact h
  have hmagM : mag_val ctx magnitude beta M = E :=
    round_odd_mag_eq_of_pos_bounds_aux ctx magnitude beta M E hMpos
      ⟨hMlow, hMupper⟩
  obtain ⟨g, hgval, hgexp⟩ := m_eq_0 ctx magnitude beta hbeta fexp x d u
    hu hucanon hd0
  refine ⟨g, hgval, ?_, ?_, ?_⟩
  · exact hmagM
  · exact hplateau E (by exact Int.le_refl _)
  · rw [hmag_u, hfix] at hgexp
    exact hgexp

theorem Fm : ∀ (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx),
    FmStatement ctx magnitude := by
  intro ctx magnitude beta hbeta fexp fexpe hvalid hne hfexpe
    x d u hd hdcanon hu hucanon hxpos
  let M := Rdiv ctx (Rplus ctx (F2R ctx d) (F2R ctx u)) (Rtwo ctx)
  let f0 : float beta := Float beta CompCert4Lean.Flocq.Core.Zaux.Z0
    (cexp ctx magnitude beta fexp (R0 ctx))
  have hf0 : F2R ctx f0 = R0 ctx := by
    exact CompCert4Lean.Flocq.Core.Float_prop.F2R_0 ctx beta _
  have hformat0 : generic_format ctx magnitude beta fexp (R0 ctx) := by
    apply round_odd_generic_format_F2R_aux ctx magnitude beta fexp
      (R0 ctx) f0 hf0
    intro hne0
    exact (hne0 rfl).elim
  have hxle : Rle ctx (R0 ctx) x :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxpos |>.1
  have hdnonneg : Rle ctx (R0 ctx) (F2R ctx d) :=
    hd.2.2 (R0 ctx) hformat0 hxle
  rcases ctx.certificate.total_order (R0 ctx) (F2R ctx d) with h | h
  · rcases h with hdpos | hd0
    · obtain ⟨g, hgval, hgexp⟩ := round_odd_positive_midpoint_float_aux
        ctx magnitude beta hbeta fexp hvalid x d u hd hdcanon hu hucanon hdpos
      have hmagM := round_odd_mag_m_aux ctx magnitude beta fexp hvalid
        x d u hd hdcanon hu hdpos
      have hmagd := round_odd_mag_d_aux ctx magnitude beta fexp hvalid
        x d hd hdcanon hdpos
      change generic_format ctx magnitude beta fexpe M
      apply round_odd_generic_format_F2R_aux ctx magnitude beta fexpe M g
      · exact hgval
      · intro _
        change Zle (fexpe (mag_val ctx magnitude beta M)) (Fexp g)
        rw [hgexp, hmagM, hmagd]
        have hh := hfexpe (mag_val ctx magnitude beta x)
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (fexpe (mag_val ctx magnitude beta x)) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zsub (fexp (mag_val ctx magnitude beta x)) Ztwo) at hh
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hh
        have htwo : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = 2 := by
          decide
        rw [htwo] at hh
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (fexpe (mag_val ctx magnitude beta x)) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zsub (fexp (mag_val ctx magnitude beta x)) Zone)
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        have hone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = 1 := by
          decide
        rw [hone]
        omega
    · obtain ⟨g, hgval, hmagM, hfix, hgexp⟩ :=
        round_odd_zero_midpoint_data_aux ctx magnitude beta hbeta fexp hvalid
          hne x d u hd hu hucanon hxpos hd0
      change generic_format ctx magnitude beta fexpe M
      apply round_odd_generic_format_F2R_aux ctx magnitude beta fexpe M g
      · exact hgval
      · intro _
        change Zle (fexpe (mag_val ctx magnitude beta M)) (Fexp g)
        rw [hmagM, hgexp]
        let E := fexp (mag_val ctx magnitude beta x)
        have hh := hfexpe E
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexpe E) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub (fexp E) Ztwo) at hh
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hh
        have htwo : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = 2 := by
          decide
        rw [htwo] at hh
        have hfix' : fexp E = E := hfix
        have hfixInt := congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hfix'
        rw [hfixInt] at hh
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexpe E) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub E Zone)
        simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        have hone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = 1 := by
          decide
        rw [hone]
        omega
  · have hnot := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.2
    exact (hnot hdnonneg).elim

end CompCert4Lean.Flocq.Prop.Round_odd

namespace CompCert4Lean.Flocq.Prop.Round_odd

open CompCert4Lean.Flocq.Core

theorem Zm : ∀ (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx),
    ZmStatement ctx magnitude := by
  intro ctx magnitude beta hbeta fexp fexpe hvalid hne hfexpe
    x d u hd hdcanon hu hucanon hxpos
  let M := Rdiv ctx (Rplus ctx (F2R ctx d) (F2R ctx u)) (Rtwo ctx)
  let f0 : float beta := Float beta CompCert4Lean.Flocq.Core.Zaux.Z0
    (cexp ctx magnitude beta fexp (R0 ctx))
  have hf0 : F2R ctx f0 = R0 ctx := by
    exact CompCert4Lean.Flocq.Core.Float_prop.F2R_0 ctx beta _
  have hformat0 : generic_format ctx magnitude beta fexp (R0 ctx) := by
    apply round_odd_generic_format_F2R_aux ctx magnitude beta fexp
      (R0 ctx) f0 hf0
    intro hne0
    exact (hne0 rfl).elim
  have hxle : Rle ctx (R0 ctx) x :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hxpos |>.1
  have hdnonneg : Rle ctx (R0 ctx) (F2R ctx d) :=
    hd.2.2 (R0 ctx) hformat0 hxle
  rcases ctx.certificate.total_order (R0 ctx) (F2R ctx d) with h | h
  · rcases h with hdpos | hd0
    · obtain ⟨g, hgval, hgexp⟩ := round_odd_positive_midpoint_float_aux
        ctx magnitude beta hbeta fexp hvalid x d u hd hdcanon hu hucanon hdpos
      have hmagM := round_odd_mag_m_aux ctx magnitude beta fexp hvalid
        x d u hd hdcanon hu hdpos
      have hmagd := round_odd_mag_d_aux ctx magnitude beta fexp hvalid
        x d hd hdcanon hdpos
      apply exists_even_fexp_lt ctx magnitude beta hbeta fexpe M
      refine ⟨g, hgval, ?_⟩
      rw [hgexp, hmagM, hmagd]
      have hh := hfexpe (mag_val ctx magnitude beta x)
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (fexpe (mag_val ctx magnitude beta x)) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Zsub (fexp (mag_val ctx magnitude beta x)) Ztwo) at hh
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (fexpe (mag_val ctx magnitude beta x)) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Zsub (fexp (mag_val ctx magnitude beta x)) Zone)
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hh ⊢
      have htwo : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = 2 := by
        decide
      have hone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = 1 := by
        decide
      rw [htwo] at hh
      rw [hone]
      omega
    · obtain ⟨g, hgval, hmagM, hfix, hgexp⟩ :=
        round_odd_zero_midpoint_data_aux ctx magnitude beta hbeta fexp hvalid
          hne x d u hd hu hucanon hxpos hd0
      apply exists_even_fexp_lt ctx magnitude beta hbeta fexpe M
      refine ⟨g, hgval, ?_⟩
      rw [hmagM, hgexp]
      let E := fexp (mag_val ctx magnitude beta x)
      have hh := hfexpe E
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexpe E) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub (fexp E) Ztwo) at hh
      have hfix' : fexp E = E := hfix
      have hfixInt := congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hfix'
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (fexpe E) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub E Zone)
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hh ⊢
      have htwo : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Ztwo = 2 := by
        decide
      have hone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = 1 := by
        decide
      rw [htwo, hfixInt] at hh
      rw [hone]
      omega
  · have hnot := (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.2
    exact (hnot hdnonneg).elim

end CompCert4Lean.Flocq.Prop.Round_odd

namespace CompCert4Lean.Flocq.Prop.Round_odd

open CompCert4Lean.Flocq.Core

private theorem round_odd_add_left_cancel_eq_aux (ctx : ExactRealContext)
    (a b c : R ctx) (h : Rplus ctx a b = Rplus ctx a c) : b = c := by
  change ctx.spec.add a b = ctx.spec.add a c at h
  change b = c
  calc
    b = ctx.spec.add ctx.spec.zero b :=
      (ctx.certificate.orderedField.zero_add b).symm
    _ = ctx.spec.add (ctx.spec.add (ctx.spec.neg a) a) b := by
      rw [ctx.certificate.orderedField.neg_add_cancel]
    _ = ctx.spec.add (ctx.spec.neg a) (ctx.spec.add a b) := by
      rw [ctx.certificate.orderedField.add_assoc]
    _ = ctx.spec.add (ctx.spec.neg a) (ctx.spec.add a c) :=
      congrArg (ctx.spec.add (ctx.spec.neg a)) h
    _ = ctx.spec.add (ctx.spec.add (ctx.spec.neg a) a) c := by
      rw [ctx.certificate.orderedField.add_assoc]
    _ = ctx.spec.add ctx.spec.zero c := by
      rw [ctx.certificate.orderedField.neg_add_cancel]
    _ = c := ctx.certificate.orderedField.zero_add c

private theorem round_odd_Zrnd_odd_eq_aux (ctx : ExactRealContext) (x : R ctx)
    (h : x = IZR ctx (Zfloor ctx x)) :
    Zrnd_odd ctx x = Zfloor ctx x := by
  unfold Zrnd_odd
  generalize hdec :
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Req_EM_T
      ctx x (IZR ctx (Zfloor ctx x)) = dec
  cases dec with
  | left _ => rfl
  | right hne => exact (hne h).elim

private theorem round_odd_Zrnd_odd_ne_even_aux (ctx : ExactRealContext) (x : R ctx)
    (hne : x ≠ IZR ctx (Zfloor ctx x)) (heven : Zeven (Zfloor ctx x) = true) :
    Zrnd_odd ctx x = Zceil ctx x := by
  unfold Zrnd_odd
  generalize hdec :
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Req_EM_T
      ctx x (IZR ctx (Zfloor ctx x)) = dec
  cases dec with
  | left heq => exact (hne heq).elim
  | right _ => rw [heven]; simp

private theorem round_odd_Zrnd_odd_ne_odd_aux (ctx : ExactRealContext) (x : R ctx)
    (hne : x ≠ IZR ctx (Zfloor ctx x)) (hodd : Zeven (Zfloor ctx x) = false) :
    Zrnd_odd ctx x = Zfloor ctx x := by
  unfold Zrnd_odd
  generalize hdec :
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Req_EM_T
      ctx x (IZR ctx (Zfloor ctx x)) = dec
  cases dec with
  | left heq => exact (hne heq).elim
  | right _ => rw [hodd]; simp

private theorem round_odd_Zrnd_odd_add_integer_aux (ctx : ExactRealContext)
    (k : Z) (y : R ctx) (hk : Zeven k = true) :
    IZR ctx (Zrnd_odd ctx (Rplus ctx (IZR ctx k) y)) =
      Rplus ctx (IZR ctx k) (IZR ctx (Zrnd_odd ctx y)) := by
  have hfloor := Zfloor_plus ctx k y
  have hceil := Zceil_plus ctx k y
  have heven_sum : Zeven (Zadd k (Zfloor ctx y)) = Zeven (Zfloor ctx y) := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add k
          (Zfloor ctx y)) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even (Zfloor ctx y)
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even k = true at hk
    rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even_add, hk]
    simp [CompCert4Lean.Foundation.Logic.Rocq.Coq.Bool.Bool.eqb]
  by_cases hy : y = IZR ctx (Zfloor ctx y)
  · have hsum : Rplus ctx (IZR ctx k) y =
        IZR ctx (Zfloor ctx (Rplus ctx (IZR ctx k) y)) := by
      rw [hfloor]
      calc
        Rplus ctx (IZR ctx k) y =
            Rplus ctx (IZR ctx k) (IZR ctx (Zfloor ctx y)) :=
          congrArg (Rplus ctx (IZR ctx k)) hy
        _ = IZR ctx (Zadd k (Zfloor ctx y)) :=
          (ctx.certificate.sourceLaws.ofZ_add k (Zfloor ctx y)).symm
    rw [round_odd_Zrnd_odd_eq_aux ctx y hy,
      round_odd_Zrnd_odd_eq_aux ctx _ hsum, hfloor]
    exact ctx.certificate.sourceLaws.ofZ_add k (Zfloor ctx y)
  · have hsum_ne : Rplus ctx (IZR ctx k) y ≠
        IZR ctx (Zfloor ctx (Rplus ctx (IZR ctx k) y)) := by
      intro hsum
      apply hy
      rw [hfloor] at hsum
      have hadd : IZR ctx (Zadd k (Zfloor ctx y)) =
          Rplus ctx (IZR ctx k) (IZR ctx (Zfloor ctx y)) :=
        ctx.certificate.sourceLaws.ofZ_add k (Zfloor ctx y)
      rw [hadd] at hsum
      exact round_odd_add_left_cancel_eq_aux ctx (IZR ctx k) y
        (IZR ctx (Zfloor ctx y)) hsum
    cases heven_y : Zeven (Zfloor ctx y) with
    | false =>
        have heven_outer : Zeven
            (Zfloor ctx (Rplus ctx (IZR ctx k) y)) = false := by
          rw [hfloor, heven_sum, heven_y]
        rw [round_odd_Zrnd_odd_ne_odd_aux ctx y hy heven_y,
          round_odd_Zrnd_odd_ne_odd_aux ctx _ hsum_ne heven_outer,
          hfloor]
        exact ctx.certificate.sourceLaws.ofZ_add k (Zfloor ctx y)
    | true =>
        have heven_outer : Zeven
            (Zfloor ctx (Rplus ctx (IZR ctx k) y)) = true := by
          rw [hfloor, heven_sum, heven_y]
        rw [round_odd_Zrnd_odd_ne_even_aux ctx y hy heven_y,
          round_odd_Zrnd_odd_ne_even_aux ctx _ hsum_ne heven_outer,
          hceil]
        exact ctx.certificate.sourceLaws.ofZ_add k (Zceil ctx y)

theorem Zrnd_odd_plus' : ∀ (ctx : ExactRealContext),
    Zrnd_odd_plus'Statement ctx := by
  intro ctx beta hbeta x y hxy
  rcases hxy with ⟨n, e, rfl, he⟩
  have he0 : Zle CompCert4Lean.Flocq.Core.Zaux.Z0 e := by
    change (0 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e
    change (1 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e at he
    omega
  have hepos : Zlt CompCert4Lean.Flocq.Core.Zaux.Z0 e := by
    change (0 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e
    change (1 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e at he
    omega
  let p := CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) e
  have hpvalue : IZR ctx p = bpow ctx beta e := by
    exact CompCert4Lean.Flocq.Core.Raux.IZR_Zpower ctx beta e he0
  have hpeven : Zeven p = true := by
    exact round_odd_even_zpower_of_even beta e hepos hbeta
  let k := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul n p
  have hkeven : Zeven k = true := by
    exact round_odd_even_mul_right n p hpeven
  have hxvalue : Rmult ctx (IZR ctx n) (bpow ctx beta e) = IZR ctx k := by
    have hmul := CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.mult_IZR
      ctx n p
    change IZR ctx k = Rmult ctx (IZR ctx n) (IZR ctx p) at hmul
    rw [hpvalue] at hmul
    exact hmul.symm
  rw [hxvalue]
  exact round_odd_Zrnd_odd_add_integer_aux ctx k y hkeven

end CompCert4Lean.Flocq.Prop.Round_odd

namespace CompCert4Lean.Flocq.Prop.Round_odd

open CompCert4Lean.Flocq.Core

private theorem round_odd_zrnd_between_aux (ctx : ExactRealContext)
    (r : R ctx) (lo hi : Z)
    (hlo : Rle ctx (IZR ctx lo) r)
    (hhi : Rlt ctx r (IZR ctx hi))
    (heven_hi : Zeven hi = true) :
    Zle lo (Zrnd_odd ctx r) ∧ Zlt (Zrnd_odd ctx r) hi := by
  have hhi_le : Rle ctx r (IZR ctx hi) :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hhi |>.1
  unfold Zrnd_odd
  generalize hdec :
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Req_EM_T
      ctx r (IZR ctx (Zfloor ctx r)) = dec
  cases dec with
  | left heq =>
      constructor
      · exact CompCert4Lean.Flocq.Core.Raux.Zfloor_lub ctx lo r hlo
      · have hle := CompCert4Lean.Flocq.Core.Raux.Zceil_glb ctx hi r hhi_le
        rw [heq, CompCert4Lean.Flocq.Core.Raux.Zceil_IZR] at hle
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zfloor ctx r) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hi
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zfloor ctx r) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hi at hle
        rcases Int.lt_or_eq_of_le hle with hlt | heqz
        · exact hlt
        · have hz : Zfloor ctx r = hi :=
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective heqz
          rw [hz] at heq
          rw [← heq] at hhi
          exact (ctx.certificate.orderedField.lt_irrefl _ hhi).elim
  | right hne =>
      have hceil : Zceil ctx r = Zadd (Zfloor ctx r) Zone :=
        CompCert4Lean.Flocq.Core.Raux.Zceil_floor_neq ctx r (Ne.symm hne)
      have hlo_floor := CompCert4Lean.Flocq.Core.Raux.Zfloor_lub ctx lo r hlo
      have hceil_hi := CompCert4Lean.Flocq.Core.Raux.Zceil_glb ctx hi r hhi_le
      have hceil_int : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Zceil ctx r) =
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zfloor ctx r) + 1 := by
        rw [hceil]
        simp only [Zadd,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        have hzone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = 1 := by
          decide
        rw [hzone]
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ lo ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zfloor ctx r) at hlo_floor
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zceil ctx r) ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hi at hceil_hi
      cases heven_floor : Zeven (Zfloor ctx r) with
      | false =>
          constructor
          · exact hlo_floor
          · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (Zfloor ctx r) <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hi
            omega
      | true =>
          have hodd_ceil : Zeven (Zceil ctx r) = false := by
            rw [hceil]
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
                  (Zfloor ctx r) Zone) = false
            rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even_add]
            change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
                (Zfloor ctx r) = true at heven_floor
            rw [heven_floor]
            rfl
          have hne_int : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Zceil ctx r) ≠
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hi := by
            intro heqz
            have hz : Zceil ctx r = hi :=
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective heqz
            rw [hz, heven_hi] at hodd_ceil
            contradiction
          constructor
          · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ lo ≤
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zceil ctx r)
            omega
          · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                (Zceil ctx r) <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hi
            omega

private theorem round_odd_scaled_mantissa_upper_aux
    (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (emin prec : Z) (x : R ctx)
    (hx : Rlt ctx (R0 ctx) x) (hprec : Zlt Zone prec) :
    Rlt ctx
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
        ctx magnitude beta (FLT_exp emin prec) x)
      (IZR ctx (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) prec)) := by
  let mx := mag_val ctx magnitude beta x
  let e := FLT_exp emin prec mx
  have hxne : x ≠ R0 ctx := by
    intro hzero
    rw [hzero] at hx
    exact (ctx.certificate.orderedField.lt_irrefl _ hx).elim
  have hxle : Rle ctx (R0 ctx) x :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hx |>.1
  have habs : ctx.spec.abs x = x :=
    ctx.certificate.sourceLaws.abs_nonnegative x hxle
  have hmag :=
    (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_bound hxne
  change Rle ctx (bpow ctx beta (Zsub mx Zone)) (ctx.spec.abs x) ∧
    Rlt ctx (ctx.spec.abs x) (bpow ctx beta mx) at hmag
  rw [habs] at hmag
  have hdiff : Zle (Zsub mx prec) e := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub mx prec) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max
          (Zsub mx prec) emin)
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max]
    by_cases h : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zsub mx prec) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emin
    · rw [if_pos h]
      exact h
    · rw [if_neg h]
      exact Int.le_refl _
  have hmx_e : Zle (Zsub mx e) prec := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub mx e) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub mx prec) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e at hdiff
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hdiff ⊢
    omega
  have hp := CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e)
  have hp' : Rlt ctx (IZR ctx CompCert4Lean.Flocq.Core.Zaux.Z0)
      (bpow ctx beta
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e)) := by
    change ctx.spec.lt (ctx.spec.ofZ CompCert4Lean.Flocq.Core.Zaux.Z0) _
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hp
  have hmul :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_compat_r
      ctx
      (bpow ctx beta
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e))
      x (bpow ctx beta mx) hp' hmag.2
  have hprod := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta mx
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e)
  have hmul' : Rlt ctx
      (Rmult ctx x (bpow ctx beta
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e)))
      (bpow ctx beta (Zsub mx e)) := by
    change ctx.spec.lt
      (ctx.spec.mul x (bpow ctx beta
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e)))
      (bpow ctx beta (Zsub mx e))
    change ctx.spec.lt
      (ctx.spec.mul x (bpow ctx beta
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e)))
      (ctx.spec.mul (bpow ctx beta mx) (bpow ctx beta
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e))) at hmul
    have hsub : CompCert4Lean.Flocq.Core.Raux.Zadd mx
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e) =
        Zsub mx e := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp only [Zadd, Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      omega
    rw [hsub] at hprod
    change ctx.spec.lt
      (ctx.spec.mul x (bpow ctx beta
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e)))
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Zsub mx e))
    rw [hprod]
    exact hmul
  have hscaled : Rlt ctx
      (Rmult ctx x (bpow ctx beta
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e)))
      (bpow ctx beta prec) :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rlt_le_trans
      ctx _ _ _ hmul' (round_odd_bpow_le_aux ctx beta hmx_e)
  have hprec0 : Zle CompCert4Lean.Flocq.Core.Zaux.Z0 prec := by
    change (0 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec
    change (1 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec at hprec
    omega
  have hpvalue := CompCert4Lean.Flocq.Core.Raux.IZR_Zpower ctx beta prec hprec0
  change IZR ctx (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) prec) =
    bpow ctx beta prec at hpvalue
  rw [hpvalue]
  simpa [CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa,
    CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp, mx, e] using hscaled

private theorem round_odd_scaled_mantissa_lower_aux
    (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (emin prec : Z) (x : R ctx)
    (hx : Rlt ctx (R0 ctx) x) (hprec : Zlt Zone prec)
    (hexp : FLT_exp emin prec (mag_val ctx magnitude beta x) =
      Zsub (mag_val ctx magnitude beta x) prec) :
    Rle ctx
      (IZR ctx (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta)
        (Zsub prec Zone)))
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
        ctx magnitude beta (FLT_exp emin prec) x) := by
  let mx := mag_val ctx magnitude beta x
  let e := FLT_exp emin prec mx
  have hxne : x ≠ R0 ctx := by
    intro hzero
    rw [hzero] at hx
    exact (ctx.certificate.orderedField.lt_irrefl _ hx).elim
  have hxle : Rle ctx (R0 ctx) x :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hx |>.1
  have habs : ctx.spec.abs x = x :=
    ctx.certificate.sourceLaws.abs_nonnegative x hxle
  have hmag :=
    (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_bound hxne
  change Rle ctx (bpow ctx beta (Zsub mx Zone)) (ctx.spec.abs x) ∧
    Rlt ctx (ctx.spec.abs x) (bpow ctx beta mx) at hmag
  rw [habs] at hmag
  have hp := CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e)
  have hp_nonneg : Rle ctx (IZR ctx CompCert4Lean.Flocq.Core.Zaux.Z0)
      (bpow ctx beta
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e)) := by
    change ctx.spec.le (ctx.spec.ofZ CompCert4Lean.Flocq.Core.Zaux.Z0) _
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hp |>.1
  have hmul :=
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
      ctx
      (bpow ctx beta
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e))
      (bpow ctx beta (Zsub mx Zone)) x hp_nonneg hmag.1
  have hprod := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta
    (Zsub mx Zone)
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e)
  have hexponents : CompCert4Lean.Flocq.Core.Raux.Zadd (Zsub mx Zone)
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e) =
      Zsub prec Zone := by
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    change FLT_exp emin prec mx = Zsub mx prec at hexp
    have hexp_int : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (FLT_exp emin prec mx) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub mx prec) :=
        congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hexp
    simp only [CompCert4Lean.Flocq.Core.Raux.Zadd, Zsub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hexp_int ⊢
    dsimp [e]
    omega
  rw [hexponents] at hprod
  have hscaled : Rle ctx (bpow ctx beta (Zsub prec Zone))
      (Rmult ctx x (bpow ctx beta
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e))) := by
    change ctx.spec.le
      (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Zsub prec Zone))
      (ctx.spec.mul x (bpow ctx beta
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e)))
    rw [hprod]
    exact hmul
  have hprec_sub0 : Zle CompCert4Lean.Flocq.Core.Zaux.Z0
      (Zsub prec Zone) := by
    change (0 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (Zsub prec Zone)
    change (1 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec at hprec
    simp only [Zsub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change (0 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec - 1
    omega
  have hpvalue := CompCert4Lean.Flocq.Core.Raux.IZR_Zpower ctx beta
    (Zsub prec Zone) hprec_sub0
  change IZR ctx (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta)
      (Zsub prec Zone)) = bpow ctx beta (Zsub prec Zone) at hpvalue
  rw [hpvalue]
  simpa [CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa,
    CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp, mx, e] using hscaled

private theorem round_odd_zrnd_pos_aux (ctx : ExactRealContext) (r : R ctx)
    (hr : Rlt ctx (R0 ctx) r) :
    Zlt CompCert4Lean.Flocq.Core.Zaux.Z0 (Zrnd_odd ctx r) := by
  have hr' : Rlt ctx (IZR ctx CompCert4Lean.Flocq.Core.Zaux.Z0) r := by
    change ctx.spec.lt (ctx.spec.ofZ CompCert4Lean.Flocq.Core.Zaux.Z0) r
    rw [ctx.certificate.sourceLaws.ofZ_zero]
    exact hr
  have hrle : Rle ctx (IZR ctx CompCert4Lean.Flocq.Core.Zaux.Z0) r :=
    (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hr' |>.1
  have hfloor_nonneg := CompCert4Lean.Flocq.Core.Raux.Zfloor_lub ctx
    CompCert4Lean.Flocq.Core.Zaux.Z0 r hrle
  unfold Zrnd_odd
  generalize hdec :
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Req_EM_T
      ctx r (IZR ctx (Zfloor ctx r)) = dec
  cases dec with
  | left heq =>
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          CompCert4Lean.Flocq.Core.Zaux.Z0 <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zfloor ctx r)
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          CompCert4Lean.Flocq.Core.Zaux.Z0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zfloor ctx r) at hfloor_nonneg
      by_cases hz : Zfloor ctx r = CompCert4Lean.Flocq.Core.Zaux.Z0
      · rw [hz] at heq
        rw [← heq] at hr'
        exact (ctx.certificate.orderedField.lt_irrefl _ hr').elim
      · have hz_int : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (Zfloor ctx r) ≠
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              CompCert4Lean.Flocq.Core.Zaux.Z0 := by
          intro hz'
          exact hz (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective hz')
        omega
  | right hne =>
      cases heven : Zeven (Zfloor ctx r) with
      | false =>
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              CompCert4Lean.Flocq.Core.Zaux.Z0 <
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zfloor ctx r)
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              CompCert4Lean.Flocq.Core.Zaux.Z0 ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zfloor ctx r) at hfloor_nonneg
          have hnezero : Zfloor ctx r ≠ CompCert4Lean.Flocq.Core.Zaux.Z0 := by
            intro hz
            rw [hz] at heven
            contradiction
          have hnezero_int : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (Zfloor ctx r) ≠ 0 := by
            intro hz
            apply hnezero
            apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
            exact hz
          have hz0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              CompCert4Lean.Flocq.Core.Zaux.Z0 = 0 := rfl
          rw [hz0] at hfloor_nonneg ⊢
          omega
      | true =>
          have hceil : Zceil ctx r = Zadd (Zfloor ctx r) Zone :=
            CompCert4Lean.Flocq.Core.Raux.Zceil_floor_neq ctx r (Ne.symm hne)
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              CompCert4Lean.Flocq.Core.Zaux.Z0 <
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zceil ctx r)
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              CompCert4Lean.Flocq.Core.Zaux.Z0 ≤
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zfloor ctx r) at hfloor_nonneg
          rw [hceil]
          simp only [Zadd,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          have hzone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = 1 := by
            decide
          rw [hzone]
          omega

private theorem round_odd_fexp_pos_aux
    (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (hbeta : Zeven (radix_val beta) = true)
    (emin prec : Z) (hprec : Zlt Zone prec) (x : R ctx)
    (hx : Rlt ctx (R0 ctx) x) :
    cexp ctx magnitude beta (FLT_exp emin prec)
        (round ctx magnitude beta (FLT_exp emin prec) (Zrnd_odd ctx) x) =
      cexp ctx magnitude beta (FLT_exp emin prec) x := by
  let mx := mag_val ctx magnitude beta x
  let e := FLT_exp emin prec mx
  let s := CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
    ctx magnitude beta (FLT_exp emin prec) x
  let z := Zrnd_odd ctx s
  let y : R ctx := F2R ctx (Float beta z e)
  have hspos : Rlt ctx (R0 ctx) s := by
    have hp := CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e)
    have hx' : Rlt ctx (IZR ctx CompCert4Lean.Flocq.Core.Zaux.Z0) x := by
      change ctx.spec.lt (ctx.spec.ofZ CompCert4Lean.Flocq.Core.Zaux.Z0) x
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact hx
    have hp' : Rlt ctx (IZR ctx CompCert4Lean.Flocq.Core.Zaux.Z0)
        (bpow ctx beta
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e)) := by
      change ctx.spec.lt (ctx.spec.ofZ CompCert4Lean.Flocq.Core.Zaux.Z0) _
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact hp
    have hmul :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_0_compat
        ctx x
        (bpow ctx beta
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e))
        hx' hp'
    change Rlt ctx (R0 ctx)
      (Rmult ctx x (bpow ctx beta
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e)))
    change ctx.spec.lt ctx.spec.zero
      (ctx.spec.mul x (bpow ctx beta
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e)))
    change ctx.spec.lt (ctx.spec.ofZ CompCert4Lean.Flocq.Core.Zaux.Z0)
      (ctx.spec.mul x (bpow ctx beta
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp e))) at hmul
    rw [ctx.certificate.sourceLaws.ofZ_zero] at hmul
    simpa [s, CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa,
      CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp, mx, e] using hmul
  have hsupper := round_odd_scaled_mantissa_upper_aux
    ctx magnitude beta emin prec x hx hprec
  have hprec0 : Zlt CompCert4Lean.Flocq.Core.Zaux.Z0 prec := by
    change (0 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec
    change (1 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec at hprec
    omega
  have heven_power := round_odd_even_zpower_of_even beta prec hprec0 hbeta
  have hsnonneg : Rle ctx
      (IZR ctx CompCert4Lean.Flocq.Core.Zaux.Z0) s := by
    have hspos' : Rlt ctx (IZR ctx CompCert4Lean.Flocq.Core.Zaux.Z0) s := by
      change ctx.spec.lt (ctx.spec.ofZ CompCert4Lean.Flocq.Core.Zaux.Z0) s
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact hspos
    exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hspos' |>.1
  have hzrange := round_odd_zrnd_between_aux ctx s
    CompCert4Lean.Flocq.Core.Zaux.Z0
    (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) prec)
    hsnonneg (by simpa [s] using hsupper) heven_power
  have hzpos : Zlt CompCert4Lean.Flocq.Core.Zaux.Z0 z := by
    exact round_odd_zrnd_pos_aux ctx s hspos
  have hypos : Rlt ctx (R0 ctx) y := by
    exact CompCert4Lean.Flocq.Core.Float_prop.F2R_gt_0 ctx
      beta (Float beta z e) hzpos
  have hround : round ctx magnitude beta (FLT_exp emin prec) (Zrnd_odd ctx) x = y := by
    rfl
  rw [hround]
  by_cases hexp : e = Zsub mx prec
  · have hslower := round_odd_scaled_mantissa_lower_aux
      ctx magnitude beta emin prec x hx hprec (by simpa [mx, e] using hexp)
    have hzrange' := round_odd_zrnd_between_aux ctx s
      (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) (Zsub prec Zone))
      (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) prec)
      (by simpa [s] using hslower) (by simpa [s] using hsupper) heven_power
    have hpow_e_pos := CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta e
    have hpow_e_nonneg : Rle ctx (IZR ctx CompCert4Lean.Flocq.Core.Zaux.Z0)
        (bpow ctx beta e) := by
      change ctx.spec.le (ctx.spec.ofZ CompCert4Lean.Flocq.Core.Zaux.Z0) _
      rw [ctx.certificate.sourceLaws.ofZ_zero]
      exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hpow_e_pos |>.1
    have hlz := round_odd_izr_le ctx
      (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) (Zsub prec Zone))
      z hzrange'.1
    have huz := round_odd_izr_lt ctx z
      (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) prec) hzrange'.2
    have hlmul :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_le_compat_r
        ctx (bpow ctx beta e)
        (IZR ctx (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta)
          (Zsub prec Zone))) (IZR ctx z) hpow_e_nonneg hlz
    have humul :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_compat_r
        ctx (bpow ctx beta e) (IZR ctx z)
        (IZR ctx (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) prec))
        (by
          change ctx.spec.lt (ctx.spec.ofZ CompCert4Lean.Flocq.Core.Zaux.Z0) _
          rw [ctx.certificate.sourceLaws.ofZ_zero]
          exact hpow_e_pos) huz
    have hprec_sub0 : Zle CompCert4Lean.Flocq.Core.Zaux.Z0 (Zsub prec Zone) := by
      change (0 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zsub prec Zone)
      change (1 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec at hprec
      simp only [Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      change (0 : Int) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ prec - 1
      omega
    have hprec_nonneg : Zle CompCert4Lean.Flocq.Core.Zaux.Z0 prec := by
      exact Int.le_of_lt hprec0
    have hlpower := CompCert4Lean.Flocq.Core.Raux.IZR_Zpower ctx beta
      (Zsub prec Zone) hprec_sub0
    have hupower := CompCert4Lean.Flocq.Core.Raux.IZR_Zpower ctx beta prec hprec_nonneg
    have hlprod := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta
      (Zsub prec Zone) e
    have huprod := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta prec e
    have hlexp : CompCert4Lean.Flocq.Core.Raux.Zadd (Zsub prec Zone) e =
        Zsub mx Zone := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      have hexp_int := congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hexp
      simp only [CompCert4Lean.Flocq.Core.Raux.Zadd, Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hexp_int ⊢
      dsimp [e] at hexp_int ⊢
      omega
    have huexp : CompCert4Lean.Flocq.Core.Raux.Zadd prec e = mx := by
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      have hexp_int := congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hexp
      simp only [CompCert4Lean.Flocq.Core.Raux.Zadd, Zsub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hexp_int ⊢
      dsimp [e] at hexp_int ⊢
      omega
    rw [hlexp] at hlprod
    rw [huexp] at huprod
    have hlmul' : Rle ctx
        (Rmult ctx (bpow ctx beta (Zsub prec Zone)) (bpow ctx beta e))
        (Rmult ctx (IZR ctx z) (bpow ctx beta e)) := by
      change ctx.spec.le
        (ctx.spec.mul (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta
          (Zsub prec Zone)) (bpow ctx beta e))
        (ctx.spec.mul (IZR ctx z) (bpow ctx beta e))
      rw [← hlpower]
      exact hlmul
    have humul' : Rlt ctx
        (Rmult ctx (IZR ctx z) (bpow ctx beta e))
        (Rmult ctx (bpow ctx beta prec) (bpow ctx beta e)) := by
      change ctx.spec.lt
        (ctx.spec.mul (IZR ctx z) (bpow ctx beta e))
        (ctx.spec.mul (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta prec)
          (bpow ctx beta e))
      rw [← hupower]
      exact humul
    have hybounds : Rle ctx (bpow ctx beta (Zsub mx Zone)) y ∧
        Rlt ctx y (bpow ctx beta mx) := by
      constructor
      · change Rle ctx (bpow ctx beta (Zsub mx Zone))
          (Rmult ctx (IZR ctx z) (bpow ctx beta e))
        change ctx.spec.le
          (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta (Zsub mx Zone))
          (ctx.spec.mul (IZR ctx z) (bpow ctx beta e))
        rw [hlprod]
        exact hlmul'
      · change Rlt ctx (Rmult ctx (IZR ctx z) (bpow ctx beta e))
          (bpow ctx beta mx)
        change ctx.spec.lt (ctx.spec.mul (IZR ctx z) (bpow ctx beta e))
          (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta mx)
        rw [huprod]
        exact humul'
    have hmagy := round_odd_mag_eq_of_pos_bounds_aux
      ctx magnitude beta y mx hypos hybounds
    unfold cexp CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp
    change FLT_exp emin prec (mag_val ctx magnitude beta y) =
      FLT_exp emin prec mx
    rw [hmagy]
  · have hemin : e = emin := by
      by_cases hle : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Zsub mx prec) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emin
      · apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        dsimp [e]
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max
              (Zsub mx prec) emin) =
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emin
        simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max, hle]
      · exfalso
        apply hexp
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        dsimp [e]
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max
              (Zsub mx prec) emin) =
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub mx prec)
        simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max, hle]
    have hpow_e_pos := CompCert4Lean.Flocq.Core.Raux.bpow_gt_0 ctx beta e
    have huz := round_odd_izr_lt ctx z
      (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) prec) hzrange.2
    have humul :=
      CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rmult_lt_compat_r
        ctx (bpow ctx beta e) (IZR ctx z)
        (IZR ctx (CompCert4Lean.Flocq.Core.Zaux.Zpower (radix_val beta) prec))
        (by
          change ctx.spec.lt (ctx.spec.ofZ CompCert4Lean.Flocq.Core.Zaux.Z0) _
          rw [ctx.certificate.sourceLaws.ofZ_zero]
          exact hpow_e_pos) huz
    have hprec_nonneg : Zle CompCert4Lean.Flocq.Core.Zaux.Z0 prec :=
      Int.le_of_lt hprec0
    have hupower := CompCert4Lean.Flocq.Core.Raux.IZR_Zpower ctx beta prec hprec_nonneg
    have huprod := CompCert4Lean.Flocq.Core.Raux.bpow_plus ctx beta prec e
    have humul' : Rlt ctx
        (Rmult ctx (IZR ctx z) (bpow ctx beta e))
        (Rmult ctx (bpow ctx beta prec) (bpow ctx beta e)) := by
      change ctx.spec.lt
        (ctx.spec.mul (IZR ctx z) (bpow ctx beta e))
        (ctx.spec.mul (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta prec)
          (bpow ctx beta e))
      rw [← hupower]
      exact humul
    have hyupper : Rlt ctx y (bpow ctx beta (Zadd e prec)) := by
      change Rlt ctx (Rmult ctx (IZR ctx z) (bpow ctx beta e))
        (bpow ctx beta (Zadd e prec))
      have hcomm : Zadd e prec = CompCert4Lean.Flocq.Core.Raux.Zadd prec e := by
        apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
        simp only [Zadd, CompCert4Lean.Flocq.Core.Raux.Zadd,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        omega
      rw [hcomm]
      change ctx.spec.lt (ctx.spec.mul (IZR ctx z) (bpow ctx beta e))
        (CompCert4Lean.Flocq.Core.Raux.Exact.bpow ctx beta
          (CompCert4Lean.Flocq.Core.Raux.Zadd prec e))
      rw [huprod]
      exact humul'
    have hyne : y ≠ R0 ctx := by
      intro hzero
      rw [hzero] at hypos
      exact (ctx.certificate.orderedField.lt_irrefl _ hypos).elim
    let my := mag_val ctx magnitude beta y
    have hymag :=
      (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta y).mag_bound hyne
    have hy_nonneg : Rle ctx (R0 ctx) y :=
      (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hypos |>.1
    have hyabs : ctx.spec.abs y = y :=
      ctx.certificate.sourceLaws.abs_nonnegative y hy_nonneg
    change Rle ctx (bpow ctx beta (Zsub my Zone)) (ctx.spec.abs y) ∧
      Rlt ctx (ctx.spec.abs y) (bpow ctx beta my) at hymag
    rw [hyabs] at hymag
    have hmy : Zle my (Zadd e prec) :=
      CompCert4Lean.Flocq.Core.Raux.bpow_lt_bpow ctx beta my (Zadd e prec)
        (CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Rle_lt_trans
          ctx _ _ _ hymag.1 hyupper)
    have hsuble : Zle (Zsub my prec) emin := by
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub my prec) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emin
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ my ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd e prec) at hmy
      have hemin_int := congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hemin
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emin at hemin_int
      simp only [Zsub, Zadd,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hmy ⊢
      omega
    unfold cexp CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp
    change FLT_exp emin prec my = e
    rw [hemin]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max
      (Zsub my prec) emin = emin
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub my prec) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ emin at hsuble
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max, hsuble]

private theorem round_odd_neg_neg_aux (ctx : ExactRealContext) (x : R ctx) :
    Ropp ctx (Ropp ctx x) = x := by
  change ctx.spec.neg (ctx.spec.neg x) = x
  calc
    ctx.spec.neg (ctx.spec.neg x) =
        ctx.spec.add (ctx.spec.neg (ctx.spec.neg x)) ctx.spec.zero :=
      (ctx.certificate.orderedField.add_zero _).symm
    _ = ctx.spec.add (ctx.spec.neg (ctx.spec.neg x))
        (ctx.spec.add (ctx.spec.neg x) x) := by
      rw [ctx.certificate.orderedField.neg_add_cancel]
    _ = ctx.spec.add
        (ctx.spec.add (ctx.spec.neg (ctx.spec.neg x)) (ctx.spec.neg x)) x := by
      rw [ctx.certificate.orderedField.add_assoc]
    _ = ctx.spec.add ctx.spec.zero x := by
      rw [ctx.certificate.orderedField.neg_add_cancel]
    _ = x := ctx.certificate.orderedField.zero_add _

private theorem round_odd_neg_zero_aux (ctx : ExactRealContext) :
    Ropp ctx (R0 ctx) = R0 ctx := by
  change ctx.spec.neg ctx.spec.zero = ctx.spec.zero
  have h := ctx.certificate.orderedField.neg_add_cancel ctx.spec.zero
  rw [ctx.certificate.orderedField.add_zero] at h
  exact h

private theorem round_odd_zopp_zopp_aux (z : Z) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp z) = z := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  omega

private theorem round_odd_floor_neg_aux (ctx : ExactRealContext) (x : R ctx) :
    Zfloor ctx (Ropp ctx x) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
        (Zceil ctx x) := by
  change CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx
      (CompCert4Lean.Flocq.Core.Raux.Exact.Ropp ctx x) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
      (CompCert4Lean.Flocq.Core.Raux.Exact.Zceil ctx x)
  unfold CompCert4Lean.Flocq.Core.Raux.Exact.Zceil
  rw [round_odd_zopp_zopp_aux]

private theorem round_odd_ceil_neg_aux (ctx : ExactRealContext) (x : R ctx) :
    Zceil ctx (Ropp ctx x) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
        (Zfloor ctx x) := by
  change CompCert4Lean.Flocq.Core.Raux.Exact.Zceil ctx
      (CompCert4Lean.Flocq.Core.Raux.Exact.Ropp ctx x) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
      (CompCert4Lean.Flocq.Core.Raux.Exact.Zfloor ctx x)
  unfold CompCert4Lean.Flocq.Core.Raux.Exact.Zceil
  have hnn : CompCert4Lean.Flocq.Core.Raux.Exact.Ropp ctx
      (CompCert4Lean.Flocq.Core.Raux.Exact.Ropp ctx x) = x :=
    round_odd_neg_neg_aux ctx x
  rw [hnn]

private theorem round_odd_even_opp_aux (z : Z) :
    Zeven (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp z) =
      Zeven z := by
  change decide (Int.natAbs
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp z)) % 2 = 0) =
    decide (Int.natAbs
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z) % 2 = 0)
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  rw [Int.natAbs_neg]

private theorem round_odd_Zrnd_opp_aux (ctx : ExactRealContext) (x : R ctx) :
    Zrnd_odd ctx (Ropp ctx x) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
        (Zrnd_odd ctx x) := by
  by_cases hx : x = IZR ctx (Zfloor ctx x)
  · have hceil_izr : Zceil ctx (IZR ctx (Zfloor ctx x)) = Zfloor ctx x :=
      CompCert4Lean.Flocq.Core.Raux.Zceil_IZR ctx (Zfloor ctx x)
    have hfloor_izr : Zfloor ctx (IZR ctx (Zfloor ctx x)) = Zfloor ctx x :=
      CompCert4Lean.Flocq.Core.Raux.Zfloor_IZR ctx (Zfloor ctx x)
    have hxneg : Ropp ctx x = IZR ctx (Zfloor ctx (Ropp ctx x)) := by
      have hnegizr := ctx.certificate.sourceLaws.ofZ_neg (Zfloor ctx x)
      change IZR ctx
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
            (Zfloor ctx x)) = Ropp ctx (IZR ctx (Zfloor ctx x)) at hnegizr
      rw [round_odd_floor_neg_aux ctx x]
      rw [hx, hceil_izr]
      exact hnegizr.symm
    rw [round_odd_Zrnd_odd_eq_aux ctx x hx,
      round_odd_Zrnd_odd_eq_aux ctx (Ropp ctx x) hxneg,
      round_odd_floor_neg_aux ctx x, hx, hceil_izr, hfloor_izr]
  · have hxneg : Ropp ctx x ≠ IZR ctx (Zfloor ctx (Ropp ctx x)) := by
      intro h
      have hr : x = IZR ctx
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
            (Zfloor ctx (Ropp ctx x))) := by
        calc
          x = Ropp ctx (Ropp ctx x) := (round_odd_neg_neg_aux ctx x).symm
          _ = Ropp ctx (IZR ctx (Zfloor ctx (Ropp ctx x))) :=
            congrArg (Ropp ctx) h
          _ = IZR ctx
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
                (Zfloor ctx (Ropp ctx x))) :=
            (ctx.certificate.sourceLaws.ofZ_neg _).symm
      apply hx
      rw [hr]
      have hfloor_izr : Zfloor ctx
          (IZR ctx
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
              (Zfloor ctx (Ropp ctx x)))) =
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
            (Zfloor ctx (Ropp ctx x)) :=
        CompCert4Lean.Flocq.Core.Raux.Zfloor_IZR ctx _
      rw [hfloor_izr]
    have hceil : Zceil ctx x = Zadd (Zfloor ctx x) Zone :=
      CompCert4Lean.Flocq.Core.Raux.Zceil_floor_neq ctx x (Ne.symm hx)
    cases heven : Zeven (Zfloor ctx x) with
    | false =>
        have heven_ceil : Zeven (Zceil ctx x) = true := by
          rw [hceil]
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
                (Zfloor ctx x) Zone) = true
          rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even_add]
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
              (Zfloor ctx x) = false at heven
          rw [heven]
          rfl
        have heven_floor_neg : Zeven (Zfloor ctx (Ropp ctx x)) = true := by
          rw [round_odd_floor_neg_aux ctx x, round_odd_even_opp_aux, heven_ceil]
        rw [round_odd_Zrnd_odd_ne_odd_aux ctx x hx heven,
          round_odd_Zrnd_odd_ne_even_aux ctx (Ropp ctx x) hxneg heven_floor_neg,
          round_odd_ceil_neg_aux ctx x]
    | true =>
        have heven_ceil : Zeven (Zceil ctx x) = false := by
          rw [hceil]
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
                (Zfloor ctx x) Zone) = false
          rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even_add]
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
              (Zfloor ctx x) = true at heven
          rw [heven]
          rfl
        have heven_floor_neg : Zeven (Zfloor ctx (Ropp ctx x)) = false := by
          rw [round_odd_floor_neg_aux ctx x, round_odd_even_opp_aux, heven_ceil]
        rw [round_odd_Zrnd_odd_ne_even_aux ctx x hx heven,
          round_odd_Zrnd_odd_ne_odd_aux ctx (Ropp ctx x) hxneg heven_floor_neg,
          round_odd_floor_neg_aux ctx x]

private theorem round_odd_abs_opp_aux (ctx : ExactRealContext) (x : R ctx) :
    ctx.spec.abs (Ropp ctx x) = ctx.spec.abs x := by
  change ctx.spec.abs (ctx.spec.neg x) = ctx.spec.abs x
  rcases ctx.certificate.total_order x ctx.spec.zero with h | h
  · rcases h with hlt | heq
    · have hneg : ctx.spec.le ctx.spec.zero (ctx.spec.neg x) := by
        have hh := ctx.certificate.orderedField.add_lt_compat_l
          (ctx.spec.neg x) x ctx.spec.zero hlt
        rw [ctx.certificate.orderedField.neg_add_cancel,
          ctx.certificate.orderedField.add_zero] at hh
        exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hh |>.1
      rw [ctx.certificate.sourceLaws.abs_nonnegative _ hneg,
        ctx.certificate.sourceLaws.abs_negative x hlt]
    · subst x
      exact congrArg (fun z => ctx.spec.abs z) (round_odd_neg_zero_aux ctx)
  · have hneglt : ctx.spec.lt (ctx.spec.neg x) ctx.spec.zero := by
      have hh := ctx.certificate.orderedField.add_lt_compat_l
        (ctx.spec.neg x) ctx.spec.zero x h
      rw [ctx.certificate.orderedField.neg_add_cancel,
        ctx.certificate.orderedField.add_zero] at hh
      exact hh
    calc
      ctx.spec.abs (ctx.spec.neg x) = ctx.spec.neg (ctx.spec.neg x) :=
        ctx.certificate.sourceLaws.abs_negative _ hneglt
      _ = x := round_odd_neg_neg_aux ctx x
      _ = ctx.spec.abs x :=
        (ctx.certificate.sourceLaws.abs_nonnegative _
          ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h |>.1)).symm

private theorem round_odd_mag_opp_aux
    (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (x : R ctx) :
    mag_val ctx magnitude beta (Ropp ctx x) =
      mag_val ctx magnitude beta x := by
  by_cases hx : x = R0 ctx
  · subst x
    rw [round_odd_neg_zero_aux]
  · have hxneg : Ropp ctx x ≠ R0 ctx := by
      intro hzero
      apply hx
      calc
        x = Ropp ctx (Ropp ctx x) := (round_odd_neg_neg_aux ctx x).symm
        _ = Ropp ctx (R0 ctx) := congrArg (Ropp ctx) hzero
        _ = R0 ctx := round_odd_neg_zero_aux ctx
    have hneg :=
      (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta
        (Ropp ctx x)).mag_bound hxneg
    have hpos :=
      (CompCert4Lean.Flocq.Core.Raux.Exact.mag magnitude beta x).mag_bound hx
    have habs := round_odd_abs_opp_aux ctx x
    change Rle ctx (bpow ctx beta
        (Zsub (mag_val ctx magnitude beta (Ropp ctx x)) Zone))
        (ctx.spec.abs (Ropp ctx x)) ∧
      Rlt ctx (ctx.spec.abs (Ropp ctx x))
        (bpow ctx beta (mag_val ctx magnitude beta (Ropp ctx x))) at hneg
    change Rle ctx (bpow ctx beta
        (Zsub (mag_val ctx magnitude beta x) Zone)) (ctx.spec.abs x) ∧
      Rlt ctx (ctx.spec.abs x)
        (bpow ctx beta (mag_val ctx magnitude beta x)) at hpos
    have hpos' : Rle ctx (bpow ctx beta
        (Zsub (mag_val ctx magnitude beta x) Zone))
        (ctx.spec.abs (Ropp ctx x)) ∧
      Rlt ctx (ctx.spec.abs (Ropp ctx x))
        (bpow ctx beta (mag_val ctx magnitude beta x)) := by
      simpa only [habs] using hpos
    exact round_odd_mag_unique_aux ctx beta (Ropp ctx x) hneg hpos'

private theorem round_odd_cexp_opp_aux
    (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (fexp : Z → Z) (x : R ctx) :
    cexp ctx magnitude beta fexp (Ropp ctx x) =
      cexp ctx magnitude beta fexp x := by
  unfold cexp CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp
  exact congrArg fexp (round_odd_mag_opp_aux ctx magnitude beta x)

private theorem round_odd_round_opp_aux
    (ctx : ExactRealContext) (magnitude : ExactMagnitude ctx)
    (beta : radix) (fexp : Z → Z) (x : R ctx) :
    round ctx magnitude beta fexp (Zrnd_odd ctx) (Ropp ctx x) =
      Ropp ctx (round ctx magnitude beta fexp (Zrnd_odd ctx) x) := by
  unfold round CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
  have hscaled := CompCert4Lean.Flocq.Core.Generic_fmt.scaled_mantissa_opp
    ctx magnitude beta fexp x
  have hcexp := round_odd_cexp_opp_aux ctx magnitude beta fexp x
  have hcexp' :
      CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp
          ctx magnitude beta fexp
          (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.Ropp ctx x) =
        CompCert4Lean.Flocq.Core.Generic_fmt.Exact.cexp
          ctx magnitude beta fexp x :=
    hcexp
  rw [hscaled, hcexp', round_odd_Zrnd_opp_aux]
  exact CompCert4Lean.Flocq.Core.Float_prop.F2R_Zopp ctx beta
    (Zrnd_odd ctx
      (CompCert4Lean.Flocq.Core.Generic_fmt.Exact.scaled_mantissa
        ctx magnitude beta fexp x))
    (cexp ctx magnitude beta fexp x)

theorem fexp_round_odd : ∀ (ctx : ExactRealContext)
    (magnitude : ExactMagnitude ctx),
    fexp_round_oddStatement ctx magnitude := by
  intro ctx magnitude beta hbeta emin prec hprec x
  rcases ctx.certificate.total_order x (R0 ctx) with h | hxpos
  · rcases h with hxneg | hxzero
    · have hnxpos : Rlt ctx (R0 ctx) (Ropp ctx x) := by
        have hh := ctx.certificate.orderedField.add_lt_compat_l
          (Ropp ctx x) x (R0 ctx) hxneg
        change ctx.spec.lt (ctx.spec.add (ctx.spec.neg x) x)
          (ctx.spec.add (ctx.spec.neg x) ctx.spec.zero) at hh
        rw [ctx.certificate.orderedField.neg_add_cancel,
          ctx.certificate.orderedField.add_zero] at hh
        exact hh
      have hp := round_odd_fexp_pos_aux ctx magnitude beta hbeta
        emin prec hprec (Ropp ctx x) hnxpos
      have hround := round_odd_round_opp_aux ctx magnitude beta
        (FLT_exp emin prec) x
      calc
        cexp ctx magnitude beta (FLT_exp emin prec)
            (round ctx magnitude beta (FLT_exp emin prec) (Zrnd_odd ctx) x) =
            cexp ctx magnitude beta (FLT_exp emin prec)
              (Ropp ctx
                (round ctx magnitude beta (FLT_exp emin prec) (Zrnd_odd ctx) x)) :=
          (round_odd_cexp_opp_aux ctx magnitude beta (FLT_exp emin prec)
            (round ctx magnitude beta (FLT_exp emin prec) (Zrnd_odd ctx) x)).symm
        _ = cexp ctx magnitude beta (FLT_exp emin prec)
              (round ctx magnitude beta (FLT_exp emin prec) (Zrnd_odd ctx)
                (Ropp ctx x)) := congrArg
          (cexp ctx magnitude beta (FLT_exp emin prec)) hround.symm
        _ = cexp ctx magnitude beta (FLT_exp emin prec) (Ropp ctx x) := hp
        _ = cexp ctx magnitude beta (FLT_exp emin prec) x :=
          round_odd_cexp_opp_aux ctx magnitude beta (FLT_exp emin prec) x
    · subst x
      have hzero_izr : R0 ctx = IZR ctx CompCert4Lean.Flocq.Core.Zaux.Z0 := by
        change ctx.spec.zero = ctx.spec.ofZ CompCert4Lean.Flocq.Core.Zaux.Z0
        exact (ctx.certificate.sourceLaws.ofZ_zero).symm
      have hfloor0 : Zfloor ctx (R0 ctx) = CompCert4Lean.Flocq.Core.Zaux.Z0 := by
        rw [hzero_izr]
        exact CompCert4Lean.Flocq.Core.Raux.Zfloor_IZR ctx _
      have hzrnd0 : Zrnd_odd ctx (R0 ctx) = CompCert4Lean.Flocq.Core.Zaux.Z0 := by
        rw [round_odd_Zrnd_odd_eq_aux ctx (R0 ctx)
          (by rw [hfloor0]; exact hzero_izr), hfloor0]
      have hround0 : round ctx magnitude beta (FLT_exp emin prec) (Zrnd_odd ctx)
          (R0 ctx) = R0 ctx := by
        unfold round CompCert4Lean.Flocq.Core.Generic_fmt.Exact.round
        rw [CompCert4Lean.Flocq.Core.Generic_fmt.scaled_mantissa_0
          ctx magnitude beta (FLT_exp emin prec), hzrnd0]
        exact CompCert4Lean.Flocq.Core.Float_prop.F2R_0 ctx beta _
      rw [hround0]
  · exact round_odd_fexp_pos_aux ctx magnitude beta hbeta
      emin prec hprec x hxpos

end CompCert4Lean.Flocq.Prop.Round_odd

namespace CompCert4Lean.Flocq.Prop.Round_odd

open CompCert4Lean.Flocq.Core

private theorem pg_valid_rnd_odd_zle_refl (z : Z) : Zle z z := by
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z
  exact Int.le_refl _

private theorem pg_valid_rnd_odd_zle_trans (a b c : Z)
    (hab : Zle a b) (hbc : Zle b c) : Zle a c := by
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b at hab
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ c at hbc
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ c
  omega

theorem valid_rnd_odd_certificate_proof :
    ∀ (ctx : ExactRealContext), Valid_rnd_odd_Certificate ctx := by
  intro ctx
  constructor
  · constructor
    · intro x y hxy
      have hfloor_xy : Zle (Zfloor ctx x) (Zfloor ctx y) :=
        CompCert4Lean.Flocq.Core.Raux.Zfloor_le ctx x y hxy
      have hfloor_y_rnd : Zle (Zfloor ctx y) (Zrnd_odd ctx y) := by
        by_cases hy : y = IZR ctx (Zfloor ctx y)
        · rw [round_odd_Zrnd_odd_eq_aux ctx y hy]
          exact pg_valid_rnd_odd_zle_refl _
        · cases hey : Zeven (Zfloor ctx y) with
          | true =>
              rw [round_odd_Zrnd_odd_ne_even_aux ctx y hy hey]
              have hreal :=
                ctx.certificate.orderedField.le_trans _ _ _
                  (CompCert4Lean.Flocq.Core.Raux.Zfloor_lb ctx y)
                  (CompCert4Lean.Flocq.Core.Raux.Zceil_ub ctx y)
              exact CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.le_IZR
                ctx _ _ hreal
          | false =>
              rw [round_odd_Zrnd_odd_ne_odd_aux ctx y hy hey]
              exact pg_valid_rnd_odd_zle_refl _
      have hfloor_x_rnd : Zle (Zfloor ctx x) (Zrnd_odd ctx y) :=
        pg_valid_rnd_odd_zle_trans _ _ _ hfloor_xy hfloor_y_rnd
      by_cases hx : x = IZR ctx (Zfloor ctx x)
      · rw [round_odd_Zrnd_odd_eq_aux ctx x hx]
        exact hfloor_x_rnd
      · cases hex : Zeven (Zfloor ctx x) with
        | false =>
            rw [round_odd_Zrnd_odd_ne_odd_aux ctx x hx hex]
            exact hfloor_x_rnd
        | true =>
            by_cases hy : y = IZR ctx (Zfloor ctx y)
            · have hceil_le : Zle (Zceil ctx x) (Zfloor ctx y) := by
                apply CompCert4Lean.Flocq.Core.Raux.Zceil_glb ctx (Zfloor ctx y) x
                change ctx.spec.le x (ctx.spec.ofZ (Zfloor ctx y))
                change ctx.spec.le x y at hxy
                rw [hy] at hxy
                exact hxy
              simpa only [round_odd_Zrnd_odd_ne_even_aux ctx x hx hex,
                round_odd_Zrnd_odd_eq_aux ctx y hy] using hceil_le
            · cases hey : Zeven (Zfloor ctx y) with
              | true =>
                  simpa only [round_odd_Zrnd_odd_ne_even_aux ctx x hx hex,
                    round_odd_Zrnd_odd_ne_even_aux ctx y hy hey] using
                    CompCert4Lean.Flocq.Core.Raux.Zceil_le ctx x y hxy
              | false =>
                  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                      (Zfloor ctx x) ≤
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zfloor ctx y)
                    at hfloor_xy
                  rcases Int.lt_or_eq_of_le hfloor_xy with hlt | heq
                  · have hceil :=
                      CompCert4Lean.Flocq.Core.Raux.Zceil_floor_neq ctx x (Ne.symm hx)
                    have hceil_le : Zle (Zceil ctx x) (Zfloor ctx y) := by
                      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                          (CompCert4Lean.Flocq.Core.Raux.Exact.Zceil ctx x) ≤
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zfloor ctx y)
                      rw [hceil]
                      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                          (Zadd (Zfloor ctx x) Zone) ≤
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zfloor ctx y)
                      simp only [Zadd,
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
                      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                          (Zfloor ctx x) + 1 ≤
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zfloor ctx y)
                      omega
                    simpa only [round_odd_Zrnd_odd_ne_even_aux ctx x hx hex,
                      round_odd_Zrnd_odd_ne_odd_aux ctx y hy hey] using hceil_le
                  · have hey' : Zeven (Zfloor ctx y) = true := by
                      have hz : Zfloor ctx x = Zfloor ctx y :=
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective heq
                      simpa only [hz] using hex
                    have hfalse : (false : Bool) = true := hey.symm.trans hey'
                    cases hfalse
    · intro n
      have hn : IZR ctx n = IZR ctx (Zfloor ctx (IZR ctx n)) :=
        (congrArg (IZR ctx) (CompCert4Lean.Flocq.Core.Raux.Zfloor_IZR ctx n)).symm
      rw [round_odd_Zrnd_odd_eq_aux ctx (IZR ctx n) hn]
      exact CompCert4Lean.Flocq.Core.Raux.Zfloor_IZR ctx n

end CompCert4Lean.Flocq.Prop.Round_odd

namespace CompCert4Lean.Flocq.Prop.Round_odd

open CompCert4Lean.Flocq.Core

theorem Zrnd_odd_Zodd : ∀ (ctx : ExactRealContext),
    Zrnd_odd_ZoddStatement ctx := by
  intro ctx x hne
  unfold Zrnd_odd
  generalize hdec :
    CompCert4Lean.Foundation.FlocqReal.Rocq.Coq.Reals.RIneq.Req_EM_T
      ctx x (IZR ctx (Zfloor ctx x)) = dec
  cases dec with
  | left heq => exact (hne heq).elim
  | right hne' =>
      cases heven : Zeven (Zfloor ctx x) with
      | false =>
          simp only [↓reduceIte]
          exact heven
      | true =>
          simp only [↓reduceIte]
          have hceil : Zceil ctx x = Zadd (Zfloor ctx x) Zone :=
            CompCert4Lean.Flocq.Core.Raux.Zceil_floor_neq ctx x (Ne.symm hne')
          rw [hceil]
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
                (Zfloor ctx x) Zone) = false
          rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even_add]
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
              (Zfloor ctx x) = true at heven
          rw [heven]
          rfl

end CompCert4Lean.Flocq.Prop.Round_odd
