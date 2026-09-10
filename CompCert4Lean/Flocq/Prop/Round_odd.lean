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
