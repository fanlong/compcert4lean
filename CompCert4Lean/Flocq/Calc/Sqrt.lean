import CompCert4Lean.Flocq.Calc.Bracket
import CompCert4Lean.Flocq.Core.Digits
import CompCert4Lean.Flocq.Core.Raux

/-!
# Flocq square-root helpers

This module translates the executable and statement-bearing surface selected
from `Flocq.Calc.Sqrt`.  Proofs assigned to the later proof-migration phase
are represented by exact source-shaped proposition descriptors.
-/

namespace CompCert4Lean.Flocq.Calc.Sqrt

abbrev R := CompCert4Lean.Flocq.Core.Raux.R
abbrev Z := CompCert4Lean.Flocq.Core.Zaux.Z
abbrev radix := CompCert4Lean.Flocq.Core.Zaux.radix
abbrev comparison := CompCert4Lean.Flocq.Core.Zaux.comparison

abbrev Lt : comparison := CompCert4Lean.Flocq.Core.Zaux.Lt
abbrev Eq : comparison := CompCert4Lean.Flocq.Core.Zaux.Eq
abbrev Gt : comparison := CompCert4Lean.Flocq.Core.Zaux.Gt

abbrev Z0 : Z := CompCert4Lean.Flocq.Core.Zaux.Z0
abbrev Zone : Z := CompCert4Lean.Flocq.Core.Zaux.Zone
abbrev Ztwo : Z := CompCert4Lean.Flocq.Core.Zaux.Ztwo
abbrev Zadd := CompCert4Lean.Flocq.Core.Zaux.Zadd
abbrev Zmul := CompCert4Lean.Flocq.Core.Zaux.Zmul
abbrev Zsub := CompCert4Lean.Flocq.Core.Zaux.Zsub
abbrev Zdiv2 := CompCert4Lean.Flocq.Core.Raux.Zdiv2
abbrev Zpower := CompCert4Lean.Flocq.Core.Zaux.Zpower
abbrev Zeq_bool := CompCert4Lean.Flocq.Core.Zaux.Zeq_bool
abbrev Zle_bool := CompCert4Lean.Flocq.Core.Zaux.Zle_bool
abbrev Zle := CompCert4Lean.Flocq.Core.Zaux.Zle
abbrev Zlt := CompCert4Lean.Flocq.Core.Zaux.Zlt
abbrev Zdigits := CompCert4Lean.Flocq.Core.Digits.Zdigits

abbrev IZR := CompCert4Lean.Flocq.Core.Raux.IZR
abbrev sqrt := CompCert4Lean.Flocq.Core.Raux.sqrt
abbrev mag := CompCert4Lean.Flocq.Core.Raux.mag
abbrev bpow := CompCert4Lean.Flocq.Core.Raux.bpow

abbrev location := CompCert4Lean.Flocq.Calc.Bracket.location
abbrev loc_Exact : location := CompCert4Lean.Flocq.Calc.Bracket.loc_Exact
abbrev loc_Inexact (c : comparison) : location :=
  CompCert4Lean.Flocq.Calc.Bracket.loc_Inexact c

abbrev float := CompCert4Lean.Flocq.Core.Float_prop.float
abbrev Float (beta : radix) (m e : Z) : float beta :=
  CompCert4Lean.Flocq.Core.Float_prop.Float beta m e
abbrev F2R {beta : radix} (f : float beta) : R :=
  CompCert4Lean.Flocq.Core.Float_prop.F2R f

def Fsqrt_core (beta : radix) (m1 e1 e : Z) : Z × location :=
  let _d1 := Zdigits beta m1
  let m1' := Zmul m1 (Zpower (beta : Z) (Zsub e1 (Zmul Ztwo e)))
  let qr := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sqrtrem m1'
  let q := qr.1
  let r := qr.2
  let l :=
    if Zeq_bool r Z0 then
      loc_Exact
    else
      loc_Inexact (if Zle_bool r q then Lt else Gt)
  (q, l)

/-! Exact source proposition descriptors for later proof migration. -/

def mag_sqrt_F2RStatement : Prop :=
  ∀ (beta : radix) (m1 e1 : Z),
    Zlt Z0 m1 →
      (mag beta (sqrt (F2R (Float beta m1 e1))) : Z) =
        Zdiv2 (Zadd (Zadd (Zdigits beta m1) e1) Zone)

def Fsqrt_core_correctStatement : Prop :=
  ∀ (beta : radix) (m1 e1 e : Z),
    Zlt Z0 m1 →
    Zle (Zmul Ztwo e) e1 →
    let (m, l) := Fsqrt_core beta m1 e1 e
    CompCert4Lean.Flocq.Calc.Bracket.inbetween_float beta m e
      (sqrt (F2R (Float beta m1 e1))) l

end CompCert4Lean.Flocq.Calc.Sqrt
