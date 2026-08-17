import CompCert4Lean.Flocq.Calc.Bracket

/-!
# Floating-point division helpers

This module translates the executable definitions selected from
`Flocq.Calc.Div`.  The two source proofs assigned to the later proof phase
are retained as exact proposition descriptors.
-/

namespace CompCert4Lean.Flocq.Calc.Div

abbrev R := CompCert4Lean.Flocq.Core.Float_prop.R
abbrev Z := CompCert4Lean.Flocq.Core.Float_prop.Z
abbrev radix := CompCert4Lean.Flocq.Core.Float_prop.radix
abbrev location := CompCert4Lean.Flocq.Calc.Bracket.location

abbrev Z0 : Z := CompCert4Lean.Flocq.Core.Float_prop.Z0
abbrev Zone : Z := CompCert4Lean.Flocq.Core.Float_prop.Zone
abbrev Zadd := CompCert4Lean.Flocq.Core.Float_prop.Zadd
abbrev Zsub := CompCert4Lean.Flocq.Core.Zaux.Zsub
abbrev Zmul := CompCert4Lean.Flocq.Core.Float_prop.Zmul
abbrev Zdiv_eucl :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div_eucl
abbrev Zdigits := CompCert4Lean.Flocq.Core.Float_prop.Zdigits
abbrev Zle := CompCert4Lean.Flocq.Core.Float_prop.Zle
abbrev Zle_bool := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zle_bool
abbrev Zlt := CompCert4Lean.Flocq.Core.Float_prop.Zlt
abbrev Zpower := CompCert4Lean.Flocq.Core.Float_prop.Zpower

abbrev IZR := CompCert4Lean.Flocq.Core.Float_prop.IZR
abbrev Rdiv := CompCert4Lean.Flocq.Core.Raux.Rdiv
abbrev float := CompCert4Lean.Flocq.Core.Float_prop.float
abbrev Float (beta : radix) (m e : Z) : float beta :=
  CompCert4Lean.Flocq.Core.Float_prop.Float beta m e
abbrev F2R {beta : radix} (f : float beta) : R :=
  CompCert4Lean.Flocq.Core.Float_prop.F2R f
abbrev mag := CompCert4Lean.Flocq.Core.Float_prop.mag
abbrev mag_prop := CompCert4Lean.Flocq.Core.Raux.mag_prop
abbrev mag_val {beta : radix} {x : R} (m : mag_prop beta x) : Z :=
  CompCert4Lean.Flocq.Core.Raux.mag_val m
abbrev inbetween_float := CompCert4Lean.Flocq.Calc.Bracket.inbetween_float
abbrev new_location := CompCert4Lean.Flocq.Calc.Bracket.new_location
abbrev loc_Exact := CompCert4Lean.Flocq.Calc.Bracket.loc_Exact

/- The source notation `bpow e` is a beta-parameterized abbreviation. -/
abbrev bpow (beta : radix) (e : Z) : R :=
  CompCert4Lean.Flocq.Core.Raux.bpow beta e

def Fdiv_core (beta : radix) (m1 e1 m2 e2 e : Z) : Z × location :=
  let (m1', m2') :=
    if Zle_bool e (Zsub e1 e2) then
      (Zmul m1 (Zpower (beta : Z) (Zsub (Zsub e1 e2) e)), m2)
    else
      (m1, Zmul m2 (Zpower (beta : Z) (Zsub e (Zsub e1 e2))))
  let (q, r) := Zdiv_eucl m1' m2'
  (q, new_location m2' r loc_Exact)

/-! Exact source proposition descriptors for later proof migration. -/

def mag_div_F2RStatement : Prop :=
  ∀ (beta : radix) (m1 e1 m2 e2 : Z),
    Zlt Z0 m1 →
      Zlt Z0 m2 →
        let x :=
          Rdiv
            (F2R (Float beta m1 e1))
            (F2R (Float beta m2 e2))
        let e :=
          Zsub
            (Zadd (Zdigits beta m1) e1)
            (Zadd (Zdigits beta m2) e2)
        Zle e (mag_val (mag beta x)) ∧
          Zle (mag_val (mag beta x)) (Zadd e Zone)

def Fdiv_core_correctStatement : Prop :=
  ∀ (beta : radix) (m1 e1 m2 e2 e : Z),
      Zlt Z0 m1 →
      Zlt Z0 m2 →
        let (m, l) := Fdiv_core beta m1 e1 m2 e2 e
        inbetween_float beta m e
          (Rdiv
            (F2R (Float beta m1 e1))
            (F2R (Float beta m2 e2))) l

end CompCert4Lean.Flocq.Calc.Div
