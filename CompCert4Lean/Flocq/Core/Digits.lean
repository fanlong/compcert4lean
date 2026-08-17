import CompCert4Lean.Flocq.Core.Zaux

/-!
# Flocq integer digit counts

This module contains the executable surfaces selected from `Flocq.Core.Digits`.
Proof-heavy source declarations are represented by exact proposition descriptors
for the later proof-migration phase.
-/

namespace CompCert4Lean.Flocq.Core.Digits

abbrev Z := CompCert4Lean.Flocq.Core.Zaux.Z
abbrev positive := CompCert4Lean.Flocq.Core.Zaux.positive
abbrev radix := CompCert4Lean.Flocq.Core.Zaux.radix

abbrev Z0 : Z := CompCert4Lean.Flocq.Core.Zaux.Z0
abbrev Zone : Z := CompCert4Lean.Flocq.Core.Zaux.Zone
abbrev Ztwo : Z := CompCert4Lean.Flocq.Core.Zaux.Ztwo

abbrev Zpos := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos
abbrev Zadd := CompCert4Lean.Flocq.Core.Zaux.Zadd
abbrev Zsub := CompCert4Lean.Flocq.Core.Zaux.Zsub
abbrev Zmul := CompCert4Lean.Flocq.Core.Zaux.Zmul
abbrev Zabs := CompCert4Lean.Flocq.Core.Zaux.Zabs
abbrev Zle := CompCert4Lean.Flocq.Core.Zaux.Zle
abbrev Zlt := CompCert4Lean.Flocq.Core.Zaux.Zlt
abbrev Zlt_bool := CompCert4Lean.Flocq.Core.Zaux.Zlt_bool
abbrev Zpower := CompCert4Lean.Flocq.Core.Zaux.Zpower
abbrev Zpower_nat := CompCert4Lean.Flocq.Core.Zaux.Zpower_nat
abbrev Z_of_nat := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
abbrev radix2 := CompCert4Lean.Flocq.Core.Zaux.radix2

abbrev digits2_pos (n : positive) : positive :=
  CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.digits2_pos n

abbrev Zdigits2 (n : Z) : Z :=
  CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.Zdigits2 n

def digits2_Pnat : positive → Nat
  | .xH => 0
  | .xO p => Nat.succ (digits2_Pnat p)
  | .xI p => Nat.succ (digits2_Pnat p)

def Zdigits_aux (beta : radix) (p nb pow : Z) : Nat → Z
  | 0 => nb
  | Nat.succ n =>
      if Zlt_bool p pow then
        nb
      else
        Zdigits_aux beta p (Zadd nb Zone) (Zmul (beta : Z) pow) n

def Zdigits (beta : radix) (n : Z) : Z :=
  match n with
  | .Z0 => Z0
  | .Zneg p => Zdigits_aux beta (Zpos p) Zone (beta : Z) (digits2_Pnat p)
  | .Zpos p => Zdigits_aux beta n Zone (beta : Z) (digits2_Pnat p)

/-! Exact source proposition descriptors for later proof migration. -/

def digits2_Pnat_correctStatement : Prop :=
  ∀ n : positive,
    let d := digits2_Pnat n
    Zle (Zpower_nat Ztwo d) (Zpos n) ∧
      Zlt (Zpos n) (Zpower_nat Ztwo (Nat.succ d))

def Zdigits_correctStatement : Prop :=
  ∀ (beta : radix) (n : Z),
    Zle (Zpower (beta : Z) (Zsub (Zdigits beta n) Zone)) (Zabs n) ∧
      Zlt (Zabs n) (Zpower (beta : Z) (Zdigits beta n))

def Zdigits_uniqueStatement : Prop :=
  ∀ (beta : radix) (n d : Z),
    (Zle (Zpower (beta : Z) (Zsub d Zone)) (Zabs n) ∧
      Zlt (Zabs n) (Zpower (beta : Z) d)) →
      Zdigits beta n = d

def Zdigits_absStatement : Prop :=
  ∀ (beta : radix) (n : Z), Zdigits beta (Zabs n) = Zdigits beta n

def Zdigits_gt_0Statement : Prop :=
  ∀ (beta : radix) (n : Z), n ≠ Z0 → Zlt Z0 (Zdigits beta n)

def Zpower_le_ZdigitsStatement : Prop :=
  ∀ (beta : radix) (e x : Z),
    Zlt e (Zdigits beta x) →
      Zle (Zpower (beta : Z) e) (Zabs x)

def Zdigits_le_ZpowerStatement : Prop :=
  ∀ (beta : radix) (e x : Z),
    Zlt (Zabs x) (Zpower (beta : Z) e) →
      Zle (Zdigits beta x) e

def Zpower_gt_ZdigitsStatement : Prop :=
  ∀ (beta : radix) (e x : Z),
    Zle (Zdigits beta x) e →
      Zlt (Zabs x) (Zpower (beta : Z) e)

def Zdigits_gt_ZpowerStatement : Prop :=
  ∀ (beta : radix) (e x : Z),
    Zle (Zpower (beta : Z) e) (Zabs x) →
      Zlt e (Zdigits beta x)

def Zdigits_mult_geStatement : Prop :=
  ∀ (beta : radix) (x y : Z),
    x ≠ Z0 → y ≠ Z0 →
      Zle
        (Zsub (Zadd (Zdigits beta x) (Zdigits beta y)) Zone)
        (Zdigits beta (Zmul x y))

def Z_of_nat_S_digits2_PnatStatement : Prop :=
  ∀ m : positive,
    Z_of_nat (Nat.succ (digits2_Pnat m)) = Zdigits radix2 (Zpos m)

def Zpos_digits2_posStatement : Prop :=
  ∀ m : positive, Zpos (digits2_pos m) = Zdigits radix2 (Zpos m)

def Zdigits2_ZdigitsStatement : Prop :=
  ∀ n : Z, Zdigits2 n = Zdigits radix2 n

end CompCert4Lean.Flocq.Core.Digits
