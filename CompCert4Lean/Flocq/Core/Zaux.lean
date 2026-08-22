import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Lib.Floats.Model

/-!
# Flocq integer and auxiliary definitions

This module contains the executable surfaces selected from `Flocq.Core.Zaux`.
Proof-heavy source declarations are represented by exact proposition descriptors
for the later proof-migration phase.
-/

namespace CompCert4Lean.Flocq.Core.Zaux

abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
abbrev positive := CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive
abbrev comparison := CompCert4Lean.Foundation.Numbers.Rocq.Coq.comparison

abbrev Lt : comparison := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Lt
abbrev Eq : comparison := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Eq
abbrev Gt : comparison := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Gt

abbrev Z0 : Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0
abbrev Zone : Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos .xH
abbrev Ztwo : Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos (.xO .xH)

abbrev Zadd := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
abbrev Zsub := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub
abbrev Zmul := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
abbrev Zopp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp
abbrev Zabs := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs
abbrev Zabs_nat := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs_nat
abbrev Zeven := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
abbrev Zle := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
abbrev Zlt := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt
abbrev Zcompare := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.compare
abbrev Zeq_bool := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool
abbrev Zle_bool := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zle_bool
abbrev Zlt_bool := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zlt_bool
abbrev Zpower := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower
abbrev Zpower_pos := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower_pos
abbrev Zpower_nat := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpower.Zpower_nat

def cond_Zopp (b : Bool) (m : Z) : Z :=
  CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.cond_Zopp b m

def iter_pos {A : Type} (f : A → A) (p : positive) (x : A) : A :=
  CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.iter_pos f p x

def eq_dep_elim (A : Type) (x : A) (P : ∀ a : A, x = a → Type)
    (f : P x rfl) (a : A) (e : x = a) : P a e := by
  cases e
  exact f

def eqbool_dep (P : Bool → Type) (h1 : P true) (b : Bool) : P b → Prop :=
  match b with
  | true => fun h2 => h1 = h2
  | false => fun _ => False

structure radix where
  radix_val : Z
  radix_prop : Zle_bool Ztwo radix_val = true

export radix (radix_val radix_prop)

instance : Coe radix Z := ⟨radix.radix_val⟩

def radix2 : radix :=
  { radix_val := Ztwo
    radix_prop := by decide }

inductive Zeq_bool_prop (x y : Z) : Bool → Prop where
  | Zeq_bool_true_ : x = y → Zeq_bool_prop x y true
  | Zeq_bool_false_ : x ≠ y → Zeq_bool_prop x y false

export Zeq_bool_prop (Zeq_bool_true_ Zeq_bool_false_)

inductive Zle_bool_prop (x y : Z) : Bool → Prop where
  | Zle_bool_true_ : Zle x y → Zle_bool_prop x y true
  | Zle_bool_false_ : Zlt y x → Zle_bool_prop x y false

export Zle_bool_prop (Zle_bool_true_ Zle_bool_false_)

inductive Zlt_bool_prop (x y : Z) : Bool → Prop where
  | Zlt_bool_true_ : Zlt x y → Zlt_bool_prop x y true
  | Zlt_bool_false_ : Zle y x → Zlt_bool_prop x y false

export Zlt_bool_prop (Zlt_bool_true_ Zlt_bool_false_)

inductive Zcompare_prop (x y : Z) : comparison → Prop where
  | Zcompare_Lt_ : Zlt x y → Zcompare_prop x y Lt
  | Zcompare_Eq_ : x = y → Zcompare_prop x y Eq
  | Zcompare_Gt_ : Zlt y x → Zcompare_prop x y Gt

export Zcompare_prop (Zcompare_Lt_ Zcompare_Eq_ Zcompare_Gt_)

def iter_nat {A : Type} (f : A → A) : Nat → A → A
  | 0, x => x
  | n + 1, x => iter_nat f n (f x)

/-! Exact source proposition descriptors for later proof migration. -/

def Zopp_le_cancelStatement : Prop :=
  ∀ x y : Z, Zle (Zopp y) (Zopp x) → Zle x y

def Zgt_not_eqStatement : Prop :=
  ∀ x y : Z, Zlt y x → x ≠ y

def eqbool_irrelevanceStatement : Prop :=
  ∀ (b : Bool) (h1 h2 : b = true), h1 = h2

def Zeven_exStatement : Prop :=
  ∀ x : Z, ∃ p : Z,
    x = Zadd (Zmul Ztwo p) (if Zeven x then Z0 else CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos .xH)

def Zpower_plusStatement : Prop :=
  ∀ n k1 k2 : Z, Zle Z0 k1 → Zle Z0 k2 →
    Zpower n (Zadd k1 k2) = Zmul (Zpower n k1) (Zpower n k2)

def Zpower_Zpower_natStatement : Prop :=
  ∀ b e : Z, Zle Z0 e → Zpower b e = Zpower_nat b (Zabs_nat e)

def Zpower_nat_SStatement : Prop :=
  ∀ b : Z, ∀ e : Nat,
    Zpower_nat b (Nat.succ e) = Zmul b (Zpower_nat b e)

def Zpower_pos_gt_0Statement : Prop :=
  ∀ b : Z, ∀ p : positive, Zlt Z0 b → Zlt Z0 (Zpower_pos b p)

def radix_gt_0Statement : Prop :=
  ∀ r : radix, Zlt Z0 (r : Z)

def radix_gt_1Statement : Prop :=
  ∀ r : radix, Zlt Zone (r : Z)

def Zpower_gt_1Statement : Prop :=
  ∀ (r : radix) (p : Z), Zlt Z0 p → Zlt Zone (Zpower (r : Z) p)

def Zpower_gt_0Statement : Prop :=
  ∀ (r : radix) (p : Z), Zle Z0 p → Zlt Z0 (Zpower (r : Z) p)

def Zpower_ge_0Statement : Prop :=
  ∀ (r : radix) (e : Z), Zle Z0 (Zpower (r : Z) e)

def Zpower_leStatement : Prop :=
  ∀ (r : radix) (e1 e2 : Z), Zle e1 e2 →
    Zle (Zpower (r : Z) e1) (Zpower (r : Z) e2)

def Zpower_ltStatement : Prop :=
  ∀ (r : radix) (e1 e2 : Z), Zle Z0 e2 → Zlt e1 e2 →
    Zlt (Zpower (r : Z) e1) (Zpower (r : Z) e2)

def Zpower_lt_ZpowerStatement : Prop :=
  ∀ (r : radix) (e1 e2 : Z),
    Zlt (Zpower (r : Z) (Zsub e1 Zone)) (Zpower (r : Z) e2) → Zle e1 e2

def Zeq_bool_specStatement : Prop :=
  ∀ x y : Z, Zeq_bool_prop x y (Zeq_bool x y)

def Zeq_bool_trueStatement : Prop :=
  ∀ x y : Z, x = y → Zeq_bool x y = true

def Zeq_bool_falseStatement : Prop :=
  ∀ x y : Z, x ≠ y → Zeq_bool x y = false

def Zle_bool_specStatement : Prop :=
  ∀ x y : Z, Zle_bool_prop x y (Zle_bool x y)

def Zle_bool_trueStatement : Prop :=
  ∀ x y : Z, Zle x y → Zle_bool x y = true

def Zle_bool_falseStatement : Prop :=
  ∀ x y : Z, Zlt y x → Zle_bool x y = false

def Zlt_bool_specStatement : Prop :=
  ∀ x y : Z, Zlt_bool_prop x y (Zlt_bool x y)

def Zlt_bool_trueStatement : Prop :=
  ∀ x y : Z, Zlt x y → Zlt_bool x y = true

def Zlt_bool_falseStatement : Prop :=
  ∀ x y : Z, Zle y x → Zlt_bool x y = false

def Zcompare_specStatement : Prop :=
  ∀ x y : Z, Zcompare_prop x y (Zcompare x y)

def Zcompare_LtStatement : Prop :=
  ∀ x y : Z, Zlt x y → Zcompare x y = Lt

def Zcompare_EqStatement : Prop :=
  ∀ x y : Z, x = y → Zcompare x y = Eq

def Zcompare_GtStatement : Prop :=
  ∀ x y : Z, Zlt y x → Zcompare x y = Gt

def cond_Zopp_negbStatement : Prop :=
  ∀ (x : Bool) (y : Z), cond_Zopp (Bool.not x) y = Zopp (cond_Zopp x y)

def abs_cond_ZoppStatement : Prop :=
  ∀ (b : Bool) (m : Z), Zabs (cond_Zopp b m) = Zabs m

def iter_nat_plusStatement : Prop :=
  ∀ {A : Type} (f : A → A) (p q : Nat) (x : A),
    iter_nat f (p + q) x = iter_nat f p (iter_nat f q x)

def iter_nat_SStatement : Prop :=
  ∀ {A : Type} (f : A → A) (p : Nat) (x : A),
    iter_nat f (Nat.succ p) x = f (iter_nat f p x)

def iter_pos_natStatement : Prop :=
  ∀ {A : Type} (f : A → A) (p : positive) (x : A),
    iter_pos f p x = iter_nat f
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p) x

def Zeven_Zpower_oddStatement : Prop :=
  ∀ (b e : Z), Zle Z0 e → Zeven b = false →
    Zeven (Zpower b e) = false

end CompCert4Lean.Flocq.Core.Zaux
