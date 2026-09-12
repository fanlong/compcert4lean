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

universe u v

def iter_pos {A : Type u} (f : A → A) (p : positive) (x : A) : A :=
  CompCert4Lean.Lib.Floats.Model.Rocq.Coq.Floats.SpecFloat.iter_pos f p x

def eq_dep_elim (A : Type u) (x : A) (P : ∀ a : A, x = a → Sort v)
    (f : P x rfl) (a : A) (e : x = a) : P a e := by
  cases e
  exact f

def eqbool_dep (P : Bool → Sort u) (h1 : P true) (b : Bool) : P b → Prop :=
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

def iter_nat {A : Type u} (f : A → A) : Nat → A → A
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
  ∀ {A : Type u} (f : A → A) (p q : Nat) (x : A),
    iter_nat f (p + q) x = iter_nat f p (iter_nat f q x)

def iter_nat_SStatement : Prop :=
  ∀ {A : Type u} (f : A → A) (p : Nat) (x : A),
    iter_nat f (Nat.succ p) x = f (iter_nat f p x)

def iter_pos_natStatement : Prop :=
  ∀ {A : Type u} (f : A → A) (p : positive) (x : A),
    iter_pos f p x = iter_nat f
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p) x

def Zeven_Zpower_oddStatement : Prop :=
  ∀ (b e : Z), Zle Z0 e → Zeven b = false →
    Zeven (Zpower b e) = false

end CompCert4Lean.Flocq.Core.Zaux

namespace CompCert4Lean.Flocq.Core.Zaux

theorem Zgt_not_eq : Zgt_not_eqStatement := by
  intro x y hxy hEq
  subst y
  exact Int.lt_irrefl _ hxy

theorem Zopp_le_cancel : Zopp_le_cancelStatement := by
  intro x y h
  simp only [Zle, Zopp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at h
  have h' :
      -CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y ≤
        -CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x := by
    exact h
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y
  omega

theorem Zeq_bool_spec : Zeq_bool_specStatement := by
  intro x y
  by_cases h : x = y
  · have hb : Zeq_bool x y = true := by
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool, h]
    rw [hb]
    exact Zeq_bool_true_ h
  · have hb : Zeq_bool x y = false := by
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool, h]
    rw [hb]
    exact Zeq_bool_false_ h

theorem Zpower_ge_0 : Zpower_ge_0Statement := by
  intro r e
  have hr0 : 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val := by
    have hp := r.radix_prop
    change (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Ztwo : Z) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val then true else false) = true at hp
    have htwo : 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Ztwo : Z) := by
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
    split at hp
    · omega
    · simp at hp
  cases e with
  | Z0 =>
      change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zpower r.radix_val Z0)
      unfold Zpower CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower
      have h : ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Z0 : Z) < 0 := by
        simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow, h,
        ↓reduceIte]
      rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      change 0 ≤ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val) ^ (0 : Nat)
      exact Int.pow_nonneg hr0
  | Zpos p =>
      change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zpower r.radix_val (.Zpos p))
      unfold Zpower CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have h : ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (.Zpos p : Z) < 0 := by
        simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow, h,
        ↓reduceIte]
      rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      exact Int.pow_nonneg hr0
  | Zneg p =>
      change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zpower r.radix_val (.Zneg p))
      unfold Zpower CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have h : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (.Zneg p : Z) < 0 := by
        simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
        omega
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow, h,
        ↓reduceIte]
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]

end CompCert4Lean.Flocq.Core.Zaux

namespace CompCert4Lean.Flocq.Core.Zaux

theorem eqbool_irrelevance : eqbool_irrelevanceStatement := by
  intro b h1 h2
  exact Subsingleton.elim h1 h2

end CompCert4Lean.Flocq.Core.Zaux

namespace CompCert4Lean.Flocq.Core.Zaux

private theorem natAbs_ofNat (n : Nat) : Int.natAbs (Int.ofNat n) = n := by
  apply Int.ofNat.inj
  simpa using (Int.natAbs_of_nonneg (a := Int.ofNat n) (by simp))

private theorem natAbs_negOfNat (n : Nat) : Int.natAbs (-Int.ofNat n) = n := by
  rw [Int.natAbs_neg]
  exact natAbs_ofNat n

private theorem even_pos_xI (p : positive) : Zeven (.Zpos (.xI p)) = false := by
  unfold Zeven CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
  change decide ((Int.natAbs (Int.ofNat (2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p + 1))) % 2 = 0) = false
  rw [natAbs_ofNat]
  have hmod : (2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p + 1) % 2 = 1 := by omega
  simp [hmod]

private theorem even_pos_xO (p : positive) : Zeven (.Zpos (.xO p)) = true := by
  unfold Zeven CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
  change decide ((Int.natAbs (Int.ofNat (2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))) % 2 = 0) = true
  rw [natAbs_ofNat]
  have hmod : (2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) % 2 = 0 := by omega
  simp [hmod]

private theorem even_neg_xI (p : positive) : Zeven (.Zneg (.xI p)) = false := by
  unfold Zeven CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
  change decide ((Int.natAbs (-Int.ofNat (2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p + 1))) % 2 = 0) = false
  rw [natAbs_negOfNat]
  have hmod : (2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p + 1) % 2 = 1 := by omega
  simp [hmod]

private theorem even_neg_xO (p : positive) : Zeven (.Zneg (.xO p)) = true := by
  unfold Zeven CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
  change decide ((Int.natAbs (-Int.ofNat (2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))) % 2 = 0) = true
  rw [natAbs_negOfNat]
  have hmod : (2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) % 2 = 0 := by omega
  simp [hmod]

private theorem intOfZ_Zadd (a b : Z) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zadd a b) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a +
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
  simp only [Zadd, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]

private theorem intOfZ_Zmul (a b : Z) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zmul a b) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a *
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
  simp only [Zmul, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]

private theorem intOfZ_Zsub (a b : Z) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub a b) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ a -
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b := by
  simp only [Zsub, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]

theorem Zeven_ex : Zeven_exStatement := by
  intro x
  cases x with
  | Z0 =>
      refine ⟨Z0, ?_⟩
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      rw [intOfZ_Zadd, intOfZ_Zmul]
      simp [Zeven, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
  | Zpos p =>
      cases p with
      | xI p =>
          refine ⟨.Zpos p, ?_⟩
          rw [even_pos_xI]
          apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
          rw [intOfZ_Zadd, intOfZ_Zmul]
          simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
      | xO p =>
          refine ⟨.Zpos p, ?_⟩
          rw [even_pos_xO]
          apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
          rw [intOfZ_Zadd, intOfZ_Zmul]
          simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
      | xH =>
          refine ⟨Z0, ?_⟩
          have he : Zeven (.Zpos (.xH) : Z) = false := by
            unfold Zeven CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
            change decide ((Int.natAbs (Int.ofNat 1)) % 2 = 0) = false
            decide
          rw [he]
          apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
          rw [intOfZ_Zadd, intOfZ_Zmul]
          simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
  | Zneg p =>
      cases p with
      | xI p =>
          refine ⟨Zsub (.Zneg p) (.Zpos .xH), ?_⟩
          rw [even_neg_xI]
          apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
          rw [intOfZ_Zadd, intOfZ_Zmul, intOfZ_Zsub]
          simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
          omega
      | xO p =>
          refine ⟨.Zneg p, ?_⟩
          rw [even_neg_xO]
          apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
          rw [intOfZ_Zadd, intOfZ_Zmul]
          simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]
          omega
      | xH =>
          refine ⟨(.Zneg .xH : Z), ?_⟩
          have he : Zeven (.Zneg (.xH) : Z) = false := by
            unfold Zeven CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
            change decide ((Int.natAbs (-Int.ofNat 1)) % 2 = 0) = false
            decide
          rw [he]
          apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
          rw [intOfZ_Zadd, intOfZ_Zmul]
          simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat]

end CompCert4Lean.Flocq.Core.Zaux

namespace CompCert4Lean.Flocq.Core.Zaux

theorem Zpower_Zpower_nat : Zpower_Zpower_natStatement := by
  intro b e he
  cases e with
  | Z0 =>
      rfl
  | Zpos p =>
      have habs : Zabs_nat (.Zpos p) =
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p := by
        unfold Zabs_nat
        change Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
            (Int.natAbs (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (.Zpos p))))) =
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p
        rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        change Int.toNat (Int.natAbs (Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))) =
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p
        have hp0 : (0 : Int) ≤ Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) := by simp
        rw [Int.natAbs_of_nonneg hp0]
        exact Int.toNat_natCast _
      rw [habs]
      change Zpower b (.Zpos p) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow b
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))
      unfold Zpower
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
      have hleft : ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (.Zpos p) < 0 := by
        simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
      have hright : ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
            (Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))) < 0 := by
        rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        simp
      rw [if_neg hleft, if_neg hright]
      rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      have hnat : Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (.Zpos p)) =
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p := by
        rfl
      rw [hnat]
      rfl
  | Zneg p =>
      exfalso
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at he
      have hp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hp' : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) := by
        simpa [Int.ofNat_eq_coe] using (Int.natCast_pos.mpr hp)
      omega

end CompCert4Lean.Flocq.Core.Zaux

namespace CompCert4Lean.Flocq.Core.Zaux

theorem Zpower_nat_S : Zpower_nat_SStatement := by
  intro b e
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpower_nat b (Nat.succ e)) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zmul b (Zpower_nat b e))
  simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpower.Zpower_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  have he : ¬ (Int.ofNat e) < 0 := Int.not_lt_of_ge (Int.ofNat_nonneg e)
  have hes : ¬ (Int.ofNat (Nat.succ e)) < 0 :=
    Int.not_lt_of_ge (Int.ofNat_nonneg (Nat.succ e))
  have hes' : ¬ (Int.ofNat e + 1) < 0 := by
    have he0 := Int.ofNat_nonneg e
    omega
  split <;> rename_i hleft
  · omega
  · split <;> rename_i hright
    · omega
    · simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      change (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b) ^ Nat.succ e =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b *
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b) ^ e
      simpa [Int.mul_comm] using
        (Int.pow_succ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ b) e)

end CompCert4Lean.Flocq.Core.Zaux

namespace CompCert4Lean.Flocq.Core.Zaux

theorem radix_gt_0 : radix_gt_0Statement := by
  intro r
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val
  have hp := r.radix_prop
  change (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Ztwo : Z) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val then true else false) = true at hp
  have hzero : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 = (0 : Int) := by decide
  rw [hzero]
  have htwo : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Ztwo : Z) = (2 : Int) := by decide
  rw [htwo] at hp
  split at hp
  · omega
  · simp at hp

end CompCert4Lean.Flocq.Core.Zaux

namespace CompCert4Lean.Flocq.Core.Zaux

theorem Zpower_pos_gt_0 : Zpower_pos_gt_0Statement := by
  intro b p hb
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpower_pos b p)
  change (0 : Int) <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpower_pos b p)
  simp only [Zpower_pos,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow_pos,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  exact Int.pow_pos hb

end CompCert4Lean.Flocq.Core.Zaux

namespace CompCert4Lean.Flocq.Core.Zaux

private theorem intPow_zero (x : Int) : Int.pow x 0 = 1 := by
  cases x <;> simp [Int.pow]

private theorem odd_pow_mod_two (n k : Nat) (h : n % 2 = 1) :
    (n ^ k) % 2 = 1 := by
  rw [Nat.pow_mod, h]
  simp

private theorem mod_two_eq_one_of_decide_false {n : Nat}
    (h : decide (n % 2 = 0) = false) : n % 2 = 1 := by
  have hne : n % 2 ≠ 0 := of_decide_eq_false h
  have hlt : n % 2 < 2 := Nat.mod_lt _ (by omega)
  omega

private theorem natAbs_pow_neg (n k : Nat) (hn : 0 < n) :
    Int.natAbs (Int.pow (-Int.ofNat n) k) = n ^ k := by
  cases n with
  | zero => omega
  | succ a =>
      change Int.natAbs (Int.pow (Int.negSucc a) k) = (Nat.succ a) ^ k
      have hnatabs' : Int.natAbs (↑a + 1) = a + 1 := by
        have hpos : (0 : Int) ≤ (↑a + 1) :=
          Int.add_nonneg (Int.ofNat_nonneg a) (by decide)
        have h := Int.natAbs_of_nonneg hpos
        have h' := congrArg Int.toNat h
        simpa using h'
      by_cases hpar : k % 2 = 0
      · simp [Int.pow, hpar]
        rw [hnatabs']
      · simp [Int.pow, hpar]
        rw [hnatabs']

theorem Zeven_Zpower_odd : Zeven_Zpower_oddStatement := by
  intro b e he hb
  cases e with
  | Z0 =>
      unfold Zeven CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
      unfold Zpower CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower
      unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
      have hzero : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 = (0 : Int) := by decide
      have hcond : ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 < 0 := by
        simp [hzero]
      rw [if_neg hcond, CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
        hzero]
      simp [intPow_zero]
  | Zpos p =>
      cases b with
      | Z0 =>
          have hzero : Zeven (Z0 : Z) = true := by decide
          rw [hzero] at hb
          contradiction
      | Zpos q =>
          unfold Zeven CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even at hb ⊢
          change decide (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q % 2 = 0) = false at hb
          have hq : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q % 2 = 1 :=
            mod_two_eq_one_of_decide_false hb
          unfold Zpower CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower
          unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
          have hcond : ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (.Zpos p) < 0 := by
            simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
          rw [if_neg hcond, CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          change decide ((Int.natAbs (Int.pow (Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q))
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))) % 2 = 0) = false
          simp [Int.pow, hq, Nat.pow_mod]
      | Zneg q =>
          unfold Zeven CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even at hb ⊢
          have hb' : decide (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q % 2 = 0) = false := by
            simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ, Int.natAbs_neg,
              Int.natAbs_of_nonneg (Int.ofNat_nonneg _)] using hb
          have hq : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q % 2 = 1 :=
            mod_two_eq_one_of_decide_false hb'
          unfold Zpower CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower
          unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
          have hcond : ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (.Zpos p) < 0 := by
            simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
          rw [if_neg hcond, CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
          change decide ((Int.natAbs (Int.pow (-Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q))
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))) % 2 = 0) = false
          rw [natAbs_pow_neg _ _
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive q)]
          simp [hq, Nat.pow_mod]
  | Zneg p =>
      exfalso
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at he
      have hp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hp' : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) := by
        simpa [Int.ofNat_eq_coe] using (Int.natCast_pos.mpr hp)
      omega

end CompCert4Lean.Flocq.Core.Zaux
