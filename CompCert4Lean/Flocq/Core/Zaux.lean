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

namespace CompCert4Lean.Flocq.Core.Zaux

theorem radix_gt_1 : radix_gt_1Statement := by
  intro r
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val
  have hp := r.radix_prop
  change (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Ztwo : Z) ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val then true else false) = true at hp
  have hone : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone = (1 : Int) := by decide
  have htwo : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Ztwo : Z) = (2 : Int) := by decide
  rw [hone]
  rw [htwo] at hp
  split at hp
  · omega
  · simp at hp

end CompCert4Lean.Flocq.Core.Zaux

namespace CompCert4Lean.Flocq.Core.Zaux

theorem Zpower_gt_1 : Zpower_gt_1Statement := by
  intro r p hp
  cases p with
  | Z0 =>
      change (0 : Int) < 0 at hp
      omega
  | Zneg q =>
      exfalso
      change (0 : Int) < -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q) at hp
      have hq := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive q
      have hq' : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q) :=
        Int.natCast_pos.mpr hq
      omega
  | Zpos q =>
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Zone <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Zpower r.radix_val (.Zpos q))
      have hbase : (1 : Int) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val := by
        exact radix_gt_1 r
      have ha_pos : (0 : Int) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val :=
        Int.lt_trans (by decide) hbase
      have hpow_gt : ∀ n : Nat, 0 < n →
          (1 : Int) <
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val) ^ n := by
        intro n
        induction n with
        | zero =>
            intro hn
            omega
        | succ n ih =>
            intro hn
            rw [Int.pow_succ]
            cases n with
            | zero =>
                simpa [Int.pow] using hbase
            | succ n =>
                have hmul := Int.mul_lt_mul_of_pos_right (ih (by omega)) ha_pos
                exact Int.lt_trans hbase (by simpa using hmul)
      unfold Zpower CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower
      unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
      have hcond : ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (.Zpos q : Z) < 0 := by
        simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
      rw [if_neg hcond, CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      apply hpow_gt
      exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive q

end CompCert4Lean.Flocq.Core.Zaux

namespace CompCert4Lean.Flocq.Core.Zaux

theorem Zpower_gt_0 : Zpower_gt_0Statement := by
  intro r p hp
  cases p with
  | Z0 =>
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zpower r.radix_val Z0)
      have hzero : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 = (0 : Int) := by
        decide
      rw [hzero]
      unfold Zpower CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower
      have hcond : ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Z0 : Z) < 0 := by
        simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow, hcond,
        ↓reduceIte]
      rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      change (0 : Int) <
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ r.radix_val) ^ (0 : Nat)
      simp
  | Zpos q =>
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (Zpower r.radix_val (.Zpos q))
      have hzero : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 = (0 : Int) := by
        decide
      rw [hzero]
      unfold Zpower CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpow_def.Zpower
      have hcond : ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (.Zpos q : Z) < 0 := by
        simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow, hcond,
        ↓reduceIte]
      rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      exact Int.pow_pos (radix_gt_0 r)
  | Zneg q =>
      exfalso
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q) at hp
      have hq := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive q
      have hq' : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q) :=
        Int.natCast_pos.mpr hq
      omega

end CompCert4Lean.Flocq.Core.Zaux

namespace CompCert4Lean.Flocq.Core.Zaux

private theorem zpower_neg_int (r : radix) (p : positive) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zpower (r : Z) (.Zneg p)) = 0 := by
  have hp : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (.Zneg p : Z) < 0 := by
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
    have hpos := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
    omega
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
        (r : Z) (.Zneg p)) = 0
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
  rw [if_pos hp]
  decide

private theorem zpower_zero_int (r : radix) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zpower (r : Z) Z0) = 1 := by
  have hp : ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Z0 : Z) < 0 := by
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
        (r : Z) Z0) = 1
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
  rw [if_neg hp]
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (r : Z)) ^ (0 : Nat) = 1
  exact intPow_zero _

private theorem zpower_pos_int (r : radix) (p : positive) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (Zpower (r : Z) (.Zpos p)) =
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (r : Z)) ^
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p := by
  have hp : ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (.Zpos p : Z) < 0 := by
    simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ]
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
        (r : Z) (.Zpos p)) = _
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
  rw [if_neg hp]
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  rfl

private theorem int_pow_mono_nonneg (a : Int) (ha : 1 ≤ a) :
    ∀ {m n : Nat}, m ≤ n → a ^ m ≤ a ^ n := by
  intro m n hmn
  induction n with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      exact Int.le_refl _
  | succ n ih =>
      by_cases heq : m = Nat.succ n
      · subst m
        exact Int.le_refl _
      · have hmlt : m < Nat.succ n := Nat.lt_of_le_of_ne hmn heq
        have hmle : m ≤ n := Nat.le_of_lt_succ hmlt
        have hnonneg : 0 ≤ a ^ n := Int.pow_nonneg (by omega)
        have hstep : a ^ n ≤ a ^ n * a := by
          have hh := Int.mul_le_mul_of_nonneg_left ha hnonneg
          simpa using hh
        rw [Int.pow_succ]
        exact Int.le_trans (ih hmle) hstep

theorem Zpower_le : Zpower_leStatement := by
  intro r e1 e2 he
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 at he
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (Zpower (r : Z) e1) ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (Zpower (r : Z) e2)
  cases e1 with
  | Zneg p =>
      cases e2 with
      | Z0 =>
          rw [zpower_neg_int, zpower_zero_int]
          omega
      | Zpos q =>
          rw [zpower_neg_int, zpower_pos_int]
          have hbase : (0 : Int) ≤
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (r : Z)) ^
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q :=
            Int.pow_nonneg (by exact Int.le_of_lt (radix_gt_0 r))
          exact hbase
      | Zneg q =>
          rw [zpower_neg_int, zpower_neg_int]
          exact Int.le_refl _
  | Z0 =>
      cases e2 with
      | Zneg q =>
          change (0 : Int) ≤ -Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q) at he
          have hq := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive q
          have hq' : (0 : Int) < Int.ofNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q) :=
            Int.natCast_pos.mpr hq
          omega
      | Z0 =>
          exact Int.le_refl _
      | Zpos q =>
          rw [zpower_zero_int, zpower_pos_int]
          have hbase : (1 : Int) ≤
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (r : Z) := by
            exact Int.le_of_lt (radix_gt_1 r)
          have hnonneg : (0 : Int) ≤
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (r : Z) := by omega
          cases CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q with
          | zero => simp
          | succ n =>
              rw [Int.pow_succ]
              have hpow : (0 : Int) ≤
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (r : Z)) ^ n :=
                Int.pow_nonneg hnonneg
              have hpow1 : (1 : Int) ≤
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (r : Z)) ^ n := by
                have hh := int_pow_mono_nonneg
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (r : Z)) hbase
                  (Nat.zero_le n)
                simpa using hh
              have hstep := Int.mul_le_mul_of_nonneg_right hbase hpow
              have hstep' :
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (r : Z)) ^ n ≤
                    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (r : Z)) ^ n *
                      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (r : Z) := by
                simpa [Int.mul_comm] using hstep
              exact Int.le_trans hpow1 hstep'
  | Zpos p =>
      cases e2 with
      | Zneg q =>
          exfalso
          change Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) ≤
            -Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q) at he
          have hp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
          have hq := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive q
          have hp' : (0 : Int) < Int.ofNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
            Int.natCast_pos.mpr hp
          have hq' : (0 : Int) < Int.ofNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q) :=
            Int.natCast_pos.mpr hq
          omega
      | Z0 =>
          exfalso
          change Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) ≤ 0 at he
          have hp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
          have hp' : (0 : Int) < Int.ofNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
            Int.natCast_pos.mpr hp
          omega
      | Zpos q =>
          rw [zpower_pos_int, zpower_pos_int]
          change Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) ≤
            Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q) at he
          have hpnat : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p ≤
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q := by
            exact Int.ofNat_le.mp he
          exact int_pow_mono_nonneg
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (r : Z))
            (Int.le_of_lt (radix_gt_1 r)) hpnat

end CompCert4Lean.Flocq.Core.Zaux

namespace CompCert4Lean.Flocq.Core.Zaux

private theorem int_pow_succ_strict (a : Int) (ha : (1 : Int) < a) (n : Nat) :
    a ^ n < a ^ (Nat.succ n) := by
  rw [Int.pow_succ]
  have hpos : (0 : Int) < a ^ n := Int.pow_pos (by omega)
  have h := Int.mul_lt_mul_of_pos_left ha hpos
  simpa using h

private theorem int_pow_strict_mono (a : Int) (ha : (1 : Int) < a) :
    ∀ {m n : Nat}, m < n → a ^ m < a ^ n := by
  intro m n hmn
  have hstep : a ^ m < a ^ (Nat.succ m) := int_pow_succ_strict a ha m
  have hsucc : Nat.succ m ≤ n := Nat.succ_le_of_lt hmn
  have hle := int_pow_mono_nonneg a (Int.le_of_lt ha) hsucc
  exact Int.lt_of_lt_of_le hstep hle

theorem Zpower_lt : Zpower_ltStatement := by
  intro r e1 e2 he2 he12
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2
      ≥ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ Z0 at he2
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 at he12
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (Zpower (r : Z) e1) <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (Zpower (r : Z) e2)
  cases e1 with
  | Zneg p =>
      cases e2 with
      | Zneg q =>
          exfalso
          change (0 : Int) ≤ -Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q) at he2
          have hq := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive q
          have hq' : (0 : Int) < Int.ofNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q) :=
            Int.natCast_pos.mpr hq
          omega
      | Z0 =>
          rw [zpower_neg_int, zpower_zero_int]
          omega
      | Zpos q =>
          rw [zpower_neg_int, zpower_pos_int]
          exact Int.pow_pos (radix_gt_0 r)
  | Z0 =>
      cases e2 with
      | Zneg q =>
          exfalso
          change -Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q) ≥ (0 : Int) at he2
          have hq := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive q
          have hq' : (0 : Int) < Int.ofNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q) :=
            Int.natCast_pos.mpr hq
          omega
      | Z0 =>
          exfalso
          omega
      | Zpos q =>
          rw [zpower_zero_int, zpower_pos_int]
          have hq := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive q
          have hpow := int_pow_strict_mono
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (r : Z))
            (radix_gt_1 r) (m := 0)
            (n := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q)
            hq
          simpa using hpow
  | Zpos p =>
      cases e2 with
      | Zneg q =>
          exfalso
          change -Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q) ≥ (0 : Int) at he2
          have hq := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive q
          have hq' : (0 : Int) < Int.ofNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q) :=
            Int.natCast_pos.mpr hq
          omega
      | Z0 =>
          exfalso
          change Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) < 0 at he12
          have hp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
          have hp' : (0 : Int) < Int.ofNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
            Int.natCast_pos.mpr hp
          omega
      | Zpos q =>
          rw [zpower_pos_int, zpower_pos_int]
          have hpnat : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat q := by
            exact Int.ofNat_lt.mp he12
          exact int_pow_strict_mono
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (r : Z))
            (radix_gt_1 r) hpnat

end CompCert4Lean.Flocq.Core.Zaux

namespace CompCert4Lean.Flocq.Core.Zaux

theorem Zeq_bool_true : Zeq_bool_trueStatement := by
  intro x y h
  simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool, h]

theorem Zeq_bool_false : Zeq_bool_falseStatement := by
  intro x y h
  simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zbool.Zeq_bool, h]

theorem Zpower_lt_Zpower : Zpower_lt_ZpowerStatement := by
  intro r e1 e2 h
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 ≤
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2
  apply Int.le_of_not_gt
  intro hgt
  have hle : Zle e2 (Zsub e1 Zone) := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (Zsub e1 Zone)
    simp only [Zsub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e2 ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ e1 - 1
    omega
  have hp := Zpower_le r e2 (Zsub e1 Zone) hle
  exact (Int.not_lt_of_ge hp) h

end CompCert4Lean.Flocq.Core.Zaux

namespace CompCert4Lean.Flocq.Core.Zaux

theorem Zle_bool_spec : Zle_bool_specStatement := by
  intro x y
  change Zle_bool_prop x y (if
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y then true else false)
  by_cases h : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y
  · simpa [h] using (Zle_bool_true_ h)
  · simpa [h] using (Zle_bool_false_ (Int.lt_of_not_ge h))

end CompCert4Lean.Flocq.Core.Zaux

namespace CompCert4Lean.Flocq.Core.Zaux

theorem Zle_bool_true : Zle_bool_trueStatement := by
  intro x y h
  change (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y then true else false) = true
  have hp : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y := h
  simp [hp]

end CompCert4Lean.Flocq.Core.Zaux

namespace CompCert4Lean.Flocq.Core.Zaux

theorem Zle_bool_false : Zle_bool_falseStatement := by
  intro x y h
  change (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y then true else false) = false
  have hn : ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y := by
    exact Int.not_le_of_gt h
  simp [hn]

end CompCert4Lean.Flocq.Core.Zaux

namespace CompCert4Lean.Flocq.Core.Zaux

theorem Zlt_bool_spec : Zlt_bool_specStatement := by
  intro x y
  change Zlt_bool_prop x y (if
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y then true else false)
  by_cases h : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y
  · simpa [h] using (Zlt_bool_true_ h)
  · have hle : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x :=
      Int.le_of_not_gt h
    simpa [h] using (Zlt_bool_false_ hle)

end CompCert4Lean.Flocq.Core.Zaux

namespace CompCert4Lean.Flocq.Core.Zaux

theorem Zlt_bool_true : Zlt_bool_trueStatement := by
  intro x y h
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y at h
  change (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y then true else false) = true
  simp [h]

theorem Zlt_bool_false : Zlt_bool_falseStatement := by
  intro x y h
  change (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y then true else false) = false
  have hn : ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y := by
    exact Int.not_lt_of_ge h
  simp [hn]

theorem Zcompare_spec : Zcompare_specStatement := by
  intro x y
  change Zcompare_prop x y (if
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y then Lt else if
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y then Eq else Gt)
  by_cases hlt : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y
  · rw [if_pos hlt]
    exact Zcompare_Lt_ hlt
  · by_cases heq : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y
    · rw [if_neg hlt, if_pos heq]
      exact Zcompare_Eq_ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective heq)
    · have hgt : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x := by
        omega
      rw [if_neg hlt, if_neg heq]
      exact Zcompare_Gt_ hgt

theorem Zcompare_Lt : Zcompare_LtStatement := by
  intro x y h
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y at h
  change (if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y then Lt else if
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y then Eq else Gt) = Lt
  simp [h]

end CompCert4Lean.Flocq.Core.Zaux

namespace CompCert4Lean.Flocq.Core.Zaux

theorem cond_Zopp_negb : cond_Zopp_negbStatement := by
  intro x y
  cases x with
  | false => rfl
  | true =>
      change y = Zopp (Zopp y)
      symm
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp only [Zopp, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      change -(-CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y) = _
      omega

end CompCert4Lean.Flocq.Core.Zaux

namespace CompCert4Lean.Flocq.Core.Zaux

theorem abs_cond_Zopp : abs_cond_ZoppStatement := by
  intro b m
  cases b with
  | false => rfl
  | true =>
      change Zabs (Zopp m) = Zabs m
      simp only [Zabs, Zopp,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.abs,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp]
      rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      exact congrArg
        (fun n : Nat => CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat n))
        (Int.natAbs_neg (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ m))

end CompCert4Lean.Flocq.Core.Zaux

namespace CompCert4Lean.Flocq.Core.Zaux

theorem iter_nat_plus : iter_nat_plusStatement := by
  intro A f p q
  induction q with
  | zero =>
      intro x
      simp [iter_nat]
  | succ q ih =>
      intro x
      simpa [Nat.add_succ, iter_nat] using ih (f x)

theorem iter_nat_S : iter_nat_SStatement := by
  intro A f p
  induction p with
  | zero =>
      intro x
      rfl
  | succ p ih =>
      intro x
      simpa [iter_nat] using ih (f x)

theorem iter_pos_nat : iter_pos_natStatement := by
  intro A f p
  induction p with
  | xH =>
      intro x
      rfl
  | xO p ih =>
      intro x
      have hiter := iter_nat_plus f
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p) x
      rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.Pnat.Pos2Nat.inj_xO]
      calc
        iter_pos f (CompCert4Lean.Foundation.Numbers.Rocq.Coq.xO p) x =
            iter_pos f p (iter_pos f p x) := rfl
        _ = iter_nat f
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p)
            (iter_nat f
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p) x) := by
          rw [ih, ih]
        _ = iter_nat f
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p +
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p) x :=
          hiter.symm
        _ = iter_nat f
            ((Nat.succ 0).succ.mul
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p)) x := by
          simp [Nat.two_mul]
  | xI p ih =>
      intro x
      have hiter := iter_nat_plus f
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p) (f x)
      rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.Pnat.Pos2Nat.inj_xI]
      calc
        iter_pos f (CompCert4Lean.Foundation.Numbers.Rocq.Coq.xI p) x =
            iter_pos f p (iter_pos f p (f x)) := rfl
        _ = iter_nat f
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p)
            (iter_nat f
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p) (f x)) := by
          rw [ih, ih]
        _ = iter_nat f
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p +
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p) (f x) :=
          hiter.symm
        _ = iter_nat f
            (Nat.succ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p +
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p)) x := by
          rfl
        _ = iter_nat f
            (Nat.succ ((Nat.succ 0).succ.mul
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat p))) x := by
          simp [Nat.two_mul]

end CompCert4Lean.Flocq.Core.Zaux
