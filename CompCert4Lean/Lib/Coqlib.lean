import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.Recursion

/-!
# Common CompCert definitions

This module translates the definition-bearing surface of `lib/Coqlib.v`.
Proofs assigned to the later proof-migration phase are represented by exact
proposition descriptors rather than theorem stubs.
-/

namespace CompCert4Lean.Lib.Coqlib

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

universe u v w

private def sumboolSelect {P Q : Prop} {A : Type u}
    (d : CompCert4Lean.Foundation.Logic.Support.Sumbool P Q) (ifso ifnot : A) : A :=
  match d with
  | .left _ => ifso
  | .right _ => ifnot

/-! ## Positive numbers -/

def peq (x y : positive) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) :=
  PArith.BinPos.Pos.eq_dec x y

def peq_trueStatement : Prop :=
  ∀ (A : Type u) (x : positive) (a b : A), sumboolSelect (peq x x) a b = a

def peq_falseStatement : Prop :=
  ∀ (A : Type u) (x y : positive) (a b : A),
    x ≠ y → sumboolSelect (peq x y) a b = b

def Plt (x y : positive) : Prop :=
  PArith.BinPos.Pos.lt x y

def Plt_neStatement : Prop :=
  ∀ x y : positive, Plt x y → x ≠ y

def Plt_transStatement : Prop :=
  ∀ x y z : positive, Plt x y → Plt y z → Plt x z

def Plt_succStatement : Prop :=
  ∀ x : positive, Plt x (PArith.BinPos.Pos.succ x)

def Plt_trans_succStatement : Prop :=
  ∀ x y : positive, Plt x y → Plt x (PArith.BinPos.Pos.succ y)

def plt (x y : positive) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (Plt x y) (¬ Plt x y) := by
  exact if h : PArith.BinPos.Pos.to_nat x < PArith.BinPos.Pos.to_nat y then
    .left (show Plt x y from h)
  else
    .right (show ¬ Plt x y from h)

def Ple (x y : positive) : Prop :=
  PArith.BinPos.Pos.le x y

def Ple_reflStatement : Prop :=
  ∀ p : positive, Ple p p

def Ple_transStatement : Prop :=
  ∀ p q r : positive, Ple p q → Ple q r → Ple p r

def Plt_PleStatement : Prop :=
  ∀ p q : positive, Plt p q → Ple p q

def Ple_succStatement : Prop :=
  ∀ p : positive, Ple p (PArith.BinPos.Pos.succ p)

def Plt_Ple_transStatement : Prop :=
  ∀ p q r : positive, Plt p q → Ple q r → Plt p r

def Plt_strictStatement : Prop :=
  ∀ p : positive, ¬ Plt p p

def Plt_wfStatement : Prop :=
  WellFounded Plt

def Ppred_PltStatement : Prop :=
  ∀ x : positive, x ≠ xH → Plt (PArith.BinPos.Pos.pred x) x

/-! ## Integers -/

def zeq (x y : Z) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) :=
  ZArith.BinInt.Z.eq_dec x y

def zeq_trueStatement : Prop :=
  ∀ (A : Type u) (x : Z) (a b : A), sumboolSelect (zeq x x) a b = a

def zeq_falseStatement : Prop :=
  ∀ (A : Type u) (x y : Z) (a b : A),
    x ≠ y → sumboolSelect (zeq x y) a b = b

def zlt (x y : Z) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool
      (ZArith.BinInt.Z.lt x y) (ZArith.BinInt.Z.ge x y) := by
  match ZArith.ZArith_dec.Z_lt_dec x y with
  | .left h => exact .left h
  | .right h => exact .right (Int.le_of_not_gt h)

def zlt_trueStatement : Prop :=
  ∀ (A : Type u) (x y : Z) (a b : A),
    ZArith.BinInt.Z.lt x y → sumboolSelect (zlt x y) a b = a

def zlt_falseStatement : Prop :=
  ∀ (A : Type u) (x y : Z) (a b : A),
    ZArith.BinInt.Z.ge x y → sumboolSelect (zlt x y) a b = b

def zle (x y : Z) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool
      (ZArith.BinInt.Z.le x y) (ZArith.BinInt.Z.gt x y) :=
  ZArith.ZArith_dec.Z_le_gt_dec x y

def zle_trueStatement : Prop :=
  ∀ (A : Type u) (x y : Z) (a b : A),
    ZArith.BinInt.Z.le x y → sumboolSelect (zle x y) a b = a

def two_power_nat_OStatement : Prop :=
  two_power_nat 0 = Zpos xH

def two_power_nat_posStatement : Prop :=
  ∀ n : Nat, ZArith.BinInt.Z.gt (two_power_nat n) Z0

def two_power_nat_two_pStatement : Prop :=
  ∀ n : Nat, two_power_nat n = two_p (ZArith.BinInt.Z.of_nat n)

def two_p_monotoneStatement : Prop :=
  ∀ x y : Z,
    ZArith.BinInt.Z.le Z0 x ∧ ZArith.BinInt.Z.le x y →
      ZArith.BinInt.Z.le (two_p x) (two_p y)

def Zmax_specStatement : Prop :=
  ∀ x y : Z,
    ZArith.BinInt.Z.max x y = sumboolSelect (zlt y x) x y

def Zmax_bound_lStatement : Prop :=
  ∀ x y z : Z,
    ZArith.BinInt.Z.le x y →
      ZArith.BinInt.Z.le x (ZArith.BinInt.Z.max y z)

def Zmax_bound_rStatement : Prop :=
  ∀ x y z : Z,
    ZArith.BinInt.Z.le x z →
      ZArith.BinInt.Z.le x (ZArith.BinInt.Z.max y z)

def Z_div_mod_eqStatement : Prop :=
  ∀ a b : Z,
    ZArith.BinInt.Z.gt b Z0 →
      a = ZArith.BinInt.Z.add
        (ZArith.BinInt.Z.mul b (ZArith.BinInt.Z.div a b))
        (ZArith.BinInt.Z.modulo a b)

def Zmod_uniqueStatement : Prop :=
  ∀ x y a b : Z,
    x = ZArith.BinInt.Z.add (ZArith.BinInt.Z.mul a y) b →
    ZArith.BinInt.Z.le Z0 b ∧ ZArith.BinInt.Z.lt b y →
      ZArith.BinInt.Z.modulo x y = b

def Zdiv_uniqueStatement : Prop :=
  ∀ x y a b : Z,
    x = ZArith.BinInt.Z.add (ZArith.BinInt.Z.mul a y) b →
    ZArith.BinInt.Z.le Z0 b ∧ ZArith.BinInt.Z.lt b y →
      ZArith.BinInt.Z.div x y = a

def Zdiv_ZdivStatement : Prop :=
  ∀ a b c : Z,
    ZArith.BinInt.Z.gt b Z0 →
    ZArith.BinInt.Z.gt c Z0 →
      ZArith.BinInt.Z.div (ZArith.BinInt.Z.div a b) c =
        ZArith.BinInt.Z.div a (ZArith.BinInt.Z.mul b c)

def Zdiv_interval_1Statement : Prop :=
  ∀ lo hi a b : Z,
    ZArith.BinInt.Z.le lo Z0 →
    ZArith.BinInt.Z.gt hi Z0 →
    ZArith.BinInt.Z.gt b Z0 →
    ZArith.BinInt.Z.le (ZArith.BinInt.Z.mul lo b) a ∧
      ZArith.BinInt.Z.lt a (ZArith.BinInt.Z.mul hi b) →
    ZArith.BinInt.Z.le lo (ZArith.BinInt.Z.div a b) ∧
      ZArith.BinInt.Z.lt (ZArith.BinInt.Z.div a b) hi

def Zdivide_intervalStatement : Prop :=
  ∀ a b c : Z,
    ZArith.BinInt.Z.lt Z0 c →
    ZArith.BinInt.Z.le Z0 a ∧ ZArith.BinInt.Z.lt a b →
    ZArith.BinInt.Z.divide c a →
    ZArith.BinInt.Z.divide c b →
    ZArith.BinInt.Z.le Z0 a ∧
      ZArith.BinInt.Z.le a (ZArith.BinInt.Z.sub b c)

def Z_to_nat_negStatement : Prop :=
  ∀ n : Z, ZArith.BinInt.Z.le n Z0 → ZArith.BinInt.Z.to_nat n = 0

def Z_to_nat_maxStatement : Prop :=
  ∀ z : Z,
    ZArith.BinInt.Z.of_nat (ZArith.BinInt.Z.to_nat z) =
      ZArith.BinInt.Z.max z Z0

def align (n amount : Z) : Z :=
  ZArith.BinInt.Z.mul
    (ZArith.BinInt.Z.div
      (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.add n amount) (Zpos xH))
      amount)
    amount

def align_leStatement : Prop :=
  ∀ x y : Z,
    ZArith.BinInt.Z.gt y Z0 → ZArith.BinInt.Z.le x (align x y)

def align_dividesStatement : Prop :=
  ∀ x y : Z,
    ZArith.BinInt.Z.gt y Z0 → ZArith.BinInt.Z.divide y (align x y)

def floor (n amount : Z) : Z :=
  ZArith.BinInt.Z.mul (ZArith.BinInt.Z.div n amount) amount

def floor_intervalStatement : Prop :=
  ∀ x y : Z,
    ZArith.BinInt.Z.gt y Z0 →
    ZArith.BinInt.Z.le (floor x y) x ∧
      ZArith.BinInt.Z.lt x (ZArith.BinInt.Z.add (floor x y) y)

/-! ## Options, sums, and lists -/

def option_eq {A : Type u}
    (eqA : ∀ x y : A,
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y)) :
    ∀ x y : Option A,
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y)
  | none, none => .left rfl
  | none, some _ => .right (by intro h; cases h)
  | some _, none => .right (by intro h; cases h)
  | some x, some y =>
      match eqA x y with
      | .left h => .left (by cases h; rfl)
      | .right h => .right (by intro h'; cases h'; exact h rfl)

inductive option_rel {A : Type u} {B : Type v} :
    (R : A → B → Prop) → Option A → Option B → Prop where
  | none (R : A → B → Prop) : option_rel R none none
  | some {R : A → B → Prop} (x : A) (y : B) :
      R x y → option_rel R (some x) (some y)

def option_map {A : Type u} {B : Type v} (f : A → B) : Option A → Option B
  | none => none
  | some y => some (f y)

def sum_left_map {A : Type u} {B : Type v} {C : Type w}
    (f : A → B) : Sum A C → Sum B C
  | .inl y => .inl (f y)
  | .inr z => .inr z

def list_length_z_aux {A : Type u} : List A → Z → Z
  | [], acc => acc
  | _ :: tl, acc => list_length_z_aux tl (ZArith.BinInt.Z.succ acc)

def list_length_z_aux_shiftStatement : Prop :=
  ∀ (A : Type u) (l : List A) (n m : Z),
    list_length_z_aux l n =
      ZArith.BinInt.Z.add (list_length_z_aux l m) (ZArith.BinInt.Z.sub n m)

def list_length_z {A : Type u} (l : List A) : Z :=
  list_length_z_aux l Z0

def list_length_z_consStatement : Prop :=
  ∀ (A : Type u) (hd : A) (tl : List A),
    list_length_z (hd :: tl) = ZArith.BinInt.Z.add (list_length_z tl) (Zpos xH)

def list_length_z_posStatement : Prop :=
  ∀ (A : Type u) (l : List A), ZArith.BinInt.Z.ge (list_length_z l) Z0

def list_nth_z {A : Type u} : List A → Z → Option A
  | [], _ => none
  | hd :: tl, n =>
      match zeq n Z0 with
      | .left _ => some hd
      | .right _ => list_nth_z tl (ZArith.BinInt.Z.pred n)

def list_nth_z_inStatement : Prop :=
  ∀ (A : Type u) (l : List A) (n : Z) (x : A),
    list_nth_z l n = some x → x ∈ l

def list_nth_z_mapStatement : Prop :=
  ∀ (A : Type u) (B : Type v) (f : A → B) (l : List A) (n : Z),
    list_nth_z (List.map f l) n = option_map f (list_nth_z l n)

def list_map_extenStatement : Prop :=
  ∀ (A : Type u) (B : Type v) (f f' : A → B) (l : List A),
    (∀ x : A, x ∈ l → f x = f' x) → List.map f' l = List.map f l

def list_map_composeStatement : Prop :=
  ∀ (A : Type u) (B : Type v) (C : Type w)
    (f : A → B) (g : B → C) (l : List A),
    List.map g (List.map f l) = List.map (fun x => g (f x)) l

def list_in_map_invStatement : Prop :=
  ∀ (A : Type u) (B : Type v) (f : A → B) (l : List A) (y : B),
    y ∈ List.map f l → ∃ x : A, y = f x ∧ x ∈ l

def app_assStatement : Prop :=
  ∀ (A : Type u) (l1 l2 l3 : List A),
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)

def list_fold_left {A : Type u} {B : Type v} (f : A → B → B) : B → List A → B
  | accu, [] => accu
  | accu, x :: xs => list_fold_left f (f x accu) xs

def list_fold_right {A : Type u} {B : Type v}
    (f : A → B → B) (l : List A) (base : B) : B :=
  list_fold_left f base (List.reverse l)

def list_fold_left_appStatement : Prop :=
  ∀ (A : Type u) (B : Type v)
    (f : A → B → B) (l1 l2 : List A) (accu : B),
    list_fold_left f accu (l1 ++ l2) =
      list_fold_left f (list_fold_left f accu l1) l2

def list_fold_right_eqStatement : Prop :=
  ∀ (A : Type u) (B : Type v) (f : A → B → B) (l : List A) (base : B),
    list_fold_right f l base =
      match l with
      | [] => base
      | x :: xs => f x (list_fold_right f xs base)

def in_appStatement : Prop :=
  ∀ (A : Type u) (x : A) (l1 l2 : List A),
    x ∈ l1 ++ l2 ↔ x ∈ l1 ∨ x ∈ l2

def list_disjoint {A : Type u} (l1 l2 : List A) : Prop :=
  ∀ x y : A, x ∈ l1 → y ∈ l2 → x ≠ y

def list_disjoint_cons_leftStatement : Prop :=
  ∀ (A : Type u) (a : A) (l1 l2 : List A),
    list_disjoint (a :: l1) l2 → list_disjoint l1 l2

def list_disjoint_notinStatement : Prop :=
  ∀ (A : Type u) (l1 l2 : List A) (a : A),
    list_disjoint l1 l2 → a ∈ l1 → ¬ a ∈ l2

def list_disjoint_symStatement : Prop :=
  ∀ (A : Type u) (l1 l2 : List A),
    list_disjoint l1 l2 → list_disjoint l2 l1

private def list_mem_dec {A : Type u}
    (eqA : ∀ x y : A,
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y))
    (x : A) : (l : List A) →
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x ∈ l) (¬ x ∈ l)
  | [] => .right (by simp)
  | y :: ys =>
      match eqA x y with
      | .left h => .left (by subst y; simp)
      | .right hxy =>
          match list_mem_dec eqA x ys with
          | .left h => .left (by simp [h])
          | .right h => .right (by
              intro hx
              simp only [List.mem_cons] at hx
              cases hx with
              | inl h => exact hxy h
              | inr h' => exact h h')

def list_disjoint_dec {A : Type u}
    (eqA : ∀ x y : A,
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y))
    (l1 l2 : List A) :
      CompCert4Lean.Foundation.Logic.Support.Sumbool
        (list_disjoint l1 l2) (¬ list_disjoint l1 l2) :=
  match l1 with
  | [] => .left (by
      intro x y hx
      cases hx)
  | x :: xs =>
      match list_mem_dec eqA x l2 with
      | .left hxy => .right (by
          intro hdisj
          exact hdisj x x (by simp) hxy rfl)
      | .right hxy =>
          match list_disjoint_dec eqA xs l2 with
          | .left htail => .left (by
              intro a b ha hb
              simp only [List.mem_cons] at ha
              cases ha with
              | inl h =>
                  subst a
                  intro hab
                  apply hxy
                  simpa [hab] using hb
              | inr h => exact htail a b h hb)
          | .right htail => .right (by
              intro hdisj
              apply htail
              intro a b ha hb hab
              exact hdisj a b (by simp [ha]) hb hab)

def list_disjoint_decStatement :=
  ∀ (A : Type u)
    (eqA : ∀ x y : A,
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y))
    (l1 l2 : List A),
    CompCert4Lean.Foundation.Logic.Support.Sumbool
      (list_disjoint l1 l2) (¬ list_disjoint l1 l2)

inductive list_norepet : {A : Type u} → List A → Prop where
  | nil (A : Type u) : list_norepet (A := A) []
  | cons {A : Type u} (hd : A) {tl : List A} :
      (¬ hd ∈ tl) → list_norepet tl → list_norepet (hd :: tl)

def list_norepet_decStatement :=
  ∀ (A : Type u)
    (eqA : ∀ x y : A,
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y))
    (l : List A),
    CompCert4Lean.Foundation.Logic.Support.Sumbool
      (list_norepet l) (¬ list_norepet l)

def list_norepet_dec {A : Type u}
    (eqA : ∀ x y : A,
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y))
    (l : List A) :
      CompCert4Lean.Foundation.Logic.Support.Sumbool
        (list_norepet l) (¬ list_norepet l) :=
  match l with
  | [] => .left (list_norepet.nil A)
  | x :: xs =>
      match list_mem_dec eqA x xs with
      | .left hmem => .right (by
          intro hnr
          cases hnr with
          | cons _ hnot _ => exact hnot hmem)
      | .right hmem =>
          match list_norepet_dec eqA xs with
          | .left htail => .left (.cons x hmem htail)
          | .right htail => .right (by
              intro hnr
              cases hnr with
              | cons _ _ h => exact htail h)

def list_norepet_append_commutStatement : Prop :=
  ∀ (A : Type u) (a b : List A),
    list_norepet (a ++ b) → list_norepet (b ++ a)

def list_norepet_appStatement : Prop :=
  ∀ (A : Type u) (l1 l2 : List A),
    list_norepet (l1 ++ l2) ↔
      list_norepet l1 ∧ list_norepet l2 ∧ list_disjoint l1 l2

def list_norepet_appendStatement : Prop :=
  ∀ (A : Type u) (l1 l2 : List A),
    list_norepet l1 → list_norepet l2 → list_disjoint l1 l2 →
      list_norepet (l1 ++ l2)

def list_norepet_append_leftStatement : Prop :=
  ∀ (A : Type u) (l1 l2 : List A),
    list_norepet (l1 ++ l2) → list_norepet l1

inductive is_tail {A : Type u} : List A → List A → Prop where
  | refl (c : List A) : is_tail c c
  | cons (i : A) {c1 c2 : List A} : is_tail c1 c2 → is_tail c1 (i :: c2)

def is_tail_inStatement : Prop :=
  ∀ (A : Type u) (i : A) (c1 c2 : List A),
    is_tail (i :: c1) c2 → i ∈ c2

def is_tail_cons_leftStatement : Prop :=
  ∀ (A : Type u) (i : A) (c1 c2 : List A),
    is_tail (i :: c1) c2 → is_tail c1 c2

def is_tail_transStatement : Prop :=
  ∀ (A : Type u) (l1 l2 : List A),
    is_tail l1 l2 → ∀ l3 : List A, is_tail l2 l3 → is_tail l1 l3

inductive list_forall2 {A : Type u} {B : Type v} :
    (P : A → B → Prop) → List A → List B → Prop where
  | nil (P : A → B → Prop) : list_forall2 P [] []
  | cons {P : A → B → Prop} (a1 : A) {al : List A} (b1 : B) {bl : List B} :
      P a1 b1 → list_forall2 P al bl → list_forall2 P (a1 :: al) (b1 :: bl)

open list_forall2 renaming nil → list_forall2_nil
export _root_ (list_forall2_nil)

def list_forall2_appStatement : Prop :=
  ∀ (A : Type u) (B : Type v) (P : A → B → Prop)
    (a2 : List A) (b2 : List B) (a1 : List A) (b1 : List B),
    list_forall2 P a1 b1 → list_forall2 P a2 b2 →
      list_forall2 P (a1 ++ a2) (b1 ++ b2)

def list_forall2_lengthStatement : Prop :=
  ∀ (A : Type u) (B : Type v) (P : A → B → Prop)
    (l1 : List A) (l2 : List B),
    list_forall2 P l1 l2 → List.length l1 = List.length l2

def list_forall2_in_leftStatement : Prop :=
  ∀ (A : Type u) (B : Type v) (P : A → B → Prop) (x1 : A)
    (l1 : List A) (l2 : List B),
    list_forall2 P l1 l2 → x1 ∈ l1 → ∃ x2 : B, x2 ∈ l2 ∧ P x1 x2

/-! ## Boolean views of proof-carrying decisions -/

def proj_sumbool {P Q : Prop}
    (a : CompCert4Lean.Foundation.Logic.Support.Sumbool P Q) : Bool :=
  match a with
  | .left _ => true
  | .right _ => false

def proj_sumbool_trueStatement : Prop :=
  ∀ (P Q : Prop) (a : CompCert4Lean.Foundation.Logic.Support.Sumbool P Q),
    proj_sumbool a = true → P

def proj_sumbool_is_trueStatement : Prop :=
  ∀ (P : Prop)
    (a : CompCert4Lean.Foundation.Logic.Support.Sumbool P (¬ P)),
    P → proj_sumbool a = true

def dec_eq_trueStatement : Prop :=
  ∀ (A : Type u)
    (dec_eq : ∀ x y : A,
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y))
    (B : Type v) (x : A) (ifso ifnot : B),
    sumboolSelect (dec_eq x x) ifso ifnot = ifso

def dec_eq_falseStatement : Prop :=
  ∀ (A : Type u)
    (dec_eq : ∀ x y : A,
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y))
    (B : Type v) (x y : A) (ifso ifnot : B),
    x ≠ y → sumboolSelect (dec_eq x y) ifso ifnot = ifnot

def dec_eq_symStatement : Prop :=
  ∀ (A : Type u)
    (dec_eq : ∀ x y : A,
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y))
    (B : Type v) (x y : A) (ifso ifnot : B),
    sumboolSelect (dec_eq x y) ifso ifnot =
      sumboolSelect (dec_eq y x) ifso ifnot

def pred_dec_trueStatement : Prop :=
  ∀ (P : Prop) (dec : CompCert4Lean.Foundation.Logic.Support.Sumbool P (¬ P))
    (A : Type u) (a b : A),
    P → sumboolSelect dec a b = a

def pred_dec_falseStatement : Prop :=
  ∀ (P : Prop) (dec : CompCert4Lean.Foundation.Logic.Support.Sumbool P (¬ P))
    (A : Type u) (a b : A),
    (¬ P) → sumboolSelect dec a b = b

/-! ## Lexicographic order -/

inductive lex_ord {A : Type u} {B : Type v} :
    (ordA : A → A → Prop) → (ordB : B → B → Prop) → A × B → A × B → Prop where
  | left (ordA : A → A → Prop) (ordB : B → B → Prop)
      (a1 : A) (b1 : B) (a2 : A) (b2 : B) :
      ordA a1 a2 → lex_ord ordA ordB (a1, b1) (a2, b2)
  | right (ordA : A → A → Prop) (ordB : B → B → Prop)
      (a : A) (b1 : B) (b2 : B) :
      ordB b1 b2 → lex_ord ordA ordB (a, b1) (a, b2)

open lex_ord renaming left → lex_ord_left, right → lex_ord_right
export _root_ (lex_ord_left lex_ord_right)

def wf_lex_ordStatement : Prop :=
  ∀ (A : Type u) (B : Type v) (ordA : A → A → Prop) (ordB : B → B → Prop),
    WellFounded ordA → WellFounded ordB → WellFounded (lex_ord ordA ordB)

end CompCert4Lean.Lib.Coqlib

namespace CompCert4Lean.Lib.Coqlib

theorem list_forall2_length : list_forall2_lengthStatement := by
  intro A B P l1 l2 h
  induction h with
  | nil => rfl
  | cons a1 b1 hp htail ih =>
      simp_all

theorem dec_eq_false : dec_eq_falseStatement := by
  intro A dec_eq B x y ifso ifnot hxy
  cases h : dec_eq x y with
  | left heq => exact False.elim (hxy heq)
  | right hne => rfl

theorem Plt_strict : Plt_strictStatement := by
  intro p hp
  exact (Nat.lt_irrefl _ hp)

theorem app_ass : app_assStatement := by
  intro A l1 l2 l3
  induction l1 with
  | nil => rfl
  | cons a l ih =>
      simp [ih]

theorem peq_true : peq_trueStatement := by
  intro A x a b
  cases h : peq x x with
  | left heq => rfl
  | right hne => exact False.elim (hne rfl)

theorem peq_false : peq_falseStatement := by
  intro A x y a b hxy
  cases h : peq x y with
  | left heq => exact False.elim (hxy heq)
  | right hne => rfl

theorem Plt_ne : Plt_neStatement := by
  intro x y hxy heq
  subst y
  exact Nat.lt_irrefl _ hxy

theorem Plt_trans : Plt_transStatement := by
  intro x y z hxy hyz
  exact Nat.lt_trans hxy hyz

end CompCert4Lean.Lib.Coqlib

namespace CompCert4Lean.Lib.Coqlib

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem coqlib_posToNat_succ (p : positive) :
    PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.succ p) =
      PArith.BinPos.Pos.to_nat p + 1 := by
  induction p with
  | xH => rfl
  | xI p ih =>
      change 2 * PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.succ p) =
        (2 * PArith.BinPos.Pos.to_nat p + 1) + 1
      rw [ih]
      omega
  | xO p ih => rfl

theorem Plt_succ : Plt_succStatement := by
  intro p
  change PArith.BinPos.Pos.to_nat p <
    PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.succ p)
  rw [coqlib_posToNat_succ]
  omega

theorem Plt_trans_succ : Plt_trans_succStatement := by
  intro x y hxy
  change PArith.BinPos.Pos.to_nat x < PArith.BinPos.Pos.to_nat y at hxy
  change PArith.BinPos.Pos.to_nat x <
    PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.succ y)
  rw [coqlib_posToNat_succ]
  omega

theorem Ple_refl : Ple_reflStatement := by
  intro p
  exact Nat.le_refl _

theorem Ple_trans : Ple_transStatement := by
  intro p q r hpq hqr
  exact Nat.le_trans hpq hqr

end CompCert4Lean.Lib.Coqlib

namespace CompCert4Lean.Lib.Coqlib

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem Plt_Ple : Plt_PleStatement := by
  intro p q hpq
  exact Nat.le_of_lt hpq

theorem Ple_succ : Ple_succStatement := by
  intro p
  exact Plt_Ple p (PArith.BinPos.Pos.succ p) (Plt_succ p)

theorem Plt_Ple_trans : Plt_Ple_transStatement := by
  intro p q r hpq hqr
  exact Nat.lt_of_lt_of_le hpq hqr

theorem Plt_wf : Plt_wfStatement := by
  exact InvImage.wf
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat
    Nat.lt_wfRel.wf

end CompCert4Lean.Lib.Coqlib

namespace CompCert4Lean.Lib.Coqlib

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem coqlib_posToNat_pred_double_lt (p : positive) :
    posToNat (PArith.BinPos.Pos.pred_double p) < 2 * posToNat p := by
  induction p with
  | xH => simp [PArith.BinPos.Pos.pred_double, posToNat]
  | xI p ih =>
      simp [PArith.BinPos.Pos.pred_double, posToNat] <;> omega
  | xO p ih =>
      simp [PArith.BinPos.Pos.pred_double, posToNat] <;> omega

theorem Ppred_Plt : Ppred_PltStatement := by
  intro x hx
  cases x with
  | xH => exact False.elim (hx rfl)
  | xI p =>
      change PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.pred (xI p)) <
        PArith.BinPos.Pos.to_nat (xI p)
      simp [PArith.BinPos.Pos.pred, PArith.BinPos.Pos.to_nat,
        posToNat]
  | xO p =>
      change PArith.BinPos.Pos.to_nat (PArith.BinPos.Pos.pred (xO p)) <
        PArith.BinPos.Pos.to_nat (xO p)
      simpa [PArith.BinPos.Pos.pred, PArith.BinPos.Pos.to_nat,
        posToNat] using coqlib_posToNat_pred_double_lt p

theorem zeq_true : zeq_trueStatement := by
  intro A x a b
  cases h : zeq x x with
  | left heq => rfl
  | right hne => exact False.elim (hne rfl)

theorem zeq_false : zeq_falseStatement := by
  intro A x y a b hxy
  cases h : zeq x y with
  | left heq => exact False.elim (hxy heq)
  | right hne => rfl

theorem zlt_true : zlt_trueStatement := by
  intro A x y a b hxy
  cases h : zlt x y with
  | left hlt => rfl
  | right hge =>
      exfalso
      change intOfZ x < intOfZ y at hxy
      change intOfZ y ≤ intOfZ x at hge
      omega

end CompCert4Lean.Lib.Coqlib

namespace CompCert4Lean.Lib.Coqlib

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem zlt_false : zlt_falseStatement := by
  intro A x y a b hxy
  cases h : zlt x y with
  | left hlt =>
      exfalso
      change intOfZ y <= intOfZ x at hxy
      change intOfZ x < intOfZ y at hlt
      omega
  | right hge => rfl

theorem zle_true : zle_trueStatement := by
  intro A x y a b hxy
  cases h : zle x y with
  | left hle => rfl
  | right hgt =>
      exfalso
      change intOfZ x <= intOfZ y at hxy
      change intOfZ y < intOfZ x at hgt
      omega

theorem two_power_nat_O : two_power_nat_OStatement := by
  change two_power_nat 0 = Zpos xH
  rfl

theorem two_power_nat_pos : two_power_nat_posStatement := by
  intro n
  change 0 < intOfZ (two_power_nat n)
  unfold two_power_nat ZArith.Zpower.two_power_nat
  unfold ZArith.BinInt.Z.pow ZArith.BinInt.Z.of_nat
  simp only [intOfZ_zOfInt]
  have hbase : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
  rw [hbase]
  have hn : Not (Int.ofNat n < 0) := by simp
  split
  case isTrue h =>
    exact (hn h).elim
  case isFalse h =>
    simp only [intOfZ_zOfInt]
    exact Int.pow_pos (by decide)

end CompCert4Lean.Lib.Coqlib

namespace CompCert4Lean.Lib.Coqlib

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem two_power_nat_two_p : two_power_nat_two_pStatement := by
  intro n
  rfl

end CompCert4Lean.Lib.Coqlib

namespace CompCert4Lean.Lib.Coqlib

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem coqlib_nat_pow_two_mono :
    ∀ m n : Nat, m ≤ n → (2 : Int) ^ m ≤ (2 : Int) ^ n := by
  intro m n h
  induction h with
  | refl => exact Int.le_refl _
  | @step n h ih =>
      apply Int.le_trans ih
      rw [Int.pow_succ]
      have hp : 0 ≤ (2 : Int) ^ n := Int.pow_nonneg (by omega)
      omega

theorem two_p_monotone : two_p_monotoneStatement := by
  intro x y h
  change intOfZ (two_p x) ≤ intOfZ (two_p y)
  change 0 ≤ intOfZ x ∧ intOfZ x ≤ intOfZ y at h
  have hnat : Int.toNat (intOfZ x) ≤ Int.toNat (intOfZ y) :=
    Int.toNat_le_toNat h.2
  unfold two_p ZArith.Zpower.two_p ZArith.BinInt.Z.pow
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [intOfZ_zOfInt]
  change (2 : Int) ^ (Int.toNat (intOfZ x)) ≤
    (2 : Int) ^ (Int.toNat (intOfZ y))
  exact coqlib_nat_pow_two_mono _ _ hnat

end CompCert4Lean.Lib.Coqlib

namespace CompCert4Lean.Lib.Coqlib

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem Zmax_spec : Zmax_specStatement := by
  intro x y
  by_cases h : intOfZ y < intOfZ x
  · have hle : ¬ intOfZ x ≤ intOfZ y := by omega
    rw [ZArith.BinInt.Z.max, if_neg hle]
    cases hz : zlt y x with
    | left hlt => rfl
    | right hge =>
        exfalso
        change intOfZ x ≤ intOfZ y at hge
        omega
  · have hle : intOfZ x ≤ intOfZ y := Int.le_of_not_gt h
    rw [ZArith.BinInt.Z.max, if_pos hle]
    cases hz : zlt y x with
    | left hlt => exact False.elim (h hlt)
    | right hge => rfl

end CompCert4Lean.Lib.Coqlib

namespace CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
theorem Zmax_bound_l : Zmax_bound_lStatement := by
  intro x y z hxy
  change intOfZ x ≤ intOfZ (ZArith.BinInt.Z.max y z)
  change intOfZ x ≤ intOfZ y at hxy
  by_cases hyz : intOfZ y ≤ intOfZ z
  · simp [ZArith.BinInt.Z.max, hyz]
    exact Int.le_trans hxy hyz
  · simp [ZArith.BinInt.Z.max, hyz]
    exact hxy
end CompCert4Lean.Lib.Coqlib

namespace CompCert4Lean.Lib.Coqlib

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem Zmax_bound_r : Zmax_bound_rStatement := by
  intro x y z hxz
  change intOfZ x ≤ intOfZ (ZArith.BinInt.Z.max y z)
  change intOfZ x ≤ intOfZ z at hxz
  by_cases hyz : intOfZ y ≤ intOfZ z
  · simp [ZArith.BinInt.Z.max, hyz]
    exact hxz
  · simp [ZArith.BinInt.Z.max, hyz]
    exact Int.le_trans hxz (Int.le_of_not_le hyz)

theorem Z_div_mod_eq : Z_div_mod_eqStatement := by
  intro a b hb
  exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Z_div_mod_eq_full a b

theorem Zmod_unique : Zmod_uniqueStatement := by
  intro x y a b hxy hrange
  change 0 ≤ intOfZ b ∧ intOfZ b < intOfZ y at hrange
  have hy : 0 < intOfZ y := by omega
  have hxy' := congrArg intOfZ hxy
  simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
    intOfZ_zOfInt] at hxy'
  have hform : intOfZ b + intOfZ y * intOfZ a = intOfZ x := by
    calc
      intOfZ b + intOfZ y * intOfZ a = intOfZ a * intOfZ y + intOfZ b := by
        rw [Int.mul_comm (intOfZ y) (intOfZ a), Int.add_comm]
      _ = intOfZ x := hxy'.symm
  have hu := (Int.ediv_emod_unique (a := intOfZ x) (b := intOfZ y)
    (q := intOfZ a) (r := intOfZ b) hy).mpr
    ⟨hform, hrange.1, hrange.2⟩
  apply intOfZ_injective
  simp only [ZArith.BinInt.Z.modulo, intOfZ_zOfInt]
  change (if intOfZ y = 0 then intOfZ x
    else if 0 < intOfZ y then Int.emod (intOfZ x) (intOfZ y) else _) = _
  have hy0 : intOfZ y ≠ 0 := Int.ne_of_gt hy
  simp [hy, hy0]
  exact hu.2

theorem Zdiv_unique : Zdiv_uniqueStatement := by
  intro x y a b hxy hrange
  change 0 ≤ intOfZ b ∧ intOfZ b < intOfZ y at hrange
  have hy : 0 < intOfZ y := by omega
  have hxy' := congrArg intOfZ hxy
  simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
    intOfZ_zOfInt] at hxy'
  have hform : intOfZ b + intOfZ y * intOfZ a = intOfZ x := by
    calc
      intOfZ b + intOfZ y * intOfZ a = intOfZ a * intOfZ y + intOfZ b := by
        rw [Int.mul_comm (intOfZ y) (intOfZ a), Int.add_comm]
      _ = intOfZ x := hxy'.symm
  have hu := (Int.ediv_emod_unique (a := intOfZ x) (b := intOfZ y)
    (q := intOfZ a) (r := intOfZ b) hy).mpr
    ⟨hform, hrange.1, hrange.2⟩
  apply intOfZ_injective
  simp only [ZArith.BinInt.Z.div, intOfZ_zOfInt]
  change (if intOfZ y = 0 then 0
    else if 0 < intOfZ y then Int.ediv (intOfZ x) (intOfZ y) else _) = _
  have hy0 : intOfZ y ≠ 0 := Int.ne_of_gt hy
  simp [hy, hy0]
  exact hu.1

end CompCert4Lean.Lib.Coqlib

namespace CompCert4Lean.Lib.Coqlib

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem Z_to_nat_neg : Z_to_nat_negStatement := by
  intro n hn
  exact Int.toNat_of_nonpos hn

theorem Zdiv_Zdiv : Zdiv_ZdivStatement := by
  intro a b c hb hc
  have div_eq_ediv : ∀ (x y : Z), 0 < intOfZ y →
      intOfZ (ZArith.BinInt.Z.div x y) = Int.ediv (intOfZ x) (intOfZ y) := by
    intro x y hy
    have hy0 : intOfZ y ≠ 0 := Int.ne_of_gt hy
    have hrem_nonneg : 0 ≤ (intOfZ x).emod (intOfZ y) :=
      Int.emod_nonneg _ hy0
    have hrem_lt : (intOfZ x).emod (intOfZ y) < intOfZ y :=
      Int.emod_lt_of_pos _ hy
    have hxy : x = ZArith.BinInt.Z.add
        (ZArith.BinInt.Z.mul (zOfInt ((intOfZ x).ediv (intOfZ y))) y)
        (zOfInt ((intOfZ x).emod (intOfZ y))) := by
      apply intOfZ_injective
      simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
      exact (Int.ediv_mul_add_emod (intOfZ x) (intOfZ y)).symm
    have hq := CompCert4Lean.Lib.Coqlib.Zdiv_unique x y
      (zOfInt ((intOfZ x).ediv (intOfZ y)))
      (zOfInt ((intOfZ x).emod (intOfZ y))) hxy
      ⟨by
        unfold ZArith.BinInt.Z.le
        rw [show intOfZ ZArith.BinInt.Z.Z0 = (0 : Int) by rfl,
          intOfZ_zOfInt]
        exact hrem_nonneg,
        by
        unfold ZArith.BinInt.Z.lt
        rw [intOfZ_zOfInt]
        exact hrem_lt⟩
    simpa only [intOfZ_zOfInt] using congrArg intOfZ hq
  have hb' : 0 < intOfZ b := hb
  have hc' : 0 < intOfZ c := hc
  have hbc' : 0 < intOfZ (ZArith.BinInt.Z.mul b c) := by
    simp only [ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    exact Int.mul_pos hb' hc'
  have hleft := div_eq_ediv (ZArith.BinInt.Z.div a b) c hc'
  have hinner := div_eq_ediv a b hb'
  have hright := div_eq_ediv a (ZArith.BinInt.Z.mul b c) hbc'
  have hright' :
      intOfZ (ZArith.BinInt.Z.div a (ZArith.BinInt.Z.mul b c)) =
        (intOfZ a).ediv (intOfZ b * intOfZ c) := by
    simpa only [ZArith.BinInt.Z.mul, intOfZ_zOfInt] using hright
  apply intOfZ_injective
  rw [hleft, hinner, hright']
  change ((intOfZ a / intOfZ b) / intOfZ c) =
    intOfZ a / (intOfZ b * intOfZ c)
  rw [Int.ediv_ediv]
  simp [Int.not_lt_of_ge (Int.le_of_lt hb')]

end CompCert4Lean.Lib.Coqlib

namespace CompCert4Lean.Lib.Coqlib

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem coqlib_zdiv_eq_ediv_pos (x y : Z) (hy : 0 < intOfZ y) :
    intOfZ (ZArith.BinInt.Z.div x y) = Int.ediv (intOfZ x) (intOfZ y) := by
  have hy0 : intOfZ y ≠ 0 := Int.ne_of_gt hy
  have hrem_nonneg : 0 ≤ (intOfZ x).emod (intOfZ y) :=
    Int.emod_nonneg _ hy0
  have hrem_lt : (intOfZ x).emod (intOfZ y) < intOfZ y :=
    Int.emod_lt_of_pos _ hy
  have hxy : x = ZArith.BinInt.Z.add
      (ZArith.BinInt.Z.mul (zOfInt ((intOfZ x).ediv (intOfZ y))) y)
      (zOfInt ((intOfZ x).emod (intOfZ y))) := by
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    exact (Int.ediv_mul_add_emod (intOfZ x) (intOfZ y)).symm
  have hq := CompCert4Lean.Lib.Coqlib.Zdiv_unique x y
    (zOfInt ((intOfZ x).ediv (intOfZ y)))
    (zOfInt ((intOfZ x).emod (intOfZ y))) hxy
    ⟨by
      unfold ZArith.BinInt.Z.le
      rw [show intOfZ ZArith.BinInt.Z.Z0 = (0 : Int) by rfl,
        intOfZ_zOfInt]
      exact hrem_nonneg,
      by
      unfold ZArith.BinInt.Z.lt
      rw [intOfZ_zOfInt]
      exact hrem_lt⟩
  simpa only [intOfZ_zOfInt] using congrArg intOfZ hq

theorem Zdiv_interval_1 : Zdiv_interval_1Statement := by
  intro lo hi a b hlo hhi hb hab
  change intOfZ lo ≤ 0 at hlo
  change 0 < intOfZ hi at hhi
  change 0 < intOfZ b at hb
  have hab' : intOfZ lo * intOfZ b ≤ intOfZ a ∧
      intOfZ a < intOfZ hi * intOfZ b := by
    simpa only [ZArith.BinInt.Z.le, ZArith.BinInt.Z.lt,
      ZArith.BinInt.Z.mul, intOfZ_zOfInt] using hab
  change intOfZ lo ≤ intOfZ (ZArith.BinInt.Z.div a b) ∧
    intOfZ (ZArith.BinInt.Z.div a b) < intOfZ hi
  rw [coqlib_zdiv_eq_ediv_pos a b hb]
  constructor
  · exact (Int.le_ediv_iff_mul_le hb).2 hab'.1
  · exact (Int.ediv_lt_iff_lt_mul hb).2 hab'.2

end CompCert4Lean.Lib.Coqlib

namespace CompCert4Lean.Lib.Coqlib

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem Zdivide_interval : Zdivide_intervalStatement := by
  intro a b c hc hab hca hcb
  change 0 < intOfZ c at hc
  have hab' : 0 ≤ intOfZ a ∧ intOfZ a < intOfZ b := by
    constructor
    · simpa [ZArith.BinInt.Z.le, intOfZ] using hab.1
    · simpa only [ZArith.BinInt.Z.lt] using hab.2
  rcases hca with ⟨ka, hka⟩
  rcases hcb with ⟨kb, hkb⟩
  have hka' : intOfZ a = intOfZ c * intOfZ ka := by
    simpa only [ZArith.BinInt.Z.mul, intOfZ_zOfInt] using congrArg intOfZ hka
  have hkb' : intOfZ b = intOfZ c * intOfZ kb := by
    simpa only [ZArith.BinInt.Z.mul, intOfZ_zOfInt] using congrArg intOfZ hkb
  have hkl_mul : intOfZ c * intOfZ ka < intOfZ c * intOfZ kb := by
    calc
      intOfZ c * intOfZ ka = intOfZ a := hka'.symm
      _ < intOfZ b := hab'.2
      _ = intOfZ c * intOfZ kb := hkb'
  have hkl : intOfZ ka < intOfZ kb := (Int.mul_lt_mul_left hc).mp hkl_mul
  have hkl_succ : intOfZ ka + 1 ≤ intOfZ kb := by omega
  have hmul : intOfZ c * (intOfZ ka + 1) ≤ intOfZ c * intOfZ kb :=
    (Int.mul_le_mul_left hc).2 hkl_succ
  have hsum : intOfZ a + intOfZ c ≤ intOfZ b := by
    calc
      intOfZ a + intOfZ c = intOfZ c * (intOfZ ka + 1) := by
        rw [hka']
        simp [Int.mul_add, Int.mul_one]
      _ ≤ intOfZ b := by
        rw [hkb']
        exact hmul
  constructor
  · exact hab.1
  · unfold ZArith.BinInt.Z.le ZArith.BinInt.Z.sub
    rw [intOfZ_zOfInt]
    omega

end CompCert4Lean.Lib.Coqlib

namespace CompCert4Lean.Lib.Coqlib

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem Z_to_nat_max : Z_to_nat_maxStatement := by
  intro z
  apply intOfZ_injective
  simp only [ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.to_nat, intOfZ_zOfInt]
  change (Int.toNat (intOfZ z) : Int) = _
  rw [Int.ofNat_toNat]
  have hz0 : intOfZ Z0 = (0 : Int) := rfl
  by_cases h : intOfZ z ≤ 0
  · rw [Int.max_eq_right h]
    unfold ZArith.BinInt.Z.max
    have h' : intOfZ z ≤ intOfZ Z0 := by rw [hz0]; exact h
    simp [h, hz0]
  · have hp : 0 ≤ intOfZ z := by omega
    rw [Int.max_eq_left hp]
    unfold ZArith.BinInt.Z.max
    have h' : ¬ intOfZ z ≤ intOfZ Z0 := by rw [hz0]; exact h
    simp [h, hz0]

theorem align_le : align_leStatement := by
  intro x y hy
  change intOfZ x ≤ intOfZ (align x y)
  unfold align
  let a : Z := ZArith.BinInt.Z.sub (ZArith.BinInt.Z.add x y) (Zpos xH)
  have hdiv := Z_div_mod_eq a y hy
  have hmod := ZArith.Zdiv.Z_mod_lt a y hy
  change 0 ≤ intOfZ (ZArith.BinInt.Z.modulo a y) ∧
    intOfZ (ZArith.BinInt.Z.modulo a y) < intOfZ y at hmod
  have hdiv' := congrArg intOfZ hdiv
  simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
    intOfZ_zOfInt] at hdiv'
  have hbase : intOfZ a = intOfZ x + intOfZ y - 1 := by
    dsimp [a]
    unfold ZArith.BinInt.Z.sub ZArith.BinInt.Z.add
    simp only [intOfZ_zOfInt]
    have hxH : intOfZ (Zpos xH) = (1 : Int) := rfl
    rw [hxH]
  rw [hbase] at hdiv'
  rw [Int.mul_comm (intOfZ y)] at hdiv'
  change intOfZ x ≤ intOfZ (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.div a y) y)
  have hprod : intOfZ (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.div a y) y) =
      intOfZ (ZArith.BinInt.Z.div a y) * intOfZ y := by
    change intOfZ (zOfInt (intOfZ (ZArith.BinInt.Z.div a y) * intOfZ y)) = _
    rw [intOfZ_zOfInt]
  rw [hprod]
  have hy' : 0 < intOfZ y := hy
  omega

theorem align_divides : align_dividesStatement := by
  intro x y hy
  refine ⟨ZArith.BinInt.Z.div (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.add x y) (Zpos xH)) y, ?_⟩
  unfold align
  apply intOfZ_injective
  simp only [ZArith.BinInt.Z.mul, intOfZ_zOfInt]
  exact Int.mul_comm _ _

theorem floor_interval : floor_intervalStatement := by
  intro x y hy
  unfold floor
  change intOfZ (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.div x y) y) ≤ intOfZ x ∧
    intOfZ x < intOfZ (ZArith.BinInt.Z.add
      (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.div x y) y) y)
  have hdiv := Z_div_mod_eq x y hy
  have hmod := ZArith.Zdiv.Z_mod_lt x y hy
  change 0 ≤ intOfZ (ZArith.BinInt.Z.modulo x y) ∧
    intOfZ (ZArith.BinInt.Z.modulo x y) < intOfZ y at hmod
  have hdiv' := congrArg intOfZ hdiv
  simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
    intOfZ_zOfInt] at hdiv'
  rw [Int.mul_comm (intOfZ y)] at hdiv'
  have hprod : intOfZ (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.div x y) y) =
      intOfZ (ZArith.BinInt.Z.div x y) * intOfZ y := by
    change intOfZ (zOfInt (intOfZ (ZArith.BinInt.Z.div x y) * intOfZ y)) = _
    rw [intOfZ_zOfInt]
  rw [hprod]
  have hadd : intOfZ (ZArith.BinInt.Z.add
      (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.div x y) y) y) =
      intOfZ (ZArith.BinInt.Z.div x y) * intOfZ y + intOfZ y := by
    unfold ZArith.BinInt.Z.add
    rw [intOfZ_zOfInt]
    rw [hprod]
  rw [hadd]
  have hy' : 0 < intOfZ y := hy
  constructor <;> omega

end CompCert4Lean.Lib.Coqlib

namespace CompCert4Lean.Lib.Coqlib

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem list_length_z_aux_shift : list_length_z_aux_shiftStatement := by
  intro A l
  induction l with
  | nil =>
      intro n m
      apply intOfZ_injective
      simp only [list_length_z_aux, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
        intOfZ_zOfInt]
      simpa [Int.add_comm] using
        (Int.sub_add_cancel (intOfZ n) (intOfZ m)).symm
  | cons hd tl ih =>
      intro n m
      simp only [list_length_z_aux]
      have h := ih (ZArith.BinInt.Z.succ n) (ZArith.BinInt.Z.succ m)
      have hsub : ZArith.BinInt.Z.sub (ZArith.BinInt.Z.succ n)
          (ZArith.BinInt.Z.succ m) = ZArith.BinInt.Z.sub n m := by
        apply intOfZ_injective
        simp only [ZArith.BinInt.Z.succ, ZArith.BinInt.Z.add,
          ZArith.BinInt.Z.sub, intOfZ_zOfInt]
        omega
      rw [hsub] at h
      exact h

end CompCert4Lean.Lib.Coqlib

namespace CompCert4Lean.Lib.Coqlib

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem list_length_z_cons : list_length_z_consStatement := by
  intro A hd tl
  unfold list_length_z
  simp only [list_length_z_aux]
  have h := list_length_z_aux_shift A tl (ZArith.BinInt.Z.succ ZArith.BinInt.Z.Z0)
    ZArith.BinInt.Z.Z0
  rw [h]
  apply congrArg (ZArith.BinInt.Z.add (list_length_z_aux tl ZArith.BinInt.Z.Z0))
  apply intOfZ_injective
  simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.succ,
    ZArith.BinInt.Z.add, intOfZ_zOfInt]
  rfl

end CompCert4Lean.Lib.Coqlib

namespace CompCert4Lean.Lib.Coqlib

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem list_length_z_pos : list_length_z_posStatement := by
  intro A l
  induction l with
  | nil =>
      change intOfZ Z0 ≤ intOfZ (list_length_z [])
      simp [list_length_z, list_length_z_aux]
  | cons hd tl ih =>
      rw [list_length_z_cons]
      unfold ZArith.BinInt.Z.ge ZArith.BinInt.Z.add
      simp only [intOfZ_zOfInt]
      have hZero : intOfZ Z0 = 0 := by rfl
      have htl : 0 ≤ intOfZ (list_length_z tl) := by
        exact ih
      have hOne : intOfZ (Zpos xH) = 1 := by
        rfl
      omega

end CompCert4Lean.Lib.Coqlib

namespace CompCert4Lean.Lib.Coqlib

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem list_nth_z_in : list_nth_z_inStatement := by
  intro A l
  induction l with
  | nil =>
      intro n x h
      simp [list_nth_z] at h
  | cons hd tl ih =>
      intro n x h
      simp only [list_nth_z] at h
      split at h
      next hzero =>
        simp_all
      next hnonzero =>
        exact List.mem_cons_of_mem hd (ih (ZArith.BinInt.Z.pred n) x h)

end CompCert4Lean.Lib.Coqlib

namespace CompCert4Lean.Lib.Coqlib

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem list_nth_z_map : list_nth_z_mapStatement := by
  intro A B f l
  induction l with
  | nil =>
      intro n
      rfl
  | cons hd tl ih =>
      intro n
      simp only [List.map, list_nth_z, option_map]
      split
      · rfl
      · exact ih (ZArith.BinInt.Z.pred n)

theorem list_map_exten : list_map_extenStatement := by
  intro A B f f' l h
  induction l with
  | nil => rfl
  | cons hd tl ih =>
      simp only [List.map]
      have hhd : f' hd = f hd := (h hd (by simp)).symm
      have htl : List.map f' tl = List.map f tl := by
        apply ih
        intro x hx
        exact h x (by simp [hx])
      simp [hhd, htl]

theorem list_map_compose : list_map_composeStatement := by
  intro A B C f g l
  induction l with
  | nil => rfl
  | cons hd tl ih =>
      simp only [List.map]
      rw [ih]

theorem list_in_map_inv : list_in_map_invStatement := by
  intro A B f l y h
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
      simp only [List.map, List.mem_cons] at h
      rcases h with hhead | htail
      · exact ⟨hd, hhead, by simp⟩
      · obtain ⟨x, hfx, hxl⟩ := ih htail
        exact ⟨x, hfx, by simp [hxl]⟩

end CompCert4Lean.Lib.Coqlib

namespace CompCert4Lean.Lib.Coqlib

theorem list_fold_left_app : list_fold_left_appStatement := by
  intro A B f l1
  induction l1 with
  | nil =>
      intro l2 accu
      rfl
  | cons x xs ih =>
      intro l2 accu
      simp only [List.cons_append, list_fold_left]
      exact ih l2 (f x accu)

theorem list_fold_right_eq : list_fold_right_eqStatement := by
  intro A B f l base
  cases l with
  | nil => rfl
  | cons x xs =>
      simp only [list_fold_right, List.reverse_cons]
      rw [list_fold_left_app]
      rfl

theorem in_app : in_appStatement := by
  intro A x l1 l2
  exact List.mem_append

theorem list_disjoint_cons_left : list_disjoint_cons_leftStatement := by
  intro A a l1 l2 h x y hx hy
  exact h x y (List.Mem.tail a hx) hy

end CompCert4Lean.Lib.Coqlib

namespace CompCert4Lean.Lib.Coqlib

private theorem coqlib_list_norepet_to_nodup {A : Type u} {l : List A} :
    list_norepet l → l.Nodup := by
  intro h
  induction h with
  | nil => exact List.nodup_nil
  | cons hd hmem htail ih =>
      exact (List.nodup_cons).2 ⟨hmem, ih⟩

private theorem coqlib_list_norepet_of_nodup {A : Type u} {l : List A} :
    l.Nodup → list_norepet l := by
  intro h
  cases l with
  | nil => exact list_norepet.nil A
  | cons hd tl =>
      have h' := (List.nodup_cons).mp h
      exact list_norepet.cons hd h'.1 (coqlib_list_norepet_of_nodup h'.2)

theorem list_disjoint_notin : list_disjoint_notinStatement := by
  intro A l1 l2 a hdisj ha hb
  exact hdisj a a ha hb rfl

theorem list_disjoint_sym : list_disjoint_symStatement := by
  intro A l1 l2 h x y hx hy hxy
  exact h y x hy hx hxy.symm

theorem list_norepet_app : list_norepet_appStatement := by
  intro A l1 l2
  constructor
  · intro h
    have hn : (l1 ++ l2).Nodup := coqlib_list_norepet_to_nodup h
    have hs := (List.nodup_append).mp hn
    refine ⟨coqlib_list_norepet_of_nodup hs.1,
      coqlib_list_norepet_of_nodup hs.2.1, ?_⟩
    intro x y hx hy
    exact hs.2.2 x hx y hy
  · rintro ⟨h1, h2, hd⟩
    apply coqlib_list_norepet_of_nodup
    apply (List.nodup_append).mpr
    refine ⟨coqlib_list_norepet_to_nodup h1,
      coqlib_list_norepet_to_nodup h2, ?_⟩
    intro x hx y hy
    exact hd x y hx hy

theorem list_norepet_append_commut : list_norepet_append_commutStatement := by
  intro A a b h
  apply coqlib_list_norepet_of_nodup
  have hs := (List.nodup_append).mp (coqlib_list_norepet_to_nodup h)
  apply (List.nodup_append).mpr
  refine ⟨hs.2.1, hs.1, ?_⟩
  intro x hx y hy hxy
  exact hs.2.2 y hy x hx hxy.symm

end CompCert4Lean.Lib.Coqlib

namespace CompCert4Lean.Lib.Coqlib

theorem list_norepet_append : list_norepet_appendStatement := by
  intro A l1 l2 h1 h2 hd
  exact (list_norepet_app A l1 l2).2 ⟨h1, h2, hd⟩

end CompCert4Lean.Lib.Coqlib
