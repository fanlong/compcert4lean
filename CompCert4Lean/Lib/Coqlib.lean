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
