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

private def sumboolSelect {P Q : Prop} {A : Type}
    (d : CompCert4Lean.Foundation.Logic.Support.Sumbool P Q) (ifso ifnot : A) : A :=
  match d with
  | .left _ => ifso
  | .right _ => ifnot

/-! ## Positive numbers -/

def peq (x y : positive) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) :=
  PArith.BinPos.Pos.eq_dec x y

def peq_trueStatement : Prop :=
  ∀ (A : Type) (x : positive) (a b : A), sumboolSelect (peq x x) a b = a

def peq_falseStatement : Prop :=
  ∀ (A : Type) (x y : positive) (a b : A),
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
  ∀ (A : Type) (x : Z) (a b : A), sumboolSelect (zeq x x) a b = a

def zeq_falseStatement : Prop :=
  ∀ (A : Type) (x y : Z) (a b : A),
    x ≠ y → sumboolSelect (zeq x y) a b = b

def zlt (x y : Z) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool
      (ZArith.BinInt.Z.lt x y) (ZArith.BinInt.Z.ge x y) := by
  match ZArith.ZArith_dec.Z_lt_dec x y with
  | .left h => exact .left h
  | .right h => exact .right (Int.le_of_not_gt h)

def zlt_trueStatement : Prop :=
  ∀ (A : Type) (x y : Z) (a b : A),
    ZArith.BinInt.Z.lt x y → sumboolSelect (zlt x y) a b = a

def zlt_falseStatement : Prop :=
  ∀ (A : Type) (x y : Z) (a b : A),
    ZArith.BinInt.Z.ge x y → sumboolSelect (zlt x y) a b = b

def zle (x y : Z) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool
      (ZArith.BinInt.Z.le x y) (ZArith.BinInt.Z.gt x y) :=
  ZArith.ZArith_dec.Z_le_gt_dec x y

def zle_trueStatement : Prop :=
  ∀ (A : Type) (x y : Z) (a b : A),
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

def option_eq {A : Type}
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

inductive option_rel {A B : Type} (R : A → B → Prop) : Option A → Option B → Prop where
  | none : option_rel R none none
  | some {x : A} {y : B} : R x y → option_rel R (some x) (some y)

def option_map {A B : Type} (f : A → B) : Option A → Option B
  | none => none
  | some y => some (f y)

def sum_left_map {A B C : Type} (f : A → B) : Sum A C → Sum B C
  | .inl y => .inl (f y)
  | .inr z => .inr z

def list_length_z_aux {A : Type} : List A → Z → Z
  | [], acc => acc
  | _ :: tl, acc => list_length_z_aux tl (ZArith.BinInt.Z.succ acc)

def list_length_z_aux_shiftStatement : Prop :=
  ∀ (A : Type) (l : List A) (n m : Z),
    list_length_z_aux l n =
      ZArith.BinInt.Z.add (list_length_z_aux l m) (ZArith.BinInt.Z.sub n m)

def list_length_z {A : Type} (l : List A) : Z :=
  list_length_z_aux l Z0

def list_length_z_consStatement : Prop :=
  ∀ (A : Type) (hd : A) (tl : List A),
    list_length_z (hd :: tl) = ZArith.BinInt.Z.add (list_length_z tl) (Zpos xH)

def list_length_z_posStatement : Prop :=
  ∀ (A : Type) (l : List A), ZArith.BinInt.Z.ge (list_length_z l) Z0

def list_nth_z {A : Type} : List A → Z → Option A
  | [], _ => none
  | hd :: tl, n =>
      match zeq n Z0 with
      | .left _ => some hd
      | .right _ => list_nth_z tl (ZArith.BinInt.Z.pred n)

def list_nth_z_inStatement : Prop :=
  ∀ (A : Type) (l : List A) (n : Z) (x : A),
    list_nth_z l n = some x → x ∈ l

def list_nth_z_mapStatement : Prop :=
  ∀ (A B : Type) (f : A → B) (l : List A) (n : Z),
    list_nth_z (List.map f l) n = option_map f (list_nth_z l n)

def list_map_extenStatement : Prop :=
  ∀ (A B : Type) (f f' : A → B) (l : List A),
    (∀ x : A, x ∈ l → f x = f' x) → List.map f' l = List.map f l

def list_map_composeStatement : Prop :=
  ∀ (A B C : Type) (f : A → B) (g : B → C) (l : List A),
    List.map g (List.map f l) = List.map (fun x => g (f x)) l

def list_in_map_invStatement : Prop :=
  ∀ (A B : Type) (f : A → B) (l : List A) (y : B),
    y ∈ List.map f l → ∃ x : A, y = f x ∧ x ∈ l

def app_assStatement : Prop :=
  ∀ (A : Type) (l1 l2 l3 : List A),
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)

def list_fold_left {A B : Type} (f : A → B → B) : B → List A → B
  | accu, [] => accu
  | accu, x :: xs => list_fold_left f (f x accu) xs

def list_fold_right {A B : Type} (f : A → B → B) (l : List A) (base : B) : B :=
  list_fold_left f base
    (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.rev' l)

def list_fold_left_appStatement : Prop :=
  ∀ (A B : Type) (f : A → B → B) (l1 l2 : List A) (accu : B),
    list_fold_left f accu (l1 ++ l2) =
      list_fold_left f (list_fold_left f accu l1) l2

def list_fold_right_eqStatement : Prop :=
  ∀ (A B : Type) (f : A → B → B) (l : List A) (base : B),
    list_fold_right f l base =
      match l with
      | [] => base
      | x :: xs => f x (list_fold_right f xs base)

def in_appStatement : Prop :=
  ∀ (A : Type) (x : A) (l1 l2 : List A),
    x ∈ l1 ++ l2 ↔ x ∈ l1 ∨ x ∈ l2

def list_disjoint {A : Type} (l1 l2 : List A) : Prop :=
  ∀ x y : A, x ∈ l1 → y ∈ l2 → x ≠ y

def list_disjoint_cons_leftStatement : Prop :=
  ∀ (A : Type) (a : A) (l1 l2 : List A),
    list_disjoint (a :: l1) l2 → list_disjoint l1 l2

def list_disjoint_notinStatement : Prop :=
  ∀ (A : Type) (l1 l2 : List A) (a : A),
    list_disjoint l1 l2 → a ∈ l1 → ¬ a ∈ l2

def list_disjoint_symStatement : Prop :=
  ∀ (A : Type) (l1 l2 : List A),
    list_disjoint l1 l2 → list_disjoint l2 l1

def list_disjoint_decStatement :=
  ∀ (A : Type)
    (eqA : ∀ x y : A,
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y))
    (l1 l2 : List A),
    CompCert4Lean.Foundation.Logic.Support.Sumbool
      (list_disjoint l1 l2) (¬ list_disjoint l1 l2)

inductive list_norepet {A : Type} : List A → Prop where
  | nil : list_norepet []
  | cons {hd : A} {tl : List A} :
      (¬ hd ∈ tl) → list_norepet tl → list_norepet (hd :: tl)

def list_norepet_decStatement :=
  ∀ (A : Type)
    (eqA : ∀ x y : A,
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y))
    (l : List A),
    CompCert4Lean.Foundation.Logic.Support.Sumbool
      (list_norepet l) (¬ list_norepet l)

def list_norepet_append_commutStatement : Prop :=
  ∀ (A : Type) (a b : List A),
    list_norepet (a ++ b) → list_norepet (b ++ a)

def list_norepet_appStatement : Prop :=
  ∀ (A : Type) (l1 l2 : List A),
    list_norepet (l1 ++ l2) ↔
      list_norepet l1 ∧ list_norepet l2 ∧ list_disjoint l1 l2

def list_norepet_appendStatement : Prop :=
  ∀ (A : Type) (l1 l2 : List A),
    list_norepet l1 → list_norepet l2 → list_disjoint l1 l2 →
      list_norepet (l1 ++ l2)

def list_norepet_append_leftStatement : Prop :=
  ∀ (A : Type) (l1 l2 : List A),
    list_norepet (l1 ++ l2) → list_norepet l1

inductive is_tail {A : Type} : List A → List A → Prop where
  | refl (c : List A) : is_tail c c
  | cons (i : A) {c1 c2 : List A} : is_tail c1 c2 → is_tail c1 (i :: c2)

def is_tail_inStatement : Prop :=
  ∀ (A : Type) (i : A) (c1 c2 : List A),
    is_tail (i :: c1) c2 → i ∈ c2

def is_tail_cons_leftStatement : Prop :=
  ∀ (A : Type) (i : A) (c1 c2 : List A),
    is_tail (i :: c1) c2 → is_tail c1 c2

def is_tail_transStatement : Prop :=
  ∀ (A : Type) (l1 l2 : List A),
    is_tail l1 l2 → ∀ l3 : List A, is_tail l2 l3 → is_tail l1 l3

inductive list_forall2 {A B : Type} (P : A → B → Prop) : List A → List B → Prop where
  | nil : list_forall2 P [] []
  | cons {a1 : A} {al : List A} {b1 : B} {bl : List B} :
      P a1 b1 → list_forall2 P al bl → list_forall2 P (a1 :: al) (b1 :: bl)

abbrev list_forall2_nil {A B : Type} {P : A → B → Prop} :
    list_forall2 P [] [] :=
  list_forall2.nil

def list_forall2_appStatement : Prop :=
  ∀ (A B : Type) (P : A → B → Prop)
    (a2 : List A) (b2 : List B) (a1 : List A) (b1 : List B),
    list_forall2 P a1 b1 → list_forall2 P a2 b2 →
      list_forall2 P (a1 ++ a2) (b1 ++ b2)

def list_forall2_lengthStatement : Prop :=
  ∀ (A B : Type) (P : A → B → Prop) (l1 : List A) (l2 : List B),
    list_forall2 P l1 l2 → List.length l1 = List.length l2

def list_forall2_in_leftStatement : Prop :=
  ∀ (A B : Type) (P : A → B → Prop) (x1 : A)
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
  ∀ (A : Type)
    (dec_eq : ∀ x y : A,
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y))
    (B : Type) (x : A) (ifso ifnot : B),
    sumboolSelect (dec_eq x x) ifso ifnot = ifso

def dec_eq_falseStatement : Prop :=
  ∀ (A : Type)
    (dec_eq : ∀ x y : A,
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y))
    (B : Type) (x y : A) (ifso ifnot : B),
    x ≠ y → sumboolSelect (dec_eq x y) ifso ifnot = ifnot

def dec_eq_symStatement : Prop :=
  ∀ (A : Type)
    (dec_eq : ∀ x y : A,
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y))
    (B : Type) (x y : A) (ifso ifnot : B),
    sumboolSelect (dec_eq x y) ifso ifnot =
      sumboolSelect (dec_eq y x) ifso ifnot

def pred_dec_trueStatement : Prop :=
  ∀ (P : Prop) (dec : CompCert4Lean.Foundation.Logic.Support.Sumbool P (¬ P))
    (A : Type) (a b : A),
    P → sumboolSelect dec a b = a

def pred_dec_falseStatement : Prop :=
  ∀ (P : Prop) (dec : CompCert4Lean.Foundation.Logic.Support.Sumbool P (¬ P))
    (A : Type) (a b : A),
    (¬ P) → sumboolSelect dec a b = b

/-! ## Lexicographic order -/

inductive lex_ord {A B : Type} (ordA : A → A → Prop) (ordB : B → B → Prop) :
    A × B → A × B → Prop where
  | left {a1 a2 : A} {b1 b2 : B} :
      ordA a1 a2 → lex_ord ordA ordB (a1, b1) (a2, b2)
  | right {a : A} {b1 b2 : B} :
      ordB b1 b2 → lex_ord ordA ordB (a, b1) (a, b2)

abbrev lex_ord_left {A B : Type} {ordA : A → A → Prop} {ordB : B → B → Prop}
    {a1 a2 : A} {b1 b2 : B} (h : ordA a1 a2) :
    lex_ord ordA ordB (a1, b1) (a2, b2) :=
  lex_ord.left h

abbrev lex_ord_right {A B : Type} {ordA : A → A → Prop} {ordB : B → B → Prop}
    {a : A} {b1 b2 : B} (h : ordB b1 b2) :
    lex_ord ordA ordB (a, b1) (a, b2) :=
  lex_ord.right h

def wf_lex_ordStatement : Prop :=
  ∀ (A B : Type) (ordA : A → A → Prop) (ordB : B → B → Prop),
    WellFounded ordA → WellFounded ordB → WellFounded (lex_ord ordA ordB)

end CompCert4Lean.Lib.Coqlib
