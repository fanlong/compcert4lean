import Std

/-!
# Rocq logical and standard-library compatibility surface

This file is intentionally a small naming facade.  The computational pieces
reuse Lean's checked primitives; only source-shaped adapters and the assigned
proofs are defined here.
-/

namespace CompCert4Lean.Foundation.Logic

namespace Support

inductive Sumbool (A B : Prop) : Type where
  | left (h : A) : Sumbool A B
  | right (h : B) : Sumbool A B

inductive Sumor (A : Type) (B : Prop) : Type where
  | inleft (a : A) : Sumor A B
  | inright (h : B) : Sumor A B

end Support

namespace Rocq.Coq.Bool.Bool

def eqb (b1 b2 : _root_.Bool) : _root_.Bool :=
  if h : b1 = b2 then true else false

theorem andb_diag (b : _root_.Bool) : _root_.Bool.and b b = b := by
  cases b <;> rfl

theorem andb_false_intro1 (b1 b2 : _root_.Bool) (h : b1 = false) :
    _root_.Bool.and b1 b2 = false := by
  cases b1 <;> simp_all

theorem andb_false_intro2 (b1 b2 : _root_.Bool) (h : b2 = false) :
    _root_.Bool.and b1 b2 = false := by
  cases b1 <;> cases b2 <;> simp_all

theorem andb_false_r (b : _root_.Bool) : _root_.Bool.and b false = false := by
  cases b <;> rfl

theorem andb_true_iff (b1 b2 : _root_.Bool) :
    (_root_.Bool.and b1 b2 = true) ↔ b1 = true ∧ b2 = true := by
  cases b1 <;> cases b2 <;> simp

theorem andb_true_r (b : _root_.Bool) : _root_.Bool.and b true = b := by
  cases b <;> rfl

def bool_dec (b1 b2 : _root_.Bool) :
    Support.Sumbool (b1 = b2) (¬ b1 = b2) := by
  by_cases h : b1 = b2
  · exact .left h
  · exact .right h

theorem diff_false_true : ¬ (false = true) := by decide

theorem diff_true_false : ¬ (true = false) := by decide

theorem eqb_prop (a b : _root_.Bool) (h : eqb a b = true) : a = b := by
  simp [eqb] at h
  exact h

theorem eqb_true_iff (a b : _root_.Bool) : eqb a b = true ↔ a = b := by
  simp [eqb]

theorem negb_false_iff (b : _root_.Bool) :
    (_root_.Bool.not b = false) ↔ b = true := by
  cases b <;> simp

theorem negb_involutive (b : _root_.Bool) :
    _root_.Bool.not (_root_.Bool.not b) = b := by
  cases b <;> rfl

theorem negb_sym (b b' : _root_.Bool) (h : b' = _root_.Bool.not b) :
    b = _root_.Bool.not b' := by
  cases b <;> cases b' <;> simp_all

theorem negb_true_iff (b : _root_.Bool) :
    (_root_.Bool.not b = true) ↔ b = false := by
  cases b <;> simp

theorem orb_comm (b1 b2 : _root_.Bool) :
    _root_.Bool.or b1 b2 = _root_.Bool.or b2 b1 := by
  cases b1 <;> cases b2 <;> rfl

theorem orb_diag (b : _root_.Bool) : _root_.Bool.or b b = b := by
  cases b <;> rfl

theorem orb_false_elim (b1 b2 : _root_.Bool) (h : _root_.Bool.or b1 b2 = false) :
    b1 = false ∧ b2 = false := by
  cases b1 <;> cases b2 <;> simp_all

theorem orb_false_intro (b1 b2 : _root_.Bool) (h1 : b1 = false) (h2 : b2 = false) :
    _root_.Bool.or b1 b2 = false := by
  cases b1 <;> cases b2 <;> simp_all

theorem orb_false_l (b : _root_.Bool) : _root_.Bool.or false b = b := by
  cases b <;> rfl

theorem orb_false_r (b : _root_.Bool) : _root_.Bool.or b false = b := by
  cases b <;> rfl

theorem orb_prop (a b : _root_.Bool) (h : _root_.Bool.or a b = true) :
    a = true ∨ b = true := by
  cases a <;> cases b <;> simp_all

def orb_true_elim (b1 b2 : _root_.Bool) (h : _root_.Bool.or b1 b2 = true) :
    Support.Sumbool (b1 = true) (b2 = true) := by
  cases b1 <;> cases b2
  · cases h
  · exact .right rfl
  · exact .left rfl
  · exact .left rfl

theorem orb_true_iff (b1 b2 : _root_.Bool) :
    (_root_.Bool.or b1 b2 = true) ↔ b1 = true ∨ b2 = true := by
  cases b1 <;> cases b2 <;> simp

theorem orb_true_intro (b1 b2 : _root_.Bool) (h : b1 = true ∨ b2 = true) :
    _root_.Bool.or b1 b2 = true := by
  cases b1 <;> cases b2 <;> simp_all

theorem orb_true_r (b : _root_.Bool) : _root_.Bool.or b true = true := by
  cases b <;> rfl

theorem xorb_comm (b b' : _root_.Bool) :
    _root_.Bool.xor b b' = _root_.Bool.xor b' b := by
  cases b <;> cases b' <;> rfl

theorem xorb_false_r (b : _root_.Bool) : _root_.Bool.xor b false = b := by
  cases b <;> rfl

end Rocq.Coq.Bool.Bool

namespace Rocq.Coq.Init.Datatypes

inductive comparison : Type where
  | Eq
  | Lt
  | Gt

/- Source-named endpoints.  The constructors remain `comparison.*`; these
   constants provide the promised canonical identities at the Rocq names. -/
abbrev Eq : comparison := comparison.Eq
abbrev Lt : comparison := comparison.Lt
abbrev Gt : comparison := comparison.Gt

def CompOpp (r : comparison) : comparison :=
  match r with
  | .Lt => .Gt
  | .Eq => .Eq
  | .Gt => .Lt

inductive Empty_set : Type where

def andb (b1 b2 : _root_.Bool) : _root_.Bool := _root_.Bool.and b1 b2

theorem andb_prop (a b : _root_.Bool) (h : andb a b = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andb] at h ⊢

theorem andb_true_intro {b1 b2 : _root_.Bool} (h : b1 = true ∧ b2 = true) :
    andb b1 b2 = true := by
  cases b1 <;> cases b2 <;> simp [andb] at h ⊢

def fst {A B : Type} (p : A × B) : A := p.1

abbrev length {A : Type} (l : _root_.List A) : Nat := _root_.List.length l

def nat_rect (P : Nat → Type) (f : P 0)
    (f0 : (n : Nat) → P n → P (Nat.succ n)) (n : Nat) : P n :=
  Nat.rec f f0 n

def negb (b : _root_.Bool) : _root_.Bool := _root_.Bool.not b

def orb (b1 b2 : _root_.Bool) : _root_.Bool := _root_.Bool.or b1 b2

def snd {A B : Type} (p : A × B) : B := p.2

def xorb (b1 b2 : _root_.Bool) : _root_.Bool := _root_.Bool.xor b1 b2

end Rocq.Coq.Init.Datatypes

namespace Rocq.Coq.Init.Logic

/-! Rocq's disjunction is Lean's native `Or`; source names are narrow adapters
    with the original constructor propositions. -/

abbrev or (A B : Prop) : Prop := Or A B

def or_introl {A B : Prop} (h : A) : or A B := Or.inl h

def or_intror {A B : Prop} (h : B) : or A B := Or.inr h

def False_ind (P : Prop) (h : False) : P := False.elim h

theorem eq_sym {A : Type} {x y : A} (h : x = y) : y = x := h.symm

theorem f_equal {A B : Type} (f : A → B) {x y : A} (h : x = y) : f x = f y :=
  congrArg f h

theorem f_equal2 {A1 A2 B : Type} (f : A1 → A2 → B)
    {x1 y1 : A1} {x2 y2 : A2} (h1 : x1 = y1) (h2 : x2 = y2) :
    f x1 x2 = f y1 y2 := by cases h1; cases h2; rfl

theorem f_equal3 {A1 A2 A3 B : Type} (f : A1 → A2 → A3 → B)
    {x1 y1 : A1} {x2 y2 : A2} {x3 y3 : A3}
    (h1 : x1 = y1) (h2 : x2 = y2) (h3 : x3 = y3) :
    f x1 x2 x3 = f y1 y2 y3 := by cases h1; cases h2; cases h3; rfl

theorem f_equal4 {A1 A2 A3 A4 B : Type} (f : A1 → A2 → A3 → A4 → B)
    {x1 y1 : A1} {x2 y2 : A2} {x3 y3 : A3} {x4 y4 : A4}
    (h1 : x1 = y1) (h2 : x2 = y2) (h3 : x3 = y3) (h4 : x4 = y4) :
    f x1 x2 x3 x4 = f y1 y2 y3 y4 := by
  cases h1; cases h2; cases h3; cases h4; rfl

theorem not_eq_sym {A : Type} {x y : A} (h : ¬ x = y) : ¬ y = x := by
  intro h'
  exact h h'.symm

theorem proj1 {A B : Prop} (h : A ∧ B) : A := h.1

theorem proj2 {A B : Prop} (h : A ∧ B) : B := h.2

abbrev refl_equal {A : Type} {x : A} : x = x := rfl

abbrev sym_eq {A : Type} {x y : A} : x = y → y = x := Eq.symm

abbrev sym_not_eq {A : Type} {x y : A} : ¬ x = y → ¬ y = x := by
  intro h hxy
  exact h hxy.symm

abbrev trans_eq {A : Type} {x y z : A} : x = y → y = z → x = z := Eq.trans

end Rocq.Coq.Init.Logic

namespace Rocq.Coq.Init.Nat

def max (n m : Nat) : Nat := _root_.Nat.max n m

end Rocq.Coq.Init.Nat

namespace Rocq.Coq.Init.Specif

/-! Dependent containers use Lean's checked native carriers.  The source
    constructors below retain Rocq's names and argument order. -/

abbrev sig {A : Type} (P : A → Prop) : Type := Subtype P

abbrev sig2 {A : Type} (P Q : A → Prop) : Type :=
  Subtype (fun x => P x ∧ Q x)

abbrev sigT {A : Type} (P : A → Type) : Type := Sigma P

def exist {A : Type} (P : A → Prop) (x : A) (h : P x) : sig P :=
  ⟨x, h⟩

def exist2 {A : Type} (P Q : A → Prop) (x : A) (hp : P x) (hq : Q x) : sig2 P Q :=
  ⟨x, hp, hq⟩

def existT {A : Type} (P : A → Type) (x : A) (h : P x) : sigT P :=
  ⟨x, h⟩

/- Pattern aliases preserve existing source-shaped matches for the native
   `Subtype`/`Sigma` carriers. -/
namespace sig
@[match_pattern] def exist {A : Type} {P : A → Prop} (x : A) (h : P x) : sig P :=
  _root_.CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Specif.exist P x h
end sig

namespace sigT
@[match_pattern] def existT {A : Type} {P : A → Type} (x : A) (h : P x) : sigT P :=
  _root_.CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Specif.existT P x h
end sigT

namespace sig2
@[match_pattern] def exist2 {A : Type} {P Q : A → Prop}
    (x : A) (hp : P x) (hq : Q x) : sig2 P Q :=
  _root_.CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Specif.exist2 P Q x hp hq
end sig2

/-! `sumbool` and `sumor` retain the canonical support carriers used by the
    rest of the migration.  Exporting their constructors gives the promised
    Rocq source names without introducing a second carrier provider. -/

export Support.Sumbool (left right)
export Support.Sumor (inleft inright)

def proj1_sig {A : Type} {P : A → Prop} (e : sig P) : A := e.1

def proj2_sig {A : Type} {P : A → Prop} (e : sig P) : P (proj1_sig e) := e.2

def inleft {A : Type} {B : Prop} (a : A) : Support.Sumor A B :=
  Support.Sumor.inleft a

def inright {A : Type} {B : Prop} (h : B) : Support.Sumor A B :=
  Support.Sumor.inright h

def left {A B : Prop} (h : A) : Support.Sumbool A B :=
  Support.Sumbool.left h

def right {A B : Prop} (h : B) : Support.Sumbool A B :=
  Support.Sumbool.right h

end Rocq.Coq.Init.Specif

namespace Rocq.Coq.Lists.List

inductive Forall {A : Type} (P : A → Prop) : _root_.List A → Prop where
  | nil : Forall P []
  | cons {x : A} {l : _root_.List A} : P x → Forall P l → Forall P (x :: l)

abbrev In {A : Type} (a : A) (l : _root_.List A) : Prop := _root_.List.Mem a l

abbrev length {A : Type} (l : _root_.List A) : Nat := _root_.List.length l

abbrev app_length {A : Type} (l l' : _root_.List A) :
    length (l ++ l') = Nat.add (length l) (length l') := _root_.List.length_append

theorem app_assoc {A : Type} (l m n : _root_.List A) :
    l ++ (m ++ n) = (l ++ m) ++ n := by
  exact (_root_.List.append_assoc l m n).symm

theorem app_eq_nil {A : Type} (l l' : _root_.List A) (h : l ++ l' = []) :
    l = [] ∧ l' = [] := by
  cases l with
  | nil => exact ⟨rfl, h⟩
  | cons a l => cases h

theorem app_nil_r {A : Type} (l : _root_.List A) : l ++ [] = l := by
  exact _root_.List.append_nil l

def existsb {A : Type} (f : A → _root_.Bool) (l : _root_.List A) : _root_.Bool :=
  match l with
  | [] => false
  | x :: xs => f x || existsb f xs

theorem existsb_exists {A : Type} (f : A → _root_.Bool) (l : _root_.List A) :
    existsb f l = true ↔ ∃ x, In x l ∧ f x = true := by
  induction l with
  | nil =>
    constructor
    · intro h; cases h
    · rintro ⟨x, hx, _⟩; exact (_root_.List.not_mem_nil hx).elim
  | cons x xs ih =>
    cases hf : f x
    · constructor
      · intro h
        have hxs : existsb f xs = true := by simpa [existsb, hf] using h
        rcases ih.mp hxs with ⟨y, hy, hfy⟩
        exact ⟨y, _root_.List.Mem.tail x hy, hfy⟩
      · rintro ⟨y, hy, hfy⟩
        cases (_root_.List.mem_cons.mp hy) with
        | inl hxy => simp_all
        | inr hy' => simp [existsb, hf, ih.mpr ⟨y, hy', hfy⟩]
    · constructor
      · intro _
        exact ⟨x, _root_.List.Mem.head xs, hf⟩
      · intro _
        simp [existsb, hf]

def filter {A : Type} (f : A → _root_.Bool) (l : _root_.List A) : _root_.List A :=
  _root_.List.filter f l

theorem filter_In {A : Type} (f : A → _root_.Bool) (x : A) (l : _root_.List A) :
    In x (filter f l) ↔ In x l ∧ f x = true := by
  exact _root_.List.mem_filter

def fold_left {A B : Type} (f : A → B → A) (l : _root_.List B) (a0 : A) : A :=
  _root_.List.foldl f a0 l

theorem fold_left_app {A B : Type} (f : A → B → A) (l l' : _root_.List B) (i : A) :
    fold_left f (l ++ l') i = fold_left f l' (fold_left f l i) := by
  exact _root_.List.foldl_append

def fold_right {A B : Type} (f : B → A → A) (a0 : A) (l : _root_.List B) : A :=
  _root_.List.foldr f a0 l

theorem Forall_forall {A : Type} (P : A → Prop) (l : _root_.List A) :
    Forall P l ↔ ∀ x, In x l → P x := by
  induction l with
  | nil =>
    constructor
    · intro _ x hx; exact (_root_.List.not_mem_nil hx).elim
    · intro _; exact .nil
  | cons a l ih =>
    constructor
    · intro h x hx
      cases h with
      | cons ha htail =>
        cases (_root_.List.mem_cons.mp hx) with
        | inl hxa => simpa [hxa] using ha
        | inr hx' => exact (ih.mp htail) x hx'
    · intro h
      apply Forall.cons (h a (_root_.List.Mem.head l))
      apply ih.mpr
      intro x hx
      exact h x (_root_.List.Mem.tail a hx)

def forallb {A : Type} (f : A → _root_.Bool) (l : _root_.List A) : _root_.Bool :=
  match l with
  | [] => true
  | x :: xs => f x && forallb f xs

theorem forallb_forall {A : Type} (f : A → _root_.Bool) (l : _root_.List A) :
    forallb f l = true ↔ ∀ x, In x l → f x = true := by
  induction l with
  | nil =>
    constructor
    · intro _ x hx; exact (_root_.List.not_mem_nil hx).elim
    · intro _; rfl
  | cons x xs ih =>
    cases hf : f x
    · constructor
      · intro h y hy
        cases (_root_.List.mem_cons.mp hy) with
        | inl hyx =>
          subst y
          have : False := by simpa [forallb, hf] using h
          exact this.elim
        | inr hy' =>
          have hxs : forallb f xs = true := by simpa [forallb, hf] using h
          exact ih.mp hxs y hy'
      · intro hall
        have hx := hall x (_root_.List.Mem.head xs)
        simp [hf] at hx
    · constructor
      · intro h y hy
        cases (_root_.List.mem_cons.mp hy) with
        | inl hyx => simpa [hyx] using hf
        | inr hy' =>
          have hxs : forallb f xs = true := by simpa [forallb, hf] using h
          exact ih.mp hxs y hy'
      · intro hall
        have hxs : forallb f xs = true := ih.mpr (fun y hy => hall y (_root_.List.Mem.tail x hy))
        simp [forallb, hf, hxs]

def hd {A : Type} (default : A) (l : _root_.List A) : A :=
  match l with
  | [] => default
  | x :: _ => x

theorem in_app_iff {A : Type} (l l' : _root_.List A) (a : A) :
    In a (l ++ l') ↔ In a l ∨ In a l' := by
  exact _root_.List.mem_append

theorem in_app_or {A : Type} (l m : _root_.List A) (a : A)
    (h : In a (l ++ m)) : In a l ∨ In a m :=
  (in_app_iff l m a).mp h

theorem in_cons {A : Type} (a b : A) (l : _root_.List A) (h : In b l) :
    In b (a :: l) := by
  exact List.Mem.tail a h

def in_dec {A : Type} (eq_dec : (x y : A) → Support.Sumbool (x = y) (¬ x = y))
    (a : A) (l : _root_.List A) : Support.Sumbool (In a l) (¬ In a l) :=
  match l with
  | [] => .right _root_.List.not_mem_nil
  | b :: l =>
    match eq_dec a b with
    | .left hab => .left (by simpa [hab] using (_root_.List.Mem.head l : In b (b :: l)))
    | .right hne =>
      match in_dec eq_dec a l with
      | .left hmem => .left (_root_.List.Mem.tail b hmem)
      | .right hnot =>
        .right (by
          intro hmem
          cases (_root_.List.mem_cons.mp hmem) with
          | inl hh => exact hne hh
          | inr ht => exact hnot ht)

abbrev In_dec {A : Type} (eq_dec : (x y : A) → Support.Sumbool (x = y) (¬ x = y))
    (a : A) (l : _root_.List A) := in_dec eq_dec a l

theorem in_eq {A : Type} (a : A) (l : _root_.List A) : In a (a :: l) := by
  exact _root_.List.Mem.head l

theorem in_map {A B : Type} (f : A → B) (l : _root_.List A) (x : A) (h : In x l) :
    In (f x) (_root_.List.map f l) := by
  exact (_root_.List.mem_map.mpr ⟨x, h, rfl⟩)

theorem in_or_app {A : Type} (l m : _root_.List A) (a : A)
    (h : In a l ∨ In a m) : In a (l ++ m) := by
  exact (in_app_iff l m a).mpr h

def list_prod {A B : Type} (l : _root_.List A) (l' : _root_.List B) :
    _root_.List (A × B) :=
  l.flatMap (fun x => l'.map (fun y => (x, y)))

theorem in_prod {A B : Type} (l : _root_.List A) (l' : _root_.List B)
    (x : A) (y : B) (hx : In x l) (hy : In y l') : In (x, y) (list_prod l l') := by
  change (x, y) ∈ l.flatMap (fun z => l'.map (fun w => (z, w)))
  rw [_root_.List.mem_flatMap]
  exact ⟨x, hx, _root_.List.mem_map.mpr ⟨y, hy, rfl⟩⟩

def remove {A : Type} (eq_dec : (x y : A) → Support.Sumbool (x = y) (¬ x = y))
    (x : A) (l : _root_.List A) : _root_.List A :=
  match l with
  | [] => []
  | y :: ys =>
    match eq_dec x y with
    | .left _ => remove eq_dec x ys
    | .right _ => y :: remove eq_dec x ys

theorem in_remove {A : Type}
    (eq_dec : (x y : A) → Support.Sumbool (x = y) (¬ x = y))
    (l : _root_.List A) (x y : A) (h : In x (remove eq_dec y l)) :
    In x l ∧ ¬ x = y := by
  induction l with
  | nil => exact (_root_.List.not_mem_nil h).elim
  | cons a l ih =>
    cases hd : eq_dec y a with
    | left hya =>
      have h' : remove eq_dec y (a :: l) = remove eq_dec y l := by simp [remove, hd]
      rw [h'] at h
      rcases ih h with ⟨hin, hne⟩
      exact ⟨_root_.List.Mem.tail a hin, hne⟩
    | right hya =>
      have h' : remove eq_dec y (a :: l) = a :: remove eq_dec y l := by simp [remove, hd]
      rw [h'] at h
      cases (_root_.List.mem_cons.mp h) with
      | inl hhead =>
        exact ⟨hhead ▸ _root_.List.Mem.head l, fun hxy => hya (hxy.symm.trans hhead)⟩
      | inr htail =>
        rcases ih htail with ⟨hin, hne⟩
        exact ⟨_root_.List.Mem.tail a hin, hne⟩

theorem in_rev {A : Type} (l : _root_.List A) (x : A) :
    In x l ↔ In x (_root_.List.reverse l) := by
  exact (_root_.List.mem_reverse.symm)

def incl {A : Type} (l m : _root_.List A) : Prop := ∀ ⦃a⦄, In a l → In a m

theorem incl_refl {A : Type} (l : _root_.List A) : incl l l := by
  intro a h
  exact h

theorem incl_tl {A : Type} (a : A) {l m : _root_.List A} (h : incl l m) : incl l (a :: m) := by
  intro x hx
  exact List.Mem.tail a (h hx)

theorem incl_tran {A : Type} {l m n : _root_.List A} (h1 : incl l m) (h2 : incl m n) : incl l n := by
  intro x hx
  exact h2 (h1 hx)

def list_eq_dec {A : Type}
    (eq_dec : (x y : A) → Support.Sumbool (x = y) (¬ x = y))
    (l l' : _root_.List A) : Support.Sumbool (l = l') (¬ l = l') :=
  match l, l' with
  | [], [] => .left rfl
  | [], _ :: _ => .right (by intro h; cases h)
  | _ :: _, [] => .right (by intro h; cases h)
  | a :: as, b :: bs =>
    match eq_dec a b with
    | .right hab => .right (by intro h; cases h; exact hab rfl)
    | .left hab =>
      match list_eq_dec eq_dec as bs with
      | .left htail => .left (by cases hab; cases htail; rfl)
      | .right htail => .right (by intro h; cases h; exact htail rfl)

def map {A B : Type} (f : A → B) (l : _root_.List A) : _root_.List B := _root_.List.map f l

theorem map_app {A B : Type} (f : A → B) (l l' : _root_.List A) :
    map f (l ++ l') = map f l ++ map f l' := by
  induction l <;> simp [map, *]

abbrev map_length {A B : Type} (f : A → B) (l : _root_.List A) :
    _root_.List.length (map f l) = _root_.List.length l := _root_.List.length_map f

def nth_error {A : Type} (l : _root_.List A) (n : Nat) : Option A :=
  match l, n with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => nth_error xs n

def «repeat» {A : Type} (x : A) (n : Nat) : _root_.List A := _root_.List.replicate n x

theorem repeat_spec {A : Type} (n : Nat) (x y : A) (h : In y («repeat» x n)) : y = x := by
  exact (_root_.List.mem_replicate.mp h).2

def rev {A : Type} (l : _root_.List A) : _root_.List A := _root_.List.reverse l

def rev' {A : Type} (l : _root_.List A) : _root_.List A := _root_.List.reverseAux l []

theorem rev_alt {A : Type} (l : _root_.List A) : rev l = _root_.List.reverseAux l [] := by
  simpa [rev] using (_root_.List.reverseAux_eq (as := l) (bs := ([] : _root_.List A))).symm

theorem rev_app_distr {A : Type} (x y : _root_.List A) :
    rev (x ++ y) = rev y ++ rev x := by
  exact _root_.List.reverse_append

theorem rev_involutive {A : Type} (l : _root_.List A) : rev (rev l) = l := by
  exact _root_.List.reverse_reverse l

abbrev rev_length {A : Type} (l : _root_.List A) :
    _root_.List.length (rev l) = _root_.List.length l := by
  simpa [rev] using congrArg _root_.List.length (_root_.List.reverse_reverse l)

abbrev tail {A : Type} (l : _root_.List A) : _root_.List A :=
  match l with
  | [] => []
  | _ :: xs => xs

def tl {A : Type} (l : _root_.List A) : _root_.List A := tail l

end Rocq.Coq.Lists.List

namespace Rocq.Coq.Lists.SetoidList

def InA {A : Type} (eqA : A → A → Prop) (x : A) (l : _root_.List A) : Prop :=
  ∃ y, eqA x y ∧ Rocq.Coq.Lists.List.In y l

theorem InA_alt {A : Type} (eqA : A → A → Prop) (x : A) (l : _root_.List A) :
    InA eqA x l ↔ ∃ y, eqA x y ∧ Rocq.Coq.Lists.List.In y l := Iff.rfl

inductive NoDupA {A : Type} (eqA : A → A → Prop) : _root_.List A → Prop where
  | nil : NoDupA eqA []
  | cons {x : A} {l : _root_.List A} :
      (¬ InA eqA x l) → NoDupA eqA l → NoDupA eqA (x :: l)

abbrev NoDupA_nil {A : Type} (eqA : A → A → Prop) : NoDupA eqA [] :=
  NoDupA.nil

abbrev NoDupA_cons {A : Type} {eqA : A → A → Prop}
    {x : A} {l : _root_.List A}
    (notIn : ¬ InA eqA x l) (noDup : NoDupA eqA l) : NoDupA eqA (x :: l) :=
  NoDupA.cons notIn noDup

def NoDupA_ind {A : Type} {eqA : A → A → Prop}
    {P : _root_.List A → Prop}
    (nilCase : P [])
    (consCase : ∀ (x : A) (l : _root_.List A),
      (¬ InA eqA x l) → NoDupA eqA l → P l → P (x :: l))
    {l : _root_.List A} (noDup : NoDupA eqA l) : P l := by
  induction noDup with
  | nil => exact nilCase
  | @cons x l notIn noDup ih => exact consCase x l notIn noDup ih

end Rocq.Coq.Lists.SetoidList

namespace Rocq.Coq.Logic.Classical_Pred_Type

theorem not_all_ex_not (U : Type) (P : U → Prop) (h : ¬ ∀ n, P n) :
    ∃ n, ¬ P n := by
  exact Classical.byContradiction (fun hn => h (fun n =>
    Classical.byContradiction (fun hpn => hn ⟨n, hpn⟩)))

theorem not_ex_all_not (U : Type) (P : U → Prop) (h : ¬ ∃ n, P n) (n : U) :
    ¬ P n := by
  intro hn
  exact h ⟨n, hn⟩

end Rocq.Coq.Logic.Classical_Pred_Type

namespace Rocq.Coq.Logic.Classical_Prop

theorem classic (P : Prop) : P ∨ ¬ P := Classical.em P

theorem imply_to_and (P Q : Prop) (h : ¬ (P → Q)) : P ∧ ¬ Q := by
  constructor
  · exact Classical.byContradiction (fun hP => h (fun hp => False.elim (hP hp)))
  · intro hQ
    exact h (fun _ => hQ)

theorem not_and_or (P Q : Prop) (h : ¬ (P ∧ Q)) : ¬ P ∨ ¬ Q := by
  by_cases hp : P
  · exact Or.inr (by intro hq; exact h ⟨hp, hq⟩)
  · exact Or.inl hp

theorem not_or_and (P Q : Prop) (h : ¬ (P ∨ Q)) : ¬ P ∧ ¬ Q := by
  exact ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩

end Rocq.Coq.Logic.Classical_Prop

namespace Rocq.Coq.Logic.ClassicalEpsilon

noncomputable def constructive_indefinite_description
    {A : Type} (P : A → Prop) (h : ∃ x, P x) : Subtype P :=
  ⟨Classical.choose h, Classical.choose_spec h⟩

end Rocq.Coq.Logic.ClassicalEpsilon

namespace Rocq.Coq.Logic.ClassicalFacts

def proof_irrelevance : Prop := ∀ {A : Prop} (a1 a2 : A), a1 = a2

end Rocq.Coq.Logic.ClassicalFacts

namespace Rocq.Coq.Logic.Eqdep_dec

theorem UIP_dec {A : Type}
    (_eq_dec : (x y : A) → Support.Sumbool (x = y) (¬ x = y))
    {x y : A} (p1 p2 : x = y) : p1 = p2 := Subsingleton.elim _ _

end Rocq.Coq.Logic.Eqdep_dec

namespace Rocq.Coq.Logic.FunctionalExtensionality

universe uA uB

theorem functional_extensionality {A : Type uA} {B : Type uB} (f g : A → B)
    (h : ∀ x, f x = g x) : f = g := funext h

theorem functional_extensionality_dep {A : Type uA} {B : A → Type uB}
    (f g : (x : A) → B x) (h : ∀ x, f x = g x) : f = g := funext h

/- Universe probes: the domain is itself `Type`, while the codomain remains
   independently at `Type 0`. -/
example (f g : Type → Nat) (h : ∀ x, f x = g x) : f = g :=
  functional_extensionality (A := Type) f g h

example (B : Type → Type) (f g : (x : Type) → B x)
    (h : ∀ x, f x = g x) : f = g :=
  functional_extensionality_dep (A := Type) (B := B) f g h

end Rocq.Coq.Logic.FunctionalExtensionality

end CompCert4Lean.Foundation.Logic
