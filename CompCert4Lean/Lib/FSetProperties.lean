import CompCert4Lean.Lib.FSetDecide

/-!
# Generic finite-set properties

This is the source-shaped property surface of `FSetProperties.v`.  The
functor remains generic in the element equality provider and set provider.
Executable definitions (`Add`, `of_list`, `to_list`) and dependent
induction/decision principles are kept as definitions with their source
types; theorem bodies are intentionally represented by transparent
proposition descriptors.
-/

namespace CompCert4Lean.Lib.FSetProperties

open CompCert4Lean.Lib.FSetInterface
open CompCert4Lean.Lib.FSetFacts
open CompCert4Lean.Lib.FSetDecide

private def equivlistA {A : Type} (eqA : A → A → Prop) (l l' : List A) : Prop :=
  ∀ x, InA eqA x l ↔ InA eqA x l'

abbrev Dec (E : DecidableType) (M : WSfun E) := WDecide_fun E M

structure WProperties_fun (E : DecidableType) (M : WSfun E) : Type 3 where
  Dec : Dec E M

abbrev WProperties := WProperties_fun
abbrev Properties := WProperties

namespace WProperties_fun

universe u

abbrev FM {E : DecidableType} {M : WSfun E}
    (P : WProperties_fun E M) : WFacts_fun E M := P.Dec.F

abbrev elt (E : DecidableType) (_M : WSfun E) : Type := E.t
abbrev t (_E : DecidableType) (M : WSfun _E) : Type := M.t
abbrev In (E : DecidableType) (M : WSfun E) := M.In
abbrev Equal (E : DecidableType) (M : WSfun E) := M.Equal
abbrev Subset (E : DecidableType) (M : WSfun E) := M.Subset
abbrev Empty (E : DecidableType) (M : WSfun E) := M.Empty
abbrev For_all (E : DecidableType) (M : WSfun E) := M.For_all
abbrev Exists (E : DecidableType) (M : WSfun E) := M.Exists

def In_dec (E : DecidableType) (M : WSfun E) (x : E.t) (s : M.t) :
    Sumbool (M.In x s) (¬ M.In x s) :=
  if h : M.mem x s = true then
    .left (M.mem_2 s x h)
  else
    .right (fun hin => h (M.mem_1 s x hin))

def Add (E : DecidableType) (M : WSfun E) (x : E.t) (s s' : M.t) : Prop :=
  ∀ y, M.In y s' ↔ E.eq x y ∨ M.In y s

def Add_Equal (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ x s s', Add E M x s s' ↔ M.Equal s' (M.add x s)

def equal_refl (E : DecidableType) (M : WSfun E) : Prop := ∀ s, M.Equal s s
def equal_sym (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Equal s s' → M.Equal s' s
def equal_trans (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' s'', M.Equal s s' → M.Equal s' s'' → M.Equal s s''
def subset_refl (E : DecidableType) (M : WSfun E) : Prop := ∀ s, M.Subset s s
def subset_trans (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' s'', M.Subset s s' → M.Subset s' s'' → M.Subset s s''
def subset_antisym (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Subset s s' → M.Subset s' s → M.Equal s s'
def subset_equal (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Equal s s' → M.Subset s s'
def subset_empty (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s, M.Subset M.empty s
def subset_remove_3 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s1 s2 x, M.Subset s1 s2 → M.Subset (M.remove x s1) s2
def subset_diff (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s1 s2 s3, M.Subset s1 s3 → M.Subset (M.diff s1 s2) s3
def subset_add_3 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s1 s2 x, M.In x s2 → M.Subset s1 s2 → M.Subset (M.add x s1) s2
def subset_add_2 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s1 s2 x, M.Subset s1 s2 → M.Subset s1 (M.add x s2)
def in_subset (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s1 s2 x, M.In x s1 → M.Subset s1 s2 → M.In x s2
def double_inclusion (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s1 s2, M.Equal s1 s2 ↔ M.Subset s1 s2 ∧ M.Subset s2 s1
def empty_is_empty_1 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s, M.Empty s → M.Equal s M.empty
def empty_is_empty_2 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s, M.Equal s M.empty → M.Empty s
def add_equal (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s x, M.In x s → M.Equal (M.add x s) s
def add_add (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s x x', M.Equal (M.add x (M.add x' s)) (M.add x' (M.add x s))
def remove_equal (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s x, ¬ M.In x s → M.Equal (M.remove x s) s
def Equal_remove (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' x, M.Equal s s' → M.Equal (M.remove x s) (M.remove x s')
def add_remove (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s x, M.In x s → M.Equal (M.add x (M.remove x s)) s
def remove_add (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s x, ¬ M.In x s → M.Equal (M.remove x (M.add x s)) s
def singleton_equal_add (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ x, M.Equal (M.singleton x) (M.add x M.empty)
def remove_singleton_empty (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s x, M.In x s → M.Equal (M.remove x s) M.empty → M.Equal (M.singleton x) s
def union_sym (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Equal (M.union s s') (M.union s' s)
def union_subset_equal (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Subset s s' → M.Equal (M.union s s') s'
def union_equal_1 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' s'', M.Equal s s' → M.Equal (M.union s s'') (M.union s' s'')
def union_equal_2 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' s'', M.Equal s' s'' → M.Equal (M.union s s') (M.union s s'')
def union_assoc (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' s'', M.Equal (M.union (M.union s s') s'') (M.union s (M.union s' s''))
def add_union_singleton (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s x, M.Equal (M.add x s) (M.union (M.singleton x) s)
def union_add (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' x, M.Equal (M.union (M.add x s) s') (M.add x (M.union s s'))
def union_remove_add_1 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' x, M.Equal (M.union (M.remove x s) (M.add x s'))
    (M.union (M.add x s) (M.remove x s'))
def union_remove_add_2 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' x, M.In x s → M.Equal (M.union (M.remove x s) (M.add x s'))
    (M.union s s')
def union_subset_1 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Subset s (M.union s s')
def union_subset_2 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Subset s' (M.union s s')
def union_subset_3 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' s'', M.Subset s s'' → M.Subset s' s'' → M.Subset (M.union s s') s''
def union_subset_4 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' s'', M.Subset s s' → M.Subset (M.union s s'') (M.union s' s'')
def union_subset_5 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' s'', M.Subset s s' → M.Subset (M.union s'' s) (M.union s'' s')
def empty_union_1 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Empty s → M.Equal (M.union s s') s'
def empty_union_2 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Empty s → M.Equal (M.union s' s) s'
def not_in_union (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' x, ¬ M.In x s → ¬ M.In x s' → ¬ M.In x (M.union s s')
def inter_sym (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Equal (M.inter s s') (M.inter s' s)
def inter_subset_equal (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Subset s s' → M.Equal (M.inter s s') s
def inter_equal_1 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' s'', M.Equal s s' → M.Equal (M.inter s s'') (M.inter s' s'')
def inter_equal_2 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' s'', M.Equal s' s'' → M.Equal (M.inter s s') (M.inter s s'')
def inter_assoc (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' s'', M.Equal (M.inter (M.inter s s') s'') (M.inter s (M.inter s' s''))
def union_inter_1 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' s'', M.Equal (M.inter (M.union s s') s'')
    (M.union (M.inter s s'') (M.inter s' s''))
def union_inter_2 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' s'', M.Equal (M.union (M.inter s s') s'')
    (M.inter (M.union s s'') (M.union s' s''))
def inter_add_1 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' x, M.In x s' → M.Equal (M.inter (M.add x s) s')
    (M.add x (M.inter s s'))
def inter_add_2 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' x, ¬ M.In x s' → M.Equal (M.inter (M.add x s) s') (M.inter s s')
def empty_inter_1 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Empty s → M.Empty (M.inter s s')
def empty_inter_2 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Empty s' → M.Empty (M.inter s s')
def inter_subset_1 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Subset (M.inter s s') s
def inter_subset_2 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Subset (M.inter s s') s'
def inter_subset_3 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' s'', M.Subset s'' s → M.Subset s'' s' → M.Subset s'' (M.inter s s')
def empty_diff_1 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Empty s → M.Empty (M.diff s s')
def empty_diff_2 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Empty s → M.Equal (M.diff s' s) s'
def diff_subset (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Subset (M.diff s s') s
def diff_subset_equal (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Subset s s' → M.Equal (M.diff s s') M.empty
def remove_diff_singleton (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s x, M.Equal (M.remove x s) (M.diff s (M.singleton x))
def diff_inter_empty (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Equal (M.inter (M.diff s s') (M.inter s s')) M.empty
def diff_inter_all (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Equal (M.union (M.diff s s') (M.inter s s')) s

def Add_add (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s x, Add E M x s (M.add x s)
def Add_remove (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s x, M.In x s → Add E M x (M.remove x s) s
def union_Add (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' s'' x, Add E M x s s' → Add E M x (M.union s s'') (M.union s' s'')
def inter_Add (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' s'' x, M.In x s'' → Add E M x s s' →
    Add E M x (M.inter s s'') (M.inter s' s'')
def union_Equal (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' s'' x, M.In x s'' → Add E M x s s' →
    M.Equal (M.union s s'') (M.union s' s'')
def inter_Add_2 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' s'' x, ¬ M.In x s'' → Add E M x s s' →
    M.Equal (M.inter s s'') (M.inter s' s'')

def elements_Empty (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s, M.Empty s ↔ M.elements s = []
def elements_empty (E : DecidableType) (M : WSfun E) : Prop :=
  M.elements M.empty = []

def of_list (E : DecidableType) (M : WSfun E) (l : List E.t) : M.t :=
  l.foldr M.add M.empty
def to_list (E : DecidableType) (M : WSfun E) : M.t → List E.t := M.elements

def of_list_1 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ l x, M.In x (of_list E M l) ↔ InA E.eq x l
def of_list_2 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ l, equivlistA E.eq (to_list E M (of_list E M l)) l
def of_list_3 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s, M.Equal (of_list E M (to_list E M s)) s

def fold_spec_right (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s (A : Type) (i : A) (f : E.t → A → A),
    M.fold f s i = List.foldr f i (List.reverse (M.elements s))

def fold_rec {E : DecidableType} (M : WSfun E) : Type (u + 1) :=
  ∀ (A : Type) (P : M.t → A → Type u) (f : E.t → A → A) (i : A) (s : M.t),
    (∀ s', M.Empty s' → P s' i) →
    (∀ x a s' s'', M.In x s → ¬ M.In x s' → Add E M x s' s'' →
      P s' a → P s'' (f x a)) →
    P s (M.fold f s i)

def fold_rec_bis {E : DecidableType} (M : WSfun E) : Type (u + 1) :=
  ∀ (A : Type) (P : M.t → A → Type u) (f : E.t → A → A) (i : A) (s : M.t),
    (∀ s s' a, M.Equal s s' → P s a → P s' a) → P M.empty i →
    (∀ x a s', M.In x s → ¬ M.In x s' → P s' a → P (M.add x s') (f x a)) →
    P s (M.fold f s i)

def fold_rec_nodep {E : DecidableType} (M : WSfun E) : Type (u + 1) :=
  ∀ (A : Type) (P : A → Type u) (f : E.t → A → A) (i : A) (s : M.t),
    P i → (∀ x a, M.In x s → P a → P (f x a)) → P (M.fold f s i)

def fold_rec_weak {E : DecidableType} (M : WSfun E) : Type (u + 1) :=
  ∀ (A : Type) (P : M.t → A → Type u) (f : E.t → A → A) (i : A),
    (∀ s s' a, M.Equal s s' → P s a → P s' a) → P M.empty i →
    (∀ x a s, ¬ M.In x s → P s a → P (M.add x s) (f x a)) →
    ∀ s, P s (M.fold f s i)

def fold_rel {E : DecidableType} (M : WSfun E) : Type (u + 1) :=
  ∀ (A B : Type) (R : A → B → Type u) (f : E.t → A → A) (g : E.t → B → B)
    (i : A) (j : B) (s : M.t), R i j →
    (∀ x a b, M.In x s → R a b → R (f x a) (g x b)) →
    R (M.fold f s i) (M.fold g s j)

def set_induction {E : DecidableType} (M : WSfun E) : Type (u + 1) :=
  ∀ (P : M.t → Type u), (∀ s, M.Empty s → P s) →
    (∀ s s', P s → ∀ x, ¬ M.In x s → Add E M x s s' → P s') → ∀ s, P s

def set_induction_bis {E : DecidableType} (M : WSfun E) : Type (u + 1) :=
  ∀ (P : M.t → Type u), (∀ s s', M.Equal s s' → P s → P s') → P M.empty →
    (∀ x s, ¬ M.In x s → P s → P (M.add x s)) → ∀ s, P s

def fold_identity (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s, M.Equal (M.fold M.add s M.empty) s
def fold_0 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s (A : Type) (i : A) (f : E.t → A → A), ∃ l : List E.t,
    NoDupA E.eq l ∧ (∀ x, M.In x s ↔ InA E.eq x l) ∧
    M.fold f s i = List.foldr f i l
def fold_1 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s (A : Type) (eqA : A → A → Prop) (_st : Equivalence eqA) (i : A)
    (f : E.t → A → A), M.Empty s → eqA (M.fold f s i) i
def fold_2 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' x (A : Type) (eqA : A → A → Prop) (_st : Equivalence eqA)
    (i : A) (f : E.t → A → A), compat_op E.eq eqA f → transpose eqA f →
    ¬ M.In x s → Add E M x s s' → eqA (M.fold f s' i) (f x (M.fold f s i))
def fold_1b (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s (A : Type) (i : A) (f : E.t → A → A), M.Empty s → M.fold f s i = i
def fold_commutes (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ (A : Type) (eqA : A → A → Prop) (_st : Equivalence eqA)
    (f : E.t → A → A) (_Comp : compat_op E.eq eqA f) (_Ass : transpose eqA f)
    (i : A) s x, eqA (M.fold f s (f x i)) (f x (M.fold f s i))
def fold_init (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ (A : Type) (eqA : A → A → Prop) (f : E.t → A → A)
    (_Comp : compat_op E.eq eqA f) i i' s,
    eqA i i' → eqA (M.fold f s i) (M.fold f s i')
def fold_equal (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ (A : Type) (eqA : A → A → Prop) (_st : Equivalence eqA)
    (f : E.t → A → A) (_Comp : compat_op E.eq eqA f) i s s',
    M.Equal s s' → eqA (M.fold f s i) (M.fold f s' i)
def fold_empty (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ (A : Type) (f : E.t → A → A) i, M.fold f M.empty i = i
def fold_add (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ (A : Type) (eqA : A → A → Prop) (_st : Equivalence eqA)
    (f : E.t → A → A) (_Comp : compat_op E.eq eqA f) (_Ass : transpose eqA f)
    i s x, ¬ M.In x s → eqA (M.fold f (M.add x s) i) (f x (M.fold f s i))
def add_fold (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ (A : Type) (eqA : A → A → Prop) (_st : Equivalence eqA)
    (f : E.t → A → A) (_Comp : compat_op E.eq eqA f) (_Ass : transpose eqA f)
    i s x, M.In x s → eqA (M.fold f (M.add x s) i) (M.fold f s i)
def remove_fold_1 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ (A : Type) (eqA : A → A → Prop) (_st : Equivalence eqA)
    (f : E.t → A → A) (_Comp : compat_op E.eq eqA f) (_Ass : transpose eqA f)
    i s x, M.In x s → eqA (f x (M.fold f (M.remove x s) i)) (M.fold f s i)
def remove_fold_2 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ (A : Type) (eqA : A → A → Prop) (_st : Equivalence eqA)
    (f : E.t → A → A) (_Comp : compat_op E.eq eqA f) (_Ass : transpose eqA f)
    i s x, ¬ M.In x s → eqA (M.fold f (M.remove x s) i) (M.fold f s i)
def fold_union_inter (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ (A : Type) (eqA : A → A → Prop) (_st : Equivalence eqA)
    (f : E.t → A → A) (_Comp : compat_op E.eq eqA f) (_Ass : transpose eqA f)
    i s s', eqA (M.fold f (M.union s s') (M.fold f (M.inter s s') i))
      (M.fold f s (M.fold f s' i))
def fold_diff_inter (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ (A : Type) (eqA : A → A → Prop) (_st : Equivalence eqA)
    (f : E.t → A → A) (_Comp : compat_op E.eq eqA f) (_Ass : transpose eqA f)
    i s s', eqA (M.fold f (M.diff s s') (M.fold f (M.inter s s') i))
      (M.fold f s i)
def fold_union (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ (A : Type) (eqA : A → A → Prop) (_st : Equivalence eqA)
    (f : E.t → A → A) (_Comp : compat_op E.eq eqA f) (_Ass : transpose eqA f)
    i s s', (∀ x, ¬ (M.In x s ∧ M.In x s')) →
      eqA (M.fold f (M.union s s') i) (M.fold f s (M.fold f s' i))
def fold_plus (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ (s : M.t) (p : Nat), M.fold (fun _ n => Nat.succ n) s p =
    M.fold (fun _ n => Nat.succ n) s 0 + p
def cardinal_fold (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s, M.cardinal s = M.fold (fun _ n => Nat.succ n) s 0
def cardinal_0 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s, ∃ l : List E.t, NoDupA E.eq l ∧
    (∀ x, M.In x s ↔ InA E.eq x l) ∧ M.cardinal s = l.length
def cardinal_1 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s, M.Empty s → M.cardinal s = 0
def cardinal_2 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' x, ¬ M.In x s → Add E M x s s' → M.cardinal s' = Nat.succ (M.cardinal s)
def cardinal_Empty (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s, M.Empty s ↔ M.cardinal s = 0
def cardinal_inv_1 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s, M.cardinal s = 0 → M.Empty s

def cardinal_inv_2 (E : DecidableType) (M : WSfun E) : Type :=
  ∀ s n, M.cardinal s = Nat.succ n → Subtype (fun x : E.t => M.In x s)
def cardinal_inv_2b (E : DecidableType) (M : WSfun E) : Type :=
  ∀ s, M.cardinal s ≠ 0 → Subtype (fun x : E.t => M.In x s)

def Equal_cardinal (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Equal s s' → M.cardinal s = M.cardinal s'
def cardinal_m (E : DecidableType) (M : WSfun E) : Prop := Equal_cardinal E M
def cardinal_m_Proper (E : DecidableType) (M : WSfun E) : Prop := Equal_cardinal E M
def empty_cardinal (E : DecidableType) (M : WSfun E) : Prop := M.cardinal M.empty = 0
def singleton_cardinal (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ x, M.cardinal (M.singleton x) = 1
def diff_inter_cardinal (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.cardinal (M.diff s s') + M.cardinal (M.inter s s') = M.cardinal s
def union_cardinal (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', (∀ x, ¬ (M.In x s ∧ M.In x s')) →
    M.cardinal (M.union s s') = M.cardinal s + M.cardinal s'
def subset_cardinal (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.Subset s s' → M.cardinal s ≤ M.cardinal s'
def subset_cardinal_lt (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s' x, M.Subset s s' → M.In x s' → ¬ M.In x s → M.cardinal s < M.cardinal s'
def union_inter_cardinal (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.cardinal (M.union s s') + M.cardinal (M.inter s s') =
    M.cardinal s + M.cardinal s'
def union_cardinal_inter (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.cardinal (M.union s s') = M.cardinal s + M.cardinal s' - M.cardinal (M.inter s s')
def union_cardinal_le (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s s', M.cardinal (M.union s s') ≤ M.cardinal s + M.cardinal s'
def add_cardinal_1 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s x, M.In x s → M.cardinal (M.add x s) = M.cardinal s
def add_cardinal_2 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s x, ¬ M.In x s → M.cardinal (M.add x s) = Nat.succ (M.cardinal s)
def remove_cardinal_1 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s x, M.In x s → Nat.succ (M.cardinal (M.remove x s)) = M.cardinal s
def remove_cardinal_2 (E : DecidableType) (M : WSfun E) : Prop :=
  ∀ s x, ¬ M.In x s → M.cardinal (M.remove x s) = M.cardinal s

end WProperties_fun

namespace WProperties

def ofWS (M : WS) : WProperties_fun M.E M.toWSfun :=
  ⟨WDecide_fun.make M.E M.toWSfun⟩

end WProperties

end CompCert4Lean.Lib.FSetProperties
