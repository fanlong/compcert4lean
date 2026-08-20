import CompCert4Lean.Lib.FSetInterface

/-!
# Generic facts generated from a weak finite-set interface

`WFacts_fun` is a structural carrier for an element provider and a matching
`WSfun` implementation.  Its callable boolean equality is executable; the
70 proof-bearing source members are retained as transparent, exact
proposition descriptors.
-/

namespace CompCert4Lean.Lib.FSetFacts

open CompCert4Lean.Lib.FSetInterface

structure PreOrder {A : Type} (r : A → A → Prop) : Prop where
  reflexive : ∀ x, r x x
  transitive : ∀ x y z, r x y → r y z → r x z

/-- The source rewrite-relation class carries no data and remains Prop-valued. -/
structure RewriteRelation {A : Type} (_r : A → A → Prop) : Prop where

structure WFacts_fun (E : DecidableType) (M : WSfun E) : Type 2 where
  source : { provider : WSfun E // provider = M }

def WFacts_fun.make (E : DecidableType) (M : WSfun E) : WFacts_fun E M :=
  ⟨⟨M, rfl⟩⟩

abbrev WFacts := WFacts_fun
abbrev Facts := WFacts

namespace WFacts_fun

variable {ElementProvider : DecidableType} {SetProvider : WSfun ElementProvider}

local notation "WFacts_fun" =>
  CompCert4Lean.Lib.FSetFacts.WFacts_fun ElementProvider SetProvider

abbrev E (_F : WFacts_fun) : DecidableType := ElementProvider
abbrev M (_F : WFacts_fun) : WSfun ElementProvider := SetProvider

abbrev elt (F : WFacts_fun) : Type := F.E.t
abbrev t (F : WFacts_fun) : Type := F.M.t

def eqb (F : WFacts_fun) (x y : F.elt) : Bool :=
  match F.E.eq_dec x y with
  | .left _ => true
  | .right _ => false

def E_ST (F : WFacts_fun) : Prop := Equivalence F.E.eq

def Equal_ST (F : WFacts_fun) : Prop := Equivalence F.M.Equal

def In_eq_iff (F : WFacts_fun) : Prop :=
  ∀ s x y, F.E.eq x y → (F.M.In x s ↔ F.M.In y s)

def mem_iff (F : WFacts_fun) : Prop :=
  ∀ s x, F.M.In x s ↔ F.M.mem x s = true

def not_mem_iff (F : WFacts_fun) : Prop :=
  ∀ s x, ¬ F.M.In x s ↔ F.M.mem x s = false

def equal_iff (F : WFacts_fun) : Prop :=
  ∀ s s', F.M.Equal s s' ↔ F.M.equal s s' = true

def subset_iff (F : WFacts_fun) : Prop :=
  ∀ s s', F.M.Subset s s' ↔ F.M.subset s s' = true

def empty_iff (F : WFacts_fun) : Prop :=
  ∀ x, F.M.In x F.M.empty ↔ False

def is_empty_iff (F : WFacts_fun) : Prop :=
  ∀ s, F.M.Empty s ↔ F.M.is_empty s = true

def singleton_iff (F : WFacts_fun) : Prop :=
  ∀ x y, F.M.In y (F.M.singleton x) ↔ F.E.eq x y

def add_iff (F : WFacts_fun) : Prop :=
  ∀ s x y, F.M.In y (F.M.add x s) ↔ F.E.eq x y ∨ F.M.In y s

def add_neq_iff (F : WFacts_fun) : Prop :=
  ∀ s x y, ¬ F.E.eq x y →
    (F.M.In y (F.M.add x s) ↔ F.M.In y s)

def remove_iff (F : WFacts_fun) : Prop :=
  ∀ s x y, F.M.In y (F.M.remove x s) ↔
    F.M.In y s ∧ ¬ F.E.eq x y

def remove_neq_iff (F : WFacts_fun) : Prop :=
  ∀ s x y, ¬ F.E.eq x y →
    (F.M.In y (F.M.remove x s) ↔ F.M.In y s)

def union_iff (F : WFacts_fun) : Prop :=
  ∀ s s' x, F.M.In x (F.M.union s s') ↔
    F.M.In x s ∨ F.M.In x s'

def inter_iff (F : WFacts_fun) : Prop :=
  ∀ s s' x, F.M.In x (F.M.inter s s') ↔
    F.M.In x s ∧ F.M.In x s'

def diff_iff (F : WFacts_fun) : Prop :=
  ∀ s s' x, F.M.In x (F.M.diff s s') ↔
    F.M.In x s ∧ ¬ F.M.In x s'

def filter_iff (F : WFacts_fun) : Prop :=
  ∀ s x f, compat_bool F.E.eq f →
    (F.M.In x (F.M.filter f s) ↔ F.M.In x s ∧ f x = true)

def for_all_iff (F : WFacts_fun) : Prop :=
  ∀ s f, compat_bool F.E.eq f →
    (F.M.For_all (fun x => f x = true) s ↔ F.M.for_all f s = true)

def exists_iff (F : WFacts_fun) : Prop :=
  ∀ s f, compat_bool F.E.eq f →
    (F.M.Exists (fun x => f x = true) s ↔ F.M.exists_ f s = true)

def elements_iff (F : WFacts_fun) : Prop :=
  ∀ s x, F.M.In x s ↔ InA F.E.eq x (F.M.elements s)

def mem_b (F : WFacts_fun) : Prop :=
  ∀ s x y, F.E.eq x y → F.M.mem x s = F.M.mem y s

def empty_b (F : WFacts_fun) : Prop :=
  ∀ y, F.M.mem y F.M.empty = false

def add_b (F : WFacts_fun) : Prop :=
  ∀ s x y, F.M.mem y (F.M.add x s) = (F.eqb x y || F.M.mem y s)

def add_neq_b (F : WFacts_fun) : Prop :=
  ∀ s x y, ¬ F.E.eq x y → F.M.mem y (F.M.add x s) = F.M.mem y s

def remove_b (F : WFacts_fun) : Prop :=
  ∀ s x y, F.M.mem y (F.M.remove x s) =
    (F.M.mem y s && !(F.eqb x y))

def remove_neq_b (F : WFacts_fun) : Prop :=
  ∀ s x y, ¬ F.E.eq x y →
    F.M.mem y (F.M.remove x s) = F.M.mem y s

def singleton_b (F : WFacts_fun) : Prop :=
  ∀ x y, F.M.mem y (F.M.singleton x) = F.eqb x y

def union_b (F : WFacts_fun) : Prop :=
  ∀ s s' x, F.M.mem x (F.M.union s s') =
    (F.M.mem x s || F.M.mem x s')

def inter_b (F : WFacts_fun) : Prop :=
  ∀ s s' x, F.M.mem x (F.M.inter s s') =
    (F.M.mem x s && F.M.mem x s')

def diff_b (F : WFacts_fun) : Prop :=
  ∀ s s' x, F.M.mem x (F.M.diff s s') =
    (F.M.mem x s && !(F.M.mem x s'))

def elements_b (F : WFacts_fun) : Prop :=
  ∀ s x, F.M.mem x s = (F.M.elements s).any (F.eqb x)

def filter_b (F : WFacts_fun) : Prop :=
  ∀ s x f, compat_bool F.E.eq f →
    F.M.mem x (F.M.filter f s) = (F.M.mem x s && f x)

def for_all_b (F : WFacts_fun) : Prop :=
  ∀ s f, compat_bool F.E.eq f →
    F.M.for_all f s = (F.M.elements s).all f

def exists_b (F : WFacts_fun) : Prop :=
  ∀ s f, compat_bool F.E.eq f →
    F.M.exists_ f s = (F.M.elements s).any f

def In_m (F : WFacts_fun) : Prop :=
  ∀ x y, F.E.eq x y → ∀ s s', F.M.Equal s s' →
    (F.M.In x s ↔ F.M.In y s')

def In_s_m (F : WFacts_fun) : Prop :=
  ∀ x y, F.E.eq x y → ∀ s s', F.M.Subset s s' →
    F.M.In x s → F.M.In y s'

def Empty_m (F : WFacts_fun) : Prop :=
  ∀ s s', F.M.Equal s s' →
    (F.M.Empty s ↔ F.M.Empty s')

def Empty_s_m (F : WFacts_fun) : Prop :=
  ∀ s s', F.M.Subset s' s → F.M.Empty s → F.M.Empty s'

def Empty_s_m_Proper (F : WFacts_fun) : Prop :=
  ∀ s s', F.M.Subset s' s → F.M.Empty s → F.M.Empty s'

def Subset_m (F : WFacts_fun) : Prop :=
  ∀ s s', F.M.Equal s s' → ∀ s'' s''', F.M.Equal s'' s''' →
    (F.M.Subset s s'' ↔ F.M.Subset s' s''')

def Subset_refl (F : WFacts_fun) : Prop :=
  ∀ s, F.M.Subset s s

def Subset_trans (F : WFacts_fun) : Prop :=
  ∀ s s' s'', F.M.Subset s s' → F.M.Subset s' s'' → F.M.Subset s s''

def SubsetSetoid (F : WFacts_fun) : Prop := PreOrder F.M.Subset

def SubsetSetoid_Reflexive (F : WFacts_fun) : Prop :=
  ∀ s, F.M.Subset s s

def SubsetSetoid_Transitive (F : WFacts_fun) : Prop :=
  ∀ s s' s'', F.M.Subset s s' → F.M.Subset s' s'' → F.M.Subset s s''

def SubsetSetoid_relation (F : WFacts_fun) : Prop :=
  RewriteRelation F.M.Subset

def add_m (F : WFacts_fun) : Prop :=
  ∀ x y, F.E.eq x y → ∀ s s', F.M.Equal s s' →
    F.M.Equal (F.M.add x s) (F.M.add y s')

def add_s_m (F : WFacts_fun) : Prop :=
  ∀ x y, F.E.eq x y → ∀ s s', F.M.Subset s s' →
    F.M.Subset (F.M.add x s) (F.M.add y s')

def add_s_m_Proper (F : WFacts_fun) : Prop :=
  ∀ x y, F.E.eq x y → ∀ s s', F.M.Subset s s' →
    F.M.Subset (F.M.add x s) (F.M.add y s')

def remove_m (F : WFacts_fun) : Prop :=
  ∀ x y, F.E.eq x y → ∀ s s', F.M.Equal s s' →
    F.M.Equal (F.M.remove x s) (F.M.remove y s')

def remove_s_m (F : WFacts_fun) : Prop :=
  ∀ x y, F.E.eq x y → ∀ s s', F.M.Subset s s' →
    F.M.Subset (F.M.remove x s) (F.M.remove y s')

def remove_s_m_Proper (F : WFacts_fun) : Prop :=
  ∀ x y, F.E.eq x y → ∀ s s', F.M.Subset s s' →
    F.M.Subset (F.M.remove x s) (F.M.remove y s')

def union_m (F : WFacts_fun) : Prop :=
  ∀ s s', F.M.Equal s s' → ∀ s'' s''', F.M.Equal s'' s''' →
    F.M.Equal (F.M.union s s'') (F.M.union s' s''')

def union_s_m (F : WFacts_fun) : Prop :=
  ∀ s s', F.M.Subset s s' → ∀ s'' s''', F.M.Subset s'' s''' →
    F.M.Subset (F.M.union s s'') (F.M.union s' s''')

def union_s_m_Proper (F : WFacts_fun) : Prop :=
  ∀ s s', F.M.Subset s s' → ∀ s'' s''', F.M.Subset s'' s''' →
    F.M.Subset (F.M.union s s'') (F.M.union s' s''')

def inter_m (F : WFacts_fun) : Prop :=
  ∀ s s', F.M.Equal s s' → ∀ s'' s''', F.M.Equal s'' s''' →
    F.M.Equal (F.M.inter s s'') (F.M.inter s' s''')

def inter_s_m (F : WFacts_fun) : Prop :=
  ∀ s s', F.M.Subset s s' → ∀ s'' s''', F.M.Subset s'' s''' →
    F.M.Subset (F.M.inter s s'') (F.M.inter s' s''')

def inter_s_m_Proper (F : WFacts_fun) : Prop :=
  ∀ s s', F.M.Subset s s' → ∀ s'' s''', F.M.Subset s'' s''' →
    F.M.Subset (F.M.inter s s'') (F.M.inter s' s''')

def diff_m (F : WFacts_fun) : Prop :=
  ∀ s s', F.M.Equal s s' → ∀ s'' s''', F.M.Equal s'' s''' →
    F.M.Equal (F.M.diff s s'') (F.M.diff s' s''')

def diff_s_m (F : WFacts_fun) : Prop :=
  ∀ s s', F.M.Subset s s' → ∀ s'' s''', F.M.Subset s''' s'' →
    F.M.Subset (F.M.diff s s'') (F.M.diff s' s''')

def diff_s_m_Proper (F : WFacts_fun) : Prop :=
  ∀ s s', F.M.Subset s s' → ∀ s'' s''', F.M.Subset s''' s'' →
    F.M.Subset (F.M.diff s s'') (F.M.diff s' s''')

def singleton_m (F : WFacts_fun) : Prop :=
  ∀ x y, F.E.eq x y → F.M.Equal (F.M.singleton x) (F.M.singleton y)

def is_empty_m (F : WFacts_fun) : Prop :=
  ∀ s s', F.M.Equal s s' → F.M.is_empty s = F.M.is_empty s'

def mem_m (F : WFacts_fun) : Prop :=
  ∀ x y, F.E.eq x y → ∀ s s', F.M.Equal s s' →
    F.M.mem x s = F.M.mem y s'

def equal_m (F : WFacts_fun) : Prop :=
  ∀ s s', F.M.Equal s s' → ∀ s'' s''', F.M.Equal s'' s''' →
    F.M.equal s s'' = F.M.equal s' s'''

def subset_m (F : WFacts_fun) : Prop :=
  ∀ s s', F.M.Equal s s' → ∀ s'' s''', F.M.Equal s'' s''' →
    F.M.subset s s'' = F.M.subset s' s'''

def filter_equal (F : WFacts_fun) : Prop :=
  ∀ f, compat_bool F.E.eq f → ∀ s s', F.M.Equal s s' →
    F.M.Equal (F.M.filter f s) (F.M.filter f s')

def filter_ext (F : WFacts_fun) : Prop :=
  ∀ f f', compat_bool F.E.eq f → (∀ x, f x = f' x) → ∀ s s',
    F.M.Equal s s' → F.M.Equal (F.M.filter f s) (F.M.filter f' s')

def filter_subset (F : WFacts_fun) : Prop :=
  ∀ f, compat_bool F.E.eq f → ∀ s s', F.M.Subset s s' →
    F.M.Subset (F.M.filter f s) (F.M.filter f s')

end «WFacts_fun»

namespace WFacts

def ofWS (M : WS) : WFacts_fun M.E M.toWSfun := WFacts_fun.make M.E M.toWSfun

end WFacts

namespace Facts

def ofS (M : S) : WFacts_fun M.E.toDecidableType M.toSfun.toWSfun :=
  WFacts_fun.make M.E.toDecidableType M.toSfun.toWSfun

end Facts

end CompCert4Lean.Lib.FSetFacts
