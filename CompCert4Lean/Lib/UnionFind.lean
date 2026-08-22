import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Recursion

/-!
# Persistent union-find interfaces and executable definitions

This module keeps the source-shaped `MAP`, `UNIONFIND`, and `UF` names.  The
proof-bearing source lemmas assigned to the later proof phase are represented
by exact proposition descriptors; executable definitions remain checked Lean
definitions.
-/

namespace CompCert4Lean.Lib.UnionFind

open CompCert4Lean.Foundation.Logic.Support
open CompCert4Lean.Foundation.Recursion.Rocq.Coq.Init.Wf

structure MAP where
  elt : Type
  elt_eq : DecidableEq elt
  t : Type → Type
  empty : (A : Type) → t A
  get : {A : Type} → elt → t A → Option A
  set : {A : Type} → elt → A → t A → t A
  gempty : {A : Type} → (x : elt) → get x (empty A) = none
  gsspec : {A : Type} → (x y : elt) → (v : A) → (m : t A) →
    get x (set y v m) = if h : x = y then some v else get x m

private instance (M : MAP) : DecidableEq M.elt := M.elt_eq

structure UNIONFIND where
  elt : Type
  elt_eq : DecidableEq elt
  t : Type
  repr : t → elt → elt
  repr_canonical : ∀ uf a, repr uf (repr uf a) = repr uf a
  sameclass_refl : ∀ uf a, repr uf a = repr uf a
  sameclass_sym : ∀ uf a b, repr uf a = repr uf b → repr uf b = repr uf a
  sameclass_trans : ∀ uf a b c,
    repr uf a = repr uf b → repr uf b = repr uf c → repr uf a = repr uf c
  sameclass_repr : ∀ uf a, repr uf a = repr uf (repr uf a)
  empty : t
  repr_empty : ∀ a, repr empty a = a
  sameclass_empty : ∀ a b, repr empty a = repr empty b → a = b
  find : t → elt → elt × t
  find_repr : ∀ uf a, (find uf a).1 = repr uf a
  find_unchanged : ∀ uf a x, repr (find uf a).2 x = repr uf x
  sameclass_find_1 : ∀ uf a x y,
    repr (find uf a).2 x = repr (find uf a).2 y ↔ repr uf x = repr uf y
  sameclass_find_2 : ∀ uf a, repr uf a = repr uf (find uf a).1
  sameclass_find_3 : ∀ uf a,
    repr (find uf a).2 a = repr (find uf a).2 (find uf a).1
  union : t → elt → elt → t
  repr_union_1 : ∀ uf a b x, repr uf x ≠ repr uf a →
    repr (union uf a b) x = repr uf x
  repr_union_2 : ∀ uf a b x, repr uf x = repr uf a →
    repr (union uf a b) x = repr uf b
  repr_union_3 : ∀ uf a b, repr (union uf a b) b = repr uf b
  sameclass_union_1 : ∀ uf a b,
    repr (union uf a b) a = repr (union uf a b) b
  sameclass_union_2 : ∀ uf a b x y,
    repr uf x = repr uf y → repr (union uf a b) x = repr (union uf a b) y
  sameclass_union_3 : ∀ uf a b x y,
    repr (union uf a b) x = repr (union uf a b) y →
      repr uf x = repr uf y ∨
      (repr uf x = repr uf a ∧ repr uf y = repr uf b) ∨
      (repr uf x = repr uf b ∧ repr uf y = repr uf a)
  merge : t → elt → elt → t
  repr_merge : ∀ uf a b x, repr (merge uf a b) x = repr (union uf a b) x
  sameclass_merge : ∀ uf a b x y,
    repr (merge uf a b) x = repr (merge uf a b) y ↔
      repr (union uf a b) x = repr (union uf a b) y
  path_ord : t → elt → elt → Prop
  path_ord_wellfounded : ∀ uf, WellFounded (path_ord uf)
  path_ord_canonical : ∀ uf x y, repr uf x = x → ¬ path_ord uf y x
  path_ord_merge_1 : ∀ uf a b x y,
    path_ord uf x y → path_ord (merge uf a b) x y
  path_ord_merge_2 : ∀ uf a b,
    repr uf a ≠ repr uf b → path_ord (merge uf a b) b (repr uf a)
  pathlen : t → elt → Nat
  pathlen_zero : ∀ uf a, repr uf a = a ↔ pathlen uf a = 0
  pathlen_merge : ∀ uf a b x,
    pathlen (merge uf a b) x =
      if h : repr uf a = repr uf b then pathlen uf x
      else if h' : repr uf x = repr uf a then
        pathlen uf x + pathlen uf b + 1
      else pathlen uf x
  pathlen_gt_merge : ∀ uf a b x y,
    repr uf x = repr uf y → pathlen uf x > pathlen uf y →
      pathlen (merge uf a b) x > pathlen (merge uf a b) y

private def UFOrder (M : MAP) (m : M.t M.elt) (a a' : M.elt) : Prop :=
  M.get a' m = some a

namespace UNIONFIND

def sameclass (U : UNIONFIND) (uf : U.t) (a b : U.elt) : Prop :=
  U.repr uf a = U.repr uf b

end UNIONFIND

namespace UF

variable (M : MAP)

structure unionfind (M : MAP) where
  m : M.t M.elt
  mwf : WellFounded (UFOrder M m)

export unionfind (m mwf)

abbrev elt : Type := M.elt

def elt_eq : DecidableEq (elt M) := M.elt_eq

abbrev order (m : M.t (elt M)) (a a' : elt M) : Prop :=
  UFOrder M m a a'

abbrev t : Type := unionfind M

def getlink (m : M.t (elt M)) (a : elt M) :
    Sumor (Subtype (fun a' => M.get a m = some a')) (M.get a m = none) :=
  match M.get a m with
  | some a' => .inleft ⟨a', rfl⟩
  | none => .inright rfl

def F_repr (uf : t M) (a : elt M)
    (rec : ∀ b, UFOrder M uf.m b a → elt M) : elt M :=
  match getlink M uf.m a with
  | .inleft h => rec h.1 h.2
  | .inright _ => a

def repr (uf : t M) (a : elt M) : elt M :=
  WellFounded.fix uf.mwf (F_repr M uf) a

private theorem repr_unroll_calc (uf : t M) (a : elt M) :
    repr M uf a = match M.get a uf.m with
      | some a' => repr M uf a'
      | none => a := by
  unfold repr
  rw [WellFounded.fix_eq]
  cases h : getlink M uf.m a with
  | inleft h' =>
      cases h' with
      | mk a' ha =>
          simp [F_repr, h, ha]
  | inright hnone =>
      simp [F_repr, h, hnone]

private theorem repr_none_calc (uf : t M) (a : elt M)
    (h : M.get a uf.m = none) : repr M uf a = a := by
  rw [repr_unroll_calc M uf a, h]

private theorem repr_some_calc (uf : t M) (a a' : elt M)
    (h : M.get a uf.m = some a') : repr M uf a = repr M uf a' := by
  rw [repr_unroll_calc M uf a, h]

private theorem repr_res_none_calc (uf : t M) (a : elt M) :
    M.get (repr M uf a) uf.m = none := by
  apply uf.mwf.induction a
  intro x ih
  rw [repr_unroll_calc M uf x]
  cases h : M.get x uf.m with
  | none => simpa [h]
  | some y =>
      simpa [h] using ih y h

def sameclass (uf : t M) (a b : elt M) : Prop :=
  repr M uf a = repr M uf b

def empty : t M :=
  { m := M.empty (elt M)
    mwf := by
      apply _root_.WellFounded.intro
      intro x
      apply _root_.Acc.intro x
      intro y h
      change M.get x (M.empty (elt M)) = some y at h
      rw [M.gempty] at h
      cases h }

private theorem identify_order (uf : t M) (a b : elt M)
    (ha : M.get a uf.m = none) (x y : elt M) :
  order M (M.set a b uf.m) y x ↔
    order M uf.m y x ∨ (x = a ∧ y = b) := by
  change M.get x (M.set a b uf.m) = some y ↔
    M.get x uf.m = some y ∨ (x = a ∧ y = b)
  rw [M.gsspec]
  by_cases hxa : x = a
  · subst x
    simp only [dif_pos rfl]
    constructor
    · intro h
      have hyb : y = b := by simpa using h.symm
      exact Or.inr ⟨by simp, hyb⟩
    · intro h
      rcases h with h | ⟨_, h⟩
      · rw [ha] at h
        cases h
      · simpa [h]
  · simp [hxa]

private def identify_Acc_b (uf : t M) (a b : elt M) (x : elt M)
    (ha : M.get a uf.m = none) (hneq : repr M uf x ≠ a) :
    _root_.Acc (order M (M.set a b uf.m)) x :=
  by
    refine (_root_.WellFounded.induction uf.mwf
      (C := fun x => repr M uf x ≠ a →
        _root_.Acc (order M (M.set a b uf.m)) x) x ?_) hneq
    intro x ih hneq
    apply Acc.intro x
    intro y hxy
    rw [identify_order M uf a b ha x y] at hxy
    cases hxy with
    | inl hxy =>
        apply ih y hxy
        intro hya
        apply hneq
        exact (repr_some_calc M uf x y hxy).trans hya
    | inr hxy =>
        rcases hxy with ⟨hxa, hyb⟩
        subst x
        subst y
        exact False.elim (hneq (repr_none_calc M uf a ha))

private def identify_Acc (uf : t M) (a b : elt M) (x : elt M)
    (ha : M.get a uf.m = none) (hneq : repr M uf b ≠ a) :
    _root_.Acc (order M (M.set a b uf.m)) x :=
  by
    apply _root_.WellFounded.induction uf.mwf
      (C := fun _x => _root_.Acc (order M (M.set a b uf.m)) _x) x
    intro x ih
    apply Acc.intro x
    intro y hxy
    rw [identify_order M uf a b ha x y] at hxy
    cases hxy with
    | inl hxy => exact ih y hxy
    | inr hxy =>
        rcases hxy with ⟨hxa, hyb⟩
        subst x
        subst y
        exact identify_Acc_b M uf a b b ha hneq

private def identify_wf (uf : t M) (a b : elt M)
    (ha : M.get a uf.m = none) (hneq : repr M uf b ≠ a) :
    WellFounded (order M (M.set a b uf.m)) := by
  apply _root_.WellFounded.intro
  intro x
  exact identify_Acc M uf a b x ha hneq

def identify (uf : t M) (a b : elt M) : t M :=
  if ha : M.get a uf.m = none then
    if hneq : repr M uf b ≠ a then
      { m := M.set a b uf.m
        mwf := identify_wf M uf a b ha hneq }
    else
      uf
  else
    uf

def union (uf : t M) (a b : elt M) : t M :=
  let a' := repr M uf a
  let b' := repr M uf b
  if h : a' = b' then
    uf
  else
    identify M uf a' b'

def merge (uf : t M) (a b : elt M) : t M :=
  let a' := repr M uf a
  let b' := repr M uf b
  if h : a' = b' then
    uf
  else
    identify M uf a' b

def path_ord (uf : t M) : elt M → elt M → Prop := order M uf.m

def F_pathlen (uf : t M) (a : elt M)
    (rec : ∀ b, UFOrder M uf.m b a → Nat) : Nat :=
  match getlink M uf.m a with
  | .inleft h => Nat.succ (rec h.1 h.2)
  | .inright _ => 0

def pathlen (uf : t M) (a : elt M) : Nat :=
  WellFounded.fix uf.mwf (F_pathlen M uf) a

private def compress_Acc (uf : t M) (a b : elt M) (x : elt M)
    (hneq : a ≠ b) (hrepr : repr M uf a = b) :
    _root_.Acc (order M (M.set a b uf.m)) x :=
  by
    apply _root_.WellFounded.induction uf.mwf
      (C := fun _x => _root_.Acc (order M (M.set a b uf.m)) _x) x
    intro x ih
    apply Acc.intro x
    intro y hxy
    change M.get x (M.set a b uf.m) = some y at hxy
    rw [M.gsspec] at hxy
    by_cases hxa : x = a
    · subst x
      simp at hxy
      subst y
      apply Acc.intro b
      intro z hzb
      change M.get b (M.set a b uf.m) = some z at hzb
      rw [M.gsspec] at hzb
      by_cases hba : b = a
      · exact False.elim (hneq hba.symm)
      · simp [hba] at hzb
        have hnone := repr_res_none_calc M uf a
        rw [hrepr] at hnone
        rw [hzb] at hnone
        cases hnone
    · have hxy' : M.get x uf.m = some y := by simpa [hxa] using hxy
      exact ih y (show UFOrder M uf.m y x from hxy')

private def compress_wf (uf : t M) (a b : elt M)
    (hneq : a ≠ b) (hrepr : repr M uf a = b) :
    WellFounded (order M (M.set a b uf.m)) := by
  apply _root_.WellFounded.intro
  intro x
  exact compress_Acc M uf a b x hneq hrepr

def compress (uf : t M) (a b : elt M) : t M :=
  if hneq : a ≠ b then
    if hrepr : repr M uf a = b then
      { m := M.set a b uf.m
        mwf := compress_wf M uf a b hneq hrepr }
    else
      uf
  else
    uf

def find_x (uf : t M) (a : elt M) : elt M × t M :=
  WellFounded.fix uf.mwf
    (fun x rec =>
      match getlink M uf.m x with
      | .inleft h =>
          let r : elt M × t M := rec h.1 h.2
          (r.1, compress M r.2 x r.1)
      | .inright _ => (x, uf))
    a

def find (uf : t M) (a : elt M) : elt M × t M := find_x M uf a

def union_not_same_classStatement : Prop :=
  ∀ (uf : t M) (a b : elt M), repr M uf a ≠ repr M uf b →
    repr M uf (repr M uf b) ≠ repr M uf a

def repr_unrollStatement : Prop :=
  ∀ (uf : t M) (a : elt M),
    repr M uf a = match M.get a uf.m with
      | some a' => repr M uf a'
      | none => a

def repr_noneStatement : Prop :=
  ∀ (uf : t M) (a : elt M), M.get a uf.m = none → repr M uf a = a

def repr_someStatement : Prop :=
  ∀ (uf : t M) (a a' : elt M),
    M.get a uf.m = some a' → repr M uf a = repr M uf a'

def repr_res_noneStatement : Prop :=
  ∀ (uf : t M) (a : elt M), M.get (repr M uf a) uf.m = none

def repr_canonicalStatement : Prop :=
  ∀ (uf : t M) (a : elt M), repr M uf (repr M uf a) = repr M uf a

def repr_some_diffStatement : Prop :=
  ∀ (uf : t M) (a a' : elt M),
    M.get a uf.m = some a' → a ≠ repr M uf a'

def repr_emptyStatement : Prop :=
  ∀ (a : elt M), repr M (empty M) a = a

def sameclass_reflStatement : Prop :=
  ∀ (uf : t M) (a : elt M), sameclass M uf a a

def sameclass_symStatement : Prop :=
  ∀ (uf : t M) (a b : elt M), sameclass M uf a b → sameclass M uf b a

def sameclass_transStatement : Prop :=
  ∀ (uf : t M) (a b c : elt M), sameclass M uf a b →
    sameclass M uf b c → sameclass M uf a c

def sameclass_reprStatement : Prop :=
  ∀ (uf : t M) (a : elt M), sameclass M uf a (repr M uf a)

def sameclass_emptyStatement : Prop :=
  ∀ (a b : elt M), sameclass M (empty M) a b → a = b

def repr_identify_1Statement : Prop :=
  ∀ (uf : t M) (a b x : elt M), repr M uf x ≠ a →
    repr M (identify M uf a b) x = repr M uf x

def repr_identify_2Statement : Prop :=
  ∀ (uf : t M) (a b x : elt M), repr M uf x = a →
    repr M (identify M uf a b) x = repr M uf b

def repr_union_1Statement : Prop :=
  ∀ (uf : t M) (a b x : elt M), repr M uf x ≠ repr M uf a →
    repr M (union M uf a b) x = repr M uf x

def repr_union_2Statement : Prop :=
  ∀ (uf : t M) (a b x : elt M), repr M uf x = repr M uf a →
    repr M (union M uf a b) x = repr M uf b

def repr_union_3Statement : Prop :=
  ∀ (uf : t M) (a b : elt M),
    repr M (union M uf a b) b = repr M uf b

def sameclass_union_1Statement : Prop :=
  ∀ (uf : t M) (a b : elt M), sameclass M (union M uf a b) a b

def sameclass_union_2Statement : Prop :=
  ∀ (uf : t M) (a b x y : elt M), sameclass M uf x y →
    sameclass M (union M uf a b) x y

def sameclass_union_3Statement : Prop :=
  ∀ (uf : t M) (a b x y : elt M), sameclass M (union M uf a b) x y →
    sameclass M uf x y ∨
      (sameclass M uf x a ∧ sameclass M uf y b) ∨
      (sameclass M uf x b ∧ sameclass M uf y a)

def repr_mergeStatement : Prop :=
  ∀ (uf : t M) (a b x : elt M),
    repr M (merge M uf a b) x = repr M (union M uf a b) x

def sameclass_mergeStatement : Prop :=
  ∀ (uf : t M) (a b x y : elt M),
    sameclass M (merge M uf a b) x y ↔ sameclass M (union M uf a b) x y

def path_ord_wellfoundedStatement : Prop :=
  ∀ (uf : t M), WellFounded (path_ord M uf)

def path_ord_canonicalStatement : Prop :=
  ∀ (uf : t M) (x y : elt M), repr M uf x = x → ¬ path_ord M uf y x

def path_ord_merge_1Statement : Prop :=
  ∀ (uf : t M) (a b x y : elt M), path_ord M uf x y →
    path_ord M (merge M uf a b) x y

def path_ord_merge_2Statement : Prop :=
  ∀ (uf : t M) (a b : elt M), repr M uf a ≠ repr M uf b →
    path_ord M (merge M uf a b) b (repr M uf a)

def pathlen_unrollStatement : Prop :=
  ∀ (uf : t M) (a : elt M),
    pathlen M uf a = match M.get a uf.m with
      | some a' => Nat.succ (pathlen M uf a')
      | none => 0

def pathlen_noneStatement : Prop :=
  ∀ (uf : t M) (a : elt M), M.get a uf.m = none → pathlen M uf a = 0

def pathlen_someStatement : Prop :=
  ∀ (uf : t M) (a a' : elt M), M.get a uf.m = some a' →
    pathlen M uf a = Nat.succ (pathlen M uf a')

def pathlen_zeroStatement : Prop :=
  ∀ (uf : t M) (a : elt M), repr M uf a = a ↔ pathlen M uf a = 0

def pathlen_mergeStatement : Prop := by
  letI : DecidableEq (elt M) := M.elt_eq
  exact ∀ (uf : t M) (a b x : elt M),
    pathlen M (merge M uf a b) x =
      if h : repr M uf a = repr M uf b then pathlen M uf x
      else if h' : repr M uf x = repr M uf a then
        pathlen M uf x + pathlen M uf b + 1
      else pathlen M uf x

def pathlen_gt_mergeStatement : Prop :=
  ∀ (uf : t M) (a b x y : elt M), repr M uf x = repr M uf y →
    pathlen M uf x > pathlen M uf y →
      pathlen M (merge M uf a b) x > pathlen M (merge M uf a b) y

def repr_compressStatement : Prop :=
  ∀ (uf : t M) (a b x : elt M), repr M (compress M uf a b) x = repr M uf x

def compress_orderStatement : Prop :=
  ∀ (uf : t M) (a b : elt M),
    ∀ x y, order M (M.set a b uf.m) y x →
      order M uf.m y x ∨ (x = a ∧ y = b)

def compress_AccStatement : Prop :=
  ∀ (uf : t M) (a b : elt M), ∀ x,
    _root_.Acc (order M uf.m) x → _root_.Acc (order M (M.set a b uf.m)) x

def compress_wfStatement : Prop :=
  ∀ (uf : t M) (a b : elt M), WellFounded (order M (M.set a b uf.m))

def find_reprStatement : Prop :=
  ∀ (uf : t M) (a : elt M), (find M uf a).1 = repr M uf a

def find_unchangedStatement : Prop :=
  ∀ (uf : t M) (a x : elt M), repr M (find M uf a).2 x = repr M uf x

def sameclass_find_1Statement : Prop :=
  ∀ (uf : t M) (a x y : elt M),
    sameclass M (find M uf a).2 x y ↔ sameclass M uf x y

def sameclass_find_2Statement : Prop :=
  ∀ (uf : t M) (a : elt M), sameclass M uf a (find M uf a).1

def sameclass_find_3Statement : Prop :=
  ∀ (uf : t M) (a : elt M),
    sameclass M (find M uf a).2 a (find M uf a).1

def identify_orderStatement : Prop :=
  ∀ (uf : t M) (a b : elt M), ∀ x y,
    order M (M.set a b uf.m) y x ↔ order M uf.m y x ∨ (x = a ∧ y = b)

def identify_Acc_bStatement : Prop :=
  ∀ (uf : t M) (a b : elt M) (x : elt M),
    _root_.Acc (order M uf.m) x → repr M uf x ≠ a →
      _root_.Acc (order M (M.set a b uf.m)) x

def identify_AccStatement : Prop :=
  ∀ (uf : t M) (a b : elt M) (x : elt M),
    _root_.Acc (order M uf.m) x → _root_.Acc (order M (M.set a b uf.m)) x

def identify_wfStatement : Prop :=
  ∀ (uf : t M) (a b : elt M), WellFounded (order M (M.set a b uf.m))

def wf_emptyStatement : Prop :=
  WellFounded (order M (M.empty (elt M)))

end UF

end CompCert4Lean.Lib.UnionFind
