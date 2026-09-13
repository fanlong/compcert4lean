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
  elt_eq : ∀ x y : elt, Sumbool (x = y) (x ≠ y)
  t : Type → Type
  empty : (A : Type) → t A
  get : {A : Type} → elt → t A → Option A
  set : {A : Type} → elt → A → t A → t A
  gempty : (A : Type) → (x : elt) → get x (empty A) = none
  gsspec : {A : Type} → (x y : elt) → (v : A) → (m : t A) →
    get x (set y v m) =
      match elt_eq x y with
      | .left _ => some v
      | .right _ => get x m

private def decidableEqOfSumbool {A : Type}
    (eqDec : ∀ x y : A, Sumbool (x = y) (x ≠ y)) : DecidableEq A :=
  fun x y =>
    match eqDec x y with
    | .left h => .isTrue h
    | .right h => .isFalse h

private instance (M : MAP) : DecidableEq M.elt :=
  decidableEqOfSumbool M.elt_eq

private abbrev mapGet (M : MAP) {A : Type} : M.elt → M.t A → Option A :=
  M.get

private abbrev mapSet (M : MAP) {A : Type} : M.elt → A → M.t A → M.t A :=
  M.set

private theorem mapGet_empty (M : MAP) {A : Type} (x : M.elt) :
    mapGet M x (M.empty A) = none := M.gempty A x

private theorem mapGet_set (M : MAP) {A : Type} (x y : M.elt)
    (v : A) (m : M.t A) :
    mapGet M x (mapSet M y v m) =
      if h : x = y then some v else mapGet M x m := by
  change M.get x (M.set y v m) =
    if h : x = y then some v else M.get x m
  rw [M.gsspec]
  cases hxy : M.elt_eq x y with
  | left h => simp [h]
  | right h => simp [h]

structure UNIONFIND where
  elt : Type
  elt_eq : ∀ x y : elt, Sumbool (x = y) (x ≠ y)
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
      match elt_eq (repr uf a) (repr uf b) with
      | .left _ => pathlen uf x
      | .right _ =>
          match elt_eq (repr uf x) (repr uf a) with
          | .left _ => pathlen uf x + pathlen uf b + 1
          | .right _ => pathlen uf x
  pathlen_gt_merge : ∀ uf a b x y,
    repr uf x = repr uf y → pathlen uf x > pathlen uf y →
      pathlen (merge uf a b) x > pathlen (merge uf a b) y

private def UFOrder (M : MAP) (m : M.t M.elt) (a a' : M.elt) : Prop :=
  mapGet M a' m = some a

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

def elt_eq (x y : elt M) : Sumbool (x = y) (x ≠ y) := M.elt_eq x y

abbrev order (m : M.t (elt M)) (a a' : elt M) : Prop :=
  UFOrder M m a a'

abbrev t : Type := unionfind M

def getlink (m : M.t (elt M)) (a : elt M) :
    Sumor (Subtype (fun a' => mapGet M a m = some a')) (mapGet M a m = none) :=
  match mapGet M a m with
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
    repr M uf a = match mapGet M a uf.m with
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
    (h : mapGet M a uf.m = none) : repr M uf a = a := by
  rw [repr_unroll_calc M uf a, h]

private theorem repr_some_calc (uf : t M) (a a' : elt M)
    (h : mapGet M a uf.m = some a') : repr M uf a = repr M uf a' := by
  rw [repr_unroll_calc M uf a, h]

private theorem repr_res_none_calc (uf : t M) (a : elt M) :
    mapGet M (repr M uf a) uf.m = none := by
  apply uf.mwf.induction a
  intro x ih
  rw [repr_unroll_calc M uf x]
  cases h : mapGet M x uf.m with
  | none => simpa [h]
  | some y =>
      simpa [h] using ih y h

private theorem repr_canonical_calc (uf : t M) (a : elt M) :
    repr M uf (repr M uf a) = repr M uf a :=
  repr_none_calc M uf (repr M uf a) (repr_res_none_calc M uf a)

private theorem repr_some_diff_calc (uf : t M) (a a' : elt M)
    (h : mapGet M a uf.m = some a') : a ≠ repr M uf a' := by
  intro ha
  have hnone := repr_res_none_calc M uf a'
  rw [← ha, h] at hnone
  cases hnone

def sameclass (uf : t M) (a b : elt M) : Prop :=
  repr M uf a = repr M uf b

def empty : t M :=
  { m := M.empty (elt M)
    mwf := by
      apply _root_.WellFounded.intro
      intro x
      apply _root_.Acc.intro x
      intro y h
      change mapGet M x (M.empty (elt M)) = some y at h
      rw [mapGet_empty] at h
      cases h }

private theorem identify_order_calc (uf : t M) (a b : elt M)
    (ha : mapGet M a uf.m = none) (x y : elt M) :
  order M (mapSet M a b uf.m) y x ↔
    order M uf.m y x ∨ (x = a ∧ y = b) := by
  change mapGet M x (mapSet M a b uf.m) = some y ↔
    mapGet M x uf.m = some y ∨ (x = a ∧ y = b)
  rw [mapGet_set]
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

private def identify_Acc_b_calc (uf : t M) (a b : elt M) (x : elt M)
    (ha : mapGet M a uf.m = none) (hneq : repr M uf x ≠ a) :
    _root_.Acc (order M (mapSet M a b uf.m)) x :=
  by
    refine (_root_.WellFounded.induction uf.mwf
      (C := fun x => repr M uf x ≠ a →
        _root_.Acc (order M (mapSet M a b uf.m)) x) x ?_) hneq
    intro x ih hneq
    apply Acc.intro x
    intro y hxy
    rw [identify_order_calc M uf a b ha x y] at hxy
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

private def identify_Acc_calc (uf : t M) (a b : elt M) (x : elt M)
    (ha : mapGet M a uf.m = none) (hneq : repr M uf b ≠ a) :
    _root_.Acc (order M (mapSet M a b uf.m)) x :=
  by
    apply _root_.WellFounded.induction uf.mwf
      (C := fun _x => _root_.Acc (order M (mapSet M a b uf.m)) _x) x
    intro x ih
    apply Acc.intro x
    intro y hxy
    rw [identify_order_calc M uf a b ha x y] at hxy
    cases hxy with
    | inl hxy => exact ih y hxy
    | inr hxy =>
        rcases hxy with ⟨hxa, hyb⟩
        subst x
        subst y
        exact identify_Acc_b_calc M uf a b b ha hneq

private def identify_wf_calc (uf : t M) (a b : elt M)
    (ha : mapGet M a uf.m = none) (hneq : repr M uf b ≠ a) :
    WellFounded (order M (mapSet M a b uf.m)) := by
  apply _root_.WellFounded.intro
  intro x
  exact identify_Acc_calc M uf a b x ha hneq

def identify (uf : t M) (a b : elt M)
    (a_canon : mapGet M a uf.m = none)
    (not_same_class : repr M uf b ≠ a) : t M :=
  { m := mapSet M a b uf.m
    mwf := identify_wf_calc M uf a b a_canon not_same_class }

def union (uf : t M) (a b : elt M) : t M :=
  let a' := repr M uf a
  let b' := repr M uf b
  if h : a' = b' then
    uf
  else
    identify M uf a' b'
      (by simpa [a'] using repr_res_none_calc M uf a)
      (by
        intro hrepr
        apply h
        calc
          a' = repr M uf b' := hrepr.symm
          _ = b' := by simpa [b'] using repr_canonical_calc M uf b)

def merge (uf : t M) (a b : elt M) : t M :=
  let a' := repr M uf a
  let b' := repr M uf b
  if h : a' = b' then
    uf
  else
    identify M uf a' b
      (by simpa [a'] using repr_res_none_calc M uf a)
      (by
        intro hba
        exact h (by simpa [a', b'] using hba.symm))

def path_ord (uf : t M) : elt M → elt M → Prop := order M uf.m

def F_pathlen (uf : t M) (a : elt M)
    (rec : ∀ b, UFOrder M uf.m b a → Nat) : Nat :=
  match getlink M uf.m a with
  | .inleft h => Nat.succ (rec h.1 h.2)
  | .inright _ => 0

def pathlen (uf : t M) (a : elt M) : Nat :=
  WellFounded.fix uf.mwf (F_pathlen M uf) a

private def compress_Acc_calc (uf : t M) (a b : elt M) (x : elt M)
    (hneq : a ≠ b) (hrepr : repr M uf a = b) :
    _root_.Acc (order M (mapSet M a b uf.m)) x :=
  by
    apply _root_.WellFounded.induction uf.mwf
      (C := fun _x => _root_.Acc (order M (mapSet M a b uf.m)) _x) x
    intro x ih
    apply Acc.intro x
    intro y hxy
    change mapGet M x (mapSet M a b uf.m) = some y at hxy
    rw [mapGet_set] at hxy
    by_cases hxa : x = a
    · subst x
      simp at hxy
      subst y
      apply Acc.intro b
      intro z hzb
      change mapGet M b (mapSet M a b uf.m) = some z at hzb
      rw [mapGet_set] at hzb
      by_cases hba : b = a
      · exact False.elim (hneq hba.symm)
      · simp [hba] at hzb
        have hnone := repr_res_none_calc M uf a
        rw [hrepr] at hnone
        rw [hzb] at hnone
        cases hnone
    · have hxy' : mapGet M x uf.m = some y := by simpa [hxa] using hxy
      exact ih y (show UFOrder M uf.m y x from hxy')

private def compress_wf_calc (uf : t M) (a b : elt M)
    (hneq : a ≠ b) (hrepr : repr M uf a = b) :
    WellFounded (order M (mapSet M a b uf.m)) := by
  apply _root_.WellFounded.intro
  intro x
  exact compress_Acc_calc M uf a b x hneq hrepr

def compress (uf : t M) (a b : elt M)
    (a_diff_b : a ≠ b) (a_repr_b : repr M uf a = b) : t M :=
  { m := mapSet M a b uf.m
    mwf := compress_wf_calc M uf a b a_diff_b a_repr_b }

private theorem repr_compress_calc (uf : t M) (a b : elt M)
    (a_diff_b : a ≠ b) (a_repr_b : repr M uf a = b) (x : elt M) :
    repr M (compress M uf a b a_diff_b a_repr_b) x = repr M uf x := by
  apply (compress M uf a b a_diff_b a_repr_b).mwf.induction x
  intro x ih
  rw [repr_unroll_calc M (compress M uf a b a_diff_b a_repr_b) x]
  cases hget : mapGet M x (compress M uf a b a_diff_b a_repr_b).m with
  | some y =>
      simp only
      rw [ih y hget]
      change mapGet M x (mapSet M a b uf.m) = some y at hget
      rw [mapGet_set] at hget
      by_cases hxa : x = a
      · subst x
        simp at hget
        subst y
        rw [← a_repr_b]
        exact repr_canonical_calc M uf a
      · have hxy : mapGet M x uf.m = some y := by simpa [hxa] using hget
        exact (repr_some_calc M uf x y hxy).symm
  | none =>
      simp only
      change mapGet M x (mapSet M a b uf.m) = none at hget
      rw [mapGet_set] at hget
      by_cases hxa : x = a
      · subst x
        simp at hget
      · have hxnone : mapGet M x uf.m = none := by simpa [hxa] using hget
        exact (repr_none_calc M uf x hxnone).symm

private structure FindResult (uf : t M) (a : elt M) where
  value : elt M × t M
  fst_repr : value.1 = repr M uf a
  repr_unchanged : ∀ x, repr M value.2 x = repr M uf x

private def F_find (uf : t M) (a : elt M)
    (rec : ∀ b, UFOrder M uf.m b a → FindResult M uf b) : FindResult M uf a :=
  match hget : mapGet M a uf.m with
  | some a' =>
      let r := rec a' hget
      let b := r.value.1
      let uf' := r.value.2
      have a_diff_b : a ≠ b := by
        intro hab
        exact repr_some_diff_calc M uf a a' hget (hab.trans r.fst_repr)
      have a_repr_b : repr M uf' a = b := by
        calc
          repr M uf' a = repr M uf a := r.repr_unchanged a
          _ = repr M uf a' := repr_some_calc M uf a a' hget
          _ = b := r.fst_repr.symm
      { value := (b, compress M uf' a b a_diff_b a_repr_b)
        fst_repr := r.fst_repr.trans (repr_some_calc M uf a a' hget).symm
        repr_unchanged := fun x =>
          (repr_compress_calc M uf' a b a_diff_b a_repr_b x).trans
            (r.repr_unchanged x) }
  | none =>
      { value := (a, uf)
        fst_repr := (repr_none_calc M uf a hget).symm
        repr_unchanged := fun _ => rfl }

private def find_x_certified (uf : t M) (a : elt M) : FindResult M uf a :=
  WellFounded.fix uf.mwf (F_find M uf) a

def find_xCertificate (uf : t M) (a : elt M) (r : elt M × t M) : Prop :=
  r.1 = repr M uf a ∧ ∀ x, repr M r.2 x = repr M uf x

def find_x (uf : t M) (a : elt M) :
    {r : elt M × t M // find_xCertificate M uf a r} :=
  let r := find_x_certified M uf a
  ⟨r.value, ⟨r.fst_repr, r.repr_unchanged⟩⟩

def find_xCertificateStatement : Prop :=
  ∀ (uf : t M) (a : elt M),
    find_xCertificate M uf a (find_x M uf a).1

/-! Stable companion identities for the six obligations generated by Rocq's
`Program Fixpoint find_x`.  The recursive function argument below is kept
source-shaped: it receives a predecessor and its well-founded proof and
returns the generated certified result.  DMC-003 keeps these propositions
detached from the executable pair while preserving the exact invariant
boundary. -/
private abbrev find_xRecursive (uf : t M) (a : elt M) :=
  ∀ a₀ : elt M, order M uf.m a₀ a →
    {r : elt M × t M //
      r.1 = repr M uf a₀ ∧ ∀ x, repr M r.2 x = repr M uf x}

def find_x_obligation_1Statement : Prop :=
  ∀ (uf : t M) (a : elt M),
    let filtered_var := mapGet M a uf.m
    ∀ (a' : elt M), some a' = filtered_var →
      order M uf.m a' a

def find_x_obligation_2Statement : Prop :=
  ∀ (uf : t M) (a : elt M) (find_x : find_xRecursive M uf a)
    (find_x_obligation_1 : find_x_obligation_1Statement M),
    let filtered_var₀ := mapGet M a uf.m
    ∀ (a' : elt M) (h₀ : some a' = filtered_var₀),
      let filtered_var :=
        (find_x a' (find_x_obligation_1 uf a a' h₀)).1
      ∀ (b : elt M) (uf' : t M),
        (b, uf') = filtered_var →
        let _s := find_x a' (find_x_obligation_1 uf a a' h₀)
        a ≠ b

def find_x_obligation_3Statement : Prop :=
  ∀ (uf : t M) (a : elt M) (find_x : find_xRecursive M uf a)
    (find_x_obligation_1 : find_x_obligation_1Statement M),
    let filtered_var₀ := mapGet M a uf.m
    ∀ (a' : elt M) (h₀ : some a' = filtered_var₀),
      let filtered_var :=
        (find_x a' (find_x_obligation_1 uf a a' h₀)).1
      ∀ (b : elt M) (uf' : t M),
        (b, uf') = filtered_var →
        let _s := find_x a' (find_x_obligation_1 uf a a' h₀)
        repr M uf' a = b

def find_x_obligation_4Statement : Prop :=
  ∀ (uf : t M) (a : elt M) (find_x : find_xRecursive M uf a)
    (find_x_obligation_1 : find_x_obligation_1Statement M)
    (find_x_obligation_2 : find_x_obligation_2Statement M)
    (find_x_obligation_3 : find_x_obligation_3Statement M),
    let filtered_var₀ := mapGet M a uf.m
    ∀ (a' : elt M) (h₀ : some a' = filtered_var₀),
      let filtered_var :=
        (find_x a' (find_x_obligation_1 uf a a' h₀)).1
      ∀ (b : elt M) (uf' : t M) (h : (b, uf') = filtered_var),
        (b, compress M uf' a b
          (find_x_obligation_2 uf a find_x find_x_obligation_1 a' h₀ b uf' h)
          (find_x_obligation_3 uf a find_x find_x_obligation_1 a' h₀ b uf' h)).1 =
            repr M uf a ∧
        ∀ x, repr M
          (b, compress M uf' a b
            (find_x_obligation_2 uf a find_x find_x_obligation_1 a' h₀ b uf' h)
            (find_x_obligation_3 uf a find_x find_x_obligation_1 a' h₀ b uf' h)).2 x =
              repr M uf x

def find_x_obligation_5Statement : Prop :=
  ∀ (uf : t M) (a : elt M),
    let filtered_var := mapGet M a uf.m
    none = filtered_var →
      (a, uf).1 = repr M uf a ∧
      ∀ x, repr M (a, uf).2 x = repr M uf x

private def find_x_MR {α β : Type} (R : α → α → Prop) (f : β → α) :
    β → β → Prop :=
  fun x y => R (f x) (f y)

def find_x_obligation_6Statement : Prop :=
  ∀ (uf : t M),
    CompCert4Lean.Foundation.Recursion.Rocq.Coq.Init.Wf.well_founded
      (find_x_MR (order M uf.m) (fun recarg => let a := recarg; a))

def find (uf : t M) (a : elt M) : elt M × t M := (find_x M uf a).1

def union_not_same_classStatement : Prop :=
  ∀ (uf : t M) (a b : elt M), repr M uf a ≠ repr M uf b →
    repr M uf (repr M uf b) ≠ repr M uf a

def repr_unrollStatement : Prop :=
  ∀ (uf : t M) (a : elt M),
    repr M uf a = match mapGet M a uf.m with
      | some a' => repr M uf a'
      | none => a

def repr_noneStatement : Prop :=
  ∀ (uf : t M) (a : elt M), mapGet M a uf.m = none → repr M uf a = a

def repr_someStatement : Prop :=
  ∀ (uf : t M) (a a' : elt M),
    mapGet M a uf.m = some a' → repr M uf a = repr M uf a'

def repr_res_noneStatement : Prop :=
  ∀ (uf : t M) (a : elt M), mapGet M (repr M uf a) uf.m = none

def repr_canonicalStatement : Prop :=
  ∀ (uf : t M) (a : elt M), repr M uf (repr M uf a) = repr M uf a

def repr_some_diffStatement : Prop :=
  ∀ (uf : t M) (a a' : elt M),
    mapGet M a uf.m = some a' → a ≠ repr M uf a'

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
  ∀ (uf : t M) (a b : elt M)
    (a_canon : mapGet M a uf.m = none)
    (not_same_class : repr M uf b ≠ a) (x : elt M),
    repr M uf x ≠ a →
      repr M (identify M uf a b a_canon not_same_class) x = repr M uf x

def repr_identify_2Statement : Prop :=
  ∀ (uf : t M) (a b : elt M)
    (a_canon : mapGet M a uf.m = none)
    (not_same_class : repr M uf b ≠ a) (x : elt M),
    repr M uf x = a →
      repr M (identify M uf a b a_canon not_same_class) x = repr M uf b

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
    pathlen M uf a = match mapGet M a uf.m with
      | some a' => Nat.succ (pathlen M uf a')
      | none => 0

def pathlen_noneStatement : Prop :=
  ∀ (uf : t M) (a : elt M), mapGet M a uf.m = none → pathlen M uf a = 0

def pathlen_someStatement : Prop :=
  ∀ (uf : t M) (a a' : elt M), mapGet M a uf.m = some a' →
    pathlen M uf a = Nat.succ (pathlen M uf a')

def pathlen_zeroStatement : Prop :=
  ∀ (uf : t M) (a : elt M), repr M uf a = a ↔ pathlen M uf a = 0

def pathlen_mergeStatement : Prop :=
  ∀ (uf : t M) (a b x : elt M),
    pathlen M (merge M uf a b) x =
      match M.elt_eq (repr M uf a) (repr M uf b) with
      | .left _ => pathlen M uf x
      | .right _ =>
          match M.elt_eq (repr M uf x) (repr M uf a) with
          | .left _ => pathlen M uf x + pathlen M uf b + 1
          | .right _ => pathlen M uf x

def pathlen_gt_mergeStatement : Prop :=
  ∀ (uf : t M) (a b x y : elt M), repr M uf x = repr M uf y →
    pathlen M uf x > pathlen M uf y →
      pathlen M (merge M uf a b) x > pathlen M (merge M uf a b) y

def repr_compressStatement : Prop :=
  ∀ (uf : t M) (a b : elt M)
    (a_diff_b : a ≠ b) (a_repr_b : repr M uf a = b) (x : elt M),
    repr M (compress M uf a b a_diff_b a_repr_b) x = repr M uf x

def compress_orderStatement : Prop :=
  ∀ (uf : t M) (a b : elt M),
    ∀ x y, order M (mapSet M a b uf.m) y x →
      order M uf.m y x ∨ (x = a ∧ y = b)

def compress_AccStatement : Prop :=
  ∀ (uf : t M) (a b : elt M)
    (a_diff_b : a ≠ b) (a_repr_b : repr M uf a = b), ∀ x,
    _root_.Acc (order M uf.m) x → _root_.Acc (order M (mapSet M a b uf.m)) x

def compress_wfStatement : Prop :=
  ∀ (uf : t M) (a b : elt M)
    (a_diff_b : a ≠ b) (a_repr_b : repr M uf a = b),
    WellFounded (order M (mapSet M a b uf.m))

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
  ∀ (uf : t M) (a b : elt M)
    (a_canon : mapGet M a uf.m = none), ∀ x y,
    order M (mapSet M a b uf.m) y x ↔ order M uf.m y x ∨ (x = a ∧ y = b)

def identify_Acc_bStatement : Prop :=
  ∀ (uf : t M) (a b : elt M)
    (a_canon : mapGet M a uf.m = none) (x : elt M),
    _root_.Acc (order M uf.m) x → repr M uf x ≠ a →
      _root_.Acc (order M (mapSet M a b uf.m)) x

def identify_AccStatement : Prop :=
  ∀ (uf : t M) (a b : elt M)
    (a_canon : mapGet M a uf.m = none)
    (not_same_class : repr M uf b ≠ a) (x : elt M),
    _root_.Acc (order M uf.m) x → _root_.Acc (order M (mapSet M a b uf.m)) x

def identify_wfStatement : Prop :=
  ∀ (uf : t M) (a b : elt M)
    (a_canon : mapGet M a uf.m = none)
    (not_same_class : repr M uf b ≠ a),
    WellFounded (order M (mapSet M a b uf.m))

def wf_emptyStatement : Prop :=
  WellFounded (order M (M.empty (elt M)))

/-! Public source identities for proof declarations whose proof terms remain
assigned to proof grinding.  Each identity is definitionally the exact mapped
statement descriptor above; the private calculation lemmas remain internal to
the executable implementation. -/
abbrev repr_unroll : Prop := repr_unrollStatement M
abbrev repr_none : Prop := repr_noneStatement M
abbrev repr_some : Prop := repr_someStatement M
abbrev repr_res_none : Prop := repr_res_noneStatement M
abbrev repr_canonical : Prop := repr_canonicalStatement M
abbrev repr_some_diff : Prop := repr_some_diffStatement M
abbrev sameclass_refl : Prop := sameclass_reflStatement M
abbrev sameclass_sym : Prop := sameclass_symStatement M
abbrev sameclass_trans : Prop := sameclass_transStatement M
abbrev sameclass_repr : Prop := sameclass_reprStatement M
abbrev wf_empty : Prop := wf_emptyStatement M
abbrev repr_empty : Prop := repr_emptyStatement M
abbrev sameclass_empty : Prop := sameclass_emptyStatement M
abbrev identify_order : Prop := identify_orderStatement M
abbrev identify_Acc_b : Prop := identify_Acc_bStatement M
abbrev identify_Acc : Prop := identify_AccStatement M
abbrev identify_wf : Prop := identify_wfStatement M
abbrev repr_identify_1 : Prop := repr_identify_1Statement M
abbrev repr_identify_2 : Prop := repr_identify_2Statement M
abbrev union_not_same_class : Prop := union_not_same_classStatement M
abbrev repr_union_1 : Prop := repr_union_1Statement M
abbrev repr_union_2 : Prop := repr_union_2Statement M
abbrev repr_union_3 : Prop := repr_union_3Statement M
abbrev sameclass_union_1 : Prop := sameclass_union_1Statement M
abbrev sameclass_union_2 : Prop := sameclass_union_2Statement M
abbrev sameclass_union_3 : Prop := sameclass_union_3Statement M
abbrev repr_merge : Prop := repr_mergeStatement M
abbrev sameclass_merge : Prop := sameclass_mergeStatement M
abbrev path_ord_wellfounded : Prop := path_ord_wellfoundedStatement M
abbrev path_ord_canonical : Prop := path_ord_canonicalStatement M
abbrev path_ord_merge_1 : Prop := path_ord_merge_1Statement M
abbrev path_ord_merge_2 : Prop := path_ord_merge_2Statement M
abbrev pathlen_unroll : Prop := pathlen_unrollStatement M
abbrev pathlen_none : Prop := pathlen_noneStatement M
abbrev pathlen_some : Prop := pathlen_someStatement M
abbrev pathlen_zero : Prop := pathlen_zeroStatement M
abbrev pathlen_merge : Prop := pathlen_mergeStatement M
abbrev pathlen_gt_merge : Prop := pathlen_gt_mergeStatement M
abbrev compress_order : Prop := compress_orderStatement M
abbrev compress_Acc : Prop := compress_AccStatement M
abbrev compress_wf : Prop := compress_wfStatement M
abbrev repr_compress : Prop := repr_compressStatement M
abbrev find_repr : Prop := find_reprStatement M
abbrev find_unchanged : Prop := find_unchangedStatement M
abbrev sameclass_find_1 : Prop := sameclass_find_1Statement M
abbrev sameclass_find_2 : Prop := sameclass_find_2Statement M
abbrev sameclass_find_3 : Prop := sameclass_find_3Statement M

end UF

end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind

namespace UF

theorem find_x_obligation_1 :
    ∀ (M : MAP), find_x_obligation_1Statement M := by
  intro M uf a
  dsimp
  intro a' h
  change mapGet M a uf.m = some a'
  exact h.symm

theorem repr_unroll_proof :
    ∀ (M : MAP), repr_unrollStatement M := by
  intro M uf a
  exact repr_unroll_calc M uf a

theorem repr_none_proof :
    ∀ (M : MAP), repr_noneStatement M := by
  intro M uf a h
  exact repr_none_calc M uf a h

theorem repr_some_proof :
    ∀ (M : MAP), repr_someStatement M := by
  intro M uf a a' h
  exact repr_some_calc M uf a a' h

end UF

end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind

namespace UF

theorem find_x_obligation_2 :
    ∀ (M : MAP), find_x_obligation_2Statement M := by
  intro M uf a find_x find_x_obligation_1
  dsimp
  intro a' h₀ b uf' h
  have hne : a ≠ repr M uf a' :=
    repr_some_diff_calc M uf a a' h₀.symm
  let r := find_x a' (find_x_obligation_1 uf a a' h₀)
  change (b, uf') = r.1 at h
  have hr : r.1.1 = repr M uf a' := r.2.1
  have hb : b = r.1.1 := by simpa using congrArg Prod.fst h
  intro hab
  apply hne
  exact hab.trans (hb.trans hr)

theorem find_x_obligation_3 :
    ∀ (M : MAP), find_x_obligation_3Statement M := by
  intro M uf a find_x find_x_obligation_1
  dsimp
  intro a' h₀ b uf' h
  let r := find_x a' (find_x_obligation_1 uf a a' h₀)
  change (b, uf') = r.1 at h
  have hr : r.1.1 = repr M uf a' := r.2.1
  have hunchanged : repr M r.1.2 a = repr M uf a := r.2.2 a
  have huf : uf' = r.1.2 := by simpa using congrArg Prod.snd h
  have hb : b = r.1.1 := by simpa using congrArg Prod.fst h
  rw [huf]
  calc
    repr M r.1.2 a = repr M uf a := hunchanged
    _ = repr M uf a' := repr_some_calc M uf a a' h₀.symm
    _ = r.1.1 := hr.symm
    _ = b := hb.symm

theorem repr_res_none_proof :
    ∀ (M : MAP), repr_res_noneStatement M := by
  intro M uf a
  exact repr_res_none_calc M uf a

theorem repr_canonical_proof :
    ∀ (M : MAP), repr_canonicalStatement M := by
  intro M uf a
  exact repr_canonical_calc M uf a

end UF

end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind

namespace UF

theorem repr_some_diff_proof :
    ∀ (M : MAP), repr_some_diffStatement M := by
  intro M uf a a' h
  exact repr_some_diff_calc M uf a a' h

theorem sameclass_refl_proof :
    ∀ (M : MAP), sameclass_reflStatement M := by
  intro M uf a
  rfl

theorem sameclass_sym_proof :
    ∀ (M : MAP), sameclass_symStatement M := by
  intro M uf a b h
  exact h.symm

theorem sameclass_trans_proof :
    ∀ (M : MAP), sameclass_transStatement M := by
  intro M uf a b c hab hbc
  exact hab.trans hbc

end UF

end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind

namespace UF

theorem sameclass_repr_proof :
    ∀ (M : MAP), sameclass_reprStatement M := by
  intro M uf a
  change repr M uf a = repr M uf (repr M uf a)
  exact (repr_canonical_calc M uf a).symm

theorem wf_empty_proof :
    ∀ (M : MAP), wf_emptyStatement M := by
  intro M
  exact (empty M).mwf

theorem repr_empty_proof :
    ∀ (M : MAP), repr_emptyStatement M := by
  intro M a
  exact repr_none_calc M (empty M) a (mapGet_empty M a)

theorem sameclass_empty_proof :
    ∀ (M : MAP), sameclass_emptyStatement M := by
  intro M a b h
  change repr M (empty M) a = repr M (empty M) b at h
  rw [repr_empty_proof M a, repr_empty_proof M b] at h
  exact h

end UF

end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF
theorem identify_order_proof :
    ∀ (M : MAP), identify_orderStatement M := by
  intro M uf a b a_canon x y
  exact identify_order_calc M uf a b a_canon x y
end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem identify_Acc_b_proof :
    ∀ (M : MAP), identify_Acc_bStatement M := by
  intro M uf a b a_canon x _hacc hneq
  exact identify_Acc_b_calc M uf a b x a_canon hneq

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem identify_Acc_proof :
    ∀ (M : MAP), identify_AccStatement M := by
  intro M uf a b a_canon not_same_class x _hacc
  exact identify_Acc_calc M uf a b x a_canon not_same_class

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem identify_wf_proof :
    ∀ (M : MAP), identify_wfStatement M := by
  intro M uf a b a_canon not_same_class
  exact identify_wf_calc M uf a b a_canon not_same_class

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem union_not_same_class_proof :
    ∀ (M : MAP), union_not_same_classStatement M := by
  intro M uf a b hne h
  apply hne
  exact h.symm.trans (repr_canonical_calc M uf b)

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem repr_identify_1_proof :
    ∀ (M : MAP), repr_identify_1Statement M := by
  intro M uf a b a_canon not_same_class x
  apply uf.mwf.induction x
  intro x ih hneq
  rw [repr_unroll_calc M uf x]
  cases hget : mapGet M x uf.m with
  | some y =>
      rw [repr_unroll_calc M (identify M uf a b a_canon not_same_class) x]
      change (match mapGet M x (mapSet M a b uf.m) with
        | some a' => repr M (identify M uf a b a_canon not_same_class) a'
        | none => x) = repr M uf y
      rw [mapGet_set]
      by_cases hxa : x = a
      · subst x
        rw [a_canon] at hget
        cases hget
      · rw [dif_neg hxa, hget]
        exact ih y hget (by
          intro hya
          apply hneq
          exact (repr_some_calc M uf x y hget).trans hya)
  | none =>
      rw [repr_unroll_calc M (identify M uf a b a_canon not_same_class) x]
      change (match mapGet M x (mapSet M a b uf.m) with
        | some a' => repr M (identify M uf a b a_canon not_same_class) a'
        | none => x) = x
      rw [mapGet_set]
      by_cases hxa : x = a
      · subst x
        simp [a_canon]
        exact False.elim (hneq (repr_none_calc M uf a a_canon))
      · simp [hxa, hget]

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem repr_identify_2_proof :
    forall (M : MAP), repr_identify_2Statement M := by
  intro M uf a b a_canon not_same_class x
  apply uf.mwf.induction x
  intro x ih hrepr
  rw [repr_unroll_calc M uf x] at hrepr
  cases hget : mapGet M x uf.m with
  | some y =>
      rw [repr_unroll_calc M (identify M uf a b a_canon not_same_class) x]
      change (match mapGet M x (mapSet M a b uf.m) with
        | some a' => repr M (identify M uf a b a_canon not_same_class) a'
        | none => x) = repr M uf b
      rw [mapGet_set]
      by_cases hxa : x = a
      · subst x
        rw [a_canon] at hget
        cases hget
      · rw [dif_neg hxa, hget]
        exact ih y hget (by simpa [hget] using hrepr)
  | none =>
      simp [hget] at hrepr
      rw [hrepr]
      rw [repr_unroll_calc M (identify M uf a b a_canon not_same_class) a]
      change (match mapGet M a (mapSet M a b uf.m) with
        | some a' => repr M (identify M uf a b a_canon not_same_class) a'
        | none => a) = repr M uf b
      rw [mapGet_set]
      simp only [dif_pos rfl]
      apply repr_identify_1_proof M uf a b a_canon not_same_class b
      exact not_same_class

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem repr_union_1_proof :
    ∀ (M : MAP), repr_union_1Statement M := by
  intro M uf a b x hneq
  unfold union
  dsimp
  by_cases hab : repr M uf a = repr M uf b
  · simp [hab]
  · simp only [dif_neg hab]
    apply repr_identify_1_proof M uf (repr M uf a) (repr M uf b) _ _ x
    exact hneq

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem repr_union_3_proof :
    ∀ (M : MAP), repr_union_3Statement M := by
  intro M uf a b
  unfold union
  dsimp
  by_cases hab : repr M uf a = repr M uf b
  · simp [hab]
  · simp only [dif_neg hab]
    apply repr_identify_1_proof M uf (repr M uf a) (repr M uf b)
      (repr_res_none_calc M uf a)
    · intro hba
      apply hab
      exact hba.symm

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem repr_union_2_proof :
    ∀ (M : MAP), repr_union_2Statement M := by
  intro M uf a b x h
  unfold union
  dsimp
  by_cases hab : repr M uf a = repr M uf b
  · simp [hab, h]
  · simp only [dif_neg hab]
    have ha : mapGet M (repr M uf a) uf.m = none :=
      repr_res_none_calc M uf a
    have hneq : repr M uf (repr M uf b) ≠ repr M uf a := by
      intro hrepr
      apply hab
      calc
        repr M uf a = repr M uf (repr M uf b) := hrepr.symm
        _ = repr M uf b := repr_canonical_calc M uf b
    have hi := repr_identify_2_proof M uf (repr M uf a) (repr M uf b) ha hneq x h
    exact hi.trans (repr_canonical_calc M uf b)

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem sameclass_union_1_proof :
    ∀ (M : MAP), sameclass_union_1Statement M := by
  intro M uf a b
  change repr M (union M uf a b) a = repr M (union M uf a b) b
  have ha := repr_union_2_proof M uf a b a rfl
  have hb := repr_union_3_proof M uf a b
  exact ha.trans hb.symm

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem sameclass_union_2_proof :
    ∀ (M : MAP), sameclass_union_2Statement M := by
  intro M uf a b x y hxy
  change repr M (union M uf a b) x = repr M (union M uf a b) y
  change repr M uf x = repr M uf y at hxy
  by_cases hx : repr M uf x = repr M uf a
  · by_cases hy : repr M uf y = repr M uf a
    · have hux := repr_union_2_proof M uf a b x hx
      have huy := repr_union_2_proof M uf a b y hy
      exact hux.trans huy.symm
    · exfalso
      apply hy
      exact hxy.symm.trans hx
  · by_cases hy : repr M uf y = repr M uf a
    · exfalso
      apply hx
      exact hxy.trans hy
    · have hux := repr_union_1_proof M uf a b x hx
      have huy := repr_union_1_proof M uf a b y hy
      exact hux.trans (hxy.trans huy.symm)

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem sameclass_union_3_proof :
    ∀ (M : MAP), sameclass_union_3Statement M := by
  intro M uf a b x y hxy
  change repr M (union M uf a b) x = repr M (union M uf a b) y at hxy
  change repr M uf x = repr M uf y ∨
      (repr M uf x = repr M uf a ∧ repr M uf y = repr M uf b) ∨
      (repr M uf x = repr M uf b ∧ repr M uf y = repr M uf a)
  by_cases hxa : repr M uf x = repr M uf a
  · by_cases hya : repr M uf y = repr M uf a
    · exact Or.inl (hxa.trans hya.symm)
    · right
      left
      constructor
      · exact hxa
      · have hxu := repr_union_2_proof M uf a b x hxa
        have hyu := repr_union_1_proof M uf a b y hya
        exact hyu.symm.trans (hxy.symm.trans hxu)
  · by_cases hya : repr M uf y = repr M uf a
    · right
      right
      constructor
      · have hxu := repr_union_1_proof M uf a b x hxa
        have hyu := repr_union_2_proof M uf a b y hya
        exact hxu.symm.trans (hxy.trans hyu)
      · exact hya
    · left
      have hxu := repr_union_1_proof M uf a b x hxa
      have hyu := repr_union_1_proof M uf a b y hya
      exact hxu.symm.trans (hxy.trans hyu)

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem path_ord_wellfounded_proof :
    ∀ (M : MAP), path_ord_wellfoundedStatement M := by
  intro M uf
  exact uf.mwf

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem repr_merge_proof :
    ∀ (M : MAP), repr_mergeStatement M := by
  intro M uf a b x
  unfold merge union
  dsimp
  by_cases hab : repr M uf a = repr M uf b
  · simp [hab]
  · simp only [dif_neg hab]
    have hba : repr M uf b ≠ repr M uf a := by
      intro h
      exact hab h.symm
    by_cases hxa : repr M uf x = repr M uf a
    · have hmerge := repr_identify_2_proof M uf (repr M uf a) b
        (repr_res_none_calc M uf a) hba x hxa
      have hunion := repr_identify_2_proof M uf (repr M uf a) (repr M uf b)
        (repr_res_none_calc M uf a)
        (by
          intro h
          apply hab
          calc
            repr M uf a = repr M uf (repr M uf b) := h.symm
            _ = repr M uf b := repr_canonical_calc M uf b)
        x hxa
      calc
        repr M (identify M uf (repr M uf a) b _ _) x = repr M uf b := hmerge
        _ = repr M uf (repr M uf b) := (repr_canonical_calc M uf b).symm
        _ = repr M (identify M uf (repr M uf a) (repr M uf b) _ _) x := hunion.symm
    · have hmerge := repr_identify_1_proof M uf (repr M uf a) b
        (repr_res_none_calc M uf a) hba x hxa
      have hunion := repr_identify_1_proof M uf (repr M uf a) (repr M uf b)
        (repr_res_none_calc M uf a)
        (by
          intro h
          apply hab
          calc
            repr M uf a = repr M uf (repr M uf b) := h.symm
            _ = repr M uf b := repr_canonical_calc M uf b)
        x hxa
      exact hmerge.trans hunion.symm

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem sameclass_merge_proof :
    ∀ (M : MAP), sameclass_mergeStatement M := by
  intro M uf a b x y
  change repr M (merge M uf a b) x = repr M (merge M uf a b) y ↔
    repr M (union M uf a b) x = repr M (union M uf a b) y
  rw [repr_merge_proof M uf a b x, repr_merge_proof M uf a b y]

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem path_ord_canonical_proof :
    ∀ (M : MAP), path_ord_canonicalStatement M := by
  intro M uf x y hrepr hpath
  change mapGet M x uf.m = some y at hpath
  have hnone := repr_res_none_calc M uf x
  rw [hrepr] at hnone
  rw [hnone] at hpath
  cases hpath

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem path_ord_merge_1_proof :
    ∀ (M : MAP), path_ord_merge_1Statement M := by
  intro M uf a b x y hpath
  change mapGet M y uf.m = some x at hpath
  unfold merge
  dsimp
  by_cases hab : repr M uf a = repr M uf b
  · simp only [dif_pos hab]
    change mapGet M y uf.m = some x
    exact hpath
  · simp only [dif_neg hab]
    change mapGet M y (mapSet M (repr M uf a) b uf.m) = some x
    rw [mapGet_set]
    by_cases hya : y = repr M uf a
    · subst y
      have hnone := repr_res_none_calc M uf a
      rw [hpath] at hnone
      cases hnone
    · simp [hya, hpath]

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem path_ord_merge_2_proof :
    ∀ (M : MAP), path_ord_merge_2Statement M := by
  intro M uf a b hneq
  change mapGet M (repr M uf a) (merge M uf a b).m = some b
  unfold merge
  dsimp
  by_cases hab : repr M uf a = repr M uf b
  · exact False.elim (hneq hab)
  · simp only [dif_neg hab]
    change mapGet M (repr M uf a)
      (mapSet M (repr M uf a) b uf.m) = some b
    rw [mapGet_set]
    simp

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem pathlen_unroll_proof :
    ∀ (M : MAP), pathlen_unrollStatement M := by
  intro M uf a
  unfold pathlen
  rw [WellFounded.fix_eq]
  cases h : getlink M uf.m a with
  | inleft h' =>
      cases h' with
      | mk a' ha =>
          simp [F_pathlen, h, ha]
  | inright hnone =>
      simp [F_pathlen, h, hnone]

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem pathlen_none_proof :
    ∀ (M : MAP), pathlen_noneStatement M := by
  intro M uf a hnone
  rw [pathlen_unroll_proof M uf a]
  simp [hnone]

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem pathlen_some_proof :
    ∀ (M : MAP), pathlen_someStatement M := by
  intro M uf a a' hsome
  rw [pathlen_unroll_proof M uf a]
  simp [hsome]

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem pathlen_zero_proof :
    ∀ (M : MAP), pathlen_zeroStatement M := by
  intro M uf a
  constructor
  · intro hrepr
    apply pathlen_none_proof M uf a
    have hnone := repr_res_none_calc M uf a
    rw [hrepr] at hnone
    exact hnone
  · intro hzero
    rw [pathlen_unroll_proof M uf a] at hzero
    cases h : mapGet M a uf.m with
    | none => exact repr_none_calc M uf a h
    | some a' => simp [h] at hzero

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem pathlen_merge_proof :
    ∀ (M : MAP), pathlen_mergeStatement M := by
  intro M uf a b x
  unfold merge
  dsimp
  by_cases hab : repr M uf a = repr M uf b
  · simp only [dif_pos hab]
    cases hEq : M.elt_eq (repr M uf a) (repr M uf b) with
    | left h => simp [h]
    | right h => exact False.elim (h hab)
  · simp only [dif_neg hab]
    cases hEq : M.elt_eq (repr M uf a) (repr M uf b) with
    | left h => exact False.elim (hab h)
    | right h =>
      simp only [hEq]
      let uf' : t M := identify M uf (repr M uf a) b
        (repr_res_none_calc M uf a)
        (by
          intro hba
          exact hab (by simpa using hba.symm))
      change pathlen M uf' x = _
      apply uf'.mwf.induction x
      intro x0 ih
      rw [pathlen_unroll_proof M uf' x0]
      cases hget : mapGet M x0 uf'.m with
      | some x' =>
          change Nat.succ (pathlen M uf' x') = _
          rw [ih x' hget]
          change mapGet M x0 (mapSet M (repr M uf a) b uf.m) = some x' at hget
          rw [mapGet_set] at hget
          by_cases hxa : x0 = repr M uf a
          · subst x0
            simp only [dif_pos rfl] at hget
            cases hget
            have hcanon := repr_canonical_calc M uf a
            have hba : repr M uf b ≠ repr M uf a := by
              intro hba
              exact hab hba.symm
            cases e : M.elt_eq (repr M uf b) (repr M uf a) with
            | left heq => exact False.elim (hba heq)
            | right hneq =>
                cases e' : M.elt_eq (repr M uf (repr M uf a)) (repr M uf a) with
                | left heq' =>
                    have hzero : pathlen M uf (repr M uf a) = 0 :=
                      (pathlen_zero_proof M uf (repr M uf a)).mp heq'
                    simp only [e, e']
                    omega
                | right hneq' => exact False.elim (hneq' hcanon)
          · have hget' : mapGet M x0 uf.m = some x' := by
              simpa [hxa] using hget
            have hreprx : repr M uf x0 = repr M uf x' :=
              repr_some_calc M uf x0 x' hget'
            rw [pathlen_unroll_proof M uf x0, hget']
            simp only [hreprx]
            cases e : M.elt_eq (repr M uf x') (repr M uf a) with
            | left heq =>
                cases e0 : M.elt_eq (repr M uf x0) (repr M uf a) with
                | left heq0 =>
                    simp only [e, e0]
                    omega
                | right hneq0 =>
                    exact False.elim (hneq0 (hreprx.trans heq))
            | right hneq =>
                cases e0 : M.elt_eq (repr M uf x0) (repr M uf a) with
                | left heq0 =>
                    exact False.elim (hneq (hreprx.symm.trans heq0))
                | right hneq0 =>
                    simp only [e, e0]
      | none =>
          change 0 = _
          change mapGet M x0 (mapSet M (repr M uf a) b uf.m) = none at hget
          rw [mapGet_set] at hget
          by_cases hxa : x0 = repr M uf a
          · subst x0
            simp at hget
          · have hnone : mapGet M x0 uf.m = none := by
              simpa [hxa] using hget
            have hreprx : repr M uf x0 = x0 := repr_none_calc M uf x0 hnone
            have hzero : pathlen M uf x0 = 0 :=
              (pathlen_zero_proof M uf x0).mp hreprx
            cases hxeq : M.elt_eq (repr M uf x0) (repr M uf a) with
            | left heq => exact False.elim (hxa (hreprx.symm.trans heq))
            | right heq => simp [hzero]

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem compress_order_proof :
    ∀ (M : MAP), compress_orderStatement M := by
  intro M uf a b x y hxy
  change mapGet M x (mapSet M a b uf.m) = some y at hxy
  rw [mapGet_set] at hxy
  by_cases hxa : x = a
  · subst x
    simp at hxy
    exact Or.inr ⟨rfl, by simpa using hxy.symm⟩
  · simp only [dif_neg hxa] at hxy
    exact Or.inl hxy

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem compress_Acc_proof :
    ∀ (M : MAP), compress_AccStatement M := by
  intro M uf a b a_diff_b a_repr_b x _hx
  exact compress_Acc_calc M uf a b x a_diff_b a_repr_b

theorem compress_wf_proof :
    ∀ (M : MAP), compress_wfStatement M := by
  intro M uf a b a_diff_b a_repr_b
  exact compress_wf_calc M uf a b a_diff_b a_repr_b

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem pathlen_gt_merge_proof :
    ∀ (M : MAP), pathlen_gt_mergeStatement M := by
  intro M uf a b x y hrepr hgt
  simp only [pathlen_merge_proof M uf a b x, pathlen_merge_proof M uf a b y]
  cases hEq : M.elt_eq (repr M uf a) (repr M uf b) with
  | left _ => exact hgt
  | right _ =>
      simp only [hEq]
      cases hEqx : M.elt_eq (repr M uf x) (repr M uf a) with
      | left hx =>
          cases hEqy : M.elt_eq (repr M uf y) (repr M uf a) with
          | left hy =>
              simp only [hEqx, hEqy]
              omega
          | right hy =>
              exact False.elim (hy (hrepr ▸ hx))
      | right hx =>
          cases hEqy : M.elt_eq (repr M uf y) (repr M uf a) with
          | left hy =>
              exact False.elim (hx (hrepr.symm ▸ hy))
          | right hy =>
              simp only [hEqx, hEqy]
              exact hgt

end UF
end CompCert4Lean.Lib.UnionFind

namespace CompCert4Lean.Lib.UnionFind
namespace UF

theorem find_x_obligation_5 :
    ∀ (M : MAP), find_x_obligation_5Statement M := by
  intro M uf a
  dsimp
  intro h
  exact ⟨(repr_none_calc M uf a h.symm).symm, fun _ => rfl⟩

theorem find_x_obligation_6 :
    ∀ (M : MAP), find_x_obligation_6Statement M := by
  intro M uf
  exact (uf.mwf :
    CompCert4Lean.Foundation.Recursion.Rocq.Coq.Init.Wf.well_founded
      (order M uf.m))

theorem repr_compress_proof :
    ∀ (M : MAP), repr_compressStatement M := by
  intro M uf a b h1 h2 x
  exact repr_compress_calc M uf a b h1 h2 x

theorem find_x_obligation_4 :
    ∀ (M : MAP), find_x_obligation_4Statement M := by
  intro M uf a find_x find_x_obligation_1 find_x_obligation_2 find_x_obligation_3
  dsimp
  intro a' h₀ b uf' h
  let r := find_x a' (find_x_obligation_1 uf a a' h₀)
  change (b, uf') = r.1 at h
  have hrrepr : r.1.1 = repr M uf a' := r.2.1
  have hrunchanged : ∀ x, repr M r.1.2 x = repr M uf x := r.2.2
  have hb : b = r.1.1 := by simpa using congrArg Prod.fst h
  have huf : uf' = r.1.2 := by simpa using congrArg Prod.snd h
  have hne := find_x_obligation_2 uf a find_x find_x_obligation_1 a' h₀ b uf' h
  have hrepr := find_x_obligation_3 uf a find_x find_x_obligation_1 a' h₀ b uf' h
  have hrepr' : repr M uf' a = b := hrepr
  have hfirst : b = repr M uf a := by
    calc
      b = repr M uf' a := hrepr'.symm
      _ = repr M r.1.2 a := congrArg (fun q => repr M q a) huf
      _ = repr M uf a := hrunchanged a
  constructor
  · exact hfirst
  · intro x
    have hu : repr M uf' x = repr M r.1.2 x :=
      congrArg (fun q => repr M q x) huf
    exact (repr_compress_calc M uf' a b hne hrepr' x).trans
      (hu.trans (hrunchanged x))

end UF
end CompCert4Lean.Lib.UnionFind
