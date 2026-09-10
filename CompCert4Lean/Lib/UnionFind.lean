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
