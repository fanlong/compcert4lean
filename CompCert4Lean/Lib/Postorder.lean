import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.Ordered
import CompCert4Lean.Foundation.Recursion
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Iteration
import CompCert4Lean.Lib.Maps

/-!
# Postorder numbering of finite positive-keyed graphs

This module translates the executable surface of CompCert's
`lib/Postorder.v`.  The source proof declarations assigned to the later proof
phase are represented by exact proposition descriptors at the end of the
module; no theorem stubs are introduced here.
-/

namespace CompCert4Lean.Lib.Postorder

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Sorted
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

def node : Type := positive

def graph : Type := PTree.t (List node)

/-! ## Generated stable-sort application

`Sort` is the owned application of Rocq's `Mergesort.Sort(PositiveOrd)`.
The source order tests `x <= y` by deciding whether `y < x`; consequently the
left input wins on equal keys, preserving the source merge's stability.  The
application identity is the actual sort-function type, not a marker, and every
public member in the authenticated generated surface has a stable target name.
-/

namespace «Sort»

private def leb (x y : positive) : Bool :=
  match plt y x with
  | .left _ => false
  | .right _ => true

def merge (l1 l2 : List positive) : List positive :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | a1 :: l1', a2 :: l2' =>
      if leb a1 a2 then
        a1 :: merge l1' (a2 :: l2')
      else
        a2 :: merge (a1 :: l1') l2'
termination_by l1.length + l2.length

def merge_list_to_stack :
    List (Option (List positive)) → List positive →
      List (Option (List positive))
  | [], l => [some l]
  | none :: stack, l => some l :: stack
  | some l' :: stack, l =>
      none :: merge_list_to_stack stack (merge l' l)

def merge_stack : List (Option (List positive)) → List positive
  | [] => []
  | none :: stack => merge_stack stack
  | some l :: stack => merge l (merge_stack stack)

def iter_merge : List (Option (List positive)) → List positive → List positive
  | stack, [] => merge_stack stack
  | stack, a :: l => iter_merge (merge_list_to_stack stack [a]) l

def «Sort» : Type := List positive → List positive

def sort : «Sort» := iter_merge []

private def ordered (x y : positive) : Prop := leb x y = true

def SortedStack : List (Option (List positive)) → Prop
  | [] => True
  | none :: stack => SortedStack stack
  | some l :: stack => LocallySorted ordered l ∧ SortedStack stack

def flatten_stack : List (Option (List positive)) → List positive
  | [] => []
  | none :: stack => flatten_stack stack
  | some l :: stack => l ++ flatten_stack stack

def Sorted_merge : Prop :=
  ∀ l1 l2, LocallySorted ordered l1 → LocallySorted ordered l2 →
    LocallySorted ordered (merge l1 l2)

def Permuted_merge : Prop :=
  ∀ l1 l2,
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Permutation.Permutation
      (l1 ++ l2) (merge l1 l2)

def Sorted_merge_list_to_stack : Prop :=
  ∀ stack l, SortedStack stack → LocallySorted ordered l →
    SortedStack (merge_list_to_stack stack l)

def Permuted_merge_list_to_stack : Prop :=
  ∀ stack l,
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Permutation.Permutation
      (l ++ flatten_stack stack) (flatten_stack (merge_list_to_stack stack l))

def Sorted_merge_stack : Prop :=
  ∀ stack, SortedStack stack → LocallySorted ordered (merge_stack stack)

def Permuted_merge_stack : Prop :=
  ∀ stack,
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Permutation.Permutation
      (flatten_stack stack) (merge_stack stack)

def Sorted_iter_merge : Prop :=
  ∀ stack l, SortedStack stack → LocallySorted ordered (iter_merge stack l)

def Permuted_iter_merge : Prop :=
  ∀ l stack,
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Permutation.Permutation
      (flatten_stack stack ++ l) (iter_merge stack l)

def LocallySorted_sort : Prop :=
  ∀ l, LocallySorted ordered (sort l)

def Sorted_sort : Prop :=
  ∀ l, Sorted ordered (sort l)

def Permuted_sort : Prop :=
  ∀ l,
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Permutation.Permutation
      l (sort l)

def StronglySorted_sort : Prop :=
  ∀ l, (∀ x y z, ordered x y → ordered y z → ordered x z) →
    StronglySorted ordered (sort l)

end «Sort»

structure state where
  gr : graph
  wrk : List (node × List node)
  map : PTree.t positive
  next : positive

export state (gr wrk map next)

def init_state (g : graph) (root : node) : state :=
  match PTree.get root g with
  | some succs =>
      { gr := PTree.remove root g
        wrk := [(root, Sort.sort succs)]
        map := PTree.empty positive
        next := xH }
  | none =>
      { gr := g
        wrk := []
        map := PTree.empty positive
        next := xH }

def transition (s : state) : PTree.t positive ⊕ state :=
  match s.wrk with
  | [] =>
      .inl s.map
  | (x, []) :: l =>
      .inr
        { gr := s.gr
          wrk := l
          map := PTree.set x s.next s.map
          next := PArith.BinPos.Pos.succ s.next }
  | (x, y :: succsX) :: l =>
      match PTree.get y s.gr with
      | none =>
          .inr
            { gr := s.gr
              wrk := (x, succsX) :: l
              map := s.map
              next := s.next }
      | some succsY =>
          .inr
            { gr := PTree.remove y s.gr
              wrk := (y, Sort.sort succsY) :: (x, succsX) :: l
              map := s.map
              next := s.next }

def size_worklist : List (positive × List positive) → Nat
  | [] => 0
  | (_, succs) :: w => succs.length + 1 + size_worklist w

private def graphCardinal {A : Type} (m : PTree.t A) : Nat :=
  PTree_Properties.cardinal m

def lt_state (s1 s2 : state) : Prop :=
  lex_ord Nat.lt Nat.lt
    (graphCardinal s1.gr, size_worklist s1.wrk)
    (graphCardinal s2.gr, size_worklist s2.wrk)

/-! The following local cardinal lemmas discharge the exact transition
decrease required by the source iteration.  They inspect the translated
`PTree` representation directly and connect its structural number of stored
values to the canonical `PTree_Properties.cardinal` operation. -/

private def optionCard {A : Type} : Option A → Nat
  | none => 0
  | some _ => 1

private def ptreeCard' {A : Type} : PTree.tree' A → Nat
  | .Node001 r => ptreeCard' r
  | .Node010 _ => 1
  | .Node011 _ r => 1 + ptreeCard' r
  | .Node100 l => ptreeCard' l
  | .Node101 l r => ptreeCard' l + ptreeCard' r
  | .Node110 l _ => ptreeCard' l + 1
  | .Node111 l _ r => ptreeCard' l + 1 + ptreeCard' r

private def ptreeCard {A : Type} : PTree.tree A → Nat
  | .Empty => 0
  | .Nodes m => ptreeCard' m

private theorem ptreeCard_Node {A : Type} (l : PTree.tree A) (o : Option A)
    (r : PTree.tree A) :
    ptreeCard (PTree.Node l o r) =
      ptreeCard l + optionCard o + ptreeCard r := by
  cases l <;> cases o <;> cases r <;>
    simp [PTree.Node, ptreeCard, ptreeCard', optionCard]

private theorem ptreeCard_remove'_lt {A : Type} (p : positive)
    (m : PTree.tree' A) (v : A) (h : PTree.get' p m = some v) :
    ptreeCard (PTree.remove' p m) < ptreeCard' m := by
  induction p generalizing m with
  | xH =>
      cases m <;> simp_all [PTree.get', PTree.remove', ptreeCard, ptreeCard']
  | xO p ih =>
      cases m <;> simp_all [PTree.get', PTree.remove', ptreeCard, ptreeCard']
      all_goals
        have decrease := ih _ h
        cases hrem : PTree.remove' p _ <;>
          simp [PTree.remove', hrem, ptreeCard, ptreeCard'] at decrease ⊢ <;> omega
  | xI p ih =>
      cases m <;> simp_all [PTree.get', PTree.remove', ptreeCard, ptreeCard']
      all_goals
        have decrease := ih _ h
        cases hrem : PTree.remove' p _ <;>
          simp [PTree.remove', hrem, ptreeCard, ptreeCard'] at decrease ⊢ <;> omega

private theorem ptreeCard_remove_lt {A : Type} (p : positive)
    (m : PTree.tree A) (v : A) (h : PTree.get p m = some v) :
    ptreeCard (PTree.remove p m) < ptreeCard m := by
  cases m with
  | Empty => simp [PTree.get] at h
  | Nodes m =>
      exact ptreeCard_remove'_lt p m v (by simpa [PTree.get] using h)

private theorem ptreeCard_xelements' {A : Type} (m : PTree.tree' A)
    (i : positive) (k : List (positive × A)) :
    (PTree.xelements' m i k).length = ptreeCard' m + k.length := by
  induction m generalizing i k <;>
    simp [PTree.xelements', ptreeCard', *] <;> omega

private theorem ptreeCard_elements {A : Type} (m : PTree.tree A) :
    (PTree.elements m).length = ptreeCard m := by
  cases m with
  | Empty => rfl
  | Nodes m =>
      simpa [PTree.elements, PTree.xelements, ptreeCard] using
        ptreeCard_xelements' m xH []

private theorem graphCardinal_remove {A : Type} (p : positive)
    (m : PTree.tree A) (v : A) (h : PTree.get p m = some v) :
    graphCardinal (PTree.remove p m) < graphCardinal m := by
  calc
    graphCardinal (PTree.remove p m) = ptreeCard (PTree.remove p m) :=
      ptreeCard_elements _
    _ < ptreeCard m := ptreeCard_remove_lt p m v h
    _ = graphCardinal m := (ptreeCard_elements m).symm

private theorem lexNat_wf : WellFounded (lex_ord Nat.lt Nat.lt) := by
  constructor
  intro p
  rcases p with ⟨n, m⟩
  induction n using Nat.strongRecOn generalizing m with
  | _ n ihN =>
      induction m using Nat.strongRecOn with
      | _ m ihM =>
          constructor
          intro q hq
          cases hq with
          | left _ _ _ _ hlt => exact ihN _ hlt _
          | right _ _ _ hlt => exact ihM _ hlt

def lt_state_wfStatement : Prop :=
  WellFounded lt_state

theorem lt_state_wf : lt_state_wfStatement := by
  exact InvImage.wf
    (fun s : state => (graphCardinal s.gr, size_worklist s.wrk))
    lexNat_wf

def transition_decreasesStatement : Prop :=
  ∀ s s', transition s = Sum.inr s' → lt_state s' s

theorem transition_decreases : transition_decreasesStatement := by
  intro s s' hstep
  rcases s with ⟨gr, wrk, map, next⟩
  cases wrk with
  | nil => simp [transition] at hstep
  | cons work rest =>
      rcases work with ⟨x, succs⟩
      cases succs with
      | nil =>
          simp [transition] at hstep
          subst s'
          apply lex_ord.right Nat.lt Nat.lt (graphCardinal gr)
            (size_worklist rest) (size_worklist ((x, []) :: rest))
          simp [size_worklist]
      | cons y succsX =>
          cases hget : PTree.get y gr with
          | none =>
              simp [transition, hget] at hstep
              subst s'
              apply lex_ord.right Nat.lt Nat.lt (graphCardinal gr)
                (size_worklist ((x, succsX) :: rest))
                (size_worklist ((x, y :: succsX) :: rest))
              change succsX.length + 1 + size_worklist rest <
                (succsX.length + 1) + 1 + size_worklist rest
              omega
          | some succsY =>
              simp [transition, hget] at hstep
              subst s'
              exact lex_ord.left Nat.lt Nat.lt
                (graphCardinal (PTree.remove y gr))
                (size_worklist
                  ((y, Sort.sort succsY) :: (x, succsX) :: rest))
                (graphCardinal gr)
                (size_worklist ((x, y :: succsX) :: rest))
                (graphCardinal_remove y gr succsY hget)

def postorder (g : graph) (root : node) : PTree.t positive :=
  CompCert4Lean.Lib.Iteration.WfIter.iterate
    state (PTree.t positive) transition lt_state lt_state_wf
      transition_decreases (init_state g root)

inductive reachable (g : graph) (root : positive) : positive → Prop where
  | reachable_root : reachable g root root
  | reachable_succ (x : positive) (succs : List positive) (y : positive) :
      reachable g root x → PTree.get x g = some succs → List.Mem y succs →
        reachable g root y

export reachable (reachable_root reachable_succ)

def postorder_correctStatement : Prop :=
  ∀ (g : graph) (root : node),
    let m := postorder g root
    (∀ (x₁ x₂ y : positive),
      PTree.get x₁ m = some y → PTree.get x₂ m = some y → x₁ = x₂) ∧
    (∀ x : positive,
      reachable g root x → PTree.get x g ≠ none → PTree.get x m ≠ none)

end CompCert4Lean.Lib.Postorder

namespace CompCert4Lean.Lib.Postorder

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem sort_merge_mem (x : positive) (l1 l2 : List positive) :
    x ∈ «Sort».merge l1 l2 ↔ x ∈ l1 ∨ x ∈ l2 := by
  induction hlen : l1.length + l2.length using Nat.strongRecOn generalizing l1 l2 with
  | _ n ih =>
      cases l1 with
      | nil => simp [«Sort».merge]
      | cons a l1 =>
          cases l2 with
          | nil => simp [«Sort».merge]
          | cons b l2 =>
              simp only [«Sort».merge]
              split <;>
                simp only [List.mem_cons]
              · have hrec := ih (l1.length + (b :: l2).length) (by simp_all; omega)
                simp only [hrec]
                simp [or_assoc, or_left_comm, or_comm]
              · have hrec := ih ((a :: l1).length + l2.length) (by simp_all; omega)
                simp only [hrec]
                simp [or_assoc, or_left_comm, or_comm]

private theorem sort_merge_list_to_stack_mem (x : positive)
    (stack : List (Option (List positive))) (l : List positive) :
    x ∈ «Sort».flatten_stack («Sort».merge_list_to_stack stack l) ↔
      x ∈ l ∨ x ∈ «Sort».flatten_stack stack := by
  induction stack generalizing l with
  | nil => simp [«Sort».merge_list_to_stack, «Sort».flatten_stack]
  | cons h stack ih =>
      cases h with
      | none =>
          simp [«Sort».merge_list_to_stack, «Sort».flatten_stack,
            or_assoc, or_left_comm, or_comm]
      | some l' =>
          simp only [«Sort».merge_list_to_stack, «Sort».flatten_stack,
            List.mem_append, List.mem_cons]
          have hm := sort_merge_mem x l' l
          have hi := ih («Sort».merge l' l)
          simp only [hm] at hi
          rw [hi]
          simp [hm, or_assoc, or_left_comm, or_comm]

private theorem sort_merge_stack_mem (x : positive)
    (stack : List (Option (List positive))) :
    x ∈ «Sort».merge_stack stack ↔ x ∈ «Sort».flatten_stack stack := by
  induction stack with
  | nil => simp [«Sort».merge_stack, «Sort».flatten_stack]
  | cons h stack ih =>
      cases h with
      | none => simpa [«Sort».merge_stack, «Sort».flatten_stack] using ih
      | some l =>
          simp only [«Sort».merge_stack, «Sort».flatten_stack, List.mem_append]
          rw [sort_merge_mem, ih]

private theorem sort_iter_merge_mem (x : positive)
    (stack : List (Option (List positive))) (l : List positive) :
    x ∈ «Sort».iter_merge stack l ↔
      x ∈ «Sort».flatten_stack stack ++ l := by
  induction hlen : l.length using Nat.strongRecOn generalizing stack l with
  | _ n ih =>
      cases l with
      | nil =>
          simpa [«Sort».iter_merge, List.mem_append] using sort_merge_stack_mem x stack
      | cons a l =>
          have hrec := ih l.length (by simp_all; omega)
            («Sort».merge_list_to_stack stack [a]) l (by rfl)
          have hstack := sort_merge_list_to_stack_mem x stack [a]
          simp only [«Sort».iter_merge, List.mem_append, List.mem_cons] at hrec hstack ⊢
          rw [hrec, hstack]
          simp [or_assoc, or_left_comm, or_comm]

private theorem sort_mem (x : positive) (l : List positive) :
    x ∈ «Sort».sort l ↔ x ∈ l := by
  simpa [«Sort».sort, «Sort».flatten_stack, or_assoc, or_left_comm, or_comm]
    using (sort_iter_merge_mem x [] l)

private structure Invariant (ginit : graph) (root : node) (s : state) : Prop where
  sub : ∀ x y, PTree.get x s.gr = some y → PTree.get x ginit = some y
  root : PTree.get root s.gr = none
  below : ∀ x y, PTree.get x s.map = some y → Plt y s.next
  inj : ∀ x₁ x₂ y, PTree.get x₁ s.map = some y → PTree.get x₂ s.map = some y → x₁ = x₂
  rem : ∀ x y, PTree.get x s.gr = some y → PTree.get x s.map = none
  color : ∀ x succs n y, PTree.get x ginit = some succs →
    PTree.get x s.map = some n → y ∈ succs → PTree.get y s.gr = none
  wklist : ∀ x l, (x, l) ∈ s.wrk →
    PTree.get x s.gr = none ∧
      ∃ l', PTree.get x ginit = some l' ∧ ∀ y, y ∈ l' → y ∉ l → PTree.get y s.gr = none
  grey : ∀ x, PTree.get x ginit ≠ none → PTree.get x s.gr = none →
    PTree.get x s.map = none → ∃ l, (x, l) ∈ s.wrk

private structure Postcondition (ginit : graph) (root : node) (m : PTree.t positive) : Prop where
  inj : ∀ x₁ x₂ y, PTree.get x₁ m = some y → PTree.get x₂ m = some y → x₁ = x₂
  root : PTree.get root ginit ≠ none → PTree.get root m ≠ none
  succs : ∀ x succs y, PTree.get x ginit = some succs → PTree.get x m ≠ none →
    y ∈ succs → PTree.get y ginit ≠ none → PTree.get y m ≠ none

private theorem initial_invariant (ginit : graph) (root : node) :
    Invariant ginit root (init_state ginit root) := by
  cases h : PTree.get root ginit with
  | none =>
      simp [init_state, h]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x y hx; exact hx
      · exact h
      · intro x y hx; simp [PTree.empty, PTree.get] at hx
      · intro x₁ x₂ y h₁ h₂; simp [PTree.empty, PTree.get] at h₁
      · intro x y hx; simp [PTree.empty, PTree.get]
      · intro x succs n y hx hm hy; simp [PTree.empty, PTree.get] at hm
      · intro x l hx; simp at hx
      · intro x hxg hxgr hxmap; exact (hxg hxgr).elim
  | some succs =>
      simp [init_state, h]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x y hx
        by_cases hxr : x = root
        · subst x
          rw [PTree.grs_proof root ginit] at hx
          cases hx
        · have hkeep : PTree.get x (PTree.remove root ginit) = PTree.get x ginit :=
            PTree.gro_proof (m := ginit) hxr
          rw [hkeep] at hx
          exact hx
      · exact PTree.grs_proof root ginit
      · intro x y hx; simp [PTree.empty, PTree.get] at hx
      · intro x₁ x₂ y h₁ h₂; simp [PTree.empty, PTree.get] at h₁
      · intro x y hx; simp [PTree.empty, PTree.get]
      · intro x succs' n y hx hm hy; simp [PTree.empty, PTree.get] at hm
      · intro x l hx
        simp at hx
        injection hx with hxr hl
        subst x; subst l
        exact ⟨PTree.grs_proof root ginit, by
          refine ⟨succs, h, ?_⟩
          intro y hy hn
          exact (hn ((sort_mem y succs).2 hy)).elim⟩
      · intro x hxg hxgr hxmap
        by_cases hxr : x = root
        · subst x
          exact ⟨Sort.sort succs, List.mem_cons.mpr (Or.inl rfl)⟩
        · have hxnone : PTree.get x ginit = none := by
            have hkeep : PTree.get x (PTree.remove root ginit) = PTree.get x ginit :=
              PTree.gro_proof (m := ginit) hxr
            rw [hkeep] at hxgr
            exact hxgr
          exact (hxg hxnone).elim

end CompCert4Lean.Lib.Postorder

namespace CompCert4Lean.Lib.Postorder

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem invariant_done (g : graph) (root : node)
    (gr : graph) (m : PTree.t positive) (n : positive)
    (h : Invariant g root ⟨gr, [], m, n⟩) : Postcondition g root m := by
  refine ⟨h.inj, ?_, ?_⟩
  · intro hg hm
    obtain ⟨l, hl⟩ := h.grey root hg h.root hm
    exact List.not_mem_nil hl
  · intro x succs y hx hm hy hyg hym
    cases hxm : PTree.get x m with
    | none => exact hm hxm
    | some v =>
        obtain ⟨l, hl⟩ := h.grey y hyg (h.color x succs v y hx hxm hy) hym
        exact List.not_mem_nil hl

private theorem invariant_number (g : graph) (root : node)
    (gr : graph) (m : PTree.t positive) (n : positive)
    (x : node) (l : List (node × List node))
    (h : Invariant g root ⟨gr, (x, []) :: l, m, n⟩) :
    Invariant g root ⟨gr, l, PTree.set x n m, PArith.BinPos.Pos.succ n⟩ := by
  change positive at x
  change PTree.tree positive at m
  have hw := h.wklist x [] (by simp)
  refine ⟨h.sub, h.root, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a v hv
    change PTree.get a (PTree.set x n m) = some v at hv
    rw [PTree.getSet_equation] at hv
    by_cases ha : a = x
    · simp [ha] at hv
      subst v
      exact Plt_succ n
    · simp [ha] at hv
      exact Plt_trans_succ _ _ (h.below a v hv)
  · intro a b v ha hb
    change PTree.get a (PTree.set x n m) = some v at ha
    change PTree.get b (PTree.set x n m) = some v at hb
    rw [PTree.getSet_equation] at ha hb
    by_cases hax : a = x <;> by_cases hbx : b = x
    · exact hax.trans hbx.symm
    · simp [hax] at ha
      simp [hbx] at hb
      subst v
      exact (Plt_strict n (h.below b n hb)).elim
    · simp [hax] at ha
      simp [hbx] at hb
      subst v
      exact (Plt_strict n (h.below a n ha)).elim
    · simp [hax] at ha
      simp [hbx] at hb
      exact h.inj a b v ha hb
  · intro a succs ha
    change PTree.get a (PTree.set x n m) = none
    have hax : a ≠ x := by
      intro heq
      subst a
      have hx := hw.1
      change PTree.get x gr = none at hx
      change PTree.get x gr = some succs at ha
      rw [hx] at ha
      cases ha
    simp [PTree.getSet_equation, hax]
    exact h.rem a succs ha
  · intro a succs v y ha hv hy
    change PTree.get a (PTree.set x n m) = some v at hv
    rw [PTree.getSet_equation] at hv
    by_cases hax : a = x
    · subst a
      obtain ⟨orig, horig, hs⟩ := hw.2
      have heq : orig = succs := Option.some.inj (horig.symm.trans ha)
      subst orig
      exact hs y hy (by simp)
    · simp [hax] at hv
      exact h.color a succs v y ha hv hy
  · intro a succs ha
    exact h.wklist a succs (List.mem_cons_of_mem _ ha)
  · intro a hag hagr ham
    change PTree.get a (PTree.set x n m) = none at ham
    rw [PTree.getSet_equation] at ham
    have hax : a ≠ x := by
      intro heq
      simp [heq] at ham
    simp [hax] at ham
    obtain ⟨succs, hs⟩ := h.grey a hag hagr ham
    rcases List.mem_cons.mp hs with heq | ht
    · have heq' : a = x := congrArg Prod.fst heq
      exact (hax heq').elim
    · exact ⟨succs, ht⟩

end CompCert4Lean.Lib.Postorder

namespace CompCert4Lean.Lib.Postorder

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem invariant_push (g : graph) (root : node)
    (gr : graph) (m : PTree.t positive) (n : positive)
    (x y : node) (succ_x succs_y : List node) (l : List (node × List node))
    (h : Invariant g root ⟨gr, (x, y :: succ_x) :: l, m, n⟩)
    (hget : PTree.get y gr = some succs_y) :
    Invariant g root
      ⟨PTree.remove y gr, (y, Sort.sort succs_y) :: (x, succ_x) :: l, m, n⟩ := by
  change positive at root x y
  change PTree.tree (List node) at gr
  change PTree.tree positive at m
  change List positive at succ_x succs_y
  change List (positive × List positive) at l
  have hxgr : PTree.get x gr = none := by simpa using h.wklist x (y :: succ_x) (List.mem_cons.mpr (Or.inl rfl)) |>.1
  have hroot : PTree.get root gr = none := by simpa using h.root
  have hyroot : y ≠ root := by
    intro hyr
    subst root
    rw [hroot] at hget
    cases hget
  refine ⟨?_, ?_, h.below, h.inj, ?_, ?_, ?_, ?_⟩
  · intro a v ha
    change positive at a
    change PTree.get a (PTree.remove y gr) = some v at ha
    rw [PTree.getRemove_equation] at ha
    by_cases hay : a = y
    · simp [hay] at ha
    · simp [hay] at ha
      exact h.sub a v ha
  · change PTree.get root (PTree.remove y gr) = none
    rw [PTree.getRemove_equation]
    simp [hyroot, hroot]
  · intro a succs ha
    change positive at a
    change PTree.get a (PTree.remove y gr) = some succs at ha
    change PTree.get a m = none
    rw [PTree.getRemove_equation] at ha
    by_cases hay : a = y
    · simp [hay] at ha
    · simp [hay] at ha
      exact h.rem a succs ha
  · intro a succs v z ha hv hz
    change positive at a z
    change PTree.get a g = some succs at ha
    change PTree.get a m = some v at hv
    change PTree.get z (PTree.remove y gr) = none
    rw [PTree.getRemove_equation]
    by_cases hzy : z = y
    · simp [hzy]
    · simp [hzy]
      simpa using h.color a succs v z ha hv hz
  · intro a succs ha
    change positive at a
    change PTree.get a (PTree.remove y gr) = none ∧
      ∃ (orig : List node), PTree.get a g = some orig ∧
        ∀ z, z ∈ orig → z ∉ succs → PTree.get z (PTree.remove y gr) = none
    change (a, succs) ∈ (y, Sort.sort succs_y) :: (x, succ_x) :: l at ha
    rcases List.mem_cons.mp ha with hEq | htail
    · cases hEq
      refine ⟨PTree.grs_proof y gr, ?_⟩
      refine ⟨succs_y, h.sub y succs_y hget, ?_⟩
      intro z hz hzs
      exact (hzs ((sort_mem z succs_y).2 hz)).elim
    · rcases List.mem_cons.mp htail with hEq | htail
      · cases hEq
        have hremove : PTree.get x (PTree.remove y gr) = none := by
          rw [PTree.getRemove_equation]
          have hxy : x ≠ y := by
            intro heq
            subst x
            rw [hget] at hxgr
            cases hxgr
          simp [hxy, hxgr]
        refine ⟨hremove, ?_⟩
        obtain ⟨orig, horig, hnot⟩ := h.wklist x (y :: succ_x) (List.mem_cons.mpr (Or.inl rfl)) |>.2
        refine ⟨orig, horig, ?_⟩
        intro z hz hzs
        change positive at z
        rw [PTree.getRemove_equation]
        by_cases hzy : z = y
        · simp [hzy]
        · simp [hzy]
          apply hnot z hz
          intro hzold
          rcases List.mem_cons.mp hzold with rfl | hzold
          · exact (hzy rfl).elim
          · exact hzs hzold
      · obtain ⟨agr, hagrwork⟩ := h.wklist a succs (List.mem_cons_of_mem _ htail)
        refine ⟨?_, ?_⟩
        · rw [PTree.getRemove_equation]
          by_cases hay : a = y
          · simp [hay] at agr
            rw [hget] at agr
            cases agr
          · simp [hay]
            simpa using agr
        · obtain ⟨orig, horig, hnot⟩ := h.wklist a succs (List.mem_cons_of_mem _ htail) |>.2
          refine ⟨orig, horig, ?_⟩
          intro z hz hzs
          change positive at z
          rw [PTree.getRemove_equation]
          by_cases hzy : z = y
          · simp [hzy]
          · simp [hzy]
            apply hnot z hz
            intro hzold
            exact hzs hzold
  · intro a hag hagr ham
    change positive at a
    change PTree.get a (PTree.remove y gr) = none at hagr
    change PTree.get a m = none at ham
    by_cases hay : a = y
    · subst a
      change ∃ (la : List positive), (y, la) ∈ (y, Sort.sort succs_y) :: (x, succ_x) :: l
      exact ⟨Sort.sort succs_y, by simp⟩
    · have hagr' : PTree.get a gr = none := by
        rw [PTree.getRemove_equation] at hagr
        simpa [hay] using hagr
      obtain ⟨la, hla⟩ := h.grey a hag hagr' ham
      change ∃ (la : List positive), (a, la) ∈ (y, Sort.sort succs_y) :: (x, succ_x) :: l
      rcases List.mem_cons.mp hla with hEq | htail
      · cases hEq
        exact ⟨succ_x, by simp⟩
      · exact ⟨la, List.mem_cons_of_mem (y, Sort.sort succs_y) (List.mem_cons_of_mem (x, succ_x) htail)⟩

end CompCert4Lean.Lib.Postorder

namespace CompCert4Lean.Lib.Postorder

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem invariant_skip (g : graph) (root : node)
    (gr : graph) (m : PTree.t positive) (n : positive)
    (x y : node) (succ_x : List node) (l : List (node × List node))
    (h : Invariant g root ⟨gr, (x, y :: succ_x) :: l, m, n⟩)
    (hget : PTree.get y gr = none) :
    Invariant g root ⟨gr, (x, succ_x) :: l, m, n⟩ := by
  change positive at root x y
  change PTree.tree (List node) at gr
  change PTree.tree positive at m
  change List positive at succ_x
  change List (positive × List positive) at l
  have hwork := h.wklist x (y :: succ_x) (List.mem_cons.mpr (Or.inl rfl))
  refine ⟨h.sub, h.root, h.below, h.inj, h.rem, h.color, ?_, ?_⟩
  · intro a succs ha
    change positive at a
    change (a, succs) ∈ (x, succ_x) :: l at ha
    rcases List.mem_cons.mp ha with hhead | htail
    · cases hhead
      refine ⟨hwork.1, ?_⟩
      obtain ⟨orig, horig, hnot⟩ := hwork.2
      refine ⟨orig, horig, ?_⟩
      intro z hz hzs
      by_cases hzy : z = y
      · subst z
        exact hget
      · apply hnot z hz
        intro hzold
        rcases List.mem_cons.mp hzold with rfl | hzold
        · exact (hzy rfl).elim
        · exact hzs hzold
    · obtain ⟨agr, hagr⟩ := h.wklist a succs (List.mem_cons_of_mem (x, y :: succ_x) htail)
      refine ⟨agr, ?_⟩
      obtain ⟨orig, horig, hnot⟩ := hagr
      refine ⟨orig, horig, ?_⟩
      intro z hz hzs
      by_cases hzy : z = y
      · subst z
        exact hget
      · apply hnot z hz
        intro hzold
        exact hzs hzold
  · intro a hag hagr ham
    change positive at a
    change PTree.get a gr = none at hagr
    change PTree.get a m = none at ham
    obtain ⟨la, hla⟩ := h.grey a hag hagr ham
    rcases List.mem_cons.mp hla with hEq | htail
    · have heq : a = x := congrArg Prod.fst hEq
      have hlaeq : la = y :: succ_x := congrArg Prod.snd hEq
      subst a
      subst la
      exact ⟨succ_x, List.mem_cons.mpr (Or.inl rfl)⟩
    · exact ⟨la, List.mem_cons_of_mem _ htail⟩


private theorem transition_spec_local (g : graph) (root : node) (s : state)
    (h : Invariant g root s) :
    match transition s with
    | Sum.inr s' => Invariant g root s'
    | Sum.inl m => Postcondition g root m := by
  cases s with
  | mk gr wrk m n =>
      cases wrk with
      | nil =>
          exact invariant_done g root gr m n h
      | cons work rest =>
          rcases work with ⟨x, succs⟩
          cases succs with
          | nil =>
              simp [transition]
              exact invariant_number g root gr m n x rest h
          | cons y succ_x =>
              cases hget : PTree.get y gr with
              | none =>
                  simp [transition, hget]
                  exact invariant_skip g root gr m n x y succ_x rest h hget
              | some succs_y =>
                  simp [transition, hget]
                  exact invariant_push g root gr m n x y succ_x succs_y rest h hget

private theorem transition_spec_iter (g : graph) (root : node) :
    ∀ (s : state), Invariant g root s →
    match transition s with
    | Sum.inl m => Postcondition g root m
    | Sum.inr s' => Invariant g root s' := by
  intro s hs
  cases htrans : transition s with
  | inl m =>
      have hh := transition_spec_local g root s hs
      rw [htrans] at hh
      exact hh
  | inr s' =>
      have hh := transition_spec_local g root s hs
      rw [htrans] at hh
      exact hh

theorem postorder_correct : postorder_correctStatement := by
  intro g root
  let m := postorder g root
  have hp : Postcondition g root m := by
    unfold m postorder
    apply CompCert4Lean.Lib.Iteration.WfIter.iterate_prop
      state (PTree.t positive) transition lt_state lt_state_wf
      transition_decreases
      (Invariant g root)
      (Postcondition g root)
    · intro a ha
      cases htrans : transition a with
      | inl b =>
          have hh := transition_spec_local g root a ha
          rw [htrans] at hh
          exact hh
      | inr a' =>
          have hh := transition_spec_local g root a ha
          rw [htrans] at hh
          exact hh
    · exact initial_invariant g root
  refine ⟨hp.inj, ?_⟩
  intro x hr hg
  induction hr with
  | reachable_root => exact hp.root hg
  | @reachable_succ x succs y hr hxs hy ih =>
      exact hp.succs x succs y hxs (ih (by
        intro hm
        exact hg (by simpa [hxs] using hm)) ) hy hg

end CompCert4Lean.Lib.Postorder
