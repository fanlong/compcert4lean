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

private inductive LocallySorted (R : positive → positive → Prop) :
    List positive → Prop where
  | nil : LocallySorted R []
  | singleton (a : positive) : LocallySorted R [a]
  | cons (a b : positive) (l : List positive) :
      LocallySorted R (b :: l) → R a b → LocallySorted R (a :: b :: l)

private inductive HeadRel (R : positive → positive → Prop) (a : positive) :
    List positive → Prop where
  | nil : HeadRel R a []
  | cons (b : positive) (l : List positive) : R a b → HeadRel R a (b :: l)

private inductive Sorted (R : positive → positive → Prop) :
    List positive → Prop where
  | nil : Sorted R []
  | cons (a : positive) (l : List positive) :
      Sorted R l → HeadRel R a l → Sorted R (a :: l)

private inductive StronglySorted (R : positive → positive → Prop) :
    List positive → Prop where
  | nil : StronglySorted R []
  | cons (a : positive) (l : List positive) :
      StronglySorted R l → (∀ b ∈ l, R a b) → StronglySorted R (a :: l)

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

private theorem ptreeCard_remove_lt {A : Type} (p : positive)
    (m : PTree.tree A) (v : A) (h : PTree.get p m = some v) :
    ptreeCard (PTree.remove p m) < ptreeCard m := by
  cases m with
  | Empty => simp [PTree.get] at h
  | Nodes m =>
      simp only [PTree.remove, PTree.remove', PTree.get] at h ⊢
      induction p generalizing m with
      | xH =>
          cases m <;>
            simp_all [PTree.get', PTree.rem', ptreeCard, ptreeCard']
      | xO p ih =>
          cases m <;>
            simp_all [PTree.get', PTree.rem', ptreeCard, ptreeCard']
          all_goals
            change ptreeCard (PTree.Node _ _ _) < _
            rw [ptreeCard_Node]
            simp only [ptreeCard, optionCard]
            have hlt := ih _ h
            omega
      | xI p ih =>
          cases m <;>
            simp_all [PTree.get', PTree.rem', ptreeCard, ptreeCard']
          all_goals
            change ptreeCard (PTree.Node _ _ _) < _
            rw [ptreeCard_Node]
            simp only [ptreeCard, optionCard]
            have hlt := ih _ h
            omega

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
          | left hlt => exact ihN _ hlt _
          | right hlt => exact ihM _ hlt

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
          apply lex_ord.right
          simp [size_worklist]
      | cons y succsX =>
          cases hget : PTree.get y gr with
          | none =>
              simp [transition, hget] at hstep
              subst s'
              apply lex_ord.right
              change succsX.length + 1 + size_worklist rest <
                (succsX.length + 1) + 1 + size_worklist rest
              omega
          | some succsY =>
              simp [transition, hget] at hstep
              subst s'
              exact lex_ord.left (graphCardinal_remove y gr succsY hget)

def postorder (g : graph) (root : node) : PTree.t positive :=
  CompCert4Lean.Lib.Iteration.WfIter.iterate
    transition lt_state lt_state_wf transition_decreases (init_state g root)

inductive reachable (g : graph) (root : positive) : positive → Prop where
  | reachable_root : reachable g root root
  | reachable_succ (x : positive) (succs : List positive) (y : positive) :
      reachable g root x → PTree.get x g = some succs → List.Mem y succs →
        reachable g root y

export reachable (reachable_root reachable_succ)

end CompCert4Lean.Lib.Postorder
