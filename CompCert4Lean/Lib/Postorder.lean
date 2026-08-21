import CompCert4Lean.Foundation.RocqStdlib
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

/-! The source sorting modules are excluded collateral.  The executable adapter
keeps their observable operation—a stable increasing sort of successor
lists—locally. -/

private def insertPos (x : positive) : List positive → List positive
  | [] => [x]
  | y :: ys =>
      match plt x y with
      | .left _ => x :: y :: ys
      | .right _ => y :: insertPos x ys

private def orderSuccessors : List positive → List positive
  | [] => []
  | x :: xs => insertPos x (orderSuccessors xs)

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
        wrk := [(root, orderSuccessors succs)]
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
              wrk := (y, orderSuccessors succsY) :: (x, succsX) :: l
              map := s.map
              next := s.next }

def size_worklist : List (positive × List positive) → Nat
  | [] => 0
  | (_, succs) :: w => succs.length + 1 + size_worklist w

private def graphCardinal {A : Type} (m : PTree.t A) : Nat :=
  (PTree.elements m).length

def lt_state (s1 s2 : state) : Prop :=
  lex_ord Nat.lt Nat.lt
    (graphCardinal s1.gr, size_worklist s1.wrk)
    (graphCardinal s2.gr, size_worklist s2.wrk)

/-! A checked, structural fuel runner gives the executable result while the
source well-foundedness and decrease obligations remain descriptors for the
later proof phase.  The fuel is one larger than the sum of every graph node's
out-degree plus one, which bounds every edge inspection and node finalization
performed by `transition`. -/

private def graphFuel : graph → Nat
  | g =>
      1 + (PTree.elements g).foldl
        (fun fuel entry => fuel + entry.2.length + 1) 0

private def iterateFuel (fuel : Nat) (s : state) : PTree.t positive :=
  match fuel with
  | 0 => s.map
  | fuel + 1 =>
      match transition s with
      | .inl m => m
      | .inr s' => iterateFuel fuel s'

def postorder (g : graph) (root : node) : PTree.t positive :=
  iterateFuel (graphFuel g) (init_state g root)

private def edge (g : graph) (x y : positive) : Prop :=
  ∃ succs, PTree.get x g = some succs ∧ List.Mem y succs

def reachable (g : graph) (root x : positive) : Prop :=
  x = root ∨ Relation.TransGen (edge g) root x

/-! Exact statement descriptors for the proof declarations assigned to the
later proof-migration phase. -/

def lt_state_wfStatement : Prop :=
  WellFounded lt_state

def transition_decreasesStatement : Prop :=
  ∀ s s', transition s = Sum.inr s' → lt_state s' s

end CompCert4Lean.Lib.Postorder
