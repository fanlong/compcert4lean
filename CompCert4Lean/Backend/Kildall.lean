import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.Recursion
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Heaps
import CompCert4Lean.Lib.Iteration
import CompCert4Lean.Lib.Lattice
import CompCert4Lean.Lib.Maps

/-!
# Kildall dataflow solvers

This module is the checked definition-translation surface for
backend/Kildall.v. Executable declarations are translated directly using
the source-shaped map, heap, and iteration providers. Proof declarations that
belong to the later proof-migration phase are retained as exact statement
descriptors; no theorem stub or unchecked project assumption is introduced.
-/

namespace CompCert4Lean.Backend.Kildall

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Heaps
open CompCert4Lean.Lib.Iteration
open CompCert4Lean.Lib.Maps

abbrev PTreeT (A : Type) := CompCert4Lean.Lib.Maps.PTree.t A
abbrev PMapT (A : Type) := CompCert4Lean.Lib.Maps.PMap.t A

structure SemiLattice where
  t : Type
  bot : t
  lub : t → t → t
  beq : t → t → Bool
  eq : t → t → Prop
  ge : t → t → Prop

structure SemiLatticeLaws (L : SemiLattice) : Prop where
  eq_refl : ∀ x, L.eq x x
  eq_sym : ∀ x y, L.eq x y → L.eq y x
  eq_trans : ∀ x y z, L.eq x y → L.eq y z → L.eq x z
  beq_correct : ∀ x y, L.beq x y = true → L.eq x y
  ge_refl : ∀ x y, L.eq x y → L.ge x y
  ge_trans : ∀ x y z, L.ge x y → L.ge y z → L.ge x z
  ge_bot : ∀ x, L.ge x L.bot
  ge_lub_left : ∀ x y, L.ge (L.lub x y) x
  ge_lub_right : ∀ x y, L.ge (L.lub x y) y

structure NodeSetOps where
  t : Type
  empty : t
  add : positive → t → t
  pick : t → Option (positive × t)
  all_nodes : {A : Type} → PTreeT A → t
  In : positive → t → Prop

structure NodeSetLaws (NS : NodeSetOps) : Prop where
  empty_spec : ∀ n, ¬ NS.In n NS.empty
  add_spec : ∀ n n' s, NS.In n' (NS.add n s) ↔ n = n' ∨ NS.In n' s
  pick_none : ∀ s n, NS.pick s = none → ¬ NS.In n s
  pick_some : ∀ s n s', NS.pick s = some (n, s') →
    ∀ n', NS.In n' s ↔ n = n' ∨ NS.In n' s'
  all_nodes_spec : ∀ (A : Type) (code : PTreeT A) n instr,
    PTree.get n code = some instr → NS.In n (NS.all_nodes code)

structure OrderedTop where
  t : Type
  ge : t → t → Prop
  top : t

structure OrderedTopLaws (L : OrderedTop) : Prop where
  top_ge : ∀ x, L.ge L.top x
  refl_ge : ∀ x, L.ge x x

abbrev «DATAFLOW_SOLVER.L» := SemiLattice
abbrev «BACKWARD_DATAFLOW_SOLVER.L» := SemiLattice
abbrev «BBLOCK_SOLVER.L» := OrderedTop

structure DATAFLOW_SOLVER where
  L : SemiLattice
  L_laws : SemiLatticeLaws L
  fixpoint : {A : Type} → PTreeT A → (A → List positive) →
    (positive → L.t → L.t) → positive → L.t → Option (PMapT L.t)
  fixpoint_solution :
    ∀ (A : Type) (code : PTreeT A) successors transf ep ev res n instr s,
      fixpoint code successors transf ep ev = some res →
      PTree.get n code = some instr → s ∈ successors instr →
      (∀ n, L.eq (transf n L.bot) L.bot) →
      L.ge (PMap.get s res) (transf n (PMap.get n res))
  fixpoint_entry :
    ∀ (A : Type) (code : PTreeT A) successors transf ep ev res,
      fixpoint code successors transf ep ev = some res →
      L.ge (PMap.get ep res) ev
  fixpoint_invariant :
    ∀ (A : Type) (code : PTreeT A) successors transf ep ev
      (P : L.t → Prop), P L.bot →
      (∀ x y, P x → P y → P (L.lub x y)) →
      (∀ pc instr x, PTree.get pc code = some instr → P x → P (transf pc x)) →
      P ev → ∀ res pc, fixpoint code successors transf ep ev = some res →
      P (PMap.get pc res)

structure NODE_SET where
  t : Type
  empty : t
  add : positive → t → t
  pick : t → Option (positive × t)
  all_nodes : {A : Type} → PTreeT A → t
  In : positive → t → Prop
  empty_spec : ∀ n, ¬ In n empty
  add_spec : ∀ n n' s, In n' (add n s) ↔ n = n' ∨ In n' s
  pick_none : ∀ s n, pick s = none → ¬ In n s
  pick_some : ∀ s n s', pick s = some (n, s') →
    ∀ n', In n' s ↔ n = n' ∨ In n' s'
  all_nodes_spec : ∀ (A : Type) (code : PTreeT A) n instr,
    PTree.get n code = some instr → In n (all_nodes code)

structure BACKWARD_DATAFLOW_SOLVER where
  L : SemiLattice
  L_laws : SemiLatticeLaws L
  fixpoint : {A : Type} → PTreeT A → (A → List positive) →
    (positive → L.t → L.t) → Option (PMapT L.t)
  fixpoint_solution :
    ∀ (A : Type) (code : PTreeT A) successors transf res n instr s,
      fixpoint code successors transf = some res →
      PTree.get n code = some instr → s ∈ successors instr →
      (∀ n a, PTree.get n code = none → L.eq (transf n a) L.bot) →
      L.ge (PMap.get n res) (transf s (PMap.get s res))
  fixpoint_allnodes : {A : Type} → PTreeT A → (A → List positive) →
    (positive → L.t → L.t) → Option (PMapT L.t)
  fixpoint_allnodes_solution :
    ∀ (A : Type) (code : PTreeT A) successors transf res n instr s,
      fixpoint_allnodes code successors transf = some res →
      PTree.get n code = some instr → s ∈ successors instr →
      L.ge (PMap.get n res) (transf s (PMap.get s res))

structure ORDERED_TYPE_WITH_TOP where
  t : Type
  ge : t → t → Prop
  top : t
  top_ge : ∀ x, ge top x
  refl_ge : ∀ x, ge x x

inductive reachable {A : Type} (code : PTreeT A)
    (successors : A → List positive) : positive → positive → Prop where
  | reachable_refl (n : positive) : reachable code successors n n
  | reachable_left (n1 n2 n3 : positive) (i : A)
      (hcode : PTree.get n1 code = some i)
      (hsucc : n2 ∈ successors i)
      (hreach : reachable code successors n2 n3) :
      reachable code successors n1 n3

export reachable (reachable_refl reachable_left)

def reachable_ind {A : Type} (code : PTreeT A)
    (successors : A → List positive)
    (P : ∀ n1 n2, reachable code successors n1 n2 → Prop)
    (hrefl : ∀ n, P n n (reachable_refl n))
    (hleft : ∀ n1 n2 n3 i (hcode : PTree.get n1 code = some i)
      (hsucc : n2 ∈ successors i) (hreach : reachable code successors n2 n3),
      P n2 n3 hreach →
      P n1 n3 (reachable_left n1 n2 n3 i hcode hsucc hreach)) :
    ∀ n1 n2 (h : reachable code successors n1 n2), P n1 n2 h := by
  intro n1 n2 h
  induction h with
  | reachable_refl n => exact hrefl n
  | reachable_left n1 n2 n3 i hcode hsucc hreach ih =>
      exact hleft n1 n2 n3 i hcode hsucc hreach ih

/-!
The Rocq functor result contains polymorphic operation fields, so its direct
Lean representation lives one universe above the ordinary `Type` used by the
generated application seams.  Keep the exact source operation record in a
proof-erased `PLift (Nonempty ...)` carrier and expose the mandatory DMC-004
law certificate on the lower-universe bundled result.
-/
abbrev DataflowSolverOps (LAT : SemiLattice) : Type 1 :=
  { solver : DATAFLOW_SOLVER // solver.L = LAT }

abbrev DataflowSolverCertificate (LAT : SemiLattice) (NS : NodeSetOps) : Prop :=
  SemiLatticeLaws LAT ∧ NodeSetLaws NS

structure DataflowSolverBundle (LAT : SemiLattice) (NS : NodeSetOps) where
  operations : PLift (Nonempty (DataflowSolverOps LAT))
  law_certificate : DataflowSolverCertificate LAT NS

def Dataflow_Solver (LAT : SemiLattice) (NS : NodeSetOps) : Type :=
  DataflowSolverBundle LAT NS

def «Dataflow_Solver.L» (LAT : SemiLattice) (_NS : NodeSetOps) : SemiLattice := LAT

namespace Dataflow_Solver

def L (LAT : SemiLattice) (_NS : NodeSetOps) : SemiLattice := LAT

structure state (LAT : SemiLattice) (NS : NodeSetOps) where
  aval : PTreeT LAT.t
  worklist : NS.t
  visited : positive → Prop

export state (aval worklist visited)

def abstr_value {LAT : SemiLattice} {NS : NodeSetOps}
    (n : positive) (s : state LAT NS) : LAT.t :=
  match PTree.get n s.aval with
  | none => LAT.bot
  | some v => v

def propagate_succ {LAT : SemiLattice} {NS : NodeSetOps}
    (s : state LAT NS) (out : LAT.t) (n : positive) : state LAT NS :=
  match PTree.get n s.aval with
  | none =>
      { aval := PTree.set n out s.aval
        worklist := NS.add n s.worklist
        visited := fun p => p = n ∨ s.visited p }
  | some oldl =>
      let newl := LAT.lub oldl out
      if LAT.beq oldl newl then s else
        { aval := PTree.set n newl s.aval
          worklist := NS.add n s.worklist
          visited := fun p => p = n ∨ s.visited p }

def propagate_succ_list {LAT : SemiLattice} {NS : NodeSetOps}
    (s : state LAT NS) (out : LAT.t) : List positive → state LAT NS
  | [] => s
  | n :: rem => propagate_succ_list (propagate_succ s out n) out rem

def step {A : Type} {LAT : SemiLattice} {NS : NodeSetOps}
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t)
    (s : state LAT NS) : Sum (PMapT LAT.t) (state LAT NS) :=
  match NS.pick s.worklist with
  | none => Sum.inl (LAT.bot, s.aval)
  | some (n, rem) =>
      match PTree.get n code with
      | none => Sum.inr { aval := s.aval, worklist := rem, visited := s.visited }
      | some instr =>
          Sum.inr (propagate_succ_list
            { aval := s.aval, worklist := rem, visited := s.visited }
            (transf n (abstr_value n s)) (successors instr))

def fixpoint_from {A : Type} {LAT : SemiLattice} {NS : NodeSetOps}
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t)
    (start : state LAT NS) : Option (PMapT LAT.t) :=
  CompCert4Lean.Lib.Iteration.PrimIter.iterate (state LAT NS) (PMapT LAT.t)
    (step code successors transf) start

def start_state {LAT : SemiLattice} {NS : NodeSetOps}
    (enode : positive) (eval : LAT.t) : state LAT NS :=
  { aval := PTree.set enode eval (PTree.empty LAT.t)
    worklist := NS.add enode NS.empty
    visited := fun n => n = enode }

def fixpoint {A : Type} (LAT : SemiLattice) (NS : NodeSetOps)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t)
    (enode : positive) (eval : LAT.t) : Option (PMapT LAT.t) :=
  fixpoint_from (NS := NS) code successors transf
    (@start_state LAT NS enode eval)

def start_state_nodeset {LAT : SemiLattice} (NS : NodeSetOps)
    (enodes : NS.t) : state LAT NS :=
  { aval := PTree.empty LAT.t
    worklist := enodes
    visited := fun n => NS.In n enodes }

def fixpoint_nodeset {A : Type} (LAT : SemiLattice) (NS : NodeSetOps)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t)
    (enodes : NS.t) : Option (PMapT LAT.t) :=
  fixpoint_from code successors transf (start_state_nodeset NS enodes)

def start_state_allnodes {A : Type} {LAT : SemiLattice} (NS : NodeSetOps)
    (code : PTreeT A) : state LAT NS :=
  { aval := PTree.empty LAT.t
    worklist := NS.all_nodes code
    visited := fun n => ∃ instr, PTree.get n code = some instr }

def fixpoint_allnodes {A : Type} (LAT : SemiLattice) (NS : NodeSetOps)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) : Option (PMapT LAT.t) :=
  fixpoint_from code successors transf (start_state_allnodes NS code)

inductive optge (LAT : SemiLattice) : Option LAT.t → Option LAT.t → Prop where
  | optge_some {l l' : LAT.t} : LAT.ge l l' → optge LAT (some l) (some l')
  | optge_none (ol : Option LAT.t) : optge LAT ol none

export optge (optge_some optge_none)

inductive steps {A : Type} {LAT : SemiLattice} {NS : NodeSetOps}
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) :
    state LAT NS → state LAT NS → Prop where
  | steps_base (s : state LAT NS) : steps code successors transf s s
  | steps_right (s1 s2 s3 : state LAT NS) :
      steps code successors transf s1 s2 →
      step code successors transf s2 = Sum.inr s3 →
      steps code successors transf s1 s3

export steps (steps_base steps_right)

def steps_ind {A : Type} {LAT : SemiLattice} {NS : NodeSetOps}
    (code : PTreeT A)
    (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t)
    (P : ∀ s s0, steps code successors transf s s0 → Prop)
    (f : ∀ s, P s s (steps_base s))
    (f0 : ∀ (s1 s2 s3 : state LAT NS)
      (s : steps code successors transf s1 s2)
      (_ih : P s1 s2 s)
      (e : step code successors transf s2 = Sum.inr s3),
      P s1 s3 (steps_right s1 s2 s3 s e))
    (s s0 : state LAT NS)
    (s1 : steps code successors transf s s0) : P s s0 s1 :=
  @steps.rec A LAT NS code successors transf s
    (fun s0 h => P s s0 h)
    (f s)
    (fun s2 s3 a_1 a_2 ih => f0 s s2 s3 a_1 ih a_2)
    s0 s1

structure good_state {A : Type} {LAT : SemiLattice} {NS : NodeSetOps}
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (st : state LAT NS) : Prop where
  gs_stable : ∀ n, st.visited n →
    NS.In n st.worklist ∨
      ∀ i s, PTree.get n code = some i → s ∈ successors i →
        optge LAT (PTree.get s st.aval)
          (some (transf n (abstr_value n st)))
  gs_defined : ∀ n v, PTree.get n st.aval = some v → st.visited n

export good_state (gs_stable gs_defined)

end Dataflow_Solver

def successors_list (successors : PTreeT (List positive))
    (pc : positive) : List positive :=
  match PTree.get pc successors with
  | none => []
  | some l => l

def add_successors (pred : PTreeT (List positive))
    (src : positive) : List positive → PTreeT (List positive)
  | [] => pred
  | to :: rem =>
      add_successors (PTree.set to (src :: successors_list pred to) pred) src rem

def make_predecessors {A : Type} (code : PTreeT A)
    (successors : A → List positive) : PTreeT (List positive) :=
  PTree.fold (fun pred pc instr => add_successors pred pc (successors instr))
    code (PTree.empty (List positive))

abbrev BackwardDataflowSolverOps (LAT : SemiLattice) : Type 1 :=
  { solver : BACKWARD_DATAFLOW_SOLVER // solver.L = LAT }

abbrev BackwardDataflowSolverCertificate (LAT : SemiLattice) (NS : NodeSetOps) : Prop :=
  SemiLatticeLaws LAT ∧ NodeSetLaws NS

structure BackwardDataflowSolverBundle (LAT : SemiLattice) (NS : NodeSetOps) where
  operations : PLift (Nonempty (BackwardDataflowSolverOps LAT))
  law_certificate : BackwardDataflowSolverCertificate LAT NS

def Backward_Dataflow_Solver (LAT : SemiLattice) (NS : NodeSetOps) : Type :=
  BackwardDataflowSolverBundle LAT NS
def «Backward_Dataflow_Solver.L» (LAT : SemiLattice) (_NS : NodeSetOps) : SemiLattice := LAT
def «Backward_Dataflow_Solver.DS» (LAT : SemiLattice) (NS : NodeSetOps) : Type :=
  Dataflow_Solver LAT NS
namespace Backward_Dataflow_Solver

def L (LAT : SemiLattice) (_NS : NodeSetOps) : SemiLattice := LAT
def DS (LAT : SemiLattice) (NS : NodeSetOps) : Type := Dataflow_Solver LAT NS

def sequential_node {A : Type} (code : PTreeT A)
    (successors : A → List positive) (pc : positive) (instr : A) : Bool :=
  (successors instr).any (fun s =>
    match PTree.get s code with
    | none => false
    | some _ =>
        match plt s pc with
        | .left _ => true
        | .right _ => false)

def exit_points {A : Type} (NS : NodeSetOps) (code : PTreeT A)
    (successors : A → List positive) : NS.t :=
  PTree.fold (fun ep pc instr =>
      if sequential_node code successors pc instr then ep else NS.add pc ep)
    code NS.empty

def fixpoint {A : Type} (LAT : SemiLattice) (NS : NodeSetOps)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) : Option (PMapT LAT.t) :=
  Dataflow_Solver.fixpoint_nodeset LAT NS
    (make_predecessors code successors) (fun l => l) transf
    (exit_points NS code successors)

def fixpoint_allnodes {A : Type} (LAT : SemiLattice) (NS : NodeSetOps)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) : Option (PMapT LAT.t) :=
  Dataflow_Solver.fixpoint_allnodes LAT NS
    (make_predecessors code successors) (fun l => l) transf

end Backward_Dataflow_Solver

structure BBLOCK_SOLVER where
  L : OrderedTop
  L_laws : OrderedTopLaws L
  fixpoint : {A : Type} → PTreeT A → (A → List positive) →
    (positive → L.t → L.t) → positive → Option (PMapT L.t)
  fixpoint_solution :
    ∀ (A : Type) (code : PTreeT A) successors transf entrypoint res n instr s,
      fixpoint code successors transf entrypoint = some res →
      PTree.get n code = some instr → s ∈ successors instr →
      L.ge (PMap.get s res) (transf n (PMap.get n res))
  fixpoint_entry :
    ∀ (A : Type) (code : PTreeT A) successors transf entrypoint res,
      fixpoint code successors transf entrypoint = some res →
      PMap.get entrypoint res = L.top
  fixpoint_invariant :
    ∀ (A : Type) (code : PTreeT A) successors transf entrypoint
      (P : L.t → Prop), P L.top →
      (∀ pc instr x, PTree.get pc code = some instr → P x → P (transf pc x)) →
      ∀ res pc, fixpoint code successors transf entrypoint = some res →
      P (PMap.get pc res)

abbrev BBlockSolverOps (LAT : OrderedTop) : Type 1 :=
  { solver : BBLOCK_SOLVER // solver.L = LAT }

abbrev BBlockSolverCertificate (LAT : OrderedTop) : Prop := OrderedTopLaws LAT

structure BBlockSolverBundle (LAT : OrderedTop) where
  operations : PLift (Nonempty (BBlockSolverOps LAT))
  law_certificate : BBlockSolverCertificate LAT

def BBlock_solver (LAT : OrderedTop) : Type := BBlockSolverBundle LAT
def «BBlock_solver.L» (LAT : OrderedTop) : OrderedTop := LAT
namespace BBlock_solver

def L (LAT : OrderedTop) : OrderedTop := LAT
abbrev bbmap := positive → Bool
def result (LAT : OrderedTop) : Type := PMapT LAT.t

structure state (LAT : OrderedTop) where
  aval : result LAT
  worklist : List positive

export state (aval worklist)

def propagate_successors {LAT : OrderedTop}
    (bb : bbmap) (succs : List positive) (l : LAT.t) (st : state LAT) : state LAT :=
  match succs with
  | [] => st
  | s1 :: sl =>
      if bb s1 then propagate_successors bb sl l st
      else propagate_successors bb sl l
        { aval := PMap.set s1 l st.aval, worklist := s1 :: st.worklist }

def step {A : Type} {LAT : OrderedTop}
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t)
    (bb : bbmap) (st : state LAT) : Sum (result LAT) (state LAT) :=
  match st.worklist with
  | [] => Sum.inl st.aval
  | pc :: rem =>
      match PTree.get pc code with
      | none => Sum.inr { aval := st.aval, worklist := rem }
      | some instr =>
          Sum.inr (propagate_successors bb (successors instr)
            (transf pc (PMap.get pc st.aval)) { aval := st.aval, worklist := rem })

def is_basic_block_head (entrypoint : positive)
    (preds : PTreeT (List positive)) (pc : positive) : Bool :=
  if _h : pc = entrypoint then true else
    match successors_list preds pc with
    | [] => false
    | [s] => if s = pc then true else false
    | _ :: _ :: _ => true

def basic_block_map {A : Type} (entrypoint : positive)
    (code : PTreeT A) (successors : A → List positive) : bbmap :=
  fun pc => is_basic_block_head entrypoint
    (make_predecessors code successors) pc

def basic_block_list {A : Type} (bb : bbmap) (code : PTreeT A) : List positive :=
  PTree.fold (fun l pc _ => if bb pc then pc :: l else l) code []

def fixpoint {A : Type} (LAT : OrderedTop)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t)
    (entrypoint : positive) : Option (result LAT) :=
  let bb := basic_block_map entrypoint code successors
  CompCert4Lean.Lib.Iteration.PrimIter.iterate (state LAT) (result LAT)
    (step code successors transf bb)
    { aval := PMap.init LAT.top, worklist := basic_block_list bb code }

def predecessors {A : Type} (code : PTreeT A)
    (successors : A → List positive) : PTreeT (List positive) :=
  make_predecessors code successors

def state_invariant {A : Type} {LAT : OrderedTop}
    (entrypoint : positive) (code : PTreeT A)
    (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t)
    (st : state LAT) : Prop :=
  (∀ n, basic_block_map entrypoint code successors n = true →
      PMap.get n st.aval = LAT.top) ∧
  (∀ n, n ∈ st.worklist ∨
    ∀ instr s, PTree.get n code = some instr → s ∈ successors instr →
      LAT.ge (PMap.get s st.aval) (transf n (PMap.get n st.aval)))

def Pstate {LAT : OrderedTop} (P : LAT.t → Prop) (st : state LAT) : Prop :=
  ∀ pc, P (PMap.get pc st.aval)

end BBlock_solver

def NodeSetForward : NodeSetOps :=
  { t := PHeap.t
    empty := PHeap.empty
    add := fun n s => PHeap.insert n s
    pick := fun s => match PHeap.findMax s with
      | some n => some (n, PHeap.deleteMax s)
      | none => none
    all_nodes := fun {A} code =>
      PTree.fold (fun s pc _ => PHeap.insert pc s) code PHeap.empty
    In := PHeap.In }

namespace NodeSetForward
abbrev t : Type := PHeap.t
def empty : t := PHeap.empty
def add (n : positive) (s : t) : t := PHeap.insert n s
def pick (s : t) : Option (positive × t) :=
  match PHeap.findMax s with
  | some n => some (n, PHeap.deleteMax s)
  | none => none
def all_nodes {A : Type} (code : PTreeT A) : t :=
  PTree.fold (fun s pc _ => PHeap.insert pc s) code PHeap.empty
def In (n : positive) (s : t) : Prop := PHeap.In n s
def law_obligation : Prop := NodeSetLaws NodeSetForward
end NodeSetForward

def NodeSetBackward : NodeSetOps :=
  { t := PHeap.t
    empty := PHeap.empty
    add := fun n s => PHeap.insert n s
    pick := fun s => match PHeap.findMin s with
      | some n => some (n, PHeap.deleteMin s)
      | none => none
    all_nodes := fun {A} code =>
      PTree.fold (fun s pc _ => PHeap.insert pc s) code PHeap.empty
    In := PHeap.In }

namespace NodeSetBackward
abbrev t : Type := PHeap.t
def empty : t := PHeap.empty
def add (n : positive) (s : t) : t := PHeap.insert n s
def pick (s : t) : Option (positive × t) :=
  match PHeap.findMin s with
  | some n => some (n, PHeap.deleteMin s)
  | none => none
def all_nodes {A : Type} (code : PTreeT A) : t :=
  PTree.fold (fun s pc _ => PHeap.insert pc s) code PHeap.empty
def In (n : positive) (s : t) : Prop := PHeap.In n s
def law_obligation : Prop := NodeSetLaws NodeSetBackward
end NodeSetBackward

def reachable_transStatement : Prop :=
  ∀ {A : Type} (code : PTreeT A) (successors : A → List positive)
    (n1 n2 : positive), reachable code successors n1 n2 →
    ∀ n3, reachable code successors n2 n3 → reachable code successors n1 n3

def reachable_rightStatement : Prop :=
  ∀ {A : Type} (code : PTreeT A) (successors : A → List positive)
    (n1 n2 n3 : positive) (i : A), reachable code successors n1 n2 →
    PTree.get n2 code = some i → n3 ∈ successors i →
    reachable code successors n1 n3

namespace Dataflow_Solver
def optge_reflStatement : Prop :=
  ∀ {LAT : SemiLattice} (_LATlaws : SemiLatticeLaws LAT)
    (ol : Option LAT.t), optge LAT ol ol
def optge_transStatement : Prop :=
  ∀ {LAT : SemiLattice} (_LATlaws : SemiLatticeLaws LAT)
    (ol1 ol2 ol3 : Option LAT.t),
    optge LAT ol1 ol2 → optge LAT ol2 ol3 → optge LAT ol1 ol3
def optge_abstr_valueStatement : Prop :=
  ∀ {LAT : SemiLattice} {NS : NodeSetOps}
    (_LATlaws : SemiLatticeLaws LAT) (_NSlaws : NodeSetLaws NS)
    (st st' : state LAT NS) (n : positive),
    optge LAT (PTree.get n st.aval) (PTree.get n st'.aval) →
    LAT.ge (abstr_value n st) (abstr_value n st')
def propagate_succ_charactStatement : Prop :=
  ∀ {LAT : SemiLattice} {NS : NodeSetOps}
    (_LATlaws : SemiLatticeLaws LAT) (_NSlaws : NodeSetLaws NS)
    (st : state LAT NS) (out : LAT.t) (n : positive),
    let st' := propagate_succ st out n
    optge LAT (PTree.get n st'.aval) (some out) ∧
    (∀ s, n ≠ s → PTree.get s st'.aval = PTree.get s st.aval) ∧
    (∀ s, optge LAT (PTree.get s st'.aval) (PTree.get s st.aval)) ∧
    (NS.In n st'.worklist ∨ PTree.get n st'.aval = PTree.get n st.aval) ∧
    (∀ n', NS.In n' st.worklist → NS.In n' st'.worklist) ∧
    (∀ n', NS.In n' st'.worklist → n' = n ∨ NS.In n' st.worklist) ∧
    (∀ n', st.visited n' → st'.visited n') ∧
    (∀ n', st'.visited n' → NS.In n' st'.worklist ∨ st.visited n') ∧
    (∀ n', PTree.get n' st.aval = none → PTree.get n' st'.aval ≠ none →
      st'.visited n')
def propagate_succ_list_charactStatement : Prop :=
  ∀ {LAT : SemiLattice} {NS : NodeSetOps}
    (_LATlaws : SemiLatticeLaws LAT) (_NSlaws : NodeSetLaws NS)
    (out : LAT.t) (l : List positive) (st : state LAT NS),
    let st' := propagate_succ_list st out l
    (∀ n, n ∈ l → optge LAT (PTree.get n st'.aval) (some out)) ∧
    (∀ n, n ∉ l → PTree.get n st'.aval = PTree.get n st.aval) ∧
    (∀ n, optge LAT (PTree.get n st'.aval) (PTree.get n st.aval)) ∧
    (∀ n, NS.In n st'.worklist ∨ PTree.get n st'.aval = PTree.get n st.aval) ∧
    (∀ n', NS.In n' st.worklist → NS.In n' st'.worklist) ∧
    (∀ n', NS.In n' st'.worklist → n' ∈ l ∨ NS.In n' st.worklist) ∧
    (∀ n', st.visited n' → st'.visited n') ∧
    (∀ n', st'.visited n' → NS.In n' st'.worklist ∨ st.visited n') ∧
    (∀ n', PTree.get n' st.aval = none → PTree.get n' st'.aval ≠ none →
      st'.visited n')
def fixpoint_from_charactStatement : Prop :=
  ∀ {A : Type} {LAT : SemiLattice} {NS : NodeSetOps}
    (_LATlaws : SemiLatticeLaws LAT) (_NSlaws : NodeSetLaws NS)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (start : state LAT NS)
    (res : PMapT LAT.t), fixpoint_from code successors transf start = some res →
    ∃ st, steps code successors transf start st ∧
      NS.pick st.worklist = none ∧ res = (LAT.bot, st.aval)
def step_incrStatement : Prop :=
  ∀ {A : Type} {LAT : SemiLattice} {NS : NodeSetOps}
    (_LATlaws : SemiLatticeLaws LAT) (_NSlaws : NodeSetLaws NS)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (n : positive)
    (s1 s2 : state LAT NS), step code successors transf s1 = Sum.inr s2 →
    optge LAT (PTree.get n s2.aval) (PTree.get n s1.aval) ∧
      (s1.visited n → s2.visited n)
def steps_incrStatement : Prop :=
  ∀ {A : Type} {LAT : SemiLattice} {NS : NodeSetOps}
    (_LATlaws : SemiLatticeLaws LAT) (_NSlaws : NodeSetLaws NS)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (n : positive)
    (s1 s2 : state LAT NS), steps code successors transf s1 s2 →
    optge LAT (PTree.get n s2.aval) (PTree.get n s1.aval) ∧
      (s1.visited n → s2.visited n)
def step_state_goodStatement : Prop :=
  ∀ {A : Type} {LAT : SemiLattice} {NS : NodeSetOps}
    (_LATlaws : SemiLatticeLaws LAT) (_NSlaws : NodeSetLaws NS)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (st : state LAT NS)
    (pc : positive) (rem : NS.t) (instr : A),
    NS.pick st.worklist = some (pc, rem) → PTree.get pc code = some instr →
    good_state code successors transf st →
    good_state code successors transf
      (propagate_succ_list
        { aval := st.aval, worklist := rem, visited := st.visited }
        (transf pc (abstr_value pc st)) (successors instr))
def step_state_good_2Statement : Prop :=
  ∀ {A : Type} {LAT : SemiLattice} {NS : NodeSetOps}
    (_LATlaws : SemiLatticeLaws LAT) (_NSlaws : NodeSetLaws NS)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (st : state LAT NS)
    (pc : positive) (rem : NS.t), good_state code successors transf st →
    NS.pick st.worklist = some (pc, rem) → PTree.get pc code = none →
    good_state code successors transf
      { aval := st.aval, worklist := rem, visited := st.visited }
def steps_state_goodStatement : Prop :=
  ∀ {A : Type} {LAT : SemiLattice} {NS : NodeSetOps}
    (_LATlaws : SemiLatticeLaws LAT) (_NSlaws : NodeSetLaws NS)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (st1 st2 : state LAT NS),
    steps code successors transf st1 st2 → good_state code successors transf st1 →
    good_state code successors transf st2
def start_state_goodStatement : Prop :=
  ∀ {A : Type} {LAT : SemiLattice} {NS : NodeSetOps}
    (_LATlaws : SemiLatticeLaws LAT) (_NSlaws : NodeSetLaws NS)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (enode : positive) (eval : LAT.t),
    good_state code successors transf (@start_state LAT NS enode eval)
def start_state_nodeset_goodStatement : Prop :=
  ∀ {A : Type} {LAT : SemiLattice} (NS : NodeSetOps)
    (_LATlaws : SemiLatticeLaws LAT) (_NSlaws : NodeSetLaws NS)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (enodes : NS.t),
    good_state code successors transf (start_state_nodeset NS enodes)
def start_state_allnodes_goodStatement : Prop :=
  ∀ {A : Type} {LAT : SemiLattice} (NS : NodeSetOps)
    (_LATlaws : SemiLatticeLaws LAT) (_NSlaws : NodeSetLaws NS)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t),
    good_state code successors transf (start_state_allnodes NS code)
def reachable_visitedStatement : Prop :=
  ∀ {A : Type} {LAT : SemiLattice} {NS : NodeSetOps}
    (_LATlaws : SemiLatticeLaws LAT) (_NSlaws : NodeSetLaws NS)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (st : state LAT NS),
    good_state code successors transf st → NS.pick st.worklist = none →
    ∀ p q, reachable code successors p q → st.visited p → st.visited q
def fixpoint_solutionStatement : Prop :=
  ∀ {A : Type} (LAT : SemiLattice) (NS : NodeSetOps)
    (_LATlaws : SemiLatticeLaws LAT) (_NSlaws : NodeSetLaws NS)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (ep : positive) (ev : LAT.t)
    (res : PMapT LAT.t) (n : positive) (instr : A) (s : positive),
    fixpoint LAT NS code successors transf ep ev = some res →
    PTree.get n code = some instr → s ∈ successors instr →
    (∀ n, LAT.eq (transf n LAT.bot) LAT.bot) →
    LAT.ge (PMap.get s res) (transf n (PMap.get n res))
def fixpoint_entryStatement : Prop :=
  ∀ {A : Type} (LAT : SemiLattice) (NS : NodeSetOps)
    (_LATlaws : SemiLatticeLaws LAT) (_NSlaws : NodeSetLaws NS)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (ep : positive) (ev : LAT.t)
    (res : PMapT LAT.t), fixpoint LAT NS code successors transf ep ev = some res →
    LAT.ge (PMap.get ep res) ev
def fixpoint_allnodes_solutionStatement : Prop :=
  ∀ {A : Type} (LAT : SemiLattice) (NS : NodeSetOps)
    (_LATlaws : SemiLatticeLaws LAT) (_NSlaws : NodeSetLaws NS)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (res : PMapT LAT.t)
    (n : positive) (instr : A) (s : positive),
    fixpoint_allnodes LAT NS code successors transf = some res →
    PTree.get n code = some instr → s ∈ successors instr →
    LAT.ge (PMap.get s res) (transf n (PMap.get n res))
def fixpoint_nodeset_solutionStatement : Prop :=
  ∀ {A : Type} (LAT : SemiLattice) (NS : NodeSetOps)
    (_LATlaws : SemiLatticeLaws LAT) (_NSlaws : NodeSetLaws NS)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (enodes : NS.t)
    (res : PMapT LAT.t) (e n : positive) (instr : A) (s : positive),
    fixpoint_nodeset LAT NS code successors transf enodes = some res →
    NS.In e enodes → reachable code successors e n →
    PTree.get n code = some instr → s ∈ successors instr →
    LAT.ge (PMap.get s res) (transf n (PMap.get n res))
def fixpoint_invariantStatement : Prop :=
  ∀ {A : Type} (LAT : SemiLattice) (NS : NodeSetOps)
    (_LATlaws : SemiLatticeLaws LAT) (_NSlaws : NodeSetLaws NS)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (ep : positive) (ev : LAT.t)
    (P : LAT.t → Prop), P LAT.bot →
    (∀ x y, P x → P y → P (LAT.lub x y)) →
    (∀ pc instr x, PTree.get pc code = some instr → P x → P (transf pc x)) →
    P ev → ∀ res pc, fixpoint LAT NS code successors transf ep ev = some res →
      P (PMap.get pc res)
end Dataflow_Solver

def add_successors_correctStatement : Prop :=
  ∀ (tolist : List positive) (src : positive)
    (pred : PTreeT (List positive)) (n s : positive),
    n ∈ successors_list pred s ∨ (n = src ∧ s ∈ tolist) →
    n ∈ successors_list (add_successors pred src tolist) s
def make_predecessors_correct_1Statement : Prop :=
  ∀ {A : Type} (code : PTreeT A) (successors : A → List positive)
    (n : positive) (instr : A) (s : positive),
    PTree.get n code = some instr → s ∈ successors instr →
    n ∈ successors_list (make_predecessors code successors) s
def make_predecessors_correct_2Statement : Prop :=
  ∀ {A : Type} (code : PTreeT A) (successors : A → List positive)
    (n : positive) (instr : A) (s : positive),
    PTree.get n code = some instr → s ∈ successors instr →
    ∃ l, PTree.get s (make_predecessors code successors) = some l ∧ n ∈ l
def reachable_predecessorsStatement : Prop :=
  ∀ {A : Type} (code : PTreeT A) (successors : A → List positive)
    (p q : positive), reachable code successors p q →
    reachable (make_predecessors code successors) (fun l => l) q p

namespace Backward_Dataflow_Solver
def exit_points_charactStatement : Prop :=
  ∀ {A : Type} (NS : NodeSetOps) (code : PTreeT A)
    (_NSlaws : NodeSetLaws NS)
    (successors : A → List positive) (n : positive),
    NS.In n (exit_points NS code successors) ↔
      ∃ i, PTree.get n code = some i ∧ sequential_node code successors n i = false
def reachable_exit_pointsStatement : Prop :=
  ∀ {A : Type} (NS : NodeSetOps) (code : PTreeT A)
    (_NSlaws : NodeSetLaws NS)
    (successors : A → List positive) (pc : positive) (i : A),
    PTree.get pc code = some i →
    ∃ x, NS.In x (exit_points NS code successors) ∧ reachable code successors pc x
def reachable_exit_points_predecessorStatement : Prop :=
  ∀ {A : Type} (NS : NodeSetOps) (code : PTreeT A)
    (_NSlaws : NodeSetLaws NS)
    (successors : A → List positive) (pc : positive) (i : A),
    PTree.get pc code = some i →
    ∃ x, NS.In x (exit_points NS code successors) ∧
      reachable (make_predecessors code successors) (fun l => l) x pc
def fixpoint_solutionStatement : Prop :=
  ∀ {A : Type} (LAT : SemiLattice) (NS : NodeSetOps)
    (_LATlaws : SemiLatticeLaws LAT) (_NSlaws : NodeSetLaws NS)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (res : PMapT LAT.t)
    (n : positive) (instr : A) (s : positive),
    fixpoint LAT NS code successors transf = some res →
    PTree.get n code = some instr → s ∈ successors instr →
    (∀ n a, PTree.get n code = none → LAT.eq (transf n a) LAT.bot) →
    LAT.ge (PMap.get n res) (transf s (PMap.get s res))
def fixpoint_allnodes_solutionStatement : Prop :=
  ∀ {A : Type} (LAT : SemiLattice) (NS : NodeSetOps)
    (_LATlaws : SemiLatticeLaws LAT) (_NSlaws : NodeSetLaws NS)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (res : PMapT LAT.t)
    (n : positive) (instr : A) (s : positive),
    fixpoint_allnodes LAT NS code successors transf = some res →
    PTree.get n code = some instr → s ∈ successors instr →
    LAT.ge (PMap.get n res) (transf s (PMap.get s res))
end Backward_Dataflow_Solver

namespace BBlock_solver
def predecessors_correctStatement : Prop :=
  ∀ {A : Type} (code : PTreeT A) (successors : A → List positive)
    (n : positive) (instr : A) (s : positive),
    PTree.get n code = some instr → s ∈ successors instr →
    n ∈ successors_list (predecessors code successors) s
def multiple_predecessorsStatement : Prop :=
  ∀ {A : Type} (entrypoint : positive) (code : PTreeT A)
    (successors : A → List positive) (s n1 : positive) (instr1 : A)
    (n2 : positive) (instr2 : A), PTree.get n1 code = some instr1 →
    s ∈ successors instr1 → PTree.get n2 code = some instr2 →
    s ∈ successors instr2 → n1 ≠ n2 →
    basic_block_map entrypoint code successors s = true
def no_self_loopStatement : Prop :=
  ∀ {A : Type} (entrypoint : positive) (code : PTreeT A)
    (successors : A → List positive) (n : positive) (instr : A),
    PTree.get n code = some instr → n ∈ successors instr →
    basic_block_map entrypoint code successors n = true
def propagate_successors_charact1Statement : Prop :=
  ∀ {LAT : OrderedTop} (_LATlaws : OrderedTopLaws LAT)
    (bb : bbmap) (succs : List positive)
    (l : LAT.t) (st : state LAT) (n : positive),
    n ∈ st.worklist → n ∈ (propagate_successors bb succs l st).worklist
def propagate_successors_charact2Statement : Prop :=
  ∀ {LAT : OrderedTop} (_LATlaws : OrderedTopLaws LAT)
    (bb : bbmap) (succs : List positive)
    (l : LAT.t) (st : state LAT) (n : positive),
    let st' := propagate_successors bb succs l st
    (n ∈ succs → bb n = false → n ∈ st'.worklist ∧ PMap.get n st'.aval = l) ∧
    (n ∉ succs ∨ bb n = true → PMap.get n st'.aval = PMap.get n st.aval)
def propagate_successors_invariantStatement : Prop :=
  ∀ {A : Type} {LAT : OrderedTop} (entrypoint : positive)
    (_LATlaws : OrderedTopLaws LAT)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (pc : positive) (instr : A)
    (res : result LAT) (rem : List positive), PTree.get pc code = some instr →
    state_invariant entrypoint code successors transf
      { aval := res, worklist := pc :: rem } →
    state_invariant entrypoint code successors transf
      (propagate_successors (basic_block_map entrypoint code successors)
        (successors instr) (transf pc (PMap.get pc res))
        { aval := res, worklist := rem })
def propagate_successors_invariant_2Statement : Prop :=
  ∀ {A : Type} {LAT : OrderedTop} (entrypoint : positive)
    (_LATlaws : OrderedTopLaws LAT)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (pc : positive)
    (res : result LAT) (rem : List positive), PTree.get pc code = none →
    state_invariant entrypoint code successors transf
      { aval := res, worklist := pc :: rem } →
    state_invariant entrypoint code successors transf
      { aval := res, worklist := rem }
def initial_state_invariantStatement : Prop :=
  ∀ {A : Type} (LAT : OrderedTop) (entrypoint : positive)
    (_LATlaws : OrderedTopLaws LAT)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t),
    let bb := basic_block_map entrypoint code successors
    state_invariant entrypoint code successors transf
      { aval := PMap.init LAT.top, worklist := basic_block_list bb code }
def analyze_invariantStatement : Prop :=
  ∀ {A : Type} (LAT : OrderedTop) (entrypoint : positive)
    (_LATlaws : OrderedTopLaws LAT)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (res : result LAT),
    fixpoint LAT code successors transf entrypoint = some res →
    state_invariant entrypoint code successors transf
      { aval := res, worklist := [] }
def fixpoint_solutionStatement : Prop :=
  ∀ {A : Type} (LAT : OrderedTop) (entrypoint : positive)
    (_LATlaws : OrderedTopLaws LAT)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (res : result LAT)
    (n : positive) (instr : A) (s : positive),
    fixpoint LAT code successors transf entrypoint = some res →
    PTree.get n code = some instr → s ∈ successors instr →
    LAT.ge (PMap.get s res) (transf n (PMap.get n res))
def fixpoint_entryStatement : Prop :=
  ∀ {A : Type} (LAT : OrderedTop) (entrypoint : positive)
    (_LATlaws : OrderedTopLaws LAT)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (res : result LAT),
    fixpoint LAT code successors transf entrypoint = some res →
    PMap.get entrypoint res = LAT.top
def propagate_successors_PStatement : Prop :=
  ∀ {LAT : OrderedTop} (_LATlaws : OrderedTopLaws LAT)
    (P : LAT.t → Prop) (bb : bbmap) (l : LAT.t),
    P l → ∀ succs st, Pstate P st → Pstate P (propagate_successors bb succs l st)
def fixpoint_invariantStatement : Prop :=
  ∀ {A : Type} (LAT : OrderedTop) (entrypoint : positive)
    (_LATlaws : OrderedTopLaws LAT)
    (code : PTreeT A) (successors : A → List positive)
    (transf : positive → LAT.t → LAT.t) (P : LAT.t → Prop),
    P LAT.top →
    (∀ pc instr x, PTree.get pc code = some instr → P x → P (transf pc x)) →
    ∀ res pc, fixpoint LAT code successors transf entrypoint = some res →
      P (PMap.get pc res)
end BBlock_solver

namespace NodeSetForward
def empty_specStatement : Prop := ∀ n, ¬ In n empty
def add_specStatement : Prop := ∀ n n' s, In n' (add n s) ↔ n = n' ∨ In n' s
def pick_noneStatement : Prop := ∀ s n, pick s = none → ¬ In n s
def pick_someStatement : Prop :=
  ∀ s n s', pick s = some (n, s') → ∀ n', In n' s ↔ n = n' ∨ In n' s'
def all_nodes_specStatement : Prop :=
  ∀ (A : Type) (code : PTreeT A) n instr,
    PTree.get n code = some instr → In n (all_nodes code)
end NodeSetForward

namespace NodeSetBackward
def empty_specStatement : Prop := ∀ n, ¬ In n empty
def add_specStatement : Prop := ∀ n n' s, In n' (add n s) ↔ n = n' ∨ In n' s
def pick_noneStatement : Prop := ∀ s n, pick s = none → ¬ In n s
def pick_someStatement : Prop :=
  ∀ s n s', pick s = some (n, s') → ∀ n', In n' s ↔ n = n' ∨ In n' s'
def all_nodes_specStatement : Prop :=
  ∀ (A : Type) (code : PTreeT A) n instr,
    PTree.get n code = some instr → In n (all_nodes code)
end NodeSetBackward

end CompCert4Lean.Backend.Kildall

namespace CompCert4Lean.Backend.Kildall.NodeSetBackward

theorem empty_spec : empty_specStatement := by
  intro n
  change ¬ CompCert4Lean.Lib.Heaps.PHeap.In n
    CompCert4Lean.Lib.Heaps.PHeap.empty
  simp [CompCert4Lean.Lib.Heaps.PHeap.In,
    CompCert4Lean.Lib.Heaps.PHeap.empty,
    CompCert4Lean.Lib.Heaps.SplayHeapSet.empty,
    CompCert4Lean.Lib.Heaps.SplayHeapSet.In,
    CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In]

end CompCert4Lean.Backend.Kildall.NodeSetBackward

namespace CompCert4Lean.Backend.Kildall.NodeSetBackward

private theorem pheap_in_insert_self (n :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
    (s : CompCert4Lean.Lib.Heaps.PHeap.t) :
    CompCert4Lean.Lib.Heaps.PHeap.In n
      (CompCert4Lean.Lib.Heaps.PHeap.insert n s) := by
  rcases s with ⟨h, hb⟩
  change CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In _ n
    (CompCert4Lean.Lib.Heaps.SplayHeapSet.R.insert _ n h)
  simp only [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.insert,
    CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In]
  exact Or.inr (Or.inl rfl)

private theorem raw_in_partition {E : CompCert4Lean.Lib.Heaps.OrderedType}
    (y pivot : E.t) (hne : ¬ E.eq y pivot) :
    ∀ h : CompCert4Lean.Lib.Heaps.SplayHeapSet.R.heap E,
      (CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y h ↔
        CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y
          (CompCert4Lean.Lib.Heaps.SplayHeapSet.R.partition E pivot h).1 ∨
        CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y
          (CompCert4Lean.Lib.Heaps.SplayHeapSet.R.partition E pivot h).2)
  | .Empty => by
      simp [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.partition,
        CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In]
  | .Node a x b => by
      cases hcmp : E.compare x pivot with
      | EQ hx =>
          have hyx : ¬ E.eq y x := fun h =>
            hne (E.eq_trans y x pivot h hx)
          rw [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.partition.eq_def]
          simp only [hcmp, CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In]
          simp_all [or_assoc, or_left_comm, or_comm]
      | LT hx =>
          cases b with
          | Empty =>
              rw [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.partition.eq_def]
              simp only [hcmp, CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In]
              simp_all [or_assoc, or_left_comm, or_comm]
          | Node b1 z b2 =>
              cases hzcmp : E.compare z pivot with
              | EQ hz =>
                  have hyz : ¬ E.eq y z := fun h =>
                    hne (E.eq_trans y z pivot h hz)
                  rw [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.partition.eq_def]
                  simp only [hcmp, hzcmp,
                    CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In]
                  simp_all [or_assoc, or_left_comm, or_comm]
              | LT hz =>
                  have hi := raw_in_partition y pivot hne b2
                  rw [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.partition.eq_def]
                  simp only [hcmp, hzcmp,
                    CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In] at hi ⊢
                  simp_all [or_assoc, or_left_comm, or_comm]
              | GT hz =>
                  have hi := raw_in_partition y pivot hne b1
                  rw [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.partition.eq_def]
                  simp only [hcmp, hzcmp,
                    CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In] at hi ⊢
                  simp_all [or_assoc, or_left_comm, or_comm]
      | GT hx =>
          cases a with
          | Empty =>
              rw [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.partition.eq_def]
              simp only [hcmp, CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In]
              simp_all [or_assoc, or_left_comm, or_comm]
          | Node a1 z a2 =>
              cases hzcmp : E.compare z pivot with
              | EQ hz =>
                  have hyz : ¬ E.eq y z := fun h =>
                    hne (E.eq_trans y z pivot h hz)
                  rw [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.partition.eq_def]
                  simp only [hcmp, hzcmp,
                    CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In]
                  simp_all [or_assoc, or_left_comm, or_comm]
              | LT hz =>
                  have hi := raw_in_partition y pivot hne a2
                  rw [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.partition.eq_def]
                  simp only [hcmp, hzcmp,
                    CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In] at hi ⊢
                  simp_all [or_assoc, or_left_comm, or_comm]
              | GT hz =>
                  have hi := raw_in_partition y pivot hne a1
                  rw [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.partition.eq_def]
                  simp only [hcmp, hzcmp,
                    CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In] at hi ⊢
                  simp_all [or_assoc, or_left_comm, or_comm]

private theorem raw_in_insert {E : CompCert4Lean.Lib.Heaps.OrderedType}
    (x y : E.t) (h : CompCert4Lean.Lib.Heaps.SplayHeapSet.R.heap E) :
    (CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y
        (CompCert4Lean.Lib.Heaps.SplayHeapSet.R.insert E x h) ↔
      E.eq y x ∨ CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y h) := by
  unfold CompCert4Lean.Lib.Heaps.SplayHeapSet.R.insert
  cases hpart : CompCert4Lean.Lib.Heaps.SplayHeapSet.R.partition E x h with
  | mk a b =>
      simp only [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In]
      by_cases hyx : E.eq y x
      · simp [hyx]
      · have hp := raw_in_partition y x hyx h
        rw [hpart] at hp
        simp_all [or_assoc, or_left_comm, or_comm]

private theorem pheap_in_insert (s : CompCert4Lean.Lib.Heaps.PHeap.t)
    (x y : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) :
    (CompCert4Lean.Lib.Heaps.PHeap.In y
        (CompCert4Lean.Lib.Heaps.PHeap.insert x s) ↔
      x = y ∨ CompCert4Lean.Lib.Heaps.PHeap.In y s) := by
  rcases s with ⟨h, hb⟩
  have hraw := raw_in_insert x y h
  constructor
  · intro hin
    rcases hraw.mp hin with hxy | hin
    · exact Or.inl hxy.symm
    · exact Or.inr hin
  · intro hin
    rcases hin with hxy | hin
    · exact hraw.mpr (Or.inl hxy.symm)
    · exact hraw.mpr (Or.inr hin)

theorem add_spec : add_specStatement := by
  intro n n' s
  change CompCert4Lean.Lib.Heaps.PHeap.In n'
      (CompCert4Lean.Lib.Heaps.PHeap.insert n s) ↔
    n = n' ∨ CompCert4Lean.Lib.Heaps.PHeap.In n' s
  exact pheap_in_insert s n n'

theorem all_nodes_spec : all_nodes_specStatement := by
  intro A code n instr hget
  let P : PTreeT A → CompCert4Lean.Lib.Heaps.PHeap.t → Prop :=
    fun m s => ∀ n instr, CompCert4Lean.Lib.Maps.PTree.get n m = some instr →
      CompCert4Lean.Lib.Heaps.PHeap.In n s
  have hfold : P code
      (CompCert4Lean.Lib.Maps.PTree.fold
        (fun s pc _ => CompCert4Lean.Lib.Heaps.PHeap.insert pc s)
        code CompCert4Lean.Lib.Heaps.PHeap.empty) := by
    apply CompCert4Lean.Lib.Maps.PTree_Properties.fold_rec_proof
    · intro m m' s hmaps hP n instr hn
      apply hP n instr
      rw [hmaps n]
      exact hn
    · intro n instr hn
      simp [CompCert4Lean.Lib.Maps.PTree.empty,
        CompCert4Lean.Lib.Maps.PTree.get] at hn
    · intro m s k v hnone hsome hP n instr hn
      rw [CompCert4Lean.Lib.Maps.PTree.getSet_equation] at hn
      split at hn
      · subst n
        exact pheap_in_insert_self k s
      · exact (pheap_in_insert s k n).mpr (Or.inr (hP n instr hn))
  change CompCert4Lean.Lib.Heaps.PHeap.In n (all_nodes code)
  simpa [all_nodes] using hfold n instr hget

end CompCert4Lean.Backend.Kildall.NodeSetBackward

namespace CompCert4Lean.Backend.Kildall.NodeSetBackward

private theorem pheap_findMin_none_eq_empty (s :
    CompCert4Lean.Lib.Heaps.PHeap.t) :
    CompCert4Lean.Lib.Heaps.PHeap.findMin s = none → s.1 = .Empty := by
  rcases s with ⟨h, hb⟩
  revert hb
  induction h with
  | Empty =>
      intro hb hs
      rfl
  | Node l x r ihl ihr =>
      intro hb hs
      cases l with
      | Empty =>
          have hcontra : (some x : Option
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) = none := by
            simpa [CompCert4Lean.Lib.Heaps.PHeap.findMin,
              CompCert4Lean.Lib.Heaps.SplayHeapSet.findMin,
              CompCert4Lean.Lib.Heaps.SplayHeapSet.R.findMin] using hs
          cases hcontra
      | Node l₁ y l₂ =>
          have hs' : CompCert4Lean.Lib.Heaps.PHeap.findMin
              ⟨.Node l₁ y l₂, hb.1⟩ = none := hs
          have he := ihl hb.1 hs'
          cases he

theorem pick_none : pick_noneStatement := by
  intro s n hs
  intro hn
  unfold pick at hs
  cases hfind : CompCert4Lean.Lib.Heaps.PHeap.findMin s with
  | some x => simp [hfind] at hs
  | none =>
    have he := pheap_findMin_none_eq_empty s hfind
    rcases s with ⟨h, hb⟩
    cases he
    change CompCert4Lean.Lib.Heaps.PHeap.In n ⟨.Empty, hb⟩ at hn
    simpa [CompCert4Lean.Lib.Heaps.PHeap.In,
      CompCert4Lean.Lib.Heaps.SplayHeapSet.In,
      CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In] using hn

private def raw_heap_size {E : CompCert4Lean.Lib.Heaps.OrderedType} :
    CompCert4Lean.Lib.Heaps.SplayHeapSet.R.heap E → Nat
  | .Empty => 0
  | .Node l _ r => raw_heap_size l + raw_heap_size r + 1

private def raw_in_deleteMin {E : CompCert4Lean.Lib.Heaps.OrderedType}
    (h : CompCert4Lean.Lib.Heaps.SplayHeapSet.R.heap E)
    (hb : CompCert4Lean.Lib.Heaps.SplayHeapSet.R.bst E h)
    (x y : E.t)
    (hs : CompCert4Lean.Lib.Heaps.SplayHeapSet.R.findMin E h = some x) :
    (CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y h ↔
      E.eq x y ∨ CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y
        (CompCert4Lean.Lib.Heaps.SplayHeapSet.R.deleteMin E h)) := by
  cases h with
  | Empty => simp [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.findMin] at hs
  | Node l z r =>
      cases l with
      | Empty =>
          simp only [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.findMin] at hs
          cases hs
          simp only [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In,
            CompCert4Lean.Lib.Heaps.SplayHeapSet.R.deleteMin]
          constructor <;> intro h
          · rcases h with h | h | h
            · exact False.elim h
            · exact Or.inl (E.eq_sym _ _ h)
            · exact Or.inr h
          · rcases h with h | h
            · exact Or.inr (Or.inl (E.eq_sym _ _ h))
            · exact Or.inr (Or.inr h)
      | Node l₁ w l₂ =>
          cases l₁ with
          | Empty =>
              simp only [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.findMin] at hs
              cases hs
              change
                ((False ∨ E.eq y x ∨
                    CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y l₂) ∨
                  E.eq y z ∨
                  CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y r ↔
                  E.eq x y ∨
                    CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y l₂ ∨
                      E.eq y z ∨
                        CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y r)
              constructor <;> intro h
              · rcases h with h | h | h
                · rcases h with h | h | h
                  · exact False.elim h
                  · exact Or.inl (E.eq_sym _ _ h)
                  · exact Or.inr (Or.inl h)
                · exact Or.inr (Or.inr (Or.inl h))
                · exact Or.inr (Or.inr (Or.inr h))
              · rcases h with h | h | h | h
                · exact Or.inl (Or.inr (Or.inl (E.eq_sym _ _ h)))
                · exact Or.inl (Or.inr (Or.inr h))
                · exact Or.inr (Or.inl h)
                · exact Or.inr (Or.inr h)
          | Node a u b =>
              have hs₁ : CompCert4Lean.Lib.Heaps.SplayHeapSet.R.findMin E
                  (.Node a u b) = some x := by
                simpa only [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.findMin] using hs
              have hi := raw_in_deleteMin (.Node a u b) hb.1.1 x y hs₁
              change
                ((CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y (.Node a u b) ∨
                    E.eq y w ∨
                    CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y l₂) ∨
                  E.eq y z ∨
                  CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y r ↔
                  E.eq x y ∨
                    CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y
                      (CompCert4Lean.Lib.Heaps.SplayHeapSet.R.deleteMin E
                        (.Node a u b)) ∨
                    E.eq y w ∨
                    CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y l₂ ∨
                    E.eq y z ∨
                    CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y r)
              constructor
              · intro h
                rcases h with h | h | h
                · rcases h with h | h | h
                  · rcases hi.mp h with h | h
                    · exact Or.inl h
                    · exact Or.inr (Or.inl h)
                  · exact Or.inr (Or.inr (Or.inl h))
                  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
              · intro h
                rcases h with h | h | h | h | h | h
                · exact Or.inl (Or.inl (hi.mpr (Or.inl h)))
                · exact Or.inl (Or.inl (hi.mpr (Or.inr h)))
                · exact Or.inl (Or.inr (Or.inl h))
                · exact Or.inl (Or.inr (Or.inr h))
                · exact Or.inr (Or.inl h)
                · exact Or.inr (Or.inr h)

private theorem pheap_in_deleteMin :
    ∀ (s : CompCert4Lean.Lib.Heaps.PHeap.t)
      (x y : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive),
      CompCert4Lean.Lib.Heaps.PHeap.findMin s = some x →
      (CompCert4Lean.Lib.Heaps.PHeap.In y s ↔
        x = y ∨ CompCert4Lean.Lib.Heaps.PHeap.In y
          (CompCert4Lean.Lib.Heaps.PHeap.deleteMin s)) := by
  intro s x y hs
  rcases s with ⟨h, hb⟩
  exact raw_in_deleteMin h hb x y hs

theorem pick_some : pick_someStatement := by
  intro s n s' hs n'
  unfold pick at hs
  cases hfind : CompCert4Lean.Lib.Heaps.PHeap.findMin s with
  | none => simp [hfind] at hs
  | some m =>
      rw [hfind] at hs
      have hresult := pheap_in_deleteMin s m n' hfind
      change some (m, CompCert4Lean.Lib.Heaps.PHeap.deleteMin s) =
        some (n, s') at hs
      cases hs
      exact hresult

end CompCert4Lean.Backend.Kildall.NodeSetBackward

namespace CompCert4Lean.Backend.Kildall.NodeSetForward

theorem empty_spec : empty_specStatement := by
  intro n hn
  exact hn

theorem add_spec : add_specStatement := by
  simpa [CompCert4Lean.Backend.Kildall.NodeSetForward.add_specStatement,
    CompCert4Lean.Backend.Kildall.NodeSetBackward.add_specStatement,
    CompCert4Lean.Backend.Kildall.NodeSetForward.add,
    CompCert4Lean.Backend.Kildall.NodeSetBackward.add,
    CompCert4Lean.Backend.Kildall.NodeSetForward.In,
    CompCert4Lean.Backend.Kildall.NodeSetBackward.In] using
    (CompCert4Lean.Backend.Kildall.NodeSetBackward.add_spec)

private theorem pheap_findMax_none_eq_empty (s :
    CompCert4Lean.Lib.Heaps.PHeap.t) :
    CompCert4Lean.Lib.Heaps.PHeap.findMax s = none → s.1 = .Empty := by
  rcases s with ⟨h, hb⟩
  revert hb
  induction h with
  | Empty =>
      intro hb hs
      rfl
  | Node l x r ihl ihr =>
      intro hb hs
      cases r with
      | Empty =>
          have hcontra : (some x : Option
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) = none := by
            simpa [CompCert4Lean.Lib.Heaps.PHeap.findMax,
              CompCert4Lean.Lib.Heaps.SplayHeapSet.findMax,
              CompCert4Lean.Lib.Heaps.SplayHeapSet.R.findMax] using hs
          cases hcontra
      | Node r₁ y r₂ =>
          have hs' : CompCert4Lean.Lib.Heaps.PHeap.findMax
              ⟨.Node r₁ y r₂, hb.2.1⟩ = none := by
            simpa [CompCert4Lean.Lib.Heaps.PHeap.findMax,
              CompCert4Lean.Lib.Heaps.SplayHeapSet.findMax,
              CompCert4Lean.Lib.Heaps.SplayHeapSet.R.findMax] using hs
          have he := ihr hb.2.1 hs'
          cases he

theorem pick_none : pick_noneStatement := by
  intro s n hs hn
  unfold pick at hs
  cases hfind : CompCert4Lean.Lib.Heaps.PHeap.findMax s with
  | some x => simp [hfind] at hs
  | none =>
      have he := pheap_findMax_none_eq_empty s hfind
      rcases s with ⟨h, hb⟩
      cases he
      change CompCert4Lean.Lib.Heaps.PHeap.In n ⟨.Empty, hb⟩ at hn
      simpa [CompCert4Lean.Lib.Heaps.PHeap.In,
        CompCert4Lean.Lib.Heaps.SplayHeapSet.In,
        CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In] using hn

end CompCert4Lean.Backend.Kildall.NodeSetForward

namespace CompCert4Lean.Backend.Kildall.NodeSetBackward

theorem law_obligation_proof : law_obligation := by
  constructor
  · exact empty_spec
  · exact add_spec
  · exact pick_none
  · exact pick_some
  · exact all_nodes_spec

end CompCert4Lean.Backend.Kildall.NodeSetBackward

namespace CompCert4Lean.Backend.Kildall

theorem reachable_trans : reachable_transStatement := by
  intro A code successors n1 n2 hreach
  induction hreach with
  | reachable_refl n =>
      intro n3 hreach'
      exact hreach'
  | reachable_left n₁ n₂ n₃ i hcode hsucc htail ih =>
      intro n4 hreach'
      exact reachable_left n₁ n₂ n4 i hcode hsucc (ih n4 hreach')

theorem reachable_right : reachable_rightStatement := by
  intro A code successors n1 n2 n3 i hreach hcode hsucc
  exact reachable_trans code successors n1 n2 hreach n3
    (reachable_left n2 n3 n3 i hcode hsucc (reachable_refl n3))

end CompCert4Lean.Backend.Kildall

namespace CompCert4Lean.Backend.Kildall.NodeSetForward

private theorem forward_pheap_in_insert_self (n :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
    (s : CompCert4Lean.Lib.Heaps.PHeap.t) :
    CompCert4Lean.Lib.Heaps.PHeap.In n
      (CompCert4Lean.Lib.Heaps.PHeap.insert n s) := by
  rcases s with ⟨h, hb⟩
  change CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In _ n
    (CompCert4Lean.Lib.Heaps.SplayHeapSet.R.insert _ n h)
  simp only [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.insert,
    CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In]
  exact Or.inr (Or.inl rfl)

theorem all_nodes_spec : all_nodes_specStatement := by
  intro A code n instr hget
  let P : PTreeT A → CompCert4Lean.Lib.Heaps.PHeap.t → Prop :=
    fun m s => ∀ n instr, CompCert4Lean.Lib.Maps.PTree.get n m = some instr →
      CompCert4Lean.Lib.Heaps.PHeap.In n s
  have hfold : P code
      (CompCert4Lean.Lib.Maps.PTree.fold
        (fun s pc _ => CompCert4Lean.Lib.Heaps.PHeap.insert pc s)
        code CompCert4Lean.Lib.Heaps.PHeap.empty) := by
    apply CompCert4Lean.Lib.Maps.PTree_Properties.fold_rec_proof
    · intro m m' s hmaps hP n instr hn
      apply hP n instr
      rw [hmaps n]
      exact hn
    · intro n instr hn
      simp [CompCert4Lean.Lib.Maps.PTree.empty,
        CompCert4Lean.Lib.Maps.PTree.get] at hn
    · intro m s k v hnone hsome hP n instr hn
      rw [CompCert4Lean.Lib.Maps.PTree.getSet_equation] at hn
      split at hn
      · subst n
        exact forward_pheap_in_insert_self k s
      · exact (add_spec k n s).mpr (Or.inr (hP n instr hn))
  change CompCert4Lean.Lib.Heaps.PHeap.In n (all_nodes code)
  simpa [all_nodes] using hfold n instr hget

end CompCert4Lean.Backend.Kildall.NodeSetForward

namespace CompCert4Lean.Backend.Kildall.NodeSetForward

private def forward_raw_in_deleteMax {E : CompCert4Lean.Lib.Heaps.OrderedType}
    (h : CompCert4Lean.Lib.Heaps.SplayHeapSet.R.heap E)
    (hb : CompCert4Lean.Lib.Heaps.SplayHeapSet.R.bst E h)
    (x y : E.t)
    (hs : CompCert4Lean.Lib.Heaps.SplayHeapSet.R.findMax E h = some x) :
    (CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y h ↔
      E.eq x y ∨ CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y
        (CompCert4Lean.Lib.Heaps.SplayHeapSet.R.deleteMax E h)) := by
  cases h with
  | Empty => simp [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.findMax] at hs
  | Node l z r =>
      cases r with
      | Empty =>
          simp only [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.findMax] at hs
          cases hs
          simp only [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In,
            CompCert4Lean.Lib.Heaps.SplayHeapSet.R.deleteMax]
          constructor <;> intro h
          · rcases h with h | h | h
            · exact Or.inr h
            · exact Or.inl (E.eq_sym _ _ h)
            · exact False.elim h
          · rcases h with h | h
            · exact Or.inr (Or.inl (E.eq_sym _ _ h))
            · exact Or.inl h
      | Node r₁ w r₂ =>
          cases r₂ with
          | Empty =>
              simp only [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.findMax] at hs
              cases hs
              change
                (CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y l ∨ E.eq y z ∨
                    (CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y r₁ ∨
                      E.eq y x ∨ False) ↔
                  E.eq x y ∨
                    (CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y l ∨
                      E.eq y z ∨
                        CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y r₁))
              constructor <;> intro h
              · rcases h with h | h | h | h | h
                · exact Or.inr (Or.inl h)
                · exact Or.inr (Or.inr (Or.inl h))
                · exact Or.inr (Or.inr (Or.inr h))
                · exact Or.inl (E.eq_sym _ _ h)
                · exact False.elim h
              · rcases h with h | h | h | h
                · exact Or.inr (Or.inr (Or.inr (Or.inl (E.eq_sym _ _ h))))
                · exact Or.inl h
                · exact Or.inr (Or.inl h)
                · exact Or.inr (Or.inr (Or.inl h))
          | Node a u b =>
              have hs₁ : CompCert4Lean.Lib.Heaps.SplayHeapSet.R.findMax E
                  (.Node a u b) = some x := by
                simpa only [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.findMax] using hs
              have hi := forward_raw_in_deleteMax (.Node a u b) hb.2.1.2.1 x y hs₁
              change
                (CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y l ∨ E.eq y z ∨
                    (CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y r₁ ∨
                      E.eq y w ∨
                        CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y
                          (.Node a u b))) ↔
                  E.eq x y ∨
                    CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In E y
                      (.Node (.Node l z r₁) w
                        (CompCert4Lean.Lib.Heaps.SplayHeapSet.R.deleteMax E
                          (.Node a u b)))
              rw [hi]
              simp only [CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In]
              simp [or_assoc, or_left_comm, or_comm]

private theorem forward_pheap_in_deleteMax :
    ∀ (s : CompCert4Lean.Lib.Heaps.PHeap.t)
      (x y : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive),
      CompCert4Lean.Lib.Heaps.PHeap.findMax s = some x →
      (CompCert4Lean.Lib.Heaps.PHeap.In y s ↔
        x = y ∨ CompCert4Lean.Lib.Heaps.PHeap.In y
          (CompCert4Lean.Lib.Heaps.PHeap.deleteMax s)) := by
  intro s x y hs
  rcases s with ⟨h, hb⟩
  exact forward_raw_in_deleteMax h hb x y hs

theorem pick_some : pick_someStatement := by
  intro s n s' hs n'
  unfold pick at hs
  cases hfind : CompCert4Lean.Lib.Heaps.PHeap.findMax s with
  | none => simp [hfind] at hs
  | some m =>
      rw [hfind] at hs
      have hresult := forward_pheap_in_deleteMax s m n' hfind
      change some (m, CompCert4Lean.Lib.Heaps.PHeap.deleteMax s) =
        some (n, s') at hs
      cases hs
      exact hresult

end CompCert4Lean.Backend.Kildall.NodeSetForward

namespace CompCert4Lean.Backend.Kildall.NodeSetForward

theorem law_obligation_proof : law_obligation := by
  constructor
  · exact empty_spec
  · exact add_spec
  · exact pick_none
  · exact pick_some
  · exact all_nodes_spec

end CompCert4Lean.Backend.Kildall.NodeSetForward

namespace CompCert4Lean.Backend.Kildall.Dataflow_Solver

theorem optge_refl : optge_reflStatement := by
  intro LAT LATlaws ol
  cases ol with
  | none => exact optge_none none
  | some l => exact optge_some (LATlaws.ge_refl l l (LATlaws.eq_refl l))

end CompCert4Lean.Backend.Kildall.Dataflow_Solver

namespace CompCert4Lean.Backend.Kildall.Dataflow_Solver

theorem optge_trans : optge_transStatement := by
  intro LAT LATlaws ol1 ol2 ol3 h12 h23
  cases h23 with
  | optge_none _ => exact optge_none ol1
  | optge_some h23 =>
      cases h12 with
      | optge_some h12 =>
          exact optge_some (LATlaws.ge_trans _ _ _ h12 h23)

end CompCert4Lean.Backend.Kildall.Dataflow_Solver

namespace CompCert4Lean.Backend.Kildall.Dataflow_Solver

open CompCert4Lean.Lib.Maps

theorem propagate_succ_charact : propagate_succ_charactStatement := by
  intro LAT NS LATlaws NSlaws st out n
  unfold propagate_succ
  cases hget : PTree.get n st.aval with
  | none =>
      simp only [hget]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have hset : PTree.get n (PTree.set n out st.aval) = some out := by
          simpa using PTree.getSet_equation n n out st.aval
        rw [hset]
        exact optge_refl LATlaws (some out)
      · intro s hne
        have hsn : s ≠ n := fun h => hne h.symm
        simpa [hsn] using PTree.getSet_equation s n out st.aval
      · intro s
        by_cases heq : s = n
        · subst s
          have hset : PTree.get n (PTree.set n out st.aval) = some out := by
            simpa using PTree.getSet_equation n n out st.aval
          rw [hset, hget]
          exact optge_none (some out)
        · have hset : PTree.get s (PTree.set n out st.aval) = PTree.get s st.aval := by
            simpa [heq] using PTree.getSet_equation s n out st.aval
          rw [hset]
          exact optge_refl LATlaws _
      · exact Or.inl ((NSlaws.add_spec n n st.worklist).mpr (Or.inl rfl))
      · intro n' hn'
        exact (NSlaws.add_spec n n' st.worklist).mpr (Or.inr hn')
      · intro n' hn'
        rcases (NSlaws.add_spec n n' st.worklist).mp hn' with h | h
        · exact Or.inl h.symm
        · exact Or.inr h
      · intro n' hn'
        exact Or.inr hn'
      · intro n' hn'
        rcases hn' with h | h
        · exact Or.inl ((NSlaws.add_spec n n' st.worklist).mpr (Or.inl h.symm))
        · exact Or.inr h
      · intro n' hnone hsome
        by_cases heq : n' = n
        · subst n'
          exact Or.inl rfl
        · have hsame : PTree.get n' (PTree.set n out st.aval) = PTree.get n' st.aval := by
            simpa [heq] using PTree.getSet_equation n' n out st.aval
          apply False.elim
          apply hsome
          rw [hsame]
          exact hnone
  | some oldl =>
      by_cases hbeq : LAT.beq oldl (LAT.lub oldl out) = true
      · simp only [hbeq, ↓reduceIte]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hget]
          apply optge_some
          apply LATlaws.ge_trans oldl (LAT.lub oldl out) out
          · exact LATlaws.ge_refl oldl (LAT.lub oldl out)
              (LATlaws.beq_correct oldl (LAT.lub oldl out) hbeq)
          · exact LATlaws.ge_lub_right oldl out
        · intro s hne
          trivial
        · exact fun s => optge_refl LATlaws _
        · exact Or.inr hget
        · exact fun n' h => h
        · exact fun n' h => Or.inr h
        · exact fun n' h => h
        · exact fun n' h => Or.inr h
        · intro n' hnone hsome
          exact False.elim (hsome hnone)
      · have hfalse : LAT.beq oldl (LAT.lub oldl out) = false :=
          Bool.eq_false_iff.mpr hbeq
        simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have hset : PTree.get n (PTree.set n (LAT.lub oldl out) st.aval) =
            some (LAT.lub oldl out) := by
            simpa using PTree.getSet_equation n n (LAT.lub oldl out) st.aval
          rw [hset]
          apply optge_some
          exact LATlaws.ge_lub_right oldl out
        · intro s hne
          have hsn : s ≠ n := fun h => hne h.symm
          simpa [hsn] using PTree.getSet_equation s n (LAT.lub oldl out) st.aval
        · intro s
          by_cases heq : s = n
          · subst s
            have hset : PTree.get n (PTree.set n (LAT.lub oldl out) st.aval) =
                some (LAT.lub oldl out) := by
                simpa using PTree.getSet_equation n n (LAT.lub oldl out) st.aval
            rw [hset, hget]
            apply optge_some
            exact LATlaws.ge_lub_left oldl out
          · have hset : PTree.get s (PTree.set n (LAT.lub oldl out) st.aval) =
              PTree.get s st.aval := by
              simpa [heq] using PTree.getSet_equation s n (LAT.lub oldl out) st.aval
            rw [hset]
            exact optge_refl LATlaws _
        · exact Or.inl ((NSlaws.add_spec n n st.worklist).mpr (Or.inl rfl))
        · intro n' hn'
          exact (NSlaws.add_spec n n' st.worklist).mpr (Or.inr hn')
        · intro n' hn'
          rcases (NSlaws.add_spec n n' st.worklist).mp hn' with h | h
          · exact Or.inl h.symm
          · exact Or.inr h
        · intro n' hn'
          exact Or.inr hn'
        · intro n' hn'
          rcases hn' with h | h
          · exact Or.inl ((NSlaws.add_spec n n' st.worklist).mpr (Or.inl h.symm))
          · exact Or.inr h
        · intro n' hnone hsome
          by_cases heq : n' = n
          · subst n'
            rw [hget] at hnone
            cases hnone
          · have hsame : PTree.get n' (PTree.set n (LAT.lub oldl out) st.aval) =
              PTree.get n' st.aval := by
              simpa [heq] using
                PTree.getSet_equation n' n (LAT.lub oldl out) st.aval
            apply False.elim
            apply hsome
            rw [hsame]
            exact hnone

end CompCert4Lean.Backend.Kildall.Dataflow_Solver

namespace CompCert4Lean.Backend.Kildall.Dataflow_Solver

open CompCert4Lean.Lib.Maps

theorem propagate_succ_list_charact : propagate_succ_list_charactStatement := by
  intro LAT NS LATlaws NSlaws out l
  induction l with
  | nil =>
      intro st
      change
        (∀ n, n ∈ [] → optge LAT (PTree.get n st.aval) (some out)) ∧
          (∀ n, n ∉ [] → PTree.get n st.aval = PTree.get n st.aval) ∧
          (∀ n, optge LAT (PTree.get n st.aval) (PTree.get n st.aval)) ∧
          (∀ n, NS.In n st.worklist ∨ PTree.get n st.aval = PTree.get n st.aval) ∧
          (∀ n', NS.In n' st.worklist → NS.In n' st.worklist) ∧
          (∀ n', NS.In n' st.worklist → n' ∈ [] ∨ NS.In n' st.worklist) ∧
          (∀ n', st.visited n' → st.visited n') ∧
          (∀ n', st.visited n' → NS.In n' st.worklist ∨ st.visited n') ∧
          (∀ n', PTree.get n' st.aval = none → PTree.get n' st.aval ≠ none →
            st.visited n')
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro n hn; cases hn
      · intro n hn; rfl
      · intro n; exact optge_refl LATlaws _
      · intro n; exact Or.inr rfl
      · intro n' hn'; exact hn'
      · intro n' hn'; exact Or.inr hn'
      · intro n' hn'; exact hn'
      · intro n' hn'; exact Or.inr hn'
      · intro n' hnone hsome; exact False.elim (hsome hnone)
  | cons a l ih =>
      intro st
      let st1 := propagate_succ st out a
      let st2 := propagate_succ_list st1 out l
      change
        (∀ n, n ∈ a :: l → optge LAT (PTree.get n st2.aval) (some out)) ∧
          (∀ n, n ∉ a :: l → PTree.get n st2.aval = PTree.get n st.aval) ∧
          (∀ n, optge LAT (PTree.get n st2.aval) (PTree.get n st.aval)) ∧
          (∀ n, NS.In n st2.worklist ∨ PTree.get n st2.aval = PTree.get n st.aval) ∧
          (∀ n', NS.In n' st.worklist → NS.In n' st2.worklist) ∧
          (∀ n', NS.In n' st2.worklist → n' ∈ a :: l ∨ NS.In n' st.worklist) ∧
          (∀ n', st.visited n' → st2.visited n') ∧
          (∀ n', st2.visited n' → NS.In n' st2.worklist ∨ st.visited n') ∧
          (∀ n', PTree.get n' st.aval = none → PTree.get n' st2.aval ≠ none →
            st2.visited n')
      have hA := propagate_succ_charact (LAT := LAT) (NS := NS) LATlaws NSlaws st out a
      have hB := ih st1
      rcases hA with ⟨A1, A2, A3, A4, A5, A6, A7, A8, A9⟩
      rcases hB with ⟨B1, B2, B3, B4, B5, B6, B7, B8, B9⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro n hn
        simp only [List.mem_cons] at hn
        rcases hn with hna | hn
        · cases hna
          exact optge_trans LATlaws _ _ _ (B3 a) A1
        · exact B1 n hn
      · intro n hn
        have hnL : n ∉ l := by
          intro h
          exact hn (by simp [h])
        have hna : a ≠ n := by
          intro h
          exact hn (by simp [h])
        exact (B2 n hnL).trans (A2 n hna)
      · intro n
        exact optge_trans LATlaws _ _ _ (B3 n) (A3 n)
      · intro n
        rcases B4 n with h | h
        · exact Or.inl h
        · by_cases hna : n = a
          · rcases A4 with ha | ha
            · exact Or.inl (by simpa [hna] using B5 a ha)
            · have h' : PTree.get n st2.aval = PTree.get n st1.aval := by
                simpa [hna] using h
              have ha' : PTree.get n st1.aval = PTree.get n st.aval := by
                simpa [hna] using ha
              exact Or.inr (h'.trans ha')
          · exact Or.inr (h.trans (A2 n (fun e => hna e.symm)))
      · intro n' hn'
        exact B5 n' (A5 n' hn')
      · intro n' hn'
        rcases B6 n' hn' with h | h
        · exact Or.inl (List.mem_cons_of_mem a h)
        · rcases A6 n' h with ha | ha
          · exact Or.inl (ha ▸ List.mem_cons_self)
          · exact Or.inr ha
      · intro n' hn'
        exact B7 n' (A7 n' hn')
      · intro n' hn'
        rcases B8 n' hn' with h | h
        · exact Or.inl h
        · rcases A8 n' h with ha | ha
          · exact Or.inl (B5 n' ha)
          · exact Or.inr ha
      · intro n' hnone hsome
        cases hst1 : PTree.get n' st1.aval with
        | none =>
            exact B9 n' hst1 hsome
        | some v =>
            apply B7 n'
            apply A9 n' hnone
            intro hnone1
            rw [hst1] at hnone1
            cases hnone1

end CompCert4Lean.Backend.Kildall.Dataflow_Solver

namespace CompCert4Lean.Backend.Kildall.Dataflow_Solver

open CompCert4Lean.Lib.Maps

theorem fixpoint_from_charact : fixpoint_from_charactStatement := by
  intro A LAT NS LATlaws NSlaws code successors transf start res hfix
  unfold fixpoint_from at hfix
  have hprop := CompCert4Lean.Lib.Iteration.PrimIter.iterate_prop
    (state LAT NS) (PMapT LAT.t)
    (step code successors transf)
    (fun st => steps code successors transf start st)
    (fun result => ∃ st, steps code successors transf start st ∧
      NS.pick st.worklist = none ∧ result = (LAT.bot, st.aval))
    (by
      intro st hst
      cases hstep : step code successors transf st with
      | inl result =>
          unfold step at hstep
          cases hpick : NS.pick st.worklist with
          | none =>
              simp only [hpick] at hstep
              injection hstep with hresult
              subst result
              exact ⟨st, hst, hpick, rfl⟩
          | some pair =>
              cases pair with
              | mk n rem =>
                  cases hcode : PTree.get n code with
                  | none =>
                      simp only [hpick, hcode] at hstep
                      cases hstep
                  | some instr =>
                      simp only [hpick, hcode] at hstep
                      cases hstep
      | inr st' =>
          have hstep_orig := hstep
          unfold step at hstep
          cases hpick : NS.pick st.worklist with
          | none =>
              simp only [hpick] at hstep
              cases hstep
          | some pair =>
              cases pair with
              | mk n rem =>
                  cases hcode : PTree.get n code with
                  | none =>
                      simp only [hpick, hcode] at hstep
                      injection hstep with hst'
                      subst st'
                      exact steps_right start st _ hst hstep_orig
                  | some instr =>
                      simp only [hpick, hcode] at hstep
                      injection hstep with hst'
                      subst st'
                      exact steps_right start st _ hst hstep_orig)
  unfold CompCert4Lean.Lib.Iteration.PrimIter.iterate_propStatement at hprop
  exact hprop start res hfix (steps_base start)

end CompCert4Lean.Backend.Kildall.Dataflow_Solver

namespace CompCert4Lean.Backend.Kildall.Dataflow_Solver

open CompCert4Lean.Lib.Maps

theorem step_incr : step_incrStatement := by
  intro A LAT NS LATlaws NSlaws code successors transf n s1 s2 hstep
  unfold step at hstep
  cases hpick : NS.pick s1.worklist with
  | none =>
      simp only [hpick] at hstep
      cases hstep
  | some pair =>
      rcases pair with ⟨p, rem⟩
      cases hcode : PTree.get p code with
      | none =>
          simp only [hpick, hcode] at hstep
          injection hstep with hs2
          subst s2
          constructor
          · exact optge_refl LATlaws _
          · intro hv
            exact hv
      | some instr =>
          simp only [hpick, hcode] at hstep
          injection hstep with hs2
          subst s2
          have hprop := propagate_succ_list_charact
            (LAT := LAT) (NS := NS) LATlaws NSlaws
            (transf p (abstr_value p s1)) (successors instr)
            ({ aval := s1.aval, worklist := rem, visited := s1.visited } : state LAT NS)
          rcases hprop with ⟨A1, A2, A3, A4, A5, A6, A7, A8, A9⟩
          constructor
          · exact A3 n
          · intro hv
            exact A7 n hv

end CompCert4Lean.Backend.Kildall.Dataflow_Solver

namespace CompCert4Lean.Backend.Kildall.Dataflow_Solver

open CompCert4Lean.Lib.Maps

theorem steps_incr : steps_incrStatement := by
  intro A LAT NS LATlaws NSlaws code successors transf n s1 s2 hsteps
  induction hsteps with
  | steps_base =>
      constructor
      · exact optge_refl LATlaws _
      · intro hv
        exact hv
  | steps_right =>
      rename_i s2' s3' hprev hstep ih
      have hstep' := step_incr (LAT := LAT) (NS := NS) LATlaws NSlaws
        code successors transf n s2' s3' hstep
      rcases ih with ⟨hprev_ge, hprev_vis⟩
      rcases hstep' with ⟨hstep_ge, hstep_vis⟩
      constructor
      · exact optge_trans LATlaws _ _ _ hstep_ge hprev_ge
      · intro hv
        exact hstep_vis (hprev_vis hv)

end CompCert4Lean.Backend.Kildall.Dataflow_Solver

namespace CompCert4Lean.Backend.Kildall.Dataflow_Solver

open CompCert4Lean.Lib.Maps

theorem step_state_good : step_state_goodStatement := by
  intro A LAT NS LATlaws NSlaws code successors transf st pc rem instr hpick hcode hgood
  rcases hgood with ⟨hstable, hdefined⟩
  have hprop := propagate_succ_list_charact (LAT := LAT) (NS := NS) LATlaws NSlaws
    (transf pc (abstr_value pc st)) (successors instr)
    ({ aval := st.aval, worklist := rem, visited := st.visited } : state LAT NS)
  rcases hprop with ⟨A1, A2, A3, A4, A5, A6, A7, A8, A9⟩
  constructor
  · intro n hnvis
    rcases A8 n hnvis with hnwork | hnvis
    · exact Or.inl hnwork
    · rcases A4 n with hnwork | haval
      · exact Or.inl hnwork
      · have haval' : PTree.get n
            (propagate_succ_list
              { aval := st.aval, worklist := rem, visited := st.visited }
              (transf pc (abstr_value pc st)) (successors instr)).aval =
            PTree.get n st.aval := haval
        have habstr : abstr_value n
            (propagate_succ_list
              { aval := st.aval, worklist := rem, visited := st.visited }
              (transf pc (abstr_value pc st)) (successors instr)) =
            abstr_value n st := by
          exact congrArg (fun ov : Option LAT.t =>
            match ov with
            | none => LAT.bot
            | some v => v) haval'
        rcases hstable n hnvis with hwork | hstable
        · rcases (NSlaws.pick_some st.worklist pc rem hpick n).mp hwork with hpc | hrem
          · subst n
            right
            rw [habstr]
            intro i s hget hsucc
            have hinstr : i = instr := by
              rw [hcode] at hget
              exact (Option.some.inj hget).symm
            subst i
            simpa using A1 s hsucc
          · exact Or.inl (A5 n hrem)
        · right
          rw [habstr]
          intro i s hget hsucc
          exact optge_trans LATlaws _ _ _ (A3 s) (hstable i s hget hsucc)
  · intro n v hget
    cases hold : PTree.get n st.aval with
    | none =>
        exact A9 n hold (by
          intro hnone
          rw [hnone] at hget
          cases hget)
    | some old =>
        exact A7 n (hdefined n old hold)

end CompCert4Lean.Backend.Kildall.Dataflow_Solver

namespace CompCert4Lean.Backend.Kildall.Dataflow_Solver

theorem step_state_good_2 : step_state_good_2Statement := by
  intro A LAT NS LATlaws NSlaws code successors transf st pc rem hgood hpick hcode
  rcases hgood with ⟨hstable, hdefined⟩
  constructor
  · intro n hnvis
    rcases hstable n hnvis with hwork | hstable'
    · rcases (NSlaws.pick_some st.worklist pc rem hpick n).mp hwork with hpc | hrem
      · subst n
        right
        intro i s hget hsucc
        rw [hcode] at hget
        cases hget
      · exact Or.inl hrem
    · right
      exact hstable'
  · intro n v hget
    exact hdefined n v hget

end CompCert4Lean.Backend.Kildall.Dataflow_Solver

namespace CompCert4Lean.Backend.Kildall.Dataflow_Solver

open CompCert4Lean.Lib.Maps

theorem steps_state_good : steps_state_goodStatement := by
  intro A LAT NS LATlaws NSlaws code successors transf st1 st2 hsteps hgood
  induction hsteps with
  | steps_base =>
      exact hgood
  | steps_right s2 s3 hprev hstep ih =>
      unfold step at hstep
      cases hpick : NS.pick s2.worklist with
      | none =>
          simp only [hpick] at hstep
          cases hstep
      | some pair =>
          rcases pair with ⟨n, rem⟩
          cases hcode : PTree.get n code with
          | none =>
              simp only [hpick, hcode] at hstep
              injection hstep with hs3
              subst s3
              exact step_state_good_2 (LAT := LAT) (NS := NS)
                LATlaws NSlaws code successors transf s2 n rem ih hpick hcode
          | some instr =>
              simp only [hpick, hcode] at hstep
              injection hstep with hs3
              subst s3
              exact step_state_good (LAT := LAT) (NS := NS)
                LATlaws NSlaws code successors transf s2 n rem instr hpick hcode ih

end CompCert4Lean.Backend.Kildall.Dataflow_Solver
