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
