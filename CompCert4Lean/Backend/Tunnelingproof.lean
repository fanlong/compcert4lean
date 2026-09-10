import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Backend.Tunneling
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Smallstep

/-!
# Correctness surface for branch tunneling

The executable definitions in this module mirror the source proof module.
Proof obligations are recorded as transparent proposition descriptors for the
later proof-migration phase; no theorem placeholder is introduced here.
-/

namespace CompCert4Lean.Backend.Tunnelingproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Specif
open CompCert4Lean.Backend.LTL
open CompCert4Lean.Backend.Tunneling
open CompCert4Lean.Backend.Locations
open CompCert4Lean.X86.Machregs
open CompCert4Lean.X86.Op
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig

private def peqNode (x y : node) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) :=
  U.elt_eq x y

/-! ## Program matching and branch-map definitions -/

def match_prog (p tp : program) : Prop :=
  @match_program fundef Unit fundef Unit
    (Linker_fundef function) Linker_unit
    (fun _ f tf => tf = tunnel_fundef f)
    (fun x y : Unit => x = y) p tp

def measure_branch (u : U.t) (pc s : node) (f : node → Nat) : node → Nat :=
  fun x =>
    match peqNode (U.repr u s) pc with
    | .left _ => f x
    | .right _ =>
        match peqNode (U.repr u x) pc with
        | .left _ => f x + f s + 1
        | .right _ => f x

def measure_cond (u : U.t) (pc s1 s2 : node) (f : node → Nat) : node → Nat :=
  fun x =>
    match peqNode (U.repr u s1) pc with
    | .left _ => f x
    | .right _ =>
        match peqNode (U.repr u x) pc with
        | .left _ => f x + Nat.max (f s1) (f s2) + 1
        | .right _ => f x

def branch_map_correct_1 (c : code) (u : U.t) (f : node → Nat) : Prop :=
  ∀ pc,
    match PTree.get pc c with
    | some (Lbranch s :: _) =>
        U.repr u pc = pc ∨ (U.repr u pc = U.repr u s ∧ f s < f pc)
    | _ => U.repr u pc = pc

def branch_map_correct_2 (fn : function) (c : code) (u : U.t)
    (f : node → Nat) : Prop :=
  ∀ pc,
    match PTree.get pc fn.fn_code with
    | some (Lbranch s :: _) =>
        U.repr u pc = pc ∨ (U.repr u pc = U.repr u s ∧ f s < f pc)
    | some (Lcond _cond _args s1 s2 :: _) =>
        U.repr u pc = pc ∨
          (PTree.get pc c = none ∧ U.repr u pc = U.repr u s1 ∧
            U.repr u pc = U.repr u s2 ∧ f s1 < f pc ∧ f s2 < f pc)
    | _ => U.repr u pc = pc

def code_compat (fn : function) (c : code) : Prop :=
  ∀ pc b, PTree.get pc c = some b → PTree.get pc fn.fn_code = some b

def code_invariant (c0 c1 c2 : code) : Prop :=
  ∀ pc, PTree.get pc c0 = none → PTree.get pc c1 = PTree.get pc c2

def branch_map_correct (fn : function) (u : U.t) (f : node → Nat) : Prop :=
  ∀ pc,
    match PTree.get pc fn.fn_code with
    | some (Lbranch s :: _) =>
        U.repr u pc = pc ∨ (U.repr u pc = U.repr u s ∧ f s < f pc)
    | some (Lcond _cond _args s1 s2 :: _) =>
        U.repr u pc = pc ∨
          (U.repr u pc = U.repr u s1 ∧ U.repr u pc = U.repr u s2 ∧
            f s1 < f pc ∧ f s2 < f pc)
    | _ => U.repr u pc = pc

def branch_target (fn : function) (pc : node) : node :=
  U.repr (record_gotos fn) pc

/-! The source witness is computational: proof erasure removes only its
correctness field, while retaining the function built by the two folds.  Keep
that executable carrier separate from the source-shaped result descriptor. -/

private def record_branch_measure
    (st : U.t × (node → Nat)) (pc : node) (b : bblock) : U.t × (node → Nat) :=
  match b with
  | Lbranch s :: _ =>
      (U.union st.1 pc s, measure_branch st.1 pc s st.2)
  | _ => st

private def record_branches_measure (fn : function) : U.t × (node → Nat) :=
  PTree.fold record_branch_measure fn.fn_code (U.empty, fun _ => 0)

private def record_cond_measure
    (st : (((code × U.t) × Bool) × (node → Nat)))
    (pc : node) (b : bblock) : (((code × U.t) × Bool) × (node → Nat)) :=
  let next := record_cond st.1 pc b
  match b with
  | Lcond _cond _args s1 s2 :: _ =>
      match peqNode (U.repr st.1.1.2 s1) (U.repr st.1.1.2 s2) with
      | .left _ => (next, measure_cond st.1.1.2 pc s1 s2 st.2)
      | .right _ => (next, st.2)
  | _ => (next, st.2)

private def record_conds_1_witness (cu : code × U.t) (f : node → Nat) :
    node → Nat :=
  (PTree.fold record_cond_measure cu.1 (((cu.1, cu.2), false), f)).2

private def record_conds_1_measure (cu : code × U.t) (f : node → Nat) :
    (((code × U.t) × Bool) × (node → Nat)) :=
  (record_conds_1 cu, record_conds_1_witness cu f)

private abbrev cond_measure_state := (code × U.t) × (node → Nat)

private def record_conds_measure_rel
    (s' s : cond_measure_state) : Prop :=
  PTree_Properties.cardinal s'.1.1 < PTree_Properties.cardinal s.1.1

private theorem record_conds_measure_rel_wf :
    WellFounded record_conds_measure_rel := by
  exact InvImage.wf
    (fun s : cond_measure_state => PTree_Properties.cardinal s.1.1)
    Nat.lt_wfRel.wf

private theorem record_conds_measure_termination :
    ∀ (cu : code × U.t) (f : node → Nat),
      (record_conds_1_measure cu f).1.2 = true →
        PTree_Properties.cardinal (record_conds_1_measure cu f).1.1.1 <
          PTree_Properties.cardinal cu.1 := by
  intro cu f hchanged
  rcases cu with ⟨c0, u0⟩
  let P : code → ((code × U.t) × Bool) → Prop := fun c s =>
    (∀ pc, PTree.get pc c = none → PTree.get pc s.1.1 = PTree.get pc c0) ∧
      (PTree_Properties.cardinal s.1.1 + (if s.2 then 1 else 0) ≤
        PTree_Properties.cardinal c0)
  have hfold : P c0 (PTree.fold record_cond c0 ((c0, u0), false)) := by
    apply PTree_Properties.fold_rec_proof
    · intro m m' a hget hP
      refine ⟨?_, hP.2⟩
      intro pc hnone
      exact hP.1 pc (by
        rw [hget pc]
        exact hnone)
    · constructor
      · intro pc hnone
        simpa [PTree.get] using hnone
      · simp [PTree_Properties.cardinal, PTree.elements, PTree.xelements]
    · intro m a k b hnone hsome hP
      rcases a with ⟨⟨c, u⟩, changed⟩
      change PTree.tree bblock at c
      unfold P at hP ⊢
      change
        (∀ pc, PTree.get pc m = none → PTree.get pc c = PTree.get pc c0) ∧
          (PTree_Properties.cardinal c + (if changed = true then 1 else 0) ≤
            PTree_Properties.cardinal c0) at hP
      have hset_none :
          ∀ pc v, PTree.get pc (PTree.set k v m) = none →
            PTree.get pc m = none := by
        intro pc v hpc
        have hset := PTree.getSet_equation (A := bblock) pc k v m
        rw [hset] at hpc
        split at hpc <;> simp_all
      have hpreserve :
          ∀ pc, PTree.get pc (PTree.set k b m) = none →
            PTree.get pc c = PTree.get pc c0 := by
        intro pc hpc
        exact hP.1 pc (hset_none pc b hpc)
      cases b with
      | nil =>
          simp [record_cond]
          exact ⟨hpreserve, hP.2⟩
      | cons instr tail =>
          cases instr with
          | Lop op args res =>
              simp [record_cond]
              exact ⟨hpreserve, hP.2⟩
          | Lload chunk addr args dst =>
              simp [record_cond]
              exact ⟨hpreserve, hP.2⟩
          | Lgetstack sl ofs ty dst =>
              simp [record_cond]
              exact ⟨hpreserve, hP.2⟩
          | Lsetstack src sl ofs ty =>
              simp [record_cond]
              exact ⟨hpreserve, hP.2⟩
          | Lstore chunk addr args src =>
              simp [record_cond]
              exact ⟨hpreserve, hP.2⟩
          | Lcall sig ros =>
              simp [record_cond]
              exact ⟨hpreserve, hP.2⟩
          | Ltailcall sig ros =>
              simp [record_cond]
              exact ⟨hpreserve, hP.2⟩
          | Lbuiltin ef args res =>
              simp [record_cond]
              exact ⟨hpreserve, hP.2⟩
          | Lbranch succ =>
              simp [record_cond]
              exact ⟨hpreserve, hP.2⟩
          | Lcond cond args s1 s2 =>
              unfold record_cond
              cases hpeq : peq (U.repr u s1) (U.repr u s2) with
              | right hneq =>
                  simp [hpeq]
                  exact ⟨hpreserve, hP.2⟩
              | left heq =>
                  simp [hpeq]
                  let block : bblock := Lcond cond args s1 s2 :: tail
                  have hsome_block : PTree.get k c0 = some block := by
                    simpa [block] using hsome
                  have hcode : PTree.get k c = some block := by
                    rw [hP.1 k hnone]
                    exact hsome_block
                  have hcard := PTree_Properties.cardinal_remove_proof
                    (V := bblock) k c block hcode
                  refine ⟨?_, ?_⟩
                  · intro pc hpc
                    let block : bblock := Lcond cond args s1 s2 :: tail
                    have hpc_block :
                        PTree.get pc (PTree.set k block m) = none := by
                      simpa [block] using hpc
                    have hpc_ne : pc ≠ k := by
                      intro heqpc
                      subst pc
                      have hset := PTree.getSet_equation
                        (A := bblock) k k block m
                      rw [hset] at hpc_block
                      simp at hpc_block
                    have hpc' : PTree.get pc m = none :=
                      hset_none pc block hpc_block
                    have hremove := @PTree.getRemove_equation bblock pc k c
                    calc
                      PTree.get pc (PTree.remove k c) = PTree.get pc c := by
                        rw [hremove]
                        simp [hpc_ne]
                      _ = PTree.get pc c0 := hP.1 pc hpc'
                  · omega
          | Ljumptable arg tbl =>
              simp [record_cond]
              exact ⟨hpreserve, hP.2⟩
          | Lreturn =>
              simp [record_cond]
              exact ⟨hpreserve, hP.2⟩
  let c0tree : PTree.tree bblock := c0
  have hchanged' :
      (PTree.fold record_cond c0tree ((c0tree, u0), false)).2 = true := by
    simpa [record_conds_1_measure, record_conds_1, c0tree] using hchanged
  have hbound :
      PTree_Properties.cardinal
          (PTree.fold record_cond c0tree ((c0tree, u0), false)).1.1 +
        (if (PTree.fold record_cond c0tree ((c0tree, u0), false)).2 = true then 1 else 0) ≤
      PTree_Properties.cardinal c0tree := by
    simpa [c0tree, Prod.fst, Prod.snd] using hfold.2
  simp [hchanged'] at hbound
  have hlt :
      PTree_Properties.cardinal
          (PTree.fold record_cond c0tree ((c0tree, u0), false)).1.1 <
        PTree_Properties.cardinal c0tree := by
    omega
  simpa [record_conds_1_measure, record_conds_1, c0tree] using hlt

private def record_conds_measure_wf
    (cu : cond_measure_state) : U.t × (node → Nat) :=
  WellFounded.fix record_conds_measure_rel_wf (fun cu rec =>
    let result := record_conds_1_measure cu.1 cu.2
    match hchanged : result.1.2 with
    | true =>
      rec (result.1.1, result.2)
        (record_conds_measure_termination cu.1 cu.2 (by simpa [hchanged]))
    | false =>
      (cu.1.2, cu.2)) cu

private def record_gotos_measure (fn : function) : U.t × (node → Nat) :=
  let branches := record_branches_measure fn
  record_conds_measure_wf ((fn.fn_code, branches.1), branches.2)

/-! This is the executable companion for the source `proj1_sig` witness.
The correctness field is deliberately a separate obligation: until proof
grinding supplies a value of `record_gotos_correct_1Statement`, the executable
provider must not fabricate one. -/
structure record_gotos_correct_1_companion (fn : function) : Type where
  witness : node → Nat

def record_gotos_correct_1_provider (fn : function) :
    record_gotos_correct_1_companion fn :=
  { witness := (record_gotos_measure fn).2 }

def record_gotos_correct_1_projection (fn : function) : node → Nat :=
  (record_gotos_correct_1_provider fn).witness

def record_gotos_correct_1_bridge (fn : function) : Prop :=
  branch_map_correct fn (record_gotos fn)
    (record_gotos_correct_1_projection fn)

def count_gotos (fn : function) (pc : node) : Nat :=
  record_gotos_correct_1_projection fn pc

def tunneled_block (f : function) (b : bblock) : bblock :=
  tunnel_block (record_gotos f) b

def locmap_lessdef (ls1 ls2 : locset) : Prop :=
  ∀ l, Val.lessdef (ls1 l) (ls2 l)

inductive match_stackframes : stackframe → stackframe → Prop where
  | intro (f : function) (sp : val) (ls0 : locset) (bb : bblock)
      (tls0 : locset) :
      locmap_lessdef ls0 tls0 →
      match_stackframes
        (Stackframe f sp ls0 bb)
        (Stackframe (tunnel_function f) sp tls0 (tunneled_block f bb))

/-! Authenticated source constructor endpoint.  Keep the relation's existing
constructor while exposing its reconciled flat identity. -/
abbrev match_stackframes_intro := @match_stackframes.intro

inductive match_states : state → state → Prop where
  | intro (s : List stackframe) (f : function) (sp : val) (pc : node)
      (ls : locset) (m : mem) (ts : List stackframe) (tls : locset)
      (tm : mem) :
      list_forall2 match_stackframes s ts →
      locmap_lessdef ls tls →
      Mem.extends m tm →
      match_states (State s f sp pc ls m)
        (State ts (tunnel_function f) sp (branch_target f pc) tls tm)
  | block (s : List stackframe) (f : function) (sp : val) (bb : bblock)
      (ls : locset) (m : mem) (ts : List stackframe) (tls : locset)
      (tm : mem) :
      list_forall2 match_stackframes s ts →
      locmap_lessdef ls tls →
      Mem.extends m tm →
      match_states (Block s f sp bb ls m)
        (Block ts (tunnel_function f) sp (tunneled_block f bb) tls tm)
  | interm_branch (s : List stackframe) (f : function) (sp : val)
      (pc : node) (bb : bblock) (ls : locset) (m : mem)
      (ts : List stackframe) (tls : locset) (tm : mem) :
      list_forall2 match_stackframes s ts →
      locmap_lessdef ls tls →
      Mem.extends m tm →
      match_states (Block s f sp (Lbranch pc :: bb) ls m)
        (State ts (tunnel_function f) sp (branch_target f pc) tls tm)
  | interm_cond (s : List stackframe) (f : function) (sp : val)
      (cond : condition) (args : List mreg) (pc1 pc2 : node) (bb : bblock)
      (ls : locset) (m : mem) (ts : List stackframe) (tls : locset)
      (tm : mem) :
      list_forall2 match_stackframes s ts →
      locmap_lessdef ls tls →
      Mem.extends m tm →
      branch_target f pc1 = branch_target f pc2 →
      match_states
        (Block s f sp (Lcond cond args pc1 pc2 :: bb) ls m)
        (State ts (tunnel_function f) sp (branch_target f pc1) tls tm)
  | call (s : List stackframe) (f : fundef) (ls : locset) (m : mem)
      (ts : List stackframe) (tls : locset) (tm : mem) :
      list_forall2 match_stackframes s ts →
      locmap_lessdef ls tls →
      Mem.extends m tm →
      match_states (Callstate s f ls m)
        (Callstate ts (tunnel_fundef f) tls tm)
  | return (s : List stackframe) (ls : locset) (m : mem)
      (ts : List stackframe) (tls : locset) (tm : mem) :
      list_forall2 match_stackframes s ts →
      locmap_lessdef ls tls →
      Mem.extends m tm →
      match_states (Returnstate s ls m) (Returnstate ts tls tm)

/-! Authenticated source constructor endpoints; these aliases preserve the
exact relation propositions and constructor obligations above. -/
abbrev match_states_intro := @match_states.intro
abbrev match_states_block := @match_states.block
abbrev match_states_interm_branch := @match_states.interm_branch
abbrev match_states_interm_cond := @match_states.interm_cond
abbrev match_states_call := @match_states.call
abbrev match_states_return := @match_states.return

def measure : state → Nat
  | State _ f _ pc _ _ => count_gotos f pc * 2
  | Block _ f _ (Lbranch pc :: _) _ _ => count_gotos f pc * 2 + 1
  | Block _ f _ (Lcond _ _ pc1 pc2 :: _) _ _ =>
      Nat.max (count_gotos f pc1) (count_gotos f pc2) * 2 + 1
  | Block _ _ _ _ _ _ => 0
  | Callstate _ _ _ _ => 0
  | Returnstate _ _ _ => 0

/-! ## Exact statement descriptors for later proof migration -/

def transf_program_matchStatement : Prop :=
  ∀ p : program, match_prog p (tunnel_program p)

def record_branch_correctStatement : Type :=
  ∀ (c : code) (u : U.t) (f : node → Nat) (pc : node) (b : bblock),
    branch_map_correct_1 (PTree.remove pc c) u f →
    PTree.get pc c = some b →
    sig (fun f' : node → Nat =>
      branch_map_correct_1 c (record_branch u pc b) f')

def record_branches_correctStatement : Type :=
  ∀ fn : function,
    sig (fun f : node → Nat =>
      branch_map_correct_1 fn.fn_code (record_branches fn) f)

def record_cond_correctStatement : Type :=
  ∀ (fn : function) (c : code) (u : U.t) (changed : Bool)
    (f : node → Nat) (pc : node) (b : bblock),
    branch_map_correct_2 fn c u f →
    PTree.get pc fn.fn_code = some b →
    PTree.get pc c ≠ none →
    sig (fun f' : node → Nat =>
      branch_map_correct_2 fn
        (record_cond ((c, u), changed) pc b).1.1
        (record_cond ((c, u), changed) pc b).1.2 f')

def record_conds_1_correctStatement : Type :=
  ∀ (fn : function) (c : code) (u : U.t) (f : node → Nat),
    branch_map_correct_2 fn c u f →
      code_compat fn c →
      -- `PLift` keeps the Coq proof component inside this Type-level product.
      PLift (code_compat fn (record_conds_1 (c, u)).1.1) ×
      sig (fun f' : node → Nat =>
        branch_map_correct_2 fn
          (record_conds_1 (c, u)).1.1 (record_conds_1 (c, u)).1.2 f')

def record_conds_correctStatement : Type :=
  ∀ (fn : function) (cu : code × U.t),
    sig (fun f : node → Nat => branch_map_correct_2 fn cu.1 cu.2 f) →
    code_compat fn cu.1 →
    sig (fun f : node → Nat =>
      branch_map_correct fn (record_conds cu) f)

def record_gotos_correct_1Statement : Type :=
  ∀ fn : function,
    sig (fun f : node → Nat => branch_map_correct fn (record_gotos fn) f)

def record_gotos_correctStatement : Prop :=
  ∀ (fn : function) (pc : node),
    match PTree.get pc fn.fn_code with
    | some (Lbranch s :: _) =>
        branch_target fn pc = pc ∨
          (branch_target fn pc = branch_target fn s ∧
            count_gotos fn s < count_gotos fn pc)
    | some (Lcond _cond _args s1 s2 :: _) =>
        branch_target fn pc = pc ∨
          (branch_target fn pc = branch_target fn s1 ∧
            branch_target fn pc = branch_target fn s2 ∧
            count_gotos fn s1 < count_gotos fn pc ∧
            count_gotos fn s2 < count_gotos fn pc)
    | _ => branch_target fn pc = pc

def functions_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ (v : val) (f : fundef),
      Genv.find_funct (Genv.globalenv prog) v = some f →
      Genv.find_funct (Genv.globalenv tprog) v = some (tunnel_fundef f)

def function_ptr_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ (v : block) (f : fundef),
      Genv.find_funct_ptr (Genv.globalenv prog) v = some f →
      Genv.find_funct_ptr (Genv.globalenv tprog) v = some (tunnel_fundef f)

def symbols_preservedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ id, Genv.find_symbol (Genv.globalenv tprog) id =
      Genv.find_symbol (Genv.globalenv prog) id

def senv_preservedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    Senv.equiv (Genv.to_senv (Genv.globalenv prog))
      (Genv.to_senv (Genv.globalenv tprog))

def sig_preservedStatement : Prop :=
  ∀ f : fundef, funsig (tunnel_fundef f) = funsig f

def reglist_lessdefStatement : Prop :=
  ∀ (rl : List mreg) (ls1 ls2 : locset),
    locmap_lessdef ls1 ls2 →
    Val.lessdef_list (reglist ls1 rl) (reglist ls2 rl)

def locmap_set_lessdefStatement : Prop :=
  ∀ (ls1 ls2 : locset) (v1 v2 : val) (l : loc),
    locmap_lessdef ls1 ls2 → Val.lessdef v1 v2 →
    locmap_lessdef (Locmap.set l v1 ls1) (Locmap.set l v2 ls2)

def locmap_set_undef_lessdefStatement : Prop :=
  ∀ (ls1 ls2 : locset) (l : loc), locmap_lessdef ls1 ls2 →
    locmap_lessdef (Locmap.set l Vundef ls1) ls2

def locmap_undef_regs_lessdefStatement : Prop :=
  ∀ (rl : List mreg) (ls1 ls2 : locset), locmap_lessdef ls1 ls2 →
    locmap_lessdef (undef_regs rl ls1) (undef_regs rl ls2)

def locmap_undef_regs_lessdef_1Statement : Prop :=
  ∀ (rl : List mreg) (ls1 ls2 : locset), locmap_lessdef ls1 ls2 →
    locmap_lessdef (undef_regs rl ls1) ls2

def locmap_getpair_lessdefStatement : Prop :=
  ∀ (p : rpair loc) (ls1 ls2 : locset), locmap_lessdef ls1 ls2 →
    Val.lessdef (Locmap.getpair p ls1) (Locmap.getpair p ls2)

def locmap_getpairs_lessdefStatement : Prop :=
  ∀ (pl : List (rpair loc)) (ls1 ls2 : locset), locmap_lessdef ls1 ls2 →
    Val.lessdef_list (pl.map (fun p => Locmap.getpair p ls1))
      (pl.map (fun p => Locmap.getpair p ls2))

def locmap_setpair_lessdefStatement : Prop :=
  ∀ (p : rpair mreg) (ls1 ls2 : locset) (v1 v2 : val),
    locmap_lessdef ls1 ls2 → Val.lessdef v1 v2 →
    locmap_lessdef (Locmap.setpair p v1 ls1) (Locmap.setpair p v2 ls2)

def locmap_setres_lessdefStatement : Prop :=
  ∀ (res : builtin_res mreg) (ls1 ls2 : locset) (v1 v2 : val),
    locmap_lessdef ls1 ls2 → Val.lessdef v1 v2 →
    locmap_lessdef (Locmap.setres res v1 ls1) (Locmap.setres res v2 ls2)

def locmap_undef_caller_save_regs_lessdefStatement : Prop :=
  ∀ (cfg : CompilerConfig) (ls1 ls2 : locset), locmap_lessdef ls1 ls2 →
    locmap_lessdef (undef_caller_save_regs cfg ls1)
      (undef_caller_save_regs cfg ls2)

def find_function_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ (ros : Sum mreg ident) (ls tls : locset) (fd : fundef),
      locmap_lessdef ls tls →
      find_function (Genv.globalenv prog) ros ls = some fd →
      find_function (Genv.globalenv tprog) ros tls = some (tunnel_fundef fd)

def call_regs_lessdefStatement : Prop :=
  ∀ (ls1 ls2 : locset), locmap_lessdef ls1 ls2 →
    locmap_lessdef (call_regs ls1) (call_regs ls2)

def return_regs_lessdefStatement : Prop :=
  ∀ (cfg : CompilerConfig) (caller1 callee1 caller2 callee2 : locset),
    locmap_lessdef caller1 caller2 → locmap_lessdef callee1 callee2 →
    locmap_lessdef (return_regs cfg caller1 callee1)
      (return_regs cfg caller2 callee2)

def match_parent_locsetStatement : Prop :=
  ∀ (s ts : List stackframe),
    list_forall2 match_stackframes s ts →
    locmap_lessdef (parent_locset s) (parent_locset ts)

def tunnel_step_correctStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog tprog : program),
    match_prog prog tprog →
    ∀ (st1 : state) (t : trace) (st2 : state),
      step (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg xi (Genv.globalenv prog) st1 t st2 →
      ∀ st1', match_states st1 st1' →
        (∃ st2',
          step (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            cfg xi (Genv.globalenv tprog) st1' t st2' ∧
          match_states st2 st2') ∨
        (measure st2 < measure st1 ∧ t = E0 ∧ match_states st2 st1')

def transf_initial_statesStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ st1, initial_state prog st1 →
      ∃ st2, initial_state tprog st2 ∧ match_states st1 st2

def transf_final_statesStatement : Prop :=
  ∀ (st1 st2 : state) (r : CompCert4Lean.Lib.Integers.int),
    match_states st1 st2 → final_state st1 r → final_state st2 r

def transf_program_correctStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog tprog : program),
    match_prog prog tprog →
    forward_simulation
      (semantics (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg xi prog)
      (semantics (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg xi tprog)

end CompCert4Lean.Backend.Tunnelingproof

namespace CompCert4Lean.Backend.Tunnelingproof

open CompCert4Lean.Backend.Tunneling
open CompCert4Lean.Backend.LTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib

theorem transf_program_match : transf_program_matchStatement := by
  letI : Linker fundef := Linker_fundef function
  letI : Linker program := Linker_prog fundef Unit
  intro p
  unfold match_prog tunnel_program
    CompCert4Lean.Common.AST.transform_program
  constructor
  · induction p.prog_defs with
    | nil => exact list_forall2.nil _
    | cons hd tl ih =>
        cases hd with
        | mk id gd =>
            cases gd with
            | Gfun f =>
                change list_forall2 _
                  ((id, Gfun f) :: tl)
                  ((id, Gfun (tunnel_fundef f)) ::
                    List.map (transform_program_globdef tunnel_fundef) tl)
                apply list_forall2.cons
                · constructor
                  · rfl
                  · apply match_globdef.match_globdef_fun (ctx' := p)
                    · exact linkorder_refl _
                    · rfl
                · exact ih
            | Gvar v =>
                change list_forall2 _
                  ((id, Gvar v) :: tl)
                  ((id, Gvar v) ::
                    List.map (transform_program_globdef tunnel_fundef) tl)
                apply list_forall2.cons
                · constructor
                  · rfl
                  · apply match_globdef.match_globdef_var
                    exact match_globvar.match_globvar_intro _ _ _ _ _ _ rfl
                · exact ih
  · exact ⟨rfl, rfl⟩

end CompCert4Lean.Backend.Tunnelingproof

namespace CompCert4Lean.Backend.Tunnelingproof

open CompCert4Lean.Backend.Tunneling
open CompCert4Lean.Backend.LTL
open CompCert4Lean.Lib.UnionFind
open CompCert4Lean.Lib.Maps

private theorem tunnel_map_get_set {M : MAP} {A : Type} (x y : M.elt)
    (v : A) (m : M.t A) :
    M.get x (M.set y v m) = if _h : x = y then some v else M.get x m := by
  rw [M.gsspec]
  cases hxy : M.elt_eq x y with
  | left h => simp [h]
  | right h => simp [h]

private theorem tunnel_repr_res_none {M : MAP} (uf : UF.t M) (a : UF.elt M) :
    M.get (UF.repr M uf a) uf.m = none := by
  apply uf.mwf.induction a
  intro x ih
  rw [UF.repr_unroll_proof M uf x]
  cases h : M.get x uf.m with
  | none => simpa [h]
  | some y => simpa [h] using ih y (by
      change M.get x uf.m = some y
      exact h)

private theorem tunnel_repr_canonical {M : MAP} (uf : UF.t M) (a : UF.elt M) :
    UF.repr M uf (UF.repr M uf a) = UF.repr M uf a := by
  rw [UF.repr_none_proof M uf (UF.repr M uf a) (tunnel_repr_res_none uf a)]

private theorem tunnel_repr_none {M : MAP} (uf : UF.t M) (a : UF.elt M)
    (h : M.get a uf.m = none) : UF.repr M uf a = a :=
  UF.repr_none_proof M uf a h

private theorem tunnel_repr_some {M : MAP} (uf : UF.t M) (a a' : UF.elt M)
    (h : M.get a uf.m = some a') : UF.repr M uf a = UF.repr M uf a' :=
  UF.repr_some_proof M uf a a' h

private theorem tunnel_repr_identify_1 {M : MAP} (uf : UF.t M) (a b : UF.elt M)
    (ha : M.get a uf.m = none) (hn : UF.repr M uf b ≠ a) (x : UF.elt M)
    (hx : UF.repr M uf x ≠ a) :
    UF.repr M (UF.identify M uf a b ha hn) x = UF.repr M uf x := by
  revert hx
  apply (UF.identify M uf a b ha hn).mwf.induction x
  intro x ih hx
  rw [UF.repr_unroll_proof M (UF.identify M uf a b ha hn) x]
  cases hnew : M.get x (UF.identify M uf a b ha hn).m with
  | none =>
      simp only [hnew]
      change M.get x (M.set a b uf.m) = none at hnew
      rw [tunnel_map_get_set] at hnew
      by_cases hxa : x = a
      · subst x
        simp at hnew
      · simp [hxa] at hnew
        exact (tunnel_repr_none uf x hnew).symm
  | some y =>
      simp only [hnew]
      change M.get x (M.set a b uf.m) = some y at hnew
      rw [tunnel_map_get_set] at hnew
      by_cases hxa : x = a
      · subst x
        simp at hnew
        subst y
        exact False.elim (hx (tunnel_repr_none uf a ha))
      · simp [hxa] at hnew
        have hy : UF.repr M uf y ≠ a := by
          intro hya
          apply hx
          exact (tunnel_repr_some uf x y hnew).trans hya
        exact (ih y (by
          change M.get x (M.set a b uf.m) = some y
          rw [tunnel_map_get_set]
          simp [hxa, hnew]) hy).trans (tunnel_repr_some uf x y hnew).symm

private theorem tunnel_repr_identify_2 {M : MAP} (uf : UF.t M) (a b : UF.elt M)
    (ha : M.get a uf.m = none) (hn : UF.repr M uf b ≠ a) (x : UF.elt M)
    (hx : UF.repr M uf x = a) :
    UF.repr M (UF.identify M uf a b ha hn) x = UF.repr M uf b := by
  revert hx
  apply (UF.identify M uf a b ha hn).mwf.induction x
  intro x ih hx
  rw [UF.repr_unroll_proof M (UF.identify M uf a b ha hn) x]
  cases hnew : M.get x (UF.identify M uf a b ha hn).m with
  | none =>
      simp only [hnew]
      change M.get x (M.set a b uf.m) = none at hnew
      rw [tunnel_map_get_set] at hnew
      by_cases hxa : x = a
      · subst x
        simp at hnew
      · simp [hxa] at hnew
        exact False.elim (hxa ((tunnel_repr_none uf x hnew).symm.trans hx))
  | some y =>
      simp only [hnew]
      change M.get x (M.set a b uf.m) = some y at hnew
      rw [tunnel_map_get_set] at hnew
      by_cases hxa : x = a
      · subst x
        simp at hnew
        subst y
        exact tunnel_repr_identify_1 uf a b ha hn b hn
      · simp [hxa] at hnew
        apply ih y (by
          change M.get x (M.set a b uf.m) = some y
          rw [tunnel_map_get_set]
          simp [hxa, hnew])
        exact (tunnel_repr_some uf x y hnew).symm.trans hx

private theorem tunnel_repr_union_1 {M : MAP} (uf : UF.t M) (a b x : UF.elt M)
    (hx : UF.repr M uf x ≠ UF.repr M uf a) :
    UF.repr M (UF.union M uf a b) x = UF.repr M uf x := by
  unfold UF.union
  dsimp
  split <;> rename_i h
  · rfl
  · apply tunnel_repr_identify_1
    exact hx

private theorem tunnel_repr_union_2 {M : MAP} (uf : UF.t M) (a b x : UF.elt M)
    (hx : UF.repr M uf x = UF.repr M uf a) :
    UF.repr M (UF.union M uf a b) x = UF.repr M uf b := by
  unfold UF.union
  dsimp
  split
  · next heq => exact hx.trans heq
  · next heq =>
      exact (tunnel_repr_identify_2 uf (UF.repr M uf a) (UF.repr M uf b) _ _ x hx).trans
        (tunnel_repr_canonical uf b)

private theorem tunnel_repr_union_3 {M : MAP} (uf : UF.t M) (a b : UF.elt M) :
    UF.repr M (UF.union M uf a b) b = UF.repr M uf b := by
  by_cases h : UF.repr M uf a = UF.repr M uf b
  · unfold UF.union
    dsimp
    simp [h]
  · exact tunnel_repr_union_1 uf a b b (Ne.symm h)

private theorem tunnel_sameclass_union_2 {M : MAP} (uf : UF.t M)
    (a b x y : UF.elt M) (hxy : UF.repr M uf x = UF.repr M uf y) :
    UF.repr M (UF.union M uf a b) x = UF.repr M (UF.union M uf a b) y := by
  by_cases hx : UF.repr M uf x = UF.repr M uf a
  · rw [tunnel_repr_union_2 uf a b x hx]
    rw [tunnel_repr_union_2 uf a b y (hxy.symm.trans hx)]
  · rw [tunnel_repr_union_1 uf a b x hx]
    rw [tunnel_repr_union_1 uf a b y (by
      intro hy
      exact hx (hxy.trans hy))]
    exact hxy

private theorem tunnel_u_repr_union_1 (uf : U.t) (a b x : U.elt)
    (hx : U.repr uf x ≠ U.repr uf a) :
    U.repr (U.union uf a b) x = U.repr uf x := by
  cases uf
  unfold U.repr at hx
  unfold U.repr U.union
  apply tunnel_repr_union_1
  exact hx

private theorem tunnel_u_repr_union_2 (uf : U.t) (a b x : U.elt)
    (hx : U.repr uf x = U.repr uf a) :
    U.repr (U.union uf a b) x = U.repr uf b := by
  cases uf
  unfold U.repr at hx
  unfold U.repr U.union
  apply tunnel_repr_union_2
  exact hx

private theorem tunnel_u_repr_union_3 (uf : U.t) (a b : U.elt) :
    U.repr (U.union uf a b) b = U.repr uf b := by
  cases uf
  unfold U.repr U.union
  apply tunnel_repr_union_3

private theorem tunnel_u_sameclass_union_2 (uf : U.t) (a b x y : U.elt)
    (hxy : U.repr uf x = U.repr uf y) :
    U.repr (U.union uf a b) x = U.repr (U.union uf a b) y := by
  cases uf
  unfold U.repr at hxy
  unfold U.repr U.union
  apply tunnel_sameclass_union_2
  exact hxy

def record_branch_correct : record_branch_correctStatement := by
  intro c u f pc b hmap hget
  have hpc : U.repr u pc = pc := by
    have hremove := PTree.grs_proof pc c
    have h := hmap pc
    simp only [hremove] at h
    exact h
  have hdefault : branch_map_correct_1 c u f := by
    intro p
    by_cases hppc : p = pc
    · subst p
      rw [hget]
      cases b with
      | nil => exact hpc
      | cons instr tail =>
          cases instr with
          | Lbranch s => exact Or.inl hpc
          | Lop op args res => exact hpc
          | Lload chunk addr args dst => exact hpc
          | Lgetstack sl ofs ty dst => exact hpc
          | Lsetstack src sl ofs ty => exact hpc
          | Lstore chunk addr args src => exact hpc
          | Lcall sig ros => exact hpc
          | Ltailcall sig ros => exact hpc
          | Lbuiltin ef args res => exact hpc
          | Ljumptable arg tbl => exact hpc
          | Lreturn => exact hpc
          | Lcond cond args s1 s2 => exact hpc
    · have hremove := PTree.gro_proof c hppc
      have h := hmap p
      simp only [hremove] at h
      exact h
  cases b with
  | nil => exact ⟨f, hdefault⟩
  | cons instr tail =>
      cases instr with
      | Lbranch s =>
          refine ⟨measure_branch u pc s f, ?_⟩
          intro p
          by_cases hppc : p = pc
          · subst p
            rw [hget]
            simp only [record_branch]
            cases hs : peqNode (U.repr u s) pc with
            | left heq => exact Or.inl ((tunnel_u_repr_union_2 u pc s pc rfl).trans heq)
            | right hne =>
                right
                refine ⟨(tunnel_u_repr_union_2 u pc s pc rfl).trans
                  (tunnel_u_repr_union_3 u pc s).symm, ?_⟩
                unfold measure_branch
                cases hpc' : peqNode (U.repr u pc) pc with
                | left heq => simp [hs, hpc']; omega
                | right hnepc => exact False.elim (hnepc hpc)
          · have hpreserve : U.repr u p = p → U.repr (U.union u pc s) p = p := by
              intro hp
              exact (tunnel_u_repr_union_1 u pc s p (by
                intro hrepr
                apply hppc
                exact hp.symm.trans (hrepr.trans hpc))).trans hp
            have hpmap := hdefault p
            cases hpget : PTree.get p c with
            | none =>
                simp only [hpget] at hpmap
                simpa [record_branch] using hpreserve hpmap
            | some block =>
                cases block with
                | nil =>
                    simp only [hpget] at hpmap
                    simpa [record_branch] using hpreserve hpmap
                | cons pinstr ptail =>
                    cases pinstr with
                    | Lbranch ps =>
                        simp only [hpget] at hpmap
                        simp only [record_branch] at hpmap ⊢
                        cases hpmap with
                        | inl hp => exact Or.inl (hpreserve hp)
                        | inr hp =>
                            right
                            refine ⟨tunnel_u_sameclass_union_2 u pc s p ps hp.1, ?_⟩
                            unfold measure_branch
                            cases hs : peqNode (U.repr u s) pc with
                            | left heq => simpa [hs] using hp.2
                            | right hne =>
                                cases hps : peqNode (U.repr u ps) pc with
                                | left heqps =>
                                    cases hp' : peqNode (U.repr u p) pc with
                                    | left heqp => simp [hs, hps, hp']; omega
                                    | right hnep =>
                                        exact False.elim (hnep (hp.1.trans heqps))
                                | right hneps =>
                                    cases hp' : peqNode (U.repr u p) pc with
                                    | left heqp =>
                                        exact False.elim (hneps (hp.1.symm.trans heqp))
                                    | right hnep => simpa [hs, hps, hp'] using hp.2
                    | Lop op args res => simp only [hpget] at hpmap; simpa [record_branch] using hpreserve hpmap
                    | Lload chunk addr args dst => simp only [hpget] at hpmap; simpa [record_branch] using hpreserve hpmap
                    | Lgetstack sl ofs ty dst => simp only [hpget] at hpmap; simpa [record_branch] using hpreserve hpmap
                    | Lsetstack src sl ofs ty => simp only [hpget] at hpmap; simpa [record_branch] using hpreserve hpmap
                    | Lstore chunk addr args src => simp only [hpget] at hpmap; simpa [record_branch] using hpreserve hpmap
                    | Lcall sig ros => simp only [hpget] at hpmap; simpa [record_branch] using hpreserve hpmap
                    | Ltailcall sig ros => simp only [hpget] at hpmap; simpa [record_branch] using hpreserve hpmap
                    | Lbuiltin ef args res => simp only [hpget] at hpmap; simpa [record_branch] using hpreserve hpmap
                    | Ljumptable arg tbl => simp only [hpget] at hpmap; simpa [record_branch] using hpreserve hpmap
                    | Lreturn => simp only [hpget] at hpmap; simpa [record_branch] using hpreserve hpmap
                    | Lcond cond args s1 s2 => simp only [hpget] at hpmap; simpa [record_branch] using hpreserve hpmap
      | Lop op args res => exact ⟨f, hdefault⟩
      | Lload chunk addr args dst => exact ⟨f, hdefault⟩
      | Lgetstack sl ofs ty dst => exact ⟨f, hdefault⟩
      | Lsetstack src sl ofs ty => exact ⟨f, hdefault⟩
      | Lstore chunk addr args src => exact ⟨f, hdefault⟩
      | Lcall sig ros => exact ⟨f, hdefault⟩
      | Ltailcall sig ros => exact ⟨f, hdefault⟩
      | Lbuiltin ef args res => exact ⟨f, hdefault⟩
      | Ljumptable arg tbl => exact ⟨f, hdefault⟩
      | Lreturn => exact ⟨f, hdefault⟩
      | Lcond cond args s1 s2 => exact ⟨f, hdefault⟩

end CompCert4Lean.Backend.Tunnelingproof
