import CompCert4Lean.Foundation.RocqStdlib
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

/-! The source extracts the witness supplied by `record_gotos_correct_1`.
The migration phase has only recorded that proposition, so this total adapter
uses the witness when the proposition is inhabited and a neutral fallback
otherwise. -/
noncomputable def count_gotos (fn : function) (pc : node) : Nat :=
  by
    classical
    exact if h : ∃ f, branch_map_correct fn (record_gotos fn) f then
      Classical.choose h pc
    else
      0

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

noncomputable def measure : state → Nat
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

def record_branch_correctStatement : Prop :=
  ∀ (c : code) (u : U.t) (f : node → Nat) (pc : node) (b : bblock),
    branch_map_correct_1 (PTree.remove pc c) u f →
    PTree.get pc c = some b →
    ∃ f', branch_map_correct_1 c (record_branch u pc b) f'

def record_branches_correctStatement : Prop :=
  ∀ fn : function,
    ∃ f, branch_map_correct_1 fn.fn_code (record_branches fn) f

def record_cond_correctStatement : Prop :=
  ∀ (fn : function) (c : code) (u : U.t) (changed : Bool)
    (f : node → Nat) (pc : node) (b : bblock),
    branch_map_correct_2 fn c u f →
    PTree.get pc fn.fn_code = some b →
    PTree.get pc c ≠ none →
    ∃ f',
      branch_map_correct_2 fn
        (record_cond (c, u, changed) pc b).1
        (record_cond (c, u, changed) pc b).2.1 f'

def record_conds_1_correctStatement : Prop :=
  ∀ (fn : function) (c : code) (u : U.t) (f : node → Nat),
    branch_map_correct_2 fn c u f →
    code_compat fn c →
      code_compat fn (record_conds_1 (c, u)).1 ∧
      (∃ f', branch_map_correct_2 fn
        (record_conds_1 (c, u)).1 (record_conds_1 (c, u)).2.1 f')

def record_conds_correctStatement : Prop :=
  ∀ (fn : function) (cu : code × U.t),
    (∃ f, branch_map_correct_2 fn cu.1 cu.2 f) →
    code_compat fn cu.1 →
    ∃ f, branch_map_correct fn (record_conds cu) f

def record_gotos_correct_1Statement : Prop :=
  ∀ fn : function, ∃ f, branch_map_correct fn (record_gotos fn) f

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

def tunnel_step_correctStatement : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog tprog : program),
    match_prog prog tprog →
    ∀ (st1 st2 : state) (t : trace),
      step cfg xi (Genv.globalenv prog) st1 t st2 →
      ∀ st1', match_states st1 st1' →
        (∃ st2', step cfg xi (Genv.globalenv tprog) st1' t st2' ∧
          match_states st2 st2') ∨
        (measure st2 < measure st1 ∧ t = E0 ∧ match_states st2 st1')

def transf_initial_statesStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ st1, initial_state prog st1 →
      ∃ st2, initial_state tprog st2 ∧ match_states st1 st2

def transf_final_statesStatement : Prop :=
  ∀ (st1 st2 : state) (r : CompCert4Lean.Lib.Integers.int),
    match_states st1 st2 → final_state st1 r → final_state st2 r

def transf_program_correctStatement : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog tprog : program),
    match_prog prog tprog →
    forward_simulation (semantics cfg xi prog) (semantics cfg xi tprog)

end CompCert4Lean.Backend.Tunnelingproof
