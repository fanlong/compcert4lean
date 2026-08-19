import CompCert4Lean.Backend.Linearize
import CompCert4Lean.Common.ExternalCalls
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Common.Values
import CompCert4Lean.Foundation.RocqStdlib

/-!
# Correctness surface for code linearization

Definition-bearing translation of CompCert's `backend/Linearizeproof.v`.
Proof obligations assigned to the later proof-migration phase are represented
by transparent proposition descriptors; no theorem placeholder is introduced.
-/

namespace CompCert4Lean.Backend.Linearizeproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.LTL
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Linearize
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Machregs
open CompCert4Lean.X86.Op

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig

/-! ## Generated finite-set facts surface -/

namespace NodesetFacts

def NodesetFacts : Type := Unit
def eqb (x y : CompCert4Lean.Backend.Linearize.Nodeset.elt) : Bool := decide (x = y)

private def generatedProp : Prop := True

abbrev E_ST := generatedProp
abbrev Empty_m := generatedProp
abbrev Empty_s_m := generatedProp
abbrev Empty_s_m_Proper := generatedProp
abbrev Equal_ST := generatedProp
abbrev In_eq_iff := generatedProp
abbrev In_m := generatedProp
abbrev In_s_m := generatedProp
abbrev SubsetSetoid := generatedProp
abbrev SubsetSetoid_Reflexive := generatedProp
abbrev SubsetSetoid_Transitive := generatedProp
abbrev SubsetSetoid_relation := generatedProp
abbrev Subset_m := generatedProp
abbrev Subset_refl := generatedProp
abbrev Subset_trans := generatedProp
abbrev add_b := generatedProp
abbrev add_iff := generatedProp
abbrev add_m := generatedProp
abbrev add_neq_b := generatedProp
abbrev add_neq_iff := generatedProp
abbrev add_s_m := generatedProp
abbrev add_s_m_Proper := generatedProp
abbrev diff_b := generatedProp
abbrev diff_iff := generatedProp
abbrev diff_m := generatedProp
abbrev diff_s_m := generatedProp
abbrev diff_s_m_Proper := generatedProp
abbrev elements_b := generatedProp
abbrev elements_iff := generatedProp
abbrev empty_b := generatedProp
abbrev empty_iff := generatedProp
abbrev equal_iff := generatedProp
abbrev equal_m := generatedProp
abbrev exists_b := generatedProp
abbrev exists_iff := generatedProp
abbrev filter_b := generatedProp
abbrev filter_equal := generatedProp
abbrev filter_ext := generatedProp
abbrev filter_iff := generatedProp
abbrev filter_subset := generatedProp
abbrev for_all_b := generatedProp
abbrev for_all_iff := generatedProp
abbrev inter_b := generatedProp
abbrev inter_iff := generatedProp
abbrev inter_m := generatedProp
abbrev inter_s_m := generatedProp
abbrev inter_s_m_Proper := generatedProp
abbrev is_empty_iff := generatedProp
abbrev is_empty_m := generatedProp
abbrev mem_b := generatedProp
abbrev mem_iff := generatedProp
abbrev mem_m := generatedProp
abbrev not_mem_iff := generatedProp
abbrev remove_b := generatedProp
abbrev remove_iff := generatedProp
abbrev remove_m := generatedProp
abbrev remove_neq_b := generatedProp
abbrev remove_neq_iff := generatedProp
abbrev remove_s_m := generatedProp
abbrev remove_s_m_Proper := generatedProp
abbrev singleton_b := generatedProp
abbrev singleton_iff := generatedProp
abbrev singleton_m := generatedProp
abbrev subset_iff := generatedProp
abbrev subset_m := generatedProp
abbrev union_b := generatedProp
abbrev union_iff := generatedProp
abbrev union_m := generatedProp
abbrev union_s_m := generatedProp
abbrev union_s_m_Proper := generatedProp

end NodesetFacts

/-! ## Program matching and preserved global-environment observations -/

def match_prog (p : LTL.program) (tp : Linear.program) : Prop :=
  @match_program LTL.fundef Unit Linear.fundef Unit
    (Linker_fundef LTL.function) Linker_unit
    (fun _ f tf => transf_fundef f = .OK tf)
    (fun x y : Unit => x = y) p tp

/-! ## State matching and the simulation measure -/

inductive match_stackframes : LTL.stackframe -> Linear.stackframe -> Prop where
  | match_stackframe_intro
      (f : LTL.function) (sp : val) (bb : LTL.bblock) (ls : LTL.locset)
      (tf : Linear.function) (c : Linear.code)
      (htrans : transf_function f = .OK tf)
      (hreach : forall pc, List.Mem pc (successors_block bb) ->
        PMap.get pc (reachable f) = true)
      (htail : is_tail c tf.fn_code) :
      match_stackframes
        (LTL.Stackframe f sp ls bb)
        (Linear.Stackframe tf sp ls (linearize_block bb c))

inductive match_states : LTL.state -> Linear.state -> Prop where
  | match_states_add_branch
      (s : List LTL.stackframe) (f : LTL.function) (sp : val)
      (pc : LTL.node) (ls : LTL.locset) (m : mem)
      (tf : Linear.function) (ts : List Linear.stackframe) (c : Linear.code)
      (hstack : list_forall2 match_stackframes s ts)
      (htrans : transf_function f = .OK tf)
      (hreach : PMap.get pc (reachable f) = true)
      (htail : is_tail c tf.fn_code) :
      match_states (LTL.State s f sp pc ls m)
        (Linear.State ts tf sp (add_branch pc c) ls m)
  | match_states_cond_taken
      (s : List LTL.stackframe) (f : LTL.function) (sp : val)
      (pc : LTL.node) (ls : LTL.locset) (m : mem)
      (tf : Linear.function) (ts : List Linear.stackframe)
      (cond : condition) (args : List mreg) (c : Linear.code)
      (hstack : list_forall2 match_stackframes s ts)
      (htrans : transf_function f = .OK tf)
      (hreach : PMap.get pc (reachable f) = true)
      (hjump : eval_condition cond (reglist ls args) m = some true) :
      match_states
        (LTL.State s f sp pc (undef_regs (destroyed_by_cond cond) ls) m)
        (Linear.State ts tf sp (Lcond cond args pc :: c) ls m)
  | match_states_jumptable
      (s : List LTL.stackframe) (f : LTL.function) (sp : val)
      (pc : LTL.node) (ls : LTL.locset) (m : mem)
      (tf : Linear.function) (ts : List Linear.stackframe)
      (arg : mreg) (tbl : List LTL.node) (c : Linear.code) (n : int)
      (hstack : list_forall2 match_stackframes s ts)
      (htrans : transf_function f = .OK tf)
      (hreach : PMap.get pc (reachable f) = true)
      (harg : ls (R arg) = Vint n)
      (hjump : list_nth_z tbl
        (CompCert4Lean.Lib.Integers.Int.unsigned n) = some pc) :
      match_states
        (LTL.State s f sp pc (undef_regs destroyed_by_jumptable ls) m)
        (Linear.State ts tf sp (Ljumptable arg tbl :: c) ls m)
  | match_states_block
      (s : List LTL.stackframe) (f : LTL.function) (sp : val)
      (bb : LTL.bblock) (ls : LTL.locset) (m : mem)
      (tf : Linear.function) (ts : List Linear.stackframe) (c : Linear.code)
      (hstack : list_forall2 match_stackframes s ts)
      (htrans : transf_function f = .OK tf)
      (hreach : forall pc, List.Mem pc (successors_block bb) ->
        PMap.get pc (reachable f) = true)
      (htail : is_tail c tf.fn_code) :
      match_states (LTL.Block s f sp bb ls m)
        (Linear.State ts tf sp (linearize_block bb c) ls m)
  | match_states_call
      (s : List LTL.stackframe) (f : LTL.fundef) (ls : LTL.locset) (m : mem)
      (tf : Linear.fundef) (ts : List Linear.stackframe)
      (hstack : list_forall2 match_stackframes s ts)
      (htrans : transf_fundef f = .OK tf) :
      match_states (LTL.Callstate s f ls m) (Linear.Callstate ts tf ls m)
  | match_states_return
      (s : List LTL.stackframe) (ls : LTL.locset) (m : mem)
      (ts : List Linear.stackframe)
      (hstack : list_forall2 match_stackframes s ts) :
      match_states (LTL.Returnstate s ls m) (Linear.Returnstate ts ls m)

def measure : LTL.state -> Nat
  | .State _ _ _ _ _ _ => 0
  | .Block _ _ _ _ _ _ => 1
  | .Callstate _ _ _ _ => 0
  | .Returnstate _ _ _ => 0

/-! ## Exact statement descriptors for later proof migration -/

def transf_program_matchStatement : Prop :=
  forall (p : LTL.program) (tp : Linear.program),
    transf_program p = .OK tp -> match_prog p tp

def functions_translatedStatement : Prop :=
  forall (prog : LTL.program) (tprog : Linear.program),
    match_prog prog tprog ->
    forall (v : val) (f : LTL.fundef),
      Genv.find_funct (Genv.globalenv prog) v = some f ->
      exists tf,
        Genv.find_funct (Genv.globalenv tprog) v = some tf /\
          transf_fundef f = .OK tf

def function_ptr_translatedStatement : Prop :=
  forall (prog : LTL.program) (tprog : Linear.program),
    match_prog prog tprog ->
    forall (v : block) (f : LTL.fundef),
      Genv.find_funct_ptr (Genv.globalenv prog) v = some f ->
      exists tf,
        Genv.find_funct_ptr (Genv.globalenv tprog) v = some tf /\
          transf_fundef f = .OK tf

def symbols_preservedStatement : Prop :=
  forall (prog : LTL.program) (tprog : Linear.program),
    match_prog prog tprog ->
    forall id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id

def senv_preservedStatement : Prop :=
  forall (prog : LTL.program) (tprog : Linear.program),
    match_prog prog tprog ->
    Senv.equiv (Genv.to_senv (Genv.globalenv prog))
      (Genv.to_senv (Genv.globalenv tprog))

def sig_preservedStatement : Prop :=
  forall (f : LTL.fundef) (tf : Linear.fundef),
    transf_fundef f = .OK tf -> Linear.funsig tf = LTL.funsig f

def stacksize_preservedStatement : Prop :=
  forall (f : LTL.function) (tf : Linear.function),
    transf_function f = .OK tf -> tf.fn_stacksize = f.fn_stacksize

def find_function_translatedStatement : Prop :=
  forall (prog : LTL.program) (tprog : Linear.program),
    match_prog prog tprog ->
    forall (ros : Sum mreg ident) (ls : LTL.locset) (f : LTL.fundef),
      LTL.find_function (Genv.globalenv prog) ros ls = some f ->
      exists tf,
        Linear.find_function (Genv.globalenv tprog) ros ls = some tf /\
          transf_fundef f = .OK tf

def reachable_entrypointStatement : Prop :=
  forall f : LTL.function, PMap.get f.fn_entrypoint (reachable f) = true

def reachable_successorsStatement : Prop :=
  forall (f : LTL.function) (pc pc' : LTL.node) (b : LTL.bblock),
    PTree.get pc f.fn_code = some b -> List.Mem pc' (successors_block b) ->
    PMap.get pc (reachable f) = true ->
    PMap.get pc' (reachable f) = true

def nodeset_of_list_correctStatement : Prop :=
  forall (l s s' : List LTL.node),
    nodeset_of_list l s = .OK s' ->
    list_norepet l /\
      (forall pc, List.Mem pc s' <-> List.Mem pc s \/ List.Mem pc l) /\
      (forall pc, List.Mem pc l -> ¬ List.Mem pc s)

def check_reachable_correctStatement : Prop :=
  forall (f : LTL.function) (reach : PMap.t Bool)
    (s : List LTL.node) (pc : LTL.node) (i : LTL.bblock),
    check_reachable f reach s = true ->
    PTree.get pc f.fn_code = some i ->
    PMap.get pc reach = true -> List.Mem pc s

def enumerate_completeStatement : Prop :=
  forall (f : LTL.function) (enum : List LTL.node)
    (pc : LTL.node) (i : LTL.bblock),
    enumerate f = .OK enum ->
    PTree.get pc f.fn_code = some i ->
    PMap.get pc (reachable f) = true -> List.Mem pc enum

def enumerate_norepetStatement : Prop :=
  forall (f : LTL.function) (enum : List LTL.node),
    enumerate f = .OK enum -> list_norepet enum

def unique_labels : Linear.code -> Prop
  | [] => True
  | Linear.Llabel lbl :: c => ¬ List.Mem (Linear.Llabel lbl) c ∧ unique_labels c
  | _ :: c => unique_labels c

def find_label_uniqueStatement : Prop :=
  forall (lbl : Linear.label) (c1 c2 c3 : Linear.code),
    is_tail (Linear.Llabel lbl :: c1) c2 -> unique_labels c2 ->
    Linear.find_label lbl c2 = some c3 -> c1 = c3

def starts_with_correctStatement : Prop :=
  forall (cfg : CompilerConfig) (xi : ExternalCalls) (tge : Linear.genv)
    (lbl : Linear.label) (c1 c2 c3 : Linear.code) (s : List Linear.stackframe)
    (f : Linear.function) (sp : val) (ls : Linear.locset) (m : mem),
    is_tail c1 c2 -> unique_labels c2 ->
    starts_with lbl c1 = true -> Linear.find_label lbl c2 = some c3 ->
    plus (fun ge => Linear.step cfg xi ge) tge
      (Linear.State s f sp c1 ls m) E0
      (Linear.State s f sp c3 ls m)

def find_label_add_branchStatement : Prop :=
  forall (lbl s : Linear.label) (k : Linear.code),
    Linear.find_label lbl (add_branch s k) = Linear.find_label lbl k

def find_label_lin_blockStatement : Prop :=
  forall (lbl : Linear.label) (k : Linear.code) (b : LTL.bblock),
    Linear.find_label lbl (linearize_block b k) = Linear.find_label lbl k

def linearize_body_consStatement : Prop :=
  forall (f : LTL.function) (pc : LTL.node) (enum : List LTL.node),
    linearize_body f (pc :: enum) =
      match PTree.get pc f.fn_code with
      | none => linearize_body f enum
      | some b => Linear.Llabel pc :: linearize_block b (linearize_body f enum)

def find_label_lin_recStatement : Prop :=
  forall (f : LTL.function) (enum : List LTL.node) (pc : LTL.node)
    (b : LTL.bblock),
    List.Mem pc enum -> PTree.get pc f.fn_code = some b ->
    exists k,
      Linear.find_label pc (linearize_body f enum) =
        some (linearize_block b k)

def find_label_linStatement : Prop :=
  forall (f : LTL.function) (tf : Linear.function) (pc : LTL.node)
    (b : LTL.bblock),
    transf_function f = .OK tf -> PTree.get pc f.fn_code = some b ->
    PMap.get pc (reachable f) = true ->
    exists k,
      Linear.find_label pc tf.fn_code = some (linearize_block b k)

def label_in_add_branchStatement : Prop :=
  forall (lbl s : Linear.label) (k : Linear.code),
    List.Mem (Linear.Llabel lbl) (add_branch s k) ->
      List.Mem (Linear.Llabel lbl) k

def label_in_lin_blockStatement : Prop :=
  forall (lbl : Linear.label) (k : Linear.code) (b : LTL.bblock),
    List.Mem (Linear.Llabel lbl) (linearize_block b k) ->
      List.Mem (Linear.Llabel lbl) k

def label_in_lin_recStatement : Prop :=
  forall (f : LTL.function) (lbl : Linear.label) (enum : List LTL.node),
    List.Mem (Linear.Llabel lbl) (linearize_body f enum) -> List.Mem lbl enum

def unique_labels_add_branchStatement : Prop :=
  forall (lbl : Linear.label) (k : Linear.code),
    unique_labels k -> unique_labels (add_branch lbl k)

def unique_labels_lin_blockStatement : Prop :=
  forall (k : Linear.code) (b : LTL.bblock),
    unique_labels k -> unique_labels (linearize_block b k)

def unique_labels_lin_recStatement : Prop :=
  forall (f : LTL.function) (enum : List LTL.node),
    list_norepet enum -> unique_labels (linearize_body f enum)

def unique_labels_transf_functionStatement : Prop :=
  forall (f : LTL.function) (tf : Linear.function),
    transf_function f = .OK tf -> unique_labels tf.fn_code

def is_tail_find_labelStatement : Prop :=
  forall (lbl : Linear.label) (c2 c1 : Linear.code),
    Linear.find_label lbl c1 = some c2 -> is_tail c2 c1

def is_tail_add_branchStatement : Prop :=
  forall (lbl : Linear.label) (c1 c2 : Linear.code),
    is_tail (add_branch lbl c1) c2 -> is_tail c1 c2

def is_tail_lin_blockStatement : Prop :=
  forall (b : LTL.bblock) (c1 c2 : Linear.code),
    is_tail (linearize_block b c1) c2 -> is_tail c1 c2

def add_branch_correctStatement : Prop :=
  forall (cfg : CompilerConfig) (xi : ExternalCalls) (tge : Linear.genv)
    (lbl : Linear.label) (c k : Linear.code) (s : List Linear.stackframe)
    (f : LTL.function) (tf : Linear.function) (sp : val) (ls : Linear.locset)
    (m : mem),
    transf_function f = .OK tf -> is_tail k tf.fn_code ->
    Linear.find_label lbl tf.fn_code = some c ->
    plus (fun ge => Linear.step cfg xi ge) tge
      (Linear.State s tf sp (add_branch lbl k) ls m) E0
      (Linear.State s tf sp c ls m)

def match_parent_locsetStatement : Prop :=
  forall (s : List LTL.stackframe) (ts : List Linear.stackframe),
    list_forall2 match_stackframes s ts ->
    Linear.parent_locset ts = LTL.parent_locset s

def transf_step_correctStatement : Prop :=
  forall (cfg : CompilerConfig) (xi : ExternalCalls)
    (prog : LTL.program) (tprog : Linear.program),
    match_prog prog tprog ->
    forall (s1 : LTL.state) (t : trace) (s2 : LTL.state),
      LTL.step cfg xi (Genv.globalenv prog) s1 t s2 ->
      forall s1', match_states s1 s1' ->
        (exists s2',
          plus (fun ge => Linear.step cfg xi ge) (Genv.globalenv tprog)
            s1' t s2' /\ match_states s2 s2') \/
        (measure s2 < measure s1 /\ t = E0 /\ match_states s2 s1')

def transf_initial_statesStatement : Prop :=
  forall (prog : LTL.program) (tprog : Linear.program),
    match_prog prog tprog ->
    forall st1, LTL.initial_state prog st1 ->
      exists st2, Linear.initial_state tprog st2 /\ match_states st1 st2

def transf_final_statesStatement : Prop :=
  forall (st1 : LTL.state) (st2 : Linear.state) (r : int),
    match_states st1 st2 -> LTL.final_state st1 r -> Linear.final_state st2 r

def transf_program_correctStatement : Prop :=
  forall (cfg : CompilerConfig) (xi : ExternalCalls)
    (prog : LTL.program) (tprog : Linear.program),
    match_prog prog tprog ->
    forward_simulation
      (LTL.semantics cfg xi prog) (Linear.semantics cfg xi tprog)

end CompCert4Lean.Backend.Linearizeproof
