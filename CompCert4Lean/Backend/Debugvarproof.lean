import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Backend.Debugvar
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.ExternalCalls
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Smallstep

/-!
# Correctness surface for debug-variable live-range analysis

Definition-bearing translation of CompCert's `backend/Debugvarproof.v`.
Proof obligations assigned to the later proof-migration phase are represented
by exact transparent proposition descriptors.
-/

namespace CompCert4Lean.Backend.Debugvarproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Debugvar
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Common.AST
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

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig

/-! ## Relational characterization of the transformation -/

def match_prog (cfg : CompilerConfig) (p tp : program) : Prop :=
  @match_program fundef Unit fundef Unit
    (Linker_fundef function) Linker_unit
    (fun _ f tf => CompCert4Lean.Backend.Debugvar.transf_fundef cfg f = .OK tf)
    (fun x y : Unit => x = y) p tp

def transf_program_matchStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program),
    CompCert4Lean.Backend.Debugvar.transf_program cfg p = .OK tp →
      match_prog cfg p tp

inductive match_code : code → code → Prop where
  | nil : match_code [] []
  | cons (i : instruction) (before after : Option avail) (c c' : code) :
      match_code c c' →
      match_code (i :: c) (i :: add_delta_ranges before after c')

def diff_sameStatement : Prop :=
  ∀ s : avail, diff s s = []

def delta_state_sameStatement : Prop :=
  ∀ s : Option avail, delta_state s s = ([], [])

def transf_code_matchStatement : Prop :=
  ∀ (cfg : CompilerConfig) (lm : labelmap) (c : code) (before : Option avail),
    match_code c (transf_code cfg lm before c)

inductive match_function : function → function → Prop where
  | intro (f : function) (c : code) :
      match_code f.fn_code c →
      match_function f
        { fn_sig := f.fn_sig
          fn_stacksize := f.fn_stacksize
          fn_code := c }

def transf_function_matchStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : function) (tf : function),
    CompCert4Lean.Backend.Debugvar.transf_function cfg f = .OK tf →
      match_function f tf

def find_label_add_delta_rangesStatement : Prop :=
  ∀ (lbl : label) (c : code) (before after : Option avail),
    find_label lbl (add_delta_ranges before after c) = find_label lbl c

def find_label_match_recStatement : Prop :=
  ∀ (lbl : label) (c' c tc : code),
    match_code c tc →
    find_label lbl c = some c' →
      ∃ (before after : Option avail) (tc' : code),
        find_label lbl tc = some (add_delta_ranges before after tc') ∧
          match_code c' tc'

def find_label_matchStatement : Prop :=
  ∀ (f tf : function) (lbl : label) (c : code),
    match_function f tf →
    find_label lbl f.fn_code = some c →
      ∃ (before after : Option avail) (tc : code),
        find_label lbl tf.fn_code = some (add_delta_ranges before after tc) ∧
          match_code c tc

/-! ## Preserved global-environment observations -/

def symbols_preservedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog tprog : program),
    match_prog cfg prog tprog →
      ∀ s : ident,
        Genv.find_symbol (Genv.globalenv tprog) s =
          Genv.find_symbol (Genv.globalenv prog) s

def senv_preservedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog tprog : program),
    match_prog cfg prog tprog →
      Senv.equiv
        (Genv.to_senv (Genv.globalenv prog))
        (Genv.to_senv (Genv.globalenv tprog))

def functions_translatedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog tprog : program),
    match_prog cfg prog tprog →
      ∀ (v : val) (f : fundef),
        Genv.find_funct (Genv.globalenv prog) v = some f →
          ∃ tf,
            Genv.find_funct (Genv.globalenv tprog) v = some tf ∧
              CompCert4Lean.Backend.Debugvar.transf_fundef cfg f = .OK tf

def function_ptr_translatedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog tprog : program),
    match_prog cfg prog tprog →
      ∀ (b : block) (f : fundef),
        Genv.find_funct_ptr (Genv.globalenv prog) b = some f →
          ∃ tf,
            Genv.find_funct_ptr (Genv.globalenv tprog) b = some tf ∧
              CompCert4Lean.Backend.Debugvar.transf_fundef cfg f = .OK tf

def sig_preservedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f tf : fundef),
    CompCert4Lean.Backend.Debugvar.transf_fundef cfg f = .OK tf →
      funsig tf = funsig f

def find_function_translatedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog tprog : program),
    match_prog cfg prog tprog →
      ∀ (ros : Sum mreg ident) (ls : locset) (f : fundef),
        find_function (Genv.globalenv prog) ros ls = some f →
          ∃ tf,
            find_function (Genv.globalenv tprog) ros ls = some tf ∧
              CompCert4Lean.Backend.Debugvar.transf_fundef cfg f = .OK tf

/-! ## Evaluation and state matching -/

def can_eval_safe_argStatement : Prop :=
  ∀ (tprog : program),
    ∀ (rs : locset) (sp : val) (m : mem) (a : builtin_arg loc),
      safe_builtin_arg a →
        ∃ v,
          eval_builtin_arg (Genv.to_senv (Genv.globalenv tprog)) rs sp m a v

def eval_add_delta_rangesStatement : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (tprog : program),
    ∀ (s : List stackframe) (f : function) (sp : val) (c : code)
      (rs : locset) (m : mem) (before after : Option avail),
      star (step cfg xi) (Genv.globalenv tprog)
        (State s f sp (add_delta_ranges before after c) rs m)
        E0 (State s f sp c rs m)

inductive match_stackframes : stackframe → stackframe → Prop where
  | intro (f : function) (sp : val) (rs : locset) (c : code)
      (tf : function) (tc : code) (before after : Option avail) :
      match_function f tf →
      match_code c tc →
      match_stackframes
        (Stackframe f sp rs c)
        (Stackframe tf sp rs (add_delta_ranges before after tc))

inductive match_states (cfg : CompilerConfig) : state → state → Prop where
  | instr (s : List stackframe) (f : function) (sp : val) (c : code)
      (rs : locset) (m : mem) (tf : function) (ts : List stackframe)
      (tc : code) :
      list_forall2 match_stackframes s ts →
      match_function f tf →
      match_code c tc →
      match_states cfg (State s f sp c rs m) (State ts tf sp tc rs m)
  | call (s : List stackframe) (f : fundef) (rs : locset) (m : mem)
      (tf : fundef) (ts : List stackframe) :
      list_forall2 match_stackframes s ts →
      CompCert4Lean.Backend.Debugvar.transf_fundef cfg f = .OK tf →
      match_states cfg (Callstate s f rs m) (Callstate ts tf rs m)
  | return (s : List stackframe) (rs : locset) (m : mem)
      (ts : List stackframe) :
      list_forall2 match_stackframes s ts →
      match_states cfg (Returnstate s rs m) (Returnstate ts rs m)

def parent_locset_matchStatement : Prop :=
  ∀ (s ts : List stackframe),
    list_forall2 match_stackframes s ts →
      parent_locset ts = parent_locset s

def transf_step_correctStatement : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog tprog : program),
    match_prog cfg prog tprog →
      ∀ (s1 : state) (t : trace) (s2 : state),
        step cfg xi (Genv.globalenv prog) s1 t s2 →
          ∀ ts1, match_states cfg s1 ts1 →
            ∃ ts2,
              plus (step cfg xi) (Genv.globalenv tprog) ts1 t ts2 ∧
                match_states cfg s2 ts2

def transf_initial_statesStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog tprog : program),
    match_prog cfg prog tprog →
      ∀ st1, initial_state prog st1 →
        ∃ st2, initial_state tprog st2 ∧ match_states cfg st1 st2

def transf_final_statesStatement : Prop :=
  ∀ (cfg : CompilerConfig) (st1 st2 : state) (r : int),
    match_states cfg st1 st2 → final_state st1 r → final_state st2 r

def transf_program_correctStatement : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog tprog : program),
    match_prog cfg prog tprog →
      forward_simulation
        (semantics cfg xi prog) (semantics cfg xi tprog)

end CompCert4Lean.Backend.Debugvarproof
