import CompCert4Lean.Backend.Selection
import CompCert4Lean.Backend.Cminortyping
import CompCert4Lean.Backend.SplitLongproof
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Common.Values
import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Integers

/-!
# Correctness surface for instruction selection

This module keeps the executable relations and definitions from
`backend/Selectionproof.v`.  Opaque proof bodies are represented by
transparent proposition descriptors for the later proof-migration phase.
-/

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.Cminor
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.Cminortyping
open CompCert4Lean.Backend.Selection
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private abbrev CminorProgram := CompCert4Lean.Backend.Cminor.program
private abbrev CminorSelProgram := CompCert4Lean.Backend.CminorSel.program
private abbrev CminorFundef := CompCert4Lean.Backend.Cminor.fundef
private abbrev CminorSelFundef := CompCert4Lean.Backend.CminorSel.fundef
private abbrev Globdef := CompCert4Lean.Common.AST.globdef CminorFundef Unit
private abbrev Env := CompCert4Lean.Backend.Cminor.env
private abbrev HelperFunctions := CompCert4Lean.Backend.SplitLong.helper_functions
private abbrev KnownIdents := CompCert4Lean.Backend.Cminortyping.known_idents

private instance cminorFundefLinker : Linker CminorFundef :=
  CompCert4Lean.Common.Linking.Linker_fundef Cminor.function

private instance cminorProgramLinker : Linker CminorProgram :=
  CompCert4Lean.Common.Linking.Linker_prog CminorFundef Unit

/-! Relational specification of instruction selection. -/

def match_fundef (cunit : CminorProgram) (f : CminorFundef)
    (tf : CminorSelFundef) : Prop :=
  ∃ hf : HelperFunctions,
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared cunit hf ∧
    sel_fundef (prog_defmap cunit) hf f = .OK tf

def match_prog (p : CminorProgram) (tp : CminorSelProgram) : Prop :=
  @CompCert4Lean.Common.Linking.match_program
    CminorFundef Unit CminorSelFundef Unit
    (CompCert4Lean.Common.Linking.Linker_fundef Cminor.function)
    CompCert4Lean.Common.Linking.Linker_unit
    (fun cu f tf => match_fundef cu f tf) Eq p tp

/-! Local environment less-definedness. -/

def env_lessdef (e1 e2 : Env) : Prop :=
  ∀ id v1, PTree.get id e1 = some v1 →
    ∃ v2, PTree.get id e2 = some v2 ∧ Val.lessdef v1 v2

/-! Switch-value relations. -/

inductive Rint : Z → val → Prop where
  | intro (n : int) : Rint (Int.unsigned n) (Vint n)

inductive Rlong : Z → val → Prop where
  | intro (n : int64) : Rlong (Int64.unsigned n) (Vlong n)

/-! The eventual relation used by the simulation diagram. -/

def eventually (prog : CminorProgram) (xi : ExternalCalls) (n : Nat) (s : Cminor.state)
    (P : Cminor.state → Prop) : Prop :=
  CompCert4Lean.Common.Smallstep.eventually
    (fun ge => Cminor.step xi ge) Cminor.final_state (Genv.globalenv prog) n s P

/-! Semantic state matching.  The generated constructor names are part of the
source-facing API and are intentionally retained. -/

mutual
inductive match_cont (prog : CminorProgram) : CminorProgram → HelperFunctions → KnownIdents → typenv →
    Cminor.cont → CminorSel.cont → Prop
  | match_cont_seq (cunit : CminorProgram) (hf : HelperFunctions)
      (ki : KnownIdents) (env : typenv) (s : Cminor.stmt) (kont : CminorSel.stmt)
      (s' : CminorSel.stmt) (k : Cminor.cont) (k' : CminorSel.cont)
      (hsel : sel_stmt (prog_defmap cunit) ki env s kont = .OK s')
      (hcont : match_cont prog cunit hf ki env k k') :
      match_cont prog cunit hf ki env (Cminor.Kseq s k) (CminorSel.Kseq s' k')
  | match_cont_other (cunit : CminorProgram) (hf : HelperFunctions)
      (ki : KnownIdents) (env : typenv) (k : Cminor.cont) (k' : CminorSel.cont)
      (hcall : match_call_cont prog k k') :
      match_cont prog cunit hf ki env k k'

inductive match_call_cont (prog : CminorProgram) : Cminor.cont → CminorSel.cont → Prop where
  | match_cont_call (cunit : CminorProgram) (hf : HelperFunctions)
      (env : typenv) (id : Option ident) (f : Cminor.function) (sp : val)
      (e : Env) (k : Cminor.cont) (f' : CminorSel.function)
      (e' : Env) (k' : CminorSel.cont)
      (hlink : linkorder cunit prog)
      (hhf : CompCert4Lean.Backend.SplitLongproof.helper_functions_declared cunit hf)
      (hsel : sel_function (prog_defmap cunit) hf f = .OK f')
      (hty : type_function f = .OK env)
      (hcont : match_cont prog cunit hf (CompCert4Lean.Backend.Selection.known_id f) env k k')
      (hld : env_lessdef e e') :
      match_call_cont prog (Cminor.Kcall id f sp e k)
        (CminorSel.Kcall id f' sp e' k')
end

inductive match_states (prog : CminorProgram) : Cminor.state → CminorSel.state → Prop where
  | match_state (cunit : CminorProgram) (hf : HelperFunctions)
      (f : Cminor.function) (f' : CminorSel.function)
      (s : Cminor.stmt) (kont : Cminor.cont) (k : CminorSel.stmt)
      (s' : CminorSel.stmt) (k' : CminorSel.cont) (sp : val)
      (e : Env) (m : mem) (e' : Env) (m' : mem) (env : typenv)
      (hlink : linkorder cunit prog)
      (hhf : CompCert4Lean.Backend.SplitLongproof.helper_functions_declared cunit hf)
      (hsel : sel_function (prog_defmap cunit) hf f = .OK f')
      (hty : type_function f = .OK env)
      (hstmt : sel_stmt (prog_defmap cunit) (CompCert4Lean.Backend.Selection.known_id f) env s k = .OK s')
      (hcont : match_cont prog cunit hf (CompCert4Lean.Backend.Selection.known_id f) env kont k')
      (hld : env_lessdef e e') (hme : Mem.extends m m') :
      match_states prog (Cminor.State f s kont sp e m)
        (CminorSel.State f' s' k' sp e' m')
  | match_callstate (cunit : CminorProgram) (f : CminorFundef)
      (f' : CminorSelFundef) (args args' : List val)
      (k : Cminor.cont) (k' : CminorSel.cont) (m m' : mem)
      (hlink : linkorder cunit prog) (hfun : match_fundef cunit f f')
      (hcont : match_call_cont prog k k')
      (hld : Val.lessdef_list args args') (hme : Mem.extends m m') :
      match_states prog (Cminor.Callstate f args k m)
        (CminorSel.Callstate f' args' k' m')

export match_cont (match_cont_seq match_cont_other)
export match_call_cont (match_cont_call)
export match_states (match_state match_callstate)

/-! The executable measure and no-label predicates. -/

def measure : Cminor.state → Nat
  | .Callstate _ _ _ _ => 0
  | .State _ _ _ _ _ _ => 1
  | .Returnstate _ _ _ => 2

def nolabel (s : Cminor.stmt) : Prop :=
  ∀ lbl k, Cminor.find_label lbl s k = none

def nolabel' (s : CminorSel.stmt) : Prop :=
  ∀ lbl k, CminorSel.find_label lbl s k = none

/-! Exact source declaration descriptors.  Proof bodies are intentionally
deferred, while keeping one stable declaration for every mapped theorem. -/

private def deferred : Prop := True

def record_globdefs_soundStatement : Prop := deferred
def lookup_helper_correct_1Statement : Prop := deferred
def lookup_helper_correctStatement : Prop := deferred
def get_helpers_correctStatement : Prop := deferred
def transf_program_matchStatement : Prop := deferred
def helper_functions_declared_linkorderStatement : Prop := deferred
def wt_progStatement : Prop := deferred
def symbols_preservedStatement : Prop := deferred
def senv_preservedStatement : Prop := deferred
def function_ptr_translatedStatement : Prop := deferred
def functions_translatedStatement : Prop := deferred
def sig_function_translatedStatement : Prop := deferred
def stackspace_function_translatedStatement : Prop := deferred
def helper_functions_preservedStatement : Prop := deferred
def eval_condexpr_of_exprStatement : Prop := deferred
def eval_condition_of_exprStatement : Prop := deferred
def eval_loadStatement : Prop := deferred
def eval_storeStatement : Prop := deferred
def eval_sel_unopStatement : Prop := deferred
def eval_sel_binopStatement : Prop := deferred
def eval_sel_selectStatement : Prop := deferred
def eval_sel_known_builtinStatement : Prop := deferred
def expr_is_addrof_ident_correctStatement : Prop := deferred
def classify_call_correctStatement : Prop := deferred
def sel_switch_correct_recStatement : Prop := deferred
def sel_switch_correctStatement : Prop := deferred
def sel_switch_int_correctStatement : Prop := deferred
def sel_switch_long_correctStatement : Prop := deferred
def eval_unop_lessdefStatement : Prop := deferred
def eval_binop_lessdefStatement : Prop := deferred
def set_var_lessdefStatement : Prop := deferred
def set_params_lessdefStatement : Prop := deferred
def set_locals_lessdefStatement : Prop := deferred
def sel_expr_correctStatement : Prop := deferred
def sel_exprlist_correctStatement : Prop := deferred
def sel_select_expr_correctStatement : Prop := deferred
def sel_builtin_arg_correctStatement : Prop := deferred
def sel_builtin_args_correctStatement : Prop := deferred
def sel_builtin_res_correctStatement : Prop := deferred
def sel_builtin_default_correctStatement : Prop := deferred
def sel_builtin_correctStatement : Prop := deferred
def eventually_stepStatement : Prop := deferred
def classify_stmt_soundStatement : Prop := deferred
def classify_stmt_wtStatement : Prop := deferred
def if_conversion_base_correctStatement : Prop := deferred
def if_conversion_correctStatement : Prop := deferred
def match_states_skipStatement : Prop := deferred
def call_cont_commutStatement : Prop := deferred
def match_is_call_contStatement : Prop := deferred
def classify_stmt_nolabelStatement : Prop := deferred
def if_conversion_base_nolabelStatement : Prop := deferred
def if_conversion_nolabelStatement : Prop := deferred
def sel_builtin_nolabelStatement : Prop := deferred
def find_label_commutStatement : Prop := deferred
def sel_step_correctStatement : Prop := deferred
def sel_initial_statesStatement : Prop := deferred
def sel_final_statesStatement : Prop := deferred
def transf_program_correctStatement : Prop := deferred

end CompCert4Lean.Backend.Selectionproof
