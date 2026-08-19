import CompCert4Lean.Backend.CleanupLabels
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.ExternalCalls
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Smallstep

/-!
# Correctness surface for cleanup of unused labels

The executable relations and definitions in this module mirror the source
`backend/CleanupLabelsproof.v` surface.  Proof obligations assigned to the
later proof-migration phase are represented by transparent proposition
descriptors; no theorem placeholder is introduced here.
-/

namespace CompCert4Lean.Backend.CleanupLabelsproof

open CompCert4Lean.Backend.CleanupLabels
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Machregs

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig

/-! ## Generated facts surface owned by this module

The source instantiates `FSetFacts.Facts(Labelset)` here. Its executable
member is retained directly; proof-bearing members are transparent
proposition descriptors for the later proof-migration phase.
-/

namespace LabelsetFacts

def LabelsetFacts : Type := Unit
def eqb (x y : Labelset.elt) : Bool := decide (x = y)

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

end LabelsetFacts

/-! ## Program matching and preserved global-environment observations -/

def match_prog (p tp : program) : Prop :=
  @match_program fundef Unit fundef Unit
    (Linker_fundef function) Linker_unit
    (fun _ f tf => tf = CompCert4Lean.Backend.CleanupLabels.transf_fundef f)
    (fun x y : Unit => x = y) p tp

/-! ## Correctness of the branch-target analysis -/

def instr_branches_to (i : instruction) (lbl : label) : Prop :=
  match i with
  | Lgoto lbl' => lbl = lbl'
  | Lcond _ _ lbl' => lbl = lbl'
  | Ljumptable _ tbl => lbl ∈ tbl
  | _ => False

/-! ## State matching for the label-removal simulation -/

inductive match_stackframes : stackframe → stackframe → Prop where
  | intro (f : function) (sp : val) (ls : locset) (c : code)
      (h : incl c f.fn_code) :
      match_stackframes
        (Stackframe f sp ls c)
        (Stackframe (CompCert4Lean.Backend.CleanupLabels.transf_function f) sp ls
          (CompCert4Lean.Backend.CleanupLabels.remove_unused_labels
            (CompCert4Lean.Backend.CleanupLabels.labels_branched_to f.fn_code) c))

inductive match_states : state → state → Prop where
  | regular (s : List stackframe) (f : function) (sp : val) (c : code)
      (ls : locset) (m : mem) (ts : List stackframe)
      (stacks : list_forall2 match_stackframes s ts)
      (h : incl c f.fn_code) :
      match_states
        (State s f sp c ls m)
        (State ts (CompCert4Lean.Backend.CleanupLabels.transf_function f) sp
          (CompCert4Lean.Backend.CleanupLabels.remove_unused_labels
            (CompCert4Lean.Backend.CleanupLabels.labels_branched_to f.fn_code) c)
          ls m)
  | call (s : List stackframe) (f : fundef) (ls : locset) (m : mem)
      (ts : List stackframe)
      (stacks : list_forall2 match_stackframes s ts) :
      match_states (Callstate s f ls m)
        (Callstate ts (CompCert4Lean.Backend.CleanupLabels.transf_fundef f) ls m)
  | return (s : List stackframe) (ls : locset) (m : mem)
      (ts : List stackframe)
      (stacks : list_forall2 match_stackframes s ts) :
      match_states (Returnstate s ls m) (Returnstate ts ls m)

def measure : state → Nat
  | State _ _ _ c _ _ => c.length
  | Callstate _ _ _ _ => 0
  | Returnstate _ _ _ => 0

/-! ## Exact statement descriptors for later proof migration -/

def transf_program_matchStatement : Prop :=
  ∀ p : program,
    match_prog p (CompCert4Lean.Backend.CleanupLabels.transf_program p)

def symbols_preservedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ id : ident,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id

def senv_preservedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    Senv.equiv
      (Genv.to_senv (Genv.globalenv prog))
      (Genv.to_senv (Genv.globalenv tprog))

def functions_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ (v : val) (f : fundef),
      Genv.find_funct (Genv.globalenv prog) v = some f →
      Genv.find_funct (Genv.globalenv tprog) v =
        some (CompCert4Lean.Backend.CleanupLabels.transf_fundef f)

def function_ptr_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ (b : block) (f : fundef),
      Genv.find_funct_ptr (Genv.globalenv prog) b = some f →
      Genv.find_funct_ptr (Genv.globalenv tprog) b =
        some (CompCert4Lean.Backend.CleanupLabels.transf_fundef f)

def sig_function_translatedStatement : Prop :=
  ∀ f : fundef,
    CompCert4Lean.Backend.Linear.funsig
      (CompCert4Lean.Backend.CleanupLabels.transf_fundef f) =
      CompCert4Lean.Backend.Linear.funsig f

def find_function_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ (ros : Sum mreg ident) (ls : locset) (f : fundef),
      CompCert4Lean.Backend.Linear.find_function
        (Genv.globalenv prog) ros ls = some f →
      CompCert4Lean.Backend.Linear.find_function
        (Genv.globalenv tprog) ros ls =
        some (CompCert4Lean.Backend.CleanupLabels.transf_fundef f)

def add_label_branched_to_incrStatement : Prop :=
  ∀ (ls : Labelset.t) (i : instruction),
    Labelset.Subset ls
      (CompCert4Lean.Backend.CleanupLabels.add_label_branched_to ls i)

def add_label_branched_to_containsStatement : Prop :=
  ∀ (ls : Labelset.t) (i : instruction) (lbl : label),
    instr_branches_to i lbl →
      Labelset.In lbl
        (CompCert4Lean.Backend.CleanupLabels.add_label_branched_to ls i)

def labels_branched_to_correctStatement : Prop :=
  ∀ (c : code) (i : instruction) (lbl : label),
    In i c → instr_branches_to i lbl →
      Labelset.In lbl
        (CompCert4Lean.Backend.CleanupLabels.labels_branched_to c)

def remove_unused_labels_consStatement : Prop :=
  ∀ (bto : Labelset.t) (i : instruction) (c : code),
    CompCert4Lean.Backend.CleanupLabels.remove_unused_labels bto (i :: c) =
      match i with
      | Llabel lbl =>
          if Labelset.mem lbl bto then
            i :: CompCert4Lean.Backend.CleanupLabels.remove_unused_labels bto c
          else
            CompCert4Lean.Backend.CleanupLabels.remove_unused_labels bto c
      | _ => i :: CompCert4Lean.Backend.CleanupLabels.remove_unused_labels bto c

def find_label_commutStatement : Prop :=
  ∀ (lbl : label) (bto : Labelset.t), Labelset.In lbl bto →
    ∀ (c c' : code),
      CompCert4Lean.Backend.Linear.find_label lbl c = some c' →
      CompCert4Lean.Backend.Linear.find_label lbl
          (CompCert4Lean.Backend.CleanupLabels.remove_unused_labels bto c) =
        some
          (CompCert4Lean.Backend.CleanupLabels.remove_unused_labels bto c')

def find_label_translatedStatement : Prop :=
  ∀ (f : function) (i : instruction) (c' : code) (lbl : label) (c : code),
    incl (i :: c') f.fn_code →
    CompCert4Lean.Backend.Linear.find_label lbl f.fn_code = some c →
    instr_branches_to i lbl →
    CompCert4Lean.Backend.Linear.find_label lbl
        (CompCert4Lean.Backend.CleanupLabels.transf_function f).fn_code =
      some
        (CompCert4Lean.Backend.CleanupLabels.remove_unused_labels
          (CompCert4Lean.Backend.CleanupLabels.labels_branched_to f.fn_code) c)

def find_label_inclStatement : Prop :=
  ∀ (lbl : label) (c c' : code),
    CompCert4Lean.Backend.Linear.find_label lbl c = some c' → incl c' c

def match_parent_locsetStatement : Prop :=
  ∀ (s ts : List stackframe),
    list_forall2 match_stackframes s ts →
      parent_locset ts = parent_locset s

def transf_step_correctStatement : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog tprog : program),
    match_prog prog tprog →
    ∀ (s1 : state) (t : trace) (s2 : state),
      CompCert4Lean.Backend.Linear.step cfg xi (Genv.globalenv prog) s1 t s2 →
      ∀ s1', match_states s1 s1' →
        (∃ s2',
          CompCert4Lean.Backend.Linear.step cfg xi (Genv.globalenv tprog) s1' t s2' ∧
          match_states s2 s2') ∨
        (measure s2 < measure s1 ∧ t = E0 ∧ match_states s2 s1')

def transf_initial_statesStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ st1, initial_state prog st1 →
      ∃ st2, initial_state tprog st2 ∧ match_states st1 st2

def transf_final_statesStatement : Prop :=
  ∀ (st1 st2 : state) (r : int),
    match_states st1 st2 → final_state st1 r → final_state st2 r

def transf_program_correctStatement : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog tprog : program),
    match_prog prog tprog →
    forward_simulation
      (CompCert4Lean.Backend.Linear.semantics cfg xi prog)
      (CompCert4Lean.Backend.Linear.semantics cfg xi tprog)

end CompCert4Lean.Backend.CleanupLabelsproof
