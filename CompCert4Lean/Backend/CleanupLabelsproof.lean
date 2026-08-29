import CompCert4Lean.Backend.CleanupLabels
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.ExternalCalls
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Foundation.Numbers

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
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
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
def eqb (x y : Labelset.elt) : Bool :=
  match CompCert4Lean.Backend.Registers.Regset.E.eq_dec x y with
  | .left _ => true
  | .right _ => false

abbrev E_ST := CompCert4Lean.Backend.Registers.RegsetFacts.E_ST
abbrev Empty_m := CompCert4Lean.Backend.Registers.RegsetFacts.Empty_m
abbrev Empty_s_m := CompCert4Lean.Backend.Registers.RegsetFacts.Empty_s_m
abbrev Empty_s_m_Proper := CompCert4Lean.Backend.Registers.RegsetFacts.Empty_s_m_Proper
abbrev Equal_ST := CompCert4Lean.Backend.Registers.RegsetFacts.Equal_ST
abbrev In_eq_iff := CompCert4Lean.Backend.Registers.RegsetFacts.In_eq_iff
abbrev In_m := CompCert4Lean.Backend.Registers.RegsetFacts.In_m
abbrev In_s_m := CompCert4Lean.Backend.Registers.RegsetFacts.In_s_m
abbrev SubsetSetoid := CompCert4Lean.Backend.Registers.RegsetFacts.SubsetSetoid
abbrev SubsetSetoid_Reflexive :=
  CompCert4Lean.Backend.Registers.RegsetFacts.SubsetSetoid_Reflexive
abbrev SubsetSetoid_Transitive :=
  CompCert4Lean.Backend.Registers.RegsetFacts.SubsetSetoid_Transitive
abbrev SubsetSetoid_relation :=
  CompCert4Lean.Backend.Registers.RegsetFacts.SubsetSetoid_relation
abbrev Subset_m := CompCert4Lean.Backend.Registers.RegsetFacts.Subset_m
abbrev Subset_refl := CompCert4Lean.Backend.Registers.RegsetFacts.Subset_refl
abbrev Subset_trans := CompCert4Lean.Backend.Registers.RegsetFacts.Subset_trans
abbrev add_b := CompCert4Lean.Backend.Registers.RegsetFacts.add_b
abbrev add_iff := CompCert4Lean.Backend.Registers.RegsetFacts.add_iff
abbrev add_m := CompCert4Lean.Backend.Registers.RegsetFacts.add_m
abbrev add_neq_b := CompCert4Lean.Backend.Registers.RegsetFacts.add_neq_b
abbrev add_neq_iff := CompCert4Lean.Backend.Registers.RegsetFacts.add_neq_iff
abbrev add_s_m := CompCert4Lean.Backend.Registers.RegsetFacts.add_s_m
abbrev add_s_m_Proper := CompCert4Lean.Backend.Registers.RegsetFacts.add_s_m_Proper
abbrev diff_b := CompCert4Lean.Backend.Registers.RegsetFacts.diff_b
abbrev diff_iff := CompCert4Lean.Backend.Registers.RegsetFacts.diff_iff
abbrev diff_m := CompCert4Lean.Backend.Registers.RegsetFacts.diff_m
abbrev diff_s_m := CompCert4Lean.Backend.Registers.RegsetFacts.diff_s_m
abbrev diff_s_m_Proper := CompCert4Lean.Backend.Registers.RegsetFacts.diff_s_m_Proper
abbrev elements_b := CompCert4Lean.Backend.Registers.RegsetFacts.elements_b
abbrev elements_iff := CompCert4Lean.Backend.Registers.RegsetFacts.elements_iff
abbrev empty_b := CompCert4Lean.Backend.Registers.RegsetFacts.empty_b
abbrev empty_iff := CompCert4Lean.Backend.Registers.RegsetFacts.empty_iff
abbrev equal_iff := CompCert4Lean.Backend.Registers.RegsetFacts.equal_iff
abbrev equal_m := CompCert4Lean.Backend.Registers.RegsetFacts.equal_m
abbrev exists_b := CompCert4Lean.Backend.Registers.RegsetFacts.exists_b
abbrev exists_iff := CompCert4Lean.Backend.Registers.RegsetFacts.exists_iff
abbrev filter_b := CompCert4Lean.Backend.Registers.RegsetFacts.filter_b
abbrev filter_equal := CompCert4Lean.Backend.Registers.RegsetFacts.filter_equal
abbrev filter_ext := CompCert4Lean.Backend.Registers.RegsetFacts.filter_ext
abbrev filter_iff := CompCert4Lean.Backend.Registers.RegsetFacts.filter_iff
abbrev filter_subset := CompCert4Lean.Backend.Registers.RegsetFacts.filter_subset
abbrev for_all_b := CompCert4Lean.Backend.Registers.RegsetFacts.for_all_b
abbrev for_all_iff := CompCert4Lean.Backend.Registers.RegsetFacts.for_all_iff
abbrev inter_b := CompCert4Lean.Backend.Registers.RegsetFacts.inter_b
abbrev inter_iff := CompCert4Lean.Backend.Registers.RegsetFacts.inter_iff
abbrev inter_m := CompCert4Lean.Backend.Registers.RegsetFacts.inter_m
abbrev inter_s_m := CompCert4Lean.Backend.Registers.RegsetFacts.inter_s_m
abbrev inter_s_m_Proper := CompCert4Lean.Backend.Registers.RegsetFacts.inter_s_m_Proper
abbrev is_empty_iff := CompCert4Lean.Backend.Registers.RegsetFacts.is_empty_iff
abbrev is_empty_m := CompCert4Lean.Backend.Registers.RegsetFacts.is_empty_m
abbrev mem_b := CompCert4Lean.Backend.Registers.RegsetFacts.mem_b
abbrev mem_iff := CompCert4Lean.Backend.Registers.RegsetFacts.mem_iff
abbrev mem_m := CompCert4Lean.Backend.Registers.RegsetFacts.mem_m
abbrev not_mem_iff := CompCert4Lean.Backend.Registers.RegsetFacts.not_mem_iff
abbrev remove_b := CompCert4Lean.Backend.Registers.RegsetFacts.remove_b
abbrev remove_iff := CompCert4Lean.Backend.Registers.RegsetFacts.remove_iff
abbrev remove_m := CompCert4Lean.Backend.Registers.RegsetFacts.remove_m
abbrev remove_neq_b := CompCert4Lean.Backend.Registers.RegsetFacts.remove_neq_b
abbrev remove_neq_iff := CompCert4Lean.Backend.Registers.RegsetFacts.remove_neq_iff
abbrev remove_s_m := CompCert4Lean.Backend.Registers.RegsetFacts.remove_s_m
abbrev remove_s_m_Proper := CompCert4Lean.Backend.Registers.RegsetFacts.remove_s_m_Proper
abbrev singleton_b := CompCert4Lean.Backend.Registers.RegsetFacts.singleton_b
abbrev singleton_iff := CompCert4Lean.Backend.Registers.RegsetFacts.singleton_iff
abbrev singleton_m := CompCert4Lean.Backend.Registers.RegsetFacts.singleton_m
abbrev subset_iff := CompCert4Lean.Backend.Registers.RegsetFacts.subset_iff
abbrev subset_m := CompCert4Lean.Backend.Registers.RegsetFacts.subset_m
abbrev union_b := CompCert4Lean.Backend.Registers.RegsetFacts.union_b
abbrev union_iff := CompCert4Lean.Backend.Registers.RegsetFacts.union_iff
abbrev union_m := CompCert4Lean.Backend.Registers.RegsetFacts.union_m
abbrev union_s_m := CompCert4Lean.Backend.Registers.RegsetFacts.union_s_m
abbrev union_s_m_Proper := CompCert4Lean.Backend.Registers.RegsetFacts.union_s_m_Proper

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

/-! Source-facing constructor endpoint for the pinned Rocq binder surface. -/
abbrev match_stackframe_intro := @match_stackframes.intro

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

/-! Source-facing constructor endpoints for the pinned Rocq binder surfaces. -/
abbrev match_states_intro := @match_states.regular
abbrev match_states_call := @match_states.call
abbrev match_states_return := @match_states.return

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

def transf_step_correctStatement
  [binary64_certificate :
    CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
  [binary32_certificate :
    CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (prog tprog : program),
    match_prog prog tprog →
    ∀ (s1 : state) (t : trace) (s2 : state),
      CompCert4Lean.Backend.Linear.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg xi (Genv.globalenv prog) s1 t s2 →
      ∀ s1', match_states s1 s1' →
        (∃ s2',
          CompCert4Lean.Backend.Linear.step
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            cfg xi (Genv.globalenv tprog) s1' t s2' ∧
          match_states s2 s2') ∨
        (measure s2 < measure s1 ∧ t = E0 ∧ match_states s2 s1')

def transf_initial_statesStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ st1, initial_state prog st1 →
      ∃ st2, initial_state tprog st2 ∧ match_states st1 st2

def transf_final_statesStatement : Prop :=
  ∀ (st1 st2 : state) (r : int),
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
      (CompCert4Lean.Backend.Linear.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg xi prog)
      (CompCert4Lean.Backend.Linear.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg xi tprog)

end CompCert4Lean.Backend.CleanupLabelsproof
