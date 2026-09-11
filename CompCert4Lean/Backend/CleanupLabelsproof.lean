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

namespace CompCert4Lean.Backend.CleanupLabelsproof

open CompCert4Lean.Backend.CleanupLabels
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib

theorem sig_function_translated : sig_function_translatedStatement := by
  intro f
  cases f <;> rfl

theorem add_label_branched_to_incr : add_label_branched_to_incrStatement := by
  intro ls i
  unfold Labelset.Subset
  intro x hx
  cases i with
  | Lgoto lbl => exact CompCert4Lean.Lib.FSetAVLplus.Make.add_2 ls lbl x hx
  | Lcond cond args lbl => exact CompCert4Lean.Lib.FSetAVLplus.Make.add_2 ls lbl x hx
  | Ljumptable arg tbl =>
      change Labelset.In x (tbl.foldr Labelset.add ls)
      induction tbl generalizing ls with
      | nil => exact hx
      | cons lbl tbl ih =>
          simp only [List.foldr]
          exact CompCert4Lean.Lib.FSetAVLplus.Make.add_2
            (List.foldr Labelset.add ls tbl) lbl x (ih ls hx)
  | Lgetstack sl ofs ty dst => exact hx
  | Lsetstack src sl ofs ty => exact hx
  | Lop op args res => exact hx
  | Lload chunk addr args dst => exact hx
  | Lstore chunk addr args src => exact hx
  | Lcall sig ros => exact hx
  | Ltailcall sig ros => exact hx
  | Lbuiltin ef args res => exact hx
  | Llabel lbl => exact hx
  | Lreturn => exact hx

theorem transf_program_match : transf_program_matchStatement := by
  letI : Linker fundef := Linker_fundef function
  letI : Linker program := Linker_prog fundef Unit
  intro p
  unfold match_prog CompCert4Lean.Backend.CleanupLabels.transf_program
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
                    ((id, Gfun (CompCert4Lean.Backend.CleanupLabels.transf_fundef f)) ::
                      List.map (transform_program_globdef
                        CompCert4Lean.Backend.CleanupLabels.transf_fundef) tl)
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
                      List.map (transform_program_globdef
                        CompCert4Lean.Backend.CleanupLabels.transf_fundef) tl)
                  apply list_forall2.cons
                  · constructor
                    · rfl
                    · apply match_globdef.match_globdef_var
                      exact match_globvar.match_globvar_intro _ _ _ _ _ _ rfl
                  · exact ih
  · exact ⟨rfl, rfl⟩

end CompCert4Lean.Backend.CleanupLabelsproof

namespace CompCert4Lean.Backend.CleanupLabelsproof

open CompCert4Lean.Backend.CleanupLabels
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib

private theorem cleanup_symbol_add_global
    (ge1 ge2 : Genv.t fundef Unit) (id : ident)
    (hm : ∀ id', CompCert4Lean.Lib.Maps.PTree.get id' ge2.genv_symb =
      CompCert4Lean.Lib.Maps.PTree.get id' ge1.genv_symb)
    (hn : ge2.genv_next = ge1.genv_next) :
    ∀ id', CompCert4Lean.Lib.Maps.PTree.get id'
      (CompCert4Lean.Lib.Maps.PTree.set id ge2.genv_next ge2.genv_symb) =
      CompCert4Lean.Lib.Maps.PTree.get id'
      (CompCert4Lean.Lib.Maps.PTree.set id ge1.genv_next ge1.genv_symb) := by
  intro id'
  have h2 := @CompCert4Lean.Lib.Maps.PTree.getSet_equation _ id' id
      ge2.genv_next ge2.genv_symb
  have h1 := @CompCert4Lean.Lib.Maps.PTree.getSet_equation _ id' id
      ge1.genv_next ge1.genv_symb
  by_cases h : id' = id
  · rw [h2, h1]
    simp only [dif_pos h]
    exact congrArg some hn
  · rw [h2, h1]
    simp only [dif_neg h]
    exact hm id'

private theorem cleanup_symbol_add_globals
    (xs ys : List (ident × globdef fundef Unit))
    (hxy : list_forall2 (fun a b => a.1 = b.1) xs ys)
    (ge1 ge2 : Genv.t fundef Unit)
    (hm : ∀ id', CompCert4Lean.Lib.Maps.PTree.get id' ge2.genv_symb =
      CompCert4Lean.Lib.Maps.PTree.get id' ge1.genv_symb)
    (hn : ge2.genv_next = ge1.genv_next) :
    ∀ id', CompCert4Lean.Lib.Maps.PTree.get id'
      (Genv.add_globals ge2 ys).genv_symb =
      CompCert4Lean.Lib.Maps.PTree.get id'
      (Genv.add_globals ge1 xs).genv_symb := by
  induction hxy generalizing ge1 ge2 with
  | nil =>
      intro id'
      simpa [Genv.add_globals] using hm id'
  | @cons a xs b ys hab htail ih =>
      rcases a with ⟨aid, ag⟩
      rcases b with ⟨bid, bg⟩
      change aid = bid at hab
      subst bid
      simp only [Genv.add_globals, List.foldl_cons]
      apply ih
      · intro id'
        exact cleanup_symbol_add_global ge1 ge2 aid hm hn id'
      · exact congrArg PArith.BinPos.Pos.succ hn

private theorem cleanup_add_globals_public
    (ge : Genv.t fundef Unit) (gl : List (ident × globdef fundef Unit)) :
    (Genv.add_globals ge gl).genv_public = ge.genv_public := by
  induction gl generalizing ge with
  | nil => rfl
  | cons idg gl ih =>
      simp only [Genv.add_globals, List.foldl_cons]
      simpa [Genv.add_globals, Genv.add_global] using ih (Genv.add_global ge idg)

private theorem cleanup_match_genvs_add_global
    (R : globdef fundef Unit → globdef fundef Unit → Prop)
    (ge1 ge2 : Genv.t fundef Unit) (id : ident)
    (g1 g2 : globdef fundef Unit)
    (hm : Genv.match_genvs R ge1 ge2) (hg : R g1 g2) :
    Genv.match_genvs R (Genv.add_global ge1 (id, g1))
      (Genv.add_global ge2 (id, g2)) := by
  constructor
  · exact congrArg PArith.BinPos.Pos.succ hm.mge_next
  · exact cleanup_symbol_add_global ge1 ge2 id hm.mge_symb hm.mge_next
  · intro b
    change option_rel R
      (CompCert4Lean.Lib.Maps.PTree.get b
        (CompCert4Lean.Lib.Maps.PTree.set ge1.genv_next g1 ge1.genv_defs))
      (CompCert4Lean.Lib.Maps.PTree.get b
        (CompCert4Lean.Lib.Maps.PTree.set ge2.genv_next g2 ge2.genv_defs))
    have h1 := @CompCert4Lean.Lib.Maps.PTree.getSet_equation
      (globdef fundef Unit) b ge1.genv_next g1 ge1.genv_defs
    have h2 := @CompCert4Lean.Lib.Maps.PTree.getSet_equation
      (globdef fundef Unit) b ge2.genv_next g2 ge2.genv_defs
    by_cases h : b = ge1.genv_next
    · have h' : b = ge2.genv_next := h.trans hm.mge_next.symm
      rw [h1, h2]
      simp only [dif_pos h, dif_pos h']
      exact option_rel.some g1 g2 hg
    · have h' : b ≠ ge2.genv_next := by
        intro hb
        apply h
        exact hb.trans hm.mge_next
      rw [h1, h2]
      simp only [dif_neg h, dif_neg h']
      exact hm.mge_defs b

private theorem cleanup_match_genvs_add_globals
    (R : globdef fundef Unit → globdef fundef Unit → Prop)
    (xs ys : List (ident × globdef fundef Unit))
    (hxy : list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) xs ys)
    (ge1 ge2 : Genv.t fundef Unit) (hm : Genv.match_genvs R ge1 ge2) :
    Genv.match_genvs R (Genv.add_globals ge1 xs) (Genv.add_globals ge2 ys) := by
  induction hxy generalizing ge1 ge2 with
  | nil => simpa [Genv.add_globals] using hm
  | @cons a xs b ys hab htail ih =>
      rcases a with ⟨aid, ag⟩
      rcases b with ⟨bid, bg⟩
      change aid = bid ∧ R ag bg at hab
      rcases hab with ⟨rfl, hab⟩
      simp only [Genv.add_globals, List.foldl_cons]
      apply ih
      simpa using (cleanup_match_genvs_add_global R ge1 ge2 aid ag bg hm hab)

private theorem cleanup_globalenvs_match
    (prog tprog : CompCert4Lean.Common.AST.program fundef Unit)
    (hm : match_prog prog tprog) :
    Genv.match_genvs
      (@match_globdef (CompCert4Lean.Common.AST.program fundef Unit)
        fundef Unit fundef Unit
        (@Linker_prog fundef Unit (Linker_fundef function) Linker_unit)
        (fun (_ : CompCert4Lean.Common.AST.program fundef Unit) f tf =>
          tf = CompCert4Lean.Backend.CleanupLabels.transf_fundef f)
        (fun _ _ : Unit => True) prog)
      (Genv.globalenv prog) (Genv.globalenv tprog) := by
  letI : Linker fundef := Linker_fundef function
  letI : Linker (CompCert4Lean.Common.AST.program fundef Unit) :=
    Linker_prog fundef Unit
  unfold match_prog match_program match_program_gen at hm
  let R : globdef fundef Unit → globdef fundef Unit → Prop :=
    match_globdef
      (fun (_ : CompCert4Lean.Common.AST.program fundef Unit) f tf =>
        tf = CompCert4Lean.Backend.CleanupLabels.transf_fundef f)
      (fun _ _ : Unit => True) prog
  have hempty : Genv.match_genvs R
      (Genv.empty_genv fundef Unit prog.prog_public)
      (Genv.empty_genv fundef Unit tprog.prog_public) := by
    constructor
    · rfl
    · intro id'
      rfl
    · intro b
      exact option_rel.none R
  have hlist_of : ∀ (xs ys : List (ident × globdef fundef Unit)),
      list_forall2 (match_ident_globdef
        (fun (_ : CompCert4Lean.Common.AST.program fundef Unit) f tf =>
          tf = CompCert4Lean.Backend.CleanupLabels.transf_fundef f)
        (fun x y : Unit => x = y) prog) xs ys →
      list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) xs ys := by
    intro xs ys h
    induction h with
    | nil => exact list_forall2.nil _
    | @cons a xs b ys hab htail ih =>
        apply list_forall2.cons
        · constructor
          · exact hab.1
          · simpa [R] using hab.2
        · exact ih
  have hlist := hlist_of prog.prog_defs tprog.prog_defs hm.1
  exact cleanup_match_genvs_add_globals R prog.prog_defs tprog.prog_defs
    hlist _ _ hempty

theorem symbols_preserved : symbols_preservedStatement := by
  intro prog tprog hm id
  letI : Linker fundef := Linker_fundef function
  letI : Linker (CompCert4Lean.Common.AST.program fundef Unit) :=
    Linker_prog fundef Unit
  unfold match_prog match_program match_program_gen at hm
  have hlist_of : ∀ (xs ys : List (ident × globdef fundef Unit)),
      list_forall2 (@match_ident_globdef program fundef Unit fundef Unit
        (Linker_prog fundef Unit)
        (fun _ f tf => tf = CompCert4Lean.Backend.CleanupLabels.transf_fundef f)
        (fun x y : Unit => x = y) prog) xs ys →
      list_forall2 (fun a b => a.1 = b.1) xs ys := by
    intro xs ys h
    induction h with
    | nil => exact list_forall2.nil _
    | @cons a xs b ys hab htail ih =>
        apply list_forall2.cons
        · exact hab.1
        · exact ih
  have hlist := hlist_of prog.prog_defs tprog.prog_defs hm.1
  have hempty : ∀ id',
      CompCert4Lean.Lib.Maps.PTree.get id'
        (Genv.empty_genv fundef Unit tprog.prog_public).genv_symb =
      CompCert4Lean.Lib.Maps.PTree.get id'
        (Genv.empty_genv fundef Unit prog.prog_public).genv_symb := by
    intro id'
    rfl
  have hnext :
      (Genv.empty_genv fundef Unit tprog.prog_public).genv_next =
      (Genv.empty_genv fundef Unit prog.prog_public).genv_next := rfl
  have hsymb := cleanup_symbol_add_globals prog.prog_defs tprog.prog_defs
    hlist (Genv.empty_genv fundef Unit prog.prog_public)
    (Genv.empty_genv fundef Unit tprog.prog_public) hempty hnext id
  simpa [Genv.find_symbol, Genv.globalenv] using hsymb

theorem function_ptr_translated : function_ptr_translatedStatement := by
  intro prog tprog hm b f hfind
  have hg := cleanup_globalenvs_match prog tprog hm
  unfold Genv.find_funct_ptr Genv.find_def at hfind ⊢
  cases h1 : CompCert4Lean.Lib.Maps.PTree.get b (Genv.globalenv prog).genv_defs with
  | none => simp [h1] at hfind
  | some gd1 =>
      cases gd1 with
      | Gfun f1 =>
          have hf : f1 = f := by simpa [h1] using hfind
          subst f1
          cases h2 : CompCert4Lean.Lib.Maps.PTree.get b (Genv.globalenv tprog).genv_defs with
          | none =>
              have hd := hg.mge_defs b
              simp [h1, h2] at hd
              cases hd
          | some gd2 =>
              cases gd2 with
              | Gfun f2 =>
                  have hd := hg.mge_defs b
                  simp [h1, h2] at hd
                  cases hd with
                  | some x y hrel =>
                      cases hrel with
                      | match_globdef_fun ctx' f1 f2 horder htrans =>
                          simpa using htrans
              | Gvar v2 =>
                  have hd := hg.mge_defs b
                  simp [h1, h2] at hd
                  cases hd with
                  | some x y hrel => cases hrel
      | Gvar v1 => simp [h1] at hfind

theorem functions_translated : functions_translatedStatement := by
  intro prog tprog hm v f hfind
  unfold Genv.find_funct at hfind ⊢
  cases v with
  | Vundef => simp at hfind
  | Vint n => simp at hfind
  | Vlong n => simp at hfind
  | Vfloat n => simp at hfind
  | Vsingle n => simp at hfind
  | Vptr b ofs =>
      cases hzero : CompCert4Lean.Lib.Integers.Ptrofs.eq ofs
          CompCert4Lean.Lib.Integers.Ptrofs.zero with
      | false => simp [hzero] at hfind
      | true =>
          simp [hzero] at hfind ⊢
          exact function_ptr_translated prog tprog hm b f hfind

theorem senv_preserved : senv_preservedStatement := by
  intro prog tprog hm
  unfold Senv.equiv
  constructor
  · intro id
    exact symbols_preserved prog tprog hm id
  constructor
  · intro id
    change Genv.public_symbol (Genv.globalenv tprog) id =
      Genv.public_symbol (Genv.globalenv prog) id
    have ht : (Genv.globalenv tprog).genv_public = tprog.prog_public := by
      unfold Genv.globalenv
      exact cleanup_add_globals_public _ _
    have hp : (Genv.globalenv prog).genv_public = prog.prog_public := by
      unfold Genv.globalenv
      exact cleanup_add_globals_public _ _
    unfold Genv.public_symbol
    rw [symbols_preserved prog tprog hm id]
    unfold match_prog match_program match_program_gen at hm
    rw [ht, hp, hm.2.2]
  · intro b
    change Genv.block_is_volatile (Genv.globalenv tprog) b =
      Genv.block_is_volatile (Genv.globalenv prog) b
    have hg := cleanup_globalenvs_match prog tprog hm
    unfold Genv.block_is_volatile Genv.find_var_info Genv.find_def
    cases h1 : CompCert4Lean.Lib.Maps.PTree.get b (Genv.globalenv prog).genv_defs with
    | none =>
        cases h2 : CompCert4Lean.Lib.Maps.PTree.get b (Genv.globalenv tprog).genv_defs with
        | none => rfl
        | some gd2 =>
            have hd := hg.mge_defs b
            simp [h1, h2] at hd
            cases hd
    | some gd1 =>
        cases h2 : CompCert4Lean.Lib.Maps.PTree.get b (Genv.globalenv tprog).genv_defs with
        | none =>
            have hd := hg.mge_defs b
            simp [h1, h2] at hd
            cases hd
        | some gd2 =>
            have hd := hg.mge_defs b
            simp [h1, h2] at hd
            cases hd with
            | some x y hrel =>
                cases hrel with
                | match_globdef_fun ctx' f1 f2 horder htrans => rfl
                | match_globdef_var v1 v2 hvar =>
                    cases hvar
                    rfl

end CompCert4Lean.Backend.CleanupLabelsproof

namespace CompCert4Lean.Backend.CleanupLabelsproof

open CompCert4Lean.Backend.CleanupLabels
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib

theorem add_label_branched_to_contains : add_label_branched_to_containsStatement := by
  intro ls i lbl hbranch
  cases i with
  | Lgoto target =>
      change lbl = target at hbranch
      exact CompCert4Lean.Lib.FSetAVLplus.Make.add_1 ls target lbl hbranch.symm
  | Lcond cond args target =>
      change lbl = target at hbranch
      exact CompCert4Lean.Lib.FSetAVLplus.Make.add_1 ls target lbl hbranch.symm
  | Ljumptable arg tbl =>
      change lbl ∈ tbl at hbranch
      change Labelset.In lbl (tbl.foldr Labelset.add ls)
      induction tbl with
      | nil => exact (_root_.List.not_mem_nil hbranch).elim
      | cons target tbl ih =>
          simp only [List.foldr, _root_.List.mem_cons] at hbranch ⊢
          rcases hbranch with hEq | hMem
          · exact CompCert4Lean.Lib.FSetAVLplus.Make.add_1
              (tbl.foldr Labelset.add ls) target lbl hEq.symm
          · exact CompCert4Lean.Lib.FSetAVLplus.Make.add_2
              (tbl.foldr Labelset.add ls) target lbl (ih hMem)
  | Lgetstack sl ofs ty dst => exact (False.elim hbranch)
  | Lsetstack src sl ofs ty => exact (False.elim hbranch)
  | Lop op args res => exact (False.elim hbranch)
  | Lload chunk addr args dst => exact (False.elim hbranch)
  | Lstore chunk addr args src => exact (False.elim hbranch)
  | Lcall sig ros => exact (False.elim hbranch)
  | Ltailcall sig ros => exact (False.elim hbranch)
  | Lbuiltin ef args res => exact (False.elim hbranch)
  | Llabel target => exact (False.elim hbranch)
  | Lreturn => exact (False.elim hbranch)

private theorem cleanup_labels_list_fold_left_append
    {A B : Type} (f : A → B → B) (acc : B) (xs ys : List A) :
    list_fold_left f acc (xs ++ ys) =
      list_fold_left f (list_fold_left f acc xs) ys := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, list_fold_left]
      exact ih (f x acc)

private theorem cleanup_labels_list_fold_right_cons
    {A B : Type} (f : A → B → B) (x : A) (xs : List A) (acc : B) :
    list_fold_right f (x :: xs) acc =
      f x (list_fold_right f xs acc) := by
  unfold list_fold_right
  rw [List.reverse_cons, cleanup_labels_list_fold_left_append]
  rfl

theorem remove_unused_labels_cons : remove_unused_labels_consStatement := by
  intro bto i c
  unfold CompCert4Lean.Backend.CleanupLabels.remove_unused_labels
  change list_fold_right (remove_unused bto) (i :: c) [] = _
  calc
    list_fold_right (remove_unused bto) (i :: c) [] =
        remove_unused bto i (list_fold_right (remove_unused bto) c []) :=
      cleanup_labels_list_fold_right_cons (remove_unused bto) i c []
    _ = _ := by rfl

theorem labels_branched_to_correct : labels_branched_to_correctStatement := by
  intro c i lbl hi hbranch
  have fold_preserves : ∀ (c' : code) (bto : Labelset.t),
      Labelset.Subset bto
        (List.foldl (fun ls j => add_label_branched_to ls j) bto c') := by
    intro c' bto
    induction c' generalizing bto with
    | nil => intro x hx; exact hx
    | cons j js ih =>
        simp only [List.foldl]
        intro x hx
        exact ih (add_label_branched_to bto j) x
          (add_label_branched_to_incr bto j x hx)
  have mem_fold : ∀ (c' : code) (bto : Labelset.t),
      CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.In i c' →
        instr_branches_to i lbl →
      Labelset.In lbl
        (List.foldl (fun ls j => add_label_branched_to ls j) bto c') := by
    intro c' bto hi' hbranch'
    induction c' generalizing bto with
    | nil => exact (_root_.List.not_mem_nil hi').elim
    | cons j js ih =>
        simp only [List.foldl]
        rcases (_root_.List.mem_cons.mp hi') with hhead | htail
        · subst j
          apply fold_preserves js (add_label_branched_to bto i) lbl
          exact add_label_branched_to_contains bto i lbl hbranch'
        · exact ih (add_label_branched_to bto j) htail
  unfold CompCert4Lean.Backend.CleanupLabels.labels_branched_to
  exact mem_fold c Labelset.empty hi hbranch

theorem find_function_translated : find_function_translatedStatement := by
  intro prog tprog hm ros ls f hfind
  unfold CompCert4Lean.Backend.Linear.find_function at hfind ⊢
  cases ros with
  | inl r =>
      exact functions_translated prog tprog hm
        (ls (CompCert4Lean.Backend.Locations.R r)) f hfind
  | inr symb =>
      change
        (match Genv.find_symbol (Genv.globalenv prog) symb with
        | none => none
        | some b => Genv.find_funct_ptr (Genv.globalenv prog) b) = some f at hfind
      change
        (match Genv.find_symbol (Genv.globalenv tprog) symb with
        | none => none
        | some b => Genv.find_funct_ptr (Genv.globalenv tprog) b) =
          some (CompCert4Lean.Backend.CleanupLabels.transf_fundef f)
      cases hs : Genv.find_symbol (Genv.globalenv prog) symb with
      | none => simp [hs] at hfind
      | some b =>
          have hs' := symbols_preserved prog tprog hm symb
          rw [hs', hs]
          exact function_ptr_translated prog tprog hm b f (by simpa [hs] using hfind)

end CompCert4Lean.Backend.CleanupLabelsproof

namespace CompCert4Lean.Backend.CleanupLabelsproof

open CompCert4Lean.Backend.CleanupLabels
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib

theorem find_label_incl : find_label_inclStatement := by
  intro lbl c
  induction c with
  | nil =>
      intro c' h
      simp [CompCert4Lean.Backend.Linear.find_label] at h
  | cons i c ih =>
      intro c' h
      change (if CompCert4Lean.Backend.Linear.is_label lbl i then some c
        else CompCert4Lean.Backend.Linear.find_label lbl c) = some c' at h
      by_cases hi : CompCert4Lean.Backend.Linear.is_label lbl i = true
      · simp [hi] at h
        cases h
        exact CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.incl_tl _
          (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.incl_refl _)
      · simp [hi] at h
        exact CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.incl_tl i (ih c' h)

theorem match_parent_locset : match_parent_locsetStatement := by
  intro s ts h
  induction h with
  | nil => rfl
  | cons a1 b1 hab hrest ih =>
      cases hab
      rfl

end CompCert4Lean.Backend.CleanupLabelsproof

namespace CompCert4Lean.Backend.CleanupLabelsproof

open CompCert4Lean.Backend.CleanupLabels
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib

theorem find_label_commut : find_label_commutStatement := by
  intro lbl bto hl
  intro c
  induction c with
  | nil =>
      intro c' h
      simp [CompCert4Lean.Backend.Linear.find_label] at h
  | cons i c ih =>
      intro c' h
      have hrem := remove_unused_labels_cons bto i c
      rw [hrem]
      cases i with
      | Llabel l =>
          cases hp : CompCert4Lean.Lib.Coqlib.peq lbl l with
          | left heq =>
              subst l
              simp [CompCert4Lean.Backend.Linear.find_label,
                CompCert4Lean.Backend.Linear.is_label, hp] at h
              cases h
              simp [CompCert4Lean.Backend.Linear.find_label,
                CompCert4Lean.Backend.Linear.is_label, hp]
              have hmem : Labelset.mem lbl bto = true :=
                Labelset.mem_1_proof bto lbl hl
              simp [hmem, CompCert4Lean.Backend.Linear.find_label,
                CompCert4Lean.Backend.Linear.is_label, hp]
          | right hne =>
              simp [CompCert4Lean.Backend.Linear.find_label,
                CompCert4Lean.Backend.Linear.is_label, hp] at h
              by_cases hmem : Labelset.mem l bto = true
              · simp [hmem, CompCert4Lean.Backend.Linear.find_label,
                  CompCert4Lean.Backend.Linear.is_label, hp]
                exact ih c' h
              · simp [hmem]
                exact ih c' h
      | Lgetstack sl ofs ty dst =>
          simp [CompCert4Lean.Backend.Linear.find_label,
            CompCert4Lean.Backend.Linear.is_label] at h ⊢
          exact ih c' h
      | Lsetstack src sl ofs ty =>
          simp [CompCert4Lean.Backend.Linear.find_label,
            CompCert4Lean.Backend.Linear.is_label] at h ⊢
          exact ih c' h
      | Lop op args res =>
          simp [CompCert4Lean.Backend.Linear.find_label,
            CompCert4Lean.Backend.Linear.is_label] at h ⊢
          exact ih c' h
      | Lload chunk addr args dst =>
          simp [CompCert4Lean.Backend.Linear.find_label,
            CompCert4Lean.Backend.Linear.is_label] at h ⊢
          exact ih c' h
      | Lstore chunk addr args src =>
          simp [CompCert4Lean.Backend.Linear.find_label,
            CompCert4Lean.Backend.Linear.is_label] at h ⊢
          exact ih c' h
      | Lcall sig ros =>
          simp [CompCert4Lean.Backend.Linear.find_label,
            CompCert4Lean.Backend.Linear.is_label] at h ⊢
          exact ih c' h
      | Ltailcall sig ros =>
          simp [CompCert4Lean.Backend.Linear.find_label,
            CompCert4Lean.Backend.Linear.is_label] at h ⊢
          exact ih c' h
      | Lbuiltin ef args res =>
          simp [CompCert4Lean.Backend.Linear.find_label,
            CompCert4Lean.Backend.Linear.is_label] at h ⊢
          exact ih c' h
      | Lgoto l =>
          simp [CompCert4Lean.Backend.Linear.find_label,
            CompCert4Lean.Backend.Linear.is_label] at h ⊢
          exact ih c' h
      | Lcond cond args l =>
          simp [CompCert4Lean.Backend.Linear.find_label,
            CompCert4Lean.Backend.Linear.is_label] at h ⊢
          exact ih c' h
      | Ljumptable arg tbl =>
          simp [CompCert4Lean.Backend.Linear.find_label,
            CompCert4Lean.Backend.Linear.is_label] at h ⊢
          exact ih c' h
      | Lreturn =>
          simp [CompCert4Lean.Backend.Linear.find_label,
            CompCert4Lean.Backend.Linear.is_label] at h ⊢
          exact ih c' h

end CompCert4Lean.Backend.CleanupLabelsproof

namespace CompCert4Lean.Backend.CleanupLabelsproof

open CompCert4Lean.Backend.CleanupLabels
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib

theorem find_label_translated : find_label_translatedStatement := by
  intro f i c' lbl c hinc hfind hbranch
  change find_label lbl
      (remove_unused_labels (labels_branched_to f.fn_code) f.fn_code) =
    some (remove_unused_labels (labels_branched_to f.fn_code) c)
  apply find_label_commut lbl (labels_branched_to f.fn_code)
  exact labels_branched_to_correct f.fn_code i lbl
    (hinc i (List.mem_cons_self)) hbranch
  exact hfind

end CompCert4Lean.Backend.CleanupLabelsproof
