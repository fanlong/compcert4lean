import CompCert4Lean.Backend.Linearize
import CompCert4Lean.Common.ExternalCalls
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Common.Values
import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Lib.FSetFacts

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
abbrev EnumerationService := CompCert4Lean.Backend.Linearize.EnumerationService

/-! ## Generated finite-set facts surface -/

namespace NodesetFacts

def NodesetFacts : Type := Unit
def eqb (x y : CompCert4Lean.Backend.Linearize.Nodeset.elt) : Bool :=
  match CompCert4Lean.Lib.Coqlib.peq x y with
  | .left _ => true
  | .right _ => false

abbrev F := CompCert4Lean.Lib.FSetAVLplus.Make.MF
  CompCert4Lean.Backend.Linearize.Nodeset.E
abbrev E_ST := CompCert4Lean.Lib.FSetFacts.WFacts_fun.E_ST F
abbrev Empty_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.Empty_m F
abbrev Empty_s_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.Empty_s_m F
abbrev Empty_s_m_Proper := CompCert4Lean.Lib.FSetFacts.WFacts_fun.Empty_s_m_Proper F
abbrev Equal_ST := CompCert4Lean.Lib.FSetFacts.WFacts_fun.Equal_ST F
abbrev In_eq_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.In_eq_iff F
abbrev In_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.In_m F
abbrev In_s_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.In_s_m F
abbrev SubsetSetoid := CompCert4Lean.Lib.FSetFacts.WFacts_fun.SubsetSetoid F
abbrev SubsetSetoid_Reflexive :=
  CompCert4Lean.Lib.FSetFacts.WFacts_fun.SubsetSetoid_Reflexive F
abbrev SubsetSetoid_Transitive :=
  CompCert4Lean.Lib.FSetFacts.WFacts_fun.SubsetSetoid_Transitive F
abbrev SubsetSetoid_relation :=
  CompCert4Lean.Lib.FSetFacts.WFacts_fun.SubsetSetoid_relation F
abbrev Subset_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.Subset_m F
abbrev Subset_refl := CompCert4Lean.Lib.FSetFacts.WFacts_fun.Subset_refl F
abbrev Subset_trans := CompCert4Lean.Lib.FSetFacts.WFacts_fun.Subset_trans F
abbrev add_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_b F
abbrev add_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_iff F
abbrev add_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_m F
abbrev add_neq_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_neq_b F
abbrev add_neq_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_neq_iff F
abbrev add_s_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_s_m F
abbrev add_s_m_Proper := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_s_m_Proper F
abbrev diff_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.diff_b F
abbrev diff_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.diff_iff F
abbrev diff_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.diff_m F
abbrev diff_s_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.diff_s_m F
abbrev diff_s_m_Proper := CompCert4Lean.Lib.FSetFacts.WFacts_fun.diff_s_m_Proper F
abbrev elements_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.elements_b F
abbrev elements_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.elements_iff F
abbrev empty_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.empty_b F
abbrev empty_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.empty_iff F
abbrev equal_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.equal_iff F
abbrev equal_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.equal_m F
abbrev exists_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.exists_b F
abbrev exists_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.exists_iff F
abbrev filter_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.filter_b F
abbrev filter_equal := CompCert4Lean.Lib.FSetFacts.WFacts_fun.filter_equal F
abbrev filter_ext := CompCert4Lean.Lib.FSetFacts.WFacts_fun.filter_ext F
abbrev filter_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.filter_iff F
abbrev filter_subset := CompCert4Lean.Lib.FSetFacts.WFacts_fun.filter_subset F
abbrev for_all_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.for_all_b F
abbrev for_all_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.for_all_iff F
abbrev inter_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.inter_b F
abbrev inter_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.inter_iff F
abbrev inter_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.inter_m F
abbrev inter_s_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.inter_s_m F
abbrev inter_s_m_Proper := CompCert4Lean.Lib.FSetFacts.WFacts_fun.inter_s_m_Proper F
abbrev is_empty_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.is_empty_iff F
abbrev is_empty_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.is_empty_m F
abbrev mem_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.mem_b F
abbrev mem_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.mem_iff F
abbrev mem_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.mem_m F
abbrev not_mem_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.not_mem_iff F
abbrev remove_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_b F
abbrev remove_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_iff F
abbrev remove_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_m F
abbrev remove_neq_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_neq_b F
abbrev remove_neq_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_neq_iff F
abbrev remove_s_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_s_m F
abbrev remove_s_m_Proper := CompCert4Lean.Lib.FSetFacts.WFacts_fun.remove_s_m_Proper F
abbrev singleton_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.singleton_b F
abbrev singleton_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.singleton_iff F
abbrev singleton_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.singleton_m F
abbrev subset_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.subset_iff F
abbrev subset_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.subset_m F
abbrev union_b := CompCert4Lean.Lib.FSetFacts.WFacts_fun.union_b F
abbrev union_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.union_iff F
abbrev union_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.union_m F
abbrev union_s_m := CompCert4Lean.Lib.FSetFacts.WFacts_fun.union_s_m F
abbrev union_s_m_Proper := CompCert4Lean.Lib.FSetFacts.WFacts_fun.union_s_m_Proper F

end NodesetFacts

/-! ## Program matching and preserved global-environment observations -/

def match_prog (service : EnumerationService)
    (p : LTL.program) (tp : Linear.program) : Prop :=
  @match_program LTL.fundef Unit Linear.fundef Unit
    (Linker_fundef LTL.function) Linker_unit
    (fun _ f tf =>
      CompCert4Lean.Backend.Linearize.transf_fundef service f = .OK tf)
    (fun x y : Unit => x = y) p tp

/-! ## State matching and the simulation measure -/

inductive match_stackframes (service : EnumerationService) :
    LTL.stackframe -> Linear.stackframe -> Prop where
  | match_stackframe_intro
      (f : LTL.function) (sp : val) (bb : LTL.bblock) (ls : LTL.locset)
      (tf : Linear.function) (c : Linear.code)
      (htrans : transf_function service f = .OK tf)
      (hreach : forall pc, List.Mem pc (successors_block bb) ->
        PMap.get pc (reachable f) = true)
      (htail : is_tail c tf.fn_code) :
      match_stackframes service
        (LTL.Stackframe f sp ls bb)
        (Linear.Stackframe tf sp ls (linearize_block bb c))

inductive match_states (service : EnumerationService) :
    LTL.state -> Linear.state -> Prop where
  | match_states_add_branch
      (s : List LTL.stackframe) (f : LTL.function) (sp : val)
      (pc : LTL.node) (ls : LTL.locset) (m : mem)
      (tf : Linear.function) (ts : List Linear.stackframe) (c : Linear.code)
      (hstack : list_forall2 (match_stackframes service) s ts)
      (htrans : transf_function service f = .OK tf)
      (hreach : PMap.get pc (reachable f) = true)
      (htail : is_tail c tf.fn_code) :
      match_states service (LTL.State s f sp pc ls m)
        (Linear.State ts tf sp (add_branch pc c) ls m)
  | match_states_cond_taken
      (s : List LTL.stackframe) (f : LTL.function) (sp : val)
      (pc : LTL.node) (ls : LTL.locset) (m : mem)
      (tf : Linear.function) (ts : List Linear.stackframe)
      (cond : condition) (args : List mreg) (c : Linear.code)
      (hstack : list_forall2 (match_stackframes service) s ts)
      (htrans : transf_function service f = .OK tf)
      (hreach : PMap.get pc (reachable f) = true)
      (hjump : eval_condition cond (reglist ls args) m = some true) :
      match_states service
        (LTL.State s f sp pc (undef_regs (destroyed_by_cond cond) ls) m)
        (Linear.State ts tf sp (Lcond cond args pc :: c) ls m)
  | match_states_jumptable
      (s : List LTL.stackframe) (f : LTL.function) (sp : val)
      (pc : LTL.node) (ls : LTL.locset) (m : mem)
      (tf : Linear.function) (ts : List Linear.stackframe)
      (arg : mreg) (tbl : List LTL.node) (c : Linear.code) (n : int)
      (hstack : list_forall2 (match_stackframes service) s ts)
      (htrans : transf_function service f = .OK tf)
      (hreach : PMap.get pc (reachable f) = true)
      (harg : ls (R arg) = Vint n)
      (hjump : list_nth_z tbl
        (CompCert4Lean.Lib.Integers.Int.unsigned n) = some pc) :
      match_states service
        (LTL.State s f sp pc (undef_regs destroyed_by_jumptable ls) m)
        (Linear.State ts tf sp (Ljumptable arg tbl :: c) ls m)
  | match_states_block
      (s : List LTL.stackframe) (f : LTL.function) (sp : val)
      (bb : LTL.bblock) (ls : LTL.locset) (m : mem)
      (tf : Linear.function) (ts : List Linear.stackframe) (c : Linear.code)
      (hstack : list_forall2 (match_stackframes service) s ts)
      (htrans : transf_function service f = .OK tf)
      (hreach : forall pc, List.Mem pc (successors_block bb) ->
        PMap.get pc (reachable f) = true)
      (htail : is_tail c tf.fn_code) :
      match_states service (LTL.Block s f sp bb ls m)
        (Linear.State ts tf sp (linearize_block bb c) ls m)
  | match_states_call
      (s : List LTL.stackframe) (f : LTL.fundef) (ls : LTL.locset) (m : mem)
      (tf : Linear.fundef) (ts : List Linear.stackframe)
      (hstack : list_forall2 (match_stackframes service) s ts)
      (htrans :
        CompCert4Lean.Backend.Linearize.transf_fundef service f = .OK tf) :
      match_states service (LTL.Callstate s f ls m)
        (Linear.Callstate ts tf ls m)
  | match_states_return
      (s : List LTL.stackframe) (ls : LTL.locset) (m : mem)
      (ts : List Linear.stackframe)
      (hstack : list_forall2 (match_stackframes service) s ts) :
      match_states service (LTL.Returnstate s ls m)
        (Linear.Returnstate ts ls m)

def measure : LTL.state -> Nat
  | .State _ _ _ _ _ _ => 0
  | .Block _ _ _ _ _ _ => 1
  | .Callstate _ _ _ _ => 0
  | .Returnstate _ _ _ => 0

/-! ## Exact statement descriptors for later proof migration -/

def transf_program_matchStatement : Prop :=
  forall (service : EnumerationService) (p : LTL.program)
    (tp : Linear.program),
    transf_program service p = .OK tp -> match_prog service p tp

def functions_translatedStatement : Prop :=
  forall (service : EnumerationService) (prog : LTL.program)
    (tprog : Linear.program),
    match_prog service prog tprog ->
    forall (v : val) (f : LTL.fundef),
      Genv.find_funct (Genv.globalenv prog) v = some f ->
      exists tf,
        Genv.find_funct (Genv.globalenv tprog) v = some tf /\
          CompCert4Lean.Backend.Linearize.transf_fundef service f = .OK tf

def function_ptr_translatedStatement : Prop :=
  forall (service : EnumerationService) (prog : LTL.program)
    (tprog : Linear.program),
    match_prog service prog tprog ->
    forall (v : block) (f : LTL.fundef),
      Genv.find_funct_ptr (Genv.globalenv prog) v = some f ->
      exists tf,
        Genv.find_funct_ptr (Genv.globalenv tprog) v = some tf /\
          CompCert4Lean.Backend.Linearize.transf_fundef service f = .OK tf

def symbols_preservedStatement : Prop :=
  forall (service : EnumerationService) (prog : LTL.program)
    (tprog : Linear.program),
    match_prog service prog tprog ->
    forall id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id

def senv_preservedStatement : Prop :=
  forall (service : EnumerationService) (prog : LTL.program)
    (tprog : Linear.program),
    match_prog service prog tprog ->
    Senv.equiv (Genv.to_senv (Genv.globalenv prog))
      (Genv.to_senv (Genv.globalenv tprog))

def sig_preservedStatement : Prop :=
  forall (service : EnumerationService) (f : LTL.fundef)
    (tf : Linear.fundef),
    CompCert4Lean.Backend.Linearize.transf_fundef service f = .OK tf ->
      Linear.funsig tf = LTL.funsig f

def stacksize_preservedStatement : Prop :=
  forall (service : EnumerationService) (f : LTL.function)
    (tf : Linear.function),
    transf_function service f = .OK tf -> tf.fn_stacksize = f.fn_stacksize

def find_function_translatedStatement : Prop :=
  forall (service : EnumerationService) (prog : LTL.program)
    (tprog : Linear.program),
    match_prog service prog tprog ->
    forall (ros : Sum mreg ident) (ls : LTL.locset) (f : LTL.fundef),
      LTL.find_function (Genv.globalenv prog) ros ls = some f ->
      exists tf,
        Linear.find_function (Genv.globalenv tprog) ros ls = some tf /\
          CompCert4Lean.Backend.Linearize.transf_fundef service f = .OK tf

def reachable_entrypointStatement : Prop :=
  forall f : LTL.function, PMap.get f.fn_entrypoint (reachable f) = true

def reachable_successorsStatement : Prop :=
  forall (f : LTL.function) (pc pc' : LTL.node) (b : LTL.bblock),
    PTree.get pc f.fn_code = some b -> List.Mem pc' (successors_block b) ->
    PMap.get pc (reachable f) = true ->
    PMap.get pc' (reachable f) = true

def nodeset_of_list_correctStatement : Prop :=
  forall (l : List LTL.node) (s s' : Nodeset.t),
    nodeset_of_list l s = .OK s' ->
    list_norepet l /\
      (forall pc, Nodeset.In pc s' <-> Nodeset.In pc s \/ List.Mem pc l) /\
      (forall pc, List.Mem pc l -> ¬ Nodeset.In pc s)

def check_reachable_correctStatement : Prop :=
  forall (f : LTL.function) (reach : PMap.t Bool)
    (s : Nodeset.t) (pc : LTL.node) (i : LTL.bblock),
    check_reachable f reach s = true ->
    PTree.get pc f.fn_code = some i ->
    PMap.get pc reach = true -> Nodeset.In pc s

def enumerate_completeStatement : Prop :=
  forall (service : EnumerationService) (f : LTL.function)
    (enum : List LTL.node)
    (pc : LTL.node) (i : LTL.bblock),
    enumerate service f = .OK enum ->
    PTree.get pc f.fn_code = some i ->
    PMap.get pc (reachable f) = true -> List.Mem pc enum

def enumerate_norepetStatement : Prop :=
  forall (service : EnumerationService) (f : LTL.function)
    (enum : List LTL.node),
    enumerate service f = .OK enum -> list_norepet enum

def unique_labels : Linear.code -> Prop
  | [] => True
  | Linear.Llabel lbl :: c => ¬ List.Mem (Linear.Llabel lbl) c ∧ unique_labels c
  | _ :: c => unique_labels c

def find_label_uniqueStatement : Prop :=
  forall (lbl : Linear.label) (c1 c2 c3 : Linear.code),
    is_tail (Linear.Llabel lbl :: c1) c2 -> unique_labels c2 ->
    Linear.find_label lbl c2 = some c3 -> c1 = c3

def starts_with_correct_genvStatement
  [binary64_certificate :
    CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
  [binary32_certificate :
    CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  forall (cfg : CompilerConfig) (xi : ExternalCalls) (tge : Linear.genv)
    (lbl : Linear.label) (c1 c2 c3 : Linear.code) (s : List Linear.stackframe)
    (f : Linear.function) (sp : val) (ls : Linear.locset) (m : mem),
    is_tail c1 c2 -> unique_labels c2 ->
    starts_with lbl c1 = true -> Linear.find_label lbl c2 = some c3 ->
    plus (fun ge => Linear.step cfg xi ge) tge
      (Linear.State s f sp c1 ls m) E0
      (Linear.State s f sp c3 ls m)

def starts_with_correctStatement
  [binary64_certificate :
    CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
  [binary32_certificate :
    CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  forall (cfg : CompilerConfig) (xi : ExternalCalls) (tprog : Linear.program)
    (lbl : Linear.label) (c1 c2 : List Linear.instruction) (c3 : Linear.code)
    (s : List Linear.stackframe) (f : Linear.function) (sp : val)
    (ls : Linear.locset) (m : mem),
    is_tail c1 c2 -> unique_labels c2 ->
    starts_with lbl c1 = true -> Linear.find_label lbl c2 = some c3 ->
    plus (fun ge => Linear.step cfg xi ge) (Genv.globalenv tprog)
      (Linear.State s f sp c1 ls m) E0
      (Linear.State s f sp c3 ls m)

def find_label_add_branchStatement : Prop :=
  forall (lbl : Linear.label) (k : Linear.code) (s : Linear.label),
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
  forall (service : EnumerationService) (f : LTL.function)
    (tf : Linear.function) (pc : LTL.node) (b : LTL.bblock),
    transf_function service f = .OK tf -> PTree.get pc f.fn_code = some b ->
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
  forall (service : EnumerationService) (f : LTL.function)
    (tf : Linear.function),
    transf_function service f = .OK tf -> unique_labels tf.fn_code

def is_tail_find_labelStatement : Prop :=
  forall (lbl : Linear.label) (c2 c1 : Linear.code),
    Linear.find_label lbl c1 = some c2 -> is_tail c2 c1

def is_tail_add_branchStatement : Prop :=
  forall (lbl : Linear.label) (c1 c2 : Linear.code),
    is_tail (add_branch lbl c1) c2 -> is_tail c1 c2

def is_tail_lin_blockStatement : Prop :=
  forall (b : LTL.bblock) (c1 c2 : Linear.code),
    is_tail (linearize_block b c1) c2 -> is_tail c1 c2

def add_branch_correct_genvStatement
  [binary64_certificate :
    CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
  [binary32_certificate :
    CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  forall (cfg : CompilerConfig) (xi : ExternalCalls) (tge : Linear.genv)
    (service : EnumerationService)
    (lbl : Linear.label) (c k : Linear.code) (s : List Linear.stackframe)
    (f : LTL.function) (tf : Linear.function) (sp : val) (ls : Linear.locset)
    (m : mem),
    transf_function service f = .OK tf -> is_tail k tf.fn_code ->
    Linear.find_label lbl tf.fn_code = some c ->
    plus (fun ge => Linear.step cfg xi ge) tge
      (Linear.State s tf sp (add_branch lbl k) ls m) E0
      (Linear.State s tf sp c ls m)

def add_branch_correctStatement
  [binary64_certificate :
    CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
  [binary32_certificate :
    CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  forall (cfg : CompilerConfig) (xi : ExternalCalls)
    (service : EnumerationService) (tprog : Linear.program)
    (lbl : Linear.label) (c : Linear.code) (k : List Linear.instruction)
    (s : List Linear.stackframe) (f : LTL.function) (tf : Linear.function)
    (sp : val) (ls : Linear.locset) (m : mem),
    transf_function service f = .OK tf -> is_tail k tf.fn_code ->
    Linear.find_label lbl tf.fn_code = some c ->
    plus (fun ge => Linear.step cfg xi ge) (Genv.globalenv tprog)
      (Linear.State s tf sp (add_branch lbl k) ls m) E0
      (Linear.State s tf sp c ls m)

def match_parent_locsetStatement : Prop :=
  forall (service : EnumerationService) (s : List LTL.stackframe)
    (ts : List Linear.stackframe),
    list_forall2 (match_stackframes service) s ts ->
    Linear.parent_locset ts = LTL.parent_locset s

def transf_step_correctStatement
  [binary64_certificate :
    CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
  [binary32_certificate :
    CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  forall (cfg : CompilerConfig) (xi : ExternalCalls)
    (service : EnumerationService)
    (prog : LTL.program) (tprog : Linear.program),
    match_prog service prog tprog ->
    forall (s1 : LTL.state) (t : trace) (s2 : LTL.state),
      LTL.step (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cfg xi (Genv.globalenv prog) s1 t s2 ->
      forall s1', match_states service s1 s1' ->
        (exists s2',
          plus (fun ge => Linear.step cfg xi ge) (Genv.globalenv tprog)
            s1' t s2' /\ match_states service s2 s2') \/
        (measure s2 < measure s1 /\ t = E0 /\ match_states service s2 s1')

def transf_initial_statesStatement : Prop :=
  forall (service : EnumerationService) (prog : LTL.program)
    (tprog : Linear.program),
    match_prog service prog tprog ->
    forall st1, LTL.initial_state prog st1 ->
      exists st2,
        Linear.initial_state tprog st2 /\ match_states service st1 st2

def transf_final_statesStatement : Prop :=
  forall (service : EnumerationService) (st1 : LTL.state)
    (st2 : Linear.state) (r : int),
    match_states service st1 st2 ->
      LTL.final_state st1 r -> Linear.final_state st2 r

def transf_program_correctStatement
  [binary64_certificate :
    CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
  [binary32_certificate :
    CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  forall (cfg : CompilerConfig) (xi : ExternalCalls)
    (service : EnumerationService)
    (prog : LTL.program) (tprog : Linear.program),
    match_prog service prog tprog ->
    forward_simulation
      (LTL.semantics (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) cfg xi prog)
      (Linear.semantics cfg xi tprog)

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib

theorem transf_program_match : transf_program_matchStatement := by
  letI : Linker LTL.fundef := Linker_fundef LTL.function
  letI : Linker Linear.fundef := Linker_fundef Linear.function
  letI : Linker Unit := Linker_unit
  letI : Linker LTL.program := Linker_prog LTL.fundef Unit
  intro service p tp htrans
  unfold match_prog at *
  unfold CompCert4Lean.Backend.Linearize.transf_program
    CompCert4Lean.Common.AST.transform_partial_program
    CompCert4Lean.Common.AST.transform_partial_program2 at htrans
  cases hdefs : CompCert4Lean.Common.AST.transf_globdefs
      (fun _ f => CompCert4Lean.Backend.Linearize.transf_fundef service f)
      (fun _ v => .OK v) p.prog_defs with
  | Error msg =>
      simp only [hdefs] at htrans
      cases htrans
  | OK defs =>
      simp only [hdefs] at htrans
      cases htrans
      have hlist : ∀ (xs : List (ident × globdef LTL.fundef Unit))
          (ys : List (ident × globdef Linear.fundef Unit)),
          CompCert4Lean.Common.AST.transf_globdefs
              (fun _ f => CompCert4Lean.Backend.Linearize.transf_fundef service f)
              (fun _ v => .OK v) xs = .OK ys →
            list_forall2
              (match_ident_globdef
                (fun _ f tf =>
                  CompCert4Lean.Backend.Linearize.transf_fundef service f = .OK tf)
                (fun x y : Unit => x = y) p) xs ys := by
        intro xs
        induction xs with
        | nil =>
            intro ys h
            cases ys with
            | nil => exact list_forall2.nil _
            | cons y ys =>
                simp only [CompCert4Lean.Common.AST.transf_globdefs] at h
                cases h
        | cons hd tl ih =>
            intro ys h
            cases hd with
            | mk id gd =>
                cases gd with
                | Gfun f =>
                    cases htf : CompCert4Lean.Backend.Linearize.transf_fundef service f with
                    | Error msg =>
                        simp only [CompCert4Lean.Common.AST.transf_globdefs, htf] at h
                        cases h
                    | OK tf =>
                        cases htail : CompCert4Lean.Common.AST.transf_globdefs
                            (fun _ f => CompCert4Lean.Backend.Linearize.transf_fundef service f)
                            (fun _ v => .OK v) tl with
                        | Error msg =>
                            simp only [CompCert4Lean.Common.AST.transf_globdefs, htf, htail] at h
                            cases h
                        | OK ys' =>
                            cases ys with
                            | nil =>
                                simp only [CompCert4Lean.Common.AST.transf_globdefs,
                                  htf, htail] at h
                                cases h
                            | cons y ys =>
                                simp only [CompCert4Lean.Common.AST.transf_globdefs,
                                  htf, htail] at h
                                cases h
                                apply list_forall2.cons
                                · constructor
                                  · rfl
                                  · apply match_globdef.match_globdef_fun (ctx' := p)
                                    · exact linkorder_refl _
                                    · exact htf
                                · exact ih ys' htail
                | Gvar v =>
                    cases htail : CompCert4Lean.Common.AST.transf_globdefs
                        (fun _ f => CompCert4Lean.Backend.Linearize.transf_fundef service f)
                        (fun _ v => .OK v) tl with
                    | Error msg =>
                        simp only [CompCert4Lean.Common.AST.transf_globdefs,
                          CompCert4Lean.Common.AST.transf_globvar, htail] at h
                        cases h
                    | OK ys' =>
                        cases ys with
                        | nil =>
                            simp only [CompCert4Lean.Common.AST.transf_globdefs,
                              CompCert4Lean.Common.AST.transf_globvar, htail] at h
                            cases h
                        | cons y ys =>
                            simp only [CompCert4Lean.Common.AST.transf_globdefs,
                              CompCert4Lean.Common.AST.transf_globvar, htail] at h
                            cases h
                            apply list_forall2.cons
                            · constructor
                              · rfl
                              · apply match_globdef.match_globdef_var
                                exact match_globvar.match_globvar_intro _ _ _ _ _ _ rfl
                            · exact ih ys' htail
      exact ⟨hlist p.prog_defs defs hdefs, rfl, rfl⟩

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof.NodesetFacts

theorem add_iff_proof : add_iff := by
  intro s x y
  constructor
  · intro hy
    by_cases hxy : F.E.eq x y
    · exact Or.inl hxy
    · exact Or.inr (F.M.add_3 s x y hxy hy)
  · intro hy
    cases hy with
    | inl hxy => exact F.M.add_1 s x y hxy
    | inr hy => exact F.M.add_2 s x y hy

theorem not_mem_iff_proof : not_mem_iff := by
  intro s x
  constructor
  · intro hnot
    cases hmem : F.M.mem x s with
    | false => rfl
    | true => exact False.elim (hnot (F.M.mem_2 s x hmem))
  · intro hmem hin
    have htrue := F.M.mem_1 s x hin
    rw [hmem] at htrue
    cases htrue

end CompCert4Lean.Backend.Linearizeproof.NodesetFacts

namespace CompCert4Lean.Backend.Linearizeproof

open CompCert4Lean.Backend.LTL
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

local instance linearizeLinkerLTLFundef : Linker LTL.fundef :=
  Linker_fundef LTL.function
local instance linearizeLinkerLinearFundef : Linker Linear.fundef :=
  Linker_fundef Linear.function
local instance linearizeLinkerUnit : Linker Unit := Linker_unit
local instance linearizeLinkerLTLProgram : Linker LTL.program :=
  Linker_prog LTL.fundef Unit

private theorem linearize_symbol_add_global
    (ge1 : Genv.t LTL.fundef Unit) (ge2 : Genv.t Linear.fundef Unit) (id : ident)
    (hm : ∀ id', PTree.get id' ge2.genv_symb = PTree.get id' ge1.genv_symb)
    (hn : ge2.genv_next = ge1.genv_next) :
    ∀ id', PTree.get id'
      (PTree.set id ge2.genv_next ge2.genv_symb) =
      PTree.get id'
      (PTree.set id ge1.genv_next ge1.genv_symb) := by
  intro id'
  have h2 := @PTree.getSet_equation _ id' id ge2.genv_next ge2.genv_symb
  have h1 := @PTree.getSet_equation _ id' id ge1.genv_next ge1.genv_symb
  by_cases h : id' = id
  · rw [h2, h1]
    simp only [dif_pos h]
    exact congrArg some hn
  · rw [h2, h1]
    simp only [dif_neg h]
    exact hm id'

private theorem linearize_symbol_add_globals
    (xs : List (ident × globdef LTL.fundef Unit))
    (ys : List (ident × globdef Linear.fundef Unit))
    (hxy : list_forall2 (fun a b => a.1 = b.1) xs ys)
    (ge1 : Genv.t LTL.fundef Unit) (ge2 : Genv.t Linear.fundef Unit)
    (hm : ∀ id', PTree.get id' ge2.genv_symb = PTree.get id' ge1.genv_symb)
    (hn : ge2.genv_next = ge1.genv_next) :
    ∀ id', PTree.get id' (Genv.add_globals ge2 ys).genv_symb =
      PTree.get id' (Genv.add_globals ge1 xs).genv_symb := by
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
        exact linearize_symbol_add_global ge1 ge2 aid hm hn id'
      · exact congrArg PArith.BinPos.Pos.succ hn

private theorem linearize_match_genvs_add_global
    (R : globdef LTL.fundef Unit → globdef Linear.fundef Unit → Prop)
    (ge1 : Genv.t LTL.fundef Unit) (ge2 : Genv.t Linear.fundef Unit)
    (id : ident) (g1 : globdef LTL.fundef Unit)
    (g2 : globdef Linear.fundef Unit)
    (hm : Genv.match_genvs R ge1 ge2) (hg : R g1 g2) :
    Genv.match_genvs R (Genv.add_global ge1 (id, g1))
      (Genv.add_global ge2 (id, g2)) := by
  constructor
  · exact congrArg PArith.BinPos.Pos.succ hm.mge_next
  · exact linearize_symbol_add_global ge1 ge2 id hm.mge_symb hm.mge_next
  · intro b
    change option_rel R
      (PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs))
      (PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs))
    have h1 := @PTree.getSet_equation
      (globdef LTL.fundef Unit) b ge1.genv_next g1 ge1.genv_defs
    have h2 := @PTree.getSet_equation
      (globdef Linear.fundef Unit) b ge2.genv_next g2 ge2.genv_defs
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

private theorem linearize_match_genvs_add_globals
    (R : globdef LTL.fundef Unit → globdef Linear.fundef Unit → Prop)
    (xs : List (ident × globdef LTL.fundef Unit))
    (ys : List (ident × globdef Linear.fundef Unit))
    (hxy : list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) xs ys)
    (ge1 : Genv.t LTL.fundef Unit) (ge2 : Genv.t Linear.fundef Unit)
    (hm : Genv.match_genvs R ge1 ge2) :
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
      simpa using (linearize_match_genvs_add_global R ge1 ge2 aid ag bg hm hab)

private theorem linearize_globalenvs_match
    (service : EnumerationService) (prog : LTL.program)
    (tprog : Linear.program) (hm : match_prog service prog tprog) :
    Genv.match_genvs
      (match_globdef
        (fun (_ : LTL.program) f tf =>
          CompCert4Lean.Backend.Linearize.transf_fundef service f = .OK tf)
        (fun x y : Unit => x = y) prog)
      (Genv.globalenv prog) (Genv.globalenv tprog) := by
  letI : Linker LTL.fundef := Linker_fundef LTL.function
  letI : Linker Linear.fundef := Linker_fundef Linear.function
  letI : Linker Unit := Linker_unit
  letI : Linker LTL.program := Linker_prog LTL.fundef Unit
  let R : globdef LTL.fundef Unit → globdef Linear.fundef Unit → Prop :=
    match_globdef
      (fun (_ : LTL.program) f tf =>
        CompCert4Lean.Backend.Linearize.transf_fundef service f = .OK tf)
      (fun x y : Unit => x = y) prog
  have hempty : Genv.match_genvs R
      (Genv.empty_genv LTL.fundef Unit prog.prog_public)
      (Genv.empty_genv Linear.fundef Unit tprog.prog_public) := by
    constructor
    · rfl
    · intro id'
      rfl
    · intro b
      exact option_rel.none R
  have hlist : list_forall2
      (fun a b => a.1 = b.1 ∧ R a.2 b.2)
      prog.prog_defs tprog.prog_defs := by
    unfold match_prog match_program match_program_gen at hm
    have hlist_of : ∀ (xs : List (ident × globdef LTL.fundef Unit))
        (ys : List (ident × globdef Linear.fundef Unit)),
        list_forall2 (match_ident_globdef
          (fun (_ : LTL.program) f tf =>
            CompCert4Lean.Backend.Linearize.transf_fundef service f = .OK tf)
          (fun x y : Unit => x = y) prog) xs ys →
        list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) xs ys := by
      intro xs ys h
      induction h with
      | nil => exact list_forall2.nil _
      | @cons a xs b ys hab htail ih =>
          apply list_forall2.cons
          · exact ⟨hab.1, by simpa [R] using hab.2⟩
          · exact ih
    exact hlist_of _ _ hm.1
  have hgenv := linearize_match_genvs_add_globals R
    prog.prog_defs tprog.prog_defs hlist
    (Genv.empty_genv LTL.fundef Unit prog.prog_public)
    (Genv.empty_genv Linear.fundef Unit tprog.prog_public) hempty
  simpa [Genv.globalenv, R] using hgenv

private theorem linearize_function_ptr_translated
    (service : EnumerationService) (prog : LTL.program)
    (tprog : Linear.program) (hm : match_prog service prog tprog)
    (b : block) (f : LTL.fundef)
    (hfind : Genv.find_funct_ptr (Genv.globalenv prog) b = some f) :
    ∃ tf, Genv.find_funct_ptr (Genv.globalenv tprog) b = some tf ∧
      CompCert4Lean.Backend.Linearize.transf_fundef service f = .OK tf := by
  have hg := linearize_globalenvs_match service prog tprog hm
  unfold Genv.find_funct_ptr Genv.find_def at hfind ⊢
  cases h1 : PTree.get b (Genv.globalenv prog).genv_defs with
  | none => simp [h1] at hfind
  | some gd1 =>
      cases gd1 with
      | Gfun f1 =>
          have hf : f1 = f := by simpa [h1] using hfind
          subst f1
          cases h2 : PTree.get b (Genv.globalenv tprog).genv_defs with
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
                          exact ⟨f2, by simp [h2], htrans⟩
              | Gvar v2 =>
                  have hd := hg.mge_defs b
                  simp [h1, h2] at hd
                  cases hd with
                  | some x y hrel => cases hrel
      | Gvar v1 => simp [h1] at hfind

theorem functions_translated : functions_translatedStatement := by
  intro service prog tprog hm v f hfind
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
          exact linearize_function_ptr_translated service prog tprog hm b f hfind

end CompCert4Lean.Backend.Linearizeproof
