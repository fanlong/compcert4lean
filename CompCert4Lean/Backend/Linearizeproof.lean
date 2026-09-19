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

namespace CompCert4Lean.Backend.Linearizeproof

theorem function_ptr_translated : function_ptr_translatedStatement := by
  intro service prog tprog hm v f hfind
  exact linearize_function_ptr_translated service prog tprog hm v f hfind

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Maps

theorem sig_preserved : sig_preservedStatement := by
  intro service f tf htrans
  cases f with
  | Internal f =>
      unfold CompCert4Lean.Backend.Linearize.transf_fundef at htrans
      simp only [CompCert4Lean.Common.AST.transf_partial_fundef] at htrans
      cases htf : CompCert4Lean.Backend.Linearize.transf_function service f with
      | Error msg => rw [htf] at htrans; cases htrans
      | OK tf' =>
          rw [htf] at htrans
          cases htrans
          unfold CompCert4Lean.Backend.Linearize.transf_function at htf
          cases henum : CompCert4Lean.Backend.Linearize.enumerate service f with
          | Error msg => simp [henum] at htf
          | OK enum =>
              simp [henum] at htf
              cases htf
              rfl
  | External ef =>
      unfold CompCert4Lean.Backend.Linearize.transf_fundef at htrans
      cases htrans
      rfl

theorem stacksize_preserved : stacksize_preservedStatement := by
  intro service f tf htrans
  unfold CompCert4Lean.Backend.Linearize.transf_function at htrans
  cases henum : CompCert4Lean.Backend.Linearize.enumerate service f with
  | Error msg => simp [henum] at htrans
  | OK enum =>
      simp [henum] at htrans
      cases htrans
      rfl

theorem symbols_preserved : symbols_preservedStatement := by
  letI : Linker LTL.fundef := Linker_fundef LTL.function
  letI : Linker Linear.fundef := Linker_fundef Linear.function
  letI : Linker Unit := Linker_unit
  letI : Linker LTL.program := Linker_prog LTL.fundef Unit
  intro service prog tprog hm id
  have hg := linearize_globalenvs_match service prog tprog hm
  simpa [Genv.find_symbol, Genv.globalenv] using hg.mge_symb id

private theorem linearize_add_globals_public {F V : Type}
    (ge : Genv.t F V) (gl : List (ident × globdef F V)) :
    (Genv.add_globals ge gl).genv_public = ge.genv_public := by
  induction gl generalizing ge with
  | nil => rfl
  | cons x xs ih =>
      simp only [Genv.add_globals, List.foldl]
      exact ih (Genv.add_global ge x)

theorem senv_preserved : senv_preservedStatement := by
  letI : Linker LTL.fundef := Linker_fundef LTL.function
  letI : Linker Linear.fundef := Linker_fundef Linear.function
  letI : Linker Unit := Linker_unit
  letI : Linker LTL.program := Linker_prog LTL.fundef Unit
  intro service prog tprog hm
  unfold Senv.equiv
  constructor
  · intro id
    exact symbols_preserved service prog tprog hm id
  constructor
  · intro id
    change Genv.public_symbol (Genv.globalenv tprog) id =
      Genv.public_symbol (Genv.globalenv prog) id
    have ht : (Genv.globalenv tprog).genv_public = tprog.prog_public := by
      unfold Genv.globalenv
      exact linearize_add_globals_public _ _
    have hp : (Genv.globalenv prog).genv_public = prog.prog_public := by
      unfold Genv.globalenv
      exact linearize_add_globals_public _ _
    unfold Genv.public_symbol
    rw [symbols_preserved service prog tprog hm id, ht, hp]
    unfold match_prog match_program match_program_gen at hm
    rw [hm.2.2]
  · intro b
    change Genv.block_is_volatile (Genv.globalenv tprog) b =
      Genv.block_is_volatile (Genv.globalenv prog) b
    have hg := linearize_globalenvs_match service prog tprog hm
    unfold Genv.block_is_volatile Genv.find_var_info Genv.find_def
    cases h1 : PTree.get b (Genv.globalenv prog).genv_defs with
    | none =>
        cases h2 : PTree.get b (Genv.globalenv tprog).genv_defs with
        | none => rfl
        | some gd2 =>
            have hd := hg.mge_defs b
            simp [h1, h2] at hd
            cases hd
    | some gd1 =>
        cases h2 : PTree.get b (Genv.globalenv tprog).genv_defs with
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

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof

open CompCert4Lean.Common.Globalenvs

theorem find_function_translated : find_function_translatedStatement := by
  intro service prog tprog hm ros ls f hfind
  cases ros with
  | inl r =>
      unfold CompCert4Lean.Backend.LTL.find_function at hfind
      unfold CompCert4Lean.Backend.Linear.find_function
      exact functions_translated service prog tprog hm
        (ls (CompCert4Lean.Backend.Locations.R r)) f hfind
  | inr symb =>
      unfold CompCert4Lean.Backend.LTL.find_function at hfind
      unfold CompCert4Lean.Backend.Linear.find_function
      change
        (match Genv.find_symbol (Genv.globalenv prog) symb with
        | none => none
        | some b => Genv.find_funct_ptr (Genv.globalenv prog) b) = some f at hfind
      change
        ∃ tf,
          (match Genv.find_symbol (Genv.globalenv tprog) symb with
          | none => none
          | some b => Genv.find_funct_ptr (Genv.globalenv tprog) b) = some tf ∧
            CompCert4Lean.Backend.Linearize.transf_fundef service f = .OK tf
      cases hs : Genv.find_symbol (Genv.globalenv prog) symb with
      | none => simp [hs] at hfind
      | some b =>
          have hs' := symbols_preserved service prog tprog hm symb
          rw [hs', hs]
          exact function_ptr_translated service prog tprog hm b f
            (by simpa [hs] using hfind)

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof

open CompCert4Lean.Backend.Linearize
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Maps

theorem check_reachable_correct : check_reachable_correctStatement := by
  intro f reach s
  have hfold : ∀ (l : List (LTL.node × LTL.bblock)) (ok : Bool),
      List.foldl
          (fun a p => check_reachable_aux reach s a p.1 p.2) ok l = true ->
      ok = true /\
        (∀ pc i, List.Mem (pc, i) l -> PMap.get pc reach = true ->
          Nodeset.In pc s) := by
    intro l
    induction l with
    | nil =>
        intro ok h
        constructor
        · simpa using h
        · intro pc i hmem
          cases hmem
    | cons p l ih =>
        intro ok h
        rcases p with ⟨pc1, i1⟩
        simp only [List.foldl] at h
        have hrest := ih (check_reachable_aux reach s ok pc1 i1) h
        rcases hrest with ⟨hokrest, hmemrest⟩
        constructor
        · unfold check_reachable_aux at hokrest
          cases hpc : PMap.get pc1 reach with
          | false => simpa [hpc] using hokrest
          | true =>
              have hparts : ok && Nodeset.mem pc1 s = true := by
                simpa [hpc] using hokrest
              exact (Bool.and_eq_true_iff.mp hparts).1
        · intro pc i hmem hreach
          cases hmem with
          | head =>
            unfold check_reachable_aux at hokrest
            cases hpc : PMap.get pc1 reach with
            | false => simp [hpc] at hreach
            | true =>
                have hparts : ok && Nodeset.mem pc1 s = true := by
                  simpa [hpc] using hokrest
                have hmem : Nodeset.mem pc1 s = true := by
                  simpa using (Bool.and_eq_true_iff.mp hparts).2
                exact CompCert4Lean.Backend.Linearize.Nodeset.mem_2_proof s pc1 hmem
          | tail _ htail => exact hmemrest pc i htail hreach
  intro pc i hcheck hcode hreach
  have hspec := CompCert4Lean.Lib.Maps.PTree.fold_spec_proof
    (A := LTL.bblock) (B := Bool)
    (check_reachable_aux reach s) true f.fn_code
  have hlist : List.foldl
      (fun a p => check_reachable_aux reach s a p.1 p.2) true
      (PTree.elements f.fn_code) = true := by
    rw [← hspec]
    exact hcheck
  rcases hfold (PTree.elements f.fn_code) true hlist with ⟨_, hall⟩
  apply hall pc i
  · exact PTree.elements_correct_proof f.fn_code pc (v := i) hcode
  · exact hreach

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof

open CompCert4Lean.Backend.Linearize
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem linearize_nodeset_of_list_correct_aux :
    nodeset_of_list_correctStatement := by
  intro l
  induction l with
  | nil =>
      intro s s' h
      cases h
      refine ⟨CompCert4Lean.Lib.Coqlib.list_norepet.nil _, ?_, ?_⟩
      · intro pc
        constructor
        · intro hin
          exact Or.inl hin
        · intro hor
          cases hor with
          | inl hin => exact hin
          | inr hmem => cases hmem
      · intro pc hmem
        cases hmem
  | cons a l ih =>
      intro s s' h
      cases hmem : Nodeset.mem a s with
      | true =>
          simp only [nodeset_of_list, hmem] at h
          cases h
      | false =>
          simp only [nodeset_of_list, hmem] at h
          have hi := ih (Nodeset.add a s) s' h
          rcases hi with ⟨hnr, heq, hdisj⟩
          refine ⟨?_, ?_, ?_⟩
          · apply CompCert4Lean.Lib.Coqlib.list_norepet.cons a
            · intro ha
              exact hdisj a ha
                (CompCert4Lean.Lib.FSetAVLplus.Make.add_1 s a a rfl)
            · exact hnr
          · intro pc
            constructor
            · intro hin
              rcases (heq pc).mp hin with hadd | htail
              · rcases (NodesetFacts.add_iff_proof (s := s) a pc).mp hadd with ha | hs
                · subst pc
                  exact Or.inr (List.Mem.head l)
                · exact Or.inl hs
              · exact Or.inr (List.Mem.tail a htail)
            · intro hor
              rcases hor with hs | hlist
              · exact (heq pc).mpr (Or.inl
                    (CompCert4Lean.Lib.FSetAVLplus.Make.add_2 s a pc hs))
              · cases hlist with
                | head =>
                    exact (heq a).mpr (Or.inl
                      (CompCert4Lean.Lib.FSetAVLplus.Make.add_1 s a a rfl))
                | tail _ htail =>
                    exact (heq pc).mpr (Or.inr htail)
          · intro pc htail
            cases htail with
            | head =>
                intro hs
                have hm := CompCert4Lean.Lib.FSetAVLplus.Make.mem_1 s a hs
                change Nodeset.mem a s = true at hm
                rw [hmem] at hm
                cases hm
            | tail _ htail =>
                intro hs
                exact hdisj pc htail
                  (CompCert4Lean.Lib.FSetAVLplus.Make.add_2 s a pc hs)

theorem enumerate_complete : enumerate_completeStatement := by
  intro service f enum pc i henum hcode hreach
  unfold enumerate enumerateWithProposal at henum
  dsimp [enumerate_aux] at henum
  cases hnodes : nodeset_of_list (service f) Nodeset.empty with
  | Error msg =>
      simp [hnodes] at henum
  | OK s =>
      cases hcheck : check_reachable f (reachable f) s with
      | false =>
          simp [hnodes, hcheck] at henum
      | true =>
          simp [hnodes, hcheck] at henum
          cases henum
          have hs := check_reachable_correct f (reachable f) s pc i hcheck hcode hreach
          have hprops := linearize_nodeset_of_list_correct_aux
            (service f) Nodeset.empty s hnodes
          rcases (hprops.2.1 pc).mp hs with hempty | hmem
          · exact False.elim
              (CompCert4Lean.Backend.Linearize.Nodeset.empty_1_proof pc hempty)
          · exact hmem

theorem enumerate_norepet : enumerate_norepetStatement := by
  intro service f enum henum
  unfold enumerate enumerateWithProposal at henum
  dsimp [enumerate_aux] at henum
  cases hnodes : nodeset_of_list (service f) Nodeset.empty with
  | Error msg =>
      simp [hnodes] at henum
  | OK s =>
      cases hcheck : check_reachable f (reachable f) s with
      | false =>
          simp [hnodes, hcheck] at henum
      | true =>
          simp [hnodes, hcheck] at henum
          cases henum
          exact (linearize_nodeset_of_list_correct_aux
            (service f) Nodeset.empty s hnodes).1

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Linearize

private theorem linearize_is_tail_in {A : Type} (x : A) (c1 c2 : List A) :
    CompCert4Lean.Lib.Coqlib.is_tail (x :: c1) c2 -> List.Mem x c2 := by
  intro h
  induction c2 with
  | nil => cases h
  | cons a c2 ih =>
      cases h with
      | refl _ => exact List.Mem.head c1
      | cons _ htail => exact List.Mem.tail _ (ih htail)

private theorem linearize_is_tail_head {A : Type} (x a : A) (c1 c2 : List A) :
    CompCert4Lean.Lib.Coqlib.is_tail (x :: c1) (a :: c2) ->
      (a = x ∧ c1 = c2) ∨ CompCert4Lean.Lib.Coqlib.is_tail (x :: c1) c2 := by
  intro h
  cases h with
  | refl _ => exact Or.inl ⟨rfl, rfl⟩
  | cons i htail => exact Or.inr htail

private theorem linearize_unique_labels_tail (i : Linear.instruction)
    (c : Linear.code) : unique_labels (i :: c) -> unique_labels c := by
  intro h
  cases i <;> simp_all [unique_labels]

theorem find_label_unique : find_label_uniqueStatement := by
  intro lbl c1 c2
  induction c2 with
  | nil =>
      intro c3 htail huniq hfind
      change (none : Option Linear.code) = some _ at hfind
      cases hfind
  | cons a c2 ih =>
      intro c3 htail huniq hfind
      change (if CompCert4Lean.Backend.Linear.is_label lbl a then
          some (show Linear.code from c2)
        else CompCert4Lean.Backend.Linear.find_label lbl (show Linear.code from c2)) =
        some _ at hfind
      cases hlabel : CompCert4Lean.Backend.Linear.is_label lbl a with
      | false =>
          simp [hlabel] at hfind
          rcases linearize_is_tail_head (Linear.Llabel lbl) a c1 c2 htail with
            ⟨haeq, hceq⟩ | htail'
          · subst a
            cases hpeq : CompCert4Lean.Lib.Coqlib.peq lbl lbl with
            | left heq => simp [CompCert4Lean.Backend.Linear.is_label, hpeq] at hlabel
            | right hne => exact False.elim (hne rfl)
          · exact ih c3 htail' (linearize_unique_labels_tail a c2 huniq) hfind
      | true =>
          simp [hlabel] at hfind
          cases hfind
          have haeq : a = Linear.Llabel lbl := by
            have hc := CompCert4Lean.Backend.Linear.is_label_correct lbl a
            simpa [hlabel] using hc
          rcases linearize_is_tail_head (Linear.Llabel lbl) a c1 c2 htail with
            ⟨haeq', hceq⟩ | htail'
          · cases haeq'
            cases hceq
            rfl
          · subst a
            have hu : ¬ List.Mem (Linear.Llabel lbl) c2 := by
              have hu' : ¬ List.Mem (Linear.Llabel lbl) c2 ∧ unique_labels c2 := by
                simpa [unique_labels] using huniq
              exact hu'.1
            exact False.elim (hu (linearize_is_tail_in _ _ _ htail'))

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Linearize

theorem find_label_add_branch : find_label_add_branchStatement := by
  intro lbl k s
  unfold add_branch
  by_cases h : starts_with s k
  · simp [h]
  · simp [h, Linear.find_label, Linear.is_label]

private theorem find_label_cond_add_branch
    (lbl : Linear.label) (k : Linear.code)
    (cond : CompCert4Lean.X86.Op.condition)
    (args : List CompCert4Lean.X86.Machregs.mreg)
    (s1 s2 : CompCert4Lean.Backend.LTL.node) :
    Linear.find_label lbl
        (if starts_with s1 k then
          Linear.Lcond (CompCert4Lean.X86.Op.negate_condition cond) args s2 ::
            add_branch s1 k
        else
          Linear.Lcond cond args s1 :: add_branch s2 k) =
      Linear.find_label lbl k := by
  by_cases h : starts_with s1 k = true
  · simp [h, Linear.find_label, Linear.is_label]
    exact find_label_add_branch lbl k s1
  · simp [h, Linear.find_label, Linear.is_label]
    exact find_label_add_branch lbl k s2

theorem find_label_lin_block : find_label_lin_blockStatement := by
  intro lbl k b
  induction b with
  | nil => rfl
  | cons a b ih =>
      cases a <;>
        simp [linearize_block, Linear.find_label, Linear.is_label,
          ih, find_label_add_branch]
      all_goals
        first
        | exact find_label_add_branch lbl k _
        | exact find_label_cond_add_branch lbl k _ _ _ _

private theorem linearize_body_fold_left_append
    {A B : Type} (f : A → B → B) (acc : B) (xs ys : List A) :
    CompCert4Lean.Lib.Coqlib.list_fold_left f acc (xs ++ ys) =
      CompCert4Lean.Lib.Coqlib.list_fold_left f
        (CompCert4Lean.Lib.Coqlib.list_fold_left f acc xs) ys := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, CompCert4Lean.Lib.Coqlib.list_fold_left]
      exact ih (f x acc)

private theorem linearize_body_fold_right_cons
    (f : LTL.function) (pc : LTL.node) (enum : List LTL.node) :
    CompCert4Lean.Lib.Coqlib.list_fold_right (linearize_node f) (pc :: enum) [] =
      linearize_node f pc
        (CompCert4Lean.Lib.Coqlib.list_fold_right (linearize_node f) enum []) := by
  unfold CompCert4Lean.Lib.Coqlib.list_fold_right
  rw [List.reverse_cons]
  rw [linearize_body_fold_left_append (linearize_node f) ([] : Linear.code)
    (List.reverse enum) [pc]]
  rfl

theorem linearize_body_cons : linearize_body_consStatement := by
  intro f pc enum
  unfold linearize_body
  rw [linearize_body_fold_right_cons]
  unfold linearize_node
  rfl

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Linearize
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Lib.Coqlib

private theorem starts_with_is_tail_cons_left {A : Type} (x : A) (c1 c2 : List A) :
    is_tail (x :: c1) c2 -> is_tail c1 c2 := by
  induction c2 with
  | nil =>
      intro h
      cases h
  | cons i c2 ih =>
      intro h
      cases h with
      | refl _ => exact is_tail.cons x (is_tail.refl c1)
      | cons _ htail => exact is_tail.cons _ (ih htail)

theorem starts_with_correct
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 53)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 24)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 128)] :
    starts_with_correctStatement := by
  intro cfg xi tprog lbl c1
  induction c1 with
  | nil =>
      intro c2 c3 s f sp ls m htail huniq hstart hfind
      simp [starts_with] at hstart
  | cons a c1 ih =>
      intro c2 c3 s f sp ls m htail huniq hstart hfind
      cases a with
      | Llabel l =>
          simp only [starts_with] at hstart
          cases hpeq : CompCert4Lean.Lib.Coqlib.peq lbl l with
          | left heq =>
              subst l
              have hc := find_label_unique lbl c1 c2 c3 htail huniq hfind
              subst c3
              apply CompCert4Lean.Common.Smallstep.plus_left
                (Linear.State s f sp (Linear.Llabel lbl :: c1) ls m)
                CompCert4Lean.Common.Events.E0
              · exact CompCert4Lean.Backend.Linear.step.exec_Llabel
                  s f sp lbl c1 ls m
              · exact CompCert4Lean.Common.Smallstep.star_refl _ _ _
              · rfl
          | right hne =>
              apply CompCert4Lean.Common.Smallstep.plus_left
                (Linear.State s f sp (Linear.Llabel l :: c1) ls m)
                CompCert4Lean.Common.Events.E0
              · exact CompCert4Lean.Backend.Linear.step.exec_Llabel
                  s f sp l c1 ls m
              · exact CompCert4Lean.Common.Smallstep.plus_star _ _ _ _ _ _ _
                  (ih c2 c3 s f sp ls m
                    (starts_with_is_tail_cons_left _ _ _ htail)
                    huniq
                    (by simpa [hpeq] using hstart) hfind)
              · rfl
      | Lgetstack sl ofs ty dst => simp [starts_with] at hstart
      | Lsetstack src sl ofs ty => simp [starts_with] at hstart
      | Lop op args res => simp [starts_with] at hstart
      | Lload chunk addr args dst => simp [starts_with] at hstart
      | Lstore chunk addr args src => simp [starts_with] at hstart
      | Lcall sig ros => simp [starts_with] at hstart
      | Ltailcall sig ros => simp [starts_with] at hstart
      | Lbuiltin ef args res => simp [starts_with] at hstart
      | Lgoto l => simp [starts_with] at hstart
      | Lcond cond args l => simp [starts_with] at hstart
      | Ljumptable arg tbl => simp [starts_with] at hstart
      | Lreturn => simp [starts_with] at hstart

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Linearize

theorem label_in_add_branch : label_in_add_branchStatement := by
  intro lbl s k h
  unfold add_branch at h
  by_cases hs : starts_with s k
  · simpa [hs] using h
  · simp only [hs] at h
    cases h with
    | tail _ htail => exact htail

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Linearize

theorem label_in_lin_block : label_in_lin_blockStatement := by
  intro lbl k b h
  induction b with
  | nil => exact h
  | cons a b ih =>
      cases a with
      | Lop op args res =>
          simp only [linearize_block] at h
          cases h with
          | tail _ htail => exact ih htail
      | Lload chunk addr args dst =>
          simp only [linearize_block] at h
          cases h with
          | tail _ htail => exact ih htail
      | Lgetstack sl ofs ty dst =>
          simp only [linearize_block] at h
          cases h with
          | tail _ htail => exact ih htail
      | Lsetstack src sl ofs ty =>
          simp only [linearize_block] at h
          cases h with
          | tail _ htail => exact ih htail
      | Lstore chunk addr args src =>
          simp only [linearize_block] at h
          cases h with
          | tail _ htail => exact ih htail
      | Lcall sig ros =>
          simp only [linearize_block] at h
          cases h with
          | tail _ htail => exact ih htail
      | Ltailcall sig ros =>
          simp only [linearize_block] at h
          cases h with
          | tail _ htail => exact htail
      | Lbuiltin ef args res =>
          simp only [linearize_block] at h
          cases h with
          | tail _ htail => exact ih htail
      | Lbranch s =>
          simp only [linearize_block] at h
          exact label_in_add_branch lbl s k h
      | Lcond cond args s1 s2 =>
          simp only [linearize_block] at h
          by_cases hs : starts_with s1 k
          · simp only [hs] at h
            cases h with
            | tail _ htail => exact label_in_add_branch lbl s1 k htail
          · simp only [hs] at h
            cases h with
            | tail _ htail => exact label_in_add_branch lbl s2 k htail
      | Ljumptable arg tbl =>
          simp only [linearize_block] at h
          cases h with
          | tail _ htail => exact htail
      | Lreturn =>
          simp only [linearize_block] at h
          cases h with
          | tail _ htail => exact htail

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Linearize

theorem find_label_lin_rec : find_label_lin_recStatement := by
  intro f enum
  induction enum with
  | nil =>
      intro pc b hmem
      cases hmem
  | cons a enum ih =>
      intro pc b hmem hcode
      rw [linearize_body_cons]
      cases hpeq : CompCert4Lean.Lib.Coqlib.peq a pc with
      | left heq =>
          subst a
          refine ⟨linearize_body f enum, ?_⟩
          rw [hcode]
          simp [Linear.find_label, Linear.is_label, hpeq]
      | right hne =>
          have hmem' : List.Mem pc enum := by
            cases hmem with
            | head => exact False.elim (hne rfl)
            | tail _ htail => exact htail
          rcases ih pc b hmem' hcode with ⟨k, hk⟩
          cases hget : CompCert4Lean.Lib.Maps.PTree.get a f.fn_code with
          | none =>
              exact ⟨k, by simpa [hget] using hk⟩
          | some b' =>
              have hne' : ¬ pc = a := by
                intro heq
                exact hne heq.symm
              cases hpeq' : CompCert4Lean.Lib.Coqlib.peq pc a with
              | left heq' => exact False.elim (hne' heq')
              | right hneq' =>
                  refine ⟨k, ?_⟩
                  simp [Linear.find_label, Linear.is_label, hpeq']
                  have hfl := find_label_lin_block
                    (show Linear.label from pc) (linearize_body f enum) b'
                  rw [hfl]
                  exact hk

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Linearize

theorem find_label_lin : find_label_linStatement := by
  intro service f tf pc b htrans hcode hreach
  unfold CompCert4Lean.Backend.Linearize.transf_function at htrans
  cases henum : enumerate service f with
  | Error msg =>
      simp [henum] at htrans
  | OK enum =>
      simp [henum] at htrans
      cases htrans
      have hmem := enumerate_complete service f enum pc b henum hcode hreach
      rcases find_label_lin_rec f enum pc b hmem hcode with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      change Linear.find_label (show Linear.label from pc)
        (add_branch f.fn_entrypoint (linearize_body f enum)) = _
      calc
        Linear.find_label (show Linear.label from pc)
            (add_branch f.fn_entrypoint (linearize_body f enum)) =
            Linear.find_label (show Linear.label from pc)
              (linearize_body f enum) :=
          find_label_add_branch (show Linear.label from pc)
            (linearize_body f enum) f.fn_entrypoint
        _ = some (linearize_block b k) := hk

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Linearize

theorem label_in_lin_rec : label_in_lin_recStatement := by
  intro f lbl enum h
  induction enum with
  | nil =>
      simp [linearize_body, CompCert4Lean.Lib.Coqlib.list_fold_right,
        CompCert4Lean.Lib.Coqlib.list_fold_left] at h
      cases h
  | cons a enum ih =>
      rw [linearize_body_cons] at h
      cases hcode : CompCert4Lean.Lib.Maps.PTree.get a f.fn_code with
      | none =>
          apply List.Mem.tail a
          apply ih
          simpa [hcode] using h
      | some b =>
          simp only [hcode] at h
          cases h with
          | head => exact List.Mem.head enum
          | tail _ htail =>
              apply List.Mem.tail a
              apply ih
              exact label_in_lin_block lbl _ b htail

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Linearize

theorem unique_labels_add_branch : unique_labels_add_branchStatement := by
  intro lbl k huniq
  unfold add_branch
  by_cases hs : starts_with lbl k
  · simp [hs, huniq]
  · simpa [hs, unique_labels] using huniq

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Linearize
theorem unique_labels_lin_block : unique_labels_lin_blockStatement := by
  intro k b huniq
  induction b with
  | nil => exact huniq
  | cons a b ih =>
      cases a with
      | Lop _ _ _ | Lload _ _ _ _ | Lgetstack _ _ _ _ | Lsetstack _ _ _ _
      | Lstore _ _ _ _ | Lcall _ _ | Lbuiltin _ _ _ =>
          simp only [linearize_block]
          exact ih
      | Ltailcall _ _ | Ljumptable _ _ | Lreturn =>
          simp only [linearize_block]
          exact huniq
      | Lbranch s =>
          simp only [linearize_block]
          exact unique_labels_add_branch s k huniq
      | Lcond cond args s1 s2 =>
          simp only [linearize_block]
          by_cases hs : starts_with s1 k
          · simp only [hs]
            exact unique_labels_add_branch s1 k huniq
          · simp only [hs]
            exact unique_labels_add_branch s2 k huniq
end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Linearize
open CompCert4Lean.Lib.Coqlib

theorem unique_labels_lin_rec : unique_labels_lin_recStatement := by
  intro f enum
  induction enum with
  | nil =>
      intro hnr
      simp [linearize_body, CompCert4Lean.Lib.Coqlib.list_fold_right,
        CompCert4Lean.Lib.Coqlib.list_fold_left, unique_labels]
  | cons a enum ih =>
      intro hnr
      have htail : list_norepet enum := by
        cases hnr with
        | cons _ _ h => exact h
      rw [linearize_body_cons]
      cases hcode : CompCert4Lean.Lib.Maps.PTree.get a f.fn_code with
      | none =>
          simp only [hcode]
          exact ih htail
      | some b =>
          simp only [hcode, unique_labels]
          constructor
          · intro hmem
            have hmem' := label_in_lin_block
              (show Linear.label from a) (linearize_body f enum) b hmem
            have hmem'' := label_in_lin_rec f
              (show Linear.label from a) enum hmem'
            cases hnr with
            | cons _ hnot _ => exact hnot hmem''
          · exact unique_labels_lin_block (linearize_body f enum) b (ih htail)

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Linearize
open CompCert4Lean.Lib.Coqlib

theorem is_tail_find_label : is_tail_find_labelStatement := by
  intro lbl c2 c1
  induction c1 with
  | nil =>
      simp [Linear.find_label]
  | cons a c1 ih =>
      cases hlabel : Linear.is_label lbl a with
      | true =>
          simp [Linear.find_label, hlabel]
          intro h
          cases h
          exact is_tail.cons _ (is_tail.refl _)
      | false =>
          simp [Linear.find_label, hlabel]
          intro h
          exact is_tail.cons _ (ih h)

theorem is_tail_add_branch : is_tail_add_branchStatement := by
  intro lbl c1 c2 h
  unfold add_branch at h
  by_cases hs : starts_with lbl c1
  · simpa [hs] using h
  · apply starts_with_is_tail_cons_left _ _ _
    simpa [hs] using h

theorem is_tail_lin_block : is_tail_lin_blockStatement := by
  intro b c1 c2
  induction b with
  | nil =>
      intro h
      exact h
  | cons a b ih =>
      cases a with
      | Lop op args res =>
          intro h
          apply ih
          exact starts_with_is_tail_cons_left _ _ _ h
      | Lload chunk addr args dst =>
          intro h
          apply ih
          exact starts_with_is_tail_cons_left _ _ _ h
      | Lgetstack sl ofs ty dst =>
          intro h
          apply ih
          exact starts_with_is_tail_cons_left _ _ _ h
      | Lsetstack src sl ofs ty =>
          intro h
          apply ih
          exact starts_with_is_tail_cons_left _ _ _ h
      | Lstore chunk addr args src =>
          intro h
          apply ih
          exact starts_with_is_tail_cons_left _ _ _ h
      | Lcall sig ros =>
          intro h
          apply ih
          exact starts_with_is_tail_cons_left _ _ _ h
      | Ltailcall sig ros =>
          intro h
          exact starts_with_is_tail_cons_left _ _ _ h
      | Lbuiltin ef args res =>
          intro h
          apply ih
          exact starts_with_is_tail_cons_left _ _ _ h
      | Lbranch s =>
          intro h
          exact is_tail_add_branch s c1 c2 h
      | Lcond cond args s1 s2 =>
          intro h
          by_cases hs : starts_with s1 c1
          · apply is_tail_add_branch s1 c1 c2
            simp only [linearize_block, hs] at h
            exact starts_with_is_tail_cons_left _ _ _ h
          · apply is_tail_add_branch s2 c1 c2
            simp only [linearize_block, hs] at h
            exact starts_with_is_tail_cons_left _ _ _ h
      | Ljumptable arg tbl =>
          intro h
          exact starts_with_is_tail_cons_left _ _ _ h
      | Lreturn =>
          intro h
          exact starts_with_is_tail_cons_left _ _ _ h

theorem unique_labels_transf_function : unique_labels_transf_functionStatement := by
  intro service f tf htrans
  unfold CompCert4Lean.Backend.Linearize.transf_function at htrans
  cases henum : enumerate service f with
  | Error msg =>
      simp [henum] at htrans
  | OK enum =>
      simp [henum] at htrans
      cases htrans
      apply unique_labels_add_branch
      apply unique_labels_lin_rec
      exact enumerate_norepet service f enum henum

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof

theorem match_parent_locset : match_parent_locsetStatement := by
  intro service s ts h
  induction h with
  | nil =>
      rfl
  | cons a1 b1 hab hrest ih =>
      cases hab with
      | match_stackframe_intro f sp bb ls tf c htrans hreach htail =>
          rfl

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Linearize
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Smallstep

theorem add_branch_correct
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 53)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 24)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 128)] :
    add_branch_correctStatement := by
  intro cfg xi service tprog lbl c k s f tf sp ls m htrans htail hfind
  unfold add_branch
  by_cases hs : starts_with lbl k
  · simp only [hs]
    exact starts_with_correct cfg xi tprog lbl k tf.fn_code c s tf sp ls m
      htail (unique_labels_transf_function service f tf htrans) hs hfind
  · simp only [hs]
    apply plus_one
    exact Linear.step.exec_Lgoto s tf sp lbl k ls m c hfind

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof

open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.LTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib

private theorem linearize_initial_store_init_data
    {prog : LTL.program} {tprog : Linear.program}
    (hsymb : ∀ id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id)
    (m : mem) (b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
    (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (i : init_data) :
    Genv.store_init_data (Genv.globalenv prog) m b p i =
      Genv.store_init_data (Genv.globalenv tprog) m b p i := by
  cases i with
  | Init_addrof symb ofs =>
      simp [Genv.store_init_data, hsymb symb]
  | _ => rfl

private theorem linearize_initial_store_init_data_list
    {prog : LTL.program} {tprog : Linear.program}
    (hsymb : ∀ id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id) :
    ∀ (m : mem) (b : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
      (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (il : List init_data),
      Genv.store_init_data_list (Genv.globalenv prog) m b p il =
        Genv.store_init_data_list (Genv.globalenv tprog) m b p il := by
  intro m b p il
  induction il generalizing m b p with
  | nil => rfl
  | cons i rest ih =>
      simp only [Genv.store_init_data_list]
      rw [linearize_initial_store_init_data hsymb]
      cases h : Genv.store_init_data (Genv.globalenv tprog) m b p i with
      | none => simp [h]
      | some m' =>
          simp only [h]
          exact ih m' b
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
              p (init_data_size i))

private theorem linearize_initial_alloc_global
    [Linker LTL.program]
    (service : EnumerationService)
    {prog : LTL.program} {tprog : Linear.program}
    (hsymb : ∀ id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id)
    {id : ident} {gd : globdef LTL.fundef Unit}
    {tg : globdef Linear.fundef Unit}
    (hgd : match_globdef
      (fun (_ : LTL.program) f tf =>
        CompCert4Lean.Backend.Linearize.transf_fundef service f = .OK tf)
      (fun x y : Unit => x = y) prog gd tg)
    (m : mem) :
    Genv.alloc_global (Genv.globalenv prog) m (id, gd) =
      Genv.alloc_global (Genv.globalenv tprog) m (id, tg) := by
  cases hgd with
  | match_globdef_fun ctx' f1 f2 horder htrans =>
      rfl
  | match_globdef_var v1 v2 hvar =>
      cases hvar with
      | match_globvar_intro info1 info2 init ro vol hinfo =>
          cases hinfo
          simp only [Genv.alloc_global]
          simp [linearize_initial_store_init_data_list hsymb]

private theorem linearize_initial_alloc_globals
    [Linker LTL.program]
    (service : EnumerationService)
    {prog : LTL.program} {tprog : Linear.program}
    (hsymb : ∀ id,
      Genv.find_symbol (Genv.globalenv tprog) id =
        Genv.find_symbol (Genv.globalenv prog) id)
    (gl : List (ident × globdef LTL.fundef Unit))
    (tgl : List (ident × globdef Linear.fundef Unit))
    (hlist : CompCert4Lean.Lib.Coqlib.list_forall2
      (match_ident_globdef
        (fun (_ : LTL.program) f tf =>
          CompCert4Lean.Backend.Linearize.transf_fundef service f = .OK tf)
        (fun x y : Unit => x = y) prog) gl tgl) :
    ∀ (m m' : mem),
      Genv.alloc_globals (Genv.globalenv prog) m gl = some m' →
        Genv.alloc_globals (Genv.globalenv tprog) m tgl = some m' := by
  induction hlist with
  | nil =>
      intro m m' h
      simpa [Genv.alloc_globals] using h
  | cons hd thd hhd htl ih =>
      intro m m' h
      rcases hhd with ⟨hid, hgd⟩
      rcases hd with ⟨id, gd⟩
      rcases thd with ⟨tid, tgd⟩
      have halloc :
          Genv.alloc_global (Genv.globalenv prog) m (id, gd) =
            Genv.alloc_global (Genv.globalenv tprog) m (tid, tgd) := by
        change id = tid at hid
        subst tid
        exact linearize_initial_alloc_global service hsymb hgd m
      simp only [Genv.alloc_globals] at h ⊢
      rw [halloc] at h
      cases ha : Genv.alloc_global (Genv.globalenv tprog) m (tid, tgd) with
      | none => simp [ha] at h
      | some m1 =>
          simp only [ha] at h ⊢
          exact ih m1 m' h

theorem transf_initial_states : transf_initial_statesStatement := by
  letI : Linker LTL.fundef := Linker_fundef LTL.function
  letI : Linker Linear.fundef := Linker_fundef Linear.function
  letI : Linker Unit := Linker_unit
  letI : Linker LTL.program := Linker_prog LTL.fundef Unit
  intro service prog tprog hmatch st1 hinit
  cases hinit with
  | intro b f m0 hmem hsymb hfun hsig =>
      rcases function_ptr_translated service prog tprog hmatch b f hfun with
        ⟨tf, htf, htrans⟩
      refine ⟨Linear.Callstate [] tf
        (CompCert4Lean.Backend.Locations.Locmap.init Vundef) m0, ?_, ?_⟩
      · apply Linear.initial_state.initial_state_intro b tf m0
        · unfold Genv.init_mem at hmem ⊢
          exact linearize_initial_alloc_globals service
            (fun id => symbols_preserved service prog tprog hmatch id)
            prog.prog_defs tprog.prog_defs hmatch.1 Mem.empty m0 hmem
        · change Genv.find_symbol (Genv.globalenv tprog) tprog.prog_main = some b
          rw [hmatch.2.1]
          rw [symbols_preserved service prog tprog hmatch prog.prog_main]
          exact hsymb
        · exact htf
        · rw [sig_preserved service f tf htrans]
          exact hsig
      · exact match_states.match_states_call [] f
          (CompCert4Lean.Backend.Locations.Locmap.init Vundef) m0 tf []
          (CompCert4Lean.Lib.Coqlib.list_forall2.nil _) htrans

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof

open CompCert4Lean.Backend.Linearize
open CompCert4Lean.Backend.LTL
open CompCert4Lean.Lib.Maps

theorem reachable_entrypoint : reachable_entrypointStatement := by
  intro f
  unfold reachable
  cases h : reachable_aux f with
  | none =>
      change PMap.get f.fn_entrypoint (PMap.init true) = true
      exact PMap.gi f.fn_entrypoint true
  | some reach =>
      have hfix : CompCert4Lean.Backend.Linearize.DS.fixpoint
          f.fn_code LTL.successors_block (fun _ reachable => reachable)
          f.fn_entrypoint true = some reach := by
        exact h
      have hentry := CompCert4Lean.Backend.Linearize.DS.fixpoint_entry_proof
        CompCert4Lean.Backend.Linearize.DS.law_obligation_proof
      have hge := hentry LTL.bblock f.fn_code LTL.successors_block
        (fun _ reachable => reachable) f.fn_entrypoint true reach hfix
      change PMap.get f.fn_entrypoint reach = true ∨
        PMap.get f.fn_entrypoint reach = true at hge
      rcases hge with hge | hge <;> exact hge

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof

open CompCert4Lean.Backend.Linearize
open CompCert4Lean.Backend.LTL
open CompCert4Lean.Lib.Maps

theorem reachable_successors : reachable_successorsStatement := by
  intro f pc pc' b hcode hsucc hreach
  unfold reachable at hreach ⊢
  cases h : reachable_aux f with
  | none =>
      simp only [h] at hreach ⊢
      exact PMap.gi pc' true
  | some reach =>
      simp only [h] at hreach ⊢
      have hfix : CompCert4Lean.Backend.Linearize.DS.fixpoint
          f.fn_code LTL.successors_block (fun _ reachable => reachable)
          f.fn_entrypoint true = some reach := by
        exact h
      have hsol := CompCert4Lean.Backend.Linearize.DS.fixpoint_solution_proof
        CompCert4Lean.Backend.Linearize.DS.law_obligation_proof
      have hge := hsol LTL.bblock f.fn_code LTL.successors_block
        (fun _ reachable => reachable) f.fn_entrypoint true reach pc b pc'
        hfix hcode hsucc (by
          intro n
          rfl)
      change PMap.get pc' reach = PMap.get pc reach ∨
        PMap.get pc' reach = true at hge
      rw [hreach] at hge
      rcases hge with hge | hge <;> exact hge

end CompCert4Lean.Backend.Linearizeproof

namespace CompCert4Lean.Backend.Linearizeproof

theorem nodeset_of_list_correct : nodeset_of_list_correctStatement :=
  linearize_nodeset_of_list_correct_aux

end CompCert4Lean.Backend.Linearizeproof
