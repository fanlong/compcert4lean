import CompCert4Lean.Backend.Renumber
import CompCert4Lean.Common.Linking

/-!
# Correctness surface for RTL postorder renumbering

Definition-bearing translation of CompCert's `backend/Renumberproof.v`.
Proofs assigned to the later proof-migration phase are represented by exact
transparent proposition descriptors.
-/

namespace CompCert4Lean.Backend.Renumberproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
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

private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate

def match_prog (p tp : program) : Prop :=
  @match_program fundef Unit fundef Unit
    (Linker_fundef function) Linker_unit
    (fun _ f tf => tf = CompCert4Lean.Backend.Renumber.transf_fundef f)
    (fun x y : Unit => x = y)
    p tp

def transf_program_matchStatement : Prop :=
  ∀ p : program,
    match_prog p (CompCert4Lean.Backend.Renumber.transf_program p)

def functions_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ (v : val) (f : fundef),
      Genv.find_funct (Genv.globalenv prog) v = some f →
      Genv.find_funct (Genv.globalenv tprog) v =
        some (CompCert4Lean.Backend.Renumber.transf_fundef f)

def function_ptr_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ (v : block) (f : fundef),
      Genv.find_funct_ptr (Genv.globalenv prog) v = some f →
      Genv.find_funct_ptr (Genv.globalenv tprog) v =
        some (CompCert4Lean.Backend.Renumber.transf_fundef f)

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

def sig_preservedStatement : Prop :=
  ∀ f : fundef,
    funsig (CompCert4Lean.Backend.Renumber.transf_fundef f) = funsig f

def find_function_translatedStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ (ros : Sum reg ident) (rs : regset) (fd : fundef),
      find_function (Genv.globalenv prog) ros rs = some fd →
      find_function (Genv.globalenv tprog) ros rs =
        some (CompCert4Lean.Backend.Renumber.transf_fundef fd)

def pnum (f : function) : PTree.t positive :=
  CompCert4Lean.Lib.Postorder.postorder (successors_map f) f.fn_entrypoint

def reach (f : function) (pc : node) : Prop :=
  CompCert4Lean.Lib.Postorder.reachable (successors_map f) f.fn_entrypoint pc

def renum_cfg_nodesStatement : Prop :=
  ∀ (f : PTree.t positive),
    (∀ (x₁ x₂ y : positive),
      PTree.get x₁ f = some y → PTree.get x₂ f = some y → x₁ = x₂) →
    ∀ (c : code) (x y : positive) (i : instruction),
      PTree.get x c = some i →
      PTree.get x f = some y →
      PTree.get y (CompCert4Lean.Backend.Renumber.renum_cfg f c) =
        some (CompCert4Lean.Backend.Renumber.renum_instr f i)

def transf_function_atStatement : Prop :=
  ∀ (f : function) (pc : node) (i : instruction),
    PTree.get pc f.fn_code = some i →
    reach f pc →
    PTree.get
        (CompCert4Lean.Backend.Renumber.renum_pc (pnum f) pc)
        (CompCert4Lean.Backend.Renumber.transf_function f).fn_code =
      some (CompCert4Lean.Backend.Renumber.renum_instr (pnum f) i)

def reach_succStatement : Prop :=
  ∀ (f : function) (pc : positive) (i : instruction) (s : node),
    PTree.get pc f.fn_code = some i →
    s ∈ successors_instr i →
    reach f pc →
    reach f s

inductive match_frames : stackframe → stackframe → Prop where
  | match_frames_intro (res : reg) (f : function) (sp : val) (pc : node) (rs : regset)
      (hreach : reach f pc) :
      match_frames
        (Stackframe res f sp pc rs)
        (Stackframe res (CompCert4Lean.Backend.Renumber.transf_function f) sp
          (CompCert4Lean.Backend.Renumber.renum_pc (pnum f) pc) rs)

export match_frames (match_frames_intro)

inductive match_states : state → state → Prop where
  | match_regular_states (stk : List stackframe) (f : function) (sp : val) (pc : node)
      (rs : regset) (m : mem) (stk' : List stackframe)
      (stacks : list_forall2 match_frames stk stk')
      (hreach : reach f pc) :
      match_states
        (State stk f sp pc rs m)
        (State stk' (CompCert4Lean.Backend.Renumber.transf_function f) sp
          (CompCert4Lean.Backend.Renumber.renum_pc (pnum f) pc) rs m)
  | match_callstates (stk : List stackframe) (f : fundef) (args : List val) (m : mem)
      (stk' : List stackframe)
      (stacks : list_forall2 match_frames stk stk') :
      match_states
        (Callstate stk f args m)
        (Callstate stk' (CompCert4Lean.Backend.Renumber.transf_fundef f) args m)
  | match_returnstates (stk : List stackframe) (v : val) (m : mem)
      (stk' : List stackframe)
      (stacks : list_forall2 match_frames stk stk') :
      match_states
        (Returnstate stk v m)
        (Returnstate stk' v m)

export match_states (match_regular_states match_callstates match_returnstates)

def step_simulationStatement
    [binary64_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog tprog : program), match_prog prog tprog →
    ∀ (S1 : state) (t : trace) (S2 : state),
      step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) S1 t S2 →
      ∀ S1', match_states S1 S1' →
        ∃ S2',
          step
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            xi (Genv.globalenv tprog) S1' t S2' ∧
          match_states S2 S2'

def transf_initial_statesStatement : Prop :=
  ∀ (prog tprog : program), match_prog prog tprog →
    ∀ S1 : state, initial_state prog S1 →
      ∃ S2, initial_state tprog S2 ∧ match_states S1 S2

def transf_final_statesStatement : Prop :=
  ∀ (S1 S2 : state) (r : int),
    match_states S1 S2 → final_state S1 r → final_state S2 r

def transf_program_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog tprog : program),
    match_prog prog tprog →
    forward_simulation
      (semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi prog)
      (semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi tprog)

end CompCert4Lean.Backend.Renumberproof
