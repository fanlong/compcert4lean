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
open CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Builtins0
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
open CompCert4Lean.Common.Switch
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

private abbrev CminorProgram := CompCert4Lean.Backend.Cminor.program
private abbrev CminorSelProgram := CompCert4Lean.Backend.CminorSel.program
private abbrev CminorFundef := CompCert4Lean.Backend.Cminor.fundef
private abbrev CminorSelFundef := CompCert4Lean.Backend.CminorSel.fundef
private abbrev Globdef := CompCert4Lean.Common.AST.globdef CminorFundef Unit
private abbrev Env := CompCert4Lean.Backend.Cminor.env
private abbrev HelperFunctions := CompCert4Lean.Backend.SplitLong.helper_functions
private abbrev KnownIdents := CompCert4Lean.Backend.Cminortyping.known_idents
private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev SelectionOracle := CompCert4Lean.Backend.Selection.SelectionOracle
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev BexactInverseCertificate :=
  CompCert4Lean.Lib.IEEE754_extra.Bexact_inverse_certificate
private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string
private abbrev zle := ZArith.BinInt.Z.le
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

private instance cminorFundefLinker : Linker CminorFundef :=
  CompCert4Lean.Common.Linking.Linker_fundef Cminor.function

private instance cminorProgramLinker : Linker CminorProgram :=
  CompCert4Lean.Common.Linking.Linker_prog CminorFundef Unit

/-! Relational specification of instruction selection. -/

def match_fundef
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (oracle : SelectionOracle)
    (cunit : CminorProgram) (f : CminorFundef)
    (tf : CminorSelFundef) : Prop :=
  ∃ hf : HelperFunctions,
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared cunit hf ∧
    sel_fundef cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      (prog_defmap cunit) hf f = .OK tf

def match_prog
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (oracle : SelectionOracle) (p : CminorProgram)
    (tp : CminorSelProgram) : Prop :=
  @CompCert4Lean.Common.Linking.match_program
    CminorFundef Unit CminorSelFundef Unit
    (CompCert4Lean.Common.Linking.Linker_fundef Cminor.function)
    CompCert4Lean.Common.Linking.Linker_unit
    (fun cu f tf => match_fundef cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) cu f tf) Eq p tp

/-! Local environment less-definedness. -/

def env_lessdef (e1 e2 : Env) : Prop :=
  ∀ id v1, PTree.get id e1 = some v1 →
    ∃ v2, PTree.get id e2 = some v2 ∧ Val.lessdef v1 v2

/-! Switch-value relations. -/

inductive Rint : Z → val → Prop where
  | intro (n : int) : Rint (Int.unsigned n) (Vint n)

inductive Rlong : Z → val → Prop where
  | intro (n : int64) : Rlong (Int64.unsigned n) (Vlong n)

/-! Preserve the exact source-facing names of the two primary constructors.
The aliases add no proof obligation and delegate to the corresponding Lean
kernel constructors without changing either relation. -/

abbrev Rint_intro := @Rint.intro

abbrev Rlong_intro := @Rlong.intro

/-! The eventual relation used by the simulation diagram. -/

def eventually
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (prog : CminorProgram) (xi : ExternalCalls) (n : Nat) (s : Cminor.state)
    (P : Cminor.state → Prop) : Prop :=
  CompCert4Lean.Common.Smallstep.eventually
    (fun ge => Cminor.step
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge)
    Cminor.final_state (Genv.globalenv prog) n s P

/-! Semantic state matching.  The generated constructor names are part of the
source-facing API and are intentionally retained. -/

mutual
inductive match_cont
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (oracle : SelectionOracle)
    (prog : CminorProgram) :
    CminorProgram → HelperFunctions → KnownIdents → typenv →
    Cminor.cont → CminorSel.cont → Prop
  | match_cont_seq (cunit : CminorProgram) (hf : HelperFunctions)
      (ki : KnownIdents) (env : typenv) (s : Cminor.stmt) (kont : CminorSel.stmt)
      (s' : CminorSel.stmt) (k : Cminor.cont) (k' : CminorSel.cont)
      (hsel : sel_stmt cfg oracle
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        (prog_defmap cunit) ki env s kont = .OK s')
      (hcont : match_cont
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog cunit hf ki env k k') :
      match_cont
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog cunit hf ki env
        (Cminor.Kseq s k) (CminorSel.Kseq s' k')
  | match_cont_block (cunit : CminorProgram) (hf : HelperFunctions)
      (ki : KnownIdents) (env : typenv) (k : Cminor.cont) (k' : CminorSel.cont)
      (hcont : match_cont
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog cunit hf ki env k k') :
      match_cont
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog cunit hf ki env
        (Cminor.Kblock k) (CminorSel.Kblock k')
  | match_cont_other (cunit : CminorProgram) (hf : HelperFunctions)
      (ki : KnownIdents) (env : typenv) (k : Cminor.cont) (k' : CminorSel.cont)
      (hcall : match_call_cont
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog k k') :
      match_cont
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog cunit hf ki env k k'

inductive match_call_cont
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (oracle : SelectionOracle)
    (prog : CminorProgram) :
    Cminor.cont → CminorSel.cont → Prop where
  | match_cont_stop :
      match_call_cont
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog Cminor.Kstop CminorSel.Kstop
  | match_cont_call (cunit : CminorProgram) (hf : HelperFunctions)
      (env : typenv) (id : Option ident) (f : Cminor.function) (sp : val)
      (e : Env) (k : Cminor.cont) (f' : CminorSel.function)
      (e' : Env) (k' : CminorSel.cont)
      (hlink : linkorder cunit prog)
      (hhf : CompCert4Lean.Backend.SplitLongproof.helper_functions_declared cunit hf)
      (hsel : sel_function cfg oracle
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        (prog_defmap cunit) hf f = .OK f')
      (hty : type_function f = .OK env)
      (hcont : match_cont
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog cunit hf
        (CompCert4Lean.Backend.Selection.known_id f) env k k')
      (hld : env_lessdef e e') :
      match_call_cont
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog (Cminor.Kcall id f sp e k)
        (CminorSel.Kcall id f' sp e' k')
end

inductive match_states
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (oracle : SelectionOracle)
    (prog : CminorProgram) :
    Cminor.state → CminorSel.state → Prop where
  | match_state (cunit : CminorProgram) (hf : HelperFunctions)
      (f : Cminor.function) (f' : CminorSel.function)
      (s : Cminor.stmt) (kont : Cminor.cont) (k : CminorSel.stmt)
      (s' : CminorSel.stmt) (k' : CminorSel.cont) (sp : val)
      (e : Env) (m : mem) (e' : Env) (m' : mem) (env : typenv)
      (hlink : linkorder cunit prog)
      (hhf : CompCert4Lean.Backend.SplitLongproof.helper_functions_declared cunit hf)
      (hsel : sel_function cfg oracle
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        (prog_defmap cunit) hf f = .OK f')
      (hty : type_function f = .OK env)
      (hstmt : sel_stmt cfg oracle
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        (prog_defmap cunit)
        (CompCert4Lean.Backend.Selection.known_id f) env s k = .OK s')
      (hcont : match_cont
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog cunit hf
        (CompCert4Lean.Backend.Selection.known_id f) env kont k')
      (hld : env_lessdef e e') (hme : Mem.extends m m') :
      match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog (Cminor.State f s kont sp e m)
        (CminorSel.State f' s' k' sp e' m')
  | match_callstate (cunit : CminorProgram) (f : CminorFundef)
      (f' : CminorSelFundef) (args args' : List val)
      (k : Cminor.cont) (k' : CminorSel.cont) (m m' : mem)
      (hlink : linkorder cunit prog)
      (hfun : match_fundef cfg oracle
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cunit f f')
      (hcont : match_call_cont
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog k k')
      (hld : Val.lessdef_list args args') (hme : Mem.extends m m') :
      match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog (Cminor.Callstate f args k m)
        (CminorSel.Callstate f' args' k' m')
  | match_returnstate (v v' : val) (k : Cminor.cont) (k' : CminorSel.cont)
      (m m' : mem)
      (hcont : match_call_cont
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog k k')
      (hld : Val.lessdef v v') (hme : Mem.extends m m') :
      match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog (Cminor.Returnstate v k m)
        (.Returnstate v' k' m')
  | match_builtin_1 (cunit : CminorProgram) (hf : HelperFunctions)
      (ef : external_function) (args : List val) (optid : Option ident)
      (f : Cminor.function) (sp : val) (e : Env) (k : Cminor.cont)
      (m : mem) (al : List Cminor.expr) (f' : CminorSel.function)
      (e' : Env) (k' : CminorSel.cont) (m' : mem) (env : typenv)
      (hlink : linkorder cunit prog)
      (hhf : CompCert4Lean.Backend.SplitLongproof.helper_functions_declared cunit hf)
      (hsel : sel_function cfg oracle
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        (prog_defmap cunit) hf f = .OK f')
      (hty : type_function f = .OK env)
      (hcont : match_cont
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog cunit hf
        (CompCert4Lean.Backend.Selection.known_id f) env k k')
      (heval : @Cminor.eval_exprlist
        binary64_certificate binary32_certificate
        (Genv.globalenv prog) sp e m al args)
      (hld : env_lessdef e e') (hme : Mem.extends m m') :
      match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog
        (Cminor.Callstate (.External ef) args (Cminor.Kcall optid f sp e k) m)
        (CminorSel.State f'
          (sel_builtin cfg
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            (binary64_inverse_certificate := binary64_inverse_certificate)
            (binary32_inverse_certificate := binary32_inverse_certificate)
            optid ef al) k' sp e' m')
  | match_builtin_2 (cunit : CminorProgram) (hf : HelperFunctions)
      (v v' : val) (optid : Option ident) (f : Cminor.function) (sp : val)
      (e : Env) (k : Cminor.cont) (m : mem) (f' : CminorSel.function)
      (e' : Env) (m' : mem) (k' : CminorSel.cont) (env : typenv)
      (hlink : linkorder cunit prog)
      (hhf : CompCert4Lean.Backend.SplitLongproof.helper_functions_declared cunit hf)
      (hsel : sel_function cfg oracle
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        (prog_defmap cunit) hf f = .OK f')
      (hty : type_function f = .OK env)
      (hcont : match_cont
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog cunit hf
        (CompCert4Lean.Backend.Selection.known_id f) env k k')
      (hld : Val.lessdef v v')
      (hlde : env_lessdef (Cminor.set_optvar optid v e) e')
      (hme : Mem.extends m m') :
      match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog
        (Cminor.Returnstate v (Cminor.Kcall optid f sp e k) m)
        (CminorSel.State f' CminorSel.Sskip k' sp e' m')

export match_cont (match_cont_seq match_cont_block match_cont_other)
export match_call_cont (match_cont_stop match_cont_call)
export match_states (match_state match_callstate match_returnstate match_builtin_1 match_builtin_2)

/-! The executable measure and no-label predicates. -/

def measure : Cminor.state → Nat
  | .Callstate _ _ _ _ => 0
  | .State _ _ _ _ _ _ => 1
  | .Returnstate _ _ _ => 2

def nolabel (s : Cminor.stmt) : Prop :=
  ∀ lbl k, Cminor.find_label lbl s k = none

def nolabel' (s : CminorSel.stmt) : Prop :=
  ∀ lbl k, CminorSel.find_label lbl s k = none

/-! Exact source declaration descriptors for later proof migration. -/

variable [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
variable [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
variable [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
variable [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
variable (cfg : CompilerConfig) (oracle : SelectionOracle)

def record_globdefs_soundStatement : Prop :=
  ∀ (dm : PTree.t Globdef) (id : ident) (gd : Globdef),
    PTree.get id (record_globdefs dm) = some gd → PTree.get id dm = some gd

def lookup_helper_correct_1Statement : Prop :=
  ∀ (globs : PTree.t Globdef) (name : RocqString) (sg : signature) (id : ident),
    lookup_helper globs name sg = .OK id →
      PTree.get id globs = some (.Gfun (.External (.EF_runtime name sg)))

def lookup_helper_correctStatement : Prop :=
  ∀ (p : CminorProgram) (name : RocqString) (sg : signature) (id : ident),
    lookup_helper (record_globdefs (prog_defmap p)) name sg = .OK id →
      CompCert4Lean.Backend.SplitLongproof.helper_declared p id name sg

def get_helpers_correctStatement : Prop :=
  ∀ (p : CminorProgram) (hf : HelperFunctions),
    get_helpers (prog_defmap p) = .OK hf →
      CompCert4Lean.Backend.SplitLongproof.helper_functions_declared p hf

def transf_program_matchStatement : Prop :=
  ∀ (p : CminorProgram) (tp : CminorSelProgram),
    sel_program cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      p = .OK tp → match_prog cfg oracle
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate) p tp

def helper_functions_declared_linkorderStatement : Prop :=
  ∀ (p p' : CminorProgram) (hf : HelperFunctions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared p hf →
    linkorder p p' →
      CompCert4Lean.Backend.SplitLongproof.helper_functions_declared p' hf

def wt_progStatement : Prop :=
  ∀ (prog : CminorProgram) (tprog : CminorSelProgram),
    match_prog cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) prog tprog → wt_program prog

def symbols_preservedStatement : Prop :=
  ∀ (prog : CminorProgram) (tprog : CminorSelProgram),
    match_prog cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) prog tprog →
      ∀ s : ident,
        Genv.find_symbol (Genv.globalenv tprog) s =
          Genv.find_symbol (Genv.globalenv prog) s

def senv_preservedStatement : Prop :=
  ∀ (prog : CminorProgram) (tprog : CminorSelProgram),
    match_prog cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) prog tprog →
      Senv.equiv (Genv.to_senv (Genv.globalenv prog))
        (Genv.to_senv (Genv.globalenv tprog))

def function_ptr_translatedStatement : Prop :=
  ∀ (prog : CminorProgram) (tprog : CminorSelProgram),
    match_prog cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) prog tprog →
      ∀ (b : block) (f : CminorFundef),
        Genv.find_funct_ptr (Genv.globalenv prog) b = some f →
          ∃ (cu : CminorProgram) (tf : CminorSelFundef),
            Genv.find_funct_ptr (Genv.globalenv tprog) b = some tf ∧
            match_fundef cfg oracle
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate)
              (binary64_inverse_certificate := binary64_inverse_certificate)
              (binary32_inverse_certificate := binary32_inverse_certificate)
              cu f tf ∧ linkorder cu prog

def functions_translatedStatement : Prop :=
  ∀ (prog : CminorProgram) (tprog : CminorSelProgram),
    match_prog cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) prog tprog →
      ∀ (v v' : val) (f : CminorFundef),
        Genv.find_funct (Genv.globalenv prog) v = some f →
        Val.lessdef v v' →
          ∃ (cu : CminorProgram) (tf : CminorSelFundef),
            Genv.find_funct (Genv.globalenv tprog) v' = some tf ∧
            match_fundef cfg oracle
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate)
              (binary64_inverse_certificate := binary64_inverse_certificate)
              (binary32_inverse_certificate := binary32_inverse_certificate)
              cu f tf ∧ linkorder cu prog

def sig_function_translatedStatement : Prop :=
  ∀ (cu : CminorProgram) (f : CminorFundef) (tf : CminorSelFundef),
    match_fundef cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      cu f tf → CminorSel.funsig tf = Cminor.funsig f

def stackspace_function_translatedStatement : Prop :=
  ∀ (dm : PTree.t Globdef) (hf : HelperFunctions)
    (f : Cminor.function) (tf : CminorSel.function),
    sel_function cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      dm hf f = .OK tf → tf.fn_stackspace = f.fn_stackspace

def helper_functions_preservedStatement : Prop :=
  ∀ (prog : CminorProgram) (tprog : CminorSelProgram),
    match_prog cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) prog tprog →
      ∀ hf : HelperFunctions,
        CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
          CompCert4Lean.Backend.SplitLongproof.helper_functions_declared tprog hf

def eval_condexpr_of_exprStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (tprog : CminorSelProgram) (sp : val) (e : Env) (m : mem)
    (a : CminorSel.expr) (le : CminorSel.letenv) (v : val) (b : Bool),
    CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le a v →
    Val.bool_of_val v b →
      CminorSel.eval_condexpr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le
        (condexpr_of_expr a) b

def eval_condition_of_exprStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (tprog : CminorSelProgram) (sp : val) (e : Env) (m : mem)
    (a : CminorSel.expr) (le : CminorSel.letenv) (v : val) (b : Bool),
    CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le a v →
    Val.bool_of_val v b →
      ∃ vl,
        CminorSel.eval_exprlist
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le
          (condition_of_expr a).2 vl ∧
        eval_condition (condition_of_expr a).1 vl m = some b

def eval_loadStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (tprog : CminorSelProgram) (sp : val) (e : Env) (m : mem)
    (le : CminorSel.letenv) (a : CminorSel.expr) (v : val) (chunk : memory_chunk)
    (v' : val),
    CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le a v →
    Mem.loadv chunk m v = some v' →
      CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le (load chunk a) v'

def eval_storeStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (tprog : CminorSelProgram) (sp : val) (e : Env) (m : mem)
    (chunk : memory_chunk) (a1 a2 : CminorSel.expr) (v1 v2 : val)
    (f : CminorSel.function) (k : CminorSel.cont) (m' : mem),
    CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m [] a1 v1 →
    CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m [] a2 v2 →
    Mem.storev chunk m v1 v2 = some m' →
      CminorSel.step
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog)
        (CminorSel.State f (store chunk a1 a2) k sp e m) E0
        (CminorSel.State f CminorSel.Sskip k sp e m')

def eval_sel_unopStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorProgram) (tprog : CminorSelProgram),
    match_prog cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) prog tprog →
    ∀ (cunit : CminorProgram) (hf : HelperFunctions),
      linkorder cunit prog →
      CompCert4Lean.Backend.SplitLongproof.helper_functions_declared cunit hf →
      ∀ (sp : val) (e : Env) (m : mem) (le : CminorSel.letenv)
        (op : Cminor.unary_operation) (a1 : CminorSel.expr) (v1 v : val),
        CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le a1 v1 →
        Cminor.eval_unop
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) op v1 = some v →
          ∃ v',
            CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le
              (sel_unop
                (binary64_certificate := binary64_certificate)
                (binary32_certificate := binary32_certificate)
                op a1) v' ∧ Val.lessdef v v'

def eval_sel_binopStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorProgram) (tprog : CminorSelProgram),
    match_prog cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) prog tprog →
    ∀ (cunit : CminorProgram) (hf : HelperFunctions),
      linkorder cunit prog →
      CompCert4Lean.Backend.SplitLongproof.helper_functions_declared cunit hf →
      ∀ (sp : val) (e : Env) (m : mem) (le : CminorSel.letenv)
        (op : Cminor.binary_operation) (a1 a2 : CminorSel.expr)
        (v1 v2 v : val),
        CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le a1 v1 →
        CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le a2 v2 →
        Cminor.eval_binop op v1 v2 m = some v →
          ∃ v',
            CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le
              (sel_binop cfg
                (binary64_inverse_certificate := binary64_inverse_certificate)
                (binary32_inverse_certificate := binary32_inverse_certificate)
                op a1 a2) v' ∧ Val.lessdef v v'

def eval_sel_selectStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (tprog : CminorSelProgram) (sp : val) (e : Env) (m : mem)
    (le : CminorSel.letenv) (a1 a2 a3 : CminorSel.expr) (v1 v2 v3 : val)
    (b : Bool) (ty : typ),
    CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le a1 v1 →
    CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le a2 v2 →
    CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le a3 v3 →
    Val.bool_of_val v1 b →
      ∃ v,
        CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le
          (sel_select ty a1 a2 a3) v ∧
        Val.lessdef (Val.select (some b) v2 v3 ty) v

def eval_sel_known_builtinStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (tprog : CminorSelProgram) (sp : val) (e : Env) (m : mem)
    (bf : builtin_function) (args : CminorSel.exprlist) (a : CminorSel.expr)
    (vl : List val) (v : val) (le : CminorSel.letenv),
    sel_known_builtin bf args = some a →
    CminorSel.eval_exprlist
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le args vl →
    builtin_function_sem
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) bf vl = some v →
      ∃ v',
        CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le a v' ∧
        Val.lessdef v v'

def expr_is_addrof_ident_correctStatement : Prop :=
  ∀ (e : Cminor.expr) (id : ident),
    expr_is_addrof_ident e = some id →
      e = Cminor.Econst (Cminor.Oaddrsymbol id Ptrofs.zero)

def classify_call_correctStatement
 : Prop :=
  ∀ (prog unit : CminorProgram) (sp : val) (e : Env) (m : mem)
      (a : Cminor.expr) (v : val) (fd : CminorFundef),
    linkorder unit prog →
    Cminor.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) (Genv.globalenv prog) sp e m a v →
    Genv.find_funct (Genv.globalenv prog) v = some fd →
    match classify_call (prog_defmap unit) a with
    | Call_default => True
    | Call_imm id => ∃ b, Genv.find_symbol (Genv.globalenv prog) id = some b ∧
        v = Vptr b Ptrofs.zero
    | Call_builtin ef => fd = .External ef

def sel_switch_correct_recStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (tprog : CminorSelProgram)
    (make_cmp_eq make_cmp_ltu make_sub : CminorSel.expr → Z → CminorSel.expr)
    (make_to_int : CminorSel.expr → CminorSel.expr) (modulus : Z)
    (R : Z → val → Prop),
    (∀ (sp : val) (e : Env) (m : mem) (le : CminorSel.letenv)
      (a : CminorSel.expr) (v : val) (i n : Z),
      CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le a v →
      R i v → zle .Z0 n ∧ ZArith.BinInt.Z.lt n modulus →
      CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le (make_cmp_eq a n)
        (Val.of_bool (proj_sumbool (zeq i n)))) →
    (∀ (sp : val) (e : Env) (m : mem) (le : CminorSel.letenv)
      (a : CminorSel.expr) (v : val) (i n : Z),
      CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le a v →
      R i v → zle .Z0 n ∧ ZArith.BinInt.Z.lt n modulus →
      CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le (make_cmp_ltu a n)
        (Val.of_bool (proj_sumbool (CompCert4Lean.Lib.Coqlib.zlt i n)))) →
    (∀ (sp : val) (e : Env) (m : mem) (le : CminorSel.letenv)
      (a : CminorSel.expr) (v : val) (i n : Z),
      CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le a v →
      R i v → zle .Z0 n ∧ ZArith.BinInt.Z.lt n modulus →
      ∃ v',
        CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le (make_sub a n) v' ∧
        R (ZArith.BinInt.Z.modulo (ZArith.BinInt.Z.sub i n) modulus) v') →
    (∀ (sp : val) (e : Env) (m : mem) (le : CminorSel.letenv)
      (a : CminorSel.expr) (v : val) (i : Z),
      CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le a v →
      R i v →
      ∃ v',
        CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le (make_to_int a) v' ∧
        Rint (ZArith.BinInt.Z.modulo i Int.modulus) v') →
    ∀ (sp : val) (e : Env) (m : mem) (varg : val) (i : Z) (x : Nat),
      R i varg →
      ∀ (t : comptree) (arg : Nat) (le : CminorSel.letenv),
        wf_comptree modulus t → nth_error le arg = some varg →
        comptree_match modulus i t = some x →
        CminorSel.eval_exitexpr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le
          (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int arg t) x

def sel_switch_correctStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (tprog : CminorSelProgram)
    (make_cmp_eq make_cmp_ltu make_sub : CminorSel.expr → Z → CminorSel.expr)
    (make_to_int : CminorSel.expr → CminorSel.expr) (modulus : Z)
    (R : Z → val → Prop),
    (∀ (sp : val) (e : Env) (m : mem) (le : CminorSel.letenv)
      (a : CminorSel.expr) (v : val) (i n : Z),
      CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le a v →
      R i v → zle .Z0 n ∧ ZArith.BinInt.Z.lt n modulus →
      CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le (make_cmp_eq a n)
        (Val.of_bool (proj_sumbool (zeq i n)))) →
    (∀ (sp : val) (e : Env) (m : mem) (le : CminorSel.letenv)
      (a : CminorSel.expr) (v : val) (i n : Z),
      CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le a v →
      R i v → zle .Z0 n ∧ ZArith.BinInt.Z.lt n modulus →
      CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le (make_cmp_ltu a n)
        (Val.of_bool (proj_sumbool (CompCert4Lean.Lib.Coqlib.zlt i n)))) →
    (∀ (sp : val) (e : Env) (m : mem) (le : CminorSel.letenv)
      (a : CminorSel.expr) (v : val) (i n : Z),
      CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le a v →
      R i v → zle .Z0 n ∧ ZArith.BinInt.Z.lt n modulus →
      ∃ v',
        CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le (make_sub a n) v' ∧
        R (ZArith.BinInt.Z.modulo (ZArith.BinInt.Z.sub i n) modulus) v') →
    (∀ (sp : val) (e : Env) (m : mem) (le : CminorSel.letenv)
      (a : CminorSel.expr) (v : val) (i : Z),
      CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le a v →
      R i v →
      ∃ v',
        CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le (make_to_int a) v' ∧
        Rint (ZArith.BinInt.Z.modulo i Int.modulus) v') →
    ∀ (dfl : Nat) (cases : table) (arg : CminorSel.expr)
      (sp : val) (e : Env) (m : mem) (varg : val) (i : Z) (t : comptree)
      (le : CminorSel.letenv),
      validate_switch modulus dfl cases t = true →
      CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le arg varg →
      R i varg → zle .Z0 i ∧ ZArith.BinInt.Z.lt i modulus →
      CminorSel.eval_exitexpr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le
        (.XElet arg (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int 0 t))
        (switch_target i dfl cases)

def sel_switch_int_correctStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (tprog : CminorSelProgram) (dfl : Nat) (cases : table)
    (arg : CminorSel.expr) (sp : val) (e : Env) (m : mem) (i : int)
    (t : comptree) (le : CminorSel.letenv),
    validate_switch Int.modulus dfl cases t = true →
    CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le arg (.Vint i) →
    CminorSel.eval_exitexpr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le
      (.XElet arg (sel_switch_int 0 t))
      (switch_target (Int.unsigned i) dfl cases)

def sel_switch_long_correctStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (tprog : CminorSelProgram) (dfl : Nat) (cases : table)
    (arg : CminorSel.expr) (sp : val) (e : Env) (m : mem) (i : int64)
    (t : comptree) (le : CminorSel.letenv),
    validate_switch Int64.modulus dfl cases t = true →
    CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le arg (.Vlong i) →
    CminorSel.eval_exitexpr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e m le
      (.XElet arg (sel_switch_long 0 t))
      (switch_target (Int64.unsigned i) dfl cases)

def eval_unop_lessdefStatement
 : Prop :=
  ∀ (op : Cminor.unary_operation) (v1 v1' v : val),
    Cminor.eval_unop
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) op v1 = some v → Val.lessdef v1 v1' →
      ∃ v2, Cminor.eval_unop
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) op v1' = some v2 ∧ Val.lessdef v v2

def eval_binop_lessdefStatement : Prop :=
  ∀ (op : Cminor.binary_operation) (v1 v1' v2 v2' v : val) (m m' : mem),
    Cminor.eval_binop op v1 v2 m = some v → Val.lessdef v1 v1' →
    Val.lessdef v2 v2' → Mem.extends m m' →
      ∃ v', Cminor.eval_binop op v1' v2' m' = some v' ∧ Val.lessdef v v'

def set_var_lessdefStatement : Prop :=
  ∀ (e1 e2 : Env) (id : ident) (v1 v2 : val),
    env_lessdef e1 e2 → Val.lessdef v1 v2 →
      env_lessdef (PTree.set id v1 e1) (PTree.set id v2 e2)

def set_params_lessdefStatement : Prop :=
  ∀ (il : List ident) (vl1 vl2 : List val),
    Val.lessdef_list vl1 vl2 → env_lessdef (Cminor.set_params vl1 il) (Cminor.set_params vl2 il)

def set_locals_lessdefStatement : Prop :=
  ∀ (e1 e2 : Env), env_lessdef e1 e2 →
    ∀ il : List ident, env_lessdef (Cminor.set_locals il e1) (Cminor.set_locals il e2)

def sel_expr_correctStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorProgram) (tprog : CminorSelProgram),
    match_prog cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) prog tprog →
    ∀ (cunit : CminorProgram) (hf : HelperFunctions),
      linkorder cunit prog →
      CompCert4Lean.Backend.SplitLongproof.helper_functions_declared cunit hf →
      ∀ (sp : val) (e : Env) (m : mem) (a : Cminor.expr) (v : val),
        Cminor.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) (Genv.globalenv prog) sp e m a v →
        ∀ (e' : Env) (le : CminorSel.letenv) (m' : mem),
          env_lessdef e e' → Mem.extends m m' →
            ∃ v',
              CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e' m' le
                (sel_expr cfg
                  (binary64_certificate := binary64_certificate)
                  (binary32_certificate := binary32_certificate)
                  (binary64_inverse_certificate := binary64_inverse_certificate)
                  (binary32_inverse_certificate := binary32_inverse_certificate)
                  a) v' ∧
              Val.lessdef v v'

def sel_exprlist_correctStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorProgram) (tprog : CminorSelProgram),
    match_prog cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) prog tprog →
    ∀ (cunit : CminorProgram) (hf : HelperFunctions),
      linkorder cunit prog →
      CompCert4Lean.Backend.SplitLongproof.helper_functions_declared cunit hf →
      ∀ (sp : val) (e : Env) (m : mem) (a : List Cminor.expr) (v : List val),
        Cminor.eval_exprlist
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) (Genv.globalenv prog) sp e m a v →
        ∀ (e' : Env) (le : CminorSel.letenv) (m' : mem),
          env_lessdef e e' → Mem.extends m m' →
            ∃ v',
              CminorSel.eval_exprlist
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e' m' le
                (sel_exprlist cfg
                  (binary64_certificate := binary64_certificate)
                  (binary32_certificate := binary32_certificate)
                  (binary64_inverse_certificate := binary64_inverse_certificate)
                  (binary32_inverse_certificate := binary32_inverse_certificate)
                  a) v' ∧ Val.lessdef_list v v'

def sel_select_expr_correctStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorProgram) (tprog : CminorSelProgram),
    match_prog cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) prog tprog →
    ∀ (cunit : CminorProgram) (hf : HelperFunctions),
      linkorder cunit prog →
      CompCert4Lean.Backend.SplitLongproof.helper_functions_declared cunit hf →
      ∀ (ty : typ) (cond a1 a2 : Cminor.expr) (sp : val) (e : Env) (m : mem)
        (vcond v1 v2 : val) (b : Bool) (e' : Env) (m' : mem)
        (le : CminorSel.letenv),
        select_supported ty = true →
        Cminor.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) (Genv.globalenv prog) sp e m cond vcond →
        Cminor.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) (Genv.globalenv prog) sp e m a1 v1 →
        Cminor.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) (Genv.globalenv prog) sp e m a2 v2 →
        Val.bool_of_val vcond b → env_lessdef e e' → Mem.extends m m' →
          ∃ v',
            CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e' m' le
              (sel_select_expr cfg
                (binary64_certificate := binary64_certificate)
                (binary32_certificate := binary32_certificate)
                (binary64_inverse_certificate := binary64_inverse_certificate)
                (binary32_inverse_certificate := binary32_inverse_certificate)
                ty cond a1 a2) v' ∧
            Val.lessdef (Val.select (some b) v1 v2 ty) v'

def sel_builtin_arg_correctStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorProgram) (tprog : CminorSelProgram),
    match_prog cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) prog tprog →
    ∀ (cunit : CminorProgram) (hf : HelperFunctions),
      linkorder cunit prog →
      CompCert4Lean.Backend.SplitLongproof.helper_functions_declared cunit hf →
      ∀ (sp : val) (e e' : Env) (m m' : mem) (a : Cminor.expr)
        (v : val) (c : builtin_arg_constraint),
        env_lessdef e e' → Mem.extends m m' →
        Cminor.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) (Genv.globalenv prog) sp e m a v →
          ∃ v',
            CminorSel.eval_builtin_arg
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e' m'
              (sel_builtin_arg cfg
                (binary64_certificate := binary64_certificate)
                (binary32_certificate := binary32_certificate)
                (binary64_inverse_certificate := binary64_inverse_certificate)
                (binary32_inverse_certificate := binary32_inverse_certificate)
                a c) v' ∧ Val.lessdef v v'

def sel_builtin_args_correctStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorProgram) (tprog : CminorSelProgram),
    match_prog cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) prog tprog →
    ∀ (cunit : CminorProgram) (hf : HelperFunctions),
      linkorder cunit prog →
      CompCert4Lean.Backend.SplitLongproof.helper_functions_declared cunit hf →
      ∀ (sp : val) (e e' : Env) (m m' : mem),
        env_lessdef e e' → Mem.extends m m' →
        ∀ (al : List Cminor.expr) (vl : List val),
          Cminor.eval_exprlist
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) (Genv.globalenv prog) sp e m al vl →
          ∀ cl : List builtin_arg_constraint,
            ∃ vl',
              list_forall2
                (CminorSel.eval_builtin_arg
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) sp e' m')
                (sel_builtin_args cfg
                  (binary64_certificate := binary64_certificate)
                  (binary32_certificate := binary32_certificate)
                  (binary64_inverse_certificate := binary64_inverse_certificate)
                  (binary32_inverse_certificate := binary32_inverse_certificate)
                  al cl) vl' ∧ Val.lessdef_list vl vl'

def sel_builtin_res_correctStatement : Prop :=
  ∀ (oid : Option ident) (v : val) (e : Env) (v' : val) (e' : Env),
    env_lessdef e e' → Val.lessdef v v' →
      env_lessdef (Cminor.set_optvar oid v e)
        (CminorSel.set_builtin_res (sel_builtin_res oid) v' e')

def sel_builtin_default_correctStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorProgram) (tprog : CminorSelProgram),
    match_prog cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) prog tprog →
    ∀ (cunit : CminorProgram) (hf : HelperFunctions),
      linkorder cunit prog →
      CompCert4Lean.Backend.SplitLongproof.helper_functions_declared cunit hf →
      ∀ (optid : Option ident) (ef : external_function) (al : List Cminor.expr)
        (sp : val) (e1 : Env) (m1 : mem) (vl : List val) (t : trace)
        (v : val) (m2 : mem) (e1' : Env) (m1' : mem) (f : CminorSel.function)
        (k : CminorSel.cont),
        Cminor.eval_exprlist
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) (Genv.globalenv prog) sp e1 m1 al vl →
        external_call
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ef (Genv.to_senv (Genv.globalenv prog)) vl m1 t v m2 →
        env_lessdef e1 e1' → Mem.extends m1 m1' →
          ∃ e2' m2',
            plus (CminorSel.step
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi) (Genv.globalenv tprog)
              (CminorSel.State f
                (sel_builtin_default cfg
                  (binary64_certificate := binary64_certificate)
                  (binary32_certificate := binary32_certificate)
                  (binary64_inverse_certificate := binary64_inverse_certificate)
                  (binary32_inverse_certificate := binary32_inverse_certificate)
                  optid ef al) k sp e1' m1') t
              (CminorSel.State f CminorSel.Sskip k sp e2' m2') ∧
            env_lessdef (Cminor.set_optvar optid v e1) e2' ∧ Mem.extends m2 m2'

def sel_builtin_correctStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorProgram) (tprog : CminorSelProgram),
    match_prog cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) prog tprog →
    ∀ (cunit : CminorProgram) (hf : HelperFunctions),
      linkorder cunit prog →
      CompCert4Lean.Backend.SplitLongproof.helper_functions_declared cunit hf →
      ∀ (optid : Option ident) (ef : external_function) (al : List Cminor.expr)
        (sp : val) (e1 : Env) (m1 : mem) (vl : List val) (t : trace)
        (v : val) (m2 : mem) (e1' : Env) (m1' : mem) (f : CminorSel.function)
        (k : CminorSel.cont),
        Cminor.eval_exprlist
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) (Genv.globalenv prog) sp e1 m1 al vl →
        external_call
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi ef (Genv.to_senv (Genv.globalenv prog)) vl m1 t v m2 →
        env_lessdef e1 e1' → Mem.extends m1 m1' →
          ∃ e2' m2',
            plus (CminorSel.step
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi) (Genv.globalenv tprog)
              (CminorSel.State f
                (sel_builtin cfg
                  (binary64_certificate := binary64_certificate)
                  (binary32_certificate := binary32_certificate)
                  (binary64_inverse_certificate := binary64_inverse_certificate)
                  (binary32_inverse_certificate := binary32_inverse_certificate)
                  optid ef al) k sp e1' m1') t
              (CminorSel.State f CminorSel.Sskip k sp e2' m2') ∧
            env_lessdef (Cminor.set_optvar optid v e1) e2' ∧ Mem.extends m2 m2'

def eventually_stepStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorProgram) (f : Cminor.function)
    (s : Cminor.stmt) (k : Cminor.cont) (sp : val) (e : Env) (m : mem)
    (n : Nat) (P : Cminor.state → Prop),
    (∀ (t : trace) (s' : Cminor.state),
      Cminor.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog)
        (Cminor.State f s k sp e m) t s' →
        t = E0 ∧ eventually
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) prog xi n s' P) →
      eventually
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) prog xi (Nat.succ n) (Cminor.State f s k sp e m) P

def classify_stmt_soundStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorProgram) (s : Cminor.stmt),
    match classify_stmt s with
    | SCskip =>
        ∃ n, ∀ (f : Cminor.function) (k : Cminor.cont) (sp : val) (e : Env) (m : mem),
          eventually
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) prog xi n (Cminor.State f s k sp e m)
            (Eq (Cminor.State f Cminor.Sskip k sp e m))
    | SCassign id a =>
        ∃ n, ∀ (f : Cminor.function) (k : Cminor.cont) (sp : val) (e : Env) (m : mem)
          (v : val),
          Cminor.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) (Genv.globalenv prog) sp e m a v →
            eventually
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) prog xi n (Cminor.State f s k sp e m)
              (Eq (Cminor.State f Cminor.Sskip k sp (PTree.set id v e) m))
    | SCother => True

def classify_stmt_wtStatement : Prop :=
  ∀ (env : typenv) (tyret : xtype) (id : ident) (a : Cminor.expr) (s : Cminor.stmt),
    classify_stmt s = SCassign id a → wt_stmt env tyret s → wt_expr env a (env id)

def if_conversion_base_correctStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorProgram) (tprog : CminorSelProgram),
    match_prog cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) prog tprog →
    ∀ (cunit : CminorProgram) (hf : HelperFunctions),
      linkorder cunit prog →
      CompCert4Lean.Backend.SplitLongproof.helper_functions_declared cunit hf →
      ∀ (f : Cminor.function) (env : typenv) (cond : Cminor.expr) (id : ident)
        (ifso ifnot : Cminor.expr) (kont s : CminorSel.stmt) (e : Env)
        (ty : typ) (vb : val) (b : Bool) (sp : val) (m : mem)
        (tf : CminorSel.function) (tk : CminorSel.cont) (e' : Env) (m' : mem),
        if_conversion_base cfg oracle
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (binary64_inverse_certificate := binary64_inverse_certificate)
          (binary32_inverse_certificate := binary32_inverse_certificate)
          (Selection.known_id f) env cond id ifso ifnot kont = some s →
        def_env f e → wt_env env e → env id = ty → wt_expr env ifso ty →
        wt_expr env ifnot ty →
        Cminor.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) (Genv.globalenv prog) sp e m cond vb →
        Val.bool_of_val vb b → env_lessdef e e' → Mem.extends m m' →
          ∃ v1 v2 v',
            Cminor.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) (Genv.globalenv prog) sp e m ifso v1 ∧
            Cminor.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) (Genv.globalenv prog) sp e m ifnot v2 ∧
            Val.lessdef (if b then v1 else v2) v' ∧
            CminorSel.step
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog)
              (CminorSel.State tf s tk sp e' m') E0
              (CminorSel.State tf CminorSel.Sskip tk sp (PTree.set id v' e') m')

def if_conversion_correctStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorProgram) (tprog : CminorSelProgram),
    match_prog cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) prog tprog →
    ∀ (cunit : CminorProgram) (hf : HelperFunctions),
      linkorder cunit prog →
      CompCert4Lean.Backend.SplitLongproof.helper_functions_declared cunit hf →
      ∀ (f : Cminor.function) (env : typenv) (tyret : xtype) (cond : Cminor.expr)
        (ifso ifnot : Cminor.stmt) (kont s : CminorSel.stmt) (vb : val) (b : Bool)
        (k : Cminor.cont) (f' : CminorSel.function) (k' : CminorSel.cont)
        (sp : val) (e : Env) (m : mem) (e' : Env) (m' : mem),
        if_conversion cfg oracle
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (binary64_inverse_certificate := binary64_inverse_certificate)
          (binary32_inverse_certificate := binary32_inverse_certificate)
          (Selection.known_id f) env cond ifso ifnot kont = some s →
        def_env f e → wt_env env e → wt_stmt env tyret ifso → wt_stmt env tyret ifnot →
        Cminor.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) (Genv.globalenv prog) sp e m cond vb →
        Val.bool_of_val vb b → env_lessdef e e' → Mem.extends m m' →
        let s0 := if b then ifso else ifnot
        ∃ n e1 e1',
          CminorSel.step
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog)
            (CminorSel.State f' s k' sp e' m') E0
            (CminorSel.State f' CminorSel.Sskip k' sp e1' m') ∧
          eventually
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) prog xi n (Cminor.State f s0 k sp e m)
            (Eq (Cminor.State f Cminor.Sskip k sp e1 m)) ∧ env_lessdef e1 e1'

def match_states_skipStatement
 : Prop :=
  ∀ (prog : CminorProgram) (cunit : CminorProgram) (hf : HelperFunctions)
    (f : Cminor.function) (f' : CminorSel.function) (k : Cminor.cont)
    (k' : CminorSel.cont) (sp : val) (e : Env) (m : mem) (e' : Env) (m' : mem)
    (env : typenv),
    linkorder cunit prog →
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared cunit hf →
    sel_function cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      (prog_defmap cunit) hf f = .OK f' → type_function f = .OK env →
    match_cont
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      cfg oracle prog cunit hf (Selection.known_id f) env k k' → env_lessdef e e' →
    Mem.extends m m' →
      match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog (Cminor.State f Cminor.Sskip k sp e m)
        (CminorSel.State f' CminorSel.Sskip k' sp e' m')

def call_cont_commutStatement : Prop :=
  ∀ (prog : CminorProgram) (cunit : CminorProgram) (hf : HelperFunctions)
    (ki : KnownIdents) (env : typenv) (k : Cminor.cont) (k' : CminorSel.cont),
    match_cont
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      cfg oracle prog cunit hf ki env k k' →
      match_call_cont
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog (Cminor.call_cont k) (CminorSel.call_cont k')

def match_is_call_contStatement : Prop :=
  ∀ (prog : CminorProgram) (cunit : CminorProgram) (hf : typenv)
    (ki : HelperFunctions) (env : KnownIdents) (k : Cminor.cont) (k' : CminorSel.cont),
    match_cont
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      cfg oracle prog cunit ki env hf k k' → Cminor.is_call_cont k →
      match_call_cont
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog k k' ∧ CminorSel.is_call_cont k'

def classify_stmt_nolabelStatement : Prop :=
  ∀ (s : Cminor.stmt), classify_stmt s ≠ SCother → nolabel s

def if_conversion_base_nolabelStatement : Prop :=
  ∀ (hf : HelperFunctions) (ki : KnownIdents) (env : typenv) (a : Cminor.expr)
    (id : ident) (a1 a2 : Cminor.expr) (kont s : CminorSel.stmt),
    if_conversion_base cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      ki env a id a1 a2 kont = some s → nolabel' s

def if_conversion_nolabelStatement : Prop :=
  ∀ (hf : HelperFunctions) (ki : KnownIdents) (env : typenv) (a : Cminor.expr)
    (s1 s2 : Cminor.stmt) (kont s : CminorSel.stmt),
    if_conversion cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      ki env a s1 s2 kont = some s →
      nolabel s1 ∧ nolabel s2 ∧ nolabel' s

def sel_builtin_nolabelStatement : Prop :=
  ∀ (hf : HelperFunctions) (optid : Option ident) (ef : external_function)
    (args : List Cminor.expr), nolabel'
      (sel_builtin cfg
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        optid ef args)

def find_label_commutStatement : Prop :=
  ∀ (prog : CminorProgram) (cunit : CminorProgram) (hf : HelperFunctions)
    (ki : KnownIdents) (env : typenv) (lbl : ident) (s : Cminor.stmt)
    (kont : CminorSel.stmt) (k : Cminor.cont) (s' : CminorSel.stmt) (k' : CminorSel.cont),
    match_cont
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      cfg oracle prog cunit hf ki env k k' →
    sel_stmt cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      (prog_defmap cunit) ki env s kont = .OK s' →
    match Cminor.find_label lbl s k with
    | some (s1, k1) =>
        match CminorSel.find_label lbl s' k' with
        | some (s1', k1') =>
            ∃ kont1, sel_stmt cfg oracle
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate)
              (binary64_inverse_certificate := binary64_inverse_certificate)
              (binary32_inverse_certificate := binary32_inverse_certificate)
              (prog_defmap cunit) ki env s1 kont1 = .OK s1' ∧
              match_cont
                (binary64_certificate := binary64_certificate)
                (binary32_certificate := binary32_certificate)
                (binary64_inverse_certificate := binary64_inverse_certificate)
                (binary32_inverse_certificate := binary32_inverse_certificate)
                cfg oracle prog cunit hf ki env k1 k1'
        | none => False
    | none =>
        match CminorSel.find_label lbl s' k' with
        | some _ => False
        | none => True

def sel_step_correctStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorProgram) (tprog : CminorSelProgram),
    match_prog cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) prog tprog →
    ∀ (s1 : Cminor.state) (t : trace) (s2 : Cminor.state),
      Cminor.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) s1 t s2 →
      ∀ t1 : CminorSel.state, match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog s1 t1 → wt_state s1 →
        (∃ t2, plus (CminorSel.step
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi) (Genv.globalenv tprog) t1 t t2 ∧
          match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog s2 t2) ∨
        (measure s2 < measure s1 ∧ t = E0 ∧ match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog s2 t1) ∨
        (∃ t2 n, CminorSel.step
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi (Genv.globalenv tprog) t1 t t2 ∧
          eventually
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) prog xi n s2 (fun s3 => match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog s3 t2))

def sel_initial_statesStatement
 : Prop :=
  ∀ (prog : CminorProgram) (tprog : CminorSelProgram),
    match_prog cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) prog tprog →
      ∀ s, Cminor.initial_state prog s →
        ∃ r, CminorSel.initial_state tprog r ∧ match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog s r

def sel_final_statesStatement
 : Prop :=
  ∀ (prog : CminorProgram) (s : Cminor.state) (r : CminorSel.state) (v : int),
    match_states
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg oracle prog s r → Cminor.final_state s v → CminorSel.final_state r v

def transf_program_correctStatement
 : Prop :=
  ∀ (xi : ExternalCalls) (prog : CminorProgram) (tprog : CminorSelProgram),
    match_prog cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) prog tprog →
      forward_simulation (Cminor.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi prog) (CminorSel.semantics
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi tprog)

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Lib.Maps
open CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String

theorem lookup_helper_correct_1 :
    CompCert4Lean.Backend.Selectionproof.lookup_helper_correct_1Statement := by
  intro globs name sg id hlookup
  change positive at id
  let P := fun (m : PTree.t CompCert4Lean.Backend.Selection.globdef)
      (result : Option positive) =>
    result = some id →
      PTree.get id m = some (.Gfun (.External (.EF_runtime name sg)))
  have hfold : P globs
      (PTree.fold (CompCert4Lean.Backend.Selection.lookup_helper_aux name sg)
        globs none) := by
    apply PTree_Properties.fold_rec_proof
    · intro m m' a heq hP ha
      rw [← heq id]
      exact hP ha
    · intro ha
      cases ha
    · intro m a k v hk hfinal hP
      unfold P at hP ⊢
      have hpreserve : PTree.get id m =
          some (.Gfun (.External (.EF_runtime name sg))) →
          PTree.get id (PTree.set k v m) =
            some (.Gfun (.External (.EF_runtime name sg))) := by
        intro hm
        rw [PTree.getSet_equation]
        split
        · rename_i hik
          subst k
          rw [hk] at hm
          contradiction
        · exact hm
      cases v with
      | Gvar v =>
          change a = some id → _
          intro ha
          exact hpreserve (hP ha)
      | Gfun f =>
        cases f with
        | Internal f =>
            change a = some id → _
            intro ha
            exact hpreserve (hP ha)
        | External ef =>
          cases ef with
          | EF_runtime name' sg' =>
              change
                (if (match string_dec name name' with
                    | .left _ => true
                    | .right _ => false) &&
                    (match signature_eq sg sg' with
                    | .left _ => true
                    | .right _ => false)
                  then some k else a) = some id → _
              cases hname : string_dec name name' with
              | left hname =>
                cases hsg : signature_eq sg sg' with
                | left hsg =>
                  subst name'
                  subst sg'
                  simp
                  intro hkid
                  subst k
                  simpa using
                    (PTree.getSet_equation
                      (A := CompCert4Lean.Backend.Selection.globdef) id id
                      (.Gfun (.External (.EF_runtime name sg))) m)
                | right hsg =>
                    simp
                    intro ha
                    exact hpreserve (hP ha)
              | right hname =>
                  simp
                  intro ha
                  exact hpreserve (hP ha)
          | EF_external name' sg' =>
              change a = some id → _
              intro ha
              exact hpreserve (hP ha)
          | EF_builtin name' sg' =>
              change a = some id → _
              intro ha
              exact hpreserve (hP ha)
          | EF_vload chunk =>
              change a = some id → _
              intro ha
              exact hpreserve (hP ha)
          | EF_vstore chunk =>
              change a = some id → _
              intro ha
              exact hpreserve (hP ha)
          | EF_malloc =>
              change a = some id → _
              intro ha
              exact hpreserve (hP ha)
          | EF_free =>
              change a = some id → _
              intro ha
              exact hpreserve (hP ha)
          | EF_memcpy size alignment =>
              change a = some id → _
              intro ha
              exact hpreserve (hP ha)
          | EF_annot kind text targs =>
              change a = some id → _
              intro ha
              exact hpreserve (hP ha)
          | EF_annot_val kind text targ =>
              change a = some id → _
              intro ha
              exact hpreserve (hP ha)
          | EF_inline_asm text sg clobbers =>
              change a = some id → _
              intro ha
              exact hpreserve (hP ha)
          | EF_debug kind text targs =>
              change a = some id → _
              intro ha
              exact hpreserve (hP ha)
  unfold CompCert4Lean.Backend.Selection.lookup_helper at hlookup
  cases hresult : PTree.fold
      (CompCert4Lean.Backend.Selection.lookup_helper_aux name sg) globs none with
  | none =>
      simp [hresult] at hlookup
  | some result =>
      change positive at result
      have hid : result = id := by
        have hEq : CompCert4Lean.Common.Errors.res.OK result =
            CompCert4Lean.Common.Errors.res.OK id := by
          rw [hresult] at hlookup
          exact hlookup
        cases hEq
        rfl
      subst result
      exact hfold hresult

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Lib.Maps

theorem record_globdefs_sound :
    CompCert4Lean.Backend.Selectionproof.record_globdefs_soundStatement := by
  intro dm id gd hget
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive at id
  unfold CompCert4Lean.Backend.Selection.record_globdefs at hget
  let P := fun (m a : PTree.t CompCert4Lean.Backend.Selection.globdef) =>
    PTree.get id a = some gd → PTree.get id m = some gd
  have hfold : P dm
      (PTree.fold
        (fun m id gd =>
          if CompCert4Lean.Backend.Selection.globdef_of_interest gd then
            PTree.set id gd m
          else m)
        dm (PTree.empty _)) := by
    apply PTree_Properties.fold_rec_proof
    · intro m m' a heq hP ha
      rw [← heq id]
      exact hP ha
    · intro ha
      exact ha
    · intro m a k v hk hfinal hP
      unfold P at hP ⊢
      cases hv : CompCert4Lean.Backend.Selection.globdef_of_interest v <;>
        simp [hv] at *
      · intro ha
        have hm := hP ha
        rw [PTree.getSet_equation]
        split
        · rename_i hid
          subst k
          rw [hk] at hm
          contradiction
        · exact hm
      · intro ha
        have hcase (x : PTree.tree CompCert4Lean.Backend.Selection.globdef) :
            PTree.get id (PTree.set k v x) =
              if id = k then some v else PTree.get id x :=
          PTree.getSet_equation id k v x
        rw [hcase a] at ha
        rw [hcase m]
        by_cases hik : id = k
        · simp [hik] at ha ⊢
          exact ha
        · simp [hik] at ha ⊢
          exact hP ha
  exact hfold hget

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

theorem lookup_helper_correct :
    CompCert4Lean.Backend.Selectionproof.lookup_helper_correctStatement := by
  intro p name sg id hlookup
  unfold CompCert4Lean.Backend.SplitLongproof.helper_declared
  apply record_globdefs_sound
  apply lookup_helper_correct_1
  exact hlookup

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

theorem get_helpers_correct :
    CompCert4Lean.Backend.Selectionproof.get_helpers_correctStatement := by
  intro p hf h
  unfold CompCert4Lean.Backend.Selection.get_helpers at h
  dsimp at h
  repeat split at h <;> try contradiction
  cases h
  repeat' constructor
  all_goals apply lookup_helper_correct
  all_goals assumption

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

private theorem helper_declared_linkorder
    (p p' : CompCert4Lean.Backend.Cminor.program)
    (id : CompCert4Lean.Common.AST.ident)
    (name : CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string)
    (sg : CompCert4Lean.Common.AST.signature)
    (hdecl : CompCert4Lean.Backend.SplitLongproof.helper_declared p id name sg)
    (hlink : CompCert4Lean.Common.Linking.linkorder p p') :
    CompCert4Lean.Backend.SplitLongproof.helper_declared p' id name sg := by
  unfold CompCert4Lean.Backend.SplitLongproof.helper_declared at hdecl ⊢
  rcases CompCert4Lean.Common.Linking.prog_defmap_linkorder_proof
      p p' id (.Gfun (.External (.EF_runtime name sg))) hlink hdecl with
    ⟨gd, hget, hgd⟩
  cases hgd with
  | linkorder_def_fun _ _ hfd =>
      cases hfd with
      | linkorder_fundef_refl _ => exact hget

theorem helper_functions_declared_linkorder :
    CompCert4Lean.Backend.Selectionproof.helper_functions_declared_linkorderStatement := by
  intro p p' hf hdecl hlink
  unfold CompCert4Lean.Backend.SplitLongproof.helper_functions_declared at hdecl ⊢
  rcases hdecl with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  exact ⟨helper_declared_linkorder p p' _ _ _ h1 hlink,
    helper_declared_linkorder p p' _ _ _ h2 hlink,
    helper_declared_linkorder p p' _ _ _ h3 hlink,
    helper_declared_linkorder p p' _ _ _ h4 hlink,
    helper_declared_linkorder p p' _ _ _ h5 hlink,
    helper_declared_linkorder p p' _ _ _ h6 hlink,
    helper_declared_linkorder p p' _ _ _ h7 hlink,
    helper_declared_linkorder p p' _ _ _ h8 hlink,
    helper_declared_linkorder p p' _ _ _ h9 hlink,
    helper_declared_linkorder p p' _ _ _ h10 hlink,
    helper_declared_linkorder p p' _ _ _ h11 hlink,
    helper_declared_linkorder p p' _ _ _ h12 hlink,
    helper_declared_linkorder p p' _ _ _ h13 hlink,
    helper_declared_linkorder p p' _ _ _ h14 hlink,
    helper_declared_linkorder p p' _ _ _ h15 hlink⟩

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

private theorem list_forall2_mem_left
    {A B : Type} {P : A → B → Prop} :
    ∀ {xs : List A} {ys : List B},
      CompCert4Lean.Lib.Coqlib.list_forall2 P xs ys → ∀ {x : A}, x ∈ xs →
        ∃ y : B, y ∈ ys ∧ P x y := by
  intro xs ys h
  induction h with
  | nil =>
      intro x hx
      cases hx
  | cons a b hp ht ih =>
      intro x hx
      cases hx with
      | head as =>
          exact ⟨b, by simp, hp⟩
      | tail b' hx' =>
          rcases ih hx' with ⟨y, hy, hpy⟩
          exact ⟨y, by simp [hy], hpy⟩

variable [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
variable [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
variable [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
variable [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]

theorem wt_prog
    (cfg : CompilerConfig) (oracle : SelectionOracle) :
    wt_progStatement cfg oracle := by
  intro prog tprog hmatch
  unfold CompCert4Lean.Backend.Cminortyping.wt_program
  intro i f hmem
  unfold match_prog CompCert4Lean.Common.Linking.match_program at hmatch
  rcases hmatch with ⟨hdefs, _, _⟩
  rcases list_forall2_mem_left hdefs hmem with ⟨ig', hi', hgd⟩
  rcases ig' with ⟨i', gd'⟩
  simp only [CompCert4Lean.Common.Linking.match_ident_globdef] at hgd
  rcases hgd with ⟨hid, hglob⟩
  cases f with
  | Internal fn =>
      cases gd' with
      | Gfun tfn =>
          cases hglob with
          | match_globdef_fun ctx' f1 f2 hlink hfun =>
              unfold match_fundef at hfun
              rcases hfun with ⟨hf, hhelpers, hsel⟩
              cases ht : CompCert4Lean.Backend.Cminortyping.type_function fn with
              | Error msg =>
                  simp [CompCert4Lean.Backend.Selection.sel_fundef,
                    CompCert4Lean.Common.AST.transf_partial_fundef,
                    CompCert4Lean.Backend.Selection.sel_function, ht] at hsel
              | OK env =>
                  apply CompCert4Lean.Backend.Cminortyping.wt_fundef_internal
                  exact CompCert4Lean.Backend.Cminortyping.type_function_sound fn env ht
      | Gvar v =>
          cases hglob
  | External ef =>
      exact CompCert4Lean.Backend.Cminortyping.wt_fundef_external ef

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

variable [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
variable [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
variable [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
variable [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
variable (cfg : CompilerConfig) (oracle : SelectionOracle)

private theorem selection_symbol_add_global
    {F1 F2 : Type} (ge1 : Genv.t F1 Unit) (ge2 : Genv.t F2 Unit) (id : ident)
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

private theorem selection_symbol_add_globals
    (xs : List (ident × Globdef))
    (ys : List (ident × CompCert4Lean.Common.AST.globdef CminorSelFundef Unit))
    (hxy : list_forall2 (fun a b => a.1 = b.1) xs ys)
    (ge1 : Genv.t CminorFundef Unit)
    (ge2 : Genv.t CminorSelFundef Unit)
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
        exact selection_symbol_add_global ge1 ge2 aid hm hn id'
      · exact congrArg PArith.BinPos.Pos.succ hn

private theorem selection_match_genvs_add_global
    (R : Globdef → CompCert4Lean.Common.AST.globdef CminorSelFundef Unit → Prop)
    (ge1 : Genv.t CminorFundef Unit)
    (ge2 : Genv.t CminorSelFundef Unit) (id : ident)
    (g1 : Globdef)
    (g2 : CompCert4Lean.Common.AST.globdef CminorSelFundef Unit)
    (hm : Genv.match_genvs R ge1 ge2) (hg : R g1 g2) :
    Genv.match_genvs R (Genv.add_global ge1 (id, g1))
      (Genv.add_global ge2 (id, g2)) := by
  constructor
  · exact congrArg PArith.BinPos.Pos.succ hm.mge_next
  · exact selection_symbol_add_global ge1 ge2 id hm.mge_symb hm.mge_next
  · intro b
    change option_rel R
      (PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs))
      (PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs))
    have h1 := @PTree.getSet_equation Globdef
      b ge1.genv_next g1 ge1.genv_defs
    have h2 := @PTree.getSet_equation
      (CompCert4Lean.Common.AST.globdef CminorSelFundef Unit)
      b ge2.genv_next g2 ge2.genv_defs
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

private theorem selection_match_genvs_add_globals
    (R : Globdef → CompCert4Lean.Common.AST.globdef CminorSelFundef Unit → Prop)
    (xs : List (ident × Globdef))
    (ys : List (ident × CompCert4Lean.Common.AST.globdef CminorSelFundef Unit))
    (hxy : list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) xs ys)
    (ge1 : Genv.t CminorFundef Unit)
    (ge2 : Genv.t CminorSelFundef Unit)
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
      simpa using (selection_match_genvs_add_global R ge1 ge2 aid ag bg hm hab)

private theorem selection_globalenvs_match
    (prog : CminorProgram) (tprog : CminorSelProgram)
    (hm : match_prog cfg oracle prog tprog) :
    Genv.match_genvs
      (@match_globdef CminorProgram CminorFundef Unit CminorSelFundef Unit
        cminorProgramLinker
        (fun (cunit : CminorProgram) f tf =>
          match_fundef cfg oracle cunit f tf)
        (fun x y : Unit => x = y) prog)
      (Genv.globalenv prog) (Genv.globalenv tprog) := by
  let R : Globdef → CompCert4Lean.Common.AST.globdef CminorSelFundef Unit → Prop :=
    @match_globdef CminorProgram CminorFundef Unit CminorSelFundef Unit
      cminorProgramLinker
      (fun (cunit : CminorProgram) f tf => match_fundef cfg oracle cunit f tf)
      (fun x y : Unit => x = y) prog
  unfold match_prog match_program match_program_gen at hm
  have hempty : Genv.match_genvs R
      (Genv.empty_genv CminorFundef Unit prog.prog_public)
      (Genv.empty_genv CminorSelFundef Unit tprog.prog_public) := by
    constructor
    · rfl
    · intro id'
      rfl
    · intro b
      exact option_rel.none R
  have hlist : list_forall2
      (fun a b => a.1 = b.1 ∧ R a.2 b.2)
      prog.prog_defs tprog.prog_defs := by
    have hlist_of : ∀ (xs : List (ident × Globdef))
        (ys : List (ident × CompCert4Lean.Common.AST.globdef CminorSelFundef Unit)),
        list_forall2
          (@match_ident_globdef CminorProgram CminorFundef Unit CminorSelFundef Unit
            cminorProgramLinker
            (fun (cunit : CminorProgram) f tf => match_fundef cfg oracle cunit f tf)
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
  exact selection_match_genvs_add_globals R prog.prog_defs tprog.prog_defs
    hlist _ _ hempty

private theorem selection_add_globals_public
    {F : Type} (ge : Genv.t F Unit)
    (gl : List (ident × CompCert4Lean.Common.AST.globdef F Unit)) :
    (Genv.add_globals ge gl).genv_public = ge.genv_public := by
  induction gl generalizing ge with
  | nil => rfl
  | cons idg gl ih =>
      simp only [Genv.add_globals, List.foldl_cons]
      simpa [Genv.add_globals, Genv.add_global] using ih (Genv.add_global ge idg)

private theorem selection_symbols_preserved
    (prog : CminorProgram) (tprog : CminorSelProgram)
    (hm : match_prog cfg oracle prog tprog) (id : ident) :
    Genv.find_symbol (Genv.globalenv tprog) id =
      Genv.find_symbol (Genv.globalenv prog) id := by
  have hg := selection_globalenvs_match cfg oracle prog tprog hm
  simpa [Genv.find_symbol] using hg.mge_symb id

theorem senv_preserved : senv_preservedStatement cfg oracle := by
  intro prog tprog hm
  unfold Senv.equiv
  constructor
  · intro id
    exact selection_symbols_preserved cfg oracle prog tprog hm id
  constructor
  · intro id
    change Genv.public_symbol (Genv.globalenv tprog) id =
      Genv.public_symbol (Genv.globalenv prog) id
    have ht : (Genv.globalenv tprog).genv_public = tprog.prog_public := by
      unfold Genv.globalenv
      exact selection_add_globals_public _ _
    have hp : (Genv.globalenv prog).genv_public = prog.prog_public := by
      unfold Genv.globalenv
      exact selection_add_globals_public _ _
    unfold Genv.public_symbol
    rw [selection_symbols_preserved cfg oracle prog tprog hm id]
    unfold match_prog match_program match_program_gen at hm
    rw [ht, hp, hm.2.2]
  · intro b
    change Genv.block_is_volatile (Genv.globalenv tprog) b =
      Genv.block_is_volatile (Genv.globalenv prog) b
    have hg := selection_globalenvs_match cfg oracle prog tprog hm
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

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Integers

variable [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
variable [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
variable [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
variable [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
variable (cfg : CompilerConfig) (oracle : SelectionOracle)

theorem functions_translated : functions_translatedStatement cfg oracle := by
  intro prog tprog hm v v' f hfind hld
  cases v with
  | Vundef => simp [Genv.find_funct] at hfind
  | Vint n => simp [Genv.find_funct] at hfind
  | Vfloat n => simp [Genv.find_funct] at hfind
  | Vlong n => simp [Genv.find_funct] at hfind
  | Vsingle n => simp [Genv.find_funct] at hfind
  | Vptr b ofs =>
      cases hld with
      | lessdef_refl _ =>
          change (if Ptrofs.eq ofs Ptrofs.zero = true then
            Genv.find_funct_ptr (Genv.globalenv prog) b else none) = some f at hfind
          cases heq : Ptrofs.eq ofs Ptrofs.zero with
          | false => simp [heq] at hfind
          | true =>
              simp only [heq] at hfind
              have hge := selection_globalenvs_match cfg oracle prog tprog hm
              unfold Genv.find_funct_ptr at hfind
              have hsrc : Genv.find_def (Genv.globalenv prog) b = some (.Gfun f) := by
                cases hfd : Genv.find_def (Genv.globalenv prog) b with
                | none => simp [hfd] at hfind
                | some gd =>
                    cases gd with
                    | Gfun f0 =>
                        simp [hfd] at hfind
                        subst f0
                        rfl
                    | Gvar gv => simp [hfd] at hfind
              cases ht : Genv.find_def (Genv.globalenv tprog) b with
              | none =>
                  have hdefs := hge.mge_defs b
                  change CompCert4Lean.Lib.Coqlib.option_rel _
                    (Genv.find_def (Genv.globalenv prog) b)
                    (Genv.find_def (Genv.globalenv tprog) b) at hdefs
                  rw [hsrc, ht] at hdefs
                  cases hdefs
              | some gd2 =>
                  have hdefs := hge.mge_defs b
                  change CompCert4Lean.Lib.Coqlib.option_rel _
                    (Genv.find_def (Genv.globalenv prog) b)
                    (Genv.find_def (Genv.globalenv tprog) b) at hdefs
                  rw [hsrc, ht] at hdefs
                  cases hdefs with
                  | some g1 g2 hrel =>
                      cases hrel with
                      | match_globdef_fun cu f1 f2 horder hmatch =>
                          refine ⟨cu, f2, ?_, hmatch, horder⟩
                          simp [Genv.find_funct, Genv.find_funct_ptr, heq, ht]

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

variable [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
variable [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
variable [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
variable [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
variable (cfg : CompilerConfig) (oracle : SelectionOracle)

theorem sig_function_translated : sig_function_translatedStatement cfg oracle := by
  intro cu f tf hmatch
  unfold match_fundef at hmatch
  rcases hmatch with ⟨hf, hhelpers, hsel⟩
  have sel_function_sig : ∀ (fn : Cminor.function) (tf' : CminorSel.function),
      CompCert4Lean.Backend.Selection.sel_function cfg oracle
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        (CompCert4Lean.Common.AST.prog_defmap cu) hf fn = .OK tf' →
      tf'.fn_sig = fn.fn_sig := by
    intro fn tf' htrans
    unfold CompCert4Lean.Backend.Selection.sel_function at htrans
    cases ht : CompCert4Lean.Backend.Cminortyping.type_function fn with
    | Error msg => simp [ht] at htrans
    | OK env =>
        cases hs : CompCert4Lean.Backend.Selection.sel_stmt cfg oracle
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            (binary64_inverse_certificate := binary64_inverse_certificate)
            (binary32_inverse_certificate := binary32_inverse_certificate)
            (CompCert4Lean.Common.AST.prog_defmap cu)
            (CompCert4Lean.Backend.Selection.known_id fn) env fn.fn_body .Sskip with
        | Error msg => simp [ht, hs] at htrans
        | OK body' =>
            simp [ht, hs] at htrans
            cases htrans
            rfl
  cases f with
  | Internal fn =>
      unfold CompCert4Lean.Backend.Selection.sel_fundef
        CompCert4Lean.Common.AST.transf_partial_fundef at hsel
      cases htrans : CompCert4Lean.Backend.Selection.sel_function cfg oracle
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (binary64_inverse_certificate := binary64_inverse_certificate)
          (binary32_inverse_certificate := binary32_inverse_certificate)
          (CompCert4Lean.Common.AST.prog_defmap cu) hf fn with
      | Error msg => simp [htrans] at hsel
      | OK tf' =>
          simp [htrans] at hsel
          cases hsel
          exact sel_function_sig fn tf' htrans
  | External ef =>
      simp [CompCert4Lean.Backend.Selection.sel_fundef,
        CompCert4Lean.Common.AST.transf_partial_fundef] at hsel
      cases hsel
      rfl

end CompCert4Lean.Backend.Selectionproof


namespace CompCert4Lean.Backend.Selectionproof

theorem stackspace_function_translated
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)] :
    ∀ (cfg : CompilerConfig) (oracle : SelectionOracle),
      stackspace_function_translatedStatement
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate) cfg oracle := by
  intro cfg oracle dm hf f tf h
  unfold CompCert4Lean.Backend.Selection.sel_function at h
  cases ht : CompCert4Lean.Backend.Cminortyping.type_function f with
  | Error msg => simp [ht] at h
  | OK env =>
      cases hs : CompCert4Lean.Backend.Selection.sel_stmt cfg oracle
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (binary64_inverse_certificate := binary64_inverse_certificate)
          (binary32_inverse_certificate := binary32_inverse_certificate)
          dm (CompCert4Lean.Backend.Selection.known_id f) env f.fn_body .Sskip with
      | Error msg => simp [ht, hs] at h
      | OK body' =>
          simp [ht, hs] at h
          cases h
          rfl

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

private theorem helper_declared_preserved
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (oracle : SelectionOracle)
    (prog : CminorProgram) (tprog : CminorSelProgram)
    (hm : match_prog cfg oracle prog tprog)
    (id : CompCert4Lean.Common.AST.ident)
    (name : RocqString) (sg : CompCert4Lean.Common.AST.signature)
    (hdecl : CompCert4Lean.Backend.SplitLongproof.helper_declared prog id name sg) :
    CompCert4Lean.Backend.SplitLongproof.helper_declared tprog id name sg := by
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive at id
  unfold CompCert4Lean.Backend.SplitLongproof.helper_declared at hdecl ⊢
  have hrel := @CompCert4Lean.Common.Linking.match_program_defmap
    CminorProgram CminorFundef Unit CminorSelFundef Unit
    cminorProgramLinker
    (fun (cunit : CminorProgram) f tf => match_fundef cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) cunit f tf)
    (fun x y : Unit => x = y) prog prog tprog hm id
  generalize hsrc : CompCert4Lean.Lib.Maps.PTree.get id
      (CompCert4Lean.Common.AST.prog_defmap prog) = src at hrel
  generalize htgt : CompCert4Lean.Lib.Maps.PTree.get id
      (CompCert4Lean.Common.AST.prog_defmap tprog) = tgt at hrel
  cases hrel with
  | none =>
      have hcontra := hsrc.symm.trans hdecl
      cases hcontra
  | some g1 g2 hglob =>
      have hg1 : g1 = .Gfun (.External (.EF_runtime name sg)) := by
        apply Option.some.inj
        exact hsrc.symm.trans hdecl
      subst g1
      cases hglob with
      | match_globdef_fun ctx' f1 f2 horder hfun =>
          unfold match_fundef at hfun
          rcases hfun with ⟨hf, hhelpers, hsel⟩
          simp [CompCert4Lean.Backend.Selection.sel_fundef,
            CompCert4Lean.Common.AST.transf_partial_fundef] at hsel
          cases hsel
          exact htgt

theorem helper_functions_preserved
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)] :
    ∀ (cfg : CompilerConfig) (oracle : SelectionOracle),
      helper_functions_preservedStatement
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate) cfg oracle := by
  intro cfg oracle prog tprog hm hf hdecl
  unfold CompCert4Lean.Backend.SplitLongproof.helper_functions_declared at hdecl ⊢
  rcases hdecl with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  exact ⟨helper_declared_preserved cfg oracle prog tprog hm _ _ _ h1,
    helper_declared_preserved cfg oracle prog tprog hm _ _ _ h2,
    helper_declared_preserved cfg oracle prog tprog hm _ _ _ h3,
    helper_declared_preserved cfg oracle prog tprog hm _ _ _ h4,
    helper_declared_preserved cfg oracle prog tprog hm _ _ _ h5,
    helper_declared_preserved cfg oracle prog tprog hm _ _ _ h6,
    helper_declared_preserved cfg oracle prog tprog hm _ _ _ h7,
    helper_declared_preserved cfg oracle prog tprog hm _ _ _ h8,
    helper_declared_preserved cfg oracle prog tprog hm _ _ _ h9,
    helper_declared_preserved cfg oracle prog tprog hm _ _ _ h10,
    helper_declared_preserved cfg oracle prog tprog hm _ _ _ h11,
    helper_declared_preserved cfg oracle prog tprog hm _ _ _ h12,
    helper_declared_preserved cfg oracle prog tprog hm _ _ _ h13,
    helper_declared_preserved cfg oracle prog tprog hm _ _ _ h14,
    helper_declared_preserved cfg oracle prog tprog hm _ _ _ h15⟩

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.Selection
open CompCert4Lean.X86.Op
open CompCert4Lean.Lib.Integers

theorem eval_condexpr_of_expr
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_condexpr_of_exprStatement := by
  intro xi tprog sp e m a le v b
  let P : CminorSel.expr → CminorSel.condexpr → Prop := fun a ce =>
    ∀ (le : CminorSel.letenv) (v : val) (b : Bool),
      CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv tprog) sp e m le a v →
      Val.bool_of_val v b →
      CminorSel.eval_condexpr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv tprog) sp e m le ce b
  have hP : ∀ a : CminorSel.expr, P a (condexpr_of_expr a) := by
    apply CompCert4Lean.Backend.Selection.condexpr_of_expr_ind
    · intro ex c el hex
      subst ex
      intro le' v' b' hev hbv
      cases hev with
      | eval_Eop =>
          rename_i vl hargs hop
          apply eval_condexpr.condition le' c el vl b'
          · exact hargs
          · have hopt : eval_condition c vl m = some b' := by
              change some (Val.of_optbool (eval_condition c vl m)) = some v' at hop
              have hv : Val.of_optbool (eval_condition c vl m) = v' := by
                exact Option.some.inj hop
              have hbv' : Val.bool_of_val (Val.of_optbool (eval_condition c vl m)) b' := by
                simpa [hv] using hbv
              exact Val.bool_of_val_of_optbool _ _ hbv'
            exact hopt
    · intro ex ca eb ec hex ihb ihc
      subst ex
      intro le' v' b' hev hbv
      cases hev with
      | eval_Econdition =>
          rename_i va hcond hbranch
          apply eval_condexpr.eval_CEcondition le' ca (condexpr_of_expr eb)
            (condexpr_of_expr ec) va b'
          · exact hcond
          · cases va with
            | false => exact ihc le' v' b' (by simpa using hbranch) hbv
            | true => exact ihb le' v' b' (by simpa using hbranch) hbv
    · intro ex ea eb hex ihe
      subst ex
      intro le' v' b' hev hbv
      cases hev with
      | eval_Elet =>
          rename_i v1 hbound hbody
          apply eval_condexpr.eval_CElet le' ea (condexpr_of_expr eb) v1 b'
          · exact hbound
          · exact ihe (v1 :: le') v' b' hbody hbv
    · intro ex x hex hnot
      subst ex
      intro le' v' b' hev hbv
      cases hbv with
      | bool_of_val_int n =>
          apply eval_condexpr.condition le' (.Ccompuimm .Cne Int.zero)
            (.Econs x .Enil) [Vint n] (!(Int.eq n Int.zero))
          · exact eval_exprlist.cons le' x .Enil (Vint n) [] hev (eval_exprlist.nil le')
          · rfl
  exact hP a le v b

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.Selection
open CompCert4Lean.X86.Op
open CompCert4Lean.Lib.Integers

theorem eval_condition_of_expr
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_condition_of_exprStatement := by
  intro xi tprog sp e m a le v b
  let P : CminorSel.expr -> Prod condition CminorSel.exprlist -> Prop := fun a c =>
    forall le' v' b',
      CminorSel.eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv tprog) sp e m le' a v' ->
      Val.bool_of_val v' b' ->
      exists vl,
        CminorSel.eval_exprlist
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          xi (Genv.globalenv tprog) sp e m le' c.2 vl /\
        eval_condition c.1 vl m = some b'
  have hP : forall a : CminorSel.expr, P a (condition_of_expr a) := by
    apply CompCert4Lean.Backend.Selection.condition_of_expr_ind
    · intro ex c el hex
      subst ex
      intro le' v' b' hev hbv
      cases hev with
      | eval_Eop =>
          rename_i vl hargs hop
          refine Exists.intro vl (And.intro hargs ?_)
          change some (Val.of_optbool (eval_condition c vl m)) = some v' at hop
          have hv : Val.of_optbool (eval_condition c vl m) = v' :=
            Option.some.inj hop
          have hbv' : Val.bool_of_val (Val.of_optbool (eval_condition c vl m)) b' := by
            simpa [hv] using hbv
          exact Val.bool_of_val_of_optbool _ _ hbv'
    · intro ex x hex hnot
      subst ex
      intro le' v' b' hev hbv
      cases hbv with
      | bool_of_val_int n =>
          refine Exists.intro [Vint n] (And.intro ?_ ?_)
          · exact CminorSel.eval_exprlist.cons le' x .Enil (Vint n) [] hev
              (CminorSel.eval_exprlist.nil le')
          · rfl
  exact hP a le v b

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.Selection
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

open Lean Elab Tactic Meta

private def selectionPrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem selection_wordcore_add_val {bits : Nat}
    (x y : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    (CompCert4Lean.Lib.Integers.WordCore.add x y).val =
      (x.val + y.val) % (2 ^ bits) := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let yF := (lctx.findFromUserName? `y).get!
    let e ← mkAppM
      (selectionPrivateName "CompCert4Lean.Lib.Integers.WordCore.add_val")
      #[mkFVar xF.fvarId, mkFVar yF.fvarId]
    closeMainGoal Name.anonymous e

private theorem selection_wordcore_zero_val (bits : Nat) :
    (CompCert4Lean.Lib.Integers.WordCore.zero bits).val = 0 := by
  unfold CompCert4Lean.Lib.Integers.WordCore.zero
  run_tac
    let lctx ← getLCtx
    let bF := (lctx.findFromUserName? `bits).get!
    let e ← mkAppM
      (selectionPrivateName "CompCert4Lean.Lib.Integers.WordCore.val_repr_residue")
      #[mkFVar bF.fvarId,
        mkConst ``CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0]
    closeMainGoal Name.anonymous e

private theorem selection_wordcore_val_lt {bits : Nat}
    (x : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    x.val < 2 ^ bits := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let e ← mkAppM
      (selectionPrivateName "CompCert4Lean.Lib.Integers.WordCore.val_lt")
      #[mkFVar xF.fvarId]
    closeMainGoal Name.anonymous e

private theorem selection_ptrofs_add_zero
    (ofs : CompCert4Lean.Lib.Integers.Ptrofs.int) :
    CompCert4Lean.Lib.Integers.Ptrofs.add ofs
      (CompCert4Lean.Lib.Integers.Ptrofs.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0)) = ofs := by
  change CompCert4Lean.Lib.Integers.WordCore.add ofs
    (CompCert4Lean.Lib.Integers.WordCore.zero
      CompCert4Lean.Lib.Integers.Ptrofs.wordsize) = ofs
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [selection_wordcore_add_val, selection_wordcore_zero_val, Nat.add_zero]
  exact Nat.mod_eq_of_lt (selection_wordcore_val_lt ofs)

theorem eval_store
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_storeStatement := by
  intro xi tprog sp e m chunk a1 a2 v1 v2 f k m' h1 h2 hstore
  cases v1 with
  | Vundef => simp [Mem.storev] at hstore
  | Vint n => simp [Mem.storev] at hstore
  | Vlong n => simp [Mem.storev] at hstore
  | Vfloat f => simp [Mem.storev] at hstore
  | Vsingle f => simp [Mem.storev] at hstore
  | Vptr b ofs =>
      cases hcase : addressing_match a1 with
      | addressing_case1 addr args =>
          have hadd :
              CompCert4Lean.X86.SelectOp.addressing chunk (Eop (.Olea addr) args) =
                (.Aindexed (zOfNat 0), Econs (Eop (.Olea addr) args) Enil) := by
            simp [CompCert4Lean.X86.SelectOp.addressing, addressing_match,
              CompCert4Lean.X86_64.Archi.ptr64]
            rfl
          have haddr :
              eval_addressing (Genv.globalenv tprog) sp (.Aindexed (zOfNat 0))
                [Vptr b ofs] = some (Vptr b ofs) := by
            simp [eval_addressing, eval_addressing64,
              CompCert4Lean.X86_64.Archi.ptr64, Val.addl,
              CompCert4Lean.Lib.Integers.Ptrofs.of_int64,
              CompCert4Lean.Lib.Integers.Int64.repr]
            rw [show CompCert4Lean.Lib.Integers.Ptrofs.repr
                (CompCert4Lean.Lib.Integers.Int64.unsigned
                  (CompCert4Lean.Lib.Integers.WordCore.repr
                    CompCert4Lean.Lib.Integers.Int64.wordsize (zOfNat 0))) =
                CompCert4Lean.Lib.Integers.Ptrofs.repr
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0) by rfl]
            exact selection_ptrofs_add_zero ofs
          unfold CompCert4Lean.Backend.Selection.store
          rw [hadd]
          apply CminorSel.step.step_store
          · exact eval_exprlist.cons [] (Eop (.Olea addr) args) Enil
              (Vptr b ofs) [] h1 (eval_exprlist.nil [])
          · exact h2
          · exact haddr
          · exact hstore
      | addressing_case2 addr args =>
          by_cases hvalid : addressing_valid addr
          · cases h1 with
            | eval_Eop le' op al vl vv hargs hop =>
                have hadd :
                    CompCert4Lean.X86.SelectOp.addressing chunk (Eop (.Oleal addr) args) =
                      (addr, args) := by
                  simp [CompCert4Lean.X86.SelectOp.addressing, addressing_match,
                    hvalid, CompCert4Lean.X86_64.Archi.ptr64]
                have haddr :
                    eval_addressing (Genv.globalenv tprog) sp addr vl =
                      some (Vptr b ofs) := by
                  change eval_addressing64 (Genv.globalenv tprog) sp addr vl =
                    some (Vptr b ofs)
                  change eval_addressing64 (Genv.globalenv tprog) sp addr vl =
                    some (Vptr b ofs) at hop
                  exact hop
                unfold CompCert4Lean.Backend.Selection.store
                rw [hadd]
                apply CminorSel.step.step_store
                · exact hargs
                · exact h2
                · exact haddr
                · exact hstore
          · have hadd :
                CompCert4Lean.X86.SelectOp.addressing chunk (Eop (.Oleal addr) args) =
                  (.Aindexed (zOfNat 0), Econs (Eop (.Oleal addr) args) Enil) := by
              simp [CompCert4Lean.X86.SelectOp.addressing, addressing_match, hvalid,
                CompCert4Lean.X86_64.Archi.ptr64]
              rfl
            have haddr :
                eval_addressing (Genv.globalenv tprog) sp (.Aindexed (zOfNat 0))
                  [Vptr b ofs] = some (Vptr b ofs) := by
              simp [eval_addressing, eval_addressing64,
                CompCert4Lean.X86_64.Archi.ptr64, Val.addl,
                CompCert4Lean.Lib.Integers.Ptrofs.of_int64,
                CompCert4Lean.Lib.Integers.Int64.repr]
              rw [show CompCert4Lean.Lib.Integers.Ptrofs.repr
                  (CompCert4Lean.Lib.Integers.Int64.unsigned
                    (CompCert4Lean.Lib.Integers.WordCore.repr
                      CompCert4Lean.Lib.Integers.Int64.wordsize (zOfNat 0))) =
                  CompCert4Lean.Lib.Integers.Ptrofs.repr
                    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0) by rfl]
              exact selection_ptrofs_add_zero ofs
            unfold CompCert4Lean.Backend.Selection.store
            rw [hadd]
            apply CminorSel.step.step_store
            · exact eval_exprlist.cons [] (Eop (.Oleal addr) args) Enil
                (Vptr b ofs) [] h1 (eval_exprlist.nil [])
            · exact h2
            · exact haddr
            · exact hstore
      | addressing_default _ =>
          have hadd :
              CompCert4Lean.X86.SelectOp.addressing chunk a1 =
                (.Aindexed (zOfNat 0), Econs a1 Enil) := by
            unfold CompCert4Lean.X86.SelectOp.addressing
            cases a1 with
            | Eop op args =>
                cases op <;>
                  simp [addressing_match, CompCert4Lean.X86_64.Archi.ptr64] at hcase ⊢ <;>
                  rfl
            | _ =>
                simp [addressing_match, CompCert4Lean.X86_64.Archi.ptr64] at hcase ⊢ <;>
                  rfl
          have haddr :
              eval_addressing (Genv.globalenv tprog) sp (.Aindexed (zOfNat 0))
                [Vptr b ofs] = some (Vptr b ofs) := by
            simp [eval_addressing, eval_addressing64,
              CompCert4Lean.X86_64.Archi.ptr64, Val.addl,
              CompCert4Lean.Lib.Integers.Ptrofs.of_int64,
              CompCert4Lean.Lib.Integers.Int64.repr]
            rw [show CompCert4Lean.Lib.Integers.Ptrofs.repr
                (CompCert4Lean.Lib.Integers.Int64.unsigned
                  (CompCert4Lean.Lib.Integers.WordCore.repr
                    CompCert4Lean.Lib.Integers.Int64.wordsize (zOfNat 0))) =
                CompCert4Lean.Lib.Integers.Ptrofs.repr
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0) by rfl]
            exact selection_ptrofs_add_zero ofs
          unfold CompCert4Lean.Backend.Selection.store
          rw [hadd]
          apply CminorSel.step.step_store
          · exact eval_exprlist.cons [] a1 Enil (Vptr b ofs) [] h1
              (eval_exprlist.nil [])
          · exact h2
          · exact haddr
          · exact hstore

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.Selection
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

private theorem selection_lessdef_normalize (v : val) (ty : typ) :
    Val.lessdef (Val.normalize v ty) v := by
  cases v <;> cases ty <;>
    simp [Val.normalize, CompCert4Lean.X86_64.Archi.ptr64] <;>
    first | exact Val.lessdef_refl _ | exact Val.lessdef_undef _

theorem eval_sel_select
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_sel_selectStatement := by
  intro xi tprog sp e m le aCond aThen aElse vCond vThen vElse b ty
    hCond hThen hElse hb
  have hc := eval_condition_of_expr
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    xi tprog sp e m aCond le vCond b hCond hb
  cases hshape : condition_of_expr aCond with
  | mk cond args =>
      simp only [hshape] at hc
      rcases hc with ⟨vl, hargs, hcond⟩
      by_cases hsupported : select_supported ty = true
      · have hsel : sel_select ty aCond aThen aElse =
            CompCert4Lean.X86.SelectOp.select ty cond args aThen aElse := by
          simp [sel_select, hshape, hsupported]
        rw [hsel]
        by_cases hswap : select_swap cond = true
        · have hneg := eval_negate_condition cond vl m
          have hneg' :
              eval_condition (negate_condition cond) vl m = some (!b) := by
            rw [hneg, hcond]
            rfl
          refine ⟨Val.select (some b) vThen vElse ty, ?_, Val.lessdef_refl _⟩
          simp only [CompCert4Lean.X86.SelectOp.select, hswap, ↓reduceIte]
          apply eval_Eop
          · exact eval_exprlist.cons le aElse (Econs aThen args) vElse
              (vThen :: vl) hElse
              (eval_exprlist.cons le aThen args vThen vl hThen hargs)
          · change some (Val.select (eval_condition (negate_condition cond) vl m)
                vElse vThen ty) = some (Val.select (some b) vThen vElse ty)
            rw [hneg']
            cases b <;> rfl
        · refine ⟨Val.select (some b) vThen vElse ty, ?_, Val.lessdef_refl _⟩
          simp only [CompCert4Lean.X86.SelectOp.select, hswap, ↓reduceIte]
          apply eval_Eop
          · exact eval_exprlist.cons le aThen (Econs aElse args) vThen
              (vElse :: vl) hThen
              (eval_exprlist.cons le aElse args vElse vl hElse hargs)
          · change some (Val.select (eval_condition cond vl m) vThen vElse ty) =
                some (Val.select (some b) vThen vElse ty)
            rw [hcond]
      · refine ⟨if b then vThen else vElse, ?_, ?_⟩
        · have hsel : sel_select ty aCond aThen aElse =
              .Econdition (condexpr_of_expr aCond) aThen aElse := by
            simp [sel_select, hshape, hsupported]
          rw [hsel]
          apply eval_Econdition
          · exact eval_condexpr_of_expr
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate)
              xi tprog sp e m aCond le vCond b hCond hb
          · cases b
            · exact hElse
            · exact hThen
        · exact selection_lessdef_normalize _ _

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.Selection
open CompCert4Lean.Common.Switch
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers

private theorem selection_bool_of_bool (b : Bool) :
    Val.bool_of_val (Val.of_bool b) b := by
  cases b <;> simp [Val.of_bool, Vtrue, Vfalse]
  · constructor
  · constructor

private theorem selection_Rint_inv (i : Z) (v : val) (h : Rint i v) :
    ∃ n, v = Vint n ∧ i = Int.unsigned n := by
  cases h
  exact ⟨_, rfl, rfl⟩

theorem sel_switch_correct_rec
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    sel_switch_correct_recStatement := by
  intro xi tprog make_cmp_eq make_cmp_ltu make_sub make_to_int modulus R
    hEq hLt hSub hToInt sp e m varg i x hRi t
  induction t generalizing sp e m varg i x with
  | CTaction act =>
      intro arg le hWF hNth hMatch
      simp [comptree_match] at hMatch
      cases hMatch
      exact eval_exitexpr.exit le act
  | CTifeq key act cne ih =>
      intro arg le hWF hNth hMatch
      cases hWF with
      | wf_ifeq key act cne hkey hWf =>
          cases hz : zeq i key with
          | left hik =>
              have hcmp := hEq sp e m le (.Eletvar arg) varg i key
                (eval_expr.eval_Eletvar le arg varg hNth) hRi hkey
              apply eval_exitexpr.eval_XEcondition le
                (condexpr_of_expr (make_cmp_eq (.Eletvar arg) key))
                (.XEexit act)
                (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int arg cne)
                true x
              · apply CompCert4Lean.Backend.Selectionproof.eval_condexpr_of_expr
                · exact hcmp
                · simpa [hz, proj_sumbool] using selection_bool_of_bool true
              · simp [comptree_match, hz] at hMatch
                cases hMatch
                exact eval_exitexpr.exit _ _
          | right hik =>
              have hcmp := hEq sp e m le (.Eletvar arg) varg i key
                (eval_expr.eval_Eletvar le arg varg hNth) hRi hkey
              apply eval_exitexpr.eval_XEcondition le
                (condexpr_of_expr (make_cmp_eq (.Eletvar arg) key))
                (.XEexit act)
                (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int arg cne)
                false x
              · apply CompCert4Lean.Backend.Selectionproof.eval_condexpr_of_expr
                · exact hcmp
                · simpa [hz, proj_sumbool] using selection_bool_of_bool false
              · simp [comptree_match, hz] at hMatch
                apply ih sp e m varg i x hRi arg le hWf hNth hMatch
  | CTiflt key clt cge ihl ihr =>
      intro arg le hWF hNth hMatch
      cases hWF with
      | wf_iflt key clt cge hkey hWfl hWfr =>
          cases hz : zlt i key with
          | left hil =>
              have hcmp := hLt sp e m le (.Eletvar arg) varg i key
                (eval_expr.eval_Eletvar le arg varg hNth) hRi hkey
              apply eval_exitexpr.eval_XEcondition le
                (condexpr_of_expr (make_cmp_ltu (.Eletvar arg) key))
                (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int arg clt)
                (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int arg cge)
                true x
              · apply CompCert4Lean.Backend.Selectionproof.eval_condexpr_of_expr
                · exact hcmp
                · simpa [hz, proj_sumbool] using selection_bool_of_bool true
              · simp [comptree_match, hz] at hMatch
                apply ihl sp e m varg i x hRi arg le hWfl hNth hMatch
          | right hil =>
              have hcmp := hLt sp e m le (.Eletvar arg) varg i key
                (eval_expr.eval_Eletvar le arg varg hNth) hRi hkey
              apply eval_exitexpr.eval_XEcondition le
                (condexpr_of_expr (make_cmp_ltu (.Eletvar arg) key))
                (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int arg clt)
                (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int arg cge)
                false x
              · apply CompCert4Lean.Backend.Selectionproof.eval_condexpr_of_expr
                · exact hcmp
                · simpa [hz, proj_sumbool] using selection_bool_of_bool false
              · simp [comptree_match, hz] at hMatch
                apply ihr sp e m varg i x hRi arg le hWfr hNth hMatch
  | CTjumptable ofs sz acts cother ih =>
      intro arg le hWF hNth hMatch
      cases hWF with
      | wf_jumptable ofs sz acts cother hofs hsz hWf =>
          obtain ⟨v', hv', hRv'⟩ := hSub sp e m le (.Eletvar arg) varg i ofs
            (eval_expr.eval_Eletvar le arg varg hNth) hRi hofs
          apply eval_exitexpr.letBinding le
            (make_sub (.Eletvar arg) ofs)
            (.XEcondition
              (condexpr_of_expr (make_cmp_ltu (.Eletvar 0) sz))
              (.XEjumptable (make_to_int (.Eletvar 0)) acts)
              (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int (arg + 1) cother))
            v' x
          · exact hv'
          · have hzero : CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.nth_error
                (v' :: le) 0 = some v' := by rfl
            have hcmp := hLt sp e m (v' :: le) (.Eletvar 0) v'
              (ZArith.BinInt.Z.modulo (ZArith.BinInt.Z.sub i ofs) modulus) sz
              (eval_expr.eval_Eletvar (v' :: le) 0 v' hzero)
              hRv' hsz
            cases hz : zlt (ZArith.BinInt.Z.modulo (ZArith.BinInt.Z.sub i ofs) modulus) sz with
            | left hinside =>
                apply eval_exitexpr.eval_XEcondition (v' :: le)
                  (condexpr_of_expr (make_cmp_ltu (.Eletvar 0) sz))
                  (.XEjumptable (make_to_int (.Eletvar 0)) acts)
                  (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int (arg + 1) cother)
                  true x
                · apply CompCert4Lean.Backend.Selectionproof.eval_condexpr_of_expr
                  · exact hcmp
                  · simpa [hz, proj_sumbool] using selection_bool_of_bool true
                · obtain ⟨v'', hv'', hRv''⟩ := hToInt sp e m (v' :: le)
                    (.Eletvar 0) v' (ZArith.BinInt.Z.modulo (ZArith.BinInt.Z.sub i ofs) modulus)
                    (eval_expr.eval_Eletvar (v' :: le) 0 v' hzero) hRv'
                  obtain ⟨n, hvn, hidx⟩ := selection_Rint_inv _ _ hRv''
                  subst v''
                  apply eval_exitexpr.jumptable (v' :: le)
                    (make_to_int (.Eletvar 0)) acts n x hv''
                  simpa [comptree_match, hz, hidx] using hMatch
            | right hout =>
                apply eval_exitexpr.eval_XEcondition (v' :: le)
                  (condexpr_of_expr (make_cmp_ltu (.Eletvar 0) sz))
                  (.XEjumptable (make_to_int (.Eletvar 0)) acts)
                  (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int (arg + 1) cother)
                  false x
                · apply CompCert4Lean.Backend.Selectionproof.eval_condexpr_of_expr
                  · exact hcmp
                  · simpa [hz, proj_sumbool] using selection_bool_of_bool false
                · simp [comptree_match, hz] at hMatch
                  have hNth' : CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.nth_error
                      (v' :: le) (arg + 1) = some varg := by
                    change CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.nth_error
                      le arg = some varg
                    exact hNth
                  apply ih sp e m varg i x hRi (arg + 1) (v' :: le) hWf hNth' hMatch

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.Cminor

theorem eval_unop_lessdef
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_unop_lessdefStatement := by
  intro op v1 v1' v hEval hld
  cases hld with
  | lessdef_refl =>
      exact ⟨v, hEval, Val.lessdef_refl _⟩
  | lessdef_undef =>
      cases op <;> simp [Cminor.eval_unop, Val.zero_ext, Val.sign_ext, Val.negint,
        Val.notint, Val.negf, Val.absf, Val.negfs, Val.absfs,
        Val.singleoffloat, Val.floatofsingle, Val.intoffloat, Val.intuoffloat,
        Val.floatofint, Val.floatofintu, Val.intofsingle, Val.intuofsingle,
        Val.singleofint, Val.singleofintu, Val.negl, Val.notl, Val.loword,
        Val.longofint, Val.longofintu, Val.longoffloat, Val.longuoffloat,
        Val.floatoflong, Val.floatoflongu, Val.longofsingle, Val.longuofsingle,
        Val.singleoflong, Val.singleoflongu] at hEval ⊢ <;>
        subst v <;> exact Val.lessdef_undef _

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Lib.Maps

theorem set_var_lessdef : set_var_lessdefStatement := by
  intro e1 e2 id v1 v2 hEnv hVal id0 v1' hGet
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive at id
  change CompCert4Lean.Lib.Maps.PTree.tree CompCert4Lean.Common.Values.val at e1 e2
  rw [CompCert4Lean.Lib.Maps.PTree.getSet_equation] at hGet
  by_cases hid : id0 = id
  · subst id0
    simp at hGet
    cases hGet
    exact ⟨v2,
      CompCert4Lean.Lib.Maps.PTree.gss
        (A := CompCert4Lean.Common.Values.val) id v2 e2,
      hVal⟩
  · simp [hid] at hGet
    rcases hEnv id0 v1' hGet with ⟨v2', hGet2, hld⟩
    have hSet2 :
        CompCert4Lean.Lib.Maps.PTree.get id0
            (CompCert4Lean.Lib.Maps.PTree.set id v2 e2) =
          CompCert4Lean.Lib.Maps.PTree.get id0 e2 :=
      CompCert4Lean.Lib.Maps.PTree.gso
        (A := CompCert4Lean.Common.Values.val) (i := id0) (j := id) v2 e2 hid
    exact ⟨v2', by rw [hSet2, hGet2], hld⟩

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Lib.Maps

theorem set_params_lessdef : set_params_lessdefStatement := by
  intro il vl1 vl2 hld
  induction il generalizing vl1 vl2 with
  | nil =>
      intro id v hget
      have hset :
          CompCert4Lean.Backend.Cminor.set_params vl1 [] =
            CompCert4Lean.Lib.Maps.PTree.empty CompCert4Lean.Common.Values.val := by
        cases vl1 <;> rfl
      have hempty :
          CompCert4Lean.Lib.Maps.PTree.get id
              (CompCert4Lean.Lib.Maps.PTree.empty CompCert4Lean.Common.Values.val) = none :=
        CompCert4Lean.Lib.Maps.PTree.gempty CompCert4Lean.Common.Values.val id
      rw [hset, hempty] at hget
      cases hget
  | cons i il ih =>
      cases vl1 with
      | nil =>
          cases vl2 with
          | nil =>
              apply set_var_lessdef
              · exact ih [] [] CompCert4Lean.Common.Values.Val.lessdef_list_nil
              · exact CompCert4Lean.Common.Values.Val.lessdef_undef _
          | cons v2 vl2 =>
              cases hld
      | cons v1 vl1 =>
          cases vl2 with
          | nil =>
              cases hld
          | cons v2 vl2 =>
              cases hld with
              | lessdef_list_cons _ _ _ _ hv htail =>
                  apply set_var_lessdef
                  · exact ih vl1 vl2 htail
                  · exact hv

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Lib.Maps

theorem set_locals_lessdef : set_locals_lessdefStatement := by
  intro e1 e2 hEnv il
  induction il with
  | nil =>
      simpa [CompCert4Lean.Backend.Cminor.set_locals] using hEnv
  | cons i il ih =>
      dsimp [CompCert4Lean.Backend.Cminor.set_locals]
      apply set_var_lessdef
      · exact ih
      · exact CompCert4Lean.Common.Values.Val.lessdef_undef _

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

theorem sel_builtin_res_correct : sel_builtin_res_correctStatement := by
  intro oid v e v' e' hEnv hVal
  cases oid with
  | none =>
      exact hEnv
  | some id =>
      apply set_var_lessdef
      · exact hEnv
      · exact hVal

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

theorem classify_stmt_wt : classify_stmt_wtStatement := by
  intro env tyret id a s hclass hwt
  induction hwt with
  | wt_Sskip =>
      simp [CompCert4Lean.Backend.Selection.classify_stmt] at hclass
  | wt_Sassign id' a' htyped =>
      cases a' <;>
        simp [CompCert4Lean.Backend.Selection.classify_stmt] at hclass
      case Evar id'' =>
        cases heq : CompCert4Lean.Common.AST.ident_eq id' id'' with
        | left h =>
            simp [heq] at hclass
        | right h =>
            simp [heq] at hclass
            obtain ⟨rfl, rfl⟩ := hclass
            exact htyped
      all_goals
        obtain ⟨rfl, rfl⟩ := hclass
        exact htyped
  | wt_Sbuiltin optid ef al hargs hopt =>
      clear hargs hopt
      cases optid <;> cases ef <;>
        simp [CompCert4Lean.Backend.Selection.classify_stmt] at hclass
  | wt_Sseq s1 s2 hwt1 hwt2 ih1 ih2 =>
      cases hclass1 : CompCert4Lean.Backend.Selection.classify_stmt s1 with
      | SCskip =>
          cases hclass2 : CompCert4Lean.Backend.Selection.classify_stmt s2 with
          | SCskip | SCother =>
              simp [CompCert4Lean.Backend.Selection.classify_stmt, hclass1, hclass2] at hclass
          | SCassign id' a' =>
              simp [CompCert4Lean.Backend.Selection.classify_stmt, hclass1, hclass2] at hclass
              obtain ⟨rfl, rfl⟩ := hclass
              exact ih2 hclass2
      | SCassign id' a' =>
          cases hclass2 : CompCert4Lean.Backend.Selection.classify_stmt s2 with
          | SCskip =>
              simp [CompCert4Lean.Backend.Selection.classify_stmt, hclass1, hclass2] at hclass
              obtain ⟨rfl, rfl⟩ := hclass
              exact ih1 hclass1
          | SCassign | SCother =>
              simp [CompCert4Lean.Backend.Selection.classify_stmt, hclass1, hclass2] at hclass
      | SCother =>
          cases hclass2 : CompCert4Lean.Backend.Selection.classify_stmt s2 <;>
            simp [CompCert4Lean.Backend.Selection.classify_stmt, hclass1, hclass2] at hclass
  | wt_Sstore | wt_Scall | wt_Stailcall | wt_Sifthenelse | wt_Sloop |
    wt_Sblock | wt_Sexit | wt_Sswitch | wt_Sreturn_none | wt_Sreturn_some |
    wt_Slabel | wt_Sgoto =>
      simp [CompCert4Lean.Backend.Selection.classify_stmt] at hclass

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

theorem eventually_step
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eventually_stepStatement := by
  intro xi prog f s k sp e m n P hstep
  unfold eventually
  apply CompCert4Lean.Common.Smallstep.eventually_later
  · intro r hfinal
    cases hfinal
  · intro t s' h
    exact (hstep t s' h).1
  · intro t s' h
    exact (hstep t s' h).2

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

theorem classify_stmt_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    classify_stmt_soundStatement := by
  intro xi prog s
  induction s with
  | Sskip =>
      simp [CompCert4Lean.Backend.Selection.classify_stmt]
      refine ⟨0, ?_⟩
      intro f k sp e m
      unfold eventually
      exact CompCert4Lean.Common.Smallstep.eventually_now _ _ _ _ _ rfl
  | Sassign id a =>
      have base :
          ∃ n, ∀ (f : CompCert4Lean.Backend.Cminor.function)
            (k : CompCert4Lean.Backend.Cminor.cont)
            (sp : CompCert4Lean.Common.Values.val) (e : Env)
            (m : CompCert4Lean.Common.Memory.mem)
            (v : CompCert4Lean.Common.Values.val),
            CompCert4Lean.Backend.Cminor.eval_expr
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate)
              (CompCert4Lean.Common.Globalenvs.Genv.globalenv prog) sp e m a v →
            eventually prog xi n
              (CompCert4Lean.Backend.Cminor.State f (.Sassign id a) k sp e m)
              (Eq (CompCert4Lean.Backend.Cminor.State f .Sskip k sp
                (CompCert4Lean.Lib.Maps.PTree.set id v e) m)) := by
        refine ⟨1, ?_⟩
        intro f k sp e m v heval
        apply eventually_step
        intro t s' hstep
        cases hstep with
        | step_assign _ _ _ _ _ _ _ v' heval' =>
            have hv : v' = v :=
              CompCert4Lean.Backend.Cminor.eval_expr_determ _ _ _ _ _ _ heval v' heval'
            subst v'
            refine ⟨rfl, ?_⟩
            unfold eventually
            exact CompCert4Lean.Common.Smallstep.eventually_now _ _ _ _ _ rfl
      cases a with
      | Evar id' =>
          cases heq : CompCert4Lean.Common.AST.ident_eq id id' with
          | left hid =>
              subst id'
              simp [CompCert4Lean.Backend.Selection.classify_stmt, heq]
              refine ⟨1, ?_⟩
              intro f k sp e m
              apply eventually_step
              intro t s' hstep
              cases hstep with
              | step_assign _ _ _ _ _ _ _ v heval =>
                  cases heval with
                  | eval_Evar _ _ hget =>
                      refine ⟨rfl, ?_⟩
                      rw [CompCert4Lean.Lib.Maps.PTree.gsident id e hget]
                      unfold eventually
                      exact CompCert4Lean.Common.Smallstep.eventually_now _ _ _ _ _ rfl
          | right hne =>
              simpa [CompCert4Lean.Backend.Selection.classify_stmt, heq] using base
      | _ =>
          simpa [CompCert4Lean.Backend.Selection.classify_stmt] using base
  | Sbuiltin optid ef args =>
      cases optid <;> cases ef <;>
        simp [CompCert4Lean.Backend.Selection.classify_stmt]
      all_goals
        refine ⟨1, ?_⟩
        intro f k sp e m
        apply eventually_step
        intro t s' hstep
        cases hstep with
        | step_builtin _ _ _ _ _ _ _ _ _ _ _ _ hargs hext =>
            cases hext
            refine ⟨rfl, ?_⟩
            unfold eventually
            exact CompCert4Lean.Common.Smallstep.eventually_now _ _ _ _ _ rfl
  | Sseq s1 s2 ih1 ih2 =>
      have eseq :
          ∀ n1 n2 (f : CompCert4Lean.Backend.Cminor.function)
            (sp : CompCert4Lean.Common.Values.val)
            (m : CompCert4Lean.Common.Memory.mem) (e e' e'' : Env),
            (∀ k, eventually prog xi n1
              (CompCert4Lean.Backend.Cminor.State f s1 k sp e m)
              (Eq (CompCert4Lean.Backend.Cminor.State f .Sskip k sp e' m))) →
            (∀ k, eventually prog xi n2
              (CompCert4Lean.Backend.Cminor.State f s2 k sp e' m)
              (Eq (CompCert4Lean.Backend.Cminor.State f .Sskip k sp e'' m))) →
            ∀ k, eventually prog xi (Nat.succ (n1 + Nat.succ n2))
              (CompCert4Lean.Backend.Cminor.State f (.Sseq s1 s2) k sp e m)
              (Eq (CompCert4Lean.Backend.Cminor.State f .Sskip k sp e'' m)) := by
        intro n1 n2 f sp m e e' e'' hfirst hsecond k
        apply eventually_step
        intro t s' hstep
        cases hstep with
        | step_seq =>
            refine ⟨rfl, ?_⟩
            apply CompCert4Lean.Common.Smallstep.eventually_trans
            · exact hfirst _
            · intro s' hs'
              subst s'
              apply eventually_step
              intro t s' hstep
              cases hstep with
              | step_skip_seq => exact ⟨rfl, hsecond _⟩
              | step_skip_call _ _ _ _ _ _ hcall _ =>
                  simp [CompCert4Lean.Backend.Cminor.is_call_cont] at hcall
      cases hc1 : CompCert4Lean.Backend.Selection.classify_stmt s1 with
      | SCskip =>
          cases hc2 : CompCert4Lean.Backend.Selection.classify_stmt s2 with
          | SCskip =>
              simp [CompCert4Lean.Backend.Selection.classify_stmt, hc1, hc2] at ih1 ih2 ⊢
              rcases ih1 with ⟨n1, h1⟩
              rcases ih2 with ⟨n2, h2⟩
              exact ⟨Nat.succ (n1 + Nat.succ n2), fun f k sp e m =>
                eseq n1 n2 f sp m e e e
                  (fun k => h1 f k sp e m) (fun k => h2 f k sp e m) k⟩
          | SCassign id a =>
              simp [CompCert4Lean.Backend.Selection.classify_stmt, hc1, hc2] at ih1 ih2 ⊢
              rcases ih1 with ⟨n1, h1⟩
              rcases ih2 with ⟨n2, h2⟩
              refine ⟨Nat.succ (n1 + Nat.succ n2), ?_⟩
              intro f k sp e m v heval
              exact eseq n1 n2 f sp m e e (CompCert4Lean.Lib.Maps.PTree.set id v e)
                (fun k => h1 f k sp e m) (fun k => h2 f k sp e m v heval) k
          | SCother =>
              simp [CompCert4Lean.Backend.Selection.classify_stmt, hc1, hc2]
      | SCassign id a =>
          cases hc2 : CompCert4Lean.Backend.Selection.classify_stmt s2 with
          | SCskip =>
              simp [CompCert4Lean.Backend.Selection.classify_stmt, hc1, hc2] at ih1 ih2 ⊢
              rcases ih1 with ⟨n1, h1⟩
              rcases ih2 with ⟨n2, h2⟩
              refine ⟨Nat.succ (n1 + Nat.succ n2), ?_⟩
              intro f k sp e m v heval
              exact eseq n1 n2 f sp m e (CompCert4Lean.Lib.Maps.PTree.set id v e)
                (CompCert4Lean.Lib.Maps.PTree.set id v e)
                (fun k => h1 f k sp e m v heval)
                (fun k => h2 f k sp (CompCert4Lean.Lib.Maps.PTree.set id v e) m) k
          | SCassign | SCother =>
              simp [CompCert4Lean.Backend.Selection.classify_stmt, hc1, hc2]
      | SCother =>
          cases hc2 : CompCert4Lean.Backend.Selection.classify_stmt s2 <;>
            simp [CompCert4Lean.Backend.Selection.classify_stmt, hc1, hc2]
  | Sstore | Scall | Stailcall | Sifthenelse | Sloop | Sblock | Sexit |
    Sswitch | Sreturn | Slabel | Sgoto =>
      simp [CompCert4Lean.Backend.Selection.classify_stmt]

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

theorem classify_stmt_nolabel : classify_stmt_nolabelStatement := by
  intro s hclass
  induction s with
  | Sskip =>
      intro lbl k
      rfl
  | Sassign id a =>
      intro lbl k
      rfl
  | Sstore chunk address value =>
      simp [CompCert4Lean.Backend.Selection.classify_stmt] at hclass
  | Scall result sig callee args =>
      simp [CompCert4Lean.Backend.Selection.classify_stmt] at hclass
  | Stailcall sig callee args =>
      simp [CompCert4Lean.Backend.Selection.classify_stmt] at hclass
  | Sbuiltin optid ef args =>
      cases optid <;> cases ef <;>
        simp [CompCert4Lean.Backend.Selection.classify_stmt] at hclass
      intro lbl k
      rfl
  | Sseq s1 s2 ih1 ih2 =>
      cases hc1 : CompCert4Lean.Backend.Selection.classify_stmt s1 with
      | SCskip =>
          cases hc2 : CompCert4Lean.Backend.Selection.classify_stmt s2 with
          | SCskip | SCassign _ _ =>
              have h1 := ih1 (by simpa [hc1])
              have h2 := ih2 (by simpa [hc2])
              intro lbl k
              simp only [CompCert4Lean.Backend.Cminor.find_label]
              rw [h1 lbl (CompCert4Lean.Backend.Cminor.Kseq s2 k)]
              exact h2 lbl k
          | SCother =>
              simp [CompCert4Lean.Backend.Selection.classify_stmt, hc1, hc2] at hclass
      | SCassign _ _ =>
          cases hc2 : CompCert4Lean.Backend.Selection.classify_stmt s2 with
          | SCskip =>
              have h1 := ih1 (by simpa [hc1])
              have h2 := ih2 (by simpa [hc2])
              intro lbl k
              simp only [CompCert4Lean.Backend.Cminor.find_label]
              rw [h1 lbl (CompCert4Lean.Backend.Cminor.Kseq s2 k)]
              exact h2 lbl k
          | SCassign _ _ | SCother =>
              simp [CompCert4Lean.Backend.Selection.classify_stmt, hc1, hc2] at hclass
      | SCother =>
          cases hc2 : CompCert4Lean.Backend.Selection.classify_stmt s2 <;>
            simp [CompCert4Lean.Backend.Selection.classify_stmt, hc1, hc2] at hclass
  | Sifthenelse condition ifso ifnot =>
      simp [CompCert4Lean.Backend.Selection.classify_stmt] at hclass
  | Sloop body =>
      simp [CompCert4Lean.Backend.Selection.classify_stmt] at hclass
  | Sblock body =>
      simp [CompCert4Lean.Backend.Selection.classify_stmt] at hclass
  | Sexit depth =>
      simp [CompCert4Lean.Backend.Selection.classify_stmt] at hclass
  | Sswitch isLong argument cases default =>
      simp [CompCert4Lean.Backend.Selection.classify_stmt] at hclass
  | Sreturn value =>
      simp [CompCert4Lean.Backend.Selection.classify_stmt] at hclass
  | Slabel label body =>
      simp [CompCert4Lean.Backend.Selection.classify_stmt] at hclass
  | Sgoto label =>
      simp [CompCert4Lean.Backend.Selection.classify_stmt] at hclass

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

variable [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
variable [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
variable [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
variable [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
variable (cfg : CompilerConfig) (oracle : SelectionOracle)

theorem if_conversion_base_nolabel : if_conversion_base_nolabelStatement cfg oracle := by
  intro hf ki env a id a1 a2 kont s h
  unfold CompCert4Lean.Backend.Selection.if_conversion_base at h
  dsimp at h
  split at h <;> try cases h
  intro lbl k
  rfl

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

variable [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
variable [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
variable [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
variable [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
variable (cfg : CompilerConfig) (oracle : SelectionOracle)

theorem if_conversion_nolabel : if_conversion_nolabelStatement cfg oracle := by
  intro hf ki env a s1 s2 kont s h
  unfold CompCert4Lean.Backend.Selection.if_conversion at h
  cases hc1 : CompCert4Lean.Backend.Selection.classify_stmt s1 <;>
    cases hc2 : CompCert4Lean.Backend.Selection.classify_stmt s2 <;>
    simp [CompCert4Lean.Backend.Selection.if_conversion, hc1, hc2] at h
  · have hs1 : nolabel s1 := classify_stmt_nolabel s1 (by simp [hc1])
    have hs2 : nolabel s2 := classify_stmt_nolabel s2 (by simp [hc2])
    exact ⟨hs1, hs2,
      if_conversion_base_nolabel cfg oracle hf ki env a _ _ _ _ s h⟩
  · have hs1 : nolabel s1 := classify_stmt_nolabel s1 (by simp [hc1])
    have hs2 : nolabel s2 := classify_stmt_nolabel s2 (by simp [hc2])
    exact ⟨hs1, hs2,
      if_conversion_base_nolabel cfg oracle hf ki env a _ _ _ _ s h⟩
  · have hs1 : nolabel s1 := classify_stmt_nolabel s1 (by simp [hc1])
    have hs2 : nolabel s2 := classify_stmt_nolabel s2 (by simp [hc2])
    split at h
    · exact ⟨hs1, hs2,
        if_conversion_base_nolabel cfg oracle hf ki env a _ _ _ _ s h⟩
    · cases h

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

variable [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
variable [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
variable [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
variable [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
variable (cfg : CompilerConfig) (oracle : SelectionOracle)

theorem sel_final_states : sel_final_statesStatement cfg oracle := by
  intro prog s tr v hmatch hfinal
  cases hfinal with
  | final_state_intro r m =>
      cases hmatch with
      | match_returnstate v tv k ks m ms hc hl hm =>
          cases hc with
          | match_cont_stop =>
              cases hl with
              | lessdef_refl =>
                  exact CminorSel.final_state.intro v ms

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

variable [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
variable [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
variable [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
variable [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
variable (cfg : CompilerConfig) (oracle : SelectionOracle)

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers

private theorem selection_mem_extends_refl
    (m : CompCert4Lean.Common.Memory.Mem.mem) :
    CompCert4Lean.Common.Memory.Mem.extends m m := by
  refine ⟨rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro b1 b2 delta ofs k p hmap hp
      have hpair : (b1, (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)) = (b2, delta) := by
        simpa [CompCert4Lean.Common.Values.inject_id] using Option.some.inj hmap
      cases hpair
      change CompCert4Lean.Common.Memory.Mem.perm m b1
        (ZArith.BinInt.Z.add ofs (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)) k p
      have hzadd : ZArith.BinInt.Z.add ofs
          (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) = ofs := by
        apply intOfZ_injective
        change intOfZ (zOfInt (intOfZ ofs + 0)) = intOfZ ofs
        rw [intOfZ_zOfInt]
        simp
      rw [hzadd]
      exact hp
    · intro b1 b2 delta chunk ofs p hmap hp
      have hpair : (b1, (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)) = (b2, delta) := by
        simpa [CompCert4Lean.Common.Values.inject_id] using Option.some.inj hmap
      cases hpair
      refine ⟨.Z0, ?_⟩
      apply intOfZ_injective
      change 0 = intOfZ (ZArith.BinInt.Z.mul
        (CompCert4Lean.Common.Memdata.align_chunk chunk)
        (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z))
      change 0 = intOfZ (zOfInt (intOfZ
        (CompCert4Lean.Common.Memdata.align_chunk chunk) * 0))
      rw [intOfZ_zOfInt]
      simp
    · intro b ofs b' delta hmap hval
      have hpair : (b, (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)) = (b', delta) := by
        simpa [CompCert4Lean.Common.Values.inject_id] using Option.some.inj hmap
      cases hpair
      change CompCert4Lean.Common.Memdata.memval_inject
        CompCert4Lean.Common.Values.inject_id
        (CompCert4Lean.Lib.Maps.ZMap.get ofs (CompCert4Lean.Lib.Maps.PMap.get b m.mem_contents))
        (CompCert4Lean.Lib.Maps.ZMap.get
          (ZArith.BinInt.Z.add ofs
            (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z))
          (CompCert4Lean.Lib.Maps.PMap.get b m.mem_contents))
      have hzadd : ZArith.BinInt.Z.add ofs
          (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) = ofs := by
        apply intOfZ_injective
        change intOfZ (zOfInt (intOfZ ofs + 0)) = intOfZ ofs
        rw [intOfZ_zOfInt]
        simp
      rw [hzadd]
      exact CompCert4Lean.Common.Memdata.memval_lessdef_refl _
  · intro b ofs k p hp
    exact Or.inl hp

theorem sel_initial_states : sel_initial_statesStatement cfg oracle := by
  intro prog tprog hm s hinit
  cases hinit with
  | initial_state_intro b f m0 hmem hsym hfun hsig =>
      rcases @CompCert4Lean.Common.Globalenvs.Genv.find_funct_ptr_match
          CminorProgram CminorFundef Unit CminorSelFundef Unit
          cminorProgramLinker
          (fun cu f tf => match_fundef cfg oracle cu f tf)
          (fun x y : Unit => x = y) prog prog tprog
          (by
            change CompCert4Lean.Common.Linking.match_program_gen
              (fun cu f tf => match_fundef cfg oracle cu f tf)
              (fun x y : Unit => x = y) prog prog tprog
            exact hm) b f hfun with
        ⟨cu, tf, htf, hmatch, horder⟩
      refine ⟨CminorSel.Callstate tf [] CminorSel.Kstop m0, ?_, ?_⟩
      · apply CminorSel.initial_state.intro b tf m0
        · unfold Genv.init_mem at hmem ⊢
          apply Genv.alloc_globals_match
            CminorProgram CminorFundef Unit CminorSelFundef Unit
            (fun cu f tf => match_fundef cfg oracle cu f tf)
            (fun x y : Unit => x = y) prog prog tprog hm
            prog.prog_defs tprog.prog_defs hm.1 Mem.empty m0 hmem
        · change Genv.find_symbol (Genv.globalenv tprog) tprog.prog_main = some b
          rw [CompCert4Lean.Common.Linking.match_program_main hm]
          rw [selection_symbols_preserved cfg oracle prog tprog
            (by exact ⟨hm.1, hm.2.1, hm.2.2⟩) prog.prog_main]
          exact hsym
        · exact htf
        · rw [sig_function_translated cfg oracle cu f tf hmatch]
          exact hsig
      · exact match_callstate cu f tf [] [] Cminor.Kstop CminorSel.Kstop m0 m0
          horder hmatch match_cont_stop
          CompCert4Lean.Common.Values.Val.lessdef_list_nil
          (selection_mem_extends_refl m0)

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Backend.Cminor
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.Selection
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Switch

variable [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
variable [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
variable [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
variable [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
variable (cfg : CompilerConfig) (oracle : SelectionOracle)

private theorem selection_sel_builtin_nolabel (hf : HelperFunctions) :
    ∀ (optid : Option ident) (ef : external_function) (args : List Cminor.expr),
      nolabel' (sel_builtin cfg
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate) optid ef args) := by
  letI : HelperFunctions := hf
  intro optid ef args lbl k
  cases ef with
  | EF_builtin name sg =>
      cases hbf : CompCert4Lean.Common.Builtins.lookup_builtin_function name sg with
      | none => simp [sel_builtin, sel_builtin_default, Sno_op, hbf, CminorSel.find_label]
      | some bf =>
          cases optid with
          | none => simp [sel_builtin, sel_builtin_default, Sno_op, hbf, CminorSel.find_label]
          | some id =>
              cases hknown : sel_known_builtin bf
                  (sel_exprlist
                    (binary64_certificate := binary64_certificate)
                    (binary32_certificate := binary32_certificate)
                    (binary64_inverse_certificate := binary64_inverse_certificate)
                    (binary32_inverse_certificate := binary32_inverse_certificate) cfg args) with
              | none => simp [sel_builtin, sel_builtin_default, Sno_op, hbf, hknown, CminorSel.find_label]
              | some a => simp [sel_builtin, sel_builtin_default, Sno_op, hbf, hknown, CminorSel.find_label]
  | _ => simp [sel_builtin, sel_builtin_default, Sno_op, CminorSel.find_label]

theorem find_label_commut : find_label_commutStatement cfg oracle := by
  intro prog cunit hf ki env lbl s kont k s' k' hcont hsel
  letI : HelperFunctions := hf
  induction s generalizing kont k s' k' with
  | Sskip =>
      cases hsel
      simp [Cminor.find_label, CminorSel.find_label]
  | Sassign id a =>
      cases hsel
      simp [Cminor.find_label, CminorSel.find_label]
  | Sstore chunk address value =>
      cases hsel
      simp [Cminor.find_label, CminorSel.find_label]
  | Scall optid sg callee args =>
      cases hclass : classify_call (prog_defmap cunit) callee
      case Call_default =>
        simp [Selection.sel_stmt, hclass] at hsel
        cases hsel
        simp [Cminor.find_label, CminorSel.find_label]
      case Call_imm id =>
        simp [Selection.sel_stmt, hclass] at hsel
        cases hsel
        simp [Cminor.find_label, CminorSel.find_label]
      case Call_builtin ef =>
        simp [Selection.sel_stmt, hclass] at hsel
        cases hsel
        simp only [Cminor.find_label]
        have hn := selection_sel_builtin_nolabel (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (binary64_inverse_certificate := binary64_inverse_certificate)
          (binary32_inverse_certificate := binary32_inverse_certificate)
          cfg hf optid ef args lbl k'
        simp [hn]
  | Stailcall sg callee args =>
      cases hclass : classify_call (prog_defmap cunit) callee
      case Call_default =>
        simp [Selection.sel_stmt, hclass] at hsel
        cases hsel
        simp [Cminor.find_label, CminorSel.find_label]
      case Call_imm id =>
        simp [Selection.sel_stmt, hclass] at hsel
        cases hsel
        simp [Cminor.find_label, CminorSel.find_label]
      case Call_builtin =>
        simp [Selection.sel_stmt, hclass] at hsel
        cases hsel
        simp [Cminor.find_label, CminorSel.find_label]
  | Sbuiltin optid ef args =>
      simp [Selection.sel_stmt] at hsel
      cases hsel
      simp only [Cminor.find_label]
      have hn := selection_sel_builtin_nolabel (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        cfg hf optid ef args lbl k'
      simp [hn]
  | Sseq s1 s2 ih1 ih2 =>
      cases hs2 : sel_stmt cfg oracle (prog_defmap cunit) ki env s2 kont with
      | Error msg => simp [Selection.sel_stmt, hs2] at hsel
      | OK s2' =>
        cases hs1 : sel_stmt cfg oracle (prog_defmap cunit) ki env s1 s2' with
        | Error msg => simp [Selection.sel_stmt, hs2, hs1] at hsel
        | OK s1' =>
          have hseq : s' = CminorSel.Sseq s1' s2' := by
            simpa [Selection.sel_stmt, hs2, hs1] using hsel.symm
          subst s'
          have hmc : match_cont cfg oracle prog cunit hf ki env
              (Cminor.Kseq s2 k) (CminorSel.Kseq s2' k') :=
            match_cont_seq cunit hf ki env s2 kont s2' k k' hs2 hcont
          cases hsrc : Cminor.find_label lbl s1 (Cminor.Kseq s2 k) with
          | some p =>
            rcases p with ⟨sx, kx⟩
            cases htgt : CminorSel.find_label lbl s1' (CminorSel.Kseq s2' k') with
            | some q =>
              rcases q with ⟨sy, ky⟩
              have hi := ih1 (kont := s2') (k := Cminor.Kseq s2 k)
                (s' := s1') (k' := CminorSel.Kseq s2' k') hmc hs1
              simpa [Cminor.find_label, CminorSel.find_label, hsrc, htgt] using hi
            | none =>
              have hi := ih1 (kont := s2') (k := Cminor.Kseq s2 k)
                (s' := s1') (k' := CminorSel.Kseq s2' k') hmc hs1
              have hfalse : False := by
                simpa [hsrc, htgt] using hi
              exact hfalse.elim
          | none =>
            cases htgt : CminorSel.find_label lbl s1' (CminorSel.Kseq s2' k') with
            | some q =>
              rcases q with ⟨sy, ky⟩
              have hi := ih1 (kont := s2') (k := Cminor.Kseq s2 k)
                (s' := s1') (k' := CminorSel.Kseq s2' k') hmc hs1
              have hfalse : False := by
                simpa [hsrc, htgt] using hi
              exact hfalse.elim
            | none =>
              cases hsrc2 : Cminor.find_label lbl s2 k with
              | some q =>
                rcases q with ⟨sx, kx⟩
                cases htgt2 : CminorSel.find_label lbl s2' k' with
                | some r =>
                  rcases r with ⟨sy, ky⟩
                  have hi := ih2 (kont := kont) (k := k) (s' := s2')
                    (k' := k') hcont hs2
                  simpa [Cminor.find_label, CminorSel.find_label, hsrc, htgt,
                    hsrc2, htgt2] using hi
                | none =>
                  have hi := ih2 (kont := kont) (k := k) (s' := s2')
                    (k' := k') hcont hs2
                  have hfalse : False := by
                    simpa [hsrc2, htgt2] using hi
                  exact hfalse.elim
              | none =>
                cases htgt2 : CminorSel.find_label lbl s2' k' with
                | some r =>
                  rcases r with ⟨sy, ky⟩
                  have hi := ih2 (kont := kont) (k := k) (s' := s2')
                    (k' := k') hcont hs2
                  have hfalse : False := by
                    simpa [hsrc2, htgt2] using hi
                  exact hfalse.elim
                | none =>
                  simp [Cminor.find_label, CminorSel.find_label, hsrc, htgt,
                    hsrc2, htgt2]
  | Sifthenelse cond ifso ifnot ih1 ih2 =>
      cases hifc : if_conversion cfg oracle ki env cond ifso ifnot kont with
      | some sf =>
          have hsf : s' = sf := by
            simpa [Selection.sel_stmt, hifc] using hsel.symm
          subst s'
          have hn := if_conversion_nolabel (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            (binary64_inverse_certificate := binary64_inverse_certificate)
            (binary32_inverse_certificate := binary32_inverse_certificate)
            cfg oracle hf ki env cond ifso ifnot kont sf hifc
          rcases hn with ⟨hn1, hn2, hns⟩
          simp [Cminor.find_label, hn1 lbl k, hn2 lbl k, hns lbl k']
      | none =>
          cases hs1 : sel_stmt cfg oracle (prog_defmap cunit) ki env ifso kont with
          | Error msg => simp [Selection.sel_stmt, hifc, hs1] at hsel
          | OK ifso' =>
            cases hs2 : sel_stmt cfg oracle (prog_defmap cunit) ki env ifnot kont with
            | Error msg => simp [Selection.sel_stmt, hifc, hs1, hs2] at hsel
            | OK ifnot' =>
              have hif : s' = CminorSel.Sifthenelse
                  (condexpr_of_expr (sel_expr cfg cond)) ifso' ifnot' := by
                simpa [Selection.sel_stmt, hifc, hs1, hs2] using hsel.symm
              subst s'
              cases hsrc : Cminor.find_label lbl ifso k with
              | some p =>
                rcases p with ⟨sx, kx⟩
                cases htgt : CminorSel.find_label lbl ifso' k' with
                | some q =>
                  rcases q with ⟨sy, ky⟩
                  have hi := ih1 (kont := kont) (k := k) (s' := ifso')
                    (k' := k') hcont hs1
                  simpa [Cminor.find_label, CminorSel.find_label, hsrc, htgt] using hi
                | none =>
                  have hi := ih1 (kont := kont) (k := k) (s' := ifso')
                    (k' := k') hcont hs1
                  have hfalse : False := by simpa [hsrc, htgt] using hi
                  exact hfalse.elim
              | none =>
                cases htgt : CminorSel.find_label lbl ifso' k' with
                | some q =>
                  rcases q with ⟨sy, ky⟩
                  have hi := ih1 (kont := kont) (k := k) (s' := ifso')
                    (k' := k') hcont hs1
                  have hfalse : False := by simpa [hsrc, htgt] using hi
                  exact hfalse.elim
                | none =>
                  cases hsrc2 : Cminor.find_label lbl ifnot k with
                  | some q =>
                    rcases q with ⟨sx, kx⟩
                    cases htgt2 : CminorSel.find_label lbl ifnot' k' with
                    | some r =>
                      rcases r with ⟨sy, ky⟩
                      have hi := ih2 (kont := kont) (k := k) (s' := ifnot')
                        (k' := k') hcont hs2
                      simpa [Cminor.find_label, CminorSel.find_label, hsrc, htgt,
                        hsrc2, htgt2] using hi
                    | none =>
                      have hi := ih2 (kont := kont) (k := k) (s' := ifnot')
                        (k' := k') hcont hs2
                      have hfalse : False := by simpa [hsrc2, htgt2] using hi
                      exact hfalse.elim
                  | none =>
                    cases htgt2 : CminorSel.find_label lbl ifnot' k' with
                    | some r =>
                      rcases r with ⟨sy, ky⟩
                      have hi := ih2 (kont := kont) (k := k) (s' := ifnot')
                        (k' := k') hcont hs2
                      have hfalse : False := by simpa [hsrc2, htgt2] using hi
                      exact hfalse.elim
                    | none =>
                      simp [Cminor.find_label, CminorSel.find_label, hsrc, htgt,
                        hsrc2, htgt2]
  | Sloop body ih =>
      cases hbody : sel_stmt cfg oracle (prog_defmap cunit) ki env body CminorSel.Sskip with
      | Error msg => simp [Selection.sel_stmt, hbody] at hsel
      | OK body' =>
          have hloop : s' = CminorSel.Sloop body' := by
            simpa [Selection.sel_stmt, hbody] using hsel.symm
          subst s'
          have hmc : match_cont cfg oracle prog cunit hf ki env
              (Cminor.Kseq (Cminor.Sloop body) k)
              (CminorSel.Kseq (CminorSel.Sloop body') k') :=
            match_cont_seq cunit hf ki env (Cminor.Sloop body) kont
              (CminorSel.Sloop body') k k' hsel hcont
          have hi := ih (kont := CminorSel.Sskip)
            (k := Cminor.Kseq (Cminor.Sloop body) k)
            (s' := body') (k' := CminorSel.Kseq (CminorSel.Sloop body') k') hmc hbody
          simpa [Cminor.find_label, CminorSel.find_label] using hi
  | Sblock body ih =>
      cases hbody : sel_stmt cfg oracle (prog_defmap cunit) ki env body kont with
      | Error msg => simp [Selection.sel_stmt, hbody] at hsel
      | OK body' =>
          have hblock : s' = CminorSel.Sblock body' := by
            simpa [Selection.sel_stmt, hbody] using hsel.symm
          subst s'
          have hmc : match_cont cfg oracle prog cunit hf ki env
              (Cminor.Kblock k) (CminorSel.Kblock k') :=
            match_cont_block cunit hf ki env k k' hcont
          have hi := ih (kont := kont) (k := Cminor.Kblock k)
            (s' := body') (k' := CminorSel.Kblock k') hmc hbody
          simpa [Cminor.find_label, CminorSel.find_label] using hi
  | Sexit depth =>
      cases hsel
      simp [Cminor.find_label, CminorSel.find_label]
  | Sswitch isLong arg cases default =>
      cases isLong with
      | false =>
          cases hvalid : validate_switch CompCert4Lean.Lib.Integers.Int.modulus default cases
              (compile_switch oracle CompCert4Lean.Lib.Integers.Int.modulus default cases) with
          | false => simp [Selection.sel_stmt, hvalid] at hsel
          | true =>
              simp [Selection.sel_stmt, hvalid] at hsel
              cases hsel
              simp [Cminor.find_label, CminorSel.find_label]
      | true =>
          cases hvalid : validate_switch CompCert4Lean.Lib.Integers.Int64.modulus default cases
              (compile_switch oracle CompCert4Lean.Lib.Integers.Int64.modulus default cases) with
          | false => simp [Selection.sel_stmt, hvalid] at hsel
          | true =>
              simp [Selection.sel_stmt, hvalid] at hsel
              cases hsel
              simp [Cminor.find_label, CminorSel.find_label]
  | Sreturn value =>
      cases value with
      | none =>
          simp [Selection.sel_stmt] at hsel
          cases hsel
          simp [Cminor.find_label, CminorSel.find_label]
      | some e =>
          simp [Selection.sel_stmt] at hsel
          cases hsel
          simp [Cminor.find_label, CminorSel.find_label]
  | Slabel label body ih =>
      cases hbody : sel_stmt cfg oracle (prog_defmap cunit) ki env body kont with
      | Error msg => simp [Selection.sel_stmt, hbody] at hsel
      | OK body' =>
          have hlabel : s' = CminorSel.Slabel label body' := by
            simpa [Selection.sel_stmt, hbody] using hsel.symm
          subst s'
          cases heq : ident_eq lbl label with
          | left hll =>
              simp only [Cminor.find_label, CminorSel.find_label, heq]
              exact ⟨kont, hbody, hcont⟩
          | right hll =>
              have hi := ih (kont := kont) (k := k) (s' := body')
                (k' := k') hcont hbody
              simpa [Cminor.find_label, CminorSel.find_label, heq] using hi
  | Sgoto label =>
      cases hsel
      simp [Cminor.find_label, CminorSel.find_label]

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Backend.Selection

theorem transf_program_match
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (oracle : SelectionOracle) :
    transf_program_matchStatement cfg oracle := by
  intro p tp h
  unfold CompCert4Lean.Backend.Selection.sel_program at h
  cases hget : get_helpers (prog_defmap p) with
  | Error msg =>
      simp [hget] at h
  | OK hf =>
      simp [hget] at h
      apply CompCert4Lean.Common.Linking.match_transform_partial_program_contextual
        (match_fundef := fun cunit f tf =>
          match_fundef cfg oracle cunit f tf)
        (transf_fun := sel_fundef cfg oracle
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (binary64_inverse_certificate := binary64_inverse_certificate)
          (binary32_inverse_certificate := binary32_inverse_certificate)
          (prog_defmap p) hf)
      · exact h
      · intro f tf htf
        exact ⟨hf, get_helpers_correct p hf hget, htf⟩

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

theorem symbols_preserved
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (oracle : SelectionOracle) :
    symbols_preservedStatement cfg oracle := by
  intro prog tprog hm id
  exact selection_symbols_preserved cfg oracle prog tprog hm id

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking

variable [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
variable [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
variable [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
variable [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
variable (cfg : CompilerConfig) (oracle : SelectionOracle)

theorem function_ptr_translated : function_ptr_translatedStatement cfg oracle := by
  intro prog tprog hmatch b f hfind
  unfold match_prog CompCert4Lean.Common.Linking.match_program at hmatch
  rcases Genv.find_funct_ptr_match CminorProgram CminorFundef Unit CminorSelFundef Unit
    (fun cu f tf => match_fundef cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) cu f tf) Eq
    prog prog tprog hmatch b f hfind with ⟨cu, tf, hfindtf, hmatchf, horder⟩
  exact ⟨cu, tf, hfindtf, hmatchf, horder⟩

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.Selection
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

theorem eval_load
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_loadStatement := by
  intro xi tprog sp e m le a v chunk v' heval hload
  cases v with
  | Vundef => simp [Mem.loadv] at hload
  | Vint n => simp [Mem.loadv] at hload
  | Vlong n => simp [Mem.loadv] at hload
  | Vfloat f => simp [Mem.loadv] at hload
  | Vsingle f => simp [Mem.loadv] at hload
  | Vptr b ofs =>
      have hzero :
          eval_addressing (Genv.globalenv tprog) sp (.Aindexed (zOfNat 0))
            [Vptr b ofs] = some (Vptr b ofs) := by
        simp [eval_addressing, eval_addressing64,
          CompCert4Lean.X86_64.Archi.ptr64, Val.addl,
          CompCert4Lean.Lib.Integers.Ptrofs.of_int64,
          CompCert4Lean.Lib.Integers.Int64.repr]
        rw [show CompCert4Lean.Lib.Integers.Ptrofs.repr
            (CompCert4Lean.Lib.Integers.Int64.unsigned
              (CompCert4Lean.Lib.Integers.WordCore.repr
                CompCert4Lean.Lib.Integers.Int64.wordsize (zOfNat 0))) =
            CompCert4Lean.Lib.Integers.Ptrofs.repr
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0 by rfl]
        exact selection_ptrofs_add_zero ofs
      have hfallback (a0 : CminorSel.expr)
          (ha0 : CminorSel.eval_expr xi (Genv.globalenv tprog) sp e m le a0 (Vptr b ofs))
          (haddr : CompCert4Lean.X86.SelectOp.addressing chunk a0 =
            (.Aindexed (zOfNat 0), Econs a0 Enil)) :
          CminorSel.eval_expr xi (Genv.globalenv tprog) sp e m le (load chunk a0) v' := by
        unfold CompCert4Lean.Backend.Selection.load
        rw [haddr]
        exact eval_expr.eval_Eload le chunk (.Aindexed (zOfNat 0))
          (Econs a0 Enil) [Vptr b ofs] (Vptr b ofs) v'
          (eval_exprlist.cons le a0 Enil (Vptr b ofs) [] ha0 (eval_exprlist.nil le))
          hzero hload
      cases hcase : addressing_match a with
      | addressing_case1 addr args =>
          apply hfallback _ heval
          simp [CompCert4Lean.X86.SelectOp.addressing, addressing_match,
            CompCert4Lean.X86_64.Archi.ptr64]
          rfl
      | addressing_case2 addr args =>
          by_cases hvalid : addressing_valid addr
          · cases heval with
            | eval_Eop le' op al vl vv hargs hop =>
                have hadd :
                    CompCert4Lean.X86.SelectOp.addressing chunk (Eop (.Oleal addr) args) =
                      (addr, args) := by
                  simp [CompCert4Lean.X86.SelectOp.addressing, addressing_match,
                    hvalid, CompCert4Lean.X86_64.Archi.ptr64]
                have haddr :
                    eval_addressing (Genv.globalenv tprog) sp addr vl =
                      some (Vptr b ofs) := by
                  change eval_addressing64 (Genv.globalenv tprog) sp addr vl =
                    some (Vptr b ofs)
                  change eval_addressing64 (Genv.globalenv tprog) sp addr vl =
                    some (Vptr b ofs) at hop
                  exact hop
                unfold CompCert4Lean.Backend.Selection.load
                rw [hadd]
                exact eval_expr.eval_Eload le chunk addr args vl (Vptr b ofs) v'
                  hargs haddr hload
          · apply hfallback _ heval
            simp [CompCert4Lean.X86.SelectOp.addressing, addressing_match, hvalid,
              CompCert4Lean.X86_64.Archi.ptr64]
            rfl
      | addressing_default _ =>
          apply hfallback _ heval
          unfold CompCert4Lean.X86.SelectOp.addressing
          cases a with
          | Eop op args =>
              cases op <;>
                simp [addressing_match] at hcase ⊢ <;>
                rfl
          | _ =>
              simp [addressing_match] at hcase ⊢ <;>
                rfl

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.Cminor
open CompCert4Lean.Backend.Selection
open CompCert4Lean.Lib.Integers

theorem expr_is_addrof_ident_correct : expr_is_addrof_ident_correctStatement := by
  intro e id h
  cases e with
  | Evar _ => simp [CompCert4Lean.Backend.Selection.expr_is_addrof_ident] at h
  | Econst c =>
      cases c with
      | Ointconst _ => simp [CompCert4Lean.Backend.Selection.expr_is_addrof_ident] at h
      | Ofloatconst _ => simp [CompCert4Lean.Backend.Selection.expr_is_addrof_ident] at h
      | Osingleconst _ => simp [CompCert4Lean.Backend.Selection.expr_is_addrof_ident] at h
      | Olongconst _ => simp [CompCert4Lean.Backend.Selection.expr_is_addrof_ident] at h
      | Oaddrsymbol id' ofs =>
          cases heq : Ptrofs.eq ofs Ptrofs.zero with
          | false => simp [CompCert4Lean.Backend.Selection.expr_is_addrof_ident, heq] at h
          | true =>
              simp [CompCert4Lean.Backend.Selection.expr_is_addrof_ident, heq] at h
              have hofs : ofs = Ptrofs.zero := by
                unfold CompCert4Lean.Lib.Integers.Ptrofs.eq
                  CompCert4Lean.Lib.Integers.WordCore.eq at heq
                apply CompCert4Lean.Lib.Integers.WordCore.ext
                exact of_decide_eq_true heq
              cases h
              cases hofs
              rfl
      | Oaddrstack _ => simp [CompCert4Lean.Backend.Selection.expr_is_addrof_ident] at h
  | Eunop _ _ => simp [CompCert4Lean.Backend.Selection.expr_is_addrof_ident] at h
  | Ebinop _ _ _ => simp [CompCert4Lean.Backend.Selection.expr_is_addrof_ident] at h
  | Eload _ _ => simp [CompCert4Lean.Backend.Selection.expr_is_addrof_ident] at h

end CompCert4Lean.Backend.Selectionproof


namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.Cminor
open CompCert4Lean.Backend.Selection
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Common.Linking

theorem classify_call_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    classify_call_correctStatement := by
  intro prog unit sp e m a v fd hlink hev hfd
  cases hcall : CompCert4Lean.Backend.Selection.expr_is_addrof_ident a with
  | none => simp [CompCert4Lean.Backend.Selection.classify_call, hcall]
  | some id =>
      have ha : a = Cminor.Econst (Cminor.Oaddrsymbol id Ptrofs.zero) :=
        expr_is_addrof_ident_correct a id hcall
      subst a
      cases hev with
      | eval_Econst cst v' heval =>
          cases hs : Genv.find_symbol (Genv.globalenv prog) id with
          | none =>
              have hv : v = Vundef := by
                simp [Cminor.eval_constant, Genv.symbol_address, hs] at heval
                exact heval.symm
              subst v
              exfalso
              simpa [Genv.find_funct] using hfd
          | some b =>
              have hv : v = Vptr b Ptrofs.zero := by
                simp [Cminor.eval_constant, Genv.symbol_address, hs] at heval
                exact heval.symm
              cases hg : PTree.get
                  (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
                  (prog_defmap unit) with
              | none =>
                  have hkind :
                      CompCert4Lean.Backend.Selection.classify_call (prog_defmap unit)
                        (Cminor.Econst (Cminor.Oaddrsymbol id Ptrofs.zero)) = Call_imm id := by
                    change (match
                      CompCert4Lean.Lib.Maps.PTree.get
                        (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
                        (prog_defmap unit) with
                      | some (.Gfun (.External ef)) =>
                          if ef_inline ef then Call_builtin ef else Call_imm id
                      | _ => Call_imm id) = Call_imm id
                    rw [hg]
                  rw [hkind]
                  exact ⟨b, hs, hv⟩
              | some gd =>
                  cases gd with
                  | Gvar gv =>
                      have hkind :
                          CompCert4Lean.Backend.Selection.classify_call (prog_defmap unit)
                            (Cminor.Econst (Cminor.Oaddrsymbol id Ptrofs.zero)) = Call_imm id := by
                        change (match
                          CompCert4Lean.Lib.Maps.PTree.get
                            (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
                            (prog_defmap unit) with
                          | some (.Gfun (.External ef0)) =>
                              if ef_inline ef0 then Call_builtin ef0 else Call_imm id
                          | _ => Call_imm id) = Call_imm id
                        rw [hg]
                      rw [hkind]
                      exact ⟨b, hs, hv⟩
                  | Gfun f =>
                      cases f with
                      | Internal fn =>
                          have hkind :
                              CompCert4Lean.Backend.Selection.classify_call (prog_defmap unit)
                                (Cminor.Econst (Cminor.Oaddrsymbol id Ptrofs.zero)) = Call_imm id := by
                            change (match
                          CompCert4Lean.Lib.Maps.PTree.get
                            (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
                            (prog_defmap unit) with
                          | some (.Gfun (.External ef0)) =>
                              if ef_inline ef0 then Call_builtin ef0 else Call_imm id
                          | _ => Call_imm id) = Call_imm id
                            rw [hg]
                          rw [hkind]
                          exact ⟨b, hs, hv⟩
                      | External ef =>
                          cases hi : ef_inline ef with
                          | false =>
                              have hkind :
                                  CompCert4Lean.Backend.Selection.classify_call (prog_defmap unit)
                                    (Cminor.Econst (Cminor.Oaddrsymbol id Ptrofs.zero)) = Call_imm id := by
                                change (match
                                  CompCert4Lean.Lib.Maps.PTree.get
                                    (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
                                    (prog_defmap unit) with
                                  | some (.Gfun (.External ef0)) =>
                                      if ef_inline ef0 then Call_builtin ef0 else Call_imm id
                                  | _ => Call_imm id) = Call_imm id
                                rw [hg]
                                simp [hi]
                              rw [hkind]
                              exact ⟨b, hs, hv⟩
                          | true =>
                              have hkind :
                                  CompCert4Lean.Backend.Selection.classify_call (prog_defmap unit)
                                    (Cminor.Econst (Cminor.Oaddrsymbol id Ptrofs.zero)) = Call_builtin ef := by
                                change (match
                                  CompCert4Lean.Lib.Maps.PTree.get
                                    (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
                                    (prog_defmap unit) with
                                  | some (.Gfun (.External ef0)) =>
                                      if ef_inline ef0 then Call_builtin ef0 else Call_imm id
                                  | _ => Call_imm id) = Call_builtin ef
                                rw [hg]
                                simp [hi]
                              rw [hkind]
                              rcases prog_defmap_linkorder_proof unit prog id
                                  (.Gfun (.External ef)) hlink hg with
                                ⟨gd2, hg2, hgd⟩
                              cases hgd with
                              | linkorder_def_fun fd1 fd2 hfd12 =>
                                  have hfun : Genv.find_funct_ptr (Genv.globalenv prog) b = some fd := by
                                    rw [← Genv.find_funct_find_funct_ptr]
                                    simpa [hv] using hfd
                                  have hdef : Genv.find_def (Genv.globalenv prog) b = some (.Gfun fd) :=
                                    (Genv.find_funct_ptr_iff (F := Cminor.fundef) (V := Unit)
                                      (ge := Genv.globalenv prog) (b := b) (f := fd)).mp hfun
                                  cases hfd12 with
                                  | linkorder_fundef_refl _ =>
                                      have hdef2 : Genv.find_def (Genv.globalenv prog) b =
                                          some (.Gfun (.External ef)) := by
                                        rcases (Genv.find_def_symbol (F := Cminor.fundef) (V := Unit)
                                          prog id (.Gfun (.External ef))).mp hg2 with
                                          ⟨b2, hs2, hdef2⟩
                                        have hs2' : PTree.get id (Genv.globalenv prog).genv_symb = some b2 := by
                                          simpa [Genv.find_symbol] using hs2
                                        have hs' : PTree.get id (Genv.globalenv prog).genv_symb = some b := by
                                          simpa [Genv.find_symbol] using hs
                                        have hb : b2 = b := Option.some.inj (hs2'.symm.trans hs')
                                        subst b2
                                        exact hdef2
                                      have hfd_eq : fd = .External ef := by
                                        have hh := Option.some.inj (hdef.symm.trans hdef2)
                                        cases hh
                                        rfl
                                      exact hfd_eq
                                  | linkorder_fundef_ext_int fn2 name sg =>
                                      simp [ef_inline] at hi

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.Selection
open CompCert4Lean.Common.Switch

theorem sel_switch_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    sel_switch_correctStatement := by
  intro xi tprog make_cmp_eq make_cmp_ltu make_sub make_to_int modulus R
    hEq hLt hSub hToInt
  intro dfl cases arg sp e m varg i t le hvalid harg hRi hRange
  have hvalidated := CompCert4Lean.Common.Switch.validate_switch_correct
    modulus (ZArith.BinInt.Z.le_lt_trans .Z0 i modulus hRange.1 hRange.2) dfl t cases hvalid
  rcases hvalidated with ⟨hWF, hAgree⟩
  apply eval_exitexpr.letBinding le arg
    (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int 0 t)
    varg (switch_target i dfl cases)
  · exact harg
  · apply sel_switch_correct_rec
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi tprog make_cmp_eq make_cmp_ltu make_sub make_to_int modulus R
      hEq hLt hSub hToInt sp e m varg i (switch_target i dfl cases) hRi t 0
      (varg :: le) hWF (by rfl) (hAgree i hRange)

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.Selection
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

private theorem switch_int_unsigned_repr_aux (n : Z)
    (hn : ZArith.BinInt.Z.le .Z0 n ∧ ZArith.BinInt.Z.lt n CompCert4Lean.Lib.Integers.Int.modulus) :
    CompCert4Lean.Lib.Integers.Int.unsigned (CompCert4Lean.Lib.Integers.Int.repr n) = n := by
  apply CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api n
  refine ⟨hn.1, ?_⟩
  have h := hn.2
  change intOfZ n < 4294967296 at h
  change intOfZ n ≤ 4294967295
  omega

private theorem switch_int_lessdef_bool_aux (b : Bool) (v : val)
    (h : Val.lessdef (Val.of_bool b) v) : v = Val.of_bool b := by
  cases b <;> simp only [Val.of_bool, Bool.false_eq_true, if_false, if_true] at h ⊢ <;>
    cases h <;> rfl

theorem sel_switch_int_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    sel_switch_int_correctStatement := by
  intro xi tprog dfl cases arg sp e m i t le hvalid harg
  have hConst (n : int) (sp : val) (e : Env) (m : mem) (le : letenv) :
      eval_expr xi (Genv.globalenv tprog) sp e m le (.Eop (.Ointconst n) .Enil) (.Vint n) :=
    eval_expr.eval_Eop le (.Ointconst n) .Enil [] (.Vint n) (eval_exprlist.nil le) rfl
  refine sel_switch_correct xi tprog _ _ _ _ CompCert4Lean.Lib.Integers.Int.modulus Rint
    ?_ ?_ ?_ ?_ dfl cases arg sp e m (.Vint i) (CompCert4Lean.Lib.Integers.Int.unsigned i) t le
    hvalid harg (Rint.intro i) (CompCert4Lean.Lib.Integers.Int.unsigned_range_proof i)
  · intro sp e m le a v i n heval hR hn
    cases hR with
    | intro j =>
        obtain ⟨v', he, hv⟩ := CompCert4Lean.X86.SelectOpproof.eval_comp
          xi (Genv.globalenv tprog) sp e m .Ceq le a (.Vint j)
          (.Eop (.Ointconst (CompCert4Lean.Lib.Integers.Int.repr n)) .Enil) (.Vint (CompCert4Lean.Lib.Integers.Int.repr n))
          heval (hConst (CompCert4Lean.Lib.Integers.Int.repr n) sp e m le)
        have hb : CompCert4Lean.Lib.Integers.Int.eq j (CompCert4Lean.Lib.Integers.Int.repr n) = proj_sumbool (zeq (CompCert4Lean.Lib.Integers.Int.unsigned j) n) := by
          change decide (CompCert4Lean.Lib.Integers.Int.unsigned j = CompCert4Lean.Lib.Integers.Int.unsigned (CompCert4Lean.Lib.Integers.Int.repr n)) = _
          rw [switch_int_unsigned_repr_aux n hn]
          cases h : zeq (CompCert4Lean.Lib.Integers.Int.unsigned j) n with
          | left hEq => simp [proj_sumbool, hEq]
          | right hNe => simp [proj_sumbool, hNe]
        have hs : Val.cmp .Ceq (.Vint j) (.Vint (CompCert4Lean.Lib.Integers.Int.repr n)) =
            Val.of_bool (proj_sumbool (zeq (CompCert4Lean.Lib.Integers.Int.unsigned j) n)) := by
          change Val.of_optbool (some (CompCert4Lean.Lib.Integers.Int.eq j (CompCert4Lean.Lib.Integers.Int.repr n))) = _
          rw [hb]
          cases proj_sumbool (zeq (CompCert4Lean.Lib.Integers.Int.unsigned j) n) <;> rfl
        rw [hs] at hv
        rw [switch_int_lessdef_bool_aux _ _ hv] at he
        exact he
  · intro sp e m le a v i n heval hR hn
    cases hR with
    | intro j =>
        obtain ⟨v', he, hv⟩ := CompCert4Lean.X86.SelectOpproof.eval_compu
          xi (Genv.globalenv tprog) sp e m .Clt le a (.Vint j)
          (.Eop (.Ointconst (CompCert4Lean.Lib.Integers.Int.repr n)) .Enil) (.Vint (CompCert4Lean.Lib.Integers.Int.repr n))
          heval (hConst (CompCert4Lean.Lib.Integers.Int.repr n) sp e m le)
        have hb : CompCert4Lean.Lib.Integers.Int.ltu j (CompCert4Lean.Lib.Integers.Int.repr n) =
            proj_sumbool (CompCert4Lean.Lib.Coqlib.zlt (CompCert4Lean.Lib.Integers.Int.unsigned j) n) := by
          have hu := switch_int_unsigned_repr_aux n hn
          cases h : CompCert4Lean.Lib.Coqlib.zlt (CompCert4Lean.Lib.Integers.Int.unsigned j) n with
          | left hLt =>
              change CompCert4Lean.Lib.Integers.Int.ltu j (CompCert4Lean.Lib.Integers.Int.repr n) = true
              have hRev : CompCert4Lean.Lib.Integers.Int.ltu
                  (CompCert4Lean.Lib.Integers.Int.repr n) j = false := by
                cases hr : CompCert4Lean.Lib.Integers.Int.ltu
                    (CompCert4Lean.Lib.Integers.Int.repr n) j with
                | false => rfl
                | true =>
                    have hrange := (CompCert4Lean.Lib.Integers.Int.ltu_inv_proof _ _ hr).2
                    rw [hu] at hrange
                    exact False.elim (_root_.Int.lt_asymm hLt hrange)
              have hNe : CompCert4Lean.Lib.Integers.Int.eq j
                  (CompCert4Lean.Lib.Integers.Int.repr n) = false := by
                change decide (CompCert4Lean.Lib.Integers.Int.unsigned j =
                  CompCert4Lean.Lib.Integers.Int.unsigned (CompCert4Lean.Lib.Integers.Int.repr n)) = false
                rw [hu]
                have hneq : CompCert4Lean.Lib.Integers.Int.unsigned j ≠ n := by
                  intro heq
                  rw [heq] at hLt
                  exact _root_.Int.lt_irrefl _ hLt
                simp [hneq]
              have hNot := CompCert4Lean.Lib.Integers.Int.not_ltu_proof j
                (CompCert4Lean.Lib.Integers.Int.repr n)
              simpa [hRev, hNe] using hNot.symm
          | right hGe =>
              change CompCert4Lean.Lib.Integers.Int.ltu j (CompCert4Lean.Lib.Integers.Int.repr n) = false
              cases hl : CompCert4Lean.Lib.Integers.Int.ltu j (CompCert4Lean.Lib.Integers.Int.repr n) with
              | false => rfl
              | true =>
                  have hLt := (CompCert4Lean.Lib.Integers.Int.ltu_inv_proof _ _ hl).2
                  rw [hu] at hLt
                  exact False.elim ((_root_.Int.not_lt.mpr hGe) hLt)
        have hs : Val.cmpu (Mem.valid_pointer m) .Clt (.Vint j) (.Vint (CompCert4Lean.Lib.Integers.Int.repr n)) =
            Val.of_bool (proj_sumbool (CompCert4Lean.Lib.Coqlib.zlt (CompCert4Lean.Lib.Integers.Int.unsigned j) n)) := by
          change Val.of_optbool (some (CompCert4Lean.Lib.Integers.Int.ltu j (CompCert4Lean.Lib.Integers.Int.repr n))) = _
          rw [hb]
          cases proj_sumbool (CompCert4Lean.Lib.Coqlib.zlt (CompCert4Lean.Lib.Integers.Int.unsigned j) n) <;> rfl
        rw [hs] at hv
        rw [switch_int_lessdef_bool_aux _ _ hv] at he
        exact he
  · intro sp e m le a v i n heval hR hn
    cases hR with
    | intro j =>
        obtain ⟨v', he, hv⟩ := CompCert4Lean.X86.SelectOpproof.eval_sub
          xi (Genv.globalenv tprog) sp e m le a (.Vint j)
          (.Eop (.Ointconst (CompCert4Lean.Lib.Integers.Int.repr n)) .Enil) (.Vint (CompCert4Lean.Lib.Integers.Int.repr n))
          heval (hConst (CompCert4Lean.Lib.Integers.Int.repr n) sp e m le)
        change Val.lessdef (.Vint (CompCert4Lean.Lib.Integers.Int.sub j (CompCert4Lean.Lib.Integers.Int.repr n))) v' at hv
        cases hv
        refine ⟨_, he, ?_⟩
        have hu : CompCert4Lean.Lib.Integers.Int.unsigned (CompCert4Lean.Lib.Integers.Int.sub j (CompCert4Lean.Lib.Integers.Int.repr n)) =
            ZArith.BinInt.Z.modulo (ZArith.BinInt.Z.sub (CompCert4Lean.Lib.Integers.Int.unsigned j) n) CompCert4Lean.Lib.Integers.Int.modulus := by
          change CompCert4Lean.Lib.Integers.Int.unsigned (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.sub
            (CompCert4Lean.Lib.Integers.Int.unsigned j) (CompCert4Lean.Lib.Integers.Int.unsigned (CompCert4Lean.Lib.Integers.Int.repr n)))) = _
          rw [CompCert4Lean.Lib.Integers.Int.unsigned_repr_eq_proof, switch_int_unsigned_repr_aux n hn]
        rw [← hu]
        exact Rint.intro _
  · intro sp e m le a v i heval hR
    refine ⟨v, heval, ?_⟩
    cases hR with
    | intro j =>
        rw [ZArith.BinInt.Z.mod_small _ _ (CompCert4Lean.Lib.Integers.Int.unsigned_range_proof j)]
        exact Rint.intro j

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem selection_is_longconst_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (prog : CompCert4Lean.Backend.CminorSel.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (le : letenv) (a : expr) (x : val) (n : CompCert4Lean.Lib.Integers.Int64.int) :
    is_longconst a = some n →
    eval_expr xi (Genv.globalenv prog) sp e m le a x → x = .Vlong n := by
  intro hconst heval
  have ha : a = Eop (Olongconst n) Enil := by
    cases a with
    | Evar id => simp [is_longconst] at hconst
    | Eop op args =>
        cases op <;> cases args <;> simp [is_longconst] at hconst ⊢ <;>
          cases hconst <;> rfl
    | Eload chunk addr args => simp [is_longconst] at hconst
    | Econdition c b d => simp [is_longconst] at hconst
    | Elet b d => simp [is_longconst] at hconst
    | Eletvar i => simp [is_longconst] at hconst
    | Ebuiltin ef args => simp [is_longconst] at hconst
    | Eexternal id sg args => simp [is_longconst] at hconst
  subst a
  cases heval with
  | eval_Eop _ _ _ vl _ hargs hop =>
      cases hargs
      change some (.Vlong n) = some x at hop
      cases hop
      rfl

private theorem selection_cmpl_result
    (c : CompCert4Lean.Lib.Integers.comparison) (x y v : val)
    (h : Val.cmpl c x y = some v) :
    some (Val.of_optbool (Val.cmpl_bool c x y)) = some v := by
  unfold Val.cmpl at h
  cases hc : Val.cmpl_bool c x y with
  | none => simp [hc] at h
  | some bv =>
      simp [hc] at h
      rw [← h]
      cases bv <;> rfl

private theorem selection_swap_cmpl_bool
    (c : CompCert4Lean.Lib.Integers.comparison) (x y : val) :
    Val.cmpl_bool (swap_comparison c) x y = Val.cmpl_bool c y x := by
  cases c <;> cases x <;> cases y <;>
    simp [Val.cmpl_bool, swap_comparison, CompCert4Lean.Lib.Integers.Int64.cmp, WordCore.cmp,
      WordCore.eq, eq_comm]

private theorem selection_eval_cmpl
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (prog : CompCert4Lean.Backend.CminorSel.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (c : CompCert4Lean.Lib.Integers.comparison) (le : letenv) (a : expr) (x : val)
    (b : expr) (y v : val) :
    eval_expr xi (Genv.globalenv prog) sp e m le a x →
    eval_expr xi (Genv.globalenv prog) sp e m le b y →
    Val.cmpl c x y = some v →
    eval_expr xi (Genv.globalenv prog) sp e m le (cmpl c a b) v := by
  intro ha hb hv
  unfold cmpl
  cases hca : is_longconst a with
  | none =>
      cases hcb : is_longconst b with
      | none =>
          simp only [hca, hcb]
          exact eval_expr.eval_Eop le (Ocmp (Ccompl c))
            (Econs a (Econs b Enil)) [x, y] v
            (eval_exprlist.cons le a (Econs b Enil) x [y] ha
              (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le)))
            (selection_cmpl_result c x y v hv)
      | some n2 =>
          have hy : y = .Vlong n2 :=
            selection_is_longconst_sound xi prog sp e m le b y n2 hcb hb
          subst y
          simp only [hca, hcb]
          exact eval_expr.eval_Eop le (Ocmp (Ccomplimm c n2))
            (Econs a Enil) [x] v
            (eval_exprlist.cons le a Enil x [] ha (eval_exprlist.nil le))
            (selection_cmpl_result c x (.Vlong n2) v hv)
  | some n1 =>
      have hx : x = .Vlong n1 :=
        selection_is_longconst_sound xi prog sp e m le a x n1 hca ha
      subst x
      cases hcb : is_longconst b with
      | none =>
          simp only [hca, hcb]
          apply eval_expr.eval_Eop le (Ocmp (Ccomplimm (swap_comparison c) n1))
            (Econs b Enil) [y] v
            (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))
          change some (Val.of_optbool
            (Val.cmpl_bool (swap_comparison c) y (.Vlong n1))) = some v
          rw [selection_swap_cmpl_bool]
          exact selection_cmpl_result c (.Vlong n1) y v hv
      | some n2 =>
          have hy : y = .Vlong n2 :=
            selection_is_longconst_sound xi prog sp e m le b y n2 hcb hb
          subst y
          simp only [hca, hcb]
          apply eval_expr.eval_Eop le (Ointconst
            (if CompCert4Lean.Lib.Integers.Int64.cmp c n1 n2 then Int.one else Int.zero)) Enil [] v
            (eval_exprlist.nil le)
          unfold Val.cmpl Val.cmpl_bool at hv
          simp only [Option.map_some] at hv
          rw [← hv]
          cases CompCert4Lean.Lib.Integers.Int64.cmp c n1 n2 <;> rfl

private theorem selection_cmplu_result
    (valid : block → CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z → Bool) (c : CompCert4Lean.Lib.Integers.comparison) (x y v : val)
    (h : Val.cmplu valid c x y = some v) :
    some (Val.of_optbool (Val.cmplu_bool valid c x y)) = some v := by
  unfold Val.cmplu at h
  cases hc : Val.cmplu_bool valid c x y with
  | none => simp [hc] at h
  | some bv =>
      simp [hc] at h
      rw [← h]
      cases bv <;> rfl

private theorem selection_swap_int64_cmpu
    (c : CompCert4Lean.Lib.Integers.comparison) (x y : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.cmpu (swap_comparison c) x y = CompCert4Lean.Lib.Integers.Int64.cmpu c y x := by
  cases c <;>
    simp [CompCert4Lean.Lib.Integers.Int64.cmpu, WordCore.cmpu, swap_comparison, WordCore.eq, eq_comm]

private theorem selection_swap_cmplu_bool_long
    (valid : block → CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z → Bool) (c : CompCert4Lean.Lib.Integers.comparison) (n : CompCert4Lean.Lib.Integers.Int64.int) (y : val) :
    Val.cmplu_bool valid (swap_comparison c) y (.Vlong n) =
      Val.cmplu_bool valid c (.Vlong n) y := by
  cases y with
  | Vlong y => exact congrArg some (selection_swap_int64_cmpu c y n)
  | Vundef => cases c <;> rfl
  | Vint y => cases c <;> rfl
  | Vfloat y => cases c <;> rfl
  | Vsingle y => cases c <;> rfl
  | Vptr b ofs =>
      cases c <;>
        simp [Val.cmplu_bool, Val.cmp_different_blocks, swap_comparison]

private theorem selection_eval_cmplu
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (prog : CompCert4Lean.Backend.CminorSel.program)
    (sp : val) (e : CompCert4Lean.Backend.Cminor.env) (m : mem)
    (c : CompCert4Lean.Lib.Integers.comparison) (le : letenv) (a : expr) (x : val)
    (b : expr) (y v : val) :
    eval_expr xi (Genv.globalenv prog) sp e m le a x →
    eval_expr xi (Genv.globalenv prog) sp e m le b y →
    Val.cmplu (fun b ofs => Mem.valid_pointer m b ofs) c x y = some v →
    eval_expr xi (Genv.globalenv prog) sp e m le (cmplu c a b) v := by
  intro ha hb hv
  unfold cmplu
  cases hca : is_longconst a with
  | none =>
      cases hcb : is_longconst b with
      | none =>
          simp only [hca, hcb]
          exact eval_expr.eval_Eop le (Ocmp (Ccomplu c))
            (Econs a (Econs b Enil)) [x, y] v
            (eval_exprlist.cons le a (Econs b Enil) x [y] ha
              (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le)))
            (selection_cmplu_result (fun b ofs => Mem.valid_pointer m b ofs)
              c x y v hv)
      | some n2 =>
          have hy : y = .Vlong n2 :=
            selection_is_longconst_sound xi prog sp e m le b y n2 hcb hb
          subst y
          simp only [hca, hcb]
          exact eval_expr.eval_Eop le (Ocmp (Ccompluimm c n2))
            (Econs a Enil) [x] v
            (eval_exprlist.cons le a Enil x [] ha (eval_exprlist.nil le))
            (selection_cmplu_result (fun b ofs => Mem.valid_pointer m b ofs)
              c x (.Vlong n2) v hv)
  | some n1 =>
      have hx : x = .Vlong n1 :=
        selection_is_longconst_sound xi prog sp e m le a x n1 hca ha
      subst x
      cases hcb : is_longconst b with
      | none =>
          simp only [hca, hcb]
          apply eval_expr.eval_Eop le (Ocmp (Ccompluimm (swap_comparison c) n1))
            (Econs b Enil) [y] v
            (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))
          change some (Val.of_optbool
            (Val.cmplu_bool (Mem.valid_pointer m) (swap_comparison c) y
              (.Vlong n1))) = some v
          rw [selection_swap_cmplu_bool_long
            (valid := fun b ofs => Mem.valid_pointer m b ofs)]
          exact selection_cmplu_result (fun b ofs => Mem.valid_pointer m b ofs)
            c (.Vlong n1) y v hv
      | some n2 =>
          have hy : y = .Vlong n2 :=
            selection_is_longconst_sound xi prog sp e m le b y n2 hcb hb
          subst y
          simp only [hca, hcb]
          apply eval_expr.eval_Eop le (Ointconst
            (if CompCert4Lean.Lib.Integers.Int64.cmpu c n1 n2 then Int.one else Int.zero)) Enil [] v
            (eval_exprlist.nil le)
          unfold Val.cmplu Val.cmplu_bool at hv
          simp only [Option.map_some] at hv
          rw [← hv]
          cases CompCert4Lean.Lib.Integers.Int64.cmpu c n1 n2 <;> rfl


open Lean Elab Tactic Meta

private theorem selection_int64_unsigned_repr_eq_exact (x : Z) :
    CompCert4Lean.Lib.Integers.Int64.unsigned (CompCert4Lean.Lib.Integers.Int64.repr x) = ZArith.BinInt.Z.modulo x CompCert4Lean.Lib.Integers.Int64.modulus := by
  run_tac
    let n := Name.mkSimple "_private" |>.str "CompCert4Lean" |>.str "Lib" |>.str "Integers"
      |>.num 0 |>.str "CompCert4Lean" |>.str "Lib" |>.str "Integers"
      |>.str "Int64" |>.str "suffix_int64_unsigned_repr_eq_exact"
    let ident := Lean.mkIdent n
    let arg := Lean.mkIdent `x
    evalTactic (← `(tactic| exact $ident $arg))

private theorem selection_int64_mod_int (x : Z) :
    intOfZ (ZArith.BinInt.Z.modulo x CompCert4Lean.Lib.Integers.Int64.modulus) =
      intOfZ x % intOfZ CompCert4Lean.Lib.Integers.Int64.modulus := by
  run_tac
    let env ← getEnv
    let some (n, _) := env.constants.toList.find?
        (fun (n, _) => (toString n).endsWith "X86.Op.suffix64_mod_int")
      | throwError "frozen modular arithmetic helper not found"
    let ident := Lean.mkIdent n
    let arg := Lean.mkIdent `x
    evalTactic (← `(tactic| exact $ident $arg))

private theorem selection_int64_unsigned_range (i : int64) :
    ZArith.BinInt.Z.le .Z0 (CompCert4Lean.Lib.Integers.Int64.unsigned i) ∧
      ZArith.BinInt.Z.lt (CompCert4Lean.Lib.Integers.Int64.unsigned i) CompCert4Lean.Lib.Integers.Int64.modulus := by
  constructor
  · have h := i.intrange.1
    change (-1 : _root_.Int) < intOfZ (CompCert4Lean.Lib.Integers.Int64.unsigned i) at h
    change 0 ≤ intOfZ (CompCert4Lean.Lib.Integers.Int64.unsigned i)
    omega
  · exact i.intrange.2

private theorem selection_int64_unsigned_repr_small (n : Z)
    (hn : ZArith.BinInt.Z.le .Z0 n ∧ ZArith.BinInt.Z.lt n CompCert4Lean.Lib.Integers.Int64.modulus) :
    CompCert4Lean.Lib.Integers.Int64.unsigned (CompCert4Lean.Lib.Integers.Int64.repr n) = n := by
  rw [selection_int64_unsigned_repr_eq_exact]
  exact ZArith.BinInt.Z.mod_small _ _ hn

private theorem selection_int64_repr_unsigned (i : int64) :
    CompCert4Lean.Lib.Integers.Int64.repr (CompCert4Lean.Lib.Integers.Int64.unsigned i) = i := by
  apply WordCore.ext
  exact selection_int64_unsigned_repr_small _ (selection_int64_unsigned_range i)

private theorem selection_int64_repr_signed (i : int64) :
    CompCert4Lean.Lib.Integers.Int64.repr (CompCert4Lean.Lib.Integers.Int64.signed i) = i := by
  apply WordCore.ext
  change CompCert4Lean.Lib.Integers.Int64.unsigned (CompCert4Lean.Lib.Integers.Int64.repr (CompCert4Lean.Lib.Integers.Int64.signed i)) = CompCert4Lean.Lib.Integers.Int64.unsigned i
  rw [selection_int64_unsigned_repr_eq_exact]
  apply intOfZ_injective
  rw [selection_int64_mod_int]
  have hu := selection_int64_unsigned_range i
  change 0 ≤ intOfZ (CompCert4Lean.Lib.Integers.Int64.unsigned i) ∧
    intOfZ (CompCert4Lean.Lib.Integers.Int64.unsigned i) < intOfZ CompCert4Lean.Lib.Integers.Int64.modulus at hu
  change intOfZ (WordCore.signed i) % intOfZ CompCert4Lean.Lib.Integers.Int64.modulus = _
  unfold WordCore.signed
  dsimp
  run_tac
    for suffix in ["CompCert4Lean.Lib.Integers.zltSelect",
        "CompCert4Lean.Lib.Integers.sumboolSelect"] do
      let env ← getEnv
      let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith suffix)
        | throwError "frozen comparison helper not found"
      let ident := Lean.mkIdent n
      evalTactic (← `(tactic| unfold $ident))
  split
  · exact _root_.Int.emod_eq_of_lt hu.1 hu.2
  · change intOfZ (ZArith.BinInt.Z.sub
      (CompCert4Lean.Lib.Integers.Int64.unsigned i)
      CompCert4Lean.Lib.Integers.Int64.modulus) %
        intOfZ CompCert4Lean.Lib.Integers.Int64.modulus = _
    simp [ZArith.BinInt.Z.sub, intOfZ_zOfInt, _root_.Int.sub_emod,
      _root_.Int.emod_eq_of_lt hu.1 hu.2]

private theorem selection_int64_add_comm (i j : int64) :
    CompCert4Lean.Lib.Integers.Int64.add i j = CompCert4Lean.Lib.Integers.Int64.add j i := by
  change CompCert4Lean.Lib.Integers.Int64.repr (ZArith.BinInt.Z.add (CompCert4Lean.Lib.Integers.Int64.unsigned i) (CompCert4Lean.Lib.Integers.Int64.unsigned j)) =
    CompCert4Lean.Lib.Integers.Int64.repr (ZArith.BinInt.Z.add (CompCert4Lean.Lib.Integers.Int64.unsigned j) (CompCert4Lean.Lib.Integers.Int64.unsigned i))
  congr 1
  apply intOfZ_injective
  simp [ZArith.BinInt.Z.add, _root_.Int.add_comm]

private theorem selection_int64_add_zero (i : int64) :
    CompCert4Lean.Lib.Integers.Int64.add i CompCert4Lean.Lib.Integers.Int64.zero = i := by
  change CompCert4Lean.Lib.Integers.Int64.repr (ZArith.BinInt.Z.add (CompCert4Lean.Lib.Integers.Int64.unsigned i) .Z0) = i
  have h : ZArith.BinInt.Z.add (CompCert4Lean.Lib.Integers.Int64.unsigned i) .Z0 = CompCert4Lean.Lib.Integers.Int64.unsigned i := by
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
    change intOfZ _ + 0 = intOfZ _
    omega
  rw [h]
  exact selection_int64_repr_unsigned i

private theorem selection_int64_sub_add_neg (i j : int64) :
    CompCert4Lean.Lib.Integers.Int64.sub i j = CompCert4Lean.Lib.Integers.Int64.add i (CompCert4Lean.Lib.Integers.Int64.neg j) := by
  apply WordCore.ext
  change CompCert4Lean.Lib.Integers.Int64.unsigned (CompCert4Lean.Lib.Integers.Int64.repr (ZArith.BinInt.Z.sub (CompCert4Lean.Lib.Integers.Int64.unsigned i)
      (CompCert4Lean.Lib.Integers.Int64.unsigned j))) =
    CompCert4Lean.Lib.Integers.Int64.unsigned (CompCert4Lean.Lib.Integers.Int64.repr (ZArith.BinInt.Z.add (CompCert4Lean.Lib.Integers.Int64.unsigned i)
      (CompCert4Lean.Lib.Integers.Int64.unsigned (CompCert4Lean.Lib.Integers.Int64.repr (ZArith.BinInt.Z.opp (CompCert4Lean.Lib.Integers.Int64.unsigned j))))))
  rw [selection_int64_unsigned_repr_eq_exact, selection_int64_unsigned_repr_eq_exact,
    selection_int64_unsigned_repr_eq_exact]
  apply intOfZ_injective
  simp only [selection_int64_mod_int, ZArith.BinInt.Z.sub,
    ZArith.BinInt.Z.add, ZArith.BinInt.Z.opp, intOfZ_zOfInt]
  rw [_root_.Int.add_emod, _root_.Int.emod_emod]
  rw [_root_.Int.sub_eq_add_neg, _root_.Int.add_emod]

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.Selection
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong
open Lean Elab Tactic Meta

private theorem selection_eval_addlimm_long
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (prog : CminorSelProgram)
    (sp : val) (e : Env) (m : mem) (le : letenv)
    (a : expr) (i n : int64)
    (ha : eval_expr xi (Genv.globalenv prog) sp e m le a (.Vlong i)) :
    eval_expr xi (Genv.globalenv prog) sp e m le (addlimm n a)
      (.Vlong (CompCert4Lean.Lib.Integers.Int64.add i n)) := by
  by_cases hz : CompCert4Lean.Lib.Integers.Int64.eq n
      CompCert4Lean.Lib.Integers.Int64.zero = true
  · have hn : n = CompCert4Lean.Lib.Integers.Int64.zero := by
      apply WordCore.ext
      exact of_decide_eq_true hz
    subst n
    simpa [addlimm, hz, selection_int64_add_zero] using ha
  · unfold addlimm
    rw [if_neg hz]
    cases hc : addlimm_match a with
    | addlimm_case1 j =>
        have hij : i = j := by
          have h := selection_is_longconst_sound xi prog sp e m le
            (Eop (Olongconst j) Enil) (.Vlong i) j rfl ha
          exact val.Vlong.inj h
        subst i
        rw [selection_int64_add_comm]
        exact eval_expr.eval_Eop le (Olongconst _) Enil [] _
          (eval_exprlist.nil le) rfl
    | addlimm_case2 addr args =>
        cases ha with
        | eval_Eop le' op al vl v hargs hop =>
            change eval_addressing64 (Genv.globalenv prog) sp addr vl =
              some (.Vlong i) at hop
            have hnew := eval_offset_addressing_total_64
              (F := CompCert4Lean.Backend.CminorSel.fundef) (V := Unit)
              (Genv.globalenv prog) sp addr vl
              (CompCert4Lean.Lib.Integers.Int64.signed n) (.Vlong i) hop
            simp only [hc]
            apply eval_expr.eval_Eop le
              (Oleal (offset_addressing_total addr
                (CompCert4Lean.Lib.Integers.Int64.signed n))) args vl _ hargs
            change eval_addressing64 (Genv.globalenv prog) sp
              (offset_addressing_total addr
                (CompCert4Lean.Lib.Integers.Int64.signed n)) vl = _
            simpa only [selection_int64_repr_signed, Val.addl] using hnew
    | addlimm_default a' =>
        simp only [hc]
        apply eval_expr.eval_Eop le
          (Oleal (Aindexed (CompCert4Lean.Lib.Integers.Int64.signed n)))
          (Econs a Enil) [.Vlong i] _
          (eval_exprlist.cons le a Enil (.Vlong i) [] ha (eval_exprlist.nil le))
        change some (Val.addl (.Vlong i) (.Vlong
          (CompCert4Lean.Lib.Integers.Int64.repr
            (CompCert4Lean.Lib.Integers.Int64.signed n)))) = _
        rw [selection_int64_repr_signed]
        rfl

private theorem selection_int64_ltu_repr (j : int64) (n : Z)
    (hn : ZArith.BinInt.Z.le .Z0 n ∧
      ZArith.BinInt.Z.lt n CompCert4Lean.Lib.Integers.Int64.modulus) :
    CompCert4Lean.Lib.Integers.Int64.ltu j
        (CompCert4Lean.Lib.Integers.Int64.repr n) =
      proj_sumbool (CompCert4Lean.Lib.Coqlib.zlt
        (CompCert4Lean.Lib.Integers.Int64.unsigned j) n) := by
  unfold CompCert4Lean.Lib.Integers.Int64.ltu WordCore.ltu
  run_tac
    for suffix in ["CompCert4Lean.Lib.Integers.zltSelect",
        "CompCert4Lean.Lib.Integers.sumboolSelect"] do
      let env ← getEnv
      let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith suffix)
        | throwError "frozen comparison helper not found"
      let ident := Lean.mkIdent n
      evalTactic (← `(tactic| unfold $ident))
  have hu := selection_int64_unsigned_repr_small n hn
  change WordCore.unsigned (CompCert4Lean.Lib.Integers.Int64.repr n) = n at hu
  rw [hu]

  unfold CompCert4Lean.Lib.Integers.Int64.unsigned
  cases CompCert4Lean.Lib.Coqlib.zlt (WordCore.unsigned j) n <;> rfl

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.Selection
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong

 theorem sel_switch_long_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    sel_switch_long_correctStatement := by
  intro xi tprog dfl cases arg sp e m i t le hvalid harg
  have hConst (n : int64) (sp : val) (e : Env) (m : mem) (le : letenv) :
      eval_expr xi (Genv.globalenv tprog) sp e m le (longconst n) (.Vlong n) :=
    eval_expr.eval_Eop le (.Olongconst n) .Enil [] (.Vlong n) (eval_exprlist.nil le) rfl
  refine sel_switch_correct xi tprog _ _ _ _ CompCert4Lean.Lib.Integers.Int64.modulus Rlong
    ?_ ?_ ?_ ?_ dfl cases arg sp e m (.Vlong i)
    (CompCert4Lean.Lib.Integers.Int64.unsigned i) t le
    hvalid harg (Rlong.intro i) (selection_int64_unsigned_range i)
  · intro sp e m le a v i n heval hR hn
    cases hR with
    | intro j =>
        apply selection_eval_cmpl xi tprog sp e m .Ceq le a (.Vlong j)
          (longconst (CompCert4Lean.Lib.Integers.Int64.repr n))
          (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr n)) _ heval
          (hConst (CompCert4Lean.Lib.Integers.Int64.repr n) sp e m le)
        have hb : CompCert4Lean.Lib.Integers.Int64.eq j
            (CompCert4Lean.Lib.Integers.Int64.repr n) =
            proj_sumbool (zeq (CompCert4Lean.Lib.Integers.Int64.unsigned j) n) := by
          change decide (CompCert4Lean.Lib.Integers.Int64.unsigned j =
            CompCert4Lean.Lib.Integers.Int64.unsigned
              (CompCert4Lean.Lib.Integers.Int64.repr n)) = _
          rw [selection_int64_unsigned_repr_small n hn]
          cases h : zeq (CompCert4Lean.Lib.Integers.Int64.unsigned j) n with
          | left heq => simp [proj_sumbool, heq]
          | right hne => simp [proj_sumbool, hne]
        change some (Val.of_bool (CompCert4Lean.Lib.Integers.Int64.eq j
          (CompCert4Lean.Lib.Integers.Int64.repr n))) = _
        rw [hb]
  · intro sp e m le a v i n heval hR hn
    cases hR with
    | intro j =>
        apply selection_eval_cmplu xi tprog sp e m .Clt le a (.Vlong j)
          (longconst (CompCert4Lean.Lib.Integers.Int64.repr n))
          (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr n)) _ heval
          (hConst (CompCert4Lean.Lib.Integers.Int64.repr n) sp e m le)
        change some (Val.of_bool (CompCert4Lean.Lib.Integers.Int64.ltu j
          (CompCert4Lean.Lib.Integers.Int64.repr n))) = _
        rw [selection_int64_ltu_repr j n hn]
  · intro sp e m le a v i n heval hR hn
    cases hR with
    | intro j =>
        refine ⟨.Vlong (CompCert4Lean.Lib.Integers.Int64.sub j
          (CompCert4Lean.Lib.Integers.Int64.repr n)), ?_, ?_⟩
        · have hs : subl a (longconst (CompCert4Lean.Lib.Integers.Int64.repr n)) =
              addlimm (CompCert4Lean.Lib.Integers.Int64.neg
                (CompCert4Lean.Lib.Integers.Int64.repr n)) a := by
            cases a <;> rfl
          rw [hs, selection_int64_sub_add_neg]
          exact selection_eval_addlimm_long xi tprog sp e m le a j _ heval
        · have hu : CompCert4Lean.Lib.Integers.Int64.unsigned
              (CompCert4Lean.Lib.Integers.Int64.sub j
                (CompCert4Lean.Lib.Integers.Int64.repr n)) =
              ZArith.BinInt.Z.modulo
                (ZArith.BinInt.Z.sub (CompCert4Lean.Lib.Integers.Int64.unsigned j) n)
                CompCert4Lean.Lib.Integers.Int64.modulus := by
            change CompCert4Lean.Lib.Integers.Int64.unsigned
              (CompCert4Lean.Lib.Integers.Int64.repr (ZArith.BinInt.Z.sub
                (CompCert4Lean.Lib.Integers.Int64.unsigned j)
                (CompCert4Lean.Lib.Integers.Int64.unsigned
                  (CompCert4Lean.Lib.Integers.Int64.repr n)))) = _
            rw [selection_int64_unsigned_repr_eq_exact,
              selection_int64_unsigned_repr_small n hn]
          rw [← hu]
          exact Rlong.intro _
  · intro sp e m le a v i heval hR
    cases hR with
    | intro j =>
        obtain ⟨v', he, hv⟩ := CompCert4Lean.Backend.SplitLongproof.eval_lowlong
          xi tprog sp e m le a (.Vlong j) heval
        change Val.lessdef (.Vint (CompCert4Lean.Lib.Integers.Int64.loword j)) v' at hv
        cases hv
        refine ⟨_, he, ?_⟩
        have hu : CompCert4Lean.Lib.Integers.Int.unsigned
            (CompCert4Lean.Lib.Integers.Int64.loword j) =
            ZArith.BinInt.Z.modulo (CompCert4Lean.Lib.Integers.Int64.unsigned j)
              CompCert4Lean.Lib.Integers.Int.modulus :=
          CompCert4Lean.Lib.Integers.Int.unsigned_repr_eq_proof _
        rw [← hu]
        exact Rint.intro _

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

theorem match_states_skip
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (oracle : SelectionOracle) :
    match_states_skipStatement cfg oracle := by
  intro prog cunit hf f f' k k' sp e m e' m' env
    hlink hhf hsel hty hcont hld hme
  exact match_state cunit hf f f' Cminor.Sskip k CminorSel.Sskip
    CminorSel.Sskip k' sp e m e' m' env
    hlink hhf hsel hty rfl hcont hld hme

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

theorem call_cont_commut
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (oracle : SelectionOracle) :
    call_cont_commutStatement cfg oracle := by
  intro prog cunit hf ki env k k' hmatch
  refine match_cont.rec (cfg := cfg) (oracle := oracle) (prog := prog)
    (motive_1 := fun _ _ _ _ k k' _ =>
      match_call_cont cfg oracle prog (Cminor.call_cont k) (CminorSel.call_cont k'))
    (motive_2 := fun k k' _ =>
      match_call_cont cfg oracle prog (Cminor.call_cont k) (CminorSel.call_cont k'))
    ?_ ?_ ?_ ?_ ?_ hmatch
  · intro cunit hf ki env s kont s' k k' hsel hcont ih
    simpa [Cminor.call_cont, CminorSel.call_cont] using ih
  · intro cunit hf ki env k k' hcont ih
    simpa [Cminor.call_cont, CminorSel.call_cont] using ih
  · intro cunit hf ki env k k' hcall ih
    exact ih
  · exact .match_cont_stop
  · intro cunit hf env id f sp e k f' e' k' hlink hhf hsel hty hcont hld ih
    exact .match_cont_call cunit hf env id f sp e k f' e' k'
      hlink hhf hsel hty hcont hld

end CompCert4Lean.Backend.Selectionproof
namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Builtins0
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.Selection
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp
open CompCert4Lean.X86.SelectOpproof
open CompCert4Lean.X86.Builtins1

theorem eval_sel_known_builtin
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_sel_known_builtinStatement := by
  intro xi tprog sp e m bf args a vl v le hsel hargs hsem
  cases bf with
  | BI_standard bf =>
      cases bf with
      | BI_select ty =>
          cases args with
          | Enil => simp [sel_known_builtin, CompCert4Lean.X86.SelectOp.platform_builtin] at hsel
          | Econs a1 rest =>
              cases rest with
              | Enil => simp [sel_known_builtin, CompCert4Lean.X86.SelectOp.platform_builtin] at hsel
              | Econs a2 rest2 =>
                  cases rest2 with
                  | Enil => simp [sel_known_builtin, CompCert4Lean.X86.SelectOp.platform_builtin] at hsel
                  | Econs a3 rest3 =>
                      cases rest3 with
                      | Enil =>
                          simp [sel_known_builtin, CompCert4Lean.X86.SelectOp.platform_builtin] at hsel
                          subst a
                          cases hargs with
                          | cons _ _ _ vv0 _ h1 ht =>
                              cases ht with
                              | cons _ _ _ vv1 _ h2 ht2 =>
                                  cases ht2 with
                                  | cons _ _ _ vv2 _ h3 ht3 =>
                                      cases ht3
                                      cases vv0 with
                                      | Vundef => change none = some v at hsem; cases hsem
                                      | Vint n =>
                                          change some (Val.normalize
                                            (if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero then vv2 else vv1) ty) = some v at hsem
                                          cases hsem
                                          have hb : Val.bool_of_val (.Vint n) (!(CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero)) :=
                                            Val.bool_of_val_int n
                                          have hs := eval_sel_select xi tprog sp e m le
                                            a1 a2 a3 (.Vint n) vv1 vv2 (!(CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero)) ty
                                            h1 h2 h3 hb
                                          rcases hs with ⟨v', hev, hless⟩
                                          refine ⟨v', hev, ?_⟩
                                          have heq : Val.normalize
                                              (if CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero then vv2 else vv1) ty =
                                              Val.select (some (!(CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero))) vv1 vv2 ty := by
                                            by_cases hn : CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero = true <;>
                                              simp [hn, Val.select]
                                          rw [heq]
                                          exact hless
                                      | Vlong n => change none = some v at hsem; cases hsem
                                      | Vfloat f => change none = some v at hsem; cases hsem
                                      | Vsingle f => change none = some v at hsem; cases hsem
                                      | Vptr b ofs => change none = some v at hsem; cases hsem
                      | Econs _ _ => simp [sel_known_builtin, CompCert4Lean.X86.SelectOp.platform_builtin] at hsel
      | BI_fabs =>
          cases args with
          | Enil => simp [sel_known_builtin, CompCert4Lean.X86.SelectOp.platform_builtin] at hsel
          | Econs a1 rest =>
              cases rest with
              | Enil =>
                  simp [sel_known_builtin, CompCert4Lean.X86.SelectOp.platform_builtin] at hsel
                  subst a
                  cases hargs with
                  | cons _ _ _ vv _ h1 ht =>
                      cases ht
                      cases vv with
                      | Vfloat f =>
                          change some (Val.absf (.Vfloat f)) = some v at hsem
                          cases hsem
                          exact CompCert4Lean.X86.SelectOpproof.eval_absf xi
                            (Genv.globalenv tprog) sp e m le a1 (.Vfloat f) h1
                      | _ =>
                          dsimp [builtin_function_sem, standard_builtin_sem,
                            CompCert4Lean.Common.Builtins0.mkbuiltin_n1t,
                            CompCert4Lean.Common.Builtins0.mkbuiltin_v1t] at hsem
                          cases hsem
                          exact CompCert4Lean.X86.SelectOpproof.eval_absf xi
                            (Genv.globalenv tprog) sp e m le a1 _ h1
              | Econs _ _ => simp [sel_known_builtin, CompCert4Lean.X86.SelectOp.platform_builtin] at hsel
      | BI_fabsf =>
          cases args with
          | Enil => simp [sel_known_builtin, CompCert4Lean.X86.SelectOp.platform_builtin] at hsel
          | Econs a1 rest =>
              cases rest with
              | Enil =>
                  simp [sel_known_builtin, CompCert4Lean.X86.SelectOp.platform_builtin] at hsel
                  subst a
                  cases hargs with
                  | cons _ _ _ vv _ h1 ht =>
                      cases ht
                      cases vv with
                      | Vsingle f =>
                          change some (Val.absfs (.Vsingle f)) = some v at hsem
                          cases hsem
                          exact CompCert4Lean.X86.SelectOpproof.eval_absfs xi
                            (Genv.globalenv tprog) sp e m le a1 (.Vsingle f) h1
                      | _ =>
                          dsimp [builtin_function_sem, standard_builtin_sem,
                            CompCert4Lean.Common.Builtins0.mkbuiltin_n1t,
                            CompCert4Lean.Common.Builtins0.mkbuiltin_v1t] at hsem
                          cases hsem
                          exact CompCert4Lean.X86.SelectOpproof.eval_absfs xi
                            (Genv.globalenv tprog) sp e m le a1 _ h1
              | Econs _ _ => simp [sel_known_builtin, CompCert4Lean.X86.SelectOp.platform_builtin] at hsel
      | _ => simp [sel_known_builtin, CompCert4Lean.X86.SelectOp.platform_builtin] at hsel
  | BI_platform bf =>
      cases bf with
      | BI_fmin =>
          cases args with
          | Enil => simp [sel_known_builtin, CompCert4Lean.X86.SelectOp.platform_builtin] at hsel
          | Econs a1 rest =>
              cases rest with
              | Enil => simp [sel_known_builtin, CompCert4Lean.X86.SelectOp.platform_builtin] at hsel
              | Econs a2 rest2 =>
                  cases rest2 with
                  | Enil =>
                      simp [sel_known_builtin, CompCert4Lean.X86.SelectOp.platform_builtin] at hsel
                      subst a
                      cases hargs with
                      | cons _ _ _ vv1 _ h1 ht =>
                          cases ht with
                          | cons _ _ _ vv2 _ h2 ht2 =>
                              cases ht2
                              cases vv1 <;> cases vv2
                              all_goals
                                try
                                  change some Vundef = some v at hsem
                                  cases hsem
                                  refine ⟨Vundef, ?_, Val.lessdef_refl _⟩
                                  apply eval_expr.eval_Eop le Ominf
                                    (Econs a1 (Econs a2 Enil)) _ Vundef
                                  · exact eval_exprlist.cons le a1 (Econs a2 Enil) _ [_] h1
                                      (eval_exprlist.cons le a2 Enil _ [] h2
                                        (eval_exprlist.nil le))
                                  · rfl
                              case Vfloat.Vfloat f1 f2 =>
                                change some (Vfloat (match CompCert4Lean.Lib.Floats.Float.compare f1 f2 with
                                  | some .Lt => f1
                                  | some .Eq | some .Gt | none => f2)) = some v at hsem
                                cases hsem
                                refine ⟨_, ?_, Val.lessdef_refl _⟩
                                apply eval_expr.eval_Eop le Ominf
                                  (Econs a1 (Econs a2 Enil)) [Vfloat f1, Vfloat f2] _
                                · exact eval_exprlist.cons le a1 (Econs a2 Enil) _ [Vfloat f2] h1
                                    (eval_exprlist.cons le a2 Enil _ [] h2
                                      (eval_exprlist.nil le))
                                · rfl
                  | Econs _ _ => simp [sel_known_builtin, CompCert4Lean.X86.SelectOp.platform_builtin] at hsel
      | BI_fmax =>
          cases args with
          | Enil => simp [sel_known_builtin, CompCert4Lean.X86.SelectOp.platform_builtin] at hsel
          | Econs a1 rest =>
              cases rest with
              | Enil => simp [sel_known_builtin, CompCert4Lean.X86.SelectOp.platform_builtin] at hsel
              | Econs a2 rest2 =>
                  cases rest2 with
                  | Enil =>
                      simp [sel_known_builtin, CompCert4Lean.X86.SelectOp.platform_builtin] at hsel
                      subst a
                      cases hargs with
                      | cons _ _ _ vv1 _ h1 ht =>
                          cases ht with
                          | cons _ _ _ vv2 _ h2 ht2 =>
                              cases ht2
                              cases vv1 <;> cases vv2
                              all_goals
                                try
                                  change some Vundef = some v at hsem
                                  cases hsem
                                  refine ⟨Vundef, ?_, Val.lessdef_refl _⟩
                                  apply eval_expr.eval_Eop le Omaxf
                                    (Econs a1 (Econs a2 Enil)) _ Vundef
                                  · exact eval_exprlist.cons le a1 (Econs a2 Enil) _ [_] h1
                                      (eval_exprlist.cons le a2 Enil _ [] h2
                                        (eval_exprlist.nil le))
                                  · rfl
                              case Vfloat.Vfloat f1 f2 =>
                                change some (Vfloat (match CompCert4Lean.Lib.Floats.Float.compare f1 f2 with
                                  | some .Gt => f1
                                  | some .Eq | some .Lt | none => f2)) = some v at hsem
                                cases hsem
                                refine ⟨_, ?_, Val.lessdef_refl _⟩
                                apply eval_expr.eval_Eop le Omaxf
                                  (Econs a1 (Econs a2 Enil)) [Vfloat f1, Vfloat f2] _
                                · exact eval_exprlist.cons le a1 (Econs a2 Enil) _ [Vfloat f2] h1
                                    (eval_exprlist.cons le a2 Enil _ [] h2
                                      (eval_exprlist.nil le))
                                · rfl
                  | Econs _ _ => simp [sel_known_builtin, CompCert4Lean.X86.SelectOp.platform_builtin] at hsel

end CompCert4Lean.Backend.Selectionproof

namespace CompCert4Lean.Backend.Selectionproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.Cminor
open CompCert4Lean.Common.Memory

private theorem selection_valid_pointer_extends
    {m m' : mem} (hext : Mem.extends m m') :
    ∀ b ofs, Mem.valid_pointer m b ofs = true →
      Mem.valid_pointer m' b ofs = true := by
  intro b ofs hp
  apply (Mem.valid_pointer_nonempty_perm m' b ofs).2
  have h := hext.mext_inj.mi_perm b b (.Z0) ofs _ _ rfl
    ((Mem.valid_pointer_nonempty_perm m b ofs).1 hp)
  have hz : ZArith.BinInt.Z.add ofs .Z0 = ofs := by
    apply intOfZ_injective
    change intOfZ (zOfInt (intOfZ ofs + 0)) = intOfZ ofs
    rw [intOfZ_zOfInt]
    simp
  simpa only [hz] using h

set_option maxHeartbeats 2000000 in
theorem eval_binop_lessdef
    :
    eval_binop_lessdefStatement := by
  intro op v1 v1' v2 v2' v m m' hEval hld1 hld2 hMem
  have hsame : ∃ v', Cminor.eval_binop op v1' v2' m = some v' ∧ Val.lessdef v v' := by
    cases hld1 with
    | lessdef_refl =>
        cases hld2 with
        | lessdef_refl => exact ⟨v, hEval, Val.lessdef_refl _⟩
        | lessdef_undef =>
            cases op <;> cases v1 <;> cases v2' <;>
              simp [Cminor.eval_binop, Val.add, Val.sub, Val.mul, Val.divs, Val.divu, Val.mods, Val.modu,
                Val.and, Val.or, Val.xor, Val.shl, Val.shr, Val.shru,
                Val.addf, Val.subf, Val.mulf, Val.divf, Val.addfs, Val.subfs, Val.mulfs, Val.divfs,
                Val.addl, Val.subl, Val.mull, Val.divls, Val.divlu, Val.modls, Val.modlu,
                Val.andl, Val.orl, Val.xorl, Val.shll, Val.shrl, Val.shrlu,
                Val.cmp, Val.cmpu, Val.cmpf, Val.cmpfs, Val.cmpl, Val.cmplu,
                Val.cmp_bool, Val.cmpu_bool, Val.cmpf_bool, Val.cmpfs_bool,
                Val.cmpl_bool, Val.cmplu_bool, Val.of_optbool, Val.cmp_different_blocks] at hEval ⊢ <;>
              subst v <;> exact Val.lessdef_undef _
    | lessdef_undef =>
        cases hld2 with
        | lessdef_refl =>
            cases op <;> cases v2 <;> cases v1' <;>
              simp [Cminor.eval_binop, Val.add, Val.sub, Val.mul, Val.divs, Val.divu, Val.mods, Val.modu,
                Val.and, Val.or, Val.xor, Val.shl, Val.shr, Val.shru,
                Val.addf, Val.subf, Val.mulf, Val.divf, Val.addfs, Val.subfs, Val.mulfs, Val.divfs,
                Val.addl, Val.subl, Val.mull, Val.divls, Val.divlu, Val.modls, Val.modlu,
                Val.andl, Val.orl, Val.xorl, Val.shll, Val.shrl, Val.shrlu,
                Val.cmp, Val.cmpu, Val.cmpf, Val.cmpfs, Val.cmpl, Val.cmplu,
                Val.cmp_bool, Val.cmpu_bool, Val.cmpf_bool, Val.cmpfs_bool,
                Val.cmpl_bool, Val.cmplu_bool, Val.of_optbool, Val.cmp_different_blocks] at hEval ⊢ <;>
              subst v <;> exact Val.lessdef_undef _
        | lessdef_undef =>
            cases op <;> cases v1' <;> cases v2' <;>
              simp [Cminor.eval_binop, Val.add, Val.sub, Val.mul, Val.divs, Val.divu, Val.mods, Val.modu,
                Val.and, Val.or, Val.xor, Val.shl, Val.shr, Val.shru,
                Val.addf, Val.subf, Val.mulf, Val.divf, Val.addfs, Val.subfs, Val.mulfs, Val.divfs,
                Val.addl, Val.subl, Val.mull, Val.divls, Val.divlu, Val.modls, Val.modlu,
                Val.andl, Val.orl, Val.xorl, Val.shll, Val.shrl, Val.shrlu,
                Val.cmp, Val.cmpu, Val.cmpf, Val.cmpfs, Val.cmpl, Val.cmplu,
                Val.cmp_bool, Val.cmpu_bool, Val.cmpf_bool, Val.cmpfs_bool,
                Val.cmpl_bool, Val.cmplu_bool, Val.of_optbool, Val.cmp_different_blocks] at hEval ⊢ <;>
              subst v <;> exact Val.lessdef_undef _
  have hcmpu : ∀ c,
      Cminor.eval_binop (.Ocmpu c) v1 v2 m = some v →
      ∃ v', Cminor.eval_binop (.Ocmpu c) v1' v2' m' = some v' ∧ Val.lessdef v v' := by
    intro c h
    change some (Val.cmpu (Mem.valid_pointer m) c v1 v2) = some v at h
    change ∃ v', some (Val.cmpu (Mem.valid_pointer m') c v1' v2') = some v' ∧ Val.lessdef v v'
    have hv : Val.cmpu (Mem.valid_pointer m) c v1 v2 = v := Option.some.inj h
    subst v
    refine ⟨Val.cmpu (Mem.valid_pointer m') c v1' v2', rfl, ?_⟩
    apply Val.of_optbool_lessdef _ _
    intro b hb
    exact Val.cmpu_bool_lessdef _ _ c v1 v1' v2 v2' b
      (selection_valid_pointer_extends hMem) hld1 hld2 hb
  have hcmplu : ∀ c,
      Cminor.eval_binop (.Ocmplu c) v1 v2 m = some v →
      ∃ v', Cminor.eval_binop (.Ocmplu c) v1' v2' m' = some v' ∧ Val.lessdef v v' := by
    intro c h
    change Val.cmplu (Mem.valid_pointer m) c v1 v2 = some v at h
    unfold Val.cmplu at h
    cases hs : Val.cmplu_bool (Mem.valid_pointer m) c v1 v2 with
    | none => simp [hs] at h
    | some b =>
        simp [hs] at h
        subst v
        refine ⟨Val.of_bool b, ?_, Val.lessdef_refl _⟩
        change Val.cmplu (Mem.valid_pointer m') c v1' v2' = some (Val.of_bool b)
        unfold Val.cmplu
        have hb := Val.cmplu_bool_lessdef _ _ c v1 v1' v2 v2' b
          (selection_valid_pointer_extends hMem) hld1 hld2 hs
        rw [hb]
        rfl
  cases op with
  | Ocmpu c => exact hcmpu c hEval
  | Ocmplu c => exact hcmplu c hEval
  | _ =>
      obtain ⟨v', hv', hld⟩ := hsame
      refine ⟨v', ?_, hld⟩
      simpa [Cminor.eval_binop] using hv'

end CompCert4Lean.Backend.Selectionproof
