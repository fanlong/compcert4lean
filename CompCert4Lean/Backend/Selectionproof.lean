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
