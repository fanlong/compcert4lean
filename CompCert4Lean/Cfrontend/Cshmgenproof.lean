import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Errors
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Common.Values
import CompCert4Lean.Cfrontend.Clight
import CompCert4Lean.Cfrontend.Cop
import CompCert4Lean.Cfrontend.Cshmgen
import CompCert4Lean.Cfrontend.Csharpminor
import CompCert4Lean.Cfrontend.Ctyping
import CompCert4Lean.Cfrontend.Ctypes
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Maps

/-!
# Correctness interface for Clight to Csharpminor generation

The executable relations and constructor specifications are translated here.
Proofs assigned to the later migration phase are represented by transparent
proposition descriptors below.
-/

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.Cshmgen
open CompCert4Lean.Cfrontend.Csharpminor
open CompCert4Lean.Cfrontend.Ctyping
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private abbrev ident := CompCert4Lean.Common.AST.ident
private abbrev block := CompCert4Lean.Common.Values.block
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev CProgram := CompCert4Lean.Cfrontend.Clight.program
private abbrev TProgram := CompCert4Lean.Cfrontend.Csharpminor.program
private abbrev CFundef := CompCert4Lean.Cfrontend.Clight.fundef
private abbrev TFundef := CompCert4Lean.Cfrontend.Csharpminor.fundef
private abbrev CFunction := CompCert4Lean.Cfrontend.Clight.function
private abbrev TFunction := CompCert4Lean.Cfrontend.Csharpminor.function
private abbrev CType := CompCert4Lean.Cfrontend.Ctypes.type
private abbrev CExpr := CompCert4Lean.Cfrontend.Clight.expr
private abbrev TExpr := CompCert4Lean.Cfrontend.Csharpminor.expr
private abbrev CStmt := CompCert4Lean.Cfrontend.Clight.statement
private abbrev TStmt := CompCert4Lean.Cfrontend.Csharpminor.stmt
private abbrev CCont := CompCert4Lean.Cfrontend.Clight.cont
private abbrev TCont := CompCert4Lean.Cfrontend.Csharpminor.cont
private abbrev CState := CompCert4Lean.Cfrontend.Clight.machine_state
private abbrev TState := CompCert4Lean.Cfrontend.Csharpminor.state
private abbrev CEnv := CompCert4Lean.Cfrontend.Clight.env
private abbrev TEnv := CompCert4Lean.Cfrontend.Csharpminor.env
private abbrev CTempEnv := CompCert4Lean.Cfrontend.Clight.temp_env
private abbrev TTempEnv := CompCert4Lean.Cfrontend.Csharpminor.temp_env
private abbrev CGenv := CompCert4Lean.Cfrontend.Clight.genv
private abbrev TGenv := CompCert4Lean.Cfrontend.Csharpminor.genv
private abbrev CLabel := CompCert4Lean.Cfrontend.Clight.label
private abbrev Res := CompCert4Lean.Common.Errors.res
private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev CCInt64 := CompCert4Lean.Lib.Integers.int64
private abbrev CCFloat := CompCert4Lean.Lib.Floats.float
private abbrev CCFloat32 := CompCert4Lean.Lib.Floats.float32
private abbrev Signature := CompCert4Lean.Common.AST.signature
private abbrev Comparison := CompCert4Lean.Lib.Integers.comparison
private abbrev UnaryOp := CompCert4Lean.Cfrontend.Cop.unary_operation
private abbrev BinaryOp := CompCert4Lean.Cfrontend.Cop.binary_operation
private abbrev IntSize := CompCert4Lean.Cfrontend.Ctypes.intsize
private abbrev Signedness := CompCert4Lean.Cfrontend.Ctypes.signedness
private abbrev Bitfield := CompCert4Lean.Cfrontend.Ctypes.bitfield
private abbrev Ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

private abbrev C_eval_expr
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :=
  Clight.eval_expr
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
private abbrev C_eval_lvalue
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :=
  Clight.eval_lvalue
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
private abbrev C_eval_exprlist
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :=
  Clight.eval_exprlist
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
private abbrev T_eval_expr
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :=
  Csharpminor.eval_expr
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
private abbrev T_eval_exprlist
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :=
  Csharpminor.eval_exprlist
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
private abbrev T_step
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :=
  Csharpminor.step
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
private abbrev C_step2
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :=
  Clight.step2
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
private abbrev C_semantics2
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :=
  Clight.semantics2
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
private abbrev T_semantics
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :=
  Csharpminor.semantics
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)

private abbrev z0 : Z := .Z0
local instance : OfNat Z 0 := ⟨z0⟩
local instance : HAdd Z Z Z := ⟨ZArith.BinInt.Z.add⟩
local instance : HSub Z Z Z := ⟨ZArith.BinInt.Z.sub⟩
local instance : LE Z := ⟨ZArith.BinInt.Z.le⟩
local instance : LT Z := ⟨ZArith.BinInt.Z.lt⟩

/-! ## Program matching -/

inductive match_fundef (p : CProgram) : CFundef → TFundef → Prop where
  | match_fundef_internal (f : CFunction) (tf : TFunction) :
      transl_function p.prog_comp_env f = .OK tf →
      match_fundef p (.Internal f) (.Internal tf)
  | match_fundef_external (ef : external_function) (args : List CType)
      (res : CType) (cc : calling_convention) :
      CompCert4Lean.Common.AST.ef_sig ef = signature_of_type args res cc →
      match_fundef p (.External ef args res cc) (.External ef)

export match_fundef (match_fundef_internal match_fundef_external)

def match_varinfo (_v : CType) (_tv : Unit) : Prop := True

def match_prog (p : CProgram) (tp : TProgram) : Prop :=
  list_forall2
      (fun idg tidg =>
        idg.1 = tidg.1 ∧
          match idg.2, tidg.2 with
          | .Gfun f, .Gfun tf =>
              ∃ cu, Ctypes.linkorder_program cu p ∧ match_fundef cu f tf
          | .Gvar v, .Gvar tv =>
              match_varinfo v.gvar_info tv.gvar_info ∧
                v.gvar_init = tv.gvar_init ∧
                v.gvar_readonly = tv.gvar_readonly ∧
                v.gvar_volatile = tv.gvar_volatile
          | _, _ => False)
      (Ctypes.program_of_program p).prog_defs tp.prog_defs ∧
    tp.prog_main = (Ctypes.program_of_program p).prog_main ∧
    tp.prog_public = (Ctypes.program_of_program p).prog_public

/-! ## Constructor correctness specifications -/

def binary_constructor_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (ge : TGenv)
    (make : TExpr → CType → TExpr → CType → Res TExpr)
    (sem : val → CType → val → CType → mem → Option val) : Prop :=
  ∀ a tya b tyb c va vb v e le m,
    sem va tya vb tyb m = some v →
    make a tya b tyb = .OK c →
    T_eval_expr ge e le m a va →
    T_eval_expr ge e le m b vb →
    T_eval_expr ge e le m c v

def shift_constructor_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (ge : TGenv)
    (make : TExpr → CType → TExpr → CType → Res TExpr)
    (sem : val → CType → val → CType → Option val) : Prop :=
  ∀ a tya b tyb c va vb v e le m,
    sem va tya vb tyb = some v →
    make a tya b tyb = .OK c →
    T_eval_expr ge e le m a va →
    T_eval_expr ge e le m b vb →
    T_eval_expr ge e le m c v

/-! ## Environment matching -/

structure match_env (prog : CProgram) (e : CEnv) (te : TEnv) : Prop where
  me_local : ∀ id b ty,
    PTree.get id e = some (b, ty) →
    PTree.get id te = some (b, Ctypes.sizeof prog.prog_comp_env ty)
  me_local_inv : ∀ id b sz,
    PTree.get id te = some (b, sz) →
    ∃ ty, PTree.get id e = some (b, ty)

export match_env (me_local me_local_inv)

/-! ## Continuation and state matching -/

inductive match_transl : TStmt → TCont → TStmt → TCont → Prop where
  | match_transl_0 (ts : TStmt) (tk : TCont) : match_transl ts tk ts tk
  | match_transl_1 (ts : TStmt) (tk : TCont) :
      match_transl (.Sblock ts) tk ts (.Kblock tk)

inductive match_cont (prog : CProgram) (tprog : TProgram) :
    composite_env → CType → Nat → Nat → CCont → TCont → Prop where
  | match_Kstop (ce : composite_env) (tyret : CType) (nbrk ncnt : Nat) :
      match_cont prog tprog ce tyret nbrk ncnt .Kstop .Kstop
  | match_Kseq (ce : composite_env) (tyret : CType) (nbrk ncnt : Nat)
      (s : CStmt) (k : CCont) (ts : TStmt) (tk : TCont) :
      transl_statement ce tyret nbrk ncnt s = .OK ts →
      match_cont prog tprog ce tyret nbrk ncnt k tk →
      match_cont prog tprog ce tyret nbrk ncnt (.Kseq s k) (.Kseq ts tk)
  | match_Kloop1 (ce : composite_env) (tyret : CType)
      (s1 s2 : CStmt) (k : CCont) (ts1 ts2 : TStmt) (nbrk ncnt : Nat) (tk : TCont) :
      transl_statement ce tyret 1 0 s1 = .OK ts1 →
      transl_statement ce tyret 0 (Nat.succ ncnt) s2 = .OK ts2 →
      match_cont prog tprog ce tyret nbrk ncnt k tk →
      match_cont prog tprog ce tyret 1 0 (.Kloop1 s1 s2 k)
        (.Kblock (.Kseq ts2 (.Kseq (.Sloop (.Sseq (.Sblock ts1) ts2)) (.Kblock tk))))
  | match_Kloop2 (ce : composite_env) (tyret : CType)
      (s1 s2 : CStmt) (k : CCont) (ts1 ts2 : TStmt) (nbrk ncnt : Nat) (tk : TCont) :
      transl_statement ce tyret 1 0 s1 = .OK ts1 →
      transl_statement ce tyret 0 (Nat.succ ncnt) s2 = .OK ts2 →
      match_cont prog tprog ce tyret nbrk ncnt k tk →
      match_cont prog tprog ce tyret 0 (Nat.succ ncnt) (.Kloop2 s1 s2 k)
        (.Kseq (.Sloop (.Sseq (.Sblock ts1) ts2)) (.Kblock tk))
  | match_Kswitch (ce : composite_env) (tyret : CType) (nbrk ncnt : Nat)
      (k : CCont) (tk : TCont) :
      match_cont prog tprog ce tyret nbrk ncnt k tk →
      match_cont prog tprog ce tyret 0 (Nat.succ ncnt) (.Kswitch k) (.Kblock tk)
  | match_Kcall (ce : composite_env) (tyret : CType) (nbrk ncnt nbrk' ncnt' : Nat)
      (f : CFunction) (e : CEnv) (k : CCont) (id : Option ident)
      (tf : TFunction) (te : TEnv) (le : CTempEnv) (tk : TCont) (cu : CProgram) :
      Ctypes.linkorder_program cu prog →
      transl_function cu.prog_comp_env f = .OK tf →
      match_env prog e te →
      match_cont prog tprog cu.prog_comp_env f.fn_return nbrk' ncnt' k tk →
      match_cont prog tprog ce tyret nbrk ncnt (.Kcall id f e le k)
        (.Kcall id tf te le tk)
  | match_Kcall_normalize
      [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
      (ce : composite_env) (tyret : CType)
      (nbrk ncnt nbrk' ncnt' : Nat) (f : CFunction) (e : CEnv) (k : CCont)
      (id : ident) (a : TExpr) (tf : TFunction) (te : TEnv)
      (le : CTempEnv) (tk : TCont) (cu : CProgram) :
      Ctypes.linkorder_program cu prog →
      transl_function cu.prog_comp_env f = .OK tf →
      match_env prog e te →
      match_cont prog tprog cu.prog_comp_env f.fn_return nbrk' ncnt' k tk →
      (∀ v e le m, wt_val v tyret → PTree.get id le = some v →
        T_eval_expr (Genv.globalenv tprog) e le m a v) →
      match_cont prog tprog ce tyret nbrk ncnt (.Kcall (some id) f e le k)
        (.Kcall (some id) tf te le (.Kseq (.Sset id a) tk))

export match_cont (match_Kstop match_Kcall match_Kcall_normalize)

inductive match_states (prog : CProgram) (tprog : TProgram) : CState → TState → Prop where
  | match_state (f : CFunction) (nbrk ncnt : Nat) (s : CStmt) (k : CCont)
      (e : CEnv) (le : CTempEnv) (m : mem) (tf : TFunction) (ts : TStmt)
      (tk : TCont) (te : TEnv) (ts' : TStmt) (tk' : TCont) (cu : CProgram) :
      Ctypes.linkorder_program cu prog →
      transl_function cu.prog_comp_env f = .OK tf →
      transl_statement cu.prog_comp_env f.fn_return nbrk ncnt s = .OK ts →
      match_transl ts tk ts' tk' →
      match_env prog e te →
      match_cont prog tprog cu.prog_comp_env f.fn_return nbrk ncnt k tk →
      match_states prog tprog (.State f s k e le m) (.State tf ts' tk' te le m)
  | match_callstate (fd : CFundef) (args : List val) (k : CCont) (m : mem)
      (tfd : TFundef) (tk : TCont) (targs : List CType) (tres : CType)
      (cconv : calling_convention) (cu : CProgram) (ce : composite_env) :
      Ctypes.linkorder_program cu prog →
      match_fundef cu fd tfd →
      match_cont prog tprog ce tres 0 0 k tk →
      Clight.is_call_cont k →
      Clight.type_of_fundef fd = .Tfunction targs tres cconv →
      Val.has_argtype_list args (List.map argtype_of_type targs) →
      match_states prog tprog (.Callstate fd args k m) (.Callstate tfd args tk m)
  | match_returnstate (res : val) (tres : CType) (k : CCont) (m : mem)
      (tk : TCont) (ce : composite_env) :
      match_cont prog tprog ce tres 0 0 k tk →
      wt_val res tres →
      match_states prog tprog (.Returnstate res k m) (.Returnstate res tk m)

export match_states (match_returnstate)

/-! ## Later-proof statement descriptors -/

def bind_parameter_temps_matchStatement : Prop :=
  ∀ vars vals le1 le2,
    Clight.bind_parameter_temps vars vals le1 = some le2 →
    Csharpminor.bind_parameters (vars.map Prod.fst) vals le1 = some le2

def create_undef_temps_matchStatement : Prop :=
  ∀ temps,
    Csharpminor.create_undef_temps (temps.map Prod.fst) =
      Clight.create_undef_temps temps

def field_offset_stableStatement : Prop :=
  ∀ (cunit prog : CProgram) id co f,
    Ctypes.linkorder_program cunit prog →
    PTree.get id cunit.prog_comp_env = some co →
    PTree.get id prog.prog_comp_env = some co ∧
      Ctypes.field_offset prog.prog_comp_env f co.co_members =
        Ctypes.field_offset cunit.prog_comp_env f co.co_members

def first_bit_rangeStatement : Prop :=
  ∀ sz pos width,
    0 ≤ pos → 0 < width → pos + width ≤ Cop.bitsize_carrier sz →
    0 ≤ Cop.first_bit sz pos width ∧
      Cop.first_bit sz pos width < CompCert4Lean.Lib.Integers.Int.zwordsize ∧
      0 ≤ CompCert4Lean.Lib.Integers.Int.zwordsize - Cop.first_bit sz pos width - width ∧
      CompCert4Lean.Lib.Integers.Int.zwordsize - Cop.first_bit sz pos width - width <
        CompCert4Lean.Lib.Integers.Int.zwordsize

def function_ptr_translatedStatement : Prop :=
  ∀ prog tprog, match_prog prog tprog →
    ∀ b f, Genv.find_funct_ptr (Clight.globalenv prog).genv_genv b = some f →
      ∃ cu tf,
        Genv.find_funct_ptr (Genv.globalenv tprog) b = some tf ∧
        match_fundef cu f tf ∧ Ctypes.linkorder_program cu prog

def functions_translatedStatement : Prop :=
  ∀ prog tprog, match_prog prog tprog →
    ∀ v f, Genv.find_funct (Clight.globalenv prog).genv_genv v = some f →
      ∃ cu tf,
        Genv.find_funct (Genv.globalenv tprog) v = some tf ∧
        match_fundef cu f tf ∧ Ctypes.linkorder_program cu prog

def int_ltu_trueStatement : Prop :=
  ∀ x : Z, 0 ≤ x → x < CompCert4Lean.Lib.Integers.Int.zwordsize →
    CompCert4Lean.Lib.Integers.Int.ltu
      (CompCert4Lean.Lib.Integers.Int.repr x)
      CompCert4Lean.Lib.Integers.Int.iwordsize = true

def make_absfloat_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) a tya c va v e le m,
    sem_absfloat va tya = some v → make_absfloat a tya = .OK c →
    T_eval_expr ge e le m a va → T_eval_expr ge e le m c v

def make_add_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) (cunit prog : CProgram),
    Ctypes.linkorder_program cunit prog →
    binary_constructor_correct ge (make_add cunit.prog_comp_env)
      (sem_add prog.prog_comp_env)

def make_and_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv), binary_constructor_correct ge make_and sem_and

def make_binarith_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) sem_int sem_long sem_float sem_single iop iopu fop sop lop lopu,
    binary_constructor_correct ge
      (make_binarith iop iopu fop sop lop lopu)
      (sem_binarith sem_int sem_long sem_float sem_single)

def make_binarith_int_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) sem_int sem_long iop iopu lop lopu,
    binary_constructor_correct ge
      (make_binarith_int iop iopu lop lopu)
      (sem_binarith sem_int sem_long (fun _ _ => none) (fun _ _ => none))

def make_boolean_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) e le m a v ty b,
    T_eval_expr ge e le m a v → bool_val v ty m = some b →
    T_eval_expr ge e le m (make_boolean a ty) (Val.of_bool b)

def make_cast_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) e le m a b v ty1 ty2 v',
    make_cast ty1 ty2 a = .OK b → T_eval_expr ge e le m a v →
    sem_cast v ty1 ty2 m = some v' → T_eval_expr ge e le m b v'

def make_cast_int_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) e le m a n sz si,
    T_eval_expr ge e le m a (.Vint n) →
    T_eval_expr ge e le m (make_cast_int a sz si)
      (.Vint (cast_int_int sz si n))

def make_cmp_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) cmp, binary_constructor_correct ge (make_cmp cmp) (sem_cmp cmp)

def make_cmp_ptr_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) cmp e le m a va b vb v,
    cmp_ptr m cmp va vb = some v → T_eval_expr ge e le m a va →
    T_eval_expr ge e le m b vb → T_eval_expr ge e le m (make_cmp_ptr cmp a b) v

def make_cmpu_ne_zero_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) e le m a n,
    T_eval_expr ge e le m a (.Vint n) →
    T_eval_expr ge e le m (make_cmpu_ne_zero a)
      (.Vint (if Int.eq n Int.zero then Int.zero else Int.one))

def make_cmpu_ne_zero_correct_ptrStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) e le m a b i,
    T_eval_expr ge e le m a (.Vptr b i) →
    CompCert4Lean.X86_64.Archi.ptr64 = false →
    Mem.weak_valid_pointer m b (Ptrofs.unsigned i) = true →
    T_eval_expr ge e le m (make_cmpu_ne_zero a) (.Vint Int.one)

def make_div_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv), binary_constructor_correct ge make_div sem_div

def make_floatconst_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) n e le m,
    T_eval_expr ge e le m (make_floatconst n) (.Vfloat n)

def make_intconst_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) n e le m,
    T_eval_expr ge e le m (make_intconst n) (.Vint n)

def make_load_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) addr ty bf code b ofs v e le m,
    make_load addr ty bf = .OK code →
    T_eval_expr ge e le m addr (.Vptr b ofs) →
    Clight.deref_loc ty m b ofs bf v →
    T_eval_expr ge e le m code v

def make_longconst_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) n e le m,
    T_eval_expr ge e le m (make_longconst n) (.Vlong n)

def make_memcpy_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (ge : TGenv) (cunit prog : CProgram)
    (f : TFunction) dst src ty k e le m b ofs v m' s,
    Ctypes.linkorder_program cunit prog →
    T_eval_expr ge e le m dst (.Vptr b ofs) →
    T_eval_expr ge e le m src v →
    Clight.assign_loc prog.prog_comp_env ty m b ofs .Full v m' →
    access_mode ty = .By_copy →
    make_memcpy cunit.prog_comp_env dst src ty = .OK s →
    T_step xi ge (.State f s k e le m) E0
      (.State f .Sskip k e le m')

def make_mod_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv), binary_constructor_correct ge make_mod sem_mod

def make_mul_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv), binary_constructor_correct ge make_mul sem_mul

def make_neg_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) a tya c va v e le m,
    sem_neg va tya = some v → make_neg a tya = .OK c →
    T_eval_expr ge e le m a va → T_eval_expr ge e le m c v

def make_normalization_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) e le m a v t,
    T_eval_expr ge e le m a v → wt_val v t →
    T_eval_expr ge e le m (make_normalization t a) v

def make_notbool_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) a tya c va v e le m,
    sem_notbool va tya m = some v → make_notbool a tya = .OK c →
    T_eval_expr ge e le m a va → T_eval_expr ge e le m c v

def make_notint_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) a tya c va v e le m,
    sem_notint va tya = some v → make_notint a tya = .OK c →
    T_eval_expr ge e le m a va → T_eval_expr ge e le m c v

def make_or_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv), binary_constructor_correct ge make_or sem_or

def make_ptrofs_of_int64_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) e le m a i,
    T_eval_expr ge e le m a (.Vlong i) →
    T_eval_expr ge e le m
      (if CompCert4Lean.X86_64.Archi.ptr64 then a else .Eunop .Ointoflong a)
      (if CompCert4Lean.X86_64.Archi.ptr64 then
        .Vlong (Ptrofs.to_int64 (Ptrofs.of_int64 i))
       else
        .Vint (Ptrofs.to_int (Ptrofs.of_int64 i)))

def make_ptrofs_of_int_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) e le m a i si,
    T_eval_expr ge e le m a (.Vint i) →
    T_eval_expr ge e le m
      (if CompCert4Lean.X86_64.Archi.ptr64 then make_longofint a si else a)
      (if CompCert4Lean.X86_64.Archi.ptr64 then
        .Vlong (Ptrofs.to_int64 (ptrofs_of_int si i))
       else
        .Vint (Ptrofs.to_int (ptrofs_of_int si i)))

def make_ptrofsconst_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) n e le m,
    T_eval_expr ge e le m (make_ptrofsconst n)
      (if CompCert4Lean.X86_64.Archi.ptr64 then
        .Vlong (CompCert4Lean.Lib.Integers.Int64.repr n)
       else
        .Vint (CompCert4Lean.Lib.Integers.Int.repr n))

def make_shl_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv), shift_constructor_correct ge make_shl sem_shl

def make_shr_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv), shift_constructor_correct ge make_shr sem_shr

def make_singleconst_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) n e le m,
    T_eval_expr ge e le m (make_singleconst n) (.Vsingle n)

def make_store_bitfield_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (ge : TGenv) (prog : CProgram) (f : TFunction)
    sz sg pos width dst src ty k e le m b ofs v m' s,
    T_eval_expr ge e le m dst (.Vptr b ofs) →
    T_eval_expr ge e le m src v →
    Clight.assign_loc prog.prog_comp_env ty m b ofs (.Bits sz sg pos width) v m' →
    make_store_bitfield sz sg pos width dst src = .OK s →
    T_step xi ge (.State f s k e le m) E0
      (.State f .Sskip k e le m')

def make_store_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (ge : TGenv) (cunit prog : CProgram)
    addr ty bf rhs code e le m b ofs v m' f k,
    Ctypes.linkorder_program cunit prog →
    make_store cunit.prog_comp_env addr ty bf rhs = .OK code →
    T_eval_expr ge e le m addr (.Vptr b ofs) →
    T_eval_expr ge e le m rhs v →
    Clight.assign_loc prog.prog_comp_env ty m b ofs bf v m' →
    T_step xi ge (.State f code k e le m) E0
      (.State f .Sskip k e le m')

def make_sub_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) (cunit prog : CProgram),
    Ctypes.linkorder_program cunit prog →
    binary_constructor_correct ge (make_sub cunit.prog_comp_env)
      (sem_sub prog.prog_comp_env)

def make_xor_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv), binary_constructor_correct ge make_xor sem_xor
def match_cont_call_contStatement : Prop :=
  ∀ (prog : CProgram) (tprog : TProgram)
    ce' nbrk' ncnt' ce tyret nbrk ncnt k tk,
    match_cont prog tprog ce tyret nbrk ncnt k tk →
    match_cont prog tprog ce' tyret nbrk' ncnt'
      (Clight.call_cont k) (Csharpminor.call_cont tk)

def match_cont_is_call_contStatement : Prop :=
  ∀ (prog : CProgram) (tprog : TProgram)
    ce tyret nbrk ncnt k tk ce' nbrk' ncnt',
    match_cont prog tprog ce tyret nbrk ncnt k tk →
    Clight.is_call_cont k →
    match_cont prog tprog ce' tyret nbrk' ncnt' k tk ∧
      Csharpminor.is_call_cont tk

def match_env_alloc_variablesStatement : Prop :=
  ∀ (prog cunit : CProgram) e1 m1 vars e2 m2 tvars te1,
    Ctypes.linkorder_program cunit prog →
    Clight.alloc_variables (Clight.globalenv prog) e1 m1 vars e2 m2 →
    CompCert4Lean.Common.Errors.mmap (transl_var cunit.prog_comp_env) vars = .OK tvars →
    match_env prog e1 te1 →
    ∃ te2,
      Csharpminor.alloc_variables te1 m1 tvars te2 m2 ∧
      match_env prog e2 te2

def match_env_emptyStatement : Prop :=
  ∀ (prog : CProgram), match_env prog Clight.empty_env Csharpminor.empty_env

def match_env_free_blocksStatement : Prop :=
  ∀ (prog : CProgram) e te m m',
    match_env prog e te →
    Mem.free_list m (Clight.blocks_of_env (Clight.globalenv prog) e) = some m' →
    Mem.free_list m (Csharpminor.blocks_of_env te) = some m'

def match_env_globalsStatement : Prop :=
  ∀ (prog : CProgram) e te id,
    match_env prog e te →
    PTree.get id e = none → PTree.get id te = none

def match_env_same_blocksStatement : Prop :=
  ∀ (prog : CProgram) e te,
    match_env prog e te →
    Csharpminor.blocks_of_env te =
      Clight.blocks_of_env (Clight.globalenv prog) e

def match_states_skipStatement : Prop :=
  ∀ (prog : CProgram) (tprog : TProgram) f e le te nbrk ncnt k tf tk m cu,
    Ctypes.linkorder_program cu prog →
    transl_function cu.prog_comp_env f = .OK tf →
    match_env prog e te →
    match_cont prog tprog cu.prog_comp_env f.fn_return nbrk ncnt k tk →
    match_states prog tprog
      (.State f .Sskip k e le m) (.State tf .Sskip tk te le m)

def match_transl_stepStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (tprog : TProgram) ts tk ts' tk' f te le m,
    match_transl (.Sblock ts) tk ts' tk' →
    star (T_step xi) (Genv.globalenv tprog)
      (.State f ts' tk' te le m) E0
      (.State f ts (.Kblock tk) te le m)

def senv_preservedStatement : Prop :=
  ∀ (prog : CProgram) (tprog : TProgram), match_prog prog tprog →
    Senv.equiv
      (Genv.to_senv (Clight.globalenv prog).genv_genv)
      (Genv.to_senv (Genv.globalenv tprog))

def small_shift_amount_1Statement : Prop :=
  ∀ i,
    Int64.ltu i Int64.iwordsize = true →
    Int.ltu (Int64.loword i) Int64.iwordsize' = true ∧
      Int64.unsigned i = Int.unsigned (Int64.loword i)

def small_shift_amount_2Statement : Prop :=
  ∀ i,
    Int64.ltu i (Int64.repr (zOfInt (Int.ofNat 32))) = true →
    Int.ltu (Int64.loword i) Int.iwordsize = true

def small_shift_amount_3Statement : Prop :=
  ∀ i,
    Int.ltu i Int64.iwordsize' = true →
    Int64.unsigned (Int64.repr (Int.unsigned i)) = Int.unsigned i

def symbols_preservedStatement : Prop :=
  ∀ (prog : CProgram) (tprog : TProgram), match_prog prog tprog →
    ∀ s, Genv.find_symbol (Genv.globalenv tprog) s =
      Genv.find_symbol (Clight.globalenv prog).genv_genv s

def transf_program_matchStatement : Prop :=
  ∀ (p : CProgram) tp, transl_program p = .OK tp → match_prog p tp

def transl_alignofStatement : Prop :=
  ∀ (cunit prog : CProgram) t al,
    Ctypes.linkorder_program cunit prog →
    Cshmgen.alignof cunit.prog_comp_env t = .OK al →
    al = Ctypes.alignof prog.prog_comp_env t

def transl_alignof_blockcopyStatement : Prop :=
  ∀ (cunit prog : CProgram) t sz,
    Ctypes.linkorder_program cunit prog →
    Cshmgen.sizeof cunit.prog_comp_env t = .OK sz →
    sz = Ctypes.sizeof prog.prog_comp_env t ∧
      alignof_blockcopy cunit.prog_comp_env t =
        alignof_blockcopy prog.prog_comp_env t

def transl_arglist_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (prog cunit : CProgram) (tprog : TProgram) (e : CEnv) (le : CTempEnv)
    (m : mem) (te : TEnv) (al : List CExpr) (tyl : List CType) (vl : List val),
    match_prog prog tprog →
    Ctypes.linkorder_program cunit prog →
    match_env prog e te →
    C_eval_exprlist (Clight.globalenv prog) e le m al tyl vl →
    ∀ tal, transl_arglist cunit.prog_comp_env al tyl = .OK tal →
      T_eval_exprlist (Genv.globalenv tprog) te le m tal vl

def transl_arglist_typedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (prog : CProgram) e le m (al : List CExpr) (tyl : List CType) (vl : List val),
    C_eval_exprlist (Clight.globalenv prog) e le m al tyl vl →
    Val.has_argtype_list vl (tyl.map argtype_of_type)

def transl_binop_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) (cunit prog : CProgram) op a tya b tyb c va vb v e le m,
    Ctypes.linkorder_program cunit prog →
    transl_binop cunit.prog_comp_env op a tya b tyb = .OK c →
    sem_binary_operation prog.prog_comp_env op va tya vb tyb m = some v →
    T_eval_expr ge e le m a va → T_eval_expr ge e le m b vb →
    T_eval_expr ge e le m c v

def transl_expr_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (prog cunit : CProgram) (tprog : TProgram) (e : CEnv) (te : TEnv)
    (le : CTempEnv) (m : mem) (a : CExpr) (v : val),
    match_prog prog tprog →
    Ctypes.linkorder_program cunit prog →
    match_env prog e te →
    C_eval_expr (Clight.globalenv prog) e le m a v →
    ∀ ta, transl_expr cunit.prog_comp_env a = .OK ta →
      T_eval_expr (Genv.globalenv tprog) te le m ta v

def transl_expr_lvalueStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (prog cunit : CProgram) (e : CEnv) (le : CTempEnv) (m : mem)
    a loc ofs bf ta,
    Ctypes.linkorder_program cunit prog →
    C_eval_lvalue (Clight.globalenv prog) e le m a loc ofs bf →
    transl_expr cunit.prog_comp_env a = .OK ta →
    ∃ tb, transl_lvalue cunit.prog_comp_env a = .OK (tb, bf) ∧
      make_load tb (Clight.typeof a) bf = .OK ta

def transl_expr_lvalue_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (prog cunit : CProgram) (tprog : TProgram) (e : CEnv) (te : TEnv)
    (le : CTempEnv) (m : mem),
    match_prog prog tprog →
    Ctypes.linkorder_program cunit prog →
    match_env prog e te →
    (∀ a v, C_eval_expr (Clight.globalenv prog) e le m a v →
      ∀ ta, transl_expr cunit.prog_comp_env a = .OK ta →
        T_eval_expr (Genv.globalenv tprog) te le m ta v) ∧
    (∀ a b ofs bf, C_eval_lvalue (Clight.globalenv prog) e le m a b ofs bf →
      ∀ ta bf', transl_lvalue cunit.prog_comp_env a = .OK (ta, bf') →
        bf = bf' ∧ T_eval_expr (Genv.globalenv tprog) te le m ta
          (.Vptr b ofs))

def transl_final_statesStatement : Prop :=
  ∀ (prog : CProgram) (tprog : TProgram) S R r,
    match_prog prog tprog →
    match_states prog tprog S R →
    Clight.final_state S r → Csharpminor.final_state R r

def transl_find_labelStatement : Prop :=
  ∀ (prog : CProgram) (tprog : TProgram) lbl ce tyret s nbrk ncnt k ts tk,
    transl_statement ce tyret nbrk ncnt s = .OK ts →
    match_cont prog tprog ce tyret nbrk ncnt k tk →
    match Clight.find_label lbl s k with
    | none => Csharpminor.find_label lbl ts tk = none
    | some (s', k') =>
        ∃ ts' tk' nbrk' ncnt',
          Csharpminor.find_label lbl ts tk = some (ts', tk') ∧
          transl_statement ce tyret nbrk' ncnt' s' = .OK ts' ∧
          match_cont prog tprog ce tyret nbrk' ncnt' k' tk'

def transl_fundef_sig1Statement : Prop :=
  ∀ (p : CProgram) f tf args res cc,
    match_fundef p f tf →
    classify_fun (Clight.type_of_fundef f) =
      classify_fun (.Tfunction args res cc) →
    Csharpminor.funsig tf = Ctypes.signature_of_type args res cc

def transl_fundef_sig2Statement : Prop :=
  ∀ (p : CProgram) f tf args res cc,
    match_fundef p f tf →
    Clight.type_of_fundef f = .Tfunction args res cc →
    Csharpminor.funsig tf = Ctypes.signature_of_type args res cc

def transl_initial_statesStatement : Prop :=
  ∀ (prog : CProgram) (tprog : TProgram), match_prog prog tprog →
    ∀ S, Clight.initial_state prog S →
      ∃ R, Csharpminor.initial_state tprog R ∧ match_states prog tprog S R

def transl_lbl_stmt_1Statement : Prop :=
  ∀ ce tyret nbrk ncnt n sl tsl,
    transl_lbl_stmt ce tyret nbrk ncnt sl = .OK tsl →
    transl_lbl_stmt ce tyret nbrk ncnt (Clight.select_switch n sl) =
      .OK (Csharpminor.select_switch n tsl)

def transl_lbl_stmt_2Statement : Prop :=
  ∀ ce tyret nbrk ncnt sl tsl,
    transl_lbl_stmt ce tyret nbrk ncnt sl = .OK tsl →
    transl_statement ce tyret nbrk ncnt (Clight.seq_of_labeled_statement sl) =
      .OK (Csharpminor.seq_of_lbl_stmt tsl)

def transl_lvalue_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (prog cunit : CProgram) (tprog : TProgram) (e : CEnv) (te : TEnv)
    (le : CTempEnv) (m : mem) a b ofs bf,
    match_prog prog tprog →
    Ctypes.linkorder_program cunit prog →
    match_env prog e te →
    C_eval_lvalue (Clight.globalenv prog) e le m a b ofs bf →
    ∀ ta bf', transl_lvalue cunit.prog_comp_env a = .OK (ta, bf') →
      bf = bf' ∧ T_eval_expr (Genv.globalenv tprog) te le m ta
        (.Vptr b ofs)

def transl_program_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (prog : CProgram) (tprog : TProgram), match_prog prog tprog →
    forward_simulation (C_semantics2 xi prog)
      (T_semantics xi tprog)

def transl_sizeofStatement : Prop :=
  ∀ (cunit prog : CProgram) t sz,
    Ctypes.linkorder_program cunit prog →
    Cshmgen.sizeof cunit.prog_comp_env t = .OK sz →
    sz = Ctypes.sizeof prog.prog_comp_env t

def transl_stepStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (prog : CProgram) (tprog : TProgram), match_prog prog tprog →
    ∀ S1 t S2, C_step2 xi (Clight.globalenv prog) S1 t S2 →
      ∀ T1, match_states prog tprog S1 T1 →
        ∃ T2,
          plus (T_step xi) (Genv.globalenv tprog) T1 t T2 ∧
          match_states prog tprog S2 T2

def transl_unop_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) op a tya c va v e le m,
    transl_unop op a tya = .OK c →
    sem_unary_operation op va tya m = some v →
    T_eval_expr ge e le m a va → T_eval_expr ge e le m c v

def transl_vars_namesStatement : Prop :=
  ∀ ce vars tvars,
    CompCert4Lean.Common.Errors.mmap (transl_var ce) vars = .OK tvars →
    tvars.map Prod.fst = Clight.var_names vars

def typlist_of_arglist_eqStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (prog : CProgram) e le m (al : List CExpr) (tyl : List CType) (vl : List val),
    C_eval_exprlist (Clight.globalenv prog) e le m al tyl vl →
    typlist_of_arglist al tyl = tyl.map argtype_of_type

def union_field_offset_stableStatement : Prop :=
  ∀ (cunit prog : CProgram) id co f,
    Ctypes.linkorder_program cunit prog →
    PTree.get id cunit.prog_comp_env = some co →
    PTree.get id prog.prog_comp_env = some co ∧
      Ctypes.union_field_offset prog.prog_comp_env f co.co_members =
        Ctypes.union_field_offset cunit.prog_comp_env f co.co_members

end CompCert4Lean.Cfrontend.Cshmgenproof
