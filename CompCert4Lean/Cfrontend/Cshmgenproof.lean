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
private abbrev TBinaryOp := CompCert4Lean.Backend.Cminor.binary_operation
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
  | match_Kstop (ce : CType) (tyret : composite_env) (nbrk ncnt : Nat) :
      match_cont prog tprog tyret ce nbrk ncnt .Kstop .Kstop
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
  ∀ (sz : IntSize) (pos width : Z),
    0 ≤ pos → 0 < width → pos + width ≤ Cop.bitsize_carrier sz →
    (0 ≤ Cop.first_bit sz pos width ∧
      Cop.first_bit sz pos width < CompCert4Lean.Lib.Integers.Int.zwordsize) ∧
    (0 ≤ CompCert4Lean.Lib.Integers.Int.zwordsize - Cop.first_bit sz pos width - width ∧
      CompCert4Lean.Lib.Integers.Int.zwordsize - Cop.first_bit sz pos width - width <
        CompCert4Lean.Lib.Integers.Int.zwordsize)

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
  ∀ x : Z, (0 ≤ x ∧ x < CompCert4Lean.Lib.Integers.Int.zwordsize) →
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
  ∀ (cunit prog : CProgram),
    Ctypes.linkorder_program cunit prog →
    ∀ (ge : TGenv),
      binary_constructor_correct ge (make_add cunit.prog_comp_env)
        (sem_add prog.prog_comp_env)

def make_and_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv), binary_constructor_correct ge make_and sem_and

def make_binarith_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv)
    (sem_int : Signedness → CCInt → CCInt → Option val)
    (sem_long : Signedness → CCInt64 → CCInt64 → Option val)
    (sem_float : CCFloat → CCFloat → Option val)
    (sem_single : CCFloat32 → CCFloat32 → Option val)
    (iop iopu fop sop lop lopu : TBinaryOp),
    (∀ (x y : CCInt) (m : mem),
      Csharpminor.eval_binop iop (.Vint x) (.Vint y) m = sem_int .Signed x y) →
    (∀ (x y : CCInt) (m : mem),
      Csharpminor.eval_binop iopu (.Vint x) (.Vint y) m = sem_int .Unsigned x y) →
    (∀ (x y : CCInt64) (m : mem),
      Csharpminor.eval_binop lop (.Vlong x) (.Vlong y) m = sem_long .Signed x y) →
    (∀ (x y : CCInt64) (m : mem),
      Csharpminor.eval_binop lopu (.Vlong x) (.Vlong y) m = sem_long .Unsigned x y) →
    (∀ (x y : CCFloat) (m : mem),
      Csharpminor.eval_binop fop (.Vfloat x) (.Vfloat y) m = sem_float x y) →
    (∀ (x y : CCFloat32) (m : mem),
      Csharpminor.eval_binop sop (.Vsingle x) (.Vsingle y) m = sem_single x y) →
    binary_constructor_correct ge
      (make_binarith iop iopu fop sop lop lopu)
      (sem_binarith sem_int sem_long sem_float sem_single)

def make_binarith_int_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv)
    (sem_int : Signedness → CCInt → CCInt → Option val)
    (sem_long : Signedness → CCInt64 → CCInt64 → Option val)
    (iop iopu lop lopu : TBinaryOp),
    (∀ (x y : CCInt) (m : mem),
      Csharpminor.eval_binop iop (.Vint x) (.Vint y) m = sem_int .Signed x y) →
    (∀ (x y : CCInt) (m : mem),
      Csharpminor.eval_binop iopu (.Vint x) (.Vint y) m = sem_int .Unsigned x y) →
    (∀ (x y : CCInt64) (m : mem),
      Csharpminor.eval_binop lop (.Vlong x) (.Vlong y) m = sem_long .Signed x y) →
    (∀ (x y : CCInt64) (m : mem),
      Csharpminor.eval_binop lopu (.Vlong x) (.Vlong y) m = sem_long .Unsigned x y) →
    binary_constructor_correct ge
      (make_binarith_int iop iopu lop lopu)
      (sem_binarith sem_int sem_long (fun _ _ => none) (fun _ _ => none))

def make_boolean_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (ge : TGenv) e le m a v ty b,
    T_eval_expr ge e le m a v → bool_val v ty m = some b →
    ∃ vb,
      T_eval_expr ge e le m (make_boolean a ty) vb ∧
        Val.bool_of_val vb b

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
    (cunit prog : CProgram),
    Ctypes.linkorder_program cunit prog →
    ∀ (ge : TGenv)
    (f : TFunction) dst src ty k e le m b ofs v m' s,
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
      (Vptrofs (Ptrofs.repr n))

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
    (prog : CProgram) (ge : TGenv) (f : TFunction)
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
    (cunit prog : CProgram),
    Ctypes.linkorder_program cunit prog →
    ∀ (ge : TGenv)
    addr ty bf rhs code e le m b ofs v m' f k,
    make_store cunit.prog_comp_env addr ty bf rhs = .OK code →
    T_eval_expr ge e le m addr (.Vptr b ofs) →
    T_eval_expr ge e le m rhs v →
    Clight.assign_loc prog.prog_comp_env ty m b ofs bf v m' →
    T_step xi ge (.State f code k e le m) E0
      (.State f .Sskip k e le m')

def make_sub_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cunit prog : CProgram),
    Ctypes.linkorder_program cunit prog →
    ∀ (ge : TGenv),
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
  ∀ (prog cunit : CProgram),
    Ctypes.linkorder_program cunit prog →
    ∀ e1 m1 vars e2 m2,
    Clight.alloc_variables (Clight.globalenv prog) e1 m1 vars e2 m2 →
    ∀ tvars te1,
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
  ∀ (prog : CProgram) (tprog : TProgram),
    match_prog prog tprog →
    ∀ (cunit : CProgram),
    Ctypes.linkorder_program cunit prog →
    ∀ (e : CEnv) (le : CTempEnv) (m : mem) (te : TEnv),
    match_env prog e te →
    ∀ (al : List CExpr) (tyl : List CType) (vl : List val),
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
  ∀ (cunit prog : CProgram),
    Ctypes.linkorder_program cunit prog →
    ∀ (ge : TGenv) op a tya b tyb c va vb v e le m,
    transl_binop cunit.prog_comp_env op a tya b tyb = .OK c →
    sem_binary_operation prog.prog_comp_env op va tya vb tyb m = some v →
    T_eval_expr ge e le m a va → T_eval_expr ge e le m b vb →
    T_eval_expr ge e le m c v

def transl_expr_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (prog : CProgram) (tprog : TProgram),
    match_prog prog tprog →
    ∀ (cunit : CProgram),
    Ctypes.linkorder_program cunit prog →
    ∀ (e : CEnv) (le : CTempEnv) (m : mem) (te : TEnv),
    match_env prog e te →
    ∀ (a : CExpr) (v : val),
    C_eval_expr (Clight.globalenv prog) e le m a v →
    ∀ ta, transl_expr cunit.prog_comp_env a = .OK ta →
      T_eval_expr (Genv.globalenv tprog) te le m ta v

def transl_expr_lvalueStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (prog cunit : CProgram),
    Ctypes.linkorder_program cunit prog →
    ∀ (e : CEnv) (le : CTempEnv) (m : mem)
    a loc ofs bf ta,
    C_eval_lvalue (Clight.globalenv prog) e le m a loc ofs bf →
    transl_expr cunit.prog_comp_env a = .OK ta →
    ∃ tb, transl_lvalue cunit.prog_comp_env a = .OK (tb, bf) ∧
      make_load tb (Clight.typeof a) bf = .OK ta

def transl_expr_lvalue_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (prog : CProgram) (tprog : TProgram),
    match_prog prog tprog →
    ∀ (cunit : CProgram),
    Ctypes.linkorder_program cunit prog →
    ∀ (e : CEnv) (le : CTempEnv) (m : mem) (te : TEnv),
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
    match_states prog tprog S R →
    Clight.final_state S r → Csharpminor.final_state R r

def transl_find_labelStatement : Prop :=
  ∀ (prog : CProgram) (tprog : TProgram) ce lbl tyret s nbrk ncnt k ts tk,
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
  ∀ (prog : CProgram) (tprog : TProgram),
    match_prog prog tprog →
    ∀ (cunit : CProgram),
    Ctypes.linkorder_program cunit prog →
    ∀ (e : CEnv) (le : CTempEnv) (m : mem) (te : TEnv) a b ofs bf,
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

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Cfrontend.Cshmgen
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Coqlib

private theorem transl_fundef_match (p : CompCert4Lean.Cfrontend.Clight.program)
    (i : ident) (f : CompCert4Lean.Cfrontend.Clight.fundef) tf :
    Cshmgen.transl_fundef p.prog_comp_env i f = .OK tf →
      ∃ cu, Ctypes.linkorder_program cu p ∧ match_fundef cu f tf := by
  intro h
  cases f with
  | Internal g =>
    simp only [Cshmgen.transl_fundef] at h
    cases htf : Cshmgen.transl_function p.prog_comp_env g with
    | Error msg => simp [htf] at h
    | OK tg =>
      simp [htf] at h
      cases h
      exact ⟨p, by
        unfold Ctypes.linkorder_program
        constructor
        · exact Linker.linkorder_refl (Ctypes.program_of_program p)
        · intro id co hget; exact hget,
        .match_fundef_internal g tg htf⟩
  | External ef args res cc =>
    simp only [Cshmgen.transl_fundef] at h
    generalize heq : CompCert4Lean.Common.AST.signature_eq
      (CompCert4Lean.Common.AST.ef_sig ef)
      (Ctypes.signature_of_type args res cc) = d at h
    cases d with
    | left hs =>
      simp [heq] at h
      cases h
      exact ⟨p, by
        unfold Ctypes.linkorder_program
        constructor
        · exact Linker.linkorder_refl (Ctypes.program_of_program p)
        · intro id co hget; exact hget,
        .match_fundef_external ef args res cc hs⟩
    | right hs =>
      simp [heq] at h
      cases h

private theorem transl_defs_match (p : CompCert4Lean.Cfrontend.Clight.program) :
  ∀ (src : List (CompCert4Lean.Common.AST.ident ×
      CompCert4Lean.Common.AST.globdef
        (CompCert4Lean.Cfrontend.Clight.fundef)
        CompCert4Lean.Cfrontend.Ctypes.type))
    (defs : List (CompCert4Lean.Common.AST.ident ×
      CompCert4Lean.Common.AST.globdef
        (CompCert4Lean.Cfrontend.Csharpminor.fundef) Unit)),
    CompCert4Lean.Common.AST.transf_globdefs
      (CompCert4Lean.Cfrontend.Cshmgen.transl_fundef p.prog_comp_env)
      CompCert4Lean.Cfrontend.Cshmgen.transl_globvar src = .OK defs →
    list_forall2 (fun idg tidg => idg.1 = tidg.1 ∧
      match idg.2, tidg.2 with
      | .Gfun f, .Gfun tf =>
          ∃ cu, Ctypes.linkorder_program cu p ∧ match_fundef cu f tf
      | .Gvar v, .Gvar tv =>
          match_varinfo v.gvar_info tv.gvar_info ∧
            v.gvar_init = tv.gvar_init ∧
            v.gvar_readonly = tv.gvar_readonly ∧
            v.gvar_volatile = tv.gvar_volatile
      | _, _ => False) src defs := by
  intro src
  induction src with
  | nil =>
      intro defs h
      simp only [transf_globdefs] at h
      cases h
      exact list_forall2_nil _
  | cons hd tl ih =>
      intro defs h
      rcases hd with ⟨id, gd⟩
      cases gd with
      | Gfun f =>
          simp only [transf_globdefs] at h
          cases htf : Cshmgen.transl_fundef p.prog_comp_env id f with
          | Error msg => simp [htf] at h
          | OK tf =>
            cases htl : transf_globdefs
                (Cshmgen.transl_fundef p.prog_comp_env)
                Cshmgen.transl_globvar tl with
            | Error msg => simp [htf, htl] at h
            | OK defsTail =>
              simp [htf, htl] at h
              cases h
              apply list_forall2.cons
              · constructor
                · rfl
                · change ∃ cu, Ctypes.linkorder_program cu p ∧
                    match_fundef cu f tf
                  exact transl_fundef_match p id f tf htf
              · exact ih defsTail htl
      | Gvar v =>
          simp only [transf_globdefs] at h
          have hvar : CompCert4Lean.Common.AST.transf_globvar
              Cshmgen.transl_globvar id v =
              .OK ({ gvar_info := (), gvar_init := v.gvar_init, gvar_readonly := v.gvar_readonly, gvar_volatile := v.gvar_volatile } :
                CompCert4Lean.Common.AST.globvar Unit) := by
            rfl
          cases htl : transf_globdefs
              (Cshmgen.transl_fundef p.prog_comp_env)
              Cshmgen.transl_globvar tl with
          | Error msg =>
            rw [hvar, htl] at h
            cases h
          | OK defsTail =>
              rw [hvar, htl] at h
              cases h
              apply list_forall2.cons
              · constructor
                · rfl
                · change match_varinfo v.gvar_info () ∧
                    v.gvar_init = v.gvar_init ∧
                    v.gvar_readonly = v.gvar_readonly ∧
                    v.gvar_volatile = v.gvar_volatile
                  exact ⟨True.intro, rfl, rfl, rfl⟩
              · exact ih defsTail htl

theorem transf_program_match : transf_program_matchStatement := by
  intro p tp h
  unfold Cshmgen.transl_program at h
  unfold transform_partial_program2 at h
  cases hdefs : transf_globdefs (transl_fundef p.prog_comp_env)
      transl_globvar (program_of_program p).prog_defs with
  | Error msg => simp [hdefs] at h
  | OK defs =>
    simp [hdefs] at h
    cases h
    unfold match_prog
    refine ⟨transl_defs_match p (program_of_program p).prog_defs defs hdefs,
      rfl, rfl⟩

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Cshmgen
open CompCert4Lean.Cfrontend.Csharpminor
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Lib.Maps

private theorem transl_sizeof_stable_local (env1 env2 : composite_env) :
    (forall id co, PTree.get id env1 = some co -> PTree.get id env2 = some co) ->
    forall t, Ctypes.complete_type env1 t = true -> Ctypes.sizeof env2 t = Ctypes.sizeof env1 t := by
  intro henv t hcomplete
  induction t using Ctypes.type.rec (motive_2 := fun _ => True) with
  | Tvoid => rfl
  | Tint s sg a => cases s <;> rfl
  | Tlong sg a => rfl
  | Tfloat s a => cases s <;> rfl
  | Tpointer t a ih => rfl
  | Tarray t n a ih =>
    simp only [Ctypes.complete_type] at hcomplete
    simp [Ctypes.sizeof, ih hcomplete]
  | Tfunction args res cc ihargs ihres => rfl
  | Tstruct id a =>
    cases hget : PTree.get id env1 with
    | none => simp [Ctypes.complete_type, hget] at hcomplete
    | some co =>
      have hget2 := henv id co hget
      simp [Ctypes.sizeof, hget, hget2]
  | Tunion id a =>
    cases hget : PTree.get id env1 with
    | none => simp [Ctypes.complete_type, hget] at hcomplete
    | some co =>
      have hget2 := henv id co hget
      simp [Ctypes.sizeof, hget, hget2]
  | nil => trivial
  | cons head tail ihhead ihtail => trivial

private theorem transl_alignof_stable_local (env1 env2 : composite_env) :
    (forall id co, PTree.get id env1 = some co -> PTree.get id env2 = some co) ->
    forall t, Ctypes.complete_type env1 t = true -> Ctypes.alignof env2 t = Ctypes.alignof env1 t := by
  intro henv t hcomplete
  induction t using Ctypes.type.rec (motive_2 := fun _ => True) with
  | Tvoid => rfl
  | Tint s sg a => cases s <;> rfl
  | Tlong sg a => rfl
  | Tfloat s a => cases s <;> rfl
  | Tpointer t a ih => rfl
  | Tarray t n a ih =>
    simp only [Ctypes.complete_type] at hcomplete
    simp [Ctypes.alignof, ih hcomplete]
  | Tfunction args res cc ihargs ihres => rfl
  | Tstruct id a =>
    cases hget : PTree.get id env1 with
    | none => simp [Ctypes.complete_type, hget] at hcomplete
    | some co =>
      have hget2 := henv id co hget
      simp [Ctypes.alignof, hget, hget2]
  | Tunion id a =>
    cases hget : PTree.get id env1 with
    | none => simp [Ctypes.complete_type, hget] at hcomplete
    | some co =>
      have hget2 := henv id co hget
      simp [Ctypes.alignof, hget, hget2]
  | nil => trivial
  | cons head tail ihhead ihtail => trivial

theorem transl_fundef_sig1 : transl_fundef_sig1Statement := by
  intro p f tf args res cc hmatch hclass
  cases hmatch with
  | match_fundef_internal f tf htrans =>
    unfold Cshmgen.transl_function at htrans
    cases hbody : Cshmgen.transl_statement p.prog_comp_env f.fn_return 1 0 f.fn_body with
    | Error msg => simp [hbody] at htrans
    | OK tbody =>
      cases hvars : CompCert4Lean.Common.Errors.mmap
          (Cshmgen.transl_var p.prog_comp_env) f.fn_vars with
      | Error msg => simp [hbody, hvars] at htrans
      | OK tvars =>
        simp [hbody, hvars] at htrans
        cases htrans
        obtain ⟨hargs, hres, hcc⟩ := by
          simpa [Clight.type_of_fundef, Clight.type_of_function, classify_fun] using hclass
        subst args
        subst res
        subst cc
        change Cshmgen.signature_of_function f =
          Ctypes.signature_of_type (Ctypes.type_of_params f.fn_params) f.fn_return f.fn_callconv
        simp [Cshmgen.signature_of_function, Ctypes.signature_of_type,
          Ctypes.type_of_params, List.map_map]
  | match_fundef_external ef args0 res0 cc0 hsig =>
    obtain ⟨hargs, hres, hcc⟩ := by
      simpa [Clight.type_of_fundef, classify_fun] using hclass
    subst args
    subst res
    subst cc
    change CompCert4Lean.Common.AST.ef_sig ef = Ctypes.signature_of_type args0 res0 cc0
    exact hsig

theorem transl_fundef_sig2 : transl_fundef_sig2Statement := by
  intro p f tf args res cc hmatch htype
  apply transl_fundef_sig1 p f tf args res cc hmatch
  rw [htype]

theorem transl_sizeof : transl_sizeofStatement := by
  intro cunit prog t sz hlink hsize
  rcases hlink with ⟨_, henv⟩
  unfold Cshmgen.sizeof at hsize
  cases hcomplete : Ctypes.complete_type cunit.prog_comp_env t with
  | false =>
    simp [hcomplete] at hsize
    cases hsize
  | true =>
    simp [hcomplete] at hsize
    cases hsize
    exact (transl_sizeof_stable_local cunit.prog_comp_env prog.prog_comp_env henv t hcomplete).symm

theorem transl_alignof : transl_alignofStatement := by
  intro cunit prog t al hlink halign
  rcases hlink with ⟨_, henv⟩
  unfold Cshmgen.alignof at halign
  cases hcomplete : Ctypes.complete_type cunit.prog_comp_env t with
  | false =>
    simp [hcomplete] at halign
    cases halign
  | true =>
    simp [hcomplete] at halign
    cases halign
    exact (transl_alignof_stable_local cunit.prog_comp_env prog.prog_comp_env henv t hcomplete).symm

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Cshmgen
open CompCert4Lean.Cfrontend.Csharpminor
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Maps

private theorem alignof_blockcopy_stable_local (env1 env2 : composite_env)
    (henv : forall id co, PTree.get id env1 = some co -> PTree.get id env2 = some co) :
    forall t, Ctypes.complete_type env1 t = true →
      Ctypes.alignof_blockcopy env1 t = Ctypes.alignof_blockcopy env2 t := by
  intro t hcomplete
  induction t using Ctypes.type.rec (motive_2 := fun _ => True) with
  | Tvoid => rfl
  | Tint s sg a => cases s <;> rfl
  | Tlong sg a => rfl
  | Tfloat s a => cases s <;> rfl
  | Tpointer t a => rfl
  | Tarray t n a ih =>
      simp only [Ctypes.complete_type] at hcomplete
      exact ih hcomplete
  | Tfunction args res cc ihargs ihres => rfl
  | Tstruct id a =>
      cases hget : PTree.get id env1 with
      | none => simp [Ctypes.complete_type, hget] at hcomplete
      | some co =>
          have hget2 := henv id co hget
          simp [Ctypes.alignof_blockcopy, hget, hget2]
  | Tunion id a =>
      cases hget : PTree.get id env1 with
      | none => simp [Ctypes.complete_type, hget] at hcomplete
      | some co =>
          have hget2 := henv id co hget
          simp [Ctypes.alignof_blockcopy, hget, hget2]
  | nil => trivial
  | cons head tail ihhead ihtail => trivial

theorem transl_alignof_blockcopy : transl_alignof_blockcopyStatement := by
  intro cunit prog t sz hlink hsize
  rcases hlink with ⟨_, henv⟩
  unfold Cshmgen.sizeof at hsize
  cases hcomplete : Ctypes.complete_type cunit.prog_comp_env t with
  | false =>
    simp [hcomplete] at hsize
    cases hsize
  | true =>
    simp [hcomplete] at hsize
    cases hsize
    constructor
    · exact (transl_sizeof_stable_local cunit.prog_comp_env prog.prog_comp_env
        henv t hcomplete).symm
    · exact alignof_blockcopy_stable_local cunit.prog_comp_env prog.prog_comp_env
        henv t hcomplete

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Cshmgen
open CompCert4Lean.Cfrontend.Csharpminor

theorem transl_lbl_stmt_1 : transl_lbl_stmt_1Statement := by
  intro ce tyret nbrk ncnt n sl tsl h
  have hdefault : ∀ sl tsl,
      transl_lbl_stmt ce tyret nbrk ncnt sl = .OK tsl →
      transl_lbl_stmt ce tyret nbrk ncnt (Clight.select_switch_default sl) =
        .OK (Csharpminor.select_switch_default tsl) := by
    intro sl
    induction sl using Clight.labeled_statements.rec
      (motive_1 := fun _ => True) with
    | Sskip | Sassign _ _ | Sset _ _ | Scall _ _ _ | Sbuiltin _ _ _ _
    | Ssequence _ _ _ _ | Sifthenelse _ _ _ _ _ | Sloop _ _ _ _
    | Sbreak | Scontinue | Sreturn _ | Sswitch _ _ _ | Slabel _ _ _ | Sgoto _ =>
        trivial
    | LSnil =>
        intro tsl h
        simp [Clight.select_switch_default, Csharpminor.select_switch_default] at *
        cases h
        rfl
    | LScons lbl stmt rest ihstmt ihrest =>
        intro tsl h
        cases lbl with
        | none =>
            simp only [Cshmgen.transl_lbl_stmt] at h
            cases hstmt : transl_statement ce tyret nbrk ncnt stmt with
            | Error msg => simp [hstmt] at h
            | OK tstmt =>
                cases hrest : transl_lbl_stmt ce tyret nbrk ncnt rest with
                | Error msg => simp [hstmt, hrest] at h
                | OK trest =>
                    simp [hstmt, hrest] at h
                    cases h
                    simp [Clight.select_switch_default, Csharpminor.select_switch_default,
                      Cshmgen.transl_lbl_stmt, hstmt, hrest]
        | some l =>
            simp only [Cshmgen.transl_lbl_stmt] at h
            cases hstmt : transl_statement ce tyret nbrk ncnt stmt with
            | Error msg => simp [hstmt] at h
            | OK tstmt =>
                cases hrest : transl_lbl_stmt ce tyret nbrk ncnt rest with
                | Error msg => simp [hstmt, hrest] at h
                | OK trest =>
                    simp [hstmt, hrest] at h
                    cases h
                    simpa [Clight.select_switch_default, Csharpminor.select_switch_default] using
                      (ihrest trest hrest)
  have hcase : ∀ sl tsl,
      transl_lbl_stmt ce tyret nbrk ncnt sl = .OK tsl →
      match Clight.select_switch_case n sl with
      | none => Csharpminor.select_switch_case n tsl = none
      | some sl' => ∃ tsl',
          Csharpminor.select_switch_case n tsl = some tsl' ∧
          transl_lbl_stmt ce tyret nbrk ncnt sl' = .OK tsl' := by
    intro sl
    induction sl using Clight.labeled_statements.rec
      (motive_1 := fun _ => True) with
    | Sskip | Sassign _ _ | Sset _ _ | Scall _ _ _ | Sbuiltin _ _ _ _
    | Ssequence _ _ _ _ | Sifthenelse _ _ _ _ _ | Sloop _ _ _ _
    | Sbreak | Scontinue | Sreturn _ | Sswitch _ _ _ | Slabel _ _ _ | Sgoto _ =>
        trivial
    | LSnil =>
        intro tsl h
        simp only [Cshmgen.transl_lbl_stmt] at h
        cases h
        simp [Clight.select_switch_case, Csharpminor.select_switch_case]
    | LScons lbl stmt rest ihstmt ihrest =>
        intro tsl h
        simp only [Cshmgen.transl_lbl_stmt] at h
        cases hstmt : transl_statement ce tyret nbrk ncnt stmt with
        | Error msg => simp [hstmt] at h
        | OK tstmt =>
            cases hrest : transl_lbl_stmt ce tyret nbrk ncnt rest with
            | Error msg => simp [hstmt, hrest] at h
            | OK trest =>
                simp [hstmt, hrest] at h
                cases h
                cases lbl with
                | none => exact ihrest trest hrest
                | some l =>
                    simp only [Clight.select_switch_case, Csharpminor.select_switch_case]
                    cases hz : CompCert4Lean.Lib.Coqlib.zeq l n with
                    | left heq =>
                        subst n
                        exact ⟨Csharpminor.LScons (some l) tstmt trest, rfl,
                          by simp [Cshmgen.transl_lbl_stmt, hstmt, hrest]⟩
                    | right hneq =>
                        exact ihrest trest hrest
  unfold Clight.select_switch
  cases hsel : Clight.select_switch_case n sl with
  | some sl' =>
      have hinfo := hcase sl tsl h
      rw [hsel] at hinfo
      rcases hinfo with ⟨tsl', hts, htrans⟩
      unfold Csharpminor.select_switch
      rw [hts]
      exact htrans
  | none =>
      have hinfo := hcase sl tsl h
      rw [hsel] at hinfo
      unfold Csharpminor.select_switch
      rw [hinfo]
      exact hdefault sl tsl h

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Cfrontend.Cshmgen
open CompCert4Lean.Cfrontend.Csharpminor

theorem make_intconst_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_intconst_correctStatement := by
  intro ge n e le m
  apply Csharpminor.eval_Econst
  rfl

theorem make_floatconst_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_floatconst_correctStatement := by
  intro ge n e le m
  apply Csharpminor.eval_Econst
  rfl

theorem make_singleconst_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_singleconst_correctStatement := by
  intro ge n e le m
  apply Csharpminor.eval_Econst
  rfl

theorem transl_lbl_stmt_2 : transl_lbl_stmt_2Statement := by
  intro ce tyret nbrk ncnt sl
  induction sl using Clight.labeled_statements.rec
      (motive_1 := fun _ => True) with
  | Sskip | Sassign _ _ | Sset _ _ | Scall _ _ _ | Sbuiltin _ _ _ _
  | Ssequence _ _ _ _ | Sifthenelse _ _ _ _ _ | Sloop _ _ _ _
  | Sbreak | Scontinue | Sreturn _ | Sswitch _ _ _ | Slabel _ _ _ | Sgoto _ =>
      trivial
  | LSnil =>
      intro tsl h
      simp only [Cshmgen.transl_lbl_stmt] at h
      cases h
      rfl
  | LScons n s rest ihstmt ihrest =>
      intro tsl h
      simp only [Cshmgen.transl_lbl_stmt] at h
      cases hstmt : transl_statement ce tyret nbrk ncnt s with
      | Error msg =>
          simp [hstmt] at h
      | OK ts =>
          cases hrest : transl_lbl_stmt ce tyret nbrk ncnt rest with
          | Error msg =>
              simp [hstmt, hrest] at h
          | OK trs =>
              simp [hstmt, hrest] at h
              cases h
              simp only [Clight.seq_of_labeled_statement, Csharpminor.seq_of_lbl_stmt,
                Cshmgen.transl_statement, hstmt]
              rw [ihrest trs hrest]

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Cfrontend.Cshmgen
open CompCert4Lean.Cfrontend.Csharpminor
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Common.Values

theorem make_longconst_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_longconst_correctStatement := by
  intro ge n e le m
  apply Csharpminor.eval_Econst
  rfl

theorem make_cmpu_ne_zero_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_cmpu_ne_zero_correctStatement := by
  intro ge e le m a n ha
  have hdefault :
      Csharpminor.eval_expr ge e le m
        (Csharpminor.Ebinop (.Ocmpu .Cne) a
          (make_intconst CompCert4Lean.Lib.Integers.Int.zero))
        (.Vint (if CompCert4Lean.Lib.Integers.Int.eq n
            CompCert4Lean.Lib.Integers.Int.zero then
          CompCert4Lean.Lib.Integers.Int.zero else
          CompCert4Lean.Lib.Integers.Int.one)) := by
    apply Csharpminor.eval_Ebinop
    · exact ha
    · apply Csharpminor.eval_Econst
      rfl
    · cases hEq : decide (n.intval =
        CompCert4Lean.Lib.Integers.Int.zero.intval) <;>
        simp [Csharpminor.eval_binop, CompCert4Lean.Backend.Cminor.eval_binop,
          CompCert4Lean.Common.Values.Val.cmpu,
          CompCert4Lean.Common.Values.Val.cmpu_bool,
          CompCert4Lean.Lib.Integers.Int.cmpu, hEq,
          CompCert4Lean.Lib.Integers.Int.eq,
          CompCert4Lean.Lib.Integers.WordCore.cmpu,
          CompCert4Lean.Lib.Integers.WordCore.eq,
          CompCert4Lean.Common.Values.Val.of_optbool,
          CompCert4Lean.Common.Values.Vtrue,
          CompCert4Lean.Common.Values.Vfalse]
  have h_of_optbool : ∀ ob : Option Bool,
      CompCert4Lean.Common.Values.Val.of_optbool ob = .Vint n →
        n = if CompCert4Lean.Lib.Integers.Int.eq n
            CompCert4Lean.Lib.Integers.Int.zero then
          CompCert4Lean.Lib.Integers.Int.zero else
          CompCert4Lean.Lib.Integers.Int.one := by
    intro ob h
    cases ob with
    | none => simp [CompCert4Lean.Common.Values.Val.of_optbool] at h
    | some b =>
        cases b with
        | false =>
            change CompCert4Lean.Common.Values.Vint
                CompCert4Lean.Lib.Integers.Int.zero = .Vint n at h
            cases h
            rfl
        | true =>
            change CompCert4Lean.Common.Values.Vint
                CompCert4Lean.Lib.Integers.Int.one = .Vint n at h
            cases h
            by_cases hEq : CompCert4Lean.Lib.Integers.Int.eq
                CompCert4Lean.Lib.Integers.Int.one
                CompCert4Lean.Lib.Integers.Int.zero = true
            · have hz : CompCert4Lean.Lib.Integers.Int.one.intval =
                  CompCert4Lean.Lib.Integers.Int.zero.intval := by
                simpa [CompCert4Lean.Lib.Integers.Int.eq,
                  CompCert4Lean.Lib.Integers.WordCore.eq] using hEq
              exact False.elim ((by decide :
                CompCert4Lean.Lib.Integers.Int.one ≠
                  CompCert4Lean.Lib.Integers.Int.zero)
                (CompCert4Lean.Lib.Integers.WordCore.ext hz))
            · simp [hEq]
  have h_of_bool : ∀ b : Bool,
      CompCert4Lean.Common.Values.Val.of_bool b = .Vint n →
        n = if CompCert4Lean.Lib.Integers.Int.eq n
            CompCert4Lean.Lib.Integers.Int.zero then
          CompCert4Lean.Lib.Integers.Int.zero else
          CompCert4Lean.Lib.Integers.Int.one := by
    intro b h
    cases b with
    | false =>
        change CompCert4Lean.Common.Values.Vint
            CompCert4Lean.Lib.Integers.Int.zero = .Vint n at h
        cases h
        rfl
    | true =>
        change CompCert4Lean.Common.Values.Vint
            CompCert4Lean.Lib.Integers.Int.one = .Vint n at h
        cases h
        by_cases hEq : CompCert4Lean.Lib.Integers.Int.eq
            CompCert4Lean.Lib.Integers.Int.one
            CompCert4Lean.Lib.Integers.Int.zero = true
        · have hz : CompCert4Lean.Lib.Integers.Int.one.intval =
              CompCert4Lean.Lib.Integers.Int.zero.intval := by
            simpa [CompCert4Lean.Lib.Integers.Int.eq,
              CompCert4Lean.Lib.Integers.WordCore.eq] using hEq
          exact False.elim ((by decide :
            CompCert4Lean.Lib.Integers.Int.one ≠
              CompCert4Lean.Lib.Integers.Int.zero)
            (CompCert4Lean.Lib.Integers.WordCore.ext hz))
        · simp [hEq]
  cases a with
  | Evar id => exact hdefault
  | Eaddrof id => exact hdefault
  | Econst cst => exact hdefault
  | Eunop op a1 => exact hdefault
  | Eload chunk addr => exact hdefault
  | Ebinop op a1 a2 =>
      cases op with
      | Ocmp cmp =>
          cases ha with
          | eval_Ebinop _ _ _ v1 v2 _ h1 h2 hop =>
              have hop0 := hop
              change some (CompCert4Lean.Common.Values.Val.cmp cmp v1 v2) =
                some (.Vint n) at hop
              injection hop with hv
              have hn := h_of_optbool _ hv
              apply Csharpminor.eval_Ebinop
              · exact h1
              · exact h2
              · rw [← hn]
                exact hop0
      | Ocmpu cmp =>
          cases ha with
          | eval_Ebinop _ _ _ v1 v2 _ h1 h2 hop =>
              have hop0 := hop
              change some (CompCert4Lean.Common.Values.Val.cmpu
                (CompCert4Lean.Common.Memory.Mem.valid_pointer m) cmp v1 v2) =
                some (.Vint n) at hop
              injection hop with hv
              have hn := h_of_optbool _ hv
              apply Csharpminor.eval_Ebinop
              · exact h1
              · exact h2
              · rw [← hn]
                exact hop0
      | Ocmpf cmp =>
          cases ha with
          | eval_Ebinop _ _ _ v1 v2 _ h1 h2 hop =>
              have hop0 := hop
              change some (CompCert4Lean.Common.Values.Val.cmpf cmp v1 v2) =
                some (.Vint n) at hop
              injection hop with hv
              have hn := h_of_optbool _ hv
              apply Csharpminor.eval_Ebinop
              · exact h1
              · exact h2
              · rw [← hn]
                exact hop0
      | Ocmpfs cmp =>
          cases ha with
          | eval_Ebinop _ _ _ v1 v2 _ h1 h2 hop =>
              have hop0 := hop
              change some (CompCert4Lean.Common.Values.Val.cmpfs cmp v1 v2) =
                some (.Vint n) at hop
              injection hop with hv
              have hn := h_of_optbool _ hv
              apply Csharpminor.eval_Ebinop
              · exact h1
              · exact h2
              · rw [← hn]
                exact hop0
      | Ocmpl cmp =>
          cases ha with
          | eval_Ebinop _ _ _ v1 v2 _ h1 h2 hop =>
              have hop0 := hop
              change Option.map CompCert4Lean.Common.Values.Val.of_bool
                  (CompCert4Lean.Common.Values.Val.cmpl_bool cmp v1 v2) =
                some (.Vint n) at hop
              cases hbool : CompCert4Lean.Common.Values.Val.cmpl_bool cmp v1 v2 with
              | none => simp [hbool] at hop
              | some b =>
                  have hb : CompCert4Lean.Common.Values.Val.of_bool b = .Vint n := by
                    simpa [hbool] using hop
                  have hn := h_of_bool b hb
                  apply Csharpminor.eval_Ebinop
                  · exact h1
                  · exact h2
                  · rw [← hn]
                    exact hop0
      | Ocmplu cmp =>
          cases ha with
          | eval_Ebinop _ _ _ v1 v2 _ h1 h2 hop =>
              have hop0 := hop
              change Option.map CompCert4Lean.Common.Values.Val.of_bool
                  (CompCert4Lean.Common.Values.Val.cmplu_bool
                    (CompCert4Lean.Common.Memory.Mem.valid_pointer m) cmp v1 v2) =
                some (.Vint n) at hop
              cases hbool : CompCert4Lean.Common.Values.Val.cmplu_bool
                  (CompCert4Lean.Common.Memory.Mem.valid_pointer m) cmp v1 v2 with
              | none => simp [hbool] at hop
              | some b =>
                  have hb : CompCert4Lean.Common.Values.Val.of_bool b = .Vint n := by
                    simpa [hbool] using hop
                  have hn := h_of_bool b hb
                  apply Csharpminor.eval_Ebinop
                  · exact h1
                  · exact h2
                  · rw [← hn]
                    exact hop0
      | _ => exact hdefault

theorem make_cmpu_ne_zero_correct_ptr
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_cmpu_ne_zero_correct_ptrStatement := by
  intro ge e le m a b i ha hptr hvalid
  simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

theorem make_cast_int_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_cast_int_correctStatement := by
  intro ge e le m a n sz si ha
  cases sz with
  | I8 =>
      cases si with
      | Signed =>
          apply Csharpminor.eval_Eunop
          · exact ha
          · rfl
      | Unsigned =>
          apply Csharpminor.eval_Eunop
          · exact ha
          · rfl
  | I16 =>
      cases si with
      | Signed =>
          apply Csharpminor.eval_Eunop
          · exact ha
          · rfl
      | Unsigned =>
          apply Csharpminor.eval_Eunop
          · exact ha
          · rfl
  | I32 =>
      exact ha
  | IBool =>
      exact make_cmpu_ne_zero_correct ge e le m a n ha

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Cfrontend.Cshmgen

theorem make_cast_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_cast_correctStatement := by
  intro ge e le m a b v ty1 ty2 v' hmake ha hsem
  unfold make_cast at hmake
  unfold CompCert4Lean.Cfrontend.Cop.sem_cast at hsem
  cases hclass : CompCert4Lean.Cfrontend.Cop.classify_cast ty1 ty2 <;>
    simp [hclass] at hmake hsem
  case cast_case_pointer =>
    subst b
    cases v with
    | Vint n => simp [CompCert4Lean.X86_64.Archi.ptr64] at hsem
    | Vlong n =>
        simp [CompCert4Lean.X86_64.Archi.ptr64] at hsem
        rcases hsem with ⟨_, rfl⟩
        exact ha
    | Vfloat f => simp [CompCert4Lean.X86_64.Archi.ptr64] at hsem
    | Vsingle f => simp [CompCert4Lean.X86_64.Archi.ptr64] at hsem
    | Vptr b ofs =>
        simp [CompCert4Lean.X86_64.Archi.ptr64] at hsem
        rcases hsem with ⟨_, rfl⟩
        exact ha
    | Vundef => simp [CompCert4Lean.X86_64.Archi.ptr64] at hsem
  case cast_case_i2i sz2 si2 =>
    cases v with
    | Vint n =>
        simp at hsem
        cases hsem
        subst b
        exact make_cast_int_correct ge e le m a n sz2 si2 ha
    | Vlong n | Vfloat n | Vsingle n | Vptr n _ | Vundef => simp at hsem
  case cast_case_f2f =>
    subst b
    cases v with
    | Vfloat f => simp at hsem; cases hsem; exact ha
    | Vint n | Vlong n | Vsingle n | Vptr n _ | Vundef => simp at hsem
  case cast_case_s2i sz2 si2 =>
    cases v with
    | Vsingle f =>
      cases si2 with
      | Signed =>
        cases hcast : CompCert4Lean.Cfrontend.Cop.cast_single_int .Signed f with
        | none => simp [hcast] at hsem
        | some i =>
            simp [hcast] at hsem
            cases hsem
            subst b
            apply make_cast_int_correct
            apply Csharpminor.eval_Eunop
            · exact ha
            · unfold Csharpminor.eval_unop CompCert4Lean.Backend.Cminor.eval_unop
              simpa [CompCert4Lean.Cfrontend.Cop.cast_single_int,
                CompCert4Lean.Common.Values.Val.intofsingle] using hcast
      | Unsigned =>
        cases hcast : CompCert4Lean.Cfrontend.Cop.cast_single_int .Unsigned f with
        | none => simp [hcast] at hsem
        | some i =>
            simp [hcast] at hsem
            cases hsem
            subst b
            apply make_cast_int_correct
            apply Csharpminor.eval_Eunop
            · exact ha
            · unfold Csharpminor.eval_unop CompCert4Lean.Backend.Cminor.eval_unop
              simpa [CompCert4Lean.Cfrontend.Cop.cast_single_int,
                CompCert4Lean.Common.Values.Val.intuofsingle] using hcast
    | Vint n | Vlong n | Vfloat n | Vptr n _ | Vundef => simp at hsem
  case cast_case_l2i sz2 si2 =>
    cases v with
    | Vlong n =>
        simp at hsem
        cases hsem
        subst b
        apply make_cast_int_correct
        apply Csharpminor.eval_Eunop
        · exact ha
        · unfold Csharpminor.eval_unop CompCert4Lean.Backend.Cminor.eval_unop
          rfl
    | Vint n | Vfloat n | Vsingle n | Vptr n _ | Vundef => simp at hsem
  case cast_case_f2l si2 =>
    cases v with
    | Vfloat f =>
      cases si2 with
      | Signed =>
        cases hcast : CompCert4Lean.Cfrontend.Cop.cast_float_long .Signed f with
        | none => simp [hcast] at hsem
        | some i =>
            simp [hcast] at hsem
            cases hsem
            subst b
            apply Csharpminor.eval_Eunop
            · exact ha
            · unfold Csharpminor.eval_unop CompCert4Lean.Backend.Cminor.eval_unop
              simpa [CompCert4Lean.Cfrontend.Cop.cast_float_long,
                CompCert4Lean.Common.Values.Val.longoffloat] using hcast
      | Unsigned =>
        cases hcast : CompCert4Lean.Cfrontend.Cop.cast_float_long .Unsigned f with
        | none => simp [hcast] at hsem
        | some i =>
            simp [hcast] at hsem
            cases hsem
            subst b
            apply Csharpminor.eval_Eunop
            · exact ha
            · unfold Csharpminor.eval_unop CompCert4Lean.Backend.Cminor.eval_unop
              simpa [CompCert4Lean.Cfrontend.Cop.cast_float_long,
                CompCert4Lean.Common.Values.Val.longuoffloat] using hcast
    | Vint n | Vlong n | Vsingle n | Vptr n _ | Vundef => simp at hsem
  case cast_case_s2l si2 =>
    cases v with
    | Vsingle f =>
      cases si2 with
      | Signed =>
        cases hcast : CompCert4Lean.Cfrontend.Cop.cast_single_long .Signed f with
        | none => simp [hcast] at hsem
        | some i =>
            simp [hcast] at hsem
            cases hsem
            subst b
            apply Csharpminor.eval_Eunop
            · exact ha
            · unfold Csharpminor.eval_unop CompCert4Lean.Backend.Cminor.eval_unop
              simpa [CompCert4Lean.Cfrontend.Cop.cast_single_long,
                CompCert4Lean.Common.Values.Val.longofsingle] using hcast
      | Unsigned =>
        cases hcast : CompCert4Lean.Cfrontend.Cop.cast_single_long .Unsigned f with
        | none => simp [hcast] at hsem
        | some i =>
            simp [hcast] at hsem
            cases hsem
            subst b
            apply Csharpminor.eval_Eunop
            · exact ha
            · unfold Csharpminor.eval_unop CompCert4Lean.Backend.Cminor.eval_unop
              simpa [CompCert4Lean.Cfrontend.Cop.cast_single_long,
                CompCert4Lean.Common.Values.Val.longuofsingle] using hcast
    | Vint n | Vlong n | Vfloat n | Vptr n _ | Vundef => simp at hsem
  case cast_case_i2bool =>
    cases v with
    | Vint n =>
        simp at hsem
        cases hsem
        subst b
        exact make_cmpu_ne_zero_correct ge e le m a n ha
    | Vptr b ofs => simp [CompCert4Lean.X86_64.Archi.ptr64] at hsem
    | Vlong n | Vfloat n | Vsingle n | Vundef => simp at hsem
  case cast_case_l2bool =>
    cases v with
    | Vlong n =>
        simp at hsem
        cases hsem
        subst b
        apply Csharpminor.eval_Ebinop
        · exact ha
        · exact make_longconst_correct ge CompCert4Lean.Lib.Integers.Int64.zero e le m
        · change Option.map CompCert4Lean.Common.Values.Val.of_bool
            (CompCert4Lean.Common.Values.Val.cmplu_bool
              (CompCert4Lean.Common.Memory.Mem.valid_pointer m) .Cne
              (.Vlong n) (.Vlong CompCert4Lean.Lib.Integers.Int64.zero)) = _
          cases hEq : decide (n.intval =
              CompCert4Lean.Lib.Integers.Int64.zero.intval) <;>
            simp [CompCert4Lean.Common.Values.Val.cmplu_bool,
              CompCert4Lean.Common.Values.Val.of_bool,
              CompCert4Lean.Lib.Integers.Int64.cmpu,
              CompCert4Lean.Lib.Integers.Int64.eq,
              CompCert4Lean.Lib.Integers.WordCore.cmpu,
              CompCert4Lean.Lib.Integers.WordCore.eq,
              CompCert4Lean.Common.Values.Vtrue,
              CompCert4Lean.Common.Values.Vfalse, hEq]
    | Vptr b ofs =>
        simp [CompCert4Lean.X86_64.Archi.ptr64] at hsem
        rcases hsem with ⟨hv, rfl⟩
        cases hmake
        apply Csharpminor.eval_Ebinop
        · exact ha
        · exact make_longconst_correct ge CompCert4Lean.Lib.Integers.Int64.zero e le m
        · change Option.map CompCert4Lean.Common.Values.Val.of_bool
            (CompCert4Lean.Common.Values.Val.cmplu_bool
              (CompCert4Lean.Common.Memory.Mem.valid_pointer m) .Cne
              (.Vptr b ofs) (.Vlong CompCert4Lean.Lib.Integers.Int64.zero)) =
            some CompCert4Lean.Common.Values.Vone
          simp [CompCert4Lean.Common.Memory.Mem.weak_valid_pointer,
            CompCert4Lean.Common.Values.Vtrue,
            CompCert4Lean.Common.Values.Vfalse] at hv ⊢
          simp [CompCert4Lean.Common.Values.Val.cmplu_bool,
            CompCert4Lean.Common.Values.Val.of_bool,
            CompCert4Lean.X86_64.Archi.ptr64, hv,
            CompCert4Lean.Common.Values.Vone,
            CompCert4Lean.Common.Values.Val.cmp_different_blocks,
            CompCert4Lean.Lib.Integers.Int64.eq,
            CompCert4Lean.Lib.Integers.WordCore.eq,
            CompCert4Lean.Common.Values.Vtrue,
            CompCert4Lean.Common.Values.Vfalse]
    | Vint n | Vfloat n | Vsingle n | Vundef => simp at hsem
  case cast_case_f2bool =>
    cases v with
    | Vfloat f =>
        simp at hsem
        cases hsem
        subst b
        apply Csharpminor.eval_Ebinop
        · exact ha
        · exact make_floatconst_correct ge CompCert4Lean.Lib.Floats.Float.zero e le m
        · change some (CompCert4Lean.Common.Values.Val.cmpf .Cne
            (.Vfloat f) (.Vfloat CompCert4Lean.Lib.Floats.Float.zero)) = _
          cases hcmp : CompCert4Lean.Lib.Floats.Float.compare f
              CompCert4Lean.Lib.Floats.Float.zero with
          | none =>
              simp [CompCert4Lean.Common.Values.Val.cmpf,
                CompCert4Lean.Common.Values.Val.cmpf_bool,
                CompCert4Lean.Common.Values.Val.of_optbool,
                CompCert4Lean.Lib.Floats.Float.cmp,
                CompCert4Lean.Lib.Floats.cmp_of_comparison,
                CompCert4Lean.Common.Values.Vtrue,
                CompCert4Lean.Common.Values.Vfalse, hcmp]
          | some c =>
              cases c <;>
                simp [CompCert4Lean.Common.Values.Val.cmpf,
                  CompCert4Lean.Common.Values.Val.cmpf_bool,
                  CompCert4Lean.Common.Values.Val.of_optbool,
                  CompCert4Lean.Lib.Floats.Float.cmp,
                  CompCert4Lean.Lib.Floats.cmp_of_comparison,
                  CompCert4Lean.Common.Values.Vtrue,
                  CompCert4Lean.Common.Values.Vfalse, hcmp]
    | Vint n | Vlong n | Vsingle n | Vptr n _ | Vundef => simp at hsem
  case cast_case_s2bool =>
    cases v with
    | Vsingle f =>
        simp at hsem
        cases hsem
        subst b
        apply Csharpminor.eval_Ebinop
        · exact ha
        · exact make_singleconst_correct ge CompCert4Lean.Lib.Floats.Float32.zero e le m
        · change some (CompCert4Lean.Common.Values.Val.cmpfs .Cne
            (.Vsingle f) (.Vsingle CompCert4Lean.Lib.Floats.Float32.zero)) = _
          cases hcmp : CompCert4Lean.Lib.Floats.Float32.compare f
              CompCert4Lean.Lib.Floats.Float32.zero with
          | none =>
              simp [CompCert4Lean.Common.Values.Val.cmpfs,
                CompCert4Lean.Common.Values.Val.cmpfs_bool,
                CompCert4Lean.Common.Values.Val.of_optbool,
                CompCert4Lean.Lib.Floats.Float32.cmp,
                CompCert4Lean.Lib.Floats.cmp_of_comparison,
                CompCert4Lean.Common.Values.Vtrue,
                CompCert4Lean.Common.Values.Vfalse, hcmp]
          | some c =>
              cases c <;>
                simp [CompCert4Lean.Common.Values.Val.cmpfs,
                  CompCert4Lean.Common.Values.Val.cmpfs_bool,
                  CompCert4Lean.Common.Values.Val.of_optbool,
                  CompCert4Lean.Lib.Floats.Float32.cmp,
                  CompCert4Lean.Lib.Floats.cmp_of_comparison,
                  CompCert4Lean.Common.Values.Vtrue,
                  CompCert4Lean.Common.Values.Vfalse, hcmp]
    | Vint n | Vlong n | Vfloat n | Vptr n _ | Vundef => simp at hsem
  case cast_case_struct id1 id2 =>
    subst b
    cases v with
    | Vptr b ofs =>
        by_cases h : id1 = id2 <;> simp [h] at hsem
        · cases hsem
          exact ha
    | Vint n | Vlong n | Vfloat n | Vsingle n | Vundef => simp at hsem
  case cast_case_union id1 id2 =>
    subst b
    cases v with
    | Vptr b ofs =>
        by_cases h : id1 = id2 <;> simp [h] at hsem
        · cases hsem
          exact ha
    | Vint n | Vlong n | Vfloat n | Vsingle n | Vundef => simp at hsem
  case cast_case_s2s =>
    subst b
    cases v with
    | Vsingle f => simp at hsem; cases hsem; exact ha
    | Vint n | Vlong n | Vfloat n | Vptr n _ | Vundef => simp at hsem
  case cast_case_l2l =>
    subst b
    cases v with
    | Vlong n => simp at hsem; cases hsem; exact ha
    | Vint n | Vfloat n | Vsingle n | Vptr n _ | Vundef => simp at hsem
  case cast_case_void =>
    subst b
    cases hsem
    exact ha
  case cast_case_f2s =>
    cases v with
    | Vfloat f =>
        simp at hsem
        cases hsem
        subst b
        apply Csharpminor.eval_Eunop
        · exact ha
        · rfl
    | Vint n | Vlong n | Vsingle n | Vptr n _ | Vundef => simp at hsem
  case cast_case_s2f =>
    cases v with
    | Vsingle f =>
        simp at hsem
        cases hsem
        subst b
        apply Csharpminor.eval_Eunop
        · exact ha
        · rfl
    | Vint n | Vlong n | Vfloat n | Vptr n _ | Vundef => simp at hsem
  case cast_case_i2f si1 =>
    cases si1 <;> cases v <;> simp [make_floatofint, CompCert4Lean.Cfrontend.Cop.cast_int_float] at hmake hsem ⊢
    all_goals
      cases hsem
      subst b
      apply Csharpminor.eval_Eunop
      · exact ha
      · unfold Csharpminor.eval_unop CompCert4Lean.Backend.Cminor.eval_unop
        rfl
  case cast_case_i2s si1 =>
    cases si1 <;> cases v <;> simp [make_singleofint, CompCert4Lean.Cfrontend.Cop.cast_int_single] at hmake hsem ⊢
    all_goals
      cases hsem
      subst b
      apply Csharpminor.eval_Eunop
      · exact ha
      · unfold Csharpminor.eval_unop CompCert4Lean.Backend.Cminor.eval_unop
        rfl
  case cast_case_i2l si1 =>
    cases si1 <;> cases v <;> simp [make_longofint, CompCert4Lean.Cfrontend.Cop.cast_int_long] at hmake hsem ⊢
    all_goals
      cases hsem
      subst b
      apply Csharpminor.eval_Eunop
      · exact ha
      · unfold Csharpminor.eval_unop CompCert4Lean.Backend.Cminor.eval_unop
        rfl
  case cast_case_l2f si1 =>
    cases si1 <;> cases v <;> simp [make_floatoflong, CompCert4Lean.Cfrontend.Cop.cast_long_float] at hmake hsem ⊢
    all_goals
      cases hsem
      subst b
      apply Csharpminor.eval_Eunop
      · exact ha
      · unfold Csharpminor.eval_unop CompCert4Lean.Backend.Cminor.eval_unop
        rfl
  case cast_case_l2s si1 =>
    cases si1 <;> cases v <;> simp [make_singleoflong, CompCert4Lean.Cfrontend.Cop.cast_long_single] at hmake hsem ⊢
    all_goals
      cases hsem
      subst b
      apply Csharpminor.eval_Eunop
      · exact ha
      · unfold Csharpminor.eval_unop CompCert4Lean.Backend.Cminor.eval_unop
        rfl
  case cast_case_f2i sz2 si2 =>
    cases v with
    | Vfloat f =>
      cases si2 with
      | Signed =>
        cases hcast : CompCert4Lean.Cfrontend.Cop.cast_float_int .Signed f with
        | none => simp [hcast] at hsem
        | some i =>
            simp [hcast] at hsem
            cases hsem
            subst b
            apply make_cast_int_correct
            apply Csharpminor.eval_Eunop
            · exact ha
            · unfold Csharpminor.eval_unop CompCert4Lean.Backend.Cminor.eval_unop
              simpa [CompCert4Lean.Cfrontend.Cop.cast_float_int,
                CompCert4Lean.Common.Values.Val.intoffloat] using hcast
      | Unsigned =>
        cases hcast : CompCert4Lean.Cfrontend.Cop.cast_float_int .Unsigned f with
        | none => simp [hcast] at hsem
        | some i =>
            simp [hcast] at hsem
            cases hsem
            subst b
            apply make_cast_int_correct
            apply Csharpminor.eval_Eunop
            · exact ha
            · unfold Csharpminor.eval_unop CompCert4Lean.Backend.Cminor.eval_unop
              simpa [CompCert4Lean.Cfrontend.Cop.cast_float_int,
                CompCert4Lean.Common.Values.Val.intuoffloat] using hcast
    | Vint n | Vlong n | Vsingle n | Vptr n _ | Vundef => simp at hsem

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Cfrontend.Cshmgen
open CompCert4Lean.Cfrontend.Csharpminor

theorem make_absfloat_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_absfloat_correctStatement := by
  intro ge a tya c va v e le m hsem hmake hval
  unfold CompCert4Lean.Cfrontend.Cop.sem_absfloat at hsem
  unfold make_absfloat at hmake
  cases hclass : CompCert4Lean.Cfrontend.Cop.classify_neg tya <;>
    simp [hclass] at hsem hmake
  case neg_case_i sg =>
    cases va with
    | Vint n =>
        cases hsem
        cases hmake
        have hconv : T_eval_expr ge e le m (make_floatofint a sg)
            (.Vfloat (CompCert4Lean.Cfrontend.Cop.cast_int_float sg n)) := by
          cases sg <;>
            simp [make_floatofint, CompCert4Lean.Cfrontend.Cop.cast_int_float]
          · apply Csharpminor.eval_Eunop
            · exact hval
            · rfl
          · apply Csharpminor.eval_Eunop
            · exact hval
            · rfl
        apply Csharpminor.eval_Eunop
        · exact hconv
        · unfold Csharpminor.eval_unop CompCert4Lean.Backend.Cminor.eval_unop
          rfl
    | Vlong n | Vfloat n | Vsingle n | Vptr n _ | Vundef => simp at hsem
  case neg_case_f =>
    cases va with
    | Vfloat f =>
        cases hsem
        cases hmake
        apply Csharpminor.eval_Eunop
        · exact hval
        · unfold Csharpminor.eval_unop CompCert4Lean.Backend.Cminor.eval_unop
          rfl
    | Vint n | Vlong n | Vsingle n | Vptr n _ | Vundef => simp at hsem
  case neg_case_s =>
    cases va with
    | Vsingle f =>
        cases hsem
        cases hmake
        have hconv : T_eval_expr ge e le m (make_floatofsingle a)
            (.Vfloat (CompCert4Lean.Lib.Floats.Float.of_single f)) := by
          apply Csharpminor.eval_Eunop
          · exact hval
          · rfl
        apply Csharpminor.eval_Eunop
        · exact hconv
        · unfold Csharpminor.eval_unop CompCert4Lean.Backend.Cminor.eval_unop
          rfl
    | Vint n | Vlong n | Vfloat n | Vptr n _ | Vundef => simp at hsem
  case neg_case_l sg =>
    cases va with
    | Vlong n =>
        cases hsem
        cases hmake
        have hconv : T_eval_expr ge e le m (make_floatoflong a sg)
            (.Vfloat (CompCert4Lean.Cfrontend.Cop.cast_long_float sg n)) := by
          cases sg <;>
            simp [make_floatoflong, CompCert4Lean.Cfrontend.Cop.cast_long_float]
          · apply Csharpminor.eval_Eunop
            · exact hval
            · rfl
          · apply Csharpminor.eval_Eunop
            · exact hval
            · rfl
        apply Csharpminor.eval_Eunop
        · exact hconv
        · unfold Csharpminor.eval_unop CompCert4Lean.Backend.Cminor.eval_unop
          rfl
    | Vint n | Vfloat n | Vsingle n | Vptr n _ | Vundef => simp at hsem

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Cfrontend.Cshmgen
open CompCert4Lean.Cfrontend.Csharpminor

theorem make_notint_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_notint_correctStatement := by
  intro ge a tya c va v e le m hsem hmake hval
  unfold CompCert4Lean.Cfrontend.Cop.sem_notint at hsem
  unfold make_notint at hmake
  cases hclass : CompCert4Lean.Cfrontend.Cop.classify_notint tya <;>
    simp [hclass] at hsem hmake
  case notint_case_i sg =>
    cases va with
    | Vint n =>
        cases hsem
        cases hmake
        apply Csharpminor.eval_Eunop
        · exact hval
        · unfold Csharpminor.eval_unop CompCert4Lean.Backend.Cminor.eval_unop
          rfl
    | Vlong n | Vfloat n | Vsingle n | Vptr n _ | Vundef => simp at hsem
  case notint_case_l sg =>
    cases va with
    | Vlong n =>
        cases hsem
        cases hmake
        apply Csharpminor.eval_Eunop
        · exact hval
        · unfold Csharpminor.eval_unop CompCert4Lean.Backend.Cminor.eval_unop
          rfl
    | Vint n | Vfloat n | Vsingle n | Vptr n _ | Vundef => simp at hsem
end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

theorem make_binarith_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_binarith_correctStatement := by
  intro ge sem_int sem_long sem_float sem_single iop iopu fop sop lop lopu
  intro hi hiu hl hlu hf hs
  change Csharpminor.binary_operation at iop iopu fop sop lop lopu
  intro a tya b tyb c va vb v e le m hsem hmake h1 h2
  unfold Cshmgen.make_binarith at hmake
  unfold Cop.sem_binarith at hsem
  cases hclass : Cop.classify_binarith tya tyb <;>
    simp [hclass] at hsem hmake
  case bin_case_i sg =>
    let ty := Cop.binarith_type (.bin_case_i sg)
    cases hca : Cop.sem_cast va tya ty m with
    | none =>
      have hca' : Cop.sem_cast va tya (Cop.binarith_type (.bin_case_i sg)) m = none :=
        by simpa [ty] using hca
      rw [hca'] at hsem
      simp at hsem
    | some va' =>
      cases hcb : Cop.sem_cast vb tyb ty m with
      | none =>
        have hca' : Cop.sem_cast va tya (Cop.binarith_type (.bin_case_i sg)) m = some va' :=
          by simpa [ty] using hca
        have hcb' : Cop.sem_cast vb tyb (Cop.binarith_type (.bin_case_i sg)) m = none :=
          by simpa [ty] using hcb
        rw [hca', hcb'] at hsem
        simp at hsem
      | some vb' =>
        cases hma : Cshmgen.make_cast tya ty a with
        | Error msg =>
          have hma' : Cshmgen.make_cast tya (Cop.binarith_type (.bin_case_i sg)) a =
              .Error msg := by simpa [ty] using hma
          rw [hma'] at hmake
          simp at hmake
        | OK ea =>
          cases hmb : Cshmgen.make_cast tyb ty b with
          | Error msg =>
            have hma' : Cshmgen.make_cast tya (Cop.binarith_type (.bin_case_i sg)) a =
                .OK ea := by simpa [ty] using hma
            have hmb' : Cshmgen.make_cast tyb (Cop.binarith_type (.bin_case_i sg)) b =
                .Error msg := by simpa [ty] using hmb
            rw [hma'] at hmake
            rw [hmb'] at hmake
            simp at hmake
          | OK eb =>
            have hva' : T_eval_expr ge e le m ea va' :=
              make_cast_correct ge e le m a ea va tya ty va' hma h1 hca
            have hvb' : T_eval_expr ge e le m eb vb' :=
              make_cast_correct ge e le m b eb vb tyb ty vb' hmb h2 hcb
            have hca' : Cop.sem_cast va tya (Cop.binarith_type (.bin_case_i sg)) m =
                some va' := by simpa [ty] using hca
            have hcb' : Cop.sem_cast vb tyb (Cop.binarith_type (.bin_case_i sg)) m =
                some vb' := by simpa [ty] using hcb
            rw [hca', hcb'] at hsem
            have hma' : Cshmgen.make_cast tya (Cop.binarith_type (.bin_case_i sg)) a =
                .OK ea := by simpa [ty] using hma
            have hmb' : Cshmgen.make_cast tyb (Cop.binarith_type (.bin_case_i sg)) b =
                .OK eb := by simpa [ty] using hmb
            rw [hma', hmb'] at hmake
            cases sg with
            | Signed =>
              simp at hmake
              cases hmake
              cases va' with
              | Vint na =>
                cases vb' with
                | Vint nb =>
                  simp at hsem
                  apply Csharpminor.eval_Ebinop iop ea eb _ _ _ hva' hvb'
                  rw [hi]
                  exact hsem
                | Vlong _ | Vfloat _ | Vsingle _ | Vptr _ _ | Vundef => simp at hsem
              | Vlong _ | Vfloat _ | Vsingle _ | Vptr _ _ | Vundef => simp at hsem
            | Unsigned =>
              simp at hmake
              cases hmake
              cases va' with
              | Vint na =>
                cases vb' with
                | Vint nb =>
                  simp at hsem
                  apply Csharpminor.eval_Ebinop iopu ea eb _ _ _ hva' hvb'
                  rw [hiu]
                  exact hsem
                | Vlong _ | Vfloat _ | Vsingle _ | Vptr _ _ | Vundef => simp at hsem
              | Vlong _ | Vfloat _ | Vsingle _ | Vptr _ _ | Vundef => simp at hsem
  case bin_case_l sg =>
    let ty := Cop.binarith_type (.bin_case_l sg)
    cases hca : Cop.sem_cast va tya ty m with
    | none =>
      have hca' : Cop.sem_cast va tya (Cop.binarith_type (.bin_case_l sg)) m = none :=
        by simpa [ty] using hca
      rw [hca'] at hsem
      simp at hsem
    | some va' =>
      cases hcb : Cop.sem_cast vb tyb ty m with
      | none =>
        have hca' : Cop.sem_cast va tya (Cop.binarith_type (.bin_case_l sg)) m = some va' :=
          by simpa [ty] using hca
        have hcb' : Cop.sem_cast vb tyb (Cop.binarith_type (.bin_case_l sg)) m = none :=
          by simpa [ty] using hcb
        rw [hca', hcb'] at hsem
        simp at hsem
      | some vb' =>
        cases hma : Cshmgen.make_cast tya ty a with
        | Error msg =>
          have hma' : Cshmgen.make_cast tya (Cop.binarith_type (.bin_case_l sg)) a =
              .Error msg := by simpa [ty] using hma
          rw [hma'] at hmake
          simp at hmake
        | OK ea =>
          cases hmb : Cshmgen.make_cast tyb ty b with
          | Error msg =>
            have hma' : Cshmgen.make_cast tya (Cop.binarith_type (.bin_case_l sg)) a =
                .OK ea := by simpa [ty] using hma
            have hmb' : Cshmgen.make_cast tyb (Cop.binarith_type (.bin_case_l sg)) b =
                .Error msg := by simpa [ty] using hmb
            rw [hma'] at hmake
            rw [hmb'] at hmake
            simp at hmake
          | OK eb =>
            have hva' : T_eval_expr ge e le m ea va' :=
              make_cast_correct ge e le m a ea va tya ty va' hma h1 hca
            have hvb' : T_eval_expr ge e le m eb vb' :=
              make_cast_correct ge e le m b eb vb tyb ty vb' hmb h2 hcb
            have hca' : Cop.sem_cast va tya (Cop.binarith_type (.bin_case_l sg)) m =
                some va' := by simpa [ty] using hca
            have hcb' : Cop.sem_cast vb tyb (Cop.binarith_type (.bin_case_l sg)) m =
                some vb' := by simpa [ty] using hcb
            have hma' : Cshmgen.make_cast tya (Cop.binarith_type (.bin_case_l sg)) a =
                .OK ea := by simpa [ty] using hma
            have hmb' : Cshmgen.make_cast tyb (Cop.binarith_type (.bin_case_l sg)) b =
                .OK eb := by simpa [ty] using hmb
            rw [hca', hcb'] at hsem
            rw [hma', hmb'] at hmake
            cases sg with
            | Signed =>
              simp at hmake
              cases hmake
              cases va' with
              | Vlong na =>
                cases vb' with
                | Vlong nb =>
                  simp at hsem
                  apply Csharpminor.eval_Ebinop lop ea eb _ _ _ hva' hvb'
                  rw [hl]
                  exact hsem
                | Vint _ | Vfloat _ | Vsingle _ | Vptr _ _ | Vundef => simp at hsem
              | Vint _ | Vfloat _ | Vsingle _ | Vptr _ _ | Vundef => simp at hsem
            | Unsigned =>
              simp at hmake
              cases hmake
              cases va' with
              | Vlong na =>
                cases vb' with
                | Vlong nb =>
                  simp at hsem
                  apply Csharpminor.eval_Ebinop lopu ea eb _ _ _ hva' hvb'
                  rw [hlu]
                  exact hsem
                | Vint _ | Vfloat _ | Vsingle _ | Vptr _ _ | Vundef => simp at hsem
              | Vint _ | Vfloat _ | Vsingle _ | Vptr _ _ | Vundef => simp at hsem
  case bin_case_f =>
    let ty := Cop.binarith_type (.bin_case_f)
    cases hca : Cop.sem_cast va tya ty m with
    | none =>
      have hca' : Cop.sem_cast va tya (Cop.binarith_type (.bin_case_f)) m = none :=
        by simpa [ty] using hca
      rw [hca'] at hsem
      simp at hsem
    | some va' =>
      cases hcb : Cop.sem_cast vb tyb ty m with
      | none =>
        have hca' : Cop.sem_cast va tya (Cop.binarith_type (.bin_case_f)) m = some va' :=
          by simpa [ty] using hca
        have hcb' : Cop.sem_cast vb tyb (Cop.binarith_type (.bin_case_f)) m = none :=
          by simpa [ty] using hcb
        rw [hca', hcb'] at hsem
        simp at hsem
      | some vb' =>
        cases hma : Cshmgen.make_cast tya ty a with
        | Error msg =>
          have hma' : Cshmgen.make_cast tya (Cop.binarith_type (.bin_case_f)) a =
              .Error msg := by simpa [ty] using hma
          rw [hma'] at hmake
          simp at hmake
        | OK ea =>
          cases hmb : Cshmgen.make_cast tyb ty b with
          | Error msg =>
            have hma' : Cshmgen.make_cast tya (Cop.binarith_type (.bin_case_f)) a =
                .OK ea := by simpa [ty] using hma
            have hmb' : Cshmgen.make_cast tyb (Cop.binarith_type (.bin_case_f)) b =
                .Error msg := by simpa [ty] using hmb
            rw [hma'] at hmake
            rw [hmb'] at hmake
            simp at hmake
          | OK eb =>
            have hva' : T_eval_expr ge e le m ea va' :=
              make_cast_correct ge e le m a ea va tya ty va' hma h1 hca
            have hvb' : T_eval_expr ge e le m eb vb' :=
              make_cast_correct ge e le m b eb vb tyb ty vb' hmb h2 hcb
            have hca' : Cop.sem_cast va tya (Cop.binarith_type (.bin_case_f)) m =
                some va' := by simpa [ty] using hca
            have hcb' : Cop.sem_cast vb tyb (Cop.binarith_type (.bin_case_f)) m =
                some vb' := by simpa [ty] using hcb
            have hma' : Cshmgen.make_cast tya (Cop.binarith_type (.bin_case_f)) a =
                .OK ea := by simpa [ty] using hma
            have hmb' : Cshmgen.make_cast tyb (Cop.binarith_type (.bin_case_f)) b =
                .OK eb := by simpa [ty] using hmb
            rw [hca', hcb'] at hsem
            rw [hma', hmb'] at hmake
            simp at hmake
            cases hmake
            cases va' with
            | Vfloat na =>
              cases vb' with
              | Vfloat nb =>
                simp at hsem
                apply Csharpminor.eval_Ebinop fop ea eb _ _ _ hva' hvb'
                rw [hf]
                exact hsem
              | Vint _ | Vlong _ | Vsingle _ | Vptr _ _ | Vundef => simp at hsem
            | Vint _ | Vlong _ | Vsingle _ | Vptr _ _ | Vundef => simp at hsem
  case bin_case_s =>
    let ty := Cop.binarith_type (.bin_case_s)
    cases hca : Cop.sem_cast va tya ty m with
    | none =>
      have hca' : Cop.sem_cast va tya (Cop.binarith_type (.bin_case_s)) m = none :=
        by simpa [ty] using hca
      rw [hca'] at hsem
      simp at hsem
    | some va' =>
      cases hcb : Cop.sem_cast vb tyb ty m with
      | none =>
        have hca' : Cop.sem_cast va tya (Cop.binarith_type (.bin_case_s)) m = some va' :=
          by simpa [ty] using hca
        have hcb' : Cop.sem_cast vb tyb (Cop.binarith_type (.bin_case_s)) m = none :=
          by simpa [ty] using hcb
        rw [hca', hcb'] at hsem
        simp at hsem
      | some vb' =>
        cases hma : Cshmgen.make_cast tya ty a with
        | Error msg =>
          have hma' : Cshmgen.make_cast tya (Cop.binarith_type (.bin_case_s)) a =
              .Error msg := by simpa [ty] using hma
          rw [hma'] at hmake
          simp at hmake
        | OK ea =>
          cases hmb : Cshmgen.make_cast tyb ty b with
          | Error msg =>
            have hma' : Cshmgen.make_cast tya (Cop.binarith_type (.bin_case_s)) a =
                .OK ea := by simpa [ty] using hma
            have hmb' : Cshmgen.make_cast tyb (Cop.binarith_type (.bin_case_s)) b =
                .Error msg := by simpa [ty] using hmb
            rw [hma'] at hmake
            rw [hmb'] at hmake
            simp at hmake
          | OK eb =>
            have hva' : T_eval_expr ge e le m ea va' :=
              make_cast_correct ge e le m a ea va tya ty va' hma h1 hca
            have hvb' : T_eval_expr ge e le m eb vb' :=
              make_cast_correct ge e le m b eb vb tyb ty vb' hmb h2 hcb
            have hca' : Cop.sem_cast va tya (Cop.binarith_type (.bin_case_s)) m =
                some va' := by simpa [ty] using hca
            have hcb' : Cop.sem_cast vb tyb (Cop.binarith_type (.bin_case_s)) m =
                some vb' := by simpa [ty] using hcb
            have hma' : Cshmgen.make_cast tya (Cop.binarith_type (.bin_case_s)) a =
                .OK ea := by simpa [ty] using hma
            have hmb' : Cshmgen.make_cast tyb (Cop.binarith_type (.bin_case_s)) b =
                .OK eb := by simpa [ty] using hmb
            rw [hca', hcb'] at hsem
            rw [hma', hmb'] at hmake
            simp at hmake
            cases hmake
            cases va' with
            | Vsingle na =>
              cases vb' with
              | Vsingle nb =>
                simp at hsem
                apply Csharpminor.eval_Ebinop sop ea eb _ _ _ hva' hvb'
                rw [hs]
                exact hsem
              | Vint _ | Vlong _ | Vfloat _ | Vptr _ _ | Vundef => simp at hsem
            | Vint _ | Vlong _ | Vfloat _ | Vptr _ _ | Vundef => simp at hsem
  case bin_default =>
    cases hca : Cop.sem_cast va tya (Cop.binarith_type (.bin_default)) m with
    | none =>
      rw [hca] at hsem
      simp at hsem
    | some va' =>
      cases hcb : Cop.sem_cast vb tyb (Cop.binarith_type (.bin_default)) m with
      | none =>
        rw [hca, hcb] at hsem
        simp at hsem
      | some vb' =>
        rw [hca, hcb] at hsem
        simp at hsem

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

theorem make_mul_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_mul_correctStatement := by
  intro ge
  apply make_binarith_correct ge
  · intro x y m
    rfl
  · intro x y m
    rfl
  · intro x y m
    rfl
  · intro x y m
    rfl
  · intro x y m
    rfl
  · intro x y m
    rfl

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

theorem make_binarith_int_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_binarith_int_correctStatement := by
  intro ge sem_int sem_long iop iopu lop lopu hi hiu hl hlu
  let sem_float : CCFloat → CCFloat → Option val :=
    fun x y => some (.Vfloat (CompCert4Lean.Lib.Floats.Float.mul x y))
  let sem_single : CCFloat32 → CCFloat32 → Option val :=
    fun x y => some (.Vsingle (CompCert4Lean.Lib.Floats.Float32.mul x y))
  have hf : ∀ (x y : CCFloat) (m : mem),
      Csharpminor.eval_binop (.Omulf) (.Vfloat x) (.Vfloat y) m = sem_float x y := by
    intro x y m
    rfl
  have hs : ∀ (x y : CCFloat32) (m : mem),
      Csharpminor.eval_binop (.Omulfs) (.Vsingle x) (.Vsingle y) m = sem_single x y := by
    intro x y m
    rfl
  have hfull := make_binarith_correct ge sem_int sem_long sem_float sem_single
    iop iopu .Omulf .Omulfs lop lopu hi hiu hl hlu hf hs
  intro a tya b tyb c va vb v e le m hsem hmake h1 h2
  unfold Cshmgen.make_binarith_int at hmake
  unfold Cop.sem_binarith at hsem
  cases hclass : Cop.classify_binarith tya tyb with
  | bin_case_i sg =>
      have hm : Cshmgen.make_binarith_int iop iopu lop lopu a tya b tyb =
          Cshmgen.make_binarith iop iopu .Omulf .Omulfs lop lopu a tya b tyb := by
        cases h1c : Cshmgen.make_cast tya (Cop.binarith_type (.bin_case_i sg)) a <;>
          cases h2c : Cshmgen.make_cast tyb (Cop.binarith_type (.bin_case_i sg)) b <;>
          cases sg <;>
          simp [Cshmgen.make_binarith_int, Cshmgen.make_binarith, hclass, h1c, h2c]
      have hmake' : Cshmgen.make_binarith iop iopu .Omulf .Omulfs lop lopu
          a tya b tyb = .OK c := by
        rw [← hm]
        exact hmake
      have hsem' : Cop.sem_binarith sem_int sem_long sem_float sem_single
          va tya vb tyb m = some v := by
        simpa [Cop.sem_binarith, sem_float, sem_single, hclass] using hsem
      exact hfull a tya b tyb c va vb v e le m hsem' hmake' h1 h2
  | bin_case_l sg =>
      have hm : Cshmgen.make_binarith_int iop iopu lop lopu a tya b tyb =
          Cshmgen.make_binarith iop iopu .Omulf .Omulfs lop lopu a tya b tyb := by
        cases h1c : Cshmgen.make_cast tya (Cop.binarith_type (.bin_case_l sg)) a <;>
          cases h2c : Cshmgen.make_cast tyb (Cop.binarith_type (.bin_case_l sg)) b <;>
          cases sg <;>
          simp [Cshmgen.make_binarith_int, Cshmgen.make_binarith, hclass, h1c, h2c]
      have hmake' : Cshmgen.make_binarith iop iopu .Omulf .Omulfs lop lopu
          a tya b tyb = .OK c := by
        rw [← hm]
        exact hmake
      have hsem' : Cop.sem_binarith sem_int sem_long sem_float sem_single
          va tya vb tyb m = some v := by
        simpa [Cop.sem_binarith, sem_float, sem_single, hclass] using hsem
      exact hfull a tya b tyb c va vb v e le m hsem' hmake' h1 h2
  | bin_case_f =>
      cases h1c : Cshmgen.make_cast tya (Cop.binarith_type (.bin_case_f)) a <;>
        cases h2c : Cshmgen.make_cast tyb (Cop.binarith_type (.bin_case_f)) b <;>
        simp [Cshmgen.make_binarith_int, hclass, h1c, h2c] at hmake <;>
        cases hmake
  | bin_case_s =>
      cases h1c : Cshmgen.make_cast tya (Cop.binarith_type (.bin_case_s)) a <;>
        cases h2c : Cshmgen.make_cast tyb (Cop.binarith_type (.bin_case_s)) b <;>
        simp [Cshmgen.make_binarith_int, hclass, h1c, h2c] at hmake <;>
        cases hmake
  | bin_default =>
      cases h1c : Cshmgen.make_cast tya (Cop.binarith_type (.bin_default)) a <;>
        cases h2c : Cshmgen.make_cast tyb (Cop.binarith_type (.bin_default)) b <;>
        simp [Cshmgen.make_binarith_int, hclass, h1c, h2c] at hmake <;>
        cases hmake

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

theorem make_div_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_div_correctStatement := by
  intro ge
  apply make_binarith_correct ge
  · intro x y m
    rfl
  · intro x y m
    rfl
  · intro x y m
    rfl
  · intro x y m
    rfl
  · intro x y m
    rfl
  · intro x y m
    rfl

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

theorem make_and_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_and_correctStatement := by
  intro ge
  apply make_binarith_int_correct ge
  · intro x y m
    rfl
  · intro x y m
    rfl
  · intro x y m
    rfl
  · intro x y m
    rfl

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

theorem make_xor_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_xor_correctStatement := by
  intro ge
  apply make_binarith_int_correct ge
  · intro x y m
    rfl
  · intro x y m
    rfl
  · intro x y m
    rfl
  · intro x y m
    rfl

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open Lean Elab Tactic Meta

private abbrev suffix_Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
private abbrev suffix_zZero : suffix_Z :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0
private abbrev suffix_zOfNat : Nat → suffix_Z :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
private abbrev suffix_zLe : suffix_Z → suffix_Z → Prop :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
private abbrev suffix_zLt : suffix_Z → suffix_Z → Prop :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt

private theorem int64_unsigned_repr_small (z : suffix_Z)
    (hz : suffix_zLe suffix_zZero z ∧
      suffix_zLe z CompCert4Lean.Lib.Integers.Int64.max_unsigned) :
    CompCert4Lean.Lib.Integers.Int64.unsigned
        (CompCert4Lean.Lib.Integers.Int64.repr z) = z := by
  have hzi : z = CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z) :=
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt_intOfZ z).symm
  rw [hzi]
  change (CompCert4Lean.Lib.Integers.WordCore.repr 64
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z))).intval =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z)
  let w := CompCert4Lean.Lib.Integers.WordCore.repr 64
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z))
  have hi : w.val =
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z %
        ((2 ^ 64 : Nat) : Int)).toNat := by
    dsimp [w]
    run_tac
      let env ← getEnv
      let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith "WordCore.val_repr")
        | throwError "frozen WordCore.val_repr helper not found"
      let stx := Lean.mkIdent n
      let arg := Lean.mkIdent `z
      evalTactic
        (← `(tactic| exact $stx 64
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ $arg)))
  have hwi : w.intval =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat w.val := by
    run_tac
      let env ← getEnv
      let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith "WordCore.intval_eq_zOfNat_val")
        | throwError "frozen WordCore.intval_eq_zOfNat_val helper not found"
      let stx := Lean.mkIdent n
      let arg := Lean.mkIdent `w
      evalTactic (← `(tactic| exact $stx $arg))
  change w.intval = _
  rw [hwi, hi]
  have hznonneg : 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z := hz.1
  have hzmax := hz.2
  have hzlt : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z <
      ((2 ^ 64 : Nat) : Int) := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        CompCert4Lean.Lib.Integers.Int64.max_unsigned at hzmax
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z ≤
      (2 ^ 64 : Int) - 1 at hzmax
    omega
  rw [Int.emod_eq_of_lt hznonneg hzlt]
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (↑(Int.toNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z)) : Int) = _
  rw [Int.toNat_of_nonneg hznonneg]

private theorem int64_ltu_inv_local (x y : CompCert4Lean.Lib.Integers.Int64.int)
    (h : CompCert4Lean.Lib.Integers.Int64.ltu x y = true) :
    suffix_zLe suffix_zZero (CompCert4Lean.Lib.Integers.Int64.unsigned x) ∧
      suffix_zLt (CompCert4Lean.Lib.Integers.Int64.unsigned x)
        (CompCert4Lean.Lib.Integers.Int64.unsigned y) := by
  unfold CompCert4Lean.Lib.Integers.Int64.ltu
    CompCert4Lean.Lib.Integers.WordCore.ltu at h
  run_tac
    let env ← getEnv
    for (n, _) in env.constants.toList do
      if (toString n).endsWith "Integers.zltSelect" then
        let stx := Lean.mkIdent n
        evalTactic (← `(tactic| try unfold $stx at *))
    for (n, _) in env.constants.toList do
      if (toString n).endsWith "Integers.sumboolSelect" then
        let stx := Lean.mkIdent n
        evalTactic (← `(tactic| try unfold $stx at *))
  cases hz : CompCert4Lean.Lib.Coqlib.zlt
      (CompCert4Lean.Lib.Integers.WordCore.unsigned x)
      (CompCert4Lean.Lib.Integers.WordCore.unsigned y) with
  | left hxy =>
      try simp [CompCert4Lean.Lib.Integers.Int64.ltu,
        CompCert4Lean.Lib.Integers.WordCore.ltu, hz] at h
      constructor
      · have hx := x.intrange.1
        change (-1 : Int) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Lib.Integers.Int64.unsigned x) at hx
        change 0 ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Lib.Integers.Int64.unsigned x)
        omega
      · exact hxy
  | right hxy =>
      rw [hz] at h
      simp at h

private theorem int_ltu_of_unsigned_lt (x y : CompCert4Lean.Lib.Integers.Int.int)
    (h : suffix_zLt (CompCert4Lean.Lib.Integers.Int.unsigned x)
      (CompCert4Lean.Lib.Integers.Int.unsigned y)) :
    CompCert4Lean.Lib.Integers.Int.ltu x y = true := by
  unfold CompCert4Lean.Lib.Integers.Int.ltu
    CompCert4Lean.Lib.Integers.WordCore.ltu
  run_tac
    let env ← getEnv
    for (n, _) in env.constants.toList do
      if (toString n).endsWith "Integers.zltSelect" then
        let stx := Lean.mkIdent n
        evalTactic (← `(tactic| try unfold $stx at *))
    for (n, _) in env.constants.toList do
      if (toString n).endsWith "Integers.sumboolSelect" then
        let stx := Lean.mkIdent n
        evalTactic (← `(tactic| try unfold $stx at *))
  cases hz : CompCert4Lean.Lib.Coqlib.zlt
      (CompCert4Lean.Lib.Integers.WordCore.unsigned x)
      (CompCert4Lean.Lib.Integers.WordCore.unsigned y) with
  | left hxy => rfl
  | right hxy =>
      exfalso
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int.unsigned x) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int.unsigned y) at h
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int.unsigned y) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int.unsigned x) at hxy
      omega

theorem small_shift_amount_1 : small_shift_amount_1Statement := by
  intro i h
  have hi := int64_ltu_inv_local i
    CompCert4Lean.Lib.Integers.Int64.iwordsize h
  have hword : CompCert4Lean.Lib.Integers.Int64.unsigned
      CompCert4Lean.Lib.Integers.Int64.iwordsize = suffix_zOfNat 64 := by
    rfl
  have hword' : CompCert4Lean.Lib.Integers.Int.unsigned
      CompCert4Lean.Lib.Integers.Int64.iwordsize' = suffix_zOfNat 64 := by
    rfl
  have hlt := hi.2
  rw [hword] at hlt
  have hlow : CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int64.loword i) =
      CompCert4Lean.Lib.Integers.Int64.unsigned i := by
    unfold CompCert4Lean.Lib.Integers.Int64.loword
    apply CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api
    constructor
    · exact hi.1
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int64.unsigned i) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          CompCert4Lean.Lib.Integers.Int.max_unsigned
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int64.unsigned i) < 64 at hlt
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int64.unsigned i) ≤
        (2 ^ 32 : Int) - 1
      omega
  constructor
  · apply int_ltu_of_unsigned_lt
    rw [hlow, hword']
    exact hlt
  · exact hlow.symm

theorem small_shift_amount_2 : small_shift_amount_2Statement := by
  intro i h
  have hi := int64_ltu_inv_local i
    (CompCert4Lean.Lib.Integers.Int64.repr (suffix_zOfNat 32)) h
  have hword : CompCert4Lean.Lib.Integers.Int64.unsigned
      (CompCert4Lean.Lib.Integers.Int64.repr (suffix_zOfNat 32)) =
      suffix_zOfNat 32 := by
    rfl
  have hlt := hi.2
  rw [hword] at hlt
  have hlow : CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int64.loword i) =
      CompCert4Lean.Lib.Integers.Int64.unsigned i := by
    unfold CompCert4Lean.Lib.Integers.Int64.loword
    apply CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api
    constructor
    · exact hi.1
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int64.unsigned i) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          CompCert4Lean.Lib.Integers.Int.max_unsigned
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int64.unsigned i) < 32 at hlt
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int64.unsigned i) ≤
        (2 ^ 32 : Int) - 1
      omega
  apply int_ltu_of_unsigned_lt
  rw [hlow]
  have hiword : CompCert4Lean.Lib.Integers.Int.unsigned
      CompCert4Lean.Lib.Integers.Int.iwordsize = suffix_zOfNat 32 := by
    rfl
  rw [hiword]
  exact hlt

theorem small_shift_amount_3 : small_shift_amount_3Statement := by
  intro i h
  have hi : suffix_zLe suffix_zZero
      (CompCert4Lean.Lib.Integers.Int.unsigned i) ∧
      suffix_zLt (CompCert4Lean.Lib.Integers.Int.unsigned i)
        (CompCert4Lean.Lib.Integers.Int.unsigned
          CompCert4Lean.Lib.Integers.Int64.iwordsize') := by
    apply CompCert4Lean.Lib.Integers.Int.ltu_inv_proof
    exact h
  have hbound : suffix_zLe suffix_zZero
      (CompCert4Lean.Lib.Integers.Int.unsigned i) := hi.1
  have hlt : suffix_zLt (CompCert4Lean.Lib.Integers.Int.unsigned i)
      (CompCert4Lean.Lib.Integers.Int.unsigned
        CompCert4Lean.Lib.Integers.Int64.iwordsize') := hi.2
  have hword : CompCert4Lean.Lib.Integers.Int.unsigned
      CompCert4Lean.Lib.Integers.Int64.iwordsize' = suffix_zOfNat 64 := by
    rfl
  rw [hword] at hlt
  have hmax : suffix_zLe (CompCert4Lean.Lib.Integers.Int.unsigned i)
      CompCert4Lean.Lib.Integers.Int64.max_unsigned := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Lib.Integers.Int.unsigned i) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      CompCert4Lean.Lib.Integers.Int64.max_unsigned
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Lib.Integers.Int.unsigned i) < 64 at hlt
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Lib.Integers.Int.unsigned i) ≤
      (2 ^ 64 : Int) - 1
    omega
  exact int64_unsigned_repr_small (CompCert4Lean.Lib.Integers.Int.unsigned i)
    ⟨hbound, hmax⟩

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

theorem make_cmp_ptr_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_cmp_ptr_correctStatement := by
  intro ge cmp e le m a va b vb v hsem h1 h2
  unfold CompCert4Lean.Cfrontend.Cop.cmp_ptr at hsem
  unfold CompCert4Lean.Cfrontend.Cshmgen.make_cmp_ptr
  apply Csharpminor.eval_Ebinop
  · exact h1
  · exact h2
  · exact hsem

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Cfrontend.Cshmgen
open CompCert4Lean.Cfrontend.Csharpminor

theorem make_ptrofs_of_int64_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_ptrofs_of_int64_correctStatement := by
  intro ge e le m a i h
  simp [CompCert4Lean.X86_64.Archi.ptr64]
  have hi0 : CompCert4Lean.Lib.Integers.Ptrofs.to_int64
      (CompCert4Lean.Lib.Integers.Ptrofs.of_int64 i) = i := by
    unfold CompCert4Lean.Lib.Integers.Ptrofs.to_int64
      CompCert4Lean.Lib.Integers.Ptrofs.of_int64
    change CompCert4Lean.Lib.Integers.Int64.repr
        (CompCert4Lean.Lib.Integers.Int64.unsigned
          (CompCert4Lean.Lib.Integers.Int64.repr
            (CompCert4Lean.Lib.Integers.Int64.unsigned i))) = i
    apply CompCert4Lean.Lib.Integers.WordCore.ext
    have hnonneg : suffix_zLe suffix_zZero
        (CompCert4Lean.Lib.Integers.Int64.unsigned i) := by
      have hi := i.intrange.1
      change (-1 : Int) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Lib.Integers.Int64.unsigned i) at hi
      change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Lib.Integers.Int64.unsigned i)
      omega
    have hmax : suffix_zLe
        (CompCert4Lean.Lib.Integers.Int64.unsigned i)
        CompCert4Lean.Lib.Integers.Int64.max_unsigned := by
      have hi := i.intrange.2
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int64.unsigned i) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          CompCert4Lean.Lib.Integers.Int64.modulus at hi
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int64.unsigned i) ≤
        (2 ^ 64 : Int) - 1
      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int64.unsigned i) <
        (2 ^ 64 : Int) at hi
      omega
    have hu := int64_unsigned_repr_small
      (CompCert4Lean.Lib.Integers.Int64.unsigned i) ⟨hnonneg, hmax⟩
    have hi_repr : CompCert4Lean.Lib.Integers.Int64.repr
        (CompCert4Lean.Lib.Integers.Int64.unsigned i) = i := by
      apply CompCert4Lean.Lib.Integers.WordCore.ext
      exact hu
    rw [hu]
    exact congrArg CompCert4Lean.Lib.Integers.WordCore.Word.intval hi_repr
  rw [hi0]
  exact h

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

private theorem int64_repr_unsigned_local
    (x : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.repr
        (CompCert4Lean.Lib.Integers.Int64.unsigned x) = x := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext
  have hnonneg : suffix_zLe suffix_zZero
      (CompCert4Lean.Lib.Integers.Int64.unsigned x) := by
    have hx := x.intrange.1
    change (-1 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int64.unsigned x) at hx
    change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Lib.Integers.Int64.unsigned x)
    omega
  have hmax : suffix_zLe
      (CompCert4Lean.Lib.Integers.Int64.unsigned x)
      CompCert4Lean.Lib.Integers.Int64.max_unsigned := by
    have hx := x.intrange.2
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Lib.Integers.Int64.unsigned x) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        CompCert4Lean.Lib.Integers.Int64.modulus at hx
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Lib.Integers.Int64.unsigned x) ≤
      (2 ^ 64 : Int) - 1
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Lib.Integers.Int64.unsigned x) <
      (2 ^ 64 : Int) at hx
    omega
  exact int64_unsigned_repr_small
    (CompCert4Lean.Lib.Integers.Int64.unsigned x) ⟨hnonneg, hmax⟩

private theorem make_ptrofs_of_int_correct_aux
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_ptrofs_of_int_correctStatement := by
  intro ge e le m a i si h
  simp [CompCert4Lean.X86_64.Archi.ptr64]
  cases si with
  | Signed =>
      apply Csharpminor.eval_Eunop
      · exact h
      · change some (CompCert4Lean.Common.Values.Vlong (CompCert4Lean.Lib.Integers.Int64.repr
            (CompCert4Lean.Lib.Integers.Int.signed i))) =
          some (CompCert4Lean.Common.Values.Vlong (CompCert4Lean.Lib.Integers.Int64.repr
            (CompCert4Lean.Lib.Integers.Ptrofs.unsigned
              (CompCert4Lean.Lib.Integers.Ptrofs.repr
                (CompCert4Lean.Lib.Integers.Int.signed i)))))
        congr 2
        exact (int64_repr_unsigned_local
          (CompCert4Lean.Lib.Integers.Int64.repr
            (CompCert4Lean.Lib.Integers.Int.signed i))).symm
  | Unsigned =>
      apply Csharpminor.eval_Eunop
      · exact h
      · change some (CompCert4Lean.Common.Values.Vlong (CompCert4Lean.Lib.Integers.Int64.repr
            (CompCert4Lean.Lib.Integers.Int.unsigned i))) =
          some (CompCert4Lean.Common.Values.Vlong (CompCert4Lean.Lib.Integers.Int64.repr
            (CompCert4Lean.Lib.Integers.Ptrofs.unsigned
              (CompCert4Lean.Lib.Integers.Ptrofs.repr
                (CompCert4Lean.Lib.Integers.Int.unsigned i)))))
        congr 2
        exact (int64_repr_unsigned_local
          (CompCert4Lean.Lib.Integers.Int64.repr
            (CompCert4Lean.Lib.Integers.Int.unsigned i))).symm

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

theorem make_cmp_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_cmp_correctStatement := by
  intro ge cmp
  intro a tya b tyb c va vb v e le m hsem hmake h1 h2
  have hmake_classified :
      CompCert4Lean.Cfrontend.Cshmgen.make_cmp cmp a tya b tyb =
        match CompCert4Lean.Cfrontend.Cop.classify_cmp tya tyb with
        | .cmp_case_pp => .OK (CompCert4Lean.Cfrontend.Cshmgen.make_cmp_ptr cmp a b)
        | .cmp_case_pi si => .OK (CompCert4Lean.Cfrontend.Cshmgen.make_cmp_ptr cmp a
            (if CompCert4Lean.X86_64.Archi.ptr64 then
              CompCert4Lean.Cfrontend.Cshmgen.make_longofint b si else b))
        | .cmp_case_ip si => .OK (CompCert4Lean.Cfrontend.Cshmgen.make_cmp_ptr cmp
            (if CompCert4Lean.X86_64.Archi.ptr64 then
              CompCert4Lean.Cfrontend.Cshmgen.make_longofint a si else a) b)
        | .cmp_case_pl => .OK (CompCert4Lean.Cfrontend.Cshmgen.make_cmp_ptr cmp a
            (if CompCert4Lean.X86_64.Archi.ptr64 then b else
              .Eunop .Ointoflong b))
        | .cmp_case_lp => .OK (CompCert4Lean.Cfrontend.Cshmgen.make_cmp_ptr cmp
            (if CompCert4Lean.X86_64.Archi.ptr64 then a else
              .Eunop .Ointoflong a) b)
        | .cmp_default => CompCert4Lean.Cfrontend.Cshmgen.make_binarith
            (.Ocmp cmp) (.Ocmpu cmp) (.Ocmpf cmp) (.Ocmpfs cmp)
            (.Ocmpl cmp) (.Ocmplu cmp) a tya b tyb := by
    unfold CompCert4Lean.Cfrontend.Cshmgen.make_cmp
      CompCert4Lean.Cfrontend.Cop.classify_cmp
    cases htya : CompCert4Lean.Cfrontend.Ctypes.typeconv tya <;>
      cases htyb : CompCert4Lean.Cfrontend.Ctypes.typeconv tyb <;> rfl
  rw [hmake_classified] at hmake
  unfold CompCert4Lean.Cfrontend.Cop.sem_cmp at hsem
  cases hclass : CompCert4Lean.Cfrontend.Cop.classify_cmp tya tyb <;>
    simp [hclass] at hsem hmake
  case cmp_case_pp =>
    cases hmake
    exact make_cmp_ptr_correct ge cmp e le m a va b vb v hsem h1 h2
  case cmp_case_pi si =>
    cases vb with
    | Vint n =>
        cases hmake
        exact make_cmp_ptr_correct ge cmp e le m a va _ _ v hsem h1
          (make_ptrofs_of_int_correct_aux ge e le m b n si h2)
    | Vptr block ofs =>
        simp [CompCert4Lean.X86_64.Archi.ptr64] at hsem
    | Vlong n | Vfloat n | Vsingle n | Vundef => simp at hsem
  case cmp_case_ip si =>
    cases va with
    | Vint n =>
        cases hmake
        exact make_cmp_ptr_correct ge cmp e le m _ _ b vb v hsem
          (make_ptrofs_of_int_correct_aux ge e le m a n si h1) h2
    | Vptr block ofs =>
        simp [CompCert4Lean.X86_64.Archi.ptr64] at hsem
    | Vlong n | Vfloat n | Vsingle n | Vundef => simp at hsem
  case cmp_case_pl =>
    cases vb with
    | Vlong n =>
        cases hmake
        exact make_cmp_ptr_correct ge cmp e le m a va _ _ v hsem h1
          (make_ptrofs_of_int64_correct ge e le m b n h2)
    | Vptr block ofs =>
        cases hmake
        exact make_cmp_ptr_correct ge cmp e le m a va b (.Vptr block ofs) v hsem h1 h2
    | Vint n | Vfloat n | Vsingle n | Vundef => simp at hsem
  case cmp_case_lp =>
    cases va with
    | Vlong n =>
        cases hmake
        exact make_cmp_ptr_correct ge cmp e le m _ _ b vb v hsem
          (make_ptrofs_of_int64_correct ge e le m a n h1) h2
    | Vptr block ofs =>
        cases hmake
        exact make_cmp_ptr_correct ge cmp e le m a (.Vptr block ofs) b vb v hsem h1 h2
    | Vint n | Vfloat n | Vsingle n | Vundef => simp at hsem
  case cmp_default =>
    let sem_int : Signedness → CCInt → CCInt → Option val :=
      fun sg x y => some (CompCert4Lean.Common.Values.Val.of_bool (match sg with
        | .Signed => CompCert4Lean.Lib.Integers.Int.cmp cmp x y
        | .Unsigned => CompCert4Lean.Lib.Integers.Int.cmpu cmp x y))
    let sem_long : Signedness → CCInt64 → CCInt64 → Option val :=
      fun sg x y => some (CompCert4Lean.Common.Values.Val.of_bool (match sg with
        | .Signed => CompCert4Lean.Lib.Integers.Int64.cmp cmp x y
        | .Unsigned => CompCert4Lean.Lib.Integers.Int64.cmpu cmp x y))
    let sem_float : CCFloat → CCFloat → Option val :=
      fun x y => some (CompCert4Lean.Common.Values.Val.of_bool
        (CompCert4Lean.Lib.Floats.Float.cmp cmp x y))
    let sem_single : CCFloat32 → CCFloat32 → Option val :=
      fun x y => some (CompCert4Lean.Common.Values.Val.of_bool
        (CompCert4Lean.Lib.Floats.Float32.cmp cmp x y))
    have hcorrect := make_binarith_correct ge sem_int sem_long sem_float sem_single
      (.Ocmp cmp) (.Ocmpu cmp) (.Ocmpf cmp) (.Ocmpfs cmp) (.Ocmpl cmp) (.Ocmplu cmp)
      (by intro x y m; simp [sem_int, Csharpminor.eval_binop,
        CompCert4Lean.Backend.Cminor.eval_binop, CompCert4Lean.Common.Values.Val.cmp,
        CompCert4Lean.Common.Values.Val.cmp_bool,
        CompCert4Lean.Common.Values.Val.of_optbool]
        <;> cases hcmp : CompCert4Lean.Lib.Integers.Int.cmp cmp x y <;> rfl)
      (by intro x y m; simp [sem_int, Csharpminor.eval_binop,
        CompCert4Lean.Backend.Cminor.eval_binop, CompCert4Lean.Common.Values.Val.cmpu,
        CompCert4Lean.Common.Values.Val.cmpu_bool,
        CompCert4Lean.Common.Values.Val.of_optbool]
        <;> cases hcmp : CompCert4Lean.Lib.Integers.Int.cmpu cmp x y <;> rfl)
      (by intro x y m; simp [sem_long, Csharpminor.eval_binop,
        CompCert4Lean.Backend.Cminor.eval_binop, CompCert4Lean.Common.Values.Val.cmpl,
        CompCert4Lean.Common.Values.Val.cmpl_bool])
      (by intro x y m; simp [sem_long, Csharpminor.eval_binop,
        CompCert4Lean.Backend.Cminor.eval_binop, CompCert4Lean.Common.Values.Val.cmplu,
        CompCert4Lean.Common.Values.Val.cmplu_bool])
      (by intro x y m; simp [sem_float, Csharpminor.eval_binop,
        CompCert4Lean.Backend.Cminor.eval_binop, CompCert4Lean.Common.Values.Val.cmpf,
        CompCert4Lean.Common.Values.Val.cmpf_bool,
        CompCert4Lean.Common.Values.Val.of_optbool]
        <;> cases hcmp : CompCert4Lean.Lib.Floats.Float.compare x y with
        | none =>
            cases cmp <;> simp [CompCert4Lean.Lib.Floats.Float.cmp,
              CompCert4Lean.Lib.Floats.cmp_of_comparison, hcmp,
              CompCert4Lean.Common.Values.Val.of_bool,
              CompCert4Lean.Common.Values.Vtrue, CompCert4Lean.Common.Values.Vfalse]
        | some ord =>
            cases ord <;> cases cmp <;>
              simp [CompCert4Lean.Lib.Floats.Float.cmp,
                CompCert4Lean.Lib.Floats.cmp_of_comparison, hcmp,
                CompCert4Lean.Common.Values.Val.of_bool,
                CompCert4Lean.Common.Values.Vtrue, CompCert4Lean.Common.Values.Vfalse])
      (by intro x y m; simp [sem_single, Csharpminor.eval_binop,
        CompCert4Lean.Backend.Cminor.eval_binop, CompCert4Lean.Common.Values.Val.cmpfs,
        CompCert4Lean.Common.Values.Val.cmpfs_bool,
        CompCert4Lean.Common.Values.Val.of_optbool]
        <;> cases hcmp : CompCert4Lean.Lib.Floats.Float32.compare x y with
        | none =>
            cases cmp <;> simp [CompCert4Lean.Lib.Floats.Float32.cmp,
              CompCert4Lean.Lib.Floats.cmp_of_comparison, hcmp,
              CompCert4Lean.Common.Values.Val.of_bool,
              CompCert4Lean.Common.Values.Vtrue, CompCert4Lean.Common.Values.Vfalse]
        | some ord =>
            cases ord <;> cases cmp <;>
              simp [CompCert4Lean.Lib.Floats.Float32.cmp,
                CompCert4Lean.Lib.Floats.cmp_of_comparison, hcmp,
                CompCert4Lean.Common.Values.Val.of_bool,
                CompCert4Lean.Common.Values.Vtrue, CompCert4Lean.Common.Values.Vfalse])
    apply hcorrect a tya b tyb c va vb v e le m
    · change CompCert4Lean.Cfrontend.Cop.sem_binarith
          sem_int sem_long sem_float sem_single va tya vb tyb m = some v at hsem
      exact hsem
    · exact hmake
    · exact h1
    · exact h2

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Cfrontend.Cshmgen
open CompCert4Lean.Cfrontend.Csharpminor

private theorem transl_unop_make_neg_aux
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_neg_correctStatement := by
  intro ge a tya c va v e le m hsem hmake hval
  unfold CompCert4Lean.Cfrontend.Cop.sem_neg at hsem
  unfold make_neg at hmake
  cases hclass : CompCert4Lean.Cfrontend.Cop.classify_neg tya <;>
    simp [hclass] at hsem hmake
  case neg_case_i sg =>
    cases va with
    | Vint n =>
        cases hsem
        cases hmake
        apply Csharpminor.eval_Eunop
        · exact hval
        · rfl
    | Vlong n | Vfloat n | Vsingle n | Vptr n _ | Vundef => simp at hsem
  case neg_case_f =>
    cases va with
    | Vfloat f =>
        cases hsem
        cases hmake
        apply Csharpminor.eval_Eunop
        · exact hval
        · rfl
    | Vint n | Vlong n | Vsingle n | Vptr n _ | Vundef => simp at hsem
  case neg_case_s =>
    cases va with
    | Vsingle f =>
        cases hsem
        cases hmake
        apply Csharpminor.eval_Eunop
        · exact hval
        · rfl
    | Vint n | Vlong n | Vfloat n | Vptr n _ | Vundef => simp at hsem
  case neg_case_l sg =>
    cases va with
    | Vlong n =>
        cases hsem
        cases hmake
        apply Csharpminor.eval_Eunop
        · exact hval
        · rfl
    | Vint n | Vfloat n | Vsingle n | Vptr n _ | Vundef => simp at hsem

private theorem transl_unop_make_notbool_aux
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_notbool_correctStatement := by
  intro ge a tya c va v e le m hsem hmake hval
  unfold CompCert4Lean.Cfrontend.Cop.sem_notbool at hsem
  unfold make_notbool at hmake
  cases hclass : CompCert4Lean.Cfrontend.Cop.classify_bool tya <;>
    simp [hclass] at hmake
  case bool_case_i =>
    cases va with
    | Vint n =>
        have hv : CompCert4Lean.Common.Values.Val.of_bool
            (CompCert4Lean.Lib.Integers.Int.eq n
              CompCert4Lean.Lib.Integers.Int.zero) = v := by
          simpa [CompCert4Lean.Cfrontend.Cop.bool_val, hclass] using hsem
        rw [← hv]
        cases hmake
        apply Csharpminor.eval_Ebinop
        · exact hval
        · exact make_intconst_correct ge _ e le m
        · cases heq : CompCert4Lean.Lib.Integers.WordCore.eq n
              CompCert4Lean.Lib.Integers.Int.zero <;>
            simp [Csharpminor.eval_binop, CompCert4Lean.Backend.Cminor.eval_binop,
          CompCert4Lean.Common.Values.Val.cmpu,
          CompCert4Lean.Common.Values.Val.cmpu_bool,
          CompCert4Lean.Lib.Integers.Int.cmpu,
          CompCert4Lean.Lib.Integers.Int.eq,
          CompCert4Lean.Lib.Integers.WordCore.cmpu,
          CompCert4Lean.Common.Values.Val.of_optbool,
          CompCert4Lean.Common.Values.Val.of_bool,
          CompCert4Lean.Common.Values.Vtrue,
          CompCert4Lean.Common.Values.Vfalse, heq]
    | Vlong n | Vfloat n | Vsingle n | Vptr n _ | Vundef =>
        simp [CompCert4Lean.Cfrontend.Cop.bool_val, hclass,
          CompCert4Lean.X86_64.Archi.ptr64] at hsem
  case bool_case_l =>
    cases va with
    | Vlong n =>
        have hv : CompCert4Lean.Common.Values.Val.of_bool
            (CompCert4Lean.Lib.Integers.Int64.eq n
              CompCert4Lean.Lib.Integers.Int64.zero) = v := by
          simpa [CompCert4Lean.Cfrontend.Cop.bool_val, hclass] using hsem
        rw [← hv]
        cases hmake
        apply Csharpminor.eval_Ebinop
        · exact hval
        · exact make_longconst_correct ge _ e le m
        · cases heq : CompCert4Lean.Lib.Integers.WordCore.eq n
              CompCert4Lean.Lib.Integers.Int64.zero <;>
            simp [Csharpminor.eval_binop, CompCert4Lean.Backend.Cminor.eval_binop,
          CompCert4Lean.Common.Values.Val.cmplu,
          CompCert4Lean.Common.Values.Val.cmplu_bool,
          CompCert4Lean.Lib.Integers.Int64.cmpu,
          CompCert4Lean.Lib.Integers.Int64.eq,
          CompCert4Lean.Lib.Integers.WordCore.cmpu,
          CompCert4Lean.Common.Values.Val.of_bool,
          CompCert4Lean.Common.Values.Vtrue,
          CompCert4Lean.Common.Values.Vfalse, heq]
    | Vptr b ofs =>
        cases hweak : CompCert4Lean.Common.Memory.Mem.weak_valid_pointer m b
            (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) <;>
          simp [CompCert4Lean.Cfrontend.Cop.bool_val, hclass,
            CompCert4Lean.X86_64.Archi.ptr64, hweak] at hsem
        have hv : CompCert4Lean.Common.Values.Val.of_bool false = v := by
          simpa [CompCert4Lean.Cfrontend.Cop.bool_val, hclass,
            CompCert4Lean.X86_64.Archi.ptr64, hweak] using hsem
        rw [← hv]
        have hweak' :
            (CompCert4Lean.Common.Memory.Mem.valid_pointer m b
                (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) ||
              CompCert4Lean.Common.Memory.Mem.valid_pointer m b
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub
                  (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs)
                  (.Zpos .xH))) = true := by
          simpa only [CompCert4Lean.Common.Memory.Mem.weak_valid_pointer] using hweak
        cases hmake
        apply Csharpminor.eval_Ebinop
        · exact hval
        · exact make_longconst_correct ge _ e le m
        · simp [Csharpminor.eval_binop, CompCert4Lean.Backend.Cminor.eval_binop,
          CompCert4Lean.Common.Values.Val.cmplu,
          CompCert4Lean.Common.Values.Val.cmplu_bool,
          CompCert4Lean.Lib.Integers.Int64.eq,
          CompCert4Lean.Lib.Integers.WordCore.eq,
          CompCert4Lean.X86_64.Archi.ptr64, hweak',
          CompCert4Lean.Common.Values.Val.cmp_different_blocks,
          CompCert4Lean.Common.Values.Val.of_bool,
          CompCert4Lean.Common.Values.Vtrue,
          CompCert4Lean.Common.Values.Vfalse]
    | Vint n | Vfloat n | Vsingle n | Vundef =>
        simp [CompCert4Lean.Cfrontend.Cop.bool_val, hclass] at hsem
  case bool_case_f =>
    cases va with
    | Vfloat f =>
        have hv : CompCert4Lean.Common.Values.Val.of_bool
            (CompCert4Lean.Lib.Floats.Float.cmp
              .Ceq f CompCert4Lean.Lib.Floats.Float.zero) = v := by
          simpa [CompCert4Lean.Cfrontend.Cop.bool_val, hclass] using hsem
        rw [← hv]
        cases hmake
        apply Csharpminor.eval_Ebinop
        · exact hval
        · exact make_floatconst_correct ge _ e le m
        · cases hcmp : CompCert4Lean.Lib.Floats.Float.cmp
              .Ceq f CompCert4Lean.Lib.Floats.Float.zero <;>
            simp [Csharpminor.eval_binop, CompCert4Lean.Backend.Cminor.eval_binop,
          CompCert4Lean.Common.Values.Val.cmpf,
          CompCert4Lean.Common.Values.Val.cmpf_bool,
          CompCert4Lean.Common.Values.Val.of_optbool,
          CompCert4Lean.Common.Values.Val.of_bool,
          CompCert4Lean.Common.Values.Vtrue,
          CompCert4Lean.Common.Values.Vfalse, hcmp]
    | Vint n | Vlong n | Vsingle n | Vptr n _ | Vundef =>
        simp [CompCert4Lean.Cfrontend.Cop.bool_val, hclass] at hsem
  case bool_case_s =>
    cases va with
    | Vsingle f =>
        have hv : CompCert4Lean.Common.Values.Val.of_bool
            (CompCert4Lean.Lib.Floats.Float32.cmp
              .Ceq f CompCert4Lean.Lib.Floats.Float32.zero) = v := by
          simpa [CompCert4Lean.Cfrontend.Cop.bool_val, hclass] using hsem
        rw [← hv]
        cases hmake
        apply Csharpminor.eval_Ebinop
        · exact hval
        · exact make_singleconst_correct ge _ e le m
        · cases hcmp : CompCert4Lean.Lib.Floats.Float32.cmp
              .Ceq f CompCert4Lean.Lib.Floats.Float32.zero <;>
            simp [Csharpminor.eval_binop, CompCert4Lean.Backend.Cminor.eval_binop,
          CompCert4Lean.Common.Values.Val.cmpfs,
          CompCert4Lean.Common.Values.Val.cmpfs_bool,
          CompCert4Lean.Common.Values.Val.of_optbool,
          CompCert4Lean.Common.Values.Val.of_bool,
          CompCert4Lean.Common.Values.Vtrue,
          CompCert4Lean.Common.Values.Vfalse, hcmp]
    | Vint n | Vlong n | Vfloat n | Vptr n _ | Vundef =>
        simp [CompCert4Lean.Cfrontend.Cop.bool_val, hclass] at hsem
  case bool_default =>
    simp [CompCert4Lean.Cfrontend.Cop.bool_val, hclass] at hsem

theorem transl_unop_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    transl_unop_correctStatement := by
  intro ge op a tya c va v e le m hmake hsem hval
  cases op with
  | Onotbool =>
      exact transl_unop_make_notbool_aux ge a tya c va v e le m hsem hmake hval
  | Onotint =>
      exact make_notint_correct ge a tya c va v e le m hsem hmake hval
  | Oneg =>
      exact transl_unop_make_neg_aux ge a tya c va v e le m hsem hmake hval
  | Oabsfloat =>
      exact make_absfloat_correct ge a tya c va v e le m hsem hmake hval

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open Lean Elab Tactic Meta

theorem int_ltu_true : int_ltu_trueStatement := by
  intro x hx
  have hx0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0 x := by
    change (0 : Int) ≤ intOfZ x
    exact hx.1
  have hxlt : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt x
      CompCert4Lean.Lib.Integers.Int.zwordsize := hx.2
  unfold CompCert4Lean.Lib.Integers.Int.zwordsize at hxlt
  change intOfZ x < (32 : Int) at hxlt
  have hxmax : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le x
      CompCert4Lean.Lib.Integers.Int.max_unsigned := by
    change intOfZ x ≤ intOfZ CompCert4Lean.Lib.Integers.Int.max_unsigned
    have hpow : (32 : Int) < 2 ^ (32 : Nat) := by decide
    change intOfZ x ≤ (2 ^ (32 : Nat) : Int) - 1
    omega
  have hrepr : CompCert4Lean.Lib.Integers.WordCore.unsigned
      (CompCert4Lean.Lib.Integers.Int.repr x) = x := by
    exact CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api x ⟨hx0, hxmax⟩
  have hiword : CompCert4Lean.Lib.Integers.WordCore.unsigned
      CompCert4Lean.Lib.Integers.Int.iwordsize =
      CompCert4Lean.Lib.Integers.Int.zwordsize :=
    CompCert4Lean.Lib.Integers.Int.unsigned_repr_wordsize_proof
  unfold CompCert4Lean.Lib.Integers.Int.ltu CompCert4Lean.Lib.Integers.WordCore.ltu
  rw [hrepr, hiword]
  run_tac
    let env ← Lean.MonadEnv.getEnv
    for (n, _) in env.constants.toList do
      if (toString n).endsWith "Integers.zltSelect" then
        let stx := Lean.mkIdent n
        Lean.Elab.Tactic.evalTactic (← `(tactic| try unfold $stx at *))
    for (n, _) in env.constants.toList do
      if (toString n).endsWith "Integers.sumboolSelect" then
        let stx := Lean.mkIdent n
        Lean.Elab.Tactic.evalTactic (← `(tactic| try unfold $stx at *))
  cases hlt : CompCert4Lean.Lib.Coqlib.zlt x
      CompCert4Lean.Lib.Integers.Int.zwordsize with
  | left h => simp [hlt]
  | right h =>
      exfalso
      change (32 : Int) ≤ intOfZ x at h
      omega

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem first_bit_range : first_bit_rangeStatement := by
  intro sz pos width hpos hwidth hcarrier
  have hpos' : (0 : Int) ≤ intOfZ pos := by
    change (0 : Int) ≤ intOfZ pos
    exact hpos
  have hwidth' : (0 : Int) < intOfZ width := by
    change (0 : Int) < intOfZ width
    exact hwidth
  cases sz with
  | I8 | IBool =>
      have hcarrier' : intOfZ pos + intOfZ width ≤ Int.ofNat 8 := by
        change intOfZ (ZArith.BinInt.Z.add pos width) ≤
          intOfZ (ZArith.BinInt.Z.of_nat 8) at hcarrier
        simpa only [ZArith.BinInt.Z.add, intOfZ_zOfInt,
          ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] using hcarrier
      change intOfZ pos + intOfZ width ≤ (8 : Int) at hcarrier'
      simp [CompCert4Lean.Cfrontend.Cop.first_bit,
        CompCert4Lean.X86_64.Archi.big_endian]
      constructor
      · constructor
        · exact hpos
        · unfold CompCert4Lean.Lib.Integers.Int.zwordsize
          change intOfZ pos < (32 : Int)
          omega
      · constructor
        · change (0 : Int) ≤ intOfZ
            (ZArith.BinInt.Z.sub
              (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.of_nat 32) pos) width)
          simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
          change (0 : Int) ≤ (32 : Int) - intOfZ pos - intOfZ width
          omega
        · change intOfZ
              (ZArith.BinInt.Z.sub
                (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.of_nat 32) pos) width) <
            intOfZ (ZArith.BinInt.Z.of_nat 32)
          simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt,
            ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
          change (32 : Int) - intOfZ pos - intOfZ width < (32 : Int)
          omega
  | I16 =>
      have hcarrier' : intOfZ pos + intOfZ width ≤ Int.ofNat 16 := by
        change intOfZ (ZArith.BinInt.Z.add pos width) ≤
          intOfZ (ZArith.BinInt.Z.of_nat 16) at hcarrier
        simpa only [ZArith.BinInt.Z.add, intOfZ_zOfInt,
          ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] using hcarrier
      change intOfZ pos + intOfZ width ≤ (16 : Int) at hcarrier'
      simp [CompCert4Lean.Cfrontend.Cop.first_bit,
        CompCert4Lean.X86_64.Archi.big_endian]
      constructor
      · constructor
        · exact hpos
        · unfold CompCert4Lean.Lib.Integers.Int.zwordsize
          change intOfZ pos < (32 : Int)
          omega
      · constructor
        · change (0 : Int) ≤ intOfZ
            (ZArith.BinInt.Z.sub
              (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.of_nat 32) pos) width)
          simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
          change (0 : Int) ≤ (32 : Int) - intOfZ pos - intOfZ width
          omega
        · change intOfZ
              (ZArith.BinInt.Z.sub
                (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.of_nat 32) pos) width) <
            intOfZ (ZArith.BinInt.Z.of_nat 32)
          simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt,
            ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
          change (32 : Int) - intOfZ pos - intOfZ width < (32 : Int)
          omega
  | I32 =>
      have hcarrier' : intOfZ pos + intOfZ width ≤ Int.ofNat 32 := by
        change intOfZ (ZArith.BinInt.Z.add pos width) ≤
          intOfZ (ZArith.BinInt.Z.of_nat 32) at hcarrier
        simpa only [ZArith.BinInt.Z.add, intOfZ_zOfInt,
          ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] using hcarrier
      change intOfZ pos + intOfZ width ≤ (32 : Int) at hcarrier'
      simp [CompCert4Lean.Cfrontend.Cop.first_bit,
        CompCert4Lean.X86_64.Archi.big_endian]
      constructor
      · constructor
        · exact hpos
        · unfold CompCert4Lean.Lib.Integers.Int.zwordsize
          change intOfZ pos < (32 : Int)
          omega
      · constructor
        · change (0 : Int) ≤ intOfZ
            (ZArith.BinInt.Z.sub
              (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.of_nat 32) pos) width)
          simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
          change (0 : Int) ≤ (32 : Int) - intOfZ pos - intOfZ width
          omega
        · change intOfZ
              (ZArith.BinInt.Z.sub
                (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.of_nat 32) pos) width) <
            intOfZ (ZArith.BinInt.Z.of_nat 32)
          simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt,
            ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
          change (32 : Int) - intOfZ pos - intOfZ width < (32 : Int)
          omega

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Cshmgen
open CompCert4Lean.Cfrontend.Csharpminor
open CompCert4Lean.Cfrontend.Ctypes

private abbrev suffix_two_power_nat := ZArith.Zpower.two_power_nat
private abbrev suffix_zMin := ZArith.BinInt.Z.min

private theorem suffix_intOfZ_two_power_nat (n : Nat) :
    intOfZ (suffix_two_power_nat n) = (2 : Int) ^ n := by
  unfold suffix_two_power_nat ZArith.Zpower.two_power_nat
  unfold ZArith.BinInt.Z.pow ZArith.BinInt.Z.of_nat
  simp only [intOfZ_zOfInt]
  have h2 : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
  rw [h2]
  split
  · next h => exact (Int.not_lt_of_ge (Int.natCast_nonneg _) h).elim
  · rw [intOfZ_zOfInt]
    rfl

private theorem suffix_two_power_nat_ge_eight (n : Nat) (h : 4 ≤ n) :
    (8 : Int) ≤ intOfZ (suffix_two_power_nat n) := by
  rw [suffix_intOfZ_two_power_nat]
  have hp : ∀ m : Nat, (2 : Int) ^ m = Int.ofNat (2 ^ m) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [Int.pow_succ, ih]
        rfl
  rw [hp n]
  change Int.ofNat 8 ≤ Int.ofNat (2 ^ n)
  exact Int.ofNat_le.mpr
    (Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) h))

private theorem suffix_min_eight_two_power_nat (n : Nat) (h : 4 ≤ n) :
    suffix_zMin (zOfNat 8) (suffix_two_power_nat n) = zOfNat 8 := by
  unfold suffix_zMin ZArith.BinInt.Z.min
  split
  · rfl
  · next hnot =>
      exfalso
      exact hnot (by
        change (8 : Int) ≤ intOfZ (suffix_two_power_nat n)
        exact suffix_two_power_nat_ge_eight n h)

private theorem suffix_two_power_succ (n : Nat) :
    suffix_two_power_nat (n + 1) =
      ZArith.BinInt.Z.mul (zOfNat 2) (suffix_two_power_nat n) := by
  apply intOfZ_injective
  unfold suffix_two_power_nat ZArith.Zpower.two_power_nat
  simp only [ZArith.BinInt.Z.pow, ZArith.BinInt.Z.of_nat,
    ZArith.BinInt.Z.mul, intOfZ_zOfInt]
  have h2 : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
  rw [h2]
  have hnonneg_succ : ¬ (Int.ofNat (n + 1) < 0) :=
    Int.not_lt_of_ge (Int.ofNat_nonneg _)
  have hnonneg : ¬ (Int.ofNat n < 0) :=
    Int.not_lt_of_ge (Int.ofNat_nonneg _)
  simp only [if_neg hnonneg_succ, if_neg hnonneg, intOfZ_zOfInt]
  change (2 : Int) ^ n.succ = 2 * (2 : Int) ^ n
  rw [Int.pow_succ]
  simp [Int.mul_comm]

private theorem suffix_divide_eight_two_power (n : Nat) (h : 3 ≤ n) :
    ZArith.BinInt.Z.divide (zOfNat 8) (suffix_two_power_nat n) := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn : 3 ≤ n
      · rcases ih hn with ⟨k, hk⟩
        refine ⟨ZArith.BinInt.Z.mul (zOfNat 2) k, ?_⟩
        rw [suffix_two_power_succ, hk]
        apply intOfZ_injective
        simp [zOfInt_intOfZ, intOfZ_zOfInt, ZArith.BinInt.Z.mul,
          ZArith.BinInt.Z.of_nat,
          Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      · have hn2 : n = 2 := by omega
        subst n
        refine ⟨zOfNat 1, ?_⟩
        decide

private theorem suffix_min_align_divides (co : Ctypes.composite) :
    ZArith.BinInt.Z.divide
      (suffix_zMin (zOfNat 8) co.co_alignof) co.co_alignof := by
  rcases co.co_alignof_two_p with ⟨n, hn⟩
  rw [hn]
  by_cases hs : n < 4
  · have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl <;>
      simp [suffix_zMin, ZArith.BinInt.Z.min] <;>
      exact ZArith.BinInt.Z.divide_refl _
  · rw [suffix_min_eight_two_power_nat n (by omega)]
    exact suffix_divide_eight_two_power n (by omega)

private theorem suffix_sizeof_alignof_blockcopy (env : composite_env) :
    ∀ t, ZArith.BinInt.Z.divide
      (alignof_blockcopy env t) (Ctypes.sizeof env t) := by
  intro t
  cases t with
  | Tvoid => exact ZArith.BinInt.Z.divide_refl _
  | Tint sz sg a => cases sz <;> exact ZArith.BinInt.Z.divide_refl _
  | Tlong sg a => exact ZArith.BinInt.Z.divide_refl _
  | Tfloat sz a => cases sz <;> exact ZArith.BinInt.Z.divide_refl _
  | Tpointer t a =>
      simp [alignof_blockcopy, Ctypes.sizeof,
        CompCert4Lean.X86_64.Archi.ptr64]
      exact ZArith.BinInt.Z.divide_refl _
  | Tarray t n a =>
      simpa [alignof_blockcopy, Ctypes.sizeof] using
        (ZArith.BinInt.Z.divide_mul_l _ _ _ (suffix_sizeof_alignof_blockcopy env t))
  | Tfunction args res cc => exact ZArith.BinInt.Z.divide_refl _
  | Tstruct id a =>
      simp only [alignof_blockcopy, Ctypes.sizeof]
      cases hget : CompCert4Lean.Lib.Maps.PTree.get id env with
      | none => exact ZArith.BinInt.Z.divide_0_r _
      | some co =>
          exact ZArith.BinInt.Z.divide_trans _ _ _
            (suffix_min_align_divides co) co.co_sizeof_alignof
  | Tunion id a =>
      simp only [alignof_blockcopy, Ctypes.sizeof]
      cases hget : CompCert4Lean.Lib.Maps.PTree.get id env with
      | none => exact ZArith.BinInt.Z.divide_0_r _
      | some co =>
          exact ZArith.BinInt.Z.divide_trans _ _ _
            (suffix_min_align_divides co) co.co_sizeof_alignof

theorem make_memcpy_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_memcpy_correctStatement := by
  intro xi cunit prog hlink ge f dst src ty k e le m b ofs v m' s hdst hsrc hassign hmode hmake
  cases hassign with
  | assign_loc_copy b' ofs' bytes m' hmode' hsrcAlign hdstAlign hseparated hload hstore =>
      cases hsize : Cshmgen.sizeof cunit.prog_comp_env ty with
      | Error msg => simp [Cshmgen.make_memcpy, hsize] at hmake
      | OK sz =>
          have hmake' : s = .Sbuiltin none
              (.EF_memcpy sz (alignof_blockcopy cunit.prog_comp_env ty)) [dst, src] := by
            simpa [Cshmgen.make_memcpy, hsize] using hmake.symm
          subst s
          have htrans := transl_alignof_blockcopy cunit prog ty sz hlink hsize
          rcases htrans with ⟨hsize_eq, halign_eq⟩
          apply Csharpminor.step_builtin f none
            (.EF_memcpy sz (alignof_blockcopy cunit.prog_comp_env ty))
            [dst, src] k e le m [Vptr b ofs, Vptr b' ofs'] E0 Vundef m'
          · constructor
            · exact hdst
            · constructor
              · exact hsrc
              · exact eval_Enil
          · apply extcall_memcpy_sem_intro
            · exact Ctypes.alignof_blockcopy_1248 cunit.prog_comp_env ty
            · rw [hsize_eq]
              exact Ctypes.sizeof_pos prog.prog_comp_env ty
            · simpa [halign_eq, hsize_eq] using
                (suffix_sizeof_alignof_blockcopy prog.prog_comp_env ty)
            · intro hs
              rw [halign_eq]
              apply hsrcAlign
              simpa [hsize_eq] using hs
            · intro hs
              rw [halign_eq]
              apply hdstAlign
              simpa [hsize_eq] using hs
            · simpa [hsize_eq] using hseparated
            · simpa [hsize_eq] using hload
            · exact hstore
  | assign_loc_value v chunk m' hmode' hstore =>
      have hbad : (By_copy : mode) = By_value chunk := hmode.symm.trans hmode'
      cases hbad

end CompCert4Lean.Cfrontend.Cshmgenproof

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

local instance : HSub Z Z Z := ⟨ZArith.BinInt.Z.sub⟩
private abbrev suffix_zsub (a b : Z) : Z := ZArith.BinInt.Z.sub a b

private theorem suffix_make_store_bitfield_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    ∀ (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
      (prog : CProgram) (ge : TGenv) (f : TFunction)
      sz sg pos width dst src ty k e le m b ofs v m' s,
    T_eval_expr ge e le m dst (.Vptr b ofs) →
    T_eval_expr ge e le m src v →
    Clight.assign_loc prog.prog_comp_env ty m b ofs (.Bits sz sg pos width) v m' →
    make_store_bitfield sz sg pos width dst src = .OK s →
    T_step xi ge (.State f s k e le m) E0
      (.State f .Sskip k e le m') := by
  intro xi prog ge f sz sg pos width dst src ty k e le m b ofs v m' s
    hdst hsrc hassign hmake
  cases hassign with
  | assign_loc_bitfield sz sg pos width v m' v' hstore =>
      cases hstore with
      | store_bitfield_intro sz sg1 attr sg pos width m addr c n m'
          hpos hwidth hcarrier hsg hload hstore =>
          have hfirst := first_bit_range sz pos width hpos hwidth.1 hcarrier
          have hwidth0 : ZArith.BinInt.Z.le
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0) width :=
            ZArith.Zorder.Zlt_le_weak_proof _ _ hwidth.1
          have hshl : CompCert4Lean.Lib.Integers.Int.ltu
              (CompCert4Lean.Lib.Integers.Int.repr (Cop.first_bit sz pos width))
              CompCert4Lean.Lib.Integers.Int.iwordsize = true :=
            int_ltu_true _ hfirst.1
          simp only [Cshmgen.make_store_bitfield] at hmake
          split at hmake <;> try contradiction
          cases hmake
          apply Csharpminor.step_store
          · exact hdst
          · refine Csharpminor.eval_Ebinop .Oor _ _
              (.Vint (CompCert4Lean.Lib.Integers.Int.and
                (CompCert4Lean.Lib.Integers.Int.shl n
                  (CompCert4Lean.Lib.Integers.Int.repr
                    (Cop.first_bit sz pos width)))
                (CompCert4Lean.Lib.Integers.Int.shl
                  (CompCert4Lean.Lib.Integers.Int.repr
                    (suffix_zsub (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpower.two_p width)
                      (zOfNat 1)))
                  (CompCert4Lean.Lib.Integers.Int.repr
                    (Cop.first_bit sz pos width)))))
              (.Vint (CompCert4Lean.Lib.Integers.Int.and c
                (CompCert4Lean.Lib.Integers.Int.not
                  (CompCert4Lean.Lib.Integers.Int.shl
                    (CompCert4Lean.Lib.Integers.Int.repr
                      (suffix_zsub (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpower.two_p width)
                        (zOfNat 1)))
                    (CompCert4Lean.Lib.Integers.Int.repr
                      (Cop.first_bit sz pos width))))))
              (.Vint (CompCert4Lean.Lib.Integers.Int.bitfield_insert
                (Cop.first_bit sz pos width) width c n)) ?_ ?_ ?_
            · refine Csharpminor.eval_Ebinop .Oand _ _
                (.Vint (CompCert4Lean.Lib.Integers.Int.shl n
                  (CompCert4Lean.Lib.Integers.Int.repr
                    (Cop.first_bit sz pos width))))
                (.Vint (CompCert4Lean.Lib.Integers.Int.shl
                  (CompCert4Lean.Lib.Integers.Int.repr
                    (suffix_zsub (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpower.two_p width)
                      (zOfNat 1)))
                  (CompCert4Lean.Lib.Integers.Int.repr
                    (Cop.first_bit sz pos width))))
                (.Vint (CompCert4Lean.Lib.Integers.Int.and
                  (CompCert4Lean.Lib.Integers.Int.shl n
                    (CompCert4Lean.Lib.Integers.Int.repr
                      (Cop.first_bit sz pos width)))
                  (CompCert4Lean.Lib.Integers.Int.shl
                    (CompCert4Lean.Lib.Integers.Int.repr
                      (suffix_zsub (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpower.two_p width)
                        (zOfNat 1)))
                    (CompCert4Lean.Lib.Integers.Int.repr
                      (Cop.first_bit sz pos width))))) ?_ ?_ ?_
              · refine Csharpminor.eval_Ebinop .Oshl _ _ (.Vint n)
                  (.Vint (CompCert4Lean.Lib.Integers.Int.repr
                    (Cop.first_bit sz pos width)))
                  (.Vint (CompCert4Lean.Lib.Integers.Int.shl n
                    (CompCert4Lean.Lib.Integers.Int.repr
                      (Cop.first_bit sz pos width)))) ?_ ?_ ?_
                · exact hsrc
                · exact make_intconst_correct ge _ e le m
                · simp [Csharpminor.eval_binop,
                    CompCert4Lean.Backend.Cminor.eval_binop,
                    CompCert4Lean.Common.Values.Val.shl, hshl]
              · exact make_intconst_correct ge _ e le m
              · simp [Csharpminor.eval_binop,
                  CompCert4Lean.Backend.Cminor.eval_binop,
                  CompCert4Lean.Common.Values.Val.and]
            · refine Csharpminor.eval_Ebinop .Oand _ _ (.Vint c)
                (.Vint (CompCert4Lean.Lib.Integers.Int.not
                  (CompCert4Lean.Lib.Integers.Int.shl
                    (CompCert4Lean.Lib.Integers.Int.repr
                      (suffix_zsub (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpower.two_p width)
                        (zOfNat 1)))
                    (CompCert4Lean.Lib.Integers.Int.repr
                      (Cop.first_bit sz pos width)))))
                (.Vint (CompCert4Lean.Lib.Integers.Int.and c
                  (CompCert4Lean.Lib.Integers.Int.not
                    (CompCert4Lean.Lib.Integers.Int.shl
                      (CompCert4Lean.Lib.Integers.Int.repr
                        (suffix_zsub (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpower.two_p width)
                          (zOfNat 1)))
                      (CompCert4Lean.Lib.Integers.Int.repr
                        (Cop.first_bit sz pos width)))))) ?_ ?_ ?_
              · refine Csharpminor.eval_Eload _ _ (.Vptr b ofs) (.Vint c) ?_ ?_
                · exact hdst
                · exact hload
              · exact make_intconst_correct ge _ e le m
              · simp [Csharpminor.eval_binop,
                  CompCert4Lean.Backend.Cminor.eval_binop,
                  CompCert4Lean.Common.Values.Val.and]
            · have halt :=
                CompCert4Lean.Lib.Integers.Int.bitfield_insert_alternative_proof
                  (Cop.first_bit sz pos width) width c n hwidth0
              simp only [Csharpminor.eval_binop,
                CompCert4Lean.Backend.Cminor.eval_binop,
                CompCert4Lean.Common.Values.Val.or,
                Option.some.injEq]
              congr 1
              exact halt.symm
          · exact hstore

theorem make_store_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_store_correctStatement := by
  intro xi cunit prog hlink ge addr ty bf rhs code e le m b ofs v m' f k
    hmake haddr hrhs hassign
  cases hassign with
  | assign_loc_value v chunk m' hmode hstore =>
      simp [Cshmgen.make_store, hmode] at hmake
      cases hmake
      exact Csharpminor.step_store f chunk addr rhs k e le m
        (.Vptr b ofs) v m' haddr hrhs hstore
  | assign_loc_copy b' ofs' bytes m' hmode hsrcAlign hdstAlign hseparated hload hstore =>
      have hmake' : make_memcpy cunit.prog_comp_env addr rhs ty = .OK code := by
        simpa [Cshmgen.make_store, hmode] using hmake
      exact make_memcpy_correct xi cunit prog hlink ge f addr rhs ty k e le m
        b ofs (.Vptr b' ofs') m' code haddr hrhs
        (Clight.assign_loc.assign_loc_copy b' ofs' bytes m' hmode hsrcAlign
          hdstAlign hseparated hload hstore) hmode hmake'
  | assign_loc_bitfield sz sg pos width v m' v' hstore =>
      exact suffix_make_store_bitfield_correct xi prog ge f sz sg pos width
        addr rhs ty k e le m b ofs v m' code haddr hrhs
        (Clight.assign_loc.assign_loc_bitfield sz sg pos width v m' v' hstore)
        hmake

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Cfrontend.Cshmgen
open CompCert4Lean.Cfrontend.Csharpminor
open CompCert4Lean.Cfrontend.Ctyping

theorem make_normalization_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_normalization_correctStatement := by
  intro ge e le m a v t h_eval h_wt
  have hzero : CompCert4Lean.Lib.Integers.Int.zero_ext
      (zOfNat 8) CompCert4Lean.Lib.Integers.Int.zero =
      CompCert4Lean.Lib.Integers.Int.zero := by decide
  have hone : CompCert4Lean.Lib.Integers.Int.zero_ext
      (zOfNat 8) CompCert4Lean.Lib.Integers.Int.one =
      CompCert4Lean.Lib.Integers.Int.one := by decide

  have hcast8s (n : CompCert4Lean.Lib.Integers.int)
      (hn : CompCert4Lean.Lib.Integers.Int.sign_ext (zOfNat 8) n = n)
      (hev : T_eval_expr ge e le m a (.Vint n)) :
      T_eval_expr ge e le m (.Eunop .Ocast8signed a) (.Vint n) := by
    refine Csharpminor.eval_Eunop .Ocast8signed a (.Vint n) (.Vint n) ?_ ?_
    · exact hev
    · simp [Csharpminor.eval_unop, CompCert4Lean.Backend.Cminor.eval_unop,
        CompCert4Lean.Common.Values.Val.sign_ext]
      exact Eq.trans (by rfl) hn

  have hcast8u (n : CompCert4Lean.Lib.Integers.int)
      (hn : CompCert4Lean.Lib.Integers.Int.zero_ext (zOfNat 8) n = n)
      (hev : T_eval_expr ge e le m a (.Vint n)) :
      T_eval_expr ge e le m (.Eunop .Ocast8unsigned a) (.Vint n) := by
    refine Csharpminor.eval_Eunop .Ocast8unsigned a (.Vint n) (.Vint n) ?_ ?_
    · exact hev
    · simp [Csharpminor.eval_unop, CompCert4Lean.Backend.Cminor.eval_unop,
        CompCert4Lean.Common.Values.Val.zero_ext]
      exact Eq.trans (by rfl) hn

  have hcast16s (n : CompCert4Lean.Lib.Integers.int)
      (hn : CompCert4Lean.Lib.Integers.Int.sign_ext (zOfNat 16) n = n)
      (hev : T_eval_expr ge e le m a (.Vint n)) :
      T_eval_expr ge e le m (.Eunop .Ocast16signed a) (.Vint n) := by
    refine Csharpminor.eval_Eunop .Ocast16signed a (.Vint n) (.Vint n) ?_ ?_
    · exact hev
    · simp [Csharpminor.eval_unop, CompCert4Lean.Backend.Cminor.eval_unop,
        CompCert4Lean.Common.Values.Val.sign_ext]
      exact Eq.trans (by rfl) hn

  have hcast16u (n : CompCert4Lean.Lib.Integers.int)
      (hn : CompCert4Lean.Lib.Integers.Int.zero_ext (zOfNat 16) n = n)
      (hev : T_eval_expr ge e le m a (.Vint n)) :
      T_eval_expr ge e le m (.Eunop .Ocast16unsigned a) (.Vint n) := by
    refine Csharpminor.eval_Eunop .Ocast16unsigned a (.Vint n) (.Vint n) ?_ ?_
    · exact hev
    · simp [Csharpminor.eval_unop, CompCert4Lean.Backend.Cminor.eval_unop,
        CompCert4Lean.Common.Values.Val.zero_ext]
      exact Eq.trans (by rfl) hn

  have hcast8s_undef (hev : T_eval_expr ge e le m a .Vundef) :
      T_eval_expr ge e le m (.Eunop .Ocast8signed a) .Vundef := by
    refine Csharpminor.eval_Eunop .Ocast8signed a .Vundef .Vundef ?_ ?_
    · exact hev
    · rfl

  have hcast8u_undef (hev : T_eval_expr ge e le m a .Vundef) :
      T_eval_expr ge e le m (.Eunop .Ocast8unsigned a) .Vundef := by
    refine Csharpminor.eval_Eunop .Ocast8unsigned a .Vundef .Vundef ?_ ?_
    · exact hev
    · rfl

  have hcast16s_undef (hev : T_eval_expr ge e le m a .Vundef) :
      T_eval_expr ge e le m (.Eunop .Ocast16signed a) .Vundef := by
    refine Csharpminor.eval_Eunop .Ocast16signed a .Vundef .Vundef ?_ ?_
    · exact hev
    · rfl

  have hcast16u_undef (hev : T_eval_expr ge e le m a .Vundef) :
      T_eval_expr ge e le m (.Eunop .Ocast16unsigned a) .Vundef := by
    refine Csharpminor.eval_Eunop .Ocast16unsigned a .Vundef .Vundef ?_ ?_
    · exact hev
    · rfl

  cases t with
  | Tvoid => exact h_eval
  | Tint size signed attr =>
      cases size with
      | I8 =>
          cases signed with
          | Signed =>
              cases h_wt with
              | wt_val_int n _ _ _ hwt =>
                  exact hcast8s n (Eq.trans (by rfl) hwt) h_eval
              | wt_val_undef _ => exact hcast8s_undef h_eval
          | Unsigned =>
              cases h_wt with
              | wt_val_int n _ _ _ hwt =>
                  exact hcast8u n (Eq.trans (by rfl) hwt) h_eval
              | wt_val_undef _ => exact hcast8u_undef h_eval
      | I16 =>
          cases signed with
          | Signed =>
              cases h_wt with
              | wt_val_int n _ _ _ hwt =>
                  exact hcast16s n (Eq.trans (by rfl) hwt) h_eval
              | wt_val_undef _ => exact hcast16s_undef h_eval
          | Unsigned =>
              cases h_wt with
              | wt_val_int n _ _ _ hwt =>
                  exact hcast16u n (Eq.trans (by rfl) hwt) h_eval
              | wt_val_undef _ => exact hcast16u_undef h_eval
      | I32 => exact h_eval
      | IBool =>
          cases h_wt with
          | wt_val_int n _ _ _ hwt =>
              cases hwt with
              | inl h =>
                  subst n
                  exact hcast8u _ hzero h_eval
              | inr h =>
                  subst n
                  exact hcast8u _ hone h_eval
          | wt_val_undef _ => exact hcast8u_undef h_eval
  | Tlong signed attr => exact h_eval
  | Tfloat size attr => exact h_eval
  | Tpointer ty attr => exact h_eval
  | Tarray ty sz attr => exact h_eval
  | Tfunction args res cc => exact h_eval
  | Tstruct id attr => exact h_eval
  | Tunion id attr => exact h_eval

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem cshmgenproof_add_global_match
    {A B V W : Type} (R : globdef A V → globdef B W → Prop)
    (ge1 : Genv.t A V) (ge2 : Genv.t B W)
    (h : Genv.match_genvs R ge1 ge2)
    (id : ident) (g1 : globdef A V) (g2 : globdef B W) (hr : R g1 g2) :
    Genv.match_genvs R (Genv.add_global ge1 (id, g1))
      (Genv.add_global ge2 (id, g2)) := by
  change positive at id
  constructor
  · simp only [Genv.add_global]
    change PArith.BinPos.Pos.succ ge2.genv_next =
      PArith.BinPos.Pos.succ ge1.genv_next
    exact congrArg _ h.mge_next
  · intro id'
    simp only [Genv.add_global]
    change PTree.get id' (PTree.set id ge2.genv_next ge2.genv_symb) =
      PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb)
    have hx2 := @PTree.gsspec_proof _ id' id ge2.genv_next ge2.genv_symb
    have hx1 := @PTree.gsspec_proof _ id' id ge1.genv_next ge1.genv_symb
    cases heq : peq id' id with
    | left hij =>
        have hx2' : PTree.get id' (PTree.set id ge2.genv_next ge2.genv_symb) =
            some ge2.genv_next := by
          simpa [heq] using hx2
        have hx1' : PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb) =
            some ge1.genv_next := by
          simpa [heq] using hx1
        rw [hx2', hx1', h.mge_next]
    | right hne =>
        have hx2' : PTree.get id' (PTree.set id ge2.genv_next ge2.genv_symb) =
            PTree.get id' ge2.genv_symb := by
          simpa [heq] using hx2
        have hx1' : PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb) =
            PTree.get id' ge1.genv_symb := by
          simpa [heq] using hx1
        rw [hx2', hx1', h.mge_symb]
  · intro b
    simp only [Genv.add_global]
    change option_rel R
      (PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs))
      (PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs))
    have hx1 := @PTree.gsspec_proof _ b ge1.genv_next g1 ge1.genv_defs
    have hx2 := @PTree.gsspec_proof _ b ge2.genv_next g2 ge2.genv_defs
    cases heq : peq b ge1.genv_next with
    | left hb =>
        have heq' : b = ge2.genv_next := hb.trans h.mge_next.symm
        cases hpeq2 : peq b ge2.genv_next with
        | left hb2 =>
            have hx1' : PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs) =
                some g1 := by
              simpa [heq] using hx1
            have hx2' : PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs) =
                some g2 := by
              simpa [hpeq2] using hx2
            rw [hx1', hx2']
            exact option_rel.some g1 g2 hr
        | right hb2 => exact False.elim (hb2 heq')
    | right hb =>
        have hb2 : b ≠ ge2.genv_next := by
          intro hbeq
          apply hb
          exact hbeq.trans h.mge_next
        cases hpeq2 : peq b ge2.genv_next with
        | left hb2' => exact False.elim (hb (hb2'.trans h.mge_next))
        | right hb2' =>
            have hx1' : PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs) =
                PTree.get b ge1.genv_defs := by
              simpa [heq] using hx1
            have hx2' : PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs) =
                PTree.get b ge2.genv_defs := by
              simpa [hpeq2] using hx2
            rw [hx1', hx2']
            exact h.mge_defs b

private theorem cshmgenproof_add_globals_match
    {A B V W : Type} (R : globdef A V → globdef B W → Prop)
    (gl1 : List (ident × globdef A V)) (gl2 : List (ident × globdef B W))
    (ge1 : Genv.t A V) (ge2 : Genv.t B W) :
    list_forall2 (fun x y => x.1 = y.1 ∧ R x.2 y.2) gl1 gl2 →
    Genv.match_genvs R ge1 ge2 →
    Genv.match_genvs R (Genv.add_globals ge1 gl1) (Genv.add_globals ge2 gl2) := by
  intro hlist hge
  induction hlist generalizing ge1 ge2 with
  | nil => exact hge
  | cons hd1 hd2 hhd htl ih =>
      rcases hhd with ⟨hid, hrel⟩
      cases hd1 with
      | mk id1 gd1 =>
          cases hd2 with
          | mk id2 gd2 =>
              simp only [Genv.add_globals, List.foldl]
              change id1 = id2 at hid
              subst id2
              exact ih
                (Genv.add_global ge1 (id1, gd1))
                (Genv.add_global ge2 (id1, gd2))
                (cshmgenproof_add_global_match R ge1 ge2 hge id1 gd1 gd2 hrel)

private theorem cshmgenproof_globalenvs_match
    (p : CProgram) (tp : TProgram)
    (hmatch : match_prog p tp) :
    Genv.match_genvs
      (fun g1 g2 =>
        match g1, g2 with
        | .Gfun f, .Gfun tf =>
            ∃ cu, Ctypes.linkorder_program cu p ∧ match_fundef cu f tf
        | .Gvar v, .Gvar tv =>
            match_varinfo v.gvar_info tv.gvar_info ∧
              v.gvar_init = tv.gvar_init ∧
              v.gvar_readonly = tv.gvar_readonly ∧
              v.gvar_volatile = tv.gvar_volatile
        | _, _ => False)
      (Genv.globalenv (Ctypes.program_of_program p)) (Genv.globalenv tp) := by
  let R : globdef CFundef CType → globdef TFundef Unit → Prop := fun g1 g2 =>
    match g1, g2 with
    | .Gfun f, .Gfun tf =>
        ∃ cu, Ctypes.linkorder_program cu p ∧ match_fundef cu f tf
    | .Gvar v, .Gvar tv =>
        match_varinfo v.gvar_info tv.gvar_info ∧
          v.gvar_init = tv.gvar_init ∧
          v.gvar_readonly = tv.gvar_readonly ∧
          v.gvar_volatile = tv.gvar_volatile
    | _, _ => False
  have hempty : Genv.match_genvs R
      (Genv.empty_genv CFundef CType
        (Ctypes.program_of_program p).prog_public)
      (Genv.empty_genv Csharpminor.fundef Unit tp.prog_public) := by
    constructor
    · rfl
    · intro id
      rfl
    · intro b
      exact option_rel.none _
  have hlist : list_forall2
      (fun x y => x.1 = y.1 ∧ R x.2 y.2)
      (Ctypes.program_of_program p).prog_defs tp.prog_defs := by
    unfold match_prog at hmatch
    have hdefs := hmatch.1
    change list_forall2
      (fun x y => x.1 = y.1 ∧ R x.2 y.2)
      (Ctypes.program_of_program p).prog_defs tp.prog_defs at hdefs
    exact hdefs
  have hall := cshmgenproof_add_globals_match R
    (Ctypes.program_of_program p).prog_defs tp.prog_defs
    (Genv.empty_genv CFundef CType
      (Ctypes.program_of_program p).prog_public)
    (Genv.empty_genv Csharpminor.fundef Unit tp.prog_public)
    hlist hempty
  simpa [Genv.globalenv, R] using hall

theorem symbols_preserved : symbols_preservedStatement := by
  intro prog tprog hmatch s
  have hgenv := cshmgenproof_globalenvs_match prog tprog hmatch
  exact hgenv.mge_symb s

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Lib.Maps

theorem match_env_globals : match_env_globalsStatement := by
  intro prog e te id hmatch hnone
  cases hte : PTree.get id te with
  | none => rfl
  | some pair =>
      rcases pair with ⟨b, sz⟩
      have hex := hmatch.me_local_inv id b sz hte
      rcases hex with ⟨ty, he⟩
      rw [hnone] at he
      cases he

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem cshmgenproof_option_rel_some
    {A B : Type} {R : A → B → Prop} {a : Option A} {b : Option B}
    {x : A} {y : B} (h : option_rel R a b)
    (ha : a = some x) (hb : b = some y) : R x y := by
  cases h with
  | none => cases ha
  | some x' y' hxy =>
      cases ha
      cases hb
      exact hxy

private theorem cshmgenproof_option_rel_some_none
    {A B : Type} {R : A → B → Prop} {a : Option A} {b : Option B}
    {x : A} (h : option_rel R a b)
    (ha : a = some x) (hb : b = none) : False := by
  cases h with
  | none => cases ha
  | some x' y' hxy => cases hb

theorem function_ptr_translated : function_ptr_translatedStatement := by
  intro prog tprog hm b f hfind
  have hg := cshmgenproof_globalenvs_match prog tprog hm
  change Genv.find_funct_ptr (Genv.globalenv (Ctypes.program_of_program prog)) b = some f at hfind
  unfold Genv.find_funct_ptr Genv.find_def at hfind ⊢
  have hsrc : PTree.get b (Genv.globalenv (Ctypes.program_of_program prog)).genv_defs = some (.Gfun f) := by
    cases hfd : PTree.get b (Genv.globalenv (Ctypes.program_of_program prog)).genv_defs with
    | none => simp [hfd] at hfind
    | some gd =>
        cases gd with
        | Gfun f0 =>
            simp [hfd] at hfind
            cases hfind
            rfl
        | Gvar v => simp [hfd] at hfind
  generalize ht : PTree.get b (Genv.globalenv tprog).genv_defs = tgt at ⊢
  cases tgt with
  | none =>
      exact False.elim (cshmgenproof_option_rel_some_none
        (hg.mge_defs b) hsrc ht)
  | some gd2 =>
      cases gd2 with
      | Gfun f2 =>
          have hrel := cshmgenproof_option_rel_some
            (hg.mge_defs b) hsrc ht
          rcases hrel with ⟨ctx', horder, htrans⟩
          refine ⟨ctx', f2, ?_, htrans, horder⟩
          simp [Genv.find_funct_ptr, Genv.find_def, ht]
      | Gvar v2 =>
          have hrel := cshmgenproof_option_rel_some
            (hg.mge_defs b) hsrc ht
          simp at hrel

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Integers

theorem functions_translated : functions_translatedStatement := by
  intro prog tprog hm v f hfind
  change Genv.find_funct (Genv.globalenv (Ctypes.program_of_program prog)) v = some f at hfind
  unfold Genv.find_funct at hfind ⊢
  cases v with
  | Vundef => simp at hfind
  | Vint n => simp at hfind
  | Vlong n => simp at hfind
  | Vfloat n => simp at hfind
  | Vsingle n => simp at hfind
  | Vptr b ofs =>
      cases hzero : Ptrofs.eq ofs Ptrofs.zero with
      | false => simp [hzero] at hfind
      | true =>
          simp [hzero] at hfind ⊢
          exact function_ptr_translated prog tprog hm b f hfind

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem cshmgenproof_option_rel_none_some
    {A B : Type} {R : A → B → Prop} {a : Option A} {b : Option B}
    {y : B} (h : option_rel R a b)
    (ha : a = none) (hb : b = some y) : False := by
  cases h with
  | none => cases hb
  | some x' y' hxy => cases ha

private theorem cshmgenproof_add_globals_public
    {A V : Type} (ge : Genv.t A V) (gl : List (ident × globdef A V)) :
    (Genv.add_globals ge gl).genv_public = ge.genv_public := by
  induction gl generalizing ge with
  | nil => rfl
  | cons x xs ih =>
      simp only [Genv.add_globals, List.foldl]
      exact ih (ge := Genv.add_global ge x)

theorem senv_preserved : senv_preservedStatement := by
  intro prog tprog hm
  have hg := cshmgenproof_globalenvs_match prog tprog hm
  unfold Senv.equiv
  constructor
  · intro id
    exact hg.mge_symb id
  constructor
  · intro id
    change Genv.public_symbol (Genv.globalenv tprog) id =
      Genv.public_symbol (Genv.globalenv (Ctypes.program_of_program prog)) id
    have ht : (Genv.globalenv tprog).genv_public = tprog.prog_public := by
      unfold Genv.globalenv
      exact cshmgenproof_add_globals_public _ _
    have hp :
        (Genv.globalenv (Ctypes.program_of_program prog)).genv_public =
          (Ctypes.program_of_program prog).prog_public := by
      unfold Genv.globalenv
      exact cshmgenproof_add_globals_public _ _
    unfold Genv.public_symbol Genv.find_symbol
    rw [hg.mge_symb id, ht, hp, hm.2.2]
    rfl
  · intro b
    change Genv.block_is_volatile (Genv.globalenv tprog) b =
      Genv.block_is_volatile (Genv.globalenv (Ctypes.program_of_program prog)) b
    unfold Genv.block_is_volatile Genv.find_var_info Genv.find_def
    generalize hs : PTree.get b (Genv.globalenv (Ctypes.program_of_program prog)).genv_defs = src at ⊢
    generalize ht : PTree.get b (Genv.globalenv tprog).genv_defs = tgt at ⊢
    cases src with
    | none =>
        cases tgt with
        | none => rfl
        | some gd2 =>
            exact False.elim (cshmgenproof_option_rel_none_some
              (hg.mge_defs b) hs ht)
    | some gd1 =>
        cases gd1 with
        | Gfun f1 =>
            cases tgt with
            | none =>
                exact False.elim (cshmgenproof_option_rel_some_none
                  (hg.mge_defs b) hs ht)
            | some gd2 =>
                cases gd2 with
                | Gfun f2 => rfl
                | Gvar v2 =>
                    have hrel := cshmgenproof_option_rel_some
                      (hg.mge_defs b) hs ht
                    simp at hrel
        | Gvar v1 =>
            cases tgt with
            | none =>
                exact False.elim (cshmgenproof_option_rel_some_none
                  (hg.mge_defs b) hs ht)
            | some gd2 =>
                cases gd2 with
                | Gfun f2 =>
                    have hrel := cshmgenproof_option_rel_some
                      (hg.mge_defs b) hs ht
                    simp at hrel
                | Gvar v2 =>
                    have hrel := cshmgenproof_option_rel_some
                      (hg.mge_defs b) hs ht
                    exact hrel.2.2.2.symm

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Csharpminor
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Maps

private theorem cshmgenproof_map_list_forall2
    {A B C : Type} {R : A → B → Prop} (f : A → C) (g : B → C) :
    ∀ {xs ys}, CompCert4Lean.Lib.Coqlib.list_forall2 R xs ys →
      (∀ x y, R x y → g y = f x) → ys.map g = xs.map f := by
  intro xs ys hrel hfg
  induction hrel with
  | nil => rfl
  | cons x y hxy htail ih =>
      simp only [List.map_cons]
      rw [hfg x y hxy, ih]

theorem match_env_same_blocks : match_env_same_blocksStatement := by
  intro prog e te hmatch
  have hrel := PTree.elements_canonical_order
    (R := fun x y =>
      y.1 = x.1 ∧ y.2 = Ctypes.sizeof prog.prog_comp_env x.2)
    e te
    (by
      intro id x hx
      rcases x with ⟨b, ty⟩
      exact ⟨(b, Ctypes.sizeof prog.prog_comp_env ty),
        hmatch.me_local id b ty hx, rfl, rfl⟩)
    (by
      intro id y hy
      rcases y with ⟨b, sz⟩
      rcases hmatch.me_local_inv id b sz hy with ⟨ty, hx⟩
      have hlocal := hmatch.me_local id b ty hx
      have hpairs :
          (b, Ctypes.sizeof prog.prog_comp_env ty) = (b, sz) :=
        Option.some.inj (hlocal.symm.trans hy)
      have hsz : Ctypes.sizeof prog.prog_comp_env ty = sz :=
        congrArg Prod.snd hpairs
      exact ⟨(b, ty), hx, rfl, hsz.symm⟩)
  unfold Csharpminor.blocks_of_env Clight.blocks_of_env
  apply cshmgenproof_map_list_forall2
      (Clight.block_of_binding (Clight.globalenv prog))
      Csharpminor.block_of_binding hrel
  intro x y hxy
  rcases x with ⟨idx, ⟨bx, tx⟩⟩
  rcases y with ⟨idy, ⟨bt, sy⟩⟩
  rcases hxy with ⟨_, hb, hs⟩
  simp only [Csharpminor.block_of_binding, Clight.block_of_binding,
    Prod.fst, Prod.snd] at hb hs ⊢
  rw [hb, hs]
  change (bx, (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z),
      Ctypes.sizeof prog.prog_comp_env tx) =
    (bx, (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z),
      Ctypes.sizeof prog.prog_comp_env tx)
  rfl

theorem match_env_empty : match_env_emptyStatement := by
  intro prog
  constructor
  · intro id b ty hget
    change PTree.get id (PTree.empty _) = some (b, ty) at hget
    rw [PTree.gempty] at hget
    cases hget
  · intro id b sz hget
    change PTree.get id (PTree.empty _) = some (b, sz) at hget
    rw [PTree.gempty] at hget
    cases hget

theorem match_env_free_blocks : match_env_free_blocksStatement := by
  intro prog e te m m' hmatch hfree
  rw [match_env_same_blocks prog e te hmatch]
  exact hfree

theorem match_env_alloc_variables : match_env_alloc_variablesStatement := by
  intro prog cunit hlink e1 m1 vars e2 m2 halloc
    tvars te1 hmmap hmatch
  induction halloc generalizing tvars te1 with
  | nil e m =>
      simp only [CompCert4Lean.Common.Errors.mmap] at hmmap
      cases hmmap
      exact ⟨te1, Csharpminor.alloc_variables_nil te1 m, hmatch⟩
  | cons e m id ty vars m1 b1 m2 e2 hmem hrest ih =>
      cases hvar : Cshmgen.transl_var cunit.prog_comp_env (id, ty) with
      | Error msg =>
          simp [CompCert4Lean.Common.Errors.mmap, hvar] at hmmap
      | OK idsize =>
          cases htail : CompCert4Lean.Common.Errors.mmap
              (Cshmgen.transl_var cunit.prog_comp_env) vars with
          | Error msg =>
              simp [CompCert4Lean.Common.Errors.mmap, hvar, htail] at hmmap
          | OK tvars' =>
              simp only [CompCert4Lean.Common.Errors.mmap, hvar, htail] at hmmap
              cases hmmap
              rcases idsize with ⟨tid, sz⟩
              unfold Cshmgen.transl_var at hvar
              cases hsize : Cshmgen.sizeof cunit.prog_comp_env ty with
              | Error msg => simp [hsize] at hvar
              | OK sz' =>
                  simp [hsize] at hvar
                  rcases hvar with ⟨rfl, rfl⟩
                  have hsz := transl_sizeof cunit prog ty sz' hlink hsize
                  subst sz'
                  have hmatch' :
                      match_env prog (PTree.set id (b1, ty) e)
                        (PTree.set id
                          (b1, Ctypes.sizeof prog.prog_comp_env ty) te1) := by
                    constructor
                    · intro id0 b ty0 hget
                      have hsrc := PTree.gsspec_proof
                        (A := CompCert4Lean.Common.Values.block × Ctypes.type)
                        id0 id (b1, ty) e
                      have htgt := PTree.gsspec_proof
                        (A := CompCert4Lean.Common.Values.block ×
                          CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
                        id0 id
                        (b1, Ctypes.sizeof prog.prog_comp_env ty) te1
                      rw [hsrc] at hget
                      rw [htgt]
                      cases hq : CompCert4Lean.Lib.Coqlib.peq id0 id with
                      | left heq =>
                          simp [hq] at hget ⊢
                          exact ⟨hget.1,
                            congrArg (Ctypes.sizeof prog.prog_comp_env) hget.2⟩
                      | right hne =>
                          simp [hq] at hget ⊢
                          exact hmatch.me_local id0 b ty0 hget
                    · intro id0 b size hget
                      have htgt := PTree.gsspec_proof
                        (A := CompCert4Lean.Common.Values.block ×
                          CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
                        id0 id
                        (b1, Ctypes.sizeof prog.prog_comp_env ty) te1
                      have hsrc := PTree.gsspec_proof
                        (A := CompCert4Lean.Common.Values.block × Ctypes.type)
                        id0 id (b1, ty) e
                      rw [htgt] at hget
                      rw [hsrc]
                      cases hq : CompCert4Lean.Lib.Coqlib.peq id0 id with
                      | left heq =>
                          simp [hq] at hget ⊢
                          exact hget.1
                      | right hne =>
                          simp [hq] at hget ⊢
                          exact hmatch.me_local_inv id0 b size hget
                  rcases ih tvars'
                      (PTree.set id
                        (b1, Ctypes.sizeof prog.prog_comp_env ty) te1)
                      htail hmatch' with ⟨te2, halloc2, hmatch2⟩
                  exact ⟨te2,
                    Csharpminor.alloc_variables_cons te1 m id
                      (Ctypes.sizeof prog.prog_comp_env ty) tvars' m1 b1 m2 te2
                      hmem halloc2,
                    hmatch2⟩

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

theorem create_undef_temps_match : create_undef_temps_matchStatement := by
  intro temps
  induction temps with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk id ty =>
          simp only [Clight.create_undef_temps, Csharpminor.create_undef_temps,
            List.map_cons]
          rw [ih]

theorem bind_parameter_temps_match : bind_parameter_temps_matchStatement := by
  intro vars vals le1 le2 h
  induction vars generalizing vals le1 with
  | nil =>
      cases vals with
      | nil =>
          simp only [Clight.bind_parameter_temps] at h
          exact h
      | cons v vs => simp [Clight.bind_parameter_temps] at h
  | cons head tail ih =>
      cases head with
      | mk id ty =>
          cases vals with
          | nil => simp [Clight.bind_parameter_temps] at h
          | cons v vs =>
              apply ih
              simpa [Clight.bind_parameter_temps] using h

theorem transl_vars_names : transl_vars_namesStatement := by
  intro ce vars tvars h
  have hm := CompCert4Lean.Common.Errors.mmap_inversion _ _
    (Cshmgen.transl_var ce) vars tvars h
  have aux : ∀ {xs ys},
      CompCert4Lean.Lib.Coqlib.list_forall2
        (fun x y => Cshmgen.transl_var ce x = .OK y) xs ys →
      ys.map Prod.fst = Clight.var_names xs := by
    intro xs ys hxy
    induction hxy with
    | nil => rfl
    | cons x y hxy htail ih =>
        cases x with
        | mk id ty =>
            cases y with
            | mk id' sz =>
                unfold Cshmgen.transl_var at hxy
                cases hsize : Cshmgen.sizeof ce ty with
                | Error msg => simp [hsize] at hxy
                | OK sz' =>
                    simp [hsize] at hxy
                    cases hxy
                    simp_all [Clight.var_names]
  exact aux hm

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

theorem transl_expr_lvalue
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    transl_expr_lvalueStatement := by
  intro prog cunit hlink e le m a loc ofs bf ta heval htrans
  cases heval with
  | eval_Evar_local id loc ty hfind =>
      refine ⟨.Eaddrof id, ?_, ?_⟩
      · rfl
      · simpa [Cshmgen.transl_expr, Clight.typeof] using htrans
  | eval_Evar_global id loc ty hlocal hglobal =>
      refine ⟨.Eaddrof id, ?_, ?_⟩
      · rfl
      · simpa [Cshmgen.transl_expr, Clight.typeof] using htrans
  | eval_Ederef a ty loc ofs ha =>
      cases htransl : Cshmgen.transl_expr cunit.prog_comp_env a with
      | Error msg =>
          simp only [Cshmgen.transl_expr] at htrans
          simp [htransl] at htrans
      | OK tb =>
          simp only [Cshmgen.transl_expr] at htrans
          simp [htransl] at htrans
          refine ⟨tb, ?_, ?_⟩
          · simp only [Cshmgen.transl_lvalue, htransl]
          · simpa only [Clight.typeof] using htrans
  | eval_Efield_struct a id ty loc ofs structId co att delta bf ha htype hcomposite hoffset =>
      simp only [Cshmgen.transl_expr] at htrans
      cases hbase : Cshmgen.transl_expr cunit.prog_comp_env a with
      | Error msg => simp [hbase] at htrans
      | OK tbase =>
          cases hacc : Cshmgen.make_field_access cunit.prog_comp_env
              (Clight.typeof a) id tbase with
          | Error msg => simp [hbase, hacc] at htrans
          | OK pair =>
              rcases pair with ⟨addr, bf'⟩
              have hload : Cshmgen.make_load addr ty bf' = .OK ta := by
                simpa [hbase, hacc] using htrans
              have haccOrig := hacc
              rw [htype] at hacc
              unfold Cshmgen.make_field_access at hacc
              cases hget : CompCert4Lean.Lib.Maps.PTree.get structId cunit.prog_comp_env with
              | none => simp [hget] at hacc
              | some co' =>
                  cases hfield : Ctypes.field_offset cunit.prog_comp_env id co'.co_members with
                  | Error msg => simp [hget, hfield] at hacc
                  | OK offset =>
                      rcases offset with ⟨delta', bf0⟩
                      simp [hget, hfield] at hacc
                      have hgetprog : CompCert4Lean.Lib.Maps.PTree.get structId
                          prog.prog_comp_env = some co' := hlink.2 structId co' hget
                      have hcomposite' : CompCert4Lean.Lib.Maps.PTree.get structId
                          prog.prog_comp_env = some co := by
                        simpa [Clight.globalenv] using hcomposite
                      have hcoeq : co' = co := Option.some.inj
                        (hgetprog.symm.trans hcomposite')
                      subst co'
                      have hconsistent := Ctypes.build_composite_env_consistent
                        cunit.prog_types cunit.prog_comp_env
                        cunit.prog_comp_env_eq structId co hget
                      have hstable := Ctypes.field_offset_stable
                        cunit.prog_comp_env prog.prog_comp_env hlink.2 id
                        co.co_members hconsistent.co_consistent_complete
                      have hoffset' : Ctypes.field_offset prog.prog_comp_env
                          id co.co_members = .OK (delta, bf) := by
                        simpa [Clight.globalenv] using hoffset
                      have hpairs : (delta, bf) = (delta', bf0) :=
                        CompCert4Lean.Common.Errors.res.OK.inj
                          (hoffset'.symm.trans (hstable.trans hfield))
                      have hbf : bf = bf' :=
                        (congrArg Prod.snd hpairs).trans hacc.2
                      subst bf'
                      refine ⟨addr, ?_, ?_⟩
                      · simp only [Cshmgen.transl_lvalue, hbase, haccOrig]
                      · simpa only [Clight.typeof] using hload
  | eval_Efield_union a id ty loc ofs unionId co att delta bf ha htype hcomposite hoffset =>
      simp only [Cshmgen.transl_expr] at htrans
      cases hbase : Cshmgen.transl_expr cunit.prog_comp_env a with
      | Error msg => simp [hbase] at htrans
      | OK tbase =>
          cases hacc : Cshmgen.make_field_access cunit.prog_comp_env
              (Clight.typeof a) id tbase with
          | Error msg => simp [hbase, hacc] at htrans
          | OK pair =>
              rcases pair with ⟨addr, bf'⟩
              have hload : Cshmgen.make_load addr ty bf' = .OK ta := by
                simpa [hbase, hacc] using htrans
              have haccOrig := hacc
              rw [htype] at hacc
              unfold Cshmgen.make_field_access at hacc
              cases hget : CompCert4Lean.Lib.Maps.PTree.get unionId cunit.prog_comp_env with
              | none => simp [hget] at hacc
              | some co' =>
                  cases hfield : Ctypes.union_field_offset cunit.prog_comp_env
                      id co'.co_members with
                  | Error msg => simp [hget, hfield] at hacc
                  | OK offset =>
                      rcases offset with ⟨delta', bf0⟩
                      simp [hget, hfield] at hacc
                      have hgetprog : CompCert4Lean.Lib.Maps.PTree.get unionId
                          prog.prog_comp_env = some co' := hlink.2 unionId co' hget
                      have hcomposite' : CompCert4Lean.Lib.Maps.PTree.get unionId
                          prog.prog_comp_env = some co := by
                        simpa [Clight.globalenv] using hcomposite
                      have hcoeq : co' = co := Option.some.inj
                        (hgetprog.symm.trans hcomposite')
                      subst co'
                      have hconsistent := Ctypes.build_composite_env_consistent
                        cunit.prog_types cunit.prog_comp_env
                        cunit.prog_comp_env_eq unionId co hget
                      have hstable := Ctypes.union_field_offset_stable
                        cunit.prog_comp_env prog.prog_comp_env hlink.2 id
                        co.co_members hconsistent.co_consistent_complete
                      have hoffset' : Ctypes.union_field_offset prog.prog_comp_env
                          id co.co_members = .OK (delta, bf) := by
                        simpa [Clight.globalenv] using hoffset
                      have hpairs : (delta, bf) = (delta', bf0) :=
                        CompCert4Lean.Common.Errors.res.OK.inj
                          (hoffset'.symm.trans (hstable.trans hfield))
                      have hbf : bf = bf' :=
                        (congrArg Prod.snd hpairs).trans hacc.2
                      subst bf'
                      refine ⟨addr, ?_, ?_⟩
                      · simp only [Cshmgen.transl_lvalue, hbase, haccOrig]
                      · simpa only [Clight.typeof] using hload

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Cfrontend.Cshmgen
open CompCert4Lean.Cfrontend.Ctypes

theorem typlist_of_arglist_eq
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    typlist_of_arglist_eqStatement := by
  intro prog e le m al tyl vl h
  induction h with
  | nil => rfl
  | @cons a rest ty types v1 v2 values ha hcast hrest ih =>
      simp only [typlist_of_arglist, List.map]
      exact congrArg (fun xs => argtype_of_type _ :: xs) ih

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Cfrontend.Csharpminor

theorem match_transl_step
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    match_transl_stepStatement := by
  intro xi tprog ts tk ts' tk' f te le m hmatch
  cases hmatch with
  | match_transl_0 _ _ =>
      exact star_one _ _ _ _ _ _ _ (step_block f ts tk te le m)
  | match_transl_1 _ _ =>
      exact star_refl _ _ _

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Cfrontend.Cshmgen

theorem match_states_skip : match_states_skipStatement := by
  intro prog tprog f e le te nbrk ncnt k tf tk m cu hlink htrans henv hcont
  exact match_states.match_state f nbrk ncnt .Sskip k e le m tf .Sskip tk te .Sskip tk cu
    hlink htrans (by rfl) (match_transl.match_transl_0 _ _) henv hcont

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

theorem match_cont_is_call_cont : match_cont_is_call_contStatement := by
  intro prog tprog ce tyret nbrk ncnt k tk ce' nbrk' ncnt' hmatch hcall
  cases hmatch with
  | match_Kstop ce0 tyret0 nbrk0 ncnt0 =>
      simp [Clight.is_call_cont] at hcall
      exact ⟨match_cont.match_Kstop tyret ce' nbrk' ncnt', trivial⟩
  | match_Kseq ce0 tyret0 nbrk0 ncnt0 s k ts tk htr hmc =>
      simp [Clight.is_call_cont] at hcall
  | match_Kloop1 ce0 tyret0 s1 s2 k ts1 ts2 nbrk0 ncnt0 tk h1 h2 hmc =>
      simp [Clight.is_call_cont] at hcall
  | match_Kloop2 ce0 tyret0 s1 s2 k ts1 ts2 nbrk0 ncnt0 tk h1 h2 hmc =>
      simp [Clight.is_call_cont] at hcall
  | match_Kswitch ce0 tyret0 nbrk0 ncnt0 k tk hmc =>
      simp [Clight.is_call_cont] at hcall
  | match_Kcall ce0 tyret0 nbrk0 ncnt0 nbrk1 ncnt1 f e k id tf te le tk cu hlink htf henv hmc =>
      simp [Clight.is_call_cont] at hcall
      exact ⟨match_cont.match_Kcall (prog := prog) (tprog := tprog)
        (ce := ce') (tyret := tyret) (nbrk := nbrk') (ncnt := ncnt')
        (nbrk' := nbrk1) (ncnt' := ncnt1) f e k id tf te le tk cu
        hlink htf henv hmc, trivial⟩
  | match_Kcall_normalize ce0 tyret0 nbrk0 ncnt0 nbrk1 ncnt1 f e k id a tf te le tk cu hlink htf henv hmc hwt =>
      simp [Clight.is_call_cont] at hcall
      exact ⟨match_cont.match_Kcall_normalize (prog := prog) (tprog := tprog)
        (ce := ce') (tyret := tyret) (nbrk := nbrk') (ncnt := ncnt')
        (nbrk' := nbrk1) (ncnt' := ncnt1) f e k id a tf te le tk cu
        hlink htf henv hmc hwt, trivial⟩

theorem match_cont_call_cont : match_cont_call_contStatement := by
  intro prog tprog ce' nbrk' ncnt' ce tyret nbrk ncnt k tk hmatch
  induction hmatch with
  | match_Kstop ce tyret nbrk ncnt =>
      simp [Clight.call_cont, Csharpminor.call_cont]
      exact match_cont.match_Kstop _ _ nbrk' ncnt'
  | match_Kseq ce tyret nbrk ncnt s k ts tk htr hmc ih =>
      simpa [Clight.call_cont, Csharpminor.call_cont] using ih
  | match_Kloop1 ce tyret s1 s2 k ts1 ts2 nbrk ncnt tk h1 h2 hmc ih =>
      simpa [Clight.call_cont, Csharpminor.call_cont] using ih
  | match_Kloop2 ce tyret s1 s2 k ts1 ts2 nbrk ncnt tk h1 h2 hmc ih =>
      simpa [Clight.call_cont, Csharpminor.call_cont] using ih
  | match_Kswitch ce tyret nbrk ncnt k tk hmc ih =>
      simpa [Clight.call_cont, Csharpminor.call_cont] using ih
  | match_Kcall ce tyret nbrk ncnt nbrk0 ncnt0 f e k id tf te le tk cu hlink htf henv hmc ih =>
      simpa [Clight.call_cont, Csharpminor.call_cont] using
        (match_cont.match_Kcall (prog := prog) (tprog := tprog)
          (ce := ce') (tyret := tyret) (nbrk := nbrk') (ncnt := ncnt')
          (nbrk' := nbrk0) (ncnt' := ncnt0) f e k id tf te le tk cu
          hlink htf henv hmc)
  | match_Kcall_normalize ce tyret nbrk ncnt nbrk0 ncnt0 f e k id a tf te le tk cu hlink htf henv hmc hwt ih =>
      simpa [Clight.call_cont, Csharpminor.call_cont] using
        (match_cont.match_Kcall_normalize (prog := prog) (tprog := tprog)
          (ce := ce') (tyret := tyret) (nbrk := nbrk') (ncnt := ncnt')
          (nbrk' := nbrk0) (ncnt' := ncnt0) f e k id a tf te le tk cu
          hlink htf henv hmc hwt)

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Csharpminor
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib

private theorem cshmgenproof_match_prog_gen (prog : CProgram) (tprog : TProgram)
    (hm : match_prog prog tprog) :
    match_program_gen
      (fun _ f tf => ∃ cu, Ctypes.linkorder_program cu prog ∧ match_fundef cu f tf)
      match_varinfo ()
      (Ctypes.program_of_program prog) tprog := by
  refine ⟨?_, hm.2.1, hm.2.2⟩
  have convert :
      ∀ (src : List (ident × globdef CFundef CType))
        (defs : List (ident × globdef TFundef Unit)),
        list_forall2
          (fun idg tidg =>
            idg.1 = tidg.1 ∧
              match idg.2, tidg.2 with
              | .Gfun f, .Gfun tf =>
                  ∃ cu, Ctypes.linkorder_program cu prog ∧ match_fundef cu f tf
              | .Gvar v, .Gvar tv =>
                  match_varinfo v.gvar_info tv.gvar_info ∧
                    v.gvar_init = tv.gvar_init ∧
                    v.gvar_readonly = tv.gvar_readonly ∧
                    v.gvar_volatile = tv.gvar_volatile
              | _, _ => False) src defs →
        list_forall2
          (match_ident_globdef
            (fun _ f tf => ∃ cu, Ctypes.linkorder_program cu prog ∧ match_fundef cu f tf)
            match_varinfo ()) src defs := by
    intro src
    induction src with
    | nil =>
        intro defs h
        cases h
        exact list_forall2.nil _
    | cons hd tl ih =>
        intro defs h
        cases defs with
        | nil => cases h
        | cons hd' tl' =>
            cases h with
            | cons _ _ hhd htail =>
                rcases hd with ⟨id1, gd1⟩
                rcases hd' with ⟨id2, gd2⟩
                rcases hhd with ⟨hid, hgd⟩
                change id1 = id2 at hid
                subst id2
                apply list_forall2.cons
                · constructor
                  · rfl
                  · cases gd1 with
                    | Gfun f1 =>
                        cases gd2 with
                        | Gfun f2 =>
                            rcases hgd with ⟨cu, horder, hmatch⟩
                            apply match_globdef.match_globdef_fun (ctx' := ())
                            · exact Linker.linkorder_refl ()
                            · exact ⟨cu, horder, hmatch⟩
                        | Gvar v2 => cases hgd
                    | Gvar v1 =>
                        cases gd2 with
                        | Gfun f2 => cases hgd
                        | Gvar v2 =>
                            rcases v1 with ⟨info1, init1, ro1, vol1⟩
                            rcases v2 with ⟨info2, init2, ro2, vol2⟩
                            rcases hgd with
                              ⟨hinfo, rfl, rfl, rfl⟩
                            apply match_globdef.match_globdef_var
                            exact match_globvar.match_globvar_intro match_varinfo
                              info1 info2 init1 ro1 vol1 hinfo
                · exact ih tl' htail
  exact convert _ _ hm.1

theorem transl_initial_states : transl_initial_statesStatement := by
  intro prog tprog hm S hinit
  cases hinit with
  | intro b f m0 hmem hsymbol hfun htype =>
      rcases function_ptr_translated prog tprog hm b f hfun with
        ⟨cu, tf, hfun', hmatchf, horder⟩
      have hmgen := cshmgenproof_match_prog_gen prog tprog hm
      have hmem' : Genv.init_mem tprog = some m0 := by
        exact Genv.init_mem_match
          (C := Unit) (F1 := CFundef) (V1 := CType)
          (F2 := TFundef) (V2 := Unit)
          (match_fundef :=
            fun _ f tf => ∃ cu, Ctypes.linkorder_program cu prog ∧ match_fundef cu f tf)
          (match_varinfo := match_varinfo) ()
          (Ctypes.program_of_program prog) tprog hmgen m0 hmem
      have hmain : tprog.prog_main = (Ctypes.program_of_program prog).prog_main := hm.2.1
      have hsymbol' :
          Genv.find_symbol (Genv.globalenv tprog) tprog.prog_main = some b := by
        calc
          Genv.find_symbol (Genv.globalenv tprog) tprog.prog_main =
              Genv.find_symbol (Genv.globalenv tprog)
                (Ctypes.program_of_program prog).prog_main := by rw [hmain]
          _ = Genv.find_symbol (Genv.globalenv (Ctypes.program_of_program prog))
                (Ctypes.program_of_program prog).prog_main := by
            change Genv.find_symbol (Genv.globalenv tprog)
                (Ctypes.program_of_program prog).prog_main =
              Genv.find_symbol (Clight.globalenv prog).genv_genv
                (Ctypes.program_of_program prog).prog_main
            exact symbols_preserved prog tprog hm
              (Ctypes.program_of_program prog).prog_main
          _ = some b := hsymbol
      have hsig : funsig tf = signature_main := by
        have hs := transl_fundef_sig2 cu f tf [] type_int32s cc_default hmatchf htype
        simpa [signature_main, signature_of_type, rettype_of_type, type_int32s] using hs
      refine ⟨.Callstate tf [] .Kstop m0, ?_, ?_⟩
      · exact Csharpminor.initial_state.initial_state_intro b tf m0 hmem' hsymbol' hfun' hsig
      · apply match_states.match_callstate (ce := cu.prog_comp_env)
          (targs := []) (tres := type_int32s) (cconv := cc_default)
        · exact horder
        · exact hmatchf
        · exact match_cont.match_Kstop _ _ _ _
        · trivial
        · exact htype
        · change list_forall2 _ [] []
          exact list_forall2.nil _

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Csharpminor

theorem transl_final_states : transl_final_statesStatement := by
  intro prog tprog S R r hmatch hfinal
  cases hfinal with
  | intro r m =>
      cases hmatch with
      | match_returnstate res tres k m tk ce hcont hwt =>
          cases hcont
          exact Csharpminor.final_state.final_state_intro r m

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

theorem union_field_offset_stable : union_field_offset_stableStatement := by
  intro cunit prog id co f hlink hget
  have hconsistent := Ctypes.build_composite_env_consistent
    cunit.prog_types cunit.prog_comp_env cunit.prog_comp_env_eq id co hget
  refine ⟨hlink.2 id co hget, ?_⟩
  exact Ctypes.union_field_offset_stable cunit.prog_comp_env prog.prog_comp_env
    hlink.2 f co.co_members hconsistent.co_consistent_complete

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

theorem field_offset_stable : field_offset_stableStatement := by
  intro cunit prog id co f hlink hget
  have hconsistent := Ctypes.build_composite_env_consistent
    cunit.prog_types cunit.prog_comp_env cunit.prog_comp_env_eq id co hget
  refine ⟨hlink.2 id co hget, ?_⟩
  exact Ctypes.field_offset_stable cunit.prog_comp_env prog.prog_comp_env
    hlink.2 f co.co_members hconsistent.co_consistent_complete

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

theorem make_ptrofsconst_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_ptrofsconst_correctStatement := by
  intro ge n e le m
  change T_eval_expr ge e le m
    (Cshmgen.make_longconst (CompCert4Lean.Lib.Integers.Int64.repr n))
    (.Vlong (CompCert4Lean.Lib.Integers.Int64.repr
      (CompCert4Lean.Lib.Integers.Int64.unsigned
        (CompCert4Lean.Lib.Integers.Int64.repr n))))
  rw [int64_repr_unsigned_local]
  exact make_longconst_correct ge (CompCert4Lean.Lib.Integers.Int64.repr n) e le m

end CompCert4Lean.Cfrontend.Cshmgenproof

namespace CompCert4Lean.Cfrontend.Cshmgenproof

open CompCert4Lean.Cfrontend.Cshmgen
open CompCert4Lean.Cfrontend.Csharpminor
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers

theorem make_boolean_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_boolean_correctStatement := by
  intro ge e le m a v ty b hval hbool
  unfold make_boolean
  cases hclass : classify_bool ty with
  | bool_case_i =>
      cases v with
      | Vint n =>
          have hb : b = !(Int.eq n Int.zero) := by
            simpa [bool_val, hclass] using hbool.symm
          refine ⟨_, make_cmpu_ne_zero_correct ge e le m a n hval, ?_⟩
          rw [hb]
          cases heq : Int.eq n Int.zero <;> simp [heq] <;>
            exact CompCert4Lean.Common.Values.Val.bool_of_val_int _
      | Vptr block ofs =>
          simp [bool_val, hclass, CompCert4Lean.X86_64.Archi.ptr64] at hbool
      | Vlong n | Vfloat n | Vsingle n | Vundef =>
          simp [bool_val, hclass, CompCert4Lean.X86_64.Archi.ptr64] at hbool
  | bool_case_l =>
      cases v with
      | Vlong n =>
          have hb : b = !(Int64.eq n Int64.zero) := by
            simpa [bool_val, hclass] using hbool.symm
          refine ⟨.Vint (if Int64.eq n Int64.zero then Int.zero else Int.one), ?_, ?_⟩
          · apply Csharpminor.eval_Ebinop
            · exact hval
            · exact make_longconst_correct ge Int64.zero e le m
            · change Option.map Val.of_bool
                (Val.cmplu_bool (CompCert4Lean.Common.Memory.Mem.valid_pointer m) .Cne
                  (.Vlong n) (.Vlong Int64.zero)) = some _
              cases hEq : decide (n.intval = Int64.zero.intval) <;>
                simp [Val.cmplu_bool, Val.of_bool, Int64.cmpu,
                  Int64.eq, WordCore.cmpu, WordCore.eq,
                  Vtrue, Vfalse, hEq]
          · rw [hb]
            cases heq : Int64.eq n Int64.zero <;> simp [heq] <;>
              exact CompCert4Lean.Common.Values.Val.bool_of_val_int _
      | Vptr block ofs =>
          have hh : CompCert4Lean.Common.Memory.Mem.weak_valid_pointer m block
              (Ptrofs.unsigned ofs) = true ∧ b = true := by
            simpa [bool_val, hclass, CompCert4Lean.X86_64.Archi.ptr64] using hbool
          have hv : CompCert4Lean.Common.Memory.Mem.weak_valid_pointer m block
              (Ptrofs.unsigned ofs) = true := by
            exact hh.1
          refine ⟨CompCert4Lean.Common.Values.Vone, ?_, ?_⟩
          · apply Csharpminor.eval_Ebinop
            · exact hval
            · exact make_longconst_correct ge Int64.zero e le m
            · change Option.map Val.of_bool
                (Val.cmplu_bool (CompCert4Lean.Common.Memory.Mem.valid_pointer m) .Cne
                  (.Vptr block ofs) (.Vlong Int64.zero)) = some CompCert4Lean.Common.Values.Vone
              simp [CompCert4Lean.Common.Memory.Mem.weak_valid_pointer] at hv ⊢
              simp [Val.cmplu_bool, Val.of_bool, CompCert4Lean.X86_64.Archi.ptr64,
                hv, Val.cmp_different_blocks, Int64.eq, WordCore.eq,
                Vtrue, Vfalse, CompCert4Lean.Common.Values.Vone]
          · rw [hh.2]
            exact .bool_of_val_int _
      | Vint n | Vfloat n | Vsingle n | Vundef =>
          simp [bool_val, hclass, CompCert4Lean.X86_64.Archi.ptr64] at hbool
  | bool_case_f =>
      cases v with
      | Vfloat f =>
          have hb : b = !(CompCert4Lean.Lib.Floats.Float.cmp .Ceq f
              CompCert4Lean.Lib.Floats.Float.zero) := by
            simpa [bool_val, hclass] using hbool.symm
          refine ⟨.Vint (if CompCert4Lean.Lib.Floats.Float.cmp .Ceq f
              CompCert4Lean.Lib.Floats.Float.zero then Int.zero else Int.one), ?_, ?_⟩
          · apply Csharpminor.eval_Ebinop
            · exact hval
            · exact make_floatconst_correct ge CompCert4Lean.Lib.Floats.Float.zero e le m
            · change some (Val.cmpf .Cne (.Vfloat f)
                (.Vfloat CompCert4Lean.Lib.Floats.Float.zero)) = some _
              cases hcmp : CompCert4Lean.Lib.Floats.Float.compare f
                  CompCert4Lean.Lib.Floats.Float.zero with
              | none =>
                  simp [Val.cmpf, Val.cmpf_bool, Val.of_optbool,
                    Vtrue, Vfalse, CompCert4Lean.Lib.Floats.Float.cmp,
                    CompCert4Lean.Lib.Floats.cmp_of_comparison, hcmp]
              | some c =>
                  cases c <;>
                    simp [Val.cmpf, Val.cmpf_bool, Val.of_optbool,
                      Vtrue, Vfalse, CompCert4Lean.Lib.Floats.Float.cmp,
                      CompCert4Lean.Lib.Floats.cmp_of_comparison, hcmp]
          · rw [hb]
            cases hEq : CompCert4Lean.Lib.Floats.Float.cmp .Ceq f
                CompCert4Lean.Lib.Floats.Float.zero <;>
              simp [hEq] <;> exact .bool_of_val_int _
      | Vint n | Vlong n | Vsingle n | Vptr n _ | Vundef =>
          simp [bool_val, hclass] at hbool
  | bool_case_s =>
      cases v with
      | Vsingle f =>
          have hb : b = !(CompCert4Lean.Lib.Floats.Float32.cmp .Ceq f
              CompCert4Lean.Lib.Floats.Float32.zero) := by
            simpa [bool_val, hclass] using hbool.symm
          refine ⟨.Vint (if CompCert4Lean.Lib.Floats.Float32.cmp .Ceq f
              CompCert4Lean.Lib.Floats.Float32.zero then Int.zero else Int.one), ?_, ?_⟩
          · apply Csharpminor.eval_Ebinop
            · exact hval
            · exact make_singleconst_correct ge CompCert4Lean.Lib.Floats.Float32.zero e le m
            · change some (Val.cmpfs .Cne (.Vsingle f)
                (.Vsingle CompCert4Lean.Lib.Floats.Float32.zero)) = some _
              cases hcmp : CompCert4Lean.Lib.Floats.Float32.compare f
                  CompCert4Lean.Lib.Floats.Float32.zero with
              | none =>
                  simp [Val.cmpfs, Val.cmpfs_bool, Val.of_optbool,
                    Vtrue, Vfalse, CompCert4Lean.Lib.Floats.Float32.cmp,
                    CompCert4Lean.Lib.Floats.cmp_of_comparison, hcmp]
              | some c =>
                  cases c <;>
                    simp [Val.cmpfs, Val.cmpfs_bool, Val.of_optbool,
                      Vtrue, Vfalse, CompCert4Lean.Lib.Floats.Float32.cmp,
                      CompCert4Lean.Lib.Floats.cmp_of_comparison, hcmp]
          · rw [hb]
            cases hEq : CompCert4Lean.Lib.Floats.Float32.cmp .Ceq f
                CompCert4Lean.Lib.Floats.Float32.zero <;>
              simp [hEq] <;> exact .bool_of_val_int _
      | Vint n | Vlong n | Vfloat n | Vptr n _ | Vundef =>
          simp [bool_val, hclass] at hbool
  | bool_default =>
      simp [bool_val, hclass] at hbool

end CompCert4Lean.Cfrontend.Cshmgenproof
