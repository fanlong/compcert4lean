import CompCert4Lean.Backend.SplitLong
import CompCert4Lean.Common.Builtins
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Memory
import CompCert4Lean.X86.SelectOpproof

/-!
# Correctness surface for 64-bit integer splitting

The source file is proof-heavy.  This migration pass provides the four
computational/relational definitions and records the remaining theorem
statements as transparent proposition descriptors for the later proof phase.
-/

namespace CompCert4Lean.Backend.SplitLongproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.SplitLong
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.SelectOp

private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev CCInt64 := CompCert4Lean.Lib.Integers.int64
private abbrev CCComparison := CompCert4Lean.Lib.Integers.comparison
private abbrev env := CompCert4Lean.Backend.Cminor.env
private abbrev zLe := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
private abbrev zLt := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt
private abbrev zZero : Z := .Z0
private abbrev intEq := CompCert4Lean.Lib.Integers.Int.eq
private abbrev intLt := CompCert4Lean.Lib.Integers.Int.lt
private abbrev intLtu := CompCert4Lean.Lib.Integers.Int.ltu
private abbrev intSub := CompCert4Lean.Lib.Integers.Int.sub
private abbrev intUnsigned := CompCert4Lean.Lib.Integers.Int.unsigned
private abbrev intZero := CompCert4Lean.Lib.Integers.Int.zero
private abbrev intIwordsize := CompCert4Lean.Lib.Integers.Int.iwordsize
private abbrev intZwordsize := CompCert4Lean.Lib.Integers.Int.zwordsize
private abbrev intOr := CompCert4Lean.Lib.Integers.Int.or
private abbrev int64Eq := CompCert4Lean.Lib.Integers.Int64.eq
private abbrev int64Ofwords := CompCert4Lean.Lib.Integers.Int64.ofwords
private abbrev int64Hiword := CompCert4Lean.Lib.Integers.Int64.hiword
private abbrev int64Loword := CompCert4Lean.Lib.Integers.Int64.loword
private abbrev int64Zero := CompCert4Lean.Lib.Integers.Int64.zero
private abbrev int64Iwordsize := CompCert4Lean.Lib.Integers.Int64.iwordsize'
private abbrev int64Zwordsize := CompCert4Lean.Lib.Integers.Int64.zwordsize
private abbrev int64Xor := CompCert4Lean.Lib.Integers.Int64.xor
private abbrev int64Lt := CompCert4Lean.Lib.Integers.Int64.lt
private abbrev zOfNat :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string

private def ofString (s : String) : RocqString :=
  (String.toUTF8 s).toList.foldr
    (fun b tail =>
      CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.String b tail)
    CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.EmptyString

def helper_declared {F V : Type}
    (p : CompCert4Lean.Common.AST.program
      (CompCert4Lean.Common.AST.fundef F) V)
    (id : ident) (name : RocqString)
    (sg : signature) : Prop :=
  PTree.get id (prog_defmap p) =
    some (Gfun (.External (.EF_runtime name sg)))

def helper_functions_declared {F V : Type}
    (p : CompCert4Lean.Common.AST.program
      (CompCert4Lean.Common.AST.fundef F) V)
    (hf : helper_functions) : Prop :=
  helper_declared p i64_dtos (ofString "__compcert_i64_dtos") sig_f_l ∧
  helper_declared p i64_dtou (ofString "__compcert_i64_dtou") sig_f_l ∧
  helper_declared p i64_stod (ofString "__compcert_i64_stod") sig_l_f ∧
  helper_declared p i64_utod (ofString "__compcert_i64_utod") sig_l_f ∧
  helper_declared p i64_stof (ofString "__compcert_i64_stof") sig_l_s ∧
  helper_declared p i64_utof (ofString "__compcert_i64_utof") sig_l_s ∧
  helper_declared p i64_sdiv (ofString "__compcert_i64_sdiv") sig_ll_l ∧
  helper_declared p i64_udiv (ofString "__compcert_i64_udiv") sig_ll_l ∧
  helper_declared p i64_smod (ofString "__compcert_i64_smod") sig_ll_l ∧
  helper_declared p i64_umod (ofString "__compcert_i64_umod") sig_ll_l ∧
  helper_declared p i64_shl (ofString "__compcert_i64_shl") sig_li_l ∧
  helper_declared p i64_shr (ofString "__compcert_i64_shr") sig_li_l ∧
  helper_declared p i64_sar (ofString "__compcert_i64_sar") sig_li_l ∧
  helper_declared p i64_umulh (ofString "__compcert_i64_umulh") sig_ll_l ∧
  helper_declared p i64_smulh (ofString "__compcert_i64_smulh") sig_ll_l

def unary_constructor_sound (xi : ExternalCalls) (prog : program) (sp : val)
    (e : env) (m : mem) (cstr : expr → expr) (sem : val → val) : Prop :=
  ∀ (le : letenv) (a : expr) (x : val),
    eval_expr (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) sp e m le a x →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (cstr a) v ∧ Val.lessdef (sem x) v

def binary_constructor_sound (xi : ExternalCalls) (prog : program) (sp : val)
    (e : env) (m : mem) (cstr : expr → expr → expr)
    (sem : val → val → val) : Prop :=
  ∀ (le : letenv) (a : expr) (x : val) (b : expr) (y : val),
    eval_expr (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) sp e m le a x →
    eval_expr (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      xi (Genv.globalenv prog) sp e m le b y →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi (Genv.globalenv prog) sp e m le (cstr a b) v ∧ Val.lessdef (sem x y) v

/-! ## Exact statement descriptors for later proof migration -/

def eval_helperStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    ∀ (sp : val) (e : env) (m : mem),
      ∀ (bf : builtin_function) (le : letenv) (id : ident)
        (name : RocqString)
        (sg : signature) (args : exprlist) (vargs : List val) (vres : val),
        eval_exprlist (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          xi (Genv.globalenv prog) sp e m le args vargs →
        helper_declared prog id name sg →
        lookup_builtin_function name sg = some bf →
        builtin_function_sem (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) bf vargs = some vres →
        eval_expr (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          xi (Genv.globalenv prog) sp e m le
          (Eexternal id sg args) vres

def eval_helper_1Statement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (bf : builtin_function) (le : letenv) (id : ident) (name : RocqString)
      (sg : signature) (arg1 : expr) (varg1 : val) (vres : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le arg1 varg1 →
      helper_declared prog id name sg →
      lookup_builtin_function name sg = some bf →
      builtin_function_sem (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) bf [varg1] = some vres →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le
        (Eexternal id sg (Econs arg1 Enil)) vres

def eval_helper_2Statement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (bf : builtin_function) (le : letenv) (id : ident) (name : RocqString)
      (sg : signature) (arg1 arg2 : expr) (varg1 varg2 : val) (vres : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le arg1 varg1 →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le arg2 varg2 →
      helper_declared prog id name sg →
      lookup_builtin_function name sg = some bf →
      builtin_function_sem (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) bf [varg1, varg2] = some vres →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le
        (Eexternal id sg (Econs arg1 (Econs arg2 Enil))) vres

def eval_builtin_1Statement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (bf : builtin_function) (le : letenv) (id : RocqString) (sg : signature)
      (arg1 : expr) (varg1 vres : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le arg1 varg1 →
      lookup_builtin_function id sg = some bf →
      builtin_function_sem (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) bf [varg1] = some vres →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le
        (Ebuiltin (EF_builtin id sg) (Econs arg1 Enil)) vres

def eval_builtin_2Statement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (bf : builtin_function) (le : letenv) (id : RocqString) (sg : signature)
      (arg1 arg2 : expr) (varg1 varg2 vres : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le arg1 varg1 →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le arg2 varg2 →
      lookup_builtin_function id sg = some bf →
      builtin_function_sem (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) bf [varg1, varg2] = some vres →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le
        (Ebuiltin (EF_builtin id sg) (Econs arg1 (Econs arg2 Enil))) vres

def eval_splitlongStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a : expr) (f : expr → expr → expr) (v : val)
      (sem : val → val),
      (∀ (le : letenv) (a b : expr) (x y : val),
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le b y →
        ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (f a b) v ∧
          ∀ (p q : CCInt), x = .Vint p → y = .Vint q →
            v = sem (.Vlong (int64Ofwords p q))) →
      (match v with | .Vlong _ => True | _ => sem v = .Vundef) →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a v →
      ∃ v', eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (splitlong a f) v' ∧
        Val.lessdef (sem v) v'

def eval_splitlong_strictStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a : expr) (f : expr → expr → expr)
      (va : CCInt64) (v : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a (.Vlong va) →
      (∀ (le : letenv) (a1 a2 : expr),
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a1
          (.Vint (int64Hiword va)) →
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a2
          (.Vint (int64Loword va)) →
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (f a1 a2) v) →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (splitlong a f) v

def eval_splitlong2Statement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a b : expr) (f : expr → expr → expr → expr → expr)
      (va vb : val) (sem : val → val → val),
      (∀ (le : letenv) (a1 a2 b1 b2 : expr)
          (x1 x2 y1 y2 : val),
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a1 x1 →
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a2 x2 →
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le b1 y1 →
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le b2 y2 →
        ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (f a1 a2 b1 b2) v ∧
          ∀ (p1 p2 q1 q2 : CCInt),
            x1 = .Vint p1 → x2 = .Vint p2 →
            y1 = .Vint q1 → y2 = .Vint q2 →
            v = sem (.Vlong (int64Ofwords p1 p2))
              (.Vlong (int64Ofwords q1 q2))) →
      (match va, vb with
        | .Vlong _, .Vlong _ => True
        | _, _ => sem va vb = .Vundef) →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a va →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le b vb →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (splitlong2 a b f) v ∧
        Val.lessdef (sem va vb) v

def eval_splitlong2_strictStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a b : expr) (f : expr → expr → expr → expr → expr)
      (va vb : CCInt64) (v : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a (.Vlong va) →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le b (.Vlong vb) →
      (∀ (le : letenv) (a1 a2 b1 b2 : expr),
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a1
          (.Vint (int64Hiword va)) →
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a2
          (.Vint (int64Loword va)) →
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le b1
          (.Vint (int64Hiword vb)) →
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le b2
          (.Vint (int64Loword vb)) →
        eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (f a1 a2 b1 b2) v) →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (splitlong2 a b f) v

def is_longconst_soundStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a : expr) (x : val) (n : CCInt64),
      is_longconst a = some n →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      x = .Vlong n

def is_longconst_zero_soundStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a : expr) (x : val),
      is_longconst_zero a = true →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      x = .Vlong int64Zero

def eval_lowlongStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m lowlong Val.loword

def eval_highlongStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m highlong Val.hiword

def eval_longconstStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (n : CCInt64),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (longconst n) (.Vlong n)

def eval_intoflongStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m intoflong Val.loword

def eval_longofintuStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m longofintu Val.longofintu

def eval_longofintStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m longofint Val.longofint

def eval_neglStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m negl Val.negl

def eval_notlStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m notl Val.notl

def eval_longoffloatStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a : expr) (x y : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      Val.longoffloat x = some y →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (longoffloat a) v ∧
        Val.lessdef y v

def eval_longuoffloatStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a : expr) (x y : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      Val.longuoffloat x = some y →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (longuoffloat a) v ∧
        Val.lessdef y v

def eval_floatoflongStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a : expr) (x y : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      Val.floatoflong x = some y →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (floatoflong a) v ∧
        Val.lessdef y v

def eval_floatoflonguStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a : expr) (x y : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      Val.floatoflongu x = some y →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (floatoflongu a) v ∧
        Val.lessdef y v

def eval_longofsingleStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a : expr) (x y : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      Val.longofsingle x = some y →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (longofsingle a) v ∧
        Val.lessdef y v

def eval_longuofsingleStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a : expr) (x y : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      Val.longuofsingle x = some y →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (longuofsingle a) v ∧
        Val.lessdef y v

def eval_singleoflongStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a : expr) (x y : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      Val.singleoflong x = some y →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (singleoflong a) v ∧
        Val.lessdef y v

def eval_singleoflonguStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a : expr) (x y : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      Val.singleoflongu x = some y →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (singleoflongu a) v ∧
        Val.lessdef y v

def eval_andlStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m andl Val.andl

def eval_orlStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m orl Val.orl

def eval_xorlStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m xorl Val.xorl

def is_intconst_soundStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a : expr) (x : val) (n : CCInt),
      is_intconst a = some n →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      x = .Vint n

def eval_shift_immStatement : Prop :=
  ∀ (P : expr → Prop) (n : CCInt) (a0 a1 a2 a3 : expr),
    (n = intZero → P a0) →
    (zLe zZero (intUnsigned n) ∧ zLt (intUnsigned n) intZwordsize →
      intLtu n intIwordsize = true →
      intLtu (intSub intIwordsize n) intIwordsize = true →
      intLtu n int64Iwordsize = true → P a1) →
    (zLe intZwordsize (intUnsigned n) ∧ zLt (intUnsigned n) int64Zwordsize →
      intLtu (intSub n intIwordsize) intIwordsize = true → P a2) →
    P a3 →
    P (if intEq n intZero then a0 else
      if intLtu n intIwordsize then a1 else
      if intLtu n int64Iwordsize then a2 else a3)

def eval_shllimmStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem)
    (n : CCInt),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m
      (fun e => shllimm e n) (fun v => Val.shll v (.Vint n))

def eval_shllStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m shll Val.shll

def eval_shrluimmStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem)
    (n : CCInt),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m
      (fun e => shrluimm e n) (fun v => Val.shrlu v (.Vint n))

def eval_shrluStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m shrlu Val.shrlu

def eval_shrlimmStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem)
    (n : CCInt),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m
      (fun e => shrlimm e n) (fun v => Val.shrl v (.Vint n))

def eval_shrlStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m shrl Val.shrl

def eval_addlStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    CompCert4Lean.X86_64.Archi.ptr64 = false →
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m addl Val.addl

def eval_sublStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    CompCert4Lean.X86_64.Archi.ptr64 = false →
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m subl Val.subl

def eval_mull_baseStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m mull_base Val.mull

def eval_mullimmStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem)
    (n : CCInt64),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m
      (mullimm n) (fun v => Val.mull v (.Vlong n))

def eval_mullStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m mull Val.mull

def eval_mullhuStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem)
    (n : CCInt64),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m
      (fun a => mullhu a n) (fun v => Val.mullhu v (.Vlong n))

def eval_mullhsStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem)
    (n : CCInt64),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m
      (fun a => mullhs a n) (fun v => Val.mullhs v (.Vlong n))

def eval_shrxlimmStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a : expr) (n : CCInt) (x z : val),
      CompCert4Lean.X86_64.Archi.ptr64 = false →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      Val.shrxl x (.Vint n) = some z →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (shrxlimm a n) v ∧
        Val.lessdef z v

def eval_divlu_baseStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a b : expr) (x y z : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le b y →
      Val.divlu x y = some z →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (divlu_base a b) v ∧
        Val.lessdef z v

def eval_modlu_baseStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a b : expr) (x y z : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le b y →
      Val.modlu x y = some z →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (modlu_base a b) v ∧
        Val.lessdef z v

def eval_divls_baseStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a b : expr) (x y z : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le b y →
      Val.divls x y = some z →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (divls_base a b) v ∧
        Val.lessdef z v

def eval_modls_baseStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : helper_functions),
    helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a b : expr) (x y z : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le b y →
      Val.modls x y = some z →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (modls_base a b) v ∧
        Val.lessdef z v

def decompose_cmpl_eq_zeroStatement : Prop :=
  ∀ (h l : CCInt),
    int64Eq (int64Ofwords h l) int64Zero = intEq (intOr h l) intZero

def eval_cmpl_eq_zeroStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a : expr) (x : CCInt64),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a (.Vlong x) →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (cmpl_eq_zero a)
        (Val.of_bool (int64Eq x int64Zero))

def eval_cmpl_ne_zeroStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (le : letenv) (a : expr) (x : CCInt64),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a (.Vlong x) →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (cmpl_ne_zero a)
        (Val.of_bool (!(int64Eq x int64Zero)))

def eval_cmplu_genStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (ch cl : CCComparison) (a b : expr) (le : letenv)
      (x y : CCInt64),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a (.Vlong x) →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le b (.Vlong y) →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (cmplu_gen ch cl a b)
        (Val.of_bool (if intEq (int64Hiword x) (int64Hiword y) then
          Int.cmpu cl (int64Loword x) (int64Loword y) else
          Int.cmpu ch (int64Hiword x) (int64Hiword y)))

def int64_eq_xorStatement : Prop :=
  ∀ (p q : CCInt64),
    int64Eq p q = int64Eq (int64Xor p q) int64Zero

def eval_cmpluStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (c : CCComparison) (le : letenv) (a : expr) (x : val) (b : expr)
      (y : val) (v : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le b y →
      Val.cmplu (Mem.valid_pointer m) c x y = some v →
      CompCert4Lean.X86_64.Archi.ptr64 = false →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (cmplu c a b) v

def eval_cmpl_genStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (ch cl : CCComparison) (a b : expr) (le : letenv)
      (x y : CCInt64),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a (.Vlong x) →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le b (.Vlong y) →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (cmpl_gen ch cl a b)
        (Val.of_bool (if intEq (int64Hiword x) (int64Hiword y) then
          Int.cmpu cl (int64Loword x) (int64Loword y) else
          Int.cmp ch (int64Hiword x) (int64Hiword y)))

def decompose_cmpl_lt_zeroStatement : Prop :=
  ∀ (h l : CCInt),
    int64Lt (int64Ofwords h l) int64Zero = intLt h intZero

def eval_cmplStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    ∀ (c : CCComparison) (le : letenv) (a : expr) (x : val) (b : expr)
      (y : val) (v : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le b y →
      Val.cmpl c x y = some v →
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (cmpl c a b) v

end CompCert4Lean.Backend.SplitLongproof

namespace CompCert4Lean.Backend.SplitLongproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

theorem eval_builtin_1 : eval_builtin_1Statement := by
  intro xi prog sp e m bf le id sg arg1 varg1 vres harg hlookup hsem
  refine CompCert4Lean.Backend.CminorSel.eval_expr.builtin (le := le)
    (ef := .EF_builtin id sg)
    (al := CompCert4Lean.Backend.CminorSel.exprlist.Econs arg1
      CompCert4Lean.Backend.CminorSel.exprlist.Enil) (vl := [varg1])
    (v := vres) ?_ ?_
  · exact CompCert4Lean.Backend.CminorSel.eval_exprlist.cons le arg1
      CompCert4Lean.Backend.CminorSel.exprlist.Enil varg1 [] harg
      (CompCert4Lean.Backend.CminorSel.eval_exprlist.nil le)
  · simpa [CompCert4Lean.Common.Events.external_call,
      CompCert4Lean.Common.Events.builtin_or_external_sem, hlookup] using
      (CompCert4Lean.Common.Events.known_builtin_sem_intro [varg1] vres m hsem)

private theorem splitlong_ptreeGetSet0Same {A : Type} (i : positive) (x : A) :
    PTree.get' i (PTree.set0 i x) = some x := by
  induction i <;> simp [PTree.get', PTree.set0, *]

private theorem splitlong_ptreeGetSet'Same {A : Type} (i : positive) (x : A)
    (m : PTree.tree' A) : PTree.get' i (PTree.set' i x m) = some x := by
  induction i generalizing m <;> cases m <;>
    simp [PTree.get', PTree.set', splitlong_ptreeGetSet0Same, *]

private theorem splitlong_ptreeGetSetSame {A : Type} (i : positive) (x : A) (m : PTree.t A) :
    PTree.get i (PTree.set i x m) = some x := by
  cases m <;> simp [PTree.get, PTree.set, splitlong_ptreeGetSet0Same,
    splitlong_ptreeGetSet'Same]

private theorem splitlong_ptreeGetSet0Other {A : Type} (i j : positive) (x : A) (h : i ≠ j) :
    PTree.get' i (PTree.set0 j x) = none := by
  induction j generalizing i with
  | xH => cases i <;> simp_all [PTree.get', PTree.set0]
  | xI j ih => cases i <;> simp_all [PTree.get', PTree.set0]
  | xO j ih => cases i <;> simp_all [PTree.get', PTree.set0]

private theorem splitlong_ptreeGetSet'Other {A : Type} (i j : positive) (x : A)
    (m : PTree.tree' A) (h : i ≠ j) :
    PTree.get' i (PTree.set' j x m) = PTree.get' i m := by
  induction j generalizing i m with
  | xH => cases i <;> cases m <;> simp_all [PTree.get', PTree.set']
  | xI j ih => cases i <;> cases m <;>
      simp_all [PTree.get', PTree.set', splitlong_ptreeGetSet0Other]
  | xO j ih => cases i <;> cases m <;>
      simp_all [PTree.get', PTree.set', splitlong_ptreeGetSet0Other]

private theorem splitlong_ptreeGetSetOther {A : Type} (i j : positive) (x : A)
    (m : PTree.t A) (h : i ≠ j) :
    PTree.get i (PTree.set j x m) = PTree.get i m := by
  cases m <;> simp [PTree.get, PTree.set, splitlong_ptreeGetSet0Other,
    splitlong_ptreeGetSet'Other, h]

private def splitlong_maps_rel {F V : Type}
    (ge : Genv.t F V) (dm : PTree.t (globdef F V)) : Prop :=
  ∀ id g, PTree.get id dm = some g →
    ∃ b, Genv.find_symbol ge id = some b ∧ Genv.find_def ge b = some g

private theorem splitlong_add_global_rel {F V : Type}
    (ge : Genv.t F V) (dm : PTree.t (globdef F V))
    (idg : ident × globdef F V)
    (hrel : splitlong_maps_rel ge dm) :
    splitlong_maps_rel (Genv.add_global ge idg)
      (PTree.set idg.1 idg.2 dm) := by
  intro id g hget
  by_cases hid : id = idg.1
  · subst id
    have hnew : g = idg.2 := by
      have := splitlong_ptreeGetSetSame (idg.1 : positive) idg.2 dm
      exact Option.some.inj (hget.symm.trans this)
    subst g
    refine ⟨ge.genv_next, ?_, ?_⟩
    · change PTree.get idg.1 (PTree.set idg.1 ge.genv_next ge.genv_symb) =
        some ge.genv_next
      exact splitlong_ptreeGetSetSame idg.1 ge.genv_next ge.genv_symb
    · change PTree.get ge.genv_next
        (PTree.set ge.genv_next idg.2 ge.genv_defs) = some idg.2
      exact splitlong_ptreeGetSetSame ge.genv_next idg.2 ge.genv_defs
  · have hget' : PTree.get id dm = some g := by
      exact (splitlong_ptreeGetSetOther (id : positive) (idg.1 : positive)
        idg.2 dm hid).symm.trans hget
    obtain ⟨b, hsym, hdef⟩ := hrel id g hget'
    have hbnext : b ≠ ge.genv_next :=
      CompCert4Lean.Lib.Coqlib.Plt_ne _ _ (ge.genv_defs_range b hdef)
    refine ⟨b, ?_, ?_⟩
    · change PTree.get id (PTree.set idg.1 ge.genv_next ge.genv_symb) = some b
      rw [splitlong_ptreeGetSetOther id idg.1 ge.genv_next ge.genv_symb hid]
      exact hsym
    · change PTree.get b (PTree.set ge.genv_next idg.2 ge.genv_defs) = some g
      rw [splitlong_ptreeGetSetOther b ge.genv_next idg.2 ge.genv_defs hbnext]
      exact hdef

private theorem splitlong_empty_maps_rel {F V : Type} (pub : List ident) :
    splitlong_maps_rel (Genv.empty_genv F V pub) (PTree.empty (globdef F V)) := by
  intro id g h
  change (none : Option (globdef F V)) = some g at h
  cases h

private theorem splitlong_fold_rel {F V : Type} :
    ∀ (gl : List (ident × globdef F V)) (ge : Genv.t F V)
      (dm : PTree.t (globdef F V)),
      splitlong_maps_rel ge dm →
      splitlong_maps_rel (Genv.add_globals ge gl)
        (gl.foldl (fun m idg => PTree.set idg.1 idg.2 m) dm) := by
  intro gl
  induction gl with
  | nil =>
      intro ge dm hrel
      simpa [Genv.add_globals, List.foldl] using hrel
  | cons idg gl ih =>
      intro ge dm hrel
      apply ih (Genv.add_global ge idg)
        (PTree.set idg.1 idg.2 dm)
        (splitlong_add_global_rel ge dm idg hrel)

private theorem splitlong_find_def_symbol {F V : Type}
    (p : program F V) (id : ident) (g : globdef F V)
    (h : PTree.get id (prog_defmap p) = some g) :
    ∃ b, Genv.find_symbol (Genv.globalenv p) id = some b ∧
      Genv.find_def (Genv.globalenv p) b = some g := by
  have hrel := splitlong_fold_rel p.prog_defs
    (Genv.empty_genv F V p.prog_public)
    (PTree.empty (globdef F V))
    (splitlong_empty_maps_rel p.prog_public)
  exact hrel id g h

theorem eval_helper : eval_helperStatement := by
  intro xi prog sp e m bf le id name sg args vargs vres hargs hdecl hlookup hsem
  obtain ⟨b, hsym, hdef⟩ := splitlong_find_def_symbol prog id
    (.Gfun (.External (.EF_runtime name sg))) hdecl
  refine CompCert4Lean.Backend.CminorSel.eval_expr.external (le := le)
    (id := id) (sg := sg) (al := args) (b := b)
    (ef := .EF_runtime name sg) (vl := vargs) (v := vres)
    hsym ?_ rfl hargs ?_
  · simp [Genv.find_funct_ptr, hdef]
  · simpa [CompCert4Lean.Common.Events.external_call,
      CompCert4Lean.Common.Events.builtin_or_external_sem, hlookup] using
      (CompCert4Lean.Common.Events.known_builtin_sem_intro vargs vres m hsem)

theorem eval_helper_1 : eval_helper_1Statement := by
  intro xi prog sp e m bf le id name sg arg1 varg1 vres harg hdecl hlookup hsem
  exact eval_helper xi prog sp e m bf le id name sg
    (CompCert4Lean.Backend.CminorSel.exprlist.Econs arg1
      CompCert4Lean.Backend.CminorSel.exprlist.Enil)
    [varg1] vres
    (CompCert4Lean.Backend.CminorSel.eval_exprlist.cons le arg1
      CompCert4Lean.Backend.CminorSel.exprlist.Enil varg1 [] harg
      (CompCert4Lean.Backend.CminorSel.eval_exprlist.nil le))
    hdecl hlookup hsem

theorem eval_helper_2 : eval_helper_2Statement := by
  intro xi prog sp e m bf le id name sg arg1 arg2 varg1 varg2 vres
    harg1 harg2 hdecl hlookup hsem
  exact eval_helper xi prog sp e m bf le id name sg
    (CompCert4Lean.Backend.CminorSel.exprlist.Econs arg1
      (CompCert4Lean.Backend.CminorSel.exprlist.Econs arg2
        CompCert4Lean.Backend.CminorSel.exprlist.Enil))
    [varg1, varg2] vres
    (CompCert4Lean.Backend.CminorSel.eval_exprlist.cons le arg1
      (CompCert4Lean.Backend.CminorSel.exprlist.Econs arg2
        CompCert4Lean.Backend.CminorSel.exprlist.Enil) varg1 [varg2] harg1
      (CompCert4Lean.Backend.CminorSel.eval_exprlist.cons le arg2
        CompCert4Lean.Backend.CminorSel.exprlist.Enil varg2 [] harg2
        (CompCert4Lean.Backend.CminorSel.eval_exprlist.nil le)))
    hdecl hlookup hsem

end CompCert4Lean.Backend.SplitLongproof

namespace CompCert4Lean.Backend.SplitLongproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

theorem eval_builtin_2 : eval_builtin_2Statement := by
  intro xi prog sp e m bf le id sg arg1 arg2 varg1 varg2 vres
    harg1 harg2 hlookup hsem
  refine CompCert4Lean.Backend.CminorSel.eval_expr.builtin (le := le)
    (ef := .EF_builtin id sg)
    (al := CompCert4Lean.Backend.CminorSel.exprlist.Econs arg1
      (CompCert4Lean.Backend.CminorSel.exprlist.Econs arg2
        CompCert4Lean.Backend.CminorSel.exprlist.Enil))
    (vl := [varg1, varg2]) (v := vres) ?_ ?_
  · exact CompCert4Lean.Backend.CminorSel.eval_exprlist.cons le arg1
      (CompCert4Lean.Backend.CminorSel.exprlist.Econs arg2
        CompCert4Lean.Backend.CminorSel.exprlist.Enil) varg1 [varg2] harg1
      (CompCert4Lean.Backend.CminorSel.eval_exprlist.cons le arg2
        CompCert4Lean.Backend.CminorSel.exprlist.Enil varg2 [] harg2
        (CompCert4Lean.Backend.CminorSel.eval_exprlist.nil le))
  · simpa [CompCert4Lean.Common.Events.external_call,
      CompCert4Lean.Common.Events.builtin_or_external_sem, hlookup] using
      (CompCert4Lean.Common.Events.known_builtin_sem_intro [varg1, varg2] vres m hsem)

end CompCert4Lean.Backend.SplitLongproof

namespace CompCert4Lean.Backend.SplitLongproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.SplitLong
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op

set_option maxHeartbeats 1000000

variable
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 53)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 24)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 128)]

private theorem splitlong_eval_eop_inv
    (xi : ExternalCalls)
    (ge : CompCert4Lean.Backend.CminorSel.genv)
    (sp : CompCert4Lean.Common.Values.val)
    (e : CompCert4Lean.Backend.Cminor.env)
    (m : CompCert4Lean.Common.Memory.mem)
    (le : CompCert4Lean.Backend.CminorSel.letenv)
    (op : CompCert4Lean.X86.Op.operation)
    (al : CompCert4Lean.Backend.CminorSel.exprlist)
    (x : CompCert4Lean.Common.Values.val)
    (h : eval_expr (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge sp e m le (.Eop op al) x) :
    ∃ vl, eval_exprlist (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge sp e m le al vl ∧
      CompCert4Lean.X86.Op.eval_operation (F := CompCert4Lean.Backend.CminorSel.fundef)
        (V := Unit) ge sp op vl m = some x := by
  cases h with
  | eval_Eop _ _ _ vl _ hargs hop => exact ⟨vl, hargs, hop⟩

private theorem splitlong_eval_cons_inv
    (xi : ExternalCalls)
    (ge : CompCert4Lean.Backend.CminorSel.genv)
    (sp : CompCert4Lean.Common.Values.val)
    (e : CompCert4Lean.Backend.Cminor.env)
    (m : CompCert4Lean.Common.Memory.mem)
    (le : CompCert4Lean.Backend.CminorSel.letenv)
    (a : CompCert4Lean.Backend.CminorSel.expr)
    (al : CompCert4Lean.Backend.CminorSel.exprlist)
    (vl : List CompCert4Lean.Common.Values.val)
    (h : eval_exprlist (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge sp e m le
      (.Econs a al) vl) :
    ∃ v vl', vl = v :: vl' ∧
      eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge sp e m le a v ∧
      eval_exprlist (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge sp e m le al vl' := by
  cases h with
  | cons _ _ _ v vl hhead htail => exact ⟨v, vl, rfl, hhead, htail⟩

private theorem splitlong_eval_nil_inv
    (xi : ExternalCalls)
    (ge : CompCert4Lean.Backend.CminorSel.genv)
    (sp : CompCert4Lean.Common.Values.val)
    (e : CompCert4Lean.Backend.Cminor.env)
    (m : CompCert4Lean.Common.Memory.mem)
    (le : CompCert4Lean.Backend.CminorSel.letenv)
    (vl : List CompCert4Lean.Common.Values.val)
    (h : eval_exprlist (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge sp e m le .Enil vl) :
    vl = [] := by
  cases h
  rfl

private theorem splitlong_is_longconst_shape (a : expr) (n : CCInt64) :
    is_longconst a = some n →
      ∃ h l : CCInt, a = Eop Omakelong
        (Econs (Eop (Ointconst h) Enil)
          (Econs (Eop (Ointconst l) Enil) Enil)) ∧
        n = int64Ofwords h l := by
  intro hconst
  unfold is_longconst at hconst
  cases hmatch : is_longconst_match a with
  | is_longconst_case1 h l =>
      simp only [hmatch] at hconst
      cases hconst
      exact ⟨h, l, rfl, rfl⟩
  | is_longconst_default e =>
      simp only [hmatch] at hconst
      cases hconst

set_option maxHeartbeats 1000000 in
theorem is_longconst_sound :
    @is_longconst_soundStatement binary64_certificate binary32_certificate := by
  unfold is_longconst_soundStatement
  intro xi prog sp e m le a x n hconst heval
  obtain ⟨h, l, ha, hn⟩ := splitlong_is_longconst_shape a n hconst
  rw [ha] at heval
  rw [hn] at ⊢
  obtain ⟨vl, hargs, hop⟩ := splitlong_eval_eop_inv xi
        (Genv.globalenv prog) sp e m le
        (.Omakelong)
        (.Econs (Eop (.Ointconst h) .Enil)
          (Econs (Eop (.Ointconst l) .Enil) .Enil)) x heval
  obtain ⟨v1, vl', hvl, hh, ht⟩ := splitlong_eval_cons_inv xi
    (Genv.globalenv prog) sp e m le
    (Eop (.Ointconst h) .Enil)
    (Econs (Eop (.Ointconst l) .Enil) .Enil) vl hargs
  obtain ⟨v2, vl2, hvl', hl, hn⟩ := splitlong_eval_cons_inv xi
    (Genv.globalenv prog) sp e m le
    (Eop (.Ointconst l) .Enil) .Enil vl' ht
  have hnil := splitlong_eval_nil_inv xi (Genv.globalenv prog) sp e m le vl2 hn
  rw [hvl, hvl', hnil] at hop
  obtain ⟨wh, hnilh, hhi⟩ := splitlong_eval_eop_inv xi
    (Genv.globalenv prog) sp e m le (.Ointconst h) .Enil _ hh
  obtain ⟨wl, hnill, hlo⟩ := splitlong_eval_eop_inv xi
    (Genv.globalenv prog) sp e m le (.Ointconst l) .Enil _ hl
  have wh0 := splitlong_eval_nil_inv xi (Genv.globalenv prog) sp e m le wh hnilh
  have wl0 := splitlong_eval_nil_inv xi (Genv.globalenv prog) sp e m le wl hnill
  rw [wh0] at hhi
  rw [wl0] at hlo
  change some (CompCert4Lean.Common.Values.val.Vint h) = some v1 at hhi
  change some (CompCert4Lean.Common.Values.val.Vint l) = some v2 at hlo
  cases hhi
  cases hlo
  change some (CompCert4Lean.Common.Values.val.Vlong (int64Ofwords h l)) = some x at hop
  cases hop
  rfl

set_option maxHeartbeats 1000000 in
theorem is_longconst_zero_sound :
    @is_longconst_zero_soundStatement binary64_certificate binary32_certificate := by
  unfold is_longconst_zero_soundStatement
  intro xi prog sp e m le a x hzero heval
  unfold is_longconst_zero at hzero
  cases hmatch : is_longconst a with
  | none =>
      simp only [hmatch] at hzero
      cases hzero
  | some n =>
      simp only [hmatch] at hzero
      have hn : n = int64Zero := by
        -- Int64.eq is the boolean equality decision on the word carrier.
        apply CompCert4Lean.Lib.Integers.WordCore.ext
        simpa [int64Eq, CompCert4Lean.Lib.Integers.Int64.eq,
          CompCert4Lean.Lib.Integers.WordCore.eq] using hzero
      rw [← hn]
      exact is_longconst_sound xi prog sp e m le a x n hmatch heval

end CompCert4Lean.Backend.SplitLongproof

namespace CompCert4Lean.Backend.SplitLongproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.CminorSel

theorem is_intconst_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    is_intconst_soundStatement := by
  intro xi prog sp e m le a x n hconst hev
  unfold CompCert4Lean.Backend.SplitLong.is_intconst at hconst
  cases a with
  | Evar id => simp at hconst
  | Eop op al =>
      cases op with
      | Ointconst n' =>
          cases al with
          | Enil =>
              cases hconst
              cases hev with
              | eval_Eop le' op' al' vl v' hargs hop =>
                  cases hargs with
                  | nil _ =>
                      change some (.Vint n) = some x at hop
                      cases hop
                      rfl
          | Econs a al => simp at hconst
      | _ => simp at hconst
  | Eload chunk addr al => simp at hconst
  | Econdition a b c => simp at hconst
  | Elet a b => simp at hconst
  | Eletvar n' => simp at hconst
  | Ebuiltin ef al => simp at hconst
  | Eexternal id sg al => simp at hconst

end CompCert4Lean.Backend.SplitLongproof

namespace CompCert4Lean.Backend.SplitLongproof

theorem eval_addl
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_addlStatement := by
  unfold eval_addlStatement
  intro xi prog sp e m hptr
  simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr

end CompCert4Lean.Backend.SplitLongproof

namespace CompCert4Lean.Backend.SplitLongproof

theorem eval_subl
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_sublStatement := by
  unfold eval_sublStatement
  intro xi prog sp e m hptr
  simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr

end CompCert4Lean.Backend.SplitLongproof

namespace CompCert4Lean.Backend.SplitLongproof

theorem eval_shrxlimm
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_shrxlimmStatement := by
  unfold eval_shrxlimmStatement
  intro xi prog hf hdecl sp e m le a n x z hptr
  simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr

end CompCert4Lean.Backend.SplitLongproof

namespace CompCert4Lean.Backend.SplitLongproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Builtins0
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.SplitLong

private def splitlong_rocqStringBytes : RocqString → List UInt8
  | .EmptyString => []
  | .String b tail => b :: splitlong_rocqStringBytes tail

private theorem splitlong_rocqStringBytes_ofString (s : String) :
    splitlong_rocqStringBytes (ofString s) = s.toUTF8.toList := by
  unfold ofString
  generalize s.toUTF8.toList = bytes
  induction bytes with
  | nil => rfl
  | cons b bytes ih =>
      simp only [List.foldr, splitlong_rocqStringBytes]
      exact congrArg (List.cons b) ih

private theorem splitlong_byteArrayToListLoop (bs : ByteArray) :
    ∀ i r, ByteArray.toList.loop bs i r =
      r.reverse ++ bs.data.toList.drop i := by
  intro i r
  fun_induction ByteArray.toList.loop bs i r with
  | case1 i r h ih =>
      rw [ih, List.reverse_cons, List.append_assoc]
      simp only [List.append_cancel_left_eq, List.singleton_append]
      have hi : i < bs.data.toList.length := by
        simpa [ByteArray.size_data] using h
      rw [List.drop_eq_getElem_cons hi]
      congr 1
      simp [ByteArray.get!, Array.getElem_toList, h]
  | case2 i r h =>
      have hle : bs.data.toList.length ≤ i := by
        simpa [ByteArray.size_data] using Nat.le_of_not_gt h
      rw [List.drop_eq_nil_of_le hle, List.append_nil]

private theorem splitlong_byteArrayToList (bs : ByteArray) :
    bs.toList = bs.data.toList := by
  rw [ByteArray.toList.eq_1, splitlong_byteArrayToListLoop]
  simp

private theorem splitlong_ofString_injective {s t : String}
    (h : ofString s = ofString t) : s = t := by
  have hb : s.toUTF8.toList = t.toUTF8.toList := by
    rw [← splitlong_rocqStringBytes_ofString s,
      ← splitlong_rocqStringBytes_ofString t, h]
  have hd : s.toByteArray.data = t.toByteArray.data := by
    simp only [String.toUTF8_eq_toByteArray, splitlong_byteArrayToList] at hb
    exact Array.toList_inj.mp hb
  apply String.toByteArray_inj.mp
  exact ByteArray.ext hd

private theorem splitlong_ofString_ne {s t : String} (h : s ≠ t) :
    ofString s ≠ ofString t := by
  intro heq
  exact h (splitlong_ofString_injective heq)

private theorem splitlong_lookupBuiltin_cons_ne {A : Type}
    (sigOf : A → signature) (name n : RocqString) (sg : signature)
    (b : A) (rest : List (RocqString × A)) (hne : name ≠ n) :
    CompCert4Lean.Common.Builtins0.lookup_builtin sigOf name sg
        ((n, b) :: rest) =
      CompCert4Lean.Common.Builtins0.lookup_builtin sigOf name sg rest := by
  rw [CompCert4Lean.Common.Builtins0.lookup_builtin]
  cases hname :
      CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string_dec
        name n with
  | left h => exact (hne h).elim
  | right _ => simp only [hname]

private theorem splitlong_lookupBuiltin_cons_eq {A : Type}
    (sigOf : A → signature) (name n : RocqString) (sg : signature)
    (b : A) (rest : List (RocqString × A)) (hname : name = n)
    (hsig : sg = sigOf b) :
    CompCert4Lean.Common.Builtins0.lookup_builtin sigOf name sg
        ((n, b) :: rest) = some b := by
  rw [CompCert4Lean.Common.Builtins0.lookup_builtin]
  cases hnameDec :
      CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string_dec
        name n with
  | right hne => exact (hne hname).elim
  | left _ =>
      cases hsigDec : CompCert4Lean.Common.AST.signature_eq sg (sigOf b) with
      | right hne => exact (hne hsig).elim
      | left _ => simp only [hnameDec, hsigDec]

theorem eval_divlu_base
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_divlu_baseStatement binary64_certificate binary32_certificate := by
  unfold eval_divlu_baseStatement
  intro xi prog hf hdecl sp e m le a b x y z ha hb hz
  refine ⟨z, ?_, Val.lessdef_refl z⟩
  unfold divlu_base
  rcases hdecl with ⟨_, _, _, _, _, _, _, hudiv, _⟩
  have htable : CompCert4Lean.Common.Builtins0.standard_builtin_table =
      [ (ofString "__builtin_sel", BI_select Tint)
      , (ofString "__builtin_sel", BI_select Tlong)
      , (ofString "__builtin_sel", BI_select Tfloat)
      , (ofString "__builtin_sel", BI_select Tsingle)
      , (ofString "__builtin_fabs", BI_fabs)
      , (ofString "__builtin_fabsf", BI_fabsf)
      , (ofString "__builtin_fsqrt", BI_fsqrt)
      , (ofString "__builtin_sqrt", BI_fsqrt)
      , (ofString "__builtin_negl", BI_negl)
      , (ofString "__builtin_addl", BI_addl)
      , (ofString "__builtin_subl", BI_subl)
      , (ofString "__builtin_mull", BI_mull)
      , (ofString "__builtin_bswap16", BI_i16_bswap)
      , (ofString "__builtin_bswap", BI_i32_bswap)
      , (ofString "__builtin_bswap32", BI_i32_bswap)
      , (ofString "__builtin_bswap64", BI_i64_bswap)
      , (ofString "__builtin_unreachable", BI_unreachable)
      , (ofString "__compcert_i64_umulh", BI_i64_umulh)
      , (ofString "__compcert_i64_smulh", BI_i64_smulh)
      , (ofString "__compcert_i64_sdiv", BI_i64_sdiv)
      , (ofString "__compcert_i64_udiv", BI_i64_udiv) ] ++
        CompCert4Lean.Common.Builtins0.standard_builtin_table.drop 21 := by
    rfl
  have hsel : ofString "__compcert_i64_udiv" ≠ ofString "__builtin_sel" :=
    splitlong_ofString_ne (by decide)
  have hfabs : ofString "__compcert_i64_udiv" ≠ ofString "__builtin_fabs" :=
    splitlong_ofString_ne (by decide)
  have hfabsf : ofString "__compcert_i64_udiv" ≠ ofString "__builtin_fabsf" :=
    splitlong_ofString_ne (by decide)
  have hfsqrt : ofString "__compcert_i64_udiv" ≠ ofString "__builtin_fsqrt" :=
    splitlong_ofString_ne (by decide)
  have hsqrt : ofString "__compcert_i64_udiv" ≠ ofString "__builtin_sqrt" :=
    splitlong_ofString_ne (by decide)
  have hnegl : ofString "__compcert_i64_udiv" ≠ ofString "__builtin_negl" :=
    splitlong_ofString_ne (by decide)
  have haddl : ofString "__compcert_i64_udiv" ≠ ofString "__builtin_addl" :=
    splitlong_ofString_ne (by decide)
  have hsubl : ofString "__compcert_i64_udiv" ≠ ofString "__builtin_subl" :=
    splitlong_ofString_ne (by decide)
  have hmull : ofString "__compcert_i64_udiv" ≠ ofString "__builtin_mull" :=
    splitlong_ofString_ne (by decide)
  have hbswap16 : ofString "__compcert_i64_udiv" ≠ ofString "__builtin_bswap16" :=
    splitlong_ofString_ne (by decide)
  have hbswap : ofString "__compcert_i64_udiv" ≠ ofString "__builtin_bswap" :=
    splitlong_ofString_ne (by decide)
  have hbswap32 : ofString "__compcert_i64_udiv" ≠ ofString "__builtin_bswap32" :=
    splitlong_ofString_ne (by decide)
  have hbswap64 : ofString "__compcert_i64_udiv" ≠ ofString "__builtin_bswap64" :=
    splitlong_ofString_ne (by decide)
  have hunreachable : ofString "__compcert_i64_udiv" ≠ ofString "__builtin_unreachable" :=
    splitlong_ofString_ne (by decide)
  have humulh : ofString "__compcert_i64_udiv" ≠ ofString "__compcert_i64_umulh" :=
    splitlong_ofString_ne (by decide)
  have hsmulh : ofString "__compcert_i64_udiv" ≠ ofString "__compcert_i64_smulh" :=
    splitlong_ofString_ne (by decide)
  have hsdiv : ofString "__compcert_i64_udiv" ≠ ofString "__compcert_i64_sdiv" :=
    splitlong_ofString_ne (by decide)
  have hlookup :
      lookup_builtin_function (ofString "__compcert_i64_udiv") sig_ll_l =
        some (.BI_standard .BI_i64_udiv) := by
    have hsig : sig_ll_l =
        CompCert4Lean.Common.Builtins0.standard_builtin_sig BI_i64_udiv := rfl
    unfold lookup_builtin_function
    rw [htable]
    simp only [List.cons_append, List.nil_append]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hsel]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hsel]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hsel]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hsel]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hfabs]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hfabsf]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hfsqrt]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hsqrt]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hnegl]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ haddl]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hsubl]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hmull]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hbswap16]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hbswap]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hbswap32]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hbswap64]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hunreachable]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ humulh]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hsmulh]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hsdiv]
    rw [splitlong_lookupBuiltin_cons_eq _ _ _ _ _ _ rfl hsig]
  exact eval_helper_2 xi prog sp e m (.BI_standard .BI_i64_udiv) le
    hf.i64_udiv (ofString "__compcert_i64_udiv") sig_ll_l
    a b x y z ha hb hudiv hlookup hz

end CompCert4Lean.Backend.SplitLongproof

namespace CompCert4Lean.Backend.SplitLongproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Builtins0
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.SplitLong

theorem eval_modlu_base
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_modlu_baseStatement binary64_certificate binary32_certificate := by
  unfold eval_modlu_baseStatement
  intro xi prog hf hdecl sp e m le a b x y z ha hb hz
  refine ⟨z, ?_, Val.lessdef_refl z⟩
  unfold modlu_base
  rcases hdecl with ⟨_, _, _, _, _, _, _, _, _, humod, _⟩
  have htable : CompCert4Lean.Common.Builtins0.standard_builtin_table =
      [ (ofString "__builtin_sel", BI_select Tint)
      , (ofString "__builtin_sel", BI_select Tlong)
      , (ofString "__builtin_sel", BI_select Tfloat)
      , (ofString "__builtin_sel", BI_select Tsingle)
      , (ofString "__builtin_fabs", BI_fabs)
      , (ofString "__builtin_fabsf", BI_fabsf)
      , (ofString "__builtin_fsqrt", BI_fsqrt)
      , (ofString "__builtin_sqrt", BI_fsqrt)
      , (ofString "__builtin_negl", BI_negl)
      , (ofString "__builtin_addl", BI_addl)
      , (ofString "__builtin_subl", BI_subl)
      , (ofString "__builtin_mull", BI_mull)
      , (ofString "__builtin_bswap16", BI_i16_bswap)
      , (ofString "__builtin_bswap", BI_i32_bswap)
      , (ofString "__builtin_bswap32", BI_i32_bswap)
      , (ofString "__builtin_bswap64", BI_i64_bswap)
      , (ofString "__builtin_unreachable", BI_unreachable)
      , (ofString "__compcert_i64_umulh", BI_i64_umulh)
      , (ofString "__compcert_i64_smulh", BI_i64_smulh)
      , (ofString "__compcert_i64_sdiv", BI_i64_sdiv)
      , (ofString "__compcert_i64_udiv", BI_i64_udiv)
      , (ofString "__compcert_i64_smod", BI_i64_smod)
      , (ofString "__compcert_i64_umod", BI_i64_umod) ] ++
        CompCert4Lean.Common.Builtins0.standard_builtin_table.drop 23 := by
    rfl
  have hsel : ofString "__compcert_i64_umod" ≠ ofString "__builtin_sel" :=
    splitlong_ofString_ne (by decide)
  have hfabs : ofString "__compcert_i64_umod" ≠ ofString "__builtin_fabs" :=
    splitlong_ofString_ne (by decide)
  have hfabsf : ofString "__compcert_i64_umod" ≠ ofString "__builtin_fabsf" :=
    splitlong_ofString_ne (by decide)
  have hfsqrt : ofString "__compcert_i64_umod" ≠ ofString "__builtin_fsqrt" :=
    splitlong_ofString_ne (by decide)
  have hsqrt : ofString "__compcert_i64_umod" ≠ ofString "__builtin_sqrt" :=
    splitlong_ofString_ne (by decide)
  have hnegl : ofString "__compcert_i64_umod" ≠ ofString "__builtin_negl" :=
    splitlong_ofString_ne (by decide)
  have haddl : ofString "__compcert_i64_umod" ≠ ofString "__builtin_addl" :=
    splitlong_ofString_ne (by decide)
  have hsubl : ofString "__compcert_i64_umod" ≠ ofString "__builtin_subl" :=
    splitlong_ofString_ne (by decide)
  have hmull : ofString "__compcert_i64_umod" ≠ ofString "__builtin_mull" :=
    splitlong_ofString_ne (by decide)
  have hbswap16 : ofString "__compcert_i64_umod" ≠ ofString "__builtin_bswap16" :=
    splitlong_ofString_ne (by decide)
  have hbswap : ofString "__compcert_i64_umod" ≠ ofString "__builtin_bswap" :=
    splitlong_ofString_ne (by decide)
  have hbswap32 : ofString "__compcert_i64_umod" ≠ ofString "__builtin_bswap32" :=
    splitlong_ofString_ne (by decide)
  have hbswap64 : ofString "__compcert_i64_umod" ≠ ofString "__builtin_bswap64" :=
    splitlong_ofString_ne (by decide)
  have hunreachable : ofString "__compcert_i64_umod" ≠ ofString "__builtin_unreachable" :=
    splitlong_ofString_ne (by decide)
  have humulh : ofString "__compcert_i64_umod" ≠ ofString "__compcert_i64_umulh" :=
    splitlong_ofString_ne (by decide)
  have hsmulh : ofString "__compcert_i64_umod" ≠ ofString "__compcert_i64_smulh" :=
    splitlong_ofString_ne (by decide)
  have hsdiv : ofString "__compcert_i64_umod" ≠ ofString "__compcert_i64_sdiv" :=
    splitlong_ofString_ne (by decide)
  have hudiv : ofString "__compcert_i64_umod" ≠ ofString "__compcert_i64_udiv" :=
    splitlong_ofString_ne (by decide)
  have hsmod : ofString "__compcert_i64_umod" ≠ ofString "__compcert_i64_smod" :=
    splitlong_ofString_ne (by decide)
  have hlookup :
      lookup_builtin_function (ofString "__compcert_i64_umod") sig_ll_l =
        some (.BI_standard .BI_i64_umod) := by
    have hsig : sig_ll_l =
        CompCert4Lean.Common.Builtins0.standard_builtin_sig BI_i64_umod := rfl
    unfold lookup_builtin_function
    rw [htable]
    simp only [List.cons_append, List.nil_append]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hsel]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hsel]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hsel]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hsel]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hfabs]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hfabsf]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hfsqrt]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hsqrt]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hnegl]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ haddl]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hsubl]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hmull]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hbswap16]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hbswap]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hbswap32]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hbswap64]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hunreachable]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ humulh]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hsmulh]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hsdiv]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hudiv]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ hsmod]
    rw [splitlong_lookupBuiltin_cons_eq _ _ _ _ _ _ rfl hsig]
  exact eval_helper_2 xi prog sp e m (.BI_standard .BI_i64_umod) le
    hf.i64_umod (ofString "__compcert_i64_umod") sig_ll_l
    a b x y z ha hb humod hlookup hz

end CompCert4Lean.Backend.SplitLongproof

namespace CompCert4Lean.Backend.SplitLongproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Builtins0
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.SplitLong

theorem eval_divls_base
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_divls_baseStatement binary64_certificate binary32_certificate := by
  unfold eval_divls_baseStatement
  intro xi prog hf hdecl sp e m le a b x y z ha hb hz
  refine ⟨z, ?_, Val.lessdef_refl z⟩
  unfold divls_base
  rcases hdecl with ⟨_, _, _, _, _, _, hdiv, _⟩
  have hlookup :
      lookup_builtin_function (ofString "__compcert_i64_sdiv") sig_ll_l =
        some (.BI_standard .BI_i64_sdiv) := by
    have htable : CompCert4Lean.Common.Builtins0.standard_builtin_table =
        [ (ofString "__builtin_sel", BI_select Tint)
        , (ofString "__builtin_sel", BI_select Tlong)
        , (ofString "__builtin_sel", BI_select Tfloat)
        , (ofString "__builtin_sel", BI_select Tsingle)
        , (ofString "__builtin_fabs", BI_fabs)
        , (ofString "__builtin_fabsf", BI_fabsf)
        , (ofString "__builtin_fsqrt", BI_fsqrt)
        , (ofString "__builtin_sqrt", BI_fsqrt)
        , (ofString "__builtin_negl", BI_negl)
        , (ofString "__builtin_addl", BI_addl)
        , (ofString "__builtin_subl", BI_subl)
        , (ofString "__builtin_mull", BI_mull)
        , (ofString "__builtin_bswap16", BI_i16_bswap)
        , (ofString "__builtin_bswap", BI_i32_bswap)
        , (ofString "__builtin_bswap32", BI_i32_bswap)
        , (ofString "__builtin_bswap64", BI_i64_bswap)
        , (ofString "__builtin_unreachable", BI_unreachable)
        , (ofString "__compcert_i64_umulh", BI_i64_umulh)
        , (ofString "__compcert_i64_smulh", BI_i64_smulh)
        , (ofString "__compcert_i64_sdiv", BI_i64_sdiv) ] ++
          CompCert4Lean.Common.Builtins0.standard_builtin_table.drop 20 := by rfl
    have hn : ∀ n : String, n ≠ "__compcert_i64_sdiv" →
        ofString "__compcert_i64_sdiv" ≠ ofString n := by
      intro n h
      exact splitlong_ofString_ne (Ne.symm h)
    have hsig : sig_ll_l =
        CompCert4Lean.Common.Builtins0.standard_builtin_sig BI_i64_sdiv := rfl
    unfold lookup_builtin_function
    rw [htable]
    simp only [List.cons_append, List.nil_append]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_eq _ _ _ _ _ _ rfl hsig]
  exact eval_helper_2 xi prog sp e m (.BI_standard .BI_i64_sdiv) le
    hf.i64_sdiv (ofString "__compcert_i64_sdiv") sig_ll_l
    a b x y z ha hb hdiv hlookup hz

theorem eval_modls_base
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_modls_baseStatement binary64_certificate binary32_certificate := by
  unfold eval_modls_baseStatement
  intro xi prog hf hdecl sp e m le a b x y z ha hb hz
  refine ⟨z, ?_, Val.lessdef_refl z⟩
  unfold modls_base
  rcases hdecl with ⟨_, _, _, _, _, _, _, _, hmod, _⟩
  have hlookup :
      lookup_builtin_function (ofString "__compcert_i64_smod") sig_ll_l =
        some (.BI_standard .BI_i64_smod) := by
    have htable : CompCert4Lean.Common.Builtins0.standard_builtin_table =
        [ (ofString "__builtin_sel", BI_select Tint)
        , (ofString "__builtin_sel", BI_select Tlong)
        , (ofString "__builtin_sel", BI_select Tfloat)
        , (ofString "__builtin_sel", BI_select Tsingle)
        , (ofString "__builtin_fabs", BI_fabs)
        , (ofString "__builtin_fabsf", BI_fabsf)
        , (ofString "__builtin_fsqrt", BI_fsqrt)
        , (ofString "__builtin_sqrt", BI_fsqrt)
        , (ofString "__builtin_negl", BI_negl)
        , (ofString "__builtin_addl", BI_addl)
        , (ofString "__builtin_subl", BI_subl)
        , (ofString "__builtin_mull", BI_mull)
        , (ofString "__builtin_bswap16", BI_i16_bswap)
        , (ofString "__builtin_bswap", BI_i32_bswap)
        , (ofString "__builtin_bswap32", BI_i32_bswap)
        , (ofString "__builtin_bswap64", BI_i64_bswap)
        , (ofString "__builtin_unreachable", BI_unreachable)
        , (ofString "__compcert_i64_umulh", BI_i64_umulh)
        , (ofString "__compcert_i64_smulh", BI_i64_smulh)
        , (ofString "__compcert_i64_sdiv", BI_i64_sdiv)
        , (ofString "__compcert_i64_udiv", BI_i64_udiv)
        , (ofString "__compcert_i64_smod", BI_i64_smod) ] ++
          CompCert4Lean.Common.Builtins0.standard_builtin_table.drop 22 := by rfl
    have hn : ∀ n : String, n ≠ "__compcert_i64_smod" →
        ofString "__compcert_i64_smod" ≠ ofString n := by
      intro n h
      exact splitlong_ofString_ne (Ne.symm h)
    have hsig : sig_ll_l =
        CompCert4Lean.Common.Builtins0.standard_builtin_sig BI_i64_smod := rfl
    unfold lookup_builtin_function
    rw [htable]
    simp only [List.cons_append, List.nil_append]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_ne _ _ _ _ _ _ (hn _ (by decide))]
    rw [splitlong_lookupBuiltin_cons_eq _ _ _ _ _ _ rfl hsig]
  exact eval_helper_2 xi prog sp e m (.BI_standard .BI_i64_smod) le
    hf.i64_smod (ofString "__compcert_i64_smod") sig_ll_l
    a b x y z ha hb hmod hlookup hz

end CompCert4Lean.Backend.SplitLongproof

namespace CompCert4Lean.Backend.SplitLongproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers

private theorem test_mod_congr_add_one (a b m : Nat) (h : a % m = b % m) :
    (2 * a + 1) % m = (2 * b + 1) % m := by
  rw [← Nat.mod_add_div a m, ← Nat.mod_add_div b m]
  simp [Nat.add_mod, Nat.mul_mod, h]

private theorem test_mod_congr_mul (a b m : Nat) (h : a % m = b % m) :
    (2 * a) % m = (2 * b) % m := by
  rw [← Nat.mod_add_div a m, ← Nat.mod_add_div b m]
  simp [Nat.add_mod, Nat.mul_mod, h]

private theorem test_repr_Zpos (bits : Nat) (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.positive) :
    (CompCert4Lean.Lib.Integers.WordCore.repr bits
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Zpos p)).val =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p % (2 ^ bits) := by
  induction p with
  | xH => simp_all!
  | xI p ih =>
      simp_all!
      exact test_mod_congr_add_one _ _ _ ih
  | xO p ih =>
      simp_all!
      exact test_mod_congr_mul _ _ _ ih

private theorem test_repr_zOfNat (bits n : Nat) :
    (CompCert4Lean.Lib.Integers.WordCore.repr bits
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)).val =
      n % (2 ^ bits) := by
  cases n with
  | zero => rfl
  | succ n =>
      dsimp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat]
      exact test_repr_Zpos bits
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat (n + 1)) |>.trans
        (by rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat (by omega)])

private theorem test_or_val {bits : Nat}
    (x y : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    (CompCert4Lean.Lib.Integers.WordCore.or x y).val = Nat.lor x.val y.val := by
  unfold CompCert4Lean.Lib.Integers.WordCore.or
  rw [test_repr_zOfNat]
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow
    (CompCert4Lean.Lib.Integers.WordCore.Word.toFin x).isLt
    (CompCert4Lean.Lib.Integers.WordCore.Word.toFin y).isLt)

private theorem test_unsigned_eq_zOfNat {bits : Nat}
    (x : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    CompCert4Lean.Lib.Integers.WordCore.unsigned x =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat x.val := by
  have hx0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0 x.intval := by
    have h := x.intrange.1
    change (-1 : Int) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval at h
    change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval
    omega
  exact (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Z2Nat.id
    x.intval hx0).symm

private theorem test_shl_val {bits : Nat}
    (x y : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    (CompCert4Lean.Lib.Integers.WordCore.shl x y).val =
      (x.val * 2 ^ y.val) % (2 ^ bits) := by
  change (CompCert4Lean.Lib.Integers.WordCore.repr bits
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftl
      (CompCert4Lean.Lib.Integers.WordCore.unsigned x)
      (CompCert4Lean.Lib.Integers.WordCore.unsigned y))).val = _
  rw [test_unsigned_eq_zOfNat x, test_unsigned_eq_zOfNat y]
  rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftl
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat x.val)
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat y.val) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (x.val * 2 ^ y.val) by
    unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftl
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
      Int.ofNat_eq_natCast, Int.natCast_nonneg, ↓reduceIte]
    rw [Int.natCast_mul, Int.natCast_pow]
    rfl]
  exact test_repr_zOfNat bits (x.val * 2 ^ y.val)

private theorem test_int64_repr_unsigned_val (x : CCInt) :
    (CompCert4Lean.Lib.Integers.Int64.repr
      (CompCert4Lean.Lib.Integers.Int.unsigned x)).val = x.val := by
  rw [show CompCert4Lean.Lib.Integers.Int.unsigned x =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat x.val by
    exact test_unsigned_eq_zOfNat x]
  unfold CompCert4Lean.Lib.Integers.Int64.repr
  rw [test_repr_zOfNat]
  apply Nat.mod_eq_of_lt
  have hx := (CompCert4Lean.Lib.Integers.WordCore.Word.toFin x).isLt
  change x.val < 2 ^ 32 at hx
  have hpow : 2 ^ 32 ≤ 2 ^ 64 :=
    Nat.pow_le_pow_right Nat.zero_lt_two (by decide)
  exact Nat.lt_of_lt_of_le hx hpow

private theorem test_int64_repr_zwordsize_val :
    (CompCert4Lean.Lib.Integers.Int64.repr
      CompCert4Lean.Lib.Integers.Int.zwordsize).val = 32 := by
  rw [show CompCert4Lean.Lib.Integers.Int.zwordsize =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 32 by rfl]
  unfold CompCert4Lean.Lib.Integers.Int64.repr
  rw [test_repr_zOfNat]
  decide

private theorem test_int64_ofwords_val (h l : CCInt) :
    (int64Ofwords h l).val = Nat.lor (Nat.shiftLeft h.val 32) l.val := by
  unfold int64Ofwords CompCert4Lean.Lib.Integers.Int64.ofwords
    CompCert4Lean.Lib.Integers.Int64.or
    CompCert4Lean.Lib.Integers.Int64.shl
  rw [test_or_val, test_shl_val,
    test_int64_repr_unsigned_val, test_int64_repr_zwordsize_val,
    test_int64_repr_unsigned_val]
  have hshift : Nat.shiftLeft h.val 32 = h.val * 2 ^ 32 :=
    Nat.shiftLeft_eq h.val 32
  rw [hshift]
  unfold CompCert4Lean.Lib.Integers.Int64.wordsize
  have hh := (CompCert4Lean.Lib.Integers.WordCore.Word.toFin h).isLt
  change h.val < 2 ^ 32 at hh
  have hmul' := Nat.mul_lt_mul_of_pos_right hh (Nat.two_pow_pos 32)
  have hpow : 2 ^ 32 * 2 ^ 32 = 2 ^ 64 := by
    rw [← Nat.pow_add]
  have hmul : h.val * 2 ^ 32 < 2 ^ 64 := hpow ▸ hmul'
  rw [Nat.mod_eq_of_lt hmul]

private theorem test_nat_lor_zero (a b : Nat) :
    Nat.lor a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro hab
    have ha : a = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      have hz : (Nat.lor a b).testBit i = false := by
        rw [hab]
        simp
      rw [Nat.lor_eq, Nat.testBit_or] at hz
      by_cases hbit : a.testBit i = true <;> simp [hbit] at hz ⊢
    have hb : b = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      have hz : (Nat.lor a b).testBit i = false := by
        rw [hab]
        simp
      rw [Nat.lor_eq, Nat.testBit_or] at hz
      by_cases hbit : b.testBit i = true <;> simp [hbit] at hz ⊢
    exact ⟨ha, hb⟩
  · rintro ⟨rfl, rfl⟩
    simp

private theorem test_int_or_val (h l : CCInt) :
    (CompCert4Lean.Lib.Integers.Int.or h l).val = Nat.lor h.val l.val := by
  change (CompCert4Lean.Lib.Integers.WordCore.or h l).val = _
  exact test_or_val h l

private theorem test_int_zero_val :
    (CompCert4Lean.Lib.Integers.Int.zero : CCInt).val = 0 := by
  rfl

private theorem test_int64_zero_val :
    (CompCert4Lean.Lib.Integers.Int64.zero).val = 0 := by
  rfl

private theorem test_int64_ofwords_zero_iff (h l : CCInt) :
    int64Ofwords h l = CompCert4Lean.Lib.Integers.Int64.zero ↔
      h = CompCert4Lean.Lib.Integers.Int.zero ∧
      l = CompCert4Lean.Lib.Integers.Int.zero := by
  constructor
  · intro hz
    have hv := congrArg (fun q => q.val) hz
    rw [test_int64_ofwords_val, test_int64_zero_val] at hv
    obtain ⟨hh, hl⟩ := test_nat_lor_zero _ _ |>.mp hv
    have hh0 : h.val = 0 := Nat.shiftLeft_eq_zero_iff.mp hh
    have hle : h = CompCert4Lean.Lib.Integers.Int.zero := by
      apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
      simpa [test_int_zero_val] using hh0
    have lle : l = CompCert4Lean.Lib.Integers.Int.zero := by
      apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
      simpa [test_int_zero_val] using hl
    exact ⟨hle, lle⟩
  · rintro ⟨rfl, rfl⟩
    apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
    rw [test_int64_ofwords_val, test_int64_zero_val,
      test_int_zero_val]
    simp

private theorem test_decompose_word_eq_iff (h l : CCInt) :
    int64Ofwords h l = CompCert4Lean.Lib.Integers.Int64.zero ↔
      CompCert4Lean.Lib.Integers.Int.or h l =
        CompCert4Lean.Lib.Integers.Int.zero := by
  constructor
  · intro hz
    obtain ⟨hh, hl⟩ := test_int64_ofwords_zero_iff h l |>.mp hz
    subst hh
    subst hl
    rfl
  · intro hz
    have hv := congrArg (fun q => q.val) hz
    rw [test_int_or_val, test_int_zero_val] at hv
    obtain ⟨hh, hl⟩ := test_nat_lor_zero _ _ |>.mp hv
    have hheq : h = CompCert4Lean.Lib.Integers.Int.zero := by
      apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
      simpa [test_int_zero_val] using hh
    have hleq : l = CompCert4Lean.Lib.Integers.Int.zero := by
      apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
      simpa [test_int_zero_val] using hl
    exact test_int64_ofwords_zero_iff h l |>.mpr ⟨hheq, hleq⟩

theorem decompose_cmpl_eq_zero : decompose_cmpl_eq_zeroStatement := by
  intro h l
  change decide ((int64Ofwords h l).intval = int64Zero.intval) =
    decide ((intOr h l).intval = intZero.intval)
  have hiff : (int64Ofwords h l).intval = int64Zero.intval ↔
      (intOr h l).intval = intZero.intval := by
    constructor
    · intro hz
      have hw : int64Ofwords h l = int64Zero :=
        CompCert4Lean.Lib.Integers.WordCore.ext hz
      have ho := test_decompose_word_eq_iff h l |>.mp hw
      exact congrArg (fun q => q.intval) ho
    · intro hz
      have ho : intOr h l = intZero :=
        CompCert4Lean.Lib.Integers.WordCore.ext hz
      have hw := test_decompose_word_eq_iff h l |>.mpr ho
      exact congrArg (fun q => q.intval) hw
  by_cases hz : (int64Ofwords h l).intval = int64Zero.intval
  · have ho := hiff.mp hz
    simp [hz, ho]
  · have ho : ¬ (intOr h l).intval = intZero.intval := by
      intro ho
      exact hz (hiff.mpr ho)
    simp [hz, ho]

end CompCert4Lean.Backend.SplitLongproof

namespace CompCert4Lean.Backend.SplitLongproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.SplitLong
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

variable
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

private abbrev SLInt := CompCert4Lean.Lib.Integers.int
private abbrev SLEnv := CompCert4Lean.Backend.Cminor.env
private abbrev SLMem := CompCert4Lean.Common.Memory.mem
private abbrev SLVal := CompCert4Lean.Common.Values.val
private abbrev SLGenv := CompCert4Lean.Backend.CminorSel.genv

private theorem splitlong_eval_orcomp
    (xi : ExternalCalls) (ge : SLGenv) (sp : SLVal) (e : SLEnv) (m : SLMem)
    (le : letenv) (h l : expr) (p q : SLInt)
    (hh : eval_expr xi ge sp e m le h (.Vint p))
    (hl : eval_expr xi ge sp e m le l (.Vint q)) :
    ∃ v, eval_expr xi ge sp e m le
      (CompCert4Lean.X86.SelectOp.comp .Ceq
        (CompCert4Lean.X86.SelectOp.or h l)
        (Eop (Ointconst (CompCert4Lean.Lib.Integers.Int.zero)) Enil)) v ∧
      v = CompCert4Lean.Common.Values.Val.of_bool
        (CompCert4Lean.Lib.Integers.Int.eq
          (CompCert4Lean.Lib.Integers.Int.or p q)
          CompCert4Lean.Lib.Integers.Int.zero) := by
  obtain ⟨vo, ho, hdo⟩ := CompCert4Lean.X86.SelectOpproof.eval_or
    xi ge sp e m le h (.Vint p) l (.Vint q) hh hl
  have hdo' : vo = .Vint (CompCert4Lean.Lib.Integers.Int.or p q) := by
    cases hdo
    simp [CompCert4Lean.Common.Values.Val.or]
  subst vo
  have hz : eval_expr xi ge sp e m le
      (Eop (Ointconst (CompCert4Lean.Lib.Integers.Int.zero)) Enil)
      (.Vint (CompCert4Lean.Lib.Integers.Int.zero)) := by
    apply eval_expr.eval_Eop (le := le)
      (op := Ointconst (CompCert4Lean.Lib.Integers.Int.zero))
      (al := Enil) (vl := [])
    · exact eval_exprlist.nil le
    · rfl
  obtain ⟨vc, hc, hdc⟩ := CompCert4Lean.X86.SelectOpproof.eval_comp
    xi ge sp e m .Ceq le (CompCert4Lean.X86.SelectOp.or h l)
      (.Vint (CompCert4Lean.Lib.Integers.Int.or p q))
      (Eop (Ointconst (CompCert4Lean.Lib.Integers.Int.zero)) Enil)
      (.Vint (CompCert4Lean.Lib.Integers.Int.zero)) ho hz
  have hsrc : CompCert4Lean.Common.Values.Val.cmp .Ceq
      (.Vint (CompCert4Lean.Lib.Integers.Int.or p q))
      (.Vint (CompCert4Lean.Lib.Integers.Int.zero)) =
      CompCert4Lean.Common.Values.Val.of_bool
        (CompCert4Lean.Lib.Integers.Int.eq
          (CompCert4Lean.Lib.Integers.Int.or p q)
          (CompCert4Lean.Lib.Integers.Int.zero)) := by
    cases h : decide ((CompCert4Lean.Lib.Integers.Int.or p q).intval =
        CompCert4Lean.Lib.Integers.Int.zero.intval) <;>
      simp [CompCert4Lean.Common.Values.Val.cmp,
        CompCert4Lean.Common.Values.Val.cmp_bool,
        CompCert4Lean.Common.Values.Val.of_optbool,
        CompCert4Lean.Common.Values.Val.of_bool,
        CompCert4Lean.Lib.Integers.Int.cmp,
        CompCert4Lean.Lib.Integers.WordCore.cmp,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, h]
  rw [hsrc] at hdc
  refine ⟨vc, hc, ?_⟩
  cases heq : CompCert4Lean.Lib.Integers.Int.eq
      (CompCert4Lean.Lib.Integers.Int.or p q)
      (CompCert4Lean.Lib.Integers.Int.zero) with
  | false =>
      simp [CompCert4Lean.Common.Values.Val.of_bool, heq] at hdc ⊢
      cases hdc <;> rfl
  | true =>
      simp [CompCert4Lean.Common.Values.Val.of_bool, heq] at hdc ⊢
      cases hdc <;> rfl

private theorem splitlong_shru_val {bits : Nat}
    (x y : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    (CompCert4Lean.Lib.Integers.WordCore.shru x y).val =
      x.val / 2 ^ y.val := by
  change (CompCert4Lean.Lib.Integers.WordCore.repr bits
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftr
      (CompCert4Lean.Lib.Integers.WordCore.unsigned x)
      (CompCert4Lean.Lib.Integers.WordCore.unsigned y))).val = _
  rw [test_unsigned_eq_zOfNat x, test_unsigned_eq_zOfNat y]
  rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftr
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat x.val)
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat y.val) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (x.val / 2 ^ y.val) by
    unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftr
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
      Int.ofNat_eq_natCast, Int.natCast_nonneg, ↓reduceIte,
      Int.toNat_natCast, Int.natCast_pow]
    exact congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      Int.ofNat_ediv_ofNat]
  rw [test_repr_zOfNat]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
    (CompCert4Lean.Lib.Integers.WordCore.Word.toFin x).isLt

private theorem splitlong_hiword_val (x : CompCert4Lean.Lib.Integers.int64) :
    (CompCert4Lean.Lib.Integers.Int64.hiword x).val = x.val / 2 ^ 32 := by
  unfold CompCert4Lean.Lib.Integers.Int64.hiword
    CompCert4Lean.Lib.Integers.Int64.shru
    CompCert4Lean.Lib.Integers.Int64.repr
    CompCert4Lean.Lib.Integers.Int64.unsigned
  have hshift :
      (CompCert4Lean.Lib.Integers.WordCore.repr
        CompCert4Lean.Lib.Integers.Int64.wordsize
        CompCert4Lean.Lib.Integers.Int.zwordsize).val = 32 := by
    change (CompCert4Lean.Lib.Integers.WordCore.repr 64
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 32)).val = 32
    rw [test_repr_zOfNat]
  rw [test_unsigned_eq_zOfNat, splitlong_shru_val, hshift]
  change (CompCert4Lean.Lib.Integers.WordCore.repr
    CompCert4Lean.Lib.Integers.Int.wordsize
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
      (x.val / 2 ^ 32))).val = x.val / 2 ^ 32
  rw [test_repr_zOfNat]
  apply Nat.mod_eq_of_lt
  have hx := (CompCert4Lean.Lib.Integers.WordCore.Word.toFin x).isLt
  change x.val < 2 ^ 64 at hx
  have hpow : 2 ^ 32 * 2 ^ 32 = 2 ^ 64 := by
    rw [← Nat.pow_add]
  have hx' : x.val < 2 ^ 32 * 2 ^ 32 := hpow ▸ hx
  have hq : x.val / 2 ^ 32 < 2 ^ 32 :=
    Nat.div_lt_of_lt_mul hx'
  simpa [CompCert4Lean.Lib.Integers.Int.wordsize] using hq

private theorem splitlong_loword_val (x : CompCert4Lean.Lib.Integers.int64) :
    (CompCert4Lean.Lib.Integers.Int64.loword x).val = x.val % 2 ^ 32 := by
  unfold CompCert4Lean.Lib.Integers.Int64.loword
    CompCert4Lean.Lib.Integers.Int.repr
    CompCert4Lean.Lib.Integers.Int64.unsigned
  rw [test_unsigned_eq_zOfNat, test_repr_zOfNat]
  have hx := (CompCert4Lean.Lib.Integers.WordCore.Word.toFin x).isLt
  change x.val < 2 ^ 64 at hx
  have hle : x.val % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  simpa [CompCert4Lean.Lib.Integers.Int.wordsize] using hle

private theorem splitlong_int_eq_zero_iff (w : CompCert4Lean.Lib.Integers.int) :
    CompCert4Lean.Lib.Integers.Int.eq w
        CompCert4Lean.Lib.Integers.Int.zero = true ↔ w.val = 0 := by
  constructor
  · intro h
    have hw : w = CompCert4Lean.Lib.Integers.Int.zero := by
      apply CompCert4Lean.Lib.Integers.WordCore.ext
      simpa [CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq] using h
    simpa [test_int_zero_val] using congrArg (fun q => q.val) hw
  · intro h
    have hw : w = CompCert4Lean.Lib.Integers.Int.zero := by
      apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
      simpa [test_int_zero_val] using h
    subst w
    simp [CompCert4Lean.Lib.Integers.Int.eq,
      CompCert4Lean.Lib.Integers.WordCore.eq]

private theorem splitlong_int64_eq_zero_iff
    (w : CompCert4Lean.Lib.Integers.int64) :
    CompCert4Lean.Lib.Integers.Int64.eq w
        CompCert4Lean.Lib.Integers.Int64.zero = true ↔ w.val = 0 := by
  constructor
  · intro h
    have hw : w = CompCert4Lean.Lib.Integers.Int64.zero := by
      apply CompCert4Lean.Lib.Integers.WordCore.ext
      simpa [CompCert4Lean.Lib.Integers.Int64.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq] using h
    simpa [test_int64_zero_val] using congrArg (fun q => q.val) hw
  · intro h
    have hw : w = CompCert4Lean.Lib.Integers.Int64.zero := by
      apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
      simpa [test_int64_zero_val] using h
    subst w
    simp [CompCert4Lean.Lib.Integers.Int64.eq,
      CompCert4Lean.Lib.Integers.WordCore.eq]

private theorem splitlong_cmpl_zero_bool
    (x : CompCert4Lean.Lib.Integers.int64) :
    CompCert4Lean.Lib.Integers.Int64.eq x
        CompCert4Lean.Lib.Integers.Int64.zero =
      CompCert4Lean.Lib.Integers.Int.eq
        (CompCert4Lean.Lib.Integers.Int.or
          (CompCert4Lean.Lib.Integers.Int64.hiword x)
          (CompCert4Lean.Lib.Integers.Int64.loword x))
        CompCert4Lean.Lib.Integers.Int.zero := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    have hxv := splitlong_int64_eq_zero_iff x |>.mp hx
    apply (splitlong_int_eq_zero_iff _).mpr
    rw [test_int_or_val]
    apply (test_nat_lor_zero _ _).mpr
    constructor
    · rw [splitlong_hiword_val, hxv]
    · rw [splitlong_loword_val, hxv]
  · intro ho
    have hov := splitlong_int_eq_zero_iff _ |>.mp ho
    rw [test_int_or_val] at hov
    obtain ⟨hh, hl⟩ := (test_nat_lor_zero _ _).mp hov
    apply (splitlong_int64_eq_zero_iff _).mpr
    have hsum := Nat.div_add_mod x.val (2 ^ 32)
    have hh' : x.val / 2 ^ 32 = 0 := by
      rw [← splitlong_hiword_val]
      simpa [test_int_zero_val] using hh
    have hl' : x.val % 2 ^ 32 = 0 := by
      rw [← splitlong_loword_val]
      simpa [test_int_zero_val] using hl
    simpa [hh', hl'] using hsum.symm

private theorem splitlong_eval_cmpl_default
    (xi : ExternalCalls) (ge : SLGenv) (sp : SLVal) (e : SLEnv) (m : SLMem)
    (le : letenv) (a : expr) (x : CompCert4Lean.Lib.Integers.int64)
    (ha : eval_expr xi ge sp e m le a (.Vlong x)) :
    eval_expr xi ge sp e m le
      (Elet a
        (CompCert4Lean.X86.SelectOp.comp .Ceq
          (CompCert4Lean.X86.SelectOp.or
            (Eop Ohighlong (Econs (Eletvar 0) Enil))
            (Eop Olowlong (Econs (Eletvar 0) Enil)))
          (Eop (Ointconst (CompCert4Lean.Lib.Integers.Int.zero)) Enil)))
      (CompCert4Lean.Common.Values.Val.of_bool
        (CompCert4Lean.Lib.Integers.Int64.eq x
          CompCert4Lean.Lib.Integers.Int64.zero)) := by
  apply eval_expr.eval_Elet le a _ (.Vlong x) _ ha
  change List CompCert4Lean.Common.Values.val at le
  have hhigh : eval_expr xi ge sp e m (.Vlong x :: le)
      (Eop Ohighlong (Econs (Eletvar 0) Enil))
      (.Vint (CompCert4Lean.Lib.Integers.Int64.hiword x)) := by
    apply eval_expr.eval_Eop (le := .Vlong x :: le)
      (op := Ohighlong) (al := Econs (Eletvar 0) Enil)
      (vl := [.Vlong x])
    · exact eval_exprlist.cons (.Vlong x :: le) (Eletvar 0) Enil
        (.Vlong x) []
        (eval_expr.eval_Eletvar (.Vlong x :: le) 0 (.Vlong x) (by rfl))
        (eval_exprlist.nil (.Vlong x :: le))
    · rfl
  have hlow : eval_expr xi ge sp e m (.Vlong x :: le)
      (Eop Olowlong (Econs (Eletvar 0) Enil))
      (.Vint (CompCert4Lean.Lib.Integers.Int64.loword x)) := by
    apply eval_expr.eval_Eop (le := .Vlong x :: le)
      (op := Olowlong) (al := Econs (Eletvar 0) Enil)
      (vl := [.Vlong x])
    · exact eval_exprlist.cons (.Vlong x :: le) (Eletvar 0) Enil
        (.Vlong x) []
        (eval_expr.eval_Eletvar (.Vlong x :: le) 0 (.Vlong x) (by rfl))
        (eval_exprlist.nil (.Vlong x :: le))
    · rfl
  obtain ⟨v, hv, hvval⟩ := splitlong_eval_orcomp xi ge sp e m
    (.Vlong x :: le)
    (Eop Ohighlong (Econs (Eletvar 0) Enil))
    (Eop Olowlong (Econs (Eletvar 0) Enil))
    (CompCert4Lean.Lib.Integers.Int64.hiword x)
    (CompCert4Lean.Lib.Integers.Int64.loword x) hhigh hlow
  exact splitlong_cmpl_zero_bool x ▸ hvval ▸ hv

private theorem splitlong_eval_cmpl_shape
    (xi : ExternalCalls) (ge : SLGenv) (sp : SLVal) (e : SLEnv) (m : SLMem)
    (le : letenv) (h l : expr) (x : CompCert4Lean.Lib.Integers.int64)
    (ha : eval_expr xi ge sp e m le
      (Eop Omakelong (Econs h (Econs l Enil))) (.Vlong x)) :
    eval_expr xi ge sp e m le
      (CompCert4Lean.X86.SelectOp.comp .Ceq
        (CompCert4Lean.X86.SelectOp.or h l)
        (Eop (Ointconst (CompCert4Lean.Lib.Integers.Int.zero)) Enil))
      (CompCert4Lean.Common.Values.Val.of_bool
        (CompCert4Lean.Lib.Integers.Int64.eq x
          CompCert4Lean.Lib.Integers.Int64.zero)) := by
  obtain ⟨vl, hargs, hop⟩ := splitlong_eval_eop_inv xi ge sp e m le
    Omakelong (Econs h (Econs l Enil)) (.Vlong x) ha
  obtain ⟨v1, vl', hvl, hh, ht⟩ := splitlong_eval_cons_inv xi ge sp e m le
    h (Econs l Enil) vl hargs
  obtain ⟨v2, vl2, hvl', hl, ht2⟩ := splitlong_eval_cons_inv xi ge sp e m le
    l Enil vl' ht
  have hnil := splitlong_eval_nil_inv xi ge sp e m le vl2 ht2
  rw [hvl, hvl', hnil] at hop
  change some (CompCert4Lean.Common.Values.Val.longofwords v1 v2) =
    some (CompCert4Lean.Common.Values.val.Vlong x) at hop
  cases v1 with
  | Vint p =>
      cases v2 with
      | Vint q =>
          change some (CompCert4Lean.Common.Values.val.Vlong
            (CompCert4Lean.Lib.Integers.Int64.ofwords p q)) =
            some (CompCert4Lean.Common.Values.val.Vlong x) at hop
          cases hop
          obtain ⟨v, hv, hvval⟩ := splitlong_eval_orcomp xi ge sp e m le
            h l p q hh hl
          have hbool := decompose_cmpl_eq_zero p q
          have hbool' := congrArg
            CompCert4Lean.Common.Values.Val.of_bool hbool
          rw [hbool', ← hvval]
          exact hv
      | Vundef => simp [CompCert4Lean.Common.Values.Val.longofwords] at hop
      | Vlong _ => simp [CompCert4Lean.Common.Values.Val.longofwords] at hop
      | Vfloat _ => simp [CompCert4Lean.Common.Values.Val.longofwords] at hop
      | Vsingle _ => simp [CompCert4Lean.Common.Values.Val.longofwords] at hop
      | Vptr _ _ => simp [CompCert4Lean.Common.Values.Val.longofwords] at hop
  | Vundef => simp [CompCert4Lean.Common.Values.Val.longofwords] at hop
  | Vlong _ => simp [CompCert4Lean.Common.Values.Val.longofwords] at hop
  | Vfloat _ => simp [CompCert4Lean.Common.Values.Val.longofwords] at hop
  | Vsingle _ => simp [CompCert4Lean.Common.Values.Val.longofwords] at hop
  | Vptr _ _ => simp [CompCert4Lean.Common.Values.Val.longofwords] at hop

end CompCert4Lean.Backend.SplitLongproof

namespace CompCert4Lean.Backend.SplitLongproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.SplitLong
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op

variable
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 53)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 24)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 128)]

theorem eval_cmpl_eq_zero : eval_cmpl_eq_zeroStatement := by
  intro xi prog sp e m le a x ha
  unfold cmpl_eq_zero
  cases hmatch : splitlong_match a with
  | splitlong_case1 h l =>
      exact splitlong_eval_cmpl_shape xi (Genv.globalenv prog) sp e m le h l x
        (by simpa [hmatch] using ha)
  | splitlong_default =>
      simpa [splitlong, hmatch] using
        (splitlong_eval_cmpl_default xi (Genv.globalenv prog) sp e m le a x
          (by simpa [hmatch] using ha))

end CompCert4Lean.Backend.SplitLongproof

namespace CompCert4Lean.Backend.SplitLongproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.SplitLong
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op

variable
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 53)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 24)
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 128)]

private theorem splitlong_eval_orcomp_ne
    (xi : ExternalCalls) (ge : CompCert4Lean.Backend.CminorSel.genv)
    (sp : CompCert4Lean.Common.Values.val) (e : CompCert4Lean.Backend.Cminor.env)
    (m : CompCert4Lean.Common.Memory.mem) (le : letenv)
    (h l : expr) (p q : CompCert4Lean.Lib.Integers.int)
    (hh : eval_expr xi ge sp e m le h (.Vint p))
    (hl : eval_expr xi ge sp e m le l (.Vint q)) :
    ∃ v, eval_expr xi ge sp e m le
      (CompCert4Lean.X86.SelectOp.comp .Cne
        (CompCert4Lean.X86.SelectOp.or h l)
        (Eop (Ointconst (CompCert4Lean.Lib.Integers.Int.zero)) Enil)) v ∧
      v = CompCert4Lean.Common.Values.Val.of_bool
        (!(CompCert4Lean.Lib.Integers.Int.eq
          (CompCert4Lean.Lib.Integers.Int.or p q)
          CompCert4Lean.Lib.Integers.Int.zero)) := by
  obtain ⟨vo, ho, hdo⟩ := CompCert4Lean.X86.SelectOpproof.eval_or
    xi ge sp e m le h (.Vint p) l (.Vint q) hh hl
  have hdo' : vo = .Vint (CompCert4Lean.Lib.Integers.Int.or p q) := by
    cases hdo
    simp [CompCert4Lean.Common.Values.Val.or]
  subst vo
  have hz : eval_expr xi ge sp e m le
      (Eop (Ointconst (CompCert4Lean.Lib.Integers.Int.zero)) Enil)
      (.Vint (CompCert4Lean.Lib.Integers.Int.zero)) := by
    apply eval_expr.eval_Eop (le := le)
      (op := Ointconst (CompCert4Lean.Lib.Integers.Int.zero))
      (al := Enil) (vl := [])
    · exact eval_exprlist.nil le
    · rfl
  obtain ⟨vc, hc, hdc⟩ := CompCert4Lean.X86.SelectOpproof.eval_comp
    xi ge sp e m .Cne le (CompCert4Lean.X86.SelectOp.or h l)
      (.Vint (CompCert4Lean.Lib.Integers.Int.or p q))
      (Eop (Ointconst (CompCert4Lean.Lib.Integers.Int.zero)) Enil)
      (.Vint (CompCert4Lean.Lib.Integers.Int.zero)) ho hz
  have hsrc : CompCert4Lean.Common.Values.Val.cmp .Cne
      (.Vint (CompCert4Lean.Lib.Integers.Int.or p q))
      (.Vint (CompCert4Lean.Lib.Integers.Int.zero)) =
      CompCert4Lean.Common.Values.Val.of_bool
        (!(CompCert4Lean.Lib.Integers.Int.eq
          (CompCert4Lean.Lib.Integers.Int.or p q)
          CompCert4Lean.Lib.Integers.Int.zero)) := by
    cases h : decide ((CompCert4Lean.Lib.Integers.Int.or p q).intval =
        CompCert4Lean.Lib.Integers.Int.zero.intval) <;>
      simp [CompCert4Lean.Common.Values.Val.cmp,
        CompCert4Lean.Common.Values.Val.cmp_bool,
        CompCert4Lean.Common.Values.Val.of_optbool,
        CompCert4Lean.Common.Values.Val.of_bool,
        CompCert4Lean.Lib.Integers.Int.cmp,
        CompCert4Lean.Lib.Integers.WordCore.cmp,
        CompCert4Lean.Lib.Integers.Int.eq,
        CompCert4Lean.Lib.Integers.WordCore.eq, h]
  rw [hsrc] at hdc
  refine ⟨vc, hc, ?_⟩
  cases heq : CompCert4Lean.Lib.Integers.Int.eq
      (CompCert4Lean.Lib.Integers.Int.or p q)
      (CompCert4Lean.Lib.Integers.Int.zero) with
  | false =>
      simp [CompCert4Lean.Common.Values.Val.of_bool, heq] at hdc ⊢
      cases hdc <;> rfl
  | true =>
      simp [CompCert4Lean.Common.Values.Val.of_bool, heq] at hdc ⊢
      cases hdc <;> rfl

private theorem splitlong_eval_cmpl_ne_default
    (xi : ExternalCalls) (ge : CompCert4Lean.Backend.CminorSel.genv)
    (sp : CompCert4Lean.Common.Values.val) (e : CompCert4Lean.Backend.Cminor.env)
    (m : CompCert4Lean.Common.Memory.mem) (le : letenv) (a : expr)
    (x : CompCert4Lean.Lib.Integers.int64)
    (ha : eval_expr xi ge sp e m le a (.Vlong x)) :
    eval_expr xi ge sp e m le
      (Elet a
        (CompCert4Lean.X86.SelectOp.comp .Cne
          (CompCert4Lean.X86.SelectOp.or
            (Eop Ohighlong (Econs (Eletvar 0) Enil))
            (Eop Olowlong (Econs (Eletvar 0) Enil)))
          (Eop (Ointconst (CompCert4Lean.Lib.Integers.Int.zero)) Enil)))
      (CompCert4Lean.Common.Values.Val.of_bool
        (!(CompCert4Lean.Lib.Integers.Int64.eq x
          CompCert4Lean.Lib.Integers.Int64.zero))) := by
  apply eval_expr.eval_Elet le a _ (.Vlong x) _ ha
  change List CompCert4Lean.Common.Values.val at le
  have hhigh : eval_expr xi ge sp e m (.Vlong x :: le)
      (Eop Ohighlong (Econs (Eletvar 0) Enil))
      (.Vint (CompCert4Lean.Lib.Integers.Int64.hiword x)) := by
    apply eval_expr.eval_Eop (le := .Vlong x :: le)
      (op := Ohighlong) (al := Econs (Eletvar 0) Enil)
      (vl := [.Vlong x])
    · exact eval_exprlist.cons (.Vlong x :: le) (Eletvar 0) Enil
        (.Vlong x) []
        (eval_expr.eval_Eletvar (.Vlong x :: le) 0 (.Vlong x) (by rfl))
        (eval_exprlist.nil (.Vlong x :: le))
    · rfl
  have hlow : eval_expr xi ge sp e m (.Vlong x :: le)
      (Eop Olowlong (Econs (Eletvar 0) Enil))
      (.Vint (CompCert4Lean.Lib.Integers.Int64.loword x)) := by
    apply eval_expr.eval_Eop (le := .Vlong x :: le)
      (op := Olowlong) (al := Econs (Eletvar 0) Enil)
      (vl := [.Vlong x])
    · exact eval_exprlist.cons (.Vlong x :: le) (Eletvar 0) Enil
        (.Vlong x) []
        (eval_expr.eval_Eletvar (.Vlong x :: le) 0 (.Vlong x) (by rfl))
        (eval_exprlist.nil (.Vlong x :: le))
    · rfl
  obtain ⟨v, hv, hvval⟩ := splitlong_eval_orcomp_ne xi ge sp e m
    (.Vlong x :: le)
    (Eop Ohighlong (Econs (Eletvar 0) Enil))
    (Eop Olowlong (Econs (Eletvar 0) Enil))
    (CompCert4Lean.Lib.Integers.Int64.hiword x)
    (CompCert4Lean.Lib.Integers.Int64.loword x) hhigh hlow
  have hbool := congrArg Bool.not (splitlong_cmpl_zero_bool x)
  have hbool' := congrArg CompCert4Lean.Common.Values.Val.of_bool hbool
  rw [hbool', ← hvval]
  exact hv

private theorem splitlong_eval_cmpl_ne_shape
    (xi : ExternalCalls) (ge : CompCert4Lean.Backend.CminorSel.genv)
    (sp : CompCert4Lean.Common.Values.val) (e : CompCert4Lean.Backend.Cminor.env)
    (m : CompCert4Lean.Common.Memory.mem) (le : letenv) (h l : expr)
    (x : CompCert4Lean.Lib.Integers.int64)
    (ha : eval_expr xi ge sp e m le
      (Eop Omakelong (Econs h (Econs l Enil))) (.Vlong x)) :
    eval_expr xi ge sp e m le
      (CompCert4Lean.X86.SelectOp.comp .Cne
        (CompCert4Lean.X86.SelectOp.or h l)
        (Eop (Ointconst (CompCert4Lean.Lib.Integers.Int.zero)) Enil))
      (CompCert4Lean.Common.Values.Val.of_bool
        (!(CompCert4Lean.Lib.Integers.Int64.eq x
          CompCert4Lean.Lib.Integers.Int64.zero))) := by
  obtain ⟨vl, hargs, hop⟩ := splitlong_eval_eop_inv xi ge sp e m le
    Omakelong (Econs h (Econs l Enil)) (.Vlong x) ha
  obtain ⟨v1, vl', hvl, hh, ht⟩ := splitlong_eval_cons_inv xi ge sp e m le
    h (Econs l Enil) vl hargs
  obtain ⟨v2, vl2, hvl', hl, ht2⟩ := splitlong_eval_cons_inv xi ge sp e m le
    l Enil vl' ht
  have hnil := splitlong_eval_nil_inv xi ge sp e m le vl2 ht2
  rw [hvl, hvl', hnil] at hop
  change some (CompCert4Lean.Common.Values.Val.longofwords v1 v2) =
    some (CompCert4Lean.Common.Values.val.Vlong x) at hop
  cases v1 with
  | Vint p =>
      cases v2 with
      | Vint q =>
          change some (CompCert4Lean.Common.Values.val.Vlong
            (CompCert4Lean.Lib.Integers.Int64.ofwords p q)) =
            some (CompCert4Lean.Common.Values.val.Vlong x) at hop
          cases hop
          obtain ⟨v, hv, hvval⟩ := splitlong_eval_orcomp_ne xi ge sp e m le
            h l p q hh hl
          have hbool := congrArg Bool.not (decompose_cmpl_eq_zero p q)
          have hbool' := congrArg
            CompCert4Lean.Common.Values.Val.of_bool hbool
          rw [hbool', ← hvval]
          exact hv
      | Vundef => simp [CompCert4Lean.Common.Values.Val.longofwords] at hop
      | Vlong _ => simp [CompCert4Lean.Common.Values.Val.longofwords] at hop
      | Vfloat _ => simp [CompCert4Lean.Common.Values.Val.longofwords] at hop
      | Vsingle _ => simp [CompCert4Lean.Common.Values.Val.longofwords] at hop
      | Vptr _ _ => simp [CompCert4Lean.Common.Values.Val.longofwords] at hop
  | Vundef => simp [CompCert4Lean.Common.Values.Val.longofwords] at hop
  | Vlong _ => simp [CompCert4Lean.Common.Values.Val.longofwords] at hop
  | Vfloat _ => simp [CompCert4Lean.Common.Values.Val.longofwords] at hop
  | Vsingle _ => simp [CompCert4Lean.Common.Values.Val.longofwords] at hop
  | Vptr _ _ => simp [CompCert4Lean.Common.Values.Val.longofwords] at hop

theorem eval_cmpl_ne_zero : eval_cmpl_ne_zeroStatement := by
  intro xi prog sp e m le a x ha
  unfold cmpl_ne_zero
  cases hmatch : splitlong_match a with
  | splitlong_case1 h l =>
      exact splitlong_eval_cmpl_ne_shape xi (Genv.globalenv prog) sp e m le h l x
        (by simpa [hmatch] using ha)
  | splitlong_default =>
      simpa [splitlong, hmatch] using
        (splitlong_eval_cmpl_ne_default xi (Genv.globalenv prog) sp e m le a x
          (by simpa [hmatch] using ha))

end CompCert4Lean.Backend.SplitLongproof

namespace CompCert4Lean.Backend.SplitLongproof

theorem int64_eq_xor : int64_eq_xorStatement := by
  intro p q
  have hzero_val : CompCert4Lean.Lib.Integers.Int64.zero.val = 0 := by
    change (CompCert4Lean.Lib.Integers.WordCore.repr 64
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0).val = 0
    rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 0 by rfl,
      test_repr_zOfNat]
  by_cases hpq : p = q
  · subst q
    have hxor : CompCert4Lean.Lib.Integers.Int64.xor p p =
        CompCert4Lean.Lib.Integers.Int64.zero := by
      apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
      change
        (CompCert4Lean.Lib.Integers.Int64.xor p p).val =
          CompCert4Lean.Lib.Integers.Int64.zero.val
      unfold CompCert4Lean.Lib.Integers.Int64.xor
        CompCert4Lean.Lib.Integers.WordCore.xor
      rw [test_repr_zOfNat]
      rw [hzero_val]
      change Nat.xor p.val p.val % 2 ^ 64 = 0
      rw [Nat.xor_eq, Nat.xor_self, Nat.zero_mod]
    simp [int64Eq, CompCert4Lean.Lib.Integers.Int64.eq,
      CompCert4Lean.Lib.Integers.WordCore.eq, hxor]
  · have hpval : p.intval ≠ q.intval := by
      intro h
      exact hpq (CompCert4Lean.Lib.Integers.WordCore.ext h)
    have hxzero : CompCert4Lean.Lib.Integers.Int64.xor p q ≠
        CompCert4Lean.Lib.Integers.Int64.zero := by
      intro h
      have hval : (CompCert4Lean.Lib.Integers.Int64.xor p q).val =
          CompCert4Lean.Lib.Integers.Int64.zero.val := by
        rw [h]
      unfold CompCert4Lean.Lib.Integers.Int64.xor
        CompCert4Lean.Lib.Integers.WordCore.xor at hval
      rw [test_repr_zOfNat] at hval
      rw [hzero_val] at hval
      change Nat.xor p.val q.val % 2 ^ 64 = 0 at hval
      have hxorlt : Nat.xor p.val q.val < 2 ^ CompCert4Lean.Lib.Integers.Int64.wordsize :=
        Nat.xor_lt_two_pow p.toFin.isLt q.toFin.isLt
      have hxor : Nat.xor p.val q.val = 0 := by
        rw [Nat.mod_eq_of_lt (by simpa [CompCert4Lean.Lib.Integers.Int64.wordsize] using hxorlt)] at hval
        exact hval
      have hpval' : p.val = q.val := by
        apply Nat.eq_of_testBit_eq
        intro i
        have hi : (Nat.xor p.val q.val).testBit i = false := by
          rw [hxor]
          simp
        rw [Nat.xor_eq, Nat.testBit_xor] at hi
        by_cases hpi : p.val.testBit i <;>
          by_cases hqi : q.val.testBit i <;> simp [hpi, hqi] at hi ⊢
      exact hpq (CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq hpval')
    have hxvalzero : (CompCert4Lean.Lib.Integers.Int64.xor p q).intval ≠
        CompCert4Lean.Lib.Integers.Int64.zero.intval := by
      intro h
      exact hxzero (CompCert4Lean.Lib.Integers.WordCore.ext h)
    simp [int64Eq, CompCert4Lean.Lib.Integers.Int64.eq,
      CompCert4Lean.Lib.Integers.WordCore.eq, hpval, hxvalzero]

end CompCert4Lean.Backend.SplitLongproof
