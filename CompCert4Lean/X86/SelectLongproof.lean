import CompCert4Lean.Backend.SplitLongproof
import CompCert4Lean.Common.ExternalCalls
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Memory
import CompCert4Lean.X86.SelectLong

/-!
# Correctness surface for x86 long-integer instruction selection

The source file is proof-heavy.  This migration pass keeps the four
constructor-soundness predicates executable and records the remaining proof
contracts as transparent proposition descriptors.
-/

namespace CompCert4Lean.X86.SelectLongproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.SelectLong

private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev CCInt64 := CompCert4Lean.Lib.Integers.int64
private abbrev comparison := CompCert4Lean.Lib.Integers.comparison
private abbrev env := CompCert4Lean.Backend.Cminor.env
private abbrev HelperFunctions := CompCert4Lean.Backend.SplitLong.helper_functions
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

def unary_constructor_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (prog : program) (sp : val)
    (e : env) (m : mem) (cstr : expr → expr) (sem : val → val) : Prop :=
  ∀ (le : letenv) (a : expr) (x : val),
    eval_expr (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (cstr a) v ∧
        Val.lessdef (sem x) v

def binary_constructor_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (prog : program) (sp : val)
    (e : env) (m : mem) (cstr : expr → expr → expr)
    (sem : val → val → val) : Prop :=
  ∀ (le : letenv) (a : expr) (x : val) (b : expr) (y : val),
    eval_expr (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
    eval_expr (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le b y →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (cstr a b) v ∧
        Val.lessdef (sem x y) v

def partial_unary_constructor_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (prog : program) (sp : val)
    (e : env) (m : mem) (cstr : expr → expr) (sem : val → Option val) : Prop :=
  ∀ (le : letenv) (a : expr) (x y : val),
    eval_expr (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
    sem x = some y →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (cstr a) v ∧
        Val.lessdef y v

def partial_binary_constructor_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (prog : program) (sp : val)
    (e : env) (m : mem) (cstr : expr → expr → expr)
    (sem : val → val → Option val) : Prop :=
  ∀ (le : letenv) (a : expr) (x : val) (b : expr) (y z : val),
    eval_expr (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
    eval_expr (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le b y →
    sem x y = some z →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (cstr a b) v ∧
        Val.lessdef z v

/-! ## Exact statement descriptors for later proof migration -/

def eval_addlStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m addl Val.addl

def eval_addlimmStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem)
    (n : CCInt64),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m (addlimm n)
      (fun v => Val.addl v (.Vlong n))

def eval_andlStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m andl Val.andl

def eval_andlimmStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem)
    (n : CCInt64),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m (andlimm n)
      (fun v => Val.andl v (.Vlong n))

def eval_cmplStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem)
    (c : comparison) (le : letenv) (a : expr) (x : val) (b : expr) (y v : val),
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le b y →
    Val.cmpl c x y = some v →
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (cmpl c a b) v

def eval_cmpluStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem)
    (c : comparison) (le : letenv) (a : expr) (x : val) (b : expr) (y v : val),
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le b y →
    Val.cmplu (Mem.valid_pointer m) c x y = some v →
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (cmplu c a b) v

def eval_divls_baseStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : HelperFunctions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    partial_binary_constructor_sound (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi prog sp e m divls_base Val.divls

def eval_divlu_baseStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : HelperFunctions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    partial_binary_constructor_sound (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi prog sp e m divlu_base Val.divlu

def eval_floatoflongStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : HelperFunctions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem)
      (le : letenv) (a : expr) (x y : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      Val.floatoflong x = some y →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (floatoflong a) v ∧
        Val.lessdef y v

def eval_intoflongStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m intoflong Val.loword

def eval_longconstStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem)
    (le : letenv) (n : CCInt64),
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (longconst n) (.Vlong n)

def eval_longoffloatStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : HelperFunctions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem)
      (le : letenv) (a : expr) (x y : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      Val.longoffloat x = some y →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (longoffloat a) v ∧
        Val.lessdef y v

def eval_longofintStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m longofint Val.longofint

def eval_longofintuStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m longofintu Val.longofintu

def eval_longofsingleStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : HelperFunctions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem)
      (le : letenv) (a : expr) (x y : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      Val.longofsingle x = some y →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (longofsingle a) v ∧
        Val.lessdef y v

def eval_modls_baseStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : HelperFunctions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    partial_binary_constructor_sound (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi prog sp e m modls_base Val.modls

def eval_modlu_baseStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : HelperFunctions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
    partial_binary_constructor_sound (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi prog sp e m modlu_base Val.modlu

def eval_mullStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : HelperFunctions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
      binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m mull Val.mull

def eval_mullhsStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : HelperFunctions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem) (n : CCInt64),
      unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m
        (fun a => mullhs a n) (fun v => Val.mullhs v (.Vlong n))

def eval_mullhuStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : HelperFunctions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem) (n : CCInt64),
      unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m
        (fun a => mullhu a n) (fun v => Val.mullhu v (.Vlong n))

def eval_mullimmStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : HelperFunctions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem) (n : CCInt64),
      unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m (mullimm n)
        (fun v => Val.mull v (.Vlong n))

def eval_mullimm_baseStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : HelperFunctions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem) (n : CCInt64),
      unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m (mullimm_base n)
        (fun v => Val.mull v (.Vlong n))

def eval_neglStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m negl Val.negl

def eval_notlStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m notl Val.notl

def eval_orlStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m orl Val.orl

def eval_orlimmStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem)
    (n : CCInt64),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m (orlimm n)
      (fun v => Val.orl v (.Vlong n))

def eval_shllStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : HelperFunctions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
      binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m shll Val.shll

def eval_shllimmStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : HelperFunctions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem) (n : CCInt),
      unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m
        (fun e => shllimm e n) (fun v => Val.shll v (.Vint n))

def eval_shrlStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : HelperFunctions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
      binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m shrl Val.shrl

def eval_shrlimmStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : HelperFunctions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem) (n : CCInt),
      unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m
        (fun e => shrlimm e n) (fun v => Val.shrl v (.Vint n))

def eval_shrluStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : HelperFunctions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
      binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m shrlu Val.shrlu

def eval_shrluimmStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : HelperFunctions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem) (n : CCInt),
      unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m
        (fun e => shrluimm e n) (fun v => Val.shrlu v (.Vint n))

def eval_shrxlimmStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : HelperFunctions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem)
      (le : letenv) (a : expr) (n : CCInt) (x z : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      Val.shrxl x (.Vint n) = some z →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (shrxlimm a n) v ∧
        Val.lessdef z v

def eval_singleoflongStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (hf : HelperFunctions),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem)
      (le : letenv) (a : expr) (x y : val),
      eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
      Val.singleoflong x = some y →
      ∃ v, eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le (singleoflong a) v ∧
        Val.lessdef y v

def eval_sublStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m subl Val.subl

def eval_xorlStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    binary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m xorl Val.xorl

def eval_xorlimmStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem)
    (n : CCInt64),
    unary_constructor_sound (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi prog sp e m (xorlimm n)
      (fun v => Val.xorl v (.Vlong n))

def is_longconst_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem)
    (x : val) (a : expr) (n : CCInt64) (le : letenv),
    is_longconst a = some n →
    eval_expr (binary64_certificate := binary64_certificate) (binary32_certificate := binary32_certificate) xi (Genv.globalenv prog) sp e m le a x →
    x = .Vlong n

end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof

theorem eval_longconst
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_longconstStatement := by
  intro xi prog sp e m le n
  exact CompCert4Lean.Backend.CminorSel.eval_expr.eval_Eop le (.Olongconst n) (.Enil) []
    (.Vlong n) (CompCert4Lean.Backend.CminorSel.eval_exprlist.nil le) rfl

end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong

theorem is_longconst_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @is_longconst_soundStatement binary64_certificate binary32_certificate := by
  unfold is_longconst_soundStatement
  intro xi prog sp env0 mem0 val0 expr0 int64n lenv hconst heval
  have ha : expr0 = Eop (Olongconst int64n) Enil := by
    cases expr0 with
    | Evar id => simp [is_longconst] at hconst
    | Eop op args =>
        cases op <;> cases args <;> simp [is_longconst] at hconst ⊢ <;> cases hconst <;> rfl
    | Eload chunk addr args => simp [is_longconst] at hconst
    | Econdition c b d => simp [is_longconst] at hconst
    | Elet b d => simp [is_longconst] at hconst
    | Eletvar i => simp [is_longconst] at hconst
    | Ebuiltin ef args => simp [is_longconst] at hconst
    | Eexternal id sg args => simp [is_longconst] at hconst
  subst expr0
  cases heval with
  | eval_Eop _ _ _ vl _ hargs hop =>
      cases hargs
      change some (CompCert4Lean.Common.Values.val.Vlong int64n) = some val0 at hop
      cases hop
      rfl

end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong

theorem eval_intoflong
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_intoflongStatement binary64_certificate binary32_certificate := by
  unfold eval_intoflongStatement unary_constructor_sound
  intro xi prog sp e m le a x h
  unfold intoflong
  cases hmatch : is_longconst a with
  | some n =>
      simp only [hmatch]
      refine ⟨.Vint (CompCert4Lean.Lib.Integers.Int.repr (CompCert4Lean.Lib.Integers.Int64.unsigned n)), ?_, ?_⟩
      · apply eval_expr.eval_Eop le (Ointconst _) Enil [] _ (eval_exprlist.nil le)
        rfl
      · rw [is_longconst_sound xi prog sp e m x a n le hmatch h]
        exact Val.lessdef_refl _
  | none =>
      simp only [hmatch]
      refine ⟨Val.loword x, ?_, .lessdef_refl _⟩
      apply eval_expr.eval_Eop le Olowlong (Econs a Enil) [x] _
      · apply eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)
      · rfl

end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof
open CompCert4Lean.Common.AST CompCert4Lean.Common.Values CompCert4Lean.Backend.CminorSel CompCert4Lean.X86.Op CompCert4Lean.X86.SelectLong
theorem eval_longofintu
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_longofintuStatement binary64_certificate binary32_certificate := by
  unfold eval_longofintuStatement unary_constructor_sound
  intro xi prog sp e m le a x h
  unfold longofintu
  cases hmatch : CompCert4Lean.Backend.SplitLong.is_intconst a with
  | none =>
      refine ⟨Val.longofintu x, ?_, Val.lessdef_refl _⟩
      apply eval_expr.eval_Eop le Ocast32unsigned (Econs a Enil) [x] _
      · exact eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)
      · rfl
  | some n =>
      refine ⟨.Vlong (CompCert4Lean.Lib.Integers.Int64.repr (CompCert4Lean.Lib.Integers.Int.unsigned n)), ?_, ?_⟩
      · apply eval_expr.eval_Eop le (Olongconst _) Enil [] _ (eval_exprlist.nil le); rfl
      · have ha : a = Eop (Ointconst n) Enil := by
          cases a with
          | Evar id => simp [CompCert4Lean.Backend.SplitLong.is_intconst] at hmatch
          | Eop op args =>
              cases op <;> cases args <;>
                simp [CompCert4Lean.Backend.SplitLong.is_intconst] at hmatch ⊢ <;>
                try { cases hmatch; rfl }
          | Eload chunk addr args => simp [CompCert4Lean.Backend.SplitLong.is_intconst] at hmatch
          | Econdition c b d => simp [CompCert4Lean.Backend.SplitLong.is_intconst] at hmatch
          | Elet b d => simp [CompCert4Lean.Backend.SplitLong.is_intconst] at hmatch
          | Eletvar i => simp [CompCert4Lean.Backend.SplitLong.is_intconst] at hmatch
          | Ebuiltin ef args => simp [CompCert4Lean.Backend.SplitLong.is_intconst] at hmatch
          | Eexternal id sg args => simp [CompCert4Lean.Backend.SplitLong.is_intconst] at hmatch
        subst a
        cases h with
        | eval_Eop _ _ _ _ _ hargs hop =>
            cases hargs
            change some (.Vint n) = some x at hop
            cases hop
            exact Val.lessdef_refl _
end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong

theorem eval_longofint
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_longofintStatement binary64_certificate binary32_certificate := by
  unfold eval_longofintStatement unary_constructor_sound
  intro xi prog sp e m le a x h
  unfold longofint
  cases hmatch : CompCert4Lean.Backend.SplitLong.is_intconst a with
  | none =>
      refine ⟨Val.longofint x, ?_, Val.lessdef_refl _⟩
      apply eval_expr.eval_Eop le Ocast32signed (Econs a Enil) [x] _
      · exact eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)
      · rfl
  | some n =>
      refine ⟨.Vlong (CompCert4Lean.Lib.Integers.Int64.repr (CompCert4Lean.Lib.Integers.Int.signed n)), ?_, ?_⟩
      · apply eval_expr.eval_Eop le (Olongconst _) Enil [] _ (eval_exprlist.nil le)
        rfl
      · have ha : a = Eop (Ointconst n) Enil := by
          cases a with
          | Evar id => simp [CompCert4Lean.Backend.SplitLong.is_intconst] at hmatch
          | Eop op args =>
              cases op <;> cases args <;>
                simp [CompCert4Lean.Backend.SplitLong.is_intconst] at hmatch ⊢ <;>
                try { cases hmatch; rfl }
          | Eload chunk addr args => simp [CompCert4Lean.Backend.SplitLong.is_intconst] at hmatch
          | Econdition c b d => simp [CompCert4Lean.Backend.SplitLong.is_intconst] at hmatch
          | Elet b d => simp [CompCert4Lean.Backend.SplitLong.is_intconst] at hmatch
          | Eletvar i => simp [CompCert4Lean.Backend.SplitLong.is_intconst] at hmatch
          | Ebuiltin ef args => simp [CompCert4Lean.Backend.SplitLong.is_intconst] at hmatch
          | Eexternal id sg args => simp [CompCert4Lean.Backend.SplitLong.is_intconst] at hmatch
        subst a
        cases h with
        | eval_Eop _ _ _ _ _ hargs hop =>
            cases hargs
            change some (.Vint n) = some x at hop
            cases hop
            exact Val.lessdef_refl _

end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong

open Lean Elab Tactic Meta

private def suffixPrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem suffixWordValRepr64 (bits : Nat) (i : Int) :
    (CompCert4Lean.Lib.Integers.WordCore.repr bits
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt i)).val =
      Int.toNat (i % ((2 ^ bits : Nat) : Int)) := by
  run_tac
    let lctx ← getLCtx
    let bitsF := (lctx.findFromUserName? `bits).get!
    let iF := (lctx.findFromUserName? `i).get!
    let bitsE := mkFVar bitsF.fvarId
    let iE := mkFVar iF.fvarId
    let e ← mkAppM
      (suffixPrivateName "CompCert4Lean.Lib.Integers.WordCore.val_repr")
      #[bitsE, iE]
    closeMainGoal Name.anonymous e

private theorem repr_val_of_lt64 (n : Nat) (hn : n < 2 ^ 64) :
    (CompCert4Lean.Lib.Integers.WordCore.repr 64
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)).val = n := by
  rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat n) by rfl,
    suffixWordValRepr64]
  have hmod :
      Int.ofNat n % ((2 ^ 64 : Nat) : Int) = Int.ofNat n := by
    apply Int.emod_eq_of_lt
    · exact Int.natCast_nonneg n
    · exact Int.ofNat_lt.mpr hn
  rw [hmod]
  rfl

private theorem not_val64 (n : CompCert4Lean.Lib.Integers.int64) :
    (CompCert4Lean.Lib.Integers.Int64.not n).val =
      Nat.xor n.val (2 ^ 64 - 1) := by
  unfold CompCert4Lean.Lib.Integers.Int64.not
    CompCert4Lean.Lib.Integers.WordCore.not
  apply repr_val_of_lt64
  apply Nat.xor_lt_two_pow
  · exact n.toFin.isLt
  · change 2 ^ 64 - 1 < 2 ^ 64
    have hp : 0 < 2 ^ (64 : Nat) := Nat.two_pow_pos _
    omega

private theorem not64_involutive (n : CompCert4Lean.Lib.Integers.int64) :
    CompCert4Lean.Lib.Integers.Int64.not
        (CompCert4Lean.Lib.Integers.Int64.not n) = n := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [not_val64, not_val64]
  calc
    Nat.xor (Nat.xor n.val (2 ^ 64 - 1)) (2 ^ 64 - 1) =
        Nat.xor n.val (Nat.xor (2 ^ 64 - 1) (2 ^ 64 - 1)) :=
      Nat.xor_assoc _ _ _
    _ = n.val := by simp

private theorem notl_lessdef_involutive (v : val) :
    Val.lessdef (Val.notl (Val.notl v)) v := by
  cases v with
  | Vundef => exact Val.lessdef_refl _
  | Vint _ => exact Val.lessdef_undef _
  | Vlong n =>
      simp only [Val.notl]
      change Val.lessdef
        (.Vlong (CompCert4Lean.Lib.Integers.Int64.not
          (CompCert4Lean.Lib.Integers.Int64.not n))) (.Vlong n)
      rw [not64_involutive]
      exact Val.lessdef_refl _
  | Vfloat _ => exact Val.lessdef_undef _
  | Vsingle _ => exact Val.lessdef_undef _
  | Vptr _ _ => exact Val.lessdef_undef _

theorem eval_notl
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_notlStatement binary64_certificate binary32_certificate := by
  unfold eval_notlStatement unary_constructor_sound
  intro xi prog sp e m le a x h
  cases hmatch : notl_match a with
  | notl_case1 n =>
      cases h with
      | eval_Eop le' op al vl v hargs hop =>
          cases hargs with
          | nil _ =>
              change some (.Vlong n) = some x at hop
              cases hop
              refine ⟨.Vlong (CompCert4Lean.Lib.Integers.Int64.not n), ?_, ?_⟩
              · apply eval_expr.eval_Eop le (Olongconst (CompCert4Lean.Lib.Integers.Int64.not n)) Enil []
                · exact eval_exprlist.nil le
                · rfl
              · exact Val.lessdef_refl _
  | notl_case2 t1 =>
      cases h with
      | eval_Eop le' op al vl v hargs hop =>
          cases hargs with
          | cons _ a' al' v1 vl' hhead htail =>
              cases htail with
              | nil _ =>
                  change some (Val.notl v1) = some x at hop
                  cases hop
                  refine ⟨v1, ?_, ?_⟩
                  · simpa [notl, hmatch] using hhead
                  · exact notl_lessdef_involutive _
  | notl_default e1 =>
      refine ⟨Val.notl x, ?_, Val.lessdef_refl _⟩
      simp only [notl, hmatch]
      apply eval_expr.eval_Eop le Onotl (Econs a Enil) [x] (Val.notl x)
      · exact eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)
      · rfl

end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong

private theorem int64_and_val (x y : CCInt64) :
    (CompCert4Lean.Lib.Integers.Int64.and x y).val = Nat.land x.val y.val := by
  unfold CompCert4Lean.Lib.Integers.Int64.and CompCert4Lean.Lib.Integers.WordCore.and
  exact repr_val_of_lt64 _ (Nat.and_lt_two_pow _ y.toFin.isLt)

private theorem int64_and_commut (x y : CCInt64) :
    CompCert4Lean.Lib.Integers.Int64.and x y =
      CompCert4Lean.Lib.Integers.Int64.and y x := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [int64_and_val, int64_and_val]
  simpa only [Nat.land_eq] using (Nat.and_comm x.val y.val)

private theorem int64_and_assoc (x y z : CCInt64) :
    CompCert4Lean.Lib.Integers.Int64.and
        (CompCert4Lean.Lib.Integers.Int64.and x y) z =
      CompCert4Lean.Lib.Integers.Int64.and x
        (CompCert4Lean.Lib.Integers.Int64.and y z) := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [int64_and_val, int64_and_val, int64_and_val, int64_and_val]
  simpa only [Nat.land_eq] using (Nat.and_assoc x.val y.val z.val)

private theorem int64_and_zero (x : CCInt64) :
    CompCert4Lean.Lib.Integers.Int64.and x
        CompCert4Lean.Lib.Integers.Int64.zero =
      CompCert4Lean.Lib.Integers.Int64.zero := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [int64_and_val]
  have hz : CompCert4Lean.Lib.Integers.Int64.zero.val = 0 := rfl
  rw [hz]
  simpa only [Nat.land_eq] using (Nat.and_zero x.val)

private theorem int64_and_mone (x : CCInt64) :
    CompCert4Lean.Lib.Integers.Int64.and x
        CompCert4Lean.Lib.Integers.Int64.mone = x := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [int64_and_val]
  have hm : CompCert4Lean.Lib.Integers.Int64.mone.val = 2 ^ 64 - 1 := rfl
  rw [hm]
  simpa only [Nat.land_eq, CompCert4Lean.Lib.Integers.Int64.wordsize,
    CompCert4Lean.Lib.Integers.WordCore.Word.toFin] using
    (Nat.and_two_pow_sub_one_of_lt_two_pow x.toFin.isLt)

private theorem int64_eq_true_zero (n : CCInt64)
    (h : CompCert4Lean.Lib.Integers.Int64.eq n
      CompCert4Lean.Lib.Integers.Int64.zero = true) :
    n = CompCert4Lean.Lib.Integers.Int64.zero := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext
  have hd : decide (n.intval =
      CompCert4Lean.Lib.Integers.Int64.zero.intval) = true := by
    simpa [CompCert4Lean.Lib.Integers.Int64.eq,
      CompCert4Lean.Lib.Integers.WordCore.eq] using h
  exact of_decide_eq_true hd

private theorem int64_eq_true_mone (n : CCInt64)
    (h : CompCert4Lean.Lib.Integers.Int64.eq n
      CompCert4Lean.Lib.Integers.Int64.mone = true) :
    n = CompCert4Lean.Lib.Integers.Int64.mone := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext
  have hd : decide (n.intval =
      CompCert4Lean.Lib.Integers.Int64.mone.intval) = true := by
    simpa [CompCert4Lean.Lib.Integers.Int64.eq,
      CompCert4Lean.Lib.Integers.WordCore.eq] using h
  exact of_decide_eq_true hd

private theorem val_andl_commut (x y : val) :
    Val.andl x y = Val.andl y x := by
  cases x <;> cases y <;> try rfl
  case Vlong.Vlong x y =>
    change Vlong (CompCert4Lean.Lib.Integers.Int64.and x y) =
      Vlong (CompCert4Lean.Lib.Integers.Int64.and y x)
    rw [int64_and_commut]

private theorem val_andl_assoc_comm (x : val) (n1 n2 : CCInt64) :
    Val.andl (Val.andl x (.Vlong n2)) (.Vlong n1) =
      Val.andl x (.Vlong (CompCert4Lean.Lib.Integers.Int64.and n1 n2)) := by
  cases x with
  | Vundef => rfl
  | Vint _ => rfl
  | Vfloat _ => rfl
  | Vsingle _ => rfl
  | Vptr _ _ => rfl
  | Vlong x =>
      change Vlong (CompCert4Lean.Lib.Integers.Int64.and
          (CompCert4Lean.Lib.Integers.Int64.and x n2) n1) =
        Vlong (CompCert4Lean.Lib.Integers.Int64.and x
          (CompCert4Lean.Lib.Integers.Int64.and n1 n2))
      calc
        Vlong (CompCert4Lean.Lib.Integers.Int64.and
            (CompCert4Lean.Lib.Integers.Int64.and x n2) n1) =
          Vlong (CompCert4Lean.Lib.Integers.Int64.and x
            (CompCert4Lean.Lib.Integers.Int64.and n2 n1)) :=
          congrArg Vlong (int64_and_assoc x n2 n1)
        _ = Vlong (CompCert4Lean.Lib.Integers.Int64.and x
            (CompCert4Lean.Lib.Integers.Int64.and n1 n2)) := by
          rw [int64_and_commut n2 n1]

private theorem eval_longconst_value
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (le : letenv) (n : CCInt64) (x : val)
    (h : eval_expr (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi ge sp e m le
      (Eop (Olongconst n) Enil) x) :
    x = .Vlong n := by
  cases h with
  | eval_Eop _ _ _ _ _ hargs hop =>
      cases hargs
      change some (.Vlong n) = some x at hop
      cases hop
      rfl

private theorem val_andl_zero (x : val) :
    Val.lessdef (Val.andl x (.Vlong CompCert4Lean.Lib.Integers.Int64.zero))
      (.Vlong CompCert4Lean.Lib.Integers.Int64.zero) := by
  cases x with
  | Vlong n =>
      change Val.lessdef
        (.Vlong (CompCert4Lean.Lib.Integers.Int64.and n
          CompCert4Lean.Lib.Integers.Int64.zero))
        (.Vlong CompCert4Lean.Lib.Integers.Int64.zero)
      rw [int64_and_zero]
      exact Val.lessdef_refl _
  | _ => exact Val.lessdef_undef _

private theorem val_andl_mone (x : val) :
    Val.lessdef (Val.andl x (.Vlong CompCert4Lean.Lib.Integers.Int64.mone)) x := by
  cases x with
  | Vlong n =>
      change Val.lessdef
        (.Vlong (CompCert4Lean.Lib.Integers.Int64.and n
          CompCert4Lean.Lib.Integers.Int64.mone)) (.Vlong n)
      rw [int64_and_mone]
      exact Val.lessdef_refl _
  | _ => exact Val.lessdef_undef _

private theorem eval_andlimm_aux
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem)
      (n : CCInt64),
      unary_constructor_sound (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi prog sp e m (andlimm n)
        (fun v => Val.andl v (.Vlong n)) := by
  intro xi prog sp e m n le a x h
  unfold andlimm
  by_cases hz : CompCert4Lean.Lib.Integers.Int64.eq n
      CompCert4Lean.Lib.Integers.Int64.zero = true
  · have hn := int64_eq_true_zero n hz
    rw [if_pos hz]
    refine ⟨.Vlong CompCert4Lean.Lib.Integers.Int64.zero, ?_, ?_⟩
    · exact eval_longconst xi prog sp e m le CompCert4Lean.Lib.Integers.Int64.zero
    · subst n
      exact val_andl_zero x
  · by_cases hm : CompCert4Lean.Lib.Integers.Int64.eq n
        CompCert4Lean.Lib.Integers.Int64.mone = true
    · have hn := int64_eq_true_mone n hm
      rw [if_neg hz, if_pos hm]
      subst n
      refine ⟨x, h, ?_⟩
      exact val_andl_mone x
    · rw [if_neg hz, if_neg hm]
      cases hmatch : andlimm_match a with
      | andlimm_case1 n2 =>
          have hx : x = .Vlong n2 := eval_longconst_value xi
            (Genv.globalenv prog) sp e m le n2 x (by simpa [hmatch] using h)
          subst x
          refine ⟨.Vlong (CompCert4Lean.Lib.Integers.Int64.and n n2), ?_, ?_⟩
          · exact eval_longconst xi prog sp e m le
              (CompCert4Lean.Lib.Integers.Int64.and n n2)
          · change Val.lessdef
              (.Vlong (CompCert4Lean.Lib.Integers.Int64.and n2 n))
              (.Vlong (CompCert4Lean.Lib.Integers.Int64.and n n2))
            rw [int64_and_commut]
            exact Val.lessdef_refl _
      | andlimm_case2 n2 t2 =>
          cases h with
          | eval_Eop le' op al vl v hargs hop =>
              cases hargs with
              | cons _ a' al' v1 vl' hhead htail =>
                  cases htail with
                  | nil _ =>
                      change some (Val.andl v1 (.Vlong n2)) = some x at hop
                      cases hop
                      refine ⟨Val.andl v1
                        (.Vlong (CompCert4Lean.Lib.Integers.Int64.and n n2)), ?_, ?_⟩
                      · apply eval_expr.eval_Eop le
                          (Oandlimm (CompCert4Lean.Lib.Integers.Int64.and n n2))
                          (Econs t2 Enil) [v1] _
                        · exact eval_exprlist.cons le t2 Enil v1 []
                            (by simpa [hmatch] using hhead)
                            (eval_exprlist.nil le)
                        · rfl
                      · change Val.lessdef
                          (Val.andl (Val.andl v1 (.Vlong n2)) (.Vlong n))
                          (Val.andl v1
                            (.Vlong (CompCert4Lean.Lib.Integers.Int64.and n n2)))
                        rw [val_andl_assoc_comm]
                        exact Val.lessdef_refl _
      | andlimm_default e2 =>
          refine ⟨Val.andl x (.Vlong n), ?_, Val.lessdef_refl _⟩
          apply eval_expr.eval_Eop le (Oandlimm n) (Econs a Enil) [x]
            (Val.andl x (.Vlong n))
          · exact eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)
          · rfl

theorem eval_andl
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_andlStatement binary64_certificate binary32_certificate := by
  unfold eval_andlStatement binary_constructor_sound
  intro xi prog sp e m le a x b y ha hb
  cases hmatch : andl_match a b with
  | andl_case1 n1 t2 =>
      have hx : x = .Vlong n1 := eval_longconst_value xi
        (Genv.globalenv prog) sp e m le n1 x (by simpa [hmatch] using ha)
      subst x
      obtain ⟨v, hv, hd⟩ := eval_andlimm_aux xi prog sp e m n1 le b y hb
      refine ⟨v, ?_, ?_⟩
      · simpa [andl, hmatch] using hv
      · rw [val_andl_commut]
        exact hd
  | andl_case2 t1 n2 =>
      have hy : y = .Vlong n2 := eval_longconst_value xi
        (Genv.globalenv prog) sp e m le n2 y (by simpa [hmatch] using hb)
      subst y
      obtain ⟨v, hv, hd⟩ := eval_andlimm_aux xi prog sp e m n2 le a x ha
      refine ⟨v, ?_, hd⟩
      simpa [andl, hmatch] using hv
  | andl_default e1 e2 =>
      refine ⟨Val.andl x y, ?_, Val.lessdef_refl _⟩
      simp only [andl, hmatch]
      apply eval_expr.eval_Eop le Oandl (Econs a (Econs b Enil)) [x, y]
        (Val.andl x y)
      · exact eval_exprlist.cons le a (Econs b Enil) x [y] ha
          (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))
      · rfl

end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong

private theorem int64_or_val (x y : CCInt64) :
    (CompCert4Lean.Lib.Integers.Int64.or x y).val = Nat.lor x.val y.val := by
  unfold CompCert4Lean.Lib.Integers.Int64.or CompCert4Lean.Lib.Integers.WordCore.or
  exact repr_val_of_lt64 _ (Nat.or_lt_two_pow x.toFin.isLt y.toFin.isLt)

private theorem int64_or_commut (x y : CCInt64) :
    CompCert4Lean.Lib.Integers.Int64.or x y =
      CompCert4Lean.Lib.Integers.Int64.or y x := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [int64_or_val, int64_or_val]
  simpa only [Nat.lor_eq] using (Nat.or_comm x.val y.val)

private theorem int64_or_assoc (x y z : CCInt64) :
    CompCert4Lean.Lib.Integers.Int64.or
        (CompCert4Lean.Lib.Integers.Int64.or x y) z =
      CompCert4Lean.Lib.Integers.Int64.or x
        (CompCert4Lean.Lib.Integers.Int64.or y z) := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [int64_or_val, int64_or_val, int64_or_val, int64_or_val]
  simpa only [Nat.lor_eq] using (Nat.or_assoc x.val y.val z.val)

private theorem int64_or_zero (x : CCInt64) :
    CompCert4Lean.Lib.Integers.Int64.or x
        CompCert4Lean.Lib.Integers.Int64.zero = x := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [int64_or_val]
  have hz : CompCert4Lean.Lib.Integers.Int64.zero.val = 0 := rfl
  rw [hz]
  simpa only [Nat.lor_eq] using (Nat.or_zero x.val)

private theorem int64_or_mone (x : CCInt64) :
    CompCert4Lean.Lib.Integers.Int64.or x
        CompCert4Lean.Lib.Integers.Int64.mone =
      CompCert4Lean.Lib.Integers.Int64.mone := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [int64_or_val]
  have hm : CompCert4Lean.Lib.Integers.Int64.mone.val = 2 ^ 64 - 1 := rfl
  rw [hm]
  change Nat.lor x.val (2 ^ 64 - 1) = 2 ^ 64 - 1
  have hlt : Nat.lor x.val (2 ^ 64 - 1) < 2 ^ 64 :=
    Nat.or_lt_two_pow x.toFin.isLt (by omega)
  have hle : 2 ^ 64 - 1 ≤ Nat.lor x.val (2 ^ 64 - 1) := by
    exact Nat.right_le_or
  omega

private theorem val_orl_zero (x : val) :
    Val.lessdef (Val.orl x (.Vlong CompCert4Lean.Lib.Integers.Int64.zero))
      x := by
  cases x with
  | Vlong n =>
      change Val.lessdef
        (.Vlong (CompCert4Lean.Lib.Integers.Int64.or n
          CompCert4Lean.Lib.Integers.Int64.zero)) (.Vlong n)
      rw [int64_or_zero]
      exact Val.lessdef_refl _
  | _ => exact Val.lessdef_undef _

private theorem val_orl_mone (x : val) :
    Val.lessdef (Val.orl x (.Vlong CompCert4Lean.Lib.Integers.Int64.mone))
      (.Vlong CompCert4Lean.Lib.Integers.Int64.mone) := by
  cases x with
  | Vlong n =>
      change Val.lessdef
        (.Vlong (CompCert4Lean.Lib.Integers.Int64.or n
          CompCert4Lean.Lib.Integers.Int64.mone))
        (.Vlong CompCert4Lean.Lib.Integers.Int64.mone)
      rw [int64_or_mone]
      exact Val.lessdef_refl _
  | _ => exact Val.lessdef_undef _

private theorem val_orl_assoc_comm (x : val) (n1 n2 : CCInt64) :
    Val.orl (Val.orl x (.Vlong n2)) (.Vlong n1) =
      Val.orl x (.Vlong (CompCert4Lean.Lib.Integers.Int64.or n1 n2)) := by
  cases x with
  | Vundef => rfl
  | Vint _ => rfl
  | Vfloat _ => rfl
  | Vsingle _ => rfl
  | Vptr _ _ => rfl
  | Vlong x =>
      change Vlong (CompCert4Lean.Lib.Integers.Int64.or
          (CompCert4Lean.Lib.Integers.Int64.or x n2) n1) =
        Vlong (CompCert4Lean.Lib.Integers.Int64.or x
          (CompCert4Lean.Lib.Integers.Int64.or n1 n2))
      calc
        Vlong (CompCert4Lean.Lib.Integers.Int64.or
            (CompCert4Lean.Lib.Integers.Int64.or x n2) n1) =
          Vlong (CompCert4Lean.Lib.Integers.Int64.or x
            (CompCert4Lean.Lib.Integers.Int64.or n2 n1)) :=
          congrArg Vlong (int64_or_assoc x n2 n1)
        _ = Vlong (CompCert4Lean.Lib.Integers.Int64.or x
            (CompCert4Lean.Lib.Integers.Int64.or n1 n2)) := by
          rw [int64_or_commut n2 n1]

theorem eval_orlimm
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_orlimmStatement binary64_certificate binary32_certificate := by
  unfold eval_orlimmStatement unary_constructor_sound
  intro xi prog sp e m n le a x h
  unfold orlimm
  by_cases hz : CompCert4Lean.Lib.Integers.Int64.eq n
      CompCert4Lean.Lib.Integers.Int64.zero = true
  · have hn := int64_eq_true_zero n hz
    rw [if_pos hz]
    refine ⟨x, h, ?_⟩
    subst n
    exact val_orl_zero x
  · by_cases hm : CompCert4Lean.Lib.Integers.Int64.eq n
        CompCert4Lean.Lib.Integers.Int64.mone = true
    · have hn := int64_eq_true_mone n hm
      rw [if_neg hz, if_pos hm]
      refine ⟨.Vlong CompCert4Lean.Lib.Integers.Int64.mone, ?_, ?_⟩
      · exact eval_longconst xi prog sp e m le
          CompCert4Lean.Lib.Integers.Int64.mone
      · subst n
        exact val_orl_mone x
    · rw [if_neg hz, if_neg hm]
      cases hmatch : orlimm_match a with
      | orlimm_case1 n2 =>
          have hx : x = .Vlong n2 := eval_longconst_value xi
            (Genv.globalenv prog) sp e m le n2 x (by simpa [hmatch] using h)
          subst x
          refine ⟨.Vlong (CompCert4Lean.Lib.Integers.Int64.or n n2), ?_, ?_⟩
          · exact eval_longconst xi prog sp e m le
              (CompCert4Lean.Lib.Integers.Int64.or n n2)
          · change Val.lessdef
              (.Vlong (CompCert4Lean.Lib.Integers.Int64.or n2 n))
              (.Vlong (CompCert4Lean.Lib.Integers.Int64.or n n2))
            rw [int64_or_commut]
            exact Val.lessdef_refl _
      | orlimm_case2 n2 t2 =>
          cases h with
          | eval_Eop le' op al vl v hargs hop =>
              cases hargs with
              | cons _ a' al' v1 vl' hhead htail =>
                  cases htail with
                  | nil _ =>
                      change some (Val.orl v1 (.Vlong n2)) = some x at hop
                      cases hop
                      refine ⟨Val.orl v1
                        (.Vlong (CompCert4Lean.Lib.Integers.Int64.or n n2)), ?_, ?_⟩
                      · apply eval_expr.eval_Eop le
                          (Oorlimm (CompCert4Lean.Lib.Integers.Int64.or n n2))
                          (Econs t2 Enil) [v1] _
                        · exact eval_exprlist.cons le t2 Enil v1 []
                            (by simpa [hmatch] using hhead)
                            (eval_exprlist.nil le)
                        · rfl
                      · change Val.lessdef
                          (Val.orl (Val.orl v1 (.Vlong n2)) (.Vlong n))
                          (Val.orl v1
                            (.Vlong (CompCert4Lean.Lib.Integers.Int64.or n n2)))
                        rw [val_orl_assoc_comm]
                        exact Val.lessdef_refl _
      | orlimm_default e2 =>
          refine ⟨Val.orl x (.Vlong n), ?_, Val.lessdef_refl _⟩
          apply eval_expr.eval_Eop le (Oorlimm n) (Econs a Enil) [x]
            (Val.orl x (.Vlong n))
          · exact eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)
          · rfl

end CompCert4Lean.X86.SelectLongproof
namespace CompCert4Lean.X86.SelectLongproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong

private theorem int64_xor_val (x y : CCInt64) :
    (CompCert4Lean.Lib.Integers.Int64.xor x y).val = Nat.xor x.val y.val := by
  unfold CompCert4Lean.Lib.Integers.Int64.xor CompCert4Lean.Lib.Integers.WordCore.xor
  exact repr_val_of_lt64 _ (Nat.xor_lt_two_pow x.toFin.isLt y.toFin.isLt)

private theorem int64_xor_commut (x y : CCInt64) :
    CompCert4Lean.Lib.Integers.Int64.xor x y =
      CompCert4Lean.Lib.Integers.Int64.xor y x := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [int64_xor_val, int64_xor_val]
  simpa only [Nat.xor_eq] using (Nat.xor_comm x.val y.val)

private theorem int64_xor_assoc (x y z : CCInt64) :
    CompCert4Lean.Lib.Integers.Int64.xor
        (CompCert4Lean.Lib.Integers.Int64.xor x y) z =
      CompCert4Lean.Lib.Integers.Int64.xor x
        (CompCert4Lean.Lib.Integers.Int64.xor y z) := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [int64_xor_val, int64_xor_val, int64_xor_val, int64_xor_val]
  simpa only [Nat.xor_eq] using (Nat.xor_assoc x.val y.val z.val)

private theorem int64_xor_zero (x : CCInt64) :
    CompCert4Lean.Lib.Integers.Int64.xor x
        CompCert4Lean.Lib.Integers.Int64.zero = x := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [int64_xor_val]
  have hz : CompCert4Lean.Lib.Integers.Int64.zero.val = 0 := rfl
  rw [hz]
  simpa only [Nat.xor_eq] using (Nat.xor_zero x.val)

private theorem int64_xor_mone (x : CCInt64) :
    CompCert4Lean.Lib.Integers.Int64.xor x
        CompCert4Lean.Lib.Integers.Int64.mone =
      CompCert4Lean.Lib.Integers.Int64.not x := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [int64_xor_val]
  have hm : CompCert4Lean.Lib.Integers.Int64.mone.val = 2 ^ 64 - 1 := rfl
  rw [hm, not_val64]

private theorem int64_xor_not_swap (x y : CCInt64) :
    CompCert4Lean.Lib.Integers.Int64.xor
        (CompCert4Lean.Lib.Integers.Int64.not x) y =
      CompCert4Lean.Lib.Integers.Int64.xor x
        (CompCert4Lean.Lib.Integers.Int64.not y) := by
  rw [← int64_xor_mone x, ← int64_xor_mone y]
  rw [int64_xor_assoc, int64_xor_commut (CompCert4Lean.Lib.Integers.Int64.mone) y]

private theorem val_xorl_commut (x y : val) :
    Val.xorl x y = Val.xorl y x := by
  cases x <;> cases y <;> try rfl
  case Vlong.Vlong x y =>
    change Vlong (CompCert4Lean.Lib.Integers.Int64.xor x y) =
      Vlong (CompCert4Lean.Lib.Integers.Int64.xor y x)
    rw [int64_xor_commut]

private theorem val_xorl_mone (x : val) :
    Val.xorl x (.Vlong CompCert4Lean.Lib.Integers.Int64.mone) = Val.notl x := by
  cases x with
  | Vundef => rfl
  | Vint _ => rfl
  | Vfloat _ => rfl
  | Vsingle _ => rfl
  | Vptr _ _ => rfl
  | Vlong n =>
      change Vlong (CompCert4Lean.Lib.Integers.Int64.xor n
        CompCert4Lean.Lib.Integers.Int64.mone) =
        Vlong (CompCert4Lean.Lib.Integers.Int64.not n)
      rw [int64_xor_mone]

private theorem val_xorl_assoc_comm (x : val) (n1 n2 : CCInt64) :
    Val.xorl (Val.xorl x (.Vlong n2)) (.Vlong n1) =
      Val.xorl x (.Vlong (CompCert4Lean.Lib.Integers.Int64.xor n1 n2)) := by
  cases x with
  | Vundef => rfl
  | Vint _ => rfl
  | Vfloat _ => rfl
  | Vsingle _ => rfl
  | Vptr _ _ => rfl
  | Vlong x =>
      change Vlong (CompCert4Lean.Lib.Integers.Int64.xor
          (CompCert4Lean.Lib.Integers.Int64.xor x n2) n1) =
        Vlong (CompCert4Lean.Lib.Integers.Int64.xor x
          (CompCert4Lean.Lib.Integers.Int64.xor n1 n2))
      calc
        Vlong (CompCert4Lean.Lib.Integers.Int64.xor
            (CompCert4Lean.Lib.Integers.Int64.xor x n2) n1) =
          Vlong (CompCert4Lean.Lib.Integers.Int64.xor x
            (CompCert4Lean.Lib.Integers.Int64.xor n2 n1)) :=
          congrArg Vlong (int64_xor_assoc x n2 n1)
        _ = Vlong (CompCert4Lean.Lib.Integers.Int64.xor x
            (CompCert4Lean.Lib.Integers.Int64.xor n1 n2)) := by
          rw [int64_xor_commut n2 n1]

private theorem eval_xorlimm_aux
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem)
      (n : CCInt64),
      unary_constructor_sound (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi prog sp e m (xorlimm n)
        (fun v => Val.xorl v (.Vlong n)) := by
  intro xi prog sp e m n le a x h
  unfold xorlimm
  by_cases hz : CompCert4Lean.Lib.Integers.Int64.eq n
      CompCert4Lean.Lib.Integers.Int64.zero = true
  · have hn := int64_eq_true_zero n hz
    rw [if_pos hz]
    refine ⟨x, h, ?_⟩
    subst n
    cases x <;> try exact Val.lessdef_undef _
    change Val.lessdef (.Vlong (CompCert4Lean.Lib.Integers.Int64.xor _
      CompCert4Lean.Lib.Integers.Int64.zero)) (.Vlong _)
    rw [int64_xor_zero]
    exact Val.lessdef_refl _
  · by_cases hm : CompCert4Lean.Lib.Integers.Int64.eq n
        CompCert4Lean.Lib.Integers.Int64.mone = true
    · have hn := int64_eq_true_mone n hm
      rw [if_neg hz, if_pos hm]
      subst n
      obtain ⟨v, hv, hd⟩ := eval_notl xi prog sp e m le a x h
      refine ⟨v, hv, ?_⟩
      change Val.lessdef (Val.xorl x (.Vlong
        CompCert4Lean.Lib.Integers.Int64.mone)) v
      rw [val_xorl_mone]
      exact hd
    · rw [if_neg hz, if_neg hm]
      cases hmatch : xorlimm_match a with
      | xorlimm_case1 n2 =>
          have hx : x = .Vlong n2 := eval_longconst_value xi
            (Genv.globalenv prog) sp e m le n2 x (by simpa [hmatch] using h)
          subst x
          refine ⟨.Vlong (CompCert4Lean.Lib.Integers.Int64.xor n n2), ?_, ?_⟩
          · exact eval_longconst xi prog sp e m le
              (CompCert4Lean.Lib.Integers.Int64.xor n n2)
          · change Val.lessdef
              (.Vlong (CompCert4Lean.Lib.Integers.Int64.xor n2 n))
              (.Vlong (CompCert4Lean.Lib.Integers.Int64.xor n n2))
            rw [int64_xor_commut]
            exact Val.lessdef_refl _
      | xorlimm_case2 n2 t2 =>
          cases h with
          | eval_Eop le' op al vl v hargs hop =>
              cases hargs with
              | cons _ a' al' v1 vl' hhead htail =>
                  cases htail with
                  | nil _ =>
                      change some (Val.xorl v1 (.Vlong n2)) = some x at hop
                      cases hop
                      refine ⟨Val.xorl v1
                        (.Vlong (CompCert4Lean.Lib.Integers.Int64.xor n n2)), ?_, ?_⟩
                      · apply eval_expr.eval_Eop le
                          (Oxorlimm (CompCert4Lean.Lib.Integers.Int64.xor n n2))
                          (Econs t2 Enil) [v1] _
                        · exact eval_exprlist.cons le t2 Enil v1 []
                            (by simpa [hmatch] using hhead)
                            (eval_exprlist.nil le)
                        · rfl
                      · change Val.lessdef
                          (Val.xorl (Val.xorl v1 (.Vlong n2)) (.Vlong n))
                          (Val.xorl v1
                            (.Vlong (CompCert4Lean.Lib.Integers.Int64.xor n n2)))
                        rw [val_xorl_assoc_comm]
                        exact Val.lessdef_refl _
      | xorlimm_case3 t2 =>
          cases h with
          | eval_Eop le' op al vl v hargs hop =>
              cases hargs with
              | cons _ a' al' v1 vl' hhead htail =>
                  cases htail with
                  | nil _ =>
                      change some (Val.notl v1) = some x at hop
                      cases hop
                      refine ⟨Val.xorl v1
                        (.Vlong (CompCert4Lean.Lib.Integers.Int64.not n)), ?_, ?_⟩
                      · apply eval_expr.eval_Eop le
                          (Oxorlimm (CompCert4Lean.Lib.Integers.Int64.not n))
                          (Econs t2 Enil) [v1] _
                        · exact eval_exprlist.cons le t2 Enil v1 []
                            (by simpa [hmatch] using hhead)
                            (eval_exprlist.nil le)
                        · rfl
                      · change Val.lessdef
                          (Val.xorl (Val.notl v1) (.Vlong n))
                          (Val.xorl v1
                            (.Vlong (CompCert4Lean.Lib.Integers.Int64.not n)))
                        cases v1 <;> try exact Val.lessdef_undef _
                        · change Val.lessdef
                            (.Vlong (CompCert4Lean.Lib.Integers.Int64.xor
                              (CompCert4Lean.Lib.Integers.Int64.not _) n))
                            (.Vlong (CompCert4Lean.Lib.Integers.Int64.xor _
                              (CompCert4Lean.Lib.Integers.Int64.not n)))
                          rw [int64_xor_not_swap]
                          exact Val.lessdef_refl _
      | xorlimm_default e2 =>
          refine ⟨Val.xorl x (.Vlong n), ?_, Val.lessdef_refl _⟩
          apply eval_expr.eval_Eop le (Oxorlimm n) (Econs a Enil) [x]
            (Val.xorl x (.Vlong n))
          · exact eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)
          · rfl

theorem eval_xorl
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_xorlStatement binary64_certificate binary32_certificate := by
  unfold eval_xorlStatement binary_constructor_sound
  intro xi prog sp e m le a x b y ha hb
  cases hmatch : xorl_match a b with
  | xorl_case1 n1 t2 =>
      have hx : x = .Vlong n1 := eval_longconst_value xi
        (Genv.globalenv prog) sp e m le n1 x (by simpa [hmatch] using ha)
      subst x
      obtain ⟨v, hv, hd⟩ := eval_xorlimm_aux xi prog sp e m n1 le b y hb
      refine ⟨v, ?_, ?_⟩
      · simpa [xorl, hmatch] using hv
      · rw [val_xorl_commut]
        exact hd
  | xorl_case2 t1 n2 =>
      have hy : y = .Vlong n2 := eval_longconst_value xi
        (Genv.globalenv prog) sp e m le n2 y (by simpa [hmatch] using hb)
      subst y
      obtain ⟨v, hv, hd⟩ := eval_xorlimm_aux xi prog sp e m n2 le a x ha
      refine ⟨v, ?_, hd⟩
      simpa [xorl, hmatch] using hv
  | xorl_default e1 e2 =>
      refine ⟨Val.xorl x y, ?_, Val.lessdef_refl _⟩
      simp only [xorl, hmatch]
      apply eval_expr.eval_Eop le Oxorl (Econs a (Econs b Enil)) [x, y]
        (Val.xorl x y)
      · exact eval_exprlist.cons le a (Econs b Enil) x [y] ha
          (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))
      · rfl

end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong

theorem eval_negl
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_neglStatement binary64_certificate binary32_certificate := by
  unfold eval_neglStatement unary_constructor_sound
  intro xi prog sp e m le a x h
  unfold negl
  cases hmatch : is_longconst a with
  | some n =>
      have hx : x = .Vlong n :=
        is_longconst_sound xi prog sp e m x a n le hmatch h
      subst x
      refine ⟨.Vlong (CompCert4Lean.Lib.Integers.Int64.neg n), ?_, ?_⟩
      · exact eval_longconst xi prog sp e m le
          (CompCert4Lean.Lib.Integers.Int64.neg n)
      · exact Val.lessdef_refl _
  | none =>
      refine ⟨Val.negl x, ?_, Val.lessdef_refl _⟩
      apply eval_expr.eval_Eop le Onegl (Econs a Enil) [x] (Val.negl x)
      · exact eval_exprlist.cons le a Enil x [] h (eval_exprlist.nil le)
      · rfl

end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers
open Lean Elab Tactic Meta

private theorem shrl_two_power_nat (bits : Nat) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.two_power_nat bits =
      ZArith.BinInt.Z.of_nat (2 ^ bits) := by
  run_tac
    let bitsF := (← getLCtx).findFromUserName? `bits |>.get!
    let proof ← mkAppM
      (suffixPrivateName
        "CompCert4Lean.Lib.Integers.WordCore.twoPowerNat_eq_zOfNat_twoPow")
      #[mkFVar bitsF.fvarId]
    closeMainGoal Name.anonymous proof

private theorem shrl_int64_repr_signed (x : CCInt64) :
    CompCert4Lean.Lib.Integers.Int64.repr
        (CompCert4Lean.Lib.Integers.Int64.signed x) = x := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  have hx0 : ZArith.BinInt.Z.le .Z0 x.intval := by
    have h := x.intrange.1
    change (-1 : Int) < intOfZ x.intval at h
    change 0 ≤ intOfZ x.intval
    omega
  have hxrepr : x.intval = zOfNat x.val :=
    (ZArith.Znat.Z2Nat.id x.intval hx0).symm
  have hxlt : x.val < 2 ^ 64 := x.toFin.isLt
  rw [show CompCert4Lean.Lib.Integers.Int64.signed x =
      zOfInt (intOfZ (CompCert4Lean.Lib.Integers.Int64.signed x)) by
    exact (zOfInt_intOfZ _).symm]
  unfold CompCert4Lean.Lib.Integers.Int64.repr
  rw [suffixWordValRepr64]
  simp only [CompCert4Lean.Lib.Integers.Int64.signed,
    CompCert4Lean.Lib.Integers.WordCore.signed,
    CompCert4Lean.Lib.Integers.WordCore.unsigned,
    CompCert4Lean.Lib.Integers.Int64.wordsize]
  run_tac
    let zltName := Lean.mkIdent
      (suffixPrivateName "CompCert4Lean.Lib.Integers.zltSelect")
    let selectName := Lean.mkIdent
      (suffixPrivateName "CompCert4Lean.Lib.Integers.sumboolSelect")
    let subName := Lean.mkIdent
      (suffixPrivateName "CompCert4Lean.Lib.Integers.zSub")
    let powerName := Lean.mkIdent
      (suffixPrivateName "CompCert4Lean.Lib.Integers.zTwoPowerNat")
    evalTactic (← `(tactic|
      unfold $zltName $selectName $subName $powerName))
  simp only [CompCert4Lean.Lib.Integers.Int64.wordsize, Nat.reduceSub,
    shrl_two_power_nat]
  rw [hxrepr]
  unfold zOfNat
  split
  · rw [show ZArith.BinInt.Z.of_nat x.val = zOfInt (Int.ofNat x.val) by rfl,
      intOfZ_zOfInt]
    change Int.toNat ((Int.ofNat x.val) % (2 ^ 64 : Int)) = x.val
    have hvalLt : Int.ofNat x.val < (2 ^ 64 : Int) := by
      change Int.ofNat x.val < Int.ofNat (2 ^ 64)
      exact Int.ofNat_lt.mpr hxlt
    have hmod := Int.emod_eq_of_lt (Int.natCast_nonneg _) hvalLt
    exact (congrArg Int.toNat hmod).trans (by simp)
  · rw [show ZArith.BinInt.Z.of_nat x.val = zOfInt (Int.ofNat x.val) by rfl]
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    change Int.toNat
      (((Int.ofNat x.val) - (2 ^ 64 : Int)) % (2 ^ 64 : Int)) = x.val
    rw [Int.sub_emod]
    rw [Int.emod_self, Int.sub_zero]
    have hvalLt : Int.ofNat x.val < (2 ^ 64 : Int) := by
      change Int.ofNat x.val < Int.ofNat (2 ^ 64)
      exact Int.ofNat_lt.mpr hxlt
    have hmod := Int.emod_eq_of_lt (Int.natCast_nonneg _) hvalLt
    calc
      Int.toNat ((Int.ofNat x.val % (2 ^ 64 : Int)) % (2 ^ 64 : Int)) =
          Int.toNat (Int.ofNat x.val % (2 ^ 64 : Int)) := by
        exact congrArg Int.toNat (Int.emod_emod _ _)
      _ = Int.toNat (Int.ofNat x.val) := congrArg Int.toNat hmod
      _ = x.val := by simp

private theorem shrl_int64_signed_repr_int (i : Int)
    (hlo : -(2 ^ 63 : Int) ≤ i) (hhi : i < (2 ^ 63 : Int)) :
    CompCert4Lean.Lib.Integers.Int64.signed
        (CompCert4Lean.Lib.Integers.Int64.repr (zOfInt i)) = zOfInt i := by
  let w : CCInt64 := CompCert4Lean.Lib.Integers.Int64.repr (zOfInt i)
  have hwval : w.val = Int.toNat (i % (2 ^ 64 : Int)) := by
    exact suffixWordValRepr64 64 i
  have hw0 : ZArith.BinInt.Z.le .Z0 w.intval := by
    have h := w.intrange.1
    change (-1 : Int) < intOfZ w.intval at h
    change 0 ≤ intOfZ w.intval
    omega
  have hwrepr : w.intval = zOfNat w.val :=
    (ZArith.Znat.Z2Nat.id w.intval hw0).symm
  change CompCert4Lean.Lib.Integers.WordCore.signed w = zOfInt i
  simp only [CompCert4Lean.Lib.Integers.WordCore.signed,
    CompCert4Lean.Lib.Integers.WordCore.unsigned]
  run_tac
    let zltName := Lean.mkIdent
      (suffixPrivateName "CompCert4Lean.Lib.Integers.zltSelect")
    let selectName := Lean.mkIdent
      (suffixPrivateName "CompCert4Lean.Lib.Integers.sumboolSelect")
    let subName := Lean.mkIdent
      (suffixPrivateName "CompCert4Lean.Lib.Integers.zSub")
    let powerName := Lean.mkIdent
      (suffixPrivateName "CompCert4Lean.Lib.Integers.zTwoPowerNat")
    evalTactic (← `(tactic|
      unfold $zltName $selectName $subName $powerName))
  simp only [CompCert4Lean.Lib.Integers.Int64.wordsize, Nat.reduceSub,
    shrl_two_power_nat]
  rw [hwrepr, hwval]
  unfold zOfNat
  by_cases hi : 0 ≤ i
  · have himod : i % (2 ^ 64 : Int) = i := by
      apply Int.emod_eq_of_lt hi
      have hpow : (2 ^ 63 : Int) < 2 ^ 64 := by decide
      omega
    rw [himod]
    have htoNat : Int.ofNat (Int.toNat i) = i :=
      Int.toNat_of_nonneg hi
    have hlt : ZArith.BinInt.Z.lt
        (ZArith.BinInt.Z.of_nat (Int.toNat i))
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.two_power_nat 63) := by
      rw [shrl_two_power_nat]
      unfold ZArith.BinInt.Z.lt ZArith.BinInt.Z.of_nat
      simp only [intOfZ_zOfInt]
      calc
        Int.ofNat (Int.toNat i) = i := htoNat
        _ < Int.ofNat (2 ^ 63) := hhi
    cases hdec : CompCert4Lean.Lib.Coqlib.zlt
        (ZArith.BinInt.Z.of_nat (Int.toNat i))
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.two_power_nat 63) with
    | left h =>
        simp only [hdec]
        apply intOfZ_injective
        unfold ZArith.BinInt.Z.of_nat
        simp only [intOfZ_zOfInt]
        exact htoNat
    | right h => exact (Int.not_lt_of_ge h hlt).elim
  · have hineg : i < 0 := Int.lt_of_not_ge hi
    have hmodEq : i % (2 ^ 64 : Int) = i + 2 ^ 64 := by
      have heq : i % (2 ^ 64 : Int) =
          (i + 2 ^ 64) % (2 ^ 64 : Int) := by
        apply (Int.emod_eq_emod_iff_emod_sub_eq_zero).2
        rw [show i - (i + 2 ^ 64) = -(2 ^ 64 : Int) by omega]
        exact Int.neg_emod_self _
      rw [heq]
      apply Int.emod_eq_of_lt
      · have hp : 0 < (2 ^ 63 : Int) := by decide
        have hdouble : (2 ^ 64 : Int) = 2 * 2 ^ 63 := by decide
        omega
      · omega
    rw [hmodEq]
    have hisum0 : 0 ≤ i + (2 ^ 64 : Int) := by
      have hp : 0 < (2 ^ 63 : Int) := by decide
      have hdouble : (2 ^ 64 : Int) = 2 * 2 ^ 63 := by decide
      omega
    have htoNat : Int.ofNat (Int.toNat (i + 2 ^ 64)) = i + 2 ^ 64 :=
      Int.toNat_of_nonneg hisum0
    have hge : ZArith.BinInt.Z.ge
        (ZArith.BinInt.Z.of_nat (Int.toNat (i + 2 ^ 64)))
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.two_power_nat 63) := by
      rw [shrl_two_power_nat]
      unfold ZArith.BinInt.Z.ge ZArith.BinInt.Z.of_nat
      simp only [intOfZ_zOfInt]
      have hbound : (2 ^ 63 : Int) ≤ i + 2 ^ 64 := by
        have hdouble : (2 ^ 64 : Int) = 2 * 2 ^ 63 := by decide
        omega
      exact Int.le_trans hbound (Int.le_of_eq htoNat.symm)
    cases hdec : CompCert4Lean.Lib.Coqlib.zlt
        (ZArith.BinInt.Z.of_nat (Int.toNat (i + 2 ^ 64)))
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.two_power_nat 63) with
    | left h => exact (Int.not_lt_of_ge hge h).elim
    | right h =>
        simp only [hdec]
        apply intOfZ_injective
        simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.of_nat,
          intOfZ_zOfInt]
        change Int.ofNat (Int.toNat (i + 2 ^ 64)) - Int.ofNat (2 ^ 64) = i
        have hpowNat : Int.ofNat (2 ^ 64) = (2 ^ 64 : Int) := by
          exact (Int.natCast_pow 2 64).symm
        rw [htoNat, hpowNat]
        omega

private theorem shrl_int_unsigned_int (n : CCInt) :
    intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned n) = Int.ofNat n.val := by
  have hn0 : ZArith.BinInt.Z.le .Z0 n.intval := by
    have h := n.intrange.1
    change (-1 : Int) < intOfZ n.intval at h
    change 0 ≤ intOfZ n.intval
    omega
  have hnrepr : n.intval = zOfNat n.val :=
    (ZArith.Znat.Z2Nat.id n.intval hn0).symm
  unfold CompCert4Lean.Lib.Integers.Int.unsigned
    CompCert4Lean.Lib.Integers.WordCore.unsigned
  rw [hnrepr]
  unfold zOfNat ZArith.BinInt.Z.of_nat
  rw [intOfZ_zOfInt]

private theorem shrl_int_unsigned_z (n : CCInt) :
    CompCert4Lean.Lib.Integers.Int.unsigned n =
      ZArith.BinInt.Z.of_nat n.val := by
  apply intOfZ_injective
  rw [shrl_int_unsigned_int]
  unfold ZArith.BinInt.Z.of_nat
  rw [intOfZ_zOfInt]

private theorem shrl_zshiftr_nat (a : Int) (p q : Nat) :
    ZArith.BinInt.Z.shiftr
        (ZArith.BinInt.Z.shiftr (zOfInt a) (ZArith.BinInt.Z.of_nat p))
        (ZArith.BinInt.Z.of_nat q) =
      ZArith.BinInt.Z.shiftr (zOfInt a)
        (ZArith.BinInt.Z.of_nat (p + q)) := by
  unfold ZArith.BinInt.Z.shiftr ZArith.BinInt.Z.of_nat
  have hp : 0 ≤ Int.ofNat p := Int.natCast_nonneg _
  have hq : 0 ≤ Int.ofNat q := Int.natCast_nonneg _
  have hpq : 0 ≤ Int.ofNat (p + q) := Int.natCast_nonneg _
  simp only [intOfZ_zOfInt]
  rw [if_pos hp, if_pos hq, if_pos hpq]
  simp only [intOfZ_zOfInt]
  have htp : (Int.ofNat p).toNat = p := rfl
  have htq : (Int.ofNat q).toNat = q := rfl
  have htpq : (Int.ofNat (p + q)).toNat = p + q := rfl
  rw [htp, htq, htpq]
  apply congrArg zOfInt
  calc
    (a.ediv (Int.pow 2 p)).ediv (Int.pow 2 q) =
        a.ediv (Int.pow 2 p * Int.pow 2 q) :=
      Int.ediv_ediv_of_nonneg (Int.le_of_lt (Int.pow_pos (by omega)))
    _ = a.ediv (Int.pow 2 (p + q)) :=
      congrArg (fun d => a.ediv d) (Int.pow_add 2 p q).symm

private theorem shrl_zshiftr_int_unsigned
    (a : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (n : CCInt) :
    ZArith.BinInt.Z.shiftr a
        (CompCert4Lean.Lib.Integers.Int.unsigned n) =
      zOfInt (intOfZ a / (2 ^ n.val : Int)) := by
  rw [shrl_int_unsigned_z]
  unfold ZArith.BinInt.Z.shiftr ZArith.BinInt.Z.of_nat
  simp only [intOfZ_zOfInt]
  have hn : 0 ≤ Int.ofNat n.val := Int.natCast_nonneg _
  rw [if_pos hn]
  have htn : (Int.ofNat n.val).toNat = n.val := rfl
  rw [htn]
  rfl

private theorem shrl_word_add_val {bits : Nat}
    (x y : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    (CompCert4Lean.Lib.Integers.WordCore.add x y).val =
      (x.val + y.val) % (2 ^ bits) := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let yF := (lctx.findFromUserName? `y).get!
    let proof ← mkAppM
      (suffixPrivateName "CompCert4Lean.Lib.Integers.WordCore.add_val")
      #[mkFVar xF.fvarId, mkFVar yF.fvarId]
    closeMainGoal Name.anonymous proof

private theorem shrl_int_add_val_small (x y : CCInt)
    (h : x.val + y.val < 2 ^ 32) :
    (CompCert4Lean.Lib.Integers.Int.add x y).val = x.val + y.val := by
  change (CompCert4Lean.Lib.Integers.WordCore.add x y).val = _
  rw [shrl_word_add_val]
  exact Nat.mod_eq_of_lt h

private theorem shrl_int_ltu_iwordsize_val (n : CCInt)
    (h : CompCert4Lean.Lib.Integers.Int.ltu n
      CompCert4Lean.Lib.Integers.Int64.iwordsize' = true) :
    n.val < 64 := by
  have hlt := (CompCert4Lean.Lib.Integers.Int.ltu_inv_proof n
    CompCert4Lean.Lib.Integers.Int64.iwordsize' h).2
  change intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned n) <
    intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned
      CompCert4Lean.Lib.Integers.Int64.iwordsize') at hlt
  rw [shrl_int_unsigned_int n,
    shrl_int_unsigned_int CompCert4Lean.Lib.Integers.Int64.iwordsize'] at hlt
  have hi : CompCert4Lean.Lib.Integers.Int64.iwordsize'.val = 64 := rfl
  rw [hi] at hlt
  exact Int.ofNat_lt.mp hlt

private theorem shrl_int64_signed_range_int (x : CCInt64) :
    -(2 ^ 63 : Int) ≤
        intOfZ (CompCert4Lean.Lib.Integers.Int64.signed x) ∧
      intOfZ (CompCert4Lean.Lib.Integers.Int64.signed x) < (2 ^ 63 : Int) := by
  have hx0 : ZArith.BinInt.Z.le .Z0 x.intval := by
    have h := x.intrange.1
    change (-1 : Int) < intOfZ x.intval at h
    change 0 ≤ intOfZ x.intval
    omega
  have hxrepr : x.intval = zOfNat x.val :=
    (ZArith.Znat.Z2Nat.id x.intval hx0).symm
  have hxlt : x.val < 2 ^ 64 := x.toFin.isLt
  simp only [CompCert4Lean.Lib.Integers.Int64.signed,
    CompCert4Lean.Lib.Integers.WordCore.signed,
    CompCert4Lean.Lib.Integers.WordCore.unsigned,
    CompCert4Lean.Lib.Integers.Int64.wordsize]
  run_tac
    let zltName := Lean.mkIdent
      (suffixPrivateName "CompCert4Lean.Lib.Integers.zltSelect")
    let selectName := Lean.mkIdent
      (suffixPrivateName "CompCert4Lean.Lib.Integers.sumboolSelect")
    let subName := Lean.mkIdent
      (suffixPrivateName "CompCert4Lean.Lib.Integers.zSub")
    let powerName := Lean.mkIdent
      (suffixPrivateName "CompCert4Lean.Lib.Integers.zTwoPowerNat")
    evalTactic (← `(tactic|
      unfold $zltName $selectName $subName $powerName))
  simp only [Nat.reduceSub, shrl_two_power_nat]
  rw [hxrepr]
  unfold zOfNat
  split
  · rename_i d hlt heq
    unfold ZArith.BinInt.Z.lt ZArith.BinInt.Z.of_nat at hlt
    rw [intOfZ_zOfInt] at hlt
    unfold ZArith.BinInt.Z.of_nat
    constructor
    · rw [intOfZ_zOfInt]
      have hxnat : (0 : Int) ≤ Int.ofNat x.val := Int.natCast_nonneg _
      omega
    · rw [intOfZ_zOfInt]
      exact hlt
  · rename_i d hge heq
    unfold ZArith.BinInt.Z.ge ZArith.BinInt.Z.of_nat at hge
    rw [intOfZ_zOfInt] at hge
    unfold ZArith.BinInt.Z.sub ZArith.BinInt.Z.of_nat
    simp only [intOfZ_zOfInt]
    have hxnat : (0 : Int) ≤ Int.ofNat x.val := Int.natCast_nonneg _
    have hxltInt : Int.ofNat x.val < Int.ofNat (2 ^ 64) :=
      Int.ofNat_lt.mpr hxlt
    have hpow63 : intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.two_power_nat 63) =
        (2 ^ 63 : Int) := by
      rw [shrl_two_power_nat]
      unfold ZArith.BinInt.Z.of_nat
      rw [intOfZ_zOfInt]
      exact (Int.natCast_pow 2 63).symm
    have hpow64 : Int.ofNat (2 ^ 64) = (2 ^ 64 : Int) := by
      exact (Int.natCast_pow 2 64).symm
    rw [hpow63] at hge
    rw [hpow64] at hxltInt ⊢
    have hdouble : (2 ^ 64 : Int) = 2 * 2 ^ 63 := by decide
    constructor <;> omega

private theorem shrl_int64_shr_comp (x : CCInt64) (n1 n : CCInt)
    (hn1 : CompCert4Lean.Lib.Integers.Int.ltu n1
      CompCert4Lean.Lib.Integers.Int64.iwordsize' = true)
    (hn : CompCert4Lean.Lib.Integers.Int.ltu n
      CompCert4Lean.Lib.Integers.Int64.iwordsize' = true) :
    CompCert4Lean.Lib.Integers.Int64.shr'
        (CompCert4Lean.Lib.Integers.Int64.shr' x n1) n =
      CompCert4Lean.Lib.Integers.Int64.shr' x
        (CompCert4Lean.Lib.Integers.Int.add n n1) := by
  have hn1v := shrl_int_ltu_iwordsize_val n1 hn1
  have hnv := shrl_int_ltu_iwordsize_val n hn
  have haddSmall : n.val + n1.val < 2 ^ 32 := by
    have hpow : 128 < 2 ^ 32 := by decide
    omega
  have haddVal :
      (CompCert4Lean.Lib.Integers.Int.add n n1).val = n.val + n1.val :=
    shrl_int_add_val_small n n1 (by simpa [Nat.add_comm] using haddSmall)
  let sx : Int := intOfZ (CompCert4Lean.Lib.Integers.Int64.signed x)
  let d : Int := 2 ^ n1.val
  let j : Int := sx / d
  have hdpos : 0 < d := by
    dsimp [d]
    exact Int.pow_pos (by omega)
  have hdge : 1 ≤ d := by omega
  have hsrange := shrl_int64_signed_range_int x
  have hjlo : -(2 ^ 63 : Int) ≤ j := by
    apply (Int.le_ediv_iff_mul_le hdpos).2
    have hmul : -(2 ^ 63 : Int) * d ≤ -(2 ^ 63 : Int) * 1 :=
      Int.mul_le_mul_of_nonpos_left (by decide) hdge
    dsimp [sx] at hsrange
    exact Int.le_trans (by simpa using hmul) hsrange.1
  have hjhi : j < (2 ^ 63 : Int) := by
    apply (Int.ediv_lt_iff_lt_mul hdpos).2
    have hmul : (2 ^ 63 : Int) * 1 ≤ (2 ^ 63 : Int) * d :=
      Int.mul_le_mul_of_nonneg_left hdge (by decide)
    dsimp [sx] at hsrange
    exact Int.lt_of_lt_of_le hsrange.2 (by simpa using hmul)
  have hshift1 :
      ZArith.BinInt.Z.shiftr
          (CompCert4Lean.Lib.Integers.Int64.signed x)
          (CompCert4Lean.Lib.Integers.Int.unsigned n1) = zOfInt j := by
    exact shrl_zshiftr_int_unsigned
      (CompCert4Lean.Lib.Integers.Int64.signed x) n1
  have hsignedInner :
      CompCert4Lean.Lib.Integers.Int64.signed
          (CompCert4Lean.Lib.Integers.Int64.shr' x n1) = zOfInt j := by
    change CompCert4Lean.Lib.Integers.Int64.signed
      (CompCert4Lean.Lib.Integers.Int64.repr
        (ZArith.BinInt.Z.shiftr
          (CompCert4Lean.Lib.Integers.Int64.signed x)
          (CompCert4Lean.Lib.Integers.Int.unsigned n1))) = zOfInt j
    rw [hshift1]
    exact shrl_int64_signed_repr_int j hjlo hjhi
  have hxz : zOfInt sx = CompCert4Lean.Lib.Integers.Int64.signed x :=
    zOfInt_intOfZ _
  have hcomp :
      ZArith.BinInt.Z.shiftr
          (ZArith.BinInt.Z.shiftr
            (CompCert4Lean.Lib.Integers.Int64.signed x)
            (CompCert4Lean.Lib.Integers.Int.unsigned n1))
          (CompCert4Lean.Lib.Integers.Int.unsigned n) =
        ZArith.BinInt.Z.shiftr
          (CompCert4Lean.Lib.Integers.Int64.signed x)
          (CompCert4Lean.Lib.Integers.Int.unsigned
            (CompCert4Lean.Lib.Integers.Int.add n n1)) := by
    rw [← hxz, shrl_int_unsigned_z n1, shrl_int_unsigned_z n,
      shrl_int_unsigned_z (CompCert4Lean.Lib.Integers.Int.add n n1), haddVal,
      Nat.add_comm]
    exact shrl_zshiftr_nat sx n1.val n.val
  change CompCert4Lean.Lib.Integers.Int64.repr
      (ZArith.BinInt.Z.shiftr
        (CompCert4Lean.Lib.Integers.Int64.signed
          (CompCert4Lean.Lib.Integers.Int64.shr' x n1))
        (CompCert4Lean.Lib.Integers.Int.unsigned n)) =
    CompCert4Lean.Lib.Integers.Int64.repr
      (ZArith.BinInt.Z.shiftr
        (CompCert4Lean.Lib.Integers.Int64.signed x)
        (CompCert4Lean.Lib.Integers.Int.unsigned
          (CompCert4Lean.Lib.Integers.Int.add n n1)))
  rw [hsignedInner]
  apply congrArg CompCert4Lean.Lib.Integers.Int64.repr
  calc
    ZArith.BinInt.Z.shiftr (zOfInt j)
        (CompCert4Lean.Lib.Integers.Int.unsigned n) =
      ZArith.BinInt.Z.shiftr
          (ZArith.BinInt.Z.shiftr
            (CompCert4Lean.Lib.Integers.Int64.signed x)
            (CompCert4Lean.Lib.Integers.Int.unsigned n1))
          (CompCert4Lean.Lib.Integers.Int.unsigned n) :=
      congrArg
        (fun z => ZArith.BinInt.Z.shiftr z
          (CompCert4Lean.Lib.Integers.Int.unsigned n)) hshift1.symm
    _ = _ := hcomp

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong

private theorem shrl_int_eq_true_zero (n : CCInt)
    (h : CompCert4Lean.Lib.Integers.Int.eq n
      CompCert4Lean.Lib.Integers.Int.zero = true) :
    n = CompCert4Lean.Lib.Integers.Int.zero := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext
  have hd : decide (n.intval =
      CompCert4Lean.Lib.Integers.Int.zero.intval) = true := by
    simpa [CompCert4Lean.Lib.Integers.Int.eq,
      CompCert4Lean.Lib.Integers.WordCore.eq] using h
  exact of_decide_eq_true hd

private theorem shrl_int64_shr_zero (x : CCInt64) :
    CompCert4Lean.Lib.Integers.Int64.shr' x
      CompCert4Lean.Lib.Integers.Int.zero = x := by
  change CompCert4Lean.Lib.Integers.Int64.repr
      (ZArith.BinInt.Z.shiftr
        (CompCert4Lean.Lib.Integers.Int64.signed x)
        (CompCert4Lean.Lib.Integers.Int.unsigned
          CompCert4Lean.Lib.Integers.Int.zero)) = x
  rw [shrl_zshiftr_int_unsigned]
  have hz : CompCert4Lean.Lib.Integers.Int.zero.val = 0 := rfl
  rw [hz]
  simp only [Int.pow_zero, Int.ediv_one]
  rw [zOfInt_intOfZ]
  exact shrl_int64_repr_signed x

private theorem shrl_val_zero (x : val) :
    Val.lessdef
      (Val.shrl x (.Vint CompCert4Lean.Lib.Integers.Int.zero)) x := by
  cases x with
  | Vlong n =>
      change Val.lessdef
        (if CompCert4Lean.Lib.Integers.Int.ltu
            CompCert4Lean.Lib.Integers.Int.zero
            CompCert4Lean.Lib.Integers.Int64.iwordsize' then
          .Vlong (CompCert4Lean.Lib.Integers.Int64.shr' n
            CompCert4Lean.Lib.Integers.Int.zero)
        else .Vundef) (.Vlong n)
      have hlt : CompCert4Lean.Lib.Integers.Int.ltu
          CompCert4Lean.Lib.Integers.Int.zero
          CompCert4Lean.Lib.Integers.Int64.iwordsize' = true := by decide
      rw [if_pos hlt, shrl_int64_shr_zero]
      exact Val.lessdef_refl _
  | _ => exact Val.lessdef_undef _

private theorem eval_shrlimm_aux_suffix
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    ∀ (xi : ExternalCalls) (prog : program) (hf : HelperFunctions),
      CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
      ∀ (sp : val) (e : env) (m : mem) (n : CCInt),
        unary_constructor_sound (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi prog sp e m
          (fun a => shrlimm a n) (fun v => Val.shrl v (.Vint n)) := by
  intro xi prog hf hdecl sp e m n le a x h
  unfold shrlimm
  cases hz : CompCert4Lean.Lib.Integers.Int.eq n
      CompCert4Lean.Lib.Integers.Int.zero with
  | true =>
      have hn := shrl_int_eq_true_zero n hz
      simp only [hz, if_true]
      subst n
      exact ⟨x, h, shrl_val_zero x⟩
  | false =>
      cases hlt : CompCert4Lean.Lib.Integers.Int.ltu n
          CompCert4Lean.Lib.Integers.Int64.iwordsize' with
      | false =>
          simp only [hz, if_false, hlt, Bool.not_false, if_true]
          refine ⟨Val.shrl x (.Vint n), ?_, Val.lessdef_refl _⟩
          apply eval_expr.eval_Eop le Oshrl
            (Econs a (Econs (Eop (Ointconst n) Enil) Enil))
            [x, .Vint n] (Val.shrl x (.Vint n))
          · exact eval_exprlist.cons le a _ x [.Vint n] h
              (eval_exprlist.cons le (Eop (Ointconst n) Enil) Enil
                (.Vint n) []
                (eval_expr.eval_Eop le (Ointconst n) Enil [] (.Vint n)
                  (eval_exprlist.nil le) rfl)
                (eval_exprlist.nil le))
          · rfl
      | true =>
          simp only [hz, if_false, hlt, Bool.not_true]
          cases hmatch : shrlimm_match a with
          | shrlimm_case1 n1 =>
              have hx : x = .Vlong n1 := eval_longconst_value xi
                (Genv.globalenv prog) sp e m le n1 x
                (by simpa [hmatch] using h)
              subst x
              refine ⟨.Vlong (CompCert4Lean.Lib.Integers.Int64.shr' n1 n), ?_, ?_⟩
              · run_tac
                  let env ← getEnv
                  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
                      let s := toString name
                      s.startsWith "_private.CompCert4Lean.X86.SelectLong." &&
                        s.endsWith "Int64.shr'")
                    | throwError "frozen SelectLong Int64.shr' alias not found"
                  evalTactic (← `(tactic| unfold $(Lean.mkIdent name)))
                simpa [longconst, hmatch] using
                  (eval_longconst xi prog sp e m le
                    (CompCert4Lean.Lib.Integers.Int64.shr' n1 n))
              · change Val.lessdef
                  (if CompCert4Lean.Lib.Integers.Int.ltu n
                      CompCert4Lean.Lib.Integers.Int64.iwordsize' then
                    .Vlong (CompCert4Lean.Lib.Integers.Int64.shr' n1 n)
                  else .Vundef) _
                rw [if_pos hlt]
                exact Val.lessdef_refl _
          | shrlimm_case2 n1 t1 =>
              have horig := h
              cases h with
              | eval_Eop le' op al vl v hargs hop =>
                  cases hargs with
                  | cons _ a' al' v1 vl' hhead htail =>
                      cases htail with
                      | nil _ =>
                          change some (Val.shrl v1 (.Vint n1)) = some x at hop
                          cases hop
                          cases hsum : CompCert4Lean.Lib.Integers.Int.ltu
                              (CompCert4Lean.Lib.Integers.Int.add n n1)
                              CompCert4Lean.Lib.Integers.Int64.iwordsize' with
                          | false =>
                              refine ⟨Val.shrl (Val.shrl v1 (.Vint n1))
                                (.Vint n), ?_, Val.lessdef_refl _⟩
                              simp only [hmatch, hsum, if_false]
                              apply eval_expr.eval_Eop le (Oshrlimm n)
                                (Econs (Eop (Oshrlimm n1) (Econs t1 Enil)) Enil)
                                [Val.shrl v1 (.Vint n1)] _
                              · exact eval_exprlist.cons le _ Enil _ [] horig
                                  (eval_exprlist.nil le)
                              · rfl
                          | true =>
                              refine ⟨Val.shrl v1
                                (.Vint (CompCert4Lean.Lib.Integers.Int.add n n1)), ?_, ?_⟩
                              · simp only [hmatch, hsum, if_true]
                                apply eval_expr.eval_Eop le
                                  (Oshrlimm (CompCert4Lean.Lib.Integers.Int.add n n1))
                                  (Econs t1 Enil) [v1] _
                                · exact eval_exprlist.cons le t1 Enil v1 []
                                    (by simpa [hmatch] using hhead)
                                    (eval_exprlist.nil le)
                                · rfl
                              · cases v1 with
                                | Vlong i =>
                                    cases hn1 : CompCert4Lean.Lib.Integers.Int.ltu n1
                                        CompCert4Lean.Lib.Integers.Int64.iwordsize' with
                                    | false =>
                                        simp [Val.shrl, hn1]
                                        exact Val.lessdef_undef _
                                    | true =>
                                        simp only [Val.shrl, hn1, hlt, hsum,
                                          if_true]
                                        run_tac
                                          let env ← getEnv
                                          let some (name, _) := env.constants.toList.find?
                                              (fun (name, _) =>
                                                let s := toString name
                                                s.startsWith
                                                    "_private.CompCert4Lean.Common.Values." &&
                                                  s.endsWith "Int64.shr'")
                                            | throwError
                                                "frozen Values Int64.shr' alias not found"
                                          evalTactic
                                            (← `(tactic| unfold $(Lean.mkIdent name)))
                                        rw [shrl_int64_shr_comp i n1 n hn1 hlt]
                                        exact Val.lessdef_refl _
                                | _ => exact Val.lessdef_undef _
          | shrlimm_default e1 =>
              refine ⟨Val.shrl x (.Vint n), ?_, Val.lessdef_refl _⟩
              simp only [hmatch]
              apply eval_expr.eval_Eop le (Oshrlimm n) (Econs a Enil)
                [x] (Val.shrl x (.Vint n))
              · exact eval_exprlist.cons le a Enil x [] h
                  (eval_exprlist.nil le)
              · rfl

theorem eval_shrl
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_shrlStatement binary64_certificate binary32_certificate := by
  unfold eval_shrlStatement binary_constructor_sound
  intro xi prog hf hdecl sp e m le a x b y ha hb
  unfold shrl
  cases hmatch : CompCert4Lean.Backend.SplitLong.is_intconst b with
  | some n =>
      have hy : y = .Vint n :=
        CompCert4Lean.Backend.SplitLongproof.is_intconst_sound
          xi prog sp e m le b y n hmatch hb
      subst y
      obtain ⟨v, hv, hd⟩ := eval_shrlimm_aux_suffix
        xi prog hf hdecl sp e m n le a x ha
      exact ⟨v, by simpa only [hmatch] using hv, hd⟩
  | none =>
      refine ⟨Val.shrl x y, ?_, Val.lessdef_refl _⟩
      simp only [hmatch]
      apply eval_expr.eval_Eop le Oshrl (Econs a (Econs b Enil)) [x, y]
        (Val.shrl x y)
      · exact eval_exprlist.cons le a (Econs b Enil) x [y] ha
          (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))
      · rfl

end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong

theorem eval_mullhu
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_mullhuStatement binary64_certificate binary32_certificate := by
  unfold eval_mullhuStatement unary_constructor_sound
  intro xi prog hf hdecl sp e m n le a x h
  refine ⟨Val.mullhu x (.Vlong n), ?_, Val.lessdef_refl _⟩
  unfold mullhu
  apply eval_expr.eval_Eop le Omullhu
    (Econs a (Econs (longconst n) Enil)) [x, .Vlong n]
    (Val.mullhu x (.Vlong n))
  · exact eval_exprlist.cons le a (Econs (longconst n) Enil) x [.Vlong n] h
      (eval_exprlist.cons le (longconst n) Enil (.Vlong n) []
        (CompCert4Lean.X86.SelectLongproof.eval_longconst xi prog sp e m le n)
        (eval_exprlist.nil le))
  · rfl

theorem eval_mullhs
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_mullhsStatement binary64_certificate binary32_certificate := by
  unfold eval_mullhsStatement unary_constructor_sound
  intro xi prog hf hdecl sp e m n le a x h
  refine ⟨Val.mullhs x (.Vlong n), ?_, Val.lessdef_refl _⟩
  unfold mullhs
  apply eval_expr.eval_Eop le Omullhs
    (Econs a (Econs (longconst n) Enil)) [x, .Vlong n]
    (Val.mullhs x (.Vlong n))
  · exact eval_exprlist.cons le a (Econs (longconst n) Enil) x [.Vlong n] h
      (eval_exprlist.cons le (longconst n) Enil (.Vlong n) []
        (CompCert4Lean.X86.SelectLongproof.eval_longconst xi prog sp e m le n)
        (eval_exprlist.nil le))
  · rfl

end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong

theorem eval_shrxlimm
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_shrxlimmStatement binary64_certificate binary32_certificate := by
  unfold eval_shrxlimmStatement
  intro xi prog hf hdecl sp e m le a n x z ha hz
  unfold shrxlimm
  by_cases hn : CompCert4Lean.Lib.Integers.Int.eq n
      CompCert4Lean.Lib.Integers.Int.zero = true
  · have hn' := shrl_int_eq_true_zero n hn
    rw [if_pos hn]
    subst n
    refine ⟨x, ha, ?_⟩
    cases x with
    | Vlong i =>
        simp only [Val.shrxl] at hz
        split at hz
        · cases hz
          change Val.lessdef
            (.Vlong (CompCert4Lean.Lib.Integers.Int64.shrx' i
              CompCert4Lean.Lib.Integers.Int.zero)) (.Vlong i)
          have hshl : CompCert4Lean.Lib.Integers.Int64.shl'
              CompCert4Lean.Lib.Integers.Int64.one
              CompCert4Lean.Lib.Integers.Int.zero =
              CompCert4Lean.Lib.Integers.Int64.one := by
            rfl
          rw [CompCert4Lean.Lib.Integers.Int64.shrx', hshl]
          have hdiv : CompCert4Lean.Lib.Integers.Int64.divs i
              CompCert4Lean.Lib.Integers.Int64.one = i := by
            unfold CompCert4Lean.Lib.Integers.Int64.divs
              CompCert4Lean.Lib.Integers.WordCore.divs
            have hone : CompCert4Lean.Lib.Integers.WordCore.signed
                CompCert4Lean.Lib.Integers.Int64.one =
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1 := by
              rfl
            rw [hone]
            change CompCert4Lean.Lib.Integers.Int64.repr
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.quot
                (CompCert4Lean.Lib.Integers.WordCore.signed i)
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1)) = i
            have honez :
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1 =
                  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Zpos
                    CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH := by
              rfl
            rw [honez,
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.quot_1_r]
            exact shrl_int64_repr_signed i
          rw [hdiv]
          exact Val.lessdef_refl _
        · cases hz
    | Vundef => simp [Val.shrxl] at hz
    | Vint _ => simp [Val.shrxl] at hz
    | Vfloat _ => simp [Val.shrxl] at hz
    | Vsingle _ => simp [Val.shrxl] at hz
    | Vptr _ _ => simp [Val.shrxl] at hz
  · rw [if_neg hn]
    refine ⟨z, ?_, Val.lessdef_refl _⟩
    apply eval_expr.eval_Eop le (Oshrxlimm n) (Econs a Enil) [x] z
    · exact eval_exprlist.cons le a Enil x [] ha (eval_exprlist.nil le)
    · exact hz

end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong

theorem eval_divls_base
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_divls_baseStatement binary64_certificate binary32_certificate := by
  unfold eval_divls_baseStatement partial_binary_constructor_sound
  intro xi prog hf hdecl sp e m le a x b y z ha hb hz
  refine ⟨z, ?_, Val.lessdef_refl _⟩
  unfold divls_base
  apply eval_expr.eval_Eop le Odivl (Econs a (Econs b Enil)) [x, y] z
  · exact eval_exprlist.cons le a (Econs b Enil) x [y] ha
      (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))
  · exact hz

theorem eval_modls_base
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_modls_baseStatement binary64_certificate binary32_certificate := by
  unfold eval_modls_baseStatement partial_binary_constructor_sound
  intro xi prog hf hdecl sp e m le a x b y z ha hb hz
  refine ⟨z, ?_, Val.lessdef_refl _⟩
  unfold modls_base
  apply eval_expr.eval_Eop le Omodl (Econs a (Econs b Enil)) [x, y] z
  · exact eval_exprlist.cons le a (Econs b Enil) x [y] ha
      (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))
  · exact hz

theorem eval_divlu_base
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_divlu_baseStatement binary64_certificate binary32_certificate := by
  unfold eval_divlu_baseStatement partial_binary_constructor_sound
  intro xi prog hf hdecl sp e m le a x b y z ha hb hz
  refine ⟨z, ?_, Val.lessdef_refl _⟩
  unfold divlu_base
  apply eval_expr.eval_Eop le Odivlu (Econs a (Econs b Enil)) [x, y] z
  · exact eval_exprlist.cons le a (Econs b Enil) x [y] ha
      (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))
  · exact hz

theorem eval_modlu_base
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_modlu_baseStatement binary64_certificate binary32_certificate := by
  unfold eval_modlu_baseStatement partial_binary_constructor_sound
  intro xi prog hf hdecl sp e m le a x b y z ha hb hz
  refine ⟨z, ?_, Val.lessdef_refl _⟩
  unfold modlu_base
  apply eval_expr.eval_Eop le Omodlu (Econs a (Econs b Enil)) [x, y] z
  · exact eval_exprlist.cons le a (Econs b Enil) x [y] ha
      (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))
  · exact hz

end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong

theorem eval_longoffloat
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_longoffloatStatement binary64_certificate binary32_certificate := by
  unfold eval_longoffloatStatement
  intro xi prog hf hdecl sp e m le a x y ha hy
  refine ⟨y, ?_, Val.lessdef_refl _⟩
  unfold longoffloat
  exact eval_expr.eval_Eop le Olongoffloat (Econs a Enil) [x] y
    (eval_exprlist.cons le a Enil x [] ha (eval_exprlist.nil le)) hy

theorem eval_floatoflong
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_floatoflongStatement binary64_certificate binary32_certificate := by
  unfold eval_floatoflongStatement
  intro xi prog hf hdecl sp e m le a x y ha hy
  refine ⟨y, ?_, Val.lessdef_refl _⟩
  unfold floatoflong
  exact eval_expr.eval_Eop le Ofloatoflong (Econs a Enil) [x] y
    (eval_exprlist.cons le a Enil x [] ha (eval_exprlist.nil le)) hy

end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong

private theorem selectLong_swap_cmpl_bool
    (c : comparison) (x y : val) :
    Val.cmpl_bool (swap_comparison c) x y = Val.cmpl_bool c y x := by
  cases c <;> cases x <;> cases y <;>
    simp [Val.cmpl_bool, swap_comparison, Int64.cmp, WordCore.cmp,
      WordCore.eq, eq_comm]

private theorem selectLong_cmpl_result
    (c : comparison) (x y v : val)
    (h : Val.cmpl c x y = some v) :
    some (Val.of_optbool (Val.cmpl_bool c x y)) = some v := by
  unfold Val.cmpl at h
  cases hc : Val.cmpl_bool c x y with
  | none => simp [hc] at h
  | some bv =>
      simp [hc] at h
      rw [← h]
      cases bv <;> rfl

theorem eval_cmpl
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_cmplStatement binary64_certificate binary32_certificate := by
  unfold eval_cmplStatement
  intro xi prog sp e m c le a x b y v ha hb hv
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
            (selectLong_cmpl_result c x y v hv)
      | some n2 =>
          have hy : y = .Vlong n2 :=
            is_longconst_sound xi prog sp e m y b n2 le hcb hb
          subst y
          simp only [hca, hcb]
          exact eval_expr.eval_Eop le (Ocmp (Ccomplimm c n2))
            (Econs a Enil) [x] v
            (eval_exprlist.cons le a Enil x [] ha (eval_exprlist.nil le))
            (selectLong_cmpl_result c x (.Vlong n2) v hv)
  | some n1 =>
      have hx : x = .Vlong n1 :=
        is_longconst_sound xi prog sp e m x a n1 le hca ha
      subst x
      cases hcb : is_longconst b with
      | none =>
          simp only [hca, hcb]
          apply eval_expr.eval_Eop le (Ocmp (Ccomplimm (swap_comparison c) n1))
            (Econs b Enil) [y] v
            (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))
          change some (Val.of_optbool
            (Val.cmpl_bool (swap_comparison c) y (.Vlong n1))) = some v
          rw [selectLong_swap_cmpl_bool]
          exact selectLong_cmpl_result c (.Vlong n1) y v hv
      | some n2 =>
          have hy : y = .Vlong n2 :=
            is_longconst_sound xi prog sp e m y b n2 le hcb hb
          subst y
          simp only [hca, hcb]
          apply eval_expr.eval_Eop le (Ointconst
            (if Int64.cmp c n1 n2 then Int.one else Int.zero)) Enil [] v
            (eval_exprlist.nil le)
          unfold Val.cmpl Val.cmpl_bool at hv
          simp only [Option.map_some] at hv
          rw [← hv]
          cases Int64.cmp c n1 n2 <;> rfl

end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong

private theorem selectLong_swap_int64_cmpu
    (c : comparison) (x y : Int64.int) :
    Int64.cmpu (swap_comparison c) x y = Int64.cmpu c y x := by
  cases c <;>
    simp [Int64.cmpu, WordCore.cmpu, swap_comparison, WordCore.eq, eq_comm]

private theorem selectLong_swap_cmplu_bool_long
    (valid : CompCert4Lean.Common.Values.block →
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z → Bool)
    (c : comparison) (n : Int64.int) (y : val) :
    Val.cmplu_bool valid (swap_comparison c) y (.Vlong n) =
      Val.cmplu_bool valid c (.Vlong n) y := by
  cases y with
  | Vlong y =>
      exact congrArg some (selectLong_swap_int64_cmpu c y n)
  | Vundef => cases c <;> rfl
  | Vint y => cases c <;> rfl
  | Vfloat y => cases c <;> rfl
  | Vsingle y => cases c <;> rfl
  | Vptr b ofs =>
      cases c <;>
        simp [Val.cmplu_bool, Val.cmp_different_blocks, swap_comparison]

private theorem selectLong_cmplu_result
    (valid : CompCert4Lean.Common.Values.block →
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z → Bool)
    (c : comparison) (x y v : val)
    (h : Val.cmplu valid c x y = some v) :
    some (Val.of_optbool (Val.cmplu_bool valid c x y)) = some v := by
  unfold Val.cmplu at h
  cases hc : Val.cmplu_bool valid c x y with
  | none => simp [hc] at h
  | some bv =>
      simp [hc] at h
      rw [← h]
      cases bv <;> rfl

theorem eval_cmplu
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_cmpluStatement binary64_certificate binary32_certificate := by
  unfold eval_cmpluStatement
  intro xi prog sp e m c le a x b y v ha hb hv
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
            (selectLong_cmplu_result (fun b ofs => Mem.valid_pointer m b ofs)
              c x y v hv)
      | some n2 =>
          have hy : y = .Vlong n2 :=
            is_longconst_sound xi prog sp e m y b n2 le hcb hb
          subst y
          simp only [hca, hcb]
          exact eval_expr.eval_Eop le (Ocmp (Ccompluimm c n2))
            (Econs a Enil) [x] v
            (eval_exprlist.cons le a Enil x [] ha (eval_exprlist.nil le))
            (selectLong_cmplu_result (fun b ofs => Mem.valid_pointer m b ofs)
              c x (.Vlong n2) v hv)
  | some n1 =>
      have hx : x = .Vlong n1 :=
        is_longconst_sound xi prog sp e m x a n1 le hca ha
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
          rw [selectLong_swap_cmplu_bool_long
            (valid := fun b ofs => Mem.valid_pointer m b ofs)]
          exact selectLong_cmplu_result (fun b ofs => Mem.valid_pointer m b ofs)
            c (.Vlong n1) y v hv
      | some n2 =>
          have hy : y = .Vlong n2 :=
            is_longconst_sound xi prog sp e m y b n2 le hcb hb
          subst y
          simp only [hca, hcb]
          apply eval_expr.eval_Eop le (Ointconst
            (if Int64.cmpu c n1 n2 then Int.one else Int.zero)) Enil [] v
            (eval_exprlist.nil le)
          unfold Val.cmplu Val.cmplu_bool at hv
          simp only [Option.map_some] at hv
          rw [← hv]
          cases Int64.cmpu c n1 n2 <;> rfl

end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong

theorem eval_longofsingle
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_longofsingleStatement binary64_certificate binary32_certificate := by
  unfold eval_longofsingleStatement
  intro xi prog hf hdecl sp e m le a x y ha hy
  refine ⟨y, ?_, Val.lessdef_refl _⟩
  unfold longofsingle
  exact eval_expr.eval_Eop le Olongofsingle (Econs a Enil) [x] y
    (eval_exprlist.cons le a Enil x [] ha (eval_exprlist.nil le)) hy

end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong

theorem eval_singleoflong
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_singleoflongStatement binary64_certificate binary32_certificate := by
  unfold eval_singleoflongStatement
  intro xi prog hf hdecl sp e m le a x y ha hy
  refine ⟨y, ?_, Val.lessdef_refl _⟩
  unfold singleoflong
  exact eval_expr.eval_Eop le Osingleoflong (Econs a Enil) [x] y
    (eval_exprlist.cons le a Enil x [] ha (eval_exprlist.nil le)) hy

end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof

theorem eval_andlimm
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_andlimmStatement binary64_certificate binary32_certificate := by
  unfold eval_andlimmStatement
  intro xi prog sp e m n
  exact eval_andlimm_aux xi prog sp e m n

end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong
open CompCert4Lean.X86.SelectOp (same_expr_pure)

private theorem orl_word_unsigned (bits : Nat) (x : WordCore.Word bits) :
    x.intval = ZArith.BinInt.Z.of_nat x.val := by
  apply (ZArith.Znat.Z2Nat.id x.intval _).symm
  have h := x.intrange.1
  change (-1 : Int) < intOfZ x.intval at h
  change 0 ≤ intOfZ x.intval
  omega

private theorem orl_repr_nat_val (bits n : Nat) :
    (WordCore.repr bits (ZArith.BinInt.Z.of_nat n)).val = n % 2 ^ bits := by
  rw [show ZArith.BinInt.Z.of_nat n = zOfInt (Int.ofNat n) by rfl,
    suffixWordValRepr64]
  change ((n : Int) % ((2 ^ bits : Nat) : Int)).toNat = _
  rw [← Int.natCast_emod]
  rfl

private theorem orl_shl_val (x : WordCore.Word 64) (n : WordCore.Word 32) :
    (Int64.shl' x n).val = (x.val * 2 ^ n.val) % 2 ^ 64 := by
  change (WordCore.repr 64 (ZArith.BinInt.Z.shiftl x.intval n.intval)).val = _
  rw [orl_word_unsigned 64 x, orl_word_unsigned 32 n]
  have hs : ZArith.BinInt.Z.shiftl (zOfNat x.val) (zOfNat n.val) =
      zOfNat (x.val * 2 ^ n.val) := by
    unfold ZArith.BinInt.Z.shiftl
    simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
      Int.ofNat_eq_natCast, Int.natCast_nonneg, ↓reduceIte,
      Int.toNat_natCast, Int.natCast_mul, Int.natCast_pow]
    rfl
  unfold zOfNat at hs
  rw [hs, orl_repr_nat_val]

private theorem orl_shru_val (x : WordCore.Word 64) (n : WordCore.Word 32) :
    (Int64.shru' x n).val = x.val / 2 ^ n.val := by
  change (WordCore.repr 64 (ZArith.BinInt.Z.shiftr x.intval n.intval)).val = _
  rw [orl_word_unsigned 64 x, orl_word_unsigned 32 n]
  have hs : ZArith.BinInt.Z.shiftr (zOfNat x.val) (zOfNat n.val) =
      zOfNat (x.val / 2 ^ n.val) := by
    unfold ZArith.BinInt.Z.shiftr
    simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
      Int.ofNat_eq_natCast, Int.natCast_nonneg, ↓reduceIte,
      Int.toNat_natCast, Int.natCast_pow]
    exact congrArg zOfInt Int.ofNat_ediv_ofNat
  unfold zOfNat at hs
  rw [hs, orl_repr_nat_val]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.toFin.isLt)

private theorem orl_nat_or_mod (a b w : Nat) (hb : b < 2 ^ w) :
    Nat.lor (a % 2 ^ w) b = Nat.lor b a % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.lor_eq]
  rw [Nat.testBit_or, Nat.testBit_mod_two_pow,
    Nat.testBit_mod_two_pow, Nat.testBit_or]
  by_cases hk : k < w
  · simp only [decide_eq_true hk, Bool.true_and]
    exact Bool.or_comm _ _
  · have hpow : 2 ^ w ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hk)
    have hfb : b.testBit k = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb hpow)
    simp [hk, hfb]

private theorem orl_rotate_word (x : WordCore.Word 64) (n1 n2 : WordCore.Word 32)
    (h1 : Int.ltu n1 Int64.iwordsize' = true)
    (h2 : Int.ltu n2 Int64.iwordsize' = true)
    (hsum : CompCert4Lean.Lib.Integers.Int.add n1 n2 = Int64.iwordsize') :
    Int64.or (Int64.shl' x n1) (Int64.shru' x n2) =
      Int64.ror x (Int64.repr (Int.unsigned n2)) := by
  have hn1 := shrl_int_ltu_iwordsize_val n1 h1
  have hn2 := shrl_int_ltu_iwordsize_val n2 h2
  change n1.val < 64 at hn1
  change n2.val < 64 at hn2
  have hadd : (CompCert4Lean.Lib.Integers.Int.add n1 n2).val = (n1.val + n2.val) % 2 ^ 32 := by
    change (WordCore.repr 32 (ZArith.BinInt.Z.add n1.intval n2.intval)).val = _
    rw [orl_word_unsigned 32 n1, orl_word_unsigned 32 n2]
    have ha : ZArith.BinInt.Z.add (ZArith.BinInt.Z.of_nat n1.val)
        (ZArith.BinInt.Z.of_nat n2.val) =
        ZArith.BinInt.Z.of_nat (n1.val + n2.val) := by
      unfold ZArith.BinInt.Z.add
      simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
        Int.ofNat_eq_natCast, Int.natCast_add]
    rw [ha, orl_repr_nat_val]
  have hn : n1.val + n2.val = 64 := by
    have he := congrArg (fun q : CCInt => q.val) hsum
    rw [hadd, Nat.mod_eq_of_lt (by omega)] at he
    exact he
  have hn2repr : (Int64.repr (Int.unsigned n2)).val = n2.val := by
    rw [shrl_int_unsigned_z n2]
    exact repr_val_of_lt64 n2.val (by omega)
  apply WordCore.ext_of_val_eq
  rw [int64_or_val, orl_shl_val x n1, orl_shru_val x n2]
  change Nat.lor ((x.val * 2 ^ n1.val) % 2 ^ 64) (x.val / 2 ^ n2.val) =
    (WordCore.repr 64 (zOfNat (Nat.lor
      (Nat.shiftRight x.val ((Int64.repr (Int.unsigned n2)).val % 64))
      (Nat.shiftLeft x.val (64 - (Int64.repr (Int.unsigned n2)).val % 64))))).val
  rw [hn2repr, Nat.mod_eq_of_lt hn2, show 64 - n2.val = n1.val by omega,
    orl_repr_nat_val]
  rw [← Nat.shiftLeft_eq x.val n1.val, ← Nat.shiftRight_eq_div_pow x.val n2.val]
  exact orl_nat_or_mod _ _ 64
    (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) x.toFin.isLt)

private theorem orl_val_comm (x y : val) : Val.orl x y = Val.orl y x := by
  cases x <;> cases y <;> try rfl
  case Vlong.Vlong x y => exact congrArg val.Vlong (int64_or_commut x y)

private theorem orl_rotate_value (v : val) (n1 n2 : CCInt)
    (hsum : CompCert4Lean.Lib.Integers.Int.add n1 n2 = Int64.iwordsize') :
    Val.lessdef (Val.orl (Val.shll v (.Vint n1)) (Val.shrlu v (.Vint n2)))
      (Val.rorl v (.Vint n2)) := by
  cases v with
  | Vlong x =>
      by_cases h1 : Int.ltu n1 Int64.iwordsize' = true
      · by_cases h2 : Int.ltu n2 Int64.iwordsize' = true
        · simp only [Val.shll, Val.shrlu, h1, h2, ↓reduceIte, Val.orl, Val.rorl]
          change Val.lessdef
            (.Vlong (Int64.or (Int64.shl' x n1) (Int64.shru' x n2)))
            (.Vlong (Int64.ror x (Int64.repr (Int.unsigned n2))))
          rw [orl_rotate_word x n1 n2 h1 h2 hsum]
          exact Val.lessdef_refl _
        · simp [Val.shll, Val.shrlu, h1, h2, Val.orl, Val.rorl]
          exact Val.lessdef_undef _
      · simp [Val.shll, h1, Val.orl, Val.rorl]
        exact Val.lessdef_undef _
  | _ => exact Val.lessdef_undef _


private theorem orl_same_value
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (a b : expr) (le : letenv) (x y : val)
    (hsame : same_expr_pure a b = true)
    (ha : eval_expr xi ge sp e m le a x)
    (hb : eval_expr xi ge sp e m le b y) : x = y := by
  cases a <;> cases b <;> simp [same_expr_pure] at hsame
  subst_vars
  cases ha with
  | var _ _ _ hget1 =>
      cases hb with
      | var _ _ _ hget2 =>
          exact Option.some.inj (hget1.symm.trans hget2)

private theorem orl_shll_inv
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (le : letenv) (t : expr) (n : CCInt) (x : val)
    (h : eval_expr xi ge sp e m le (Eop (Oshllimm n) (Econs t Enil)) x) :
    ∃ v, eval_expr xi ge sp e m le t v ∧ x = Val.shll v (.Vint n) := by
  cases h with
  | eval_Eop _ _ _ _ _ hargs hop =>
      cases hargs with
      | cons _ _ _ v _ hhead htail =>
          cases htail with
          | nil _ =>
              change some (Val.shll v (.Vint n)) = some x at hop
              cases hop
              exact ⟨v, hhead, rfl⟩

private theorem orl_shrlu_inv
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (xi : ExternalCalls) (ge : genv) (sp : val) (e : env) (m : mem)
    (le : letenv) (t : expr) (n : CCInt) (x : val)
    (h : eval_expr xi ge sp e m le (Eop (Oshrluimm n) (Econs t Enil)) x) :
    ∃ v, eval_expr xi ge sp e m le t v ∧ x = Val.shrlu v (.Vint n) := by
  cases h with
  | eval_Eop _ _ _ _ _ hargs hop =>
      cases hargs with
      | cons _ _ _ v _ hhead htail =>
          cases htail with
          | nil _ =>
              change some (Val.shrlu v (.Vint n)) = some x at hop
              cases hop
              exact ⟨v, hhead, rfl⟩

private theorem orl_int_eq (x y : CCInt)
    (h : Int.eq x y = true) : x = y := by
  apply WordCore.ext
  change decide (x.intval = y.intval) = true at h
  exact of_decide_eq_true h

theorem eval_orl
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_orlStatement binary64_certificate binary32_certificate := by
  unfold eval_orlStatement binary_constructor_sound
  intro xi prog sp e m le a x b y ha hb
  have hdefault : ∃ v, eval_expr xi (Genv.globalenv prog) sp e m le
      (Eop Oorl (Econs a (Econs b Enil))) v ∧ Val.lessdef (Val.orl x y) v := by
    refine ⟨Val.orl x y, ?_, Val.lessdef_refl _⟩
    exact eval_expr.eval_Eop le Oorl (Econs a (Econs b Enil)) [x, y] _
      (eval_exprlist.cons le a (Econs b Enil) x [y] ha
        (eval_exprlist.cons le b Enil y [] hb (eval_exprlist.nil le))) rfl
  cases hmatch : orl_match a b with
  | orl_case1 n1 t2 =>
      have hx : x = .Vlong n1 := eval_longconst_value xi
        (Genv.globalenv prog) sp e m le n1 x (by simpa [hmatch] using ha)
      subst x
      obtain ⟨v, hv, hd⟩ := eval_orlimm xi prog sp e m n1 le b y hb
      refine ⟨v, ?_, ?_⟩
      · simpa [orl, hmatch] using hv
      · rw [orl_val_comm]
        exact hd
  | orl_case2 t1 n2 =>
      have hy : y = .Vlong n2 := eval_longconst_value xi
        (Genv.globalenv prog) sp e m le n2 y (by simpa [hmatch] using hb)
      subst y
      obtain ⟨v, hv, hd⟩ := eval_orlimm xi prog sp e m n2 le a x ha
      refine ⟨v, ?_, hd⟩
      simpa [orl, hmatch] using hv
  | orl_case3 n1 t1 n2 t2 =>
      by_cases hrot : (Int.eq (CompCert4Lean.Lib.Integers.Int.add n1 n2)
          Int64.iwordsize' && same_expr_pure t1 t2) = true
      · obtain ⟨heq, hsame⟩ := Bool.and_eq_true_iff.mp hrot
        have hsum := orl_int_eq _ _ heq
        obtain ⟨vx, htx, hx⟩ := orl_shll_inv xi (Genv.globalenv prog)
          sp e m le t1 n1 x ha
        obtain ⟨vy, hty, hy⟩ := orl_shrlu_inv xi (Genv.globalenv prog)
          sp e m le t2 n2 y hb
        have hv := orl_same_value xi (Genv.globalenv prog) sp e m
          t1 t2 le vx vy hsame htx hty
        subst vy
        subst x
        subst y
        refine ⟨Val.rorl vx (.Vint n2), ?_, orl_rotate_value vx n1 n2 hsum⟩
        simp only [orl, hmatch, if_pos hrot]
        exact eval_expr.eval_Eop le (Ororlimm n2) (Econs t1 Enil) [vx] _
          (eval_exprlist.cons le t1 Enil vx [] htx (eval_exprlist.nil le)) rfl
      · simpa only [orl, hmatch, if_neg hrot] using hdefault
  | orl_case4 n2 t2 n1 t1 =>
      by_cases hrot : (Int.eq (CompCert4Lean.Lib.Integers.Int.add n1 n2)
          Int64.iwordsize' && same_expr_pure t1 t2) = true
      · obtain ⟨heq, hsame⟩ := Bool.and_eq_true_iff.mp hrot
        have hsum := orl_int_eq _ _ heq
        obtain ⟨vx, htx, hx⟩ := orl_shrlu_inv xi (Genv.globalenv prog)
          sp e m le t2 n2 x ha
        obtain ⟨vy, hty, hy⟩ := orl_shll_inv xi (Genv.globalenv prog)
          sp e m le t1 n1 y hb
        have hv := orl_same_value xi (Genv.globalenv prog) sp e m
          t1 t2 le vy vx hsame hty htx
        subst vx
        subst x
        subst y
        refine ⟨Val.rorl vy (.Vint n2), ?_, ?_⟩
        · simp only [orl, hmatch, if_pos hrot]
          exact eval_expr.eval_Eop le (Ororlimm n2) (Econs t1 Enil) [vy] _
            (eval_exprlist.cons le t1 Enil vy [] hty (eval_exprlist.nil le)) rfl
        · rw [orl_val_comm]
          exact orl_rotate_value vy n1 n2 hsum
      · simpa only [orl, hmatch, if_neg hrot] using hdefault
  | orl_default e1 e2 =>
      simpa only [orl, hmatch] using hdefault

end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof

theorem eval_xorlimm
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_xorlimmStatement binary64_certificate binary32_certificate := by
  exact eval_xorlimm_aux

end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong

private theorem shrlu_int64_shru_zero (x : CCInt64) :
    CompCert4Lean.Lib.Integers.Int64.shru' x
      CompCert4Lean.Lib.Integers.Int.zero = x := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  have h := orl_shru_val x (CompCert4Lean.Lib.Integers.Int.zero : CCInt)
  have hz : (CompCert4Lean.Lib.Integers.Int.zero : CCInt).val = 0 := rfl
  calc
    (CompCert4Lean.Lib.Integers.Int64.shru' x
      (CompCert4Lean.Lib.Integers.Int.zero : CCInt)).val =
        x.val / 2 ^ (CompCert4Lean.Lib.Integers.Int.zero : CCInt).val := h
    _ = x.val := by simp [hz]

private theorem shrlu_val_zero (x : val) :
    Val.lessdef
      (Val.shrlu x (.Vint CompCert4Lean.Lib.Integers.Int.zero)) x := by
  cases x with
  | Vlong n =>
      change Val.lessdef
        (if CompCert4Lean.Lib.Integers.Int.ltu
            CompCert4Lean.Lib.Integers.Int.zero
            CompCert4Lean.Lib.Integers.Int64.iwordsize' then
          .Vlong (CompCert4Lean.Lib.Integers.Int64.shru' n
            CompCert4Lean.Lib.Integers.Int.zero)
        else .Vundef) (.Vlong n)
      have hlt : CompCert4Lean.Lib.Integers.Int.ltu
          CompCert4Lean.Lib.Integers.Int.zero
          CompCert4Lean.Lib.Integers.Int64.iwordsize' = true := by decide
      rw [if_pos hlt, shrlu_int64_shru_zero]
      exact Val.lessdef_refl _
  | _ => exact Val.lessdef_undef _

private theorem shrlu_int64_shru_comp (x : CCInt64) (n1 n : CCInt)
    (hn1 : CompCert4Lean.Lib.Integers.Int.ltu n1
      CompCert4Lean.Lib.Integers.Int64.iwordsize' = true)
    (hn : CompCert4Lean.Lib.Integers.Int.ltu n
      CompCert4Lean.Lib.Integers.Int64.iwordsize' = true) :
    CompCert4Lean.Lib.Integers.Int64.shru'
        (CompCert4Lean.Lib.Integers.Int64.shru' x n1) n =
      CompCert4Lean.Lib.Integers.Int64.shru' x
        (CompCert4Lean.Lib.Integers.Int.add n n1) := by
  have hn1v := shrl_int_ltu_iwordsize_val n1 hn1
  have hnv := shrl_int_ltu_iwordsize_val n hn
  have haddVal :
      (CompCert4Lean.Lib.Integers.Int.add n n1).val = n.val + n1.val :=
    shrl_int_add_val_small n n1 (by omega)
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  have h1 := orl_shru_val x n1
  have h3 := orl_shru_val x (CompCert4Lean.Lib.Integers.Int.add n n1)
  calc
    (CompCert4Lean.Lib.Integers.Int64.shru'
        (CompCert4Lean.Lib.Integers.Int64.shru' x n1) n).val =
        (CompCert4Lean.Lib.Integers.Int64.shru' x n1).val /
          2 ^ n.val := orl_shru_val _ _
    _ = (x.val / 2 ^ n1.val) / 2 ^ n.val := by
      exact congrArg (fun q => q / 2 ^ n.val) h1
    _ = x.val / 2 ^ (n.val + n1.val) := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
      rw [Nat.add_comm n1.val n.val]
    _ = (CompCert4Lean.Lib.Integers.Int64.shru'
        x (CompCert4Lean.Lib.Integers.Int.add n n1)).val := by
      rw [← haddVal]
      exact h3.symm

end CompCert4Lean.X86.SelectLongproof

namespace CompCert4Lean.X86.SelectLongproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectLong
open Lean Elab Tactic Meta

theorem eval_shrluimm
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    @eval_shrluimmStatement binary64_certificate binary32_certificate := by
  unfold eval_shrluimmStatement unary_constructor_sound
  intro xi prog hf hdecl sp e m n le a x h
  unfold CompCert4Lean.X86.SelectLong.shrluimm
  cases hz : CompCert4Lean.Lib.Integers.Int.eq n
      CompCert4Lean.Lib.Integers.Int.zero with
  | true =>
      have hn := shrl_int_eq_true_zero n hz
      simp only [hz, if_true]
      subst n
      exact ⟨x, h, shrlu_val_zero x⟩
  | false =>
      simp only [hz, if_false]
      cases hlt : CompCert4Lean.Lib.Integers.Int.ltu n
          CompCert4Lean.Lib.Integers.Int64.iwordsize' with
      | false =>
          simp only [hlt, Bool.not_false, if_true]
          refine ⟨Val.shrlu x (.Vint n), ?_, Val.lessdef_refl _⟩
          apply eval_expr.eval_Eop le Oshrlu
            (Econs a (Econs (Eop (Ointconst n) Enil) Enil))
            [x, .Vint n] (Val.shrlu x (.Vint n))
          · exact eval_exprlist.cons le a _ x [.Vint n] h
              (eval_exprlist.cons le (Eop (Ointconst n) Enil) Enil
                (.Vint n) []
                (eval_expr.eval_Eop le (Ointconst n) Enil [] (.Vint n)
                  (eval_exprlist.nil le) rfl)
                (eval_exprlist.nil le))
          · rfl
      | true =>
          simp only [hlt, Bool.not_true]
          cases hmatch : shrluimm_match a with
          | shrluimm_case1 n1 =>
              have hx : x = .Vlong n1 := eval_longconst_value xi
                (Genv.globalenv prog) sp e m le n1 x
                (by simpa [hmatch] using h)
              subst x
              refine ⟨.Vlong (CompCert4Lean.Lib.Integers.Int64.shru' n1 n), ?_, ?_⟩
              · run_tac
                  let env ← getEnv
                  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
                      let s := toString name
                      s.startsWith "_private.CompCert4Lean.X86.SelectLong." &&
                        s.endsWith "Int64.shru'")
                    | throwError "frozen SelectLong Int64.shru' alias not found"
                  evalTactic (← `(tactic| unfold $(Lean.mkIdent name)))
                simpa [longconst, hmatch] using
                  (eval_longconst xi prog sp e m le
                    (CompCert4Lean.Lib.Integers.Int64.shru' n1 n))
              · change Val.lessdef
                  (if CompCert4Lean.Lib.Integers.Int.ltu n
                      CompCert4Lean.Lib.Integers.Int64.iwordsize' then
                    .Vlong (CompCert4Lean.Lib.Integers.Int64.shru' n1 n)
                  else .Vundef) _
                rw [if_pos hlt]
                exact Val.lessdef_refl _
          | shrluimm_case2 n1 t1 =>
              have horig := h
              cases h with
              | eval_Eop le' op al vl v hargs hop =>
                  cases hargs with
                  | cons _ a' al' v1 vl' hhead htail =>
                      cases htail with
                      | nil _ =>
                          change some (Val.shrlu v1 (.Vint n1)) = some x at hop
                          cases hop
                          cases hsum : CompCert4Lean.Lib.Integers.Int.ltu
                              (CompCert4Lean.Lib.Integers.Int.add n n1)
                              CompCert4Lean.Lib.Integers.Int64.iwordsize' with
                          | false =>
                              refine ⟨Val.shrlu (Val.shrlu v1 (.Vint n1))
                                (.Vint n), ?_, Val.lessdef_refl _⟩
                              simp only [hmatch, hsum, if_false]
                              apply eval_expr.eval_Eop le (Oshrluimm n)
                                (Econs (Eop (Oshrluimm n1) (Econs t1 Enil)) Enil)
                                [Val.shrlu v1 (.Vint n1)] _
                              · exact eval_exprlist.cons le _ Enil _ [] horig
                                  (eval_exprlist.nil le)
                              · rfl
                          | true =>
                              refine ⟨Val.shrlu v1
                                (.Vint (CompCert4Lean.Lib.Integers.Int.add n n1)), ?_, ?_⟩
                              · simp only [hmatch, hsum, if_true]
                                apply eval_expr.eval_Eop le
                                  (Oshrluimm (CompCert4Lean.Lib.Integers.Int.add n n1))
                                  (Econs t1 Enil) [v1] _
                                · exact eval_exprlist.cons le t1 Enil v1 []
                                    (by simpa [hmatch] using hhead)
                                    (eval_exprlist.nil le)
                                · rfl
                              · cases v1 with
                                | Vlong i =>
                                    cases hn1 : CompCert4Lean.Lib.Integers.Int.ltu n1
                                        CompCert4Lean.Lib.Integers.Int64.iwordsize' with
                                    | false =>
                                        simp [Val.shrlu, hn1]
                                        exact Val.lessdef_undef _
                                    | true =>
                                        simp only [Val.shrlu, hn1, hlt, hsum,
                                          if_true]
                                        run_tac
                                          let env ← getEnv
                                          let some (name, _) := env.constants.toList.find?
                                              (fun (name, _) =>
                                                let s := toString name
                                                s.startsWith
                                                    "_private.CompCert4Lean.Common.Values." &&
                                                  s.endsWith "Int64.shru'")
                                            | throwError
                                                "frozen Values Int64.shru' alias not found"
                                          evalTactic
                                            (← `(tactic| unfold $(Lean.mkIdent name)))
                                        rw [shrlu_int64_shru_comp i n1 n hn1 hlt]
                                        exact Val.lessdef_refl _
                                | _ => exact Val.lessdef_refl _
          | shrluimm_default e1 =>
              refine ⟨Val.shrlu x (.Vint n), ?_, Val.lessdef_refl _⟩
              simp only [hmatch]
              apply eval_expr.eval_Eop le (Oshrluimm n) (Econs a Enil)
                [x] (Val.shrlu x (.Vint n))
              · exact eval_exprlist.cons le a Enil x [] h
                  (eval_exprlist.nil le)
              · rfl

end CompCert4Lean.X86.SelectLongproof
