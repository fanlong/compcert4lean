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
