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
