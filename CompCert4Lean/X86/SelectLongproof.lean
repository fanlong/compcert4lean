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

def unary_constructor_sound (xi : ExternalCalls) (ge : genv) (sp : val)
    (e : env) (m : mem) (cstr : expr → expr) (sem : val → val) : Prop :=
  ∀ (le : letenv) (a : expr) (x : val),
    eval_expr xi ge sp e m le a x →
      ∃ v, eval_expr xi ge sp e m le (cstr a) v ∧ Val.lessdef (sem x) v

def binary_constructor_sound (xi : ExternalCalls) (ge : genv) (sp : val)
    (e : env) (m : mem) (cstr : expr → expr → expr)
    (sem : val → val → val) : Prop :=
  ∀ (le : letenv) (a : expr) (x : val) (b : expr) (y : val),
    eval_expr xi ge sp e m le a x →
    eval_expr xi ge sp e m le b y →
      ∃ v, eval_expr xi ge sp e m le (cstr a b) v ∧
        Val.lessdef (sem x y) v

def partial_unary_constructor_sound (xi : ExternalCalls) (ge : genv) (sp : val)
    (e : env) (m : mem) (cstr : expr → expr) (sem : val → Option val) : Prop :=
  ∀ (le : letenv) (a : expr) (x y : val),
    eval_expr xi ge sp e m le a x →
    sem x = some y →
      ∃ v, eval_expr xi ge sp e m le (cstr a) v ∧ Val.lessdef y v

def partial_binary_constructor_sound (xi : ExternalCalls) (ge : genv) (sp : val)
    (e : env) (m : mem) (cstr : expr → expr → expr)
    (sem : val → val → Option val) : Prop :=
  ∀ (le : letenv) (a : expr) (x : val) (b : expr) (y z : val),
    eval_expr xi ge sp e m le a x →
    eval_expr xi ge sp e m le b y →
    sem x y = some z →
      ∃ v, eval_expr xi ge sp e m le (cstr a b) v ∧ Val.lessdef z v

/-! ## Exact statement descriptors for later proof migration -/

def eval_addlStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    binary_constructor_sound xi (Genv.globalenv prog) sp e m addl Val.addl

def eval_addlimmStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem)
    (n : CCInt64),
    unary_constructor_sound xi (Genv.globalenv prog) sp e m (addlimm n)
      (fun v => Val.addl v (.Vlong n))

def eval_andlStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    binary_constructor_sound xi (Genv.globalenv prog) sp e m andl Val.andl

def eval_andlimmStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem)
    (n : CCInt64),
    unary_constructor_sound xi (Genv.globalenv prog) sp e m (andlimm n)
      (fun v => Val.andl v (.Vlong n))

def eval_cmplStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem)
    (c : comparison) (le : letenv) (a : expr) (x : val) (b : expr) (y v : val),
    eval_expr xi (Genv.globalenv prog) sp e m le a x →
    eval_expr xi (Genv.globalenv prog) sp e m le b y →
    Val.cmpl c x y = some v →
    eval_expr xi (Genv.globalenv prog) sp e m le (cmpl c a b) v

def eval_cmpluStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem)
    (c : comparison) (le : letenv) (a : expr) (x : val) (b : expr) (y v : val),
    eval_expr xi (Genv.globalenv prog) sp e m le a x →
    eval_expr xi (Genv.globalenv prog) sp e m le b y →
    Val.cmplu (Mem.valid_pointer m) c x y = some v →
    eval_expr xi (Genv.globalenv prog) sp e m le (cmplu c a b) v

def eval_divls_baseStatement [hf : HelperFunctions] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem)
      (le : letenv) (a b : expr) (x y z : val),
      eval_expr xi (Genv.globalenv prog) sp e m le a x →
      eval_expr xi (Genv.globalenv prog) sp e m le b y →
      Val.divls x y = some z →
      ∃ v, eval_expr xi (Genv.globalenv prog) sp e m le (divls_base a b) v ∧
        Val.lessdef z v

def eval_divlu_baseStatement [hf : HelperFunctions] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem)
      (le : letenv) (a b : expr) (x y z : val),
      eval_expr xi (Genv.globalenv prog) sp e m le a x →
      eval_expr xi (Genv.globalenv prog) sp e m le b y →
      Val.divlu x y = some z →
      ∃ v, eval_expr xi (Genv.globalenv prog) sp e m le (divlu_base a b) v ∧
        Val.lessdef z v

def eval_floatoflongStatement [hf : HelperFunctions] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem)
      (le : letenv) (a : expr) (x y : val),
      eval_expr xi (Genv.globalenv prog) sp e m le a x →
      Val.floatoflong x = some y →
      ∃ v, eval_expr xi (Genv.globalenv prog) sp e m le (floatoflong a) v ∧
        Val.lessdef y v

def eval_intoflongStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    unary_constructor_sound xi (Genv.globalenv prog) sp e m intoflong Val.loword

def eval_longconstStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem)
    (le : letenv) (n : CCInt64),
    eval_expr xi (Genv.globalenv prog) sp e m le (longconst n) (.Vlong n)

def eval_longoffloatStatement [hf : HelperFunctions] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem)
      (le : letenv) (a : expr) (x y : val),
      eval_expr xi (Genv.globalenv prog) sp e m le a x →
      Val.longoffloat x = some y →
      ∃ v, eval_expr xi (Genv.globalenv prog) sp e m le (longoffloat a) v ∧
        Val.lessdef y v

def eval_longofintStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    unary_constructor_sound xi (Genv.globalenv prog) sp e m longofint Val.longofint

def eval_longofintuStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    unary_constructor_sound xi (Genv.globalenv prog) sp e m longofintu Val.longofintu

def eval_longofsingleStatement [hf : HelperFunctions] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem)
      (le : letenv) (a : expr) (x y : val),
      eval_expr xi (Genv.globalenv prog) sp e m le a x →
      Val.longofsingle x = some y →
      ∃ v, eval_expr xi (Genv.globalenv prog) sp e m le (longofsingle a) v ∧
        Val.lessdef y v

def eval_modls_baseStatement [hf : HelperFunctions] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem)
      (le : letenv) (a b : expr) (x y z : val),
      eval_expr xi (Genv.globalenv prog) sp e m le a x →
      eval_expr xi (Genv.globalenv prog) sp e m le b y →
      Val.modls x y = some z →
      ∃ v, eval_expr xi (Genv.globalenv prog) sp e m le (modls_base a b) v ∧
        Val.lessdef z v

def eval_modlu_baseStatement [hf : HelperFunctions] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem)
      (le : letenv) (a b : expr) (x y z : val),
      eval_expr xi (Genv.globalenv prog) sp e m le a x →
      eval_expr xi (Genv.globalenv prog) sp e m le b y →
      Val.modlu x y = some z →
      ∃ v, eval_expr xi (Genv.globalenv prog) sp e m le (modlu_base a b) v ∧
        Val.lessdef z v

def eval_mullStatement [hf : HelperFunctions] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
      binary_constructor_sound xi (Genv.globalenv prog) sp e m mull Val.mull

def eval_mullhsStatement [hf : HelperFunctions] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem) (n : CCInt64),
      unary_constructor_sound xi (Genv.globalenv prog) sp e m
        (fun a => mullhs a n) (fun v => Val.mullhs v (.Vlong n))

def eval_mullhuStatement [hf : HelperFunctions] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem) (n : CCInt64),
      unary_constructor_sound xi (Genv.globalenv prog) sp e m
        (fun a => mullhu a n) (fun v => Val.mullhu v (.Vlong n))

def eval_mullimmStatement [hf : HelperFunctions] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem) (n : CCInt64),
      unary_constructor_sound xi (Genv.globalenv prog) sp e m (mullimm n)
        (fun v => Val.mull v (.Vlong n))

def eval_mullimm_baseStatement [hf : HelperFunctions] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem) (n : CCInt64),
      unary_constructor_sound xi (Genv.globalenv prog) sp e m (mullimm_base n)
        (fun v => Val.mull v (.Vlong n))

def eval_neglStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    unary_constructor_sound xi (Genv.globalenv prog) sp e m negl Val.negl

def eval_notlStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    unary_constructor_sound xi (Genv.globalenv prog) sp e m notl Val.notl

def eval_orlStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    binary_constructor_sound xi (Genv.globalenv prog) sp e m orl Val.orl

def eval_orlimmStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem)
    (n : CCInt64),
    unary_constructor_sound xi (Genv.globalenv prog) sp e m (orlimm n)
      (fun v => Val.orl v (.Vlong n))

def eval_shllStatement [hf : HelperFunctions] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
      binary_constructor_sound xi (Genv.globalenv prog) sp e m shll Val.shll

def eval_shllimmStatement [hf : HelperFunctions] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem) (n : CCInt),
      unary_constructor_sound xi (Genv.globalenv prog) sp e m
        (fun e => shllimm e n) (fun v => Val.shll v (.Vint n))

def eval_shrlStatement [hf : HelperFunctions] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
      binary_constructor_sound xi (Genv.globalenv prog) sp e m shrl Val.shrl

def eval_shrlimmStatement [hf : HelperFunctions] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem) (n : CCInt),
      unary_constructor_sound xi (Genv.globalenv prog) sp e m
        (fun e => shrlimm e n) (fun v => Val.shrl v (.Vint n))

def eval_shrluStatement [hf : HelperFunctions] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem),
      binary_constructor_sound xi (Genv.globalenv prog) sp e m shrlu Val.shrlu

def eval_shrluimmStatement [hf : HelperFunctions] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem) (n : CCInt),
      unary_constructor_sound xi (Genv.globalenv prog) sp e m
        (fun e => shrluimm e n) (fun v => Val.shrlu v (.Vint n))

def eval_shrxlimmStatement [hf : HelperFunctions] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem)
      (le : letenv) (a : expr) (n : CCInt) (x z : val),
      eval_expr xi (Genv.globalenv prog) sp e m le a x →
      Val.shrxl x (.Vint n) = some z →
      ∃ v, eval_expr xi (Genv.globalenv prog) sp e m le (shrxlimm a n) v ∧
        Val.lessdef z v

def eval_singleoflongStatement [hf : HelperFunctions] : Prop :=
  ∀ (xi : ExternalCalls) (prog : program),
    CompCert4Lean.Backend.SplitLongproof.helper_functions_declared prog hf →
    ∀ (sp : val) (e : env) (m : mem)
      (le : letenv) (a : expr) (x y : val),
      eval_expr xi (Genv.globalenv prog) sp e m le a x →
      Val.singleoflong x = some y →
      ∃ v, eval_expr xi (Genv.globalenv prog) sp e m le (singleoflong a) v ∧
        Val.lessdef y v

def eval_sublStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    binary_constructor_sound xi (Genv.globalenv prog) sp e m subl Val.subl

def eval_xorlStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem),
    binary_constructor_sound xi (Genv.globalenv prog) sp e m xorl Val.xorl

def eval_xorlimmStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem)
    (n : CCInt64),
    unary_constructor_sound xi (Genv.globalenv prog) sp e m (xorlimm n)
      (fun v => Val.xorl v (.Vlong n))

def is_longconst_soundStatement : Prop :=
  ∀ (xi : ExternalCalls) (prog : program) (sp : val) (e : env) (m : mem)
    (le : letenv) (a : expr) (x : val) (n : CCInt64),
    is_longconst a = some n →
    eval_expr xi (Genv.globalenv prog) sp e m le a x →
    x = .Vlong n

end CompCert4Lean.X86.SelectLongproof
