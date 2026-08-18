import CompCert4Lean.Common.Builtins0
import CompCert4Lean.X86.Builtins1

/-!
# Known built-in functions

Definition-bearing translation of `common/Builtins.v`. Proof declarations
assigned to the later proof-migration phase are represented by transparent
proposition descriptors.
-/

namespace CompCert4Lean.Common.Builtins

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins0
open CompCert4Lean.Common.Values
open CompCert4Lean.X86.Builtins1

private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string
private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool

inductive builtin_function : Type where
  | BI_standard (b : standard_builtin)
  | BI_platform (b : platform_builtin)

export builtin_function (BI_standard BI_platform)

def eq_builtin_function (x y : builtin_function) : Sumbool (x = y) (x ≠ y) :=
  match x, y with
  | BI_standard bx, BI_standard by' =>
      match eq_standard_builtin bx by' with
      | .left h => .left (congrArg BI_standard h)
      | .right h => .right (by
          intro hxy
          cases hxy
          exact h rfl)
  | BI_standard _, BI_platform _ => .right (by intro h; cases h)
  | BI_platform _, BI_standard _ => .right (by intro h; cases h)
  | BI_platform bx, BI_platform by' =>
      match eq_platform_builtin bx by' with
      | .left h => .left (congrArg BI_platform h)
      | .right h => .right (by
          intro hxy
          cases hxy
          exact h rfl)

def builtin_function_sig : builtin_function → signature
  | BI_standard b => standard_builtin_sig b
  | BI_platform b => platform_builtin_sig b

def builtin_function_sem (b : builtin_function) :
    builtin_sem (builtin_function_sig b).sig_res :=
  match b with
  | BI_standard b => standard_builtin_sem b
  | BI_platform b => platform_builtin_sem b

def builtin_function_sem_injectStatement : Prop :=
  ∀ b (vargs : List val) (vres : val) (f : Val.meminj) vargs',
    builtin_function_sem b vargs = some vres →
    Val.inject_list f vargs vargs' →
    ∃ vres', builtin_function_sem b vargs' = some vres' ∧ Val.inject f vres vres'

def builtin_function_sem_lessdefStatement : Prop :=
  ∀ b (vargs : List val) (vres : val) vargs',
    builtin_function_sem b vargs = some vres →
    Val.lessdef_list vargs vargs' →
    ∃ vres', builtin_function_sem b vargs' = some vres' ∧ Val.lessdef vres vres'

def lookup_builtin_function (name : RocqString) (sg : signature) :
    Option builtin_function :=
  match lookup_builtin standard_builtin_sig name sg standard_builtin_table with
  | some b => some (BI_standard b)
  | none =>
      match lookup_builtin platform_builtin_sig name sg platform_builtin_table with
      | some b => some (BI_platform b)
      | none => none

def lookup_builtin_function_sigStatement : Prop :=
  ∀ name sg b,
    lookup_builtin_function name sg = some b → builtin_function_sig b = sg

end CompCert4Lean.Common.Builtins
