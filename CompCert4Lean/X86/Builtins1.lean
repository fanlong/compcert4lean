import CompCert4Lean.Common.Builtins0

/-!
# Platform-specific built-in functions

Definition-bearing translation of `x86/Builtins1.v` for the x86-64 target.
-/

namespace CompCert4Lean.X86.Builtins1

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins0

private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string
private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool

private def ofString (s : String) : RocqString :=
  (String.toUTF8 s).toList.foldr
    (fun b tail =>
      CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.String b tail)
    CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.EmptyString

inductive platform_builtin : Type where
  | BI_fmin
  | BI_fmax

export platform_builtin (BI_fmin BI_fmax)

def platform_builtin_table : List (RocqString × platform_builtin) :=
  [ (ofString "__builtin_fmin", BI_fmin)
  , (ofString "__builtin_fmax", BI_fmax)
  ]

def platform_builtin_sig : platform_builtin → signature
  | BI_fmin | BI_fmax =>
      { sig_args := [Xfloat, Xfloat]
        sig_res := Xfloat
        sig_cc := cc_default }

def platform_builtin_sem (b : platform_builtin) :
    builtin_sem (platform_builtin_sig b).sig_res :=
  match b with
  | BI_fmin =>
      mkbuiltin_n2t Tfloat Tfloat Xfloat fun f1 f2 =>
        match CompCert4Lean.Lib.Floats.Float.compare f1 f2 with
        | some .Lt => f1
        | some .Eq | some .Gt | none => f2
  | BI_fmax =>
      mkbuiltin_n2t Tfloat Tfloat Xfloat fun f1 f2 =>
        match CompCert4Lean.Lib.Floats.Float.compare f1 f2 with
        | some .Gt => f1
        | some .Eq | some .Lt | none => f2

def eq_platform_builtin (x y : platform_builtin) : Sumbool (x = y) (x ≠ y) := by
  cases x <;> cases y
  · exact .left rfl
  · exact .right (by intro h; cases h)
  · exact .right (by intro h; cases h)
  · exact .left rfl

end CompCert4Lean.X86.Builtins1
