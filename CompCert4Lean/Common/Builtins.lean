import CompCert4Lean.Common.Builtins0
import CompCert4Lean.X86.Builtins1

/-!
# Known built-in functions

Definition-bearing translation of `common/Builtins.v`. Proof declarations
assigned to the later proof-migration phase are represented by transparent
proposition descriptors.
-/

namespace CompCert4Lean.Common.Builtins

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
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

def builtin_function_sem
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (b : builtin_function) :
    builtin_sem (builtin_function_sig b).sig_res :=
  match b with
  | BI_standard b => standard_builtin_sem
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) b
  | BI_platform b => platform_builtin_sem b

def builtin_function_sem_injectStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ b (vargs : List val) (vres : val) (f : Val.meminj) vargs',
    builtin_function_sem
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) b vargs = some vres →
    Val.inject_list f vargs vargs' →
    ∃ vres', builtin_function_sem
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) b vargs' = some vres' ∧
      Val.inject f vres vres'

def builtin_function_sem_lessdefStatement
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ b (vargs : List val) (vres : val) vargs',
    builtin_function_sem
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) b vargs = some vres →
    Val.lessdef_list vargs vargs' →
    ∃ vres', builtin_function_sem
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) b vargs' = some vres' ∧
      Val.lessdef vres vres'

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

namespace CompCert4Lean.Common.Builtins

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Builtins0
open CompCert4Lean.Common.Values

theorem builtin_function_sem_inject
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] :
    builtin_function_sem_injectStatement := by
  intro b vargs vres f vargs' hsem hinj
  have hopt := builtin_sem.bs_inject
    (builtin_function_sem
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) b)
    f vargs vargs' hinj
  rw [hsem] at hopt
  cases htarget : builtin_function_sem
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) b vargs' with
  | none =>
      rw [htarget] at hopt
      simp [val_opt_inject] at hopt
  | some vres' =>
      rw [htarget] at hopt
      exact ⟨vres', rfl, by simpa [val_opt_inject] using hopt⟩

end CompCert4Lean.Common.Builtins

namespace CompCert4Lean.Common.Builtins

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Values

theorem builtin_function_sem_lessdef
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] :
    builtin_function_sem_lessdefStatement := by
  intro b vargs vres vargs' hsem hless
  have lessdef_list_to_inject : ∀ (vl1 vl2 : List val),
      Val.lessdef_list vl1 vl2 → Val.inject_list inject_id vl1 vl2 := by
    intro vl1 vl2 h
    induction h with
    | lessdef_list_nil => exact Val.inject_list_nil _
    | lessdef_list_cons v1 v2 vl1 vl2 hhead htail ih =>
        exact Val.inject_list_cons inject_id v1 v2 vl1 vl2
          ((val_inject_id v1 v2).mpr hhead) ih
  have hinj : Val.inject_list inject_id vargs vargs' :=
    lessdef_list_to_inject vargs vargs' hless
  obtain ⟨vres', hsem', hinj'⟩ := builtin_function_sem_inject
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    b vargs vres inject_id vargs' hsem hinj
  exact ⟨vres', hsem', (val_inject_id vres vres').mp hinj'⟩

end CompCert4Lean.Common.Builtins

namespace CompCert4Lean.Common.Builtins

open CompCert4Lean.Common.Builtins0
open CompCert4Lean.X86.Builtins1

theorem lookup_builtin_function_sig : lookup_builtin_function_sigStatement := by
  intro name sg b h
  unfold lookup_builtin_function at h
  cases hs : lookup_builtin standard_builtin_sig name sg standard_builtin_table with
  | some bs =>
      simp only [hs] at h
      cases Option.some.inj h
      exact lookup_builtin_sig _ standard_builtin_sig name sg bs standard_builtin_table hs
  | none =>
      simp only [hs] at h
      cases hp : lookup_builtin platform_builtin_sig name sg platform_builtin_table with
      | some bp =>
          simp only [hp] at h
          cases Option.some.inj h
          exact lookup_builtin_sig _ platform_builtin_sig name sg bp platform_builtin_table hp
      | none =>
          simp only [hp] at h
          cases h

end CompCert4Lean.Common.Builtins
