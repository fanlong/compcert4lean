import CompCert4Lean.Lib.Coqlib

/-!
# Boolean equality support

This module translates the definition-bearing surface of
`compcert.lib.BoolEqual`.  Proof-bearing declarations assigned to the later
proof-migration phase are represented by exact proposition descriptors rather
than theorem stubs.
-/

namespace CompCert4Lean.Lib.BoolEqual

namespace BE

def bool_eq {A : Type} (_x _y : A) : Type := Bool

def proj_sumbool_is_trueStatement : Prop :=
  ∀ (A : Type)
    (f : ∀ (x y : A),
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y))
    (x : A),
    CompCert4Lean.Lib.Coqlib.proj_sumbool (f x x) = true

def false_not_trueStatement : Prop :=
  ∀ (P : Prop), false = true → P

def proj_sumbool_trueStatement : Prop :=
  ∀ (A : Type) (x y : A)
    (a : CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y)),
    CompCert4Lean.Lib.Coqlib.proj_sumbool a = true → x = y

def dec_eq_from_bool_eqStatement :=
  ∀ (A : Type) (f : A → A → Bool)
    (f_refl : ∀ x, f x x = true)
    (f_sound : ∀ x y, f x y = true → x = y),
    ∀ (x y : A),
      CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y)

end BE

end CompCert4Lean.Lib.BoolEqual
