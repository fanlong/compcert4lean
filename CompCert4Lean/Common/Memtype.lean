/-!
# Memory permissions

This module translates the definition-bearing permission surface of CompCert's
`common/Memtype.v`. The transitivity lemma assigned to later proof migration is
represented by its exact proposition descriptor.
-/

namespace CompCert4Lean.Common.Memtype

inductive permission : Type where
  | Freeable
  | Writable
  | Readable
  | Nonempty

export permission (Freeable Writable Readable Nonempty)

def perm_order (p q : permission) : Prop :=
  p = q ∨ p = Freeable ∨ (p = Writable ∧ q = Readable) ∨ q = Nonempty

def perm_order_transStatement : Prop :=
  ∀ p1 p2 p3, perm_order p1 p2 → perm_order p2 p3 → perm_order p1 p3

inductive perm_kind : Type where
  | Max
  | Cur

export perm_kind (Max Cur)

end CompCert4Lean.Common.Memtype
