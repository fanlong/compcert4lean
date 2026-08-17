import CompCert4Lean.Flocq.Core.Defs

/-!
# Rounding predicates

This module contains the selected definition and statement surfaces from
`Flocq.Core.Round_pred`.  Proof-heavy declarations remain outside this
definition-translation pass and are represented only where the packet assigns
an exact statement descriptor.
-/

namespace CompCert4Lean.Flocq.Core.Round_pred

open CompCert4Lean.Flocq.Core.Raux

/-! Exact source statement descriptor for later proof migration. -/

def Rnd_UP_pt_oppStatement : Prop :=
  ∀ (F : R → Prop),
    (∀ x, F x → F (Ropp x)) →
      ∀ (x f : R),
      CompCert4Lean.Flocq.Core.Defs.Rnd_DN_pt F x f →
      CompCert4Lean.Flocq.Core.Defs.Rnd_UP_pt F (Ropp x) (Ropp f)

/-! Ensures that a real number can always be rounded. -/

inductive satisfies_any (F : R → Prop) : Prop where
  | mk :
      F R0 →
      (∀ x : R, F x → F (Ropp x)) →
      (∀ x : R, ∃ f : R, CompCert4Lean.Flocq.Core.Defs.Rnd_DN_pt F x f) →
      satisfies_any F

end CompCert4Lean.Flocq.Core.Round_pred
