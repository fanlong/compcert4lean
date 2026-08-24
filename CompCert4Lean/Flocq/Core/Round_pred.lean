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
      CompCert4Lean.Flocq.Core.Defs.round_pred_total
        (CompCert4Lean.Flocq.Core.Defs.Rnd_DN_pt F) →
      satisfies_any F

def Rnd_DN_UP_pt_splitStatement : Prop :=
  ∀ (F : R → Prop) (x d u : R),
    CompCert4Lean.Flocq.Core.Defs.Rnd_DN_pt F x d →
      CompCert4Lean.Flocq.Core.Defs.Rnd_UP_pt F x u →
      ∀ f, F f → Rle f d ∨ Rle u f

def Rnd_DN_pt_idempotentStatement : Prop :=
  ∀ (F : R → Prop) (x f : R),
    CompCert4Lean.Flocq.Core.Defs.Rnd_DN_pt F x f → F x → f = x

def Rnd_DN_pt_monotoneStatement : Prop :=
  ∀ (F : R → Prop),
    CompCert4Lean.Flocq.Core.Defs.round_pred_monotone
      (CompCert4Lean.Flocq.Core.Defs.Rnd_DN_pt F)

def Rnd_DN_pt_oppStatement : Prop :=
  ∀ (F : R → Prop),
    (∀ x, F x → F (Ropp x)) →
      ∀ (x f : R),
        CompCert4Lean.Flocq.Core.Defs.Rnd_UP_pt F x f →
          CompCert4Lean.Flocq.Core.Defs.Rnd_DN_pt F (Ropp x) (Ropp f)

def Rnd_DN_pt_uniqueStatement : Prop :=
  ∀ (F : R → Prop) (x f1 f2 : R),
    CompCert4Lean.Flocq.Core.Defs.Rnd_DN_pt F x f1 →
      CompCert4Lean.Flocq.Core.Defs.Rnd_DN_pt F x f2 → f1 = f2

def Rnd_N_pt_DNStatement : Prop :=
  ∀ (F : R → Prop) (x d u : R),
    CompCert4Lean.Flocq.Core.Defs.Rnd_DN_pt F x d →
      CompCert4Lean.Flocq.Core.Defs.Rnd_UP_pt F x u →
      Rle (Rminus x d) (Rminus u x) →
      CompCert4Lean.Flocq.Core.Defs.Rnd_N_pt F x d

def Rnd_N_pt_DN_UPStatement : Prop :=
  ∀ (F : R → Prop) (x d u f : R),
    F f →
      CompCert4Lean.Flocq.Core.Defs.Rnd_DN_pt F x d →
      CompCert4Lean.Flocq.Core.Defs.Rnd_UP_pt F x u →
      Rle (Rabs (Rminus f x)) (Rminus x d) →
      Rle (Rabs (Rminus f x)) (Rminus u x) →
      CompCert4Lean.Flocq.Core.Defs.Rnd_N_pt F x f

def Rnd_N_pt_monotoneStatement : Prop :=
  ∀ (F : R → Prop) (x y f g : R),
    CompCert4Lean.Flocq.Core.Defs.Rnd_N_pt F x f →
      CompCert4Lean.Flocq.Core.Defs.Rnd_N_pt F y g →
      Rlt x y → Rle f g

def Rnd_UP_pt_idempotentStatement : Prop :=
  ∀ (F : R → Prop) (x f : R),
    CompCert4Lean.Flocq.Core.Defs.Rnd_UP_pt F x f → F x → f = x

def Rnd_UP_pt_monotoneStatement : Prop :=
  ∀ (F : R → Prop),
    CompCert4Lean.Flocq.Core.Defs.round_pred_monotone
      (CompCert4Lean.Flocq.Core.Defs.Rnd_UP_pt F)

def Rnd_UP_pt_uniqueStatement : Prop :=
  ∀ (F : R → Prop) (x f1 f2 : R),
    CompCert4Lean.Flocq.Core.Defs.Rnd_UP_pt F x f1 →
      CompCert4Lean.Flocq.Core.Defs.Rnd_UP_pt F x f2 → f1 = f2

def round_uniqueStatement : Prop :=
  ∀ (rnd : R → R → Prop),
    CompCert4Lean.Flocq.Core.Defs.round_pred_monotone rnd →
      ∀ x f1 f2, rnd x f1 → rnd x f2 → f1 = f2

def satisfies_any_eqStatement : Prop :=
  ∀ (F1 F2 : R → Prop),
    (∀ x, F1 x ↔ F2 x) → satisfies_any F1 → satisfies_any F2

end CompCert4Lean.Flocq.Core.Round_pred
