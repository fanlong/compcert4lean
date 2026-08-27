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

/-!
The executable Flocq definitions use `Raux.R`, which is the checked runtime
carrier.  These source propositions instead range over the explicit exact
carrier selected by RPR-007.  Exact predicate ownership is provided by the
canonical `Defs.Exact` layer; this local namespace keeps only transparent
operation shorthands for the statement surfaces below.
-/

abbrev ExactRealContext := CompCert4Lean.Flocq.Core.Raux.ExactRealContext

namespace ExactSpec

abbrev R (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Defs.Exact.R ctx
abbrev R0 (ctx : ExactRealContext) : R ctx :=
  CompCert4Lean.Flocq.Core.Raux.Exact.R0 ctx
abbrev Ropp (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Raux.Exact.Ropp ctx
abbrev Rle (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Raux.Exact.Rle ctx
abbrev Rlt (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Raux.Exact.Rlt ctx
abbrev Rminus (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Raux.Exact.Rminus ctx
abbrev Rabs (ctx : ExactRealContext) :=
  CompCert4Lean.Flocq.Core.Raux.Exact.Rabs ctx

end ExactSpec

/-! Exact source statement descriptor for later proof migration. -/

def Rnd_UP_pt_oppStatement : Prop :=
  ∀ (ctx : ExactRealContext) (F : ExactSpec.R ctx → Prop),
    (∀ x, F x → F (ExactSpec.Ropp ctx x)) →
      ∀ (x f : ExactSpec.R ctx),
      CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_DN_pt ctx F x f →
      CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_UP_pt ctx F
        (ExactSpec.Ropp ctx x) (ExactSpec.Ropp ctx f)

/-! Ensures that a real number can always be rounded. -/

inductive satisfies_any (ctx : ExactRealContext) (F : ExactSpec.R ctx → Prop) : Prop where
  | Satisfies_any :
      F (ExactSpec.R0 ctx) →
      (∀ x : ExactSpec.R ctx, F x → F (ExactSpec.Ropp ctx x)) →
      CompCert4Lean.Flocq.Core.Defs.Exact.round_pred_total ctx
        (CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_DN_pt ctx F) →
      satisfies_any ctx F

def Rnd_DN_UP_pt_splitStatement : Prop :=
  ∀ (ctx : ExactRealContext) (F : ExactSpec.R ctx → Prop)
    (x d u : ExactSpec.R ctx),
    CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_DN_pt ctx F x d →
      CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_UP_pt ctx F x u →
      ∀ f, F f → ExactSpec.Rle ctx f d ∨ ExactSpec.Rle ctx u f

def Rnd_DN_pt_idempotentStatement : Prop :=
  ∀ (ctx : ExactRealContext) (F : ExactSpec.R ctx → Prop)
    (x f : ExactSpec.R ctx),
    CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_DN_pt ctx F x f → F x → f = x

def Rnd_DN_pt_monotoneStatement : Prop :=
  ∀ (ctx : ExactRealContext) (F : ExactSpec.R ctx → Prop),
    CompCert4Lean.Flocq.Core.Defs.Exact.round_pred_monotone ctx
      (CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_DN_pt ctx F)

def Rnd_DN_pt_oppStatement : Prop :=
  ∀ (ctx : ExactRealContext) (F : ExactSpec.R ctx → Prop),
    (∀ x, F x → F (ExactSpec.Ropp ctx x)) →
      ∀ (x f : ExactSpec.R ctx),
        CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_UP_pt ctx F x f →
          CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_DN_pt ctx F
            (ExactSpec.Ropp ctx x) (ExactSpec.Ropp ctx f)

def Rnd_DN_pt_uniqueStatement : Prop :=
  ∀ (ctx : ExactRealContext) (F : ExactSpec.R ctx → Prop)
    (x f1 f2 : ExactSpec.R ctx),
    CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_DN_pt ctx F x f1 →
      CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_DN_pt ctx F x f2 → f1 = f2

def Rnd_N_pt_DNStatement : Prop :=
  ∀ (ctx : ExactRealContext) (F : ExactSpec.R ctx → Prop)
    (x d u : ExactSpec.R ctx),
    CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_DN_pt ctx F x d →
      CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_UP_pt ctx F x u →
      ExactSpec.Rle ctx (ExactSpec.Rminus ctx x d) (ExactSpec.Rminus ctx u x) →
      CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_N_pt ctx F x d

def Rnd_N_pt_DN_UPStatement : Prop :=
  ∀ (ctx : ExactRealContext) (F : ExactSpec.R ctx → Prop)
    (x d u f : ExactSpec.R ctx),
    F f →
      CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_DN_pt ctx F x d →
      CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_UP_pt ctx F x u →
      ExactSpec.Rle ctx (ExactSpec.Rabs ctx (ExactSpec.Rminus ctx f x))
        (ExactSpec.Rminus ctx x d) →
      ExactSpec.Rle ctx (ExactSpec.Rabs ctx (ExactSpec.Rminus ctx f x))
        (ExactSpec.Rminus ctx u x) →
      CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_N_pt ctx F x f

def Rnd_N_pt_monotoneStatement : Prop :=
  ∀ (ctx : ExactRealContext) (F : ExactSpec.R ctx → Prop)
    (x y f g : ExactSpec.R ctx),
    CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_N_pt ctx F x f →
      CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_N_pt ctx F y g →
      ExactSpec.Rlt ctx x y → ExactSpec.Rle ctx f g

def Rnd_UP_pt_idempotentStatement : Prop :=
  ∀ (ctx : ExactRealContext) (F : ExactSpec.R ctx → Prop)
    (x f : ExactSpec.R ctx),
    CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_UP_pt ctx F x f → F x → f = x

def Rnd_UP_pt_monotoneStatement : Prop :=
  ∀ (ctx : ExactRealContext) (F : ExactSpec.R ctx → Prop),
    CompCert4Lean.Flocq.Core.Defs.Exact.round_pred_monotone ctx
      (CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_UP_pt ctx F)

def Rnd_UP_pt_uniqueStatement : Prop :=
  ∀ (ctx : ExactRealContext) (F : ExactSpec.R ctx → Prop)
    (x f1 f2 : ExactSpec.R ctx),
    CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_UP_pt ctx F x f1 →
      CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_UP_pt ctx F x f2 → f1 = f2

def round_uniqueStatement : Prop :=
  ∀ (ctx : ExactRealContext) (rnd : ExactSpec.R ctx → ExactSpec.R ctx → Prop),
    CompCert4Lean.Flocq.Core.Defs.Exact.round_pred_monotone ctx rnd →
      ∀ x f1 f2, rnd x f1 → rnd x f2 → f1 = f2

def satisfies_any_eqStatement : Prop :=
  ∀ (ctx : ExactRealContext) (F1 F2 : ExactSpec.R ctx → Prop),
    (∀ x, F1 x ↔ F2 x) → satisfies_any ctx F1 → satisfies_any ctx F2

end CompCert4Lean.Flocq.Core.Round_pred
