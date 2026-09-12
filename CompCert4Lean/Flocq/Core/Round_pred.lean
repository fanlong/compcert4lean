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

inductive satisfies_any (ctx : ExactRealContext) :
    (F : ExactSpec.R ctx → Prop) → Prop where
  | Satisfies_any (F : ExactSpec.R ctx → Prop) :
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

namespace CompCert4Lean.Flocq.Core.Round_pred

theorem round_unique : round_uniqueStatement := by
  intro ctx rnd Hr x f1 f2 H1 H2
  apply ctx.certificate.orderedField.le_antisymm
  · exact Hr x x f1 f2 H1 H2 (ctx.certificate.orderedField.le_refl x)
  · exact Hr x x f2 f1 H2 H1 (ctx.certificate.orderedField.le_refl x)

theorem Rnd_DN_pt_monotone : Rnd_DN_pt_monotoneStatement := by
  intro ctx F x y f g Hx Hy Hxy
  rcases Hx with ⟨Hf, Hfx, Hxmax⟩
  rcases Hy with ⟨Hg, Hgy, Hymax⟩
  exact Hymax f Hf (ctx.certificate.orderedField.le_trans f x y Hfx Hxy)

theorem Rnd_DN_pt_unique : Rnd_DN_pt_uniqueStatement := by
  intro ctx F x f1 f2 H1 H2
  exact round_unique ctx (CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_DN_pt ctx F)
    (Rnd_DN_pt_monotone ctx F) x f1 f2 H1 H2

theorem Rnd_UP_pt_monotone : Rnd_UP_pt_monotoneStatement := by
  intro ctx F x y f g Hx Hy Hxy
  rcases Hx with ⟨Hf, Hxf, Hxmin⟩
  rcases Hy with ⟨Hg, Hyg, Hymin⟩
  exact Hxmin g Hg (ctx.certificate.orderedField.le_trans x y g Hxy Hyg)

end CompCert4Lean.Flocq.Core.Round_pred

namespace CompCert4Lean.Flocq.Core.Round_pred

theorem Rnd_UP_pt_unique : Rnd_UP_pt_uniqueStatement := by
  intro ctx F x f1 f2 H1 H2
  exact round_unique ctx (CompCert4Lean.Flocq.Core.Defs.Exact.Rnd_UP_pt ctx F)
    (Rnd_UP_pt_monotone ctx F) x f1 f2 H1 H2

theorem Rnd_DN_UP_pt_split : Rnd_DN_UP_pt_splitStatement := by
  intro ctx F x d u Hd Hu f Hf
  rcases ctx.certificate.total_order f x with h | h
  · rcases h with h | h
    · left
      exact Hd.2.2 f Hf
        ((ctx.certificate.orderedField.lt_iff_le_not_le f x).mp h).1
    · left
      exact Hd.2.2 f Hf (h ▸ ctx.certificate.orderedField.le_refl x)
  · right
    exact Hu.2.2 f Hf
      ((ctx.certificate.orderedField.lt_iff_le_not_le x f).mp h).1

private theorem round_add_left_cancel (ctx : ExactRealContext)
    (p q r : ExactSpec.R ctx)
    (h : ctx.spec.add p q = ctx.spec.add p r) : q = r := by
  have h' := congrArg (fun z => ctx.spec.add (ctx.spec.neg p) z) h
  have hl : ctx.spec.add (ctx.spec.neg p) (ctx.spec.add p q) = q := by
    rw [← ctx.certificate.orderedField.add_assoc,
      ctx.certificate.orderedField.neg_add_cancel,
      ctx.certificate.orderedField.zero_add]
  have hr : ctx.spec.add (ctx.spec.neg p) (ctx.spec.add p r) = r := by
    rw [← ctx.certificate.orderedField.add_assoc,
      ctx.certificate.orderedField.neg_add_cancel,
      ctx.certificate.orderedField.zero_add]
  exact hl.symm.trans (h'.trans hr)

private theorem round_neg_neg (ctx : ExactRealContext) (x : ExactSpec.R ctx) :
    ctx.spec.neg (ctx.spec.neg x) = x := by
  apply round_add_left_cancel ctx (ctx.spec.neg x)
  calc
    ctx.spec.add (ctx.spec.neg x) (ctx.spec.neg (ctx.spec.neg x)) =
        ctx.spec.add (ctx.spec.neg (ctx.spec.neg x)) (ctx.spec.neg x) :=
      ctx.certificate.orderedField.add_comm _ _
    _ = ctx.spec.zero := ctx.certificate.orderedField.neg_add_cancel _
    _ = ctx.spec.add (ctx.spec.neg x) x :=
      (ctx.certificate.orderedField.neg_add_cancel _).symm

private theorem round_neg_lt_reverse (ctx : ExactRealContext)
    (a b : ExactSpec.R ctx)
    (h : ctx.spec.lt (ctx.spec.neg a) (ctx.spec.neg b)) :
    ctx.spec.lt b a := by
  have h1 := ctx.certificate.orderedField.add_lt_compat_l
    b (ctx.spec.neg a) (ctx.spec.neg b) h
  have hbb : ctx.spec.add b (ctx.spec.neg b) = ctx.spec.zero := by
    rw [ctx.certificate.orderedField.add_comm,
      ctx.certificate.orderedField.neg_add_cancel]
  rw [hbb] at h1
  have h2 := ctx.certificate.orderedField.add_lt_compat_l
    a (ctx.spec.add b (ctx.spec.neg a)) ctx.spec.zero h1
  have haa : ctx.spec.add a (ctx.spec.neg a) = ctx.spec.zero := by
    rw [ctx.certificate.orderedField.add_comm,
      ctx.certificate.orderedField.neg_add_cancel]
  have hleft : ctx.spec.add a (ctx.spec.add b (ctx.spec.neg a)) = b := by
    calc
      ctx.spec.add a (ctx.spec.add b (ctx.spec.neg a)) =
          ctx.spec.add (ctx.spec.add a b) (ctx.spec.neg a) :=
        (ctx.certificate.orderedField.add_assoc _ _ _).symm
      _ = ctx.spec.add (ctx.spec.add b a) (ctx.spec.neg a) := by
        rw [ctx.certificate.orderedField.add_comm a b]
      _ = ctx.spec.add b (ctx.spec.add a (ctx.spec.neg a)) :=
        ctx.certificate.orderedField.add_assoc _ _ _
      _ = ctx.spec.add b ctx.spec.zero := by rw [haa]
      _ = b := ctx.certificate.orderedField.add_zero _
  have hright : ctx.spec.add a ctx.spec.zero = a :=
    ctx.certificate.orderedField.add_zero _
  rw [hleft, hright] at h2
  exact h2

private theorem round_neg_le_contravar (ctx : ExactRealContext)
    (a b : ExactSpec.R ctx)
    (h : ctx.spec.le a b) :
    ctx.spec.le (ctx.spec.neg b) (ctx.spec.neg a) := by
  rcases ctx.certificate.total_order (ctx.spec.neg b) (ctx.spec.neg a) with h' | h'
  · rcases h' with h' | h'
    · exact (ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp h' |>.1
    · rw [h']
      exact ctx.certificate.orderedField.le_refl _
  · have hba : ctx.spec.lt b a := round_neg_lt_reverse ctx _ _ h'
    have hfalse : False := ((ctx.certificate.orderedField.lt_iff_le_not_le _ _).mp hba).2 h
    exact hfalse.elim

private theorem round_neg_le_cancel (ctx : ExactRealContext)
    (a b : ExactSpec.R ctx)
    (h : ctx.spec.le (ctx.spec.neg b) (ctx.spec.neg a)) :
    ctx.spec.le a b := by
  have h' := round_neg_le_contravar ctx (ctx.spec.neg b) (ctx.spec.neg a) h
  rw [round_neg_neg ctx a, round_neg_neg ctx b] at h'
  exact h'

theorem Rnd_UP_pt_opp : Rnd_UP_pt_oppStatement := by
  intro ctx F HF x f H
  refine ⟨HF f H.1, round_neg_le_contravar ctx f x H.2.1, ?_⟩
  intro g Hg Hxg
  have hnegx : ctx.spec.le (ctx.spec.neg g) x := by
    have h' := round_neg_le_contravar ctx (ctx.spec.neg x) g Hxg
    rw [round_neg_neg ctx x] at h'
    exact h'
  have hgf := H.2.2 (ctx.spec.neg g) (HF g Hg) hnegx
  have h' := round_neg_le_contravar ctx (ctx.spec.neg g) f hgf
  rw [round_neg_neg ctx g] at h'
  exact h'

theorem Rnd_DN_pt_opp : Rnd_DN_pt_oppStatement := by
  intro ctx F HF x f H
  refine ⟨HF f H.1, round_neg_le_contravar ctx x f H.2.1, ?_⟩
  intro g Hg Hgx
  have hnegx : ctx.spec.le x (ctx.spec.neg g) := by
    have h' := round_neg_le_contravar ctx g (ctx.spec.neg x) Hgx
    rw [round_neg_neg ctx x] at h'
    exact h'
  have hfg := H.2.2 (ctx.spec.neg g) (HF g Hg) hnegx
  have h' := round_neg_le_contravar ctx f (ctx.spec.neg g) hfg
  rw [round_neg_neg ctx g] at h'
  exact h'

end CompCert4Lean.Flocq.Core.Round_pred

namespace CompCert4Lean.Flocq.Core.Round_pred

theorem Rnd_DN_pt_idempotent : Rnd_DN_pt_idempotentStatement := by
  intro ctx F x f H Hx
  apply ctx.certificate.orderedField.le_antisymm
  · exact H.2.1
  · exact H.2.2 x Hx (ctx.certificate.orderedField.le_refl x)

end CompCert4Lean.Flocq.Core.Round_pred

namespace CompCert4Lean.Flocq.Core.Round_pred

theorem Rnd_UP_pt_idempotent : Rnd_UP_pt_idempotentStatement := by
  intro ctx F x f H Hx
  apply ctx.certificate.orderedField.le_antisymm
  · exact H.2.2 x Hx (ctx.certificate.orderedField.le_refl x)
  · exact H.2.1

end CompCert4Lean.Flocq.Core.Round_pred
