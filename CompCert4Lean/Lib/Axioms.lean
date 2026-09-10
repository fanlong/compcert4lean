import CompCert4Lean.Foundation.Logic

/-!
# Statement descriptors for `compcert.lib.Axioms`

The source module consists of foundational extensionality and proof-irrelevance
facts.  During definition migration these proof-bearing declarations are
represented by their exact proposition surfaces; their proof bodies are left
for the later proof-migration phase.
-/

namespace CompCert4Lean.Lib.Axioms

universe uA uB

def functional_extensionality_depStatement : Prop :=
  ∀ {A : Type uA} {B : A → Type uB} (f g : (x : A) → B x),
    (∀ x, f x = g x) → f = g

def functional_extensionalityStatement : Prop :=
  ∀ {A : Type uA} {B : Type uB} (f g : A → B),
    (∀ x, f x = g x) → f = g

def extensionalityStatement : Prop :=
  ∀ {A : Type uA} {B : Type uB} (f g : A → B),
    (∀ x, f x = g x) → f = g

def proof_irrStatement : Prop :=
  ∀ {A : Prop} (p q : A), p = q

end CompCert4Lean.Lib.Axioms

namespace CompCert4Lean.Lib.Axioms

theorem functional_extensionality_dep : functional_extensionality_depStatement :=
  CompCert4Lean.Foundation.Logic.Rocq.Coq.Logic.FunctionalExtensionality.functional_extensionality_dep

theorem functional_extensionality : functional_extensionalityStatement :=
  CompCert4Lean.Foundation.Logic.Rocq.Coq.Logic.FunctionalExtensionality.functional_extensionality

theorem extensionality : extensionalityStatement :=
  functional_extensionality

theorem proof_irr : proof_irrStatement := by
  intro A p q
  exact Subsingleton.elim p q

end CompCert4Lean.Lib.Axioms
