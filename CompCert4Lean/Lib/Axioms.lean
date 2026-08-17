import CompCert4Lean.Foundation.Logic

/-!
# Statement descriptors for `compcert.lib.Axioms`

The source module consists of foundational extensionality and proof-irrelevance
facts.  During definition migration these proof-bearing declarations are
represented by their exact proposition surfaces; their proof bodies are left
for the later proof-migration phase.
-/

namespace CompCert4Lean.Lib.Axioms

def functional_extensionality_depStatement : Prop :=
  ∀ {A : Type} {B : A → Type} (f g : (x : A) → B x),
    (∀ x, f x = g x) → f = g

def functional_extensionalityStatement : Prop :=
  ∀ {A B : Type} (f g : A → B),
    (∀ x, f x = g x) → f = g

def extensionalityStatement : Prop :=
  ∀ {A B : Type} (f g : A → B),
    (∀ x, f x = g x) → f = g

def proof_irrStatement : Prop :=
  ∀ {A : Prop} (p q : A), p = q

end CompCert4Lean.Lib.Axioms
