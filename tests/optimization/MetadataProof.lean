import CompCert4Lean.Prototype.Main

open CompCert4Lean CompCert4Lean.Prototype
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps

def metadataStep {α : Type} (index : PTree.tree α) (entry : positive × α) :
    Option (PTree.tree α) :=
  if (PTree.get entry.1 index).isSome then none
  else some (PTree.set entry.1 entry.2 index)

theorem metadataFoldLookup {α : Type} (entries : List (positive × α))
    (initial final : PTree.tree α)
    (success : entries.foldlM metadataStep initial = some final) (query : positive) :
    PTree.get query final =
      (PTree.get query initial).orElse
        (fun _ => (entries.find? (fun entry => entry.1 == query)).map Prod.snd) := by
  induction entries generalizing initial with
  | nil =>
      change some initial = some final at success
      cases success
      simp
  | cons entry rest inductionHypothesis =>
      rcases entry with ⟨identifier, value⟩
      by_cases seen : (PTree.get identifier initial).isSome = true
      · simp [List.foldlM_cons, metadataStep, seen] at success
      · have unseen : PTree.get identifier initial = none := by
          cases found : PTree.get identifier initial with
          | none => rfl
          | some value => simp [found] at seen
        have next : rest.foldlM metadataStep (PTree.set identifier value initial) = some final := by
          simpa [List.foldlM_cons, metadataStep, unseen] using success
        rw [inductionHypothesis _ next, PTree.getSet_equation]
        by_cases same : query = identifier
        · subst query
          simp [unseen]
        · simp [same, Ne.symm same]

theorem metadataIndexLookup {α : Type} (entries : List (positive × α))
    (index : PTree.tree α) (success : indexIdentifiers entries = some index)
    (query : positive) :
    PTree.get query index = (entries.find? (fun entry => entry.1 == query)).map Prod.snd := by
  have result := metadataFoldLookup entries (PTree.empty α) index success query
  simpa [PTree.get, PTree.empty] using result

#print axioms metadataIndexLookup
