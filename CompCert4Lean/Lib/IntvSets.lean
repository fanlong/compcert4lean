import CompCert4Lean.Lib.Coqlib

/-!
# Finite sets of integer intervals

This module translates the executable interface of `compcert.lib.IntvSets`.
The source's proof-bearing results are retained as exact proposition
descriptors for the later proof-migration phase.
-/

namespace CompCert4Lean.Lib.IntvSets

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

namespace ISet

/-! The raw representation and its ordering invariant from source module `R`. -/
namespace R

inductive t : Type where
  | Nil
  | Cons (lo hi : Z) (tail : t)

def In (x : Z) : t → Prop
  | .Nil => False
  | .Cons lo hi tail =>
      (ZArith.BinInt.Z.le lo x ∧ ZArith.BinInt.Z.lt x hi) ∨ In x tail

inductive ok : t → Prop where
  | ok_nil : ok .Nil
  | ok_cons (l h : Z) (s : t)
      (bounds : ZArith.BinInt.Z.lt l h)
      (below : ∀ x, In x s → ZArith.BinInt.Z.lt h x)
      (tail_ok : ok s) :
      ok (.Cons l h s)

def add (L H : Z) : t → t
  | .Nil => .Cons L H .Nil
  | .Cons l h tail =>
      if ZArith.BinInt.Z.ltb h L then
        .Cons l h (add L H tail)
      else if ZArith.BinInt.Z.ltb H l then
        .Cons L H (.Cons l h tail)
      else
        add (ZArith.BinInt.Z.min l L) (ZArith.BinInt.Z.max h H) tail

private theorem mergedInterval (l h L H x : Z)
    (hLh : ¬ ZArith.BinInt.Z.lt h L)
    (hHl : ¬ ZArith.BinInt.Z.lt H l) :
    (ZArith.BinInt.Z.le (ZArith.BinInt.Z.min l L) x ∧
      ZArith.BinInt.Z.lt x (ZArith.BinInt.Z.max h H)) ↔
    (ZArith.BinInt.Z.le L x ∧ ZArith.BinInt.Z.lt x H) ∨
      (ZArith.BinInt.Z.le l x ∧ ZArith.BinInt.Z.lt x h) := by
  simp only [ZArith.BinInt.Z.min, ZArith.BinInt.Z.max]
  split <;> split <;>
    simp_all [ZArith.BinInt.Z.lt, ZArith.BinInt.Z.le] <;> omega

private theorem inAdd (x : Z) {s : t} (hs : ok s) :
    ∀ L H, In x (add L H s) ↔
      (ZArith.BinInt.Z.le L x ∧ ZArith.BinInt.Z.lt x H) ∨ In x s := by
  induction hs with
  | ok_nil =>
      intro L H
      simp [add, In]
  | ok_cons l h s bounds below tail_ok ih =>
      intro L H
      simp only [add]
      split <;> rename_i hlt
      · simp only [In, ih]
        constructor
        · intro hx
          rcases hx with hx | hx
          · exact Or.inr (Or.inl hx)
          · rcases hx with hx | hx
            · exact Or.inl hx
            · exact Or.inr (Or.inr hx)
        · intro hx
          rcases hx with hx | hx
          · exact Or.inr (Or.inl hx)
          · rcases hx with hx | hx
            · exact Or.inl hx
            · exact Or.inr (Or.inr hx)
      · split <;> rename_i hlt'
        · simp only [In]
        · rw [ih]
          rw [mergedInterval l h L H x]
          · constructor
            · intro hx
              rcases hx with (hx | hx) | hx
              · exact Or.inl hx
              · exact Or.inr (Or.inl hx)
              · exact Or.inr (Or.inr hx)
            · intro hx
              rcases hx with hx | hx
              · exact Or.inl (Or.inl hx)
              · rcases hx with hx | hx
                · exact Or.inl (Or.inr hx)
                · exact Or.inr hx
          · simp [ZArith.BinInt.Z.ltb,
              ZArith.BinInt.Z.lt] at hlt ⊢
            exact hlt
          · simp [ZArith.BinInt.Z.ltb,
              ZArith.BinInt.Z.lt] at hlt' ⊢
            exact hlt'

private theorem addOk {s : t} (hs : ok s) :
    ∀ L H, ZArith.BinInt.Z.lt L H → ok (add L H s) := by
  induction hs with
  | ok_nil =>
      intro L H hLH
      exact .ok_cons L H .Nil hLH (by simp [In]) .ok_nil
  | ok_cons l h s bounds below tail_ok ih =>
      intro L H hLH
      simp only [add]
      split <;> rename_i hlt
      · apply ok.ok_cons l h (add L H s) bounds
        · intro x hx
          rw [inAdd x tail_ok L H] at hx
          rcases hx with hx | hx
          · simp [ZArith.BinInt.Z.ltb, ZArith.BinInt.Z.lt,
              ZArith.BinInt.Z.le] at hlt hx ⊢
            omega
          · exact below x hx
        · exact ih L H hLH
      · split <;> rename_i hlt'
        · apply ok.ok_cons L H (.Cons l h s) hLH
          · intro x hx
            rcases hx with hx | hx
            · simp [ZArith.BinInt.Z.ltb, ZArith.BinInt.Z.lt,
                ZArith.BinInt.Z.le] at hlt' hx ⊢
              omega
            · have hbelow := below x hx
              simp [ZArith.BinInt.Z.ltb,
                ZArith.BinInt.Z.lt] at hlt' bounds hbelow ⊢
              omega
          · exact .ok_cons l h s bounds below tail_ok
        · apply ih
          simp only [ZArith.BinInt.Z.min, ZArith.BinInt.Z.max]
          split <;> split <;>
            simp_all [ZArith.BinInt.Z.lt] <;> omega

def remove (L H : Z) : t → t
  | .Nil => .Nil
  | .Cons l h tail =>
      if ZArith.BinInt.Z.ltb h L then
        .Cons l h (remove L H tail)
      else if ZArith.BinInt.Z.ltb H l then
        .Cons l h tail
      else if ZArith.BinInt.Z.ltb l L then
        if ZArith.BinInt.Z.ltb H h then
          .Cons l L (.Cons H h tail)
        else
          .Cons l L (remove L H tail)
      else if ZArith.BinInt.Z.ltb H h then
        .Cons H h tail
      else
        remove L H tail

private theorem removeSubset (x L H : Z) :
    ∀ s, In x (remove L H s) → In x s := by
  intro s
  induction s with
  | Nil => simp [remove, In]
  | Cons l h s ih =>
      simp only [remove]
      split <;> rename_i hlt
      · intro hx
        rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (ih hx)
      · split <;> rename_i hlt'
        · exact fun hx => hx
        · split <;> rename_i hleft
          · split <;> rename_i hright
            · intro hx
              rcases hx with hx | hx
              · exact Or.inl (by
                  simp [ZArith.BinInt.Z.ltb, ZArith.BinInt.Z.lt,
                    ZArith.BinInt.Z.le] at hlt hx ⊢
                  omega)
              · rcases hx with hx | hx
                · exact Or.inl (by
                    simp [ZArith.BinInt.Z.lt,
                      ZArith.BinInt.Z.le] at hx ⊢
                    simp [ZArith.BinInt.Z.ltb] at hlt'
                    omega)
                · exact Or.inr hx
            · intro hx
              rcases hx with hx | hx
              · exact Or.inl (by
                  simp [ZArith.BinInt.Z.ltb, ZArith.BinInt.Z.lt,
                    ZArith.BinInt.Z.le] at hlt hx ⊢
                  omega)
              · exact Or.inr (ih hx)
          · split <;> rename_i hright
            · intro hx
              rcases hx with hx | hx
              · exact Or.inl (by
                  simp [ZArith.BinInt.Z.ltb, ZArith.BinInt.Z.lt,
                    ZArith.BinInt.Z.le] at hlt' hleft hx ⊢
                  omega)
              · exact Or.inr hx
            · exact fun hx => Or.inr (ih hx)

private theorem removeOk (L H : Z) (hLH : ZArith.BinInt.Z.lt L H) :
    ∀ {s : t}, ok s → ok (remove L H s) := by
  intro s hs
  induction hs with
  | ok_nil => exact .ok_nil
  | ok_cons l h s bounds below tail_ok ih =>
      simp only [remove]
      split <;> rename_i hlt
      · apply ok.ok_cons l h (remove L H s) bounds
        · intro x hx
          exact below x (removeSubset x L H s hx)
        · exact ih
      · split <;> rename_i hlt'
        · exact .ok_cons l h s bounds below tail_ok
        · split <;> rename_i hleft
          · split <;> rename_i hright
            · apply ok.ok_cons l L (.Cons H h s)
                (by
                  simp [ZArith.BinInt.Z.ltb, ZArith.BinInt.Z.lt] at hleft ⊢
                  exact hleft)
              · intro x hx
                rcases hx with hx | hx
                · simp [ZArith.BinInt.Z.lt,
                    ZArith.BinInt.Z.le] at hLH hx ⊢
                  omega
                · have hbelow := below x hx
                  simp [ZArith.BinInt.Z.ltb,
                    ZArith.BinInt.Z.lt] at hlt hbelow ⊢
                  omega
              · exact .ok_cons H h s
                  (by
                    simp [ZArith.BinInt.Z.ltb,
                      ZArith.BinInt.Z.lt] at hright ⊢
                    exact hright)
                  below tail_ok
            · apply ok.ok_cons l L (remove L H s)
                (by
                  simp [ZArith.BinInt.Z.ltb,
                    ZArith.BinInt.Z.lt] at hleft ⊢
                  exact hleft)
              · intro x hx
                have hbelow := below x (removeSubset x L H s hx)
                simp [ZArith.BinInt.Z.ltb,
                  ZArith.BinInt.Z.lt] at hlt hbelow ⊢
                omega
              · exact ih
          · split <;> rename_i hright
            · exact .ok_cons H h s
                (by
                  simp [ZArith.BinInt.Z.ltb,
                    ZArith.BinInt.Z.lt] at hright ⊢
                  exact hright)
                below tail_ok
            · exact ih

def contains (L H : Z) : t → Bool
  | .Nil => false
  | .Cons l h tail =>
      (ZArith.BinInt.Z.leb H h && ZArith.BinInt.Z.leb l L) ||
        contains L H tail

end R

def t : Type := {r : R.t // R.ok r}

def In (x : Z) (s : t) : Prop := R.In x s.1

def empty : t := ⟨.Nil, .ok_nil⟩

def interval (l h : Z) : t :=
  if hlt : ZArith.BinInt.Z.ltb l h then
    ⟨.Cons l h .Nil, .ok_cons l h .Nil
      (by
        simp [ZArith.BinInt.Z.ltb, ZArith.BinInt.Z.lt] at hlt ⊢
        exact hlt)
      (by simp [R.In]) .ok_nil⟩
  else
    empty

def add (l h : Z) (s : t) : t :=
  if hlt : ZArith.BinInt.Z.ltb l h then
    ⟨R.add l h s.1, R.addOk s.2 l h (by
      simp [ZArith.BinInt.Z.ltb, ZArith.BinInt.Z.lt] at hlt ⊢
      exact hlt)⟩
  else
    s

def remove (l h : Z) (s : t) : t :=
  if hlt : ZArith.BinInt.Z.ltb l h then
    ⟨R.remove l h s.1, R.removeOk l h (by
      simp [ZArith.BinInt.Z.ltb, ZArith.BinInt.Z.lt] at hlt ⊢
      exact hlt) s.2⟩
  else
    s

def contains (l h : Z) (s : t) : Bool :=
  if ZArith.BinInt.Z.ltb l h then
    R.contains l h s.1
  else
    true

def In_emptyStatement : Prop :=
  ∀ x : Z, ¬ In x empty

def In_intervalStatement : Prop :=
  ∀ x l h : Z, In x (interval l h) ↔
    (ZArith.BinInt.Z.le l x ∧ ZArith.BinInt.Z.lt x h)

def In_addStatement : Prop :=
  ∀ x l h : Z, ∀ s : t,
    In x (add l h s) ↔
      (ZArith.BinInt.Z.le l x ∧ ZArith.BinInt.Z.lt x h) ∨ In x s

def In_removeStatement : Prop :=
  ∀ x l h : Z, ∀ s : t,
    In x (remove l h s) ↔
      ¬ (ZArith.BinInt.Z.le l x ∧ ZArith.BinInt.Z.lt x h) ∧ In x s

def contains_specStatement : Prop :=
  ∀ l h : Z, ∀ s : t,
    contains l h s = true ↔
      ∀ x : Z,
        (ZArith.BinInt.Z.le l x ∧ ZArith.BinInt.Z.lt x h) → In x s

end ISet

end CompCert4Lean.Lib.IntvSets
