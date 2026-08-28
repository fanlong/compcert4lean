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
deriving DecidableEq

/-! The source module places these constructors directly under `R`.  Lean
    stores them under their inductive owner (`R.t`), so expose the same
    source-facing spellings as reducible match patterns for the genuine
    constructors. -/
@[match_pattern] abbrev Nil : t := t.Nil
@[match_pattern] abbrev Cons (lo hi : Z) (tail : t) : t := t.Cons lo hi tail

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

@[match_pattern] abbrev ok_nil : ok Nil := ok.ok_nil
@[match_pattern] abbrev ok_cons (l h : Z) (s : t)
    (bounds : ZArith.BinInt.Z.lt l h)
    (below : ∀ x, In x s → ZArith.BinInt.Z.lt h x)
    (tail_ok : ok s) : ok (Cons l h s) :=
  ok.ok_cons l h s bounds below tail_ok

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

private def length : t → Nat
  | .Nil => 0
  | .Cons _ _ tail => length tail + 1

def inter (s1 s2 : t) : t :=
  match s1, s2 with
  | .Nil, _ => .Nil
  | _, .Nil => .Nil
  | .Cons l1 h1 s1', .Cons l2 h2 s2' =>
      if ZArith.BinInt.Z.leb h1 l2 then
        inter s1' (.Cons l2 h2 s2')
      else if ZArith.BinInt.Z.leb h2 l1 then
        inter (.Cons l1 h1 s1') s2'
      else if ZArith.BinInt.Z.leb l1 l2 then
        if ZArith.BinInt.Z.leb h2 h1 then
          .Cons l2 h2 (inter (.Cons l1 h1 s1') s2')
        else
          .Cons l2 h1 (inter s1' (.Cons l2 h2 s2'))
      else if ZArith.BinInt.Z.leb h1 h2 then
        .Cons l1 h1 (inter s1' (.Cons l2 h2 s2'))
      else
        .Cons l1 h2 (inter (.Cons l1 h1 s1') s2')
termination_by length s1 + length s2
decreasing_by all_goals simp_all [length]

private theorem inInter (x : Z) (s1 s2 : t) (hs1 : ok s1) (hs2 : ok s2) :
    In x (inter s1 s2) ↔ In x s1 ∧ In x s2 := by
  induction hs1 generalizing s2 with
  | ok_nil => simp [inter, In]
  | ok_cons l1 h1 t1 bounds1 below1 tailOk1 ih1 =>
      induction hs2 with
      | ok_nil => simp [inter, In]
      | ok_cons l2 h2 t2 bounds2 below2 tailOk2 ih2 =>
          have ok1 : ok (.Cons l1 h1 t1) :=
            .ok_cons l1 h1 t1 bounds1 below1 tailOk1
          have ok2 : ok (.Cons l2 h2 t2) :=
            .ok_cons l2 h2 t2 bounds2 below2 tailOk2
          simp only [inter]
          split <;> rename_i h12
          · rw [ih1 _ ok2]
            simp only [In]
            constructor
            · rintro ⟨hx1, hx2⟩
              exact ⟨Or.inr hx1, hx2⟩
            · rintro ⟨hx1 | hx1, hx2⟩
              · rcases hx2 with hx2 | hx2
                · simp [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.le,
                    ZArith.BinInt.Z.lt] at h12 hx1 hx2
                  omega
                · have := below2 x hx2
                  simp [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.le,
                    ZArith.BinInt.Z.lt] at h12 bounds2 hx1 this
                  omega
              · exact ⟨hx1, hx2⟩
          · split <;> rename_i h21
            · rw [ih2]
              simp only [In]
              constructor
              · rintro ⟨hx1, hx2⟩
                exact ⟨hx1, Or.inr hx2⟩
              · rintro ⟨hx1, hx2 | hx2⟩
                · rcases hx1 with hx1 | hx1
                  · simp [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.le,
                      ZArith.BinInt.Z.lt] at h21 hx1 hx2
                    omega
                  · have := below1 x hx1
                    simp [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.le,
                      ZArith.BinInt.Z.lt] at h21 bounds1 hx2 this
                    omega
                · exact ⟨hx1, hx2⟩
            · split <;> rename_i hlo
              · split <;> rename_i hhi
                · simp only [In]
                  rw [ih2]
                  constructor
                  · rintro (hx | ⟨hx1, hx2⟩)
                    · constructor
                      · left
                        simp [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.le,
                          ZArith.BinInt.Z.lt] at hlo hhi hx ⊢
                        omega
                      · exact Or.inl hx
                    · exact ⟨hx1, Or.inr hx2⟩
                  · rintro ⟨hx1, hx2 | hx2⟩
                    · exact Or.inl hx2
                    · exact Or.inr ⟨hx1, hx2⟩
                · simp only [In]
                  rw [ih1 _ ok2]
                  constructor
                  · rintro (hx | ⟨hx1, hx2⟩)
                    · constructor
                      · exact Or.inl ⟨by
                          simp [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.le,
                            ZArith.BinInt.Z.lt] at hlo hx ⊢
                          omega, hx.2⟩
                      · exact Or.inl ⟨hx.1, by
                          simp [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.le,
                            ZArith.BinInt.Z.lt] at hhi hx ⊢
                          omega⟩
                    · exact ⟨Or.inr hx1, hx2⟩
                  · rintro ⟨hx1 | hx1, hx2⟩
                    · rcases hx2 with hx2 | hx2
                      · exact Or.inl ⟨hx2.1, hx1.2⟩
                      · have hb := below2 x hx2
                        exfalso
                        simp [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.le,
                          ZArith.BinInt.Z.lt] at hhi hx1 hb
                        omega
                    · exact Or.inr ⟨hx1, hx2⟩
              · split <;> rename_i hhi
                · simp only [In]
                  rw [ih1 _ ok2]
                  constructor
                  · rintro (hx | ⟨hx1, hx2⟩)
                    · constructor
                      · exact Or.inl hx
                      · exact Or.inl ⟨by
                          simp [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.le,
                            ZArith.BinInt.Z.lt] at hlo hx ⊢
                          omega, by
                          simp [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.le,
                            ZArith.BinInt.Z.lt] at hhi hx ⊢
                          omega⟩
                    · exact ⟨Or.inr hx1, hx2⟩
                  · rintro ⟨hx1, hx2 | hx2⟩
                    · rcases hx1 with hx1 | hx1
                      · exact Or.inl hx1
                      · exact Or.inr ⟨hx1, Or.inl hx2⟩
                    · rcases hx1 with hx1 | hx1
                      · have hb := below2 x hx2
                        exfalso
                        simp [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.le,
                          ZArith.BinInt.Z.lt] at hhi hx1 hb
                        omega
                      · exact Or.inr ⟨hx1, Or.inr hx2⟩
                · simp only [In]
                  rw [ih2]
                  constructor
                  · rintro (hx | ⟨hx1, hx2⟩)
                    · constructor
                      · exact Or.inl ⟨hx.1, by
                          simp [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.le,
                            ZArith.BinInt.Z.lt] at hhi hx ⊢
                          omega⟩
                      · exact Or.inl ⟨by
                          simp [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.le,
                            ZArith.BinInt.Z.lt] at hlo hx ⊢
                          omega, hx.2⟩
                    · exact ⟨hx1, Or.inr hx2⟩
                  · rintro ⟨hx1, hx2 | hx2⟩
                    · rcases hx1 with hx1 | hx1
                      · exact Or.inl ⟨hx1.1, hx2.2⟩
                      · have hb := below1 x hx1
                        exfalso
                        simp [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.le,
                          ZArith.BinInt.Z.lt] at hhi hx2 hb
                        omega
                    · exact Or.inr ⟨hx1, hx2⟩

private theorem interOk (s1 s2 : t) (hs1 : ok s1) (hs2 : ok s2) :
    ok (inter s1 s2) := by
  induction hs1 generalizing s2 with
  | ok_nil => simp [inter]; exact .ok_nil
  | ok_cons l1 h1 t1 bounds1 below1 tailOk1 ih1 =>
      induction hs2 with
      | ok_nil => simp [inter]; exact .ok_nil
      | ok_cons l2 h2 t2 bounds2 below2 tailOk2 ih2 =>
          have ok1 : ok (.Cons l1 h1 t1) :=
            .ok_cons l1 h1 t1 bounds1 below1 tailOk1
          have ok2 : ok (.Cons l2 h2 t2) :=
            .ok_cons l2 h2 t2 bounds2 below2 tailOk2
          simp only [inter]
          split <;> rename_i h12
          · exact ih1 _ ok2
          · split <;> rename_i h21
            · exact ih2
            · split <;> rename_i hlo
              · split <;> rename_i hhi
                · apply ok.ok_cons l2 h2 _ bounds2
                  · intro x hx
                    rw [inInter x _ _ ok1 tailOk2] at hx
                    exact below2 x hx.2
                  · exact ih2
                · apply ok.ok_cons l2 h1 _
                    (by
                      simp [ZArith.BinInt.Z.leb,
                        ZArith.BinInt.Z.lt] at h12 ⊢
                      omega)
                  · intro x hx
                    rw [inInter x _ _ tailOk1 ok2] at hx
                    exact below1 x hx.1
                  · exact ih1 _ ok2
              · split <;> rename_i hhi
                · apply ok.ok_cons l1 h1 _ bounds1
                  · intro x hx
                    rw [inInter x _ _ tailOk1 ok2] at hx
                    exact below1 x hx.1
                  · exact ih1 _ ok2
                · apply ok.ok_cons l1 h2 _
                    (by
                      simp [ZArith.BinInt.Z.leb,
                        ZArith.BinInt.Z.lt] at h21 ⊢
                      omega)
                  · intro x hx
                    rw [inInter x _ _ ok1 tailOk2] at hx
                    exact below2 x hx.2
                  · exact ih2

def beq : t → t → Bool
  | .Nil, .Nil => true
  | .Cons l1 h1 t1, .Cons l2 h2 t2 =>
      decide (l1 = l2) && decide (h1 = h2) && beq t1 t2
  | _, _ => false

def contains (L H : Z) : t → Bool
  | .Nil => false
  | .Cons l h tail =>
      (ZArith.BinInt.Z.leb H h && ZArith.BinInt.Z.leb l L) ||
        contains L H tail

/-! Source-named raw proof surfaces.  Their propositions retain the exact
    source binder order; proof terms are assigned to proof grinding. -/

def contains_InStatement : Prop :=
  ∀ l0 h0 : Z, ZArith.BinInt.Z.lt l0 h0 → ∀ s : t, ok s →
    (contains l0 h0 s = true ↔
      ∀ x : Z,
        (ZArith.BinInt.Z.le l0 x ∧ ZArith.BinInt.Z.lt x h0) → In x s)

def In_addStatement : Prop :=
  ∀ x : Z, ∀ s : t, ok s → ∀ l0 h0 : Z,
    In x (add l0 h0 s) ↔
      (ZArith.BinInt.Z.le l0 x ∧ ZArith.BinInt.Z.lt x h0) ∨ In x s

def add_okStatement : Prop :=
  ∀ s : t, ok s → ∀ l0 h0 : Z,
    ZArith.BinInt.Z.lt l0 h0 → ok (add l0 h0 s)

def In_removeStatement : Prop :=
  ∀ x l0 h0 : Z, ∀ s : t, ok s →
    (In x (remove l0 h0 s) ↔
      ¬ (ZArith.BinInt.Z.le l0 x ∧ ZArith.BinInt.Z.lt x h0) ∧ In x s)

def remove_okStatement : Prop :=
  ∀ l0 h0 : Z, ZArith.BinInt.Z.lt l0 h0 → ∀ s : t,
    ok s → ok (remove l0 h0 s)

def In_interStatement : Prop :=
  ∀ x : Z, ∀ s1 : t, ok s1 → ∀ s2 : t, ok s2 →
    (In x (inter s1 s2) ↔ In x s1 ∧ In x s2)

def inter_okStatement : Prop :=
  ∀ s1 : t, ok s1 → ∀ s2 : t, ok s2 → ok (inter s1 s2)

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

def inter (s1 s2 : t) : t :=
  ⟨R.inter s1.1 s2.1, R.interOk s1.1 s2.1 s1.2 s2.2⟩

def beq (s1 s2 : t) : Bool := R.beq s1.1 s2.1

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
