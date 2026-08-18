import CompCert4Lean.Common.Events
import CompCert4Lean.Foundation.Ordered
import CompCert4Lean.Foundation.Recursion
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Integers

/-!
# Small-step operational semantics

Definition-bearing translation of CompCert's `common/Smallstep.v`.  Results
assigned to later proof migration are represented by transparent proposition
descriptors with the source quantifier order.
-/

namespace CompCert4Lean.Common.Smallstep

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers

/-! ## Closures of transition relations -/

def nostep {genv state : Type}
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s : state) : Prop :=
  ∀ t s', ¬ step ge s t s'

inductive star {genv state : Type}
    (step : genv → state → trace → state → Prop)
    (ge : genv) : state → trace → state → Prop where
  | star_refl (s : state) : star step ge s E0 s
  | star_step (s1 : state) (t1 : trace) (s2 : state)
      (t2 : trace) (s3 : state) (t : trace)
      (hstep : step ge s1 t1 s2)
      (hstar : star step ge s2 t2 s3)
      (htrace : t = Eapp t1 t2) : star step ge s1 t s3

export star (star_refl star_step)

def star_oneStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s1 : state) (t : trace) (s2 : state),
    step ge s1 t s2 → star step ge s1 t s2

def star_twoStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s1 : state) (t1 : trace) (s2 : state)
    (t2 : trace) (s3 : state) (t : trace),
    step ge s1 t1 s2 → step ge s2 t2 s3 →
    t = Eapp t1 t2 → star step ge s1 t s3

def star_threeStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s1 : state) (t1 : trace) (s2 : state)
    (t2 : trace) (s3 : state) (t3 : trace) (s4 : state) (t : trace),
    step ge s1 t1 s2 → step ge s2 t2 s3 → step ge s3 t3 s4 →
    t = Eapp t1 (Eapp t2 t3) → star step ge s1 t s4

def star_transStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s1 : state) (t1 : trace) (s2 : state),
    star step ge s1 t1 s2 →
    ∀ (t2 : trace) (s3 : state) (t : trace),
      star step ge s2 t2 s3 →
      t = Eapp t1 t2 → star step ge s1 t s3

def star_leftStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s1 : state) (t1 : trace) (s2 : state)
    (t2 : trace) (s3 : state) (t : trace),
    step ge s1 t1 s2 → star step ge s2 t2 s3 →
    t = Eapp t1 t2 → star step ge s1 t s3

def star_rightStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s1 : state) (t1 : trace) (s2 : state)
    (t2 : trace) (s3 : state) (t : trace),
    star step ge s1 t1 s2 → step ge s2 t2 s3 →
    t = Eapp t1 t2 → star step ge s1 t s3

def star_E0_indStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (ge : genv) (P : state → state → Prop),
    (∀ s, P s s) →
    (∀ s1 s2 s3, step ge s1 E0 s2 → P s2 s3 → P s1 s3) →
    ∀ s1 s2, star step ge s1 E0 s2 → P s1 s2

inductive plus {genv state : Type}
    (step : genv → state → trace → state → Prop)
    (ge : genv) : state → trace → state → Prop where
  | plus_left (s1 : state) (t1 : trace) (s2 : state)
      (t2 : trace) (s3 : state) (t : trace)
      (hstep : step ge s1 t1 s2)
      (hstar : star step ge s2 t2 s3)
      (htrace : t = Eapp t1 t2) : plus step ge s1 t s3

export plus (plus_left)

def plus_oneStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s1 : state) (t : trace) (s2 : state),
    step ge s1 t s2 → plus step ge s1 t s2

def plus_twoStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s1 : state) (t1 : trace) (s2 : state)
    (t2 : trace) (s3 : state) (t : trace),
    step ge s1 t1 s2 → step ge s2 t2 s3 →
    t = Eapp t1 t2 → plus step ge s1 t s3

def plus_threeStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s1 : state) (t1 : trace) (s2 : state)
    (t2 : trace) (s3 : state) (t3 : trace) (s4 : state) (t : trace),
    step ge s1 t1 s2 → step ge s2 t2 s3 → step ge s3 t3 s4 →
    t = Eapp t1 (Eapp t2 t3) → plus step ge s1 t s4

def plus_fourStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s1 : state) (t1 : trace) (s2 : state)
    (t2 : trace) (s3 : state) (t3 : trace) (s4 : state)
    (t4 : trace) (s5 : state) (t : trace),
    step ge s1 t1 s2 → step ge s2 t2 s3 →
    step ge s3 t3 s4 → step ge s4 t4 s5 →
    t = Eapp t1 (Eapp t2 (Eapp t3 t4)) → plus step ge s1 t s5

def plus_starStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s1 : state) (t : trace) (s2 : state),
    plus step ge s1 t s2 → star step ge s1 t s2

def plus_rightStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s1 : state) (t1 : trace) (s2 : state)
    (t2 : trace) (s3 : state) (t : trace),
    star step ge s1 t1 s2 → step ge s2 t2 s3 →
    t = Eapp t1 t2 → plus step ge s1 t s3

def plus_left'Statement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s1 : state) (t1 : trace) (s2 : state)
    (t2 : trace) (s3 : state) (t : trace),
    step ge s1 t1 s2 → plus step ge s2 t2 s3 →
    t = Eapp t1 t2 → plus step ge s1 t s3

def plus_right'Statement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s1 : state) (t1 : trace) (s2 : state)
    (t2 : trace) (s3 : state) (t : trace),
    plus step ge s1 t1 s2 → step ge s2 t2 s3 →
    t = Eapp t1 t2 → plus step ge s1 t s3

def plus_star_transStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s1 : state) (t1 : trace) (s2 : state)
    (t2 : trace) (s3 : state) (t : trace),
    plus step ge s1 t1 s2 → star step ge s2 t2 s3 →
    t = Eapp t1 t2 → plus step ge s1 t s3

def star_plus_transStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s1 : state) (t1 : trace) (s2 : state)
    (t2 : trace) (s3 : state) (t : trace),
    star step ge s1 t1 s2 → plus step ge s2 t2 s3 →
    t = Eapp t1 t2 → plus step ge s1 t s3

def plus_transStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s1 : state) (t1 : trace) (s2 : state)
    (t2 : trace) (s3 : state) (t : trace),
    plus step ge s1 t1 s2 → plus step ge s2 t2 s3 →
    t = Eapp t1 t2 → plus step ge s1 t s3

def star_invStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s1 : state) (t : trace) (s2 : state),
    star step ge s1 t s2 →
    (s2 = s1 ∧ t = E0) ∨ plus step ge s1 t s2

def plus_ind2Statement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (ge : genv) (P : state → trace → state → Prop),
    (∀ s1 t s2, step ge s1 t s2 → P s1 t s2) →
    (∀ s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 → plus step ge s2 t2 s3 →
      P s2 t2 s3 → t = Eapp t1 t2 → P s1 t s3) →
    ∀ s1 t s2, plus step ge s1 t s2 → P s1 t s2

inductive starN {genv state : Type}
    (step : genv → state → trace → state → Prop)
    (ge : genv) : Nat → state → trace → state → Prop where
  | refl (s : state) : starN step ge 0 s E0 s
  | step (n : Nat) (s : state) (t t1 : trace)
      (s' : state) (t2 : trace) (s'' : state)
      (hstep : step ge s t1 s')
      (hstar : starN step ge n s' t2 s'')
      (htrace : t = Eapp t1 t2) : starN step ge (n + 1) s t s''

def star_starNStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s : state) (t : trace) (s' : state),
    star step ge s t s' → ∃ n, starN step ge n s t s'

def forever {genv state : Type}
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s : state) (T : traceinf) : Prop :=
  ∃ R : state → traceinf → Prop,
    R s T ∧
    ∀ s1 T1, R s1 T1 →
      ∃ t s2 T2, step ge s1 t s2 ∧ R s2 T2 ∧ T1 = Eappinf t T2

def forever_intro {genv state : Type}
    {step : genv → state → trace → state → Prop} {ge : genv}
    (s1 : state) (t : trace) (s2 : state) (T : traceinf)
    (hstep : step ge s1 t s2) (hforever : forever step ge s2 T) :
    forever step ge s1 (Eappinf t T) := by
  rcases hforever with ⟨R, htail, hclosed⟩
  let R' : state → traceinf → Prop :=
    fun s T' => (s = s1 ∧ T' = Eappinf t T) ∨ R s T'
  refine ⟨R', Or.inl ⟨rfl, rfl⟩, ?_⟩
  intro s T' h
  rcases h with h | h
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨t, s2, T, hstep, Or.inr htail, rfl⟩
  · rcases hclosed s T' h with ⟨u, s', U, hs, hR, hT⟩
    exact ⟨u, s', U, hs, Or.inr hR, hT⟩

def forever_silent {genv state : Type}
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s : state) : Prop :=
  ∃ R : state → Prop,
    R s ∧ ∀ s1, R s1 → ∃ s2, step ge s1 E0 s2 ∧ R s2

def forever_silent_intro {genv state : Type}
    {step : genv → state → trace → state → Prop} {ge : genv}
    (s1 s2 : state) (hstep : step ge s1 E0 s2)
    (hforever : forever_silent step ge s2) : forever_silent step ge s1 := by
  rcases hforever with ⟨R, htail, hclosed⟩
  let R' : state → Prop := fun s => s = s1 ∨ R s
  refine ⟨R', Or.inl rfl, ?_⟩
  intro s h
  rcases h with rfl | h
  · exact ⟨s2, hstep, Or.inr htail⟩
  · rcases hclosed s h with ⟨s', hs, hR⟩
    exact ⟨s', hs, Or.inr hR⟩

def forever_silent_N {genv state : Type}
    (step : genv → state → trace → state → Prop)
    {A : Type} (order : A → A → Prop) (ge : genv) (a : A) (s : state) : Prop :=
  ∃ R : A → state → Prop,
    R a s ∧
    ∀ a1 s1, R a1 s1 →
      (∃ s2 a2, star step ge s1 E0 s2 ∧ order a2 a1 ∧ R a2 s2) ∨
      (∃ s2 a2, plus step ge s1 E0 s2 ∧ R a2 s2)

def forever_silent_N_star {genv state A : Type}
    {step : genv → state → trace → state → Prop}
    {order : A → A → Prop} {ge : genv}
    (s1 s2 : state) (a1 a2 : A) (hstar : star step ge s1 E0 s2)
    (horder : order a2 a1) (hforever : forever_silent_N step order ge a2 s2) :
    forever_silent_N step order ge a1 s1 := by
  rcases hforever with ⟨R, htail, hclosed⟩
  let R' : A → state → Prop := fun a s => (a = a1 ∧ s = s1) ∨ R a s
  refine ⟨R', Or.inl ⟨rfl, rfl⟩, ?_⟩
  intro a s h
  rcases h with h | h
  · rcases h with ⟨rfl, rfl⟩
    exact Or.inl ⟨s2, a2, hstar, horder, Or.inr htail⟩
  · rcases hclosed a s h with h | h
    · rcases h with ⟨s', a', hs, ho, hR⟩
      exact Or.inl ⟨s', a', hs, ho, Or.inr hR⟩
    · rcases h with ⟨s', a', hs, hR⟩
      exact Or.inr ⟨s', a', hs, Or.inr hR⟩

def forever_silent_N_plus {genv state A : Type}
    {step : genv → state → trace → state → Prop}
    {order : A → A → Prop} {ge : genv}
    (s1 s2 : state) (a1 a2 : A) (hplus : plus step ge s1 E0 s2)
    (hforever : forever_silent_N step order ge a2 s2) :
    forever_silent_N step order ge a1 s1 := by
  rcases hforever with ⟨R, htail, hclosed⟩
  let R' : A → state → Prop := fun a s => (a = a1 ∧ s = s1) ∨ R a s
  refine ⟨R', Or.inl ⟨rfl, rfl⟩, ?_⟩
  intro a s h
  rcases h with h | h
  · rcases h with ⟨rfl, rfl⟩
    exact Or.inr ⟨s2, a2, hplus, Or.inr htail⟩
  · rcases hclosed a s h with h | h
    · rcases h with ⟨s', a', hs, ho, hR⟩
      exact Or.inl ⟨s', a', hs, ho, Or.inr hR⟩
    · rcases h with ⟨s', a', hs, hR⟩
      exact Or.inr ⟨s', a', hs, Or.inr hR⟩

def forever_silent_N_invStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (A : Type) (order : A → A → Prop),
    WellFounded order →
    ∀ (ge : genv) (a : A) (s : state),
      forever_silent_N step order ge a s →
      ∃ s' a', step ge s E0 s' ∧ forever_silent_N step order ge a' s'

def forever_silent_N_foreverStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (A : Type) (order : A → A → Prop),
    WellFounded order →
    ∀ (ge : genv) (a : A) (s : state),
      forever_silent_N step order ge a s → forever_silent step ge s

def forever_reactive {genv state : Type}
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s : state) (T : traceinf) : Prop :=
  ∃ R : state → traceinf → Prop,
    R s T ∧
    ∀ s1 T1, R s1 T1 →
      ∃ s2 t T2, star step ge s1 t s2 ∧ t ≠ E0 ∧
        R s2 T2 ∧ T1 = Eappinf t T2

def forever_reactive_intro {genv state : Type}
    {step : genv → state → trace → state → Prop} {ge : genv}
    (s1 s2 : state) (t : trace) (T : traceinf)
    (hstar : star step ge s1 t s2) (hnonempty : t ≠ E0)
    (hforever : forever_reactive step ge s2 T) :
    forever_reactive step ge s1 (Eappinf t T) := by
  rcases hforever with ⟨R, htail, hclosed⟩
  let R' : state → traceinf → Prop :=
    fun s T' => (s = s1 ∧ T' = Eappinf t T) ∨ R s T'
  refine ⟨R', Or.inl ⟨rfl, rfl⟩, ?_⟩
  intro s T' h
  rcases h with h | h
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨s2, t, T, hstar, hnonempty, Or.inr htail, rfl⟩
  · rcases hclosed s T' h with ⟨s', u, U, hs, hu, hR, hT⟩
    exact ⟨s', u, U, hs, hu, Or.inr hR, hT⟩

def star_forever_reactiveStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (ge : genv) (s1 : state) (t : trace) (s2 : state) (T : traceinf),
    star step ge s1 t s2 → forever_reactive step ge s2 T →
    forever_reactive step ge s1 (Eappinf t T)

inductive eventually {genv state : Type}
    (step : genv → state → trace → state → Prop)
    (final_state : state → int → Prop) (ge : genv) :
    Nat → state → (state → Prop) → Prop where
  | now (s : state) (P : state → Prop) (h : P s) :
      eventually step final_state ge 0 s P
  | later (n : Nat) (s : state) (P : state → Prop)
      (hfinal : ∀ r, ¬ final_state s r)
      (htrace : ∀ t s', step ge s t s' → t = E0)
      (hnext : ∀ t s', step ge s t s' →
        eventually step final_state ge n s' P) :
      eventually step final_state ge (n + 1) s P

def eventually_now {genv state : Type}
    {step : genv → state → trace → state → Prop}
    {final_state : state → int → Prop} {ge : genv}
    (s : state) (P : state → Prop) (h : P s) :
    eventually step final_state ge 0 s P :=
  .now s P h

def eventually_later {genv state : Type}
    {step : genv → state → trace → state → Prop}
    {final_state : state → int → Prop} {ge : genv}
    (n : Nat) (s : state) (P : state → Prop)
    (hfinal : ∀ r, ¬ final_state s r)
    (hlater : ∀ t s', step ge s t s' →
      t = E0 ∧ eventually step final_state ge n s' P) :
    eventually step final_state ge (n + 1) s P :=
  .later n s P hfinal
    (fun t s' h => (hlater t s' h).1)
    (fun t s' h => (hlater t s' h).2)

def eventually_transStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (final_state : state → int → Prop)
    (ge : genv) (n1 : Nat) (s1 : state) (P1 : state → Prop)
    (n2 : Nat) (P2 : state → Prop),
    eventually step final_state ge n1 s1 P1 →
    (∀ s2, P1 s2 → eventually step final_state ge n2 s2 P2) →
    eventually step final_state ge (n1 + n2) s1 P2

def eventually_impliesStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (final_state : state → int → Prop)
    (ge : genv) (n : Nat) (s : state) (P1 P2 : state → Prop),
    eventually step final_state ge n s P1 →
    (∀ s0, P1 s0 → P2 s0) → eventually step final_state ge n s P2

def eventually_and_invariantStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop)
    (final_state : state → int → Prop)
    (ge : genv) (Inv : state → Prop) (n : Nat) (s : state)
    (P : state → Prop),
    (∀ s0 t s', step ge s0 t s' → Inv s0 → Inv s') →
    eventually step final_state ge n s P → Inv s →
    eventually step final_state ge n s (fun s' => P s' ∧ Inv s')

/-! ## Transition semantics and simulations -/

structure semantics : Type 1 where
  state : Type
  genvtype : Type
  step : genvtype → state → trace → state → Prop
  initial_state : state → Prop
  final_state : state → int → Prop
  globalenv : genvtype
  symbolenv : Senv.t

export semantics (state genvtype step initial_state final_state globalenv symbolenv)

def Semantics {state funtype vartype : Type}
    (step : Genv.t funtype vartype → state → trace → state → Prop)
    (initial_state : state → Prop)
    (final_state : state → int → Prop)
    (globalenv : Genv.t funtype vartype) : semantics where
  state := state
  genvtype := Genv.t funtype vartype
  step := step
  initial_state := initial_state
  final_state := final_state
  globalenv := globalenv
  symbolenv := Genv.to_senv globalenv

structure fsim_properties (L1 L2 : semantics) (index : Type)
    (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop) : Prop where
  fsim_order_wf : WellFounded order
  fsim_match_initial_states :
    ∀ s1, initial_state L1 s1 →
      ∃ i s2, initial_state L2 s2 ∧ match_states i s1 s2
  fsim_match_final_states :
    ∀ i s1 s2 r, match_states i s1 s2 →
      final_state L1 s1 r → final_state L2 s2 r
  fsim_simulation :
    ∀ s1 t s1', step L1 (globalenv L1) s1 t s1' →
      ∀ i s2, match_states i s1 s2 →
        ∃ i' s2',
          (plus (step L2) (globalenv L2) s2 t s2' ∨
            (star (step L2) (globalenv L2) s2 t s2' ∧ order i' i)) ∧
          match_states i' s1' s2'
  fsim_public_preserved :
    ∀ id, Senv.public_symbol (symbolenv L2) id =
      Senv.public_symbol (symbolenv L1) id

export fsim_properties
  (fsim_order_wf fsim_match_initial_states fsim_match_final_states
    fsim_simulation fsim_public_preserved)

inductive forward_simulation (L1 L2 : semantics) : Prop where
  | Forward_simulation (index : Type) (order : index → index → Prop)
      (match_states : index → state L1 → state L2 → Prop)
      (props : fsim_properties L1 L2 index order match_states) :
      forward_simulation L1 L2

export forward_simulation (Forward_simulation)

def fsim_simulation'Statement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    fsim_properties L1 L2 index order match_states →
    ∀ (i : index) (s1 : state L1) (t : trace) (s1' : state L1),
      step L1 (globalenv L1) s1 t s1' →
      ∀ s2, match_states i s1 s2 →
        (∃ i' s2', plus (step L2) (globalenv L2) s2 t s2' ∧
          match_states i' s1' s2') ∨
        (∃ i', order i' i ∧ t = E0 ∧ match_states i' s1' s2)

def forward_simulation_star_wfStatement : Prop :=
  ∀ (L1 L2 : semantics),
    (∀ id, Senv.public_symbol (symbolenv L2) id =
      Senv.public_symbol (symbolenv L1) id) →
    ∀ (match_states : state L1 → state L2 → Prop),
      (∀ s1, initial_state L1 s1 →
        ∃ s2, initial_state L2 s2 ∧ match_states s1 s2) →
      (∀ s1 s2 r, match_states s1 s2 →
        final_state L1 s1 r → final_state L2 s2 r) →
      ∀ (order : state L1 → state L1 → Prop),
        WellFounded order →
        (∀ s1 t s1', step L1 (globalenv L1) s1 t s1' →
          ∀ s2, match_states s1 s2 →
            ∃ s2',
              (plus (step L2) (globalenv L2) s2 t s2' ∨
                (star (step L2) (globalenv L2) s2 t s2' ∧ order s1' s1)) ∧
              match_states s1' s2') →
        forward_simulation L1 L2

def forward_simulation_starStatement : Prop :=
  ∀ (L1 L2 : semantics),
    (∀ id, Senv.public_symbol (symbolenv L2) id =
      Senv.public_symbol (symbolenv L1) id) →
    ∀ (match_states : state L1 → state L2 → Prop),
      (∀ s1, initial_state L1 s1 →
        ∃ s2, initial_state L2 s2 ∧ match_states s1 s2) →
      (∀ s1 s2 r, match_states s1 s2 →
        final_state L1 s1 r → final_state L2 s2 r) →
      ∀ (measure : state L1 → Nat),
        (∀ s1 t s1', step L1 (globalenv L1) s1 t s1' →
          ∀ s2, match_states s1 s2 →
            (∃ s2', plus (step L2) (globalenv L2) s2 t s2' ∧
              match_states s1' s2') ∨
            (measure s1' < measure s1 ∧ t = E0 ∧ match_states s1' s2)) →
        forward_simulation L1 L2

def forward_simulation_plusStatement : Prop :=
  ∀ (L1 L2 : semantics),
    (∀ id, Senv.public_symbol (symbolenv L2) id =
      Senv.public_symbol (symbolenv L1) id) →
    ∀ (match_states : state L1 → state L2 → Prop),
      (∀ s1, initial_state L1 s1 →
        ∃ s2, initial_state L2 s2 ∧ match_states s1 s2) →
      (∀ s1 s2 r, match_states s1 s2 →
        final_state L1 s1 r → final_state L2 s2 r) →
      (∀ s1 t s1', step L1 (globalenv L1) s1 t s1' →
        ∀ s2, match_states s1 s2 →
          ∃ s2', plus (step L2) (globalenv L2) s2 t s2' ∧
            match_states s1' s2') →
      forward_simulation L1 L2

def forward_simulation_stepStatement : Prop :=
  ∀ (L1 L2 : semantics),
    (∀ id, Senv.public_symbol (symbolenv L2) id =
      Senv.public_symbol (symbolenv L1) id) →
    ∀ (match_states : state L1 → state L2 → Prop),
      (∀ s1, initial_state L1 s1 →
        ∃ s2, initial_state L2 s2 ∧ match_states s1 s2) →
      (∀ s1 s2 r, match_states s1 s2 →
        final_state L1 s1 r → final_state L2 s2 r) →
      (∀ s1 t s1', step L1 (globalenv L1) s1 t s1' →
        ∀ s2, match_states s1 s2 →
          ∃ s2', step L2 (globalenv L2) s2 t s2' ∧
            match_states s1' s2') →
      forward_simulation L1 L2

def forward_simulation_optStatement : Prop :=
  ∀ (L1 L2 : semantics),
    (∀ id, Senv.public_symbol (symbolenv L2) id =
      Senv.public_symbol (symbolenv L1) id) →
    ∀ (match_states : state L1 → state L2 → Prop),
      (∀ s1, initial_state L1 s1 →
        ∃ s2, initial_state L2 s2 ∧ match_states s1 s2) →
      (∀ s1 s2 r, match_states s1 s2 →
        final_state L1 s1 r → final_state L2 s2 r) →
      ∀ (measure : state L1 → Nat),
        (∀ s1 t s1', step L1 (globalenv L1) s1 t s1' →
          ∀ s2, match_states s1 s2 →
            (∃ s2', step L2 (globalenv L2) s2 t s2' ∧
              match_states s1' s2') ∨
            (measure s1' < measure s1 ∧ t = E0 ∧ match_states s1' s2)) →
        forward_simulation L1 L2

def forward_simulation_eventuallyStatement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    WellFounded order →
    (∀ s1, initial_state L1 s1 →
      ∃ i s2, initial_state L2 s2 ∧ match_states i s1 s2) →
    (∀ i s1 s2 r, match_states i s1 s2 →
      final_state L1 s1 r → final_state L2 s2 r) →
    (∀ s1 t s1', step L1 (globalenv L1) s1 t s1' →
      ∀ i s2, match_states i s1 s2 →
        ∃ n i' s2',
          (plus (step L2) (globalenv L2) s2 t s2' ∨
            (star (step L2) (globalenv L2) s2 t s2' ∧ order i' i)) ∧
          eventually (step L1) (final_state L1) (globalenv L1) n s1'
            (fun s1'' => match_states i' s1'' s2')) →
    (∀ id, Senv.public_symbol (symbolenv L2) id =
      Senv.public_symbol (symbolenv L1) id) →
    forward_simulation L1 L2

def forward_simulation_eventually_plusStatement : Prop :=
  ∀ (L1 L2 : semantics) (match_states : state L1 → state L2 → Prop),
    (∀ id, Senv.public_symbol (symbolenv L2) id =
      Senv.public_symbol (symbolenv L1) id) →
    (∀ s1, initial_state L1 s1 →
      ∃ s2, initial_state L2 s2 ∧ match_states s1 s2) →
    (∀ s1 s2 r, match_states s1 s2 →
      final_state L1 s1 r → final_state L2 s2 r) →
    (∀ s1 t s1', step L1 (globalenv L1) s1 t s1' →
      ∀ s2, match_states s1 s2 →
        ∃ n s2', plus (step L2) (globalenv L2) s2 t s2' ∧
          eventually (step L1) (final_state L1) (globalenv L1) n s1'
            (fun s1'' => match_states s1'' s2')) →
    forward_simulation L1 L2

def forward_simulation_eventually_star_wfStatement : Prop :=
  ∀ (L1 L2 : semantics) (match_states : state L1 → state L2 → Prop),
    (∀ id, Senv.public_symbol (symbolenv L2) id =
      Senv.public_symbol (symbolenv L1) id) →
    (∀ s1, initial_state L1 s1 →
      ∃ s2, initial_state L2 s2 ∧ match_states s1 s2) →
    (∀ s1 s2 r, match_states s1 s2 →
      final_state L1 s1 r → final_state L2 s2 r) →
    ∀ (order : state L1 → state L1 → Prop),
      WellFounded order →
      (∀ s1 t s1', step L1 (globalenv L1) s1 t s1' →
        ∀ s2, match_states s1 s2 →
          (∃ s2',
            (plus (step L2) (globalenv L2) s2 t s2' ∨
              (star (step L2) (globalenv L2) s2 t s2' ∧ order s1' s1)) ∧
            match_states s1' s2') ∨
          (∃ n s2', plus (step L2) (globalenv L2) s2 t s2' ∧
            eventually (step L1) (final_state L1) (globalenv L1) n s1'
              (fun s1'' => match_states s1'' s2'))) →
      forward_simulation L1 L2

def forward_simulation_eventually_starStatement : Prop :=
  ∀ (L1 L2 : semantics) (match_states : state L1 → state L2 → Prop),
    (∀ id, Senv.public_symbol (symbolenv L2) id =
      Senv.public_symbol (symbolenv L1) id) →
    (∀ s1, initial_state L1 s1 →
      ∃ s2, initial_state L2 s2 ∧ match_states s1 s2) →
    (∀ s1 s2 r, match_states s1 s2 →
      final_state L1 s1 r → final_state L2 s2 r) →
    ∀ (measure : state L1 → Nat),
      (∀ s1 t s1', step L1 (globalenv L1) s1 t s1' →
        ∀ s2, match_states s1 s2 →
          (∃ s2',
            (plus (step L2) (globalenv L2) s2 t s2' ∨
              (star (step L2) (globalenv L2) s2 t s2' ∧
                measure s1' < measure s1)) ∧
            match_states s1' s2') ∨
          (∃ n s2', plus (step L2) (globalenv L2) s2 t s2' ∧
            eventually (step L1) (final_state L1) (globalenv L1) n s1'
              (fun s1'' => match_states s1'' s2'))) →
      forward_simulation L1 L2

def simulation_starStatement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    fsim_properties L1 L2 index order match_states →
    ∀ (s1 : state L1) (t : trace) (s1' : state L1),
      star (step L1) (globalenv L1) s1 t s1' →
      ∀ i s2, match_states i s1 s2 →
        ∃ i' s2', star (step L2) (globalenv L2) s2 t s2' ∧
          match_states i' s1' s2'

def simulation_plusStatement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    fsim_properties L1 L2 index order match_states →
    ∀ (s1 : state L1) (t : trace) (s1' : state L1),
      plus (step L1) (globalenv L1) s1 t s1' →
      ∀ i s2, match_states i s1 s2 →
        (∃ i' s2', plus (step L2) (globalenv L2) s2 t s2' ∧
          match_states i' s1' s2') ∨
        (∃ i', Relation.TransGen order i' i ∧ t = E0 ∧
          match_states i' s1' s2)

def simulation_forever_silentStatement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    fsim_properties L1 L2 index order match_states →
    ∀ i s1 s2,
      forever_silent (step L1) (globalenv L1) s1 →
      match_states i s1 s2 → forever_silent (step L2) (globalenv L2) s2

def simulation_forever_reactiveStatement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    fsim_properties L1 L2 index order match_states →
    ∀ i s1 s2 T,
      forever_reactive (step L1) (globalenv L1) s1 T →
      match_states i s1 s2 → forever_reactive (step L2) (globalenv L2) s2 T

def compose_forward_simulationsStatement : Prop :=
  ∀ L1 L2 L3 : semantics,
    forward_simulation L1 L2 → forward_simulation L2 L3 →
    forward_simulation L1 L3

/-! ## Receptiveness and determinacy -/

def single_events (L : semantics) : Prop :=
  ∀ s t s', step L (globalenv L) s t s' → t.length ≤ 1

structure receptive (L : semantics) : Prop where
  sr_receptive :
    ∀ s t1 s1 t2, step L (globalenv L) s t1 s1 →
      match_traces (symbolenv L) t1 t2 →
      ∃ s2, step L (globalenv L) s t2 s2
  sr_traces : single_events L

export receptive (sr_receptive sr_traces)

structure determinate (L : semantics) : Prop where
  sd_determ :
    ∀ s t1 s1 t2 s2,
      step L (globalenv L) s t1 s1 → step L (globalenv L) s t2 s2 →
      match_traces (symbolenv L) t1 t2 ∧ (t1 = t2 → s1 = s2)
  sd_traces : single_events L
  sd_initial_determ :
    ∀ s1 s2, initial_state L s1 → initial_state L s2 → s1 = s2
  sd_final_nostep :
    ∀ s r, final_state L s r → nostep (step L) (globalenv L) s
  sd_final_determ :
    ∀ s r1 r2, final_state L s r1 → final_state L s r2 → r1 = r2

export determinate
  (sd_determ sd_traces sd_initial_determ sd_final_nostep sd_final_determ)

def sd_determ_1Statement : Prop :=
  ∀ L : semantics, determinate L →
    ∀ s t1 s1 t2 s2,
      step L (globalenv L) s t1 s1 → step L (globalenv L) s t2 s2 →
      match_traces (symbolenv L) t1 t2

def sd_determ_2Statement : Prop :=
  ∀ L : semantics, determinate L →
    ∀ s t s1 s2,
      step L (globalenv L) s t s1 → step L (globalenv L) s t s2 →
      s1 = s2

/-! ## Backward simulations -/

def safe (L : semantics) (s : state L) : Prop :=
  ∀ s', star (step L) (globalenv L) s E0 s' →
    (∃ r, final_state L s' r) ∨
    (∃ t s'', step L (globalenv L) s' t s'')

def star_safeStatement : Prop :=
  ∀ (L : semantics) (s s' : state L),
    star (step L) (globalenv L) s E0 s' → safe L s → safe L s'

structure bsim_properties (L1 L2 : semantics) (index : Type)
    (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop) : Prop where
  bsim_order_wf : WellFounded order
  bsim_initial_states_exist :
    ∀ s1, initial_state L1 s1 → ∃ s2, initial_state L2 s2
  bsim_match_initial_states :
    ∀ s1 s2, initial_state L1 s1 → initial_state L2 s2 →
      ∃ i s1', initial_state L1 s1' ∧ match_states i s1' s2
  bsim_match_final_states :
    ∀ i s1 s2 r, match_states i s1 s2 → safe L1 s1 →
      final_state L2 s2 r →
      ∃ s1', star (step L1) (globalenv L1) s1 E0 s1' ∧
        final_state L1 s1' r
  bsim_progress :
    ∀ i s1 s2, match_states i s1 s2 → safe L1 s1 →
      (∃ r, final_state L2 s2 r) ∨
      (∃ t s2', step L2 (globalenv L2) s2 t s2')
  bsim_simulation :
    ∀ s2 t s2', step L2 (globalenv L2) s2 t s2' →
      ∀ i s1, match_states i s1 s2 → safe L1 s1 →
        ∃ i' s1',
          (plus (step L1) (globalenv L1) s1 t s1' ∨
            (star (step L1) (globalenv L1) s1 t s1' ∧ order i' i)) ∧
          match_states i' s1' s2'
  bsim_public_preserved :
    ∀ id, Senv.public_symbol (symbolenv L2) id =
      Senv.public_symbol (symbolenv L1) id

export bsim_properties
  (bsim_order_wf bsim_initial_states_exist bsim_match_initial_states
    bsim_match_final_states bsim_progress bsim_simulation bsim_public_preserved)

inductive backward_simulation (L1 L2 : semantics) : Prop where
  | Backward_simulation (index : Type) (order : index → index → Prop)
      (match_states : index → state L1 → state L2 → Prop)
      (props : bsim_properties L1 L2 index order match_states) :
      backward_simulation L1 L2

export backward_simulation (Backward_simulation)

def bsim_simulation'Statement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    bsim_properties L1 L2 index order match_states →
    ∀ (i : index) (s2 : state L2) (t : trace) (s2' : state L2),
      step L2 (globalenv L2) s2 t s2' →
      ∀ s1, match_states i s1 s2 → safe L1 s1 →
        (∃ i' s1', plus (step L1) (globalenv L1) s1 t s1' ∧
          match_states i' s1' s2') ∨
        (∃ i', order i' i ∧ t = E0 ∧ match_states i' s1 s2')

def backward_simulation_plusStatement : Prop :=
  ∀ (L1 L2 : semantics),
    (∀ id, Senv.public_symbol (symbolenv L2) id =
      Senv.public_symbol (symbolenv L1) id) →
    ∀ (match_states : state L1 → state L2 → Prop),
      (∀ s1, initial_state L1 s1 → ∃ s2, initial_state L2 s2) →
      (∀ s1 s2, initial_state L1 s1 → initial_state L2 s2 →
        ∃ s1', initial_state L1 s1' ∧ match_states s1' s2) →
      (∀ s1 s2 r, match_states s1 s2 →
        final_state L2 s2 r → final_state L1 s1 r) →
      (∀ s1 s2, match_states s1 s2 → safe L1 s1 →
        (∃ r, final_state L2 s2 r) ∨
        (∃ t s2', step L2 (globalenv L2) s2 t s2')) →
      (∀ s2 t s2', step L2 (globalenv L2) s2 t s2' →
        ∀ s1, match_states s1 s2 → safe L1 s1 →
          ∃ s1', plus (step L1) (globalenv L1) s1 t s1' ∧
            match_states s1' s2') →
      backward_simulation L1 L2

def bsim_E0_starStatement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    bsim_properties L1 L2 index order match_states →
    ∀ s2 s2', star (step L2) (globalenv L2) s2 E0 s2' →
      ∀ i s1, match_states i s1 s2 → safe L1 s1 →
        ∃ i' s1', star (step L1) (globalenv L1) s1 E0 s1' ∧
          match_states i' s1' s2'

def bsim_safeStatement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    bsim_properties L1 L2 index order match_states →
    ∀ i s1 s2, match_states i s1 s2 → safe L1 s1 → safe L2 s2

def bsim_E0_plusStatement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    bsim_properties L1 L2 index order match_states →
    ∀ s2 t s2', plus (step L2) (globalenv L2) s2 t s2' → t = E0 →
      ∀ i s1, match_states i s1 s2 → safe L1 s1 →
        (∃ i' s1', plus (step L1) (globalenv L1) s1 E0 s1' ∧
          match_states i' s1' s2') ∨
        (∃ i', Relation.TransGen order i' i ∧ match_states i' s1 s2')

def star_non_E0_splitStatement : Prop :=
  ∀ (L2 : semantics) (s2 : state L2) (t : trace) (s2' : state L2),
    star (step L2) (globalenv L2) s2 t s2' → t.length = 1 →
    ∃ s2x s2y,
      star (step L2) (globalenv L2) s2 E0 s2x ∧
      step L2 (globalenv L2) s2x t s2y ∧
      star (step L2) (globalenv L2) s2y E0 s2'

/-! ## Composition of backward simulations -/

def bb_order {index index' : Type}
    (order : index → index → Prop) (order' : index' → index' → Prop) :
    index × index' → index × index' → Prop :=
  lex_ord (Relation.TransGen order) order'

inductive bb_match_states (L1 L2 L3 : semantics) {index : Type}
    (match_states : index → state L1 → state L2 → Prop)
    {index' : Type} (match_states' : index' → state L2 → state L3 → Prop) :
    index × index' → state L1 → state L3 → Prop where
  | bb_match_later (i1 : index) (i2 : index') (s1 : state L1) (s3 : state L3)
      (s2x s2y : state L2) (hmatch1 : match_states i1 s1 s2x)
      (hstar : star (step L2) (globalenv L2) s2x E0 s2y)
      (hmatch2 : match_states' i2 s2y s3) :
      bb_match_states L1 L2 L3 match_states match_states' (i1, i2) s1 s3

export bb_match_states (bb_match_later)

def bb_match_atStatement : Prop :=
  ∀ (L1 L2 L3 : semantics) (index : Type)
    (match_states : index → state L1 → state L2 → Prop)
    (index' : Type) (match_states' : index' → state L2 → state L3 → Prop)
    (i1 : index) (i2 : index') (s1 : state L1) (s3 : state L3) (s2 : state L2),
    match_states i1 s1 s2 → match_states' i2 s2 s3 →
    bb_match_states L1 L2 L3 match_states match_states' (i1, i2) s1 s3

def bb_simulation_baseStatement : Prop :=
  ∀ (L1 L2 L3 : semantics), single_events L3 →
    ∀ (index : Type) (order : index → index → Prop)
      (match_states : index → state L1 → state L2 → Prop),
      bsim_properties L1 L2 index order match_states →
      ∀ (index' : Type) (order' : index' → index' → Prop)
        (match_states' : index' → state L2 → state L3 → Prop),
        bsim_properties L2 L3 index' order' match_states' →
        ∀ s3 t s3', step L3 (globalenv L3) s3 t s3' →
          ∀ i1 s1 i2 s2,
            match_states i1 s1 s2 → match_states' i2 s2 s3 → safe L1 s1 →
            ∃ i' s1',
              (plus (step L1) (globalenv L1) s1 t s1' ∨
                (star (step L1) (globalenv L1) s1 t s1' ∧
                  bb_order order order' i' (i1, i2))) ∧
              bb_match_states L1 L2 L3 match_states match_states' i' s1' s3'

def bb_simulationStatement : Prop :=
  ∀ (L1 L2 L3 : semantics), single_events L3 →
    ∀ (index : Type) (order : index → index → Prop)
      (match_states : index → state L1 → state L2 → Prop),
      bsim_properties L1 L2 index order match_states →
      ∀ (index' : Type) (order' : index' → index' → Prop)
        (match_states' : index' → state L2 → state L3 → Prop),
        bsim_properties L2 L3 index' order' match_states' →
        ∀ s3 t s3', step L3 (globalenv L3) s3 t s3' →
          ∀ i s1,
            bb_match_states L1 L2 L3 match_states match_states' i s1 s3 →
            safe L1 s1 →
            ∃ i' s1',
              (plus (step L1) (globalenv L1) s1 t s1' ∨
                (star (step L1) (globalenv L1) s1 t s1' ∧
                  bb_order order order' i' i)) ∧
              bb_match_states L1 L2 L3 match_states match_states' i' s1' s3'

def compose_backward_simulationStatement : Prop :=
  ∀ L1 L2 L3 : semantics,
    single_events L3 → backward_simulation L1 L2 →
    backward_simulation L2 L3 → backward_simulation L1 L3

/-! ## Forward-to-backward conversion -/

inductive f2b_transitions (L1 L2 : semantics) {index : Type}
    (match_states : index → state L1 → state L2 → Prop) :
    state L1 → state L2 → Prop where
  | f2b_trans_final (s1 : state L1) (s2 : state L2) (s1' : state L1) (r : int)
      (hstar : star (step L1) (globalenv L1) s1 E0 s1')
      (hfinal1 : final_state L1 s1' r) (hfinal2 : final_state L2 s2 r) :
      f2b_transitions L1 L2 match_states s1 s2
  | f2b_trans_step (s1 : state L1) (s2 : state L2) (s1' : state L1)
      (t : trace) (s1'' : state L1) (s2' : state L2) (i' i'' : index)
      (hstar : star (step L1) (globalenv L1) s1 E0 s1')
      (hstep : step L1 (globalenv L1) s1' t s1'')
      (hplus : plus (step L2) (globalenv L2) s2 t s2')
      (hmatch1 : match_states i' s1' s2)
      (hmatch2 : match_states i'' s1'' s2') :
      f2b_transitions L1 L2 match_states s1 s2

export f2b_transitions (f2b_trans_final f2b_trans_step)

def f2b_progressStatement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    fsim_properties L1 L2 index order match_states →
    ∀ i s1 s2, match_states i s1 s2 → safe L1 s1 →
      f2b_transitions L1 L2 match_states s1 s2

def fsim_simulation_not_E0Statement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    fsim_properties L1 L2 index order match_states →
    ∀ s1 t s1', step L1 (globalenv L1) s1 t s1' → t ≠ E0 →
      ∀ i s2, match_states i s1 s2 →
        ∃ i' s2', plus (step L2) (globalenv L2) s2 t s2' ∧
          match_states i' s1' s2'

def silent_or_not_silentStatement : Prop :=
  ∀ t : trace, t = E0 ∨ t ≠ E0

def not_silent_lengthStatement : Prop :=
  ∀ t1 t2 : trace, (Eapp t1 t2).length ≤ 1 → t1 = E0 ∨ t2 = E0

def f2b_determinacy_invStatement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    fsim_properties L1 L2 index order match_states → determinate L2 →
    ∀ s2 t' s2' t'' s2'',
      step L2 (globalenv L2) s2 t' s2' →
      step L2 (globalenv L2) s2 t'' s2'' →
      (t' = E0 ∧ t'' = E0 ∧ s2' = s2'') ∨
      (t' ≠ E0 ∧ t'' ≠ E0 ∧ match_traces (symbolenv L1) t' t'')

def f2b_determinacy_starStatement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    fsim_properties L1 L2 index order match_states → determinate L2 →
    ∀ s s1, star (step L2) (globalenv L2) s E0 s1 →
      ∀ t s2 s3, step L2 (globalenv L2) s1 t s2 → t ≠ E0 →
        star (step L2) (globalenv L2) s t s3 →
        star (step L2) (globalenv L2) s1 t s3

inductive f2bIndex : Type where
  | F2BI_before (n : Nat)
  | F2BI_after (n : Nat)

export f2bIndex (F2BI_before F2BI_after)

inductive f2b_order : f2bIndex → f2bIndex → Prop where
  | before (n n' : Nat) (h : n' < n) :
      f2b_order (F2BI_before n') (F2BI_before n)
  | after (n n' : Nat) (h : n' < n) :
      f2b_order (F2BI_after n') (F2BI_after n)
  | switch (n n' : Nat) :
      f2b_order (F2BI_before n') (F2BI_after n)

def wf_f2b_orderStatement : Prop :=
  WellFounded f2b_order

inductive f2b_match_states (L1 L2 : semantics) {index : Type}
    (match_states : index → state L1 → state L2 → Prop) :
    f2bIndex → state L1 → state L2 → Prop where
  | at (i : index) (s1 : state L1) (s2 : state L2)
      (hmatch : match_states i s1 s2) :
      f2b_match_states L1 L2 match_states (F2BI_after 0) s1 s2
  | before (s1 : state L1) (t : trace) (s1' : state L1)
      (s2b s2 : state L2) (n : Nat) (s2a : state L2) (i : index)
      (hstep : step L1 (globalenv L1) s1 t s1') (hnonempty : t ≠ E0)
      (hstar : star (step L2) (globalenv L2) s2b E0 s2)
      (hstarN : starN (step L2) (globalenv L2) n s2 t s2a)
      (hmatch : match_states i s1 s2b) :
      f2b_match_states L1 L2 match_states (F2BI_before n) s1 s2
  | after (n : Nat) (s2 s2a : state L2) (s1 : state L1) (i : index)
      (hstarN : starN (step L2) (globalenv L2) (n + 1) s2 E0 s2a)
      (hmatch : match_states i s1 s2a) :
      f2b_match_states L1 L2 match_states (F2BI_after (n + 1)) s1 s2

def f2b_match_after'Statement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type)
    (match_states : index → state L1 → state L2 → Prop)
    (n : Nat) (s2 s2a : state L2) (s1 : state L1) (i : index),
    starN (step L2) (globalenv L2) n s2 E0 s2a →
    match_states i s1 s2a →
    f2b_match_states L1 L2 match_states (F2BI_after n) s1 s2

def f2b_simulation_stepStatement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    fsim_properties L1 L2 index order match_states → receptive L1 →
    determinate L2 →
    ∀ s2 t s2', step L2 (globalenv L2) s2 t s2' →
      ∀ i s1, f2b_match_states L1 L2 match_states i s1 s2 → safe L1 s1 →
        ∃ i' s1',
          (plus (step L1) (globalenv L1) s1 t s1' ∨
            (star (step L1) (globalenv L1) s1 t s1' ∧ f2b_order i' i)) ∧
          f2b_match_states L1 L2 match_states i' s1' s2'

def forward_to_backward_simulationStatement : Prop :=
  ∀ L1 L2 : semantics,
    forward_simulation L1 L2 → receptive L1 → determinate L2 →
    backward_simulation L1 L2

/-! ## Atomic single-event semantics -/

def well_behaved_traces (L : semantics) : Prop :=
  ∀ s t s', step L (globalenv L) s t s' →
    match t with
    | [] => True
    | _ :: t' => output_trace t'

inductive atomic_step (L : semantics) (ge : genvtype L) :
    trace × state L → trace → trace × state L → Prop where
  | atomic_step_silent (s s' : state L)
      (hstep : step L (globalenv L) s E0 s') :
      atomic_step L ge (E0, s) E0 (E0, s')
  | atomic_step_start (s : state L) (ev : event) (t : trace) (s' : state L)
      (hstep : step L (globalenv L) s (ev :: t) s') :
      atomic_step L ge (E0, s) [ev] (t, s')
  | atomic_step_continue (ev : event) (t : trace) (s : state L)
      (hout : output_trace (ev :: t)) :
      atomic_step L ge (ev :: t, s) [ev] (t, s)

export atomic_step (atomic_step_silent atomic_step_start atomic_step_continue)

def atomic (L : semantics) : semantics where
  state := trace × state L
  genvtype := genvtype L
  step := atomic_step L
  initial_state := fun s => initial_state L s.2 ∧ s.1 = E0
  final_state := fun s r => final_state L s.2 r ∧ s.1 = E0
  globalenv := globalenv L
  symbolenv := symbolenv L

inductive ffs_match (L1 L2 : semantics) {index : Type}
    (match_states : index → state L1 → state L2 → Prop) :
    index → trace × state L1 → state L2 → Prop where
  | at (i : index) (s1 : state L1) (s2 : state L2)
      (hmatch : match_states i s1 s2) : ffs_match L1 L2 match_states i (E0, s1) s2
  | buffer (i : index) (ev : event) (t : trace)
      (s1 : state L1) (s2 s2' : state L2)
      (hstar : star (step L2) (globalenv L2) s2 (ev :: t) s2')
      (hmatch : match_states i s1 s2') :
      ffs_match L1 L2 match_states i (ev :: t, s1) s2

def star_non_E0_split'Statement : Prop :=
  ∀ L2 : semantics, single_events L2 →
    ∀ s2 t s2', star (step L2) (globalenv L2) s2 t s2' →
      match t with
      | [] => True
      | ev :: t' =>
          ∃ s2x, plus (step L2) (globalenv L2) s2 [ev] s2x ∧
            star (step L2) (globalenv L2) s2x t' s2'

def ffs_simulationStatement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    fsim_properties L1 L2 index order match_states → single_events L2 →
    ∀ (s1 : state (atomic L1)) (t : trace) (s1' : state (atomic L1)),
      step (atomic L1) (globalenv (atomic L1)) s1 t s1' →
      ∀ i s2, ffs_match L1 L2 match_states i s1 s2 →
        ∃ i' s2',
          (plus (step L2) (globalenv L2) s2 t s2' ∨
            (star (step L2) (globalenv L2) s2 t s2' ∧ order i' i)) ∧
          ffs_match L1 L2 match_states i' s1' s2'

def factor_forward_simulationStatement : Prop :=
  ∀ L1 L2 : semantics,
    forward_simulation L1 L2 → single_events L2 →
    forward_simulation (atomic L1) L2

inductive fbs_match (L1 L2 : semantics) {index : Type}
    (match_states : index → state L1 → state L2 → Prop) :
    index → state L1 → trace × state L2 → Prop where
  | intro (i : index) (s1 : state L1) (t : trace)
      (s2 : state L2) (s1' : state L1)
      (hstar : star (step L1) (globalenv L1) s1 t s1')
      (hmatch : match_states i s1' s2)
      (htrace : t = E0 ∨ output_trace t) :
      fbs_match L1 L2 match_states i s1 (t, s2)

def fbs_simulationStatement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    bsim_properties L1 L2 index order match_states → single_events L1 →
    well_behaved_traces L2 →
    ∀ (s2 : state (atomic L2)) (t : trace) (s2' : state (atomic L2)),
      step (atomic L2) (globalenv (atomic L2)) s2 t s2' →
      ∀ i s1, fbs_match L1 L2 match_states i s1 s2 → safe L1 s1 →
        ∃ i' s1',
          (plus (step L1) (globalenv L1) s1 t s1' ∨
            (star (step L1) (globalenv L1) s1 t s1' ∧ order i' i)) ∧
          fbs_match L1 L2 match_states i' s1' s2'

def fbs_progressStatement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    bsim_properties L1 L2 index order match_states →
    ∀ i s1 (s2 : trace × state L2),
      fbs_match L1 L2 match_states i s1 s2 → safe L1 s1 →
      (∃ r, final_state (atomic L2) s2 r) ∨
      (∃ t s2', step (atomic L2) (globalenv (atomic L2)) s2 t s2')

def factor_backward_simulationStatement : Prop :=
  ∀ L1 L2 : semantics,
    backward_simulation L1 L2 → single_events L1 →
    well_behaved_traces L2 → backward_simulation L1 (atomic L2)

structure strongly_receptive (L : semantics) : Prop where
  ssr_receptive :
    ∀ s ev1 t1 s1 ev2,
      step L (globalenv L) s (ev1 :: t1) s1 →
      match_traces (symbolenv L) [ev1] [ev2] →
      ∃ s2 t2, step L (globalenv L) s (ev2 :: t2) s2
  ssr_well_behaved : well_behaved_traces L

export strongly_receptive (ssr_receptive ssr_well_behaved)

def atomic_receptiveStatement : Prop :=
  ∀ L : semantics, strongly_receptive L → receptive (atomic L)

/-! ## Big-step semantics -/

structure bigstep_semantics : Type where
  bigstep_terminates : trace → int → Prop
  bigstep_diverges : traceinf → Prop

export bigstep_semantics (bigstep_terminates bigstep_diverges)

structure bigstep_sound (B : bigstep_semantics) (L : semantics) : Prop where
  bigstep_terminates_sound :
    ∀ t r, bigstep_terminates B t r →
      ∃ s1 s2, initial_state L s1 ∧
        star (step L) (globalenv L) s1 t s2 ∧ final_state L s2 r
  bigstep_diverges_sound :
    ∀ T, bigstep_diverges B T →
      ∃ s1, initial_state L s1 ∧ forever (step L) (globalenv L) s1 T

export bigstep_sound (bigstep_terminates_sound bigstep_diverges_sound)

end CompCert4Lean.Common.Smallstep
