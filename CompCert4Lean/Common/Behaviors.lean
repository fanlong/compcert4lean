import CompCert4Lean.Common.Smallstep

/-!
# Whole-program behaviors

Definition-bearing translation of CompCert's `common/Behaviors.v`.  Proofs
assigned to later proof migration are represented by transparent proposition
descriptors with the source quantifier order.
-/

namespace CompCert4Lean.Common.Behaviors

open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Lib.Integers

private abbrev Step (L : semantics) := step L (globalenv L)
private abbrev Star (L : semantics) := star (step L) (globalenv L)
private abbrev Plus (L : semantics) := plus (step L) (globalenv L)
private abbrev Nostep (L : semantics) := nostep (step L) (globalenv L)
private abbrev Forever (L : semantics) := forever (step L) (globalenv L)
private abbrev ForeverSilent (L : semantics) :=
  forever_silent (step L) (globalenv L)
private abbrev ForeverReactive (L : semantics) :=
  forever_reactive (step L) (globalenv L)

/-! ## Behaviors for program executions -/

inductive program_behavior : Type where
  | Terminates : trace → int → program_behavior
  | Diverges : trace → program_behavior
  | Reacts : traceinf → program_behavior
  | Goes_wrong : trace → program_behavior

export program_behavior (Terminates Diverges Reacts Goes_wrong)

def not_wrong (beh : program_behavior) : Prop :=
  match beh with
  | .Terminates _ _ => True
  | .Diverges _ => True
  | .Reacts _ => True
  | .Goes_wrong _ => False

def behavior_app (t : trace) (beh : program_behavior) : program_behavior :=
  match beh with
  | .Terminates t1 r => Terminates (Eapp t t1) r
  | .Diverges t1 => Diverges (Eapp t t1)
  | .Reacts T => Reacts (Eappinf t T)
  | .Goes_wrong t1 => Goes_wrong (Eapp t t1)

def behavior_app_assocStatement : Prop :=
  ∀ (t1 t2 : trace) (beh : program_behavior),
    behavior_app (Eapp t1 t2) beh =
      behavior_app t1 (behavior_app t2 beh)

def behavior_app_E0Statement : Prop :=
  ∀ beh : program_behavior, behavior_app E0 beh = beh

def behavior_prefix (t : trace) (beh : program_behavior) : Prop :=
  ∃ beh', beh = behavior_app t beh'

def behavior_improves (beh1 beh2 : program_behavior) : Prop :=
  beh1 = beh2 ∨
    ∃ t, beh1 = Goes_wrong t ∧ behavior_prefix t beh2

def behavior_improves_reflStatement : Prop :=
  ∀ beh : program_behavior, behavior_improves beh beh

def behavior_improves_transStatement : Prop :=
  ∀ beh1 beh2 beh3 : program_behavior,
    behavior_improves beh1 beh2 →
    behavior_improves beh2 beh3 →
    behavior_improves beh1 beh3

def behavior_improves_botStatement : Prop :=
  ∀ beh : program_behavior, behavior_improves (Goes_wrong E0) beh

def behavior_improves_appStatement : Prop :=
  ∀ (t : trace) (beh1 beh2 : program_behavior),
    behavior_improves beh1 beh2 →
    behavior_improves (behavior_app t beh1) (behavior_app t beh2)

/-! ## Associating behaviors to programs -/

inductive state_behaves (L : semantics) (s : state L) :
    program_behavior → Prop where
  | state_terminates (t : trace) (s' : state L) (r : int)
      (hstar : Star L s t s')
      (hfinal : final_state L s' r) :
      state_behaves L s (Terminates t r)
  | state_diverges (t : trace) (s' : state L)
      (hstar : Star L s t s')
      (hforever : ForeverSilent L s') :
      state_behaves L s (Diverges t)
  | state_reacts (T : traceinf)
      (hforever : ForeverReactive L s T) :
      state_behaves L s (Reacts T)
  | state_goes_wrong (t : trace) (s' : state L)
      (hstar : Star L s t s')
      (hnostep : Nostep L s')
      (hnofinal : ∀ r, ¬ final_state L s' r) :
      state_behaves L s (Goes_wrong t)

abbrev state_terminates (L : semantics) {s : state L}
    {t : trace} {s' : state L} (r : int)
    (hstar : Star L s t s') (hfinal : final_state L s' r) :
    state_behaves L s (Terminates t r) :=
  state_behaves.state_terminates t s' r hstar hfinal

abbrev state_diverges (L : semantics) {s : state L}
    {t : trace} {s' : state L} (hstar : Star L s t s')
    (hforever : ForeverSilent L s') : state_behaves L s (Diverges t) :=
  state_behaves.state_diverges t s' hstar hforever

abbrev state_reacts (L : semantics) {s : state L} {T : traceinf}
    (hforever : ForeverReactive L s T) : state_behaves L s (Reacts T) :=
  state_behaves.state_reacts T hforever

abbrev state_goes_wrong (L : semantics) {s : state L}
    {t : trace} {s' : state L} (hstar : Star L s t s')
    (hnostep : Nostep L s') (hnofinal : ∀ r, ¬ final_state L s' r) :
    state_behaves L s (Goes_wrong t) :=
  state_behaves.state_goes_wrong t s' hstar hnostep hnofinal

inductive program_behaves (L : semantics) : program_behavior → Prop where
  | program_runs (s : state L) (beh : program_behavior)
      (hinit : initial_state L s) (hbehaves : state_behaves L s beh) :
      program_behaves L beh
  | program_goes_initially_wrong
      (hnoinit : ∀ s, ¬ initial_state L s) :
      program_behaves L (Goes_wrong E0)

abbrev program_runs {L : semantics} {s : state L} {beh : program_behavior}
    (hinit : initial_state L s) (hbehaves : state_behaves L s beh) :
    program_behaves L beh :=
  program_behaves.program_runs s beh hinit hbehaves

abbrev program_goes_initially_wrong (L : semantics)
    (hnoinit : ∀ s, ¬ initial_state L s) :
    program_behaves L (Goes_wrong E0) :=
  program_behaves.program_goes_initially_wrong hnoinit

def state_behaves_appStatement : Prop :=
  ∀ (L : semantics) (s1 : state L) (t : trace) (s2 : state L)
    (beh : program_behavior),
    Star L s1 t s2 → state_behaves L s2 beh →
    state_behaves L s1 (behavior_app t beh)

/-! ## Existence of behaviors -/

private theorem eappNilLeft (t : trace) : Eapp E0 t = t := by
  rfl

private theorem eappAssoc (t1 t2 t3 : trace) :
    Eapp (Eapp t1 t2) t3 = Eapp t1 (Eapp t2 t3) := by
  induction t1 with
  | nil => rfl
  | cons ev t ih =>
      change ev :: Eapp (Eapp t t2) t3 = ev :: Eapp t (Eapp t2 t3)
      exact congrArg (List.cons ev) ih

private theorem starAppend {genv state : Type}
    {step : genv → state → trace → state → Prop} {ge : genv}
    {s1 s2 s3 : state} {t1 t2 : trace}
    (h12 : star step ge s1 t1 s2) (h23 : star step ge s2 t2 s3) :
    star step ge s1 (Eapp t1 t2) s3 := by
  induction h12 generalizing s3 t2 with
  | star_refl s =>
      rw [eappNilLeft]
      exact h23
  | star_step s1 u s2 v s3 t hstep hstar htrace ih =>
      apply star_step
      · exact hstep
      · exact ih h23
      · rw [htrace]
        exact eappAssoc u v t2

def reacts'Statement : Type 1 :=
  ∀ (L : semantics) (s0 : state L),
    (∀ (s1 : state L) (t1 : trace),
      Star L s0 t1 s1 →
      ∃ (s2 : state L) (t2 : trace), Star L s1 t2 s2 ∧ t2 ≠ E0) →
    ∀ (s1 : state L) (t1 : trace),
      Star L s0 t1 s1 →
      Σ s2 : state L, {t2 : trace // Star L s1 t2 s2 ∧ t2 ≠ E0}

noncomputable def reacts'
    (L : semantics) {s0 : state L}
    (reacts : ∀ (s1 : state L) (t1 : trace),
      Star L s0 t1 s1 →
      ∃ (s2 : state L) (t2 : trace), Star L s1 t2 s2 ∧ t2 ≠ E0)
    {s1 : state L} {t1 : trace} (ST : Star L s0 t1 s1) :
    Σ s2 : state L, {t2 : trace // Star L s1 t2 s2 ∧ t2 ≠ E0} := by
  classical
  let s2 := Classical.choose (reacts s1 t1 ST)
  have hs2 : ∃ t2, Star L s1 t2 s2 ∧ t2 ≠ E0 :=
    Classical.choose_spec (reacts s1 t1 ST)
  let t2 := Classical.choose hs2
  have ht2 : Star L s1 t2 s2 ∧ t2 ≠ E0 :=
    Classical.choose_spec hs2
  exact ⟨s2, ⟨t2, ht2⟩⟩

private structure ReactiveCursor (L : semantics) (s0 : state L) where
  current : state L
  history : trace
  reachable : Star L s0 history current

private noncomputable def nextReactiveCursor
    (L : semantics) (s0 : state L)
    (reacts : ∀ (s1 : state L) (t1 : trace),
      Star L s0 t1 s1 →
      ∃ (s2 : state L) (t2 : trace), Star L s1 t2 s2 ∧ t2 ≠ E0)
    (cursor : ReactiveCursor L s0) : ReactiveCursor L s0 :=
  let selected := reacts' L reacts cursor.reachable
  { current := selected.1
    history := Eapp cursor.history selected.2.1
    reachable := starAppend cursor.reachable selected.2.2.1 }

private noncomputable def reactiveCursorAt
    (L : semantics) (s0 : state L)
    (reacts : ∀ (s1 : state L) (t1 : trace),
      Star L s0 t1 s1 →
      ∃ (s2 : state L) (t2 : trace), Star L s1 t2 s2 ∧ t2 ≠ E0)
    (initial : ReactiveCursor L s0) : Nat → ReactiveCursor L s0
  | 0 => initial
  | n + 1 => nextReactiveCursor L s0 reacts
      (reactiveCursorAt L s0 reacts initial n)

private noncomputable def reactiveChunkAt
    (L : semantics) (s0 : state L)
    (reacts : ∀ (s1 : state L) (t1 : trace),
      Star L s0 t1 s1 →
      ∃ (s2 : state L) (t2 : trace), Star L s1 t2 s2 ∧ t2 ≠ E0)
    (initial : ReactiveCursor L s0) (n : Nat) : {t : trace // t ≠ E0} :=
  let cursor := reactiveCursorAt L s0 reacts initial n
  let selected := reacts' L reacts cursor.reachable
  ⟨selected.2.1, selected.2.2.2⟩

noncomputable def build_traceinf'
    (L : semantics) {s0 : state L}
    (reacts : ∀ (s1 : state L) (t1 : trace),
      Star L s0 t1 s1 →
      ∃ (s2 : state L) (t2 : trace), Star L s1 t2 s2 ∧ t2 ≠ E0)
    {s1 : state L} {t1 : trace} (ST : Star L s0 t1 s1) : traceinf' :=
  { chunk := fun n =>
      (reactiveChunkAt L s0 reacts ⟨s1, t1, ST⟩ n).1
    nonempty := fun n =>
      (reactiveChunkAt L s0 reacts ⟨s1, t1, ST⟩ n).2 }

def reacts_forever_reactive_recStatement : Prop :=
  ∀ (L : semantics) (s0 : state L)
    (reacts : ∀ (s1 : state L) (t1 : trace),
      Star L s0 t1 s1 →
      ∃ (s2 : state L) (t2 : trace), Star L s1 t2 s2 ∧ t2 ≠ E0)
    (s1 : state L) (t1 : trace) (ST : Star L s0 t1 s1),
    ForeverReactive L s1
      (traceinf_of_traceinf'
        (build_traceinf' L (s0 := s0) reacts (s1 := s1) (t1 := t1) ST))

def reacts_forever_reactiveStatement : Prop :=
  ∀ (L : semantics) (s0 : state L),
    (∀ (s1 : state L) (t1 : trace),
      Star L s0 t1 s1 →
      ∃ (s2 : state L) (t2 : trace), Star L s1 t2 s2 ∧ t2 ≠ E0) →
    ∃ T : traceinf, ForeverReactive L s0 T

def diverges_forever_silentStatement : Prop :=
  ∀ (L : semantics) (s0 : state L),
    (∀ (s1 : state L) (t1 : trace),
      Star L s0 t1 s1 → ∃ s2 : state L, Step L s1 E0 s2) →
    ForeverSilent L s0

def state_behaves_existsStatement : Prop :=
  ∀ (L : semantics) (s : state L),
    ∃ beh : program_behavior, state_behaves L s beh

def program_behaves_existsStatement : Prop :=
  ∀ L : semantics, ∃ beh : program_behavior, program_behaves L beh

/-! ## Forward simulations and program behaviors -/

def forward_simulation_state_behavesStatement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    fsim_properties L1 L2 index order match_states →
    ∀ (i : index) (s1 : state L1) (s2 : state L2)
      (beh1 : program_behavior),
      match_states i s1 s2 → state_behaves L1 s1 beh1 →
      ∃ beh2 : program_behavior,
        state_behaves L2 s2 beh2 ∧ behavior_improves beh1 beh2

def forward_simulation_behavior_improvesStatement : Prop :=
  ∀ L1 L2 : semantics,
    forward_simulation L1 L2 →
    ∀ beh1 : program_behavior,
      program_behaves L1 beh1 →
      ∃ beh2 : program_behavior,
        program_behaves L2 beh2 ∧ behavior_improves beh1 beh2

def forward_simulation_same_safe_behaviorStatement : Prop :=
  ∀ L1 L2 : semantics,
    forward_simulation L1 L2 →
    ∀ beh : program_behavior,
      program_behaves L1 beh → not_wrong beh → program_behaves L2 beh

/-! ## Backward simulations and program behaviors -/

def safe_along_behavior (L1 : semantics) (s : state L1)
    (b : program_behavior) : Prop :=
  ∀ (t1 : trace) (s' : state L1) (b2 : program_behavior),
    Star L1 s t1 s' → b = behavior_app t1 b2 →
    (∃ r, final_state L1 s' r) ∨
      (∃ (t2 : trace) (s'' : state L1), Step L1 s' t2 s'')

def safe_along_safeStatement : Prop :=
  ∀ (L1 : semantics) (s : state L1) (b : program_behavior),
    safe_along_behavior L1 s b → safe L1 s

def star_safe_alongStatement : Prop :=
  ∀ (L1 : semantics) (s : state L1) (b : program_behavior)
    (t1 : trace) (s' : state L1) (b2 : program_behavior),
    safe_along_behavior L1 s b → Star L1 s t1 s' →
    b = behavior_app t1 b2 → safe_along_behavior L1 s' b2

def not_safe_along_behaviorStatement : Prop :=
  ∀ (L1 : semantics) (s : state L1) (b : program_behavior),
    ¬ safe_along_behavior L1 s b →
    ∃ (t : trace) (s' : state L1),
      behavior_prefix t b ∧ Star L1 s t s' ∧ Nostep L1 s' ∧
        (∀ r, ¬ final_state L1 s' r)

def backward_simulation_starStatement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    bsim_properties L1 L2 index order match_states →
    ∀ (s2 : state L2) (t : trace) (s2' : state L2),
      Star L2 s2 t s2' →
      ∀ (i : index) (s1 : state L1) (b : program_behavior),
        match_states i s1 s2 →
        safe_along_behavior L1 s1 (behavior_app t b) →
        ∃ (i' : index) (s1' : state L1),
          Star L1 s1 t s1' ∧ match_states i' s1' s2'

def backward_simulation_forever_silentStatement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    bsim_properties L1 L2 index order match_states →
    ∀ (i : index) (s1 : state L1) (s2 : state L2),
      ForeverSilent L2 s2 → match_states i s1 s2 → safe L1 s1 →
      ForeverSilent L1 s1

def backward_simulation_forever_reactiveStatement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    bsim_properties L1 L2 index order match_states →
    ∀ (i : index) (s1 : state L1) (s2 : state L2) (T : traceinf),
      ForeverReactive L2 s2 T → match_states i s1 s2 →
      safe_along_behavior L1 s1 (Reacts T) → ForeverReactive L1 s1 T

def backward_simulation_state_behavesStatement : Prop :=
  ∀ (L1 L2 : semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop),
    bsim_properties L1 L2 index order match_states →
    ∀ (i : index) (s1 : state L1) (s2 : state L2)
      (beh2 : program_behavior),
      match_states i s1 s2 → state_behaves L2 s2 beh2 →
      ∃ beh1 : program_behavior,
        state_behaves L1 s1 beh1 ∧ behavior_improves beh1 beh2

def backward_simulation_behavior_improvesStatement : Prop :=
  ∀ L1 L2 : semantics,
    backward_simulation L1 L2 →
    ∀ beh2 : program_behavior,
      program_behaves L2 beh2 →
      ∃ beh1 : program_behavior,
        program_behaves L1 beh1 ∧ behavior_improves beh1 beh2

def backward_simulation_same_safe_behaviorStatement : Prop :=
  ∀ L1 L2 : semantics,
    backward_simulation L1 L2 →
    (∀ beh : program_behavior, program_behaves L1 beh → not_wrong beh) →
    ∀ beh : program_behavior,
      program_behaves L2 beh → program_behaves L1 beh

/-! ## Program behaviors for the atomic construction -/

def atomic_finishStatement : Prop :=
  ∀ (L : semantics) (s : state L) (t : trace),
    output_trace t → Star (atomic L) (t, s) t (E0, s)

def step_atomic_plusStatement : Prop :=
  ∀ L : semantics,
    well_behaved_traces L →
    ∀ (s1 : state L) (t : trace) (s2 : state L),
      Step L s1 t s2 → Plus (atomic L) (E0, s1) t (E0, s2)

def star_atomic_starStatement : Prop :=
  ∀ L : semantics,
    well_behaved_traces L →
    ∀ (s1 : state L) (t : trace) (s2 : state L),
      Star L s1 t s2 → Star (atomic L) (E0, s1) t (E0, s2)

def atomic_forward_simulationStatement : Prop :=
  ∀ L : semantics,
    well_behaved_traces L → forward_simulation L (atomic L)

def atomic_star_star_genStatement : Prop :=
  ∀ (L : semantics) (ts1 : state (atomic L)) (t : trace)
    (ts2 : state (atomic L)),
    Star (atomic L) ts1 t ts2 →
    ∃ t' : trace,
      Star L ts1.2 t' ts2.2 ∧ Eapp ts1.1 t' = Eapp t ts2.1

def atomic_star_starStatement : Prop :=
  ∀ (L : semantics) (s1 : state L) (t : trace) (s2 : state L),
    Star (atomic L) (E0, s1) t (E0, s2) → Star L s1 t s2

def atomic_forever_silent_forever_silentStatement : Prop :=
  ∀ (L : semantics) (s : state (atomic L)),
    ForeverSilent (atomic L) s → ForeverSilent L s.2

def star_atomic_output_traceStatement : Prop :=
  ∀ L : semantics,
    well_behaved_traces L →
    ∀ (s : state L) (t t' : trace) (s' : state L),
      Star (atomic L) (E0, s) t (t', s') → output_trace t'

def atomic_forever_reactive_forever_reactiveStatement : Prop :=
  ∀ L : semantics,
    well_behaved_traces L →
    ∀ (s : state L) (T : traceinf),
      ForeverReactive (atomic L) (E0, s) T → ForeverReactive L s T

def atomic_behaviorsStatement : Prop :=
  ∀ L : semantics,
    well_behaved_traces L →
    ∀ beh : program_behavior,
      program_behaves L beh ↔ program_behaves (atomic L) beh

/-! ## Infinite reduction sequences -/

inductive tstate (genv state : Type)
    (step : genv → state → trace → state → Prop) (ge : genv) : Type where
  | ST (s : state) (T : traceinf) (F : forever step ge s T) :
      tstate genv state step ge

abbrev ST (genv state : Type)
    (step : genv → state → trace → state → Prop) (ge : genv)
    (s : state) (T : traceinf) (F : forever step ge s T) :
    tstate genv state step ge :=
  tstate.ST s T F

def state_of_tstate (genv state : Type)
    (step : genv → state → trace → state → Prop) (ge : genv)
    (S : tstate genv state step ge) : state :=
  match S with
  | .ST s _ _ => s

def traceinf_of_tstate (genv state : Type)
    (step : genv → state → trace → state → Prop) (ge : genv)
    (S : tstate genv state step ge) : traceinf :=
  match S with
  | .ST _ T _ => T

inductive tstep (genv state : Type)
    (step : genv → state → trace → state → Prop) (ge : genv) :
    trace → tstate genv state step ge → tstate genv state step ge → Prop where
  | tstep_intro (s1 : state) (t : trace) (T : traceinf) (s2 : state)
      (S : step ge s1 t s2) (F : forever step ge s2 T) :
      tstep genv state step ge t
        (tstate.ST s1 (Eappinf t T) (forever_intro s1 t S F))
        (tstate.ST s2 T F)

abbrev tstep_intro (genv state : Type)
    (step : genv → state → trace → state → Prop) (ge : genv)
    (s1 : state) (t : trace) (T : traceinf) (s2 : state)
    (S : step ge s1 t s2) (F : forever step ge s2 T) :
    tstep genv state step ge t
      (ST genv state step ge s1 (Eappinf t T) (forever_intro s1 t S F))
      (ST genv state step ge s2 T F) :=
  tstep.tstep_intro s1 t T s2 S F

inductive tsteps (genv state : Type)
    (step : genv → state → trace → state → Prop) (ge : genv) :
    tstate genv state step ge → tstate genv state step ge → Prop where
  | tsteps_refl (S : tstate genv state step ge) :
      tsteps genv state step ge S S
  | tsteps_left (t : trace) (S1 S2 S3 : tstate genv state step ge)
      (hstep : tstep genv state step ge t S1 S2)
      (hsteps : tsteps genv state step ge S2 S3) :
      tsteps genv state step ge S1 S3

abbrev tsteps_refl (genv state : Type)
    (step : genv → state → trace → state → Prop) (ge : genv)
    (S : tstate genv state step ge) : tsteps genv state step ge S S :=
  tsteps.tsteps_refl S

abbrev tsteps_left (genv state : Type)
    (step : genv → state → trace → state → Prop) (ge : genv)
    (t : trace) (S1 S2 S3 : tstate genv state step ge)
    (hstep : tstep genv state step ge t S1 S2)
    (hsteps : tsteps genv state step ge S2 S3) :
    tsteps genv state step ge S1 S3 :=
  tsteps.tsteps_left t S1 S2 S3 hstep hsteps

private def treactive {genv state : Type}
    (step : genv → state → trace → state → Prop) (ge : genv)
    (S : tstate genv state step ge) : Prop :=
  ∀ S1, tsteps genv state step ge S S1 →
    ∃ (S2 S3 : tstate genv state step ge) (t : trace),
      tsteps genv state step ge S1 S2 ∧
        tstep genv state step ge t S2 S3 ∧ t ≠ E0

private def tsilent {genv state : Type}
    (step : genv → state → trace → state → Prop) (ge : genv)
    (S : tstate genv state step ge) : Prop :=
  ∀ (S1 : tstate genv state step ge) (t : trace)
    (S2 : tstate genv state step ge),
    tsteps genv state step ge S S1 →
      tstep genv state step ge t S1 S2 → t = E0

def tsteps_transStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop) (ge : genv)
    (S1 S2 : tstate genv state step ge),
    tsteps genv state step ge S1 S2 →
    ∀ S3 : tstate genv state step ge,
      tsteps genv state step ge S2 S3 →
        tsteps genv state step ge S1 S3

def treactive_or_tsilentStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop) (ge : genv)
    (S : tstate genv state step ge),
    treactive step ge S ∨
      ∃ S' : tstate genv state step ge,
        tsteps genv state step ge S S' ∧ tsilent step ge S'

def tsteps_starStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop) (ge : genv)
    (S1 S2 : tstate genv state step ge),
    tsteps genv state step ge S1 S2 →
    ∃ t : trace,
      star step ge
          (state_of_tstate genv state step ge S1) t
          (state_of_tstate genv state step ge S2) ∧
        traceinf_of_tstate genv state step ge S1 =
          Eappinf t (traceinf_of_tstate genv state step ge S2)

def tsilent_forever_silentStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop) (ge : genv)
    (S : tstate genv state step ge),
    tsilent step ge S →
      forever_silent step ge (state_of_tstate genv state step ge S)

def treactive_forever_reactiveStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop) (ge : genv)
    (S : tstate genv state step ge),
    treactive step ge S →
    forever_reactive step ge
      (state_of_tstate genv state step ge S)
      (traceinf_of_tstate genv state step ge S)

def forever_silent_or_reactiveStatement : Prop :=
  ∀ (genv state : Type)
    (step : genv → state → trace → state → Prop) (ge : genv)
    (s : state) (T : traceinf),
    forever step ge s T →
    forever_reactive step ge s T ∨
      ∃ (t : trace) (s' : state) (T' : traceinf),
        star step ge s t s' ∧ forever_silent step ge s' ∧ T = Eappinf t T'

/-! ## Big-step semantics and program behaviors -/

def behavior_bigstep_terminatesStatement : Prop :=
  ∀ (B : bigstep_semantics) (L : semantics),
    bigstep_sound B L →
    ∀ (t : trace) (r : int),
      bigstep_terminates B t r → program_behaves L (Terminates t r)

def behavior_bigstep_divergesStatement : Prop :=
  ∀ (B : bigstep_semantics) (L : semantics),
    bigstep_sound B L →
    ∀ T : traceinf,
      bigstep_diverges B T →
      program_behaves L (Reacts T) ∨
        ∃ t : trace, program_behaves L (Diverges t) ∧ traceinf_prefix t T

end CompCert4Lean.Common.Behaviors

namespace CompCert4Lean.Common.Behaviors

open CompCert4Lean.Common.Events

private theorem behavior_eapp_assoc (t1 t2 t3 : trace) :
    Eapp (Eapp t1 t2) t3 = Eapp t1 (Eapp t2 t3) := by
  induction t1 with
  | nil => rfl
  | cons ev t ih =>
      exact congrArg (List.cons ev) ih

private theorem behavior_eappinf_assoc (t1 t2 : trace) (T : traceinf) :
    Eappinf (Eapp t1 t2) T = Eappinf t1 (Eappinf t2 T) := by
  induction t1 with
  | nil => rfl
  | cons ev t ih =>
      exact congrArg (Econsinf ev) ih

theorem behavior_app_assoc : behavior_app_assocStatement := by
  intro t1 t2 beh
  cases beh with
  | Terminates t r =>
      simp only [behavior_app]
      exact congrArg (fun t => Terminates t r) (behavior_eapp_assoc t1 t2 t)
  | Diverges t =>
      simp only [behavior_app]
      exact congrArg Diverges (behavior_eapp_assoc t1 t2 t)
  | Reacts T =>
      simp only [behavior_app]
      exact congrArg Reacts (behavior_eappinf_assoc t1 t2 T)
  | Goes_wrong t =>
      simp only [behavior_app]
      exact congrArg Goes_wrong (behavior_eapp_assoc t1 t2 t)

theorem behavior_app_E0 : behavior_app_E0Statement := by
  intro beh
  cases beh <;> rfl

theorem behavior_improves_refl : behavior_improves_reflStatement := by
  intro beh
  exact Or.inl rfl

theorem behavior_improves_trans : behavior_improves_transStatement := by
  intro beh1 beh2 beh3 h12 h23
  rcases h12 with h12 | ⟨t1, h1, b2, hb2⟩
  · subst beh2
    exact h23
  rcases h23 with h23 | ⟨t2, h2wrong, b3, hb3⟩
  · subst beh3
    exact Or.inr ⟨t1, h1, b2, hb2⟩
  have hEq : behavior_app t1 b2 = Goes_wrong t2 := by
    rw [← hb2, h2wrong]
  cases b2 with
  | Terminates t r =>
      simp only [behavior_app] at hEq
      cases hEq
  | Diverges t =>
      simp only [behavior_app] at hEq
      cases hEq
  | Reacts T =>
      simp only [behavior_app] at hEq
      cases hEq
  | Goes_wrong t2' =>
      simp only [behavior_app] at hEq
      cases hEq with
      | refl =>
          right
          refine ⟨t1, h1, behavior_app t2' b3, ?_⟩
          rw [hb3, ← behavior_app_assoc]

end CompCert4Lean.Common.Behaviors

namespace CompCert4Lean.Common.Behaviors

open CompCert4Lean.Common.Events

theorem behavior_improves_bot : behavior_improves_botStatement := by
  intro beh
  right
  refine ⟨E0, rfl, ?_⟩
  exact ⟨beh, (behavior_app_E0 beh).symm⟩

end CompCert4Lean.Common.Behaviors

namespace CompCert4Lean.Common.Behaviors

open CompCert4Lean.Common.Events

theorem behavior_improves_app : behavior_improves_appStatement := by
  intro t beh1 beh2 h
  rcases h with h | ⟨t', hwrong, ⟨beh', hprefix⟩⟩
  · subst beh2
    exact Or.inl rfl
  · subst beh1
    refine Or.inr ⟨Eapp t t', rfl, beh', ?_⟩
    rw [hprefix]
    exact (behavior_app_assoc t t' beh').symm

end CompCert4Lean.Common.Behaviors

namespace CompCert4Lean.Common.Behaviors

open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Smallstep

private theorem state_behaves_star_forever_reactive
    {genv state : Type}
    (step : genv → state → trace → state → Prop) (ge : genv)
    (s1 : state) (t : trace) (s2 : state) (T : traceinf)
    (hstar : star step ge s1 t s2)
    (hforever : forever_reactive step ge s2 T) :
    forever_reactive step ge s1 (Eappinf t T) := by
  refine forever_reactive_casesOn (step := step) (ge := ge)
    (motive := fun s T =>
      star step ge s1 t s → forever_reactive step ge s1 (Eappinf t T)) ?_ hforever hstar
  intro s2' s3 t' T' hstar' hnonempty htail hprefix
  have hstar'' : star step ge s1 (Eapp t t') s3 :=
    star_trans genv state step ge s1 t s2' hprefix t' s3 (Eapp t t') hstar' rfl
  have hnonempty'' : Eapp t t' ≠ E0 := by
    intro h
    cases t with
    | nil =>
        change t' = E0 at h
        exact hnonempty h
    | cons ev t => cases h
  have hassoc : Eappinf (Eapp t t') T' = Eappinf t (Eappinf t' T') :=
    behavior_eappinf_assoc t t' T'
  rw [← hassoc]
  exact forever_reactive_intro hstar'' hnonempty'' htail

theorem state_behaves_app : state_behaves_appStatement := by
  intro L s1 t s2 beh hstar hbeh
  cases hbeh with
  | state_terminates t' s' r hstar' hfinal =>
      exact state_behaves.state_terminates (Eapp t t') s' r
        (star_trans L.genvtype L.state (step L) (globalenv L) s1 t s2 hstar t' s' (Eapp t t') hstar' rfl)
        hfinal
  | state_diverges t' s' hstar' hforever =>
      exact state_behaves.state_diverges (Eapp t t') s'
        (star_trans L.genvtype L.state (step L) (globalenv L) s1 t s2 hstar t' s' (Eapp t t') hstar' rfl)
        hforever
  | state_reacts T hforever =>
      exact state_behaves.state_reacts (Eappinf t T)
        (state_behaves_star_forever_reactive (step L) (globalenv L)
          s1 t s2 T hstar hforever)
  | state_goes_wrong t' s' hstar' hnostep hnofinal =>
      exact state_behaves.state_goes_wrong (Eapp t t') s'
        (star_trans L.genvtype L.state (step L) (globalenv L) s1 t s2 hstar t' s' (Eapp t t') hstar' rfl)
        hnostep hnofinal

end CompCert4Lean.Common.Behaviors

namespace CompCert4Lean.Common.Behaviors

open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Smallstep

private theorem behaviors_traceinf_app (t : trace) (T : traceinf') (NE : t ≠ E0) :
    traceinf_of_traceinf' (Econsinf' t T NE) =
      Eappinf t (traceinf_of_traceinf' T) := by
  funext n
  induction t generalizing n with
  | nil => exact False.elim (NE rfl)
  | cons e t ih =>
      cases t with
      | nil =>
          cases n with
          | zero => rfl
          | succ n => rfl
      | cons e' t =>
          cases n with
          | zero => rfl
          | succ n =>
              exact ih (by intro h; cases h) n

private theorem behaviors_reactiveCursorAt_shift
    (L : semantics) (s0 : state L)
    (reacts : ∀ (s1 : state L) (t1 : trace),
      Star L s0 t1 s1 →
      ∃ (s2 : state L) (t2 : trace), Star L s1 t2 s2 ∧ t2 ≠ E0)
    (c : ReactiveCursor L s0) (n : Nat) :
    reactiveCursorAt L s0 reacts c (n + 1) =
      reactiveCursorAt L s0 reacts (nextReactiveCursor L s0 reacts c) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [reactiveCursorAt]
      exact congrArg (nextReactiveCursor L s0 reacts) ih

private theorem behaviors_reactiveChunkAt_shift
    (L : semantics) (s0 : state L)
    (reacts : ∀ (s1 : state L) (t1 : trace),
      Star L s0 t1 s1 →
      ∃ (s2 : state L) (t2 : trace), Star L s1 t2 s2 ∧ t2 ≠ E0)
    (c : ReactiveCursor L s0) (n : Nat) :
    reactiveChunkAt L s0 reacts c (n + 1) =
      reactiveChunkAt L s0 reacts (nextReactiveCursor L s0 reacts c) n := by
  apply Subtype.ext
  dsimp [reactiveChunkAt]
  rw [behaviors_reactiveCursorAt_shift]

private theorem behaviors_build_tail
    (L : semantics) (s0 : state L)
    (reacts : ∀ (s1 : state L) (t1 : trace),
      Star L s0 t1 s1 →
      ∃ (s2 : state L) (t2 : trace), Star L s1 t2 s2 ∧ t2 ≠ E0)
    (c : ReactiveCursor L s0) :
    traceinf'.tailChunks
        (build_traceinf' L (s0 := s0) reacts c.reachable) =
      build_traceinf' L (s0 := s0) reacts
        (nextReactiveCursor L s0 reacts c).reachable := by
  have hchunk :
      (traceinf'.tailChunks
        (build_traceinf' L (s0 := s0) reacts c.reachable)).chunk =
      (build_traceinf' L (s0 := s0) reacts
        (nextReactiveCursor L s0 reacts c).reachable).chunk := by
    funext n
    dsimp [traceinf', build_traceinf']
    exact congrArg Subtype.val
      (behaviors_reactiveChunkAt_shift L s0 reacts c n)
  cases hleft : traceinf'.tailChunks
      (build_traceinf' L (s0 := s0) reacts c.reachable) with
  | mk l ln =>
      cases hright : build_traceinf' L (s0 := s0) reacts
          (nextReactiveCursor L s0 reacts c).reachable with
      | mk r rn =>
          simpa [hleft, hright] using hchunk

private theorem behaviors_traceinf'_decompose (T : traceinf') :
    T = Econsinf' (T.chunk 0) (traceinf'.tailChunks T) (T.nonempty 0) := by
  cases T with
  | mk chunk nonempty =>
      apply (traceinf'.mk.injEq chunk nonempty _ _).mpr
      funext n
      cases n <;> rfl

private theorem behaviors_build_step
    (L : semantics) (s0 : state L)
    (reacts : ∀ (s1 : state L) (t1 : trace),
      Star L s0 t1 s1 →
      ∃ (s2 : state L) (t2 : trace), Star L s1 t2 s2 ∧ t2 ≠ E0)
    (c : ReactiveCursor L s0) :
    traceinf_of_traceinf'
        (build_traceinf' L (s0 := s0) reacts c.reachable) =
      Eappinf ((reacts' L reacts c.reachable).2.1)
        (traceinf_of_traceinf'
          (build_traceinf' L (s0 := s0) reacts
            (nextReactiveCursor L s0 reacts c).reachable)) := by
  let B := build_traceinf' L (s0 := s0) reacts c.reachable
  have hdec : B = Econsinf' (B.chunk 0) (traceinf'.tailChunks B) (B.nonempty 0) :=
    behaviors_traceinf'_decompose B
  change traceinf_of_traceinf' B = _
  rw [hdec, behaviors_traceinf_app]
  rw [behaviors_build_tail]
  rfl

theorem reacts_forever_reactive_rec : reacts_forever_reactive_recStatement := by
  intro L s0 reacts s1 t1 ST
  let c0 : ReactiveCursor L s0 := { current := s1, history := t1, reachable := ST }
  let pred : state L → traceinf → Prop := fun s T =>
    ∃ c : ReactiveCursor L s0,
      c.current = s ∧
        T = traceinf_of_traceinf'
          (build_traceinf' L (s0 := s0) reacts c.reachable)
  have hpred : pred c0.current
      (traceinf_of_traceinf'
        (build_traceinf' L (s0 := s0) reacts c0.reachable)) := by
    exact ⟨c0, rfl, rfl⟩
  exact forever_reactive.coinduct (step L) (globalenv L) pred
    (by
      intro s T hs
      rcases hs with ⟨c, rfl, rfl⟩
      let selected := reacts' L reacts c.reachable
      let cnext := nextReactiveCursor L s0 reacts c
      refine ⟨cnext.current, selected.2.1,
        traceinf_of_traceinf'
          (build_traceinf' L (s0 := s0) reacts cnext.reachable), ?_,
        selected.2.2.2, ?_, ?_⟩
      · exact selected.2.2.1
      · exact ⟨cnext, rfl, rfl⟩
      · exact behaviors_build_step L s0 reacts c)
    c0.current
    (traceinf_of_traceinf'
      (build_traceinf' L (s0 := s0) reacts c0.reachable))
    hpred

end CompCert4Lean.Common.Behaviors

namespace CompCert4Lean.Common.Behaviors
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Smallstep
theorem reacts_forever_reactive : reacts_forever_reactiveStatement := by
  intro L s0 reacts
  let h0 : Star L s0 E0 s0 := star_refl (step L) (globalenv L) s0
  refine ⟨traceinf_of_traceinf' (build_traceinf' L reacts h0), ?_⟩
  exact reacts_forever_reactive_rec L s0 reacts s0 E0 h0
end CompCert4Lean.Common.Behaviors

namespace CompCert4Lean.Common.Behaviors

open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Smallstep

theorem diverges_forever_silent : diverges_forever_silentStatement := by
  intro L s0 H
  let pred : state L → Prop := fun s =>
    ∃ t, star (step L) (globalenv L) s0 t s
  refine forever_silent.coinduct (step L) (globalenv L) pred ?_ s0 ?_
  · intro s hs
    rcases hs with ⟨t, hreach⟩
    obtain ⟨s', hstep⟩ := H s t hreach
    refine ⟨s', hstep, ?_⟩
    exact ⟨Eapp t E0,
      star_right L.genvtype (state L) (step L) (globalenv L)
        s0 t s E0 s' (Eapp t E0) hreach hstep rfl⟩
  · exact ⟨E0, star_refl (step L) (globalenv L) s0⟩

end CompCert4Lean.Common.Behaviors

namespace CompCert4Lean.Common.Behaviors

open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Lib.Integers

theorem state_behaves_exists : state_behaves_existsStatement := by
  intro L s0
  classical
  by_cases hstep_all :
      ∀ (s1 : state L) (t1 : trace),
        Star L s0 t1 s1 → ∃ s2 : state L, ∃ t2 : trace, Step L s1 t2 s2
  · by_cases hsilent :
        ∃ s1 : state L, ∃ t1 : trace,
          Star L s0 t1 s1 ∧
            (∀ (s2 : state L) (t2 : trace),
              Star L s1 t2 s2 → ∃ s3 : state L, Step L s2 E0 s3)
    · rcases hsilent with ⟨s1, t1, hreach, hsilent_tail⟩
      exact ⟨Diverges t1,
        state_behaves.state_diverges t1 s1 hreach
          (diverges_forever_silent L s1 hsilent_tail)⟩
    · obtain ⟨T, hreactive⟩ := reacts_forever_reactive L s0 (by
        intro s1 t1 hreach
        have hnot :
            ¬ (∀ (s2 : state L) (t2 : trace),
              Star L s1 t2 s2 → ∃ s3 : state L, Step L s2 E0 s3) := by
          intro hcontra
          exact hsilent ⟨s1, t1, hreach, hcontra⟩
        obtain ⟨s2, hnot_t2⟩ := Classical.not_forall.mp hnot
        obtain ⟨t2, hnot_imp⟩ := Classical.not_forall.mp hnot_t2
        obtain ⟨hreach2, hnozero⟩ :=
          CompCert4Lean.Foundation.Logic.Rocq.Coq.Logic.Classical_Prop.imply_to_and _ _ hnot_imp
        have hstep := hstep_all s2 (Eapp t1 t2) (star_trans
          L.genvtype L.state (step L) (globalenv L)
          s0 t1 s1 hreach t2 s2 (Eapp t1 t2) hreach2 rfl)
        rcases hstep with ⟨s3, t3, hstep3⟩
        refine ⟨s3, Eapp t2 t3, ?_, ?_⟩
        · exact star_right L.genvtype L.state (step L) (globalenv L)
            s1 t2 s2 t3 s3 (Eapp t2 t3) hreach2 hstep3 rfl
        · intro hempty
          obtain ⟨ht2, ht3⟩ :=
            CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.app_eq_nil
              t2 t3 hempty
          apply hnozero
          refine Exists.intro s3 ?_
          simpa [E0, ht3] using hstep3
        )
      exact ⟨Reacts T, state_behaves.state_reacts T hreactive⟩
  · obtain ⟨s1, hnot_t1⟩ := Classical.not_forall.mp hstep_all
    obtain ⟨t1, hnot_imp⟩ := Classical.not_forall.mp hnot_t1
    obtain ⟨hreach, hnostep_exists⟩ :=
      CompCert4Lean.Foundation.Logic.Rocq.Coq.Logic.Classical_Prop.imply_to_and _ _ hnot_imp
    have hnostep : Nostep L s1 := by
      intro t s2 hstep
      exact hnostep_exists (by exact ⟨s2, t, hstep⟩)
    by_cases hfinal : ∃ r : int, final_state L s1 r
    · rcases hfinal with ⟨r, hfinal⟩
      exact ⟨Terminates t1 r,
        state_behaves.state_terminates t1 s1 r hreach hfinal⟩
    · exact ⟨Goes_wrong t1,
        state_behaves.state_goes_wrong t1 s1 hreach hnostep
          (by intro r hfinal_r; exact hfinal ⟨r, hfinal_r⟩)⟩

end CompCert4Lean.Common.Behaviors

namespace CompCert4Lean.Common.Behaviors

open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Smallstep

theorem program_behaves_exists : program_behaves_existsStatement := by
  intro L
  classical
  by_cases hinit : ∃ s : state L, initial_state L s
  · rcases hinit with ⟨s, hs⟩
    obtain ⟨beh, hbeh⟩ := state_behaves_exists L s
    exact ⟨beh, program_behaves.program_runs s beh hs hbeh⟩
  · refine ⟨Goes_wrong E0, program_behaves.program_goes_initially_wrong ?_⟩
    intro s hs
    exact hinit ⟨s, hs⟩

end CompCert4Lean.Common.Behaviors

namespace CompCert4Lean.Common.Behaviors

open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Smallstep

private theorem behaviors_eapp_eq_nil_left {t1 t2 : trace}
    (h : Eapp t1 t2 = E0) : t1 = E0 := by
  cases t1 with
  | nil => rfl
  | cons ev t => cases h

private theorem behaviors_simulation_star
    (L1 L2 : semantics) (index : Type)
    (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop)
    (props : fsim_properties L1 L2 index order match_states)
    (s1 : state L1) (t : trace) (s1' : state L1)
    (hstar : star (step L1) (globalenv L1) s1 t s1') :
    ∀ i s2, match_states i s1 s2 →
      ∃ i' s2', star (step L2) (globalenv L2) s2 t s2' ∧
        match_states i' s1' s2' := by
  induction hstar with
  | star_refl s =>
      intro i s2 hmatch
      exact ⟨i, s2, star_refl (step L2) (globalenv L2) s2, hmatch⟩
  | star_step s1 t1 s2 t2 s3 t hstep htail htrace ih =>
      intro i s2x hmatch
      obtain ⟨i', s2', hsim, hmatch'⟩ :=
        props.fsim_simulation s1 t1 s2 hstep i s2x hmatch
      obtain ⟨i'', s2'', htail', hmatch''⟩ := ih i' s2' hmatch'
      rcases hsim with hplus | ⟨hstar', _⟩
      · exact ⟨i'', s2'',
          star_trans L2.genvtype (state L2) (step L2) (globalenv L2)
            s2x t1 s2'
            (plus_star L2.genvtype (state L2) (step L2) (globalenv L2)
              s2x t1 s2' hplus)
            t2 s2'' t htail' htrace,
          hmatch''⟩
      · exact ⟨i'', s2'',
          star_trans L2.genvtype (state L2) (step L2) (globalenv L2)
            s2x t1 s2' hstar' t2 s2'' t htail' htrace,
          hmatch''⟩

private theorem behaviors_forever_silent_N_inv
    {genv state A : Type}
    (step : genv → state → trace → state → Prop)
    (order : A → A → Prop) (ge : genv)
    (wf : WellFounded order) :
    ∀ a s, forever_silent_N step order ge a s →
      ∃ s' a', step ge s E0 s' ∧ forever_silent_N step order ge a' s' := by
  intro a
  apply wf.induction a
  intro a ih
  intro s hN
  have prefixN : ∀ (b : A) (s1 s2 : state) (t : trace),
          star step ge s1 t s2 → t = E0 →
          forever_silent_N step order ge b s2 →
          forever_silent_N step order ge b s1 := by
        intro b s1 s2 t hstar ht htail
        induction hstar with
        | star_refl s => exact htail
        | @star_step s1 t1 s2 t2 s3 t hstep hrest htrace ihrest =>
            have happ : Eapp t1 t2 = E0 := by simpa [htrace] using ht
            have ht1 : t1 = E0 := behaviors_eapp_eq_nil_left happ
            subst t1
            have ht2 : t2 = E0 := by
              rw [show Eapp E0 t2 = t2 by exact _root_.List.nil_append t2] at happ
              exact happ
            subst t2
            exact forever_silent_N_plus b
              (plus_left s1 E0 hstep hrest rfl) htail
  have starHead : ∀ (s1 s3 : state) (t : trace),
          star step ge s1 t s3 → t = E0 →
          ∀ a2, order a2 a →
            forever_silent_N step order ge a2 s3 →
            ∃ s2 a', step ge s1 E0 s2 ∧
              forever_silent_N step order ge a' s2 := by
    intro s1 s3 t hstar ht
    induction hstar with
    | star_refl s =>
        intro a2 horder htail
        exact ih a2 horder s htail
    | @star_step s1 t1 s2 t2 s3 t hstep hrest htrace ihrest =>
        intro a2 horder htail
        have happ : Eapp t1 t2 = E0 := by simpa [htrace] using ht
        have ht1 : t1 = E0 := behaviors_eapp_eq_nil_left happ
        subst t1
        have ht2 : t2 = E0 := by
          rw [show Eapp E0 t2 = t2 by exact _root_.List.nil_append t2] at happ
          exact happ
        subst t2
        exact ⟨s2, a, hstep,
          forever_silent_N_star a hrest horder htail⟩
  have plusHead : ∀ (s1 s3 : state) (t : trace),
          plus step ge s1 t s3 → t = E0 →
          ∀ a2, forever_silent_N step order ge a2 s3 →
            ∃ s2 a', step ge s1 E0 s2 ∧
              forever_silent_N step order ge a' s2 := by
    intro s1 s3 t hplus ht
    cases hplus with
    | plus_left =>
        rename_i t1 s2 t2 hstep htrace hrest
        intro a2 htail
        have happ : Eapp t1 t2 = E0 := by simpa [htrace] using ht
        have ht1 : t1 = E0 := behaviors_eapp_eq_nil_left happ
        subst t1
        have ht2 : t2 = E0 := by
          rw [show Eapp E0 t2 = t2 by exact _root_.List.nil_append t2] at happ
          exact happ
        subst t2
        exact ⟨s2, a2, hstep,
          prefixN a2 s2 s3 E0 hrest rfl htail⟩
  cases hN with
  | forever_silent_N_star =>
      rename_i s2 a2 htail horder hstar
      exact starHead s s2 E0 hstar rfl a2 horder htail
  | forever_silent_N_plus =>
      rename_i s2 a2 htail hplus
      exact plusHead s s2 E0 hplus rfl a2 htail

private theorem behaviors_forever_silent_N_forever
    {genv state A : Type}
    (step : genv → state → trace → state → Prop)
    (order : A → A → Prop) (ge : genv)
    (wf : WellFounded order) :
    ∀ a s, forever_silent_N step order ge a s →
      forever_silent step ge s := by
  intro a s hN
  let pred : state → Prop := fun s => ∃ a, forever_silent_N step order ge a s
  have hpred : pred s := ⟨a, hN⟩
  exact forever_silent.coinduct step ge pred
    (by
      intro s hs
      rcases hs with ⟨a, hN⟩
      obtain ⟨s', a', hstep, hN'⟩ :=
        behaviors_forever_silent_N_inv step order ge wf a s hN
      exact ⟨s', hstep, ⟨a', hN'⟩⟩)
    s hpred

private theorem behaviors_simulation_forever_silent
    (L1 L2 : semantics) (index : Type)
    (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop)
    (props : fsim_properties L1 L2 index order match_states) :
    ∀ i s1 s2, forever_silent (step L1) (globalenv L1) s1 →
      match_states i s1 s2 →
      forever_silent (step L2) (globalenv L2) s2 := by
  intro i s1 s2 hforever hmatch
  let pred : index → state L2 → Prop := fun i s2 =>
    ∃ s1, match_states i s1 s2 ∧
      forever_silent (step L1) (globalenv L1) s1
  have hN : forever_silent_N (step L2) order (globalenv L2) i s2 :=
    forever_silent_N.coinduct (step L2) order (globalenv L2) pred
      (by
        intro i s2 hs
        rcases hs with ⟨s1, hmatch, hforever⟩
        exact (forever_silent_casesOn
          (step := step L1) (ge := globalenv L1)
          (motive := fun s1 => match_states i s1 s2 →
            (∃ s2' i', star (step L2) (globalenv L2) s2 E0 s2' ∧
              order i' i ∧
              (∃ s1', match_states i' s1' s2' ∧
                forever_silent (step L1) (globalenv L1) s1')) ∨
            (∃ s2' i', plus (step L2) (globalenv L2) s2 E0 s2' ∧
              (∃ s1', match_states i' s1' s2' ∧
                forever_silent (step L1) (globalenv L1) s1')))
          (by
            intro s1' s1next hstep htail hmatch
            obtain ⟨i', s2', hsim, hmatch'⟩ :=
              props.fsim_simulation s1' E0 s1next hstep i s2 hmatch
            rcases hsim with hplus | ⟨hstar, horder⟩
            · exact Or.inr ⟨s2', i', hplus,
                ⟨s1next, hmatch', htail⟩⟩
            · exact Or.inl ⟨s2', i', hstar, horder,
                ⟨s1next, hmatch', htail⟩⟩)
          hforever) hmatch)
      i s2 ⟨s1, hmatch, hforever⟩
  exact behaviors_forever_silent_N_forever
    (step L2) order (globalenv L2) props.fsim_order_wf i s2 hN

private theorem behaviors_simulation_forever_reactive
    (L1 L2 : semantics) (index : Type)
    (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop)
    (props : fsim_properties L1 L2 index order match_states) :
    ∀ i s1 s2 T, forever_reactive (step L1) (globalenv L1) s1 T →
      match_states i s1 s2 →
      forever_reactive (step L2) (globalenv L2) s2 T := by
  intro i s1 s2 T hforever hmatch
  let pred : state L2 → traceinf → Prop := fun s2 T =>
    ∃ i s1, match_states i s1 s2 ∧
      forever_reactive (step L1) (globalenv L1) s1 T
  exact forever_reactive.coinduct (step L2) (globalenv L2) pred
    (by
      intro s2 T hs
      rcases hs with ⟨i, s1, hmatch, hforever⟩
      exact (forever_reactive_casesOn
        (step := step L1) (ge := globalenv L1)
        (motive := fun s1 T => match_states i s1 s2 →
          ∃ s2' t T',
            star (step L2) (globalenv L2) s2 t s2' ∧
              t ≠ E0 ∧
              (∃ i' s1', match_states i' s1' s2' ∧
                forever_reactive (step L1) (globalenv L1) s1' T') ∧
              (T = Eappinf t T'))
        (by
          intro s1 s1' t T' hstar hnonempty htail hmatch
          obtain ⟨i', s2', hstar', hmatch'⟩ :=
            behaviors_simulation_star L1 L2 index order match_states props
              s1 t s1' hstar i s2 hmatch
          exact ⟨s2', t, T', hstar', hnonempty,
            ⟨i', s1', hmatch', htail⟩, rfl⟩)
        hforever hmatch))
    s2 T ⟨i, s1, hmatch, hforever⟩

private theorem behaviors_forward_simulation_state_behaves
    (L1 L2 : semantics) (index : Type)
    (order : index → index → Prop)
    (match_states : index → state L1 → state L2 → Prop)
    (props : fsim_properties L1 L2 index order match_states) :
    ∀ i s1 s2 (beh1 : program_behavior),
      match_states i s1 s2 → state_behaves L1 s1 beh1 →
      ∃ beh2, state_behaves L2 s2 beh2 ∧
        behavior_improves beh1 beh2 := by
  intro i s1 s2 beh1 hmatch hbeh1
  cases hbeh1 with
  | state_terminates t s1' r hstar hfinal =>
      obtain ⟨i', s2', hstar', hmatch'⟩ :=
        behaviors_simulation_star L1 L2 index order match_states props
          s1 t s1' hstar i s2 hmatch
      exact ⟨Terminates t r,
        state_behaves.state_terminates t s2' r hstar'
          (props.fsim_match_final_states i' s1' s2' r hmatch' hfinal),
        behavior_improves_refl (Terminates t r)⟩
  | state_diverges t s1' hstar hforever =>
      obtain ⟨i', s2', hstar', hmatch'⟩ :=
        behaviors_simulation_star L1 L2 index order match_states props
          s1 t s1' hstar i s2 hmatch
      exact ⟨Diverges t,
        state_behaves.state_diverges t s2' hstar'
          (behaviors_simulation_forever_silent L1 L2 index order match_states
            props i' s1' s2' hforever hmatch'),
        behavior_improves_refl (Diverges t)⟩
  | state_reacts T hforever =>
      exact ⟨Reacts T,
        state_behaves.state_reacts T
          (behaviors_simulation_forever_reactive L1 L2 index order match_states
            props i s1 s2 T hforever hmatch),
        behavior_improves_refl (Reacts T)⟩
  | state_goes_wrong t s1' hstar hnostep hnofinal =>
      obtain ⟨i', s2', hstar', hmatch'⟩ :=
        behaviors_simulation_star L1 L2 index order match_states props
          s1 t s1' hstar i s2 hmatch
      obtain ⟨beh2, hbeh2⟩ := state_behaves_exists L2 s2'
      refine ⟨behavior_app t beh2,
        state_behaves_app L2 s2 t s2' beh2 hstar' hbeh2, ?_⟩
      have himp := behavior_improves_app t (Goes_wrong E0) beh2
        (behavior_improves_bot beh2)
      change behavior_improves (Goes_wrong (Eapp t E0))
        (behavior_app t beh2) at himp
      have ht : Eapp t E0 = t := _root_.List.append_nil t
      rw [ht] at himp
      exact himp

theorem forward_simulation_behavior_improves :
    forward_simulation_behavior_improvesStatement := by
  intro L1 L2 hsim
  cases hsim with
  | @Forward_simulation index order match_states props =>
      intro beh1 hbeh1
      cases hbeh1 with
      | program_runs s1 beh1 hinit hbehaves =>
          obtain ⟨i, s2, hinit2, hmatch⟩ :=
            props.fsim_match_initial_states s1 hinit
          obtain ⟨beh2, hbehaves2, himproves⟩ :=
            behaviors_forward_simulation_state_behaves L1 L2 index order
              match_states props i s1 s2 beh1 hmatch hbehaves
          exact ⟨beh2,
            program_behaves.program_runs s2 beh2 hinit2 hbehaves2,
            himproves⟩
      | program_goes_initially_wrong hnoinit =>
          classical
          by_cases hinit2 : ∃ s2, initial_state L2 s2
          · rcases hinit2 with ⟨s2, hinit2⟩
            obtain ⟨beh2, hbehaves2⟩ := state_behaves_exists L2 s2
            exact ⟨beh2,
              program_behaves.program_runs s2 beh2 hinit2 hbehaves2,
              behavior_improves_bot beh2⟩
          · refine ⟨Goes_wrong E0,
              program_behaves.program_goes_initially_wrong ?_,
              behavior_improves_refl (Goes_wrong E0)⟩
            intro s hs
            exact hinit2 ⟨s, hs⟩

end CompCert4Lean.Common.Behaviors

namespace CompCert4Lean.Common.Behaviors

open CompCert4Lean.Common.Events

theorem forward_simulation_same_safe_behavior :
    forward_simulation_same_safe_behaviorStatement := by
  intro L1 L2 hsim beh hbeh hnotwrong
  obtain ⟨beh2, hbeh2, himproves⟩ :
      ∃ beh2 : program_behavior,
        program_behaves L2 beh2 ∧ behavior_improves beh beh2 :=
    forward_simulation_behavior_improves L1 L2 hsim beh hbeh
  rcases himproves with heq | ⟨t, hwrong, hprefix⟩
  · rw [heq]
    exact hbeh2
  · subst beh
    simp [not_wrong] at hnotwrong

end CompCert4Lean.Common.Behaviors
