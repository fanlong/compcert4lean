import CompCert4Lean.Common.Errors
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Maps

/-!
# Unification constraint solver

This module translates the definition-bearing surface of CompCert's
`common/Unityping.v`.  The source proof declarations are retained as exact
statement descriptors for the later proof-migration phase.
-/

namespace CompCert4Lean.Common.Unityping

open CompCert4Lean.Foundation.Logic
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Common.Errors

private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string

private def ofString (s : String) : RocqString :=
  (String.toUTF8 s).toList.foldr
    (fun b tail => CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.String b tail)
    CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.EmptyString

/-! ## The interface for base types -/

structure TYPE_ALGEBRA where
  t : Type
  eq : ∀ (x y : t), CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y)
  default : t

/-! ## The constraint solver -/

namespace UniSolver

variable (T : TYPE_ALGEBRA)

def constraint : Type := positive × positive

structure typenv : Type where
  te_typ : PTree.t T.t
  te_equ : List constraint

export typenv (te_typ te_equ)

def initial : typenv T :=
  { te_typ := PTree.empty T.t
    te_equ := [] }

def set (e : typenv T) (x : positive) (ty : T.t) : res (typenv T) :=
  match PTree.get x (te_typ e) with
  | none =>
      OK { te_typ := PTree.set x ty (te_typ e), te_equ := te_equ e }
  | some ty' =>
      match T.eq ty ty' with
      | .left _ => OK e
      | .right _ => Error (MSG (ofString "bad definition/use of variable ") :: POS x :: [])

def set_list (T : TYPE_ALGEBRA) (e : typenv T) : List positive → List T.t → res (typenv T)
  | [], [] => OK e
  | r1 :: rs, ty1 :: tys =>
      match set T e r1 ty1 with
      | Error message => Error message
      | OK e1 => set_list T e1 rs tys
  | _, _ => Error (msg (ofString "arity mismatch"))

def move (e : typenv T) (r1 r2 : positive) : res (Bool × typenv T) :=
  match peq r1 r2 with
  | .left _ => OK (false, e)
  | .right _ =>
      match PTree.get r1 (te_typ e), PTree.get r2 (te_typ e) with
      | none, none =>
          OK (false,
            { te_typ := te_typ e
              te_equ := (r1, r2) :: te_equ e })
      | some ty1, none =>
          OK (true,
            { te_typ := PTree.set r2 ty1 (te_typ e)
              te_equ := te_equ e })
      | none, some ty2 =>
          OK (true,
            { te_typ := PTree.set r1 ty2 (te_typ e)
              te_equ := te_equ e })
      | some ty1, some ty2 =>
          match T.eq ty1 ty2 with
          | .left _ => OK (false, e)
          | .right _ =>
              Error
                (MSG (ofString "ill-typed move from ") ::
                  POS r1 :: MSG (ofString " to ") :: POS r2 :: [])

def solve_rec (T : TYPE_ALGEBRA) (e : typenv T) (changed : Bool) : List constraint → res (typenv T × Bool)
  | [] => OK (e, changed)
  | (r1, r2) :: q' =>
      match move T e r1 r2 with
      | Error message => Error message
      | OK (changed1, e1) => solve_rec T e1 (changed || changed1) q'

def weight_typenv (e : typenv T) : Nat := (te_equ e).length

def typassign : Type := positive → T.t

def makeassign (e : typenv T) : typassign T :=
  fun x =>
    match PTree.get x (te_typ e) with
    | some ty => ty
    | none => T.default

def satisf (te : typassign T) (e : typenv T) : Prop :=
  (∀ x ty, PTree.get x (te_typ e) = some ty → te x = ty) ∧
    (∀ x y, (x, y) ∈ te_equ e → te x = te y)

theorem length_move (T : TYPE_ALGEBRA) (e : typenv T) (r1 r2 : positive)
    (changed : Bool) (e' : typenv T) :
    move T e r1 r2 = OK (changed, e') →
      (te_equ e').length + (if changed then 1 else 0) ≤ Nat.succ (te_equ e).length := by
  intro h
  unfold move at h
  split at h
  · rcases h with ⟨rfl, rfl⟩
    simp
  · split at h <;> try split at h
    all_goals rcases h with ⟨rfl, rfl⟩ <;> simp_all [List.length] <;> omega

theorem length_solve_rec (T : TYPE_ALGEBRA) (q : List constraint) (e : typenv T)
    (ch : Bool) (e' : typenv T) (ch' : Bool) :
    solve_rec T e ch q = OK (e', ch') →
      (te_equ e').length + (if ch' && negb ch then 1 else 0) ≤
        (te_equ e).length + q.length := by
  induction q generalizing e ch e' ch' with
  | nil =>
      intro h
      simp [solve_rec] at h
      rcases h with ⟨rfl, rfl⟩
      cases ch <;> simp [List.length, negb]
  | cons a q ih =>
      rcases a with ⟨r1, r2⟩
      simp only [solve_rec]
      split
      · intro h
        cases h
      · intro h
        rename_i _ changed1 e1 hmove
        have hrec := ih (e := e1) (ch := ch || changed1)
          (e' := e') (ch' := ch') h
        have hmove_len := length_move T e r1 r2 changed1 e1 hmove
        cases ch <;> cases changed1 <;> cases ch' <;>
          simp [negb, List.length] at hrec hmove_len ⊢ <;> omega

/-! The source uses a measure-recursive fixpoint. -/

def solve_constraints_F (step : typenv T → res (typenv T)) (e : typenv T) :
    res (typenv T) :=
  match solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) with
  | Error message => Error message
  | OK (_e', false) => OK e
  | OK (e', true) => step e'

def solve_constraints (e : typenv T) : res (typenv T) :=
  match _hrec : solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) with
  | Error message => Error message
  | OK (_e', false) => OK e
  | OK (e', true) => solve_constraints e'
termination_by weight_typenv T e
decreasing_by
  have hlen := length_solve_rec T (te_equ e) { te_typ := te_typ e, te_equ := [] }
    false e' true ‹solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) =
      OK (e', true)›
  simp [weight_typenv, negb] at hlen ⊢
  omega

theorem solve_constraints_equation (T : TYPE_ALGEBRA) (e : typenv T) :
    solve_constraints T e =
      match solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) with
      | OK (e', true) => solve_constraints T e'
      | OK (_e', false) => OK e
      | Error message => Error message := by
  rw [solve_constraints.eq_1]
  cases h : solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) with
  | Error message => rfl
  | OK value =>
      cases value with
      | mk e' changed => cases changed <;> rfl

def solve_constraints_iter (step :
    ((typenv T → res (typenv T)) → typenv T → res (typenv T))) :
    Nat → (typenv T → res (typenv T)) → typenv T → res (typenv T)
  | 0, fallback, e => fallback e
  | n + 1, fallback, e => step (solve_constraints_iter step n fallback) e

/-! These are the source-generated `Function` interfaces.  The executable
    equation and graph are present above/below; the opaque proof fields keep
    their exact propositions for the later proof-grinding phase. -/

theorem solve_constraints_tcc (T : TYPE_ALGEBRA) (e : typenv T)
    (p : typenv T × Bool) (e' : typenv T) (b : Bool) :
    b = true → p = (e', true) →
      solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) =
        OK (e', true) →
      weight_typenv T e' < weight_typenv T e := by
  intro _ _ hrec
  have hlen := length_solve_rec T (te_equ e) { te_typ := te_typ e, te_equ := [] }
    false e' true hrec
  simp [weight_typenv, negb] at hlen ⊢
  omega

theorem solve_constraints_terminate (T : TYPE_ALGEBRA) (e : typenv T) :
    ∃ v : res (typenv T), ∃ p : Nat, ∀ k : Nat, p < k →
      ∀ fallback : typenv T → res (typenv T),
        solve_constraints_iter (T := T) (solve_constraints_F T) k fallback e = v := by
  cases hrec : solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) with
  | Error message =>
      refine ⟨Error message, 0, ?_⟩
      intro k hk fallback
      cases k with
      | zero => omega
      | succ n => simp [solve_constraints_iter, solve_constraints_F, hrec]
  | OK value =>
      rcases value with ⟨e', changed⟩
      cases changed with
      | false =>
          refine ⟨OK e, 0, ?_⟩
          intro k hk fallback
          cases k with
          | zero => omega
          | succ n => simp [solve_constraints_iter, solve_constraints_F, hrec]
      | true =>
          obtain ⟨v, p, ih⟩ := solve_constraints_terminate T e'
          refine ⟨v, p + 1, ?_⟩
          intro k hk fallback
          cases k with
          | zero => omega
          | succ n =>
              simp [solve_constraints_iter, solve_constraints_F, hrec]
              exact ih n (by omega) fallback
termination_by weight_typenv T e
decreasing_by exact solve_constraints_tcc T e (e', true) e' true rfl rfl hrec

inductive R_solve_constraints (T : TYPE_ALGEBRA) :
    typenv T → res (typenv T) → Type where
  | R_solve_constraints_0 (e e' : typenv T) :
      solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) =
        OK (e', false) →
      R_solve_constraints T e (OK e)
  | R_solve_constraints_1 (e e' : typenv T)
      (h : solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) =
        OK (e', true)) (r : res (typenv T)) :
      R_solve_constraints T e' r →
      R_solve_constraints T e r
  | R_solve_constraints_2 (e : typenv T) (message : errmsg) :
      solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) =
        Error message →
      R_solve_constraints T e (Error message)

abbrev R_solve_constraints_0 := @R_solve_constraints.R_solve_constraints_0
abbrev R_solve_constraints_1 := @R_solve_constraints.R_solve_constraints_1
abbrev R_solve_constraints_2 := @R_solve_constraints.R_solve_constraints_2

noncomputable def R_solve_constraints_rect (T : TYPE_ALGEBRA)
    (P : ∀ (e : typenv T) (r : res (typenv T)),
      R_solve_constraints T e r → Type)
    (hfalse : ∀ (e e' : typenv T)
      (h : solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) =
        OK (e', false)),
      P e (OK e) (R_solve_constraints_0 e e' h))
    (htrue : ∀ (e e' : typenv T)
      (h : solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) =
        OK (e', true)) (r : res (typenv T))
      (graph : R_solve_constraints T e' r),
      P e' r graph → P e r (R_solve_constraints_1 e e' h r graph))
    (herror : ∀ (e : typenv T) (message : errmsg)
      (h : solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) =
        Error message),
      P e (Error message) (R_solve_constraints_2 e message h))
    (e : typenv T) (r : res (typenv T))
    (graph : R_solve_constraints T e r) : P e r graph := by
  induction graph with
  | R_solve_constraints_0 e e' h => exact hfalse e e' h
  | R_solve_constraints_1 e e' h r graph ih => exact htrue e e' h r graph ih
  | R_solve_constraints_2 e message h => exact herror e message h

noncomputable abbrev R_solve_constraints_rec := R_solve_constraints_rect

theorem R_solve_constraints_ind (T : TYPE_ALGEBRA)
    (P : ∀ (e : typenv T) (r : res (typenv T)),
      R_solve_constraints T e r → Prop)
    (hfalse : ∀ (e e' : typenv T)
      (h : solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) =
        OK (e', false)),
      P e (OK e) (R_solve_constraints_0 e e' h))
    (htrue : ∀ (e e' : typenv T)
      (h : solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) =
        OK (e', true)) (r : res (typenv T))
      (graph : R_solve_constraints T e' r),
      P e' r graph → P e r (R_solve_constraints_1 e e' h r graph))
    (herror : ∀ (e : typenv T) (message : errmsg)
      (h : solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) =
        Error message),
      P e (Error message) (R_solve_constraints_2 e message h))
    (e : typenv T) (r : res (typenv T))
    (graph : R_solve_constraints T e r) : P e r graph := by
  induction graph with
  | R_solve_constraints_0 e e' h => exact hfalse e e' h
  | R_solve_constraints_1 e e' h r graph ih => exact htrue e e' h r graph ih
  | R_solve_constraints_2 e message h => exact herror e message h

theorem R_solve_constraints_sind (T : TYPE_ALGEBRA)
    (P : ∀ (e : typenv T) (r : res (typenv T)),
      R_solve_constraints T e r → Prop)
    (hfalse : ∀ (e e' : typenv T)
      (h : solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) =
        OK (e', false)),
      P e (OK e) (R_solve_constraints_0 e e' h))
    (htrue : ∀ (e e' : typenv T)
      (h : solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) =
        OK (e', true)) (r : res (typenv T))
      (graph : R_solve_constraints T e' r),
      P e' r graph → P e r (R_solve_constraints_1 e e' h r graph))
    (herror : ∀ (e : typenv T) (message : errmsg)
      (h : solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) =
        Error message),
      P e (Error message) (R_solve_constraints_2 e message h))
    (e : typenv T) (r : res (typenv T))
    (graph : R_solve_constraints T e r) : P e r graph :=
  R_solve_constraints_ind T P hfalse htrue herror e r graph

noncomputable def solve_constraints_rect (T : TYPE_ALGEBRA)
    (P : typenv T → res (typenv T) → Type)
    (hfalse : ∀ (e e' : typenv T),
      solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) =
        OK (e', false) → P e (OK e))
    (htrue : ∀ (e e' : typenv T),
      solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) =
        OK (e', true) → P e' (solve_constraints T e') →
          P e (solve_constraints T e'))
    (herror : ∀ (e : typenv T) (message : errmsg),
      solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) =
        Error message → P e (Error message))
    (e : typenv T) : P e (solve_constraints T e) := by
  rw [solve_constraints_equation]
  split
  · rename_i e' hrec
    exact htrue e e' hrec (solve_constraints_rect T P hfalse htrue herror e')
  · rename_i e' hrec
    exact hfalse e e' hrec
  · rename_i message hrec
    exact herror e message hrec
termination_by weight_typenv T e
decreasing_by
  rename_i next _hbranch heq
  apply solve_constraints_tcc T e (next, true) next true rfl rfl
  assumption

noncomputable abbrev solve_constraints_rec := solve_constraints_rect

theorem solve_constraints_ind (T : TYPE_ALGEBRA)
    (P : typenv T → res (typenv T) → Prop)
    (hfalse : ∀ (e e' : typenv T),
      solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) =
        OK (e', false) → P e (OK e))
    (htrue : ∀ (e e' : typenv T),
      solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) =
        OK (e', true) → P e' (solve_constraints T e') →
          P e (solve_constraints T e'))
    (herror : ∀ (e : typenv T) (message : errmsg),
      solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) =
        Error message → P e (Error message))
    (e : typenv T) : P e (solve_constraints T e) := by
  rw [solve_constraints_equation]
  split
  · rename_i e' hrec
    exact htrue e e' hrec (solve_constraints_ind T P hfalse htrue herror e')
  · rename_i e' hrec
    exact hfalse e e' hrec
  · rename_i message hrec
    exact herror e message hrec
termination_by weight_typenv T e
decreasing_by
  rename_i next _hbranch heq
  apply solve_constraints_tcc T e (next, true) next true rfl rfl
  assumption

noncomputable def R_solve_constraints_correct (T : TYPE_ALGEBRA) (e : typenv T)
    (r : res (typenv T)) (hresult : r = solve_constraints T e) :
    R_solve_constraints T e r := by
  subst r
  apply solve_constraints_rect T (fun e r => R_solve_constraints T e r)
  · intro e e' hrec
    exact R_solve_constraints_0 e e' hrec
  · intro e e' hrec ih
    exact R_solve_constraints_1 e e' hrec _ ih
  · intro e message hrec
    exact R_solve_constraints_2 e message hrec

theorem R_solve_constraints_complete (T : TYPE_ALGEBRA) (e : typenv T)
    (r : res (typenv T)) (hgraph : R_solve_constraints T e r) :
    r = solve_constraints T e := by
  induction hgraph with
  | R_solve_constraints_0 e e' hrec =>
      rw [solve_constraints_equation, hrec]
  | R_solve_constraints_1 e e' hrec r _ ih =>
      rw [solve_constraints_equation, hrec]
      exact ih
  | R_solve_constraints_2 e message hrec =>
      rw [solve_constraints_equation, hrec]

def solve (e : typenv T) : res (typassign T) :=
  match solve_constraints T e with
  | Error message => Error message
  | OK e' => OK (makeassign T e')

/-! ## Exact statement descriptors for later proofs -/

def move_shapeStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (e : typenv T) (r1 r2 : positive)
    (changed : Bool) (e' : typenv T),
    move T e r1 r2 = OK (changed, e') →
      (te_equ e' = te_equ e ∨ te_equ e' = (r1, r2) :: te_equ e) ∧
        (changed = true → te_equ e' = te_equ e)

def length_moveStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (e : typenv T) (r1 r2 : positive)
    (changed : Bool) (e' : typenv T),
    move T e r1 r2 = OK (changed, e') →
      (te_equ e').length + (if changed then 1 else 0) ≤
        Nat.succ (te_equ e).length

def length_solve_recStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (q : List constraint) (e : typenv T)
    (ch : Bool) (e' : typenv T) (ch' : Bool),
    solve_rec T e ch q = OK (e', ch') →
      (te_equ e').length + (if ch' && negb ch then 1 else 0) ≤
        (te_equ e).length + q.length

def satisf_initialStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (te : typassign T), satisf T te (initial T)

def set_incrStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (te : typassign T) (x : positive) (ty : T.t)
    (e e' : typenv T),
    set T e x ty = OK e' → satisf T te e' → satisf T te e

def set_soundStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (te : typassign T) (x : positive) (ty : T.t)
    (e e' : typenv T),
    set T e x ty = OK e' → satisf T te e' → te x = ty

def set_list_incrStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (te : typassign T) (xl : List positive)
    (tyl : List T.t) (e e' : typenv T),
    set_list T e xl tyl = OK e' → satisf T te e' → satisf T te e

def set_list_soundStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (te : typassign T) (xl : List positive)
    (tyl : List T.t) (e e' : typenv T),
    set_list T e xl tyl = OK e' → satisf T te e' → List.map te xl = tyl

def move_incrStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (te : typassign T) (e : typenv T)
    (r1 r2 : positive) (e' : typenv T) (changed : Bool),
    move T e r1 r2 = OK (changed, e') → satisf T te e' → satisf T te e

def move_soundStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (te : typassign T) (e : typenv T)
    (r1 r2 : positive) (e' : typenv T) (changed : Bool),
    move T e r1 r2 = OK (changed, e') → satisf T te e' → te r1 = te r2

def solve_rec_incrStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (te : typassign T) (q : List constraint)
    (e : typenv T) (changed : Bool) (e' : typenv T) (changed' : Bool),
    solve_rec T e changed q = OK (e', changed') →
      satisf T te e' → satisf T te e

def solve_rec_soundStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (te : typassign T) (r1 r2 : positive)
    (q : List constraint) (e : typenv T) (changed : Bool)
    (e' : typenv T) (changed' : Bool),
    solve_rec T e changed q = OK (e', changed') →
      (r1, r2) ∈ q → satisf T te e' → te r1 = te r2

def move_falseStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (e : typenv T) (r1 r2 : positive) (e' : typenv T),
    move T e r1 r2 = OK (false, e') →
      te_typ e' = te_typ e ∧ makeassign T e r1 = makeassign T e r2

def solve_rec_falseStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (r1 r2 : positive) (q : List constraint)
    (e : typenv T) (changed : Bool) (e' : typenv T),
    solve_rec T e changed q = OK (e', false) →
      changed = false ∧
        ((r1, r2) ∈ q → makeassign T e r1 = makeassign T e r2)

def solve_constraints_incrStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (te : typassign T) (e e' : typenv T),
    solve_constraints T e = OK e' → satisf T te e' → satisf T te e

def solve_constraints_soundStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (e e' : typenv T),
    solve_constraints T e = OK e' → satisf T (makeassign T e') e'

def solve_soundStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (e : typenv T) (te : typassign T),
    solve T e = OK te → satisf T te e

def set_completeStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (te : typassign T) (e : typenv T)
    (x : positive) (ty : T.t),
    satisf T te e → te x = ty →
      ∃ e', set T e x ty = OK e' ∧ satisf T te e'

def set_list_completeStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (te : typassign T) (xl : List positive)
    (tyl : List T.t) (e : typenv T),
    satisf T te e → List.map te xl = tyl →
      ∃ e', set_list T e xl tyl = OK e' ∧ satisf T te e'

def move_completeStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (te : typassign T) (e : typenv T)
    (r1 r2 : positive),
    satisf T te e → te r1 = te r2 →
      ∃ changed e', move T e r1 r2 = OK (changed, e') ∧ satisf T te e'

def solve_rec_completeStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (te : typassign T) (q : List constraint)
    (e : typenv T) (changed : Bool),
    satisf T te e →
      (∀ r1 r2, (r1, r2) ∈ q → te r1 = te r2) →
        ∃ e' changed',
          solve_rec T e changed q = OK (e', changed') ∧ satisf T te e'

def solve_constraints_completeStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (te : typassign T) (e : typenv T),
    satisf T te e → ∃ e', solve_constraints T e = OK e' ∧ satisf T te e'

def solve_completeStatement : Prop :=
  ∀ (T : TYPE_ALGEBRA) (te : typassign T) (e : typenv T),
    satisf T te e → ∃ te', solve T e = OK te'

end UniSolver

end CompCert4Lean.Common.Unityping

namespace CompCert4Lean.Common.Unityping.UniSolver

theorem move_shape : move_shapeStatement := by
  intro T e r1 r2 changed e' h
  unfold move at h
  split at h
  · rcases h with ⟨rfl, rfl⟩
    simp
  · split at h
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨Or.inr rfl, by simp⟩
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨Or.inl rfl, by simp⟩
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨Or.inl rfl, by simp⟩
    · split at h
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨Or.inl rfl, by simp⟩
      · cases h

theorem satisf_initial : satisf_initialStatement := by
  intro T te
  constructor
  · intro x ty h
    change CompCert4Lean.Lib.Maps.PTree.get x
      (CompCert4Lean.Lib.Maps.PTree.empty T.t) = some ty at h
    cases h
  · intro x y h
    change (x, y) ∈ ([] : List constraint) at h
    cases h

theorem set_incr : set_incrStatement := by
  intro T te x ty e e' hset hs
  unfold set at hset
  split at hset
  · rename_i _ hnone
    rcases hset with ⟨rfl, rfl⟩
    rcases hs with ⟨hmap, hconstraints⟩
    have hmap' : ∀ y ty',
        CompCert4Lean.Lib.Maps.PTree.get y
          (CompCert4Lean.Lib.Maps.PTree.set x ty e.te_typ) = some ty' → te y = ty' := hmap
    constructor
    · intro y ty' hy
      by_cases hxy : y = x
      · subst y
        rw [hnone] at hy
        cases hy
      · apply hmap' y ty'
        change CompCert4Lean.Lib.Maps.PTree.get y
          (show CompCert4Lean.Lib.Maps.PTree.tree T.t from e.te_typ) = some ty' at hy
        change CompCert4Lean.Lib.Maps.PTree.get y
          (CompCert4Lean.Lib.Maps.PTree.set x ty
            (show CompCert4Lean.Lib.Maps.PTree.tree T.t from e.te_typ)) = some ty'
        rw [CompCert4Lean.Lib.Maps.PTree.getSet_equation]
        simp only [dif_neg hxy]
        exact hy
    · intro y z hy
      exact hconstraints y z hy
  · rename_i _ ty' hsome
    split at hset
    · rcases hset with ⟨rfl, rfl⟩
      exact hs
    · cases hset

theorem set_sound : set_soundStatement := by
  intro T te x ty e e' hset hs
  unfold set at hset
  split at hset
  · rcases hset with ⟨rfl, rfl⟩
    rcases hs with ⟨hmap, _⟩
    apply hmap x ty
    change CompCert4Lean.Lib.Maps.PTree.get x
      (CompCert4Lean.Lib.Maps.PTree.set x ty
        (show CompCert4Lean.Lib.Maps.PTree.tree T.t from e.te_typ)) = some ty
    simpa using (CompCert4Lean.Lib.Maps.PTree.getSet_equation
      (i := x) (j := x) (x := ty)
      (m := (show CompCert4Lean.Lib.Maps.PTree.tree T.t from e.te_typ)))
  · rename_i _ ty' hsome
    split at hset
    · rename_i hty _
      rcases hset with ⟨rfl, rfl⟩
      rcases hs with ⟨hmap, _⟩
      exact (hmap x ty' hsome).trans hty.symm
    · cases hset

end CompCert4Lean.Common.Unityping.UniSolver

namespace CompCert4Lean.Common.Unityping.UniSolver

open CompCert4Lean.Foundation.Logic
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Common.Errors

private theorem set_list_incr_aux (T : TYPE_ALGEBRA) :
    ∀ (te : typassign T) (xs : List positive) (tys : List T.t)
      (e e' : typenv T),
      set_list T e xs tys = OK e' → satisf T te e' → satisf T te e := by
  intro te xs tys e e' h hs
  induction xs generalizing tys e e' with
  | nil =>
      cases tys with
      | nil =>
          cases h
          exact hs
      | cons ty tys =>
          simp [set_list] at h
  | cons x xs ih =>
      cases tys with
      | nil =>
          simp [set_list] at h
      | cons ty tys =>
          simp only [set_list] at h
          split at h
          · cases h
          · rename_i e1 hset
            have htail := ih (tys := tys) (e := e1) (e' := e') h hs
            exact set_incr T te x ty e e1 hset htail

theorem set_list_incr : set_list_incrStatement := by
  intro T te xs tys e e' h hs
  exact set_list_incr_aux T te xs tys e e' h hs

theorem set_list_sound : set_list_soundStatement := by
  intro T te xs tys e e' h hs
  induction xs generalizing tys e e' with
  | nil =>
      cases tys with
      | nil =>
          simp [set_list] at h
          cases h
          rfl
      | cons ty tys =>
          simp [set_list] at h
  | cons x xs ih =>
      cases tys with
      | nil =>
          simp [set_list] at h
      | cons ty tys =>
          simp only [set_list] at h
          split at h
          · cases h
          · rename_i e1 hset
            change set T e x ty = OK e1 at hset
            have hs1 : satisf T te e1 :=
              set_list_incr_aux T te xs tys e1 e' h hs
            have htail := ih (tys := tys) (e := e1) (e' := e') h hs
            have hx : te x = ty := set_sound T te x ty e e1 hset hs1
            simp only [List.map] at htail ⊢
            rw [hx, htail]

private theorem pget_set_same {A : Type} (i : positive) (v : A) (m : PTree.t A) :
    PTree.get i (PTree.set i v m) = some v := by
  have h := CompCert4Lean.Lib.Maps.PTree.gsspec_proof i i v m
  cases hpeq : peq i i with
  | left hEq => simpa [hpeq] using h
  | right hNe => exact False.elim (hNe rfl)

private theorem pget_set_other {A : Type} (i j : positive) (v : A) (m : PTree.t A)
    (hne : i ≠ j) : PTree.get i (PTree.set j v m) = PTree.get i m := by
  have h := CompCert4Lean.Lib.Maps.PTree.gsspec_proof i j v m
  cases hpeq : peq i j with
  | left hEq => exact False.elim (hne hEq)
  | right hNe => simpa [hpeq] using h

theorem move_incr : move_incrStatement := by
  intro T te e r1 r2 e' changed h hs
  unfold move at h
  cases hp : peq r1 r2 with
  | left hEq =>
      simp [hp] at h
      rcases h with ⟨rfl, rfl⟩
      exact hs
  | right hNe =>
      cases h1 : PTree.get r1 (te_typ e) with
      | none =>
          cases h2 : PTree.get r2 (te_typ e) with
          | none =>
              rw [hp, h1, h2] at h
              cases h
              constructor
              · intro x ty hx
                exact hs.1 x ty hx
              · intro x y hxy
                exact hs.2 x y (List.mem_cons_of_mem _ hxy)
          | some ty2 =>
              rw [hp, h1, h2] at h
              cases h
              constructor
              · intro x ty hx
                by_cases hxr : x = r1
                · subst x
                  rw [h1] at hx
                  cases hx
                · exact hs.1 x ty (by
                    rw [pget_set_other x r1 ty2 (te_typ e) hxr]
                    exact hx)
              · intro x y hxy
                exact hs.2 x y hxy
      | some ty1 =>
          cases h2 : PTree.get r2 (te_typ e) with
          | none =>
              rw [hp, h1, h2] at h
              cases h
              constructor
              · intro x ty hx
                by_cases hxr : x = r2
                · subst x
                  rw [h2] at hx
                  cases hx
                · exact hs.1 x ty (by
                    rw [pget_set_other x r2 ty1 (te_typ e) hxr]
                    exact hx)
              · intro x y hxy
                exact hs.2 x y hxy
          | some ty2 =>
              rw [hp, h1, h2] at h
              cases hEq : T.eq ty1 ty2 with
              | left hty =>
                  simp [hEq] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact hs
              | right hty =>
                  simp [hEq] at h

theorem move_sound : move_soundStatement := by
  intro T te e r1 r2 e' changed h hs
  unfold move at h
  cases hp : peq r1 r2 with
  | left hEq =>
      simp [hp] at h
      cases h
      exact hEq ▸ rfl
  | right hNe =>
      cases h1 : PTree.get r1 (te_typ e) with
      | none =>
          cases h2 : PTree.get r2 (te_typ e) with
          | none =>
              rw [hp, h1, h2] at h
              cases h
              exact hs.2 r1 r2 (List.mem_cons_self)
          | some ty2 =>
              rw [hp, h1, h2] at h
              cases h
              have hu1 := pget_set_same r1 ty2 (te_typ e)
              have hu2 := pget_set_other r2 r1 ty2 (te_typ e) hNe.symm
              have htr1 : te r1 = ty2 := hs.1 r1 ty2 hu1
              have htr2 : te r2 = ty2 := hs.1 r2 ty2 (hu2.trans h2)
              exact htr1.trans htr2.symm
      | some ty1 =>
          cases h2 : PTree.get r2 (te_typ e) with
          | none =>
              rw [hp, h1, h2] at h
              cases h
              have hu1 := pget_set_other r1 r2 ty1 (te_typ e) hNe
              have hu2 := pget_set_same r2 ty1 (te_typ e)
              have htr1 : te r1 = ty1 := hs.1 r1 ty1 (hu1.trans h1)
              have htr2 : te r2 = ty1 := hs.1 r2 ty1 hu2
              exact htr1.trans htr2.symm
          | some ty2 =>
              rw [hp, h1, h2] at h
              cases hEq : T.eq ty1 ty2 with
              | left hty =>
                  simp [hEq] at h
                  have he' : e' = e := h.2.symm
                  subst e'
                  have htr1 := hs.1 r1 ty1 h1
                  have htr2 := hs.1 r2 ty2 h2
                  exact htr1.trans (hty.trans htr2.symm)
              | right hty =>
                  simp [hEq] at h

end CompCert4Lean.Common.Unityping.UniSolver

namespace CompCert4Lean.Common.Unityping.UniSolver

theorem solve_rec_incr : solve_rec_incrStatement := by
  intro T te q e changed e' changed' h hs
  induction q generalizing e changed e' changed' with
  | nil =>
      simp [solve_rec] at h
      rcases h with ⟨rfl, rfl⟩
      exact hs
  | cons a q ih =>
      rcases a with ⟨r1, r2⟩
      simp only [solve_rec] at h
      split at h
      · cases h
      · rename_i changed1 e1 hmove
        have htail := ih (e := e1) (changed := changed || changed1)
          (e' := e') (changed' := changed') h hs
        exact move_incr T te e r1 r2 e1 changed1 hmove htail

end CompCert4Lean.Common.Unityping.UniSolver

namespace CompCert4Lean.Common.Unityping.UniSolver

theorem solve_rec_sound : solve_rec_soundStatement := by
  intro T te r1 r2 q e changed e' changed' h hmem hs
  induction q generalizing e changed e' changed' with
  | nil =>
      cases hmem
  | cons a q ih =>
      rcases a with ⟨r3, r4⟩
      simp only [solve_rec] at h
      split at h
      · cases h
      · rename_i changed1 e1 hmove
        have hs1 : satisf T te e1 :=
          solve_rec_incr T te q e1 (changed || changed1) e' changed' h hs
        cases hmem with
        | head =>
          exact move_sound T te e r1 r2 e1 changed1 hmove hs1
        | tail =>
          exact ih (e := e1) (changed := changed || changed1)
            (e' := e') (changed' := changed') h (by assumption) hs

end CompCert4Lean.Common.Unityping.UniSolver

namespace CompCert4Lean.Common.Unityping.UniSolver

open CompCert4Lean.Foundation.Logic
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Common.Errors

theorem move_false : move_falseStatement := by
  intro T e r1 r2 e' h
  unfold move at h
  cases hp : peq r1 r2 with
  | left hEq =>
      simp [hp] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨rfl, by simp [makeassign, hEq]⟩
  | right hNe =>
      cases h1 : PTree.get r1 (te_typ e) with
      | none =>
          cases h2 : PTree.get r2 (te_typ e) with
          | none =>
              rw [hp, h1, h2] at h
              rcases h with ⟨rfl, rfl⟩
              exact ⟨rfl, by simp [makeassign, h1, h2]⟩
          | some ty2 =>
              rw [hp, h1, h2] at h
              cases h
      | some ty1 =>
          cases h2 : PTree.get r2 (te_typ e) with
          | none =>
              rw [hp, h1, h2] at h
              cases h
          | some ty2 =>
              rw [hp, h1, h2] at h
              cases hEq : T.eq ty1 ty2 with
              | left hty =>
                  simp [hEq] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact ⟨rfl, by simp [makeassign, h1, h2, hty]⟩
              | right hty =>
                  simp [hEq] at h

end CompCert4Lean.Common.Unityping.UniSolver

namespace CompCert4Lean.Common.Unityping.UniSolver

open CompCert4Lean.Common.Errors

private theorem solve_constraints_incr_aux :
    ∀ (T : TYPE_ALGEBRA) (te : typassign T) (e e' : typenv T),
      solve_constraints T e = OK e' → satisf T te e' → satisf T te e := by
  intro T te e e' h hs
  let P : typenv T → res (typenv T) → Prop := fun e r =>
    ∀ e', r = OK e' → satisf T te e' → satisf T te e
  have hind :=
    solve_constraints_ind T P
      (by
        intro e e' hrec e'' heq hs'
        cases heq
        exact hs')
      (by
        intro e e' hrec ih e'' heq hs'
        have hsbase := ih e'' heq hs'
        have hsorig : satisf T te e := by
          have hs0 := solve_rec_incr T te (te_equ e)
            { te_typ := te_typ e, te_equ := [] } false e' true hrec hsbase
          constructor
          · intro x ty hx
            exact hs0.1 x ty hx
          · intro x y hxy
            exact solve_rec_sound T te x y (te_equ e)
              { te_typ := te_typ e, te_equ := [] } false e' true hrec hxy hsbase
        exact hsorig)
      (by
        intro e message hrec e'' heq hs'
        cases heq)
      e
  exact hind e' h hs

theorem solve_constraints_incr : solve_constraints_incrStatement := by
  intro T te e e' h hs
  exact solve_constraints_incr_aux T te e e' h hs

end CompCert4Lean.Common.Unityping.UniSolver

namespace CompCert4Lean.Common.Unityping.UniSolver

open CompCert4Lean.Foundation.Logic
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Init.Datatypes
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Common.Errors

private theorem solve_rec_false_aux (T : TYPE_ALGEBRA) :
    ∀ (r1 r2 : positive) (q : List constraint)
      (e : typenv T) (changed : Bool) (e' : typenv T),
      solve_rec T e changed q = OK (e', false) →
      changed = false ∧
        ((r1, r2) ∈ q →
          makeassign T e r1 = makeassign T e r2) := by
  intro r1 r2 q
  induction q with
  | nil =>
      intro e changed e' h
      simp only [solve_rec] at h
      cases changed with
      | false =>
          rcases h with ⟨rfl, rfl⟩
          exact ⟨rfl, by intro hmem; cases hmem⟩
      | true =>
          cases h
  | cons a q ih =>
      rcases a with ⟨a1, a2⟩
      intro e changed e' h
      simp only [solve_rec] at h
      split at h
      · cases h
      · rename_i changed1 e1 hmove
        have htail := ih e1 (changed || changed1) e' h
        rcases htail with ⟨hchanged, hmem⟩
        have hc : changed = false := by
          cases changed <;> cases changed1 <;> simp_all
        have hc1 : changed1 = false := by
          cases changed <;> cases changed1 <;> simp_all
        subst changed
        subst changed1
        have hmf := move_false T e a1 a2 e1 hmove
        constructor
        · rfl
        · intro hmem'
          cases hmem' with
          | head =>
            exact hmf.2
          | tail =>
            have hEq := hmem (by assumption)
            unfold makeassign at hEq ⊢
            rw [hmf.1] at hEq
            exact hEq

theorem solve_constraints_sound : solve_constraints_soundStatement := by
  intro T e e' h
  let P : typenv T → res (typenv T) → Prop := fun _ r =>
    ∀ e', r = OK e' → satisf T (makeassign T e') e'
  have hind :=
    solve_constraints_ind T P
      (by
        intro e e' hrec e'' heq
        cases heq
        constructor
        · intro x ty hx
          simp [makeassign, hx]
        · intro x y hxy
          have hf := solve_rec_false_aux T x y (te_equ e)
            { te_typ := te_typ e, te_equ := [] } false e' hrec
          have heq' := hf.2 hxy
          simpa [makeassign] using heq')
      (by
        intro e e' hrec ih e'' heq
        exact ih e'' heq)
      (by
        intro e message hrec e' heq
        cases heq)
      e
  exact hind e' h

end CompCert4Lean.Common.Unityping.UniSolver

namespace CompCert4Lean.Common.Unityping.UniSolver

theorem solve_sound : solve_soundStatement := by
  intro T e te h
  unfold solve at h
  cases hc : solve_constraints T e with
  | Error message =>
      simp [hc] at h
  | OK e' =>
      simp [hc] at h
      cases h
      exact solve_constraints_incr T (makeassign T e') e e' hc
        (solve_constraints_sound T e e' hc)

end CompCert4Lean.Common.Unityping.UniSolver

namespace CompCert4Lean.Common.Unityping.UniSolver

open CompCert4Lean.Lib.Maps

theorem set_complete : set_completeStatement := by
  intro T te e x ty hs htx
  unfold set
  split
  · rename_i hnone
    refine ⟨{ te_typ := PTree.set x ty (te_typ e), te_equ := te_equ e }, ?_, ?_⟩
    · simp [hnone]
    · constructor
      · intro y ty' hy
        by_cases hxy : y = x
        · subst y
          have hget : PTree.get x (PTree.set x ty (te_typ e)) = some ty :=
            PTree.gss x ty (te_typ e)
          rw [hget] at hy
          cases hy
          exact htx
        · have hget := PTree.gso (i := y) (j := x) (x := ty) (m := te_typ e) hxy
          rw [hget] at hy
          exact hs.1 y ty' hy
      · intro y z hy
        exact hs.2 y z hy
  · rename_i ty' hsome
    split
    · rename_i heq
      subst ty'
      refine ⟨e, ?_, hs⟩
      simp [hsome, heq]
    · cases hs with
      | intro hmap hconstraints =>
          have hty' : te x = ty' := hmap x ty' hsome
          exfalso
          exact ‹ty ≠ ty'› (htx.symm.trans hty')

end CompCert4Lean.Common.Unityping.UniSolver

namespace CompCert4Lean.Common.Unityping.UniSolver

theorem set_list_complete : set_list_completeStatement := by
  intro T te xl tyl e hs hmap
  induction xl generalizing tyl e with
  | nil =>
      cases tyl with
      | nil =>
          refine ⟨e, ?_, hs⟩
          rfl
      | cons ty tys =>
          cases hmap
  | cons x xs ih =>
      cases tyl with
      | nil =>
          cases hmap
      | cons ty tys =>
          cases hmap
          obtain ⟨e1, hset, hs1⟩ := set_complete T te e x (te x) hs rfl
          obtain ⟨e2, htail, hs2⟩ := ih (tyl := List.map te xs) (e := e1) hs1 rfl
          refine ⟨e2, ?_, hs2⟩
          simp only [set_list]
          rw [hset]
          exact htail

end CompCert4Lean.Common.Unityping.UniSolver

namespace CompCert4Lean.Common.Unityping.UniSolver

open CompCert4Lean.Lib.Coqlib

theorem move_complete : move_completeStatement := by
  intro T te e r1 r2 hs hte
  unfold move
  cases hp : peq r1 r2 with
  | left hEq =>
      simp only
      exact ⟨false, e, rfl, hs⟩
  | right hNe =>
      cases h1 : CompCert4Lean.Lib.Maps.PTree.get r1
          (show CompCert4Lean.Lib.Maps.PTree.tree T.t from te_typ e) with
      | none =>
          cases h2 : CompCert4Lean.Lib.Maps.PTree.get r2
              (show CompCert4Lean.Lib.Maps.PTree.tree T.t from te_typ e) with
          | none =>
              simp only
              refine ⟨false, { te_typ := te_typ e, te_equ := (r1, r2) :: te_equ e }, rfl, ?_⟩
              exact ⟨hs.1, fun x y hxy => by
                cases hxy with
                | head => exact hte
                | tail => exact hs.2 x y (by assumption)⟩
          | some ty2 =>
              simp only
              have htx : te r1 = ty2 := hte.trans (hs.1 r2 ty2 h2)
              obtain ⟨e', hset, hs'⟩ := set_complete T te e r1 ty2 hs htx
              have hset' := hset
              simp [set, h1] at hset'
              cases hset'
              exact ⟨true, _, rfl, hs'⟩
      | some ty1 =>
          cases h2 : CompCert4Lean.Lib.Maps.PTree.get r2
              (show CompCert4Lean.Lib.Maps.PTree.tree T.t from te_typ e) with
          | none =>
              simp only
              have htx : te r2 = ty1 := hte.symm.trans (hs.1 r1 ty1 h1)
              obtain ⟨e', hset, hs'⟩ := set_complete T te e r2 ty1 hs htx
              have hset' := hset
              simp [set, h2] at hset'
              cases hset'
              exact ⟨true, _, rfl, hs'⟩
          | some ty2 =>
              cases heq : T.eq ty1 ty2 with
              | left hty =>
                  simp only
                  rw [heq]
                  exact ⟨false, e, rfl, hs⟩
              | right hty =>
                  exfalso
                  apply hty
                  exact (hs.1 r1 ty1 h1).symm.trans (hte.trans (hs.1 r2 ty2 h2))

end CompCert4Lean.Common.Unityping.UniSolver

namespace CompCert4Lean.Common.Unityping.UniSolver

theorem solve_rec_complete : solve_rec_completeStatement := by
  intro T te q e changed hs hq
  induction q generalizing e changed with
  | nil =>
      exact ⟨e, changed, rfl, hs⟩
  | cons a q ih =>
      rcases a with ⟨r1, r2⟩
      have hpair : te r1 = te r2 := hq r1 r2 (List.mem_cons_self)
      obtain ⟨changed1, e1, hmove, hs1⟩ :=
        move_complete T te e r1 r2 hs hpair
      have hq' : ∀ a b, (a, b) ∈ q → te a = te b := by
        intro a b hab
        exact hq a b (List.mem_cons_of_mem _ hab)
      obtain ⟨e', changed', hrec, hs'⟩ :=
        ih (e := e1) (changed := changed || changed1) hs1 hq'
      refine ⟨e', changed', ?_, hs'⟩
      simp only [solve_rec]
      rw [hmove]
      exact hrec

end CompCert4Lean.Common.Unityping.UniSolver

namespace CompCert4Lean.Common.Unityping.UniSolver

open CompCert4Lean.Common.Errors

theorem solve_constraints_complete : solve_constraints_completeStatement := by
  intro T te e hs
  let P : typenv T → res (typenv T) → Prop := fun e r =>
    satisf T te e → ∃ e', r = OK e' ∧ satisf T te e'
  have hind := solve_constraints_ind T P
    (by
      intro e e' hrec
      change satisf T te e → ∃ e'', OK e = OK e'' ∧ satisf T te e''
      intro hs'
      exact ⟨e, rfl, hs'⟩)
    (by
      intro e e' hrec ih
      change satisf T te e → ∃ e'', solve_constraints T e' = OK e'' ∧ satisf T te e''
      intro hs'
      have hs0 : satisf T te { te_typ := te_typ e, te_equ := [] } := by
        constructor
        · intro x ty hx
          exact hs'.1 x ty hx
        · intro x y hxy
          cases hxy
      have hq0 : ∀ r1 r2, (r1, r2) ∈ te_equ e → te r1 = te r2 := by
        intro r1 r2 hmem
        exact hs'.2 r1 r2 hmem
      obtain ⟨e1, changed1, hcomp, hs1⟩ :=
        solve_rec_complete T te (te_equ e)
          { te_typ := te_typ e, te_equ := [] } false hs0 hq0
      have hpair : (e1, changed1) = (e', true) := by
        have hok : OK (e1, changed1) = (OK (e', true) : res (typenv T × Bool)) :=
          hcomp.symm.trans hrec
        cases hok
        rfl
      cases hpair
      exact ih hs1)
    (by
      intro e message hrec
      change satisf T te e → ∃ e'', Error message = OK e'' ∧ satisf T te e''
      intro hs'
      have hs0 : satisf T te { te_typ := te_typ e, te_equ := [] } := by
        constructor
        · intro x ty hx
          exact hs'.1 x ty hx
        · intro x y hxy
          cases hxy
      have hq0 : ∀ r1 r2, (r1, r2) ∈ te_equ e → te r1 = te r2 := by
        intro r1 r2 hmem
        exact hs'.2 r1 r2 hmem
      obtain ⟨e1, changed1, hcomp, hs1⟩ :=
        solve_rec_complete T te (te_equ e)
          { te_typ := te_typ e, te_equ := [] } false hs0 hq0
      have herr : (OK (e1, changed1) : res (typenv T × Bool)) = Error message :=
        hcomp.symm.trans hrec
      cases herr)
    e
  exact hind hs

end CompCert4Lean.Common.Unityping.UniSolver

namespace CompCert4Lean.Common.Unityping.UniSolver

theorem solve_complete : solve_completeStatement := by
  intro T te e hs
  obtain ⟨e', hsolve, _hs'⟩ := solve_constraints_complete T te e hs
  refine ⟨makeassign T e', ?_⟩
  simp [solve, hsolve]

end CompCert4Lean.Common.Unityping.UniSolver

namespace CompCert4Lean.Common.Unityping.UniSolver

theorem solve_rec_false : solve_rec_falseStatement := by
  exact solve_rec_false_aux

end CompCert4Lean.Common.Unityping.UniSolver
