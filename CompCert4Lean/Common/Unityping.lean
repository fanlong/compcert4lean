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

/-! Source record projections are flattened into the module namespace. -/

def te_typ {T : TYPE_ALGEBRA} (e : typenv T) : PTree.t T.t := e.te_typ
def te_equ {T : TYPE_ALGEBRA} (e : typenv T) : List constraint := e.te_equ

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

/-!
The source uses a measure-recursive fixpoint.  This checked implementation
uses the same one-pass iteration and a structurally recursive fuel argument;
the fuel is the number of pending equality constraints plus one.
-/

private def solve_constraints_fuel : Nat → typenv T → res (typenv T)
  | 0, e => OK e
  | fuel + 1, e =>
      match solve_rec T { te_typ := te_typ e, te_equ := [] } false (te_equ e) with
      | Error message => Error message
      | OK (e', false) => OK e
      | OK (e', true) => solve_constraints_fuel fuel e'

def solve_constraints (e : typenv T) : res (typenv T) :=
  solve_constraints_fuel T ((te_equ e).length + 1) e

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
