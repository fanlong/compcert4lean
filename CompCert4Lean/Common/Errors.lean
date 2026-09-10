import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.RocqString
import CompCert4Lean.Lib.Coqlib

/-!
# Error reporting and the error monad

This module translates the definition-bearing surface of CompCert's
`common/Errors.v`.  The three source proofs are retained as exact proposition
descriptors for the later proof-migration phase.
-/

namespace CompCert4Lean.Common.Errors

universe u v w

/-! ## Representation of error messages -/

inductive errcode : Type where
  | MSG (s : _root_.CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string)
  | CTX (p : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
  | POS (p : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)

export errcode (MSG CTX POS)

def errmsg : Type := List errcode

def msg
    (s : _root_.CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string) :
    errmsg := MSG s :: []

/-! ## The error monad -/

inductive res (A : Type u) : Type u where
  | OK (value : A)
  | Error (message : errmsg)

export res (OK Error)

def bind {A : Type u} {B : Type v} (f : res A) (g : A → res B) : res B :=
  match f with
  | OK x => g x
  | Error message => Error message

def bind2 {A : Type u} {B : Type v} {C : Type w}
    (f : res (A × B)) (g : A → B → res C) : res C :=
  match f with
  | OK (x, y) => g x y
  | Error message => Error message

/-! The source's `error_monad_scope` notation is represented by the
definition-level `bind` and `bind2` operations above. -/

def bind_inversionStatement : Prop :=
  ∀ (A : Type u) (B : Type v) (f : res A) (g : A → res B) (y : B),
    bind f g = OK y → ∃ x, f = OK x ∧ g x = OK y

def bind2_inversionStatement : Prop :=
  ∀ (A : Type u) (B : Type v) (C : Type w) (f : res (A × B))
      (g : A → B → res C) (z : C),
    bind2 f g = OK z →
      ∃ x, ∃ y, f = OK (x, y) ∧ g x y = OK z

/-! ## Assertions -/

private def bytesToString :
    List UInt8 →
      _root_.CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string
  | [] => .EmptyString
  | byte :: tail => .String byte (bytesToString tail)

private def assertionFailedText :
    _root_.CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string :=
  bytesToString [65, 115, 115, 101, 114, 116, 105, 111, 110, 32, 102, 97, 105,
    108, 101, 100]

def assertion_failed {A : Type u} : res A := Error (msg assertionFailedText)

/-! ## Monadic map -/

def mmap {A : Type u} {B : Type v} (f : A → res B) : List A → res (List B)
  | [] => OK []
  | head :: tail =>
      match f head with
      | Error message => Error message
      | OK head' =>
          match mmap f tail with
          | Error message => Error message
          | OK tail' => OK (head' :: tail')

def mmap_inversionStatement : Prop :=
  ∀ (A : Type u) (B : Type v) (f : A → res B) (l : List A) (l' : List B),
    mmap f l = OK l' →
      _root_.CompCert4Lean.Lib.Coqlib.list_forall2
        (fun x y => f x = OK y) l l'

end CompCert4Lean.Common.Errors

namespace CompCert4Lean.Common.Errors

theorem bind_inversion : bind_inversionStatement := by
  intro A B f g y h
  cases f with
  | OK x => exact ⟨x, rfl, h⟩
  | Error message => cases h

theorem bind2_inversion : bind2_inversionStatement := by
  intro A B C f g z h
  cases f with
  | OK pair =>
      cases pair with
      | mk x y => exact ⟨x, y, rfl, h⟩
  | Error message => cases h

theorem mmap_inversion : mmap_inversionStatement := by
  intro A B f l
  induction l with
  | nil =>
      intro l' h
      cases h
      exact _root_.CompCert4Lean.Lib.Coqlib.list_forall2.nil _
  | cons head tail ih =>
      intro l' h
      cases hhead : f head with
      | Error message => simp [mmap, hhead] at h
      | OK head' =>
          cases htail : mmap f tail with
          | Error message => simp [mmap, hhead, htail] at h
          | OK tail' =>
              simp only [mmap, hhead, htail] at h
              cases h
              exact _root_.CompCert4Lean.Lib.Coqlib.list_forall2.cons head head' hhead (ih tail' htail)

end CompCert4Lean.Common.Errors
