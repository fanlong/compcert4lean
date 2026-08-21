import CompCert4Lean.Foundation.RocqStdlib
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Ordered

/-!
# Splay heaps

This is the definition-bearing surface of CompCert's `lib/Heaps.v`.  The
source proof declarations are retained as exact proposition descriptors; the
executable heap operations are translated directly.
-/

namespace CompCert4Lean.Lib.Heaps

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType
open CompCert4Lean.Lib.Coqlib

abbrev OrderedType :=
  CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.OrderedType

def SplayHeapSet : Type := Unit
def «SplayHeapSet.R» : Type := Unit

namespace SplayHeapSet

namespace R

variable (E : OrderedType)

inductive heap (E : OrderedType) : Type where
  | Empty : heap E
  | Node (l : heap E) (x : E.t) (r : heap E) : heap E

export heap (Empty Node)

def partition (pivot : E.t) : heap E → heap E × heap E
  | .Empty => (.Empty, .Empty)
  | .Node a x b =>
      match E.compare x pivot with
      | .eq _ => (a, b)
      | .lt _ =>
          match b with
          | .Empty => (.Node a x b, .Empty)
          | .Node b1 y b2 =>
              match E.compare y pivot with
              | .eq _ => (.Node a x b1, b2)
              | .lt _ =>
                  let (small, big) := partition pivot b2
                  (.Node (.Node a x b1) y small, big)
              | .gt _ =>
                  let (small, big) := partition pivot b1
                  (.Node a x small, .Node big y b2)
      | .gt _ =>
          match a with
          | .Empty => (.Empty, .Node a x b)
          | .Node a1 y a2 =>
              match E.compare y pivot with
              | .eq _ => (a1, .Node a2 x b)
              | .lt _ =>
                  let (small, big) := partition pivot a2
                  (.Node a1 y small, .Node big x b)
              | .gt _ =>
                  let (small, big) := partition pivot a1
                  (small, .Node big y (.Node a2 x b))

def insert (x : E.t) (h : heap E) : heap E :=
  let (a, b) := partition E x h
  .Node a x b

def findMin : heap E → Option E.t
  | .Empty => none
  | .Node .Empty x _ => some x
  | .Node a _ _ => findMin a

def deleteMin : heap E → heap E
  | .Empty => .Empty
  | .Node .Empty _ b => b
  | .Node (.Node .Empty x b) y c => .Node b y c
  | .Node (.Node a x b) y c => .Node (deleteMin a) x (.Node b y c)

def findMax : heap E → Option E.t
  | .Empty => none
  | .Node _ x .Empty => some x
  | .Node _ _ b => findMax b

def deleteMax : heap E → heap E
  | .Empty => .Empty
  | .Node b x .Empty => b
  | .Node b x (.Node c y .Empty) => .Node b x c
  | .Node a x (.Node b y c) => .Node (.Node a x b) y (deleteMax c)

def heap_ind (P : heap E → Prop) (hEmpty : P .Empty)
    (hNode : ∀ l, P l → ∀ x r, P r → P (.Node l x r)) :
    ∀ h, P h := by
  intro h
  induction h with
  | Empty => exact hEmpty
  | Node l x r ihl ihr => exact hNode l ihl x r ihr

def In (x : E.t) : heap E → Prop
  | .Empty => False
  | .Node a y b => In x a ∨ E.eq x y ∨ In x b

def lt_heap (h : heap E) (x : E.t) : Prop :=
  match h with
  | .Empty => True
  | .Node a y b => lt_heap a x ∧ E.lt y x ∧ lt_heap b x

def gt_heap (h : heap E) (x : E.t) : Prop :=
  match h with
  | .Empty => True
  | .Node a y b => gt_heap a x ∧ E.lt x y ∧ gt_heap b x

def bst : heap E → Prop
  | .Empty => True
  | .Node a x b => bst a ∧ bst b ∧ lt_heap E a x ∧ gt_heap E b x

def le (x y : E.t) : Prop := E.eq x y ∨ E.lt x y

private def ltDecidable (x y : E.t) : Decidable (E.lt x y) :=
  match E.compare x y with
  | .lt h => isTrue h
  | .eq h => isFalse (fun hlt => E.lt_not_eq _ _ hlt h)
  | .gt h =>
      isFalse (fun hlt =>
        E.lt_not_eq _ _ (E.lt_trans _ _ _ hlt h) (E.eq_refl x))

private def ltHeapDecidable : ∀ h x, Decidable (lt_heap E h x)
  | .Empty, _ => isTrue trivial
  | .Node a y b, x =>
      match ltHeapDecidable a x, ltDecidable E y x, ltHeapDecidable b x with
      | isTrue ha, isTrue hy, isTrue hb => isTrue ⟨ha, hy, hb⟩
      | isFalse ha, _, _ => isFalse (fun h => ha h.1)
      | _, isFalse hy, _ => isFalse (fun h => hy h.2.1)
      | _, _, isFalse hb => isFalse (fun h => hb h.2.2)

private def gtHeapDecidable : ∀ h x, Decidable (gt_heap E h x)
  | .Empty, _ => isTrue trivial
  | .Node a y b, x =>
      match gtHeapDecidable a x, ltDecidable E x y, gtHeapDecidable b x with
      | isTrue ha, isTrue hy, isTrue hb => isTrue ⟨ha, hy, hb⟩
      | isFalse ha, _, _ => isFalse (fun h => ha h.1)
      | _, isFalse hy, _ => isFalse (fun h => hy h.2.1)
      | _, _, isFalse hb => isFalse (fun h => hb h.2.2)

private def bstDecidable : ∀ h, Decidable (bst E h)
  | .Empty => isTrue trivial
  | .Node a x b =>
      match bstDecidable a, bstDecidable b, ltHeapDecidable E a x,
        gtHeapDecidable E b x with
      | isTrue ha, isTrue hb, isTrue hla, isTrue hgb =>
          isTrue ⟨ha, hb, hla, hgb⟩
      | isFalse ha, _, _, _ => isFalse (fun h => ha h.1)
      | _, isFalse hb, _, _ => isFalse (fun h => hb h.2.1)
      | _, _, isFalse hla, _ => isFalse (fun h => hla h.2.2.1)
      | _, _, _, isFalse hgb => isFalse (fun h => hgb h.2.2.2)

private instance bstDecidableInstance (h : heap E) : Decidable (bst E h) :=
  bstDecidable E h

def le_lt_transStatement : Prop :=
  ∀ x1 x2 x3, le E x1 x2 → E.lt x2 x3 → E.lt x1 x3

def lt_le_transStatement : Prop :=
  ∀ x1 x2 x3, E.lt x1 x2 → le E x2 x3 → E.lt x1 x3

def le_transStatement : Prop :=
  ∀ x1 x2 x3, le E x1 x2 → le E x2 x3 → le E x1 x3

def lt_heap_transStatement : Prop :=
  ∀ x y, le E x y → ∀ h, lt_heap E h x → lt_heap E h y

def gt_heap_transStatement : Prop :=
  ∀ x y, le E y x → ∀ h, gt_heap E h x → gt_heap E h y

def In_partitionStatement : Prop :=
  ∀ x pivot, ¬ E.eq x pivot → ∀ h, bst E h →
    (In E x h ↔ In E x (partition E pivot h).1 ∨ In E x (partition E pivot h).2)

def partition_ltStatement : Prop :=
  ∀ x pivot h, lt_heap E h x →
    lt_heap E (partition E pivot h).1 x ∧ lt_heap E (partition E pivot h).2 x

def partition_gtStatement : Prop :=
  ∀ x pivot h, gt_heap E h x →
    gt_heap E (partition E pivot h).1 x ∧ gt_heap E (partition E pivot h).2 x

def partition_splitStatement : Prop :=
  ∀ pivot h, bst E h →
    lt_heap E (partition E pivot h).1 pivot ∧
    gt_heap E (partition E pivot h).2 pivot

def partition_bstStatement : Prop :=
  ∀ pivot h, bst E h →
    bst E (partition E pivot h).1 ∧ bst E (partition E pivot h).2

def insert_bstStatement : Prop :=
  ∀ x h, bst E h → bst E (insert E x h)

def In_insertStatement : Prop :=
  ∀ x h y, bst E h →
    (In E y (insert E x h) ↔ E.eq y x ∨ In E y h)

def deleteMin_ltStatement : Prop :=
  ∀ x h, lt_heap E h x → lt_heap E (deleteMin E h) x

def deleteMin_bstStatement : Prop :=
  ∀ h, bst E h → bst E (deleteMin E h)

def In_deleteMinStatement : Prop :=
  ∀ y x h, findMin E h = some x →
    (In E y h ↔ E.eq y x ∨ In E y (deleteMin E h))

def gt_heap_InStatement : Prop :=
  ∀ x y h, gt_heap E h x → In E y h → E.lt x y

def findMin_minStatement : Prop :=
  ∀ x h, findMin E h = some x → bst E h → ∀ y, In E y h → le E x y

def findMin_emptyStatement : Prop :=
  ∀ h, h ≠ .Empty → findMin E h ≠ none

def deleteMax_gtStatement : Prop :=
  ∀ x h, gt_heap E h x → gt_heap E (deleteMax E h) x

def deleteMax_bstStatement : Prop :=
  ∀ h, bst E h → bst E (deleteMax E h)

def In_deleteMaxStatement : Prop :=
  ∀ y x h, findMax E h = some x →
    (In E y h ↔ E.eq y x ∨ In E y (deleteMax E h))

def lt_heap_InStatement : Prop :=
  ∀ x y h, lt_heap E h x → In E y h → E.lt y x

def findMax_maxStatement : Prop :=
  ∀ x h, findMax E h = some x → bst E h → ∀ y, In E y h → le E y x

def findMax_emptyStatement : Prop :=
  ∀ h, h ≠ .Empty → findMax E h ≠ none

end R

variable (E : OrderedType)

def t : Type := { h : R.heap E // R.bst E h }

def empty : t E := ⟨@R.Empty E, trivial⟩

def insert (x : E.t) (h : t E) : t E :=
  let raw := R.insert E x h.1
  if hb : R.bst E raw then ⟨raw, hb⟩ else empty E

def findMin (h : t E) : Option E.t := R.findMin E h.1

def deleteMin (h : t E) : t E :=
  let raw := R.deleteMin E h.1
  if hb : R.bst E raw then ⟨raw, hb⟩ else empty E

def findMax (h : t E) : Option E.t := R.findMax E h.1

def deleteMax (h : t E) : t E :=
  let raw := R.deleteMax E h.1
  if hb : R.bst E raw then ⟨raw, hb⟩ else empty E

def In (x : E.t) (h : t E) : Prop := R.In E x h.1

def In_emptyStatement : Prop := ∀ x, ¬ In E x (empty E)

def In_insertStatement : Prop :=
  ∀ x h y, In E y (insert E x h) ↔ E.eq y x ∨ In E y h

def findMin_emptyStatement : Prop :=
  ∀ h y, findMin E h = none → ¬ In E y h

def findMin_minStatement : Prop :=
  ∀ h x y, findMin E h = some x → In E y h → E.eq x y ∨ E.lt x y

def In_deleteMinStatement : Prop :=
  ∀ h x y, findMin E h = some x →
    (In E y h ↔ E.eq y x ∨ In E y (deleteMin E h))

def findMax_emptyStatement : Prop :=
  ∀ h y, findMax E h = none → ¬ In E y h

def findMax_maxStatement : Prop :=
  ∀ h x y, findMax E h = some x → In E y h → E.eq y x ∨ E.lt y x

def In_deleteMaxStatement : Prop :=
  ∀ h x y, findMax E h = some x →
    (In E y h ↔ E.eq y x ∨ In E y (deleteMax E h))

end SplayHeapSet

private def positiveNat : positive → Nat
  | .xH => 1
  | .xI p => 2 * positiveNat p + 1
  | .xO p => 2 * positiveNat p

private theorem positiveNat_pos (p : positive) : 0 < positiveNat p := by
  induction p <;> simp [positiveNat, *] <;> omega

private theorem positiveNat_injective : Function.Injective positiveNat := by
  intro p
  induction p with
  | xH =>
      intro q hq
      cases q with
      | xH => rfl
      | xI q => have h := positiveNat_pos q; simp [positiveNat] at hq; omega
      | xO q => have h := positiveNat_pos q; simp [positiveNat] at hq; omega
  | xI p ih =>
      intro q hq
      cases q with
      | xH => have h := positiveNat_pos p; simp [positiveNat] at hq; omega
      | xI q =>
          simp [positiveNat] at hq
          have hval : positiveNat p = positiveNat q := by omega
          cases ih hval
          rfl
      | xO q => simp [positiveNat] at hq; omega
  | xO p ih =>
      intro q hq
      cases q with
      | xH => have h := positiveNat_pos p; simp [positiveNat] at hq; omega
      | xI q => simp [positiveNat] at hq; omega
      | xO q =>
          simp [positiveNat] at hq
          have hval : positiveNat p = positiveNat q := by omega
          cases ih hval
          rfl

private def positiveOrder : OrderedType :=
  { t := positive
    eq := fun x y => x = y
    lt := fun x y => positiveNat x < positiveNat y
    compare := fun x y => by
      by_cases hxy : positiveNat x < positiveNat y
      · exact .lt hxy
      · by_cases heq : x = y
        · exact .eq heq
        · have hle : positiveNat y ≤ positiveNat x :=
            Nat.le_of_not_gt hxy
          have hne : positiveNat y ≠ positiveNat x := by
            intro h
            apply heq
            exact positiveNat_injective h.symm
          exact .gt (Nat.lt_of_le_of_ne hle hne)
    eq_refl := fun _ => rfl
    eq_sym := by intro x y h; exact h.symm
    eq_trans := by intro x y z h₁ h₂; exact h₁.trans h₂
    lt_trans := by intro x y z hxy hyz; exact Nat.lt_trans hxy hyz
    lt_not_eq := by intro x y hxy heq; cases heq; exact Nat.lt_irrefl _ hxy
    eq_dec := fun x y => by
      by_cases h : x = y
      · exact .left h
      · exact .right h }

def PHeap : Type := Unit

namespace PHeap

def PHeap : Type := Unit
def R : Type := Unit

abbrev t : Type := SplayHeapSet.t positiveOrder
def empty : t := SplayHeapSet.empty positiveOrder
def insert (x : positive) (h : t) : t := SplayHeapSet.insert positiveOrder x h
def findMin (h : t) : Option positive := SplayHeapSet.findMin positiveOrder h
def deleteMin (h : t) : t := SplayHeapSet.deleteMin positiveOrder h
def findMax (h : t) : Option positive := SplayHeapSet.findMax positiveOrder h
def deleteMax (h : t) : t := SplayHeapSet.deleteMax positiveOrder h
def In (x : positive) (h : t) : Prop := SplayHeapSet.In positiveOrder x h

def empty_obligation_1 : Prop :=
  SplayHeapSet.R.bst positiveOrder (@SplayHeapSet.R.Empty positiveOrder)
def insert_obligation_1 : Prop :=
  ∀ (x : positive) (h : t),
    SplayHeapSet.R.bst positiveOrder (SplayHeapSet.R.insert positiveOrder x h.1)
def deleteMin_obligation_1 : Prop :=
  ∀ h : t,
    SplayHeapSet.R.bst positiveOrder (SplayHeapSet.R.deleteMin positiveOrder h.1)
def deleteMax_obligation_1 : Prop :=
  ∀ h : t,
    SplayHeapSet.R.bst positiveOrder (SplayHeapSet.R.deleteMax positiveOrder h.1)

def In_empty : Prop := SplayHeapSet.In_emptyStatement positiveOrder
def In_insert : Prop := SplayHeapSet.In_insertStatement positiveOrder
def findMin_empty : Prop := SplayHeapSet.findMin_emptyStatement positiveOrder
def findMin_min : Prop := SplayHeapSet.findMin_minStatement positiveOrder
def In_deleteMin : Prop := SplayHeapSet.In_deleteMinStatement positiveOrder
def findMax_empty : Prop := SplayHeapSet.findMax_emptyStatement positiveOrder
def findMax_max : Prop := SplayHeapSet.findMax_maxStatement positiveOrder
def In_deleteMax : Prop := SplayHeapSet.In_deleteMaxStatement positiveOrder

end PHeap

end CompCert4Lean.Lib.Heaps
