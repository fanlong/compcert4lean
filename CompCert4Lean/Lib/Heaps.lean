import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.Ordered
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
open CompCert4Lean.Lib.Ordered

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
      | .EQ _ => (a, b)
      | .LT _ =>
          match b with
          | .Empty => (.Node a x b, .Empty)
          | .Node b1 y b2 =>
              match E.compare y pivot with
              | .EQ _ => (.Node a x b1, b2)
              | .LT _ =>
                  let (small, big) := partition pivot b2
                  (.Node (.Node a x b1) y small, big)
              | .GT _ =>
                  let (small, big) := partition pivot b1
                  (.Node a x small, .Node big y b2)
      | .GT _ =>
          match a with
          | .Empty => (.Empty, .Node a x b)
          | .Node a1 y a2 =>
              match E.compare y pivot with
              | .EQ _ => (a1, .Node a2 x b)
              | .LT _ =>
                  let (small, big) := partition pivot a2
                  (.Node a1 y small, .Node big x b)
              | .GT _ =>
                  let (small, big) := partition pivot a1
                  (small, .Node big y (.Node a2 x b))

private theorem partitionEq (pivot : E.t) (a : heap E) (x : E.t)
    (b : heap E) {heq : E.eq x pivot}
    (hcmp : E.compare x pivot = .EQ heq) :
    partition E pivot (.Node a x b) = (a, b) := by
  rw [partition.eq_def]
  simp only [hcmp]

private theorem partitionLtEmpty (pivot : E.t) (a : heap E) (x : E.t)
    {hlt : E.lt x pivot} (hcmp : E.compare x pivot = .LT hlt) :
    partition E pivot (.Node a x .Empty) = (.Node a x .Empty, .Empty) := by
  rw [partition.eq_def]
  simp only [hcmp]

private theorem partitionLtEq (pivot : E.t) (a : heap E) (x : E.t)
    (b1 : heap E) (y : E.t) (b2 : heap E) {hlt : E.lt x pivot}
    {heq : E.eq y pivot} (hcmp : E.compare x pivot = .LT hlt)
    (hycmp : E.compare y pivot = .EQ heq) :
    partition E pivot (.Node a x (.Node b1 y b2)) = (.Node a x b1, b2) := by
  rw [partition.eq_def]
  simp only [hcmp, hycmp]

private theorem partitionLtLt (pivot : E.t) (a : heap E) (x : E.t)
    (b1 : heap E) (y : E.t) (b2 : heap E) {hltx : E.lt x pivot}
    {hlty : E.lt y pivot} (hcmp : E.compare x pivot = .LT hltx)
    (hycmp : E.compare y pivot = .LT hlty) :
    partition E pivot (.Node a x (.Node b1 y b2)) =
      let p := partition E pivot b2
      (.Node (.Node a x b1) y p.1, p.2) := by
  rw [partition.eq_def]
  simp only [hcmp, hycmp]

private theorem partitionLtGt (pivot : E.t) (a : heap E) (x : E.t)
    (b1 : heap E) (y : E.t) (b2 : heap E) {hlt : E.lt x pivot}
    {hgt : E.lt pivot y} (hcmp : E.compare x pivot = .LT hlt)
    (hycmp : E.compare y pivot = .GT hgt) :
    partition E pivot (.Node a x (.Node b1 y b2)) =
      let p := partition E pivot b1
      (.Node a x p.1, .Node p.2 y b2) := by
  rw [partition.eq_def]
  simp only [hcmp, hycmp]

private theorem partitionGtEmpty (pivot : E.t) (x : E.t) (b : heap E)
    {hgt : E.lt pivot x} (hcmp : E.compare x pivot = .GT hgt) :
    partition E pivot (.Node .Empty x b) = (.Empty, .Node .Empty x b) := by
  rw [partition.eq_def]
  simp only [hcmp]

private theorem partitionGtEq (pivot : E.t) (a1 : heap E) (y : E.t)
    (a2 : heap E) (x : E.t) (b : heap E) {hgt : E.lt pivot x}
    {heq : E.eq y pivot} (hcmp : E.compare x pivot = .GT hgt)
    (hycmp : E.compare y pivot = .EQ heq) :
    partition E pivot (.Node (.Node a1 y a2) x b) =
      (a1, .Node a2 x b) := by
  rw [partition.eq_def]
  simp only [hcmp, hycmp]

private theorem partitionGtLt (pivot : E.t) (a1 : heap E) (y : E.t)
    (a2 : heap E) (x : E.t) (b : heap E) {hgt : E.lt pivot x}
    {hlt : E.lt y pivot} (hcmp : E.compare x pivot = .GT hgt)
    (hycmp : E.compare y pivot = .LT hlt) :
    partition E pivot (.Node (.Node a1 y a2) x b) =
      let p := partition E pivot a2
      (.Node a1 y p.1, .Node p.2 x b) := by
  rw [partition.eq_def]
  simp only [hcmp, hycmp]

private theorem partitionGtGt (pivot : E.t) (a1 : heap E) (y : E.t)
    (a2 : heap E) (x : E.t) (b : heap E) {hgtx : E.lt pivot x}
    {hgty : E.lt pivot y} (hcmp : E.compare x pivot = .GT hgtx)
    (hycmp : E.compare y pivot = .GT hgty) :
    partition E pivot (.Node (.Node a1 y a2) x b) =
      let p := partition E pivot a1
      (p.1, .Node p.2 y (.Node a2 x b)) := by
  rw [partition.eq_def]
  simp only [hcmp, hycmp]

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

private theorem leLtTrans {x y z : E.t} (hxy : le E x y)
    (hyz : E.lt y z) : E.lt x z := by
  rcases hxy with hxy | hxy
  · cases E.compare x z with
    | LT hxz => exact hxz
    | EQ hxz =>
        exact False.elim
          (E.lt_not_eq y z hyz (E.eq_trans y x z (E.eq_sym x y hxy) hxz))
    | GT hzx =>
        exact False.elim
          (E.lt_not_eq y x (E.lt_trans y z x hyz hzx) (E.eq_sym x y hxy))
  · exact E.lt_trans x y z hxy hyz

private theorem ltLeTrans {x y z : E.t} (hxy : E.lt x y)
    (hyz : le E y z) : E.lt x z := by
  rcases hyz with hyz | hyz
  · cases E.compare x z with
    | LT hxz => exact hxz
    | EQ hxz =>
        exact False.elim
          (E.lt_not_eq x y hxy (E.eq_trans x z y hxz (E.eq_sym y z hyz)))
    | GT hzx =>
        exact False.elim
          (E.lt_not_eq z y (E.lt_trans z x y hzx hxy) (E.eq_sym y z hyz))
  · exact E.lt_trans x y z hxy hyz

private theorem ltHeapTrans {x y : E.t} (hxy : le E x y) :
    ∀ h, lt_heap E h x → lt_heap E h y
  | .Empty, _ => trivial
  | .Node a z b, hlt =>
      ⟨ltHeapTrans hxy a hlt.1, ltLeTrans E hlt.2.1 hxy,
        ltHeapTrans hxy b hlt.2.2⟩

private theorem gtHeapTrans {x y : E.t} (hyx : le E y x) :
    ∀ h, gt_heap E h x → gt_heap E h y
  | .Empty, _ => trivial
  | .Node a z b, hgt =>
      ⟨gtHeapTrans hyx a hgt.1, leLtTrans E hyx hgt.2.1,
        gtHeapTrans hyx b hgt.2.2⟩

private theorem partitionLtProof (x pivot : E.t) :
    ∀ h, lt_heap E h x →
      lt_heap E (partition E pivot h).1 x ∧
      lt_heap E (partition E pivot h).2 x
  | .Empty, _ => ⟨trivial, trivial⟩
  | .Node a y b, hlt => by
      cases hcmp : E.compare y pivot with
      | EQ _ =>
          simpa only [partitionEq E pivot a y b hcmp, lt_heap] using
            And.intro hlt.1 hlt.2.2
      | LT _ =>
          cases b with
          | Empty =>
              simpa only [partitionLtEmpty E pivot a y hcmp, lt_heap] using
                And.intro hlt trivial
          | Node b1 z b2 =>
              cases hzcmp : E.compare z pivot with
              | EQ _ =>
                  simpa only [partitionLtEq E pivot a y b1 z b2 hcmp hzcmp,
                    lt_heap] using
                    And.intro ⟨hlt.1, hlt.2.1, hlt.2.2.1⟩ hlt.2.2.2.2
              | LT _ =>
                  have ih := partitionLtProof x pivot b2 hlt.2.2.2.2
                  cases hp : partition E pivot b2 with
                  | mk small big =>
                      rw [hp] at ih
                      simpa only [partitionLtLt E pivot a y b1 z b2 hcmp hzcmp,
                        hp, lt_heap] using
                        And.intro
                          ⟨⟨hlt.1, hlt.2.1, hlt.2.2.1⟩,
                            hlt.2.2.2.1, ih.1⟩
                          ih.2
              | GT _ =>
                  have ih := partitionLtProof x pivot b1 hlt.2.2.1
                  cases hp : partition E pivot b1 with
                  | mk small big =>
                      rw [hp] at ih
                      simpa only [partitionLtGt E pivot a y b1 z b2 hcmp hzcmp,
                        hp, lt_heap] using
                        And.intro ⟨hlt.1, hlt.2.1, ih.1⟩
                          ⟨ih.2, hlt.2.2.2.1, hlt.2.2.2.2⟩
      | GT _ =>
          cases a with
          | Empty =>
              simpa only [partitionGtEmpty E pivot y b hcmp, lt_heap] using
                And.intro trivial hlt
          | Node a1 z a2 =>
              cases hzcmp : E.compare z pivot with
              | EQ _ =>
                  simpa only [partitionGtEq E pivot a1 z a2 y b hcmp hzcmp,
                    lt_heap] using
                    And.intro hlt.1.1 ⟨hlt.1.2.2, hlt.2.1, hlt.2.2⟩
              | LT _ =>
                  have ih := partitionLtProof x pivot a2 hlt.1.2.2
                  cases hp : partition E pivot a2 with
                  | mk small big =>
                      rw [hp] at ih
                      simpa only [partitionGtLt E pivot a1 z a2 y b hcmp hzcmp,
                        hp, lt_heap] using
                        And.intro ⟨hlt.1.1, hlt.1.2.1, ih.1⟩
                          ⟨ih.2, hlt.2.1, hlt.2.2⟩
              | GT _ =>
                  have ih := partitionLtProof x pivot a1 hlt.1.1
                  cases hp : partition E pivot a1 with
                  | mk small big =>
                      rw [hp] at ih
                      simpa only [partitionGtGt E pivot a1 z a2 y b hcmp hzcmp,
                        hp, lt_heap] using
                        And.intro ih.1
                          ⟨ih.2, hlt.1.2.1,
                            ⟨hlt.1.2.2, hlt.2.1, hlt.2.2⟩⟩

private theorem partitionGtProof (x pivot : E.t) :
    ∀ h, gt_heap E h x →
      gt_heap E (partition E pivot h).1 x ∧
      gt_heap E (partition E pivot h).2 x
  | .Empty, _ => ⟨trivial, trivial⟩
  | .Node a y b, hgt => by
      cases hcmp : E.compare y pivot with
      | EQ _ =>
          simpa only [partitionEq E pivot a y b hcmp, gt_heap] using
            And.intro hgt.1 hgt.2.2
      | LT _ =>
          cases b with
          | Empty =>
              simpa only [partitionLtEmpty E pivot a y hcmp, gt_heap] using
                And.intro hgt trivial
          | Node b1 z b2 =>
              cases hzcmp : E.compare z pivot with
              | EQ _ =>
                  simpa only [partitionLtEq E pivot a y b1 z b2 hcmp hzcmp,
                    gt_heap] using
                    And.intro ⟨hgt.1, hgt.2.1, hgt.2.2.1⟩ hgt.2.2.2.2
              | LT _ =>
                  have ih := partitionGtProof x pivot b2 hgt.2.2.2.2
                  cases hp : partition E pivot b2 with
                  | mk small big =>
                      rw [hp] at ih
                      simpa only [partitionLtLt E pivot a y b1 z b2 hcmp hzcmp,
                        hp, gt_heap] using
                        And.intro
                          ⟨⟨hgt.1, hgt.2.1, hgt.2.2.1⟩,
                            hgt.2.2.2.1, ih.1⟩
                          ih.2
              | GT _ =>
                  have ih := partitionGtProof x pivot b1 hgt.2.2.1
                  cases hp : partition E pivot b1 with
                  | mk small big =>
                      rw [hp] at ih
                      simpa only [partitionLtGt E pivot a y b1 z b2 hcmp hzcmp,
                        hp, gt_heap] using
                        And.intro ⟨hgt.1, hgt.2.1, ih.1⟩
                          ⟨ih.2, hgt.2.2.2.1, hgt.2.2.2.2⟩
      | GT _ =>
          cases a with
          | Empty =>
              simpa only [partitionGtEmpty E pivot y b hcmp, gt_heap] using
                And.intro trivial hgt
          | Node a1 z a2 =>
              cases hzcmp : E.compare z pivot with
              | EQ _ =>
                  simpa only [partitionGtEq E pivot a1 z a2 y b hcmp hzcmp,
                    gt_heap] using
                    And.intro hgt.1.1 ⟨hgt.1.2.2, hgt.2.1, hgt.2.2⟩
              | LT _ =>
                  have ih := partitionGtProof x pivot a2 hgt.1.2.2
                  cases hp : partition E pivot a2 with
                  | mk small big =>
                      rw [hp] at ih
                      simpa only [partitionGtLt E pivot a1 z a2 y b hcmp hzcmp,
                        hp, gt_heap] using
                        And.intro ⟨hgt.1.1, hgt.1.2.1, ih.1⟩
                          ⟨ih.2, hgt.2.1, hgt.2.2⟩
              | GT _ =>
                  have ih := partitionGtProof x pivot a1 hgt.1.1
                  cases hp : partition E pivot a1 with
                  | mk small big =>
                      rw [hp] at ih
                      simpa only [partitionGtGt E pivot a1 z a2 y b hcmp hzcmp,
                        hp, gt_heap] using
                        And.intro ih.1
                          ⟨ih.2, hgt.1.2.1,
                            ⟨hgt.1.2.2, hgt.2.1, hgt.2.2⟩⟩

private theorem partitionSplitProof (pivot : E.t) :
    ∀ h, bst E h →
      lt_heap E (partition E pivot h).1 pivot ∧
      gt_heap E (partition E pivot h).2 pivot
  | .Empty, _ => ⟨trivial, trivial⟩
  | .Node a x b, hbst => by
      cases hcmp : E.compare x pivot with
      | EQ hxp =>
          simpa only [partitionEq E pivot a x b hcmp, lt_heap, gt_heap] using
            And.intro
              (ltHeapTrans E (Or.inl hxp) a hbst.2.2.1)
              (gtHeapTrans E (Or.inl (E.eq_sym x pivot hxp)) b hbst.2.2.2)
      | LT hxp =>
          cases b with
          | Empty =>
              simpa only [partitionLtEmpty E pivot a x hcmp, lt_heap, gt_heap]
                using
                And.intro
                  ⟨ltHeapTrans E (Or.inr hxp) a hbst.2.2.1, hxp, trivial⟩
                  trivial
          | Node b1 y b2 =>
              cases hycmp : E.compare y pivot with
              | EQ hyp =>
                  simpa only [partitionLtEq E pivot a x b1 y b2 hcmp hycmp,
                    lt_heap, gt_heap] using
                    And.intro
                      ⟨ltHeapTrans E (Or.inr hxp) a hbst.2.2.1, hxp,
                        ltHeapTrans E (Or.inl hyp) b1 hbst.2.1.2.2.1⟩
                      (gtHeapTrans E (Or.inl (E.eq_sym y pivot hyp)) b2
                        hbst.2.1.2.2.2)
              | LT hyp =>
                  have ih := partitionSplitProof pivot b2 hbst.2.1.2.1
                  cases hp : partition E pivot b2 with
                  | mk small big =>
                      rw [hp] at ih
                      simpa only [partitionLtLt E pivot a x b1 y b2 hcmp hycmp,
                        hp, lt_heap, gt_heap] using
                        And.intro
                          ⟨⟨ltHeapTrans E (Or.inr hxp) a hbst.2.2.1, hxp,
                              ltHeapTrans E (Or.inr hyp) b1 hbst.2.1.2.2.1⟩,
                            hyp, ih.1⟩
                          ih.2
              | GT hyp =>
                  have ih := partitionSplitProof pivot b1 hbst.2.1.1
                  cases hp : partition E pivot b1 with
                  | mk small big =>
                      rw [hp] at ih
                      simpa only [partitionLtGt E pivot a x b1 y b2 hcmp hycmp,
                        hp, lt_heap, gt_heap] using
                        And.intro
                          ⟨ltHeapTrans E (Or.inr hxp) a hbst.2.2.1, hxp, ih.1⟩
                          ⟨ih.2, hyp,
                            gtHeapTrans E (Or.inr hyp) b2 hbst.2.1.2.2.2⟩
      | GT hxp =>
          cases a with
          | Empty =>
              simpa only [partitionGtEmpty E pivot x b hcmp, lt_heap, gt_heap]
                using
                And.intro trivial
                  ⟨trivial, hxp,
                    gtHeapTrans E (Or.inr hxp) b hbst.2.2.2⟩
          | Node a1 y a2 =>
              cases hycmp : E.compare y pivot with
              | EQ hyp =>
                  simpa only [partitionGtEq E pivot a1 y a2 x b hcmp hycmp,
                    lt_heap, gt_heap] using
                    And.intro
                      (ltHeapTrans E (Or.inl hyp) a1 hbst.1.2.2.1)
                      ⟨gtHeapTrans E (Or.inl (E.eq_sym y pivot hyp)) a2
                          hbst.1.2.2.2,
                        hxp, gtHeapTrans E (Or.inr hxp) b hbst.2.2.2⟩
              | LT hyp =>
                  have ih := partitionSplitProof pivot a2 hbst.1.2.1
                  cases hp : partition E pivot a2 with
                  | mk small big =>
                      rw [hp] at ih
                      simpa only [partitionGtLt E pivot a1 y a2 x b hcmp hycmp,
                        hp, lt_heap, gt_heap] using
                        And.intro
                          ⟨ltHeapTrans E (Or.inr hyp) a1 hbst.1.2.2.1, hyp, ih.1⟩
                          ⟨ih.2, hxp,
                            gtHeapTrans E (Or.inr hxp) b hbst.2.2.2⟩
              | GT hyp =>
                  have ih := partitionSplitProof pivot a1 hbst.1.1
                  cases hp : partition E pivot a1 with
                  | mk small big =>
                      rw [hp] at ih
                      simpa only [partitionGtGt E pivot a1 y a2 x b hcmp hycmp,
                        hp, lt_heap, gt_heap] using
                        And.intro ih.1
                          ⟨ih.2, hyp,
                            ⟨gtHeapTrans E (Or.inr hyp) a2 hbst.1.2.2.2,
                              hxp, gtHeapTrans E (Or.inr hxp) b hbst.2.2.2⟩⟩

private theorem partitionBstProof (pivot : E.t) :
    ∀ h, bst E h →
      bst E (partition E pivot h).1 ∧ bst E (partition E pivot h).2
  | .Empty, _ => ⟨trivial, trivial⟩
  | .Node a x b, hbst => by
      cases hcmp : E.compare x pivot with
      | EQ _ =>
          simpa only [partitionEq E pivot a x b hcmp, bst] using
            And.intro hbst.1 hbst.2.1
      | LT _ =>
          cases b with
          | Empty =>
              simpa only [partitionLtEmpty E pivot a x hcmp, bst] using
                And.intro hbst trivial
          | Node b1 y b2 =>
              cases hycmp : E.compare y pivot with
              | EQ _ =>
                  simpa only [partitionLtEq E pivot a x b1 y b2 hcmp hycmp,
                    bst] using
                    And.intro
                      ⟨hbst.1, hbst.2.1.1, hbst.2.2.1, hbst.2.2.2.1⟩
                      hbst.2.1.2.1
              | LT _ =>
                  have ih := partitionBstProof pivot b2 hbst.2.1.2.1
                  have hgt := partitionGtProof E y pivot b2 hbst.2.1.2.2.2
                  cases hp : partition E pivot b2 with
                  | mk small big =>
                      rw [hp] at ih hgt
                      simpa only [partitionLtLt E pivot a x b1 y b2 hcmp hycmp,
                        hp, bst, lt_heap, gt_heap] using
                        And.intro
                          ⟨⟨hbst.1, hbst.2.1.1, hbst.2.2.1,
                              hbst.2.2.2.1⟩,
                            ih.1,
                            ⟨ltHeapTrans E (Or.inr hbst.2.2.2.2.1) a
                                hbst.2.2.1,
                              hbst.2.2.2.2.1, hbst.2.1.2.2.1⟩,
                            hgt.1⟩
                          ih.2
              | GT _ =>
                  have ih := partitionBstProof pivot b1 hbst.2.1.1
                  have hgt := partitionGtProof E x pivot b1 hbst.2.2.2.1
                  have hlt := partitionLtProof E y pivot b1 hbst.2.1.2.2.1
                  cases hp : partition E pivot b1 with
                  | mk small big =>
                      rw [hp] at ih hgt hlt
                      simpa only [partitionLtGt E pivot a x b1 y b2 hcmp hycmp,
                        hp, bst] using
                        And.intro
                          ⟨hbst.1, ih.1, hbst.2.2.1, hgt.1⟩
                          ⟨ih.2, hbst.2.1.2.1, hlt.2, hbst.2.1.2.2.2⟩
      | GT _ =>
          cases a with
          | Empty =>
              simpa only [partitionGtEmpty E pivot x b hcmp, bst] using
                And.intro trivial hbst
          | Node a1 y a2 =>
              cases hycmp : E.compare y pivot with
              | EQ _ =>
                  simpa only [partitionGtEq E pivot a1 y a2 x b hcmp hycmp,
                    bst] using
                    And.intro hbst.1.1
                      ⟨hbst.1.2.1, hbst.2.1, hbst.2.2.1.2.2, hbst.2.2.2⟩
              | LT _ =>
                  have ih := partitionBstProof pivot a2 hbst.1.2.1
                  have hgt := partitionGtProof E y pivot a2 hbst.1.2.2.2
                  have hlt := partitionLtProof E x pivot a2 hbst.2.2.1.2.2
                  cases hp : partition E pivot a2 with
                  | mk small big =>
                      rw [hp] at ih hgt hlt
                      simpa only [partitionGtLt E pivot a1 y a2 x b hcmp hycmp,
                        hp, bst] using
                        And.intro
                          ⟨hbst.1.1, ih.1, hbst.1.2.2.1, hgt.1⟩
                          ⟨ih.2, hbst.2.1, hlt.2, hbst.2.2.2⟩
              | GT _ =>
                  have ih := partitionBstProof pivot a1 hbst.1.1
                  have hlt := partitionLtProof E y pivot a1 hbst.1.2.2.1
                  cases hp : partition E pivot a1 with
                  | mk small big =>
                      rw [hp] at ih hlt
                      simpa only [partitionGtGt E pivot a1 y a2 x b hcmp hycmp,
                        hp, bst, lt_heap, gt_heap] using
                        And.intro ih.1
                          ⟨ih.2,
                            ⟨hbst.1.2.1, hbst.2.1, hbst.2.2.1.2.2,
                              hbst.2.2.2⟩,
                            hlt.2,
                            ⟨hbst.1.2.2.2, hbst.2.2.1.2.1,
                              gtHeapTrans E (Or.inr hbst.2.2.1.2.1) b
                                hbst.2.2.2⟩⟩

private theorem insertBstProof (x : E.t) (h : heap E) (hbst : bst E h) :
    bst E (insert E x h) := by
  have hpbst := partitionBstProof E x h hbst
  have hsplit := partitionSplitProof E x h hbst
  cases hp : partition E x h with
  | mk a b =>
      rw [hp] at hpbst hsplit
      simpa [insert, hp, bst] using
        And.intro hpbst.1 (And.intro hpbst.2 (And.intro hsplit.1 hsplit.2))

private theorem deleteMinLtProof (x : E.t) :
    ∀ h, lt_heap E h x → lt_heap E (deleteMin E h) x
  | .Empty, _ => trivial
  | .Node .Empty _ b, hlt => hlt.2.2
  | .Node (.Node a y b) z c, hlt => by
      cases a with
      | Empty =>
          simpa [deleteMin, lt_heap] using And.intro hlt.1.2.2 hlt.2
      | Node a1 w a2 =>
          have ih := deleteMinLtProof x (.Node a1 w a2) hlt.1.1
          simpa [deleteMin, lt_heap] using
            And.intro ih
              (And.intro hlt.1.2.1
                (And.intro hlt.1.2.2 (And.intro hlt.2.1 hlt.2.2)))

private theorem deleteMinBstProof : ∀ h, bst E h → bst E (deleteMin E h)
  | .Empty, _ => trivial
  | .Node .Empty _ b, hbst => hbst.2.1
  | .Node (.Node a x b) y c, hbst => by
      cases a with
      | Empty =>
          simpa [deleteMin, bst] using
            And.intro hbst.1.2.1
              (And.intro hbst.2.1
                (And.intro hbst.2.2.1.2.2 hbst.2.2.2))
      | Node a1 z a2 =>
          have ih := deleteMinBstProof (.Node a1 z a2) hbst.1.1
          have hlt := deleteMinLtProof E x (.Node a1 z a2) hbst.1.2.2.1
          have hgt := gtHeapTrans E (Or.inr hbst.2.2.1.2.1) c hbst.2.2.2
          simpa [deleteMin, bst, gt_heap] using
            And.intro ih
              (And.intro
                ⟨hbst.1.2.1, hbst.2.1, hbst.2.2.1.2.2, hbst.2.2.2⟩
                (And.intro hlt
                  ⟨hbst.1.2.2.2, hbst.2.2.1.2.1, hgt⟩))

private theorem deleteMaxGtProof (x : E.t) :
    ∀ h, gt_heap E h x → gt_heap E (deleteMax E h) x
  | .Empty, _ => trivial
  | .Node a _ .Empty, hgt => hgt.1
  | .Node a y (.Node b z c), hgt => by
      cases c with
      | Empty =>
          simpa [deleteMax, gt_heap] using
            And.intro hgt.1 (And.intro hgt.2.1 hgt.2.2.1)
      | Node c1 w c2 =>
          have ih := deleteMaxGtProof x (.Node c1 w c2) hgt.2.2.2.2
          simpa [deleteMax, gt_heap] using
            And.intro
              ⟨hgt.1, hgt.2.1, hgt.2.2.1⟩
              (And.intro hgt.2.2.2.1 ih)

private theorem deleteMaxBstProof : ∀ h, bst E h → bst E (deleteMax E h)
  | .Empty, _ => trivial
  | .Node a _ .Empty, hbst => hbst.1
  | .Node a x (.Node b y c), hbst => by
      cases c with
      | Empty =>
          simpa [deleteMax, bst] using
            And.intro hbst.1
              (And.intro hbst.2.1.1
                (And.intro hbst.2.2.1 hbst.2.2.2.1))
      | Node c1 z c2 =>
          have ih := deleteMaxBstProof (.Node c1 z c2) hbst.2.1.2.1
          have hlt := ltHeapTrans E (Or.inr hbst.2.2.2.2.1) a hbst.2.2.1
          have hgt := deleteMaxGtProof E y (.Node c1 z c2) hbst.2.1.2.2.2
          simpa [deleteMax, bst, lt_heap] using
            And.intro
              ⟨hbst.1, hbst.2.1.1, hbst.2.2.1, hbst.2.2.2.1⟩
              (And.intro ih
                (And.intro
                  ⟨hlt, hbst.2.2.2.2.1, hbst.2.1.2.2.1⟩ hgt))

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

def t : Type := {h : R.heap E // R.bst E h}

def empty : t E := ⟨.Empty, trivial⟩

def insert (x : E.t) (h : t E) : t E :=
  ⟨R.insert E x h.1, R.insertBstProof E x h.1 h.2⟩

def findMin (h : t E) : Option E.t := R.findMin E h.1

def deleteMin (h : t E) : t E :=
  ⟨R.deleteMin E h.1, R.deleteMinBstProof E h.1 h.2⟩

def findMax (h : t E) : Option E.t := R.findMax E h.1

def deleteMax (h : t E) : t E :=
  ⟨R.deleteMax E h.1, R.deleteMaxBstProof E h.1 h.2⟩

def In (x : E.t) (h : t E) : Prop := R.In E x h.1

def In_emptyStatement : Prop := ∀ x, ¬ In E x (empty E)

def In_insertStatement : Prop :=
  ∀ x h y,
    (In E y (insert E x h) ↔ E.eq y x ∨ In E y h)

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

private def positiveOrder : OrderedType :=
  { t := positive
    eq := OrderedPositive.eq
    lt := OrderedPositive.lt
    compare := OrderedPositive.compare
    eq_refl := fun _ => rfl
    eq_sym := by intro x y h; exact h.symm
    eq_trans := by intro x y z h₁ h₂; exact h₁.trans h₂
    lt_trans := by intro x y z hxy hyz; exact Nat.lt_trans hxy hyz
    lt_not_eq := by
      intro x y hxy heq
      change x = y at heq
      subst y
      exact Nat.lt_irrefl _ hxy
    eq_dec := fun x y => peq x y }

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
    SplayHeapSet.R.bst positiveOrder
      (SplayHeapSet.R.insert positiveOrder x h.1)
def deleteMin_obligation_1 : Prop :=
  ∀ h : t,
    SplayHeapSet.R.bst positiveOrder
      (SplayHeapSet.R.deleteMin positiveOrder h.1)
def deleteMax_obligation_1 : Prop :=
  ∀ h : t,
    SplayHeapSet.R.bst positiveOrder
      (SplayHeapSet.R.deleteMax positiveOrder h.1)

def In_empty : Prop := SplayHeapSet.In_emptyStatement positiveOrder
def In_insert : Prop := SplayHeapSet.In_insertStatement positiveOrder
def findMin_empty : Prop := SplayHeapSet.findMin_emptyStatement positiveOrder
def findMin_min : Prop := SplayHeapSet.findMin_minStatement positiveOrder
def In_deleteMin : Prop := SplayHeapSet.In_deleteMinStatement positiveOrder
def findMax_empty : Prop := SplayHeapSet.findMax_emptyStatement positiveOrder
def findMax_max : Prop := SplayHeapSet.findMax_maxStatement positiveOrder
def In_deleteMax : Prop := SplayHeapSet.In_deleteMaxStatement positiveOrder

namespace R

/-! ## Exact statements of the generated functional-induction schemes

The source `Functional Scheme` declarations are proof-facing generated
surfaces.  Their propositions retain the branch equalities, comparison
witnesses, recursive hypotheses, and result equations; proof terms are
deferred to the proof-grinding phase.
-/

def partition_indStatement : Prop :=
  ∀ (pivot : positive)
    (P : SplayHeapSet.R.heap positiveOrder →
      SplayHeapSet.R.heap positiveOrder × SplayHeapSet.R.heap positiveOrder → Prop),
    (∀ h : SplayHeapSet.R.heap positiveOrder,
      h = (@SplayHeapSet.R.Empty positiveOrder) →
        P (@SplayHeapSet.R.Empty positiveOrder)
          ((@SplayHeapSet.R.Empty positiveOrder), (@SplayHeapSet.R.Empty positiveOrder))) →
    (∀ (h a : SplayHeapSet.R.heap positiveOrder) (x : positive)
      (b : SplayHeapSet.R.heap positiveOrder),
      h = SplayHeapSet.R.Node a x b →
      ∀ (_x : OrderedPositive.lt x pivot),
        OrderedPositive.compare x pivot = .LT _x →
      b = (@SplayHeapSet.R.Empty positiveOrder) →
      P (SplayHeapSet.R.Node a x (@SplayHeapSet.R.Empty positiveOrder))
        (h, (@SplayHeapSet.R.Empty positiveOrder))) →
    (∀ (h a : SplayHeapSet.R.heap positiveOrder) (x : positive)
      (b : SplayHeapSet.R.heap positiveOrder),
      h = SplayHeapSet.R.Node a x b →
      ∀ (_x : OrderedPositive.lt x pivot),
        OrderedPositive.compare x pivot = .LT _x →
      ∀ (b1 : SplayHeapSet.R.heap positiveOrder) (y : positive)
        (b2 : SplayHeapSet.R.heap positiveOrder),
      b = SplayHeapSet.R.Node b1 y b2 →
      ∀ (_x0 : OrderedPositive.lt y pivot),
        OrderedPositive.compare y pivot = .LT _x0 →
      P b2 (SplayHeapSet.R.partition positiveOrder pivot b2) →
      ∀ (small big : SplayHeapSet.R.heap positiveOrder),
        SplayHeapSet.R.partition positiveOrder pivot b2 = (small, big) →
      P (SplayHeapSet.R.Node a x (SplayHeapSet.R.Node b1 y b2))
        (SplayHeapSet.R.Node (SplayHeapSet.R.Node a x b1) y small, big)) →
    (∀ (h a : SplayHeapSet.R.heap positiveOrder) (x : positive)
      (b : SplayHeapSet.R.heap positiveOrder),
      h = SplayHeapSet.R.Node a x b →
      ∀ (_x : OrderedPositive.lt x pivot),
        OrderedPositive.compare x pivot = .LT _x →
      ∀ (b1 : SplayHeapSet.R.heap positiveOrder) (y : positive)
        (b2 : SplayHeapSet.R.heap positiveOrder),
      b = SplayHeapSet.R.Node b1 y b2 →
      ∀ (_x0 : OrderedPositive.eq y pivot),
        OrderedPositive.compare y pivot = .EQ _x0 →
      P (SplayHeapSet.R.Node a x (SplayHeapSet.R.Node b1 y b2))
        (SplayHeapSet.R.Node a x b1, b2)) →
    (∀ (h a : SplayHeapSet.R.heap positiveOrder) (x : positive)
      (b : SplayHeapSet.R.heap positiveOrder),
      h = SplayHeapSet.R.Node a x b →
      ∀ (_x : OrderedPositive.lt x pivot),
        OrderedPositive.compare x pivot = .LT _x →
      ∀ (b1 : SplayHeapSet.R.heap positiveOrder) (y : positive)
        (b2 : SplayHeapSet.R.heap positiveOrder),
      b = SplayHeapSet.R.Node b1 y b2 →
      ∀ (_x0 : OrderedPositive.lt pivot y),
        OrderedPositive.compare y pivot = .GT _x0 →
      P b1 (SplayHeapSet.R.partition positiveOrder pivot b1) →
      ∀ (small big : SplayHeapSet.R.heap positiveOrder),
        SplayHeapSet.R.partition positiveOrder pivot b1 = (small, big) →
      P (SplayHeapSet.R.Node a x (SplayHeapSet.R.Node b1 y b2))
        (SplayHeapSet.R.Node a x small, SplayHeapSet.R.Node big y b2)) →
    (∀ (h a : SplayHeapSet.R.heap positiveOrder) (x : positive)
      (b : SplayHeapSet.R.heap positiveOrder),
      h = SplayHeapSet.R.Node a x b →
      ∀ (_x : OrderedPositive.eq x pivot),
        OrderedPositive.compare x pivot = .EQ _x →
      P (SplayHeapSet.R.Node a x b) (a, b)) →
    (∀ (h a : SplayHeapSet.R.heap positiveOrder) (x : positive)
      (b : SplayHeapSet.R.heap positiveOrder),
      h = SplayHeapSet.R.Node a x b →
      ∀ (_x : OrderedPositive.lt pivot x),
        OrderedPositive.compare x pivot = .GT _x →
      a = (@SplayHeapSet.R.Empty positiveOrder) →
      P (@SplayHeapSet.R.Node positiveOrder
          (@SplayHeapSet.R.Empty positiveOrder) x b)
        ((@SplayHeapSet.R.Empty positiveOrder), h)) →
    (∀ (h a : SplayHeapSet.R.heap positiveOrder) (x : positive)
      (b : SplayHeapSet.R.heap positiveOrder),
      h = SplayHeapSet.R.Node a x b →
      ∀ (_x : OrderedPositive.lt pivot x),
        OrderedPositive.compare x pivot = .GT _x →
      ∀ (a1 : SplayHeapSet.R.heap positiveOrder) (y : positive)
        (a2 : SplayHeapSet.R.heap positiveOrder),
      a = SplayHeapSet.R.Node a1 y a2 →
      ∀ (_x0 : OrderedPositive.lt y pivot),
        OrderedPositive.compare y pivot = .LT _x0 →
      P a2 (SplayHeapSet.R.partition positiveOrder pivot a2) →
      ∀ (small big : SplayHeapSet.R.heap positiveOrder),
        SplayHeapSet.R.partition positiveOrder pivot a2 = (small, big) →
      P (SplayHeapSet.R.Node (SplayHeapSet.R.Node a1 y a2) x b)
        (SplayHeapSet.R.Node a1 y small, SplayHeapSet.R.Node big x b)) →
    (∀ (h a : SplayHeapSet.R.heap positiveOrder) (x : positive)
      (b : SplayHeapSet.R.heap positiveOrder),
      h = SplayHeapSet.R.Node a x b →
      ∀ (_x : OrderedPositive.lt pivot x),
        OrderedPositive.compare x pivot = .GT _x →
      ∀ (a1 : SplayHeapSet.R.heap positiveOrder) (y : positive)
        (a2 : SplayHeapSet.R.heap positiveOrder),
      a = SplayHeapSet.R.Node a1 y a2 →
      ∀ (_x0 : OrderedPositive.eq y pivot),
        OrderedPositive.compare y pivot = .EQ _x0 →
      P (SplayHeapSet.R.Node (SplayHeapSet.R.Node a1 y a2) x b)
        (a1, SplayHeapSet.R.Node a2 x b)) →
    (∀ (h a : SplayHeapSet.R.heap positiveOrder) (x : positive)
      (b : SplayHeapSet.R.heap positiveOrder),
      h = SplayHeapSet.R.Node a x b →
      ∀ (_x : OrderedPositive.lt pivot x),
        OrderedPositive.compare x pivot = .GT _x →
      ∀ (a1 : SplayHeapSet.R.heap positiveOrder) (y : positive)
        (a2 : SplayHeapSet.R.heap positiveOrder),
      a = SplayHeapSet.R.Node a1 y a2 →
      ∀ (_x0 : OrderedPositive.lt pivot y),
        OrderedPositive.compare y pivot = .GT _x0 →
      P a1 (SplayHeapSet.R.partition positiveOrder pivot a1) →
      ∀ (small big : SplayHeapSet.R.heap positiveOrder),
        SplayHeapSet.R.partition positiveOrder pivot a1 = (small, big) →
      P (SplayHeapSet.R.Node (SplayHeapSet.R.Node a1 y a2) x b)
        (small, SplayHeapSet.R.Node big y
          (SplayHeapSet.R.Node a2 x b))) →
    ∀ h : SplayHeapSet.R.heap positiveOrder,
      P h (SplayHeapSet.R.partition positiveOrder pivot h)

def deleteMin_indStatement : Prop :=
  ∀ (P : SplayHeapSet.R.heap positiveOrder →
      SplayHeapSet.R.heap positiveOrder → Prop),
    (∀ h : SplayHeapSet.R.heap positiveOrder,
      h = (@SplayHeapSet.R.Empty positiveOrder) →
        P (@SplayHeapSet.R.Empty positiveOrder) (@SplayHeapSet.R.Empty positiveOrder)) →
    (∀ (h l : SplayHeapSet.R.heap positiveOrder) (y : positive)
      (c : SplayHeapSet.R.heap positiveOrder),
      h = SplayHeapSet.R.Node l y c →
      l = @SplayHeapSet.R.Empty positiveOrder →
      P (@SplayHeapSet.R.Node positiveOrder
          (@SplayHeapSet.R.Empty positiveOrder) y c) c) →
    (∀ (h l : SplayHeapSet.R.heap positiveOrder) (y : positive)
      (c : SplayHeapSet.R.heap positiveOrder),
      h = SplayHeapSet.R.Node l y c →
      ∀ (a : SplayHeapSet.R.heap positiveOrder) (x : positive)
        (b : SplayHeapSet.R.heap positiveOrder),
      l = SplayHeapSet.R.Node a x b →
      a = (@SplayHeapSet.R.Empty positiveOrder) →
      P (@SplayHeapSet.R.Node positiveOrder
          (@SplayHeapSet.R.Node positiveOrder
            (@SplayHeapSet.R.Empty positiveOrder) x b) y c)
        (@SplayHeapSet.R.Node positiveOrder b y c)) →
    (∀ (h l : SplayHeapSet.R.heap positiveOrder) (y : positive)
      (c : SplayHeapSet.R.heap positiveOrder),
      h = SplayHeapSet.R.Node l y c →
      ∀ (a : SplayHeapSet.R.heap positiveOrder) (x : positive)
        (b : SplayHeapSet.R.heap positiveOrder),
      l = SplayHeapSet.R.Node a x b →
      ∀ (a0 : SplayHeapSet.R.heap positiveOrder) (x0 : positive)
        (b0 : SplayHeapSet.R.heap positiveOrder),
      a = SplayHeapSet.R.Node a0 x0 b0 →
      P a (SplayHeapSet.R.deleteMin positiveOrder a) →
      P (@SplayHeapSet.R.Node positiveOrder
          (@SplayHeapSet.R.Node positiveOrder
            (@SplayHeapSet.R.Node positiveOrder a0 x0 b0) x b) y c)
        (@SplayHeapSet.R.Node positiveOrder
          (SplayHeapSet.R.deleteMin positiveOrder a) x
          (@SplayHeapSet.R.Node positiveOrder b y c))) →
    ∀ h : SplayHeapSet.R.heap positiveOrder,
      P h (SplayHeapSet.R.deleteMin positiveOrder h)

def deleteMax_indStatement : Prop :=
  ∀ (P : SplayHeapSet.R.heap positiveOrder →
      SplayHeapSet.R.heap positiveOrder → Prop),
    (∀ h : SplayHeapSet.R.heap positiveOrder,
      h = (@SplayHeapSet.R.Empty positiveOrder) →
        P (@SplayHeapSet.R.Empty positiveOrder) (@SplayHeapSet.R.Empty positiveOrder)) →
    (∀ (h a : SplayHeapSet.R.heap positiveOrder) (x : positive)
      (r : SplayHeapSet.R.heap positiveOrder),
      h = SplayHeapSet.R.Node a x r →
      r = (@SplayHeapSet.R.Empty positiveOrder) →
      P (@SplayHeapSet.R.Node positiveOrder a x
          (@SplayHeapSet.R.Empty positiveOrder)) a) →
    (∀ (h a : SplayHeapSet.R.heap positiveOrder) (x : positive)
      (r : SplayHeapSet.R.heap positiveOrder),
      h = SplayHeapSet.R.Node a x r →
      ∀ (b : SplayHeapSet.R.heap positiveOrder) (y : positive)
        (c : SplayHeapSet.R.heap positiveOrder),
      r = SplayHeapSet.R.Node b y c →
      c = (@SplayHeapSet.R.Empty positiveOrder) →
      P (@SplayHeapSet.R.Node positiveOrder a x
          (@SplayHeapSet.R.Node positiveOrder b y
            (@SplayHeapSet.R.Empty positiveOrder)))
        (@SplayHeapSet.R.Node positiveOrder a x b)) →
    (∀ (h a : SplayHeapSet.R.heap positiveOrder) (x : positive)
      (r : SplayHeapSet.R.heap positiveOrder),
      h = SplayHeapSet.R.Node a x r →
      ∀ (b : SplayHeapSet.R.heap positiveOrder) (y : positive)
        (c : SplayHeapSet.R.heap positiveOrder),
      r = SplayHeapSet.R.Node b y c →
      ∀ (a0 : SplayHeapSet.R.heap positiveOrder) (x0 : positive)
        (b0 : SplayHeapSet.R.heap positiveOrder),
      c = SplayHeapSet.R.Node a0 x0 b0 →
      P c (SplayHeapSet.R.deleteMax positiveOrder c) →
      P (@SplayHeapSet.R.Node positiveOrder a x
          (@SplayHeapSet.R.Node positiveOrder b y
            (@SplayHeapSet.R.Node positiveOrder a0 x0 b0)))
        (@SplayHeapSet.R.Node positiveOrder
          (@SplayHeapSet.R.Node positiveOrder a x b) y
          (SplayHeapSet.R.deleteMax positiveOrder c))) →
    ∀ h : SplayHeapSet.R.heap positiveOrder,
      P h (SplayHeapSet.R.deleteMax positiveOrder h)

end R

end PHeap

end CompCert4Lean.Lib.Heaps

namespace CompCert4Lean.Lib.Heaps.SplayHeapSet.R

theorem le_lt_trans (E : OrderedType) : le_lt_transStatement E := by
  intro x1 x2 x3 h12 h23
  rcases h12 with h12 | h12
  · cases E.compare x1 x3 with
    | LT h13 => exact h13
    | EQ h13 =>
        exact False.elim
          (E.lt_not_eq x2 x3 h23
            (E.eq_trans x2 x1 x3 (E.eq_sym x1 x2 h12) h13))
    | GT h31 =>
        exact False.elim
          (E.lt_not_eq x2 x1 (E.lt_trans x2 x3 x1 h23 h31)
            (E.eq_sym x1 x2 h12))
  · exact E.lt_trans x1 x2 x3 h12 h23

end CompCert4Lean.Lib.Heaps.SplayHeapSet.R

namespace CompCert4Lean.Lib.Heaps.PHeap.R

private def proofHeapSize {E : OrderedType} : SplayHeapSet.R.heap E → Nat
  | .Empty => 0
  | .Node l _ r => proofHeapSize l + proofHeapSize r + 1

theorem deleteMin_ind : deleteMin_indStatement := by
  unfold deleteMin_indStatement
  intro P hEmpty hOne hTwo hRec
  have aux : ∀ n (h : _), proofHeapSize h ≤ n →
      P h (SplayHeapSet.R.deleteMin _ h) := by
    intro n
    induction n with
    | zero =>
        intro h hs
        cases h with
        | Empty => exact hEmpty .Empty rfl
        | Node l x r => simp [proofHeapSize] at hs
    | succ n ih =>
        intro h hs
        cases h with
        | Empty => exact hEmpty .Empty rfl
        | Node l y c =>
            cases l with
            | Empty =>
                simpa [SplayHeapSet.R.deleteMin] using
                  hOne (.Node .Empty y c) .Empty y c rfl rfl
            | Node a x b =>
                cases a with
                | Empty =>
                    simpa [SplayHeapSet.R.deleteMin] using
                      hTwo (.Node (.Node .Empty x b) y c) (.Node .Empty x b) y c rfl
                        .Empty x b rfl rfl
                | Node a0 x0 b0 =>
                    simpa [SplayHeapSet.R.deleteMin] using
                      hRec (.Node (.Node (.Node a0 x0 b0) x b) y c)
                        (.Node (.Node a0 x0 b0) x b) y c rfl
                        (.Node a0 x0 b0) x b rfl
                        a0 x0 b0 rfl
                        (ih (.Node a0 x0 b0)
                          (by simp [proofHeapSize] at hs ⊢; omega))
  intro h
  exact aux (proofHeapSize h) h (Nat.le_refl _)

theorem deleteMax_ind : deleteMax_indStatement := by
  unfold deleteMax_indStatement
  intro P hEmpty hOne hTwo hRec
  have aux : ∀ n (h : _), proofHeapSize h ≤ n →
      P h (SplayHeapSet.R.deleteMax _ h) := by
    intro n
    induction n with
    | zero =>
        intro h hs
        cases h with
        | Empty => exact hEmpty .Empty rfl
        | Node l x r => simp [proofHeapSize] at hs
    | succ n ih =>
        intro h hs
        cases h with
        | Empty => exact hEmpty .Empty rfl
        | Node a x r =>
            cases r with
            | Empty =>
                simpa [SplayHeapSet.R.deleteMax] using
                  hOne (.Node a x .Empty) a x .Empty rfl rfl
            | Node b y c =>
                cases c with
                | Empty =>
                    simpa [SplayHeapSet.R.deleteMax] using
                      hTwo (.Node a x (.Node b y .Empty)) a x (.Node b y .Empty) rfl
                        b y .Empty rfl rfl
                | Node a0 x0 b0 =>
                    simpa [SplayHeapSet.R.deleteMax] using
                      hRec (.Node a x (.Node b y (.Node a0 x0 b0)))
                        a x (.Node b y (.Node a0 x0 b0)) rfl
                        b y (.Node a0 x0 b0) rfl
                        a0 x0 b0 rfl
                        (ih (.Node a0 x0 b0)
                          (by simp [proofHeapSize] at hs ⊢; omega))
  intro h
  exact aux (proofHeapSize h) h (Nat.le_refl _)

theorem partition_ind : partition_indStatement := by
  unfold partition_indStatement
  intro pivot P hEmpty hLtEmpty hLtLt hLtEq hLtGt hEq hGtEmpty hGtLt hGtEq hGtGt
  have aux : ∀ n (h : _), proofHeapSize h ≤ n →
      P h (SplayHeapSet.R.partition _ pivot h) := by
    intro n
    induction n with
    | zero =>
        intro h hs
        cases h with
        | Empty => exact hEmpty .Empty rfl
        | Node l x r => simp [proofHeapSize] at hs
    | succ n ih =>
        intro h hs
        cases h with
        | Empty => exact hEmpty .Empty rfl
        | Node a x b =>
            cases hcmp : CompCert4Lean.Lib.Ordered.OrderedPositive.compare x pivot with
            | EQ heq =>
                simpa only [SplayHeapSet.R.partitionEq positiveOrder pivot a x b hcmp] using
                  hEq (.Node a x b) a x b rfl heq hcmp
            | LT hltx =>
                cases b with
                | Empty =>
                    simpa only [SplayHeapSet.R.partitionLtEmpty positiveOrder pivot a x hcmp]
                      using hLtEmpty (.Node a x .Empty) a x .Empty rfl hltx hcmp rfl
                | Node b1 y b2 =>
                    cases hycmp : CompCert4Lean.Lib.Ordered.OrderedPositive.compare y pivot with
                    | EQ heq =>
                        simpa only [SplayHeapSet.R.partitionLtEq positiveOrder pivot a x b1 y b2
                          hcmp hycmp] using
                          hLtEq (.Node a x (.Node b1 y b2)) a x (.Node b1 y b2)
                            rfl hltx hcmp b1 y b2 rfl heq hycmp
                    | LT hlty =>
                        have hrec := ih b2
                          (by simp [proofHeapSize] at hs ⊢; omega)
                        cases hp : SplayHeapSet.R.partition _ pivot b2 with
                        | mk small big =>
                            simpa only [SplayHeapSet.R.partitionLtLt positiveOrder pivot a x b1 y b2
                              hcmp hycmp, hp] using
                              hLtLt (.Node a x (.Node b1 y b2)) a x (.Node b1 y b2)
                                rfl hltx hcmp b1 y b2 rfl hlty hycmp hrec small big hp
                    | GT hgty =>
                        have hrec := ih b1
                          (by simp [proofHeapSize] at hs ⊢; omega)
                        cases hp : SplayHeapSet.R.partition _ pivot b1 with
                        | mk small big =>
                            simpa only [SplayHeapSet.R.partitionLtGt positiveOrder pivot a x b1 y b2
                              hcmp hycmp, hp] using
                              hLtGt (.Node a x (.Node b1 y b2)) a x (.Node b1 y b2)
                                rfl hltx hcmp b1 y b2 rfl hgty hycmp hrec small big hp
            | GT hgtx =>
                cases a with
                | Empty =>
                    simpa only [SplayHeapSet.R.partitionGtEmpty positiveOrder pivot x b hcmp]
                      using hGtEmpty (.Node .Empty x b) .Empty x b rfl hgtx hcmp rfl
                | Node a1 y a2 =>
                    cases hycmp : CompCert4Lean.Lib.Ordered.OrderedPositive.compare y pivot with
                    | EQ heq =>
                        simpa only [SplayHeapSet.R.partitionGtEq positiveOrder pivot a1 y a2 x b
                          hcmp hycmp] using
                          hGtEq (.Node (.Node a1 y a2) x b) (.Node a1 y a2) x b
                            rfl hgtx hcmp a1 y a2 rfl heq hycmp
                    | LT hlty =>
                        have hrec := ih a2
                          (by simp [proofHeapSize] at hs ⊢; omega)
                        cases hp : SplayHeapSet.R.partition _ pivot a2 with
                        | mk small big =>
                            simpa only [SplayHeapSet.R.partitionGtLt positiveOrder pivot a1 y a2 x b
                              hcmp hycmp, hp] using
                              hGtLt (.Node (.Node a1 y a2) x b) (.Node a1 y a2) x b
                                rfl hgtx hcmp a1 y a2 rfl hlty hycmp hrec small big hp
                    | GT hgty =>
                        have hrec := ih a1
                          (by simp [proofHeapSize] at hs ⊢; omega)
                        cases hp : SplayHeapSet.R.partition _ pivot a1 with
                        | mk small big =>
                            simpa only [SplayHeapSet.R.partitionGtGt positiveOrder pivot a1 y a2 x b
                              hcmp hycmp, hp] using
                              hGtGt (.Node (.Node a1 y a2) x b) (.Node a1 y a2) x b
                                rfl hgtx hcmp a1 y a2 rfl hgty hycmp hrec small big hp
  intro h
  exact aux (proofHeapSize h) h (Nat.le_refl _)

end CompCert4Lean.Lib.Heaps.PHeap.R

namespace CompCert4Lean.Lib.Heaps.SplayHeapSet.R

theorem lt_le_trans (E : OrderedType) : lt_le_transStatement E := by
  unfold lt_le_transStatement
  intro x1 x2 x3 h12 h23
  rcases h23 with h23 | h23
  · cases E.compare x1 x3 with
    | LT h13 => exact h13
    | EQ h13 =>
        exact False.elim
          (E.lt_not_eq x1 x2 h12
            (E.eq_trans x1 x3 x2 h13 (E.eq_sym x2 x3 h23)))
    | GT h31 =>
        exact False.elim
          (E.lt_not_eq x3 x2 (E.lt_trans x3 x1 x2 h31 h12)
            (E.eq_sym x2 x3 h23))
  · exact E.lt_trans x1 x2 x3 h12 h23

theorem le_trans (E : OrderedType) : le_transStatement E := by
  unfold le_transStatement
  intro x1 x2 x3 h12 h23
  rcases h23 with h23 | h23
  · rcases h12 with h12 | h12
    · exact Or.inl (E.eq_trans x1 x2 x3 h12 h23)
    · exact Or.inr (lt_le_trans E x1 x2 x3 h12 (Or.inl h23))
  · exact Or.inr (le_lt_trans E x1 x2 x3 h12 h23)

theorem lt_heap_trans (E : OrderedType) : lt_heap_transStatement E := by
  unfold lt_heap_transStatement
  intro x y hxy h
  induction h with
  | Empty =>
      intro _
      trivial
  | Node a z b iha ihb =>
      intro hlt
      exact ⟨iha hlt.1, lt_le_trans E z x y hlt.2.1 hxy, ihb hlt.2.2⟩

theorem gt_heap_trans (E : OrderedType) : gt_heap_transStatement E := by
  unfold gt_heap_transStatement
  intro x y hyx h
  induction h with
  | Empty =>
      intro _
      trivial
  | Node a z b iha ihb =>
      intro hgt
      exact ⟨iha hgt.1, le_lt_trans E y x z hyx hgt.2.1, ihb hgt.2.2⟩

end CompCert4Lean.Lib.Heaps.SplayHeapSet.R

namespace CompCert4Lean.Lib.Heaps.SplayHeapSet.R

theorem partition_lt (E : OrderedType) : partition_ltStatement E := by
  unfold partition_ltStatement
  intro x pivot h hlt
  exact partitionLtProof E x pivot h hlt

theorem partition_gt (E : OrderedType) : partition_gtStatement E := by
  unfold partition_gtStatement
  intro x pivot h hgt
  exact partitionGtProof E x pivot h hgt

theorem partition_split (E : OrderedType) : partition_splitStatement E := by
  unfold partition_splitStatement
  intro pivot h hbst
  exact partitionSplitProof E pivot h hbst

private def inPartitionSize {E : OrderedType} : heap E → Nat
  | .Empty => 0
  | .Node l _ r => inPartitionSize l + inPartitionSize r + 1

private theorem inPartitionAux (E : OrderedType) (x pivot : E.t)
    (hneq : ¬ E.eq x pivot) :
    ∀ n (h : heap E), inPartitionSize h ≤ n →
      (In E x h ↔ In E x (partition E pivot h).1 ∨
        In E x (partition E pivot h).2) := by
  intro n
  induction n with
  | zero =>
      intro h hs
      cases h with
      | Empty => simp [In, partition]
      | Node l y r => simp [inPartitionSize] at hs
  | succ n ih =>
      intro h hs
      cases h with
      | Empty => simp [In, partition]
      | Node a y b =>
          cases hcmp : E.compare y pivot with
          | EQ heq =>
              have hxy : ¬ E.eq x y := by
                intro hxy
                exact hneq (E.eq_trans x y pivot hxy heq)
              simp only [partitionEq E pivot a y b hcmp, In]
              simp_all [or_assoc, or_left_comm, or_comm]
          | LT hlt =>
              cases b with
              | Empty =>
                  simp only [partitionLtEmpty E pivot a y hcmp, In]
                  simp_all [or_assoc, or_left_comm, or_comm]
              | Node b1 z b2 =>
                  cases hzcmp : E.compare z pivot with
                  | EQ heq =>
                      have hxz : ¬ E.eq x z := by
                        intro hxz
                        exact hneq (E.eq_trans x z pivot hxz heq)
                      simp only [partitionLtEq E pivot a y b1 z b2 hcmp hzcmp, In]
                      simp_all [or_assoc, or_left_comm, or_comm]
                  | LT hzl =>
                      have hrec := ih b2
                        (by simp [inPartitionSize] at hs ⊢; omega)
                      cases hp : partition E pivot b2 with
                      | mk small big =>
                          rw [hp] at hrec
                          simp only [partitionLtLt E pivot a y b1 z b2 hcmp hzcmp,
                            hp, In] at hrec ⊢
                          simp_all [or_assoc, or_left_comm, or_comm]
                  | GT hzg =>
                      have hrec := ih b1
                        (by simp [inPartitionSize] at hs ⊢; omega)
                      cases hp : partition E pivot b1 with
                      | mk small big =>
                          rw [hp] at hrec
                          simp only [partitionLtGt E pivot a y b1 z b2 hcmp hzcmp,
                            hp, In] at hrec ⊢
                          simp_all [or_assoc, or_left_comm, or_comm]
          | GT hgt =>
              cases a with
              | Empty =>
                  simp only [partitionGtEmpty E pivot y b hcmp, In]
                  simp_all [or_assoc, or_left_comm, or_comm]
              | Node a1 z a2 =>
                  cases hzcmp : E.compare z pivot with
                  | EQ heq =>
                      have hxz : ¬ E.eq x z := by
                        intro hxz
                        exact hneq (E.eq_trans x z pivot hxz heq)
                      simp only [partitionGtEq E pivot a1 z a2 y b hcmp hzcmp, In]
                      simp_all [or_assoc, or_left_comm, or_comm]
                  | LT hzl =>
                      have hrec := ih a2
                        (by simp [inPartitionSize] at hs ⊢; omega)
                      cases hp : partition E pivot a2 with
                      | mk small big =>
                          rw [hp] at hrec
                          simp only [partitionGtLt E pivot a1 z a2 y b hcmp hzcmp,
                            hp, In] at hrec ⊢
                          simp_all [or_assoc, or_left_comm, or_comm]
                  | GT hzg =>
                      have hrec := ih a1
                        (by simp [inPartitionSize] at hs ⊢; omega)
                      cases hp : partition E pivot a1 with
                      | mk small big =>
                          rw [hp] at hrec
                          simp only [partitionGtGt E pivot a1 z a2 y b hcmp hzcmp,
                            hp, In] at hrec ⊢
                          simp_all [or_assoc, or_left_comm, or_comm]

theorem In_partition (E : OrderedType) : In_partitionStatement E := by
  unfold In_partitionStatement
  intro x pivot hneq h hbst
  exact inPartitionAux E x pivot hneq (inPartitionSize h) h
    (Nat.le_refl _)

end CompCert4Lean.Lib.Heaps.SplayHeapSet.R

namespace CompCert4Lean.Lib.Heaps.SplayHeapSet.R

theorem partition_bst (E : OrderedType) : partition_bstStatement E := by
  intro pivot h hbst
  exact partitionBstProof E pivot h hbst

end CompCert4Lean.Lib.Heaps.SplayHeapSet.R

namespace CompCert4Lean.Lib.Heaps.SplayHeapSet.R

theorem insert_bst : ∀ (E : OrderedType), insert_bstStatement E := by
  intro E x h hbst
  exact insertBstProof E x h hbst

end CompCert4Lean.Lib.Heaps.SplayHeapSet.R

namespace CompCert4Lean.Lib.Heaps.SplayHeapSet.R

theorem In_insert : ∀ (E : OrderedType), In_insertStatement E := by
  intro E x h y hbst
  unfold insert
  cases hp : partition E x h with
  | mk a b =>
      cases E.eq_dec y x with
      | left heq =>
          simp only [hp]
          change (In E y a ∨ E.eq y x ∨ In E y b) ↔ _
          simp [heq]
      | right hneq =>
          have hpart := In_partition E y x hneq h hbst
          rw [hp] at hpart
          simp only [hp]
          change (In E y a ∨ E.eq y x ∨ In E y b) ↔ _
          simp [hneq, hpart]

end CompCert4Lean.Lib.Heaps.SplayHeapSet.R

namespace CompCert4Lean.Lib.Heaps.SplayHeapSet.R

theorem deleteMin_bst : ∀ (E : OrderedType), deleteMin_bstStatement E := by
  intro E h hbst
  exact deleteMinBstProof E h hbst

end CompCert4Lean.Lib.Heaps.SplayHeapSet.R

namespace CompCert4Lean.Lib.Heaps.SplayHeapSet.R

theorem gt_heap_In : ∀ (E : OrderedType), gt_heap_InStatement E := by
  intro E x y h
  induction h with
  | Empty =>
      intro hgt hin
      cases hin
  | Node a z b iha ihb =>
      intro hgt hin
      rcases hin with hin | hin | hin
      · exact iha hgt.1 hin
      · exact ltLeTrans E hgt.2.1 (Or.inl (E.eq_sym y z hin))
      · exact ihb hgt.2.2 hin

private def inDeleteMinSize {E : OrderedType} : heap E → Nat
  | .Empty => 0
  | .Node l _ r => inDeleteMinSize l + inDeleteMinSize r + 1

private theorem inDeleteMinAux (E : OrderedType) (y x : E.t) :
    ∀ n (h : heap E), inDeleteMinSize h ≤ n →
      findMin E h = some x →
        (In E y h ↔ E.eq y x ∨ In E y (deleteMin E h)) := by
  intro n
  induction n with
  | zero =>
      intro h hs hfind
      cases h with
      | Empty => simp [findMin] at hfind
      | Node l z r => simp [inDeleteMinSize] at hs
  | succ n ih =>
      intro h hs hfind
      cases h with
      | Empty => simp [findMin] at hfind
      | Node l z r =>
          cases l with
          | Empty =>
              have hx : z = x := by simpa [findMin] using hfind
              subst x
              simp [In, deleteMin]
          | Node a x1 b1 =>
              cases a with
              | Empty =>
                  have hx : x1 = x := by simpa [findMin] using hfind
                  subst x
                  simp [In, deleteMin, or_assoc, or_left_comm, or_comm]
              | Node a0 x0 b0 =>
                  have hfind0 : findMin E (.Node a0 x0 b0) = some x := by
                    simpa [findMin] using hfind
                  have hrec := ih (.Node a0 x0 b0)
                    (by simp [inDeleteMinSize] at hs ⊢; omega) hfind0
                  have htop := or_congr hrec (Iff.rfl :
                    (E.eq y x1 ∨ In E y b1 ∨ E.eq y z ∨ In E y r) ↔
                      (E.eq y x1 ∨ In E y b1 ∨ E.eq y z ∨ In E y r))
                  simpa [In, deleteMin, or_assoc, or_left_comm, or_comm] using htop

theorem In_deleteMin : ∀ (E : OrderedType), In_deleteMinStatement E := by
  intro E y x h hfind
  exact inDeleteMinAux E y x (inDeleteMinSize h) h (Nat.le_refl _) hfind

end CompCert4Lean.Lib.Heaps.SplayHeapSet.R

namespace CompCert4Lean.Lib.Heaps.SplayHeapSet.R

theorem findMin_min : ∀ (E : OrderedType), findMin_minStatement E := by
  intro E x h
  induction h with
  | Empty =>
      intro hfind hbst y hin
      simp [findMin] at hfind
  | Node a z b iha ihb =>
      cases a with
      | Empty =>
          intro hfind hbst y hin
          have hx : z = x := by simpa [findMin] using hfind
          subst x
          have hin' : E.eq y z ∨ In E y b := by simpa [In] using hin
          rcases hin' with hin | hin
          · exact Or.inl (E.eq_sym y z hin)
          · exact Or.inr (gt_heap_In E z y b hbst.2.2.2 hin)
      | Node a1 x1 b1 =>
          intro hfind hbst y hin
          have hfinda : findMin E (Node a1 x1 b1) = some x := by
            simpa [findMin] using hfind
          have hxyA : ∀ w, In E w (Node a1 x1 b1) → le E x w :=
            iha hfinda hbst.1
          have hxx1 : le E x x1 :=
            hxyA x1 (Or.inr (Or.inl (E.eq_refl x1)))
          have hxz : le E x z :=
            Or.inr (le_lt_trans E x x1 z hxx1 hbst.2.2.1.2.1)
          change In E y (Node a1 x1 b1) ∨ E.eq y z ∨ In E y b at hin
          rcases hin with hin | hin | hin
          · exact hxyA y hin
          · exact le_trans E x z y hxz (Or.inl (E.eq_sym y z hin))
          · exact le_trans E x z y hxz
              (Or.inr (gt_heap_In E z y b hbst.2.2.2 hin))

end CompCert4Lean.Lib.Heaps.SplayHeapSet.R

namespace CompCert4Lean.Lib.Heaps.SplayHeapSet.R

theorem findMin_empty (E : OrderedType) : findMin_emptyStatement E := by
  intro h hne
  induction h with
  | Empty => exact False.elim (hne rfl)
  | Node a x b ih =>
      cases a with
      | Empty => simp [findMin]
      | Node a1 x1 b1 =>
          apply ih
          intro heq
          apply hne
          cases heq

end CompCert4Lean.Lib.Heaps.SplayHeapSet.R

namespace CompCert4Lean.Lib.Heaps.SplayHeapSet.R

theorem deleteMax_gt (E : OrderedType) : deleteMax_gtStatement E := by
  intro x h hgt
  exact deleteMaxGtProof E x h hgt

theorem deleteMax_bst (E : OrderedType) : deleteMax_bstStatement E := by
  intro h hbst
  exact deleteMaxBstProof E h hbst

end CompCert4Lean.Lib.Heaps.SplayHeapSet.R

namespace CompCert4Lean.Lib.Heaps.SplayHeapSet.R

private def inDeleteMaxSize {E : OrderedType} : heap E → Nat
  | .Empty => 0
  | .Node l _ r => inDeleteMaxSize l + inDeleteMaxSize r + 1

private theorem inDeleteMaxAux (E : OrderedType) (y x : E.t) :
    ∀ n (h : heap E), inDeleteMaxSize h ≤ n →
      findMax E h = some x →
        (In E y h ↔ E.eq y x ∨ In E y (deleteMax E h)) := by
  intro n
  induction n with
  | zero =>
      intro h hs hfind
      cases h with
      | Empty => simp [findMax] at hfind
      | Node l z r => simp [inDeleteMaxSize] at hs
  | succ n ih =>
      intro h hs hfind
      cases h with
      | Empty => simp [findMax] at hfind
      | Node l z r =>
          cases r with
          | Empty =>
              have hx : z = x := by simpa [findMax] using hfind
              subst x
              simp [In, deleteMax, or_assoc, or_left_comm, or_comm]
          | Node b y1 c =>
              cases c with
              | Empty =>
                  have hx : y1 = x := by simpa [findMax] using hfind
                  subst x
                  simp [In, deleteMax, or_assoc, or_left_comm, or_comm]
              | Node a0 x0 b0 =>
                  have hfind0 : findMax E (.Node a0 x0 b0) = some x := by
                    simpa [findMax] using hfind
                  have hrec := ih (.Node a0 x0 b0)
                    (by simp [inDeleteMaxSize] at hs ⊢; omega) hfind0
                  have htop := or_congr (Iff.rfl :
                    (In E y l ∨ E.eq y z ∨ In E y b ∨ E.eq y y1) ↔
                      (In E y l ∨ E.eq y z ∨ In E y b ∨ E.eq y y1)) hrec
                  simpa [In, deleteMax, or_assoc, or_left_comm, or_comm] using htop

theorem In_deleteMax (E : OrderedType) : In_deleteMaxStatement E := by
  intro y x h hfind
  exact inDeleteMaxAux E y x (inDeleteMaxSize h) h (Nat.le_refl _) hfind

end CompCert4Lean.Lib.Heaps.SplayHeapSet.R

namespace CompCert4Lean.Lib.Heaps.SplayHeapSet.R

theorem lt_heap_In : ∀ (E : OrderedType), lt_heap_InStatement E := by
  intro E x y h
  induction h with
  | Empty =>
      intro hlt hin
      cases hin
  | Node a z b iha ihb =>
      intro hlt hin
      rcases hin with hin | hin | hin
      · exact iha hlt.1 hin
      · exact leLtTrans E (Or.inl hin) hlt.2.1
      · exact ihb hlt.2.2 hin

end CompCert4Lean.Lib.Heaps.SplayHeapSet.R

namespace CompCert4Lean.Lib.Heaps.SplayHeapSet.R

theorem findMax_empty (E : OrderedType) : findMax_emptyStatement E := by
  intro h hne
  induction h with
  | Empty => exact False.elim (hne rfl)
  | Node a x b iha ihb =>
      cases b with
      | Empty => simp [findMax]
      | Node b1 y b2 =>
          apply ihb
          intro heq
          apply hne
          cases heq

end CompCert4Lean.Lib.Heaps.SplayHeapSet.R

namespace CompCert4Lean.Lib.Heaps.SplayHeapSet

theorem In_empty (E : OrderedType) : In_emptyStatement E := by
  intro x
  change ¬ R.In E x R.Empty
  simp [R.In]

end CompCert4Lean.Lib.Heaps.SplayHeapSet

namespace CompCert4Lean.Lib.Heaps.SplayHeapSet

theorem In_insert (E : OrderedType) : In_insertStatement E := by
  intro x h y
  unfold In insert
  exact R.In_insert E x h.1 y h.2

theorem findMin_empty (E : OrderedType) : findMin_emptyStatement E := by
  intro h y hnone hy
  unfold findMin at hnone
  unfold In at hy
  by_cases hne : h.1 = R.Empty
  · simpa [hne, R.In] using hy
  · exact (R.findMin_empty E h.1 hne) hnone

theorem findMin_min (E : OrderedType) : findMin_minStatement E := by
  intro h x y hfind hy
  unfold findMin at hfind
  unfold In at hy
  simpa [R.le] using (R.findMin_min E x h.1 hfind h.2 y hy)

theorem In_deleteMin (E : OrderedType) : In_deleteMinStatement E := by
  intro h x y hfind
  simpa [findMin, In, deleteMin] using (R.In_deleteMin E y x h.1 hfind)

end CompCert4Lean.Lib.Heaps.SplayHeapSet

namespace CompCert4Lean.Lib.Heaps.SplayHeapSet

theorem findMax_empty (E : OrderedType) : findMax_emptyStatement E := by
  intro h y hnone hy
  unfold findMax at hnone
  unfold In at hy
  by_cases hne : h.1 = R.Empty
  · simpa [hne, R.In] using hy
  · exact (R.findMax_empty E h.1 hne) hnone

end CompCert4Lean.Lib.Heaps.SplayHeapSet

namespace CompCert4Lean.Lib.Heaps.PHeap

theorem In_insert_proof : In_insert := by
  exact CompCert4Lean.Lib.Heaps.SplayHeapSet.In_insert positiveOrder

theorem In_deleteMin_proof : In_deleteMin := by
  exact CompCert4Lean.Lib.Heaps.SplayHeapSet.In_deleteMin positiveOrder

theorem In_deleteMax_proof : In_deleteMax := by
  intro h x y hfind
  change (SplayHeapSet.R.In positiveOrder y h.1 ↔
    positiveOrder.eq y x ∨
      SplayHeapSet.R.In positiveOrder y
        (SplayHeapSet.R.deleteMax positiveOrder h.1))
  exact CompCert4Lean.Lib.Heaps.SplayHeapSet.R.In_deleteMax
    positiveOrder y x h.1 hfind

theorem findMax_empty_proof : findMax_empty := by
  exact CompCert4Lean.Lib.Heaps.SplayHeapSet.findMax_empty positiveOrder

end CompCert4Lean.Lib.Heaps.PHeap

namespace CompCert4Lean.Lib.Heaps.PHeap

theorem findMin_empty_proof : findMin_empty := by
  exact CompCert4Lean.Lib.Heaps.SplayHeapSet.findMin_empty positiveOrder

end CompCert4Lean.Lib.Heaps.PHeap
