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

private theorem partitionEq (pivot : E.t) (a : heap E) (x : E.t)
    (b : heap E) {heq : E.eq x pivot}
    (hcmp : E.compare x pivot = .eq heq) :
    partition E pivot (.Node a x b) = (a, b) := by
  rw [partition.eq_def]
  simp only [hcmp]

private theorem partitionLtEmpty (pivot : E.t) (a : heap E) (x : E.t)
    {hlt : E.lt x pivot} (hcmp : E.compare x pivot = .lt hlt) :
    partition E pivot (.Node a x .Empty) = (.Node a x .Empty, .Empty) := by
  rw [partition.eq_def]
  simp only [hcmp]

private theorem partitionLtEq (pivot : E.t) (a : heap E) (x : E.t)
    (b1 : heap E) (y : E.t) (b2 : heap E) {hlt : E.lt x pivot}
    {heq : E.eq y pivot} (hcmp : E.compare x pivot = .lt hlt)
    (hycmp : E.compare y pivot = .eq heq) :
    partition E pivot (.Node a x (.Node b1 y b2)) = (.Node a x b1, b2) := by
  rw [partition.eq_def]
  simp only [hcmp, hycmp]

private theorem partitionLtLt (pivot : E.t) (a : heap E) (x : E.t)
    (b1 : heap E) (y : E.t) (b2 : heap E) {hltx : E.lt x pivot}
    {hlty : E.lt y pivot} (hcmp : E.compare x pivot = .lt hltx)
    (hycmp : E.compare y pivot = .lt hlty) :
    partition E pivot (.Node a x (.Node b1 y b2)) =
      let p := partition E pivot b2
      (.Node (.Node a x b1) y p.1, p.2) := by
  rw [partition.eq_def]
  simp only [hcmp, hycmp]

private theorem partitionLtGt (pivot : E.t) (a : heap E) (x : E.t)
    (b1 : heap E) (y : E.t) (b2 : heap E) {hlt : E.lt x pivot}
    {hgt : E.lt pivot y} (hcmp : E.compare x pivot = .lt hlt)
    (hycmp : E.compare y pivot = .gt hgt) :
    partition E pivot (.Node a x (.Node b1 y b2)) =
      let p := partition E pivot b1
      (.Node a x p.1, .Node p.2 y b2) := by
  rw [partition.eq_def]
  simp only [hcmp, hycmp]

private theorem partitionGtEmpty (pivot : E.t) (x : E.t) (b : heap E)
    {hgt : E.lt pivot x} (hcmp : E.compare x pivot = .gt hgt) :
    partition E pivot (.Node .Empty x b) = (.Empty, .Node .Empty x b) := by
  rw [partition.eq_def]
  simp only [hcmp]

private theorem partitionGtEq (pivot : E.t) (a1 : heap E) (y : E.t)
    (a2 : heap E) (x : E.t) (b : heap E) {hgt : E.lt pivot x}
    {heq : E.eq y pivot} (hcmp : E.compare x pivot = .gt hgt)
    (hycmp : E.compare y pivot = .eq heq) :
    partition E pivot (.Node (.Node a1 y a2) x b) =
      (a1, .Node a2 x b) := by
  rw [partition.eq_def]
  simp only [hcmp, hycmp]

private theorem partitionGtLt (pivot : E.t) (a1 : heap E) (y : E.t)
    (a2 : heap E) (x : E.t) (b : heap E) {hgt : E.lt pivot x}
    {hlt : E.lt y pivot} (hcmp : E.compare x pivot = .gt hgt)
    (hycmp : E.compare y pivot = .lt hlt) :
    partition E pivot (.Node (.Node a1 y a2) x b) =
      let p := partition E pivot a2
      (.Node a1 y p.1, .Node p.2 x b) := by
  rw [partition.eq_def]
  simp only [hcmp, hycmp]

private theorem partitionGtGt (pivot : E.t) (a1 : heap E) (y : E.t)
    (a2 : heap E) (x : E.t) (b : heap E) {hgtx : E.lt pivot x}
    {hgty : E.lt pivot y} (hcmp : E.compare x pivot = .gt hgtx)
    (hycmp : E.compare y pivot = .gt hgty) :
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
    | lt hxz => exact hxz
    | eq hxz =>
        exact False.elim
          (E.lt_not_eq y z hyz (E.eq_trans y x z (E.eq_sym x y hxy) hxz))
    | gt hzx =>
        exact False.elim
          (E.lt_not_eq y x (E.lt_trans y z x hyz hzx) (E.eq_sym x y hxy))
  · exact E.lt_trans x y z hxy hyz

private theorem ltLeTrans {x y z : E.t} (hxy : E.lt x y)
    (hyz : le E y z) : E.lt x z := by
  rcases hyz with hyz | hyz
  · cases E.compare x z with
    | lt hxz => exact hxz
    | eq hxz =>
        exact False.elim
          (E.lt_not_eq x y hxy (E.eq_trans x z y hxz (E.eq_sym y z hyz)))
    | gt hzx =>
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
      | eq _ =>
          simpa only [partitionEq E pivot a y b hcmp, lt_heap] using
            And.intro hlt.1 hlt.2.2
      | lt _ =>
          cases b with
          | Empty =>
              simpa only [partitionLtEmpty E pivot a y hcmp, lt_heap] using
                And.intro hlt trivial
          | Node b1 z b2 =>
              cases hzcmp : E.compare z pivot with
              | eq _ =>
                  simpa only [partitionLtEq E pivot a y b1 z b2 hcmp hzcmp,
                    lt_heap] using
                    And.intro ⟨hlt.1, hlt.2.1, hlt.2.2.1⟩ hlt.2.2.2.2
              | lt _ =>
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
              | gt _ =>
                  have ih := partitionLtProof x pivot b1 hlt.2.2.1
                  cases hp : partition E pivot b1 with
                  | mk small big =>
                      rw [hp] at ih
                      simpa only [partitionLtGt E pivot a y b1 z b2 hcmp hzcmp,
                        hp, lt_heap] using
                        And.intro ⟨hlt.1, hlt.2.1, ih.1⟩
                          ⟨ih.2, hlt.2.2.2.1, hlt.2.2.2.2⟩
      | gt _ =>
          cases a with
          | Empty =>
              simpa only [partitionGtEmpty E pivot y b hcmp, lt_heap] using
                And.intro trivial hlt
          | Node a1 z a2 =>
              cases hzcmp : E.compare z pivot with
              | eq _ =>
                  simpa only [partitionGtEq E pivot a1 z a2 y b hcmp hzcmp,
                    lt_heap] using
                    And.intro hlt.1.1 ⟨hlt.1.2.2, hlt.2.1, hlt.2.2⟩
              | lt _ =>
                  have ih := partitionLtProof x pivot a2 hlt.1.2.2
                  cases hp : partition E pivot a2 with
                  | mk small big =>
                      rw [hp] at ih
                      simpa only [partitionGtLt E pivot a1 z a2 y b hcmp hzcmp,
                        hp, lt_heap] using
                        And.intro ⟨hlt.1.1, hlt.1.2.1, ih.1⟩
                          ⟨ih.2, hlt.2.1, hlt.2.2⟩
              | gt _ =>
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
      | eq _ =>
          simpa only [partitionEq E pivot a y b hcmp, gt_heap] using
            And.intro hgt.1 hgt.2.2
      | lt _ =>
          cases b with
          | Empty =>
              simpa only [partitionLtEmpty E pivot a y hcmp, gt_heap] using
                And.intro hgt trivial
          | Node b1 z b2 =>
              cases hzcmp : E.compare z pivot with
              | eq _ =>
                  simpa only [partitionLtEq E pivot a y b1 z b2 hcmp hzcmp,
                    gt_heap] using
                    And.intro ⟨hgt.1, hgt.2.1, hgt.2.2.1⟩ hgt.2.2.2.2
              | lt _ =>
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
              | gt _ =>
                  have ih := partitionGtProof x pivot b1 hgt.2.2.1
                  cases hp : partition E pivot b1 with
                  | mk small big =>
                      rw [hp] at ih
                      simpa only [partitionLtGt E pivot a y b1 z b2 hcmp hzcmp,
                        hp, gt_heap] using
                        And.intro ⟨hgt.1, hgt.2.1, ih.1⟩
                          ⟨ih.2, hgt.2.2.2.1, hgt.2.2.2.2⟩
      | gt _ =>
          cases a with
          | Empty =>
              simpa only [partitionGtEmpty E pivot y b hcmp, gt_heap] using
                And.intro trivial hgt
          | Node a1 z a2 =>
              cases hzcmp : E.compare z pivot with
              | eq _ =>
                  simpa only [partitionGtEq E pivot a1 z a2 y b hcmp hzcmp,
                    gt_heap] using
                    And.intro hgt.1.1 ⟨hgt.1.2.2, hgt.2.1, hgt.2.2⟩
              | lt _ =>
                  have ih := partitionGtProof x pivot a2 hgt.1.2.2
                  cases hp : partition E pivot a2 with
                  | mk small big =>
                      rw [hp] at ih
                      simpa only [partitionGtLt E pivot a1 z a2 y b hcmp hzcmp,
                        hp, gt_heap] using
                        And.intro ⟨hgt.1.1, hgt.1.2.1, ih.1⟩
                          ⟨ih.2, hgt.2.1, hgt.2.2⟩
              | gt _ =>
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
      | eq hxp =>
          simpa only [partitionEq E pivot a x b hcmp, lt_heap, gt_heap] using
            And.intro
              (ltHeapTrans E (Or.inl hxp) a hbst.2.2.1)
              (gtHeapTrans E (Or.inl (E.eq_sym x pivot hxp)) b hbst.2.2.2)
      | lt hxp =>
          cases b with
          | Empty =>
              simpa only [partitionLtEmpty E pivot a x hcmp, lt_heap, gt_heap]
                using
                And.intro
                  ⟨ltHeapTrans E (Or.inr hxp) a hbst.2.2.1, hxp, trivial⟩
                  trivial
          | Node b1 y b2 =>
              cases hycmp : E.compare y pivot with
              | eq hyp =>
                  simpa only [partitionLtEq E pivot a x b1 y b2 hcmp hycmp,
                    lt_heap, gt_heap] using
                    And.intro
                      ⟨ltHeapTrans E (Or.inr hxp) a hbst.2.2.1, hxp,
                        ltHeapTrans E (Or.inl hyp) b1 hbst.2.1.2.2.1⟩
                      (gtHeapTrans E (Or.inl (E.eq_sym y pivot hyp)) b2
                        hbst.2.1.2.2.2)
              | lt hyp =>
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
              | gt hyp =>
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
      | gt hxp =>
          cases a with
          | Empty =>
              simpa only [partitionGtEmpty E pivot x b hcmp, lt_heap, gt_heap]
                using
                And.intro trivial
                  ⟨trivial, hxp,
                    gtHeapTrans E (Or.inr hxp) b hbst.2.2.2⟩
          | Node a1 y a2 =>
              cases hycmp : E.compare y pivot with
              | eq hyp =>
                  simpa only [partitionGtEq E pivot a1 y a2 x b hcmp hycmp,
                    lt_heap, gt_heap] using
                    And.intro
                      (ltHeapTrans E (Or.inl hyp) a1 hbst.1.2.2.1)
                      ⟨gtHeapTrans E (Or.inl (E.eq_sym y pivot hyp)) a2
                          hbst.1.2.2.2,
                        hxp, gtHeapTrans E (Or.inr hxp) b hbst.2.2.2⟩
              | lt hyp =>
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
              | gt hyp =>
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
      | eq _ =>
          simpa only [partitionEq E pivot a x b hcmp, bst] using
            And.intro hbst.1 hbst.2.1
      | lt _ =>
          cases b with
          | Empty =>
              simpa only [partitionLtEmpty E pivot a x hcmp, bst] using
                And.intro hbst trivial
          | Node b1 y b2 =>
              cases hycmp : E.compare y pivot with
              | eq _ =>
                  simpa only [partitionLtEq E pivot a x b1 y b2 hcmp hycmp,
                    bst] using
                    And.intro
                      ⟨hbst.1, hbst.2.1.1, hbst.2.2.1, hbst.2.2.2.1⟩
                      hbst.2.1.2.1
              | lt _ =>
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
              | gt _ =>
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
      | gt _ =>
          cases a with
          | Empty =>
              simpa only [partitionGtEmpty E pivot x b hcmp, bst] using
                And.intro trivial hbst
          | Node a1 y a2 =>
              cases hycmp : E.compare y pivot with
              | eq _ =>
                  simpa only [partitionGtEq E pivot a1 y a2 x b hcmp hycmp,
                    bst] using
                    And.intro hbst.1.1
                      ⟨hbst.1.2.1, hbst.2.1, hbst.2.2.1.2.2, hbst.2.2.2⟩
              | lt _ =>
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
              | gt _ =>
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

def t : Type := { h : R.heap E // R.bst E h }

def empty : t E := ⟨@R.Empty E, trivial⟩

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
