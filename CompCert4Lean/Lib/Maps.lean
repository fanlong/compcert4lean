import CompCert4Lean.Lib.Coqlib

/-!
# Applicative finite maps

This module is the definition-translation surface for CompCert's `lib/Maps.v`.
The computational tree and map operations are source-shaped; proof-heavy
source declarations are represented below by exact statement descriptors.
-/

namespace CompCert4Lean.Lib.Maps

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib

namespace PTree

def elt : Type := positive
def elt_eq (a b : elt) : CompCert4Lean.Foundation.Logic.Support.Sumbool (a = b) (a ≠ b) :=
  peq a b

inductive tree' (A : Type) : Type where
  | Node001 : tree' A → tree' A
  | Node010 : A → tree' A
  | Node011 : A → tree' A → tree' A
  | Node100 : tree' A → tree' A
  | Node101 : tree' A → tree' A → tree' A
  | Node110 : tree' A → A → tree' A
  | Node111 : tree' A → A → tree' A → tree' A

inductive tree (A : Type) : Type where
  | Empty : tree A
  | Nodes : tree' A → tree A

export tree (Empty Nodes)
export tree' (Node001 Node010 Node011 Node100 Node101 Node110 Node111)

def t (A : Type) : Type := tree A

def Node {A : Type} (l : tree A) (o : Option A) (r : tree A) : tree A :=
  match l, o, r with
  | .Empty, none, .Empty => .Empty
  | .Empty, none, .Nodes r' => .Nodes (.Node001 r')
  | .Empty, some x, .Empty => .Nodes (.Node010 x)
  | .Empty, some x, .Nodes r' => .Nodes (.Node011 x r')
  | .Nodes l', none, .Empty => .Nodes (.Node100 l')
  | .Nodes l', none, .Nodes r' => .Nodes (.Node101 l' r')
  | .Nodes l', some x, .Empty => .Nodes (.Node110 l' x)
  | .Nodes l', some x, .Nodes r' => .Nodes (.Node111 l' x r')

def empty (A : Type) : t A := .Empty

def get' {A : Type} : positive → tree' A → Option A
  | .xH, .Node001 _ => none
  | .xH, .Node010 x => some x
  | .xH, .Node011 x _ => some x
  | .xH, .Node100 _ => none
  | .xH, .Node101 _ _ => none
  | .xH, .Node110 _ x => some x
  | .xH, .Node111 _ x _ => some x
  | .xO q, .Node001 _ => none
  | .xO q, .Node010 _ => none
  | .xO q, .Node011 _ _ => none
  | .xO q, .Node100 m => get' q m
  | .xO q, .Node101 m _ => get' q m
  | .xO q, .Node110 m _ => get' q m
  | .xO q, .Node111 m _ _ => get' q m
  | .xI q, .Node001 m => get' q m
  | .xI q, .Node010 _ => none
  | .xI q, .Node011 _ m => get' q m
  | .xI q, .Node100 _ => none
  | .xI q, .Node101 _ m => get' q m
  | .xI q, .Node110 _ _ => none
  | .xI q, .Node111 _ _ m => get' q m

def get {A : Type} (p : positive) (m : tree A) : Option A :=
  match m with
  | .Empty => none
  | .Nodes m' => get' p m'

def set0 {A : Type} : positive → A → tree' A
  | .xH, x => .Node010 x
  | .xO q, x => .Node100 (set0 q x)
  | .xI q, x => .Node001 (set0 q x)

def set' {A : Type} : positive → A → tree' A → tree' A
  | .xH, x, .Node001 r => .Node011 x r
  | .xH, x, .Node010 _ => .Node010 x
  | .xH, x, .Node011 _ r => .Node011 x r
  | .xH, x, .Node100 l => .Node110 l x
  | .xH, x, .Node101 l r => .Node111 l x r
  | .xH, x, .Node110 l _ => .Node110 l x
  | .xH, x, .Node111 l _ r => .Node111 l x r
  | .xO q, x, .Node001 r => .Node101 (set0 q x) r
  | .xO q, x, .Node010 y => .Node110 (set0 q x) y
  | .xO q, x, .Node011 y r => .Node111 (set0 q x) y r
  | .xO q, x, .Node100 l => .Node100 (set' q x l)
  | .xO q, x, .Node101 l r => .Node101 (set' q x l) r
  | .xO q, x, .Node110 l y => .Node110 (set' q x l) y
  | .xO q, x, .Node111 l y r => .Node111 (set' q x l) y r
  | .xI q, x, .Node001 r => .Node001 (set' q x r)
  | .xI q, x, .Node010 y => .Node011 y (set0 q x)
  | .xI q, x, .Node011 y r => .Node011 y (set' q x r)
  | .xI q, x, .Node100 l => .Node101 l (set0 q x)
  | .xI q, x, .Node101 l r => .Node101 l (set' q x r)
  | .xI q, x, .Node110 l y => .Node111 l y (set0 q x)
  | .xI q, x, .Node111 l y r => .Node111 l y (set' q x r)

def set {A : Type} (p : positive) (x : A) (m : tree A) : tree A :=
  match m with
  | .Empty => .Nodes (set0 p x)
  | .Nodes m' => .Nodes (set' p x m')

def rem' {A : Type} : positive → tree' A → tree A
  | .xH, .Node001 r => .Nodes (.Node001 r)
  | .xH, .Node010 _ => .Empty
  | .xH, .Node011 _ r => .Nodes (.Node001 r)
  | .xH, .Node100 l => .Nodes (.Node100 l)
  | .xH, .Node101 l r => .Nodes (.Node101 l r)
  | .xH, .Node110 l _ => .Nodes (.Node100 l)
  | .xH, .Node111 l _ r => .Nodes (.Node101 l r)
  | .xO q, .Node001 r => .Nodes (.Node001 r)
  | .xO q, .Node010 y => .Nodes (.Node010 y)
  | .xO q, .Node011 y r => .Nodes (.Node011 y r)
  | .xO q, .Node100 l => Node (rem' q l) none .Empty
  | .xO q, .Node101 l r => Node (rem' q l) none (.Nodes r)
  | .xO q, .Node110 l y => Node (rem' q l) (some y) .Empty
  | .xO q, .Node111 l y r => Node (rem' q l) (some y) (.Nodes r)
  | .xI q, .Node001 r => Node .Empty none (rem' q r)
  | .xI q, .Node010 y => .Nodes (.Node010 y)
  | .xI q, .Node011 y r => Node .Empty (some y) (rem' q r)
  | .xI q, .Node100 l => .Nodes (.Node100 l)
  | .xI q, .Node101 l r => Node (.Nodes l) none (rem' q r)
  | .xI q, .Node110 l y => .Nodes (.Node110 l y)
  | .xI q, .Node111 l y r => Node (.Nodes l) (some y) (rem' q r)

def remove' {A : Type} (p : positive) (m : tree' A) : tree A := rem' p m

def remove {A : Type} (p : positive) (m : tree A) : tree A :=
  match m with
  | .Empty => .Empty
  | .Nodes m' => remove' p m'

def not_trivially_empty {A : Type} (l : tree A) (o : Option A) (r : tree A) : Prop :=
  match l, o, r with
  | .Empty, none, .Empty => False
  | _, _, _ => True

def tree_rec' {A B : Type} (emptyCase : B)
    (node : tree A → B → Option A → tree A → B → B) : tree' A → B
  | .Node001 r => node .Empty emptyCase none (.Nodes r) (tree_rec' emptyCase node r)
  | .Node010 x => node .Empty emptyCase (some x) .Empty emptyCase
  | .Node011 x r => node .Empty emptyCase (some x) (.Nodes r) (tree_rec' emptyCase node r)
  | .Node100 l => node (.Nodes l) (tree_rec' emptyCase node l) none .Empty emptyCase
  | .Node101 l r => node (.Nodes l) (tree_rec' emptyCase node l) none (.Nodes r) (tree_rec' emptyCase node r)
  | .Node110 l x => node (.Nodes l) (tree_rec' emptyCase node l) (some x) .Empty emptyCase
  | .Node111 l x r => node (.Nodes l) (tree_rec' emptyCase node l) (some x) (.Nodes r) (tree_rec' emptyCase node r)

def tree_rec {A B : Type} (emptyCase : B)
    (node : tree A → B → Option A → tree A → B → B) (m : tree A) : B :=
  match m with
  | .Empty => emptyCase
  | .Nodes m' => tree_rec' emptyCase node m'

def tree_rec2' {A B C : Type} (base : C) (base1 : tree B → C) (base2 : tree A → C)
    (nodes : tree A → Option A → tree A → tree B → Option B → tree B → C → C → C) :
    tree' A → tree' B → C
  | .Node001 l1, .Node001 l2 => nodes .Empty none (.Nodes l1) .Empty none (.Nodes l2)
      (tree_rec2' base base1 base2 nodes l1 l2) base
  | .Node001 l1, .Node010 x2 => nodes .Empty none (.Nodes l1) .Empty (some x2) .Empty (base2 (.Nodes l1)) base
  | .Node001 l1, .Node011 x2 r2 => nodes .Empty none (.Nodes l1) .Empty (some x2) (.Nodes r2) (base2 (.Nodes l1)) (tree_rec2' base base1 base2 nodes l1 r2)
  | .Node001 l1, .Node100 l2 => nodes .Empty none (.Nodes l1) (.Nodes l2) none .Empty (base1 (.Nodes l2)) (base2 (.Nodes l1))
  | .Node001 l1, .Node101 l2 r2 => nodes .Empty none (.Nodes l1) (.Nodes l2) none (.Nodes r2) (base1 (.Nodes l2)) (tree_rec2' base base1 base2 nodes l1 r2)
  | .Node001 l1, .Node110 l2 x2 => nodes .Empty none (.Nodes l1) (.Nodes l2) (some x2) .Empty (base1 (.Nodes l2)) (base2 (.Nodes l1))
  | .Node001 l1, .Node111 l2 x2 r2 => nodes .Empty none (.Nodes l1) (.Nodes l2) (some x2) (.Nodes r2) (base1 (.Nodes l2)) (tree_rec2' base base1 base2 nodes l1 r2)
  | .Node010 x1, .Node001 l2 => nodes .Empty (some x1) .Empty .Empty none (.Nodes l2) base (base1 (.Nodes l2))
  | .Node010 x1, .Node010 x2 => nodes .Empty (some x1) .Empty .Empty (some x2) .Empty base base
  | .Node010 x1, .Node011 x2 r2 => nodes .Empty (some x1) .Empty .Empty (some x2) (.Nodes r2) base (base1 (.Nodes r2))
  | .Node010 x1, .Node100 l2 => nodes .Empty (some x1) .Empty (.Nodes l2) none .Empty base (base2 .Empty)
  | .Node010 x1, .Node101 l2 r2 => nodes .Empty (some x1) .Empty (.Nodes l2) none (.Nodes r2) base (base2 .Empty)
  | .Node010 x1, .Node110 l2 x2 => nodes .Empty (some x1) .Empty (.Nodes l2) (some x2) .Empty base (base2 .Empty)
  | .Node010 x1, .Node111 l2 x2 r2 => nodes .Empty (some x1) .Empty (.Nodes l2) (some x2) (.Nodes r2) base (base2 .Empty)
  | .Node011 x1 r1, .Node001 l2 => nodes .Empty (some x1) (.Nodes r1) .Empty none (.Nodes l2) (tree_rec2' base base1 base2 nodes r1 l2) (base1 (.Nodes l2))
  | .Node011 x1 r1, .Node010 x2 => nodes .Empty (some x1) (.Nodes r1) .Empty (some x2) .Empty (tree_rec2' base base1 base2 nodes r1 (.Node010 x2)) base
  | .Node011 x1 r1, .Node011 x2 r2 => nodes .Empty (some x1) (.Nodes r1) .Empty (some x2) (.Nodes r2) (tree_rec2' base base1 base2 nodes r1 r2) base
  | .Node011 x1 r1, .Node100 l2 => nodes .Empty (some x1) (.Nodes r1) (.Nodes l2) none .Empty (base1 (.Nodes l2)) (base2 .Empty)
  | .Node011 x1 r1, .Node101 l2 r2 => nodes .Empty (some x1) (.Nodes r1) (.Nodes l2) none (.Nodes r2) (base1 (.Nodes l2)) (tree_rec2' base base1 base2 nodes r1 r2)
  | .Node011 x1 r1, .Node110 l2 x2 => nodes .Empty (some x1) (.Nodes r1) (.Nodes l2) (some x2) .Empty (base1 (.Nodes l2)) (base2 .Empty)
  | .Node011 x1 r1, .Node111 l2 x2 r2 => nodes .Empty (some x1) (.Nodes r1) (.Nodes l2) (some x2) (.Nodes r2) (base1 (.Nodes l2)) (tree_rec2' base base1 base2 nodes r1 r2)
  | .Node100 l1, .Node001 l2 => nodes (.Nodes l1) none .Empty .Empty none (.Nodes l2) (base2 (.Nodes l1)) (base1 (.Nodes l2))
  | .Node100 l1, .Node010 x2 => nodes (.Nodes l1) none .Empty .Empty (some x2) .Empty (base2 (.Nodes l1)) base
  | .Node100 l1, .Node011 x2 r2 => nodes (.Nodes l1) none .Empty .Empty (some x2) (.Nodes r2) (base2 (.Nodes l1)) (tree_rec2' base base1 base2 nodes l1 r2)
  | .Node100 l1, .Node100 l2 => nodes (.Nodes l1) none .Empty (.Nodes l2) none .Empty (base2 (.Nodes l1)) (base1 (.Nodes l2))
  | .Node100 l1, .Node101 l2 r2 => nodes (.Nodes l1) none .Empty (.Nodes l2) none (.Nodes r2) (base2 (.Nodes l1)) (tree_rec2' base base1 base2 nodes l1 r2)
  | .Node100 l1, .Node110 l2 x2 => nodes (.Nodes l1) none .Empty (.Nodes l2) (some x2) .Empty (base2 (.Nodes l1)) (base1 (.Nodes l2))
  | .Node100 l1, .Node111 l2 x2 r2 => nodes (.Nodes l1) none .Empty (.Nodes l2) (some x2) (.Nodes r2) (base2 (.Nodes l1)) (tree_rec2' base base1 base2 nodes l1 r2)
  | .Node101 l1 r1, .Node001 l2 => nodes (.Nodes l1) none (.Nodes r1) .Empty none (.Nodes l2) (tree_rec2' base base1 base2 nodes l1 l2) (base1 (.Nodes l2))
  | .Node101 l1 r1, .Node010 x2 => nodes (.Nodes l1) none (.Nodes r1) .Empty (some x2) .Empty (tree_rec2' base base1 base2 nodes l1 (.Node010 x2)) base
  | .Node101 l1 r1, .Node011 x2 r2 => nodes (.Nodes l1) none (.Nodes r1) .Empty (some x2) (.Nodes r2) (tree_rec2' base base1 base2 nodes l1 (.Node011 x2 r2)) (tree_rec2' base base1 base2 nodes r1 r2)
  | .Node101 l1 r1, .Node100 l2 => nodes (.Nodes l1) none (.Nodes r1) (.Nodes l2) none .Empty (tree_rec2' base base1 base2 nodes l1 l2) (base2 (.Nodes r1))
  | .Node101 l1 r1, .Node101 l2 r2 => nodes (.Nodes l1) none (.Nodes r1) (.Nodes l2) none (.Nodes r2) (tree_rec2' base base1 base2 nodes l1 l2) (tree_rec2' base base1 base2 nodes r1 r2)
  | .Node101 l1 r1, .Node110 l2 x2 => nodes (.Nodes l1) none (.Nodes r1) (.Nodes l2) (some x2) .Empty (tree_rec2' base base1 base2 nodes l1 l2) (base2 (.Nodes r1))
  | .Node101 l1 r1, .Node111 l2 x2 r2 => nodes (.Nodes l1) none (.Nodes r1) (.Nodes l2) (some x2) (.Nodes r2) (tree_rec2' base base1 base2 nodes l1 l2) (tree_rec2' base base1 base2 nodes r1 r2)
  | .Node110 l1 x1, .Node001 l2 => nodes (.Nodes l1) (some x1) .Empty .Empty none (.Nodes l2) (base2 (.Nodes l1)) (base1 (.Nodes l2))
  | .Node110 l1 x1, .Node010 x2 => nodes (.Nodes l1) (some x1) .Empty .Empty (some x2) .Empty (base2 (.Nodes l1)) base
  | .Node110 l1 x1, .Node011 x2 r2 => nodes (.Nodes l1) (some x1) .Empty .Empty (some x2) (.Nodes r2) (base2 (.Nodes l1)) (tree_rec2' base base1 base2 nodes (.Node110 l1 x1) r2)
  | .Node110 l1 x1, .Node100 l2 => nodes (.Nodes l1) (some x1) .Empty (.Nodes l2) none .Empty (base2 (.Nodes l1)) (base1 (.Nodes l2))
  | .Node110 l1 x1, .Node101 l2 r2 => nodes (.Nodes l1) (some x1) .Empty (.Nodes l2) none (.Nodes r2) (base2 (.Nodes l1)) (tree_rec2' base base1 base2 nodes (.Node110 l1 x1) r2)
  | .Node110 l1 x1, .Node110 l2 x2 => nodes (.Nodes l1) (some x1) .Empty (.Nodes l2) (some x2) .Empty (base2 (.Nodes l1)) (base1 (.Nodes l2))
  | .Node110 l1 x1, .Node111 l2 x2 r2 => nodes (.Nodes l1) (some x1) .Empty (.Nodes l2) (some x2) (.Nodes r2) (base2 (.Nodes l1)) (tree_rec2' base base1 base2 nodes (.Node110 l1 x1) r2)
  | .Node111 l1 x1 r1, .Node001 l2 => nodes (.Nodes l1) (some x1) (.Nodes r1) .Empty none (.Nodes l2) (tree_rec2' base base1 base2 nodes l1 l2) (tree_rec2' base base1 base2 nodes r1 l2)
  | .Node111 l1 x1 r1, .Node010 x2 => nodes (.Nodes l1) (some x1) (.Nodes r1) .Empty (some x2) .Empty (tree_rec2' base base1 base2 nodes l1 (.Node010 x2)) (tree_rec2' base base1 base2 nodes r1 (.Node010 x2))
  | .Node111 l1 x1 r1, .Node011 x2 r2 => nodes (.Nodes l1) (some x1) (.Nodes r1) .Empty (some x2) (.Nodes r2) (tree_rec2' base base1 base2 nodes l1 (.Node011 x2 r2)) (tree_rec2' base base1 base2 nodes r1 r2)
  | .Node111 l1 x1 r1, .Node100 l2 => nodes (.Nodes l1) (some x1) (.Nodes r1) (.Nodes l2) none .Empty (tree_rec2' base base1 base2 nodes l1 l2) (tree_rec2' base base1 base2 nodes r1 (.Node100 l2))
  | .Node111 l1 x1 r1, .Node101 l2 r2 => nodes (.Nodes l1) (some x1) (.Nodes r1) (.Nodes l2) none (.Nodes r2) (tree_rec2' base base1 base2 nodes l1 l2) (tree_rec2' base base1 base2 nodes r1 r2)
  | .Node111 l1 x1 r1, .Node110 l2 x2 => nodes (.Nodes l1) (some x1) (.Nodes r1) (.Nodes l2) (some x2) .Empty (tree_rec2' base base1 base2 nodes l1 l2) (tree_rec2' base base1 base2 nodes r1 (.Node110 l2 x2))
  | .Node111 l1 x1 r1, .Node111 l2 x2 r2 => nodes (.Nodes l1) (some x1) (.Nodes r1) (.Nodes l2) (some x2) (.Nodes r2) (tree_rec2' base base1 base2 nodes l1 l2) (tree_rec2' base base1 base2 nodes r1 r2)

def tree_rec2 {A B C : Type} (base : C) (base1 : tree B → C) (base2 : tree A → C)
    (nodes : tree A → Option A → tree A → tree B → Option B → tree B → C → C → C)
    (a : tree A) (b : tree B) : C :=
  match a, b with
  | .Empty, .Empty => base
  | .Empty, _ => base1 b
  | _, .Empty => base2 a
  | .Nodes a', .Nodes b' => tree_rec2' base base1 base2 nodes a' b'

def tree_ind' {A : Type} (P : tree A → Type) (emptyCase : P .Empty)
    (node : ∀ l, P l → ∀ o r, P r → not_trivially_empty l o r → P (Node l o r)) :
    (m : tree' A) → P (.Nodes m)
  | .Node001 r => node .Empty emptyCase none (.Nodes r) (tree_ind' P emptyCase node r) trivial
  | .Node010 x => node .Empty emptyCase (some x) .Empty emptyCase trivial
  | .Node011 x r => node .Empty emptyCase (some x) (.Nodes r) (tree_ind' P emptyCase node r) trivial
  | .Node100 l => node (.Nodes l) (tree_ind' P emptyCase node l) none .Empty emptyCase trivial
  | .Node101 l r => node (.Nodes l) (tree_ind' P emptyCase node l) none (.Nodes r) (tree_ind' P emptyCase node r) trivial
  | .Node110 l x => node (.Nodes l) (tree_ind' P emptyCase node l) (some x) .Empty emptyCase trivial
  | .Node111 l x r => node (.Nodes l) (tree_ind' P emptyCase node l) (some x) (.Nodes r) (tree_ind' P emptyCase node r) trivial

def tree_ind {A : Type} (P : tree A → Type) (emptyCase : P .Empty)
    (node : ∀ l, P l → ∀ o r, P r → not_trivially_empty l o r → P (Node l o r))
    (m : tree A) : P m :=
  match m with
  | .Empty => emptyCase
  | .Nodes m' => tree_ind' P emptyCase node m'

def prev_append : positive → positive → positive
  | .xH, j => j
  | .xI i, j => prev_append i (.xI j)
  | .xO i, j => prev_append i (.xO j)

def prev (i : positive) : positive := prev_append i .xH

def map' {A B : Type} (f : positive → A → B) : tree' A → positive → tree' B
  | .Node001 r, i => .Node001 (map' f r (.xI i))
  | .Node010 x, i => .Node010 (f (prev i) x)
  | .Node011 x r, i => .Node011 (f (prev i) x) (map' f r (.xI i))
  | .Node100 l, i => .Node100 (map' f l (.xO i))
  | .Node101 l r, i => .Node101 (map' f l (.xO i)) (map' f r (.xI i))
  | .Node110 l x, i => .Node110 (map' f l (.xO i)) (f (prev i) x)
  | .Node111 l x r, i => .Node111 (map' f l (.xO i)) (f (prev i) x) (map' f r (.xI i))

def map {A B : Type} (f : positive → A → B) (m : tree A) : tree B :=
  match m with
  | .Empty => .Empty
  | .Nodes m' => .Nodes (map' f m' .xH)

def map1' {A B : Type} (f : A → B) : tree' A → tree' B
  | .Node001 r => .Node001 (map1' f r)
  | .Node010 x => .Node010 (f x)
  | .Node011 x r => .Node011 (f x) (map1' f r)
  | .Node100 l => .Node100 (map1' f l)
  | .Node101 l r => .Node101 (map1' f l) (map1' f r)
  | .Node110 l x => .Node110 (map1' f l) (f x)
  | .Node111 l x r => .Node111 (map1' f l) (f x) (map1' f r)

def map1 {A B : Type} (f : A → B) (m : tree A) : tree B :=
  match m with
  | .Empty => .Empty
  | .Nodes m' => .Nodes (map1' f m')

def map_filter1_nonopt {A B : Type} (f : A → Option B) (m : tree A) : tree B :=
  tree_rec .Empty
    (fun l lrec o r rrec =>
      Node lrec (match o with | none => none | some a => f a) rrec) m

def map_filter1 {A B : Type} (f : A → Option B) (m : tree A) : tree B :=
  map_filter1_nonopt f m

def combineOpt {A B C : Type} (f : Option A → Option B → Option C)
    (o1 : Option A) (o2 : Option B) : Option C :=
  match o1, o2 with
  | none, none => none
  | none, some b => f none (some b)
  | some a, none => f (some a) none
  | some a, some b => f (some a) (some b)

def combine {A B C : Type} (f : Option A → Option B → Option C)
    (m1 : tree A) (m2 : tree B) : tree C :=
  tree_rec2 .Empty
    (map_filter1 (fun b => f none (some b)))
    (map_filter1 (fun a => f (some a) none))
    (fun l1 o1 r1 l2 o2 r2 lrec rrec => Node lrec (combineOpt f o1 o2) rrec)
    m1 m2

def xelements' {A : Type} : tree' A → positive → List (positive × A) → List (positive × A)
  | .Node001 r, i, k => xelements' r (.xI i) k
  | .Node010 x, i, k => (prev i, x) :: k
  | .Node011 x r, i, k => (prev i, x) :: xelements' r (.xI i) k
  | .Node100 l, i, k => xelements' l (.xO i) k
  | .Node101 l r, i, k => xelements' l (.xO i) (xelements' r (.xI i) k)
  | .Node110 l x, i, k => xelements' l (.xO i) ((prev i, x) :: k)
  | .Node111 l x r, i, k => xelements' l (.xO i) ((prev i, x) :: xelements' r (.xI i) k)

def xelements {A : Type} (m : tree A) (i : positive) : List (positive × A) :=
  match m with
  | .Empty => []
  | .Nodes m' => xelements' m' i []

def elements {A : Type} (m : tree A) : List (positive × A) := xelements m .xH

def xkeys {A : Type} (m : tree A) (i : positive) : List positive :=
  (xelements m i).map Prod.fst

def fold' {A B : Type} (f : B → positive → A → B) : positive → tree' A → B → B
  | i, .Node001 r, v => fold' f (.xI i) r v
  | i, .Node010 x, v => f v (prev i) x
  | i, .Node011 x r, v => fold' f (.xI i) r (f v (prev i) x)
  | i, .Node100 l, v => fold' f (.xO i) l v
  | i, .Node101 l r, v => fold' f (.xI i) r (fold' f (.xO i) l v)
  | i, .Node110 l x, v => f (fold' f (.xO i) l v) (prev i) x
  | i, .Node111 l x r, v => fold' f (.xI i) r (f (fold' f (.xO i) l v) (prev i) x)

def fold {A B : Type} (f : B → positive → A → B) (m : tree A) (v : B) : B :=
  match m with
  | .Empty => v
  | .Nodes m' => fold' f .xH m' v

def option_rel {A B : Type} (R : A → B → Prop) : Option A → Option B → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

def list_norepet {A : Type} (l : List A) : Prop := l.Nodup
inductive list_forall2 {A B : Type} (R : A → B → Prop) : List A → List B → Prop where
  | nil : list_forall2 R [] []
  | cons {a : A} {b : B} {as bs : List _} : R a b → list_forall2 R as bs → list_forall2 R (a :: as) (b :: bs)

def gemptyStatement : Prop := ∀ (A : Type) (i : positive), get i (empty A) = none
def gss0Statement : Prop := ∀ {A : Type} (p : positive) (x : A), get' p (set0 p x) = some x
def gso0Statement : Prop := ∀ {A : Type} (p q : positive) (x : A), p ≠ q → get' p (set0 q x) = none
def gssStatement : Prop := ∀ (A : Type) (i : positive) (x : A) (m : tree A), get i (set i x m) = some x
def gsoStatement : Prop := ∀ (A : Type) (i j : positive) (x : A) (m : tree A), i ≠ j → get i (set j x m) = get i m
def gsspecStatement : Prop := ∀ (A : Type) (i j : positive) (x : A) (m : t A),
  get i (set j x m) = if h : i = j then some x else get i m
def gNodeStatement : Prop := ∀ {A : Type} (i : positive) (l : tree A) (x : Option A) (r : tree A),
  get i (Node l x r) = match i with | .xH => x | .xO j => get j l | .xI j => get j r
def grsStatement : Prop := ∀ (A : Type) (i : positive) (m : tree A), get i (remove i m) = none
def groStatement : Prop := ∀ (A : Type) (i j : positive) (m : tree A), i ≠ j → get i (remove j m) = get i m
def grspecStatement : Prop := ∀ (A : Type) (i j : elt) (m : t A),
  get i (remove j m) = match elt_eq i j with | .left _ => none | .right _ => get i m

def unroll_tree_recStatement : Prop :=
  ∀ {A B : Type} (emptyCase : B)
    (node : tree A → B → Option A → tree A → B → B)
    (l : tree A) (o : Option A) (r : tree A),
    not_trivially_empty l o r →
    tree_rec emptyCase node (Node l o r) = node l (tree_rec emptyCase node l) o r (tree_rec emptyCase node r)
def unroll_tree_rec2_NEStatement : Prop :=
  ∀ {A B C : Type} (base : C) (base1 : tree B → C) (base2 : tree A → C)
    (nodes : tree A → Option A → tree A → tree B → Option B → tree B → C → C → C)
    (l1 : tree A) (o1 : Option A) (r1 : tree A),
    not_trivially_empty l1 o1 r1 →
    tree_rec2 base base1 base2 nodes (Node l1 o1 r1) .Empty = base2 (Node l1 o1 r1)
def unroll_tree_rec2_ENStatement : Prop :=
  ∀ {A B C : Type} (base : C) (base1 : tree B → C) (base2 : tree A → C)
    (nodes : tree A → Option A → tree A → tree B → Option B → tree B → C → C → C)
    (l2 : tree B) (o2 : Option B) (r2 : tree B),
    not_trivially_empty l2 o2 r2 →
    tree_rec2 base base1 base2 nodes .Empty (Node l2 o2 r2) = base1 (Node l2 o2 r2)
def unroll_tree_rec2_NNStatement : Prop :=
  ∀ {A B C : Type} (base : C) (base1 : tree B → C) (base2 : tree A → C)
    (nodes : tree A → Option A → tree A → tree B → Option B → tree B → C → C → C)
    (l1 : tree A) (o1 : Option A) (r1 : tree A) (l2 : tree B) (o2 : Option B) (r2 : tree B),
    not_trivially_empty l1 o1 r1 → not_trivially_empty l2 o2 r2 →
    tree_rec2 base base1 base2 nodes (Node l1 o1 r1) (Node l2 o2 r2) =
      nodes l1 o1 r1 l2 o2 r2
        (tree_rec2 base base1 base2 nodes l1 l2)
        (tree_rec2 base base1 base2 nodes r1 r2)

def tree'_not_emptyStatement : Prop := ∀ {A : Type} (m : tree' A), ∃ i, get' i m ≠ none
def extensionality_emptyStatement : Prop := ∀ {A : Type} (m : tree A), (∀ i, get i m = none) → m = .Empty
def extensionalityStatement : Prop := ∀ (A : Type) (m1 m2 : tree A), (∀ i, get i m1 = get i m2) → m1 = m2
def gsidentStatement : Prop := ∀ {A : Type} (i : positive) (m : t A) (v : A), get i m = some v → set i v m = m
def set2Statement : Prop := ∀ {A : Type} (i : elt) (m : t A) (v1 v2 : A), set i v2 (set i v1 m) = set i v2 m

def prev_append_prevStatement : Prop := ∀ (i j : positive), prev (prev_append i j) = prev_append j i
def prev_involutiveStatement : Prop := ∀ (i : positive), prev (prev i) = i
def prev_append_injStatement : Prop := ∀ (i j j' : positive), prev_append i j = prev_append i j' → j = j'
def gmap'Statement : Prop := ∀ {A B : Type} (f : positive → A → B) (i j : positive) (m : tree' A),
  get' i (map' f m j) = Option.map (f (prev (prev_append i j))) (get' i m)
def gmapStatement : Prop := ∀ {A B : Type} (f : positive → A → B) (i : positive) (m : t A),
  get i (map f m) = Option.map (f i) (get i m)
def gmap1Statement : Prop := ∀ {A B : Type} (f : A → B) (i : elt) (m : t A),
  get i (map1 f m) = Option.map f (get i m)
def gmap_filter1Statement : Prop := ∀ {A B : Type} (f : A → Option B) (m : tree A) (i : positive),
  get i (map_filter1 f m) = match get i m with | none => none | some a => f a
def gcombine_lStatement : Prop := ∀ {A B C : Type} (f : Option A → Option B → Option C)
  (m : tree A) (i : positive), get i (map_filter1 (fun a => f (some a) none) m) = f (get i m) none
def gcombine_rStatement : Prop := ∀ {A B C : Type} (f : Option A → Option B → Option C)
  (m : tree B) (i : positive), get i (map_filter1 (fun b => f none (some b)) m) = f none (get i m)
def gcombineStatement : Prop := ∀ {A B C : Type} (f : Option A → Option B → Option C)
  (m1 : t A) (m2 : t B) (i : positive), get i (combine f m1 m2) = f (get i m1) (get i m2)

def xelements'_appendStatement : Prop := ∀ (A : Type) (m : tree' A) (i : positive) (k1 k2 : List (positive × A)),
  xelements' m i (k1 ++ k2) = xelements' m i k1 ++ k2
def xelements_NodeStatement : Prop := ∀ (A : Type) (l : tree A) (o : Option A) (r : tree A) (i : positive),
  xelements (Node l o r) i = xelements l (.xO i) ++ (match o with | none => [] | some v => [(prev i, v)]) ++ xelements r (.xI i)
def xelements_correctStatement : Prop := ∀ (A : Type) (m : tree A) (i j : positive) (v : A),
  get i m = some v → (prev (prev_append i j), v) ∈ xelements m j
def elements_correctStatement : Prop := ∀ (A : Type) (m : t A) (i : positive) (v : A),
  get i m = some v → (i, v) ∈ elements m
def in_xelementsStatement : Prop := ∀ (A : Type) (m : tree A) (i k : positive) (v : A),
  (k, v) ∈ xelements m i → ∃ j, k = prev (prev_append j i) ∧ get j m = some v
def elements_completeStatement : Prop := ∀ (A : Type) (m : t A) (i : positive) (v : A),
  (i, v) ∈ elements m → get i m = some v
def xkeys_NodeStatement : Prop := ∀ (A : Type) (m1 : t A) (o : Option A) (m2 : t A) (i : positive),
  xkeys (Node m1 o m2) i = xkeys m1 (.xO i) ++ (match o with | none => [] | some v => [prev i]) ++ xkeys m2 (.xI i)
def in_xkeysStatement : Prop := ∀ (A : Type) (m : t A) (i k : positive), k ∈ xkeys m i → ∃ j, k = prev (prev_append j i)
def xelements_keys_norepetStatement : Prop := ∀ (A : Type) (m : t A) (i : positive), list_norepet (xkeys m i)
def elements_keys_norepetStatement : Prop := ∀ (A : Type) (m : t A), list_norepet ((elements m).map Prod.fst)
def elements_canonical_order'Statement : Prop := ∀ {A B : Type} (R : A → B → Prop) (m : t A) (n : t B),
  (∀ i, option_rel R (get i m) (get i n)) →
  list_forall2 (fun p q => p.1 = q.1 ∧ R p.2 q.2) (elements m) (elements n)
def elements_canonical_orderStatement : Prop := ∀ {A B : Type} (R : A → B → Prop) (m : t A) (n : t B),
  (∀ i x, get i m = some x → ∃ y, get i n = some y ∧ R x y) →
  (∀ i y, get i n = some y → ∃ x, get i m = some x ∧ R x y) →
  list_forall2 (fun p q => p.1 = q.1 ∧ R p.2 q.2) (elements m) (elements n)
def fold'_xelements'Statement : Prop := ∀ (A B : Type) (f : B → positive → A → B) (m : tree' A)
  (i : positive) (v : B) (l : List (positive × A)),
  List.foldl (fun a p => f a p.1 p.2) (fold' f i m v) l =
    List.foldl (fun a p => f a p.1 p.2) v (xelements' m i l)
def fold_specStatement : Prop := ∀ (A B : Type) (f : B → positive → A → B) (v : B) (m : t A),
  fold f m v = List.foldl (fun a p => f a p.1 p.2) v (elements m)

private theorem getSet0_proof (A : Type) (x y : positive) (v : A) :
    get' x (set0 y v) = if h : x = y then some v else none := by
  induction x generalizing y with
  | xH =>
      cases y <;> simp [set0, get']
  | xO x ih =>
      cases y with
      | xH => simp [set0, get']
      | xO y => simp [set0, get', ih]
      | xI y => simp [set0, get']
  | xI x ih =>
      cases y with
      | xH => simp [set0, get']
      | xO y => simp [set0, get']
      | xI y => simp [set0, get', ih]

private theorem getSet'_proof (A : Type) (x y : positive) (v : A)
    (m : tree' A) :
    get' x (set' y v m) = if h : x = y then some v else get' x m := by
  induction x generalizing y m with
  | xH =>
      cases y <;> cases m <;> simp [set', get']
  | xO x ih =>
      cases y with
      | xH => cases m <;> simp [set', get']
      | xO y => cases m <;> simp [set', get', ih, getSet0_proof]
      | xI y => cases m <;> simp [set', get', getSet0_proof]
  | xI x ih =>
      cases y with
      | xH => cases m <;> simp [set', get']
      | xO y => cases m <;> simp [set', get', getSet0_proof]
      | xI y => cases m <;> simp [set', get', ih, getSet0_proof]

private theorem getSet_proof (A : Type) (x y : positive) (v : A)
    (m : tree A) :
    get x (set y v m) = if h : x = y then some v else get x m := by
  cases m with
  | Empty => simpa [get, set] using getSet0_proof A x y v
  | Nodes m => simpa [get, set] using getSet'_proof A x y v m

theorem gsspec_proof : gsspecStatement := by
  intro A i j x m
  exact getSet_proof A i j x m

theorem getSet_equation {A : Type} (i j : positive) (x : A) (m : tree A) :
    get i (set j x m) = if h : i = j then some x else get i m :=
  getSet_proof A i j x m

private theorem getNode_equation {A : Type} (i : positive) (l : tree A)
    (o : Option A) (r : tree A) :
    get i (Node l o r) = match i with
      | .xH => o
      | .xO j => get j l
      | .xI j => get j r := by
  cases i <;> cases l <;> cases o <;> cases r <;> rfl

private theorem getNodes_equation {A : Type} (i : positive) (m : tree' A) :
    get i (Nodes m) = get' i m := rfl

private theorem getEmpty_equation {A : Type} (i : positive) :
    get i (Empty : tree A) = none := rfl

theorem gNode_proof : gNodeStatement := by
  intro A i l o r
  cases i <;> cases l <;> cases o <;> cases r <;> rfl

private theorem getRemove'_proof {A : Type} (x y : positive) (m : tree' A) :
    get x (rem' y m) = if h : x = y then none else get' x m := by
  induction x generalizing y m with
  | xH =>
      cases y <;> cases m <;> simp [rem', get', getNode_equation, getNodes_equation, getEmpty_equation]
  | xO x ih =>
      cases y with
      | xH => cases m <;> simp [rem', get', getNode_equation, getNodes_equation, getEmpty_equation]
      | xO y =>
          cases m <;> simp [rem', get', getNode_equation, getNodes_equation, getEmpty_equation, ih]
      | xI y => cases m <;> simp [rem', get', getNode_equation, getNodes_equation, getEmpty_equation]
  | xI x ih =>
      cases y with
      | xH => cases m <;> simp [rem', get', getNode_equation, getNodes_equation, getEmpty_equation]
      | xO y => cases m <;> simp [rem', get', getNode_equation, getNodes_equation, getEmpty_equation]
      | xI y =>
          cases m <;> simp [rem', get', getNode_equation, getNodes_equation, getEmpty_equation, ih]

private theorem getRemove_proof {A : Type} (x y : positive) (m : tree A) :
    get x (remove y m) = if h : x = y then none else get x m := by
  cases m with
  | Empty => simp [remove, get]
  | Nodes m => simpa [remove, get, remove'] using getRemove'_proof x y m

theorem getRemove_equation {A : Type} (x y : positive) (m : tree A) :
    get x (remove y m) = if h : x = y then none else get x m :=
  getRemove_proof x y m

theorem grspec_proof : grspecStatement := by
  intro A i j m
  unfold elt at i j ⊢
  change get i (remove j m) = _
  cases h : peq i j with
  | left hij =>
      subst j
      have hremove : get i (remove i m) = none := by
        calc
          get i (remove i m) = if h : i = i then none else get i m :=
            getRemove_proof (A := A) i i m
          _ = none := by simp
      simpa [elt_eq, h] using hremove
  | right hne =>
      have hremove : get i (remove j m) = get i m := by
        simpa [hne] using (getRemove_proof (A := A) i j m)
      simpa [elt_eq, h, hne] using hremove

theorem grs_proof : grsStatement := by
  intro A i m
  simpa using getRemove_proof i i m

theorem gro_proof : groStatement := by
  intro A i j m h
  simpa [h] using getRemove_proof i j m

private theorem foldl_step (g : B → (positive × A) → B) (a : B)
    (p : positive × A) (l : List (positive × A)) :
    List.foldl g (g a p) l = List.foldl g a (p :: l) := by
  induction l generalizing a with
  | nil => rfl
  | cons q l ih => simp [List.foldl, ih]

private theorem foldl_step' {A B : Type} (f : B → positive → A → B)
    (a : B) (k : positive) (v : A) (l : List (positive × A)) :
    List.foldl (fun a p => f a p.1 p.2) (f a k v) l =
      List.foldl (fun a p => f a p.1 p.2) a ((k, v) :: l) := by
  induction l generalizing a with
  | nil => rfl
  | cons q l ih => simp [List.foldl, ih]

private theorem fold'_xelements'_proof : fold'_xelements'Statement := by
  intro A B f m i v l
  induction m generalizing i v l <;>
    simp_all [fold', xelements', List.foldl, List.foldl_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  all_goals rw [foldl_step']
  all_goals simp_all [List.foldl_append]

theorem fold_spec_proof : fold_specStatement := by
  intro A B f v m
  cases m with
  | Empty => rfl
  | Nodes m =>
      simpa [fold, elements, xelements, fold'_xelements'Statement] using
        (fold'_xelements'_proof (A := A) (B := B) f m .xH v [])

private theorem prev_append_xI (i j : positive) :
    prev (prev_append i (xI j)) = prev (prev_append (xI i) j) := by
  induction i with
  | xH => rfl
  | xI i ih => simp [prev, prev_append, ih]
  | xO i ih => simp [prev, prev_append, ih]

private theorem prev_append_xO (i j : positive) :
    prev (prev_append i (xO j)) = prev (prev_append (xO i) j) := by
  induction i with
  | xH => rfl
  | xI i ih => simp [prev, prev_append, ih]
  | xO i ih => simp [prev, prev_append, ih]

private theorem mem_suffix_xelements' {A : Type} (m : tree' A) (i : positive)
    (suffix : List (positive × A)) (p : positive × A) :
    p ∈ suffix → p ∈ xelements' m i suffix := by
  induction m generalizing i suffix p with
  | Node001 r ih => exact ih (xI i) suffix p
  | Node010 x =>
      intro h
      exact List.mem_cons_of_mem _ h
  | Node011 x r ih =>
      intro h
      exact List.mem_cons_of_mem _ (ih (xI i) suffix p h)
  | Node100 l ih => exact ih (xO i) suffix p
  | Node101 l r ihl ihr =>
      intro h
      have hr : p ∈ xelements' r (xI i) suffix :=
        ihr (xI i) suffix p h
      exact ihl (xO i) (xelements' r (xI i) suffix) p (by
        simp [hr])
  | Node110 l x ih =>
      intro h
      exact ih (xO i) ((prev i, x) :: suffix) p (List.mem_cons_of_mem _ h)
  | Node111 l x r ihl ihr =>
      intro h
      have hr : p ∈ xelements' r (xI i) suffix :=
        ihr (xI i) suffix p h
      exact ihl (xO i) ((prev i, x) :: xelements' r (xI i) suffix) p (by
        simp [hr])

private theorem get_xelements'_correct {A : Type} (m : tree' A) (i j : positive)
    (v : A) (suffix : List (positive × A)) :
    get' i m = some v →
      (prev (prev_append i j), v) ∈ xelements' m j suffix := by
  induction m generalizing i j suffix with
  | Node001 r ih =>
      cases i with
      | xH => simp [get']
      | xO q => simp [get']
      | xI q =>
          intro h
          simpa [get', xelements', prev_append_xI] using (ih q (xI j) suffix h)
  | Node010 x =>
      cases i with
      | xH =>
          intro h
          cases h
          simp [xelements', prev_append]
      | xO q => simp [get']
      | xI q => simp [get']
  | Node011 x r ih =>
      cases i with
      | xH =>
          intro h
          cases h
          simp [xelements', prev_append]
      | xO q => simp [get']
      | xI q =>
          intro h
          have hp : (prev (prev_append (xI q) j), v) ∈
              xelements' r (xI j) suffix := by
            simpa [prev_append_xI] using (ih q (xI j) suffix h)
          exact List.mem_cons_of_mem (prev j, x) hp
  | Node100 l ih =>
      cases i with
      | xH => simp [get']
      | xO q =>
          intro h
          simpa [get', xelements', prev_append_xO] using (ih q (xO j) suffix h)
      | xI q => simp [get']
  | Node101 l r ihl ihr =>
      cases i with
      | xH => simp [get']
      | xO q =>
          intro h
          simpa [get', xelements', prev_append_xO] using
            (ihl q (xO j) (xelements' r (xI j) suffix) h)
      | xI q =>
          intro h
          have hp := ihr q (xI j) suffix h
          exact mem_suffix_xelements' l (xO j) (xelements' r (xI j) suffix) _
            (by simpa [get', xelements', prev_append_xI] using hp)
  | Node110 l x ih =>
      cases i with
      | xH =>
          intro h
          have hv : x = v := Option.some.inj h
          subst v
          exact mem_suffix_xelements' l (xO j) ((prev j, x) :: suffix) (prev j, x) (by simp)
      | xO q =>
          intro h
          simpa [get', xelements', prev_append_xO] using
            (ih q (xO j) ((prev j, x) :: suffix) h)
      | xI q => simp [get']
  | Node111 l x r ihl ihr =>
      cases i with
      | xH =>
          intro h
          have hv : x = v := Option.some.inj h
          subst v
          exact mem_suffix_xelements' l (xO j)
            ((prev j, x) :: xelements' r (xI j) suffix) (prev j, x) (by simp)
      | xO q =>
          intro h
          simpa [get', xelements', prev_append_xO] using
            (ihl q (xO j) ((prev j, x) :: xelements' r (xI j) suffix) h)
      | xI q =>
          intro h
          have hp : (prev (prev_append (xI q) j), v) ∈
              xelements' r (xI j) suffix := by
            simpa [prev_append_xI] using (ihr q (xI j) suffix h)
          exact mem_suffix_xelements' l (xO j)
            ((prev j, x) :: xelements' r (xI j) suffix)
            (prev (prev_append (xI q) j), v) (by simp [hp])


private theorem prev_append_swap (i j : positive) :
    prev (prev_append i j) = prev_append j i := by
  induction i generalizing j with
  | xH => rfl
  | xI i ih =>
      change prev (prev_append i (xI j)) = prev_append j (xI i)
      rw [ih (xI j)]
      rfl
  | xO i ih =>
      change prev (prev_append i (xO j)) = prev_append j (xO i)
      rw [ih (xO j)]
      rfl

private theorem prev_involutive (i : positive) : prev (prev i) = i := by
  have h := prev_append_swap i xH
  simpa [prev, prev_append] using h

theorem elements_correct_proof : elements_correctStatement := by
  intro A m i v h
  cases m with
  | Empty => simp [elements, xelements, get] at h
  | Nodes m =>
      have h' : get' i m = some v := by simpa [get] using h
      have hc := get_xelements'_correct m i .xH v [] h'
      have hkey : prev (prev_append i xH) = i := by
        change prev (prev i) = i
        exact prev_involutive i
      simpa [elements, xelements, hkey] using hc

private theorem xelements'_append_equation {A : Type} (m : tree' A) (i : positive)
    (k1 k2 : List (positive × A)) :
    xelements' m i (k1 ++ k2) = xelements' m i k1 ++ k2 := by
  induction m generalizing i k1 k2 with
  | Node001 r ih => exact ih (xI i) k1 k2
  | Node010 x => simp [xelements']
  | Node011 x r ih => simp [xelements', ih, List.append_assoc]
  | Node100 l ih => exact ih (xO i) k1 k2
  | Node101 l r ihl ihr =>
      simp [xelements', ihl, ihr, List.append_assoc]
  | Node110 l x ih =>
      change xelements' l (xO i) ((prev i, x) :: (k1 ++ k2)) =
        xelements' l (xO i) ((prev i, x) :: k1) ++ k2
      exact ih (xO i) ((prev i, x) :: k1) k2
  | Node111 l x r ihl ihr =>
      simp only [xelements']
      rw [ihr (xI i) k1 k2]
      exact ihl (xO i) ((prev i, x) :: xelements' r (xI i) k1) k2

private theorem in_xelements'_complete {A : Type} (m : tree' A) (i : positive)
    (p : positive × A) :
    p ∈ xelements' m i [] →
      ∃ j, p.1 = prev (prev_append j i) ∧ get' j m = some p.2 := by
  induction m generalizing i p with
  | Node001 r ih =>
      intro h
      have hr := ih (xI i) p (by simpa [xelements'] using h)
      rcases hr with ⟨j, hj, hget⟩
      refine ⟨xI j, ?_, ?_⟩
      · simpa [prev_append] using hj
      · simpa [get'] using hget
  | Node010 x =>
      intro h
      rcases p with ⟨k, v⟩
      simp [xelements'] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨xH, by simp [prev_append], by simp [get']⟩
  | Node011 x r ih =>
      intro h
      rcases p with ⟨k, v⟩
      simp [xelements'] at h
      rcases h with h | h
      · have hp : (k, v) = (prev i, x) := by simpa using h
        rcases hp with ⟨rfl, rfl⟩
        exact ⟨xH, by simp [prev_append], by simp [get']⟩
      · have hr := ih (xI i) (k, v) h
        rcases hr with ⟨j, hj, hget⟩
        refine ⟨xI j, ?_, ?_⟩
        · simpa [prev_append] using hj
        · simpa [get'] using hget
  | Node100 l ih =>
      intro h
      have hl := ih (xO i) p (by simpa [xelements'] using h)
      rcases hl with ⟨j, hj, hget⟩
      refine ⟨xO j, ?_, ?_⟩
      · simpa [prev_append] using hj
      · simpa [get'] using hget
  | Node101 l r ihl ihr =>
      intro h
      change p ∈ xelements' l (xO i) (xelements' r (xI i) []) at h
      have hsplit : xelements' l (xO i) (xelements' r (xI i) []) =
          xelements' l (xO i) [] ++ xelements' r (xI i) [] := by
        simpa using (xelements'_append_equation l (xO i) [] (xelements' r (xI i) []))
      rw [hsplit] at h
      simp only [List.mem_append] at h
      rcases h with h | h
      · have hl := ihl (xO i) p h
        rcases hl with ⟨j, hj, hget⟩
        refine ⟨xO j, ?_, ?_⟩
        · simpa [prev_append] using hj
        · simpa [get'] using hget
      · have hr := ihr (xI i) p h
        rcases hr with ⟨j, hj, hget⟩
        refine ⟨xI j, ?_, ?_⟩
        · simpa [prev_append] using hj
        · simpa [get'] using hget
  | Node110 l x ih =>
      intro h
      rcases p with ⟨k, v⟩
      change (k, v) ∈ xelements' l (xO i) [(prev i, x)] at h
      have hsplit : xelements' l (xO i) [(prev i, x)] =
          xelements' l (xO i) [] ++ [(prev i, x)] := by
        simpa using (xelements'_append_equation l (xO i) [] [(prev i, x)])
      rw [hsplit] at h
      simp only [List.mem_append] at h
      rcases h with h | h
      · have hl := ih (xO i) (k, v) h
        rcases hl with ⟨j, hj, hget⟩
        refine ⟨xO j, ?_, ?_⟩
        · simpa [prev_append] using hj
        · simpa [get'] using hget
      · have hp : (k, v) = (prev i, x) := by simpa using h
        rcases hp with ⟨rfl, rfl⟩
        exact ⟨xH, by simp [prev_append], by simp [get']⟩
  | Node111 l x r ihl ihr =>
      intro h
      rcases p with ⟨k, v⟩
      change (k, v) ∈ xelements' l (xO i)
        ((prev i, x) :: xelements' r (xI i) []) at h
      have hsplit : xelements' l (xO i)
          ((prev i, x) :: xelements' r (xI i) []) =
          xelements' l (xO i) [] ++
            ((prev i, x) :: xelements' r (xI i) []) := by
        simpa using (xelements'_append_equation l (xO i) []
          ((prev i, x) :: xelements' r (xI i) []))
      rw [hsplit] at h
      simp only [List.mem_append] at h
      rcases h with h | h
      · have hl := ihl (xO i) (k, v) h
        rcases hl with ⟨j, hj, hget⟩
        refine ⟨xO j, ?_, ?_⟩
        · simpa [prev_append] using hj
        · simpa [get'] using hget
      · simp only [List.mem_cons] at h
        rcases h with h | h
        · have hp : (k, v) = (prev i, x) := by simpa using h
          rcases hp with ⟨rfl, rfl⟩
          exact ⟨xH, by simp [prev_append], by simp [get']⟩
        · have hr := ihr (xI i) (k, v) h
          rcases hr with ⟨j, hj, hget⟩
          refine ⟨xI j, ?_, ?_⟩
          · simpa [prev_append] using hj
          · simpa [get'] using hget

private theorem prev_append_injective (i : positive) :
    Function.Injective (prev_append i) := by
  induction i with
  | xH => intro j k h; exact h
  | xI i ih =>
      intro j k h
      have h' : xI j = xI k := ih h
      cases h'
      rfl
  | xO i ih =>
      intro j k h
      have h' : xO j = xO k := ih h
      cases h'
      rfl

private theorem key_form_xelements' {A : Type} (m : tree' A) (i : positive)
    (p : positive × A) (h : p ∈ xelements' m i []) :
    ∃ j, p.1 = prev_append i j := by
  rcases in_xelements'_complete m i p h with ⟨j, hj, _⟩
  exact ⟨j, by simpa [prev_append_swap] using hj⟩

private theorem keys_disjoint_xO_xI {A B : Type} (l : tree' A) (r : tree' B)
    (i : positive) :
    ∀ k, k ∈ (xelements' l (xO i) []).map Prod.fst →
      k ∉ (xelements' r (xI i) []).map Prod.fst := by
  intro k hl hr
  rcases List.mem_map.mp hl with ⟨p, hp, rfl⟩
  rcases List.mem_map.mp hr with ⟨q, hq, hkey⟩
  rcases key_form_xelements' l (xO i) p hp with ⟨j, hj⟩
  rcases key_form_xelements' r (xI i) q hq with ⟨k, hk⟩
  have heq : prev_append i (xO j) = prev_append i (xI k) := by
    calc
      prev_append i (xO j) = p.1 := by simpa [prev_append] using hj.symm
      _ = q.1 := hkey.symm
      _ = prev_append i (xI k) := by simpa [prev_append] using hk
  have hbits : xO j = xI k := prev_append_injective i heq
  cases hbits

private theorem key_not_in_xO {A : Type} (l : tree' A) (i : positive) :
    prev i ∉ (xelements' l (xO i) []).map Prod.fst := by
  intro h
  rcases List.mem_map.mp h with ⟨p, hp, hkey⟩
  rcases key_form_xelements' l (xO i) p hp with ⟨j, hj⟩
  have heq : prev_append i xH = prev_append i (xO j) := by
    calc
      prev_append i xH = prev i := by rfl
      _ = p.1 := hkey.symm
      _ = prev_append (xO i) j := hj
      _ = prev_append i (xO j) := by rfl
  have hbits : xH = xO j := prev_append_injective i heq
  cases hbits

private theorem key_not_in_xI {A : Type} (r : tree' A) (i : positive) :
    prev i ∉ (xelements' r (xI i) []).map Prod.fst := by
  intro h
  rcases List.mem_map.mp h with ⟨p, hp, hkey⟩
  rcases key_form_xelements' r (xI i) p hp with ⟨j, hj⟩
  have heq : prev_append i xH = prev_append i (xI j) := by
    calc
      prev_append i xH = prev i := by rfl
      _ = p.1 := hkey.symm
      _ = prev_append (xI i) j := hj
      _ = prev_append i (xI j) := by rfl
  have hbits : xH = xI j := prev_append_injective i heq
  cases hbits

private theorem keys_nodup_xelements' {A : Type} (m : tree' A) (i : positive) :
    ((xelements' m i []).map Prod.fst).Nodup := by
  induction m generalizing i with
  | Node001 r ih => exact ih (xI i)
  | Node010 x => simp [xelements']
  | Node011 x r ih =>
      simp only [xelements', List.map_cons, List.nodup_cons]
      constructor
      · intro h
        rcases List.mem_map.mp h with ⟨p, hp, hkey⟩
        exact key_not_in_xI r i (by simpa [hkey] using h)
      · exact ih (xI i)
  | Node100 l ih => exact ih (xO i)
  | Node101 l r ihl ihr =>
      change ((xelements' l (xO i) (xelements' r (xI i) [])).map Prod.fst).Nodup
      have hsplit : xelements' l (xO i) (xelements' r (xI i) []) =
          xelements' l (xO i) [] ++ xelements' r (xI i) [] := by
        simpa using (xelements'_append_equation l (xO i) [] (xelements' r (xI i) []))
      rw [hsplit]
      simp only [List.map_append, List.nodup_append]
      exact ⟨ihl (xO i), ihr (xI i), by
        intro a ha b hb hEq
        apply keys_disjoint_xO_xI l r i a ha
        simpa [hEq] using hb⟩
  | Node110 l x ih =>
      change ((xelements' l (xO i) [(prev i, x)]).map Prod.fst).Nodup
      have hsplit : xelements' l (xO i) [(prev i, x)] =
          xelements' l (xO i) [] ++ [(prev i, x)] := by
        simpa using (xelements'_append_equation l (xO i) [] [(prev i, x)])
      rw [hsplit]
      simp only [List.map_append, List.map_singleton]
      rw [List.nodup_append]
      refine ⟨ih (xO i), by simp, ?_⟩
      intro k hk b hb hkb
      have hb' : b = prev i := by simpa using hb
      have hkroot : k = prev i := hkb.trans hb'
      subst b
      apply key_not_in_xO l i
      apply List.mem_map.mpr
      rcases List.mem_map.mp hk with ⟨p, hp, hpk⟩
      refine ⟨p, hp, ?_⟩
      exact hpk.trans hkroot
  | Node111 l x r ihl ihr =>
      change ((xelements' l (xO i)
        ((prev i, x) :: xelements' r (xI i) [])).map Prod.fst).Nodup
      have hsplit : xelements' l (xO i)
          ((prev i, x) :: xelements' r (xI i) []) =
          xelements' l (xO i) [] ++
            ((prev i, x) :: xelements' r (xI i) []) := by
        simpa using (xelements'_append_equation l (xO i) []
          ((prev i, x) :: xelements' r (xI i) []))
      rw [hsplit]
      simp only [List.map_append]
      rw [List.nodup_append]
      have htail : ((prev i, x) :: xelements' r (xI i) []).map Prod.fst |>.Nodup := by
        simp only [List.map_cons, List.nodup_cons]
        exact ⟨key_not_in_xI r i, ihr (xI i)⟩
      refine ⟨ihl (xO i), htail, ?_⟩
      intro k hk b hb hkb
      simp only [List.map_cons, List.mem_cons] at hb
      rcases hb with hroot | hright
      · apply key_not_in_xO l i
        apply List.mem_map.mpr
        rcases List.mem_map.mp hk with ⟨p, hp, hpk⟩
        refine ⟨p, hp, ?_⟩
        exact hpk.trans (hkb.trans hroot)
      · exact (keys_disjoint_xO_xI l r i k hk) (by simpa [hkb] using hright)

theorem elements_complete_proof : elements_completeStatement := by
  intro A m i v h
  cases m with
  | Empty => simp [elements, xelements] at h
  | Nodes m =>
      have hc := in_xelements'_complete m xH (i, v) (by simpa [elements, xelements] using h)
      rcases hc with ⟨j, hj, hget⟩
      have hji : j = i := by
        have hj' : i = prev (prev j) := by simpa [prev] using hj
        rw [prev_involutive] at hj'
        exact hj'.symm
      subst j
      simpa [get] using hget

end PTree

namespace PMap

def elt : Type := positive
def t (A : Type) : Type := A × PTree.t A
def init {A : Type} (x : A) : t A := (x, PTree.empty A)
def get {A : Type} (i : positive) (m : t A) : A :=
  match PTree.get i m.2 with
  | some x => x
  | none => m.1
def set {A : Type} (i : positive) (x : A) (m : t A) : t A := (m.1, PTree.set i x m.2)

def giStatement : Prop := ∀ (A : Type) (i : positive) (x : A), get i (init x) = x
def gssStatement : Prop := ∀ (A : Type) (i : positive) (x : A) (m : t A), get i (set i x m) = x
def gsoStatement : Prop := ∀ (A : Type) (i j : positive) (x : A) (m : t A), i ≠ j → get i (set j x m) = get i m
def gsspecStatement : Prop := ∀ (A : Type) (i j : positive) (x : A) (m : t A),
  get i (set j x m) = match peq i j with | .left _ => x | .right _ => get i m
def set2Statement : Prop := ∀ (A : Type) (i : elt) (x y : A) (m : t A),
  set i y (set i x m) = set i y m

end PMap

namespace ZIndexed

def t : Type := Z

def index : t → positive
  | .Z0 => .xH
  | .Zpos p => .xO p
  | .Zneg p => .xI p

theorem index_inj (x y : t) (h : index x = index y) : x = y := by
  cases x with
  | Z0 =>
      cases y with
      | Z0 => rfl
      | Zpos _ => cases h
      | Zneg _ => cases h
  | Zpos p =>
      cases y with
      | Z0 => cases h
      | Zpos _ => cases h; rfl
      | Zneg _ => cases h
  | Zneg p =>
      cases y with
      | Z0 => cases h
      | Zpos _ => cases h
      | Zneg _ => cases h; rfl

def eq (x y : t) : CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) := by
  change Z at x y
  exact if h : x = y then .left h else .right h

end ZIndexed

namespace ZMap

def ZMap : Type := Unit

abbrev elt : Type := ZIndexed.t
abbrev t (A : Type) : Type := PMap.t A

def elt_eq (x y : elt) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) :=
  ZIndexed.eq x y

abbrev init {A : Type} (x : A) : t A := PMap.init x
abbrev get {A : Type} (i : elt) (m : t A) : A := PMap.get (ZIndexed.index i) m
abbrev set {A : Type} (i : elt) (x : A) (m : t A) : t A :=
  PMap.set (ZIndexed.index i) x m

def map {A B : Type} (f : A → B) (m : t A) : t B :=
  (f m.1, PTree.map1 f m.2)

def gi : Prop := ∀ (A : Type) (x : A) (i : elt), get i (init x) = x
def gss : Prop := ∀ (A : Type) (i : elt) (x : A) (m : t A), get i (set i x m) = x
def gso : Prop := ∀ (A : Type) (i j : elt) (x : A) (m : t A),
  i ≠ j → get i (set j x m) = get i m
def gsspec : Prop := ∀ (A : Type) (i j : elt) (x : A) (m : t A),
  get i (set j x m) = match elt_eq i j with | .left _ => x | .right _ => get i m
def gmap : Prop := ∀ (A B : Type) (f : A → B) (i : elt) (m : t A),
  get i (map f m) = f (get i m)
def set2 : Prop := ∀ (A : Type) (i : elt) (x y : A) (m : t A),
  set i y (set i x m) = set i y m

end ZMap

namespace NMap

def NMap : Type := Unit

abbrev elt : Type := N
abbrev t (A : Type) : Type := PMap.t A

private def index : elt → positive
  | .N0 => .xH
  | .Npos p => .xO p

def elt_eq (x y : elt) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) := by
  by_cases h : x = y
  · exact .left h
  · exact .right h

abbrev init {A : Type} (x : A) : t A := PMap.init x
abbrev get {A : Type} (i : elt) (m : t A) : A := PMap.get (index i) m
abbrev set {A : Type} (i : elt) (x : A) (m : t A) : t A := PMap.set (index i) x m

def map {A B : Type} (f : A → B) (m : t A) : t B :=
  (f m.1, PTree.map1 f m.2)

def gi : Prop := ∀ (A : Type) (x : A) (i : elt), get i (init x) = x
def gss : Prop := ∀ (A : Type) (i : elt) (x : A) (m : t A), get i (set i x m) = x
def gso : Prop := ∀ (A : Type) (i j : elt) (x : A) (m : t A),
  i ≠ j → get i (set j x m) = get i m
def gsspec : Prop := ∀ (A : Type) (i j : elt) (x : A) (m : t A),
  get i (set j x m) = match elt_eq i j with | .left _ => x | .right _ => get i m
def gmap : Prop := ∀ (A B : Type) (f : A → B) (i : elt) (m : t A),
  get i (map f m) = f (get i m)
def set2 : Prop := ∀ (A : Type) (i : elt) (x y : A) (m : t A),
  set i y (set i x m) = set i y m

end NMap

namespace ZTree

def ZTree : Type := Unit

abbrev elt : Type := ZIndexed.t
abbrev t (A : Type) : Type := PTree.t A

def elt_eq (x y : elt) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) :=
  ZIndexed.eq x y

abbrev empty (A : Type) : t A := PTree.empty A
abbrev get {A : Type} (i : elt) (m : t A) : Option A := PTree.get (ZIndexed.index i) m
abbrev set {A : Type} (i : elt) (x : A) (m : t A) : t A :=
  PTree.set (ZIndexed.index i) x m
abbrev remove {A : Type} (i : elt) (m : t A) : t A := PTree.remove (ZIndexed.index i) m

def gempty : Prop := ∀ (A : Type) (i : elt), get i (empty A) = none
def gss : Prop := ∀ (A : Type) (i : elt) (x : A) (m : t A), get i (set i x m) = some x
def gso : Prop := ∀ (A : Type) (i j : elt) (x : A) (m : t A),
  i ≠ j → get i (set j x m) = get i m
def gsspec : Prop := ∀ (A : Type) (i j : elt) (x : A) (m : t A),
  get i (set j x m) = match elt_eq i j with | .left _ => some x | .right _ => get i m
def grs : Prop := ∀ (A : Type) (i : elt) (m : t A), get i (remove i m) = none
def gro : Prop := ∀ (A : Type) (i j : elt) (m : t A),
  i ≠ j → get i (remove j m) = get i m
def grspec : Prop := ∀ (A : Type) (i j : elt) (m : t A),
  get i (remove j m) = match elt_eq i j with | .left _ => none | .right _ => get i m

private def beq' {A : Type} (beqA : A → A → Bool) : PTree.tree' A → PTree.tree' A → Bool
  | .Node001 r₁, .Node001 r₂ => beq' beqA r₁ r₂
  | .Node010 x₁, .Node010 x₂ => beqA x₁ x₂
  | .Node011 x₁ r₁, .Node011 x₂ r₂ => beqA x₁ x₂ && beq' beqA r₁ r₂
  | .Node100 l₁, .Node100 l₂ => beq' beqA l₁ l₂
  | .Node101 l₁ r₁, .Node101 l₂ r₂ => beq' beqA l₁ l₂ && beq' beqA r₁ r₂
  | .Node110 l₁ x₁, .Node110 l₂ x₂ => beqA x₁ x₂ && beq' beqA l₁ l₂
  | .Node111 l₁ x₁ r₁, .Node111 l₂ x₂ r₂ =>
      beqA x₁ x₂ && beq' beqA l₁ l₂ && beq' beqA r₁ r₂
  | _, _ => false

def beq {A : Type} (beqA : A → A → Bool) : t A → t A → Bool
  | .Empty, .Empty => true
  | .Nodes m₁, .Nodes m₂ => beq' beqA m₁ m₂
  | _, _ => false

def beq_sound : Prop := ∀ (A : Type) (eqA : A → A → Bool) (t₁ t₂ : t A),
  beq eqA t₁ t₂ = true → ∀ x : elt,
    match get x t₁, get x t₂ with
    | none, none => True
    | some y₁, some y₂ => eqA y₁ y₂ = true
    | _, _ => False

abbrev combine {A B C : Type} (f : Option A → Option B → Option C)
    (m₁ : t A) (m₂ : t B) : t C := PTree.combine f m₁ m₂

def gcombine : Prop := ∀ (A B C : Type) (f : Option A → Option B → Option C),
  f none none = none → ∀ (m₁ : t A) (m₂ : t B) (i : elt),
    get i (combine f m₁ m₂) = f (get i m₁) (get i m₂)

end ZTree

namespace PTree_Properties

def PTree_Properties : Type := Unit

def fold_ind_aux : Type 1 :=
  ∀ (V A : Type) (f : A → PTree.elt → V → A)
    (P : PTree.t V → A → Type) (init : A) (mFinal : PTree.t V),
    (∀ m, (∀ k, PTree.get k m = none) → P m init) →
    (∀ m a k v, PTree.get k m = some v → PTree.get k mFinal = some v →
      P (PTree.remove k m) a → P m (f a k v)) →
    ∀ l : List (PTree.elt × V),
      (∀ k v, (k, v) ∈ l → PTree.get k mFinal = some v) →
      PTree.list_norepet (l.map Prod.fst) →
      ∀ m, (∀ k v, (k, v) ∈ l ↔ PTree.get k m = some v) →
        P m (List.foldr (fun p a => f a p.1 p.2) init l)

def fold_ind : Type 1 :=
  ∀ (V A : Type) (f : A → PTree.elt → V → A)
    (P : PTree.t V → A → Type) (init : A) (mFinal : PTree.t V),
    (∀ m, (∀ k, PTree.get k m = none) → P m init) →
    (∀ m a k v, PTree.get k m = some v → PTree.get k mFinal = some v →
      P (PTree.remove k m) a → P m (f a k v)) →
    P mFinal (PTree.fold f mFinal init)

def fold_rec : Prop :=
  ∀ (V A : Type) (f : A → PTree.elt → V → A)
    (P : PTree.t V → A → Prop) (init : A) (mFinal : PTree.t V),
    (∀ m m' a, (∀ x, PTree.get x m = PTree.get x m') → P m a → P m' a) →
    P (PTree.empty V) init →
    (∀ m a k v, PTree.get k m = none → PTree.get k mFinal = some v →
      P m a → P (PTree.set k v m) (f a k v)) →
    P mFinal (PTree.fold f mFinal init)

def cardinal {V : Type} (m : PTree.t V) : Nat := (PTree.elements m).length

def cardinal_remove : Prop := ∀ (V : Type) (x : PTree.elt) (m : PTree.t V) (y : V),
  PTree.get x m = some y → cardinal (PTree.remove x m) < cardinal m
def cardinal_set : Prop := ∀ (V : Type) (x : PTree.elt) (m : PTree.t V) (y : V),
  PTree.get x m = none → cardinal m < cardinal (PTree.set x y m)

private def treeCard' {A : Type} : PTree.tree' A → Nat
  | .Node001 r => treeCard' r
  | .Node010 _ => 1
  | .Node011 _ r => 1 + treeCard' r
  | .Node100 l => treeCard' l
  | .Node101 l r => treeCard' l + treeCard' r
  | .Node110 l _ => treeCard' l + 1
  | .Node111 l _ r => treeCard' l + 1 + treeCard' r

private def treeCard {A : Type} : PTree.tree A → Nat
  | .Empty => 0
  | .Nodes m => treeCard' m

private def optionCard {A : Type} : Option A → Nat
  | none => 0
  | some _ => 1

private theorem treeCard_node {A : Type} (l : PTree.tree A) (o : Option A)
    (r : PTree.tree A) :
    treeCard (PTree.Node l o r) = treeCard l + optionCard o + treeCard r := by
  cases l <;> cases o <;> cases r <;>
    simp [PTree.Node, treeCard, treeCard', optionCard]

private theorem xelements_length {A : Type} (m : PTree.tree' A) (i : positive)
    (suffix : List (positive × A)) :
    (PTree.xelements' m i suffix).length = treeCard' m + suffix.length := by
  induction m generalizing i suffix <;>
    simp_all [PTree.xelements', treeCard', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem cardinal_eq_treeCard {A : Type} (m : PTree.tree A) :
    cardinal m = treeCard m := by
  cases m with
  | Empty => rfl
  | Nodes m =>
      simpa [cardinal, PTree.elements, PTree.xelements, treeCard]
        using xelements_length m .xH []

private theorem treeCard_remove_lt {A : Type} (p : positive) (m : PTree.tree' A)
    (v : A) (h : PTree.get' p m = some v) :
    treeCard (PTree.rem' p m) < treeCard' m := by
  induction p generalizing m with
  | xH =>
      cases m <;> simp_all [PTree.get', PTree.rem', treeCard, treeCard']
  | xO p ih =>
      cases m <;> simp_all [PTree.get', PTree.rem', treeCard, treeCard']
      all_goals
        change treeCard (PTree.Node _ _ _) < _
        rw [treeCard_node]
        simp only [treeCard, optionCard]
        have decrease := ih _ h
        omega
  | xI p ih =>
      cases m <;> simp_all [PTree.get', PTree.rem', treeCard, treeCard']
      all_goals
        change treeCard (PTree.Node _ _ _) < _
        rw [treeCard_node]
        simp only [treeCard, optionCard]
        have decrease := ih _ h
        omega

theorem cardinal_remove_proof : cardinal_remove := by
  intro V x m y h
  rw [show cardinal (PTree.remove x m) = treeCard (PTree.remove x m) by
        exact cardinal_eq_treeCard _]
  rw [show cardinal m = treeCard m by exact cardinal_eq_treeCard _]
  cases m with
  | Empty => simp [PTree.get] at h
  | Nodes m =>
      exact treeCard_remove_lt x m y (by simpa [PTree.get] using h)

def for_all {A : Type} (m : PTree.t A) (f : PTree.elt → A → Bool) : Bool :=
  PTree.fold (fun b x a => b && f x a) m true

def for_all_correct : Prop := ∀ (A : Type) (m : PTree.t A) (f : PTree.elt → A → Bool),
  for_all m f = true ↔ ∀ x a, PTree.get x m = some a → f x a = true

def exists_ {A : Type} (m : PTree.t A) (f : PTree.elt → A → Bool) : Bool :=
  PTree.fold (fun b x a => b || f x a) m false

def exists_correct : Prop := ∀ (A : Type) (m : PTree.t A) (f : PTree.elt → A → Bool),
  exists_ m f = true ↔ ∃ x a, PTree.get x m = some a ∧ f x a = true
def exists_for_all : Prop := ∀ (A : Type) (m : PTree.t A) (f : PTree.elt → A → Bool),
  exists_ m f = Bool.not (for_all m (fun x a => Bool.not (f x a)))
def for_all_exists : Prop := ∀ (A : Type) (m : PTree.t A) (f : PTree.elt → A → Bool),
  for_all m f = Bool.not (exists_ m (fun x a => Bool.not (f x a)))
def for_all_false : Prop := ∀ (A : Type) (m : PTree.t A) (f : PTree.elt → A → Bool),
  for_all m f = false ↔ ∃ x a, PTree.get x m = some a ∧ f x a = false
def exists_false : Prop := ∀ (A : Type) (m : PTree.t A) (f : PTree.elt → A → Bool),
  exists_ m f = false ↔ ∀ x a, PTree.get x m = some a → f x a = false

def beq_false : Prop := ∀ (A : Type) (beqA : A → A → Bool) (m₁ m₂ : PTree.t A),
  ZTree.beq beqA m₁ m₂ = false ↔ ∃ x : PTree.elt,
    match PTree.get x m₁, PTree.get x m₂ with
    | none, none => False
    | some a₁, some a₂ => beqA a₁ a₂ = false
    | _, _ => True

def Equal {A : Type} (eqA : A → A → Prop) (_eqAeq : Equivalence eqA)
    (m₁ m₂ : PTree.t A) : Prop :=
  ∀ x, match PTree.get x m₁, PTree.get x m₂ with
    | none, none => True
    | some a₁, some a₂ => eqA a₁ a₂
    | _, _ => False

def Equal_refl : Prop := ∀ (A : Type) (eqA : A → A → Prop) (eqAeq : Equivalence eqA)
  (m : PTree.t A), Equal eqA eqAeq m m
def Equal_sym : Prop := ∀ (A : Type) (eqA : A → A → Prop) (eqAeq : Equivalence eqA)
  (m₁ m₂ : PTree.t A), Equal eqA eqAeq m₁ m₂ → Equal eqA eqAeq m₂ m₁
def Equal_trans : Prop := ∀ (A : Type) (eqA : A → A → Prop) (eqAeq : Equivalence eqA)
  (m₁ m₂ m₃ : PTree.t A), Equal eqA eqAeq m₁ m₂ → Equal eqA eqAeq m₂ m₃ →
    Equal eqA eqAeq m₁ m₃
def Equal_Equivalence : Prop := ∀ (A : Type) (eqA : A → A → Prop) (eqAeq : Equivalence eqA),
  Equivalence (Equal eqA eqAeq)

def Equal_dec_obligation_1 : Prop :=
  ∀ (A : Type) (eqA : A → A → Prop) (eqAeq : Equivalence eqA)
    (eqAdec : ∀ a₁ a₂, CompCert4Lean.Foundation.Logic.Support.Sumbool (eqA a₁ a₂) (¬ eqA a₁ a₂))
    (m₁ m₂ : PTree.t A),
    ZTree.beq (fun a₁ a₂ => proj_sumbool (eqAdec a₁ a₂)) m₁ m₂ = true →
      Equal eqA eqAeq m₁ m₂
def Equal_dec_obligation_2 : Prop :=
  ∀ (A : Type) (eqA : A → A → Prop) (eqAeq : Equivalence eqA)
    (eqAdec : ∀ a₁ a₂, CompCert4Lean.Foundation.Logic.Support.Sumbool (eqA a₁ a₂) (¬ eqA a₁ a₂))
    (m₁ m₂ : PTree.t A),
    ZTree.beq (fun a₁ a₂ => proj_sumbool (eqAdec a₁ a₂)) m₁ m₂ = false →
      ¬ Equal eqA eqAeq m₁ m₂

def Equal_dec : Type 1 :=
  ∀ (A : Type) (eqA : A → A → Prop) (eqAeq : Equivalence eqA),
    (∀ a₁ a₂, CompCert4Lean.Foundation.Logic.Support.Sumbool (eqA a₁ a₂) (¬ eqA a₁ a₂)) →
    ∀ m₁ m₂ : PTree.t A,
      CompCert4Lean.Foundation.Logic.Support.Sumbool
        (Equal eqA eqAeq m₁ m₂) (¬ Equal eqA eqAeq m₁ m₂)

def Equal_EqDec : Type 1 :=
  ∀ (A : Type) (eqA : A → A → Prop) (eqAeq : Equivalence eqA),
    (∀ a₁ a₂, CompCert4Lean.Foundation.Logic.Support.Sumbool (eqA a₁ a₂) (¬ eqA a₁ a₂)) →
    ∀ m₁ m₂ : PTree.t A,
      CompCert4Lean.Foundation.Logic.Support.Sumbool
        (Equal eqA eqAeq m₁ m₂) (¬ Equal eqA eqAeq m₁ m₂)

def of_list {A : Type} (l : List (PTree.elt × A)) : PTree.t A :=
  List.foldl (fun m kv => PTree.set kv.1 kv.2 m) (PTree.empty A) l

private def set_list {A : Type} (m : PTree.tree A) (l : List (positive × A)) : PTree.tree A :=
  List.foldl (fun m kv => PTree.set kv.1 kv.2 m) m l

private theorem get_set_list_preserve {A : Type} (m : PTree.tree A)
    (l : List (positive × A)) (k : positive)
    (hkeys : k ∉ l.map Prod.fst) :
    PTree.get k (set_list m l) = PTree.get k m := by
  induction l generalizing m with
  | nil => rfl
  | cons p l ih =>
      rcases p with ⟨j, v⟩
      have hne : k ≠ j := by
        intro hkj
        apply hkeys
        simp [hkj]
      have htail : k ∉ l.map Prod.fst := by
        intro hmem
        apply hkeys
        simp [hmem]
      change PTree.get k (set_list (PTree.set j v m) l) = PTree.get k m
      rw [ih (PTree.set j v m) htail]
      simpa [PTree.getSet_equation, hne]

private theorem get_set_list_none {A : Type} (m : PTree.tree A)
    (l : List (positive × A)) (k : positive)
    (h0 : PTree.get k m = none) (hkeys : k ∉ l.map Prod.fst) :
    PTree.get k (set_list m l) = none := by
  simpa [set_list] using get_set_list_preserve m l k hkeys |>.trans h0

private theorem get_set_list_some {A : Type} (m : PTree.tree A)
    (l : List (positive × A)) (k : positive) (v : A)
    (hnodup : (l.map Prod.fst).Nodup) (hmem : (k, v) ∈ l) :
    PTree.get k (set_list m l) = some v := by
  induction l generalizing m k v with
  | nil => cases hmem
  | cons p l ih =>
      rcases p with ⟨j, w⟩
      have htailnodup : (l.map Prod.fst).Nodup := (List.nodup_cons.mp hnodup).2
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨rfl, rfl⟩
        have hpres := get_set_list_preserve (PTree.set k v m) l k
          (by simpa using (List.nodup_cons.mp hnodup).1)
        change PTree.get k (set_list (PTree.set k v m) l) = some v
        rw [hpres]
        simp [PTree.getSet_equation]
      · have hne : k ≠ j := by
          intro hkj
          apply (List.nodup_cons.mp hnodup).1
          apply List.mem_map.mpr
          exact ⟨(k, v), htail, hkj⟩
        have hstep := ih (PTree.set j w m) k v htailnodup htail
        simpa [set_list, List.foldl] using hstep

private theorem get_set_list_dom {A : Type} (m : PTree.tree A)
    (l : List (positive × A)) (k : positive) (y : A)
    (h0 : PTree.get k m = none)
    (hget : PTree.get k (set_list m l) = some y) :
    ∃ v, (k, v) ∈ l := by
  induction l generalizing m k y with
  | nil =>
      change PTree.get k m = some y at hget
      rw [h0] at hget
      cases hget
  | cons p l ih =>
      rcases p with ⟨j, v⟩
      by_cases hkj : k = j
      · exact ⟨v, by simp [hkj]⟩
      · have hstep : PTree.get k (PTree.set j v m) = none := by
          simpa [PTree.getSet_equation, hkj] using h0
        have htailget := ih (PTree.set j v m) k y hstep
          (by simpa [set_list, List.foldl] using hget)
        rcases htailget with ⟨w, hw⟩
        exact ⟨w, List.mem_cons_of_mem _ hw⟩



def in_of_list : Prop := ∀ (A : Type) (l : List (PTree.elt × A)) (k : PTree.elt) (v : A),
  PTree.get k (of_list l) = some v → (k, v) ∈ l
def of_list_dom : Prop := ∀ (A : Type) (l : List (PTree.elt × A)) (k : PTree.elt),
  k ∈ l.map Prod.fst → ∃ v, PTree.get k (of_list l) = some v
def of_list_unchanged : Prop := ∀ (A : Type) (k : PTree.elt) (l : List (PTree.elt × A))
  (m : PTree.t A), k ∉ l.map Prod.fst →
    PTree.get k (List.foldl (fun m₀ kv => PTree.set kv.1 kv.2 m₀) m l) = PTree.get k m
def of_list_unique : Prop := ∀ (A : Type) (k : PTree.elt) (v : A)
  (l₁ l₂ : List (PTree.elt × A)), k ∉ l₂.map Prod.fst →
    PTree.get k (of_list (l₁ ++ (k, v) :: l₂)) = some v
def of_list_norepet : Prop := ∀ (A : Type) (l : List (PTree.elt × A)) (k : PTree.elt) (v : A),
  PTree.list_norepet (l.map Prod.fst) → (k, v) ∈ l → PTree.get k (of_list l) = some v
def of_list_elements : Prop := ∀ (A : Type) (m : PTree.t A) (k : PTree.elt),
  PTree.get k (of_list (PTree.elements m)) = PTree.get k m

theorem of_list_elements_proof : of_list_elements := by
  intro A m k
  have hcorrect : ∀ (i : positive) (v : A),
      PTree.get i m = some v → (i, v) ∈ PTree.elements m := by
    simpa [PTree.elements_correctStatement] using PTree.elements_correct_proof A m
  have hcomplete : ∀ (i : positive) (v : A),
      (i, v) ∈ PTree.elements m → PTree.get i m = some v := by
    simpa [PTree.elements_completeStatement] using PTree.elements_complete_proof A m
  have hnodup : (PTree.elements m).map Prod.fst |>.Nodup := by
    cases m with
    | Empty => simp [PTree.elements, PTree.xelements]
    | Nodes m =>
        simpa [PTree.elements, PTree.xelements] using
          PTree.keys_nodup_xelements' m .xH
  cases hkm : PTree.get k m with
  | none =>
      have hnone : k ∉ (PTree.elements m).map Prod.fst := by
        intro hmem
        rcases List.mem_map.mp hmem with ⟨p, hp, hpk⟩
        have hg := hcomplete p.1 p.2 hp
        have hg' : PTree.get k m = some p.2 := by simpa [hpk] using hg
        rw [hkm] at hg'
        cases hg'
      have hres := get_set_list_none (PTree.empty A) (PTree.elements m) k
        (by rfl) hnone
      change PTree.get k (List.foldl (fun m kv => PTree.set kv.1 kv.2 m)
        (PTree.empty A) (PTree.elements m)) = none
      exact hres
  | some y =>
      have hmem := hcorrect k y (by simpa [hkm] using hkm)
      have hres := get_set_list_some (PTree.empty A) (PTree.elements m) k y hnodup hmem
      change PTree.get k (List.foldl (fun m kv => PTree.set kv.1 kv.2 m)
        (PTree.empty A) (PTree.elements m)) = some y
      exact hres

theorem fold_rec_proof : fold_rec := by
  intro V A f P init mFinal hext hbase hstep
  have hcomplete : ∀ (i : positive) (v : V),
      (i, v) ∈ PTree.elements mFinal → PTree.get i mFinal = some v := by
    simpa [PTree.elements_completeStatement] using PTree.elements_complete_proof V mFinal
  have hnodup : (PTree.elements mFinal).map Prod.fst |>.Nodup := by
    cases mFinal with
    | Empty => simp [PTree.elements, PTree.xelements]
    | Nodes m =>
        simpa [PTree.elements, PTree.xelements] using
          PTree.keys_nodup_xelements' m .xH
  have hprocess : ∀ (m : PTree.tree V) (a : A) (l : List (positive × V)),
      P m a →
      (∀ p, p ∈ l → p ∈ PTree.elements mFinal) →
      (∀ p, p ∈ l → PTree.get p.1 m = none) →
      (l.map Prod.fst).Nodup →
      P (set_list m l)
        (List.foldl (fun a p => f a p.1 p.2) a l) := by
    intro m a l hP hsub hnone hlist
    induction l generalizing m a with
    | nil => simpa only [set_list, List.foldl] using hP
    | cons p l ih =>
        rcases p with ⟨k, v⟩
        simp only [List.map_cons, List.nodup_cons] at hlist
        have hsubhead : (k, v) ∈ PTree.elements mFinal := by simp [hsub]
        have hsubtail : ∀ q, q ∈ l → q ∈ PTree.elements mFinal := by
          intro q hq
          apply hsub q
          simp [hq]
        have hnonehead : PTree.get k m = none := hnone (k, v) (by simp)
        have hfinal := hcomplete k v hsubhead
        have hnext := hstep m a k v hnonehead hfinal hP
        have hnoneTail : ∀ q, q ∈ l → PTree.get q.1 (PTree.set k v m) = none := by
          intro q hq
          have hqkey : q.1 ≠ k := by
            intro heq
            apply hlist.1
            apply List.mem_map.mpr
            exact ⟨q, hq, heq⟩
          have hqnone := hnone q (by simp [hq])
          simpa [PTree.getSet_equation, hqkey] using hqnone
        have htail := ih (PTree.set k v m) (f a k v) hnext hsubtail
          hnoneTail hlist.2
        simpa [set_list, List.foldl] using htail
  have hfinal := hprocess (PTree.empty V) init (PTree.elements mFinal) hbase
    (by intro p hp; exact hp)
    (by intro p hp; rfl) hnodup
  have hmap : ∀ x, PTree.get x (set_list (PTree.empty V) (PTree.elements mFinal)) =
      PTree.get x mFinal := by
    change ∀ x, PTree.get x (List.foldl (fun m kv => PTree.set kv.1 kv.2 m)
      (PTree.empty V) (PTree.elements mFinal)) = PTree.get x mFinal
    intro x
    exact of_list_elements_proof V mFinal x
  have hp := hext (set_list (PTree.empty V) (PTree.elements mFinal)) mFinal
    (List.foldl (fun a p => f a p.1 p.2) init (PTree.elements mFinal)) hmap hfinal
  have hfold : PTree.fold f mFinal init =
      List.foldl (fun a p => f a p.1 p.2) init (PTree.elements mFinal) := by
    simpa [PTree.fold_specStatement] using
      (PTree.fold_spec_proof V A f init mFinal)
  rw [hfold]
  exact hp

def of_list_related : Prop := ∀ (A B : Type) (R : A → B → Prop) (k : PTree.elt)
  (l₁ : List (PTree.elt × A)) (l₂ : List (PTree.elt × B)),
  PTree.list_forall2 (fun ka kb => ka.1 = kb.1 ∧ R ka.2 kb.2) l₁ l₂ →
    PTree.option_rel R (PTree.get k (of_list l₁)) (PTree.get k (of_list l₂))

end PTree_Properties

end CompCert4Lean.Lib.Maps
