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
def of_list_related : Prop := ∀ (A B : Type) (R : A → B → Prop) (k : PTree.elt)
  (l₁ : List (PTree.elt × A)) (l₂ : List (PTree.elt × B)),
  PTree.list_forall2 (fun ka kb => ka.1 = kb.1 ∧ R ka.2 kb.2) l₁ l₂ →
    PTree.option_rel R (PTree.get k (of_list l₁)) (PTree.get k (of_list l₂))

end PTree_Properties

end CompCert4Lean.Lib.Maps
