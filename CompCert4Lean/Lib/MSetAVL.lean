import CompCert4Lean.Lib.MSetGenTree

/-!
# Ordered finite sets implemented by AVL operations

Definition-bearing translation of Rocq's `MSetAVL`, instantiated with Rocq
`Z` heights.  As in the source module, the logical invariant is the binary
search-tree invariant; the executable rotations are the original AVL
algorithms and are not replaced by extensional or unbalanced operations.
-/

namespace CompCert4Lean.Lib.MSetAVL

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

abbrev OrderedType := CompCert4Lean.Lib.MSetGenTree.OrderedType
abbrev tree (X : OrderedType) := CompCert4Lean.Lib.MSetGenTree.tree X _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
abbrev t (X : OrderedType) := tree X

variable {X : OrderedType}

abbrev Leaf : tree X := .Leaf
abbrev Node (height : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (left : tree X) (value : X.t) (right : tree X) : tree X :=
  .Node height left value right

abbrev empty : tree X := CompCert4Lean.Lib.MSetGenTree.tree.empty
abbrev is_empty (s : tree X) : Bool := CompCert4Lean.Lib.MSetGenTree.tree.is_empty s
abbrev mem (x : X.t) (s : tree X) : Bool := CompCert4Lean.Lib.MSetGenTree.tree.mem x s
abbrev min_elt (s : tree X) : Option X.t := CompCert4Lean.Lib.MSetGenTree.tree.min_elt s
abbrev max_elt (s : tree X) : Option X.t := CompCert4Lean.Lib.MSetGenTree.tree.max_elt s
abbrev choose (s : tree X) : Option X.t := CompCert4Lean.Lib.MSetGenTree.tree.choose s
abbrev fold {A : Type} (f : X.t → A → A) (s : tree X) (base : A) : A :=
  CompCert4Lean.Lib.MSetGenTree.tree.fold f s base
abbrev elements_aux (acc : List X.t) (s : tree X) : List X.t :=
  CompCert4Lean.Lib.MSetGenTree.tree.elements_aux acc s
abbrev elements (s : tree X) : List X.t := CompCert4Lean.Lib.MSetGenTree.tree.elements s
abbrev rev_elements_aux (acc : List X.t) (s : tree X) : List X.t :=
  CompCert4Lean.Lib.MSetGenTree.tree.rev_elements_aux acc s
abbrev rev_elements (s : tree X) : List X.t := CompCert4Lean.Lib.MSetGenTree.tree.rev_elements s
abbrev cardinal (s : tree X) : Nat := CompCert4Lean.Lib.MSetGenTree.tree.cardinal s
abbrev maxdepth (s : tree X) : Nat := CompCert4Lean.Lib.MSetGenTree.tree.maxdepth s
abbrev mindepth (s : tree X) : Nat := CompCert4Lean.Lib.MSetGenTree.tree.mindepth s
abbrev for_all (f : X.t → Bool) (s : tree X) : Bool := CompCert4Lean.Lib.MSetGenTree.tree.for_all f s
abbrev exists_ (f : X.t → Bool) (s : tree X) : Bool := CompCert4Lean.Lib.MSetGenTree.tree.exists_ f s
abbrev compare (s₁ s₂ : tree X) : comparison := CompCert4Lean.Lib.MSetGenTree.tree.compare s₁ s₂
abbrev equal (s₁ s₂ : tree X) : Bool := CompCert4Lean.Lib.MSetGenTree.tree.equal s₁ s₂
abbrev subset (s₁ s₂ : tree X) : Bool := CompCert4Lean.Lib.MSetGenTree.tree.subset s₁ s₂
abbrev subsetl (subsetLeft : tree X → Bool) (x : X.t) (s : tree X) : Bool :=
  CompCert4Lean.Lib.MSetGenTree.tree.subsetl subsetLeft x s
abbrev subsetr (subsetRight : tree X → Bool) (x : X.t) (s : tree X) : Bool :=
  CompCert4Lean.Lib.MSetGenTree.tree.subsetr subsetRight x s
abbrev ltb_tree (x : X.t) (s : tree X) : Bool := CompCert4Lean.Lib.MSetGenTree.tree.ltb_tree x s
abbrev gtb_tree (x : X.t) (s : tree X) : Bool := CompCert4Lean.Lib.MSetGenTree.tree.gtb_tree x s
abbrev isok (s : tree X) : Bool := CompCert4Lean.Lib.MSetGenTree.tree.isok s

abbrev In (x : X.t) (s : tree X) : Prop := CompCert4Lean.Lib.MSetGenTree.tree.In x s
abbrev InT (x : X.t) (s : tree X) : Prop := CompCert4Lean.Lib.MSetGenTree.tree.InT x s
export CompCert4Lean.Lib.MSetGenTree.tree.InT (IsRoot InLeft InRight)
abbrev Equal (s s' : tree X) : Prop := CompCert4Lean.Lib.MSetGenTree.tree.Equal s s'
abbrev Subset (s s' : tree X) : Prop := CompCert4Lean.Lib.MSetGenTree.tree.Subset s s'
abbrev Empty (s : tree X) : Prop := CompCert4Lean.Lib.MSetGenTree.tree.Empty s
abbrev For_all (P : X.t → Prop) (s : tree X) : Prop := CompCert4Lean.Lib.MSetGenTree.tree.For_all P s
abbrev Exists (P : X.t → Prop) (s : tree X) : Prop := CompCert4Lean.Lib.MSetGenTree.tree.Exists P s
abbrev lt_tree (x : X.t) (s : tree X) : Prop := CompCert4Lean.Lib.MSetGenTree.tree.lt_tree x s
abbrev gt_tree (x : X.t) (s : tree X) : Prop := CompCert4Lean.Lib.MSetGenTree.tree.gt_tree x s
abbrev bst (s : tree X) : Prop := CompCert4Lean.Lib.MSetGenTree.tree.bst s
abbrev IsOk (s : tree X) : Prop := bst s
abbrev InA (x : X.t) (l : List X.t) : Prop :=
  CompCert4Lean.Lib.MSetGenTree.InA X.eq x l
abbrev NoDupA (l : List X.t) : Prop :=
  CompCert4Lean.Lib.MSetGenTree.NoDupA X.eq l
abbrev Sorted (l : List X.t) : Prop :=
  CompCert4Lean.Lib.MSetGenTree.Sorted X.lt l
abbrev RespectsEq (f : X.t → Bool) : Prop :=
  CompCert4Lean.Lib.MSetGenTree.tree.RespectsEq f
abbrev enumeration := CompCert4Lean.Lib.MSetGenTree.tree.enumeration X
  _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
export CompCert4Lean.Lib.MSetGenTree.tree.enumeration (End More)
abbrev cons (s : tree X) (e : enumeration (X := X)) : enumeration (X := X) :=
  CompCert4Lean.Lib.MSetGenTree.tree.cons s e
abbrev compare_more (x : X.t) (cont : enumeration (X := X) → comparison)
    (e : enumeration (X := X)) : comparison :=
  CompCert4Lean.Lib.MSetGenTree.tree.compare_more x cont e
abbrev compare_cont (s : tree X)
    (cont : enumeration (X := X) → comparison) (e : enumeration (X := X)) :
    comparison :=
  CompCert4Lean.Lib.MSetGenTree.tree.compare_cont s cont e
abbrev compare_end (e : enumeration (X := X)) : comparison :=
  CompCert4Lean.Lib.MSetGenTree.tree.compare_end e
abbrev flatten_e (e : enumeration (X := X)) : List X.t :=
  CompCert4Lean.Lib.MSetGenTree.tree.flatten_e e
abbrev eq (s₁ s₂ : tree X) : Prop := CompCert4Lean.Lib.MSetGenTree.tree.eq s₁ s₂
abbrev lt (s₁ s₂ : tree X) : Prop := CompCert4Lean.Lib.MSetGenTree.tree.lt s₁ s₂
abbrev CompSpec {A : Type} (eq lt : A → A → Prop) (x y : A)
    (c : comparison) : Prop := CompCert4Lean.Lib.MSetGenTree.CompSpec eq lt x y c
abbrev CompareSpec (Peq Plt Pgt : Prop) (c : comparison) : Prop :=
  CompCert4Lean.Lib.MSetGenTree.CompareSpec Peq Plt Pgt c
export CompCert4Lean.Lib.MSetGenTree.CompareSpec (CompEq CompLt CompGt)

namespace L

abbrev eq (l₁ l₂ : List X.t) : Prop :=
  CompCert4Lean.Lib.MSetGenTree.tree.L.eq l₁ l₂
abbrev lt (l₁ l₂ : List X.t) : Prop :=
  CompCert4Lean.Lib.MSetGenTree.tree.L.lt l₁ l₂

end L

abbrev Cmp (c : comparison) (l₁ l₂ : List X.t) : Prop :=
  CompSpec L.eq L.lt l₁ l₂ c

private abbrev z0 : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z := .Z0
private abbrev z1 : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z := .Zpos .xH
private abbrev z2 : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z := .Zpos (.xO .xH)
private abbrev zadd := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
private abbrev zmax := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max
private abbrev zltb := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.ltb
private abbrev zleb := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.leb

def height : tree X → _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
  | .Leaf => z0
  | .Node h _ _ _ => h

def singleton (x : X.t) : tree X := .Node z1 .Leaf x .Leaf

def create (left : tree X) (x : X.t) (right : tree X) : tree X :=
  .Node (zadd (zmax (height left) (height right)) z1) left x right

abbrev assert_false (left : tree X) (x : X.t) (right : tree X) : tree X :=
  create left x right

def bal (left : tree X) (x : X.t) (right : tree X) : tree X :=
  let hl := height left
  let hr := height right
  if zltb (zadd hr z2) hl then
    match left with
    | .Leaf => assert_false left x right
    | .Node _ ll lx lr =>
        if zleb (height lr) (height ll) then
          create ll lx (create lr x right)
        else
          match lr with
          | .Leaf => assert_false left x right
          | .Node _ lrl lrx lrr =>
              create (create ll lx lrl) lrx (create lrr x right)
  else if zltb (zadd hl z2) hr then
    match right with
    | .Leaf => assert_false left x right
    | .Node _ rl rx rr =>
        if zleb (height rl) (height rr) then
          create (create left x rl) rx rr
        else
          match rl with
          | .Leaf => assert_false left x right
          | .Node _ rll rlx rlr =>
              create (create left x rll) rlx (create rlr rx rr)
  else
    create left x right

def add (x : X.t) : tree X → tree X
  | .Leaf => singleton x
  | .Node h left y right =>
      match X.compare x y with
      | .lt _ => bal (add x left) y right
      | .eq _ => .Node h left y right
      | .gt _ => bal left y (add x right)

/- Rocq accepts the structurally nested recursion in `join`.  Lean records the
   same calls with the well-founded measure `sizeOf left + sizeOf right`; this
   is a termination adaptation only and does not alter the executable cases. -/
def join (left : tree X) (x : X.t) (right : tree X) : tree X :=
  match left, right with
  | .Leaf, right => add x right
  | left, .Leaf => add x left
  | left@(.Node lh ll lx lr), right@(.Node rh rl rx rr) =>
      if zltb (zadd rh z2) lh then
        bal ll lx (join lr x right)
      else if zltb (zadd lh z2) rh then
        bal (join left x rl) rx rr
      else
        create left x right
termination_by sizeOf left + sizeOf right
decreasing_by all_goals simp_all; omega

def remove_min (left : tree X) (x : X.t) (right : tree X) : tree X × X.t :=
  match left with
  | .Leaf => (right, x)
  | .Node _ ll lx lr =>
      let (left', minimum) := remove_min ll lx lr
      (bal left' x right, minimum)

def merge (s₁ s₂ : tree X) : tree X :=
  match s₁, s₂ with
  | .Leaf, _ => s₂
  | _, .Leaf => s₁
  | _, .Node _ left₂ x₂ right₂ =>
      let (s₂', minimum) := remove_min left₂ x₂ right₂
      bal s₁ minimum s₂'

def remove (x : X.t) : tree X → tree X
  | .Leaf => .Leaf
  | .Node _ left y right =>
      match X.compare x y with
      | .lt _ => bal (remove x left) y right
      | .eq _ => merge left right
      | .gt _ => bal left y (remove x right)

def concat (s₁ s₂ : tree X) : tree X :=
  match s₁, s₂ with
  | .Leaf, _ => s₂
  | _, .Leaf => s₁
  | _, .Node _ left₂ x₂ right₂ =>
      let (s₂', minimum) := remove_min left₂ x₂ right₂
      join s₁ minimum s₂'

structure triple (X : OrderedType) where
  t_left : tree X
  t_in : Bool
  t_right : tree X

def split (x : X.t) : tree X → triple X
  | .Leaf => ⟨.Leaf, false, .Leaf⟩
  | .Node _ left y right =>
      match X.compare x y with
      | .lt _ =>
          let result := split x left
          ⟨result.t_left, result.t_in, join result.t_right y right⟩
      | .eq _ => ⟨left, true, right⟩
      | .gt _ =>
          let result := split x right
          ⟨join left y result.t_left, result.t_in, result.t_right⟩

def inter : tree X → tree X → tree X
  | .Leaf, _ => .Leaf
  | _, .Leaf => .Leaf
  | .Node _ left₁ x₁ right₁, s₂ =>
      let result := split x₁ s₂
      if result.t_in then
        join (inter left₁ result.t_left) x₁ (inter right₁ result.t_right)
      else
        concat (inter left₁ result.t_left) (inter right₁ result.t_right)

def diff : tree X → tree X → tree X
  | .Leaf, _ => .Leaf
  | s₁, .Leaf => s₁
  | .Node _ left₁ x₁ right₁, s₂ =>
      let result := split x₁ s₂
      if result.t_in then
        concat (diff left₁ result.t_left) (diff right₁ result.t_right)
      else
        join (diff left₁ result.t_left) x₁ (diff right₁ result.t_right)

def union : tree X → tree X → tree X
  | .Leaf, s₂ => s₂
  | s₁, .Leaf => s₁
  | .Node _ left₁ x₁ right₁, s₂ =>
      let result := split x₁ s₂
      join (union left₁ result.t_left) x₁ (union right₁ result.t_right)

def filter (f : X.t → Bool) : tree X → tree X
  | .Leaf => .Leaf
  | .Node _ left x right =>
      let left' := filter f left
      let right' := filter f right
      if f x then join left' x right' else concat left' right'

def partition (f : X.t → Bool) : tree X → tree X × tree X
  | .Leaf => (.Leaf, .Leaf)
  | .Node _ left x right =>
      let (leftTrue, leftFalse) := partition f left
      let (rightTrue, rightFalse) := partition f right
      if f x then
        (join leftTrue x rightTrue, concat leftFalse rightFalse)
      else
        (concat leftTrue rightTrue, join leftFalse x rightFalse)

@[simp] theorem singleton_spec (x y : X.t) :
    In y (singleton x) ↔ X.eq y x := by
  simp [singleton, In, CompCert4Lean.Lib.MSetGenTree.tree.In]

@[simp] theorem create_spec (left right : tree X) (x y : X.t) :
    In y (create left x right) ↔
      X.eq y x ∨ In y left ∨ In y right := by
  exact CompCert4Lean.Lib.MSetGenTree.tree.in_node

theorem create_bst {left right : tree X} {x : X.t}
    (hl : bst left) (hr : bst right)
    (hlt : lt_tree x left) (hgt : gt_tree x right) :
    bst (create left x right) := by
  exact CompCert4Lean.Lib.MSetGenTree.tree.bst.BSNode _ _ _ _ hl hr hlt hgt

theorem singleton_bst (x : X.t) : bst (singleton x) := by
  exact CompCert4Lean.Lib.MSetGenTree.tree.bst.BSNode _ _ _ _
    .BSLeaf .BSLeaf
    (CompCert4Lean.Lib.MSetGenTree.tree.lt_leaf x)
    (CompCert4Lean.Lib.MSetGenTree.tree.gt_leaf x)

theorem bal_spec (left right : tree X) (x y : X.t) :
    In y (bal left x right) ↔ X.eq y x ∨ In y left ∨ In y right := by
  unfold bal
  by_cases hleft : zltb (zadd (height right) z2) (height left) = true
  · rw [if_pos hleft]
    cases left with
    | Leaf =>
        simp [assert_false, create, In,
          CompCert4Lean.Lib.MSetGenTree.tree.In]
    | Node lh ll lx lr =>
        simp only
        by_cases hsingle : zleb (height lr) (height ll) = true
        · rw [if_pos hsingle]
          simp [create, In, CompCert4Lean.Lib.MSetGenTree.tree.In,
            or_assoc, or_left_comm, or_comm]
        · rw [if_neg hsingle]
          cases lr with
          | Leaf =>
              simp [assert_false, create, In,
                CompCert4Lean.Lib.MSetGenTree.tree.In]
          | Node lrh lrl lrx lrr =>
              simp [create, In, CompCert4Lean.Lib.MSetGenTree.tree.In,
                or_assoc, or_left_comm, or_comm]
  · rw [if_neg hleft]
    by_cases hright : zltb (zadd (height left) z2) (height right) = true
    · rw [if_pos hright]
      cases right with
      | Leaf =>
          simp [assert_false, create, In,
            CompCert4Lean.Lib.MSetGenTree.tree.In]
      | Node rh rl rx rr =>
          simp only
          by_cases hsingle : zleb (height rl) (height rr) = true
          · rw [if_pos hsingle]
            simp [create, In, CompCert4Lean.Lib.MSetGenTree.tree.In,
              or_assoc, or_left_comm, or_comm]
          · rw [if_neg hsingle]
            cases rl with
            | Leaf =>
                simp [assert_false, create, In,
                  CompCert4Lean.Lib.MSetGenTree.tree.In]
            | Node rlh rll rlx rlr =>
                simp [create, In, CompCert4Lean.Lib.MSetGenTree.tree.In,
                  or_assoc, or_left_comm, or_comm]
    · rw [if_neg hright]
      simp [create, In, CompCert4Lean.Lib.MSetGenTree.tree.In]

theorem bal_bst {left right : tree X} {x : X.t}
    (hleftBst : bst left) (hrightBst : bst right)
    (hleftLt : lt_tree x left) (hrightGt : gt_tree x right) :
    bst (bal left x right) := by
  unfold bal
  by_cases hleft : zltb (zadd (height right) z2) (height left) = true
  · rw [if_pos hleft]
    cases left with
    | Leaf => exact create_bst hleftBst hrightBst hleftLt hrightGt
    | Node lh ll lx lr =>
        simp only
        have hi := CompCert4Lean.Lib.MSetGenTree.tree.bst_node_inv hleftBst
        rcases hi with ⟨hll, hlr, hllLt, hlrGt⟩
        have hlx : X.lt lx x :=
          hleftLt lx (.IsRoot lh ll lr lx (X.eq_refl lx))
        have hlrLtX : lt_tree x lr :=
          fun y hy => hleftLt y (.InRight lh ll lr lx hy)
        by_cases hsingle : zleb (height lr) (height ll) = true
        · rw [if_pos hsingle]
          have hinner : bst (create lr x right) :=
            create_bst hlr hrightBst hlrLtX hrightGt
          apply create_bst hll hinner hllLt
          exact CompCert4Lean.Lib.MSetGenTree.tree.gt_tree_node
            hlrGt
            (CompCert4Lean.Lib.MSetGenTree.tree.gt_tree_trans hlx hrightGt)
            hlx
        · rw [if_neg hsingle]
          cases lr with
          | Leaf => exact create_bst hleftBst hrightBst hleftLt hrightGt
          | Node lrh lrl lrx lrr =>
              have hilr := CompCert4Lean.Lib.MSetGenTree.tree.bst_node_inv hlr
              rcases hilr with ⟨hlrl, hlrr, hlrlLt, hlrrGt⟩
              have hlx_lrx : X.lt lx lrx :=
                hlrGt lrx (.IsRoot lrh lrl lrr lrx (X.eq_refl lrx))
              have hlrx_x : X.lt lrx x :=
                hleftLt lrx (.InRight lh ll (.Node lrh lrl lrx lrr) lx
                  (.IsRoot lrh lrl lrr lrx (X.eq_refl lrx)))
              have hleftInner : bst (create ll lx lrl) :=
                create_bst hll hlrl hllLt
                  (fun y hy => hlrGt y (.InLeft lrh lrl lrr lrx hy))
              have hrightInner : bst (create lrr x right) :=
                create_bst hlrr hrightBst
                  (fun y hy => hleftLt y
                    (.InRight lh ll (.Node lrh lrl lrx lrr) lx
                      (.InRight lrh lrl lrr lrx hy)))
                  hrightGt
              apply create_bst hleftInner hrightInner
              · exact CompCert4Lean.Lib.MSetGenTree.tree.lt_tree_node
                  (CompCert4Lean.Lib.MSetGenTree.tree.lt_tree_trans hlx_lrx hllLt)
                  hlrlLt hlx_lrx
              · exact CompCert4Lean.Lib.MSetGenTree.tree.gt_tree_node
                  hlrrGt
                  (CompCert4Lean.Lib.MSetGenTree.tree.gt_tree_trans hlrx_x hrightGt)
                  hlrx_x
  · rw [if_neg hleft]
    by_cases hright : zltb (zadd (height left) z2) (height right) = true
    · rw [if_pos hright]
      cases right with
      | Leaf => exact create_bst hleftBst hrightBst hleftLt hrightGt
      | Node rh rl rx rr =>
          simp only
          have hi := CompCert4Lean.Lib.MSetGenTree.tree.bst_node_inv hrightBst
          rcases hi with ⟨hrl, hrr, hrlLt, hrrGt⟩
          have hxr : X.lt x rx :=
            hrightGt rx (.IsRoot rh rl rr rx (X.eq_refl rx))
          have hgtXrl : gt_tree x rl :=
            fun y hy => hrightGt y (.InLeft rh rl rr rx hy)
          by_cases hsingle : zleb (height rl) (height rr) = true
          · rw [if_pos hsingle]
            have hinner : bst (create left x rl) :=
              create_bst hleftBst hrl hleftLt hgtXrl
            apply create_bst hinner hrr
            · exact CompCert4Lean.Lib.MSetGenTree.tree.lt_tree_node
                (CompCert4Lean.Lib.MSetGenTree.tree.lt_tree_trans hxr hleftLt)
                hrlLt hxr
            · exact hrrGt
          · rw [if_neg hsingle]
            cases rl with
            | Leaf => exact create_bst hleftBst hrightBst hleftLt hrightGt
            | Node rlh rll rlx rlr =>
                have hirl := CompCert4Lean.Lib.MSetGenTree.tree.bst_node_inv hrl
                rcases hirl with ⟨hrll, hrlr, hrllLt, hrlrGt⟩
                have hx_rlx : X.lt x rlx :=
                  hrightGt rlx (.InLeft rh (.Node rlh rll rlx rlr) rr rx
                    (.IsRoot rlh rll rlr rlx (X.eq_refl rlx)))
                have hrlx_rx : X.lt rlx rx :=
                  hrlLt rlx (.IsRoot rlh rll rlr rlx (X.eq_refl rlx))
                have hleftInner : bst (create left x rll) :=
                  create_bst hleftBst hrll hleftLt
                    (fun y hy => hrightGt y
                      (.InLeft rh (.Node rlh rll rlx rlr) rr rx
                        (.InLeft rlh rll rlr rlx hy)))
                have hrightInner : bst (create rlr rx rr) :=
                  create_bst hrlr hrr
                    (fun y hy => hrlLt y (.InRight rlh rll rlr rlx hy))
                    hrrGt
                apply create_bst hleftInner hrightInner
                · exact CompCert4Lean.Lib.MSetGenTree.tree.lt_tree_node
                    (CompCert4Lean.Lib.MSetGenTree.tree.lt_tree_trans hx_rlx hleftLt)
                    hrllLt hx_rlx
                · exact CompCert4Lean.Lib.MSetGenTree.tree.gt_tree_node
                    hrlrGt
                    (CompCert4Lean.Lib.MSetGenTree.tree.gt_tree_trans hrlx_rx hrrGt)
                    hrlx_rx
    · rw [if_neg hright]
      exact create_bst hleftBst hrightBst hleftLt hrightGt

theorem add_spec (s : tree X) (x y : X.t) :
    In y (add x s) ↔ X.eq y x ∨ In y s := by
  induction s with
  | Leaf => simp [add, singleton_spec, In,
      CompCert4Lean.Lib.MSetGenTree.tree.In]
  | Node h left value right ihl ihr =>
      simp only [add]
      cases X.compare x value with
      | lt hlt =>
          rw [bal_spec, ihl]
          simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
          simp only [or_assoc, or_left_comm, or_comm]
      | eq heq =>
          simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
          constructor
          · exact Or.inr
          · rintro (hyx | hy)
            · exact Or.inl (X.eq_trans y x value hyx heq)
            · exact hy
      | gt hgt =>
          rw [bal_spec, ihr]
          simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
          simp only [or_assoc, or_left_comm, or_comm]

theorem add_bst {s : tree X} (hs : bst s) (x : X.t) : bst (add x s) := by
  induction hs with
  | BSLeaf => exact singleton_bst x
  | BSNode info value left right hleft hright hlt hgt ihl ihr =>
      simp only [add]
      cases X.compare x value with
      | lt hx =>
          apply bal_bst ihl hright
          · intro y hy
            rcases (add_spec left x y).mp hy with hyx | hy
            · exact CompCert4Lean.Lib.MSetGenTree.tree.lt_of_eq_of_lt
                (X.eq_sym y x hyx) hx
            · exact hlt y hy
          · exact hgt
      | eq _ => exact .BSNode _ _ _ _ hleft hright hlt hgt
      | gt hx =>
          apply bal_bst hleft ihr
          · exact hlt
          · intro y hy
            rcases (add_spec right x y).mp hy with hyx | hy
            · exact CompCert4Lean.Lib.MSetGenTree.tree.lt_of_lt_of_eq
                hx (X.eq_sym y x hyx)
            · exact hgt y hy

theorem join_spec (left : tree X) (x : X.t) (right : tree X) (y : X.t) :
    In y (join left x right) ↔ X.eq y x ∨ In y left ∨ In y right := by
  cases left with
  | Leaf =>
      simp only [join]
      rw [add_spec]
      simp [In, CompCert4Lean.Lib.MSetGenTree.tree.In]
  | Node lh ll lx lr =>
      cases right with
      | Leaf =>
          simp only [join]
          rw [add_spec]
          simp [In, CompCert4Lean.Lib.MSetGenTree.tree.In,
            or_assoc, or_left_comm, or_comm]
      | Node rh rl rx rr =>
          simp only [join]
          by_cases hleft : zltb (zadd rh z2) lh = true
          · rw [if_pos hleft, bal_spec, join_spec]
            simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
            simp only [or_assoc, or_left_comm, or_comm]
          · rw [if_neg hleft]
            by_cases hright : zltb (zadd lh z2) rh = true
            · rw [if_pos hright, bal_spec, join_spec]
              simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
              simp only [or_assoc, or_left_comm, or_comm]
            · rw [if_neg hright]
              simp [create, In, CompCert4Lean.Lib.MSetGenTree.tree.In]
termination_by sizeOf left + sizeOf right
decreasing_by all_goals simp_all; omega

theorem join_bst (left : tree X) (x : X.t) (right : tree X)
    (hleft : bst left) (hright : bst right)
    (hlt : lt_tree x left) (hgt : gt_tree x right) :
    bst (join left x right) := by
  cases left with
  | Leaf =>
      simp only [join]
      exact add_bst hright x
  | Node lh ll lx lr =>
      cases right with
      | Leaf =>
          simp only [join]
          exact add_bst hleft x
      | Node rh rl rx rr =>
          simp only [join]
          have hli := CompCert4Lean.Lib.MSetGenTree.tree.bst_node_inv hleft
          have hri := CompCert4Lean.Lib.MSetGenTree.tree.bst_node_inv hright
          rcases hli with ⟨hll, hlr, hllLt, hlrGt⟩
          rcases hri with ⟨hrl, hrr, hrlLt, hrrGt⟩
          by_cases hleftHeavy : zltb (zadd rh z2) lh = true
          · rw [if_pos hleftHeavy]
            have hjoined : bst (join lr x (.Node rh rl rx rr)) :=
              join_bst lr x (.Node rh rl rx rr) hlr hright
                (fun y hy => hlt y (.InRight lh ll lr lx hy)) hgt
            apply bal_bst hll hjoined hllLt
            intro y hy
            rcases (join_spec lr x (.Node rh rl rx rr) y).mp hy with
              hyx | hylr | hyr
            · exact CompCert4Lean.Lib.MSetGenTree.tree.lt_of_lt_of_eq
                (hlt lx (.IsRoot lh ll lr lx (X.eq_refl lx))) (X.eq_sym y x hyx)
            · exact hlrGt y hylr
            · exact X.lt_trans lx x y
                (hlt lx (.IsRoot lh ll lr lx (X.eq_refl lx))) (hgt y hyr)
          · rw [if_neg hleftHeavy]
            by_cases hrightHeavy : zltb (zadd lh z2) rh = true
            · rw [if_pos hrightHeavy]
              have hjoined : bst (join (.Node lh ll lx lr) x rl) :=
                join_bst (.Node lh ll lx lr) x rl hleft hrl hlt
                  (fun y hy => hgt y (.InLeft rh rl rr rx hy))
              apply bal_bst hjoined hrr
              · intro y hy
                rcases (join_spec (.Node lh ll lx lr) x rl y).mp hy with
                  hyx | hyl | hyrl
                · exact CompCert4Lean.Lib.MSetGenTree.tree.lt_of_eq_of_lt
                    (X.eq_sym y x hyx)
                    (hgt rx (.IsRoot rh rl rr rx (X.eq_refl rx)))
                · exact X.lt_trans y x rx (hlt y hyl)
                    (hgt rx (.IsRoot rh rl rr rx (X.eq_refl rx)))
                · exact hrlLt y hyrl
              · exact hrrGt
            · rw [if_neg hrightHeavy]
              exact create_bst hleft hright hlt hgt
termination_by sizeOf left + sizeOf right
decreasing_by all_goals simp_all; omega

theorem remove_min_spec (left : tree X) (x : X.t) (right : tree X)
    (y : X.t) (h : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) :
    In y (.Node h left x right) ↔
      X.eq y (remove_min left x right).2 ∨
        In y (remove_min left x right).1 := by
  induction left generalizing x right h with
  | Leaf => simp [remove_min, In, CompCert4Lean.Lib.MSetGenTree.tree.In]
  | Node lh ll lx lr ihl ihr =>
      simp only [remove_min]
      generalize hp : remove_min ll lx lr = result
      cases result with
      | mk left' minimum =>
          simp only [Prod.fst, Prod.snd]
          rw [bal_spec]
          have ih := ihl (x := lx) (right := lr) (h := lh)
          rw [hp] at ih
          simp only [Prod.fst, Prod.snd] at ih
          simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node] at ih ⊢
          rw [ih]
          simp only [or_assoc, or_left_comm, or_comm]

theorem remove_min_bst_gt (left : tree X) (x : X.t) (right : tree X)
    (h : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (hbst : bst (.Node h left x right)) :
    bst (remove_min left x right).1 ∧
      gt_tree (remove_min left x right).2 (remove_min left x right).1 := by
  induction left generalizing x right h with
  | Leaf =>
      have hi := CompCert4Lean.Lib.MSetGenTree.tree.bst_node_inv hbst
      exact ⟨hi.2.1, hi.2.2.2⟩
  | Node lh ll lx lr ihl ihr =>
      have hi := CompCert4Lean.Lib.MSetGenTree.tree.bst_node_inv hbst
      rcases hi with ⟨hleft, hright, hleftLt, hrightGt⟩
      have hlefti := CompCert4Lean.Lib.MSetGenTree.tree.bst_node_inv hleft
      have hleft' : bst (.Node lh ll lx lr) :=
        .BSNode _ _ _ _ hlefti.1 hlefti.2.1 hlefti.2.2.1 hlefti.2.2.2
      have hrec := ihl (x := lx) (right := lr) (h := lh) hleft'
      generalize hp : remove_min ll lx lr = result at hrec ⊢
      cases result with
      | mk rest minimum =>
          simp only [remove_min, hp, Prod.fst, Prod.snd] at hrec ⊢
          rcases hrec with ⟨hrest, hminimumRest⟩
          have hminimumInLeft : In minimum (.Node lh ll lx lr) := by
            have hs := remove_min_spec ll lx lr minimum lh
            rw [hp] at hs
            simp only [Prod.fst, Prod.snd] at hs
            exact hs.mpr (Or.inl (X.eq_refl minimum))
          have hminimumX : X.lt minimum x := hleftLt minimum hminimumInLeft
          constructor
          · apply bal_bst hrest hright
            · intro y hy
              have hs := remove_min_spec ll lx lr y lh
              rw [hp] at hs
              simp only [Prod.fst, Prod.snd] at hs
              exact hleftLt y (hs.mpr (Or.inr hy))
            · exact hrightGt
          · intro y hy
            rcases (bal_spec rest right x y).mp hy with hyx | hyrest | hyright
            · exact CompCert4Lean.Lib.MSetGenTree.tree.lt_of_lt_of_eq
                hminimumX (X.eq_sym y x hyx)
            · exact hminimumRest y hyrest
            · exact X.lt_trans minimum x y hminimumX (hrightGt y hyright)

theorem remove_min_bst (left : tree X) (x : X.t) (right : tree X)
    (h : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (hbst : bst (.Node h left x right)) :
    bst (remove_min left x right).1 :=
  (remove_min_bst_gt left x right h hbst).1

theorem remove_min_ok (left : tree X) (x : X.t) (right : tree X)
    (h : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (hbst : bst (.Node h left x right)) :
    bst (remove_min left x right).1 :=
  remove_min_bst left x right h hbst

theorem remove_min_gt_tree (left : tree X) (x : X.t) (right : tree X)
    (h : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (hbst : bst (.Node h left x right)) :
    gt_tree (remove_min left x right).2 (remove_min left x right).1 :=
  (remove_min_bst_gt left x right h hbst).2

theorem merge_spec (s₁ s₂ : tree X) (y : X.t) :
    In y (merge s₁ s₂) ↔ In y s₁ ∨ In y s₂ := by
  cases s₁ with
  | Leaf => simp [merge, In, CompCert4Lean.Lib.MSetGenTree.tree.In]
  | Node h₁ l₁ x₁ r₁ =>
      cases s₂ with
      | Leaf => simp [merge, In, CompCert4Lean.Lib.MSetGenTree.tree.In]
      | Node h₂ l₂ x₂ r₂ =>
          simp only [merge]
          generalize hp : remove_min l₂ x₂ r₂ = result
          cases result with
          | mk rest minimum =>
              simp only
              rw [bal_spec]
              have hmin := remove_min_spec l₂ x₂ r₂ y h₂
              rw [hp] at hmin
              simp only [Prod.fst, Prod.snd] at hmin
              simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node] at hmin ⊢
              rw [hmin]
              simp only [or_assoc, or_left_comm, or_comm]

theorem merge_bst (s₁ s₂ : tree X) (h₁ : bst s₁) (h₂ : bst s₂)
    (between : ∀ y₁ y₂, In y₁ s₁ → In y₂ s₂ → X.lt y₁ y₂) :
    bst (merge s₁ s₂) := by
  cases s₁ with
  | Leaf => simpa [merge] using h₂
  | Node h₁n l₁ x₁ r₁ =>
      cases s₂ with
      | Leaf => simpa [merge] using h₁
      | Node h₂n l₂ x₂ r₂ =>
          have h₂i := CompCert4Lean.Lib.MSetGenTree.tree.bst_node_inv h₂
          have h₂' : bst (.Node h₂n l₂ x₂ r₂) :=
            .BSNode _ _ _ _ h₂i.1 h₂i.2.1 h₂i.2.2.1 h₂i.2.2.2
          have hremove := remove_min_bst_gt l₂ x₂ r₂ h₂n h₂'
          generalize hp : remove_min l₂ x₂ r₂ = result at hremove ⊢
          cases result with
          | mk rest minimum =>
              simp only [merge, hp, Prod.fst, Prod.snd] at hremove ⊢
              rcases hremove with ⟨hrest, hminimumRest⟩
              apply bal_bst h₁ hrest
              · intro y hy
                apply between y minimum hy
                have hs := remove_min_spec l₂ x₂ r₂ minimum h₂n
                rw [hp] at hs
                simp only [Prod.fst, Prod.snd] at hs
                exact hs.mpr (Or.inl (X.eq_refl minimum))
              · exact hminimumRest

theorem concat_spec (s₁ s₂ : tree X) (y : X.t) :
    In y (concat s₁ s₂) ↔ In y s₁ ∨ In y s₂ := by
  cases s₁ with
  | Leaf => simp [concat, In, CompCert4Lean.Lib.MSetGenTree.tree.In]
  | Node h₁ l₁ x₁ r₁ =>
      cases s₂ with
      | Leaf => simp [concat, In, CompCert4Lean.Lib.MSetGenTree.tree.In]
      | Node h₂ l₂ x₂ r₂ =>
          simp only [concat]
          generalize hp : remove_min l₂ x₂ r₂ = result
          cases result with
          | mk rest minimum =>
              simp only
              rw [join_spec]
              have hmin := remove_min_spec l₂ x₂ r₂ y h₂
              rw [hp] at hmin
              simp only [Prod.fst, Prod.snd] at hmin
              simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node] at hmin ⊢
              rw [hmin]
              simp only [or_assoc, or_left_comm, or_comm]

theorem concat_bst (s₁ s₂ : tree X) (h₁ : bst s₁) (h₂ : bst s₂)
    (between : ∀ y₁ y₂, In y₁ s₁ → In y₂ s₂ → X.lt y₁ y₂) :
    bst (concat s₁ s₂) := by
  cases s₁ with
  | Leaf => simpa [concat] using h₂
  | Node h₁n l₁ x₁ r₁ =>
      cases s₂ with
      | Leaf => simpa [concat] using h₁
      | Node h₂n l₂ x₂ r₂ =>
          have h₂i := CompCert4Lean.Lib.MSetGenTree.tree.bst_node_inv h₂
          have h₂' : bst (.Node h₂n l₂ x₂ r₂) :=
            .BSNode _ _ _ _ h₂i.1 h₂i.2.1 h₂i.2.2.1 h₂i.2.2.2
          have hremove := remove_min_bst_gt l₂ x₂ r₂ h₂n h₂'
          generalize hp : remove_min l₂ x₂ r₂ = result at hremove ⊢
          cases result with
          | mk rest minimum =>
              simp only [concat, hp, Prod.fst, Prod.snd] at hremove ⊢
              rcases hremove with ⟨hrest, hminimumRest⟩
              apply join_bst (.Node h₁n l₁ x₁ r₁) minimum rest h₁ hrest
              · intro y hy
                apply between y minimum hy
                have hs := remove_min_spec l₂ x₂ r₂ minimum h₂n
                rw [hp] at hs
                simp only [Prod.fst, Prod.snd] at hs
                exact hs.mpr (Or.inl (X.eq_refl minimum))
              · exact hminimumRest

theorem remove_spec {s : tree X} (hs : bst s) (x y : X.t) :
    In y (remove x s) ↔ In y s ∧ ¬ X.eq y x := by
  induction hs with
  | BSLeaf => simp [remove, In, CompCert4Lean.Lib.MSetGenTree.tree.In]
  | BSNode info value left right hleft hright hlt hgt ihl ihr =>
      simp only [remove]
      cases X.compare x value with
      | eq hx =>
          rw [merge_spec]
          simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
          constructor
          · intro hy
            constructor
            · rcases hy with hy | hy
              · exact Or.inr (Or.inl hy)
              · exact Or.inr (Or.inr hy)
            · intro hyx
              rcases hy with hy | hy
              · have hyv := hlt y hy
                have hyvalue : X.eq y value := X.eq_trans y x value hyx hx
                exact X.lt_not_eq y value hyv hyvalue
              · have hvaluey := hgt y hy
                have hvalueyEq : X.eq value y :=
                  X.eq_trans value x y (X.eq_sym x value hx)
                    (X.eq_sym y x hyx)
                exact X.lt_not_eq value y hvaluey hvalueyEq
          · rintro ⟨hy, hne⟩
            rcases hy with hyroot | hyleft | hyright
            · exfalso
              apply hne
              exact X.eq_trans y value x hyroot (X.eq_sym x value hx)
            · exact Or.inl hyleft
            · exact Or.inr hyright
      | lt hx =>
          rw [bal_spec]
          simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
          constructor
          · intro hy
            rcases hy with hyroot | hyleft | hyright
            · constructor
              · exact Or.inl hyroot
              · intro hyx
                exact X.lt_not_eq x value hx
                  (X.eq_trans x y value (X.eq_sym y x hyx) hyroot)
            · rcases ihl.mp hyleft with ⟨hyleft, hne⟩
              exact ⟨Or.inr (Or.inl hyleft), hne⟩
            · constructor
              · exact Or.inr (Or.inr hyright)
              · intro hyx
                have hvaluex := CompCert4Lean.Lib.MSetGenTree.tree.lt_of_lt_of_eq
                  (hgt y hyright) hyx
                exact CompCert4Lean.Lib.MSetGenTree.tree.lt_asymm hx hvaluex
          · rintro ⟨hy, hne⟩
            rcases hy with hyroot | hyleft | hyright
            · exact Or.inl hyroot
            · exact Or.inr (Or.inl (ihl.mpr ⟨hyleft, hne⟩))
            · exact Or.inr (Or.inr hyright)
      | gt hx =>
          rw [bal_spec]
          simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
          constructor
          · intro hy
            rcases hy with hyroot | hyleft | hyright
            · constructor
              · exact Or.inl hyroot
              · intro hyx
                exact X.lt_not_eq value x hx
                  (X.eq_trans value y x (X.eq_sym y value hyroot) hyx)
            · constructor
              · exact Or.inr (Or.inl hyleft)
              · intro hyx
                have hxy := CompCert4Lean.Lib.MSetGenTree.tree.lt_of_eq_of_lt
                  hyx (hlt y hyleft)
                exact CompCert4Lean.Lib.MSetGenTree.tree.lt_asymm hx hxy
            · rcases ihr.mp hyright with ⟨hyright, hne⟩
              exact ⟨Or.inr (Or.inr hyright), hne⟩
          · rintro ⟨hy, hne⟩
            rcases hy with hyroot | hyleft | hyright
            · exact Or.inl hyroot
            · exact Or.inr (Or.inl hyleft)
            · exact Or.inr (Or.inr (ihr.mpr ⟨hyright, hne⟩))

theorem remove_bst {s : tree X} (hs : bst s) (x : X.t) : bst (remove x s) := by
  induction hs with
  | BSLeaf => exact .BSLeaf
  | BSNode info value left right hleft hright hlt hgt ihl ihr =>
      simp only [remove]
      cases X.compare x value with
      | eq _ =>
          apply merge_bst left right hleft hright
          intro y₁ y₂ hy₁ hy₂
          exact X.lt_trans y₁ value y₂ (hlt y₁ hy₁) (hgt y₂ hy₂)
      | lt _ =>
          apply bal_bst ihl hright
          · intro y hy
            exact hlt y ((remove_spec hleft x y).mp hy).1
          · exact hgt
      | gt _ =>
          apply bal_bst hleft ihr
          · exact hlt
          · intro y hy
            exact hgt y ((remove_spec hright x y).mp hy).1

theorem split_left_spec {s : tree X} (hs : bst s) (x y : X.t) :
    In y (split x s).t_left ↔ In y s ∧ X.lt y x := by
  induction hs with
  | BSLeaf => simp [split, In, CompCert4Lean.Lib.MSetGenTree.tree.In]
  | BSNode info value left right hleft hright hlt hgt ihl ihr =>
      simp only [split]
      cases X.compare x value with
      | lt hx =>
          simp only [triple.t_left]
          rw [ihl]
          simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
          constructor
          · rintro ⟨hy, hyx⟩
            exact ⟨Or.inr (Or.inl hy), hyx⟩
          · rintro ⟨hy, hyx⟩
            rcases hy with hyroot | hyleft | hyright
            · have hxy : X.lt x y :=
                CompCert4Lean.Lib.MSetGenTree.tree.lt_of_lt_of_eq hx
                  (X.eq_sym y value hyroot)
              exact False.elim
                (CompCert4Lean.Lib.MSetGenTree.tree.lt_asymm hxy hyx)
            · exact ⟨hyleft, hyx⟩
            · have hxy := X.lt_trans x value y hx (hgt y hyright)
              exact False.elim
                (CompCert4Lean.Lib.MSetGenTree.tree.lt_asymm hxy hyx)
      | eq hx =>
          simp only [triple.t_left]
          simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
          constructor
          · intro hy
            exact ⟨Or.inr (Or.inl hy),
              CompCert4Lean.Lib.MSetGenTree.tree.lt_of_lt_of_eq
                (hlt y hy) (X.eq_sym x value hx)⟩
          · rintro ⟨hy, hyx⟩
            rcases hy with hyroot | hyleft | hyright
            · have hyxEq := X.eq_trans y value x hyroot (X.eq_sym x value hx)
              exact False.elim (X.lt_not_eq y x hyx hyxEq)
            · exact hyleft
            · have hxy : X.lt x y :=
                CompCert4Lean.Lib.MSetGenTree.tree.lt_of_eq_of_lt
                  (X.eq_sym x value hx) (hgt y hyright)
              exact False.elim
                (CompCert4Lean.Lib.MSetGenTree.tree.lt_asymm hxy hyx)
      | gt hx =>
          simp only [triple.t_left]
          rw [join_spec, ihr]
          simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
          constructor
          · intro hy
            rcases hy with hyroot | hyleft | ⟨hyright, hyx⟩
            · exact ⟨Or.inl hyroot,
                CompCert4Lean.Lib.MSetGenTree.tree.lt_of_eq_of_lt
                  (X.eq_sym y value hyroot) hx⟩
            · exact ⟨Or.inr (Or.inl hyleft),
                X.lt_trans y value x (hlt y hyleft) hx⟩
            · exact ⟨Or.inr (Or.inr hyright), hyx⟩
          · rintro ⟨hy, hyx⟩
            rcases hy with hyroot | hyleft | hyright
            · exact Or.inl hyroot
            · exact Or.inr (Or.inl hyleft)
            · exact Or.inr (Or.inr ⟨hyright, hyx⟩)

theorem split_right_spec {s : tree X} (hs : bst s) (x y : X.t) :
    In y (split x s).t_right ↔ In y s ∧ X.lt x y := by
  induction hs with
  | BSLeaf => simp [split, In, CompCert4Lean.Lib.MSetGenTree.tree.In]
  | BSNode info value left right hleft hright hlt hgt ihl ihr =>
      simp only [split]
      cases X.compare x value with
      | lt hx =>
          simp only [triple.t_right]
          rw [join_spec, ihl]
          simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
          constructor
          · intro hy
            rcases hy with hyroot | ⟨hyleft, hxy⟩ | hyright
            · exact ⟨Or.inl hyroot,
                CompCert4Lean.Lib.MSetGenTree.tree.lt_of_lt_of_eq
                  hx (X.eq_sym y value hyroot)⟩
            · exact ⟨Or.inr (Or.inl hyleft), hxy⟩
            · exact ⟨Or.inr (Or.inr hyright),
                X.lt_trans x value y hx (hgt y hyright)⟩
          · rintro ⟨hy, hxy⟩
            rcases hy with hyroot | hyleft | hyright
            · exact Or.inl hyroot
            · exact Or.inr (Or.inl ⟨hyleft, hxy⟩)
            · exact Or.inr (Or.inr hyright)
      | eq hx =>
          simp only [triple.t_right]
          simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
          constructor
          · intro hy
            exact ⟨Or.inr (Or.inr hy),
              CompCert4Lean.Lib.MSetGenTree.tree.lt_of_eq_of_lt
                (X.eq_sym x value hx) (hgt y hy)⟩
          · rintro ⟨hy, hxy⟩
            rcases hy with hyroot | hyleft | hyright
            · have hxyEq := X.eq_trans x value y hx (X.eq_sym y value hyroot)
              exact False.elim (X.lt_not_eq x y hxy hxyEq)
            · have hyx : X.lt y x :=
                CompCert4Lean.Lib.MSetGenTree.tree.lt_of_lt_of_eq
                  (hlt y hyleft) (X.eq_sym x value hx)
              exact False.elim
                (CompCert4Lean.Lib.MSetGenTree.tree.lt_asymm hxy hyx)
            · exact hyright
      | gt hx =>
          simp only [triple.t_right]
          rw [ihr]
          simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
          constructor
          · rintro ⟨hy, hxy⟩
            exact ⟨Or.inr (Or.inr hy), hxy⟩
          · rintro ⟨hy, hxy⟩
            rcases hy with hyroot | hyleft | hyright
            · have hyx : X.lt y x :=
                CompCert4Lean.Lib.MSetGenTree.tree.lt_of_eq_of_lt
                  (X.eq_sym y value hyroot) hx
              exact False.elim
                (CompCert4Lean.Lib.MSetGenTree.tree.lt_asymm hxy hyx)
            · have hyx := X.lt_trans y value x (hlt y hyleft) hx
              exact False.elim
                (CompCert4Lean.Lib.MSetGenTree.tree.lt_asymm hxy hyx)
            · exact ⟨hyright, hxy⟩

theorem split_in_spec {s : tree X} (hs : bst s) (x : X.t) :
    (split x s).t_in = true ↔ In x s := by
  induction hs with
  | BSLeaf => simp [split, In, CompCert4Lean.Lib.MSetGenTree.tree.In]
  | BSNode info value left right hleft hright hlt hgt ihl ihr =>
      simp only [split]
      cases X.compare x value with
      | lt hx =>
          simp only [triple.t_in, ihl]
          simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
          constructor
          · exact fun hy => Or.inr (Or.inl hy)
          · intro hy
            rcases hy with hyroot | hyleft | hyright
            · exact False.elim (X.lt_not_eq x value hx hyroot)
            · exact hyleft
            · exact False.elim
                (CompCert4Lean.Lib.MSetGenTree.tree.lt_asymm hx (hgt x hyright))
      | eq hx => simp [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node, hx]
      | gt hx =>
          simp only [triple.t_in, ihr]
          simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
          constructor
          · exact fun hy => Or.inr (Or.inr hy)
          · intro hy
            rcases hy with hyroot | hyleft | hyright
            · exact False.elim
                (X.lt_not_eq value x hx (X.eq_sym x value hyroot))
            · exact False.elim
                (CompCert4Lean.Lib.MSetGenTree.tree.lt_asymm (hlt x hyleft) hx)
            · exact hyright

theorem split_bst {s : tree X} (hs : bst s) (x : X.t) :
    bst (split x s).t_left ∧ bst (split x s).t_right := by
  induction hs with
  | BSLeaf => exact ⟨.BSLeaf, .BSLeaf⟩
  | BSNode info value left right hleft hright hlt hgt ihl ihr =>
      simp only [split]
      cases X.compare x value with
      | lt hx =>
          simp only [triple.t_left, triple.t_right]
          constructor
          · exact ihl.1
          · apply join_bst (split x left).t_right value right ihl.2 hright
            · intro y hy
              exact hlt y ((split_right_spec hleft x y).mp hy).1
            · exact hgt
      | eq _ => exact ⟨hleft, hright⟩
      | gt hx =>
          simp only [triple.t_left, triple.t_right]
          constructor
          · apply join_bst left value (split x right).t_left hleft ihr.1
            · exact hlt
            · intro y hy
              exact hgt y ((split_left_spec hright x y).mp hy).1
          · exact ihr.2

theorem split_membership_spec {s : tree X} (hs : bst s) (x y : X.t) :
    In y s ↔
      In y (split x s).t_left ∨
        (X.eq y x ∧ (split x s).t_in = true) ∨
        In y (split x s).t_right := by
  constructor
  · intro hy
    cases X.compare y x with
    | lt hyx => exact Or.inl ((split_left_spec hs x y).mpr ⟨hy, hyx⟩)
    | eq hyx =>
        have hx : In x s :=
          CompCert4Lean.Lib.MSetGenTree.tree.in_of_eq hyx hy
        exact Or.inr (Or.inl ⟨hyx, (split_in_spec hs x).mpr hx⟩)
    | gt hxy => exact Or.inr (Or.inr ((split_right_spec hs x y).mpr ⟨hy, hxy⟩))
  · intro hy
    rcases hy with hleft | ⟨hyx, hpresent⟩ | hright
    · exact (split_left_spec hs x y).mp hleft |>.1
    · have hx : In x s := (split_in_spec hs x).mp hpresent
      exact CompCert4Lean.Lib.MSetGenTree.tree.in_of_eq (X.eq_sym y x hyx) hx
    · exact (split_right_spec hs x y).mp hright |>.1

theorem union_spec {s₁ s₂ : tree X} (h₁ : bst s₁) (h₂ : bst s₂) (y : X.t) :
    In y (union s₁ s₂) ↔ In y s₁ ∨ In y s₂ := by
  induction h₁ generalizing s₂ with
  | BSLeaf => simp [union, In, CompCert4Lean.Lib.MSetGenTree.tree.In]
  | BSNode info value left right hleft hright hlt hgt ihl ihr =>
      cases s₂ with
      | Leaf => simp [union, In, CompCert4Lean.Lib.MSetGenTree.tree.In]
      | Node info₂ left₂ value₂ right₂ =>
          simp only [union]
          have hsplit := split_bst h₂ value
          rw [join_spec, ihl hsplit.1, ihr hsplit.2]
          simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
          constructor
          · intro hy
            rcases hy with hyroot | hyleft | hyright
            · exact Or.inl (Or.inl hyroot)
            · rcases hyleft with hyleft | hsplitLeft
              · exact Or.inl (Or.inr (Or.inl hyleft))
              · exact Or.inr ((CompCert4Lean.Lib.MSetGenTree.tree.in_node).mp
                  ((split_left_spec h₂ value y).mp hsplitLeft).1)
            · rcases hyright with hyright | hsplitRight
              · exact Or.inl (Or.inr (Or.inr hyright))
              · exact Or.inr ((CompCert4Lean.Lib.MSetGenTree.tree.in_node).mp
                  ((split_right_spec h₂ value y).mp hsplitRight).1)
          · intro hy
            rcases hy with hy₁ | hy₂
            · rcases hy₁ with hyroot | hyleft | hyright
              · exact Or.inl hyroot
              · exact Or.inr (Or.inl (Or.inl hyleft))
              · exact Or.inr (Or.inr (Or.inl hyright))
            · cases X.compare y value with
              | lt hyvalue =>
                  exact Or.inr (Or.inl (Or.inr
                    ((split_left_spec h₂ value y).mpr
                      ⟨(CompCert4Lean.Lib.MSetGenTree.tree.in_node).mpr hy₂, hyvalue⟩)))
              | eq hyvalue => exact Or.inl hyvalue
              | gt hvaluey =>
                  exact Or.inr (Or.inr (Or.inr
                    ((split_right_spec h₂ value y).mpr
                      ⟨(CompCert4Lean.Lib.MSetGenTree.tree.in_node).mpr hy₂, hvaluey⟩)))

theorem union_bst {s₁ s₂ : tree X} (h₁ : bst s₁) (h₂ : bst s₂) :
    bst (union s₁ s₂) := by
  induction h₁ generalizing s₂ with
  | BSLeaf => simpa [union] using h₂
  | BSNode info value left right hleft hright hlt hgt ihl ihr =>
      cases s₂ with
      | Leaf => exact .BSNode _ _ _ _ hleft hright hlt hgt
      | Node info₂ left₂ value₂ right₂ =>
          simp only [union]
          have hsplit := split_bst h₂ value
          have hleftUnion := ihl hsplit.1
          have hrightUnion := ihr hsplit.2
          apply join_bst _ value _ hleftUnion hrightUnion
          · intro y hy
            rcases (union_spec hleft hsplit.1 y).mp hy with hy | hy
            · exact hlt y hy
            · exact (split_left_spec h₂ value y).mp hy |>.2
          · intro y hy
            rcases (union_spec hright hsplit.2 y).mp hy with hy | hy
            · exact hgt y hy
            · exact (split_right_spec h₂ value y).mp hy |>.2

theorem inter_spec_bst {s₁ : tree X} (h₁ : bst s₁) :
    ∀ (s₂ : tree X), bst s₂ →
      bst (inter s₁ s₂) ∧
        ∀ y, In y (inter s₁ s₂) ↔ In y s₁ ∧ In y s₂ := by
  induction h₁ with
  | BSLeaf =>
      intro s₂ h₂
      exact ⟨.BSLeaf, fun y => by
        simp [inter, In, CompCert4Lean.Lib.MSetGenTree.tree.In]⟩
  | BSNode info value left right hleft hright hlt hgt ihl ihr =>
      intro s₂ h₂
      cases s₂ with
      | Leaf =>
          exact ⟨.BSLeaf, fun y => by
            simp [inter, In, CompCert4Lean.Lib.MSetGenTree.tree.In]⟩
      | Node info₂ left₂ value₂ right₂ =>
          simp only [inter]
          have hsplit := split_bst h₂ value
          have hleftInter := ihl _ hsplit.1
          have hrightInter := ihr _ hsplit.2
          by_cases hpresent : (split value (.Node info₂ left₂ value₂ right₂)).t_in = true
          · rw [if_pos hpresent]
            constructor
            · apply join_bst _ value _ hleftInter.1 hrightInter.1
              · intro y hy
                exact hlt y (hleftInter.2 y |>.mp hy).1
              · intro y hy
                exact hgt y (hrightInter.2 y |>.mp hy).1
            · intro y
              rw [join_spec, hleftInter.2 y, hrightInter.2 y]
              simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
              constructor
              · intro hy
                rcases hy with hyroot | ⟨hyl, hysl⟩ | ⟨hyr, hysr⟩
                · have hvalue₂ : In value (.Node info₂ left₂ value₂ right₂) :=
                    (split_in_spec h₂ value).mp hpresent
                  exact ⟨Or.inl hyroot,
                    (CompCert4Lean.Lib.MSetGenTree.tree.in_node).mp
                      (CompCert4Lean.Lib.MSetGenTree.tree.in_of_eq
                        (X.eq_sym y value hyroot) hvalue₂)⟩
                · exact ⟨Or.inr (Or.inl hyl),
                    (CompCert4Lean.Lib.MSetGenTree.tree.in_node).mp
                      ((split_left_spec h₂ value y).mp hysl).1⟩
                · exact ⟨Or.inr (Or.inr hyr),
                    (CompCert4Lean.Lib.MSetGenTree.tree.in_node).mp
                      ((split_right_spec h₂ value y).mp hysr).1⟩
              · rintro ⟨hy₁, hy₂⟩
                rcases hy₁ with hyroot | hyl | hyr
                · exact Or.inl hyroot
                · exact Or.inr (Or.inl ⟨hyl,
                    (split_left_spec h₂ value y).mpr
                      ⟨(CompCert4Lean.Lib.MSetGenTree.tree.in_node).mpr hy₂, hlt y hyl⟩⟩)
                · exact Or.inr (Or.inr ⟨hyr,
                    (split_right_spec h₂ value y).mpr
                      ⟨(CompCert4Lean.Lib.MSetGenTree.tree.in_node).mpr hy₂, hgt y hyr⟩⟩)
          · rw [if_neg hpresent]
            constructor
            · apply concat_bst _ _ hleftInter.1 hrightInter.1
              intro y₁ y₂ hy₁ hy₂
              exact X.lt_trans y₁ value y₂
                (hlt y₁ (hleftInter.2 y₁ |>.mp hy₁).1)
                (hgt y₂ (hrightInter.2 y₂ |>.mp hy₂).1)
            · intro y
              rw [concat_spec, hleftInter.2 y, hrightInter.2 y]
              simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
              constructor
              · intro hy
                rcases hy with ⟨hyl, hysl⟩ | ⟨hyr, hysr⟩
                · exact ⟨Or.inr (Or.inl hyl),
                    (CompCert4Lean.Lib.MSetGenTree.tree.in_node).mp
                      ((split_left_spec h₂ value y).mp hysl).1⟩
                · exact ⟨Or.inr (Or.inr hyr),
                    (CompCert4Lean.Lib.MSetGenTree.tree.in_node).mp
                      ((split_right_spec h₂ value y).mp hysr).1⟩
              · rintro ⟨hy₁, hy₂⟩
                rcases hy₁ with hyroot | hyl | hyr
                · have hvalue₂ : In value (.Node info₂ left₂ value₂ right₂) :=
                    CompCert4Lean.Lib.MSetGenTree.tree.in_of_eq hyroot
                      ((CompCert4Lean.Lib.MSetGenTree.tree.in_node).mpr hy₂)
                  exact False.elim (hpresent ((split_in_spec h₂ value).mpr hvalue₂))
                · exact Or.inl ⟨hyl,
                    (split_left_spec h₂ value y).mpr
                      ⟨(CompCert4Lean.Lib.MSetGenTree.tree.in_node).mpr hy₂, hlt y hyl⟩⟩
                · exact Or.inr ⟨hyr,
                    (split_right_spec h₂ value y).mpr
                      ⟨(CompCert4Lean.Lib.MSetGenTree.tree.in_node).mpr hy₂, hgt y hyr⟩⟩

theorem inter_spec {s₁ s₂ : tree X} (h₁ : bst s₁) (h₂ : bst s₂) (y : X.t) :
    In y (inter s₁ s₂) ↔ In y s₁ ∧ In y s₂ :=
  (inter_spec_bst h₁ s₂ h₂).2 y

theorem inter_bst {s₁ s₂ : tree X} (h₁ : bst s₁) (h₂ : bst s₂) :
    bst (inter s₁ s₂) :=
  (inter_spec_bst h₁ s₂ h₂).1

theorem diff_spec_bst {s₁ : tree X} (h₁ : bst s₁) :
    ∀ (s₂ : tree X), bst s₂ →
      bst (diff s₁ s₂) ∧
        ∀ y, In y (diff s₁ s₂) ↔ In y s₁ ∧ ¬ In y s₂ := by
  induction h₁ with
  | BSLeaf =>
      intro s₂ h₂
      exact ⟨.BSLeaf, fun y => by
        simp [diff, In, CompCert4Lean.Lib.MSetGenTree.tree.In]⟩
  | BSNode info value left right hleft hright hlt hgt ihl ihr =>
      intro s₂ h₂
      cases s₂ with
      | Leaf =>
          exact ⟨.BSNode _ _ _ _ hleft hright hlt hgt, fun y => by
            simp [diff, In, CompCert4Lean.Lib.MSetGenTree.tree.In]⟩
      | Node info₂ left₂ value₂ right₂ =>
          simp only [diff]
          have hsplit := split_bst h₂ value
          have hleftDiff := ihl _ hsplit.1
          have hrightDiff := ihr _ hsplit.2
          by_cases hpresent : (split value (.Node info₂ left₂ value₂ right₂)).t_in = true
          · rw [if_pos hpresent]
            constructor
            · apply concat_bst _ _ hleftDiff.1 hrightDiff.1
              intro y₁ y₂ hy₁ hy₂
              exact X.lt_trans y₁ value y₂
                (hlt y₁ (hleftDiff.2 y₁ |>.mp hy₁).1)
                (hgt y₂ (hrightDiff.2 y₂ |>.mp hy₂).1)
            · intro y
              rw [concat_spec, hleftDiff.2 y, hrightDiff.2 y]
              simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
              constructor
              · intro hy
                rcases hy with ⟨hyl, hnsl⟩ | ⟨hyr, hnsr⟩
                · constructor
                  · exact Or.inr (Or.inl hyl)
                  · intro hy₂
                    exact hnsl ((split_left_spec h₂ value y).mpr
                      ⟨(CompCert4Lean.Lib.MSetGenTree.tree.in_node).mpr hy₂, hlt y hyl⟩)
                · constructor
                  · exact Or.inr (Or.inr hyr)
                  · intro hy₂
                    exact hnsr ((split_right_spec h₂ value y).mpr
                      ⟨(CompCert4Lean.Lib.MSetGenTree.tree.in_node).mpr hy₂, hgt y hyr⟩)
              · rintro ⟨hy₁, hny₂⟩
                rcases hy₁ with hyroot | hyl | hyr
                · have hvalue₂ : In value (.Node info₂ left₂ value₂ right₂) :=
                    (split_in_spec h₂ value).mp hpresent
                  have hy₂ := CompCert4Lean.Lib.MSetGenTree.tree.in_of_eq
                    (X.eq_sym y value hyroot) hvalue₂
                  exact False.elim
                    (hny₂ ((CompCert4Lean.Lib.MSetGenTree.tree.in_node).mp hy₂))
                · exact Or.inl ⟨hyl, fun hsl =>
                    hny₂ ((CompCert4Lean.Lib.MSetGenTree.tree.in_node).mp
                      ((split_left_spec h₂ value y).mp hsl).1)⟩
                · exact Or.inr ⟨hyr, fun hsr =>
                    hny₂ ((CompCert4Lean.Lib.MSetGenTree.tree.in_node).mp
                      ((split_right_spec h₂ value y).mp hsr).1)⟩
          · rw [if_neg hpresent]
            constructor
            · apply join_bst _ value _ hleftDiff.1 hrightDiff.1
              · intro y hy
                exact hlt y (hleftDiff.2 y |>.mp hy).1
              · intro y hy
                exact hgt y (hrightDiff.2 y |>.mp hy).1
            · intro y
              rw [join_spec, hleftDiff.2 y, hrightDiff.2 y]
              simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
              constructor
              · intro hy
                rcases hy with hyroot | ⟨hyl, hnsl⟩ | ⟨hyr, hnsr⟩
                · constructor
                  · exact Or.inl hyroot
                  · intro hy₂
                    have hvalue₂ : In value (.Node info₂ left₂ value₂ right₂) :=
                      CompCert4Lean.Lib.MSetGenTree.tree.in_of_eq hyroot
                        ((CompCert4Lean.Lib.MSetGenTree.tree.in_node).mpr hy₂)
                    exact hpresent ((split_in_spec h₂ value).mpr hvalue₂)
                · constructor
                  · exact Or.inr (Or.inl hyl)
                  · intro hy₂
                    exact hnsl ((split_left_spec h₂ value y).mpr
                      ⟨(CompCert4Lean.Lib.MSetGenTree.tree.in_node).mpr hy₂, hlt y hyl⟩)
                · constructor
                  · exact Or.inr (Or.inr hyr)
                  · intro hy₂
                    exact hnsr ((split_right_spec h₂ value y).mpr
                      ⟨(CompCert4Lean.Lib.MSetGenTree.tree.in_node).mpr hy₂, hgt y hyr⟩)
              · rintro ⟨hy₁, hny₂⟩
                rcases hy₁ with hyroot | hyl | hyr
                · exact Or.inl hyroot
                · exact Or.inr (Or.inl ⟨hyl, fun hsl =>
                    hny₂ ((CompCert4Lean.Lib.MSetGenTree.tree.in_node).mp
                      ((split_left_spec h₂ value y).mp hsl).1)⟩)
                · exact Or.inr (Or.inr ⟨hyr, fun hsr =>
                    hny₂ ((CompCert4Lean.Lib.MSetGenTree.tree.in_node).mp
                      ((split_right_spec h₂ value y).mp hsr).1)⟩)

theorem diff_spec {s₁ s₂ : tree X} (h₁ : bst s₁) (h₂ : bst s₂) (y : X.t) :
    In y (diff s₁ s₂) ↔ In y s₁ ∧ ¬ In y s₂ :=
  (diff_spec_bst h₁ s₂ h₂).2 y

theorem diff_bst {s₁ s₂ : tree X} (h₁ : bst s₁) (h₂ : bst s₂) :
    bst (diff s₁ s₂) :=
  (diff_spec_bst h₁ s₂ h₂).1

theorem filter_weak_spec (s : tree X) (f : X.t → Bool) (x : X.t) :
    In x (filter f s) → In x s := by
  induction s with
  | Leaf => simp [filter, In, CompCert4Lean.Lib.MSetGenTree.tree.In]
  | Node info left value right ihl ihr =>
      simp only [filter]
      by_cases hf : f value = true
      · rw [if_pos hf, join_spec]
        simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
        intro hx
        rcases hx with hx | hx | hx
        · exact Or.inl hx
        · exact Or.inr (Or.inl (ihl hx))
        · exact Or.inr (Or.inr (ihr hx))
      · rw [if_neg hf, concat_spec]
        simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
        intro hx
        rcases hx with hx | hx
        · exact Or.inr (Or.inl (ihl hx))
        · exact Or.inr (Or.inr (ihr hx))

theorem filter_spec (s : tree X) (f : X.t → Bool)
    (hf : CompCert4Lean.Lib.MSetGenTree.tree.RespectsEq f) (x : X.t) :
    In x (filter f s) ↔ In x s ∧ f x = true := by
  induction s with
  | Leaf => simp [filter, In, CompCert4Lean.Lib.MSetGenTree.tree.In]
  | Node info left value right ihl ihr =>
      simp only [filter]
      by_cases hv : f value = true
      · rw [if_pos hv, join_spec, ihl, ihr]
        simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
        constructor
        · intro hx
          rcases hx with hx | ⟨hx, hfx⟩ | ⟨hx, hfx⟩
          · exact ⟨Or.inl hx, by simpa [hf x value hx] using hv⟩
          · exact ⟨Or.inr (Or.inl hx), hfx⟩
          · exact ⟨Or.inr (Or.inr hx), hfx⟩
        · rintro ⟨hx, hfx⟩
          rcases hx with hx | hx | hx
          · exact Or.inl hx
          · exact Or.inr (Or.inl ⟨hx, hfx⟩)
          · exact Or.inr (Or.inr ⟨hx, hfx⟩)
      · rw [if_neg hv, concat_spec, ihl, ihr]
        simp only [In, CompCert4Lean.Lib.MSetGenTree.tree.in_node]
        constructor
        · intro hx
          rcases hx with ⟨hx, hfx⟩ | ⟨hx, hfx⟩
          · exact ⟨Or.inr (Or.inl hx), hfx⟩
          · exact ⟨Or.inr (Or.inr hx), hfx⟩
        · rintro ⟨hx, hfx⟩
          rcases hx with hx | hx | hx
          · exact False.elim (hv (by simpa [hf x value hx] using hfx))
          · exact Or.inl ⟨hx, hfx⟩
          · exact Or.inr ⟨hx, hfx⟩

theorem filter_bst {s : tree X} (hs : bst s) (f : X.t → Bool) :
    bst (filter f s) := by
  induction hs with
  | BSLeaf => exact .BSLeaf
  | BSNode info value left right hleft hright hlt hgt ihl ihr =>
      simp only [filter]
      have hlt' : lt_tree value (filter f left) :=
        fun y hy => hlt y (filter_weak_spec left f y hy)
      have hgt' : gt_tree value (filter f right) :=
        fun y hy => hgt y (filter_weak_spec right f y hy)
      by_cases hv : f value = true
      · rw [if_pos hv]
        exact join_bst _ _ _ ihl ihr hlt' hgt'
      · rw [if_neg hv]
        apply concat_bst _ _ ihl ihr
        intro y₁ y₂ hy₁ hy₂
        exact X.lt_trans y₁ value y₂ (hlt' y₁ hy₁) (hgt' y₂ hy₂)

theorem partition_fst (s : tree X) (f : X.t → Bool) :
    (partition f s).1 = filter f s := by
  induction s with
  | Leaf => rfl
  | Node info left value right ihl ihr =>
      simp only [partition, filter]
      generalize hl : partition f left = leftParts
      generalize hr : partition f right = rightParts
      cases leftParts with
      | mk leftTrue leftFalse =>
          cases rightParts with
          | mk rightTrue rightFalse =>
              have ihl' := ihl
              have ihr' := ihr
              rw [hl] at ihl'
              rw [hr] at ihr'
              simp only [Prod.fst] at ihl' ihr' ⊢
              rw [ihl', ihr']
              cases f value <;> rfl

theorem partition_snd (s : tree X) (f : X.t → Bool) :
    (partition f s).2 = filter (fun x => !(f x)) s := by
  induction s with
  | Leaf => rfl
  | Node info left value right ihl ihr =>
      simp only [partition, filter]
      generalize hl : partition f left = leftParts
      generalize hr : partition f right = rightParts
      cases leftParts with
      | mk leftTrue leftFalse =>
          cases rightParts with
          | mk rightTrue rightFalse =>
              have ihl' := ihl
              have ihr' := ihr
              rw [hl] at ihl'
              rw [hr] at ihr'
              simp only [Prod.snd] at ihl' ihr' ⊢
              rw [ihl', ihr']
              by_cases hv : f value = true
              · simp [hv]
              · have hvf : f value = false := by
                  cases hval : f value with
                  | false => rfl
                  | true => exact False.elim (hv hval)
                simp [hvf]

theorem partition_bst {s : tree X} (hs : bst s) (f : X.t → Bool) :
    bst (partition f s).1 ∧ bst (partition f s).2 := by
  rw [partition_fst, partition_snd]
  exact ⟨filter_bst hs f, filter_bst hs (fun x => !(f x))⟩

/-! ## Generic `MSetGenTree.Props` surface included by `MakeRaw` -/

theorem ltb_tree_iff (x : X.t) (s : tree X) :
    lt_tree x s ↔ ltb_tree x s = true :=
  CompCert4Lean.Lib.MSetGenTree.tree.ltb_tree_iff x s

theorem gtb_tree_iff (x : X.t) (s : tree X) :
    gt_tree x s ↔ gtb_tree x s = true :=
  CompCert4Lean.Lib.MSetGenTree.tree.gtb_tree_iff x s

theorem isok_iff (s : tree X) : bst s ↔ isok s = true :=
  CompCert4Lean.Lib.MSetGenTree.tree.isok_iff s

theorem In_1 (s : tree X) (x y : X.t) (hxy : X.eq x y) :
    InT x s → InT y s :=
  CompCert4Lean.Lib.MSetGenTree.tree.In_1 s x y hxy

theorem In_node_iff
    (h : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (left : tree X) (x : X.t) (right : tree X) (y : X.t) :
    InT y (.Node h left x right) ↔
      InT y left ∨ X.eq y x ∨ InT y right :=
  CompCert4Lean.Lib.MSetGenTree.tree.In_node_iff h left x right y

theorem In_leaf_iff (x : X.t) : InT x (.Leaf : tree X) ↔ False :=
  CompCert4Lean.Lib.MSetGenTree.tree.In_leaf_iff x

theorem lt_leaf (x : X.t) : lt_tree x (.Leaf : tree X) :=
  CompCert4Lean.Lib.MSetGenTree.tree.lt_leaf x

theorem gt_leaf (x : X.t) : gt_tree x (.Leaf : tree X) :=
  CompCert4Lean.Lib.MSetGenTree.tree.gt_leaf x

theorem lt_tree_node (x y : X.t) (left right : tree X)
    (h : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (hl : lt_tree x left) (hr : lt_tree x right) (hy : X.lt y x) :
    lt_tree x (.Node h left y right) :=
  CompCert4Lean.Lib.MSetGenTree.tree.lt_tree_node hl hr hy

theorem gt_tree_node (x y : X.t) (left right : tree X)
    (h : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (hl : gt_tree x left) (hr : gt_tree x right) (hy : X.lt x y) :
    gt_tree x (.Node h left y right) :=
  CompCert4Lean.Lib.MSetGenTree.tree.gt_tree_node hl hr hy

theorem lt_tree_not_in (x : X.t) (s : tree X)
    (h : lt_tree x s) : ¬ InT x s :=
  CompCert4Lean.Lib.MSetGenTree.tree.lt_tree_not_in h

theorem gt_tree_not_in (x : X.t) (s : tree X)
    (h : gt_tree x s) : ¬ InT x s :=
  CompCert4Lean.Lib.MSetGenTree.tree.gt_tree_not_in h

theorem lt_tree_trans (x y : X.t) (hxy : X.lt x y) (s : tree X)
    (h : lt_tree x s) : lt_tree y s :=
  CompCert4Lean.Lib.MSetGenTree.tree.lt_tree_trans hxy h

theorem gt_tree_trans (x y : X.t) (hyx : X.lt y x) (s : tree X)
    (h : gt_tree x s) : gt_tree y s :=
  CompCert4Lean.Lib.MSetGenTree.tree.gt_tree_trans hyx h

theorem empty_spec : Empty (empty : tree X) :=
  CompCert4Lean.Lib.MSetGenTree.tree.empty_spec

theorem empty_ok : bst (empty : tree X) :=
  CompCert4Lean.Lib.MSetGenTree.tree.empty_ok

theorem is_empty_spec (s : tree X) :
    is_empty s = true ↔ Empty s :=
  CompCert4Lean.Lib.MSetGenTree.tree.is_empty_spec s

theorem mem_spec (s : tree X) (x : X.t) (hs : bst s) :
    mem x s = true ↔ InT x s :=
  CompCert4Lean.Lib.MSetGenTree.tree.mem_spec hs x

theorem min_elt_spec1 (s : tree X) (x : X.t)
    (h : min_elt s = some x) : InT x s :=
  CompCert4Lean.Lib.MSetGenTree.tree.min_elt_spec1 h

theorem min_elt_spec2 (s : tree X) (x y : X.t) (hs : bst s)
    (hmin : min_elt s = some x) (hy : InT y s) : ¬ X.lt y x :=
  CompCert4Lean.Lib.MSetGenTree.tree.min_elt_spec2 hs hmin hy

theorem min_elt_spec3 (s : tree X)
    (h : min_elt s = none) : Empty s :=
  CompCert4Lean.Lib.MSetGenTree.tree.min_elt_spec3 h

theorem max_elt_spec1 (s : tree X) (x : X.t)
    (h : max_elt s = some x) : InT x s :=
  CompCert4Lean.Lib.MSetGenTree.tree.max_elt_spec1 h

theorem max_elt_spec2 (s : tree X) (x y : X.t) (hs : bst s)
    (hmax : max_elt s = some x) (hy : InT y s) : ¬ X.lt x y :=
  CompCert4Lean.Lib.MSetGenTree.tree.max_elt_spec2 hs hmax hy

theorem max_elt_spec3 (s : tree X)
    (h : max_elt s = none) : Empty s :=
  CompCert4Lean.Lib.MSetGenTree.tree.max_elt_spec3 h

theorem choose_spec1 (s : tree X) (x : X.t)
    (h : choose s = some x) : InT x s :=
  CompCert4Lean.Lib.MSetGenTree.tree.choose_spec1 h

theorem choose_spec2 (s : tree X)
    (h : choose s = none) : Empty s :=
  CompCert4Lean.Lib.MSetGenTree.tree.choose_spec2 h

theorem choose_spec3 (s s' : tree X) (x x' : X.t)
    (hs : bst s) (hs' : bst s')
    (hx : choose s = some x) (hx' : choose s' = some x')
    (heq : Equal s s') : X.eq x x' :=
  CompCert4Lean.Lib.MSetGenTree.tree.choose_spec3 hs hs' hx hx' heq

theorem elements_spec1' (s : tree X) (acc : List X.t) (x : X.t) :
    InA x (elements_aux acc s) ↔ InT x s ∨ InA x acc :=
  CompCert4Lean.Lib.MSetGenTree.tree.elements_spec1' s acc x

theorem elements_spec1 (s : tree X) (x : X.t) :
    InA x (elements s) ↔ InT x s :=
  CompCert4Lean.Lib.MSetGenTree.tree.elements_spec1 s x

theorem elements_spec2' (s : tree X) (acc : List X.t) (hs : bst s)
    (hacc : Sorted acc)
    (hcross : ∀ x y, InA x acc → InT y s → X.lt y x) :
    Sorted (elements_aux acc s) :=
  CompCert4Lean.Lib.MSetGenTree.tree.elements_spec2' s acc hs hacc hcross

theorem elements_spec2 (s : tree X) (hs : bst s) :
    Sorted (elements s) :=
  CompCert4Lean.Lib.MSetGenTree.tree.elements_spec2 s hs

theorem elements_spec2w (s : tree X) (hs : bst s) :
    NoDupA (elements s) :=
  CompCert4Lean.Lib.MSetGenTree.tree.elements_spec2w s hs

theorem elements_aux_cardinal (s : tree X) (acc : List X.t) :
    acc.length + cardinal s = (elements_aux acc s).length :=
  CompCert4Lean.Lib.MSetGenTree.tree.elements_aux_cardinal s acc

theorem elements_cardinal (s : tree X) :
    cardinal s = (elements s).length :=
  CompCert4Lean.Lib.MSetGenTree.tree.elements_cardinal s

theorem cardinal_spec (s : tree X) (hs : bst s) :
    cardinal s = (elements s).length :=
  CompCert4Lean.Lib.MSetGenTree.tree.cardinal_spec s hs

theorem elements_app (s : tree X) (acc : List X.t) :
    elements_aux acc s = elements s ++ acc :=
  CompCert4Lean.Lib.MSetGenTree.tree.elements_app s acc

theorem elements_node
    (h : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (left : tree X) (x : X.t) (right : tree X) :
    elements (.Node h left x right) = elements left ++ x :: elements right :=
  CompCert4Lean.Lib.MSetGenTree.tree.elements_node h left right x

theorem rev_elements_app (s : tree X) (acc : List X.t) :
    rev_elements_aux acc s = rev_elements s ++ acc :=
  CompCert4Lean.Lib.MSetGenTree.tree.rev_elements_app s acc

theorem rev_elements_node
    (h : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (left : tree X) (x : X.t) (right : tree X) :
    rev_elements (.Node h left x right) =
      rev_elements right ++ x :: rev_elements left :=
  CompCert4Lean.Lib.MSetGenTree.tree.rev_elements_node h left right x

theorem rev_elements_rev (s : tree X) :
    rev_elements s = (elements s).reverse :=
  CompCert4Lean.Lib.MSetGenTree.tree.rev_elements_rev s

theorem sorted_app_inv (l₁ l₂ : List X.t)
    (h : Sorted (l₁ ++ l₂)) :
    Sorted l₁ ∧ Sorted l₂ ∧
      ∀ x₁ x₂, InA x₁ l₁ → InA x₂ l₂ → X.lt x₁ x₂ :=
  CompCert4Lean.Lib.MSetGenTree.tree.sorted_app_inv l₁ l₂ h

theorem elements_sort_ok (s : tree X)
    (h : Sorted (elements s)) : bst s :=
  CompCert4Lean.Lib.MSetGenTree.tree.elements_sort_ok s h

theorem for_all_spec (s : tree X) (f : X.t → Bool)
    (hf : RespectsEq f) :
    for_all f s = true ↔ For_all (fun x => f x = true) s :=
  CompCert4Lean.Lib.MSetGenTree.tree.for_all_spec s f hf

theorem exists_spec (s : tree X) (f : X.t → Bool)
    (hf : RespectsEq f) :
    exists_ f s = true ↔ Exists (fun x => f x = true) s :=
  CompCert4Lean.Lib.MSetGenTree.tree.exists_spec s f hf

theorem fold_spec' {A : Type} (f : X.t → A → A) (s : tree X)
    (base : A) (acc : List X.t) :
    List.foldl (fun state x => f x state) base (elements_aux acc s) =
      List.foldl (fun state x => f x state) (fold f s base) acc :=
  CompCert4Lean.Lib.MSetGenTree.tree.fold_spec' f s base acc

theorem fold_spec (s : tree X) {A : Type} (base : A)
    (f : X.t → A → A) :
    fold f s base = List.foldl (fun state x => f x state) base (elements s) :=
  CompCert4Lean.Lib.MSetGenTree.tree.fold_spec s base f

theorem subsetl_spec (subsetLeft : tree X → Bool)
    (left₁ : tree X) (x₁ : X.t)
    (h₁ : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (s₂ : tree X) (hleft : bst (.Node h₁ left₁ x₁ .Leaf))
    (h₂ : bst s₂)
    (hsubset : ∀ s, bst s → (subsetLeft s = true ↔ Subset left₁ s)) :
    subsetl subsetLeft x₁ s₂ = true ↔
      Subset (.Node h₁ left₁ x₁ .Leaf) s₂ :=
  CompCert4Lean.Lib.MSetGenTree.tree.subsetl_spec
    subsetLeft left₁ x₁ h₁ s₂ hleft h₂ hsubset

theorem subsetr_spec (subsetRight : tree X → Bool)
    (right₁ : tree X) (x₁ : X.t)
    (h₁ : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (s₂ : tree X) (hright : bst (.Node h₁ .Leaf x₁ right₁))
    (h₂ : bst s₂)
    (hsubset : ∀ s, bst s → (subsetRight s = true ↔ Subset right₁ s)) :
    subsetr subsetRight x₁ s₂ = true ↔
      Subset (.Node h₁ .Leaf x₁ right₁) s₂ :=
  CompCert4Lean.Lib.MSetGenTree.tree.subsetr_spec
    subsetRight right₁ x₁ h₁ s₂ hright h₂ hsubset

theorem subset_spec (s₁ s₂ : tree X) (h₁ : bst s₁) (h₂ : bst s₂) :
    subset s₁ s₂ = true ↔ Subset s₁ s₂ :=
  CompCert4Lean.Lib.MSetGenTree.tree.subset_spec s₁ s₂ h₁ h₂

theorem eq_Leq (s₁ s₂ : tree X) :
    eq s₁ s₂ ↔ L.eq (elements s₁) (elements s₂) :=
  CompCert4Lean.Lib.MSetGenTree.tree.eq_Leq s₁ s₂

def eq_equiv : Equivalence (@eq X) :=
  CompCert4Lean.Lib.MSetGenTree.tree.eq_equiv

instance lt_strorder :
    CompCert4Lean.Lib.MSetGenTree.StrictOrder (@lt X) :=
  CompCert4Lean.Lib.MSetGenTree.tree.lt_strorder

theorem lt_compat {s₁ s₂ s₃ s₄ : tree X}
    (heq₁₂ : eq s₁ s₂) (heq₃₄ : eq s₃ s₄) :
    lt s₁ s₃ ↔ lt s₂ s₄ :=
  CompCert4Lean.Lib.MSetGenTree.tree.lt_compat heq₁₂ heq₃₄

theorem flatten_e_elements (left : tree X) (x : X.t) (right : tree X)
    (h : _root_.CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (e : enumeration (X := X)) :
    elements left ++ flatten_e (.More x right e) =
      elements (.Node h left x right) ++ flatten_e e :=
  CompCert4Lean.Lib.MSetGenTree.tree.flatten_e_elements left x right h e

theorem cons_1 (s : tree X) (e : enumeration (X := X)) :
    flatten_e (cons s e) = elements s ++ flatten_e e :=
  CompCert4Lean.Lib.MSetGenTree.tree.cons_1 s e

theorem compare_end_Cmp (e₂ : enumeration (X := X)) :
    Cmp (compare_end e₂) [] (flatten_e e₂) :=
  CompCert4Lean.Lib.MSetGenTree.tree.compare_end_Cmp e₂

theorem compare_more_Cmp (x₁ : X.t)
    (cont : enumeration (X := X) → comparison) (x₂ : X.t)
    (right₂ : tree X) (e₂ : enumeration (X := X)) (l : List X.t)
    (h : Cmp (cont (cons right₂ e₂)) l
      (elements right₂ ++ flatten_e e₂)) :
    Cmp (compare_more x₁ cont (.More x₂ right₂ e₂))
      (x₁ :: l) (flatten_e (.More x₂ right₂ e₂)) :=
  CompCert4Lean.Lib.MSetGenTree.tree.compare_more_Cmp
    x₁ cont x₂ right₂ e₂ l h

theorem compare_cont_Cmp (s₁ : tree X)
    (cont : enumeration (X := X) → comparison)
    (e₂ : enumeration (X := X)) (l : List X.t)
    (hcont : ∀ e, Cmp (cont e) l (flatten_e e)) :
    Cmp (compare_cont s₁ cont e₂) (elements s₁ ++ l) (flatten_e e₂) :=
  CompCert4Lean.Lib.MSetGenTree.tree.compare_cont_Cmp s₁ cont e₂ l hcont

theorem compare_Cmp (s₁ s₂ : tree X) :
    Cmp (compare s₁ s₂) (elements s₁) (elements s₂) :=
  CompCert4Lean.Lib.MSetGenTree.tree.compare_Cmp s₁ s₂

theorem compare_spec (s₁ s₂ : tree X) (h₁ : bst s₁) (h₂ : bst s₂) :
    CompSpec eq lt s₁ s₂ (compare s₁ s₂) :=
  CompCert4Lean.Lib.MSetGenTree.tree.compare_spec s₁ s₂ h₁ h₂

theorem equal_spec (s₁ s₂ : tree X) (h₁ : bst s₁) (h₂ : bst s₂) :
    equal s₁ s₂ = true ↔ eq s₁ s₂ :=
  CompCert4Lean.Lib.MSetGenTree.tree.equal_spec s₁ s₂ h₁ h₂

theorem mindepth_maxdepth (s : tree X) : mindepth s ≤ maxdepth s :=
  CompCert4Lean.Lib.MSetGenTree.tree.mindepth_maxdepth s

theorem maxdepth_cardinal (s : tree X) : cardinal s < 2 ^ maxdepth s :=
  CompCert4Lean.Lib.MSetGenTree.tree.maxdepth_cardinal s

theorem mindepth_cardinal (s : tree X) :
    2 ^ mindepth s ≤ Nat.succ (cardinal s) :=
  CompCert4Lean.Lib.MSetGenTree.tree.mindepth_cardinal s

theorem maxdepth_log_cardinal (s : tree X) (hne : s ≠ .Leaf) :
    Nat.log2 (cardinal s) < maxdepth s :=
  CompCert4Lean.Lib.MSetGenTree.tree.maxdepth_log_cardinal s hne

theorem mindepth_log_cardinal (s : tree X) :
    mindepth s ≤ Nat.log2 (Nat.succ (cardinal s)) :=
  CompCert4Lean.Lib.MSetGenTree.tree.mindepth_log_cardinal s

end CompCert4Lean.Lib.MSetAVL
