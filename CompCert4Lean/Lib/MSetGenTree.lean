import CompCert4Lean.Foundation.Ordered

/-!
# Generic ordered-set trees

Definition-bearing translation of Rocq's `MSetGenTree`.  The tree is indexed
by the complete ordered-type record as well as by its node-information type;
consequently two distinct order structures never share a tree type.
-/

namespace CompCert4Lean.Lib.MSetGenTree

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

abbrev OrderedType :=
  CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.OrderedType
abbrev elt (X : OrderedType) := X.t
abbrev InA {A : Type} (eqA : A → A → Prop) (x : A) (l : List A) :=
  CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA eqA x l
abbrev NoDupA {A : Type} (eqA : A → A → Prop) (l : List A) :=
  CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.NoDupA eqA l
abbrev Sorted {A : Type} (R : A → A → Prop) (l : List A) :=
  CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Sorted.Sorted R l
abbrev HdRel {A : Type} (R : A → A → Prop) (x : A) (l : List A) :=
  CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Sorted.HdRel R x l

inductive CompareSpec (Peq Plt Pgt : Prop) : comparison → Prop where
  | CompEq : Peq → CompareSpec Peq Plt Pgt .Eq
  | CompLt : Plt → CompareSpec Peq Plt Pgt .Lt
  | CompGt : Pgt → CompareSpec Peq Plt Pgt .Gt

abbrev CompSpec {A : Type} (eq lt : A → A → Prop) (x y : A) :
    comparison → Prop :=
  CompareSpec (eq x y) (lt x y) (lt y x)

class StrictOrder {A : Type} (r : A → A → Prop) : Prop where
  irrefl : ∀ x, ¬ r x x
  trans : ∀ {x y z}, r x y → r y z → r x z

inductive tree (X : OrderedType) (Info : Type) : Type where
  | Leaf
  | Node (info : Info) (left : tree X Info) (value : X.t)
      (right : tree X Info)

namespace tree

variable {X : OrderedType} {Info : Type}

abbrev empty : tree X Info := .Leaf

def is_empty : tree X Info → Bool
  | .Leaf => true
  | .Node _ _ _ _ => false

def mem (x : X.t) : tree X Info → Bool
  | .Leaf => false
  | .Node _ left value right =>
      match X.compare x value with
      | .lt _ => mem x left
      | .eq _ => true
      | .gt _ => mem x right

def min_elt : tree X Info → Option X.t
  | .Leaf => none
  | .Node _ .Leaf value _ => some value
  | .Node _ left value right => min_elt left

def max_elt : tree X Info → Option X.t
  | .Leaf => none
  | .Node _ _ value .Leaf => some value
  | .Node _ left value right => max_elt right

abbrev choose (s : tree X Info) : Option X.t := min_elt s

def fold {A : Type} (f : X.t → A → A) : tree X Info → A → A
  | .Leaf, base => base
  | .Node _ left value right, base =>
      fold f right (f value (fold f left base))

def elements_aux : List X.t → tree X Info → List X.t
  | acc, .Leaf => acc
  | acc, .Node _ left value right =>
      elements_aux (value :: elements_aux acc right) left

def elements (s : tree X Info) : List X.t := elements_aux [] s

def rev_elements_aux : List X.t → tree X Info → List X.t
  | acc, .Leaf => acc
  | acc, .Node _ left value right =>
      rev_elements_aux (value :: rev_elements_aux acc left) right

def rev_elements (s : tree X Info) : List X.t := rev_elements_aux [] s

def cardinal : tree X Info → Nat
  | .Leaf => 0
  | .Node _ left _ right => Nat.succ (cardinal left + cardinal right)

def maxdepth : tree X Info → Nat
  | .Leaf => 0
  | .Node _ left _ right => Nat.succ (Nat.max (maxdepth left) (maxdepth right))

def mindepth : tree X Info → Nat
  | .Leaf => 0
  | .Node _ left _ right => Nat.succ (Nat.min (mindepth left) (mindepth right))

def for_all (f : X.t → Bool) : tree X Info → Bool
  | .Leaf => true
  | .Node _ left value right =>
      f value && for_all f left && for_all f right

def exists_ (f : X.t → Bool) : tree X Info → Bool
  | .Leaf => false
  | .Node _ left value right =>
      f value || exists_ f left || exists_ f right

inductive enumeration (X : OrderedType) (Info : Type) : Type where
  | End
  | More (value : X.t) (restTree : tree X Info)
      (rest : enumeration X Info)

def cons : tree X Info → enumeration X Info → enumeration X Info
  | .Leaf, e => e
  | .Node _ left value right, e => cons left (.More value right e)

def compare_more (x₁ : X.t)
    (cont : enumeration X Info → comparison) :
    enumeration X Info → comparison
  | .End => .Gt
  | .More x₂ right₂ e₂ =>
      match X.compare x₁ x₂ with
      | .eq _ => cont (cons right₂ e₂)
      | .lt _ => .Lt
      | .gt _ => .Gt

def compare_cont (s₁ : tree X Info)
    (cont : enumeration X Info → comparison)
    (e₂ : enumeration X Info) : comparison :=
  match s₁ with
  | .Leaf => cont e₂
  | .Node _ left₁ x₁ right₁ =>
      compare_cont left₁ (compare_more x₁ (compare_cont right₁ cont)) e₂

def compare_end : enumeration X Info → comparison
  | .End => .Eq
  | .More _ _ _ => .Lt

def compare (s₁ s₂ : tree X Info) : comparison :=
  compare_cont s₁ compare_end (cons s₂ .End)

def equal (s₁ s₂ : tree X Info) : Bool :=
  match compare s₁ s₂ with
  | .Eq => true
  | _ => false

def subsetl (subsetLeft : tree X Info → Bool) (x₁ : X.t) :
    tree X Info → Bool
  | .Leaf => false
  | s₂@(.Node _ left₂ x₂ right₂) =>
      match X.compare x₁ x₂ with
      | .eq _ => subsetLeft left₂
      | .lt _ => subsetl subsetLeft x₁ left₂
      | .gt _ => mem x₁ right₂ && subsetLeft s₂

def subsetr (subsetRight : tree X Info → Bool) (x₁ : X.t) :
    tree X Info → Bool
  | .Leaf => false
  | s₂@(.Node _ left₂ x₂ right₂) =>
      match X.compare x₁ x₂ with
      | .eq _ => subsetRight right₂
      | .lt _ => mem x₁ left₂ && subsetRight s₂
      | .gt _ => subsetr subsetRight x₁ right₂

def subset : tree X Info → tree X Info → Bool
  | .Leaf, _ => true
  | .Node _ _ _ _, .Leaf => false
  | s₁@(.Node _ left₁ x₁ right₁), s₂@(.Node _ left₂ x₂ right₂) =>
      match X.compare x₁ x₂ with
      | .eq _ => subset left₁ left₂ && subset right₁ right₂
      | .lt _ => subsetl (subset left₁) x₁ left₂ && subset right₁ s₂
      | .gt _ => subsetr (subset right₁) x₁ right₂ && subset left₁ s₂

inductive InT (x : X.t) : tree X Info → Prop where
  | IsRoot (info : Info) (left right : tree X Info) (value : X.t) :
      X.eq x value → InT x (.Node info left value right)
  | InLeft (info : Info) (left right : tree X Info) (value : X.t) :
      InT x left → InT x (.Node info left value right)
  | InRight (info : Info) (left right : tree X Info) (value : X.t) :
      InT x right → InT x (.Node info left value right)

abbrev In (x : X.t) (s : tree X Info) : Prop := InT x s

def Equal (s s' : tree X Info) : Prop :=
  ∀ a, In a s ↔ In a s'

def Subset (s s' : tree X Info) : Prop :=
  ∀ a, In a s → In a s'

def Empty (s : tree X Info) : Prop :=
  ∀ a, ¬ In a s

def For_all (P : X.t → Prop) (s : tree X Info) : Prop :=
  ∀ x, In x s → P x

def Exists (P : X.t → Prop) (s : tree X Info) : Prop :=
  ∃ x, In x s ∧ P x

def lt_tree (x : X.t) (s : tree X Info) : Prop :=
  ∀ y, In y s → X.lt y x

def gt_tree (x : X.t) (s : tree X Info) : Prop :=
  ∀ y, In y s → X.lt x y

inductive bst : tree X Info → Prop where
  | BSLeaf : bst .Leaf
  | BSNode (info : Info) (x : X.t) (left right : tree X Info) :
      bst left → bst right → lt_tree x left → gt_tree x right →
      bst (.Node info left x right)

abbrev IsOk (s : tree X Info) : Prop := bst s

def ltb_tree (x : X.t) : tree X Info → Bool
  | .Leaf => true
  | .Node _ left y right =>
      match X.compare x y with
      | .gt _ => ltb_tree x left && ltb_tree x right
      | _ => false

def gtb_tree (x : X.t) : tree X Info → Bool
  | .Leaf => true
  | .Node _ left y right =>
      match X.compare x y with
      | .lt _ => gtb_tree x left && gtb_tree x right
      | _ => false

def isok : tree X Info → Bool
  | .Leaf => true
  | .Node _ left x right =>
      isok left && isok right && ltb_tree x left && gtb_tree x right

theorem bst_node_inv {info : Info} {left right : tree X Info} {x : X.t}
    (h : bst (.Node info left x right)) :
    bst left ∧ bst right ∧ lt_tree x left ∧ gt_tree x right := by
  cases h with
  | BSNode _ _ _ _ hl hr hlt hgt => exact ⟨hl, hr, hlt, hgt⟩

theorem eq_symm {x y : X.t} (h : X.eq x y) : X.eq y x :=
  X.eq_sym x y h

theorem lt_irrefl (x : X.t) : ¬ X.lt x x := by
  intro h
  exact X.lt_not_eq x x h (X.eq_refl x)

theorem lt_asymm {x y : X.t} (hxy : X.lt x y) : ¬ X.lt y x := by
  intro hyx
  exact lt_irrefl x (X.lt_trans x y x hxy hyx)

theorem lt_of_eq_of_lt {x y z : X.t}
    (hxy : X.eq x y) (hxz : X.lt x z) : X.lt y z := by
  cases X.compare y z with
  | lt h => exact h
  | eq h =>
      exact False.elim (X.lt_not_eq x z hxz (X.eq_trans x y z hxy h))
  | gt h =>
      exact False.elim
        (X.lt_not_eq x y (X.lt_trans x z y hxz h) hxy)

theorem lt_of_lt_of_eq {x y z : X.t}
    (hxy : X.lt x y) (hyz : X.eq y z) : X.lt x z := by
  cases X.compare x z with
  | lt h => exact h
  | eq h =>
      have hxz : X.eq x z := h
      have hxy' : X.eq x y := X.eq_trans x z y hxz (X.eq_sym y z hyz)
      exact False.elim (X.lt_not_eq x y hxy hxy')
  | gt h =>
      have hyx : X.lt y x := lt_of_eq_of_lt (X.eq_sym y z hyz) h
      exact False.elim (lt_asymm hxy hyx)

theorem in_of_eq {x y : X.t} (hxy : X.eq x y) :
    ∀ {s : tree X Info}, In x s → In y s := by
  intro s h
  induction h with
  | IsRoot info left right value hroot =>
      exact .IsRoot info left right value
        (X.eq_trans y x value (X.eq_sym x y hxy) hroot)
  | InLeft info left right value _ ih => exact .InLeft info left right value ih
  | InRight info left right value _ ih => exact .InRight info left right value ih

theorem In_1 (s : tree X Info) (x y : X.t) (hxy : X.eq x y) :
    InT x s → InT y s :=
  in_of_eq hxy

theorem in_compat {x y : X.t} (hxy : X.eq x y) (s : tree X Info) :
    In x s ↔ In y s := by
  constructor
  · exact in_of_eq hxy
  · exact in_of_eq (X.eq_sym x y hxy)

@[simp] theorem in_leaf (x : X.t) : ¬ In x (.Leaf : tree X Info) := by
  intro h
  cases h

@[simp] theorem in_node {info : Info} {left right : tree X Info}
    {value x : X.t} :
    In x (.Node info left value right) ↔
      X.eq x value ∨ In x left ∨ In x right := by
  constructor
  · intro h
    cases h with
    | IsRoot _ _ _ _ hroot => exact Or.inl hroot
    | InLeft _ _ _ _ hleft => exact Or.inr (Or.inl hleft)
    | InRight _ _ _ _ hright => exact Or.inr (Or.inr hright)
  · rintro (hroot | hleft | hright)
    · exact .IsRoot info left right value hroot
    · exact .InLeft info left right value hleft
    · exact .InRight info left right value hright

theorem In_node_iff (info : Info) (left : tree X Info) (value : X.t)
    (right : tree X Info) (x : X.t) :
    InT x (.Node info left value right) ↔
      InT x left ∨ X.eq x value ∨ InT x right := by
  constructor
  · intro h
    cases h with
    | IsRoot _ _ _ _ hroot => exact Or.inr (Or.inl hroot)
    | InLeft _ _ _ _ hleft => exact Or.inl hleft
    | InRight _ _ _ _ hright => exact Or.inr (Or.inr hright)
  · rintro (hleft | hroot | hright)
    · exact .InLeft info left right value hleft
    · exact .IsRoot info left right value hroot
    · exact .InRight info left right value hright

theorem In_leaf_iff (x : X.t) : InT x (.Leaf : tree X Info) ↔ False := by
  constructor
  · intro h; cases h
  · exact False.elim

theorem lt_leaf (x : X.t) : lt_tree x (.Leaf : tree X Info) := by
  intro y h
  cases h

theorem gt_leaf (x : X.t) : gt_tree x (.Leaf : tree X Info) := by
  intro y h
  cases h

theorem lt_tree_node {x y : X.t} {info : Info} {left right : tree X Info}
    (hl : lt_tree x left) (hr : lt_tree x right) (hy : X.lt y x) :
    lt_tree x (.Node info left y right) := by
  intro z hz
  cases hz with
  | IsRoot _ _ _ _ hzy => exact lt_of_eq_of_lt (X.eq_sym z y hzy) hy
  | InLeft _ _ _ _ hzl => exact hl z hzl
  | InRight _ _ _ _ hzr => exact hr z hzr

theorem gt_tree_node {x y : X.t} {info : Info} {left right : tree X Info}
    (hl : gt_tree x left) (hr : gt_tree x right) (hy : X.lt x y) :
    gt_tree x (.Node info left y right) := by
  intro z hz
  cases hz with
  | IsRoot _ _ _ _ hzy => exact lt_of_lt_of_eq hy (X.eq_sym z y hzy)
  | InLeft _ _ _ _ hzl => exact hl z hzl
  | InRight _ _ _ _ hzr => exact hr z hzr

theorem lt_tree_not_in {x : X.t} {s : tree X Info}
    (h : lt_tree x s) : ¬ In x s := by
  intro hx
  exact lt_irrefl x (h x hx)

theorem gt_tree_not_in {x : X.t} {s : tree X Info}
    (h : gt_tree x s) : ¬ In x s := by
  intro hx
  exact lt_irrefl x (h x hx)

theorem lt_tree_trans {x y : X.t} (hxy : X.lt x y) {s : tree X Info}
    (h : lt_tree x s) : lt_tree y s := by
  intro z hz
  exact X.lt_trans z x y (h z hz) hxy

theorem gt_tree_trans {x y : X.t} (hyx : X.lt y x) {s : tree X Info}
    (h : gt_tree x s) : gt_tree y s := by
  intro z hz
  exact X.lt_trans y x z hyx (h z hz)

theorem empty_spec : Empty (empty : tree X Info) := by
  intro x h
  cases h

theorem empty_ok : bst (empty : tree X Info) :=
  .BSLeaf

theorem is_empty_spec (s : tree X Info) :
    is_empty s = true ↔ Empty s := by
  cases s with
  | Leaf => simp [is_empty, Empty, in_leaf]
  | Node info left value right =>
      constructor
      · intro h
        cases h
      · intro h
        exact False.elim
          (h value (.IsRoot info left right value (X.eq_refl value)))

theorem mem_spec {s : tree X Info} (hs : bst s) (x : X.t) :
    mem x s = true ↔ In x s := by
  induction hs with
  | BSLeaf => simp [mem, in_leaf]
  | BSNode info value left right hl hr hlt hgt ihl ihr =>
      simp only [mem]
      cases hcmp : X.compare x value with
      | lt hx =>
          rw [ihl, in_node]
          constructor
          · exact fun h => Or.inr (Or.inl h)
          · intro h
            rcases h with heq | hleft | hright
            · exact False.elim (X.lt_not_eq x value hx heq)
            · exact hleft
            · exact False.elim (lt_asymm hx (hgt x hright))
      | eq heq => simp [in_node, heq]
      | gt hx =>
          rw [ihr, in_node]
          constructor
          · exact fun h => Or.inr (Or.inr h)
          · intro h
            rcases h with heq | hleft | hright
            · exact False.elim
                (X.lt_not_eq value x hx (X.eq_sym x value heq))
            · exact False.elim (lt_asymm (hlt x hleft) hx)
            · exact hright

def mem_dec {s : tree X Info} (hs : bst s) (x : X.t) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (In x s) (¬ In x s) :=
  match h : mem x s with
  | true => .left ((mem_spec hs x).mp h)
  | false => .right (fun hx => by
      have ht : mem x s = true := (mem_spec hs x).mpr hx
      rw [h] at ht
      cases ht)

theorem min_elt_spec1 {s : tree X Info} {x : X.t}
    (h : min_elt s = some x) : In x s := by
  induction s with
  | Leaf => simp [min_elt] at h
  | Node info left value right ihl ihr =>
      cases left with
      | Leaf =>
          simp [min_elt] at h
          subst x
          exact .IsRoot info .Leaf right value (X.eq_refl value)
      | Node leftInfo ll lv lr =>
          exact .InLeft info (.Node leftInfo ll lv lr) right value (ihl h)

theorem min_elt_spec3 {s : tree X Info}
    (h : min_elt s = none) : Empty s := by
  induction s with
  | Leaf => exact fun _ hx => by cases hx
  | Node info left value right ihl ihr =>
      cases left with
      | Leaf => simp [min_elt] at h
      | Node leftInfo ll lv lr =>
          exact False.elim
            (ihl h lv (.IsRoot leftInfo ll lr lv (X.eq_refl lv)))

theorem max_elt_spec1 {s : tree X Info} {x : X.t}
    (h : max_elt s = some x) : In x s := by
  induction s with
  | Leaf => simp [max_elt] at h
  | Node info left value right ihl ihr =>
      cases right with
      | Leaf =>
          simp [max_elt] at h
          subst x
          exact .IsRoot info left .Leaf value (X.eq_refl value)
      | Node rightInfo rl rv rr =>
          exact .InRight info left (.Node rightInfo rl rv rr) value (ihr h)

theorem max_elt_spec3 {s : tree X Info}
    (h : max_elt s = none) : Empty s := by
  induction s with
  | Leaf => exact fun _ hx => by cases hx
  | Node info left value right ihl ihr =>
      cases right with
      | Leaf => simp [max_elt] at h
      | Node rightInfo rl rv rr =>
          exact False.elim
            (ihr h rv (.IsRoot rightInfo rl rr rv (X.eq_refl rv)))

theorem choose_spec1 {s : tree X Info} {x : X.t}
    (h : choose s = some x) : In x s := min_elt_spec1 h

theorem choose_spec2 {s : tree X Info}
    (h : choose s = none) : Empty s := min_elt_spec3 h

theorem inA_nil (x : X.t) : ¬ InA X.eq x [] := by
  rintro ⟨y, _, hy⟩
  exact List.not_mem_nil hy

theorem inA_cons (x y : X.t) (l : List X.t) :
    InA X.eq x (y :: l) ↔ X.eq x y ∨ InA X.eq x l := by
  constructor
  · rintro ⟨z, hxz, hz⟩
    rcases List.mem_cons.mp hz with hzy | hz
    · subst z
      exact Or.inl hxz
    · exact Or.inr ⟨z, hxz, hz⟩
  · intro h
    rcases h with hxy | ⟨z, hxz, hz⟩
    · exact ⟨y, hxy, List.Mem.head l⟩
    · exact ⟨z, hxz, List.Mem.tail y hz⟩

theorem elements_aux_spec (s : tree X Info) (acc : List X.t) (x : X.t) :
    InA X.eq x (elements_aux acc s) ↔ In x s ∨ InA X.eq x acc := by
  induction s generalizing acc with
  | Leaf =>
      simp only [elements_aux]
      constructor
      · exact Or.inr
      · rintro (hin | hacc)
        · cases hin
        · exact hacc
  | Node info left value right ihl ihr =>
      rw [elements_aux, ihl, inA_cons, ihr, in_node]
      constructor <;> intro h
      · rcases h with hleft | hroot | hright | hacc
        · exact Or.inl (Or.inr (Or.inl hleft))
        · exact Or.inl (Or.inl hroot)
        · exact Or.inl (Or.inr (Or.inr hright))
        · exact Or.inr hacc
      · rcases h with (hroot | hleft | hright) | hacc
        · exact Or.inr (Or.inl hroot)
        · exact Or.inl hleft
        · exact Or.inr (Or.inr (Or.inl hright))
        · exact Or.inr (Or.inr (Or.inr hacc))

theorem elements_spec1' (s : tree X Info) (acc : List X.t) (x : X.t) :
    InA X.eq x (elements_aux acc s) ↔ InT x s ∨ InA X.eq x acc :=
  elements_aux_spec s acc x

theorem elements_spec1 (s : tree X Info) (x : X.t) :
    InA X.eq x (elements s) ↔ In x s := by
  rw [elements, elements_aux_spec]
  constructor
  · rintro (h | h)
    · exact h
    · exact False.elim (inA_nil x h)
  · exact Or.inl

theorem elements_aux_append (s : tree X Info) (acc : List X.t) :
    elements_aux acc s = elements s ++ acc := by
  induction s generalizing acc with
  | Leaf => simp [elements_aux, elements]
  | Node info left value right ihl ihr =>
      calc
        elements_aux acc (.Node info left value right) =
            elements left ++ value :: elements_aux acc right := ihl _
        _ = elements left ++ value :: (elements right ++ acc) := by rw [ihr]
        _ = (elements left ++ value :: elements right) ++ acc := by
          simp [List.append_assoc]
        _ = elements (.Node info left value right) ++ acc := by
          congr 1
          change elements left ++ value :: elements right =
            elements_aux (value :: elements_aux [] right) left
          rw [ihr]
          simpa using (ihl (value :: elements right)).symm

theorem elements_app (s : tree X Info) (acc : List X.t) :
    elements_aux acc s = elements s ++ acc :=
  elements_aux_append s acc

theorem elements_node (info : Info) (left right : tree X Info) (x : X.t) :
    elements (.Node info left x right) = elements left ++ x :: elements right := by
  unfold elements
  simp only [elements_aux]
  simpa only [elements] using elements_aux_append left (x :: elements right)

theorem rev_elements_aux_append (s : tree X Info) (acc : List X.t) :
    rev_elements_aux acc s = rev_elements s ++ acc := by
  induction s generalizing acc with
  | Leaf => simp [rev_elements_aux, rev_elements]
  | Node info left value right ihl ihr =>
      calc
        rev_elements_aux acc (.Node info left value right) =
            rev_elements right ++ value :: rev_elements_aux acc left := ihr _
        _ = rev_elements right ++ value :: (rev_elements left ++ acc) := by rw [ihl]
        _ = (rev_elements right ++ value :: rev_elements left) ++ acc := by
          simp [List.append_assoc]
        _ = rev_elements (.Node info left value right) ++ acc := by
          congr 1
          change rev_elements right ++ value :: rev_elements left =
            rev_elements_aux (value :: rev_elements_aux [] left) right
          rw [ihl]
          simpa using (ihr (value :: rev_elements left)).symm

theorem rev_elements_app (s : tree X Info) (acc : List X.t) :
    rev_elements_aux acc s = rev_elements s ++ acc :=
  rev_elements_aux_append s acc

theorem rev_elements_node (info : Info) (left right : tree X Info) (x : X.t) :
    rev_elements (.Node info left x right) =
      rev_elements right ++ x :: rev_elements left := by
  unfold rev_elements
  simp only [rev_elements_aux]
  simpa only [rev_elements] using
    rev_elements_aux_append right (x :: rev_elements left)

theorem rev_elements_rev (s : tree X Info) :
    rev_elements s = (elements s).reverse := by
  induction s with
  | Leaf => rfl
  | Node info left value right ihl ihr =>
      rw [rev_elements_node, elements_node, ihl, ihr]
      simp [List.reverse_append, List.append_assoc]

theorem elements_aux_cardinal (s : tree X Info) (acc : List X.t) :
    acc.length + cardinal s = (elements_aux acc s).length := by
  induction s generalizing acc with
  | Leaf => simp [elements_aux, cardinal]
  | Node info left value right ihl ihr =>
      simp only [elements_aux, cardinal, List.length_cons]
      have hl := ihl (value :: elements_aux acc right)
      have hr := ihr acc
      simp only [List.length_cons] at hl
      omega

theorem elements_cardinal (s : tree X Info) :
    cardinal s = (elements s).length := by
  simpa [elements] using elements_aux_cardinal s []

theorem fold_spec (s : tree X Info) {A : Type} (base : A)
    (f : X.t → A → A) :
    fold f s base = List.foldl (fun acc x => f x acc) base (elements s) := by
  induction s generalizing base with
  | Leaf => rfl
  | Node info left value right ihl ihr =>
      rw [fold, elements_node, List.foldl_append, ihl]
      simp only [List.foldl_cons]
      rw [ihr]

theorem fold_spec' {A : Type} (f : X.t → A → A) (s : tree X Info)
    (base : A) (acc : List X.t) :
    List.foldl (fun state x => f x state) base (elements_aux acc s) =
      List.foldl (fun state x => f x state) (fold f s base) acc := by
  rw [elements_aux_append, List.foldl_append, fold_spec s base f]

def RespectsEq (f : X.t → Bool) : Prop :=
  ∀ x y, X.eq x y → f x = f y

theorem for_all_spec (s : tree X Info) (f : X.t → Bool)
    (hf : RespectsEq f) :
    for_all f s = true ↔ For_all (fun x => f x = true) s := by
  induction s with
  | Leaf =>
      simp only [for_all, For_all]
      constructor <;> intro _
      · intro x hx; cases hx
      · trivial
  | Node info left value right ihl ihr =>
      simp only [for_all, Bool.and_eq_true, ihl, ihr, For_all]
      constructor
      · rintro ⟨⟨hv, hl⟩, hr⟩ x hx
        cases hx with
        | IsRoot _ _ _ _ hx => simpa [hf x value hx] using hv
        | InLeft _ _ _ _ hx => exact hl x hx
        | InRight _ _ _ _ hx => exact hr x hx
      · intro h
        exact ⟨⟨h value (.IsRoot info left right value (X.eq_refl value)),
          fun x hx => h x (.InLeft info left right value hx)⟩,
          fun x hx => h x (.InRight info left right value hx)⟩

theorem exists_spec (s : tree X Info) (f : X.t → Bool)
    (hf : RespectsEq f) :
    exists_ f s = true ↔ Exists (fun x => f x = true) s := by
  induction s with
  | Leaf =>
      simp only [exists_, Exists]
      constructor
      · intro h; cases h
      · rintro ⟨x, hx, _⟩; cases hx
  | Node info left value right ihl ihr =>
      simp only [exists_, Bool.or_eq_true, ihl, ihr, Exists]
      constructor
      · rintro ((hv | hl) | hr)
        · exact ⟨value, .IsRoot info left right value (X.eq_refl value), hv⟩
        · rcases hl with ⟨x, hx, hfx⟩
          exact ⟨x, .InLeft info left right value hx, hfx⟩
        · rcases hr with ⟨x, hx, hfx⟩
          exact ⟨x, .InRight info left right value hx, hfx⟩
      · rintro ⟨x, hx, hfx⟩
        cases hx with
        | IsRoot _ _ _ _ hx =>
            exact Or.inl (Or.inl (by simpa [hf x value hx] using hfx))
        | InLeft _ _ _ _ hx => exact Or.inl (Or.inr ⟨x, hx, hfx⟩)
        | InRight _ _ _ _ hx => exact Or.inr ⟨x, hx, hfx⟩

theorem list_mem_elements_in {s : tree X Info} {x : X.t}
    (h : x ∈ elements s) : In x s := by
  apply (elements_spec1 s x).mp
  exact ⟨x, X.eq_refl x, h⟩

theorem hdRel_of_all {x : X.t} {l : List X.t}
    (h : ∀ y, y ∈ l → X.lt x y) : HdRel X.lt x l := by
  cases l with
  | nil => exact .nil
  | cons y ys => exact .cons y ys (h y (by simp))

theorem sorted_append {l₁ l₂ : List X.t}
    (h₁ : Sorted X.lt l₁) (h₂ : Sorted X.lt l₂)
    (cross : ∀ x, x ∈ l₁ → ∀ y, y ∈ l₂ → X.lt x y) :
    Sorted X.lt (l₁ ++ l₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | @cons x xs hs hd ih =>
      apply CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Sorted.Sorted.cons
        (ih (fun a ha b hb => cross a (by simp [ha]) b hb))
      cases xs with
      | nil =>
          simp only [List.nil_append]
          exact hdRel_of_all (fun y hy => cross x (by simp) y hy)
      | cons z zs =>
          cases hd with
          | cons _ _ hxz => exact .cons z (zs ++ l₂) hxz

theorem elements_sorted {s : tree X Info} (hs : bst s) :
    Sorted X.lt (elements s) := by
  induction hs with
  | BSLeaf => exact .nil
  | BSNode info value left right hl hr hlt hgt ihl ihr =>
      rw [elements_node]
      have hright : Sorted X.lt (value :: elements right) :=
        .cons ihr (hdRel_of_all (fun y hy => hgt y (list_mem_elements_in hy)))
      apply sorted_append ihl hright
      intro x hx y hy
      have hxl : In x left := list_mem_elements_in hx
      rcases List.mem_cons.mp hy with rfl | hyr
      · exact hlt x hxl
      · exact X.lt_trans x value y (hlt x hxl)
          (hgt y (list_mem_elements_in hyr))

theorem sorted_head_all {x : X.t} {l : List X.t}
    (h : Sorted X.lt (x :: l)) : ∀ y, y ∈ l → X.lt x y := by
  intro y hy
  induction l generalizing x with
  | nil => simp at hy
  | cons z zs ih =>
      have hi := CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Sorted.Sorted_inv h
      have hxz :=
        CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Sorted.HdRel_inv hi.2
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hxz
      · exact X.lt_trans x z y hxz (ih hi.1 hy)

theorem sorted_noDupA {l : List X.t} (h : Sorted X.lt l) :
    NoDupA X.eq l := by
  induction h with
  | nil => exact .nil
  | @cons x l hs hd ih =>
      apply CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.NoDupA.cons
      · rintro ⟨y, hxy, hy⟩
        exact X.lt_not_eq x y (sorted_head_all (.cons hs hd) y hy) hxy
      · exact ih

theorem elements_noDupA {s : tree X Info} (hs : bst s) :
    NoDupA X.eq (elements s) :=
  sorted_noDupA (elements_sorted hs)

theorem elements_spec2' (s : tree X Info) (acc : List X.t) (hs : bst s)
    (hacc : Sorted X.lt acc)
    (hcross : ∀ x y, InA X.eq x acc → InT y s → X.lt y x) :
    Sorted X.lt (elements_aux acc s) := by
  rw [elements_aux_append]
  apply sorted_append (elements_sorted hs) hacc
  intro y hy x hx
  exact hcross x y ⟨x, X.eq_refl x, hx⟩ (list_mem_elements_in hy)

theorem elements_spec2 (s : tree X Info) (hs : bst s) :
    Sorted X.lt (elements s) :=
  elements_sorted hs

theorem elements_spec2w (s : tree X Info) (hs : bst s) :
    NoDupA X.eq (elements s) :=
  elements_noDupA hs

theorem lt_tree_node_iff {info : Info} {left right : tree X Info}
    {x y : X.t} :
    lt_tree x (.Node info left y right) ↔
      X.lt y x ∧ lt_tree x left ∧ lt_tree x right := by
  constructor
  · intro h
    exact ⟨h y (.IsRoot info left right y (X.eq_refl y)),
      fun z hz => h z (.InLeft info left right y hz),
      fun z hz => h z (.InRight info left right y hz)⟩
  · rintro ⟨hy, hl, hr⟩
    exact lt_tree_node hl hr hy

theorem gt_tree_node_iff {info : Info} {left right : tree X Info}
    {x y : X.t} :
    gt_tree x (.Node info left y right) ↔
      X.lt x y ∧ gt_tree x left ∧ gt_tree x right := by
  constructor
  · intro h
    exact ⟨h y (.IsRoot info left right y (X.eq_refl y)),
      fun z hz => h z (.InLeft info left right y hz),
      fun z hz => h z (.InRight info left right y hz)⟩
  · rintro ⟨hy, hl, hr⟩
    exact gt_tree_node hl hr hy

theorem ltb_tree_iff (x : X.t) (s : tree X Info) :
    lt_tree x s ↔ ltb_tree x s = true := by
  induction s with
  | Leaf =>
      constructor
      · intro _; rfl
      · intro _; exact lt_leaf x
  | Node info left y right ihl ihr =>
      rw [lt_tree_node_iff]
      cases hcmp : X.compare x y with
      | lt hxy =>
          simp only [ltb_tree, hcmp, Bool.false_eq_true, iff_false]
          rintro ⟨hyx, _, _⟩
          exact lt_asymm hxy hyx
      | eq hxy =>
          simp only [ltb_tree, hcmp, Bool.false_eq_true, iff_false]
          rintro ⟨hyx, _, _⟩
          exact X.lt_not_eq y x hyx (X.eq_sym x y hxy)
      | gt hyx =>
          simp only [ltb_tree, hcmp, Bool.and_eq_true, ← ihl, ← ihr]
          constructor
          · rintro ⟨_, hl, hr⟩; exact ⟨hl, hr⟩
          · rintro ⟨hl, hr⟩; exact ⟨hyx, hl, hr⟩

theorem gtb_tree_iff (x : X.t) (s : tree X Info) :
    gt_tree x s ↔ gtb_tree x s = true := by
  induction s with
  | Leaf =>
      constructor
      · intro _; rfl
      · intro _; exact gt_leaf x
  | Node info left y right ihl ihr =>
      rw [gt_tree_node_iff]
      cases hcmp : X.compare x y with
      | lt hxy =>
          simp only [gtb_tree, hcmp, Bool.and_eq_true, ← ihl, ← ihr]
          constructor
          · rintro ⟨_, hl, hr⟩; exact ⟨hl, hr⟩
          · rintro ⟨hl, hr⟩; exact ⟨hxy, hl, hr⟩
      | eq hxy =>
          simp only [gtb_tree, hcmp, Bool.false_eq_true, iff_false]
          rintro ⟨hxy', _, _⟩
          exact X.lt_not_eq x y hxy' hxy
      | gt hyx =>
          simp only [gtb_tree, hcmp, Bool.false_eq_true, iff_false]
          rintro ⟨hxy, _, _⟩
          exact lt_asymm hxy hyx

theorem isok_iff (s : tree X Info) : bst s ↔ isok s = true := by
  induction s with
  | Leaf =>
      constructor
      · intro _; rfl
      · intro _; exact .BSLeaf
  | Node info left x right ihl ihr =>
      simp only [isok, Bool.and_eq_true, ← ihl, ← ihr,
        ← ltb_tree_iff, ← gtb_tree_iff]
      constructor
      · intro h
        rcases bst_node_inv h with ⟨hl, hr, hlt, hgt⟩
        exact ⟨⟨⟨hl, hr⟩, hlt⟩, hgt⟩
      · rintro ⟨⟨⟨hl, hr⟩, hlt⟩, hgt⟩
        exact .BSNode info x left right hl hr hlt hgt

theorem min_elt_spec2 {s : tree X Info} {x y : X.t} (hs : bst s)
    (hmin : min_elt s = some x) (hy : In y s) : ¬ X.lt y x := by
  induction hs generalizing x y with
  | BSLeaf => simp [min_elt] at hmin
  | BSNode info z left right hleft hright hlt hgt ihl ihr =>
      cases left with
      | Leaf =>
          simp [min_elt] at hmin
          subst x
          intro hyz
          cases hy with
          | IsRoot _ _ _ _ heq =>
              exact X.lt_not_eq y z hyz heq
          | InLeft _ _ _ _ hleaf => cases hleaf
          | InRight _ _ _ _ hyr =>
              exact lt_asymm hyz (hgt y hyr)
      | Node leftInfo ll lv lr =>
          intro hyx
          have hxmin : In x (.Node leftInfo ll lv lr) := min_elt_spec1 hmin
          have hxz : X.lt x z := hlt x hxmin
          cases hy with
          | IsRoot _ _ _ _ heq =>
              have hzx : X.lt z x := lt_of_eq_of_lt heq hyx
              exact lt_asymm hxz hzx
          | InLeft _ _ _ _ hyl => exact ihl hmin hyl hyx
          | InRight _ _ _ _ hyr =>
              have hzy : X.lt z y := hgt y hyr
              exact lt_asymm hyx (X.lt_trans x z y hxz hzy)

theorem max_elt_spec2 {s : tree X Info} {x y : X.t} (hs : bst s)
    (hmax : max_elt s = some x) (hy : In y s) : ¬ X.lt x y := by
  induction hs generalizing x y with
  | BSLeaf => simp [max_elt] at hmax
  | BSNode info z left right hleft hright hlt hgt ihl ihr =>
      cases right with
      | Leaf =>
          simp [max_elt] at hmax
          subst x
          intro hzy
          cases hy with
          | IsRoot _ _ _ _ heq =>
              exact X.lt_not_eq z y hzy (X.eq_sym y z heq)
          | InLeft _ _ _ _ hyl => exact lt_asymm hzy (hlt y hyl)
          | InRight _ _ _ _ hleaf => cases hleaf
      | Node rightInfo rl rv rr =>
          intro hxy
          have hxmax : In x (.Node rightInfo rl rv rr) := max_elt_spec1 hmax
          have hzx : X.lt z x := hgt x hxmax
          cases hy with
          | IsRoot _ _ _ _ heq =>
              have hxz : X.lt x z := lt_of_lt_of_eq hxy heq
              exact lt_asymm hzx hxz
          | InLeft _ _ _ _ hyl =>
              have hyz : X.lt y z := hlt y hyl
              exact lt_asymm hxy (X.lt_trans y z x hyz hzx)
          | InRight _ _ _ _ hyr => exact ihr hmax hyr hxy

theorem choose_spec3 {s s' : tree X Info} {x x' : X.t}
    (hs : bst s) (hs' : bst s')
    (hx : choose s = some x) (hx' : choose s' = some x')
    (heq : Equal s s') : X.eq x x' := by
  have hnotxx' : ¬ X.lt x x' :=
    min_elt_spec2 hs' hx' ((heq x).mp (min_elt_spec1 hx))
  have hnotx'x : ¬ X.lt x' x :=
    min_elt_spec2 hs hx ((heq x').mpr (min_elt_spec1 hx'))
  cases X.compare x x' with
  | lt h => exact False.elim (hnotxx' h)
  | eq h => exact h
  | gt h => exact False.elim (hnotx'x h)

theorem cardinal_spec (s : tree X Info) (_hs : bst s) :
    cardinal s = (elements s).length :=
  elements_cardinal s

theorem sorted_append_inv {l₁ l₂ : List X.t}
    (h : Sorted X.lt (l₁ ++ l₂)) :
    Sorted X.lt l₁ ∧ Sorted X.lt l₂ ∧
      ∀ x₁ x₂, x₁ ∈ l₁ → x₂ ∈ l₂ → X.lt x₁ x₂ := by
  induction l₁ with
  | nil =>
      exact ⟨.nil, h,
        fun x₁ x₂ hx₁ _ => False.elim (List.not_mem_nil hx₁)⟩
  | cons a l ih =>
      have hi := CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Sorted.Sorted_inv h
      rcases ih hi.1 with ⟨hl, hr, hcross⟩
      constructor
      · cases l with
        | nil => exact .cons .nil .nil
        | cons b bs =>
            exact .cons hl (.cons b bs
              (CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Sorted.HdRel_inv hi.2))
      · refine ⟨hr, ?_⟩
        intro x₁ x₂ hx₁ hx₂
        rcases List.mem_cons.mp hx₁ with rfl | hx₁
        · exact sorted_head_all h x₂
            (List.mem_append_right l hx₂)
        · exact hcross x₁ x₂ hx₁ hx₂

theorem sorted_app_inv (l₁ l₂ : List X.t)
    (h : Sorted X.lt (l₁ ++ l₂)) :
    Sorted X.lt l₁ ∧ Sorted X.lt l₂ ∧
      ∀ x₁ x₂, InA X.eq x₁ l₁ → InA X.eq x₂ l₂ → X.lt x₁ x₂ := by
  rcases sorted_append_inv h with ⟨h₁, h₂, hcross⟩
  refine ⟨h₁, h₂, ?_⟩
  rintro x₁ x₂ ⟨y₁, hx₁y₁, hy₁⟩ ⟨y₂, hx₂y₂, hy₂⟩
  exact lt_of_lt_of_eq
    (lt_of_eq_of_lt (X.eq_sym x₁ y₁ hx₁y₁) (hcross y₁ y₂ hy₁ hy₂))
    (X.eq_sym x₂ y₂ hx₂y₂)

theorem elements_sort_ok (s : tree X Info)
    (h : Sorted X.lt (elements s)) : bst s := by
  induction s with
  | Leaf => exact .BSLeaf
  | Node info left x right ihl ihr =>
      rw [elements_node] at h
      rcases sorted_append_inv h with ⟨hleft, hxright, hcross⟩
      have hi :=
        CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Sorted.Sorted_inv hxright
      refine bst.BSNode info x left right (ihl hleft) (ihr hi.1) ?_ ?_
      · intro y hy
        rcases (elements_spec1 left y).mpr hy with ⟨z, hyz, hz⟩
        exact lt_of_eq_of_lt (X.eq_sym y z hyz)
          (hcross z x hz (List.Mem.head (elements right)))
      · intro y hy
        rcases (elements_spec1 right y).mpr hy with ⟨z, hyz, hz⟩
        exact lt_of_lt_of_eq (sorted_head_all hxright z hz) (X.eq_sym y z hyz)

theorem in_left_of_lt_root {info : Info} {left right : tree X Info}
    {x y : X.t} (hbst : bst (.Node info left x right))
    (hy : In y (.Node info left x right)) (hyx : X.lt y x) : In y left := by
  rcases bst_node_inv hbst with ⟨_, _, _, hgt⟩
  cases hy with
  | IsRoot _ _ _ _ heq => exact False.elim (X.lt_not_eq y x hyx heq)
  | InLeft _ _ _ _ hleft => exact hleft
  | InRight _ _ _ _ hright => exact False.elim (lt_asymm hyx (hgt y hright))

theorem in_right_of_gt_root {info : Info} {left right : tree X Info}
    {x y : X.t} (hbst : bst (.Node info left x right))
    (hy : In y (.Node info left x right)) (hxy : X.lt x y) : In y right := by
  rcases bst_node_inv hbst with ⟨_, _, hlt, _⟩
  cases hy with
  | IsRoot _ _ _ _ heq =>
      exact False.elim (X.lt_not_eq x y hxy (X.eq_sym y x heq))
  | InLeft _ _ _ _ hleft => exact False.elim (lt_asymm (hlt y hleft) hxy)
  | InRight _ _ _ _ hright => exact hright

theorem subsetl_spec (subsetLeft : tree X Info → Bool)
    (left₁ : tree X Info) (x₁ : X.t) (info₁ : Info) (s₂ : tree X Info)
    (h₁ : bst (.Node info₁ left₁ x₁ .Leaf)) (h₂ : bst s₂)
    (hsubset : ∀ s, bst s →
      (subsetLeft s = true ↔ Subset left₁ s)) :
    subsetl subsetLeft x₁ s₂ = true ↔
      Subset (.Node info₁ left₁ x₁ .Leaf) s₂ := by
  induction h₂ with
  | BSLeaf =>
      constructor
      · intro h; cases h
      · intro h
        have hx := h x₁ (.IsRoot info₁ left₁ .Leaf x₁ (X.eq_refl x₁))
        cases hx
  | BSNode info₂ x₂ left₂ right₂ hleft₂ hright₂ hlt₂ hgt₂ ihl ihr =>
      rcases bst_node_inv h₁ with ⟨hleft₁, _, hlt₁, _⟩
      cases hcmp : X.compare x₁ x₂ with
      | eq heq =>
          simp only [subsetl, hcmp]
          rw [hsubset left₂ hleft₂]
          constructor
          · intro hsub a ha
            cases ha with
            | IsRoot _ _ _ _ haeq =>
                exact .IsRoot info₂ left₂ right₂ x₂
                  (X.eq_trans a x₁ x₂ haeq heq)
            | InLeft _ _ _ _ haleft =>
                exact .InLeft info₂ left₂ right₂ x₂ (hsub a haleft)
            | InRight _ _ _ _ haleaf => cases haleaf
          · intro hsub a ha
            have hain : In a (.Node info₂ left₂ x₂ right₂) :=
              hsub a (.InLeft info₁ left₁ .Leaf x₁ ha)
            have hax₁ := hlt₁ a ha
            have hax₂ := lt_of_lt_of_eq hax₁ heq
            exact in_left_of_lt_root
              (.BSNode info₂ x₂ left₂ right₂ hleft₂ hright₂ hlt₂ hgt₂)
              hain hax₂
      | lt hx₁x₂ =>
          simp only [subsetl, hcmp]
          rw [ihl]
          constructor
          · intro hsub a ha
            exact .InLeft info₂ left₂ right₂ x₂ (hsub a ha)
          · intro hsub a ha
            have hain := hsub a ha
            have hax₂ : X.lt a x₂ := by
              cases ha with
              | IsRoot _ _ _ _ haeq =>
                  exact lt_of_eq_of_lt (X.eq_sym a x₁ haeq) hx₁x₂
              | InLeft _ _ _ _ haleft =>
                  exact X.lt_trans a x₁ x₂ (hlt₁ a haleft) hx₁x₂
              | InRight _ _ _ _ haleaf => cases haleaf
            exact in_left_of_lt_root
              (.BSNode info₂ x₂ left₂ right₂ hleft₂ hright₂ hlt₂ hgt₂)
              hain hax₂
      | gt hx₂x₁ =>
          simp only [subsetl, hcmp, Bool.and_eq_true]
          rw [mem_spec hright₂, hsubset _
            (.BSNode info₂ x₂ left₂ right₂
              hleft₂ hright₂ hlt₂ hgt₂)]
          constructor
          · rintro ⟨hxright, hsub⟩ a ha
            cases ha with
            | IsRoot _ _ _ _ haeq =>
                exact .InRight info₂ left₂ right₂ x₂
                  (in_of_eq (X.eq_sym a x₁ haeq) hxright)
            | InLeft _ _ _ _ haleft => exact hsub a haleft
            | InRight _ _ _ _ haleaf => cases haleaf
          · intro hsub
            constructor
            · have hx := hsub x₁
                  (.IsRoot info₁ left₁ .Leaf x₁ (X.eq_refl x₁))
              exact in_right_of_gt_root
                (.BSNode info₂ x₂ left₂ right₂
                  hleft₂ hright₂ hlt₂ hgt₂) hx hx₂x₁
            · intro a ha
              exact hsub a (.InLeft info₁ left₁ .Leaf x₁ ha)

theorem subsetr_spec (subsetRight : tree X Info → Bool)
    (right₁ : tree X Info) (x₁ : X.t) (info₁ : Info) (s₂ : tree X Info)
    (h₁ : bst (.Node info₁ .Leaf x₁ right₁)) (h₂ : bst s₂)
    (hsubset : ∀ s, bst s →
      (subsetRight s = true ↔ Subset right₁ s)) :
    subsetr subsetRight x₁ s₂ = true ↔
      Subset (.Node info₁ .Leaf x₁ right₁) s₂ := by
  induction h₂ with
  | BSLeaf =>
      constructor
      · intro h; cases h
      · intro h
        have hx := h x₁ (.IsRoot info₁ .Leaf right₁ x₁ (X.eq_refl x₁))
        cases hx
  | BSNode info₂ x₂ left₂ right₂ hleft₂ hright₂ hlt₂ hgt₂ ihl ihr =>
      rcases bst_node_inv h₁ with ⟨_, hright₁, _, hgt₁⟩
      cases hcmp : X.compare x₁ x₂ with
      | eq heq =>
          simp only [subsetr, hcmp]
          rw [hsubset right₂ hright₂]
          constructor
          · intro hsub a ha
            cases ha with
            | IsRoot _ _ _ _ haeq =>
                exact .IsRoot info₂ left₂ right₂ x₂
                  (X.eq_trans a x₁ x₂ haeq heq)
            | InLeft _ _ _ _ haleaf => cases haleaf
            | InRight _ _ _ _ haright =>
                exact .InRight info₂ left₂ right₂ x₂ (hsub a haright)
          · intro hsub a ha
            have hain : In a (.Node info₂ left₂ x₂ right₂) :=
              hsub a (.InRight info₁ .Leaf right₁ x₁ ha)
            have hx₁a := hgt₁ a ha
            have hx₂a := lt_of_eq_of_lt heq hx₁a
            exact in_right_of_gt_root
              (.BSNode info₂ x₂ left₂ right₂ hleft₂ hright₂ hlt₂ hgt₂)
              hain hx₂a
      | lt hx₁x₂ =>
          simp only [subsetr, hcmp, Bool.and_eq_true]
          rw [mem_spec hleft₂, hsubset _
            (.BSNode info₂ x₂ left₂ right₂
              hleft₂ hright₂ hlt₂ hgt₂)]
          constructor
          · rintro ⟨hxleft, hsub⟩ a ha
            cases ha with
            | IsRoot _ _ _ _ haeq =>
                exact .InLeft info₂ left₂ right₂ x₂
                  (in_of_eq (X.eq_sym a x₁ haeq) hxleft)
            | InLeft _ _ _ _ haleaf => cases haleaf
            | InRight _ _ _ _ haright => exact hsub a haright
          · intro hsub
            constructor
            · have hx := hsub x₁
                  (.IsRoot info₁ .Leaf right₁ x₁ (X.eq_refl x₁))
              exact in_left_of_lt_root
                (.BSNode info₂ x₂ left₂ right₂
                  hleft₂ hright₂ hlt₂ hgt₂) hx hx₁x₂
            · intro a ha
              exact hsub a (.InRight info₁ .Leaf right₁ x₁ ha)
      | gt hx₂x₁ =>
          simp only [subsetr, hcmp]
          rw [ihr]
          constructor
          · intro hsub a ha
            exact .InRight info₂ left₂ right₂ x₂ (hsub a ha)
          · intro hsub a ha
            have hain := hsub a ha
            have hx₂a : X.lt x₂ a := by
              cases ha with
              | IsRoot _ _ _ _ haeq => exact lt_of_lt_of_eq hx₂x₁ (X.eq_sym a x₁ haeq)
              | InLeft _ _ _ _ haleaf => cases haleaf
              | InRight _ _ _ _ haright =>
                  exact X.lt_trans x₂ x₁ a hx₂x₁ (hgt₁ a haright)
            exact in_right_of_gt_root
              (.BSNode info₂ x₂ left₂ right₂ hleft₂ hright₂ hlt₂ hgt₂)
              hain hx₂a

theorem subset_spec (s₁ s₂ : tree X Info) (h₁ : bst s₁) (h₂ : bst s₂) :
    subset s₁ s₂ = true ↔ Subset s₁ s₂ := by
  induction h₁ generalizing s₂ with
  | BSLeaf =>
      simp only [subset, Subset]
      constructor
      · intro _ a ha; cases ha
      · intro _; trivial
  | BSNode info₁ x₁ left₁ right₁ hleft₁ hright₁ hlt₁ hgt₁ ihl ihr =>
      cases h₂ with
      | BSLeaf =>
          constructor
          · intro h; cases h
          · intro h
            have hx := h x₁
              (.IsRoot info₁ left₁ right₁ x₁ (X.eq_refl x₁))
            cases hx
      | BSNode info₂ x₂ left₂ right₂ hleft₂ hright₂ hlt₂ hgt₂ =>
          let hs₁ : tree X Info := .Node info₁ left₁ x₁ right₁
          let hs₂ : tree X Info := .Node info₂ left₂ x₂ right₂
          have hbst₁ : bst hs₁ :=
            .BSNode info₁ x₁ left₁ right₁ hleft₁ hright₁ hlt₁ hgt₁
          have hbst₂ : bst hs₂ :=
            .BSNode info₂ x₂ left₂ right₂ hleft₂ hright₂ hlt₂ hgt₂
          cases hcmp : X.compare x₁ x₂ with
          | eq heq =>
              simp only [subset, hcmp, Bool.and_eq_true]
              rw [ihl left₂ hleft₂, ihr right₂ hright₂]
              constructor
              · rintro ⟨hlsub, hrsub⟩ a ha
                cases ha with
                | IsRoot _ _ _ _ haeq =>
                    exact .IsRoot info₂ left₂ right₂ x₂
                      (X.eq_trans a x₁ x₂ haeq heq)
                | InLeft _ _ _ _ haleft =>
                    exact .InLeft info₂ left₂ right₂ x₂ (hlsub a haleft)
                | InRight _ _ _ _ haright =>
                    exact .InRight info₂ left₂ right₂ x₂ (hrsub a haright)
              · intro hsub
                constructor
                · intro a ha
                  have hain := hsub a (.InLeft info₁ left₁ right₁ x₁ ha)
                  exact in_left_of_lt_root hbst₂ hain
                    (lt_of_lt_of_eq (hlt₁ a ha) heq)
                · intro a ha
                  have hain := hsub a (.InRight info₁ left₁ right₁ x₁ ha)
                  exact in_right_of_gt_root hbst₂ hain
                    (lt_of_eq_of_lt heq (hgt₁ a ha))
          | lt hx₁x₂ =>
              simp only [subset, hcmp, Bool.and_eq_true]
              rw [subsetl_spec (subset left₁) left₁ x₁ info₁ left₂
                (.BSNode info₁ x₁ left₁ .Leaf hleft₁ .BSLeaf hlt₁ (gt_leaf x₁))
                hleft₂ (fun s hs => ihl s hs),
                ihr hs₂ hbst₂]
              constructor
              · rintro ⟨hhalf, hright⟩ a ha
                cases ha with
                | IsRoot _ _ _ _ haeq =>
                    exact .InLeft info₂ left₂ right₂ x₂
                      (hhalf a (.IsRoot info₁ left₁ .Leaf x₁ haeq))
                | InLeft _ _ _ _ haleft =>
                    exact .InLeft info₂ left₂ right₂ x₂
                      (hhalf a (.InLeft info₁ left₁ .Leaf x₁ haleft))
                | InRight _ _ _ _ haright => exact hright a haright
              · intro hsub
                constructor
                · intro a ha
                  have hain := hsub a (by
                    cases ha with
                    | IsRoot _ _ _ _ heq =>
                        exact .IsRoot info₁ left₁ right₁ x₁ heq
                    | InLeft _ _ _ _ hleft =>
                        exact .InLeft info₁ left₁ right₁ x₁ hleft
                    | InRight _ _ _ _ hleaf => cases hleaf)
                  have hax₂ : X.lt a x₂ := by
                    cases ha with
                    | IsRoot _ _ _ _ heq =>
                        exact lt_of_eq_of_lt (X.eq_sym a x₁ heq) hx₁x₂
                    | InLeft _ _ _ _ hleft =>
                        exact X.lt_trans a x₁ x₂ (hlt₁ a hleft) hx₁x₂
                    | InRight _ _ _ _ hleaf => cases hleaf
                  exact in_left_of_lt_root hbst₂ hain hax₂
                · intro a ha
                  exact hsub a (.InRight info₁ left₁ right₁ x₁ ha)
          | gt hx₂x₁ =>
              simp only [subset, hcmp, Bool.and_eq_true]
              rw [subsetr_spec (subset right₁) right₁ x₁ info₁ right₂
                (.BSNode info₁ x₁ .Leaf right₁ .BSLeaf hright₁ (lt_leaf x₁) hgt₁)
                hright₂ (fun s hs => ihr s hs),
                ihl hs₂ hbst₂]
              constructor
              · rintro ⟨hhalf, hleft⟩ a ha
                cases ha with
                | IsRoot _ _ _ _ haeq =>
                    exact .InRight info₂ left₂ right₂ x₂
                      (hhalf a (.IsRoot info₁ .Leaf right₁ x₁ haeq))
                | InLeft _ _ _ _ haleft => exact hleft a haleft
                | InRight _ _ _ _ haright =>
                    exact .InRight info₂ left₂ right₂ x₂
                      (hhalf a (.InRight info₁ .Leaf right₁ x₁ haright))
              · intro hsub
                constructor
                · intro a ha
                  have hain := hsub a (by
                    cases ha with
                    | IsRoot _ _ _ _ heq =>
                        exact .IsRoot info₁ left₁ right₁ x₁ heq
                    | InLeft _ _ _ _ hleaf => cases hleaf
                    | InRight _ _ _ _ hright =>
                        exact .InRight info₁ left₁ right₁ x₁ hright)
                  have hx₂a : X.lt x₂ a := by
                    cases ha with
                    | IsRoot _ _ _ _ heq =>
                        exact lt_of_lt_of_eq hx₂x₁ (X.eq_sym a x₁ heq)
                    | InLeft _ _ _ _ hleaf => cases hleaf
                    | InRight _ _ _ _ hright =>
                        exact X.lt_trans x₂ x₁ a hx₂x₁ (hgt₁ a hright)
                  exact in_right_of_gt_root hbst₂ hain hx₂a
                · intro a ha
                  exact hsub a (.InLeft info₁ left₁ right₁ x₁ ha)

namespace L

def eq (l₁ l₂ : List X.t) : Prop :=
  ∀ x, InA X.eq x l₁ ↔ InA X.eq x l₂

inductive lt_list : List X.t → List X.t → Prop where
  | lt_nil (x : X.t) (l : List X.t) : lt_list [] (x :: l)
  | lt_cons_lt (x y : X.t) (l₁ l₂ : List X.t) :
      X.lt x y → lt_list (x :: l₁) (y :: l₂)
  | lt_cons_eq (x y : X.t) (l₁ l₂ : List X.t) :
      X.eq x y → lt_list l₁ l₂ → lt_list (x :: l₁) (y :: l₂)

abbrev lt := lt_list (X := X)

inductive EqList : List X.t → List X.t → Prop where
  | nil : EqList [] []
  | cons {x y : X.t} {l₁ l₂ : List X.t} :
      X.eq x y → EqList l₁ l₂ → EqList (x :: l₁) (y :: l₂)

theorem eq_refl (l : List X.t) : eq l l := fun _ => Iff.rfl

theorem eq_symm {l₁ l₂ : List X.t} (h : eq l₁ l₂) : eq l₂ l₁ :=
  fun x => (h x).symm

theorem eq_trans {l₁ l₂ l₃ : List X.t}
    (h₁₂ : eq l₁ l₂) (h₂₃ : eq l₂ l₃) : eq l₁ l₃ :=
  fun x => (h₁₂ x).trans (h₂₃ x)

theorem eq_cons {x y : X.t} {l₁ l₂ : List X.t}
    (hxy : X.eq x y) (heq : eq l₁ l₂) : eq (x :: l₁) (y :: l₂) := by
  intro z
  rw [inA_cons, inA_cons]
  constructor
  · rintro (hzx | hzl)
    · exact Or.inl (X.eq_trans z x y hzx hxy)
    · exact Or.inr ((heq z).mp hzl)
  · rintro (hzy | hzl)
    · exact Or.inl (X.eq_trans z y x hzy (X.eq_sym x y hxy))
    · exact Or.inr ((heq z).mpr hzl)

theorem cons_CompSpec {c : comparison} {x₁ x₂ : X.t}
    {l₁ l₂ : List X.t} (hxx : X.eq x₁ x₂)
    (h : CompSpec eq lt l₁ l₂ c) :
    CompSpec eq lt (x₁ :: l₁) (x₂ :: l₂) c := by
  cases h with
  | CompEq heq => exact .CompEq (eq_cons hxx heq)
  | CompLt hlt => exact .CompLt (.lt_cons_eq x₁ x₂ l₁ l₂ hxx hlt)
  | CompGt hgt =>
      exact .CompGt
        (.lt_cons_eq x₂ x₁ l₂ l₁ (X.eq_sym x₁ x₂ hxx) hgt)

end L

def eq (s₁ s₂ : tree X Info) : Prop := Equal s₁ s₂

theorem eq_Leq (s₁ s₂ : tree X Info) :
    eq s₁ s₂ ↔ L.eq (elements s₁) (elements s₂) := by
  constructor
  · intro h x
    rw [elements_spec1, elements_spec1]
    exact h x
  · intro h x
    rw [← elements_spec1, ← elements_spec1]
    exact h x

def lt (s₁ s₂ : tree X Info) : Prop :=
  ∃ s₁' s₂', bst s₁' ∧ bst s₂' ∧ eq s₁ s₁' ∧ eq s₂ s₂' ∧
    L.lt (elements s₁') (elements s₂')

def flatten_e : enumeration X Info → List X.t
  | .End => []
  | .More x s rest => x :: elements s ++ flatten_e rest

theorem flatten_e_elements (left : tree X Info) (x : X.t)
    (right : tree X Info) (info : Info) (e : enumeration X Info) :
    elements left ++ flatten_e (.More x right e) =
      elements (.Node info left x right) ++ flatten_e e := by
  rw [elements_node]
  simp [flatten_e, List.append_assoc]

theorem cons_1 (s : tree X Info) (e : enumeration X Info) :
    flatten_e (cons s e) = elements s ++ flatten_e e := by
  induction s generalizing e with
  | Leaf => simp [cons, elements, elements_aux]
  | Node info left x right ihl ihr =>
      simp only [cons]
      rw [ihl, flatten_e_elements]

abbrev Cmp (c : comparison) (l₁ l₂ : List X.t) : Prop :=
  CompSpec L.eq L.lt l₁ l₂ c

theorem compare_end_Cmp (e₂ : enumeration X Info) :
    Cmp (compare_end e₂) [] (flatten_e e₂) := by
  cases e₂ with
  | End => exact .CompEq (L.eq_refl [])
  | More x s rest => exact .CompLt (.lt_nil x (elements s ++ flatten_e rest))

theorem compare_more_Cmp (x₁ : X.t) (cont : enumeration X Info → comparison)
    (x₂ : X.t) (right₂ : tree X Info) (e₂ : enumeration X Info)
    (l : List X.t)
    (h : Cmp (cont (cons right₂ e₂)) l
      (elements right₂ ++ flatten_e e₂)) :
    Cmp (compare_more x₁ cont (.More x₂ right₂ e₂))
      (x₁ :: l) (flatten_e (.More x₂ right₂ e₂)) := by
  simp only [compare_more, flatten_e]
  cases X.compare x₁ x₂ with
  | eq heq => exact L.cons_CompSpec heq h
  | lt hlt => exact .CompLt (.lt_cons_lt x₁ x₂ l
      (elements right₂ ++ flatten_e e₂) hlt)
  | gt hgt => exact .CompGt (.lt_cons_lt x₂ x₁
      (elements right₂ ++ flatten_e e₂) l hgt)

theorem compare_cont_Cmp (s₁ : tree X Info)
    (cont : enumeration X Info → comparison) (e₂ : enumeration X Info)
    (l : List X.t)
    (hcont : ∀ e, Cmp (cont e) l (flatten_e e)) :
    Cmp (compare_cont s₁ cont e₂) (elements s₁ ++ l) (flatten_e e₂) := by
  induction s₁ generalizing cont e₂ l with
  | Leaf => simpa [compare_cont, elements, elements_aux] using hcont e₂
  | Node info left x right ihl ihr =>
      rw [elements_node]
      rw [List.append_assoc]
      simp only [compare_cont]
      apply ihl
      intro e
      cases e with
      | End =>
          exact .CompGt (.lt_nil x (elements right ++ l))
      | More x₂ right₂ e₂ =>
          apply compare_more_Cmp
          have hr := ihr (cont := cont) (e₂ := cons right₂ e₂)
            (l := l) hcont
          rw [cons_1] at hr
          exact hr

theorem compare_Cmp (s₁ s₂ : tree X Info) :
    Cmp (compare s₁ s₂) (elements s₁) (elements s₂) := by
  unfold compare
  have h := compare_cont_Cmp s₁ compare_end (cons s₂ .End) []
    (fun e => compare_end_Cmp e)
  rw [cons_1] at h
  simpa [flatten_e] using h

theorem compare_spec (s₁ s₂ : tree X Info) (h₁ : bst s₁) (h₂ : bst s₂) :
    CompSpec eq lt s₁ s₂ (compare s₁ s₂) := by
  have hc := compare_Cmp s₁ s₂
  cases hcmp : compare s₁ s₂ with
  | Eq =>
      rw [hcmp] at hc
      cases hc with
      | CompEq heq => exact .CompEq ((eq_Leq s₁ s₂).mpr heq)
  | Lt =>
      rw [hcmp] at hc
      cases hc with
      | CompLt hlt =>
          exact .CompLt ⟨s₁, s₂, h₁, h₂,
            fun _ => Iff.rfl, fun _ => Iff.rfl, hlt⟩
  | Gt =>
      rw [hcmp] at hc
      cases hc with
      | CompGt hgt =>
          exact .CompGt ⟨s₂, s₁, h₂, h₁,
            fun _ => Iff.rfl, fun _ => Iff.rfl, hgt⟩

theorem sorted_head_not_lt {x y : X.t} {l : List X.t}
    (hs : Sorted X.lt (x :: l)) (hy : InA X.eq y (x :: l)) : ¬ X.lt y x := by
  intro hyx
  rw [inA_cons] at hy
  rcases hy with hyxEq | ⟨z, hyz, hz⟩
  · exact X.lt_not_eq y x hyx hyxEq
  · have hxz := sorted_head_all hs z hz
    have hzx : X.lt z x := lt_of_eq_of_lt hyz hyx
    exact lt_asymm hxz hzx

theorem sorted_tail_eq {x y : X.t} {l₁ l₂ : List X.t}
    (hs₁ : Sorted X.lt (x :: l₁)) (hs₂ : Sorted X.lt (y :: l₂))
    (hxy : X.eq x y) (heq : L.eq (x :: l₁) (y :: l₂)) :
    L.eq l₁ l₂ := by
  intro z
  constructor
  · intro hz
    have hzfull := (heq z).mp ((inA_cons z x l₁).mpr (Or.inr hz))
    rw [inA_cons] at hzfull
    rcases hzfull with hzy | hzright
    · rcases hz with ⟨w, hzw, hw⟩
      have hxw := sorted_head_all hs₁ w hw
      have hxz := lt_of_lt_of_eq hxw (X.eq_sym z w hzw)
      have hxzEq := X.eq_trans x y z hxy (X.eq_sym z y hzy)
      exact False.elim (X.lt_not_eq x z hxz hxzEq)
    · exact hzright
  · intro hz
    have hzfull := (heq z).mpr ((inA_cons z y l₂).mpr (Or.inr hz))
    rw [inA_cons] at hzfull
    rcases hzfull with hzx | hzleft
    · rcases hz with ⟨w, hzw, hw⟩
      have hyw := sorted_head_all hs₂ w hw
      have hyz := lt_of_lt_of_eq hyw (X.eq_sym z w hzw)
      have hyzEq := X.eq_trans y x z (X.eq_sym x y hxy) (X.eq_sym z x hzx)
      exact False.elim (X.lt_not_eq y z hyz hyzEq)
    · exact hzleft

namespace L

theorem lt_irrefl (l : List X.t) : ¬ lt l l := by
  induction l with
  | nil => intro h; cases h
  | cons x xs ih =>
      intro h
      cases h with
      | lt_cons_lt _ _ _ _ hxx => exact lt_asymm hxx hxx
      | lt_cons_eq _ _ _ _ _ htail => exact ih htail

theorem lt_trans {l₁ l₂ l₃ : List X.t}
    (h₁₂ : lt l₁ l₂) (h₂₃ : lt l₂ l₃) : lt l₁ l₃ := by
  induction h₁₂ generalizing l₃ with
  | lt_nil x l =>
      cases h₂₃ with
      | lt_cons_lt _ z _ zs _ => exact .lt_nil z zs
      | lt_cons_eq _ z _ zs _ _ => exact .lt_nil z zs
  | lt_cons_lt x y xs ys hxy =>
      cases h₂₃ with
      | lt_cons_lt _ z _ zs hyz =>
          exact .lt_cons_lt x z xs zs (X.lt_trans x y z hxy hyz)
      | lt_cons_eq _ z _ zs hyz _ =>
          exact .lt_cons_lt x z xs zs (lt_of_lt_of_eq hxy hyz)
  | lt_cons_eq x y xs ys hxy htail ih =>
      cases h₂₃ with
      | lt_cons_lt _ z _ zs hyz =>
          exact .lt_cons_lt x z xs zs
            (lt_of_eq_of_lt (X.eq_sym x y hxy) hyz)
      | lt_cons_eq _ z _ zs hyz htail₂ =>
          exact .lt_cons_eq x z xs zs (X.eq_trans x y z hxy hyz) (ih htail₂)

theorem eqList_refl (l : List X.t) : EqList l l := by
  induction l with
  | nil => exact .nil
  | cons x xs ih => exact .cons (X.eq_refl x) ih

theorem lt_congr {l₁ l₁' l₂ l₂' : List X.t}
    (heq₁ : EqList l₁ l₁')
    (heq₂ : EqList l₂ l₂')
    (hlt : lt l₁ l₂) : lt l₁' l₂' := by
  induction hlt generalizing l₁' l₂' with
  | lt_nil x l =>
      cases heq₁
      cases heq₂ with
      | cons hxy htail => exact .lt_nil _ _
  | lt_cons_lt x y xs ys hxy =>
      cases heq₁ with
      | cons hxx hxs =>
          cases heq₂ with
          | cons hyy hys =>
              exact .lt_cons_lt _ _ _ _
                (lt_of_lt_of_eq (lt_of_eq_of_lt hxx hxy) hyy)
  | lt_cons_eq x y xs ys hxy htail ih =>
      cases heq₁ with
      | cons hxx hxs =>
          cases heq₂ with
          | cons hyy hys =>
              exact .lt_cons_eq _ _ _ _
                (X.eq_trans _ x _ (X.eq_sym x _ hxx)
                  (X.eq_trans x y _ hxy hyy))
                (ih hxs hys)

end L

theorem sorted_extensional_eqList {l₁ l₂ : List X.t}
    (hs₁ : Sorted X.lt l₁) (hs₂ : Sorted X.lt l₂)
    (heq : L.eq l₁ l₂) : L.EqList l₁ l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => exact .nil
      | cons y ys =>
          have hy : InA X.eq y ([] : List X.t) :=
            (heq y).mpr ((inA_cons y y ys).mpr (Or.inl (X.eq_refl y)))
          exact False.elim (inA_nil y hy)
  | cons x xs ih =>
      cases l₂ with
      | nil =>
          have hx : InA X.eq x ([] : List X.t) :=
            (heq x).mp ((inA_cons x x xs).mpr (Or.inl (X.eq_refl x)))
          exact False.elim (inA_nil x hx)
      | cons y ys =>
          have hnotxy : ¬ X.lt x y := sorted_head_not_lt hs₂
            ((heq x).mp ((inA_cons x x xs).mpr (Or.inl (X.eq_refl x))))
          have hnotyx : ¬ X.lt y x := sorted_head_not_lt hs₁
            ((heq y).mpr ((inA_cons y y ys).mpr (Or.inl (X.eq_refl y))))
          have hxy : X.eq x y := by
            cases X.compare x y with
            | lt h => exact False.elim (hnotxy h)
            | eq h => exact h
            | gt h => exact False.elim (hnotyx h)
          have hi₁ :=
            CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Sorted.Sorted_inv hs₁
          have hi₂ :=
            CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Sorted.Sorted_inv hs₂
          exact .cons hxy
            (ih hi₁.1 hi₂.1 (sorted_tail_eq hs₁ hs₂ hxy heq))

theorem L.lt_not_eq_sorted {l₁ l₂ : List X.t}
    (hs₁ : Sorted X.lt l₁) (hs₂ : Sorted X.lt l₂)
    (hlt : L.lt l₁ l₂) (heq : L.eq l₁ l₂) : False := by
  have hfor := sorted_extensional_eqList hs₁ hs₂ heq
  have hsame := L.lt_congr hfor (L.eqList_refl l₂) hlt
  exact L.lt_irrefl l₂ hsame

theorem lt_not_eq {s₁ s₂ : tree X Info} (hlt : lt s₁ s₂) : ¬ eq s₁ s₂ := by
  rintro heq
  rcases hlt with ⟨s₁', s₂', hbst₁, hbst₂, heq₁, heq₂, hlist⟩
  have hwitness : eq s₁' s₂' := fun a =>
    ((heq₁ a).symm.trans (heq a)).trans (heq₂ a)
  exact L.lt_not_eq_sorted (elements_sorted hbst₁) (elements_sorted hbst₂)
    hlist ((eq_Leq s₁' s₂').mp hwitness)

def eq_equiv : Equivalence (@eq X Info) where
  refl := fun _ _ => Iff.rfl
  symm := fun {x y} h a => (h a).symm
  trans := fun {x y z} h₁ h₂ a => (h₁ a).trans (h₂ a)

theorem lt_transitive {s₁ s₂ s₃ : tree X Info}
    (h₁₂ : lt s₁ s₂) (h₂₃ : lt s₂ s₃) : lt s₁ s₃ := by
  rcases h₁₂ with ⟨s₁', s₂', hb₁, hb₂, he₁, he₂, hl₁₂⟩
  rcases h₂₃ with ⟨s₂'', s₃', hb₂', hb₃, he₂', he₃, hl₂₃⟩
  have hmid : eq s₂' s₂'' := fun a => (he₂ a).symm.trans (he₂' a)
  have hmidList := sorted_extensional_eqList
    (elements_sorted hb₂') (elements_sorted hb₂)
    (L.eq_symm ((eq_Leq s₂' s₂'').mp hmid))
  have hl₂₃' := L.lt_congr hmidList (L.eqList_refl (elements s₃')) hl₂₃
  exact ⟨s₁', s₃', hb₁, hb₃, he₁, he₃,
    L.lt_trans hl₁₂ hl₂₃'⟩

instance lt_strorder : StrictOrder (@lt X Info) where
  irrefl := fun s hs => lt_not_eq hs (fun _ => Iff.rfl)
  trans := fun h₁ h₂ => lt_transitive h₁ h₂

theorem lt_compat {s₁ s₂ s₃ s₄ : tree X Info}
    (heq₁₂ : eq s₁ s₂) (heq₃₄ : eq s₃ s₄) :
    lt s₁ s₃ ↔ lt s₂ s₄ := by
  constructor
  · rintro ⟨s₁', s₃', hb₁, hb₃, he₁, he₃, hlt⟩
    exact ⟨s₁', s₃', hb₁, hb₃,
      fun a => (heq₁₂ a).symm.trans (he₁ a),
      fun a => (heq₃₄ a).symm.trans (he₃ a), hlt⟩
  · rintro ⟨s₁', s₃', hb₁, hb₃, he₁, he₃, hlt⟩
    exact ⟨s₁', s₃', hb₁, hb₃,
      fun a => (heq₁₂ a).trans (he₁ a),
      fun a => (heq₃₄ a).trans (he₃ a), hlt⟩

theorem equal_spec (s₁ s₂ : tree X Info) (h₁ : bst s₁) (h₂ : bst s₂) :
    equal s₁ s₂ = true ↔ eq s₁ s₂ := by
  have hc := compare_spec s₁ s₂ h₁ h₂
  cases hcmp : compare s₁ s₂ with
  | Eq =>
      rw [hcmp] at hc
      cases hc with
      | CompEq heq => simp [equal, hcmp, heq]
  | Lt =>
      rw [hcmp] at hc
      cases hc with
      | CompLt hlt =>
          simp only [equal, hcmp, Bool.false_eq_true]
          constructor
          · intro h; cases h
          · intro heq; exact False.elim (lt_not_eq hlt heq)
  | Gt =>
      rw [hcmp] at hc
      cases hc with
      | CompGt hgt =>
          simp only [equal, hcmp, Bool.false_eq_true]
          constructor
          · intro h; cases h
          · intro heq
            exact False.elim (lt_not_eq hgt (fun a => (heq a).symm))

theorem mindepth_maxdepth (s : tree X Info) : mindepth s ≤ maxdepth s := by
  induction s with
  | Leaf => exact Nat.le_refl 0
  | Node info left x right ihl ihr =>
      simp only [mindepth, maxdepth, Nat.succ_le_succ_iff]
      exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_trans ihl (Nat.le_max_left _ _))

theorem maxdepth_cardinal (s : tree X Info) : cardinal s < 2 ^ maxdepth s := by
  induction s with
  | Leaf => simp [cardinal, maxdepth]
  | Node info left x right ihl ihr =>
      simp only [cardinal, maxdepth, Nat.pow_succ]
      have hlpow : 2 ^ maxdepth left ≤ 2 ^ Nat.max (maxdepth left) (maxdepth right) :=
        Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
      have hrpow : 2 ^ maxdepth right ≤ 2 ^ Nat.max (maxdepth left) (maxdepth right) :=
        Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)
      omega

theorem mindepth_cardinal (s : tree X Info) :
    2 ^ mindepth s ≤ Nat.succ (cardinal s) := by
  induction s with
  | Leaf => simp [cardinal, mindepth]
  | Node info left x right ihl ihr =>
      simp only [cardinal, mindepth, Nat.pow_succ]
      have hlpow : 2 ^ Nat.min (mindepth left) (mindepth right) ≤
          2 ^ mindepth left :=
        Nat.pow_le_pow_right (by omega) (Nat.min_le_left _ _)
      have hrpow : 2 ^ Nat.min (mindepth left) (mindepth right) ≤
          2 ^ mindepth right :=
        Nat.pow_le_pow_right (by omega) (Nat.min_le_right _ _)
      omega

theorem maxdepth_log_cardinal (s : tree X Info) (hne : s ≠ .Leaf) :
    Nat.log2 (cardinal s) < maxdepth s := by
  have hcard : 0 < cardinal s := by
    cases s with
    | Leaf => exact False.elim (hne rfl)
    | Node info left x right => simp [cardinal]
  exact (Nat.log2_lt (Nat.ne_of_gt hcard)).mpr (maxdepth_cardinal s)

theorem mindepth_log_cardinal (s : tree X Info) :
    mindepth s ≤ Nat.log2 (Nat.succ (cardinal s)) := by
  exact (Nat.le_log2 (by omega)).mpr (mindepth_cardinal s)

end tree

end CompCert4Lean.Lib.MSetGenTree
