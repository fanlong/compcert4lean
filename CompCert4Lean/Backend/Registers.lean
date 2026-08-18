import CompCert4Lean.Common.Values
import CompCert4Lean.Lib.Maps

/-!
# Pseudo-registers and register states

This module is the checked definition-translation surface for
`backend/Registers.v`. Executable declarations are translated directly over
the source-shaped positive-number and applicative-map providers. Proof
declarations assigned to later proof migration are retained as exact
proposition descriptors.
-/

namespace CompCert4Lean.Backend.Registers

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values

def reg : Type := positive

instance : DecidableEq reg := by
  change DecidableEq positive
  exact inferInstance

namespace Reg

def eq (x y : reg) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) :=
  CompCert4Lean.Lib.Coqlib.peq x y

end Reg

namespace Regmap

abbrev Regmap (A : Type) : Type := CompCert4Lean.Lib.Maps.PMap.t A
abbrev elt : Type := CompCert4Lean.Lib.Maps.PMap.elt
abbrev t (A : Type) : Type := CompCert4Lean.Lib.Maps.PMap.t A
def elt_eq (x y : elt) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) :=
  CompCert4Lean.Lib.Coqlib.peq x y
abbrev init {A : Type} (x : A) : t A :=
  CompCert4Lean.Lib.Maps.PMap.init x
abbrev get {A : Type} (r : reg) (rs : t A) : A :=
  CompCert4Lean.Lib.Maps.PMap.get r rs
abbrev set {A : Type} (r : reg) (v : A) (rs : t A) : t A :=
  CompCert4Lean.Lib.Maps.PMap.set r v rs

def gi : Prop :=
  ∀ (A : Type) (i : reg) (x : A), get i (init x) = x

def gss : Prop :=
  ∀ (A : Type) (i : reg) (x : A) (m : t A),
    get i (set i x m) = x

def gso : Prop :=
  ∀ (A : Type) (i j : reg) (x : A) (m : t A),
    i ≠ j → get i (set j x m) = get i m

def gsspec : Prop :=
  ∀ (A : Type) (i j : reg) (x : A) (m : t A),
    get i (set j x m) =
      match CompCert4Lean.Lib.Coqlib.peq i j with
      | .left _ => x
      | .right _ => get i m

def gsident : Prop :=
  ∀ (A : Type) (i j : reg) (m : t A),
    get j (set i (get i m) m) = get j m

def map {A B : Type} (f : A → B) (m : t A) : t B :=
  (f m.1, CompCert4Lean.Lib.Maps.PTree.map1 f m.2)

def gmap : Prop :=
  ∀ (A B : Type) (f : A → B) (i : reg) (m : t A),
    get i (map f m) = f (get i m)

def set2 : Prop :=
  ∀ (A : Type) (i : elt) (x y : A) (m : t A),
    set i y (set i x m) = set i y m

end Regmap

namespace Regset

abbrev elt : Type := reg
abbrev t : Type := List elt
abbrev Regset : Type := t

def «X'» : Type := Unit

namespace X'

abbrev t : Type := elt
def eq (x y : t) : Prop := x = y
def lt (x y : t) : Prop := CompCert4Lean.Lib.Coqlib.Plt x y

end X'

def MSet : Type := Unit

namespace MSet
end MSet

def MF : Type := Unit

namespace MF
end MF

def E : Type := Unit

namespace E
end E

def In (x : elt) (s : t) : Prop := x ∈ s

def Equal (s s' : t) : Prop :=
  ∀ x, In x s ↔ In x s'

def Subset (s s' : t) : Prop :=
  ∀ x, In x s → In x s'

def Empty (s : t) : Prop :=
  ∀ x, ¬ In x s

def For_all (P : elt → Prop) (s : t) : Prop :=
  ∀ x, In x s → P x

def Exists (P : elt → Prop) (s : t) : Prop :=
  ∃ x, In x s ∧ P x

def empty : t := []

def is_empty : t → Bool
  | [] => true
  | _ :: _ => false

def mem : elt → t → Bool
  | _, [] => false
  | x, y :: ys =>
      match Reg.eq x y with
      | .left _ => true
      | .right _ => mem x ys

def add : elt → t → t
  | x, [] => [x]
  | x, y :: ys =>
      match PArith.BinPos.Pos.compare x y with
      | .Lt => x :: y :: ys
      | .Eq => y :: ys
      | .Gt => y :: add x ys

def singleton (x : elt) : t := [x]

def remove : elt → t → t
  | _, [] => []
  | x, y :: ys =>
      match PArith.BinPos.Pos.compare x y with
      | .Lt => y :: ys
      | .Eq => ys
      | .Gt => y :: remove x ys

def union (s s' : t) : t :=
  s.foldr add s'

def inter (s s' : t) : t :=
  s.filter (fun x => mem x s')

def diff (s s' : t) : t :=
  s.filter (fun x => !(mem x s'))

def eq (s s' : t) : Prop :=
  s = s'

private def listEq : (s s' : t) →
    CompCert4Lean.Foundation.Logic.Support.Sumbool (s = s') (s ≠ s')
  | [], [] => .left rfl
  | [], _ :: _ => .right (by intro h; cases h)
  | _ :: _, [] => .right (by intro h; cases h)
  | x :: xs, y :: ys =>
      match Reg.eq x y with
      | .left hxy =>
          match listEq xs ys with
          | .left hxs => .left (by cases hxy; cases hxs; rfl)
          | .right hxs => .right (by intro h; cases h; exact hxs rfl)
      | .right hxy => .right (by intro h; cases h; exact hxy rfl)

def eq_dec (s s' : t) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (eq s s') (¬ eq s s') :=
  listEq s s'

def equal (s s' : t) : Bool :=
  match eq_dec s s' with
  | .left _ => true
  | .right _ => false

def subset (s s' : t) : Bool :=
  s.all (fun x => mem x s')

def fold {A : Type} (f : elt → A → A) (s : t) (i : A) : A :=
  s.foldl (fun a e => f e a) i

def for_all (f : elt → Bool) (s : t) : Bool :=
  s.all f

def exists_ (f : elt → Bool) (s : t) : Bool :=
  s.any f

def filter (f : elt → Bool) (s : t) : t :=
  s.filter f

private def partitionAux (f : elt → Bool) : t → t × t
  | [] => ([], [])
  | x :: xs =>
      let rest := partitionAux f xs
      if f x then (x :: rest.1, rest.2) else (rest.1, x :: rest.2)

def partition (f : elt → Bool) (s : t) : t × t :=
  partitionAux f s

def cardinal (s : t) : Nat :=
  s.length

def elements (s : t) : List elt :=
  s

def choose : t → Option elt
  | [] => none
  | x :: _ => some x

def lt (s s' : t) : Prop :=
  s.length < s'.length

def min_elt : t → Option elt
  | [] => none
  | x :: _ => some x

def max_elt : t → Option elt
  | [] => none
  | [x] => some x
  | _ :: xs => max_elt xs

private def CompatBool (f : elt → Bool) : Prop :=
  ∀ x y, x = y → f x = f y

def In_1 : Prop :=
  ∀ (s : t) (x y : elt), x = y → In x s → In y s

def eq_refl : Prop :=
  ∀ s : t, eq s s

def eq_sym : Prop :=
  ∀ s s' : t, eq s s' → eq s' s

def eq_trans : Prop :=
  ∀ s s' s'' : t, eq s s' → eq s' s'' → eq s s''

def mem_1 : Prop :=
  ∀ (s : t) (x : elt), In x s → mem x s = true

def mem_2 : Prop :=
  ∀ (s : t) (x : elt), mem x s = true → In x s

def equal_1 : Prop :=
  ∀ s s' : t, Equal s s' → equal s s' = true

def equal_2 : Prop :=
  ∀ s s' : t, equal s s' = true → Equal s s'

def subset_1 : Prop :=
  ∀ s s' : t, Subset s s' → subset s s' = true

def subset_2 : Prop :=
  ∀ s s' : t, subset s s' = true → Subset s s'

def empty_1 : Prop :=
  Empty empty

def is_empty_1 : Prop :=
  ∀ s : t, Empty s → is_empty s = true

def is_empty_2 : Prop :=
  ∀ s : t, is_empty s = true → Empty s

def add_1 : Prop :=
  ∀ (s : t) (x y : elt), x = y → In y (add x s)

def add_2 : Prop :=
  ∀ (s : t) (x y : elt), In y s → In y (add x s)

def add_3 : Prop :=
  ∀ (s : t) (x y : elt), x ≠ y → In y (add x s) → In y s

def remove_1 : Prop :=
  ∀ (s : t) (x y : elt), x = y → ¬ In y (remove x s)

def remove_2 : Prop :=
  ∀ (s : t) (x y : elt), x ≠ y → In y s → In y (remove x s)

def remove_3 : Prop :=
  ∀ (s : t) (x y : elt), In y (remove x s) → In y s

def union_1 : Prop :=
  ∀ (s s' : t) (x : elt), In x (union s s') → In x s ∨ In x s'

def union_2 : Prop :=
  ∀ (s s' : t) (x : elt), In x s → In x (union s s')

def union_3 : Prop :=
  ∀ (s s' : t) (x : elt), In x s' → In x (union s s')

def inter_1 : Prop :=
  ∀ (s s' : t) (x : elt), In x (inter s s') → In x s

def inter_2 : Prop :=
  ∀ (s s' : t) (x : elt), In x (inter s s') → In x s'

def inter_3 : Prop :=
  ∀ (s s' : t) (x : elt), In x s → In x s' → In x (inter s s')

def diff_1 : Prop :=
  ∀ (s s' : t) (x : elt), In x (diff s s') → In x s

def diff_2 : Prop :=
  ∀ (s s' : t) (x : elt), In x (diff s s') → ¬ In x s'

def diff_3 : Prop :=
  ∀ (s s' : t) (x : elt), In x s → ¬ In x s' → In x (diff s s')

def singleton_1 : Prop :=
  ∀ x y : elt, In y (singleton x) → x = y

def singleton_2 : Prop :=
  ∀ x y : elt, x = y → In y (singleton x)

def fold_1 : Prop :=
  ∀ (s : t) (A : Type) (i : A) (f : elt → A → A),
    fold f s i = List.foldl (fun a e => f e a) i (elements s)

def cardinal_1 : Prop :=
  ∀ s : t, cardinal s = (elements s).length

def filter_1 : Prop :=
  ∀ (s : t) (x : elt) (f : elt → Bool),
    CompatBool f → In x (filter f s) → In x s

def filter_2 : Prop :=
  ∀ (s : t) (x : elt) (f : elt → Bool),
    CompatBool f → In x (filter f s) → f x = true

def filter_3 : Prop :=
  ∀ (s : t) (x : elt) (f : elt → Bool),
    CompatBool f → In x s → f x = true → In x (filter f s)

def for_all_1 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool f → For_all (fun x => f x = true) s → for_all f s = true

def for_all_2 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool f → for_all f s = true → For_all (fun x => f x = true) s

def exists_1 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool f → Exists (fun x => f x = true) s → exists_ f s = true

def exists_2 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool f → exists_ f s = true → Exists (fun x => f x = true) s

def partition_1 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool f → Equal (partition f s).1 (filter f s)

def partition_2 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool f → Equal (partition f s).2 (filter (fun x => !(f x)) s)

def choose_1 : Prop :=
  ∀ (s : t) (x : elt), choose s = some x → In x s

def choose_2 : Prop :=
  ∀ s : t, choose s = none → Empty s

def elements_1 : Prop :=
  ∀ (s : t) (x : elt), In x s → x ∈ elements s

def elements_2 : Prop :=
  ∀ (s : t) (x : elt), x ∈ elements s → In x s

def elements_3w : Prop :=
  ∀ s : t, (elements s).Nodup

def min_elt_1 : Prop :=
  ∀ (s : t) (x : elt), min_elt s = some x → In x s

def min_elt_2 : Prop :=
  ∀ (s : t) (x y : elt),
    min_elt s = some x → In y s → ¬ CompCert4Lean.Lib.Coqlib.Plt y x

def min_elt_3 : Prop :=
  ∀ s : t, min_elt s = none → Empty s

def max_elt_1 : Prop :=
  ∀ (s : t) (x : elt), max_elt s = some x → In x s

def max_elt_2 : Prop :=
  ∀ (s : t) (x y : elt),
    max_elt s = some x → In y s → ¬ CompCert4Lean.Lib.Coqlib.Plt x y

def max_elt_3 : Prop :=
  ∀ s : t, max_elt s = none → Empty s

def elements_3 : Prop :=
  ∀ s : t, (elements s).Pairwise CompCert4Lean.Lib.Coqlib.Plt

def choose_3 : Prop :=
  ∀ (s s' : t) (x y : elt),
    choose s = some x → choose s' = some y → Equal s s' → x = y

def lt_trans : Prop :=
  ∀ s s' s'' : t, lt s s' → lt s' s'' → lt s s''

def lt_not_eq : Prop :=
  ∀ s s' : t, lt s s' → ¬ eq s s'

def compare : Type :=
  ∀ s s' : t,
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.Compare
      lt eq s s'

end Regset

def regmap_optget {A : Type}
    (or : Option reg) (dfl : A) (rs : Regmap.t A) : A :=
  match or with
  | none => dfl
  | some r => Regmap.get r rs

def regmap_setres {A : Type}
    (res : builtin_res reg) (v : A) (rs : Regmap.t A) : Regmap.t A :=
  match res with
  | .BR r => Regmap.set r v rs
  | _ => rs

def regs_lessdef (rs1 rs2 : Regmap.t val) : Prop :=
  ∀ r, Val.lessdef (Regmap.get r rs1) (Regmap.get r rs2)

def regs_lessdef_regsStatement : Prop :=
  ∀ (rs1 rs2 : Regmap.t val), regs_lessdef rs1 rs2 →
    ∀ rl : List reg,
      Val.lessdef_list
        (List.map (fun r => Regmap.get r rs1) rl)
        (List.map (fun r => Regmap.get r rs2) rl)

def set_reg_lessdefStatement : Prop :=
  ∀ (r : reg) (v1 v2 : val) (rs1 rs2 : Regmap.t val),
    Val.lessdef v1 v2 → regs_lessdef rs1 rs2 →
      regs_lessdef (Regmap.set r v1 rs1) (Regmap.set r v2 rs2)

def set_res_lessdefStatement : Prop :=
  ∀ (res : builtin_res reg) (v1 v2 : val) (rs1 rs2 : Regmap.t val),
    Val.lessdef v1 v2 → regs_lessdef rs1 rs2 →
      regs_lessdef
        (regmap_setres res v1 rs1)
        (regmap_setres res v2 rs2)

end CompCert4Lean.Backend.Registers
