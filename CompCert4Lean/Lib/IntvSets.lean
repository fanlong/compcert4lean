import CompCert4Lean.Lib.Coqlib

/-!
# Finite sets of integer intervals

This module translates the executable interface of `compcert.lib.IntvSets`.
The source's proof-bearing results are retained as exact proposition
descriptors for the later proof-migration phase.
-/

namespace CompCert4Lean.Lib.IntvSets

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

/-! A private raw representation used by the exported dependent set type. -/
namespace Aux

private inductive Raw : Type where
  | nil
  | cons (lo hi : Z) (tail : Raw)

private def In (x : Z) : Raw → Prop
  | .nil => False
  | .cons lo hi tail => (ZArith.BinInt.Z.le lo x ∧ ZArith.BinInt.Z.lt x hi) ∨ In x tail

private def add (L H : Z) : Raw → Raw
  | .nil => .cons L H .nil
  | .cons l h tail =>
      if ZArith.BinInt.Z.ltb h L then
        .cons l h (add L H tail)
      else if ZArith.BinInt.Z.ltb H l then
        .cons L H (.cons l h tail)
      else
        add (ZArith.BinInt.Z.min l L) (ZArith.BinInt.Z.max h H) tail

private def remove (L H : Z) : Raw → Raw
  | .nil => .nil
  | .cons l h tail =>
      if ZArith.BinInt.Z.ltb h L then
        .cons l h (remove L H tail)
      else if ZArith.BinInt.Z.ltb H l then
        .cons l h tail
      else if ZArith.BinInt.Z.ltb l L then
        if ZArith.BinInt.Z.ltb H h then
          .cons l L (.cons H h tail)
        else
          .cons l L (remove L H tail)
      else if ZArith.BinInt.Z.ltb H h then
        .cons H h tail
      else
        remove L H tail

private def contains (L H : Z) : Raw → Bool
  | .nil => false
  | .cons l h tail =>
      (ZArith.BinInt.Z.leb H h && ZArith.BinInt.Z.leb l L) ||
        contains L H tail

end Aux

namespace ISet

def t : Type := {r : Aux.Raw // True}

def In (x : Z) (s : t) : Prop := Aux.In x s.1

def empty : t := ⟨.nil, trivial⟩

def interval (l h : Z) : t :=
  if ZArith.BinInt.Z.ltb l h then
    ⟨.cons l h .nil, trivial⟩
  else
    empty

def add (l h : Z) (s : t) : t :=
  if ZArith.BinInt.Z.ltb l h then
    ⟨Aux.add l h s.1, trivial⟩
  else
    s

def remove (l h : Z) (s : t) : t :=
  if ZArith.BinInt.Z.ltb l h then
    ⟨Aux.remove l h s.1, trivial⟩
  else
    s

def contains (l h : Z) (s : t) : Bool :=
  if ZArith.BinInt.Z.ltb l h then
    Aux.contains l h s.1
  else
    true

def In_emptyStatement : Prop :=
  ∀ x : Z, ¬ In x empty

def In_intervalStatement : Prop :=
  ∀ x l h : Z, In x (interval l h) ↔
    (ZArith.BinInt.Z.le l x ∧ ZArith.BinInt.Z.lt x h)

def In_addStatement : Prop :=
  ∀ x l h : Z, ∀ s : t,
    In x (add l h s) ↔
      (ZArith.BinInt.Z.le l x ∧ ZArith.BinInt.Z.lt x h) ∨ In x s

def In_removeStatement : Prop :=
  ∀ x l h : Z, ∀ s : t,
    In x (remove l h s) ↔
      ¬ (ZArith.BinInt.Z.le l x ∧ ZArith.BinInt.Z.lt x h) ∧ In x s

def contains_specStatement : Prop :=
  ∀ l h : Z, ∀ s : t,
    contains l h s = true ↔
      ∀ x : Z,
        (ZArith.BinInt.Z.le l x ∧ ZArith.BinInt.Z.lt x h) → In x s

end ISet

end CompCert4Lean.Lib.IntvSets
