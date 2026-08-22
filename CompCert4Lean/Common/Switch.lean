import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Common.Values
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Maps
import CompCert4Lean.Lib.Integers

/-!
# Multi-way branches and comparison trees

This module translates the definition-bearing surface of CompCert's
`common/Switch.v`. Proof declarations assigned to later proof migration are
represented by exact proposition descriptors.
-/

namespace CompCert4Lean.Common.Switch

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private abbrev val := CompCert4Lean.Common.Values.val
private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev CCInt64 := CompCert4Lean.Lib.Integers.int64
private abbrev z0 : Z := Z0
private abbrev z1 : Z := Zpos xH
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zMod := ZArith.BinInt.Z.modulo
private abbrev zSucc := ZArith.BinInt.Z.succ
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev zGt := ZArith.BinInt.Z.gt

private abbrev zeq := CompCert4Lean.Lib.Coqlib.zeq
private abbrev zlt := CompCert4Lean.Lib.Coqlib.zlt
private abbrev zle := CompCert4Lean.Lib.Coqlib.zle
private abbrev list_length_z {A : Type} (l : List A) : Z :=
  CompCert4Lean.Lib.Coqlib.list_length_z l
private abbrev list_nth_z {A : Type} (l : List A) (n : Z) : Option A :=
  CompCert4Lean.Lib.Coqlib.list_nth_z l n

private def boolOfSumbool {P Q : Prop}
    (d : CompCert4Lean.Foundation.Logic.Support.Sumbool P Q) : Bool :=
  match d with
  | .left _ => true
  | .right _ => false

def table : Type := List (Z × Nat)

def switch_target (n : Z) (dfl : Nat) : table → Nat
  | [] => dfl
  | (key, action) :: rem =>
      match zeq n key with
      | .left _ => action
      | .right _ => switch_target n dfl rem

inductive switch_argument : Bool → val → Z → Prop where
  | of32 (i : CCInt) :
      switch_argument false (.Vint i) (CompCert4Lean.Lib.Integers.Int.unsigned i)
  | of64 (i : CCInt64) :
      switch_argument true (.Vlong i) (CompCert4Lean.Lib.Integers.Int64.unsigned i)

inductive comptree : Type where
  | CTaction (act : Nat)
  | CTifeq (key : Z) (act : Nat) (cne : comptree)
  | CTiflt (key : Z) (clt : comptree) (cge : comptree)
  | CTjumptable (ofs : Z) (sz : Z) (acts : List Nat) (cother : comptree)

export comptree (CTaction CTifeq CTiflt CTjumptable)

def comptree_match (modulus n : Z) : comptree → Option Nat
  | .CTaction act => some act
  | .CTifeq key act t =>
      match zeq n key with
      | .left _ => some act
      | .right _ => comptree_match modulus n t
  | .CTiflt key t1 t2 =>
      match zlt n key with
      | .left _ => comptree_match modulus n t1
      | .right _ => comptree_match modulus n t2
  | .CTjumptable ofs sz tbl t =>
      let delta := zMod (zSub n ofs) modulus
      match zlt delta sz with
      | .left _ => list_nth_z tbl (zMod delta CompCert4Lean.Lib.Integers.Int.modulus)
      | .right _ => comptree_match modulus n t

def split_lt (pivot : Z) : table → table × table
  | [] => ([], [])
  | (key, act) :: rem =>
      let (l, r) := split_lt pivot rem
      match zlt key pivot with
      | .left _ => ((key, act) :: l, r)
      | .right _ => (l, (key, act) :: r)

def split_eq (pivot : Z) : table → Option Nat × table
  | [] => (none, [])
  | (key, act) :: rem =>
      let (same, others) := split_eq pivot rem
      match zeq key pivot with
      | .left _ => (some act, others)
      | .right _ => (same, (key, act) :: others)

def split_between (modulus : Z) (dfl : Nat) (ofs sz : Z) :
    table → CompCert4Lean.Lib.Maps.ZMap.t Nat × table
  | [] => (CompCert4Lean.Lib.Maps.ZMap.init dfl, [])
  | (key, act) :: rem =>
      let (inside, outside) := split_between modulus dfl ofs sz rem
      match zlt (zMod (zSub key ofs) modulus) sz with
      | .left _ => (CompCert4Lean.Lib.Maps.ZMap.set key act inside, outside)
      | .right _ => (inside, (key, act) :: outside)

def refine_low_bound (v lo : Z) : Z :=
  match zeq v lo with
  | .left _ => zAdd lo z1
  | .right _ => lo

def refine_high_bound (v hi : Z) : Z :=
  match zeq v hi with
  | .left _ => zSub hi z1
  | .right _ => hi

def validate_jumptable (cases : CompCert4Lean.Lib.Maps.ZMap.t Nat) : List Nat → Z → Bool
  | [], _ => true
  | act :: rem, n =>
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Arith.PeanoNat.Nat.eqb
          act (CompCert4Lean.Lib.Maps.ZMap.get n cases) &&
        validate_jumptable cases rem (zSucc n)

def validate (modulus : Z) (default : Nat) (cases : table) :
    comptree → Z → Z → Bool
  | .CTaction act, lo, hi =>
      match cases with
      | [] =>
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.Arith.PeanoNat.Nat.eqb act default
      | (key1, act1) :: _ =>
          boolOfSumbool (zeq key1 lo) &&
            (boolOfSumbool (zeq lo hi) &&
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.Arith.PeanoNat.Nat.eqb act act1)
  | .CTifeq pivot act t, lo, hi =>
      boolOfSumbool (zle z0 pivot) &&
        (boolOfSumbool (zlt pivot modulus) &&
          match split_eq pivot cases with
          | (none, _) => false
          | (some act', others) =>
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.Arith.PeanoNat.Nat.eqb act act' &&
                validate modulus default others t
                  (refine_low_bound pivot lo) (refine_high_bound pivot hi))
  | .CTiflt pivot t1 t2, lo, hi =>
      boolOfSumbool (zle z0 pivot) &&
        (boolOfSumbool (zlt pivot modulus) &&
          match split_lt pivot cases with
          | (lcases, rcases) =>
              validate modulus default lcases t1 lo (zSub pivot z1) &&
                validate modulus default rcases t2 pivot hi)
  | .CTjumptable ofs sz tbl t, lo, hi =>
      let tblLen := list_length_z tbl
      boolOfSumbool (zle z0 ofs) &&
        (boolOfSumbool (zlt ofs modulus) &&
          (boolOfSumbool (zle z0 sz) &&
            (boolOfSumbool (zlt sz modulus) &&
              (boolOfSumbool (zle (zAdd ofs sz) modulus) &&
                (boolOfSumbool (zle sz tblLen) &&
                  (boolOfSumbool (zlt sz CompCert4Lean.Lib.Integers.Int.modulus) &&
                    match split_between modulus default ofs sz cases with
                    | (inside, outside) =>
                        validate_jumptable inside tbl ofs &&
                          validate modulus default outside t lo hi))))))

def validate_switch (modulus : Z) (default : Nat) (cases : table) (t : comptree) : Bool :=
  validate modulus default cases t z0 (zSub modulus z1)

inductive wf_comptree (modulus : Z) : comptree → Prop where
  | action (act : Nat) : wf_comptree modulus (.CTaction act)
  | ifeq (key : Z) (act : Nat) (cne : comptree) :
      zLe z0 key ∧ zLt key modulus →
      wf_comptree modulus cne →
      wf_comptree modulus (.CTifeq key act cne)
  | iflt (key : Z) (clt cge : comptree) :
      zLe z0 key ∧ zLt key modulus →
      wf_comptree modulus clt →
      wf_comptree modulus cge →
      wf_comptree modulus (.CTiflt key clt cge)
  | jumptable (ofs sz : Z) (acts : List Nat) (cother : comptree) :
      zLe z0 ofs ∧ zLt ofs modulus →
      zLe z0 sz ∧ zLt sz modulus →
      wf_comptree modulus cother →
      wf_comptree modulus (.CTjumptable ofs sz acts cother)

def validate_wfStatement : Prop :=
  ∀ (modulus : Z) (default : Nat) (t : comptree) (cases : table) (lo hi : Z),
    validate modulus default cases t lo hi = true → wf_comptree modulus t

def split_eq_propStatement : Prop :=
  ∀ (v : Z) (default : Nat) (n : Z) (cases : table)
      (optact : Option Nat) (cases' : table),
    split_eq n cases = (optact, cases') →
      switch_target v default cases =
        match zeq v n with
        | .left _ => match optact with | some act => act | none => default
        | .right _ => switch_target v default cases'

def split_lt_propStatement : Prop :=
  ∀ (v : Z) (default : Nat) (n : Z) (cases lcases rcases : table),
    split_lt n cases = (lcases, rcases) →
      switch_target v default cases =
        match zlt v n with
        | .left _ => switch_target v default lcases
        | .right _ => switch_target v default rcases

def split_between_propStatement : Prop :=
  ∀ (modulus v : Z) (default : Nat) (ofs sz : Z) (cases : table)
      (inside : CompCert4Lean.Lib.Maps.ZMap.t Nat) (outside : table),
    split_between modulus default ofs sz cases = (inside, outside) →
      switch_target v default cases =
        match zlt (zMod (zSub v ofs) modulus) sz with
        | .left _ => CompCert4Lean.Lib.Maps.ZMap.get v inside
        | .right _ => switch_target v default outside

def validate_jumptable_correct_recStatement : Prop :=
  ∀ (cases : CompCert4Lean.Lib.Maps.ZMap.t Nat) (tbl : List Nat) (base v : Z),
    validate_jumptable cases tbl base = true →
      zLe z0 v ∧ zLt v (list_length_z tbl) →
        list_nth_z tbl v =
          some (CompCert4Lean.Lib.Maps.ZMap.get (zAdd base v) cases)

def validate_jumptable_correctStatement : Prop :=
  ∀ modulus : Z, zGt modulus z0 →
    ∀ (cases : CompCert4Lean.Lib.Maps.ZMap.t Nat) (tbl : List Nat) (ofs v sz : Z),
      validate_jumptable cases tbl ofs = true →
      zLt (zMod (zSub v ofs) modulus) sz →
      zLe z0 sz →
      zLe z0 ofs →
      zLe (zAdd ofs sz) modulus →
      (zLe z0 v ∧ zLt v modulus) →
      zLe sz (list_length_z tbl) →
        list_nth_z tbl (zMod (zSub v ofs) modulus) =
          some (CompCert4Lean.Lib.Maps.ZMap.get v cases)

def validate_correct_recStatement : Prop :=
  ∀ modulus : Z, zGt modulus z0 →
    ∀ (default : Nat) (v : Z),
      (zLe z0 v ∧ zLt v modulus) →
      ∀ (t : comptree) (cases : table) (lo hi : Z),
        validate modulus default cases t lo hi = true →
        (zLe lo v ∧ zLe v hi) →
          comptree_match modulus v t = some (switch_target v default cases)

def table_tree_agree (modulus : Z) (default : Nat) (cases : table) (t : comptree) : Prop :=
  ∀ v : Z, zLe z0 v ∧ zLt v modulus →
    comptree_match modulus v t = some (switch_target v default cases)

def validate_switch_correctStatement : Prop :=
  ∀ modulus : Z, zGt modulus z0 →
    ∀ (default : Nat) (t : comptree) (cases : table),
      validate_switch modulus default cases t = true →
        wf_comptree modulus t ∧ table_tree_agree modulus default cases t

end CompCert4Lean.Common.Switch
