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
  | switch_argument_32 (i : CCInt) :
      switch_argument false (.Vint i) (CompCert4Lean.Lib.Integers.Int.unsigned i)
  | switch_argument_64 (i : CCInt64) :
      switch_argument true (.Vlong i) (CompCert4Lean.Lib.Integers.Int64.unsigned i)

export switch_argument (switch_argument_32 switch_argument_64)

inductive comptree : Type where
  | CTaction (act : Nat)
  | CTifeq (key : Z) (act : Nat) (cne : comptree)
  | CTiflt (key : Z) (clt : comptree) (cge : comptree)
  | CTjumptable (ofs : Z) (sz : Z) (acts : List Nat) (cother : comptree)

export comptree (CTaction CTifeq CTiflt CTjumptable)

abbrev comptree_ind
    (P : comptree → Prop)
    (hCTaction : ∀ act, P (.CTaction act))
    (hCTifeq : ∀ key act cne, P cne → P (.CTifeq key act cne))
    (hCTiflt : ∀ key clt, P clt → ∀ cge, P cge → P (.CTiflt key clt cge))
    (hCTjumptable : ∀ ofs sz acts cother, P cother →
      P (.CTjumptable ofs sz acts cother))
    (t : comptree) : P t :=
  comptree.rec hCTaction hCTifeq
    (fun key clt cge hclt hcge => hCTiflt key clt hclt cge hcge)
    hCTjumptable t

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

inductive wf_comptree : Z → comptree → Prop where
  | wf_action (modulus : Z) (act : Nat) : wf_comptree modulus (.CTaction act)
  | wf_ifeq (modulus key : Z) (act : Nat) (cne : comptree) :
      zLe z0 key ∧ zLt key modulus →
      wf_comptree modulus cne →
      wf_comptree modulus (.CTifeq key act cne)
  | wf_iflt (modulus key : Z) (clt cge : comptree) :
      zLe z0 key ∧ zLt key modulus →
      wf_comptree modulus clt →
      wf_comptree modulus cge →
      wf_comptree modulus (.CTiflt key clt cge)
  | wf_jumptable (modulus ofs sz : Z) (acts : List Nat) (cother : comptree) :
      zLe z0 ofs ∧ zLt ofs modulus →
      zLe z0 sz ∧ zLt sz modulus →
      wf_comptree modulus cother →
      wf_comptree modulus (.CTjumptable ofs sz acts cother)

export wf_comptree (wf_action wf_ifeq wf_iflt wf_jumptable)

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

namespace CompCert4Lean.Common.Switch

theorem validate_wf : validate_wfStatement := by
  intro modulus default t cases lo hi h
  induction t generalizing cases lo hi with
  | CTaction act =>
      exact wf_action modulus act
  | CTifeq key act cne ih =>
      simp only [validate] at h
      have hkey0 : zLe z0 key := by
        cases hz : zle z0 key with
        | left hp => exact hp
        | right hp =>
            have : boolOfSumbool (zle z0 key) = false := by simp [hz, boolOfSumbool]
            have hf : False := by simpa [this] using h
            exact hf.elim
      have hkeymod : zLt key modulus := by
        cases hz : zlt key modulus with
        | left hp => exact hp
        | right hp =>
            have : boolOfSumbool (zlt key modulus) = false := by simp [hz, boolOfSumbool]
            have hf : False := by simpa [this] using h
            exact hf.elim
      cases hs : split_eq key cases with
      | mk opt others =>
          cases opt with
          | none => simp [validate, hs] at h
          | some act' =>
              have hv : validate modulus default others cne
                  (refine_low_bound key lo) (refine_high_bound key hi) = true := by
                simp [validate, hs] at h
                exact h.2.2.2
              exact wf_ifeq modulus key act cne ⟨hkey0, hkeymod⟩ (ih others _ _ hv)
  | CTiflt key clt cge ihl ihr =>
      simp only [validate] at h
      have hkey0 : zLe z0 key := by
        cases hz : zle z0 key with
        | left hp => exact hp
        | right hp =>
            have hh : False := by simpa [boolOfSumbool, hz] using h
            exact hh.elim
      have hkeymod : zLt key modulus := by
        cases hz : zlt key modulus with
        | left hp => exact hp
        | right hp =>
            have hh : False := by simpa [boolOfSumbool, hz] using h
            exact hh.elim
      cases hs : split_lt key cases with
      | mk l r =>
          have hl : validate modulus default l clt lo (zSub key z1) = true := by
            simp only [Bool.and_eq_true] at h
            rw [hs] at h
            exact h.2.2.1
          have hr : validate modulus default r cge key hi = true := by
            simp only [Bool.and_eq_true] at h
            rw [hs] at h
            exact h.2.2.2
          exact wf_iflt modulus key clt cge ⟨hkey0, hkeymod⟩
            (ihl l lo (zSub key z1) hl) (ihr r key hi hr)
  | CTjumptable ofs sz acts cother ih =>
      simp only [validate] at h
      have hofs0 : zLe z0 ofs := by
        cases hz : zle z0 ofs with
        | left hp => exact hp
        | right hp =>
            have hh : False := by simpa [boolOfSumbool, hz] using h
            exact hh.elim
      have hofsmod : zLt ofs modulus := by
        cases hz : zlt ofs modulus with
        | left hp => exact hp
        | right hp =>
            have hh : False := by simpa [boolOfSumbool, hz] using h
            exact hh.elim
      have hsz0 : zLe z0 sz := by
        cases hz : zle z0 sz with
        | left hp => exact hp
        | right hp =>
            have hh : False := by simpa [boolOfSumbool, hz] using h
            exact hh.elim
      have hszmod : zLt sz modulus := by
        cases hz : zlt sz modulus with
        | left hp => exact hp
        | right hp =>
            have hh : False := by simpa [boolOfSumbool, hz] using h
            exact hh.elim
      cases hs : split_between modulus default ofs sz cases with
      | mk inside outside =>
          simp only [Bool.and_eq_true] at h
          rw [hs] at h
          have hc : validate modulus default outside cother lo hi = true := by
            exact h.2.2.2.2.2.2.2.2
          exact wf_jumptable modulus ofs sz acts cother
            ⟨hofs0, hofsmod⟩ ⟨hsz0, hszmod⟩ (ih outside lo hi hc)

theorem split_eq_prop : split_eq_propStatement := by
  intro v default n cases
  induction cases with
  | nil =>
      intro optact cases' h
      simp [split_eq] at h
      cases h
      cases hz : zeq v n with
      | left hv => simp [switch_target, hz]
      | right hv => simp [switch_target, hz]
  | cons p rem ih =>
      rcases p with ⟨key, act⟩
      intro optact cases' h
      cases hs : split_eq n rem with
      | mk same others =>
          have hi := ih same others hs
          cases hk : zeq key n with
          | left hkn =>
              subst key
              simp [split_eq, hs, hk] at h
              rcases h with ⟨rfl, rfl⟩
              cases hv : zeq v n with
              | left hvn => simp [switch_target, hv]
              | right hvn =>
                  simp [switch_target, hv, hi]
          | right hkn =>
              simp [split_eq, hs, hk] at h
              rcases h with ⟨rfl, rfl⟩
              cases hv : zeq v n with
              | left hvn =>
                  cases hvk : zeq v key with
                  | left hvk' =>
                      have : False := hkn (hvk'.symm.trans hvn)
                      exact this.elim
                  | right hvk' =>
                      simp [switch_target, hv, hvk, hi]
              | right hvn =>
                  cases hvk : zeq v key with
                  | left hvk' => simp [switch_target, hv, hvk]
                  | right hvk' => simp [switch_target, hv, hvk, hi]

theorem split_lt_prop : split_lt_propStatement := by
  intro v default n cases
  induction cases with
  | nil =>
      intro lcases rcases h
      simp [split_lt] at h
      cases h
      cases hv : zlt v n with
      | left hvn => simp [switch_target, hv]
      | right hvn => simp [switch_target, hv]
  | cons p rem ih =>
      rcases p with ⟨key, act⟩
      intro lcases rcases h
      cases hs : split_lt n rem with
      | mk l r =>
          have hi := ih l r hs
          cases hk : zlt key n with
          | left hkn =>
              simp [split_lt, hs, hk] at h
              rcases h with ⟨rfl, rfl⟩
              cases hvn : zlt v n with
              | left hvn' =>
                  cases hvk : zeq v key with
                  | left hvk' => simp [switch_target, hvn, hvk]
                  | right hvk' =>
                      cases hvl : zlt v key with
                      | left hvl' =>
                          simp [switch_target, hvn, hvk, hvl, hi]
                      | right hvl' =>
                          simp [switch_target, hvn, hvk, hi]
              | right hvn' =>
                  cases hvk : zeq v key with
                  | left hvk' =>
                      subst v
                      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ key <
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n at hkn
                      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n ≤
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ key at hvn'
                      have : False := by omega
                      exact this.elim
                  | right hvk' =>
                      simp [switch_target, hvn, hvk, hi]
          | right hkn =>
              simp [split_lt, hs, hk] at h
              rcases h with ⟨rfl, rfl⟩
              cases hvn : zlt v n with
              | left hvn' =>
                  cases hvk : zeq v key with
                  | left hvk' =>
                      subst v
                      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ key <
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n at hvn'
                      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n ≤
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ key at hkn
                      have : False := by omega
                      exact this.elim
                  | right hvk' =>
                      simp [switch_target, hvn, hvk, hi]
              | right hvn' =>
                  cases hvk : zeq v key with
                  | left hvk' => simp [switch_target, hvn, hvk]
                  | right hvk' =>
                      simp [switch_target, hvn, hvk, hi]

private theorem zmap_get_set {A : Type}
    (i j : CompCert4Lean.Lib.Maps.ZMap.elt) (x : A)
    (m : CompCert4Lean.Lib.Maps.ZMap.t A) :
    CompCert4Lean.Lib.Maps.ZMap.get i
        (CompCert4Lean.Lib.Maps.ZMap.set j x m) =
    match CompCert4Lean.Lib.Maps.ZMap.elt_eq i j with
      | .left _ => x
      | .right _ => CompCert4Lean.Lib.Maps.ZMap.get i m := by
  rcases m with ⟨mdefault, mtree⟩
  by_cases hij : i = j
  · subst j
    simp only [CompCert4Lean.Lib.Maps.ZMap.get, CompCert4Lean.Lib.Maps.ZMap.set,
      CompCert4Lean.Lib.Maps.PMap.get, CompCert4Lean.Lib.Maps.PMap.set]
    have hg := CompCert4Lean.Lib.Maps.PTree.getSet_equation
      (A := A) (CompCert4Lean.Lib.Maps.ZIndexed.index i)
      (CompCert4Lean.Lib.Maps.ZIndexed.index i) x mtree
    rw [hg]
    cases heq : CompCert4Lean.Lib.Maps.ZMap.elt_eq i i with
    | left _ => simp [heq]
    | right hne => exact (hne rfl).elim
  · simp [CompCert4Lean.Lib.Maps.ZMap.get, CompCert4Lean.Lib.Maps.ZMap.set,
      CompCert4Lean.Lib.Maps.PMap.get, CompCert4Lean.Lib.Maps.PMap.set]
    have hg := CompCert4Lean.Lib.Maps.PTree.getSet_equation
      (A := A) (CompCert4Lean.Lib.Maps.ZIndexed.index i)
      (CompCert4Lean.Lib.Maps.ZIndexed.index j) x mtree
    rw [hg]
    cases heq : CompCert4Lean.Lib.Maps.ZMap.elt_eq i j with
    | left heq' => exact (hij heq').elim
    | right _ =>
        have hidx : CompCert4Lean.Lib.Maps.ZIndexed.index i ≠
            CompCert4Lean.Lib.Maps.ZIndexed.index j := by
          intro hidx
          exact hij (CompCert4Lean.Lib.Maps.ZIndexed.index_inj i j hidx)
        simp [hidx, heq]

theorem split_between_prop : split_between_propStatement := by
  intro modulus v default ofs sz cases
  induction cases with
  | nil =>
      intro inside outside h
      simp [split_between] at h
      cases h
      cases hz : zlt (zMod (zSub v ofs) modulus) sz with
      | left hz' =>
          simp [switch_target, hz]
          rfl
      | right hz' => simp [switch_target, hz]
  | cons p rem ih =>
      rcases p with ⟨key, act⟩
      intro inside outside h
      cases hs : split_between modulus default ofs sz rem with
      | mk ins outs =>
          have hi := ih ins outs hs
          cases hk : zlt (zMod (zSub key ofs) modulus) sz with
          | left hkin =>
              simp [split_between, hs, hk] at h
              rcases h with ⟨rfl, rfl⟩
              cases hz : zlt (zMod (zSub v ofs) modulus) sz with
              | left hzv =>
                  cases hvk : zeq v key with
                  | left hvk' =>
                      subst v
                      simp only [hz]
                      have hset := zmap_get_set (A := Nat) key key act ins
                      rw [hset]
                      cases heq : CompCert4Lean.Lib.Maps.ZMap.elt_eq key key with
                      | left _ => simp [switch_target, heq, hvk]
                      | right hne => exact (hne rfl).elim
                  | right hvk' =>
                      simp only [hz]
                      have hset := zmap_get_set (A := Nat) v key act ins
                      rw [hset]
                      cases heq : CompCert4Lean.Lib.Maps.ZMap.elt_eq v key with
                      | left heq' => exact (hvk' heq').elim
                      | right _ => simp [switch_target, hz, heq, hvk, hi]
              | right hzv =>
                  cases hvk : zeq v key with
                  | left hvk' =>
                      subst v
                      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                        (zMod (zSub key ofs) modulus) <
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ sz at hkin
                      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ sz ≤
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                          (zMod (zSub key ofs) modulus) at hzv
                      exact (Int.not_lt_of_ge hzv hkin).elim
                  | right hvk' =>
                      simp [switch_target, hz, hvk, zmap_get_set, hi]
          | right hkout =>
              simp [split_between, hs, hk] at h
              rcases h with ⟨rfl, rfl⟩
              cases hz : zlt (zMod (zSub v ofs) modulus) sz with
              | left hzv =>
                  cases hvk : zeq v key with
                  | left hvk' =>
                      subst v
                      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                        (zMod (zSub key ofs) modulus) <
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ sz at hzv
                      change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ sz ≤
                        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
                          (zMod (zSub key ofs) modulus) at hkout
                      exact (Int.not_lt_of_ge hkout hzv).elim
                  | right hvk' => simp [switch_target, hz, hvk, hi]
              | right hzv =>
                  cases hvk : zeq v key with
                  | left hvk' => simp [switch_target, hz, hvk]
                  | right hvk' => simp [switch_target, hz, hvk, hi]

end CompCert4Lean.Common.Switch

namespace CompCert4Lean.Common.Switch

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

 theorem validate_jumptable_correct_rec : validate_jumptable_correct_recStatement := by
  intro cases tbl
  have hzero : intOfZ z0 = 0 := by rfl
  have hone : intOfZ z1 = 1 := by rfl
  induction tbl with
  | nil =>
      intro base v hv hbound
      rcases hbound with ⟨hv0, hvlen⟩
      change intOfZ v < 0 at hvlen
      change 0 ≤ intOfZ v at hv0
      omega
  | cons hd tl ih =>
      intro base v hv hbound
      simp only [validate_jumptable, Bool.and_eq_true] at hv
      rcases hbound with ⟨hv0, hvlen⟩
      have hlen := CompCert4Lean.Lib.Coqlib.list_length_z_cons Nat hd tl
      have hvlen' : zLt v (zAdd (list_length_z tl) z1) := by
        change zLt v (CompCert4Lean.Lib.Coqlib.list_length_z (hd :: tl)) at hvlen
        rw [hlen] at hvlen
        exact hvlen
      cases hz : zeq v z0 with
      | left hvz =>
          subst v
          simp only [CompCert4Lean.Lib.Coqlib.list_nth_z, hz]
          have hadd : zAdd base z0 = base := by
            apply intOfZ_injective
            simp [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt, hzero]
          rw [hadd]
          have heq := (CompCert4Lean.Foundation.Numbers.Rocq.Coq.Arith.PeanoNat.Nat.eqb_eq
            hd (CompCert4Lean.Lib.Maps.ZMap.get base cases)).mp hv.1
          exact heq ▸ rfl
      | right hvz =>
          simp only [CompCert4Lean.Lib.Coqlib.list_nth_z, hz]
          have hvlt : zLt z0 v := by
            change 0 < intOfZ v
            change 0 ≤ intOfZ v at hv0
            have hvne : intOfZ v ≠ 0 := by
              intro he
              apply hvz
              apply intOfZ_injective
              simpa [hzero] using he
            omega
          have hvpred0 : zLe z0 (ZArith.BinInt.Z.pred v) :=
            (ZArith.BinInt.Z.lt_le_pred z0 v).mp hvlt
          have hvle : zLe v (list_length_z tl) := by
            exact (ZArith.BinInt.Z.lt_succ_r v (list_length_z tl)).mp hvlen'
          have hvpredlen : zLt (ZArith.BinInt.Z.pred v) (list_length_z tl) :=
            (ZArith.BinInt.Z.lt_pred_le v (list_length_z tl)).mpr hvle
          have hi := ih (zSucc base) (ZArith.BinInt.Z.pred v) hv.2
            ⟨hvpred0, hvpredlen⟩
          have hadd : zAdd (zSucc base) (ZArith.BinInt.Z.pred v) = zAdd base v := by
            apply intOfZ_injective
            simp only [zAdd, zSucc, ZArith.BinInt.Z.succ, ZArith.BinInt.Z.add,
              ZArith.BinInt.Z.pred, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
            simp [hzero, hone] at *
            omega
          rw [hadd] at hi
          exact hi

end CompCert4Lean.Common.Switch

namespace CompCert4Lean.Common.Switch

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem validate_jumptable_correct : validate_jumptable_correctStatement := by
  intro modulus hmodpos cases tbl ofs v sz hvalid hindex hsz hofs hsum hv hlen
  have hrange := ZArith.BinInt.Z.modulo_range (zSub v ofs) modulus hmodpos
  have hbound : zLe z0 (zMod (zSub v ofs) modulus) ∧
      zLt (zMod (zSub v ofs) modulus) (list_length_z tbl) := by
    refine ⟨hrange.1, ?_⟩
    change intOfZ (zMod (zSub v ofs) modulus) < intOfZ (list_length_z tbl)
    change intOfZ (zMod (zSub v ofs) modulus) < intOfZ sz at hindex
    change intOfZ sz ≤ intOfZ (list_length_z tbl) at hlen
    omega
  have hsmall : zMod (zSub v ofs) modulus = zSub v ofs := by
    change 0 ≤ intOfZ sz at hsz
    change 0 ≤ intOfZ ofs at hofs
    change intOfZ (zAdd ofs sz) ≤ intOfZ modulus at hsum
    simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hsum
    change 0 ≤ intOfZ v ∧ intOfZ v < intOfZ modulus at hv
    by_cases hle : intOfZ ofs ≤ intOfZ v
    · apply ZArith.BinInt.Z.mod_small
      change 0 ≤ intOfZ (zSub v ofs) ∧ intOfZ (zSub v ofs) < intOfZ modulus
      simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      omega
    · have hone : ZArith.BinInt.Z.mul z1 modulus = modulus := by
        apply intOfZ_injective
        simp only [ZArith.BinInt.Z.mul, intOfZ_zOfInt]
        change 1 * intOfZ modulus = intOfZ modulus
        exact Int.one_mul _
      have hshift : zMod (zAdd (zSub v ofs) modulus) modulus =
          zMod (zSub v ofs) modulus := by
        simpa only [hone] using ZArith.BinInt.Z.modulo_add_mul (zSub v ofs) z1 modulus
      have hshiftSmall : zMod (zAdd (zSub v ofs) modulus) modulus =
          zAdd (zSub v ofs) modulus := by
        apply ZArith.BinInt.Z.mod_small
        change 0 ≤ intOfZ (zAdd (zSub v ofs) modulus) ∧
          intOfZ (zAdd (zSub v ofs) modulus) < intOfZ modulus
        simp only [zAdd, zSub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
          intOfZ_zOfInt]
        omega
      rw [← hshift, hshiftSmall] at hindex
      change intOfZ (zAdd (zSub v ofs) modulus) < intOfZ sz at hindex
      simp only [zAdd, zSub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub,
        intOfZ_zOfInt] at hindex
      omega
  have hbase : zAdd ofs (zMod (zSub v ofs) modulus) = v := by
    rw [hsmall]
    apply intOfZ_injective
    simp only [zAdd, zSub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    omega
  have hresult := validate_jumptable_correct_rec cases tbl ofs
    (zMod (zSub v ofs) modulus) hvalid hbound
  rw [hbase] at hresult
  exact hresult

end CompCert4Lean.Common.Switch
