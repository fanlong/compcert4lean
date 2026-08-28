import CompCert4Lean.Backend.LTL
import CompCert4Lean.Lib.UnionFind

/-!
# Branch tunneling

Definition-bearing translation of CompCert's `backend/Tunneling.v`.
-/

namespace CompCert4Lean.Backend.Tunneling

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.LTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

namespace PTreeMap

private theorem getEmpty (A : Type) (x : positive) :
    PTree.get x (PTree.empty A) = none := by
  cases x <;> rfl

private theorem getSet0 (A : Type) (x y : positive) (v : A) :
    PTree.get' x (PTree.set0 y v) = if h : x = y then some v else none := by
  induction x generalizing y with
  | xH => cases y <;> simp [PTree.set0, PTree.get']
  | xO x ih =>
      cases y with
      | xH => simp [PTree.set0, PTree.get']
      | xO y => simp [PTree.set0, PTree.get', ih]
      | xI y => simp [PTree.set0, PTree.get']
  | xI x ih =>
      cases y with
      | xH => simp [PTree.set0, PTree.get']
      | xO y => simp [PTree.set0, PTree.get']
      | xI y => simp [PTree.set0, PTree.get', ih]

private theorem getSet' (A : Type) (x y : positive) (v : A)
    (m : PTree.tree' A) :
    PTree.get' x (PTree.set' y v m) =
      if h : x = y then some v else PTree.get' x m := by
  induction x generalizing y m with
  | xH => cases y <;> cases m <;> simp [PTree.set', PTree.get']
  | xO x ih =>
      cases y with
      | xH => cases m <;> simp [PTree.set', PTree.get']
      | xO y =>
          cases m <;> simp [PTree.set', PTree.get', ih, getSet0]
      | xI y =>
          cases m <;> simp [PTree.set', PTree.get', getSet0]
  | xI x ih =>
      cases y with
      | xH => cases m <;> simp [PTree.set', PTree.get']
      | xO y =>
          cases m <;> simp [PTree.set', PTree.get', getSet0]
      | xI y =>
          cases m <;> simp [PTree.set', PTree.get', ih, getSet0]

private theorem getSet (A : Type) (x y : positive) (v : A)
    (m : PTree.t A) :
    PTree.get x (PTree.set y v m) =
      if h : x = y then some v else PTree.get x m := by
  cases m with
  | Empty => simpa [PTree.get, PTree.set] using getSet0 A x y v
  | Nodes m => simpa [PTree.get, PTree.set] using getSet' A x y v m

private def adapter : CompCert4Lean.Lib.UnionFind.MAP where
  elt := positive
  elt_eq := PTree.elt_eq
  t := PTree.t
  empty := fun A => PTree.empty A
  get := fun _ => PTree.get
  set := fun _ => PTree.set
  gempty := fun A x => getEmpty A x
  gsspec := by
    intro A x y v m
    rw [getSet]
    cases hxy : PTree.elt_eq x y with
    | left h =>
        by_cases heq : x = y
        · simp [heq]
        · exact (heq h).elim
    | right h =>
        by_cases heq : x = y
        · exact (h heq).elim
        · simp [heq]

end PTreeMap

/-! ## Generated `UnionFind.UF(PTree)` surface -/

namespace U

private abbrev M := PTreeMap.adapter

def U : Type := Unit

abbrev elt : Type := positive

def elt_eq (x y : elt) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) :=
  PTree.elt_eq x y

abbrev t : Type := CompCert4Lean.Lib.UnionFind.UF.t M

def repr : t → elt → elt := CompCert4Lean.Lib.UnionFind.UF.repr M

def repr_canonical : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.repr_canonicalStatement M

def sameclass : t → elt → elt → Prop :=
  CompCert4Lean.Lib.UnionFind.UF.sameclass M

def sameclass_refl : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.sameclass_reflStatement M
def sameclass_sym : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.sameclass_symStatement M
def sameclass_trans : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.sameclass_transStatement M
def sameclass_repr : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.sameclass_reprStatement M

def empty : t := CompCert4Lean.Lib.UnionFind.UF.empty M

def repr_empty : Prop := CompCert4Lean.Lib.UnionFind.UF.repr_emptyStatement M
def sameclass_empty : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.sameclass_emptyStatement M

def find : t → elt → elt × t := CompCert4Lean.Lib.UnionFind.UF.find M

def find_repr : Prop := CompCert4Lean.Lib.UnionFind.UF.find_reprStatement M
def find_unchanged : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.find_unchangedStatement M
def sameclass_find_1 : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.sameclass_find_1Statement M
def sameclass_find_2 : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.sameclass_find_2Statement M
def sameclass_find_3 : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.sameclass_find_3Statement M

def union : t → elt → elt → t := CompCert4Lean.Lib.UnionFind.UF.union M

def repr_union_1 : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.repr_union_1Statement M
def repr_union_2 : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.repr_union_2Statement M
def repr_union_3 : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.repr_union_3Statement M
def sameclass_union_1 : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.sameclass_union_1Statement M
def sameclass_union_2 : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.sameclass_union_2Statement M
def sameclass_union_3 : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.sameclass_union_3Statement M

def merge : t → elt → elt → t := CompCert4Lean.Lib.UnionFind.UF.merge M

def repr_merge : Prop := CompCert4Lean.Lib.UnionFind.UF.repr_mergeStatement M
def sameclass_merge : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.sameclass_mergeStatement M

def path_ord : t → elt → elt → Prop :=
  CompCert4Lean.Lib.UnionFind.UF.path_ord M

def path_ord_wellfounded : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.path_ord_wellfoundedStatement M
def path_ord_canonical : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.path_ord_canonicalStatement M
def path_ord_merge_1 : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.path_ord_merge_1Statement M
def path_ord_merge_2 : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.path_ord_merge_2Statement M

def pathlen : t → elt → Nat := CompCert4Lean.Lib.UnionFind.UF.pathlen M

def pathlen_zero : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.pathlen_zeroStatement M
def pathlen_merge : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.pathlen_mergeStatement M
def pathlen_gt_merge : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.pathlen_gt_mergeStatement M

end U

/-! ## Construction of the union-find structure -/

def record_branch (uf : U.t) (pc : node) (b : bblock) : U.t :=
  match b with
  | Lbranch s :: _ => U.union uf pc s
  | _ => uf

def record_branches (f : function) : U.t :=
  PTree.fold record_branch f.fn_code U.empty

def record_cond (st : code × U.t × Bool) (pc : node) (b : bblock) :
    code × U.t × Bool :=
  match b with
  | Lcond _cond _args s1 s2 :: _ =>
      let (c, u, _) := st
      match peq (U.repr u s1) (U.repr u s2) with
      | .left _ => (PTree.remove pc c, U.union u pc s1, true)
      | .right _ => st
  | _ => st

def record_conds_1 (cu : code × U.t) : code × U.t × Bool :=
  let (c, u) := cu
  PTree.fold record_cond c (c, u, false)

private def measure_state (cu : code × U.t) : Nat :=
  PTree_Properties.cardinal cu.1

private def recordCondsRel (s' s : code × U.t) : Prop :=
  measure_state s' < measure_state s

private def recordCondsTerminationStatement : Prop :=
  ∀ (cu : code × U.t),
    (record_conds_1 cu).2.2 = true →
      measure_state ((record_conds_1 cu).1, (record_conds_1 cu).2.1) <
        measure_state cu

private theorem recordCondsTermination : recordCondsTerminationStatement := by
  intro cu
  rcases cu with ⟨c0, u0⟩
  let P : code → (code × U.t × Bool) → Prop := fun c s =>
    (∀ pc, PTree.get pc c = none → PTree.get pc s.1 = PTree.get pc c0) ∧
      (PTree_Properties.cardinal s.1 + (if s.2.2 then 1 else 0) ≤
        PTree_Properties.cardinal c0)
  have hfold : P c0 (PTree.fold record_cond c0 (c0, u0, false)) := by
    apply PTree_Properties.fold_rec_proof
    · intro m m' a hget hP
      refine ⟨?_, hP.2⟩
      intro pc hnone
      exact hP.1 pc (by
        rw [hget pc]
        exact hnone)
    · constructor
      · intro pc hnone
        simpa [PTree.get] using hnone
      · simp [PTree_Properties.cardinal, PTree.elements, PTree.xelements]
    · intro m a k b hnone hsome hP
      rcases a with ⟨c, u, changed⟩
      change PTree.tree bblock at c
      unfold P at hP ⊢
      change
        (∀ pc, PTree.get pc m = none → PTree.get pc c = PTree.get pc c0) ∧
          (PTree_Properties.cardinal c + (if changed = true then 1 else 0) ≤
            PTree_Properties.cardinal c0) at hP
      have hset_none :
          ∀ pc v, PTree.get pc (PTree.set k v m) = none →
            PTree.get pc m = none := by
        intro pc v hpc
        have hset := PTree.getSet_equation (A := bblock) pc k v m
        rw [hset] at hpc
        split at hpc <;> simp_all
      have hpreserve :
          ∀ pc, PTree.get pc (PTree.set k b m) = none →
            PTree.get pc c = PTree.get pc c0 := by
        intro pc hpc
        exact hP.1 pc (hset_none pc b hpc)
      cases b with
      | nil =>
          simp [record_cond]
          exact ⟨hpreserve, hP.2⟩
      | cons instr tail =>
          cases instr with
          | Lop op args res =>
              simp [record_cond]
              exact ⟨hpreserve, hP.2⟩
          | Lload chunk addr args dst =>
              simp [record_cond]
              exact ⟨hpreserve, hP.2⟩
          | Lgetstack sl ofs ty dst =>
              simp [record_cond]
              exact ⟨hpreserve, hP.2⟩
          | Lsetstack src sl ofs ty =>
              simp [record_cond]
              exact ⟨hpreserve, hP.2⟩
          | Lstore chunk addr args src =>
              simp [record_cond]
              exact ⟨hpreserve, hP.2⟩
          | Lcall sig ros =>
              simp [record_cond]
              exact ⟨hpreserve, hP.2⟩
          | Ltailcall sig ros =>
              simp [record_cond]
              exact ⟨hpreserve, hP.2⟩
          | Lbuiltin ef args res =>
              simp [record_cond]
              exact ⟨hpreserve, hP.2⟩
          | Lbranch succ =>
              simp [record_cond]
              exact ⟨hpreserve, hP.2⟩
          | Lcond cond args s1 s2 =>
              unfold record_cond
              cases hpeq : peq (U.repr u s1) (U.repr u s2) with
              | right hneq =>
                  simp [hpeq]
                  exact ⟨hpreserve, hP.2⟩
              | left heq =>
                  simp [hpeq]
                  let block : bblock := Lcond cond args s1 s2 :: tail
                  have hsome_block : PTree.get k c0 = some block := by
                    simpa [block] using hsome
                  have hcode : PTree.get k c = some block := by
                    rw [hP.1 k hnone]
                    exact hsome_block
                  have hcard := PTree_Properties.cardinal_remove_proof
                    (V := bblock) k c block hcode
                  refine ⟨?_, ?_⟩
                  · intro pc hpc
                    let block : bblock := Lcond cond args s1 s2 :: tail
                    have hpc_block : PTree.get pc (PTree.set k block m) = none := by
                      simpa [block] using hpc
                    have hpc_ne : pc ≠ k := by
                      intro heqpc
                      subst pc
                      have hset := PTree.getSet_equation (A := bblock) k k block m
                      rw [hset] at hpc_block
                      simp at hpc_block
                    have hpc' : PTree.get pc m = none :=
                      hset_none pc block hpc_block
                    have hremove := @PTree.getRemove_equation bblock pc k c
                    calc
                      PTree.get pc (PTree.remove k c) = PTree.get pc c := by
                        rw [hremove]
                        simp [hpc_ne]
                      _ = PTree.get pc c0 := hP.1 pc hpc'
                  · omega
          | Ljumptable arg tbl =>
              simp [record_cond]
              exact ⟨hpreserve, hP.2⟩
          | Lreturn =>
              simp [record_cond]
              exact ⟨hpreserve, hP.2⟩
  intro hchanged
  let c0tree : PTree.tree bblock := c0
  have hchanged' :
      (PTree.fold record_cond c0tree (c0tree, u0, false)).2.2 = true := by
    simpa [record_conds_1, c0tree] using hchanged
  have hbound :
      PTree_Properties.cardinal
          (PTree.fold record_cond c0tree (c0tree, u0, false)).1 +
        (if (PTree.fold record_cond c0tree (c0tree, u0, false)).2.2 = true then 1 else 0) ≤
      PTree_Properties.cardinal c0tree := by
    simpa [c0tree, Prod.fst, Prod.snd] using hfold.2
  simp [hchanged'] at hbound
  change PTree_Properties.cardinal
      (PTree.fold record_cond c0tree (c0tree, u0, false)).1 <
    PTree_Properties.cardinal c0tree
  omega

private theorem recordCondsRel_wf : WellFounded recordCondsRel := by
  exact InvImage.wf measure_state Nat.lt_wfRel.wf

private def recordCondsWF
    (cu : code × U.t)
    (rec : ∀ cu', recordCondsRel cu' cu → U.t) : U.t :=
  let result := record_conds_1 cu
  if h : result.2.2 then
    rec (result.1, result.2.1)
      (recordCondsTermination (cu := cu) h)
  else
    cu.2

private def recordCondsCore (cu : code × U.t) : U.t :=
  WellFounded.fix recordCondsRel_wf (fun cu rec => recordCondsWF cu rec) cu

private theorem recordCondsCore_equation (cu : code × U.t) :
    recordCondsCore cu =
      let result := record_conds_1 cu
      if result.2.2 then
        recordCondsCore (result.1, result.2.1)
      else
        cu.2 := by
  unfold recordCondsCore
  rw [WellFounded.fix_eq]
  simp [recordCondsWF]

def record_conds (cu : code × U.t) : U.t :=
  recordCondsCore cu

def record_conds_equationStatement : Prop :=
  ∀ (cu : code × U.t),
    record_conds cu =
      let result := record_conds_1 cu
      if result.2.2 then record_conds (result.1, result.2.1) else cu.2

def record_conds_recStatement : Type 1 :=
  ∀ (P : code × U.t → U.t → Type),
    (∀ (cu cu' : code × U.t) (changed : Bool),
      record_conds_1 cu = (cu'.1, (cu'.2, changed)) →
      changed = true →
      P cu' (record_conds cu') →
      P cu (record_conds cu)) →
    (∀ (cu cu' : code × U.t) (changed : Bool),
      record_conds_1 cu = (cu'.1, (cu'.2, changed)) →
      changed = false →
      P cu cu.2) →
    ∀ cu : code × U.t, P cu (record_conds cu)

def record_gotos (f : function) : U.t :=
  record_conds (f.fn_code, record_branches f)

/-! ## Code transformation -/

def tunnel_instr (u : U.t) : instruction → instruction
  | Lbranch s => Lbranch (U.repr u s)
  | Lcond cond args s1 s2 =>
      let s1' := U.repr u s1
      let s2' := U.repr u s2
      match peq s1' s2' with
      | .left _ => Lbranch s1'
      | .right _ => Lcond cond args s1' s2'
  | Ljumptable arg tbl => Ljumptable arg (tbl.map (U.repr u))
  | i => i

def tunnel_block (u : U.t) (b : bblock) : bblock :=
  b.map (tunnel_instr u)

def tunnel_function (f : function) : function :=
  let u := record_gotos f
  { fn_sig := f.fn_sig
    fn_stacksize := f.fn_stacksize
    fn_code := PTree.map1 (tunnel_block u) f.fn_code
    fn_entrypoint := U.repr u f.fn_entrypoint }

def tunnel_fundef (f : fundef) : fundef :=
  CompCert4Lean.Common.AST.transf_fundef tunnel_function f

def tunnel_program (p : program) : program :=
  CompCert4Lean.Common.AST.transform_program tunnel_fundef p

end CompCert4Lean.Backend.Tunneling
