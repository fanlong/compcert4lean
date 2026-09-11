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
  get := fun {_} => PTree.get
  set := fun {_} => PTree.set
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

/-! The result of the Rocq `UF(PTree)` application is sealed by the
`UNIONFIND` signature.  Keep the canonical provider representation private
to this generated application and expose only the source-shaped interface
below. -/
private structure state where
  carrier : CompCert4Lean.Lib.UnionFind.UF.t M

def t : Type := state

private def toProvider (uf : t) : CompCert4Lean.Lib.UnionFind.UF.t M :=
  uf.carrier

private def ofProvider (uf : CompCert4Lean.Lib.UnionFind.UF.t M) : t :=
  ⟨uf⟩

def repr (uf : t) (a : elt) : elt :=
  CompCert4Lean.Lib.UnionFind.UF.repr M (toProvider uf) a

def repr_canonical : Prop :=
  ∀ (uf : t) (a : elt), repr uf (repr uf a) = repr uf a

def sameclass (uf : t) (a b : elt) : Prop := repr uf a = repr uf b

def sameclass_refl : Prop :=
  ∀ (uf : t) (a : elt), sameclass uf a a
def sameclass_sym : Prop :=
  ∀ (uf : t) (a b : elt), sameclass uf a b → sameclass uf b a
def sameclass_trans : Prop :=
  ∀ (uf : t) (a b c : elt), sameclass uf a b → sameclass uf b c →
    sameclass uf a c
def sameclass_repr : Prop :=
  ∀ (uf : t) (a : elt), sameclass uf a (repr uf a)

def empty : t := ofProvider (CompCert4Lean.Lib.UnionFind.UF.empty M)

def repr_empty : Prop := ∀ (a : elt), repr empty a = a
def sameclass_empty : Prop :=
  ∀ (a b : elt), sameclass empty a b → a = b

def find (uf : t) (a : elt) : elt × t :=
  let r := CompCert4Lean.Lib.UnionFind.UF.find M (toProvider uf) a
  (r.1, ofProvider r.2)

def find_repr : Prop :=
  ∀ (uf : t) (a : elt), (find uf a).1 = repr uf a
def find_unchanged : Prop :=
  ∀ (uf : t) (a x : elt), repr (find uf a).2 x = repr uf x
def sameclass_find_1 : Prop :=
  ∀ (uf : t) (a x y : elt),
    sameclass (find uf a).2 x y ↔ sameclass uf x y
def sameclass_find_2 : Prop :=
  ∀ (uf : t) (a : elt), sameclass uf a (find uf a).1
def sameclass_find_3 : Prop :=
  ∀ (uf : t) (a : elt), sameclass (find uf a).2 a (find uf a).1

def union (uf : t) (a b : elt) : t :=
  ofProvider (CompCert4Lean.Lib.UnionFind.UF.union M (toProvider uf) a b)

def repr_union_1 : Prop :=
  ∀ (uf : t) (a b x : elt), repr uf x ≠ repr uf a →
    repr (union uf a b) x = repr uf x
def repr_union_2 : Prop :=
  ∀ (uf : t) (a b x : elt), repr uf x = repr uf a →
    repr (union uf a b) x = repr uf b
def repr_union_3 : Prop :=
  ∀ (uf : t) (a b : elt), repr (union uf a b) b = repr uf b
def sameclass_union_1 : Prop :=
  ∀ (uf : t) (a b : elt), sameclass (union uf a b) a b
def sameclass_union_2 : Prop :=
  ∀ (uf : t) (a b x y : elt), sameclass uf x y →
    sameclass (union uf a b) x y
def sameclass_union_3 : Prop :=
  ∀ (uf : t) (a b x y : elt), sameclass (union uf a b) x y →
    sameclass uf x y ∨
      (sameclass uf x a ∧ sameclass uf y b) ∨
      (sameclass uf x b ∧ sameclass uf y a)

def merge (uf : t) (a b : elt) : t :=
  ofProvider (CompCert4Lean.Lib.UnionFind.UF.merge M (toProvider uf) a b)

def repr_merge : Prop :=
  ∀ (uf : t) (a b x : elt),
    repr (merge uf a b) x = repr (union uf a b) x
def sameclass_merge : Prop :=
  ∀ (uf : t) (a b x y : elt),
    sameclass (merge uf a b) x y ↔ sameclass (union uf a b) x y

def path_ord (uf : t) (x y : elt) : Prop :=
  CompCert4Lean.Lib.UnionFind.UF.path_ord M (toProvider uf) x y

def path_ord_wellfounded : Prop :=
  ∀ (uf : t), WellFounded (path_ord uf)
def path_ord_canonical : Prop :=
  ∀ (uf : t) (x y : elt), repr uf x = x → ¬ path_ord uf y x
def path_ord_merge_1 : Prop :=
  ∀ (uf : t) (a b x y : elt), path_ord uf x y →
    path_ord (merge uf a b) x y
def path_ord_merge_2 : Prop :=
  ∀ (uf : t) (a b : elt), repr uf a ≠ repr uf b →
    path_ord (merge uf a b) b (repr uf a)

def pathlen (uf : t) (a : elt) : Nat :=
  CompCert4Lean.Lib.UnionFind.UF.pathlen M (toProvider uf) a

def pathlen_zero : Prop :=
  ∀ (uf : t) (a : elt), repr uf a = a ↔ pathlen uf a = 0
def pathlen_merge : Prop :=
  ∀ (uf : t) (a b x : elt),
    pathlen (merge uf a b) x =
      match elt_eq (repr uf a) (repr uf b) with
      | .left _ => pathlen uf x
      | .right _ =>
          match elt_eq (repr uf x) (repr uf a) with
          | .left _ => pathlen uf x + pathlen uf b + 1
          | .right _ => pathlen uf x
def pathlen_gt_merge : Prop :=
  ∀ (uf : t) (a b x y : elt), repr uf x = repr uf y →
    pathlen uf x > pathlen uf y →
      pathlen (merge uf a b) x > pathlen (merge uf a b) y

end U

/-! ## Construction of the union-find structure -/

def record_branch (uf : U.t) (pc : node) (b : bblock) : U.t :=
  match b with
  | Lbranch s :: _ => U.union uf pc s
  | _ => uf

def record_branches (f : function) : U.t :=
  PTree.fold record_branch f.fn_code U.empty

def record_cond (st : ((code × U.t) × Bool)) (pc : node) (b : bblock) :
    ((code × U.t) × Bool) :=
  match b with
  | Lcond _cond _args s1 s2 :: _ =>
      let ((c, u), _) := st
      match peq (U.repr u s1) (U.repr u s2) with
      | .left _ => ((PTree.remove pc c, U.union u pc s1), true)
      | .right _ => st
  | _ => st

def record_conds_1 (cu : code × U.t) : ((code × U.t) × Bool) :=
  let (c, u) := cu
  PTree.fold record_cond c ((c, u), false)

private def measure_state (cu : code × U.t) : Nat :=
  PTree_Properties.cardinal cu.1

private def recordCondsRel (s' s : code × U.t) : Prop :=
  measure_state s' < measure_state s

private def recordCondsTerminationStatement : Prop :=
  ∀ (cu : code × U.t),
    (record_conds_1 cu).2 = true →
      measure_state (record_conds_1 cu).1 < measure_state cu

private theorem recordCondsTermination : recordCondsTerminationStatement := by
  intro cu
  rcases cu with ⟨c0, u0⟩
  let P : code → ((code × U.t) × Bool) → Prop := fun c s =>
    (∀ pc, PTree.get pc c = none → PTree.get pc s.1.1 = PTree.get pc c0) ∧
      (PTree_Properties.cardinal s.1.1 + (if s.2 then 1 else 0) ≤
        PTree_Properties.cardinal c0)
  have hfold : P c0 (PTree.fold record_cond c0 ((c0, u0), false)) := by
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
      rcases a with ⟨⟨c, u⟩, changed⟩
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
      (PTree.fold record_cond c0tree ((c0tree, u0), false)).2 = true := by
    simpa [record_conds_1, c0tree] using hchanged
  have hbound :
      PTree_Properties.cardinal
          (PTree.fold record_cond c0tree ((c0tree, u0), false)).1.1 +
        (if (PTree.fold record_cond c0tree ((c0tree, u0), false)).2 = true then 1 else 0) ≤
      PTree_Properties.cardinal c0tree := by
    simpa [c0tree, Prod.fst, Prod.snd] using hfold.2
  simp [hchanged'] at hbound
  change PTree_Properties.cardinal
      (PTree.fold record_cond c0tree ((c0tree, u0), false)).1.1 <
    PTree_Properties.cardinal c0tree
  omega

private theorem recordCondsRel_wf : WellFounded recordCondsRel := by
  exact InvImage.wf measure_state Nat.lt_wfRel.wf

private def recordCondsWF
    (cu : code × U.t)
    (rec : ∀ cu', recordCondsRel cu' cu → U.t) : U.t :=
  let result := record_conds_1 cu
  if h : result.2 then
    rec result.1
      (recordCondsTermination (cu := cu) h)
  else
    cu.2

private def recordCondsCore (cu : code × U.t) : U.t :=
  WellFounded.fix recordCondsRel_wf (fun cu rec => recordCondsWF cu rec) cu

private theorem recordCondsCore_equation (cu : code × U.t) :
    recordCondsCore cu =
      let result := record_conds_1 cu
      if result.2 then
        recordCondsCore result.1
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
      if result.2 then record_conds result.1 else cu.2

def record_conds_recStatement : Type 1 :=
  ∀ (P : code × U.t → U.t → Type),
    (∀ (cu cu' : code × U.t) (changed : Bool),
      record_conds_1 cu = (cu', changed) →
      changed = true →
      P cu' (record_conds cu') →
      P cu (record_conds cu')) →
    (∀ (cu cu' : code × U.t) (changed : Bool),
      record_conds_1 cu = (cu', changed) →
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

namespace CompCert4Lean.Backend.Tunneling.U
open CompCert4Lean.Lib.Maps
private theorem provider_repr_none (uf : CompCert4Lean.Lib.UnionFind.UF.t M)
    (a : M.elt) (h : M.get a uf.m = none) :
    CompCert4Lean.Lib.UnionFind.UF.repr M uf a = a := by
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    let base := Lean.Name.str
      (Lean.Name.str
        (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "CompCert4Lean") "Lib")
      "UnionFind"
    let n := Lean.Name.str
      (Lean.Name.str
        (Lean.Name.str
          (Lean.Name.str
            (Lean.Name.str (Lean.Name.mkNum base 0) "CompCert4Lean") "Lib") "UnionFind") "UF")
      "repr_none_calc"
    let gs ← Lean.Meta.withTransparency .all <| g.apply (Lean.mkConst n)
    Lean.Elab.Tactic.replaceMainGoal gs
  exact h
theorem repr_empty_proof : repr_empty := by
  intro a
  let aM : M.elt := a
  apply provider_repr_none (CompCert4Lean.Lib.UnionFind.UF.empty M) aM
  change M.get aM (M.empty M.elt) = none
  exact M.gempty M.elt aM

end CompCert4Lean.Backend.Tunneling.U

namespace CompCert4Lean.Backend.Tunneling.U

open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.UnionFind

private theorem pg_tunnel_map_get_set {M : MAP} {A : Type} (x y : M.elt)
    (v : A) (m : M.t A) :
    M.get x (M.set y v m) = if _h : x = y then some v else M.get x m := by
  rw [M.gsspec]
  cases hxy : M.elt_eq x y with
  | left h => simp [h]
  | right h => simp [h]

private theorem pg_tunnel_repr_res_none {M : MAP} (uf : UF.t M) (a : UF.elt M) :
    M.get (UF.repr M uf a) uf.m = none := by
  apply uf.mwf.induction a
  intro x ih
  rw [UF.repr_unroll_proof M uf x]
  cases h : M.get x uf.m with
  | none => simpa [h]
  | some y => simpa [h] using ih y (by
      change M.get x uf.m = some y
      exact h)

private theorem pg_tunnel_repr_canonical {M : MAP} (uf : UF.t M) (a : UF.elt M) :
    UF.repr M uf (UF.repr M uf a) = UF.repr M uf a := by
  rw [UF.repr_none_proof M uf (UF.repr M uf a) (pg_tunnel_repr_res_none uf a)]

private theorem pg_tunnel_repr_none {M : MAP} (uf : UF.t M) (a : UF.elt M)
    (h : M.get a uf.m = none) : UF.repr M uf a = a :=
  UF.repr_none_proof M uf a h

private theorem pg_tunnel_repr_some {M : MAP} (uf : UF.t M) (a a' : UF.elt M)
    (h : M.get a uf.m = some a') : UF.repr M uf a = UF.repr M uf a' :=
  UF.repr_some_proof M uf a a' h

private theorem pg_tunnel_repr_identify_1 {M : MAP} (uf : UF.t M) (a b : UF.elt M)
    (ha : M.get a uf.m = none) (hn : UF.repr M uf b ≠ a) (x : UF.elt M)
    (hx : UF.repr M uf x ≠ a) :
    UF.repr M (UF.identify M uf a b ha hn) x = UF.repr M uf x := by
  revert hx
  apply (UF.identify M uf a b ha hn).mwf.induction x
  intro x ih hx
  rw [UF.repr_unroll_proof M (UF.identify M uf a b ha hn) x]
  cases hnew : M.get x (UF.identify M uf a b ha hn).m with
  | none =>
      simp only [hnew]
      change M.get x (M.set a b uf.m) = none at hnew
      rw [pg_tunnel_map_get_set] at hnew
      by_cases hxa : x = a
      · subst x
        simp at hnew
      · simp [hxa] at hnew
        exact (pg_tunnel_repr_none uf x hnew).symm
  | some y =>
      simp only [hnew]
      change M.get x (M.set a b uf.m) = some y at hnew
      rw [pg_tunnel_map_get_set] at hnew
      by_cases hxa : x = a
      · subst x
        simp at hnew
        subst y
        exact False.elim (hx (pg_tunnel_repr_none uf a ha))
      · simp [hxa] at hnew
        have hy : UF.repr M uf y ≠ a := by
          intro hya
          apply hx
          exact (pg_tunnel_repr_some uf x y hnew).trans hya
        exact (ih y (by
          change M.get x (M.set a b uf.m) = some y
          rw [pg_tunnel_map_get_set]
          simp [hxa, hnew]) hy).trans (pg_tunnel_repr_some uf x y hnew).symm

private theorem pg_tunnel_repr_identify_2 {M : MAP} (uf : UF.t M) (a b : UF.elt M)
    (ha : M.get a uf.m = none) (hn : UF.repr M uf b ≠ a) (x : UF.elt M)
    (hx : UF.repr M uf x = a) :
    UF.repr M (UF.identify M uf a b ha hn) x = UF.repr M uf b := by
  revert hx
  apply (UF.identify M uf a b ha hn).mwf.induction x
  intro x ih hx
  rw [UF.repr_unroll_proof M (UF.identify M uf a b ha hn) x]
  cases hnew : M.get x (UF.identify M uf a b ha hn).m with
  | none =>
      simp only [hnew]
      change M.get x (M.set a b uf.m) = none at hnew
      rw [pg_tunnel_map_get_set] at hnew
      by_cases hxa : x = a
      · subst x
        simp at hnew
      · simp [hxa] at hnew
        exact False.elim (hxa ((pg_tunnel_repr_none uf x hnew).symm.trans hx))
  | some y =>
      simp only [hnew]
      change M.get x (M.set a b uf.m) = some y at hnew
      rw [pg_tunnel_map_get_set] at hnew
      by_cases hxa : x = a
      · subst x
        simp at hnew
        subst y
        exact pg_tunnel_repr_identify_1 uf a b ha hn b hn
      · simp [hxa] at hnew
        apply ih y (by
          change M.get x (M.set a b uf.m) = some y
          rw [pg_tunnel_map_get_set]
          simp [hxa, hnew])
        exact (pg_tunnel_repr_some uf x y hnew).symm.trans hx

private theorem pg_tunnel_repr_union_1 {M : MAP} (uf : UF.t M) (a b x : UF.elt M)
    (hx : UF.repr M uf x ≠ UF.repr M uf a) :
    UF.repr M (UF.union M uf a b) x = UF.repr M uf x := by
  unfold UF.union
  dsimp
  split <;> rename_i h
  · rfl
  · apply pg_tunnel_repr_identify_1
    exact hx

private theorem pg_tunnel_repr_union_3 {M : MAP} (uf : UF.t M) (a b : UF.elt M) :
    UF.repr M (UF.union M uf a b) b = UF.repr M uf b := by
  by_cases h : UF.repr M uf a = UF.repr M uf b
  · unfold UF.union
    dsimp
    simp [h]
  · exact pg_tunnel_repr_union_1 uf a b b (Ne.symm h)

theorem repr_union_3_proof : repr_union_3 := by
  intro uf a b
  cases uf
  unfold U.repr U.union
  apply pg_tunnel_repr_union_3

end CompCert4Lean.Backend.Tunneling.U

namespace CompCert4Lean.Backend.Tunneling.U

theorem repr_union_1_proof : repr_union_1 := by
  intro uf a b x hx
  cases uf
  unfold U.repr U.union
  apply pg_tunnel_repr_union_1
  exact hx

end CompCert4Lean.Backend.Tunneling.U
