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
  elt_eq := inferInstance
  t := PTree.t
  empty := PTree.empty
  get := PTree.get
  set := PTree.set
  gempty := fun x => getEmpty _ x
  gsspec := fun x y v m => getSet _ x y v m

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

private def recordCondsFuel : Nat → code × U.t → U.t
  | 0, cu => cu.2
  | fuel + 1, cu =>
      let result := record_conds_1 cu
      if result.2.2 then
        recordCondsFuel fuel (result.1, result.2.1)
      else
        cu.2

/-- Iterate conditional-branch recording until the pass reports no change. -/
def record_conds (cu : code × U.t) : U.t :=
  recordCondsFuel (PTree_Properties.cardinal cu.1 + 1) cu

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
