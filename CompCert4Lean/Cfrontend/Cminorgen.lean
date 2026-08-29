import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.Ordered
import CompCert4Lean.Foundation.RocqString
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Errors
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Maps
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Cfrontend.Csharpminor
import CompCert4Lean.Backend.Cminor

/-!
# Translation from Csharpminor to Cminor

Definition-bearing translation of CompCert's `cfrontend/Cminorgen.v`.
-/

namespace CompCert4Lean.Cfrontend.Cminorgen

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Sorted
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Integers

private abbrev ident := CompCert4Lean.Common.AST.ident
private abbrev Ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev CSConstant := CompCert4Lean.Cfrontend.Csharpminor.constant
private abbrev CSExpr := CompCert4Lean.Cfrontend.Csharpminor.expr
private abbrev CSStmt := CompCert4Lean.Cfrontend.Csharpminor.stmt
private abbrev CSLblStmt := CompCert4Lean.Cfrontend.Csharpminor.lbl_stmt
private abbrev CSFunction := CompCert4Lean.Cfrontend.Csharpminor.function
private abbrev CSFundef := CompCert4Lean.Cfrontend.Csharpminor.fundef
private abbrev CSProgram := CompCert4Lean.Cfrontend.Csharpminor.program
private abbrev CMConstant := CompCert4Lean.Backend.Cminor.constant
private abbrev CMExpr := CompCert4Lean.Backend.Cminor.expr
private abbrev CMStmt := CompCert4Lean.Backend.Cminor.stmt
private abbrev CMFunction := CompCert4Lean.Backend.Cminor.function
private abbrev CMFundef := CompCert4Lean.Backend.Cminor.fundef
private abbrev CMProgram := CompCert4Lean.Backend.Cminor.program
private abbrev Res := CompCert4Lean.Common.Errors.res
private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string

private abbrev z0 : Z := .Z0
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zMax := ZArith.BinInt.Z.max

private def ofString (s : String) : RocqString :=
  (String.toUTF8 s).toList.foldr
    (fun b tail =>
      CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.String b tail)
    CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.EmptyString

/-! ## Handling of variables -/

def compilenv : Type := PTree.t Z

def var_addr (cenv : compilenv) (id : ident) : CMExpr :=
  match PTree.get id cenv with
  | some ofs => .Econst (.Oaddrstack (Ptrofs.repr ofs))
  | none => .Econst (.Oaddrsymbol id Ptrofs.zero)

/-! ## Translation of expressions and statements -/

def transl_constant : CSConstant → CMConstant
  | .Ointconst n => .Ointconst n
  | .Ofloatconst n => .Ofloatconst n
  | .Osingleconst n => .Osingleconst n
  | .Olongconst n => .Olongconst n

def transl_expr (cenv : compilenv) : CSExpr → Res CMExpr
  | .Evar id => .OK (.Evar id)
  | .Eaddrof id => .OK (var_addr cenv id)
  | .Econst cst => .OK (.Econst (transl_constant cst))
  | .Eunop op e1 =>
      match transl_expr cenv e1 with
      | .Error msg => .Error msg
      | .OK te1 => .OK (.Eunop op te1)
  | .Ebinop op e1 e2 =>
      match transl_expr cenv e1 with
      | .Error msg => .Error msg
      | .OK te1 =>
          match transl_expr cenv e2 with
          | .Error msg => .Error msg
          | .OK te2 => .OK (.Ebinop op te1 te2)
  | .Eload chunk e =>
      match transl_expr cenv e with
      | .Error msg => .Error msg
      | .OK te => .OK (.Eload chunk te)

def transl_exprlist (cenv : compilenv) : List CSExpr → Res (List CMExpr)
  | [] => .OK []
  | e1 :: e2 =>
      match transl_expr cenv e1 with
      | .Error msg => .Error msg
      | .OK te1 =>
          match transl_exprlist cenv e2 with
          | .Error msg => .Error msg
          | .OK te2 => .OK (te1 :: te2)

def exit_env : Type := List Bool

def shift_exit : exit_env → Nat → Nat
  | [], n => n
  | false :: e, n => Nat.succ (shift_exit e n)
  | true :: _, 0 => 0
  | true :: e, Nat.succ n => Nat.succ (shift_exit e n)

def switch_table : CSLblStmt → Nat → List (Z × Nat) × Nat
  | .LSnil, k => ([], k)
  | .LScons none _ remaining, k =>
      let (table, _) := switch_table remaining (Nat.succ k)
      (table, k)
  | .LScons (some n) _ remaining, k =>
      let (table, default) := switch_table remaining (Nat.succ k)
      ((n, k) :: table, default)

def switch_env : CSLblStmt → exit_env → exit_env
  | .LSnil, e => e
  | .LScons _ _ remaining, e => false :: switch_env remaining e

mutual
  def transl_stmt (cenv : compilenv) (xenv : exit_env) : CSStmt → Res CMStmt
    | .Sskip => .OK .Sskip
    | .Sset id e =>
        match transl_expr cenv e with
        | .Error msg => .Error msg
        | .OK te => .OK (.Sassign id te)
    | .Sstore chunk e1 e2 =>
        match transl_expr cenv e1 with
        | .Error msg => .Error msg
        | .OK te1 =>
            match transl_expr cenv e2 with
            | .Error msg => .Error msg
            | .OK te2 => .OK (.Sstore chunk te1 te2)
    | .Scall optid sig e args =>
        match transl_expr cenv e with
        | .Error msg => .Error msg
        | .OK te =>
            match transl_exprlist cenv args with
            | .Error msg => .Error msg
            | .OK targs => .OK (.Scall optid sig te targs)
    | .Sbuiltin optid ef args =>
        match transl_exprlist cenv args with
        | .Error msg => .Error msg
        | .OK targs => .OK (.Sbuiltin optid ef targs)
    | .Sseq s1 s2 =>
        match transl_stmt cenv xenv s1 with
        | .Error msg => .Error msg
        | .OK ts1 =>
            match transl_stmt cenv xenv s2 with
            | .Error msg => .Error msg
            | .OK ts2 => .OK (.Sseq ts1 ts2)
    | .Sifthenelse e s1 s2 =>
        match transl_expr cenv e with
        | .Error msg => .Error msg
        | .OK te =>
            match transl_stmt cenv xenv s1 with
            | .Error msg => .Error msg
            | .OK ts1 =>
                match transl_stmt cenv xenv s2 with
                | .Error msg => .Error msg
                | .OK ts2 => .OK (.Sifthenelse te ts1 ts2)
    | .Sloop s =>
        match transl_stmt cenv xenv s with
        | .Error msg => .Error msg
        | .OK ts => .OK (.Sloop ts)
    | .Sblock s =>
        match transl_stmt cenv (true :: xenv) s with
        | .Error msg => .Error msg
        | .OK ts => .OK (.Sblock ts)
    | .Sexit n => .OK (.Sexit (shift_exit xenv n))
    | .Sswitch isLong e cases =>
        let (table, default) := switch_table cases 0
        match transl_expr cenv e with
        | .Error msg => .Error msg
        | .OK te =>
            transl_lblstmt cenv (switch_env cases xenv) cases
              (.Sswitch isLong te table default)
    | .Sreturn none => .OK (.Sreturn none)
    | .Sreturn (some e) =>
        match transl_expr cenv e with
        | .Error msg => .Error msg
        | .OK te => .OK (.Sreturn (some te))
    | .Slabel label s =>
        match transl_stmt cenv xenv s with
        | .Error msg => .Error msg
        | .OK ts => .OK (.Slabel label ts)
    | .Sgoto label => .OK (.Sgoto label)

  def transl_lblstmt (cenv : compilenv) (xenv : exit_env) :
      CSLblStmt → CMStmt → Res CMStmt
    | .LSnil, body => .OK (.Sseq (.Sblock body) .Sskip)
    | .LScons _ s remaining, body =>
        match transl_stmt cenv xenv s with
        | .Error msg => .Error msg
        | .OK ts =>
            transl_lblstmt cenv xenv.tail remaining (.Sseq (.Sblock body) ts)
end

/-! ## Stack layout -/

def block_alignment (size : Z) : Z :=
  match zlt size (zOfNat 2) with
  | .left _ => zOfNat 1
  | .right _ =>
      match zlt size (zOfNat 4) with
      | .left _ => zOfNat 2
      | .right _ =>
          match zlt size (zOfNat 8) with
          | .left _ => zOfNat 4
          | .right _ => zOfNat 8

def assign_variable
    (cenvStacksize : compilenv × Z) (idSize : ident × Z) : compilenv × Z :=
  let (id, size) := idSize
  let (cenv, stacksize) := cenvStacksize
  let ofs := align stacksize (block_alignment size)
  (PTree.set id ofs cenv, zAdd ofs (zMax z0 size))

def assign_variables
    (cenvStacksize : compilenv × Z) (vars : List (ident × Z)) : compilenv × Z :=
  vars.foldl assign_variable cenvStacksize

/-! The source instantiates Rocq's stable `Mergesort.Sort` functor here.  The
generated application owns this namespace; the excluded authored `VarOrder`
module is not reproduced. -/

namespace VarSort

private abbrev varEntry := ident × Z

def VarSort : Type := Unit

private def leb (v1 v2 : varEntry) : Bool :=
  match zle v1.2 v2.2 with
  | .left _ => true
  | .right _ => false

def merge (l1 l2 : List varEntry) : List varEntry :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | a1 :: l1', a2 :: l2' =>
      if leb a1 a2 then
        a1 :: merge l1' (a2 :: l2')
      else
        a2 :: merge (a1 :: l1') l2'
termination_by l1.length + l2.length

def merge_list_to_stack :
    List (Option (List varEntry)) → List varEntry → List (Option (List varEntry))
  | [], l => [some l]
  | none :: stack, l => some l :: stack
  | some l' :: stack, l => none :: merge_list_to_stack stack (merge l' l)

def merge_stack : List (Option (List varEntry)) → List varEntry
  | [] => []
  | none :: stack => merge_stack stack
  | some l :: stack => merge l (merge_stack stack)

def iter_merge : List (Option (List varEntry)) → List varEntry → List varEntry
  | stack, [] => merge_stack stack
  | stack, a :: l => iter_merge (merge_list_to_stack stack [a]) l

def sort (l : List varEntry) : List varEntry := iter_merge [] l

private def ordered (v1 v2 : varEntry) : Prop :=
  leb v1 v2 = true

def SortedStack : List (Option (List varEntry)) → Prop
  | [] => True
  | none :: stack => SortedStack stack
  | some l :: stack => LocallySorted ordered l ∧ SortedStack stack

def flatten_stack : List (Option (List varEntry)) → List varEntry
  | [] => []
  | none :: stack => flatten_stack stack
  | some l :: stack => l ++ flatten_stack stack

def Sorted_merge : Prop :=
  ∀ l1 l2, LocallySorted ordered l1 → LocallySorted ordered l2 →
    LocallySorted ordered (merge l1 l2)

def Permuted_merge : Prop :=
  ∀ l1 l2,
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Permutation.Permutation
      (l1 ++ l2) (merge l1 l2)

def Sorted_merge_list_to_stack : Prop :=
  ∀ stack l, SortedStack stack → LocallySorted ordered l →
    SortedStack (merge_list_to_stack stack l)

def Permuted_merge_list_to_stack : Prop :=
  ∀ stack l,
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Permutation.Permutation
      (l ++ flatten_stack stack) (flatten_stack (merge_list_to_stack stack l))

def Sorted_merge_stack : Prop :=
  ∀ stack, SortedStack stack → LocallySorted ordered (merge_stack stack)

def Permuted_merge_stack : Prop :=
  ∀ stack,
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Permutation.Permutation
      (flatten_stack stack) (merge_stack stack)

def Sorted_iter_merge : Prop :=
  ∀ stack l, SortedStack stack → LocallySorted ordered (iter_merge stack l)

def Permuted_iter_merge : Prop :=
  ∀ l stack,
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Permutation.Permutation
      (flatten_stack stack ++ l) (iter_merge stack l)

def LocallySorted_sort : Prop :=
  ∀ l, LocallySorted ordered (sort l)

def Sorted_sort : Prop :=
  ∀ l, Sorted ordered (sort l)

def Permuted_sort : Prop :=
  ∀ l,
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Sorting.Permutation.Permutation
      l (sort l)

def StronglySorted_sort : Prop :=
  ∀ l, (∀ x y z, ordered x y → ordered y z → ordered x z) →
    StronglySorted ordered (sort l)

end VarSort

def build_compilenv (f : CSFunction) : compilenv × Z :=
  assign_variables (PTree.empty Z, z0) (VarSort.sort f.fn_vars)

/-! ## Translation of functions and programs -/

def transl_funbody (cenv : compilenv) (stacksize : Z) (f : CSFunction) :
    Res CMFunction :=
  match transl_stmt cenv [] f.fn_body with
  | .Error msg => .Error msg
  | .OK body =>
      .OK
        { fn_sig := f.fn_sig
          fn_params := f.fn_params
          fn_vars := f.fn_temps
          fn_stackspace := stacksize
          fn_body := body }

def transl_function (f : CSFunction) : Res CMFunction :=
  let (cenv, stacksize) := build_compilenv f
  match zle stacksize Ptrofs.max_unsigned with
  | .left _ => transl_funbody cenv stacksize f
  | .right _ =>
      .Error (msg (ofString "Cminorgen: too many local variables, stack size exceeded"))

def transl_fundef (f : CSFundef) : Res CMFundef :=
  transf_partial_fundef transl_function f

def transl_program (p : CSProgram) : Res CMProgram :=
  transform_partial_program transl_fundef p

end CompCert4Lean.Cfrontend.Cminorgen
