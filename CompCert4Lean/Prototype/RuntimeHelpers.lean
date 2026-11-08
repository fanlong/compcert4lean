import CompCert4Lean.Prototype.Json

namespace CompCert4Lean.Prototype

open Backend Common.AST Common.Switch
open Foundation.Numbers.Rocq.Coq
open Lib.Maps

def normalizeSwitch (cases : table) : table :=
  (cases.foldl (fun (state : Std.HashSet Int × table) (key, target) =>
    if state.1.contains (intOfZ key) then state
    else (state.1.insert (intOfZ key), (key, target) :: state.2)) ({}, [])).2

def switchTree : Nat → Nat → table → Int → Int → comptree
  | 0, default, cases, _, _ =>
      cases.foldr (fun (key, target) rest => .CTifeq key target rest) (.CTaction default)
  | fuel + 1, default, cases, minimum, maximum =>
      match cases with
      | [] => .CTaction default
      | [(key, target)] =>
          if maximum - minimum == 0 then .CTaction target
          else .CTifeq key target (.CTaction default)
      | [(key, target), (key2, target2)] =>
          .CTifeq key target (if maximum - minimum == 1 then .CTaction target2
            else .CTifeq key2 target2 (.CTaction default))
      | [(key, target), (key2, target2), (key3, target3)] =>
          .CTifeq key target (.CTifeq key2 target2
            (if maximum - minimum == 2 then .CTaction target3
             else .CTifeq key3 target3 (.CTaction default)))
      | _ =>
          let middle := cases.length / 2
          match (cases.drop middle).head? with
          | none => .CTaction default
          | some (pivot, _) => .CTiflt pivot
              (switchTree fuel default (cases.take middle) minimum (intOfZ pivot - 1))
              (switchTree fuel default (cases.drop middle) (intOfZ pivot) maximum)

def compileSwitch (modulus : Z) (default : Nat) (cases : table) : comptree :=
  let cases := (normalizeSwitch cases).mergeSort (fun left right => intOfZ left.1 ≤ intOfZ right.1)
  match cases.head?, cases.getLast? with
  | some (minimum, _), some (maximum, _) =>
      let span := intOfZ maximum - intOfZ minimum
      if cases.length ≥ 7 && span ≥ 0 && 8 + span ≤ 4 * (cases.length : Int) &&
          span < (2 : Int)^54 - 1 then
        let targets := cases.foldl (fun (targets : Std.HashMap Int Nat) (key, target) =>
          targets.insert (intOfZ key) target) {}
        .CTjumptable minimum (zOfInt (span + 1))
          ((List.range (span.toNat + 1)).map (fun index =>
            (targets.get? (intOfZ minimum + (index : Nat))).getD default)) (.CTaction default)
      else switchTree cases.length default cases 0 (intOfZ modulus)
  | _, _ => .CTaction default

def unaryCost : Cminor.unary_operation → Nat
  | .Ocast8unsigned | .Ocast8signed | .Ocast16unsigned | .Ocast16signed
  | .Onegint | .Onotint | .Onegf | .Oabsf | .Onegfs | .Oabsfs
  | .Onegl | .Onotl | .Ointoflong | .Olongofint | .Olongofintu => 1
  | .Osingleoffloat | .Ofloatofsingle => 2
  | _ => 1000

def binaryCost : Cminor.binary_operation → Nat
  | .Oadd | .Osub | .Oand | .Oor | .Oxor | .Oshl | .Oshr | .Oshru
  | .Oaddl | .Osubl | .Oandl | .Oorl | .Oxorl | .Oshll | .Oshrl | .Oshrlu => 1
  | .Omul | .Omull | .Oaddf | .Osubf | .Omulf | .Oaddfs | .Osubfs | .Omulfs
  | .Ocmp _ | .Ocmpu _ | .Ocmpf _ | .Ocmpfs _ => 2
  | .Odivf | .Odivfs => 10
  | _ => 1000

def expressionCost : Cminor.expr → Nat
  | .Evar _ => 0
  | .Econst _ => 0
  | .Eunop operation value => unaryCost operation + expressionCost value
  | .Ebinop operation left right => binaryCost operation + expressionCost left + expressionCost right
  | .Eload _ _ => 1000

def continuationTest : CminorSel.stmt → Option ident
  | .Sifthenelse (.CEcond (.Ccompuimm _ _) (.Econs (.Evar identifier) .Enil)) _ _ => some identifier
  | .Sseq .Sskip rest => continuationTest rest
  | .Sseq (.Sbuiltin _ (.EF_debug _ _ _) _) rest => continuationTest rest
  | .Sseq first _ => continuationTest first
  | _ => none

def integerConstant : Cminor.expr → Bool
  | .Econst (.Ointconst _) => true
  | _ => false

def ifConversion (enabled : Bool) : Selection.IfConversionHeuristic :=
  fun identifier _ ifso ifnot type continuation =>
    let left := expressionCost ifso
    let right := expressionCost ifnot
    enabled && (match type with | .Tint | .Tlong => true | _ => false) &&
      left + right ≤ 20 && left - right ≤ 4 && right - left ≤ 4 &&
      !(continuationTest continuation == some identifier &&
        (integerConstant ifso || integerConstant ifnot))

def joinPoints (source : LTL.function) : Std.HashSet Nat :=
  let rec visit : Nat → List positive → Std.HashSet Nat → Std.HashSet Nat → Std.HashSet Nat
    | 0, _, _, joins => joins
    | _ + 1, [], _, joins => joins
    | fuel + 1, node :: pending, visited, joins =>
        let key := posToNat node
        if visited.contains key then visit fuel pending visited (joins.insert key)
        else
          let successors := (PTree.get node source.fn_code).map LTL.successors_block |>.getD []
          visit fuel (List.append successors pending) (visited.insert key) joins
  let edges := (PTree.elements source.fn_code).foldl
    (fun count (_, block) => count + (LTL.successors_block block).length) 0
  visit (edges + 1) [source.fn_entrypoint] {} {}

def branchTarget : LTL.bblock → Option positive
  | [] => none
  | .Lbranch target :: _ => some target
  | .Lcond _ _ _ _ :: _ | .Ljumptable _ _ :: _ | .Ltailcall _ _ :: _ | .Lreturn :: _ => none
  | _ :: rest => branchTarget rest

def layoutBlock (source : LTL.function) (joins : Std.HashSet Nat) :
    Nat → positive → Std.HashSet Nat → List positive →
      List positive × List positive × Std.HashSet Nat
  | 0, node, visited, block => (block.reverse, [node], visited)
  | fuel + 1, node, visited, block =>
      if visited.contains (posToNat node) then (block.reverse, [], visited)
      else
        let visited := visited.insert (posToNat node)
        let block := node :: block
        let instructions := (PTree.get node source.fn_code).getD []
        match branchTarget instructions with
        | some target =>
            if joins.contains (posToNat target) then (block.reverse, [target], visited)
            else layoutBlock source joins fuel target visited block
        | none => (block.reverse, LTL.successors_block instructions, visited)

def enumerateBlocks (source : LTL.function) : List positive :=
  let bound := (PTree.elements source.fn_code).length + 1
  let joins := joinPoints source
  let rec visit : Nat → List positive → Std.HashSet Nat → List (Nat × List positive) →
      List (Nat × List positive)
    | 0, _, _, blocks => blocks
    | _ + 1, [], _, blocks => blocks
    | fuel + 1, node :: pending, visited, blocks =>
        if visited.contains (posToNat node) then visit fuel pending visited blocks
        else
          let (block, successors, visited) := layoutBlock source joins bound node visited []
          let minimum := block.foldl (fun minimum node => min minimum (posToNat node)) (posToNat node)
          visit fuel (successors ++ pending) visited ((minimum, block) :: blocks)
  let edges := (PTree.elements source.fn_code).foldl
    (fun count (_, block) => count + (LTL.successors_block block).length) 0
  ((visit (edges + 1) [source.fn_entrypoint] {} []).mergeSort
    (fun left right => left.1 ≥ right.1)).flatMap Prod.snd

end CompCert4Lean.Prototype
