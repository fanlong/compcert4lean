import CompCert4Lean.Prototype.Services

open CompCert4Lean CompCert4Lean.Prototype
open Foundation.Numbers.Rocq.Coq Common.AST Backend Lib.Maps

def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def makeFunction (entry : Nat) (nodes : List (Nat × LTL.bblock)) : LTL.function :=
  { fn_sig := { sig_args := [], sig_res := .Xvoid, sig_cc := cc_default }
    fn_stacksize := zOfInt 0
    fn_entrypoint := posOfNat entry
    fn_code := nodes.foldl (fun code (node, block) => PTree.set (posOfNat node) block code) (PTree.empty _) }

def checkFunction (source : LTL.function) : Except String Unit := do
  let original := (enumeration source).map posToNat
  let candidate := (enumerationFor optimizedCfg source).map posToNat
  require (original.mergeSort (· <= ·) == candidate.mergeSort (· <= ·)) "layout node coverage"
  require ((enumerationFor cfg source).map posToNat == original) "O0 layout changed"
  require ((enumerationFor optimizedCfg source).map posToNat == candidate) "nondeterministic layout"
  require (match Linearize.enumerate (enumerationFor optimizedCfg) source with
    | .OK _ => true | .Error _ => false) "layout validator rejected proposal"
  if !hasLayoutCycle source then
    require (candidate == original) "acyclic layout changed"

def tests : Except String Unit := do
  let source := makeFunction 8 [
    (8, [.Lbranch (posOfNat 7)]),
    (7, [.Lcond (.Ccompuimm .Cne Lib.Integers.Int.zero) [.AX] (posOfNat 6) (posOfNat 5)]),
    (6, [.Lbranch (posOfNat 4)]), (5, [.Lbranch (posOfNat 4)]),
    (4, [.Lcond (.Ccompuimm .Cne Lib.Integers.Int.zero) [.AX] (posOfNat 8) (posOfNat 3)]),
    (3, [.Lreturn]), (9, [.Lreturn])]
  checkFunction source
  require (hasLayoutCycle source) "reachable cycle was missed"
  require ((enumerationFor optimizedCfg source).map posToNat == [8, 7, 6, 4, 3, 5]) "trace ordering"
  let acyclic := makeFunction 1 [
    (1, [.Lcond (.Ccompuimm .Cne Lib.Integers.Int.zero) [.AX] (posOfNat 8) (posOfNat 3)]),
    (8, [.Lbranch (posOfNat 4)]), (3, [.Lbranch (posOfNat 4)]), (4, [.Lreturn]),
    (9, [.Lbranch (posOfNat 9)])]
  checkFunction acyclic
  require (!hasLayoutCycle acyclic) "an unreachable cycle or forward edge changed acyclic layout"
  let selfLoop := makeFunction 7 [(7, [.Lbranch (posOfNat 7)])]
  checkFunction selfLoop
  require (hasLayoutCycle selfLoop) "a self-loop was missed"
  let large := makeFunction 2050 ((List.range 2050).map fun index =>
    let node := index + 1
    (node, [.Lbranch (posOfNat (if node == 1 then 2050 else node - 1))]))
  require ((enumerationFor optimizedCfg large).map posToNat ==
    (enumeration large).map posToNat) "large-function fallback changed layout"
  for seed in [:200] do
    let count := 3 + seed % 29
    let nodes := (List.range count).map fun index =>
      let node := index + 1
      let first := posOfNat (1 + (node * 17 + seed) % count)
      let second := posOfNat (1 + (node * 11 + seed * 3) % count)
      let block : LTL.bblock := match (node + seed) % 4 with
        | 0 => [.Lreturn]
        | 1 => [.Lbranch first]
        | 2 => [.Lcond (.Ccompuimm .Cne Lib.Integers.Int.zero) [.AX] first second]
        | _ => [.Ljumptable .AX [first, second, posOfNat count]]
      (node, block)
    checkFunction (makeFunction count nodes)

def main : IO UInt32 := do
  match tests with
  | .ok () => IO.println "loop layout: PASS"; return 0
  | .error message => IO.eprintln message; return 1

#print axioms CompCert4Lean.Prototype.enumerateLoopBlocks
