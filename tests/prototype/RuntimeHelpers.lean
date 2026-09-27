import CompCert4Lean.Prototype.Services

open CompCert4Lean CompCert4Lean.Prototype
open Foundation.Numbers.Rocq.Coq Common.AST Common.Switch Backend Lib.Maps

def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def tests : Except String Unit := do
  let modulus := zOfInt ((2 : Int)^32)
  let dense := (List.range 12).map (fun index => (zOfInt (Int.ofNat index + 20), index))
  let tables := [[], [(zOfInt 0, 1)], [(zOfInt 0, 1), (zOfInt 0, 2)], dense,
    dense ++ [(zOfInt 20, 100)], [(zOfInt 0, 1), (zOfInt ((2 : Int)^32 - 1), 2)],
    (List.range 50).map (fun index => (zOfInt (Int.ofNat index * 100), index))]
  for cases in tables do
    require (validate_switch modulus 999 cases (compileSwitch modulus 999 cases)) "switch validator"
  require (match compileSwitch modulus 999 dense with | .CTjumptable .. => true | _ => false) "dense table"
  require (match compileSwitch modulus 999 (tables.getLast!) with | .CTiflt .. => true | _ => false) "balanced tree"
  require (!(validate_switch modulus 999 dense (.CTaction 999))) "invalid switch accepted"
  let modulus64 := zOfInt ((2 : Int)^64)
  let boundaries := [(zOfInt 0, 1), (zOfInt ((2 : Int)^64 - 1), 2)]
  require (validate_switch modulus64 999 boundaries (compileSwitch modulus64 999 boundaries)) "64-bit boundaries"
  let upperDense := (List.range 9).map (fun index => (zOfInt ((2 : Int)^64 - 9 + Int.ofNat index), index))
  require (validate_switch modulus64 999 upperDense (compileSwitch modulus64 999 upperDense)) "64-bit upper jump table"
  let identifier := posOfNat 1
  let expression := Cminor.expr.Evar identifier
  let constant := Cminor.expr.Econst (.Ointconst Lib.Integers.Int.zero)
  let continuation := CminorSel.stmt.Sseq .Sskip
    (.Sifthenelse (.CEcond (.Ccompuimm .Cne Lib.Integers.Int.zero) (.Econs (.Evar identifier) .Enil)) .Sskip .Sskip)
  require (ifConversion true identifier expression expression constant .Tint .Sskip) "cheap integer select"
  require (!(ifConversion false identifier expression expression constant .Tint .Sskip)) "O0 select"
  require (!(ifConversion true identifier expression expression constant .Tfloat .Sskip)) "slow floating select"
  require (!(ifConversion true identifier expression expression constant .Tint continuation)) "continuation heuristic"
  let costly := Cminor.expr.Ebinop .Odivf constant constant
  require (!(ifConversion true identifier expression costly expression .Tint .Sskip)) "unbalanced cost"
  let product := Cminor.expr.Ebinop .Omul expression expression
  let repeated := Cminor.expr.Ebinop .Oadd product product
  require (!(ifConversion true identifier expression repeated repeated .Tint .Sskip))
    "duplicated arithmetic exceeds selection budget"
  let signature : signature := { sig_args := [], sig_res := .Xvoid, sig_cc := cc_default }
  let function : LTL.function :=
    { fn_sig := signature
      fn_stacksize := zOfInt 0
      fn_entrypoint := posOfNat 8
      fn_code := [(8, [.Lbranch (posOfNat 7)]),
        (7, [.Lcond (.Ccompuimm .Cne Lib.Integers.Int.zero) [.AX] (posOfNat 6) (posOfNat 5)]),
        (6, [.Lbranch (posOfNat 4)]), (5, [.Lbranch (posOfNat 4)]),
        (4, [.Lcond (.Ccompuimm .Cne Lib.Integers.Int.zero) [.AX] (posOfNat 8) (posOfNat 3)]),
        (3, [.Lreturn]), (9, [.Lreturn])].foldl
          (fun code (node, block) => PTree.set (posOfNat node) block code) (PTree.empty _) }
  let nodes := enumeration function
  require (nodes.map posToNat == [8, 7, 6, 5, 4, 3]) "block ordering, loop or unreachable block"
  require (nodes.map posToNat == (enumeration function).map posToNat) "nondeterministic layout"
  require (match Linearize.enumerate enumeration function with | .OK _ => true | _ => false) "layout validator"
  require (match Linearize.enumerate (fun _ => []) function with | .Error _ => true | _ => false) "invalid layout accepted"
  require (optimizedCfg.options.optimTailcalls && optimizedCfg.options.optimConstprop &&
    optimizedCfg.options.optimCSE && optimizedCfg.options.optimRedundancy &&
    optimizedCfg.options.propagateFloatConstants && optimizedCfg.options.generateFloatConstants &&
    !optimizedCfg.options.optimForSize && !optimizedCfg.options.debug) "optimized profile"

def main : IO UInt32 := do
  match tests with
  | .ok () => IO.println "runtime helpers: PASS"; return 0
  | .error message => IO.eprintln message; return 1
