import CompCert4Lean.Lib.Maps

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps

example (fallback : Nat) (key : positive) (mapping : PTree.t Nat) :
    PTree.getDefault fallback key mapping = (PTree.get key mapping).getD fallback :=
  PTree.getDefault_eq fallback key mapping

#eval show IO Unit from do
  let mut mapping : PMap.t Nat := PMap.init 901
  for key in List.range 129 do
    if key % 3 != 0 then
      mapping := PMap.set (posOfNat (key + 1)) (key * key + 17) mapping
  for key in List.range 257 do
    let expected := if key < 129 && key % 3 != 0 then key * key + 17 else 901
    unless PMap.getDirect (posOfNat (key + 1)) mapping == expected do
      throw (IO.userError "direct default lookup returned an incorrect value")
  for key in [1024, 1048576, 1073741824] do
    unless PMap.getDirect (posOfNat key) mapping == 901 do
      throw (IO.userError "deep absent key lost the default")
  IO.println "direct default map lookup: PASS"

#print axioms CompCert4Lean.Lib.Maps.PTree.getDefault_eq
#print axioms CompCert4Lean.Lib.Maps.PMap.get_eq_getDirect
