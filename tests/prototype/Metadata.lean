import CompCert4Lean.Prototype.Main

open CompCert4Lean CompCert4Lean.Prototype
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

def metadataSamples : Nat → List (List Nat)
  | 0 => [[]]
  | fuel + 1 => (metadataSamples fuel).flatMap fun rest =>
      [rest, 1 :: rest, 2 :: rest, 3 :: rest, (2 ^ 130 + 17) :: rest]

#eval show IO Unit from do
  for keys in metadataSamples 5 do
    let entries := keys.zipIdx |>.map fun (key, value) => (posOfNat key, value)
    let indexed := indexIdentifiers entries
    let unique := keys.eraseDups.length == keys.length
    unless indexed.isSome == unique do
      throw (IO.userError s!"duplicate validation changed for {keys}")
    if let some index := indexed then
      for query in [1, 2, 3, 4, 2 ^ 130 + 17, 2 ^ 130 + 18] do
        let identifier := posOfNat query
        let expected := (entries.find? fun entry => entry.1 == identifier).map Prod.snd
        unless Lib.Maps.PTree.get identifier index == expected do
          throw (IO.userError s!"lookup changed for {keys}, key {query}")
  IO.println "metadata index: PASS"
