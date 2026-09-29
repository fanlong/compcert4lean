import CompCert4Lean.Allocator.Coloring

open CompCert4Lean CompCert4Lean.Allocator Common.AST
open Foundation.Numbers.Rocq.Coq

namespace FreezeSelection

def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def function : XFunction := {
  signature := { sig_args := [], sig_res := .Xint, sig_cc := cc_default }
  stacksize := Z0
  variables := Array.replicate 64 { type := .Tint }
  blocks := #[]
  entry := 0 }

def stateWith (frozen : List Nat) (costs : Array SpillCost)
    (degrees : Array Nat := Array.replicate 64 1) : ColoringState := {
  graph := {
    adjacency := Array.replicate 64 {}
    preferences := Array.replicate 64 {}
    costs
    present := setOfList frozen }
  parents := (List.range 64).toArray
  active := setOfList frozen
  freeze := setOfList frozen
  nodeMoves := Array.replicate 64 {}
  degrees }

def tests : Except String Unit := do
  let costs := (Array.replicate 64 { amount := 100 : SpillCost }).set!
    7 { amount := 10 } |>.set! 11 { amount := 500 }
  let state := stateWith [11, 2, 7] costs
  require (freezeCandidate function (stateWith [] costs) == none)
    "empty freeze worklist produced a candidate"
  require (freezeCandidate function state == some 7)
    "freeze selection discarded the hotter move opportunity"
  require (freezeCandidate function (stateWith [2, 7, 11]
    (costs.set! 7 { amount := 10, unspillable := true })) == some 2)
    "freeze priority ignored an unspillable temporary"
  require (freezeCandidate function (stateWith [2, 7, 11] costs
    ((Array.replicate 64 1).set! 11 10)) == some 11)
    "freeze priority ignored interference degree"
  let tied := Array.replicate 64 { amount := 10 : SpillCost }
  require (freezeCandidate function (stateWith [11, 7, 2] tied) == some 2)
    "equal freeze scores lost stable index ordering"
  let bounded := (Array.replicate 64 { amount := 100 : SpillCost }).set!
    31 { amount := 1 } |>.set! 32 { amount := 0 } |>.set! 63 { amount := 0 }
  require (freezeCandidate function (stateWith (List.range 64) bounded) == some 31)
    "freeze search exceeded its 32-node budget"
  require (freezeCandidate function (stateWith ((List.range 64).filter (· != 31)) bounded) == some 32)
    "freeze search counted removed nodes against its budget"
  for frozen in [[], [4], [63, 2, 19], [1000000000, 1], List.range 64] do
    let selected := stateWith frozen costs
    match freezeCandidate function selected with
    | none => require selected.freeze.isEmpty "nonempty freeze worklist lost every candidate"
    | some index => require (selected.freeze.contains index) "freeze selection escaped its worklist"

def main : IO UInt32 := do
  match tests with
  | .ok () => IO.println "bounded freeze priority: PASS"; return 0
  | .error message => IO.eprintln message; return 1

end FreezeSelection

def main := FreezeSelection.main

#print axioms CompilerOptimization.BoundedTreeCount.findColoringCount_csimp
