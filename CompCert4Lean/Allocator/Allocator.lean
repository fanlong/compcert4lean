import CompCert4Lean.Allocator.LTL
import CompCert4Lean.Backend.Allocation

namespace CompCert4Lean.Allocator

open Backend Common.Errors

def allocationStatistics (function : XFunction) (target : LTL.function) (coloring : Coloring)
    (rounds reused removed words dead : Nat)
    : AllocationStats := Id.run do
  let mut stats : AllocationStats := {
    pseudoRegisters := function.variables.size - X86.Machregs.all_mregs.length
    rounds, reloadsReused := reused, movesRemoved := removed, stackWords := words
    coalesced := coloring.coalesced, deadInstructions := dead }
  let mut machine : IndexSet := {}
  let mut slots : IndexSet := {}
  for (_, block) in Lib.Maps.PTree.elements target.fn_code do
    for instruction in (show List LTL.instruction from block) do
      for location in emittedLocations instruction do
        match location with
        | .R register => machine := machine.insert (machineIndex register)
        | .S .Local offset _ => slots := slots.insert (Foundation.Numbers.Rocq.Coq.intOfZ offset).toNat
        | _ => pure ()
      match instruction with
      | .Lsetstack _ .Local .. => stats := { stats with spills := stats.spills + 1 }
      | .Lgetstack .Local .. => stats := { stats with reloads := stats.reloads + 1 }
      | _ => pure ()
  return { stats with machineRegisters := machine.size, stackSlots := slots.size }

def allocationRounds (configuration : Config.CompilerConfig) (context : AllocationContext)
    (original : XFunction) (dead : Nat) : Nat → Nat → IndexSet →
      Except String (LTL.function × AllocationStats)
  | 0, _, _ => .error "register allocation did not converge within 40 rounds"
  | fuel + 1, round, spilled => do
      let (function, reused) ← if round == 0 then pure (original, 0) else insertSpills original spilled round
      let liveness ← analyzeLiveness function
      let coloring ← findColoring configuration context function liveness
      let needed ← neededSpills function coloring
      if needed.isEmpty then
        let (result, removed, words) ← emitLTL function coloring
        return (result, allocationStatistics function result coloring (round + 1) reused removed words dead)
      else
        if needed.toList.any (fun index => index >= original.variables.size) then
          throw "spill temporary could not be allocated"
        allocationRounds configuration context original dead fuel (round + 1) (setUnion spilled needed)

def allocate (configuration : Config.CompilerConfig) (context : AllocationContext)
    (source : RTL.function) : Except String (LTL.function × AllocationStats) := do
  if X86_64.Archi.win64 configuration then throw "allocator requires the System V x86-64 profile"
  unless reservedWellFormed context do throw "invalid reserved-register allocation context"
  let types ← match RTLtyping.type_function configuration source with
    | .OK types => pure types
    | .Error _ => throw "register allocator received ill-typed RTL"
  let initial ← buildXTL configuration source types
  let liveness ← analyzeLiveness initial
  let (original, dead) := eliminateDeadCode initial liveness
  allocationRounds configuration context original dead 40 0 {}

def regalloc (configuration : Config.CompilerConfig) (context : AllocationContext)
    : Allocation.RegallocOracle := fun source =>
  match allocate configuration context source with
  | .ok (result, _) => .OK result
  | .error message => .Error (msg (message.toUTF8.toList.foldr .String .EmptyString))

end CompCert4Lean.Allocator
