import CompCert4Lean.Prototype.Services

namespace CompCert4Lean.Prototype

open Allocator Backend Foundation.Numbers.Rocq.Coq

def traceResult {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

def traceCoreResult {α : Type} (result : Common.Errors.res α) : IO α :=
  match result with
  | .OK value => pure value
  | .Error errors => throw (IO.userError (errorText errors))

def traceAllocationRounds (configuration : Config.CompilerConfig) (context : AllocationContext)
    (original : XFunction) (emit : String → IO Unit) :
    Nat → Nat → IndexSet → IO LTL.function
  | 0, _, _ => throw (IO.userError "allocation trace exhausted rounds")
  | fuel + 1, round, spilled => do
      let stagePrefix := "round-" ++ toString round ++ "-"
      let (function, _) ← traceResult (if round == 0 then .ok (original, 0) else insertSpills original spilled round)
      emit (stagePrefix ++ "spills")
      let live ← traceResult (analyzeLiveness function)
      emit (stagePrefix ++ "liveness")
      let graph := buildInterference configuration function live
      emit (stagePrefix ++ "interference-" ++ toString graph.present.size)
      let initial := initialColoring context function graph
      emit (stagePrefix ++ "initial-" ++ toString initial.moves.size)
      let bound := function.variables.size + initial.moves.size + 1
      let state ← traceResult (colorWorklists context function (bound * bound * bound) initial)
      emit (stagePrefix ++ "worklists")
      let coloring ← traceResult (assignColors context function state)
      emit (stagePrefix ++ "colors")
      let needed ← traceResult (neededSpills function coloring)
      emit (stagePrefix ++ "needed-" ++ toString needed.size)
      if needed.isEmpty then
        let (target, _, _) ← traceResult (emitLTL function coloring)
        emit (stagePrefix ++ "emitted")
        return target
      else
        traceAllocationRounds configuration context original emit fuel (round + 1) (setUnion spilled needed)

def traceAllocation (configuration : Config.CompilerConfig) (context : AllocationContext)
    (program : RTL.program) (emit : String → IO Unit) : IO Unit := do
  for (identifier, definition) in program.prog_defs do
    if let .Gfun (.Internal function) := definition then
      let emit := fun stage => emit ("function-" ++ toString (posToNat identifier) ++ "-" ++ stage)
      emit "start"
      let types ← traceCoreResult (RTLtyping.type_function configuration function)
      emit "typed"
      let initial ← traceResult (buildXTL configuration function types)
      emit ("xtl-" ++ toString initial.variables.size)
      let live ← traceResult (analyzeLiveness initial)
      emit "live"
      let (original, _) := eliminateDeadCode initial live
      let target ← traceAllocationRounds configuration context original emit 40 0 {}
      emit "allocated"
      let _ ← traceCoreResult (Allocation.check_function configuration function target types)
      emit "validated"

end CompCert4Lean.Prototype
