import CompCert4Lean.Allocator.SplitRanges
import CompCert4Lean.Backend.Conventions

namespace CompCert4Lean.Allocator

open Common.AST Backend Backend.Registers Backend.Locations Lib.Maps
open X86.Machregs X86.Op Foundation.Numbers.Rocq.Coq

inductive XInstruction where
  | move (source destination : Nat)
  | reload (source destination : Nat)
  | spill (source destination : Nat)
  | parmove (sources destinations : List Nat) (integerTemp floatTemp : Nat)
  | op (operation : operation) (arguments : List Nat) (destination : Nat)
  | load (chunk : memory_chunk) (address : addressing) (arguments : List Nat) (destination : Nat)
  | store (chunk : memory_chunk) (address : addressing) (arguments : List Nat) (source : Nat)
  | call (sign : signature) (target : Sum Nat ident) (arguments results : List Nat)
  | tailcall (sign : signature) (target : Sum Nat ident) (arguments : List Nat)
  | builtin (external : external_function) (arguments : List (builtin_arg Nat)) (result : builtin_res Nat)
  | branch (successor : RTL.node)
  | cond (condition : condition) (arguments : List Nat) (ifTrue ifFalse : RTL.node)
  | jumptable (argument : Nat) (targets : List RTL.node)
  | ret (arguments : List Nat)

structure XBlock where
  source : RTL.node
  instructions : List XInstruction
  successors : List Nat := []
  predecessors : List Nat := []

structure XFunction where
  signature : signature
  stacksize : Z
  variables : Array Variable
  blocks : Array XBlock
  entry : Nat

def variableInfo (function : XFunction) (index : Nat) : Variable :=
  function.variables[index]?.getD { type := .Tint }

structure BuildState where
  variables : Array Variable

abbrev BuildM := StateT BuildState (Except String)

def fresh (type : typ) : BuildM Nat := do
  let state ← get
  let index := state.variables.size
  set { state with variables := state.variables.push { type } }
  return index

def fixed (location : loc) : BuildM Nat := do
  let state ← get
  for index in [:state.variables.size] do
    if let some previous := (state.variables[index]?.getD { type := .Tint }).fixed then
      if locEqual previous location then return index
  let index := state.variables.size
  set { state with variables := state.variables.push {
    type := Loc.type location, fixed := some location } }
  return index

def moveList (sources destinations : List Nat) : Except String (List XInstruction) := do
  unless sources.length == destinations.length do throw "mismatched XTL move arity"
  return (sources.zip destinations).filterMap fun (source, destination) =>
    if source == destination then none else some (.move source destination)

def parallel (sources destinations : List Nat) : BuildM (List XInstruction) := do
  unless sources.length == destinations.length do throw "mismatched XTL parallel move arity"
  match sources, destinations with
  | [], [] => return []
  | [_], [_] => moveList sources destinations
  | _, _ => return [.parmove sources destinations (← fresh .Tint) (← fresh .Tfloat)]

def fixedPairs (locations : List (rpair loc)) : BuildM (List Nat) :=
  locations.mapM fun
    | .One location => fixed location
    | .Twolong _ _ => throw "split-long calling convention is outside the x86-64 profile"

def constrainRegisters (variables : List Nat) (constraints : List (Option mreg)) : List Nat :=
  match variables, constraints with
  | [], _ => []
  | _, [] => variables
  | value :: rest, constraint :: tail =>
      (constraint.map machineIndex |>.getD value) :: constrainRegisters rest tail

def constrainBuiltinArg : builtin_arg Nat → List (Option mreg) →
    builtin_arg Nat × List (Option mreg)
  | .BA value, constraint :: rest =>
      (.BA (constraint.map machineIndex |>.getD value), rest)
  | .BA_splitlong high low, constraints =>
      let (high, rest) := constrainBuiltinArg high constraints
      let (low, rest) := constrainBuiltinArg low rest
      (.BA_splitlong high low, rest)
  | .BA_addptr left right, constraints =>
      let (left, rest) := constrainBuiltinArg left constraints
      let (right, rest) := constrainBuiltinArg right rest
      (.BA_addptr left right, rest)
  | argument, constraints => (argument, constraints)

def constrainBuiltinArgs : List (builtin_arg Nat) → List (Option mreg) →
    List (builtin_arg Nat) × List (Option mreg)
  | [], constraints => ([], constraints)
  | argument :: rest, constraints =>
      let (argument, constraints) := constrainBuiltinArg argument constraints
      let (rest, constraints) := constrainBuiltinArgs rest constraints
      (argument :: rest, constraints)

def constrainBuiltinResult : builtin_res Nat → List (Option mreg) →
    builtin_res Nat × List (Option mreg)
  | .BR value, constraint :: rest =>
      (.BR (constraint.map machineIndex |>.getD value), rest)
  | .BR_splitlong high low, constraints =>
      let (high, rest) := constrainBuiltinResult high constraints
      let (low, rest) := constrainBuiltinResult low rest
      (.BR_splitlong high low, rest)
  | result, constraints => (result, constraints)

def resultLocation (sign : signature) : BuildM Nat :=
  match X86.Conventions1.loc_result sign with
  | .One register => pure (machineIndex register)
  | .Twolong _ _ => throw "split-long result is outside the x86-64 profile"

def makeBlock (configuration : Config.CompilerConfig) (sign : signature)
    (types : RTLtyping.regenv) (ranges : RangeState) (info : RangeInfo)
    (instruction : RTL.instruction) : BuildM (List XInstruction) := do
  unless (RTL.instr_uses instruction).all (fun register => info.before.contains (regKey register)) &&
      (RTL.instr_defs instruction).toList.all (fun register => info.definitions.contains (regKey register)) do
    throw "incomplete live-range map for RTL instruction"
  let use := fun register =>
    rangeRoot ranges.parents ((info.before[regKey register]?).getD 0)
  let define := fun register =>
    rangeRoot ranges.parents ((info.definitions[regKey register]?).getD 0)
  let target := fun
    | .inl register => Sum.inl (use register)
    | .inr identifier => Sum.inr identifier
  match instruction with
  | .Inop successor => return [.branch successor]
  | .Iop .Omove [argument] destination successor =>
      return (← moveList [use argument] [define destination]) ++ [.branch successor]
  | .Iop operation arguments destination successor =>
      let (argumentConstraints, resultConstraint) := operationConstraints operation
      let sources := arguments.map use
      let result := define destination
      let constrainedArgs := constrainRegisters sources argumentConstraints
      let constrainedResult := resultConstraint.map machineIndex |>.getD result
      let (actualArgs, actualResult) ←
        if twoAddress operation && constrainedArgs.head? != some constrainedResult &&
            constrainedArgs.tail.contains constrainedResult then do
          let temporary ← fresh (types destination)
          pure (temporary :: constrainedArgs.tail, temporary)
        else pure (constrainedArgs, constrainedResult)
      return (← moveList sources actualArgs) ++ [.op operation actualArgs actualResult] ++
        (← moveList [actualResult] [result]) ++ [.branch successor]
  | .Iload chunk address arguments destination successor =>
      return [.load chunk address (arguments.map use) (define destination), .branch successor]
  | .Istore chunk address arguments source successor =>
      return [.store chunk address (arguments.map use) (use source), .branch successor]
  | .Icall callSign callee arguments destination successor =>
      let locations ← fixedPairs (X86.Conventions1.loc_arguments configuration callSign)
      let result ← resultLocation callSign
      return (← parallel (arguments.map use) locations) ++
        [.call callSign (target callee) locations [result]] ++
        (← parallel [result] [define destination]) ++ [.branch successor]
  | .Itailcall callSign callee arguments =>
      let locations ← fixedPairs (X86.Conventions1.loc_arguments configuration callSign)
      return (← parallel (arguments.map use) locations) ++ [.tailcall callSign (target callee) locations]
  | .Ibuiltin external arguments result successor =>
      let arguments := arguments.map (map_builtin_arg use)
      let result := map_builtin_res define result
      let (argumentConstraints, resultConstraints) := builtinConstraints external
      let (constrainedArgs, _) := constrainBuiltinArgs arguments argumentConstraints
      let (constrainedResult, _) := constrainBuiltinResult result resultConstraints
      return (← moveList (params_of_builtin_args arguments) (params_of_builtin_args constrainedArgs)) ++
        [.builtin external constrainedArgs constrainedResult] ++
        (← moveList (params_of_builtin_res constrainedResult) (params_of_builtin_res result)) ++
        [.branch successor]
  | .Icond condition arguments ifTrue ifFalse =>
      return [.cond condition (arguments.map use) ifTrue ifFalse]
  | .Ijumptable argument targets => return [.jumptable (use argument) targets]
  | .Ireturn none => return [.ret []]
  | .Ireturn (some argument) =>
      let result ← resultLocation sign
      return (← parallel [use argument] [result]) ++ [.ret [result]]

def buildXTL (configuration : Config.CompilerConfig) (source : RTL.function)
    (types : RTLtyping.regenv) : Except String XFunction := do
  let (ranges, parameters, instructions) ← splitLiveRanges source types
  let entryNode := PArith.BinPos.Pos.of_nat
    (1 + instructions.foldl (fun highest pair => max highest (regKey pair.1)) 0)
  let action : BuildM (Array XBlock) := do
    let mut blocks := #[]
    for index in [:instructions.size] do
      let some (node, instruction) := instructions[index]? | throw "invalid compact RTL index"
      let info := ranges.entries[index]?.getD {}
      let code ← makeBlock configuration source.fn_sig types ranges info instruction
      blocks := blocks.push { source := node, instructions := code
                              successors := info.successors, predecessors := info.predecessors }
    let some entry := instructions.toList.findIdx? (fun pair => regKey pair.1 == regKey source.fn_entrypoint) |
      throw "missing RTL entry point"
    let locations ← fixedPairs (Conventions.loc_parameters configuration source.fn_sig)
    let destinations := source.fn_params.map fun register =>
      rangeRoot ranges.parents ((parameters[regKey register]?).getD 0)
    let code ← parallel locations destinations
    let some first := blocks[entry]? | throw "missing compact entry block"
    blocks := blocks.set! entry { first with predecessors := blocks.size :: first.predecessors }
    return blocks.push { source := entryNode
                         instructions := code ++ [.branch source.fn_entrypoint]
                         successors := [entry] }
  let (blocks, state) ← action.run { variables := ranges.variables }
  return { signature := source.fn_sig, stacksize := source.fn_stacksize
           variables := state.variables, blocks, entry := blocks.size - 1 }

end CompCert4Lean.Allocator
