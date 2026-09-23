import CompCert4Lean.Allocator.Spilling
import CompCert4Lean.Backend.LTL

namespace CompCert4Lean.Allocator

open Common.AST Backend.Locations Backend.LTL X86.Machregs
open Foundation.Numbers.Rocq.Coq Lib.Maps

def locationClass : loc → Nat
  | .R register => machineClass register
  | .S _ _ type => registerClass type

def emitMove (source destination : loc) : Except String (List instruction) :=
  if locEqual source destination then .ok [] else
  match source, destination with
  | .R source, .R destination => .ok [.Lop .Omove [source] destination]
  | .R source, .S slot offset type => .ok [.Lsetstack source slot offset type]
  | .S slot offset type, .R destination => .ok [.Lgetstack slot offset type destination]
  | .S .., .S .. => .error "unresolved stack-to-stack move"

def emitParallelCopy (source destination : loc) (integerTemp floatTemp : mreg)
    : Except String (List instruction) :=
  if locEqual source destination then .ok [] else
  match source, destination with
  | .S sourceSlot sourceOffset sourceType, .S destinationSlot destinationOffset destinationType =>
      let temporary := if locationClass source == 0 then integerTemp else floatTemp
      .ok [.Lgetstack sourceSlot sourceOffset sourceType temporary,
           .Lsetstack temporary destinationSlot destinationOffset destinationType]
  | _, _ => emitMove source destination

def replaceMoveSources (source replacement : loc) (moves : List (loc × loc)) : List (loc × loc) :=
  moves.map fun (original, destination) =>
    (if locEqual original source then replacement else original, destination)

def parallelMoves (integerTemp floatTemp : mreg) : Nat → List (loc × loc) → Nat →
    List instruction → Except String (List instruction × Nat)
  | 0, _, _, _ => .error "parallel move resolution exhausted its bound"
  | _ + 1, [], nextSlot, code => .ok (code, nextSlot)
  | fuel + 1, moves, nextSlot, code => do
      let ready := moves.findIdx? fun (_, destination) =>
        moves.all fun (source, _) => locDisjoint destination source
      if let some index := ready then
        let some (source, destination) := moves[index]? | throw "invalid parallel move index"
        let mut pending := moves.eraseIdx index
        let mut preceding := []
        let mut nextSlot := nextSlot
        if let .S .. := source then
          if let .S .. := destination then
            let temporary := if locationClass source == 0 then integerTemp else floatTemp
            if pending.any (fun (source, _) => locEqual source (.R temporary)) then
              let type := if machineClass temporary == 0 then typ.Tany64 else typ.Tfloat
              let saved := loc.S .Local (ZArith.BinInt.Z.of_nat nextSlot) type
              preceding ← emitMove (.R temporary) saved
              pending := replaceMoveSources (.R temporary) saved pending
              nextSlot := nextSlot + 2
        let copy ← emitParallelCopy source destination integerTemp floatTemp
        parallelMoves integerTemp floatTemp fuel pending nextSlot (code ++ preceding ++ copy)
      else
        let some (source, _) := moves.head? | throw "empty unresolved parallel move"
        let temporary := if locationClass source == 0 then integerTemp else floatTemp
        let mut moves := moves
        let mut code := code
        let mut nextSlot := nextSlot
        if moves.any (fun (source, _) => locEqual source (.R temporary)) then
          let type := if machineClass temporary == 0 then typ.Tany64 else typ.Tfloat
          let saved := loc.S .Local (ZArith.BinInt.Z.of_nat nextSlot) type
          code := code ++ (← emitMove (.R temporary) saved)
          moves := replaceMoveSources (.R temporary) saved moves
          nextSlot := nextSlot + 2
        let saved := loc.R temporary
        let copy ← emitMove source saved
        parallelMoves integerTemp floatTemp fuel (replaceMoveSources source saved moves) nextSlot (code ++ copy)

def resolveParallelMoves (sources destinations : List loc) (integerTemp floatTemp : mreg)
    (nextSlot : Nat) : Except String (List instruction × Nat) := do
  unless sources.length == destinations.length do throw "parallel move arity mismatch"
  unless machineClass integerTemp == 0 && machineClass floatTemp == 1 do
    throw "parallel move temporary has the wrong register class"
  unless (sources ++ destinations).all (fun location =>
    locDisjoint location (.R integerTemp) && locDisjoint location (.R floatTemp)) do
    throw "parallel move temporary aliases an operand"
  let moves := (sources.zip destinations).filter fun (source, destination) => !locEqual source destination
  let bound := (moves.length + 1) * (moves.length + 1) * 4
  parallelMoves integerTemp floatTemp bound moves nextSlot []

def allocatedBuiltinResult (coloring : Coloring) : builtin_res Nat → Except String (builtin_res mreg)
  | .BR index => return .BR (← allocatedRegister coloring index)
  | .BR_none => return .BR_none
  | .BR_splitlong high low =>
      return .BR_splitlong (← allocatedBuiltinResult coloring high) (← allocatedBuiltinResult coloring low)

def allocatedBuiltinArg (coloring : Coloring) : builtin_arg Nat → Except String (builtin_arg loc)
  | .BA index => return .BA (← allocatedLocation coloring index)
  | .BA_int value => return .BA_int value
  | .BA_long value => return .BA_long value
  | .BA_float value => return .BA_float value
  | .BA_single value => return .BA_single value
  | .BA_loadstack chunk offset => return .BA_loadstack chunk offset
  | .BA_addrstack offset => return .BA_addrstack offset
  | .BA_loadglobal chunk symbol offset => return .BA_loadglobal chunk symbol offset
  | .BA_addrglobal symbol offset => return .BA_addrglobal symbol offset
  | .BA_splitlong high low =>
      return .BA_splitlong (← allocatedBuiltinArg coloring high) (← allocatedBuiltinArg coloring low)
  | .BA_addptr left right =>
      return .BA_addptr (← allocatedBuiltinArg coloring left) (← allocatedBuiltinArg coloring right)

def allocatedTarget (coloring : Coloring) : Sum Nat ident → Except String (Sum mreg ident)
  | .inl index => return .inl (← allocatedRegister coloring index)
  | .inr symbol => return .inr symbol

def emitInstruction (coloring : Coloring) (source : XInstruction) (nextSlot : Nat)
    : Except String (List instruction × Nat) := do
  if let .parmove sources destinations integerTemp floatTemp := source then
    return ← resolveParallelMoves (← sources.mapM (allocatedLocation coloring))
      (← destinations.mapM (allocatedLocation coloring)) (← allocatedRegister coloring integerTemp)
      (← allocatedRegister coloring floatTemp) nextSlot
  let code ← match source with
    | .move source destination | .reload source destination | .spill source destination =>
        emitMove (← allocatedLocation coloring source) (← allocatedLocation coloring destination)
    | .parmove .. => throw "unhandled parallel move"
    | .op operation arguments destination => do
        let arguments ← arguments.mapM (allocatedRegister coloring)
        let destination ← allocatedRegister coloring destination
        if twoAddress operation then
          if let source :: rest := arguments then
            unless regEqual source destination || !rest.any (regEqual destination) do
              throw "two-address result overlaps a remaining operand"
            pure ((← emitMove (.R source) (.R destination)) ++ [.Lop operation (destination :: rest) destination])
          else throw "two-address operation has no source operand"
        else pure [.Lop operation arguments destination]
    | .load chunk address arguments destination => do
        pure [.Lload chunk address (← arguments.mapM (allocatedRegister coloring)) (← allocatedRegister coloring destination)]
    | .store chunk address arguments source => do
        pure [.Lstore chunk address (← arguments.mapM (allocatedRegister coloring)) (← allocatedRegister coloring source)]
    | .call sign target _ _ => do pure [.Lcall sign (← allocatedTarget coloring target)]
    | .tailcall sign target _ => do pure [.Ltailcall sign (← allocatedTarget coloring target)]
    | .builtin external arguments result => do
        pure [.Lbuiltin external (← arguments.mapM (allocatedBuiltinArg coloring)) (← allocatedBuiltinResult coloring result)]
    | .branch successor => pure [.Lbranch successor]
    | .cond condition arguments ifTrue ifFalse => do
        pure [.Lcond condition (← arguments.mapM (allocatedRegister coloring)) ifTrue ifFalse]
    | .jumptable argument targets => do pure [.Ljumptable (← allocatedRegister coloring argument) targets]
    | .ret _ => pure [.Lreturn]
  return (code, nextSlot)

def allocatedStackWords (coloring : Coloring) : Nat :=
  coloring.locations.foldl (fun count location => match location with
    | .S .Local offset type => max count ((intOfZ offset).toNat + slotWords type)
    | _ => count) 0

def emittedLocations : instruction → List loc
  | .Lop _ arguments result | .Lload _ _ arguments result | .Lstore _ _ arguments result =>
      (result :: arguments).map loc.R
  | .Lgetstack slot offset type register | .Lsetstack register slot offset type =>
      [.R register, .S slot offset type]
  | .Lcall _ (.inl target) | .Ltailcall _ (.inl target) => [.R target]
  | .Lbuiltin _ arguments result => params_of_builtin_args arguments ++ (params_of_builtin_res result).map loc.R
  | .Lcond _ arguments _ _ => arguments.map loc.R
  | .Ljumptable argument _ => [.R argument]
  | _ => []

def emitLTL (function : XFunction) (coloring : Coloring) : Except String (Backend.LTL.function × Nat × Nat) := do
  let mut code := PTree.empty (List instruction)
  let mut nextSlot := allocatedStackWords coloring
  let mut removed := 0
  for block in function.blocks do
    let mut instructions := []
    for source in block.instructions do
      let (emitted, afterSlot) ← emitInstruction coloring source nextSlot
      nextSlot := afterSlot
      match source with
      | .move .. | .spill .. | .reload .. => if emitted.isEmpty then removed := removed + 1
      | .parmove sources _ _ _ => removed := removed + (sources.length - emitted.length)
      | _ => pure ()
      instructions := instructions ++ emitted
    code := PTree.set block.source instructions code
  let some entry := function.blocks[function.entry]? | throw "invalid allocated function entry"
  return ({ fn_sig := function.signature, fn_stacksize := function.stacksize
            fn_code := code, fn_entrypoint := entry.source }, removed, nextSlot)

end CompCert4Lean.Allocator
