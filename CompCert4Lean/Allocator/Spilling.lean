import CompCert4Lean.Allocator.Coloring

namespace CompCert4Lean.Allocator

open Common.AST Backend.Locations

def allocatedLocation (coloring : Coloring) (index : Nat) : Except String loc :=
  match coloring.locations[index]? with
  | some location => .ok location
  | none => .error "allocation references an invalid variable index"

def allocatedRegister (coloring : Coloring) (index : Nat) : Except String X86.Machregs.mreg := do
  match ← allocatedLocation coloring index with
  | .R register => return register
  | .S .. => throw "machine register required for an allocated operand"

def requiresRegister : XInstruction → List Nat
  | .op _ arguments result | .load _ _ arguments result | .store _ _ arguments result => result :: arguments
  | .call _ target _ _ | .tailcall _ target _ => targetUses target
  | .builtin (.EF_annot ..) _ _ | .builtin (.EF_debug ..) _ _ => []
  | .builtin _ arguments result => params_of_builtin_args arguments ++ params_of_builtin_res result
  | .cond _ arguments _ _ => arguments
  | .jumptable argument _ => [argument]
  | _ => []

def neededSpills (function : XFunction) (coloring : Coloring) : Except String IndexSet := do
  let mut result : IndexSet := {}
  for block in function.blocks do
    for instruction in block.instructions do
      for index in requiresRegister instruction do
        if let .S .. := ← allocatedLocation coloring index then result := result.insert index
      match instruction with
      | .move source destination =>
          let sourceLocation ← allocatedLocation coloring source
          let destinationLocation ← allocatedLocation coloring destination
          match sourceLocation, destinationLocation with
          | .S .., .S .. =>
              if !locEqual sourceLocation destinationLocation then result := (result.insert source).insert destination
          | _, _ => pure ()
      | .reload _ destination => let _ ← allocatedRegister coloring destination; pure ()
      | .spill source _ => let _ ← allocatedRegister coloring source; pure ()
      | .parmove _ _ integerTemp floatTemp =>
          let _ ← allocatedRegister coloring integerTemp
          let _ ← allocatedRegister coloring floatTemp
          pure ()
      | _ => pure ()
  return result

structure Equation where
  value : Nat
  temporary : Nat
  age : Nat := 0

structure SpillState where
  variables : Array Variable
  equations : List Equation := []
  code : Array XInstruction := #[]
  reloadsReused : Nat := 0

abbrev SpillM := StateT SpillState (Except String)

def killEquation (value : Nat) (equations : List Equation) : List Equation :=
  equations.filter fun equation => equation.value != value && equation.temporary != value

def killValue (value : Nat) : SpillM Unit :=
  modify fun state => { state with equations := killEquation value state.equations }

def rememberValue (value temporary : Nat) : SpillM Unit :=
  modify fun state => { state with equations := { value, temporary } :: state.equations }

def emitSpill (instruction : XInstruction) : SpillM Unit :=
  modify fun state => { state with code := state.code.push instruction }

def spillTemporary (value : Nat) : SpillM Nat := do
  let state ← get
  let some info := state.variables[value]? | throw "spill references an invalid variable"
  let index := state.variables.size
  set { state with variables := state.variables.push { type := info.type } }
  return index

def reloadValue (spilled : IndexSet) (value : Nat) : SpillM Nat := do
  if !spilled.contains value then return value
  let state ← get
  if let some equation := state.equations.find? (fun equation => equation.value == value) then
    modify fun state => { state with reloadsReused := state.reloadsReused + 1 }
    return equation.temporary
  let temporary ← spillTemporary value
  emitSpill (.reload value temporary)
  rememberValue value temporary
  return temporary

def saveValue (spilled : IndexSet) (value : Nat) : SpillM (Nat × List XInstruction) := do
  killValue value
  if !spilled.contains value then return (value, [])
  let temporary ← spillTemporary value
  rememberValue value temporary
  return (temporary, [.spill temporary value])

def reloadBuiltin (spilled : IndexSet) : builtin_arg Nat → SpillM (builtin_arg Nat)
  | .BA value => return .BA (← reloadValue spilled value)
  | .BA_splitlong high low => return .BA_splitlong (← reloadBuiltin spilled high) (← reloadBuiltin spilled low)
  | .BA_addptr left right => return .BA_addptr (← reloadBuiltin spilled left) (← reloadBuiltin spilled right)
  | argument => return argument

def saveBuiltin (spilled : IndexSet) : builtin_res Nat → SpillM (builtin_res Nat × List XInstruction)
  | .BR value => do
      let (temporary, code) ← saveValue spilled value
      return (.BR temporary, code)
  | .BR_none => return (.BR_none, [])
  | .BR_splitlong high low => do
      let (high, highCode) ← saveBuiltin spilled high
      let (low, lowCode) ← saveBuiltin spilled low
      return (.BR_splitlong high low, highCode ++ lowCode)

def trimEquations : Nat → Nat → List Equation → List Equation
  | 0, _, _ => []
  | _, _, [] => []
  | count + 1, maxAge, equation :: rest =>
      if equation.age <= maxAge then
        { equation with age := equation.age + 1 } :: trimEquations count maxAge rest
      else []

def spillInstruction (spilled : IndexSet) (maxAge : Nat) (instruction : XInstruction) : SpillM Unit := do
  modify fun state => { state with equations := trimEquations 3 maxAge state.equations }
  match instruction with
  | .move source destination =>
      if spilled.contains source && spilled.contains destination then
        let temporary ← reloadValue spilled source
        emitSpill (.spill temporary destination)
        killValue destination
        rememberValue destination temporary
      else
        emitSpill instruction
        killValue destination
  | .reload .. | .spill .. => throw "spill rounds must restart from original XTL"
  | .parmove _ destinations _ _ =>
      emitSpill instruction
      destinations.forM killValue
  | .op operation arguments result =>
      match twoAddress operation, arguments with
      | true, first :: rest =>
          match spilled.contains result, spilled.contains first with
          | false, false =>
              let rest ← rest.mapM (reloadValue spilled)
              emitSpill (.op operation (first :: rest) result)
              killValue result
          | true, false =>
              let temporary ← spillTemporary result
              let rest ← rest.mapM (reloadValue spilled)
              emitSpill (.move first temporary)
              emitSpill (.op operation (temporary :: rest) temporary)
              emitSpill (.spill temporary result)
              killValue result
              rememberValue result temporary
          | false, true =>
              killValue result
              rememberValue first result
              emitSpill (.move first result)
              let rest ← rest.mapM (reloadValue spilled)
              emitSpill (.op operation (result :: rest) result)
              killValue result
          | true, true =>
              let temporary ← spillTemporary result
              rememberValue first temporary
              emitSpill (.reload first temporary)
              let rest ← rest.mapM (reloadValue spilled)
              emitSpill (.op operation (temporary :: rest) temporary)
              emitSpill (.spill temporary result)
              killValue result
              killValue temporary
              rememberValue result temporary
      | _, _ =>
          let arguments ← arguments.mapM (reloadValue spilled)
          let (result, after) ← saveValue spilled result
          emitSpill (.op operation arguments result)
          after.forM emitSpill
  | .load chunk address arguments destination =>
      let arguments ← arguments.mapM (reloadValue spilled)
      let (destination, after) ← saveValue spilled destination
      emitSpill (.load chunk address arguments destination)
      after.forM emitSpill
  | .store chunk address arguments source =>
      let arguments ← arguments.mapM (reloadValue spilled)
      let source ← reloadValue spilled source
      emitSpill (.store chunk address arguments source)
  | .call sign target arguments results =>
      let target ← match target with
        | .inl value => Sum.inl <$> reloadValue spilled value
        | .inr symbol => pure (Sum.inr symbol)
      emitSpill (.call sign target arguments results)
      modify fun state => { state with equations := [] }
  | .tailcall sign target arguments =>
      let target ← match target with
        | .inl value => Sum.inl <$> reloadValue spilled value
        | .inr symbol => pure (Sum.inr symbol)
      emitSpill (.tailcall sign target arguments)
      modify fun state => { state with equations := [] }
  | .builtin (.EF_annot ..) _ _ | .builtin (.EF_debug ..) _ _ => emitSpill instruction
  | .builtin external arguments result =>
      let arguments ← arguments.mapM (reloadBuiltin spilled)
      let (result, after) ← saveBuiltin spilled result
      emitSpill (.builtin external arguments result)
      after.forM emitSpill
  | .cond condition arguments ifTrue ifFalse =>
      let arguments ← arguments.mapM (reloadValue spilled)
      emitSpill (.cond condition arguments ifTrue ifFalse)
  | .jumptable argument targets =>
      let argument ← reloadValue spilled argument
      emitSpill (.jumptable argument targets)
  | .ret _ =>
      emitSpill instruction
      modify fun state => { state with equations := [] }
  | .branch _ => emitSpill instruction

def spillTraversal (original : XFunction) (spilled : IndexSet) (maxAge : Nat) :
    Nat → List (Nat × List Equation) → IndexSet → Array XBlock → SpillState →
      Except String (Array XBlock × SpillState × IndexSet)
  | 0, _, _, _, _ => .error "extended-basic-block spill traversal exhausted its bound"
  | _ + 1, [], visited, blocks, state => .ok (blocks, state, visited)
  | fuel + 1, (index, equations) :: pending, visited, blocks, state => do
      if visited.contains index then spillTraversal original spilled maxAge fuel pending visited blocks state
      else
        let some block := original.blocks[index]? | throw "invalid block in spill traversal"
        let state := { state with equations, code := #[] }
        let (_, state) ← (block.instructions.forM (spillInstruction spilled maxAge)).run state
        let blocks := blocks.set! index { block with instructions := state.code.toList }
        let next := block.successors.filterMap fun successor =>
          match original.blocks[successor]? with
          | some next => if next.predecessors.length == 1 then some (successor, state.equations) else none
          | none => none
        spillTraversal original spilled maxAge fuel (next ++ pending) (visited.insert index) blocks state

def insertSpills (original : XFunction) (spilled : IndexSet) (round : Nat)
    : Except String (XFunction × Nat) := do
  let maxAge := if round <= 10 then 3 else if round <= 20 then 1 else 0
  let roots := original.entry :: (List.range original.blocks.size).filter fun index =>
    (original.blocks[index]?.map (fun block => block.predecessors.length != 1)).getD false
  let pending := (roots ++ List.range original.blocks.size).map fun index => (index, [])
  let fuel := pending.length + original.blocks.foldl (fun count block => count + block.successors.length) 0 + 1
  let (blocks, state, _) ← spillTraversal original spilled maxAge fuel pending {} original.blocks
    { variables := original.variables }
  return ({ original with blocks, variables := state.variables }, state.reloadsReused)

end CompCert4Lean.Allocator
