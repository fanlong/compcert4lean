import CompCert4Lean.Allocator.XTL

namespace CompCert4Lean.Allocator

open Common.AST Backend.Locations X86.Machregs

def fixedStack (function : XFunction) (index : Nat) : Bool :=
  match (variableInfo function index).fixed with
  | some (.S ..) => true
  | _ => false

def addUses (uses : List Nat) (live : IndexSet) : IndexSet :=
  uses.foldl (fun result index => result.insert index) live

def targetUses : Sum Nat ident → List Nat
  | .inl index => [index]
  | .inr _ => []

def liveBefore (function : XFunction) (instruction : XInstruction) (after : IndexSet) : IndexSet :=
  match instruction with
  | .move source destination | .reload source destination | .spill source destination =>
      if after.contains destination || fixedStack function source then
        (after.erase destination).insert source else after
  | .parmove sources destinations _ _ => addUses sources (setRemove destinations after)
  | .op _ arguments destination | .load _ _ arguments destination =>
      if after.contains destination then addUses arguments (after.erase destination) else after
  | .store _ _ arguments source => addUses arguments (after.insert source)
  | .call _ target arguments results => addUses (arguments ++ targetUses target) (setRemove results after)
  | .tailcall _ target arguments => setOfList (arguments ++ targetUses target)
  | .builtin (.EF_debug ..) _ result => setRemove (params_of_builtin_res result) after
  | .builtin _ arguments result =>
      addUses (params_of_builtin_args arguments) (setRemove (params_of_builtin_res result) after)
  | .branch _ => after
  | .cond _ arguments _ _ => addUses arguments after
  | .jumptable argument _ => after.insert argument
  | .ret arguments => setOfList arguments

structure Liveness where
  before : Array IndexSet
  after : Array IndexSet

@[inline] def sameIndexSet (left right : IndexSet) : Bool :=
  withPtrEq left right
    (fun _ => left.size == right.size && left.toList == right.toList)
    (by intro same; subst right; simp)

def livenessWorklist (function : XFunction) : Nat → List Nat → IndexSet → Liveness →
    Except String Liveness
  | 0, _, _, _ => .error "liveness exhausted its worklist bound"
  | _ + 1, [], _, state => .ok state
  | fuel + 1, index :: pending, queued, state => do
      let some block := function.blocks[index]? | throw "invalid liveness block index"
      let after := block.successors.foldl
        (fun result successor => setUnion result (state.before[successor]?.getD {})) {}
      let before := block.instructions.foldr (liveBefore function) after
      let previous := state.before[index]?.getD {}
      let changed := !sameIndexSet before previous
      let state := { before := state.before.set! index before, after := state.after.set! index after }
      let queued := queued.erase index
      let (pending, queued) := if changed then
        block.predecessors.foldl (fun (pending, queued) predecessor =>
          if queued.contains predecessor then (pending, queued)
          else (predecessor :: pending, queued.insert predecessor)) (pending, queued)
        else (pending, queued)
      livenessWorklist function fuel pending queued state

def analyzeLiveness (function : XFunction) : Except String Liveness :=
  let indices := (List.range function.blocks.size).reverse
  livenessWorklist function
    ((function.blocks.size + 1) * (function.blocks.size + 1) * (function.variables.size + 1))
    indices (setOfList indices)
    { before := Array.replicate function.blocks.size {}, after := Array.replicate function.blocks.size {} }

def eliminateInstruction (function : XFunction) (instruction : XInstruction)
    (after : IndexSet) : List XInstruction :=
  match instruction with
  | .move source destination =>
      if after.contains destination || fixedStack function source then [instruction] else []
  | .op _ _ destination | .load _ _ _ destination =>
      if after.contains destination then [instruction] else []
  | .parmove sources destinations integerTemp floatTemp =>
      let pairs := (sources.zip destinations).filter fun (source, destination) =>
        after.contains destination || fixedStack function source
      match pairs with
      | [] => []
      | [(source, destination)] => [.move source destination]
      | _ => [.parmove (pairs.map Prod.fst) (pairs.map Prod.snd) integerTemp floatTemp]
  | .builtin (.EF_debug kind text types) arguments result =>
      let across := setRemove (params_of_builtin_res result) after
      [.builtin (.EF_debug kind text types)
        (arguments.filter fun argument => (params_of_builtin_arg argument).all across.contains) result]
  | _ => [instruction]

def eliminateDeadCode (function : XFunction) (liveness : Liveness) : XFunction × Nat := Id.run do
  let mut blocks := function.blocks
  let mut removed := 0
  for index in [:blocks.size] do
    if let some block := blocks[index]? then
      let (_, code) := block.instructions.foldr (fun instruction (after, code) =>
        (liveBefore function instruction after, eliminateInstruction function instruction after ++ code))
        (liveness.after[index]?.getD {}, [])
      removed := removed + block.instructions.length - code.length
      blocks := blocks.set! index { block with instructions := code }
  return ({ function with blocks }, removed)

structure SpillCost where
  amount : Nat := 0
  accesses : Nat := 0
  unspillable : Bool := false
  stackOnly : Bool := false

structure Interference where
  adjacency : Array IndexSet
  preferences : Array IndexSet
  costs : Array SpillCost
  present : IndexSet := {}

def graphTouch (index : Nat) (graph : Interference) : Interference :=
  { graph with present := graph.present.insert index }

def graphEdge (left right : Nat) (graph : Interference) : Interference :=
  let graph := graphTouch right (graphTouch left graph)
  if left == right then graph else
    let ⟨adjacency, preferences, costs, present⟩ := graph
    let adjacency := if left < adjacency.size && right < adjacency.size then
        (adjacency.modify left (·.insert right)).modify right (·.insert left)
      else
        let leftSet := (adjacency[left]?.getD {}).insert right
        let rightSet := (adjacency[right]?.getD {}).insert left
        (adjacency.set! left leftSet).set! right rightSet
    { adjacency, preferences, costs, present }

def graphPreference (left right : Nat) (graph : Interference) : Interference :=
  let graph := graphTouch right (graphTouch left graph)
  if left == right then graph else
    let ⟨adjacency, preferences, costs, present⟩ := graph
    let preferences := (preferences.modify left (·.insert right)).modify right (·.insert left)
    { adjacency, preferences, costs, present }

def graphEdgeFromTouched (left right : Nat) (graph : Interference) : Interference :=
  let graph := graphTouch right graph
  if left == right then graph else
    let ⟨adjacency, preferences, costs, present⟩ := graph
    let adjacency := if left < adjacency.size && right < adjacency.size then
        (adjacency.modify left (·.insert right)).modify right (·.insert left)
      else
        let leftSet := (adjacency[left]?.getD {}).insert right
        let rightSet := (adjacency[right]?.getD {}).insert left
        (adjacency.set! left leftSet).set! right rightSet
    { adjacency, preferences, costs, present }

def graphLive (index : Nat) (live : IndexSet) (graph : Interference) : Interference :=
  live.foldl (fun graph other => graphEdgeFromTouched index other graph) (graphTouch index graph)

def graphDestroyed (registers : List mreg) (live : IndexSet) (graph : Interference) : Interference :=
  registers.foldl (fun graph register => graphLive (machineIndex register) live graph) graph

def graphPairwise (indices : List Nat) (graph : Interference) : Interference :=
  let live := setOfList indices
  indices.foldl (fun graph index => graphLive index live graph) graph

def charge (indices : List Nat) (amount accesses : Nat) (unspillable stackOnly : Bool)
    (graph : Interference) : Interference :=
  indices.foldl (fun graph index =>
    let cost := graph.costs[index]?.getD {}
    { graph with
      present := graph.present.insert index
      costs := graph.costs.set! index {
        amount := cost.amount + amount
        accesses := cost.accesses + accesses
        unspillable := cost.unspillable || unspillable
        stackOnly := cost.stackOnly || stackOnly } }) graph

def loopPredecessors (function : XFunction) (header : Nat) :
    Nat → List Nat → IndexSet → IndexSet
  | 0, _, visited => visited
  | _ + 1, [], visited => visited
  | fuel + 1, node :: pending, visited =>
      if visited.contains node then loopPredecessors function header fuel pending visited
      else
        let visited := visited.insert node
        let predecessors := if node == header then [] else (function.blocks[node]?.getD {}).predecessors
        loopPredecessors function header fuel (predecessors ++ pending) visited

def loopBlocks (function : XFunction) : IndexSet := Id.run do
  let mut loops : IndexSet := {}
  for index in [:function.blocks.size] do
    if let some block := function.blocks[index]? then
      for target in block.successors do
        if target < index then
          let members := loopPredecessors function target (function.blocks.size + 1) [index] {}
          if members.contains target then loops := setUnion loops members
  return loops

def instructionCosts (weight : Nat) (function : XFunction) (instruction : XInstruction)
    (graph : Interference) : Interference :=
  let chargeW := fun indices amount accesses unspillable stackOnly graph =>
    charge indices (amount * weight) accesses unspillable stackOnly graph
  match instruction with
  | .move source destination =>
      if fixedStack function source then chargeW [destination] 0 0 false true graph
      else if fixedStack function destination then chargeW [source] 0 0 false true graph
      else chargeW [source, destination] 1 1 false false graph
  | .reload source destination => chargeW [destination] 0 1 true false (chargeW [source] 1 1 false false graph)
  | .spill source destination => chargeW [source] 0 1 true false (chargeW [destination] 1 1 false false graph)
  | .parmove sources destinations integerTemp floatTemp =>
      chargeW [integerTemp, floatTemp] 0 0 true false (chargeW (sources ++ destinations) 1 1 false false graph)
  | .op _ arguments result | .load _ _ arguments result | .store _ _ arguments result =>
      chargeW (result :: arguments) 10 1 false false graph
  | .call _ target _ _ | .tailcall _ target _ => chargeW (targetUses target) 10 1 false false graph
  | .builtin (.EF_annot ..) _ _ | .builtin (.EF_debug ..) _ _ => graph
  | .builtin external arguments result =>
      let args := params_of_builtin_args arguments
      let results := params_of_builtin_res result
      match external with
      | .EF_vstore _ | .EF_memcpy .. => chargeW results 0 0 true false (chargeW args 10 1 false false graph)
      | .EF_annot_val .. => chargeW (args ++ results) 1 1 false false graph
      | _ => chargeW (args ++ results) 10 1 false false graph
  | .cond _ arguments _ _ => chargeW arguments 10 1 false false graph
  | .jumptable argument _ => chargeW [argument] 10 1 false false graph
  | _ => graph

def incoming (function : XFunction) (index : Nat) : Bool :=
  match (variableInfo function index).fixed with
  | some (.S .Incoming ..) => true
  | _ => false

def instructionInterference (weight : Nat) (configuration : Config.CompilerConfig)
    (function : XFunction) (instruction : XInstruction) (live : IndexSet)
    (graph : Interference) : Interference := Id.run do
  let mut graph := instructionCosts weight function instruction graph
  match instruction with
  | .move source destination | .reload source destination | .spill source destination =>
      graph := graphLive destination (live.erase source) (graphPreference source destination graph)
      if incoming function source then graph := graphLive (machineIndex temp_for_parent_frame) live graph
  | .parmove sources destinations integerTemp floatTemp =>
      for (source, destination) in sources.zip destinations do graph := graphPreference source destination graph
      let across := setRemove destinations live
      for destination in integerTemp :: floatTemp :: destinations do graph := graphLive destination across graph
      graph := graphPairwise destinations graph
      graph := graphLive integerTemp (setOfList (sources ++ destinations)) graph
      graph := graphLive floatTemp (setOfList (sources ++ destinations)) graph
      if sources.any (incoming function) then
        graph := graphLive (machineIndex temp_for_parent_frame) (addUses destinations across) graph
  | .op operation arguments result =>
      graph := graphLive result live graph
      if twoAddress operation then
        if let source :: rest := arguments then
          graph := graphPreference source result graph
          graph := graphLive result ((addUses rest live).erase source) graph
      graph := graphDestroyed (destroyed_by_op operation) (live.erase result) graph
  | .load chunk address _ result =>
      graph := graphDestroyed (destroyed_by_load chunk address) (live.erase result) (graphLive result live graph)
  | .store chunk address _ _ => graph := graphDestroyed (destroyed_by_store chunk address) live graph
  | .call _ target _ results =>
      graph := graphDestroyed (X86.Conventions1.destroyed_at_call configuration) (setRemove results live) graph
      graph := graphDestroyed [.AX] (setOfList (targetUses target)) graph
  | .tailcall _ target _ =>
      graph := graphDestroyed (.AX :: integerRemaining) (setOfList (targetUses target)) graph
  | .builtin external arguments result =>
      let results := params_of_builtin_res result
      let across := setRemove results live
      for result in results do graph := graphLive result across graph
      graph := graphPairwise results graph
      graph := graphDestroyed (destroyed_by_builtin external) across graph
      match external, arguments, result with
      | .EF_annot_val .., [.BA source], .BR destination => graph := graphPreference source destination graph
      | .EF_inline_asm _ _ clobbers, _, _ =>
          graph := graphDestroyed (destroyed_by_clobber clobbers)
            (setOfList (params_of_builtin_args arguments ++ results)) graph
      | _, _, _ => pure ()
  | .cond condition _ _ _ => graph := graphDestroyed (destroyed_by_cond condition) live graph
  | .jumptable _ _ => graph := graphDestroyed destroyed_by_jumptable live graph
  | _ => pure ()
  return graph

def buildInterference (configuration : Config.CompilerConfig) (function : XFunction)
    (liveness : Liveness) : Interference := Id.run do
  let loops := loopBlocks function
  let mut graph : Interference := {
    adjacency := Array.replicate function.variables.size {}
    preferences := Array.replicate function.variables.size {}
    costs := Array.replicate function.variables.size {} }
  for index in [:function.blocks.size] do
    if let some block := function.blocks[index]? then
      let weight := if loops.contains index then 2 else 1
      let (_, next) := block.instructions.foldr (fun instruction (live, graph) =>
        (liveBefore function instruction live, instructionInterference weight configuration function instruction live graph))
        (liveness.after[index]?.getD {}, graph)
      graph := next
  return graphDestroyed destroyed_at_function_entry (liveness.before[function.entry]?.getD {}) graph

end CompCert4Lean.Allocator
