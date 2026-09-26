import CompCert4Lean.Allocator.Coloring

namespace CompilerOptimization

open CompCert4Lean.Allocator

theorem arrayModifyAsSet (values : Array IndexSet) (index : Nat)
    (update : IndexSet → IndexSet) :
    values.modify index update =
      values.set! index (update (values[index]?.getD {})) := by
  by_cases bound : index < values.size <;>
    simp [Array.modify, Array.modifyM, Array.set!, Array.setIfInBounds, bound]

def graphPreferenceOriginal (left right : Nat) (graph : Interference) : Interference :=
  let graph := graphTouch right (graphTouch left graph)
  if left == right then graph else
    let leftSet := (graph.preferences[left]?.getD {}).insert right
    let rightSet := (graph.preferences[right]?.getD {}).insert left
    let preferences := graph.preferences.set! left leftSet
    { graph with preferences := preferences.set! right rightSet }


def graphPreferenceDirect (left right : Nat) (graph : Interference) : Interference :=
  let graph := graphTouch right (graphTouch left graph)
  if left == right then graph else
    let ⟨adjacency, preferences, costs, present⟩ := graph
    let preferences := (preferences.modify left (·.insert right)).modify right (·.insert left)
    { adjacency, preferences, costs, present }

theorem graphPreferenceDirect_eq (left right : Nat) (graph : Interference) :
    graphPreferenceDirect left right graph = graphPreferenceOriginal left right graph := by
  unfold graphPreferenceDirect graphPreferenceOriginal
  split
  · rfl
  · rename_i different
    have unequal : left ≠ right := by simpa using different
    cases touched : graphTouch right (graphTouch left graph)
    simp only [arrayModifyAsSet, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne unequal]

#print axioms arrayModifyAsSet
#print axioms graphPreferenceDirect_eq

def combineNodesOriginal (context : AllocationContext) (function : XFunction)
    (left right : Nat) (state : ColoringState) : ColoringState := Id.run do
  let neighbors := state.graph.adjacency[right]?.getD {}
  let previousCounts := neighbors.foldl (fun counts neighbor =>
    if neighbor == left || neighbor == right then counts else
      let oldClass := nodeClass function state.graph neighbor
      let removedRight := if countsNeighbor function state oldClass right then 1 else 0
      let removedLeft := if (state.graph.adjacency[neighbor]?.getD {}).contains left &&
          countsNeighbor function state oldClass left then 1 else 0
      counts.push (neighbor, degree function state neighbor - removedRight - removedLeft)) #[]
  let mut graph := state.graph
  let mut state := { state with graph := { adjacency := #[], preferences := #[], costs := #[] } }
  for neighbor in neighbors.toList do
    graph := { graph with adjacency := graph.adjacency.set! neighbor ((graph.adjacency[neighbor]?.getD {}).erase right) }
    if neighbor != left then graph := graphEdge left neighbor graph
  for neighbor in (graph.preferences[right]?.getD {}).toList do
    graph := { graph with preferences := graph.preferences.set! neighbor ((graph.preferences[neighbor]?.getD {}).erase right) }
    if neighbor != left then graph := graphPreferenceOriginal left neighbor graph
  let leftCost := graph.costs[left]?.getD {}
  let rightCost := graph.costs[right]?.getD {}
  graph := { graph with costs := graph.costs.set! left {
    amount := leftCost.amount + rightCost.amount
    accesses := leftCost.accesses + rightCost.accesses
    unspillable := leftCost.unspillable || rightCost.unspillable
    stackOnly := leftCost.stackOnly || rightCost.stackOnly } }
  let combinedMoves := setUnion (state.nodeMoves[left]?.getD {}) (state.nodeMoves[right]?.getD {})
  state := { state with
    graph
    parents := state.parents.set! right left
    active := state.active.erase right
    activeCache := IndexSetCache.erase state.active state.activeCache right
    nodeMoves := state.nodeMoves.set! left combinedMoves
    coalesced := state.coalesced + 1 }
  state := enableMoves (neighbors.insert left) state
  let affected := (neighbors.insert left).insert right
  let updates := previousCounts.map fun (neighbor, count) =>
    let newClass := nodeClass function state.graph neighbor
    let addedLeft := if countsNeighbor function state newClass left then 1 else 0
    (neighbor, count + addedLeft)
  let degrees := updates.foldl (fun degrees (neighbor, value) => degrees.set! neighbor value) state.degrees
  state := { state with degrees }
  state := refreshDegrees function (setOfList [left, right]) state
  return refreshNodes context function affected state

def combineNodesDirect (context : AllocationContext) (function : XFunction)
    (left right : Nat) (state : ColoringState) : ColoringState := Id.run do
  let neighbors := state.graph.adjacency[right]?.getD {}
  let previousCounts := neighbors.foldl (fun counts neighbor =>
    if neighbor == left || neighbor == right then counts else
      let oldClass := nodeClass function state.graph neighbor
      let removedRight := if countsNeighbor function state oldClass right then 1 else 0
      let removedLeft := if (state.graph.adjacency[neighbor]?.getD {}).contains left &&
          countsNeighbor function state oldClass left then 1 else 0
      counts.push (neighbor, degree function state neighbor - removedRight - removedLeft)) #[]
  let mut graph := state.graph
  let mut state := { state with graph := { adjacency := #[], preferences := #[], costs := #[] } }
  for neighbor in neighbors.toList do
    graph := { graph with adjacency := graph.adjacency.modify neighbor (·.erase right) }
    if neighbor != left then graph := graphEdge left neighbor graph
  for neighbor in (graph.preferences[right]?.getD {}).toList do
    graph := { graph with preferences := graph.preferences.modify neighbor (·.erase right) }
    if neighbor != left then graph := graphPreference left neighbor graph
  let leftCost := graph.costs[left]?.getD {}
  let rightCost := graph.costs[right]?.getD {}
  graph := { graph with costs := graph.costs.set! left {
    amount := leftCost.amount + rightCost.amount
    accesses := leftCost.accesses + rightCost.accesses
    unspillable := leftCost.unspillable || rightCost.unspillable
    stackOnly := leftCost.stackOnly || rightCost.stackOnly } }
  let combinedMoves := setUnion (state.nodeMoves[left]?.getD {}) (state.nodeMoves[right]?.getD {})
  state := { state with
    graph
    parents := state.parents.set! right left
    active := state.active.erase right
    activeCache := IndexSetCache.erase state.active state.activeCache right
    nodeMoves := state.nodeMoves.set! left combinedMoves
    coalesced := state.coalesced + 1 }
  state := enableMoves (neighbors.insert left) state
  let affected := (neighbors.insert left).insert right
  let updates := previousCounts.map fun (neighbor, count) =>
    let newClass := nodeClass function state.graph neighbor
    let addedLeft := if countsNeighbor function state newClass left then 1 else 0
    (neighbor, count + addedLeft)
  let degrees := updates.foldl (fun degrees (neighbor, value) => degrees.set! neighbor value) state.degrees
  state := { state with degrees }
  state := refreshDegrees function (setOfList [left, right]) state
  return refreshNodes context function affected state

theorem combineNodesDirect_eq (context : AllocationContext) (function : XFunction)
    (left right : Nat) (state : ColoringState) :
    combineNodesDirect context function left right state =
      combineNodesOriginal context function left right state := by
  unfold combineNodesDirect combineNodesOriginal
  simp only [arrayModifyAsSet, show graphPreference = graphPreferenceOriginal from funext fun a => funext fun b => funext fun g => graphPreferenceDirect_eq a b g]

#print axioms combineNodesDirect_eq


theorem productionPreference_eq (left right : Nat) (graph : Interference) :
    graphPreference left right graph = graphPreferenceOriginal left right graph :=
  graphPreferenceDirect_eq left right graph

theorem productionCombine_eq (context : AllocationContext) (function : XFunction)
    (left right : Nat) (state : ColoringState) :
    combineNodes context function left right state =
      combineNodesOriginal context function left right state :=
  combineNodesDirect_eq context function left right state

#print axioms productionPreference_eq
#print axioms productionCombine_eq

end CompilerOptimization
