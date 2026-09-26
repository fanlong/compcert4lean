import CompCert4Lean.Allocator.Analyses

open CompCert4Lean CompCert4Lean.Allocator

namespace GraphIntegration

def graphEdgeOriginal (left right : Nat) (graph : Interference) : Interference :=
  let graph := graphTouch right (graphTouch left graph)
  if left == right then graph else
    let leftSet := (graph.adjacency[left]?.getD {}).insert right
    let rightSet := (graph.adjacency[right]?.getD {}).insert left
    let adjacency := graph.adjacency.set! left leftSet
    { graph with adjacency := adjacency.set! right rightSet }

def graphLiveOriginal (index : Nat) (live : IndexSet) (graph : Interference) : Interference :=
  live.foldl (fun graph other => graphEdgeOriginal index other graph) (graphTouch index graph)

theorem arrayModifyAsSet (values : Array IndexSet) (index : Nat) (element : Nat) :
    values.modify index (·.insert element) =
      values.set! index ((values[index]?.getD {}).insert element) := by
  by_cases bound : index < values.size
  · simp [Array.modify, Array.modifyM, Array.set!, Array.setIfInBounds, bound]
  · simp [Array.modify, Array.modifyM, Array.set!, Array.setIfInBounds, bound]

theorem graphEdge_eq_original (left right : Nat) (graph : Interference) :
    graphEdge left right graph = graphEdgeOriginal left right graph := by
  unfold graphEdge graphEdgeOriginal
  split
  · rfl
  · rename_i different
    have unequal : left ≠ right := by simpa using different
    cases touched : graphTouch right (graphTouch left graph)
    dsimp only
    split
    · simp only [arrayModifyAsSet, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_ne unequal]
    · rfl

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl

theorem insertPresent_eq (indices : IndexSet) (index : Nat)
    (present : indices.contains index = true) : indices.insert index = indices := by
  cases indices with
  | mk map =>
    cases map with
    | mk tree =>
      cases tree with
      | mk raw wellFormed =>
        change raw.contains index = true at present
        simp only [Std.TreeSet.insert, Std.TreeMap.insertIfNew,
          Std.DTreeMap.insertIfNew, insertIfNew, present, if_true]

theorem graphEdgeFromTouched_eq (left right : Nat) (graph : Interference)
    (present : graph.present.contains left = true) :
    graphEdgeFromTouched left right graph = graphEdge left right graph := by
  have touched : graphTouch left graph = graph := by
    simp only [graphTouch, insertPresent_eq _ _ present]
  simp only [graphEdgeFromTouched, graphEdge, touched]

theorem graphEdge_present (left right : Nat) (graph : Interference) :
    (graphEdge left right graph).present.contains left = true := by
  unfold graphEdge graphTouch
  split
  · simp
  · cases graph
    dsimp only
    simp

def graphLivePrior (index : Nat) (live : IndexSet) (graph : Interference) : Interference :=
  live.foldl (fun graph other => graphEdge index other graph) (graphTouch index graph)

theorem graphLive_eq_prior (index : Nat) (live : IndexSet) (graph : Interference) :
    graphLive index live graph = graphLivePrior index live graph := by
  unfold graphLive graphLivePrior
  simp only [Std.TreeSet.foldl_eq_foldl_toList]
  have loop (indices : List Nat) (initial : Interference)
      (present : initial.present.contains index = true) :
      indices.foldl (fun currentGraph other => graphEdgeFromTouched index other currentGraph) initial =
        indices.foldl (fun currentGraph other => graphEdge index other currentGraph) initial := by
    induction indices generalizing initial with
    | nil => rfl
    | cons other rest ih =>
      simp only [List.foldl_cons, graphEdgeFromTouched_eq index other initial present]
      exact ih _ (graphEdge_present index other initial)
  apply loop
  simp [graphTouch]

theorem graphLive_eq_original (index : Nat) (live : IndexSet) (graph : Interference) :
    graphLive index live graph = graphLiveOriginal index live graph := by
  rw [graphLive_eq_prior]
  simp [graphLivePrior, graphLiveOriginal, graphEdge_eq_original]

def graphKey (graph : Interference) :=
  (graph.present.toList,
   graph.adjacency.map Std.TreeSet.toList,
   graph.preferences.map Std.TreeSet.toList,
   graph.costs.map (fun cost => (cost.amount, cost.accesses, cost.unspillable, cost.stackOnly)))

def initialGraph (count seed : Nat) : Interference :=
  { adjacency := (List.range count).toArray.map fun index =>
      setOfList ((List.range count).filter fun other => (index * 7 + other * 11 + seed) % 13 < 3)
    preferences := (List.range count).toArray.map fun index => setOfList [index]
    present := setOfList ((List.range count).filter fun index => (index + seed) % 5 == 0)
    costs := (List.range count).toArray.map fun index =>
      { amount := index, accesses := seed, stackOnly := index % 3 == 0 } }

def checkGraphs : Except String Unit := do
  for count in [0, 1, 2, 7, 32, 129] do
    for seed in [:8] do
      let graph := initialGraph count seed
      for index in [:count] do
        let live := setOfList ((List.range count).filter fun other => (other * 17 + seed) % 7 < seed)
        unless graphKey (graphLive index live graph) == graphKey (graphLiveOriginal index live graph) do
          throw "graph update changed graph contents"
        unless graphKey (graphLive index {} graph) == graphKey (graphLiveOriginal index {} graph) do
          throw "empty graph update changed graph contents"
        unless graphKey (graphEdge index index graph) == graphKey (graphEdgeOriginal index index graph) do
          throw "self graph edge changed graph contents"
  return ()

end GraphIntegration

def main : IO UInt32 := do
  match GraphIntegration.checkGraphs with
  | .error message => IO.eprintln message; return 1
  | .ok () => IO.println "integrated graph equivalence: PASS"; return 0

#print axioms GraphIntegration.arrayModifyAsSet
#print axioms GraphIntegration.graphEdge_eq_original
#print axioms GraphIntegration.graphLive_eq_original

#print axioms GraphIntegration.graphEdgeFromTouched_eq
#print axioms GraphIntegration.graphLive_eq_prior
