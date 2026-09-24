import CompCert4Lean.Allocator.Coloring

namespace CompilerOptimization

open CompCert4Lean.Allocator

def adjacentOriginal (function : XFunction) (state : ColoringState) (index : Nat) : IndexSet :=
  (state.graph.adjacency[index]?.getD {}).foldl (fun result other =>
    if (state.active.contains other || precolored function other) && registerNode function other &&
        nodeClass function state.graph other == nodeClass function state.graph index
    then result.insert other else result) {}

def adjacentHoisted (function : XFunction) (state : ColoringState) (index : Nat) : IndexSet :=
  let classId := nodeClass function state.graph index
  (state.graph.adjacency[index]?.getD {}).foldl (fun result other =>
    if (state.active.contains other || precolored function other) && registerNode function other &&
        nodeClass function state.graph other == classId
    then result.insert other else result) {}

def degreeOriginal (function : XFunction) (state : ColoringState) (index : Nat) : Nat :=
  (state.graph.adjacency[index]?.getD {}).foldl (fun count other =>
    if (state.active.contains other || precolored function other) && registerNode function other &&
        nodeClass function state.graph other == nodeClass function state.graph index
    then count + 1 else count) 0

def degreeHoisted (function : XFunction) (state : ColoringState) (index : Nat) : Nat :=
  let classId := nodeClass function state.graph index
  (state.graph.adjacency[index]?.getD {}).foldl (fun count other =>
    if (state.active.contains other || precolored function other) && registerNode function other &&
        nodeClass function state.graph other == classId
    then count + 1 else count) 0

theorem adjacentHoisted_eq : adjacentHoisted = adjacentOriginal := rfl
theorem degreeHoisted_eq : degreeHoisted = degreeOriginal := rfl

#print axioms adjacentHoisted_eq
#print axioms degreeHoisted_eq

end CompilerOptimization
