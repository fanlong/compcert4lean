import CompCert4Lean.Allocator.Coloring

namespace CompilerOptimization

open CompCert4Lean.Allocator

def countsNeighborOriginal (function : XFunction) (state : ColoringState)
    (classId other : Nat) : Bool :=
  (state.active.contains other || precolored function other) && registerNode function other &&
    nodeClass function state.graph other == classId

@[inline] def countsNeighborFused (function : XFunction) (state : ColoringState)
    (classId other : Nat) : Bool :=
  let info := variableInfo function other
  match info.fixed with
  | some (.R register) => machineClass register == classId
  | some (.S ..) => false
  | none => state.active.contains other &&
      (if (state.graph.costs[other]?.getD {}).stackOnly then 2
       else registerClass info.type) == classId

theorem countsNeighborFused_eq (function : XFunction) (state : ColoringState)
    (classId other : Nat) :
    countsNeighborFused function state classId other =
      countsNeighborOriginal function state classId other := by
  unfold countsNeighborFused countsNeighborOriginal precolored registerNode nodeClass
  cases fixed : (variableInfo function other).fixed with
  | none => simp [fixed]
  | some location => cases location <;> simp [fixed]

def adjacentFused (function : XFunction) (state : ColoringState) (index : Nat) : IndexSet :=
  let classId := nodeClass function state.graph index
  (state.graph.adjacency[index]?.getD {}).foldl (fun result other =>
    if countsNeighborFused function state classId other then result.insert other else result) {}

def adjacentOriginal (function : XFunction) (state : ColoringState) (index : Nat) : IndexSet :=
  let classId := nodeClass function state.graph index
  (state.graph.adjacency[index]?.getD {}).foldl (fun result other =>
    if countsNeighborOriginal function state classId other then result.insert other else result) {}

def degreeFused (function : XFunction) (state : ColoringState) (index : Nat) : Nat :=
  let classId := nodeClass function state.graph index
  (state.graph.adjacency[index]?.getD {}).foldl (fun count other =>
    if countsNeighborFused function state classId other then count + 1 else count) 0

def degreeOriginal (function : XFunction) (state : ColoringState) (index : Nat) : Nat :=
  let classId := nodeClass function state.graph index
  (state.graph.adjacency[index]?.getD {}).foldl (fun count other =>
    if countsNeighborOriginal function state classId other then count + 1 else count) 0

theorem adjacentFused_eq (function : XFunction) (state : ColoringState) (index : Nat) :
    adjacentFused function state index = adjacentOriginal function state index := by
  simp only [adjacentFused, countsNeighborFused_eq, adjacentOriginal]

theorem degreeFused_eq (function : XFunction) (state : ColoringState) (index : Nat) :
    degreeFused function state index = degreeOriginal function state index := by
  simp only [degreeFused, countsNeighborFused_eq, degreeOriginal]

#print axioms countsNeighborFused_eq
#print axioms adjacentFused_eq
#print axioms degreeFused_eq

def capacityCount (context : AllocationContext) (classId : Nat) : Nat :=
  if classId == 2 then 0 else
  if context.reserved.isEmpty then
    if classId == 0 then integerPreferred.length + integerRemaining.length else floatRegisters.length
  else
    let allowed := fun register => !context.reserved.any (regEqual register)
    if classId == 0 then integerPreferred.countP allowed + integerRemaining.countP allowed
    else floatRegisters.countP allowed

theorem capacityCount_eq (context : AllocationContext) (classId : Nat) :
    capacityCount context classId =
      if classId == 2 then 0 else (registerPool context classId).length := by
  have filterTrue (registers : List CompCert4Lean.X86.Machregs.mreg) :
      registers.filter (fun _ => true) = registers :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  by_cases stack : classId = 2
  · simp [capacityCount, stack]
  · by_cases integer : classId = 0 <;>
      cases reserved : context.reserved <;>
      simp [capacityCount, stack, integer, reserved, registerPool, preferredRegisters,
        remainingRegisters, available, List.countP_eq_length_filter, filterTrue]

#print axioms capacityCount_eq

theorem productionNeighbor_eq (function : XFunction) (state : ColoringState)
    (classId other : Nat) :
    countsNeighbor function state classId other =
      countsNeighborOriginal function state classId other := by
  exact countsNeighborFused_eq function state classId other

theorem productionAdjacent_eq (function : XFunction) (state : ColoringState) (index : Nat) :
    adjacent function state index = adjacentOriginal function state index := by
  exact adjacentFused_eq function state index

theorem productionDegree_eq (function : XFunction) (state : ColoringState) (index : Nat) :
    uncachedDegree function state index = degreeOriginal function state index := by
  exact degreeFused_eq function state index

theorem productionCapacity_eq (context : AllocationContext) (function : XFunction)
    (state : ColoringState) (index : Nat) :
    nodeCapacity context function state index =
      if nodeClass function state.graph index == 2 then 0
      else (registerPool context (nodeClass function state.graph index)).length := by
  exact capacityCount_eq context (nodeClass function state.graph index)

#print axioms productionNeighbor_eq
#print axioms productionAdjacent_eq
#print axioms productionDegree_eq
#print axioms productionCapacity_eq

end CompilerOptimization
