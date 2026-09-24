import CompCert4Lean.Allocator.Coloring

namespace CompilerOptimization

open CompCert4Lean.Allocator

def refreshDegreesOriginal (function : XFunction) (indices : IndexSet)
    (state : ColoringState) : ColoringState :=
  let degrees := indices.foldl (fun degrees index =>
    degrees.set! index (uncachedDegree function state index)) state.degrees
  { state with degrees }

def refreshDegreesStaged (function : XFunction) (indices : IndexSet)
    (state : ColoringState) : ColoringState :=
  let updates := indices.toList.map (fun index => (index, uncachedDegree function state index))
  let degrees := updates.foldl (fun degrees (index, value) => degrees.set! index value) state.degrees
  { state with degrees }

theorem refreshDegreesStaged_eq (function : XFunction) (indices : IndexSet)
    (state : ColoringState) : refreshDegreesStaged function indices state =
      refreshDegreesOriginal function indices state := by
  simp only [refreshDegreesStaged, refreshDegreesOriginal, Std.TreeSet.foldl_eq_foldl_toList, List.foldl_map]

#print axioms refreshDegreesStaged_eq

end CompilerOptimization
