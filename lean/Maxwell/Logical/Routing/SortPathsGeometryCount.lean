import Maxwell.Logical.Routing.SortPathsGeometryReverse
import Maxwell.Logical.Routing.SortPathsReverse
import Maxwell.Logical.Routing.SortPathsNetwork

/-! Coordinate-word counts of the canonical routing samples. -/
namespace Maxwell.Logical.Routing.SortPaths

theorem count_phasePoints {q : ℕ} (initial : SortArrays.Keys q) (start : Port q)
    (level : ℕ) (transpose : Bool) (steps : ℕ) :
    count initial start steps=3*(phasePoints initial start level transpose steps).length := by
  induction steps with
  | zero => simp [count,phasePoints]
  | succ steps ih =>
    rw [count,phasePoints_succ,List.length_append,layerPoints_length,ih]
    simp only [length,Nat.mul_add]

theorem reverseCount_reversePhasePoints {q : ℕ} (initial : SortArrays.Keys q) (start : Port q)
    (level : ℕ) (transpose : Bool) (total processed : ℕ) (bound : processed ≤ total) :
    reverseCount initial start total processed=
      3*(reversePhasePoints initial start level transpose total processed).length := by
  induction processed with
  | zero => simp [reverseCount,reversePhasePoints]
  | succ processed ih =>
    rw [reverseCount,reversePhasePoints_succ _ _ _ _ _ _ (by omega),List.length_append,
      List.length_reverse,layerPoints_length,ih (by omega)]
    simp only [length,Nat.mul_add]

theorem reverseCount_end {q : ℕ} (initial : SortArrays.Keys q) (start : Port q) (total : ℕ) :
    reverseCount initial start total total=count initial start total := by
  rw [reverseCount_reversePhasePoints initial start 0 false total total le_rfl,
    reversePhasePoints_end,List.length_reverse,count_phasePoints initial start 0 false]

theorem threePhase_count {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (start : Port q) :
    count (PhaseKeys.first colors) start (2*q)+
      count (PhaseKeys.middle colors) (nextStart (PhaseKeys.first colors) start) (2*q)+
      count (PhaseKeys.last colors) (nextStart (PhaseKeys.middle colors) (nextStart (PhaseKeys.first colors) start)) (2*q)=
      3*(threePhasePoints colors start).length := by
  rw [count_phasePoints _ _ 0 false,count_phasePoints _ _ (2*q) true,count_phasePoints _ _ (4*q) false]
  simp only [threePhasePoints,List.length_append]
  omega

#print axioms threePhase_count
end Maxwell.Logical.Routing.SortPaths
