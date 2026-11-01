import Maxwell.Logical.Routing.SortPathsSchedule
import Maxwell.Logical.Routing.SortPathsThreePhase

namespace Maxwell.Logical.Routing.SortPaths
open Schedule SortSchedule

def threePhasePoints {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) (start : Port q) : List Point :=
  phasePoints (PhaseKeys.first colors) start 0 false (2*q)++
    phasePoints (PhaseKeys.middle colors) (nextStart (PhaseKeys.first colors) start) (2*q) true (2*q)++
    phasePoints (PhaseKeys.last colors)
      (nextStart (PhaseKeys.middle colors) (nextStart (PhaseKeys.first colors) start)) (4*q) false (2*q)

theorem nextStart_column {q : ℕ} (target : Equiv.Perm (Port q)) (start : Port q) :
    nextStart (SortArrays.targetArray (transposedTarget target)) (swapPorts q start)=
      placement (columnSchedule target) (2*q) start := by
  rw [nextStart,port_placement,SortArrays.targetArray_word,columnSchedule_placement]
  rfl

theorem threePhasePoints_schedule {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (start : Port q) :
    threePhasePoints colors start=schedulePoints (SortArrays.fullSchedule colors) start 0 (6*q) := by
  let first := rowSchedule q (SortArrays.word (PhaseKeys.first colors))
  let middle := columnSchedule (PhaseArrays.prepare colors).column
  let last := rowSchedule q (SortArrays.word (PhaseKeys.last colors))
  have schedule : schedulePoints (SortArrays.fullSchedule colors) start 0 (6*q)=
      schedulePoints (appendSchedule first (appendSchedule middle last (2*q)) (2*q)) start 0 (6*q) := by
    apply schedulePoints_congr
    intro k hk
    simp only [SortArrays.fullSchedule,appendSchedule]
    by_cases initial : k<2*q
    · simp only [initial,ite_true]
      exact SortArrays.storedSchedule_at _ _ _ initial
    · simp only [initial,ite_false]
      by_cases center : k-2*q<2*q
      · simp only [center,ite_true]
        exact SortArrays.storedColumnSchedule_at _ _ center
      · simp only [center,ite_false]
        exact SortArrays.storedSchedule_at _ _ _ (by omega)
  rw [schedule,show 6*q=2*q+(2*q+2*q) by omega,schedulePoints_append,schedulePoints_append]
  simp only [Nat.zero_add]
  have endFirst : placement first (2*q) start=port (PhaseKeys.first colors) start (2*q) :=
    (port_placement _ _ _).symm
  have endMiddle : placement middle (2*q) (placement first (2*q) start)=
      nextStart (PhaseKeys.middle colors) (nextStart (PhaseKeys.first colors) start) := by
    rw [endFirst]
    exact (nextStart_column (PhaseArrays.prepare colors).column _).symm
  rw [endMiddle,endFirst]
  change _=schedulePoints (rowSchedule q (SortArrays.word (PhaseKeys.first colors))) start 0 (2*q)++
    (schedulePoints (columnSchedule (PhaseArrays.prepare colors).column) (port (PhaseKeys.first colors) start (2*q)) (2*q) (2*q)++
    schedulePoints (rowSchedule q (SortArrays.word (PhaseKeys.last colors)))
      (nextStart (PhaseKeys.middle colors) (nextStart (PhaseKeys.first colors) start)) (2*q+2*q) (2*q))
  rw [←phasePoints_row,←phasePoints_row,←phasePoints_column]
  simp only [threePhasePoints,show 2*q+2*q=4*q by omega,List.append_assoc]
  rfl

theorem threePhasePoints_network {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (incidence : Gluing.Incidence E) :
    threePhasePoints data.colors (Gluing.token data incidence)=
      EdgeEmission.networkPrefix (EdgeEmission.prepare data) (Gluing.token data incidence) := by
  rw [threePhasePoints_schedule]
  apply List.flatMap_congr
  intro k hk
  have bound := List.mem_range.mp hk
  simp only [EdgeEmission.savedSegment,EdgeEmission.prepare,
    bound,↓reduceDIte,PlacementArrays.segment,PlacementArrays.history_at,Fin.val_castSucc,Nat.zero_add]

#print axioms threePhasePoints_schedule
#print axioms threePhasePoints_network
end Maxwell.Logical.Routing.SortPaths
