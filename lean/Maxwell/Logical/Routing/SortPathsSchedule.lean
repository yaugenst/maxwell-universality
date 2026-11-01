import Maxwell.Logical.Routing.SortPathsGeometry
import Maxwell.Logical.Routing.EdgeEmission

/-! Stored-history path samples agree with the common cubic routing schedule. -/
namespace Maxwell.Logical.Routing.SortPaths
open Schedule SortSchedule

def schedulePoints {q : ℕ} (schedule : ℕ→CubicLayer q) (start : Port q) (level steps : ℕ) : List Point :=
  (List.range steps).flatMap (fun k =>
    (List.range ((schedule k).length (placement schedule k start))).map (fun t =>
      translate (0,0,16*((level+k : ℕ) : ℤ)) ((schedule k).point (placement schedule k start) t)))

theorem layer_movement {q : ℕ} (initial : SortArrays.Keys q) (k : ℕ) (p : Port q) :
    RowLayer.movement (SortArrays.arraySelection (k+1) (SortArrays.run initial k)) p=
      RowLayer.movement (selection q ((k+1)%2) (keyState q (SortArrays.word initial) k)) p := by
  have active : (SortArrays.arraySelection (k+1) (SortArrays.run initial k)).active=
      (selection q ((k+1)%2) (keyState q (SortArrays.word initial) k)).active := by
    funext col row
    simp [SortArrays.arraySelection,selection,BinaryDepth.mem_layerCenters,SortArrays.run_word,and_assoc]
  simp only [RowLayer.movement,active]

theorem layer_length {q : ℕ} (initial : SortArrays.Keys q) (k : ℕ) (p : Port q) :
    RowLayer.pathLength (SortArrays.arraySelection (k+1) (SortArrays.run initial k)) p=
      (rowSchedule q (SortArrays.word initial) k).length p := by
  change RowLayer.pathLength _ _=RowLayer.pathLength _ _
  simp only [RowLayer.pathLength,layer_movement]

theorem layer_point {q : ℕ} (initial : SortArrays.Keys q) (k : ℕ) (p : Port q) (t : ℕ) :
    RowLayer.pathPoint (SortArrays.arraySelection (k+1) (SortArrays.run initial k)) p t=
      (rowSchedule q (SortArrays.word initial) k).point p t := by
  change RowLayer.pathPoint _ _ _=RowLayer.pathPoint _ _ _
  simp only [RowLayer.pathPoint,layer_movement]

theorem phasePoints_row {q : ℕ} (initial : SortArrays.Keys q) (start : Port q) (level steps : ℕ) :
    phasePoints initial start level false steps=
      schedulePoints (rowSchedule q (SortArrays.word initial)) start level steps := by
  simp only [phasePoints,layerPoints,layer_length,layer_point,port_placement,
    Bool.false_eq_true,ite_false,schedulePoints]

theorem phasePoints_column {q : ℕ} (target : Equiv.Perm (Port q)) (start : Port q) (level steps : ℕ) :
    phasePoints (SortArrays.targetArray (transposedTarget target)) (swapPorts q start) level true steps=
      schedulePoints (columnSchedule target) start level steps := by
  simp only [phasePoints,layerPoints,layer_length,layer_point,port_placement,
    SortArrays.targetArray_word,ite_true,schedulePoints,columnSchedule_placement]
  rfl

theorem schedulePoints_congr {q : ℕ} (a b : ℕ→CubicLayer q) (start : Port q) (level steps : ℕ)
    (same : ∀k<steps,a k=b k) : schedulePoints a start level steps=schedulePoints b start level steps := by
  apply List.flatMap_congr
  intro k hk
  have bound := List.mem_range.mp hk
  have positions : placement a k=placement b k := placement_congr a b k (fun j hj => same j (by omega))
  simp only [same k bound,positions]

theorem schedulePoints_append {q : ℕ} (first second : ℕ→CubicLayer q) (start : Port q)
    (level cut steps : ℕ) :
    schedulePoints (appendSchedule first second cut) start level (cut+steps)=
      schedulePoints first start level cut++
        schedulePoints second (placement first cut start) (level+cut) steps := by
  simp only [schedulePoints,List.range_add,List.flatMap_append,List.flatMap_map]
  apply congrArg₂ List.append
  · apply List.flatMap_congr
    intro k hk
    have bound := List.mem_range.mp hk
    have positions : placement (appendSchedule first second cut) k=placement first k :=
      placement_congr _ _ k (fun j hj => by simp only [appendSchedule,show j<cut by omega,ite_true])
    simp only [appendSchedule,bound,ite_true,positions]
  · apply List.flatMap_congr
    intro k _
    simp only [placement_append,Equiv.trans_apply,appendSchedule,show ¬cut+k<cut by omega,
      ite_false,Nat.add_sub_cancel_left,Nat.add_assoc]

theorem schedulePoints_network {q : ℕ} (schedule : ℕ→CubicLayer q) (start : Port q) (steps : ℕ) :
    schedulePoints schedule start 0 steps=EdgeEmission.samplesPrefix (Walk.networkWalk schedule steps start) := by
  apply EdgeEmission.network_prefix
  intro k _
  simp only [Nat.zero_add,EdgeEmission.samplesPrefix,Walk.slabWalk]

#print axioms phasePoints_row
#print axioms phasePoints_column
#print axioms schedulePoints_append
end Maxwell.Logical.Routing.SortPaths
