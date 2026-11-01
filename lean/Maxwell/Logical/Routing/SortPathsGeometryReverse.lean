import Maxwell.Logical.Routing.SortPathsGeometry

namespace Maxwell.Logical.Routing.SortPaths

def reversePhasePoints {q : ℕ} (initial : SortArrays.Keys q) (start : Port q) (level : ℕ)
    (transpose : Bool) (total processed : ℕ) : List Point :=
  ((List.range total).reverse.take processed).flatMap (fun k =>
    (layerPoints (SortArrays.arraySelection (k+1) (SortArrays.run initial k))
      (port initial start k) (level+k) transpose).reverse)

theorem reversePhasePoints_succ {q : ℕ} (initial : SortArrays.Keys q) (start : Port q) (level : ℕ)
    (transpose : Bool) (total k : ℕ) (bound : k<total) :
    reversePhasePoints initial start level transpose total (k+1)=
      reversePhasePoints initial start level transpose total k++
      (layerPoints (SortArrays.arraySelection (total-(k+1)+1) (SortArrays.run initial (total-(k+1))))
        (port initial start (total-(k+1))) (level+(total-(k+1))) transpose).reverse := by
  have index : (List.range total).reverse[k]'(by simpa using bound)=total-(k+1) := by
    simp only [List.getElem_reverse,List.getElem_range,List.length_range]
    omega
  unfold reversePhasePoints
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_reverse,List.length_range] using bound),
    List.flatMap_append,List.flatMap_singleton,index]

theorem reversePhasePoints_end {q : ℕ} (initial : SortArrays.Keys q) (start : Port q) (level : ℕ)
    (transpose : Bool) (total : ℕ) :
    reversePhasePoints initial start level transpose total total=
      (phasePoints initial start level transpose total).reverse := by
  simp only [reversePhasePoints,List.take_of_length_le (by simp : (List.range total).reverse.length ≤ total),
    phasePoints,List.reverse_flatMap,Function.comp_def]

end Maxwell.Logical.Routing.SortPaths
