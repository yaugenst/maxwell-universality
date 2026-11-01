import Maxwell.Logical.Routing.SortPaths

/-! Chronological lattice samples of one stored row/column sorting phase. -/
namespace Maxwell.Logical.Routing.SortPaths

def layerPoints {q parity : ℕ} (selected : RowLayer.Selection q parity) (port : Port q)
    (level : ℕ) (transpose : Bool) : List Point :=
  (List.range (RowLayer.pathLength selected port)).map (fun t =>
    translate (0,0,16*(level : ℤ))
      (if transpose then transposeXY (RowLayer.pathPoint selected port t) else RowLayer.pathPoint selected port t))

theorem layerPoints_length {q parity : ℕ} (selected : RowLayer.Selection q parity) (port : Port q)
    (level : ℕ) (transpose : Bool) :
    (layerPoints selected port level transpose).length=RowLayer.pathLength selected port := by
  simp only [layerPoints,List.length_map,List.length_range]

def phasePoints {q : ℕ} (initial : SortArrays.Keys q) (start : Port q) (level : ℕ)
    (transpose : Bool) (steps : ℕ) : List Point :=
  (List.range steps).flatMap (fun k => layerPoints (SortArrays.arraySelection (k+1) (SortArrays.run initial k))
    (port initial start k) (level+k) transpose)

theorem phasePoints_succ {q : ℕ} (initial : SortArrays.Keys q) (start : Port q) (level : ℕ)
    (transpose : Bool) (k : ℕ) :
    phasePoints initial start level transpose (k+1)=phasePoints initial start level transpose k++
      layerPoints (SortArrays.arraySelection (k+1) (SortArrays.run initial k)) (port initial start k) (level+k) transpose := by
  simp only [phasePoints,List.range_succ,List.flatMap_append,List.flatMap_singleton]

end Maxwell.Logical.Routing.SortPaths
