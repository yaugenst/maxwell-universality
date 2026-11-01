import Maxwell.Continuum.SourceRoutingPathStep
import Maxwell.Logical.Routing.SortPathsGeometry

/-! Literal geometry words emitted by the machine are the selected logical
slab samples, with the same orientation and chronological order. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Maxwell.Logical.Routing
open Maxwell.Composition.SourceDecorationEnumeration (pointWords)
set_option maxRecDepth 16384
set_option maxHeartbeats 2600000

theorem emission_point {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ)
    (saved : SortArrays.Keys q) (i : Fin (q*q)) (level cursor : ℕ) (transpose : Bool)
    (t : Fin (moveShape (RowLayer.movement (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i))).length) :
    translate (bankOrigin (emissionValues p round saved i level cursor transpose))
      (orient transpose ((moveShape (RowLayer.movement (SortArrays.arraySelection round saved)
        (finProdFinEquiv.symm i))).point t))=
    translate (0,0,16*(level : ℤ)) (if transpose then
      transposeXY (RowLayer.pathPoint (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i) t.val)
      else RowLayer.pathPoint (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i) t.val) := by
  have sample := moveShape_point (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i) level t
  have origins := emission_origins p round saved i level cursor transpose
  cases transpose
  · simpa only [bankOrigin,origins.1,origins.2.1,origins.2.2,orient,Bool.false_eq_true,ite_false,
      Nat.cast_mul,Nat.cast_ofNat] using sample
  · have flipped := congrArg transposeXY sample
    simpa only [bankOrigin,origins.1,origins.2.1,origins.2.2,orient,ite_true,
      Nat.cast_mul,Nat.cast_ofNat,transposeXY,translate] using flipped

private theorem finRange_map_values (n : ℕ) (f : ℕ→Point) :
    (List.finRange n).map (fun i => f i.val)=(List.range n).map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_finRange,List.getElem_range,Fin.val_cast]

theorem emittedBits_meaning {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ)
    (saved : SortArrays.Keys q) (i : Fin (q*q)) (level cursor width : ℕ) (transpose backwards : Bool) :
    emittedBits p round saved i level cursor width transpose backwards=
      ((if backwards then
          (SortPaths.layerPoints (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i) level transpose).reverse
        else SortPaths.layerPoints (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i) level transpose).flatMap pointWords).flatMap
      (IncidenceEncoding.word width) := by
  let shape := moveShape (RowLayer.movement (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i))
  let origin := bankOrigin (emissionValues p round saved i level cursor transpose)
  have points : (shape.points transpose false).map (translate origin)=
      SortPaths.layerPoints (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i) level transpose := by
    simp only [Shape.points,Shape.indices,Bool.false_eq_true,ite_false,List.map_map,Function.comp_def]
    calc
      _ = (List.finRange shape.length).map (fun t => translate (0,0,16*(level : ℤ))
          (if transpose then transposeXY (RowLayer.pathPoint (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i) t.val)
            else RowLayer.pathPoint (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i) t.val)) := by
        apply List.map_congr_left
        intro t _
        exact emission_point p round saved i level cursor transpose t
      _ = _ := by
        simpa only [shape,moveShape_length,SortPaths.layerPoints] using
          finRange_map_values shape.length (fun t => translate (0,0,16*(level : ℤ))
            (if transpose then transposeXY (RowLayer.pathPoint (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i) t)
              else RowLayer.pathPoint (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i) t))
  have directed : (shape.points transpose backwards).map (translate origin)=
      if backwards then
        (SortPaths.layerPoints (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i) level transpose).reverse
      else SortPaths.layerPoints (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i) level transpose := by
    cases backwards
    · exact points
    · simpa only [Shape.points,Shape.indices,ite_true,Bool.false_eq_true,ite_false,List.map_reverse]
        using congrArg List.reverse points
  rw [emittedBits,Shape.entryBits_eq]
  simpa only [List.flatMap_map] using congrArg
    (fun xs : List Point => (xs.flatMap pointWords).flatMap (IncidenceEncoding.word width)) directed

#print axioms emittedBits_meaning
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
