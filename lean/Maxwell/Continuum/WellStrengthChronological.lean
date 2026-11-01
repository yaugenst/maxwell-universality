import Maxwell.Continuum.WellStrengthPhysical
import Maxwell.Continuum.SourceGeometryVertexLookup
import Maxwell.Continuum.ContinuumWellStrengthData
import Maxwell.Continuum.WellMediatorGeometry
import Maxwell.Continuum.WellInternalEntry

/-! The computed strength values at every chronological geometry index are
exactly the numerators consumed by the final well serializer. -/
noncomputable section
namespace Maxwell.Continuum.RealizationParameters.WellStrengthPhysical
open Maxwell.Cost Maxwell.Composition Maxwell.Logical Maxwell.Logical.Routing
open RationalDataflow SourceDecorationEnumeration
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
variable (data : CalibratedParts p S hm)

theorem wellNumerators_at (index : ℕ) (vertex : SourceDecoration.Vertex S (precision p S hm))
    (atVertex : (vertexList S (precision p S hm))[index]?=some vertex) :
    wellNumerators p S hm index=
      (strengthData p S hm (computedEnclosures p S hm).mode (computedEnclosures p S hm).coupling vertex).numerator := by
  obtain ⟨hi,he⟩ := List.getElem?_eq_some_iff.mp atVertex
  rw [wellNumerators_get p S hm index hi,he]

theorem internal_part {saved} (h : Represents S (precision p S hm) saved)
    (i : Fin ((sourceSquareEntries S (precision p S hm)).length+(sourceSquareEntries S (precision p S hm)).length))
    (j : ℕ) (hj : j<(saved.paths.get i).length-2) :
    Parts.literal (wellNumerators p S hm
      ((sourceCircuit S (precision p S hm)).size+(sourceCircuit S (precision p S hm)).size+
        (sourceSquareEntries S (precision p S hm)).length+pathPrefix saved 2 i.val+j):ℚ)=
      WellInternalEntry.part (wellStoredPrecision p S hm) (values p S hm data) := by
  have ht : j<(EdgeWalk.edgeWalk (SourceRouting.data S (precision p S hm))
      ((SourceEnumeration.positiveEdgeEquiv S (precision p S hm)).symm i)).length-1 := by
    rw [h.path_length] at hj
    omega
  let t : Fin _ := ⟨j,ht⟩
  rw [wellNumerators_at p S hm _ _ (Represents.internal_vertex_lookup S (precision p S hm) h i t)]
  unfold WellInternalEntry.part
  rw [internal_target p S hm data _ t]
  rw [show wellStoredPrecision p S hm=FiniteAuxiliary.onsitePrecision (length p S hm)
    (spacing p S hm) (length_pos p S hm) from rfl,numerator_eq]

theorem mediator_array_target {saved} (h : Represents S (precision p S hm) saved)
    (i : Fin ((sourceSquareEntries S (precision p S hm)).length+(sourceSquareEntries S (precision p S hm)).length))
    (t : Fin (EdgeWalk.edgeWalk (SourceRouting.data S (precision p S hm))
      ((SourceEnumeration.positiveEdgeEquiv S (precision p S hm)).symm i)).length) :
    WellMediatorGeometry.target (packedVector saved) (pathOffset saved i.val+1+3*t.val) (values p S hm data)=
      targetDiagonal p S hm (computedEnclosures p S hm).coupling
        (.inr (SourceEdgeEnumeration.toEdge S (precision p S hm)
          ⟨(SourceEnumeration.positiveEdgeEquiv S (precision p S hm)).symm i,t⟩)) := by
  let step : SourceSteps.Step S (precision p S hm) :=
    ⟨(SourceEnumeration.positiveEdgeEquiv S (precision p S hm)).symm i,t⟩
  have hfirst : t.val<(saved.paths.get i).length := by rw [h.path_length];omega
  have hnext : t.val+1<(saved.paths.get i).length := by rw [h.path_length];omega
  have pairEq : SourceSegmentList.pair S (precision p S hm) step=
      ((saved.paths.get i)[t.val],(saved.paths.get i)[t.val+1]) := by
    rw [h.path_point,h.path_point]
    exact SourceSegmentList.pair_apply S (precision p S hm) _ t
  have pointWord (j : ℕ) (hj : j<(saved.paths.get i).length) (k : Fin 3) :
      GeometryOutput.arrayValue (packedVector saved) (pathOffset saved i.val+1+3*j+k.val)=
        (shiftedPoint (saved.paths.get i)[j] k).toNat := by
    rw [path_point_lookup saved i j hj]
    fin_cases k <;> rfl
  let geometry : ℕ→ℕ := fun k=>
    if k=976 then GeometryOutput.arrayValue (packedVector saved) (pathOffset saved i.val+1+3*t.val) else
    if k=979 then GeometryOutput.arrayValue (packedVector saved) (pathOffset saved i.val+1+3*t.val+3) else
    if k=977 then GeometryOutput.arrayValue (packedVector saved) (pathOffset saved i.val+1+3*t.val+1) else
    GeometryOutput.arrayValue (packedVector saved) (pathOffset saved i.val+1+3*t.val+4)
  have hx0 : geometry 976=(shiftedPoint (SourceSegmentList.pair S (precision p S hm) step).1 0).toNat := by
    simpa only [Fin.val_zero,Fin.val_one,geometry,ite_true,pairEq,Nat.add_zero] using pointWord t.val hfirst 0
  have hy0 : geometry 979=(shiftedPoint (SourceSegmentList.pair S (precision p S hm) step).2 0).toNat := by
    simpa only [Fin.val_zero,Fin.val_one,geometry,show (979:ℕ)≠976 by decide,ite_false,ite_true,pairEq,Nat.add_zero,
      Nat.mul_add,Nat.mul_one,Nat.add_assoc] using pointWord (t.val+1) hnext 0
  have hx1 : geometry 977=(shiftedPoint (SourceSegmentList.pair S (precision p S hm) step).1 1).toNat := by
    simpa only [Fin.val_zero,Fin.val_one,geometry,show (977:ℕ)≠976 by decide,show (977:ℕ)≠979 by decide,ite_false,ite_true,pairEq]
      using pointWord t.val hfirst 1
  have hy1 : geometry 980=(shiftedPoint (SourceSegmentList.pair S (precision p S hm) step).2 1).toNat := by
    simpa only [Fin.val_zero,Fin.val_one,geometry,show (980:ℕ)≠976 by decide,show (980:ℕ)≠979 by decide,
      show (980:ℕ)≠977 by decide,ite_false,pairEq,Nat.mul_add,Nat.mul_one,Nat.add_assoc]
      using pointWord (t.val+1) hnext 1
  have result := mediator_target p S hm data step geometry
    (by rw [pairEq];exact Represents.path_nonnegative S (precision p S hm) h i _ (List.getElem_mem hfirst))
    (by rw [pairEq];exact Represents.path_nonnegative S (precision p S hm) h i _ (List.getElem_mem hnext)) hx0 hy0 hx1 hy1
  simpa only [WellMediatorGeometry.target,WellMediatorGeometry.coupling,WellMediatorLoad.coupling,
    geometry,ite_true,show (979:ℕ)≠976 by decide,show (977:ℕ)≠976 by decide,
    show (977:ℕ)≠979 by decide,show (980:ℕ)≠976 by decide,show (980:ℕ)≠979 by decide,
    show (980:ℕ)≠977 by decide,ite_false] using result

theorem mediator_part {saved} (h : Represents S (precision p S hm) saved)
    (i : Fin ((sourceSquareEntries S (precision p S hm)).length+(sourceSquareEntries S (precision p S hm)).length))
    (j : ℕ) (hj : j<(saved.paths.get i).length-1) :
    Parts.literal (wellNumerators p S hm
      ((sourceCircuit S (precision p S hm)).size+(sourceCircuit S (precision p S hm)).size+
        (sourceSquareEntries S (precision p S hm)).length+
        pathPrefix saved 2 ((sourceSquareEntries S (precision p S hm)).length+(sourceSquareEntries S (precision p S hm)).length)+
        pathPrefix saved 1 i.val+j):ℚ)=
      WellMediatorGeometry.part (wellStoredPrecision p S hm) (packedVector saved)
        (pathOffset saved i.val+1+3*j) (values p S hm data) := by
  have ht : j<(EdgeWalk.edgeWalk (SourceRouting.data S (precision p S hm))
      ((SourceEnumeration.positiveEdgeEquiv S (precision p S hm)).symm i)).length := by
    rw [h.path_length] at hj
    omega
  let t : Fin _ := ⟨j,ht⟩
  rw [wellNumerators_at p S hm _ _ (Represents.mediator_vertex_lookup S (precision p S hm) h i t)]
  unfold WellMediatorGeometry.part
  rw [mediator_array_target p S hm data h i t]
  rw [show wellStoredPrecision p S hm=FiniteAuxiliary.onsitePrecision (length p S hm)
    (spacing p S hm) (length_pos p S hm) from rfl,numerator_eq]

theorem mediator_denominator {saved} (h : Represents S (precision p S hm) saved) (hb : S.source≠0)
    (i : Fin ((sourceSquareEntries S (precision p S hm)).length+(sourceSquareEntries S (precision p S hm)).length))
    (j : ℕ) (hj : j<(saved.paths.get i).length-1) :
    (values p S hm data 1).value+
      WellMediatorGeometry.target (packedVector saved) (pathOffset saved i.val+1+3*j) (values p S hm data)≠0 := by
  have ht : j<(EdgeWalk.edgeWalk (SourceRouting.data S (precision p S hm))
      ((SourceEnumeration.positiveEdgeEquiv S (precision p S hm)).symm i)).length := by
    rw [h.path_length] at hj
    omega
  rw [mediator_array_target p S hm data h i ⟨j,ht⟩]
  exact (denominator_pos p S hm data hb _).ne'

#print axioms internal_part
#print axioms mediator_part
#print axioms mediator_denominator
end Maxwell.Continuum.RealizationParameters.WellStrengthPhysical
