import Maxwell.Continuum.SourceDecorationCenters
import Maxwell.Continuum.ContinuumRecordEncoding
import Maxwell.Continuum.StoredPlacementEncoding

/-! The description can use the arithmetic routing order. All well records
are preserved, and their existing word bounds require no choice of an
unordered finite-set enumeration. -/
noncomputable section
namespace Maxwell.Continuum.RealizationParameters
open Maxwell.Composition
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

def chronologicalWellStream : List Bool :=
  Maxwell.Codec.list (wellBits p S hm)
    (SourceDecorationEnumeration.vertexList S (precision p S hm))

def chronologicalPlacementStream : List Bool :=
  Maxwell.Codec.list (placementBits p S hm)
    (SourceDecorationEnumeration.vertexList S (precision p S hm))

theorem chronologicalWellStream_length (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S))
    (hb : S.source≠0) :
    (chronologicalWellStream p S hm).length≤
      (sites p S hm+1)*(recordBitCoefficient p+3)*(logSize S)^25 := by
  let xs := SourceDecorationEnumeration.vertexList S (precision p S hm)
  have hx : xs.length=sites p S hm := SourceDecorationEnumeration.vertexList_length _ _
  have h := Maxwell.Codec.list_length_le (wellBits p S hm) xs
    (recordBitCoefficient p*(logSize S)^25) (fun i _ => wellBits_length p S hm hm2 hu hb i)
  have hu' : Maxwell.unsignedBitLength xs.length≤xs.length := by
    rw [Maxwell.Codec.unsignedBitLength_eq_size]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self (n:=xs.length))
  have hℓ := Parameters.inputLog_pos S.nnz
  have hp : 1≤(logSize S)^25 := one_le_pow₀ (by change 0<logSize S at hℓ;omega)
  change (Maxwell.Codec.list (wellBits p S hm) xs).length≤_
  rw [hx] at h hu'
  nlinarith only [h,hu',hp,Nat.zero_le (recordBitCoefficient p*(logSize S)^25)]

theorem chronological_vertices_perm :
    (SourceDecorationEnumeration.vertexList S (precision p S hm)).Perm
      (Finset.univ : Finset (SourceDecoration.Vertex S (precision p S hm))).toList := by
  classical
  apply (List.perm_ext_iff_of_nodup (SourceDecorationEnumeration.vertexList_nodup _ _)
    (Finset.nodup_toList Finset.univ)).mpr
  intro v
  simp only [Finset.mem_toList,Finset.mem_univ,iff_true]
  exact SourceDecorationEnumeration.vertexList_complete _ _ v

/-- Reordering whole records preserves the finite physical well family. -/
theorem chronological_well_records_perm :
    ((SourceDecorationEnumeration.vertexList S (precision p S hm)).map (wellBits p S hm)).Perm
      ((Finset.univ : Finset (SourceDecoration.Vertex S (precision p S hm))).toList.map (wellBits p S hm)) :=
  (chronological_vertices_perm p S hm).map _

theorem chronologicalPlacementStream_eq_centers {saved}
    (h : SourceDecorationEnumeration.Represents S (precision p S hm) saved) :
    chronologicalPlacementStream p S hm=
      Maxwell.Codec.list (fun x : Maxwell.Spectral.Lattice.Site =>
        Maxwell.Codec.int (x 0)++Maxwell.Codec.int (x 1)++Maxwell.Codec.int (x 2)++
          Maxwell.Codec.nat (length p S hm))
        (SourceDecorationEnumeration.centers PeriodicBand.placementDiagonal (length p S hm)
          (spacing p S hm) (bufferSteps p S hm) saved) := by
  rw [h.centers_eq]
  simp only [chronologicalPlacementStream,Maxwell.Codec.list,List.length_map,List.flatMap_map]
  rfl

#print axioms chronologicalWellStream_length
#print axioms chronological_well_records_perm
#print axioms chronologicalPlacementStream_eq_centers
end Maxwell.Continuum.RealizationParameters
