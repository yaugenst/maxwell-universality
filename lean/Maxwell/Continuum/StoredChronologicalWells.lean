import Maxwell.Continuum.StoredWellStreamIdentity
import Maxwell.Continuum.ChronologicalWellEncoding

/-! The runtime well stream is the literal continuum well-record format
in the explicit chronological routing order, not an arbitrary Finset order. -/
noncomputable section
namespace Maxwell.Continuum.RealizationParameters
open Maxwell.Cost Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration
set_option maxHeartbeats 7000000
set_option maxRecDepth 16384

def placementNatural (j : Fin 3) : ℕ := (PeriodicBand.placementDiagonal j).toNat

theorem placementNatural_cast (j : Fin 3) : (placementNatural j:ℤ)=PeriodicBand.placementDiagonal j := by
  fin_cases j <;> norm_num [placementNatural,PeriodicBand.placementDiagonal]

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

def wellStoredPrecision : ℕ :=
  FiniteAuxiliary.onsitePrecision (length p S hm) (spacing p S hm) (length_pos p S hm)

def wellNumerators (i : ℕ) : ℤ :=
  if hi:i<(vertexList S (precision p S hm)).length then
    (strengthData p S hm (computedEnclosures p S hm).mode (computedEnclosures p S hm).coupling
      (vertexList S (precision p S hm))[i]).numerator
  else 0

theorem wellNumerators_get (i : ℕ) (hi : i<(vertexList S (precision p S hm)).length) :
    wellNumerators p S hm i=
      (strengthData p S hm (computedEnclosures p S hm).mode (computedEnclosures p S hm).coupling
        (vertexList S (precision p S hm))[i]).numerator := by
  simp only [wellNumerators,dite_eq_left hi]

theorem centerBits_source (i : SourceDecoration.Vertex S (precision p S hm)) :
    WellOutput.centerBits placementNatural (length p S hm) (spacing p S hm) (bufferSteps p S hm)
      (SourceDecoration.site S (precision p S hm) i)=placementBits p S hm i := by
  unfold WellOutput.centerBits
  have he : (fun j=>(placementNatural j:ℤ))=PeriodicBand.placementDiagonal := funext placementNatural_cast
  rw [he,centerPoint_site]
  rfl

theorem indexed_wellRecords :
    IndexedRecordStream.bits
      (WellOutput.recordBits placementNatural (length p S hm) (spacing p S hm) (bufferSteps p S hm)
        (wellStoredPrecision p S hm) (wellNumerators p S hm)
        (Profile.profileBits (materialPrecision p S)) (selectedTemplateBits p S hm))
      ((vertexList S (precision p S hm)).map (SourceDecoration.site S (precision p S hm))) 0=
    (vertexList S (precision p S hm)).flatMap (wellBits p S hm) := by
  rw [IndexedRecordStream.map]
  have he : IndexedRecordStream.bits
      (fun n i=>WellOutput.recordBits placementNatural (length p S hm) (spacing p S hm) (bufferSteps p S hm)
        (wellStoredPrecision p S hm) (wellNumerators p S hm)
        (Profile.profileBits (materialPrecision p S)) (selectedTemplateBits p S hm) n
        (SourceDecoration.site S (precision p S hm) i))
      (vertexList S (precision p S hm)) 0=
      IndexedRecordStream.bits (fun _ i=>wellBits p S hm i) (vertexList S (precision p S hm)) 0 := by
    apply IndexedRecordStream.congr
    intro z hz
    obtain ⟨hi,he⟩ := List.mem_zipIdx' hz
    rcases z with ⟨i,n⟩
    dsimp only at hi he ⊢
    rw [he]
    rw [WellOutput.recordBits,centerBits_source,WellPayload.bits,wellNumerators_get p S hm n hi]
    change _=placementBits p S hm _++
      (Codec.nat (wellStoredPrecision p S hm)++Codec.int
        (strengthData p S hm (computedEnclosures p S hm).mode (computedEnclosures p S hm).coupling
          (vertexList S (precision p S hm))[n]).numerator)++
      Profile.profileBits (materialPrecision p S)++selectedTemplateBits p S hm
    simp only [List.append_assoc]
  rw [he,IndexedRecordStream.bits]
  rw [←List.flatMap_map (f:=Prod.fst),List.zipIdx_map_fst]

theorem storedBits_eq_chronological {saved}
    (h : Represents S (precision p S hm) saved) (constants : ℕ→ℕ)
    (hshift : constants 982=length p S hm+length p S hm*bufferSteps p S hm+8)
    (hscale : ∀j:Fin 3,constants (983+j.val)=2*length p S hm*spacing p S hm*placementNatural j)
    (hword : constants 966=length p S hm) :
    WellOutput.bits saved constants (wellStoredPrecision p S hm) (wellNumerators p S hm)
      (Profile.profileBits (materialPrecision p S)) (selectedTemplateBits p S hm)=
        chronologicalWellStream p S hm := by
  rw [WellOutput.bits_eq saved constants placementNatural (length p S hm) (spacing p S hm)
    (bufferSteps p S hm) (length_even p S hm) hshift hscale hword (wellStoredPrecision p S hm)
    (wellNumerators p S hm) (Profile.profileBits (materialPrecision p S)) (selectedTemplateBits p S hm)
    (Represents.path_nonnegative S (precision p S hm) h)
    (Represents.original_nonnegative S (precision p S hm) h),h.sites_eq,List.length_map,
    indexed_wellRecords]
  rfl

#print axioms storedBits_eq_chronological
end Maxwell.Continuum.RealizationParameters
