import Maxwell.Continuum.ContinuumDecoder
import Maxwell.Continuum.ContinuumWellStrengthData
import Maxwell.Continuum.SourceGeometryVertexLookup
import Maxwell.Composition.SourcePhysicalDecoderRecords

/-! The singleton continuum decoder rows refer directly to the chronological
strength table and the integer coordinates already present in packed geometry.
No separate mode samples or caller-supplied decoder table are needed. -/
noncomputable section
namespace Maxwell.Continuum.RealizationParameters
open Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration Maxwell.Logical
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

theorem readout_numerator {saved} (geometry : Represents S (precision p S hm) saved) (i : Fin S.n) :
    (computedEnclosures p S hm).wellStrength (readoutSite p S hm i)=
      (wellNumerators p S hm ((sourceCircuit S (precision p S hm)).size+i.val):ℚ)/
        2^(wellStoredPrecision p S hm):=by
  have lookup:=geometry.original_vertex_lookup S (precision p S hm)
    (SourceEnumeration.vertexEquiv S (precision p S hm) (SourcePositive.inputCoordinate S (precision p S hm) i))
  rw [Equiv.symm_apply_apply,SourcePhysicalDecoderRecords.selected_index] at lookup
  obtain ⟨valid,atVertex⟩:=List.getElem?_eq_some_iff.mp lookup
  rw [wellNumerators_get p S hm _ valid,atVertex]
  rfl

theorem decoder_weight_stored {saved} (geometry : Represents S (precision p S hm) saved)
    (i : Fin S.n) (j : Fin (gridCount p S hm)) :
    (decoder p S hm).weight i j=normalizationScale S*
      ((wellNumerators p S hm ((sourceCircuit S (precision p S hm)).size+i.val):ℚ)/
        2^(wellStoredPrecision p S hm)):=by
  exact congrArg (normalizationScale S*·) (readout_numerator p S hm geometry i)

theorem gridAddress_value (i : SourceDecoration.Vertex S (precision p S hm)) :
    (gridAddress p S hm i).val=(integerCenter p S hm i 2).toNat+
      gridSide p S hm 2*(integerCenter p S hm i 1).toNat+
      (gridSide p S hm 1*gridSide p S hm 2)*(integerCenter p S hm i 0).toNat:=rfl

theorem decoder_description_singletons :
    Cost.FiniteDecoder.description (decoder p S hm)=
      Codec.nat S.n++Codec.nat (gridReportFormat p S hm).integerBits++
      Codec.nat (gridReportFormat p S hm).fractionalBits++Codec.nat (gridCount p S hm)++
      Codec.nat S.n++(List.finRange S.n).flatMap (fun i=>Codec.rat 0++Codec.nat 1++
        Codec.nat (gridAddress p S hm (readoutSite p S hm i)).val++
        Codec.rat (normalizationScale S*(computedEnclosures p S hm).wellStrength (readoutSite p S hm i))):=by
  simp only [Cost.FiniteDecoder.description,Cost.FiniteDecoder.descriptionData,
    Cost.FiniteDecoder.headerData,Cost.FiniteDecoder.rowData,decoder,Cost.DecoderParser.wire,
    Codec.list,List.length_map,List.length_finRange,Finset.sort_singleton,List.map_singleton,
    List.length_singleton,List.flatMap_map,List.flatMap_cons,List.flatMap_nil,
    Cost.DecoderParser.rationalPayload,Codec.rat,Codec.int,List.append_nil,List.append_assoc,List.cons_append,List.nil_append]
  rfl

#print axioms readout_numerator
#print axioms decoder_description_singletons
end Maxwell.Continuum.RealizationParameters
