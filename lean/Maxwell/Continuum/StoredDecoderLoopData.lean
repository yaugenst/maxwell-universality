import Maxwell.Continuum.StoredDecoderLoop
import Maxwell.Continuum.StoredDecoderRowData

/-! The stored-array row traversal emits exactly the complete singleton
row list of the concrete continuum decoder. -/
noncomputable section
namespace Maxwell.Continuum.RealizationParameters
open Maxwell.Cost Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration Maxwell.Logical
open RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent computedEnclosures strengthData momentPrecision FiniteAuxiliary.messageRangeBits

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
variable {saved} (geometry : Represents S (precision p S hm) saved)
variable (a : DecoderRow.Plan (packedLength saved) (siteCount saved))
variable (packed : a.data=packedVector saved)
variable (strengths : ∀i:Fin (siteCount saved),a.table.get i=Parts.literal (wellNumerators p S hm i.val:ℚ))
variable (hshift : a.constants 982=length p S hm+length p S hm*bufferSteps p S hm+8)
variable (hscale : ∀j:Fin 3,a.constants (983+j.val)=2*length p S hm*spacing p S hm*placementNatural j)
variable (side1 : a.constants 4705=gridSide p S hm 1) (side2 : a.constants 4706=gridSide p S hm 2)
variable (power : a.constants 144=2^wellStoredPrecision p S hm)
variable (normalization : (a.constants 4707:ℚ)/(a.constants 4708)=normalizationScale S)

theorem readout_index_valid (i : Fin S.n) :
    (sourceCircuit S (precision p S hm)).size+i.val<siteCount saved:=by
  have hi:=(sourceCircuit S (precision p S hm)).circuit.inputs_le_size
  unfold siteCount
  omega

include geometry packed strengths hshift hscale side1 side2 power normalization in
theorem stored_decoder_row (hb : S.source≠0) (i : Fin S.n):
    DecoderRow.rowBits a ((sourceCircuit S (precision p S hm)).size+i.val)=
      Codec.rat 0++Codec.nat 1++Codec.nat (gridAddress p S hm (readoutSite p S hm i)).val++
        Codec.rat (normalizationScale S*(computedEnclosures p S hm).wellStrength (readoutSite p S hm i)):=by
  have hi:=readout_index_valid p S hm i (saved:=saved)
  rw [DecoderRow.rowBits,dite_eq_left hi]
  apply decoder_row_bits p S hm geometry hb i
  · intro j
    have point : DecoderRow.coordinate
        (DecoderRow.rowValues a.data a.constants ((sourceCircuit S (precision p S hm)).size+i.val)
          (a.table.get ⟨_,hi⟩)) j=
        GeometryOutput.terminalCoordinate (packedVector saved) a.constants
          (3*((sourceCircuit S (precision p S hm)).size+i.val)) j:=by
      rw [packed]
      fin_cases j <;> simp [DecoderRow.coordinate,DecoderRow.rowValues,GeometryOutput.terminalCoordinate]
    rw [point]
    exact readout_coordinate p S hm geometry a.constants hshift hscale i j
  · simpa [DecoderRow.rowValues] using side1
  · simpa [DecoderRow.rowValues] using side2
  · simp [DecoderRow.rowValues,strengths,Parts.literal]
  · simpa [DecoderRow.rowValues] using power
  · simpa [DecoderRow.rowValues] using normalization

include geometry packed strengths hshift hscale side1 side2 power normalization in
theorem stored_decoder_rows (hb : S.source≠0):
    DecoderRow.rows a (sourceCircuit S (precision p S hm)).size S.n=
      (List.finRange S.n).flatMap (fun i=>Codec.rat 0++Codec.nat 1++
        Codec.nat (gridAddress p S hm (readoutSite p S hm i)).val++
        Codec.rat (normalizationScale S*(computedEnclosures p S hm).wellStrength (readoutSite p S hm i))):=by
  rw [DecoderRow.rows,←List.map_coe_finRange_eq_range,List.flatMap_map]
  apply List.flatMap_congr
  intro i _
  exact stored_decoder_row p S hm geometry a packed strengths hshift hscale side1 side2 power normalization hb i

include geometry packed strengths hshift hscale side1 side2 power normalization in
theorem stored_decoder_description (hb : S.source≠0):
    Codec.nat S.n++Codec.nat (gridReportFormat p S hm).integerBits++
      Codec.nat (gridReportFormat p S hm).fractionalBits++Codec.nat (gridCount p S hm)++
      Codec.nat S.n++DecoderRow.rows a (sourceCircuit S (precision p S hm)).size S.n=
      Cost.FiniteDecoder.description (decoder p S hm):=by
  rw [decoder_description_singletons,stored_decoder_rows p S hm geometry a packed strengths
    hshift hscale side1 side2 power normalization hb]

#print axioms stored_decoder_description
end Maxwell.Continuum.RealizationParameters
