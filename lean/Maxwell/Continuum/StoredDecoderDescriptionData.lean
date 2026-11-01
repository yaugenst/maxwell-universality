import Maxwell.Continuum.StoredDecoderDescription
import Maxwell.Continuum.StoredDecoderLoopData

/-! Identification of all five emitted runtime header words and every
executed row with the literal bytes of the concrete continuum decoder. -/
noncomputable section
namespace Maxwell.Continuum.RealizationParameters
open Maxwell.Cost Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration Maxwell.Logical
open RationalDataflow
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent computedEnclosures strengthData momentPrecision FiniteAuxiliary.messageRangeBits

theorem stored_decoder_bytes (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    {saved} (geometry : Represents S (precision p S hm) saved)
    (a : DecoderRow.Plan (packedLength saved) (siteCount saved))
    (packed : a.data=packedVector saved)
    (strengths : ∀i:Fin (siteCount saved),a.table.get i=Parts.literal (wellNumerators p S hm i.val:ℚ))
    (hshift : a.constants 982=length p S hm+length p S hm*bufferSteps p S hm+8)
    (hscale : ∀j:Fin 3,a.constants (983+j.val)=2*length p S hm*spacing p S hm*placementNatural j)
    (side1 : a.constants 4705=gridSide p S hm 1) (side2 : a.constants 4706=gridSide p S hm 2)
    (power : a.constants 144=2^wellStoredPrecision p S hm)
    (normalization : (a.constants 4707:ℚ)/(a.constants 4708)=normalizationScale S)
    (v : ℕ→ℕ) (dimension : v 500=S.n) (integerBits : v 4701=(gridReportFormat p S hm).integerBits)
    (fractionalBits : v 4702=(gridReportFormat p S hm).fractionalBits)
    (sampleCount : v 4703=gridCount p S hm) (hb : S.source≠0):
    StoredNatural.bits DecoderRow.headerPorts v++DecoderRow.rows a (sourceCircuit S (precision p S hm)).size S.n=
      Cost.FiniteDecoder.description (decoder p S hm):=by
  have header : StoredNatural.bits DecoderRow.headerPorts v=Codec.nat S.n++
      Codec.nat (gridReportFormat p S hm).integerBits++Codec.nat (gridReportFormat p S hm).fractionalBits++
      Codec.nat (gridCount p S hm)++Codec.nat S.n:=by
    simp only [StoredNatural.bits,DecoderRow.headerPorts,List.flatMap_cons,List.flatMap_nil,
      dimension,integerBits,fractionalBits,sampleCount,List.append_nil,List.append_assoc]
  rw [header]
  exact stored_decoder_description p S hm geometry a packed strengths hshift hscale side1 side2 power normalization hb

#print axioms stored_decoder_bytes
end Maxwell.Continuum.RealizationParameters
