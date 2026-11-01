import Maxwell.Continuum.StoredSourceStream
import Maxwell.Continuum.StoredReadoutIdentity

/-! The executed source serializer agrees with the original continuum
record definition, including its floor-dyadic rounding convention. -/
noncomputable section
namespace Maxwell.Continuum.RealizationParameters
open Maxwell.Cost Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration Maxwell.Logical
open FiniteAuxiliary
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 16384
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent computedEnclosures strengthData momentPrecision FiniteAuxiliary.messageRangeBits

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
variable {saved} (geometry : Represents S (precision p S hm) saved) (constants : ℕ→ℕ)
variable (hshift : constants 982=length p S hm+length p S hm*bufferSteps p S hm+8)
variable (hscale : ∀j:Fin 3,constants (983+j.val)=2*length p S hm*spacing p S hm*placementNatural j)
variable (hword : constants 966=length p S hm)

include geometry hshift hscale in
theorem source_coordinate (i : Fin S.n) (j : Fin 3) :
    (GeometryOutput.terminalCoordinate (packedVector saved) constants (3*i.val) j:ℤ)=
      integerCenter p S hm (sourceInputSite S (precision p S hm) i) j:=by
  let vertex : SourcePositive.Vertex S (precision p S hm):=
    Sum.inl (Sum.inl ((sourceCircuit S (precision p S hm)).circuit.inputIndex i))
  let index:=SourceEnumeration.vertexEquiv S (precision p S hm) vertex
  have coord:=original_record_coordinate saved constants placementNatural (length p S hm) (spacing p S hm)
    (bufferSteps p S hm) (length_even p S hm) hshift hscale index
    (Represents.original_nonnegative S (precision p S hm) geometry index) j
  have atIndex : index.val=i.val:=by
    simpa [index,vertex,SourceEnumeration.vertexEquiv] using
      (sourceCircuit S (precision p S hm)).circuit.inputIndex_value i
  rw [atIndex] at coord
  have point:=geometry.original vertex
  change saved.original.get index=_ at point
  have site : terminalPoint (saved.original.get index)=
      SourceDecoration.site S (precision p S hm) (sourceInputSite S (precision p S hm) i):=
    (congrArg terminalPoint point).trans (terminalPoint_embedding S (precision p S hm) (.inl vertex))
  have finish:=coord.trans (congrArg (fun x=>centerPoint (fun k=>(placementNatural k:ℤ))
    (length p S hm) (spacing p S hm) (bufferSteps p S hm) x j) site)
  have castPlacement : (fun k=>(placementNatural k:ℤ))=PeriodicBand.placementDiagonal:=funext placementNatural_cast
  rw [castPlacement,centerPoint_site] at finish
  exact finish

include geometry hshift hscale hword in
theorem source_placement (i : Fin S.n) :
    GeometryOutput.terminalBits (packedVector saved) constants (3*i.val)=
      placementBits p S hm (sourceInputSite S (precision p S hm) i):=by
  unfold GeometryOutput.terminalBits placementBits
  rw [hword,source_coordinate p S hm geometry constants hshift hscale i 0,
    source_coordinate p S hm geometry constants hshift hscale i 1,
    source_coordinate p S hm geometry constants hshift hscale i 2]
variable (q : SourcePayload.Plan (packedLength saved))
variable (hdata : q.data=packedVector saved) (hconstants : q.constants=constants)
variable (hsource : q.source=List.ofFn S.source) (hprecision : q.precision=sourcePrecision p S)
variable (hscalar : q.scalar=(computedEnclosures p S hm).sourceScalar/Normalization.sourceScale S)
variable (htemplate : q.template=selectedTemplateBits p S hm)

include geometry hshift hscale hword hdata hconstants hsource hprecision hscalar htemplate in
theorem source_row (i : Fin S.n) : SourcePayload.rowBits q i.val=sourceRecordBits p S hm i := by
  rw [SourcePayload.rowBits,hdata,hconstants,hsource,hprecision,hscalar,htemplate,
    source_placement p S hm geometry constants hshift hscale hword i]
  have hlt : i.val<(List.ofFn S.source).length:=by simp
  simp only [List.getElem?_eq_getElem hlt,Option.getD_some,List.getElem_ofFn]
  have scalarEq : S.source i*((computedEnclosures p S hm).sourceScalar/Normalization.sourceScale S)=
      (computedEnclosures p S hm).sourceScalar*Normalization.normalizedSource S i:=by
    simp only [Normalization.normalizedSource]
    ring
  rw [scalarEq]
  simp only [sourceRecordBits,sourceAmplitude,SourcePayload.payloadBits,dyadicBits,List.append_assoc]

include geometry hshift hscale hword hdata hconstants hsource hprecision hscalar htemplate in
theorem source_stream : SourcePayload.streamBits q=sourceStream p S hm := by
  simp only [SourcePayload.streamBits,SourcePayload.rows,sourceStream,Codec.list,List.length_finRange,
    hsource,List.length_ofFn,Nat.zero_add]
  rw [←List.map_coe_finRange_eq_range,List.flatMap_map]
  apply congrArg (fun xs : List Bool=>Codec.nat S.n++xs)
  apply List.flatMap_congr
  intro i _
  exact source_row p S hm geometry constants hshift hscale hword q hdata hconstants hsource hprecision hscalar htemplate i

#print axioms source_stream
end Maxwell.Continuum.RealizationParameters
