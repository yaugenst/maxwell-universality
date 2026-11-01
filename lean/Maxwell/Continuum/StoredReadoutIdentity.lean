import Maxwell.Continuum.StoredReadoutStream
import Maxwell.Continuum.StoredChronologicalWells
import Maxwell.Continuum.ContinuumStoredDecoderData

/-! The right block of stored original vertices is exactly the continuum
readout-placement list, in source-variable order. -/
noncomputable section
namespace Maxwell.Continuum.RealizationParameters
open Maxwell.Cost Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration Maxwell.Logical
set_option maxHeartbeats 1000000
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
theorem readout_coordinate (i : Fin S.n) (j : Fin 3) :
    (GeometryOutput.terminalCoordinate (packedVector saved) constants
      (3*((sourceCircuit S (precision p S hm)).size+i.val)) j:ℤ)=
      integerCenter p S hm (readoutSite p S hm i) j:=by
  let index:=SourceEnumeration.vertexEquiv S (precision p S hm) (SourcePositive.inputCoordinate S (precision p S hm) i)
  have coord:=original_record_coordinate saved constants placementNatural (length p S hm) (spacing p S hm)
    (bufferSteps p S hm) (length_even p S hm) hshift hscale index
    (Represents.original_nonnegative S (precision p S hm) geometry index) j
  have atIndex : index.val=(sourceCircuit S (precision p S hm)).size+i.val:=
    SourcePhysicalDecoderRecords.selected_index S (precision p S hm) i
  rw [atIndex] at coord
  have point:=geometry.original (SourcePositive.inputCoordinate S (precision p S hm) i)
  change saved.original.get index=_ at point
  have site : terminalPoint (saved.original.get index)=SourceDecoration.site S (precision p S hm) (readoutSite p S hm i):=
    (congrArg terminalPoint point).trans (terminalPoint_embedding S (precision p S hm)
      (SourceRouting.inputCoordinate S (precision p S hm) i))
  have finish:=coord.trans (congrArg (fun x=>centerPoint (fun k=>(placementNatural k:ℤ))
    (length p S hm) (spacing p S hm) (bufferSteps p S hm) x j) site)
  have castPlacement : (fun k=>(placementNatural k:ℤ))=PeriodicBand.placementDiagonal:=funext placementNatural_cast
  rw [castPlacement,centerPoint_site] at finish
  exact finish


include geometry hshift hscale hword in
theorem readout_record (i : Fin S.n) :
    GeometryOutput.terminalBits (packedVector saved) constants
      (3*((sourceCircuit S (precision p S hm)).size+i.val))=readoutPlacementBits p S hm i:=by
  unfold GeometryOutput.terminalBits readoutPlacementBits placementBits
  rw [hword,readout_coordinate p S hm geometry constants hshift hscale i 0,
    readout_coordinate p S hm geometry constants hshift hscale i 1,
    readout_coordinate p S hm geometry constants hshift hscale i 2]
  rfl


include geometry hshift hscale hword in
theorem readout_stream :
    GeometryOutput.Readout.stream (packedVector saved) constants (sourceCircuit S (precision p S hm)).size S.n=
      readoutPlacementStream p S hm:=by
  simp only [GeometryOutput.Readout.stream,GeometryOutput.terminalStream,readoutPlacementStream,
    Codec.list,List.length_finRange]
  rw [←List.map_coe_finRange_eq_range,List.flatMap_map]
  apply congrArg (fun xs : List Bool=>Codec.nat S.n++xs)
  apply List.flatMap_congr
  intro i _
  rw [←Nat.mul_add]
  exact readout_record p S hm geometry constants hshift hscale hword i

#print axioms readout_coordinate
#print axioms readout_stream
end Maxwell.Continuum.RealizationParameters
