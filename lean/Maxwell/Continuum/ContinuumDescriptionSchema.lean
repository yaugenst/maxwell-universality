import Maxwell.Continuum.ChronologicalDescription
import Maxwell.Cost.DecoderParser.Skip

/-! The existing physical wire format has a fixed, executable grammar.
The schema stores no dimensions or coefficient counts in its finite code. -/

noncomputable section
namespace Maxwell.Continuum.DescriptionSchema
open Maxwell.Cost.DecoderParser
open RealizationParameters Profile Calibration Maxwell.Composition FiniteAuxiliary
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

abbrev integerShape : Shape := .pair .bit .nat
abbrev dyadicShape : Shape := .pair .nat integerShape
abbrev placementShape : Shape :=
  .pair integerShape (.pair integerShape (.pair integerShape .nat))
abbrev profileShape : Shape := .pair .nat (.list integerShape)
abbrev templateShape : Shape := .pair .nat (.pair profileShape profileShape)
abbrev wellShape : Shape :=
  .pair placementShape (.pair dyadicShape (.pair profileShape templateShape))
abbrev sourceShape : Shape := .pair placementShape (.pair dyadicShape templateShape)
abbrev cubeShape : Shape := .pair .nat (.pair .nat .nat)
abbrev headerShape : Shape := .pair .nat (.pair .nat (.pair .nat (.pair .nat
  (.pair .nat (.pair .nat (.pair .nat (.pair .nat
    (.pair rationalShape (.pair rationalShape (.pair rationalShape dyadicShape))))))))))
abbrev shape : Shape := .pair headerShape (.pair (.list cubeShape)
  (.pair (.list wellShape) (.pair (.list sourceShape) (.list placementShape))))

def integerData (z : ℤ) : Payload integerShape := (decide (z<0),z.natAbs)
def dyadicData {P : ℕ} (d : Dyadic P) : Payload dyadicShape := (P,integerData d.numerator)

theorem integer_wire (z : ℤ) : wire integerShape (integerData z)=Codec.int z := rfl

theorem dyadic_wire {P : ℕ} (d : Dyadic P) :
    wire dyadicShape (dyadicData d)=dyadicBits d := rfl

def profilePayload (N : ℕ) : Payload profileShape :=
  (profileWorkBits N,(profileData N).map fun d => integerData d.numerator)

theorem profile_wire (N : ℕ) : wire profileShape (profilePayload N)=profileBits N := by
  simp [profilePayload,wire,Codec.list,profileBits,List.flatMap_map,integerData,Codec.int]

def templatePayload {ι : Type*} {B : ℕ} (s : Finset ι) (q : ι→Fin 3→ℚ)
    (a : Fin 3→ι→ComplexDyadic B) (Q N : ℕ) : Payload templateShape :=
  (waveDegree (8*Q) N,profilePayload N,
    (B+(waveWorkBits (8*Q) N+waveWorkBits (8*Q) N+waveWorkBits (8*Q) N),
      (realFinalVectorData s q a Q N).map fun d => integerData d.numerator))

theorem template_wire {ι : Type*} {B : ℕ} (s : Finset ι) (q : ι→Fin 3→ℚ)
    (a : Fin 3→ι→ComplexDyadic B) (Q N : ℕ) :
    wire templateShape (templatePayload s q a Q N)=realCompactBits s q a Q N := by
  change Codec.nat _++(wire profileShape (profilePayload N)++_)=_
  rw [profile_wire]
  simp [wire,realCompactBits,realFinalVectorBits,Codec.list,List.flatMap_map,
    integerData,Codec.int,List.append_assoc]

def compactPayload (M : ℕ) (L : ℚ) (v : FourierData) (N ellM ellR ellL : ℕ) :
    Payload templateShape :=
  templatePayload (PeriodicSampling.Product.frequencyCube v.radius) (Supercell.templateFrequency M L)
    (fun i n => Supercell.compactCoefficient M N ellM ellR v n i)
    (Supercell.templateFrequencyBound M L v.radius) (Supercell.compactTensorBits N ellL ellR)

theorem compact_wire (M : ℕ) (L : ℚ) (v : FourierData) (N ellM ellR ellL : ℕ) :
    wire templateShape (compactPayload M L v N ellM ellR ellL)=
      Supercell.compactOutputBits M L v N ellM ellR ellL :=
  template_wire _ _ _ _ _

def outputPayload (L r N : ℕ) (z : ℚ) : Payload templateShape :=
  compactPayload (FiniteAlgorithm.size L r (N+2)) (L : ℚ) (FiniteAlgorithm.mode L r (N+2) z) N
    (lengthBits (FiniteAlgorithm.size L r (N+2)))
    (FiniteAlgorithm.outputSupportBits L r N z) (lengthBits L)

theorem output_wire (L r N : ℕ) (z : ℚ) :
    wire templateShape (outputPayload L r N z)=FiniteAlgorithm.outputTemplateBits L r N z :=
  compact_wire _ _ _ _ _ _ _

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

def selectedPayload : Payload templateShape :=
  outputPayload (length p S hm) (calibrationRadius p S hm) (templatePrecision p S) (energy p S hm)

theorem selected_wire : wire templateShape (selectedPayload p S hm)=selectedTemplateBits p S hm :=
  output_wire _ _ _ _

def placementData (i : SourceDecoration.Vertex S (precision p S hm)) : Payload placementShape :=
  (integerData (integerCenter p S hm i 0),integerData (integerCenter p S hm i 1),
    integerData (integerCenter p S hm i 2),length p S hm)

theorem placement_wire (i : SourceDecoration.Vertex S (precision p S hm)) :
    wire placementShape (placementData p S hm i)=placementBits p S hm i := by
  simp [placementData,wire,integerData,Codec.int,placementBits,List.append_assoc]

def wellData (i : SourceDecoration.Vertex S (precision p S hm)) : Payload wellShape :=
  (placementData p S hm i,
    dyadicData (strengthData p S hm (computedEnclosures p S hm).mode (computedEnclosures p S hm).coupling i),
    profilePayload (materialPrecision p S),selectedPayload p S hm)

theorem well_wire (i : SourceDecoration.Vertex S (precision p S hm)) :
    wire wellShape (wellData p S hm i)=wellBits p S hm i := by
  change wire placementShape _++(wire dyadicShape _++(wire profileShape _++wire templateShape _))=_
  rw [placement_wire,dyadic_wire,profile_wire,selected_wire]
  simp only [wellBits,List.append_assoc]

def sourceData (i : Fin S.n) : Payload sourceShape :=
  (placementData p S hm (sourceInputSite S (precision p S hm) i),
    dyadicData (sourceAmplitude S (sourcePrecision p S) (computedEnclosures p S hm).sourceScalar i),
    selectedPayload p S hm)

theorem source_wire (i : Fin S.n) :
    wire sourceShape (sourceData p S hm i)=sourceRecordBits p S hm i := by
  change wire placementShape _++(wire dyadicShape _++wire templateShape _)=_
  rw [placement_wire,dyadic_wire,selected_wire]
  simp only [sourceRecordBits,List.append_assoc]

def headerData (j : Fin (drawCount p S hm)) : Payload headerShape :=
  (S.n,S.nnz,Parameters.sourcePhysicalLengths p S hm 0,
    Parameters.sourcePhysicalLengths p S hm 1,Parameters.sourcePhysicalLengths p S hm 2,
    sourcePrecision p S,momentPrecision p S,
    messageRangeBits (inverseBound p S hm) S.nnz+momentPrecision p S+3,
    rationalPayload (energy p S hm),rationalPayload (residual p S hm),
    rationalPayload (normalizationScale S),dyadicData (detuningData p S hm j))

theorem header_wire (j : Fin (drawCount p S hm)) :
    wire headerShape (headerData p S hm j)=headerBits p S hm j := by
  simp [headerData,wire,headerBits,headerNats,rationalPayload,dyadicData,
    integerData,detuningBits,Codec.rat,Codec.int,List.append_assoc]

def cubeData {a b c : ℕ} (x : Fin a×Fin b×Fin c) : Payload cubeShape :=
  (x.1.val,x.2.1.val,x.2.2.val)

theorem cube_wire {a b c : ℕ} (x : Fin a×Fin b×Fin c) :
    wire cubeShape (cubeData x)=AmbientEncoding.cubeBits x := by
  simp [cubeData,wire,AmbientEncoding.cubeBits,List.append_assoc]

def data (j : Fin (drawCount p S hm)) : Payload shape :=
  (headerData p S hm j,(ambientCells p S hm).map cubeData,
    (SourceDecorationEnumeration.vertexList S (precision p S hm)).map (wellData p S hm),
    (List.finRange S.n).map (sourceData p S hm),
    (List.finRange S.n).map fun i =>
      placementData p S hm (Sum.inl (SourceRouting.inputCoordinate S (precision p S hm) i)))

theorem data_wire (j : Fin (drawCount p S hm)) :
    wire shape (data p S hm j)=chronologicalDescriptionBits p S hm j := by
  change wire headerShape _++(wire (.list cubeShape) _++
    (wire (.list wellShape) _++(wire (.list sourceShape) _++wire (.list placementShape) _)))=_
  rw [header_wire,list_wire_map,list_wire_map,list_wire_map,list_wire_map]
  simp only [cube_wire,well_wire,source_wire,placement_wire]
  simp [chronologicalDescriptionBits,ambientBits,AmbientEncoding.bits,ambientCells,chronologicalWellStream,sourceStream,
    readoutPlacementStream,List.append_assoc]
  rfl

#print axioms data_wire

end Maxwell.Continuum.DescriptionSchema
