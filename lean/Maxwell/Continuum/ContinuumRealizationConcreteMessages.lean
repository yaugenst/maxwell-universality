import Maxwell.Continuum.ContinuumRealizationConcreteRecovery

/-! Literal signed Boolean messages for the concrete compact tests.
The actual field estimate supplies the word range; exact decoding
recovers the rounded rational data used by the source solver. -/

namespace Maxwell.Continuum.FiniteAuxiliary

def momentBitsDyadic (P B : ℕ) (bits : List Bool) : Maxwell.Dyadic P :=
  ⟨(Maxwell.Codec.bitsValue bits : ℤ)-(2 : ℤ)^B⟩

theorem momentBitsDyadic_serial (P B : ℕ) (w : Fin (2^(B+1))) :
    momentBitsDyadic P B (momentWordSerial B w)=momentWordDyadic P B w := by
  simp only [momentBitsDyadic,momentWordDyadic,momentWordSerial_value]

end Maxwell.Continuum.FiniteAuxiliary

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace Maxwell.Continuum.RealizationParameters

open Maxwell.Composition Calibration EffectiveMass FiniteAuxiliary
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent FiniteAlgorithm.mode FiniteAlgorithm.size realMode pecCurlCurl

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

theorem wellStrength_abs (C : Enclosures p S hm) (hb : S.source≠0)
    (i : SourceDecoration.Vertex S (precision p S hm)) : |C.wellStrength i|≤1 := by
  have h0 : (0 : ℚ)≤C.wellStrength i := by exact_mod_cast C.wellStrength_nonneg hb i
  rw [abs_of_nonneg h0]
  exact_mod_cast C.wellStrength_le_one hb i

def selectedReportWords (C : Enclosures p S hm) (hb : S.source≠0)
    (w : SourceDecoration.Vertex S (precision p S hm) → ℚ)
    (hwr : ∀i,|w i|≤8*inverseBound p S hm*S.nnz) :
    SourceDecoration.Vertex S (precision p S hm) →
      Fin (2^(messageRangeBits (inverseBound p S hm) S.nnz+momentPrecision p S+3)) :=
  fun i => encodedMomentReport (inverseBound p S hm) S.nnz (momentPrecision p S)
    (C.wellStrength i) (w i) (wellStrength_abs p S hm C hb i) (hwr i)

def selectedReportBits (C : Enclosures p S hm) (hb : S.source≠0)
    (w : SourceDecoration.Vertex S (precision p S hm) → ℚ)
    (hwr : ∀i,|w i|≤8*inverseBound p S hm*S.nnz) :
    SourceDecoration.Vertex S (precision p S hm) → List Bool :=
  fun i => momentWordSerial (messageRangeBits (inverseBound p S hm) S.nnz+momentPrecision p S+2)
    (selectedReportWords p S hm C hb w hwr i)

def decodedSelectedReports
    (bits : SourceDecoration.Vertex S (precision p S hm) → List Bool) :
    SourceDecoration.Vertex S (precision p S hm) → ℚ :=
  fun i => (momentBitsDyadic (momentPrecision p S)
    (messageRangeBits (inverseBound p S hm) S.nnz+momentPrecision p S+2) (bits i)).value

theorem selectedReportBits_decode (C : Enclosures p S hm) (hb : S.source≠0)
    (w : SourceDecoration.Vertex S (precision p S hm) → ℚ)
    (hwr : ∀i,|w i|≤8*inverseBound p S hm*S.nnz) :
    decodedSelectedReports p S hm (selectedReportBits p S hm C hb w hwr)=
      weightedMomentValues (momentPrecision p S) C.wellStrength w := by
  funext i
  simp only [decodedSelectedReports,selectedReportBits,momentBitsDyadic_serial,
    selectedReportWords,encodedMomentReport_value,weightedMomentValues]

theorem selectedReportBits_linear (hm2 : 2≤S.nnz) (huS : IsUnit (Source.realMatrix S))
    (C : Enclosures p S hm) (hb : S.source≠0)
    (w : SourceDecoration.Vertex S (precision p S hm) → ℚ)
    (hwr : ∀i,|w i|≤8*inverseBound p S hm*S.nnz)
    (i : SourceDecoration.Vertex S (precision p S hm)) :
    (selectedReportBits p S hm C hb w hwr i).length≤outputBitCoefficient p*logSize S :=
  moment_serial_linear p S hm hm2 huS (selectedReportWords p S hm C hb w hwr i)

theorem concrete_serialized_recovery (hm2 : 2≤S.nnz) (hp : Source.Promises p S)
    (hb : S.source≠0) (C : Enclosures p S hm)
    (hC : C.mode.width≤(1/2 : ℚ)^(calibrationPrecision p S hm))
    (j : Fin (drawCount p S hm)) (hgood : j.val∉C.badDraws hb (materialPrecision p S))
    (u : OperatorDomain (BoxModes.boxDomain (BoxCutoff.side (box p S hm))))
    (hu : ‖maxwellGraphMap (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
      (C.outputDielectric hb (materialPrecision p S) j) u-selectedSource p S hm C‖≤
      (residual p S hm : ℝ)*‖selectedSource p S hm C‖)
    (w : SourceDecoration.Vertex S (precision p S hm) → ℚ)
    (hw : ∀i,|(w i : ℝ)-(inner ℂ (selectedTemplates p S hm i)
      (GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))) u)).re|≤
        (epsilon p S hm : ℝ)/(2^27*max 1 (sites p S hm : ℝ))) :
    let hwr := fun i => (concrete_report_range p S hm hm2 hp.1 hb C hC j hgood u hu w hw i).le
    let bits := selectedReportBits p S hm C hb w hwr
    (∀i,(bits i).length≤outputBitCoefficient p*logSize S) ∧
      Source.ResidualTarget S ((accuracy p S hm : ℝ)/4)
        (sparseMomentDecode S (precision p S hm) (decodedSelectedReports p S hm bits)) := by
  dsimp only
  refine ⟨fun i => selectedReportBits_linear p S hm hm2 hp.1 C hb w _ i,?_⟩
  rw [selectedReportBits_decode]
  exact concrete_every_field_recovery p S hm hm2 hp hb C hC j hgood u hu w hw

#print axioms selectedReportBits_decode
#print axioms concrete_serialized_recovery

end Maxwell.Continuum.RealizationParameters
