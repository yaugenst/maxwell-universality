import Maxwell.Continuum.ContinuumReductionSoundness
import Maxwell.Continuum.ContinuumScalarResources
import Maxwell.Continuum.ContinuumNormalizationWords

/-! Recovery from literal fixed-width raw volume reports. The decoder multiplies
the reported dyadic by the emitted dyadic well strength and the input
normalization scale exactly; it never receives an unbounded rational report. -/

namespace Maxwell.Continuum

theorem roundDyadic_product_value {P Q : ℕ} (a : Maxwell.Dyadic P) (b : Maxwell.Dyadic Q) :
    (roundDyadic (P+Q) (a.value*b.value)).value=a.value*b.value := by
  have he : a.value*b.value*(2 : ℚ)^(P+Q)=((a.numerator*b.numerator : ℤ) : ℚ) := by
    simp only [Maxwell.Dyadic.value,pow_add,Int.cast_mul]
    field_simp
  change (⌊a.value*b.value*(2 : ℚ)^(P+Q)⌋ : ℚ)/(2 : ℚ)^(P+Q)=a.value*b.value
  rw [he,Int.floor_intCast]
  exact (div_eq_iff (by positivity : (2 : ℚ)^(P+Q)≠0)).mpr he.symm

end Maxwell.Continuum

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace Maxwell.Continuum.RealizationParameters

open Maxwell.Composition Calibration EffectiveMass FiniteAuxiliary MasterConstants
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent FiniteAlgorithm.mode FiniteAlgorithm.size realMode pecCurlCurl
  computedEnclosures strengthData

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

abbrev RawReportWord := Fin (2^(messageRangeBits (inverseBound p S hm) S.nnz+momentPrecision p S+3))

def rawReportDyadic (w : RawReportWord p S hm) : Maxwell.Dyadic (momentPrecision p S) :=
  momentWordDyadic (momentPrecision p S)
    (messageRangeBits (inverseBound p S hm) S.nnz+momentPrecision p S+2) w

def rawReportBits (w : RawReportWord p S hm) : List Bool :=
  momentWordSerial (messageRangeBits (inverseBound p S hm) S.nnz+momentPrecision p S+2) w

def weightedRawReports (C : Enclosures p S hm)
    (w : SourceDecoration.Vertex S (precision p S hm) → RawReportWord p S hm) :
    SourceDecoration.Vertex S (precision p S hm) → ℚ :=
  fun i => C.wellStrength i*(rawReportDyadic p S hm (w i)).value

def decodeRawReports (w : SourceDecoration.Vertex S (precision p S hm) → RawReportWord p S hm) :
    Fin S.n → ℚ :=
  sparseMomentDecode S (precision p S hm) (weightedRawReports p S hm (computedEnclosures p S hm) w)

theorem rawReportBits_length (hm2 : 2≤S.nnz) (huS : IsUnit (Source.realMatrix S))
    (w : RawReportWord p S hm) :
    (rawReportBits p S hm w).length≤outputBitCoefficient p*logSize S :=
  moment_serial_linear p S hm hm2 huS w

theorem weightedRawReports_exact (C : Enclosures p S hm)
    (w : SourceDecoration.Vertex S (precision p S hm) → RawReportWord p S hm) :
    weightedMomentValues
      (onsitePrecision (length p S hm) (spacing p S hm) (length_pos p S hm)+momentPrecision p S)
      C.wellStrength (fun i => (rawReportDyadic p S hm (w i)).value)=weightedRawReports p S hm C w := by
  funext i
  exact roundDyadic_product_value (strengthData p S hm C.mode C.coupling i)
    (rawReportDyadic p S hm (w i))

theorem concrete_raw_report_recovery (hm2 : 2≤S.nnz) (hp : Source.Promises p S)
    (hb : S.source≠0) (C : Enclosures p S hm)
    (hC : C.mode.width≤(1/2 : ℚ)^(calibrationPrecision p S hm))
    (j : Fin (drawCount p S hm)) (hgood : j.val∉C.badDraws hb (materialPrecision p S))
    (u : OperatorDomain (BoxModes.boxDomain (BoxCutoff.side (box p S hm))))
    (hu : ‖maxwellGraphMap (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
      (C.outputDielectric hb (materialPrecision p S) j) u-selectedSource p S hm C‖≤
      (residual p S hm : ℝ)*‖selectedSource p S hm C‖)
    (w : SourceDecoration.Vertex S (precision p S hm) → RawReportWord p S hm)
    (hw : ∀i,|((rawReportDyadic p S hm (w i)).value : ℝ)-(inner ℂ (selectedTemplates p S hm i)
      (GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))) u)).re|≤
        (epsilon p S hm : ℝ)/(2^27*max 1 (sites p S hm : ℝ))) :
    Source.ResidualTarget S ((accuracy p S hm : ℝ)/4)
      (sparseMomentDecode S (precision p S hm) (weightedRawReports p S hm C w)) := by
  have hCR : (C.mode.width : ℝ)≤(1/2 : ℝ)^(calibrationPrecision p S hm) := by
    simpa only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr hC
  have hP : (1/2 : ℝ)^(
      onsitePrecision (length p S hm) (spacing p S hm) (length_pos p S hm)+momentPrecision p S)≤
      (epsilon p S hm : ℝ)/(2^27*max 1 (sites p S hm : ℝ)) :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left _ _)).trans
      (moment_precision_budget p S hm hm2 hp.1)
  have hw' : ∀i,|((rawReportDyadic p S hm (w i)).value : ℝ)-
      (inner ℂ (fieldRealProjection (selectedTemplates p S hm i))
      (GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))) u)).re|≤
        (epsilon p S hm : ℝ)/(2^27*max 1 (sites p S hm : ℝ)) := by
    simpa only [selectedTemplates_projection] using hw
  have h := (every_field_recovery p S hm hm2 hp hb C (materialPrecision p S)
    (sourceTolerance_pos p S).le (sourceTolerance_bound p S hm hm2 hp.1)
    (material_precision_budget p S hm hm2 hp.1) (selectedTemplates p S hm)
    (selectedTemplates_norm p S hm) (selectedTemplates_supported p S hm)
    (fun i => (selectedTemplates_error p S hm i).trans (template_precision_budget p S hm hm2 hp.1))
    (sourcePrecision p S) C.sourceScalar
    (C.sourceScalar_tolerance (hCR.trans (calibration_source_budget p S hm)))
    (source_precision_budget p S) j hgood u hu
    (onsitePrecision (length p S hm) (spacing p S hm) (length_pos p S hm)+momentPrecision p S)
    (fun i => (rawReportDyadic p S hm (w i)).value) hP hw').2.2
  rw [weightedRawReports_exact] at h
  exact h

theorem computed_raw_report_recovery (hm2 : 2≤S.nnz) (hp : Source.Promises p S)
    (hb : S.source≠0) (j : Fin (drawCount p S hm))
    (hgood : j.val∉computedBadDraws p S hm hb)
    (u : OperatorDomain (BoxModes.boxDomain (BoxCutoff.side (box p S hm))))
    (hu : ‖maxwellGraphMap (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
      (computedDielectric p S hm hb j) u-computedSource p S hm‖≤
      (residual p S hm : ℝ)*‖computedSource p S hm‖)
    (w : SourceDecoration.Vertex S (precision p S hm) → RawReportWord p S hm)
    (hw : ∀i,|((rawReportDyadic p S hm (w i)).value : ℝ)-(inner ℂ (selectedTemplates p S hm i)
      (GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))) u)).re|≤
        (epsilon p S hm : ℝ)/(2^27*max 1 (sites p S hm : ℝ)))
    (eta : ℝ) (heta : Source.RequestedAccuracy p S eta) :
    Source.ResidualTarget S eta (decodeRawReports p S hm w) := by
  have h := concrete_raw_report_recovery p S hm hm2 hp hb (computedEnclosures p S hm)
    (computedEnclosures_mode_width p S hm).le j hgood u hu w hw
  exact h.trans (mul_le_mul_of_nonneg_right (requested_accuracy_bound p S hm eta heta)
    (norm_nonneg (Source.rhs S)))

#print axioms weightedRawReports_exact
#print axioms computed_raw_report_recovery
#print axioms rawReportBits_length

end Maxwell.Continuum.RealizationParameters
