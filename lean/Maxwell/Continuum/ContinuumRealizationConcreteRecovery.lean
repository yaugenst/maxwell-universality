import Maxwell.Continuum.ContinuumRealizationTemplatesCertified
import Maxwell.Continuum.ContinuumRealizationReportRange

/-! Every-field recovery for the literal finite-mode and compact-template
program.  All analytic, approximation and precision requirements have
been discharged; the finite eigenvalue/coupling enclosure input remains
separate from the solver's residual and moment-report contract. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace Maxwell.Continuum.RealizationParameters

open Maxwell.Composition Calibration EffectiveMass FiniteAuxiliary MasterConstants
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent FiniteAlgorithm.mode FiniteAlgorithm.size realMode pecCurlCurl

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

theorem concrete_every_field_recovery (hm2 : 2≤S.nnz) (hp : Source.Promises p S)
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
    Source.ResidualTarget S ((accuracy p S hm : ℝ)/4)
      (sparseMomentDecode S (precision p S hm)
        (weightedMomentValues (momentPrecision p S) C.wellStrength w)) := by
  have hw' : ∀i,|(w i : ℝ)-(inner ℂ (fieldRealProjection (selectedTemplates p S hm i))
      (GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))) u)).re|≤
        (epsilon p S hm : ℝ)/(2^27*max 1 (sites p S hm : ℝ)) := by
    simpa only [selectedTemplates_projection] using hw
  exact (selected_every_field_recovery p S hm hm2 hp hb C hC (selectedTemplates p S hm)
    (selectedTemplates_supported p S hm) (selectedTemplates_error p S hm) j hgood u hu w hw').2.2

theorem concrete_source_error (hm2 : 2≤S.nnz) (huS : IsUnit (Source.realMatrix S))
    (hb : S.source≠0) (C : Enclosures p S hm)
    (hC : C.mode.width≤(1/2 : ℚ)^(calibrationPrecision p S hm)) :
    ‖(selectedSource p S hm C : FieldL2)-
      idealSource (energyCalibration p S hm) (inverse_length_le_1024 (length_master p S hm))
        (centers p S hm) (alpha p S hm) (routedForcing S (precision p S hm))‖≤
      (sourceTolerance p S : ℝ)*‖routedForcing S (precision p S hm)‖ :=
  selected_source_error p S hm hm2 huS hb C hC (selectedTemplates p S hm)
    (selectedTemplates_supported p S hm) (selectedTemplates_error p S hm)

theorem concrete_source_norm (hm2 : 2≤S.nnz) (huS : IsUnit (Source.realMatrix S))
    (hb : S.source≠0) (C : Enclosures p S hm)
    (hC : C.mode.width≤(1/2 : ℚ)^(calibrationPrecision p S hm)) :
    ‖selectedSource p S hm C‖≤2*‖routedForcing S (precision p S hm)‖ :=
  selected_source_norm p S hm hm2 huS hb C hC (selectedTemplates p S hm)
    (selectedTemplates_supported p S hm) (selectedTemplates_error p S hm)

theorem concrete_report_range (hm2 : 2≤S.nnz) (huS : IsUnit (Source.realMatrix S))
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
    ∀i,|w i|<8*inverseBound p S hm*S.nnz := by
  apply selected_report_range p S hm hm2 huS hb C hC (selectedTemplates p S hm)
    (selectedTemplates_supported p S hm) (selectedTemplates_error p S hm) j hgood u hu w
  simpa only [selectedTemplates_projection] using hw

#print axioms concrete_every_field_recovery
#print axioms concrete_source_error
#print axioms concrete_report_range

end Maxwell.Continuum.RealizationParameters
