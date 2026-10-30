import Maxwell.Continuum.ContinuumRealizationConcreteMessages
import Maxwell.Continuum.ContinuumCalibrationEnclosures

/-! Actual finite calibration, real compact source/test output, and every-field
recovery.  The only field assumptions are the solver residual and its rational
volume-moment reports, for a detuning draw outside the proved exceptional set. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace Maxwell.Continuum.RealizationParameters

open Maxwell.Composition Calibration EffectiveMass FiniteAuxiliary
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent FiniteAlgorithm.mode FiniteAlgorithm.size realMode pecCurlCurl

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

def computedSource : testL2Closure (BoxModes.boxDomain (BoxCutoff.side (box p S hm))) :=
  selectedSource p S hm (computedEnclosures p S hm)

def computedDielectric (hb : S.source≠0) (j : Fin (drawCount p S hm)) : ScalarDielectric :=
  (computedEnclosures p S hm).outputDielectric hb (materialPrecision p S) j

def computedBadDraws (hb : S.source≠0) : Finset ℕ :=
  (computedEnclosures p S hm).badDraws hb (materialPrecision p S)

theorem computedSource_real :
    fieldConjugation (computedSource p S hm : FieldL2)=(computedSource p S hm : FieldL2) :=
  selectedSource_real p S hm (computedEnclosures p S hm)

theorem computedSource_norm (hm2 : 2≤S.nnz) (huS : IsUnit (Source.realMatrix S)) (hb : S.source≠0) :
    ‖computedSource p S hm‖≤2*‖routedForcing S (precision p S hm)‖ :=
  concrete_source_norm p S hm hm2 huS hb (computedEnclosures p S hm)
    (computedEnclosures_mode_width p S hm).le

theorem computed_every_field_recovery (hm2 : 2≤S.nnz) (hp : Source.Promises p S)
    (hb : S.source≠0) (j : Fin (drawCount p S hm))
    (hgood : j.val∉(computedEnclosures p S hm).badDraws hb (materialPrecision p S))
    (u : OperatorDomain (BoxModes.boxDomain (BoxCutoff.side (box p S hm))))
    (hu : ‖maxwellGraphMap (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
      (computedDielectric p S hm hb j) u-computedSource p S hm‖≤
      (residual p S hm : ℝ)*‖computedSource p S hm‖)
    (w : SourceDecoration.Vertex S (precision p S hm) → ℚ)
    (hw : ∀i,|(w i : ℝ)-(inner ℂ (selectedTemplates p S hm i)
      (GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))) u)).re|≤
        (epsilon p S hm : ℝ)/(2^27*max 1 (sites p S hm : ℝ))) :
    Source.ResidualTarget S ((accuracy p S hm : ℝ)/4)
      (sparseMomentDecode S (precision p S hm)
        (weightedMomentValues (momentPrecision p S) (computedEnclosures p S hm).wellStrength w)) :=
  concrete_every_field_recovery p S hm hm2 hp hb (computedEnclosures p S hm)
    (computedEnclosures_mode_width p S hm).le j hgood u hu w hw

theorem computed_report_range (hm2 : 2≤S.nnz) (hp : Source.Promises p S)
    (hb : S.source≠0) (j : Fin (drawCount p S hm))
    (hgood : j.val∉(computedEnclosures p S hm).badDraws hb (materialPrecision p S))
    (u : OperatorDomain (BoxModes.boxDomain (BoxCutoff.side (box p S hm))))
    (hu : ‖maxwellGraphMap (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
      (computedDielectric p S hm hb j) u-computedSource p S hm‖≤
      (residual p S hm : ℝ)*‖computedSource p S hm‖)
    (w : SourceDecoration.Vertex S (precision p S hm) → ℚ)
    (hw : ∀i,|(w i : ℝ)-(inner ℂ (selectedTemplates p S hm i)
      (GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))) u)).re|≤
        (epsilon p S hm : ℝ)/(2^27*max 1 (sites p S hm : ℝ))) :
    ∀i,|w i|<8*inverseBound p S hm*S.nnz :=
  concrete_report_range p S hm hm2 hp.1 hb (computedEnclosures p S hm)
    (computedEnclosures_mode_width p S hm).le j hgood u hu w hw

theorem computed_serialized_recovery (hm2 : 2≤S.nnz) (hp : Source.Promises p S)
    (hb : S.source≠0) (j : Fin (drawCount p S hm))
    (hgood : j.val∉(computedEnclosures p S hm).badDraws hb (materialPrecision p S))
    (u : OperatorDomain (BoxModes.boxDomain (BoxCutoff.side (box p S hm))))
    (hu : ‖maxwellGraphMap (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
      (computedDielectric p S hm hb j) u-computedSource p S hm‖≤
      (residual p S hm : ℝ)*‖computedSource p S hm‖)
    (w : SourceDecoration.Vertex S (precision p S hm) → ℚ)
    (hw : ∀i,|(w i : ℝ)-(inner ℂ (selectedTemplates p S hm i)
      (GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))) u)).re|≤
        (epsilon p S hm : ℝ)/(2^27*max 1 (sites p S hm : ℝ))) :
    let hwr := fun i => (computed_report_range p S hm hm2 hp hb j hgood u hu w hw i).le
    let bits := selectedReportBits p S hm (computedEnclosures p S hm) hb w hwr
    (∀i,(bits i).length≤outputBitCoefficient p*logSize S) ∧
      Source.ResidualTarget S ((accuracy p S hm : ℝ)/4)
        (sparseMomentDecode S (precision p S hm) (decodedSelectedReports p S hm bits)) :=
  concrete_serialized_recovery p S hm hm2 hp hb (computedEnclosures p S hm)
    (computedEnclosures_mode_width p S hm).le j hgood u hu w hw

#print axioms computedSource_real
#print axioms computed_every_field_recovery
#print axioms computed_serialized_recovery

end Maxwell.Continuum.RealizationParameters
