import Maxwell.Continuum.ContinuumRealizationComputedRecovery
import Maxwell.Continuum.ContinuumParameterWords
import Maxwell.Continuum.ParameterVolume
import Maxwell.Continuum.ContinuumBaseCases

/-! Soundness of the literal computed continuum instance. The construction
does not read the requested real accuracy. This theorem concerns its actual
PEC operator, computed material and source, and serialized volume reports;
the uniform execution cost is established separately. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace Maxwell.Continuum.RealizationParameters

open Maxwell.Composition SelfAdjointResolvent FiniteAuxiliary
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent Calibration.FiniteAlgorithm.mode pecCurlCurl

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

theorem requested_accuracy_bound (eta : ℝ) (heta : Source.RequestedAccuracy p S eta) :
    (accuracy p S hm : ℝ)/4≤eta := by
  have ha : (0 : ℝ)≤accuracy p S hm := by exact_mod_cast (accuracy_pos p S hm).le
  have hf := SelectedInput.accuracy_floor p S hm
  change (accuracy p S hm : ℝ)≤_ at hf
  linarith only [ha,hf,heta.1]

theorem computed_requested_recovery (hm2 : 2≤S.nnz) (hp : Source.Promises p S)
    (hb : S.source≠0) (j : Fin (drawCount p S hm))
    (hgood : j.val∉computedBadDraws p S hm hb)
    (u : OperatorDomain (BoxModes.boxDomain (BoxCutoff.side (box p S hm))))
    (hu : ‖maxwellGraphMap (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
      (computedDielectric p S hm hb j) u-computedSource p S hm‖≤
      (residual p S hm : ℝ)*‖computedSource p S hm‖)
    (w : SourceDecoration.Vertex S (precision p S hm) → ℚ)
    (hw : ∀i,|(w i : ℝ)-(inner ℂ (selectedTemplates p S hm i)
      (GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))) u)).re|≤
        (epsilon p S hm : ℝ)/(2^27*max 1 (sites p S hm : ℝ)))
    (eta : ℝ) (heta : Source.RequestedAccuracy p S eta) :
    let hwr := fun i => (computed_report_range p S hm hm2 hp hb j hgood u hu w hw i).le
    let bits := selectedReportBits p S hm (computedEnclosures p S hm) hb w hwr
    (∀i,(bits i).length≤outputBitCoefficient p*logSize S) ∧
      Source.ResidualTarget S eta
        (sparseMomentDecode S (precision p S hm) (decodedSelectedReports p S hm bits)) := by
  have h := computed_serialized_recovery p S hm hm2 hp hb j hgood u hu w hw
  refine ⟨h.1,?_⟩
  exact h.2.trans (mul_le_mul_of_nonneg_right
    (requested_accuracy_bound p S hm eta heta) (norm_nonneg (Source.rhs S)))

theorem computed_good_draw_inverse (hm2 : 2≤S.nnz) (huS : IsUnit (Source.realMatrix S))
    (hb : S.source≠0) (j : Fin (drawCount p S hm))
    (hgood : j.val∉computedBadDraws p S hm hb) :
    ∃ R : BoundedInverse (maxwellOperator (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
        (computedDielectric p S hm hb j)),
      ‖R.map‖≤(inverseBound p S hm : ℝ) ∧
      ‖maxwellGraphInverse (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
        (computedDielectric p S hm hb j) R‖≤27*(inverseBound p S hm : ℝ) ∧
      ‖maxwellGraphMap (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
          (computedDielectric p S hm hb j)‖*
        ‖maxwellGraphInverse (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
          (computedDielectric p S hm hb j) R‖≤(S.nnz : ℝ)^analysisBits p := by
  obtain ⟨R,hR,hg,hc⟩ := (computedEnclosures p S hm).good_draw_inverse hb
    (materialPrecision p S) j hgood
  exact ⟨R,hR,hg,hc.trans (inverse_polynomial p S hm hm2 huS)⟩

theorem computed_bad_probability (hb : S.source≠0) :
    DetuningGrid.gridProbability (drawCount p S hm)
      (Detuning.grid_pos S.nnz (count p S hm) (drawCount p S hm) hm
        (Parameters.sourceSpectralBudget_pos p S hm) (Detuning.gridSize_sufficient _ _))
      (computedBadDraws p S hm hb)≤3/(64*(S.nnz : ℝ)) :=
  (computedEnclosures p S hm).badDraws_probability hb (materialPrecision p S)

/-- The physical and precision guarantees hold for the concrete computed
instance and a single exceptional event, independently of the solver field. -/
theorem computed_physical_contract (hm2 : 2≤S.nnz) (huS : IsUnit (Source.realMatrix S))
    (hb : S.source≠0) :
    (∀j : Fin (drawCount p S hm), ∀x : Space,
      1≤(computedDielectric p S hm hb j).coefficient x ∧
        (computedDielectric p S hm hb j).coefficient x≤25) ∧
    fieldConjugation (computedSource p S hm : FieldL2)=(computedSource p S hm : FieldL2) ∧
    (∀i,fieldConjugation (selectedTemplates p S hm i)=selectedTemplates p S hm i) ∧
    (MeasureTheory.volume (BoxModes.openBox (BoxCutoff.side (box p S hm)))).toReal≤
      Parameters.sourceVolumeCoefficient p*(S.nnz : ℝ)^(3/2 : ℝ)*(logSize S : ℝ)^24 ∧
    (0 : ℝ)<residual p S hm ∧
    ((S.nnz : ℝ)^(2*Parameters.sourcePolynomialExponent p))⁻¹≤(residual p S hm : ℝ) ∧
    Maxwell.rationalBitLength (residual p S hm)≤(analysisBits p+4)*logSize S ∧
    Maxwell.rationalBitLength (energy p S hm)≤energyWordCoefficient p*logSize S ∧
    Detuning.randomBits S.nnz (count p S hm)≤
      (7+2^(12*Parameters.sourceMagnitude p))*logSize S := by
  refine ⟨?_,computedSource_real p S hm,selectedTemplates_real p S hm,?_,
    residual_pos p S hm,residual_polynomial p S hm hm2 huS,
    residual_word_bits p S hm hm2 huS,energy_word_bits p S hm hm2 huS,?_⟩
  · intro j x
    exact ⟨(computedDielectric p S hm hb j).lower x,(computedDielectric p S hm hb j).upper x⟩
  · exact Parameters.source_physical_volume_bound p S hm hm2 huS
  · exact Parameters.source_random_bits p S hm hm2 huS

#print axioms computed_requested_recovery
#print axioms computed_good_draw_inverse
#print axioms computed_bad_probability
#print axioms computed_physical_contract

end Maxwell.Continuum.RealizationParameters
