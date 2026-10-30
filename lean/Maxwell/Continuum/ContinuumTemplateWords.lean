import Maxwell.Continuum.CalibrationCompactModeWords
import Maxwell.Continuum.ContinuumRealizationTemplatesCertified

/-! Source-selected degree and individual coefficient words, with all
finite-calibration and parameter inequalities discharged. -/

noncomputable section
namespace Maxwell.Continuum.RealizationParameters
open Maxwell.Composition Calibration Profile
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
attribute [local irreducible] MasterConstants.exponent Parameters.sourceInput
  FiniteAlgorithm.mode FiniteAlgorithm.size FiniteAlgorithm.outputArithmeticCoefficient

def selectedTensorDegreeCoefficient (p : Source.Parameters) : ℕ :=
  waveDegreeCoefficient (FiniteAlgorithm.outputArithmeticCoefficient (calibrationInputCoefficient p))

def selectedTensorWordCoefficient (p : Source.Parameters) : ℕ :=
  FiniteAlgorithm.outputWordCoefficient (calibrationInputCoefficient p)

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

theorem selected_tensor_degree (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    FiniteAlgorithm.outputTemplateDegree (length p S hm) (calibrationRadius p S hm)
      (templatePrecision p S) (energy p S hm)≤selectedTensorDegreeCoefficient p*(logSize S)^8 := by
  have hN := (selected_precisions_linear p S hm hm2 hu).2.1
  have hi := selected_finite_inputs p S hm hm2 hu (templatePrecision p S) hN
  exact FiniteAlgorithm.outputTemplateDegree_polynomial (length_pos p S hm)
    (Parameters.inputLog_pos S.nnz) hi.1 hi.2.1 hi.2.2 (energy p S hm)

theorem selected_tensor_coefficient_words (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S))
    (c : Fin 3) (j : Fin 3→Fin (FiniteAlgorithm.outputTemplateDegree (length p S hm)
      (calibrationRadius p S hm) (templatePrecision p S) (energy p S hm))) :
    (FiniteAlgorithm.outputTemplateCoefficient (length p S hm) (calibrationRadius p S hm)
      (templatePrecision p S) (energy p S hm) c j).numeratorBits≤
        selectedTensorWordCoefficient p*logSize S := by
  have hN := (selected_precisions_linear p S hm hm2 hu).2.1
  have hi := selected_finite_inputs p S hm hm2 hu (templatePrecision p S) hN
  exact FiniteAlgorithm.outputTemplateCoefficient_bits (length_pos p S hm)
    (Parameters.inputLog_pos S.nnz) hi.1 hi.2.1 hi.2.2 (energy p S hm)
    (FiniteAlgorithm.mode_norm_le (length_master p S hm) (calibrationRadius p S hm)
      (templatePrecision p S+2) (energy p S hm) (energyCalibration p S hm)) c j

theorem selected_tensor_denominator (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    Supercell.compactFourierBits (templatePrecision p S)
      (lengthBits (FiniteAlgorithm.size (length p S hm) (calibrationRadius p S hm)
        (templatePrecision p S+2)))
      (FiniteAlgorithm.outputSupportBits (length p S hm) (calibrationRadius p S hm)
        (templatePrecision p S) (energy p S hm))+
      3*waveWorkBits
        (8*FiniteAlgorithm.outputFrequency (length p S hm) (calibrationRadius p S hm)
          (templatePrecision p S) (energy p S hm))
        (FiniteAlgorithm.outputTensorPrecision (length p S hm) (calibrationRadius p S hm)
          (templatePrecision p S) (energy p S hm))≤selectedTensorWordCoefficient p*logSize S := by
  have hN := (selected_precisions_linear p S hm hm2 hu).2.1
  have hi := selected_finite_inputs p S hm hm2 hu (templatePrecision p S) hN
  exact FiniteAlgorithm.outputTemplateDenominator_linear (length_pos p S hm)
    (Parameters.inputLog_pos S.nnz) hi.1 hi.2.1 hi.2.2 (energy p S hm)

#print axioms selected_tensor_degree
#print axioms selected_tensor_coefficient_words
#print axioms selected_tensor_denominator
end Maxwell.Continuum.RealizationParameters
