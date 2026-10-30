import Maxwell.Continuum.ContinuumRealizationTemplates
import Maxwell.Continuum.CalibrationFiniteMode

/-! Correctness of the literal selected real compact templates.  The
finite-mode algorithm discharges the physical Fourier approximation;
there is no numerical certificate or template-error input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace Maxwell.Continuum.RealizationParameters

open Maxwell.Composition Calibration EffectiveMass FiniteAuxiliary MasterConstants
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent FiniteAlgorithm.mode FiniteAlgorithm.size realMode

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

theorem selectedTemplates_certificate
    (i : SourceDecoration.Vertex S (precision p S hm)) :
    ‖selectedTemplates p S hm i‖≤2 ∧
      ‖selectedTemplates p S hm i-siteInsertion (length p S hm : ℝ)⁻¹ (centers p S hm i)
        (realMode (energyCalibration p S hm) (inverse_length_le_1024 (length_master p S hm)))‖≤
        (1/2 : ℝ)^(templatePrecision p S) := by
  have he := FiniteAlgorithm.mode_physical_error (length_master p S hm)
    (calibrationRadius p S hm) (templatePrecision p S+2) (energy p S hm)
    (energyCalibration p S hm)
  have hc := FiniteAlgorithm.outputTemplate_certificate (length_pos p S hm)
    (calibrationRadius p S hm) (templatePrecision p S) (energy p S hm)
    (energyCalibration p S hm) (inverse_length_le_1024 (length_master p S hm)) he
    (centers p S hm i)
  exact ⟨hc.2.1,hc.2.2.2⟩

theorem selectedTemplates_error
    (i : SourceDecoration.Vertex S (precision p S hm)) :
    ‖selectedTemplates p S hm i-siteInsertion (length p S hm : ℝ)⁻¹ (centers p S hm i)
      (realMode (energyCalibration p S hm) (inverse_length_le_1024 (length_master p S hm)))‖≤
      (1/2 : ℝ)^(templatePrecision p S) :=
  (selectedTemplates_certificate p S hm i).2

theorem selectedTemplates_norm
    (i : SourceDecoration.Vertex S (precision p S hm)) :
    ‖selectedTemplates p S hm i‖≤2 :=
  (selectedTemplates_certificate p S hm i).1

theorem selectedTemplateBits_bound (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    (selectedTemplateBits p S hm).length≤selectedTemplateBitCoefficient p*(logSize S)^25 :=
  selectedTemplateBits_polynomial p S hm hm2 hu
    (FiniteAlgorithm.mode_norm_le (length_master p S hm) (calibrationRadius p S hm)
      (templatePrecision p S+2) (energy p S hm) (energyCalibration p S hm))

#print axioms selectedTemplates_certificate
#print axioms selectedTemplateBits_bound

end Maxwell.Continuum.RealizationParameters
