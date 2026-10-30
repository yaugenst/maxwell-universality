import Maxwell.Continuum.CalibrationCompactModeBits
import Maxwell.Continuum.ContinuumCalibrationResources
import Maxwell.Continuum.ContinuumRealizationSelectedRecovery

/-! The literal real source/test templates at every selected physical
site, and their actual finite coefficient words. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace Maxwell.Continuum.RealizationParameters

open Maxwell.Composition Calibration Profile EffectiveMass FiniteAuxiliary MeasureTheory
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent FiniteAlgorithm.mode FiniteAlgorithm.size realMode

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

def selectedTemplates (i : SourceDecoration.Vertex S (precision p S hm)) : FieldL2 :=
  FiniteAlgorithm.outputTemplateField (length p S hm) (calibrationRadius p S hm)
    (templatePrecision p S) (energy p S hm) (length_pos p S hm) (centers p S hm i)

def selectedTemplateBits : List Bool :=
  FiniteAlgorithm.outputTemplateBits (length p S hm) (calibrationRadius p S hm)
    (templatePrecision p S) (energy p S hm)

theorem selectedTemplates_real (i : SourceDecoration.Vertex S (precision p S hm)) :
    fieldConjugation (selectedTemplates p S hm i)=selectedTemplates p S hm i :=
  realEncodedTemplateField_real _ _ _ _ _ _ _

theorem selectedTemplates_projection (i : SourceDecoration.Vertex S (precision p S hm)) :
    fieldRealProjection (selectedTemplates p S hm i)=selectedTemplates p S hm i :=
  fieldRealProjection_fixed (selectedTemplates_real p S hm i)

theorem selectedTemplates_supported (i : SourceDecoration.Vertex S (precision p S hm)) (k : Fin 3) :
    ∀ᵐx∂(volume : Measure Space),x∉Metric.ball (centers p S hm i) (length p S hm : ℝ) →
      selectedTemplates p S hm i k x=0 := by
  have hs := realEncodedTemplateField_supported
    (s := PeriodicSampling.Product.frequencyCube
      (FiniteAlgorithm.mode (length p S hm) (calibrationRadius p S hm)
        (templatePrecision p S+2) (energy p S hm)).radius)
    (q := Supercell.templateFrequency (FiniteAlgorithm.size (length p S hm)
      (calibrationRadius p S hm) (templatePrecision p S+2)) (length p S hm : ℚ))
    (a := Supercell.compactCoefficient
      (FiniteAlgorithm.size (length p S hm) (calibrationRadius p S hm) (templatePrecision p S+2))
      (templatePrecision p S)
      (lengthBits (FiniteAlgorithm.size (length p S hm) (calibrationRadius p S hm) (templatePrecision p S+2)))
      (FiniteAlgorithm.outputSupportBits (length p S hm) (calibrationRadius p S hm)
        (templatePrecision p S) (energy p S hm))
      (FiniteAlgorithm.mode (length p S hm) (calibrationRadius p S hm)
        (templatePrecision p S+2) (energy p S hm)))
    (Supercell.templateFrequencyBound
      (FiniteAlgorithm.size (length p S hm) (calibrationRadius p S hm) (templatePrecision p S+2))
      (length p S hm : ℚ)
      (FiniteAlgorithm.mode (length p S hm) (calibrationRadius p S hm)
        (templatePrecision p S+2) (energy p S hm)).radius)
    (Supercell.compactTensorBits (templatePrecision p S) (lengthBits (length p S hm))
      (FiniteAlgorithm.outputSupportBits (length p S hm) (calibrationRadius p S hm)
        (templatePrecision p S) (energy p S hm)))
    (L := ((length p S hm : ℚ) : ℝ))
    (by exact_mod_cast length_pos p S hm) (centers p S hm i) k
  filter_upwards [hs] with x hx hnot
  exact hx (by simpa only [Metric.mem_ball,dist_eq_norm,not_lt,Rat.cast_natCast] using hnot)

def selectedSource (C : Enclosures p S hm) :
    testL2Closure (BoxModes.boxDomain (BoxCutoff.side (box p S hm))) :=
  outputSource p S hm (sourcePrecision p S) C.sourceScalar (selectedTemplates p S hm)
    (selectedTemplates_supported p S hm)

theorem selectedSource_real (C : Enclosures p S hm) :
    fieldConjugation (selectedSource p S hm C : FieldL2)=(selectedSource p S hm C : FieldL2) :=
  outputSource_real p S hm _ _ _ _

theorem selectedSource_field (C : Enclosures p S hm) :
    (selectedSource p S hm C : FieldL2)=
      emittedSource S (precision p S hm) (sourcePrecision p S) C.sourceScalar (selectedTemplates p S hm) := by
  change emittedSource _ _ _ _ (fun i => fieldRealProjection (selectedTemplates p S hm i))=_
  simp only [selectedTemplates_projection]

def selectedTemplateBitCoefficient (p : Source.Parameters) : ℕ :=
  realCompactBitsCoefficient (FiniteAlgorithm.outputArithmeticCoefficient (calibrationInputCoefficient p))

theorem selectedTemplateBits_polynomial (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S))
    (hv : ‖(FiniteAlgorithm.mode (length p S hm) (calibrationRadius p S hm)
      (templatePrecision p S+2) (energy p S hm)).value‖≤2) :
    (selectedTemplateBits p S hm).length≤selectedTemplateBitCoefficient p*(logSize S)^25 := by
  have hN := (selected_precisions_linear p S hm hm2 hu).2.1
  have hi := selected_finite_inputs p S hm hm2 hu (templatePrecision p S) hN
  exact FiniteAlgorithm.outputTemplateBits_polynomial (length_pos p S hm)
    (Parameters.inputLog_pos S.nnz) hi.1 hi.2.1 hi.2.2 (energy p S hm) hv

#print axioms selectedTemplates_real
#print axioms selectedTemplates_supported
#print axioms selectedSource_field
#print axioms selectedTemplateBits_polynomial

end Maxwell.Continuum.RealizationParameters
