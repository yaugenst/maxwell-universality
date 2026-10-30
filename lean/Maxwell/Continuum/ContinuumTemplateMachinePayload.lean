import Maxwell.Continuum.FourierTensorOutputPayload
import Maxwell.Continuum.ContinuumRealizationTemplatesCertified

/-! The source-selected payload is exactly the declared real template.
Mode normalization is supplied by the actual finite calibration theorem. -/
noncomputable section
namespace Maxwell.Continuum.RealizationParameters
open Maxwell.Composition Maxwell.Cost Calibration RationalDataflow PartArray
open Profile Profile.WaveMachine.Runtime
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 16384
set_option maxHeartbeats 2500000
attribute [local irreducible] MasterConstants.exponent Parameters.sourceInput
  FiniteAlgorithm.mode FiniteAlgorithm.size

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

theorem selectedTemplateBits_components
    (a : Table (2*aliasArraySize (FiniteAlgorithm.mode (length p S hm) (calibrationRadius p S hm)
      (templatePrecision p S+2) (energy p S hm)).radius))
    (ha : GlobalPower.tableData (FiniteAlgorithm.mode (length p S hm) (calibrationRadius p S hm)
      (templatePrecision p S+2) (energy p S hm)).radius a=
      FiniteAlgorithm.mode (length p S hm) (calibrationRadius p S hm)
        (templatePrecision p S+2) (energy p S hm)) :
    selectedTemplateBits p S hm=
      ModeAllocation.outputTemplateHeader (length p S hm) (calibrationRadius p S hm)
        (templatePrecision p S) (energy p S hm)++
      ModeAllocation.outputComponentPayload (length p S hm) (calibrationRadius p S hm)
        (templatePrecision p S) (energy p S hm) a 0++
      ModeAllocation.outputComponentPayload (length p S hm) (calibrationRadius p S hm)
        (templatePrecision p S) (energy p S hm) a 1++
      ModeAllocation.outputComponentPayload (length p S hm) (calibrationRadius p S hm)
        (templatePrecision p S) (energy p S hm) a 2 :=
  ModeAllocation.outputTemplateBits_components _ _ _ _ a ha

theorem selected_template_table_norm
    (a : Table (2*aliasArraySize (FiniteAlgorithm.mode (length p S hm) (calibrationRadius p S hm)
      (templatePrecision p S+2) (energy p S hm)).radius))
    (ha : GlobalPower.tableData (FiniteAlgorithm.mode (length p S hm) (calibrationRadius p S hm)
      (templatePrecision p S+2) (energy p S hm)).radius a=
      FiniteAlgorithm.mode (length p S hm) (calibrationRadius p S hm)
        (templatePrecision p S+2) (energy p S hm)) :
    ‖(GlobalPower.tableData (FiniteAlgorithm.mode (length p S hm) (calibrationRadius p S hm)
      (templatePrecision p S+2) (energy p S hm)).radius a).value‖≤2 := by
  rw [ha]
  exact FiniteAlgorithm.mode_norm_le (length_master p S hm) (calibrationRadius p S hm)
    (templatePrecision p S+2) (energy p S hm) (energyCalibration p S hm)

#print axioms selectedTemplateBits_components
#print axioms selected_template_table_norm
end Maxwell.Continuum.RealizationParameters
