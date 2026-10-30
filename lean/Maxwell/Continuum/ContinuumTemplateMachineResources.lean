import Maxwell.Continuum.FourierTensorOutputParameters
import Maxwell.Continuum.ContinuumCalibrationResources

/-! Actual continuum-selected tensor dimensions and arithmetic workspace.
The source promises discharge all frequency, radius and precision bounds. -/
noncomputable section
namespace Maxwell.Continuum.RealizationParameters
open Maxwell.Composition Calibration Profile Profile.WaveMachine.Runtime
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 16384
set_option maxHeartbeats 2500000
attribute [local irreducible] MasterConstants.exponent Parameters.sourceInput
  FiniteAlgorithm.mode FiniteAlgorithm.size FiniteAlgorithm.outputArithmeticCoefficient

def templateWorkspaceCoefficient (p : Source.Parameters) : ℕ :=
  ModeAllocation.outputWorkspaceCoefficient (calibrationInputCoefficient p)

def templateAliasCoefficient (p : Source.Parameters) : ℕ :=
  ModeAllocation.outputAliasCoefficient (calibrationInputCoefficient p)

def templateLoopCoefficient (p : Source.Parameters) : ℕ :=
  2*ModeAllocation.outputLoopCoefficient (calibrationInputCoefficient p)

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

theorem selected_tensor_machine_workspace (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    ModeAllocation.outputArithmeticWidth (length p S hm) (calibrationRadius p S hm)
      (templatePrecision p S) (energy p S hm)≤templateWorkspaceCoefficient p*logSize S := by
  have hN := (selected_precisions_linear p S hm hm2 hu).2.1
  have hi := selected_finite_inputs p S hm hm2 hu (templatePrecision p S) hN
  exact ModeAllocation.outputParameters_work (length_pos p S hm) (Parameters.inputLog_pos S.nnz)
    hi.1 hi.2.1 hi.2.2 (energy p S hm)

theorem selected_tensor_machine_aliases (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    RowArithmetic.rowCount (FiniteAlgorithm.mode (length p S hm) (calibrationRadius p S hm)
      (templatePrecision p S+2) (energy p S hm)).radius+1≤templateAliasCoefficient p*(logSize S)^33 := by
  have hN := (selected_precisions_linear p S hm hm2 hu).2.1
  have hi := selected_finite_inputs p S hm hm2 hu (templatePrecision p S) hN
  exact ModeAllocation.outputParameters_aliases (length_pos p S hm) (Parameters.inputLog_pos S.nnz)
    hi.1 hi.2.1 hi.2.2 (energy p S hm)

theorem selected_tensor_machine_loop (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    FiniteAlgorithm.outputFrequency (length p S hm) (calibrationRadius p S hm)
      (templatePrecision p S) (energy p S hm)+
    FiniteAlgorithm.outputTensorPrecision (length p S hm) (calibrationRadius p S hm)
      (templatePrecision p S) (energy p S hm)+
    ModeAllocation.outputArithmeticWidth (length p S hm) (calibrationRadius p S hm)
      (templatePrecision p S) (energy p S hm)+64≤templateLoopCoefficient p*(logSize S)^8 := by
  have hN := (selected_precisions_linear p S hm hm2 hu).2.1
  have hi := selected_finite_inputs p S hm hm2 hu (templatePrecision p S) hN
  exact ModeAllocation.outputParameters_loop (length_pos p S hm) (Parameters.inputLog_pos S.nnz)
    hi.1 hi.2.1 hi.2.2 (energy p S hm)

#print axioms selected_tensor_machine_workspace
#print axioms selected_tensor_machine_aliases
#print axioms selected_tensor_machine_loop
end Maxwell.Continuum.RealizationParameters
