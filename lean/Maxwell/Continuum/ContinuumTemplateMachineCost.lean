import Maxwell.Continuum.FourierTensorOutputCost
import Maxwell.Continuum.ContinuumTemplateMachineResources

/-! Source-selected component cost. All physical, Fourier and precision
budgets are discharged; the remaining storage inequalities refer to the
literal normalized calibration table produced by its machine initializer. -/
noncomputable section
namespace Maxwell.Continuum.RealizationParameters
open Maxwell.Composition Maxwell.Cost Calibration RationalDataflow PartArray
open Profile Profile.WaveMachine.Runtime
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 16384
set_option maxHeartbeats 2500000
attribute [local irreducible] MasterConstants.exponent Parameters.sourceInput
  FiniteAlgorithm.mode FiniteAlgorithm.size FiniteAlgorithm.iterations FiniteAlgorithm.precision

def templateComponentTimeCoefficient (p : Source.Parameters) (Bc H b d : ℕ) : ℕ :=
  ModeAllocation.computedTimeCoefficient (ModeAllocation.normalizationTensorCoefficient
    (ModeAllocation.outputNormalizationCoefficient (calibrationInputCoefficient p) Bc) H b d)

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

theorem selected_template_component_cost_of_storage
    (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) (B heap D den Bc H b d : ℕ)
    (a : CalibrationMatrix.Buffers (2*aliasArraySize (FiniteAlgorithm.mode (length p S hm)
      (calibrationRadius p S hm) (templatePrecision p S+2) (energy p S hm)).radius))
    (memory : ℕ→Bool) (hb : 33≤b) (hbmax : b<2000)
    (hB : B≤Bc*(logSize S)^b) (hheap : heap≤H*(logSize S)^d) :
    let t := PowerMachine.BufferNorm.normalizedOutput a
      (PowerMachine.BufferNorm.Allocation.outputTable
        (2*aliasArraySize (FiniteAlgorithm.mode (length p S hm) (calibrationRadius p S hm)
          (templatePrecision p S+2) (energy p S hm)).radius)
        (FiniteAlgorithm.iterations (templatePrecision p S+2))
        (FiniteAlgorithm.precision (length p S hm) (calibrationRadius p S hm) (templatePrecision p S+2))
        B heap memory)
      D (FiniteAlgorithm.iterations (templatePrecision p S+2))
        (FiniteAlgorithm.precision (length p S hm) (calibrationRadius p S hm) (templatePrecision p S+2)) den
    ModeAllocation.outputComponentCost (length p S hm) (calibrationRadius p S hm)
      (templatePrecision p S) (energy p S hm) t t≤
      templateComponentTimeCoefficient p Bc H b d*(logSize S)^4096 := by
  have hN := (selected_precisions_linear p S hm hm2 hu).2.1
  have hi := selected_finite_inputs p S hm hm2 hu (templatePrecision p S) hN
  exact ModeAllocation.outputNormalizedCost_polylog (energy p S hm) B heap D den Bc H b d a memory
    (length_pos p S hm) (Parameters.inputLog_pos S.nnz) hi.1 hi.2.1 hi.2.2 hb hbmax hB hheap

#print axioms selected_template_component_cost_of_storage
end Maxwell.Continuum.RealizationParameters
