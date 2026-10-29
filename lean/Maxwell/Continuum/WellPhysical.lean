import Maxwell.Continuum.WellElliptic
import Maxwell.Continuum.WellHeatFourier
import Maxwell.Continuum.PeriodicHessianError

/-! The auxiliary scalar operator for the literal periodic-band Hessian.
The tensor and its ellipticity are already constructed, not supplied here. -/

noncomputable section

namespace Maxwell.Continuum.Well

open MeasureTheory Matrix
open scoped NNReal

def physicalResolvent : ScalarL2 →L[ℂ] ScalarL2 :=
  resolvent PeriodicBand.hessianOperator PeriodicBand.hessianOperator_nonneg

def physicalBirmanSchwinger : ScalarL2 →L[ℂ] ScalarL2 :=
  birmanSchwinger PeriodicBand.hessianOperator PeriodicBand.hessianOperator_nonneg

theorem physicalResolvent_unique (f : ScalarL2) :
    ∃! u : ScalarL2, WeakEllipticEquation PeriodicBand.hessianOperator u f := by
  refine ⟨physicalResolvent f, resolvent_weak_solution _ _ f, ?_⟩
  intro u hu
  exact (weakEllipticEquation_iff _ PeriodicBand.hessianOperator_nonneg u f).mp hu

theorem physicalResolvent_selfAdjoint : IsSelfAdjoint physicalResolvent :=
  resolvent_selfAdjoint _ _

theorem physicalBirmanSchwinger_selfAdjoint : IsSelfAdjoint physicalBirmanSchwinger :=
  birmanSchwinger_selfAdjoint _ _

theorem physicalBirmanSchwinger_nonnegative (u : ScalarL2) :
    0 ≤ RCLike.re (inner ℂ u (physicalBirmanSchwinger u)) :=
  birmanSchwinger_inner_nonneg _ _ u

theorem physical_diagonal_bounds (i : Fin 3) :
    (2 * FreeFiber.backgroundAmplitude)⁻¹ ≤ PeriodicBand.hessian i i ∧
      PeriodicBand.hessian i i ≤ 256 / FreeFiber.backgroundAmplitude := by
  have h := PeriodicBand.hessian_bounds (Pi.single i 1)
  simpa [PeriodicBand.hessian, Matrix.mulVec, dotProduct, Pi.single_apply] using h

theorem physical_diagonal_pos (i : Fin 3) : 0 < PeriodicBand.hessian i i := by
  have hρ := FreeFiber.backgroundAmplitude_pos
  exact lt_of_lt_of_le (by positivity) (physical_diagonal_bounds i).1

def physicalCoefficients (i : Fin 3) : ℝ≥0 :=
  ⟨PeriodicBand.hessian i i, (physical_diagonal_pos i).le⟩

theorem physicalCoefficients_ne_zero (i : Fin 3) : physicalCoefficients i ≠ 0 := by
  intro h
  have hc := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
  change PeriodicBand.hessian i i = 0 at hc
  exact (physical_diagonal_pos i).ne' hc

theorem physical_diagonalTensor : diagonalTensor physicalCoefficients = PeriodicBand.hessianOperator := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  rw [diagonalTensor_apply]
  change PeriodicBand.hessian i i * x i = (PeriodicBand.hessian *ᵥ x.ofLp) i
  simp [PeriodicBand.hessian, Matrix.mulVec_diagonal]

def physicalKernel : Space → ℝ := resolventKernel physicalCoefficients

theorem physicalKernel_integrable : Integrable physicalKernel :=
  resolventKernel_integrable _ physicalCoefficients_ne_zero

theorem physicalKernel_fourier (ξ : Space) :
    FourierTransform.fourier (fun x : Space => (physicalKernel x : ℂ)) ξ =
      ((1 + ellipticSymbol PeriodicBand.hessianOperator ξ)⁻¹ : ℝ) := by
  rw [← physical_diagonalTensor]
  exact resolventKernel_fourier _ physicalCoefficients_ne_zero ξ

end Maxwell.Continuum.Well
