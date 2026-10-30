import Maxwell.Continuum.PeriodicPoleGaussian
import Maxwell.Continuum.MasterConstants

/-! An explicit bound for the fully instantiated Gaussian remainder. The
large geometric radius cost remains below the symbolic master constant. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric MeasureTheory TransverseGaussian

attribute [local irreducible] imaginaryPole poleSlope transversePole selectedPoleAmplitude
  polePlanePhase poleGaussianHessian

theorem selectedGaussian_errorConstant {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    (selectedGaussianData D hh j).errorConstant ≤ (2 : ℝ)^4600 := by
  change ((2 : ℝ)^192 + ‖selectedPoleAmplitude D hh j 0‖ / poleGaussianRadius) *
      (2 * Real.pi / ((2 : ℝ)^(-256 : ℤ) * Real.sqrt ((2 : ℝ)^(-256 : ℤ)))) +
      ‖selectedPoleAmplitude D hh j 0‖ * (2 : ℝ)^246 *
      (32 * Real.pi / (((2 : ℝ)^(-256 : ℤ))^2 * Real.sqrt ((2 : ℝ)^(-256 : ℤ)))) ≤ _
  have ha := selectedPoleAmplitude_zero_bound D hh j
  have hsq : Real.sqrt ((2 : ℝ)^(-256 : ℤ)) = (2 : ℝ)^(-128 : ℤ) := by
    rw [show (2 : ℝ)^(-256 : ℤ) = ((2 : ℝ)^(-128 : ℤ))^2 by norm_num,
      Real.sqrt_sq (by positivity)]
  calc
    _ ≤ ((2 : ℝ)^192 + (2 : ℝ)^64 / poleGaussianRadius) *
        (2 * 4 / ((2 : ℝ)^(-256 : ℤ) * Real.sqrt ((2 : ℝ)^(-256 : ℤ)))) +
        (2 : ℝ)^64 * (2 : ℝ)^246 *
        (32 * 4 / (((2 : ℝ)^(-256 : ℤ))^2 * Real.sqrt ((2 : ℝ)^(-256 : ℤ)))) := by
      have hr := poleGaussianRadius_pos
      gcongr <;> first | exact ha | exact Real.pi_lt_four.le
    _ ≤ _ := by rw [hsq]; norm_num [poleGaussianRadius]

theorem selectedGaussian_asymptotic_bound {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {T : ℝ} (hT : 0 < T) :
    ‖selectedGaussianIntegral D hh j T - selectedPoleAmplitude D hh j 0 *
      ((2 * Real.pi * poleSlope D hh j /
        (T * Real.sqrt (poleGaussianHessian D hh j 0 * poleGaussianHessian D hh j 1)) : ℝ) : ℂ)‖ ≤
      (2 : ℝ)^4600 / (T * Real.sqrt T) :=
  (selectedGaussian_asymptotic D hh j hT).trans
    (div_le_div_of_nonneg_right (selectedGaussian_errorConstant D hh j) (by positivity))

theorem selectedGaussian_asymptotic_master {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {T : ℝ} (hT : 0 < T) :
    ‖selectedGaussianIntegral D hh j T - selectedPoleAmplitude D hh j 0 *
      ((2 * Real.pi * poleSlope D hh j /
        (T * Real.sqrt (poleGaussianHessian D hh j 0 * poleGaussianHessian D hh j 1)) : ℝ) : ℂ)‖ ≤
      MasterConstants.Cs / (T * Real.sqrt T) :=
  (selectedGaussian_asymptotic_bound D hh j hT).trans
    (div_le_div_of_nonneg_right
      (MasterConstants.fixed_power_le_Cs (by have := MasterConstants.exponent_large; omega)) (by positivity))

#print axioms selectedGaussian_asymptotic_master

end Maxwell.Continuum.PeriodicBand
