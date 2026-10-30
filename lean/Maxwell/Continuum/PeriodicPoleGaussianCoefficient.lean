import Maxwell.Continuum.PeriodicPoleGaussianBound

/-! The positive leading coefficient after the actual longitudinal
residue factor. This fixes both its sign and its quantitative size. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric MeasureTheory TransverseGaussian

attribute [local irreducible] imaginaryPole poleSlope selectedPoleAmplitude
  selectedPoleNumerator poleGaussianHessian

def selectedGaussianCoefficient {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) : ℝ :=
  4 * Real.pi^2 * (selectedPoleNumerator D hh j 0).re /
    Real.sqrt (poleGaussianHessian D hh j 0 * poleGaussianHessian D hh j 1)

theorem selectedGaussian_determinant_pos {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    0 < Real.sqrt (poleGaussianHessian D hh j 0 * poleGaussianHessian D hh j 1) := by
  exact Real.sqrt_pos.mpr (mul_pos
    (lt_trans (by positivity) (poleGaussianHessian_bounds D hh j 0).1)
    (lt_trans (by positivity) (poleGaussianHessian_bounds D hh j 1).1))

theorem selectedGaussian_determinant_upper {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    Real.sqrt (poleGaussianHessian D hh j 0 * poleGaussianHessian D hh j 1) ≤ (2 : ℝ)^110 := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  simpa only [pow_two] using mul_le_mul
    (poleGaussianHessian_bounds D hh j 0).2.le (poleGaussianHessian_bounds D hh j 1).2.le
    (lt_trans (by positivity) (poleGaussianHessian_bounds D hh j 1).1).le (by positivity : (0 : ℝ) ≤ 2^110)

theorem selectedGaussianCoefficient_lower {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    1 / (2 : ℝ)^208 ≤ selectedGaussianCoefficient D hh j := by
  have hn := (selectedPoleNumerator_zero_positive D hh j).2
  have hn0 : 0 ≤ (selectedPoleNumerator D hh j 0).re := (by positivity : (0 : ℝ) ≤ 1 / 2^96).trans hn
  have hpi : 1 ≤ 4 * Real.pi^2 := by nlinarith only [Real.pi_gt_three]
  unfold selectedGaussianCoefficient
  apply (le_div_iff₀ (selectedGaussian_determinant_pos D hh j)).mpr
  calc
    _ ≤ 1 / (2 : ℝ)^208 * (2 : ℝ)^110 := mul_le_mul_of_nonneg_left
      (selectedGaussian_determinant_upper D hh j) (by positivity)
    _ ≤ 1 / (2 : ℝ)^96 := by norm_num
    _ ≤ (selectedPoleNumerator D hh j 0).re := hn
    _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hpi hn0

theorem selectedGaussian_residue_coefficient {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (T : ℝ) :
    (((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
      (selectedPoleAmplitude D hh j 0 *
        ((2 * Real.pi * poleSlope D hh j /
          (T * Real.sqrt (poleGaussianHessian D hh j 0 * poleGaussianHessian D hh j 1)) : ℝ) : ℂ)) =
      ((selectedGaussianCoefficient D hh j : ℝ) : ℂ) / (T : ℂ) := by
  have hn : selectedPoleNumerator D hh j 0 = ((selectedPoleNumerator D hh j 0).re : ℂ) := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · exact Complex.conj_eq_iff_im.mp (selectedPoleNumerator_zero_positive D hh j).1
  have hc : (poleSlope D hh j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (lt_trans (by norm_num : (0 : ℝ) < 1) (poleSlope_bounds D hh j).1).ne'
  rw [selectedPoleAmplitude_zero, hn]
  unfold selectedGaussianCoefficient
  push_cast
  by_cases hT : (T : ℂ) = 0
  · simp only [hT, zero_mul, div_zero, mul_zero]
  · have hQ : (Real.sqrt (poleGaussianHessian D hh j 0 * poleGaussianHessian D hh j 1) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (selectedGaussian_determinant_pos D hh j).ne'
    field_simp [hc, Complex.I_ne_zero, hT, hQ]
    ring

theorem selectedGaussian_residue_asymptotic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {T : ℝ} (hT : 0 < T) :
    ‖(((2 * Real.pi : ℝ) : ℂ) * Complex.I) * selectedGaussianIntegral D hh j T -
      ((selectedGaussianCoefficient D hh j : ℝ) : ℂ) / (T : ℂ)‖ ≤
      (2 : ℝ)^4603 / (T * Real.sqrt T) := by
  rw [← selectedGaussian_residue_coefficient D hh j T, ← mul_sub, norm_mul]
  have hf : ‖(((2 * Real.pi : ℝ) : ℂ) * Complex.I)‖ ≤ 8 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), Complex.norm_I, mul_one]
    linarith only [Real.pi_lt_four]
  calc
    _ ≤ 8 * ((2 : ℝ)^4600 / (T * Real.sqrt T)) :=
      mul_le_mul hf (selectedGaussian_asymptotic_bound D hh j hT) (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num; ring

#print axioms selectedGaussianCoefficient_lower
#print axioms selectedGaussian_residue_asymptotic

end Maxwell.Continuum.PeriodicBand
