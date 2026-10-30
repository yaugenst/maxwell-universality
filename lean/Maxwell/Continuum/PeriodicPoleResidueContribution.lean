import Maxwell.Continuum.PeriodicPoleGaussianCoefficient
import Maxwell.Continuum.PeriodicPoleAction

/-! The actual local pole-residue contribution in a literal placement
direction. This is the residue contribution; identification with the full
selected resolvent additionally uses the longitudinal contour identity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric MeasureTheory TransverseGaussian

attribute [local irreducible] imaginaryPole poleSlope selectedPoleAmplitude
  selectedPoleNumerator poleGaussianHessian selectedGaussianCoefficient poleAction

theorem placementDiagonal_residue_bounds (j : Fin 3) :
    1 ≤ 2 * (placementDiagonal j : ℝ) ∧ 2 * (placementDiagonal j : ℝ) ≤ (2 : ℝ)^54 := by
  fin_cases j <;> norm_num [placementDiagonal]

def selectedLeadingCoefficient {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) : ℝ :=
  selectedGaussianCoefficient D hh j / (2 * (placementDiagonal j : ℝ))

theorem selectedLeadingCoefficient_lower {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    1 / (2 : ℝ)^262 ≤ selectedLeadingCoefficient D hh j := by
  have hB := placementDiagonal_pos j
  unfold selectedLeadingCoefficient
  apply (le_div_iff₀ (by positivity : 0 < 2 * (placementDiagonal j : ℝ))).mpr
  calc
    _ ≤ 1 / (2 : ℝ)^262 * (2 : ℝ)^54 := mul_le_mul_of_nonneg_left
      (placementDiagonal_residue_bounds j).2 (by positivity)
    _ = 1 / (2 : ℝ)^208 := by norm_num
    _ ≤ _ := selectedGaussianCoefficient_lower D hh j

theorem selectedLeadingCoefficient_paper_lower {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    1 / (2 : ℝ)^512 ≤ selectedLeadingCoefficient D hh j :=
  (by norm_num : (1 : ℝ) / 2^512 ≤ 1 / 2^262).trans (selectedLeadingCoefficient_lower D hh j)

def selectedPoleResidueContribution {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (d : ℝ) : ℂ :=
  (Real.exp (-poleAction D hh j * d) : ℂ) *
    ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
      selectedGaussianIntegral D hh j (2 * (placementDiagonal j : ℝ) * d))

theorem selectedPoleResidueContribution_asymptotic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {d : ℝ} (hd : 0 < d) :
    ‖selectedPoleResidueContribution D hh j d -
      (Real.exp (-poleAction D hh j * d) : ℂ) * ((selectedLeadingCoefficient D hh j / d : ℝ) : ℂ)‖ ≤
      (2 : ℝ)^4603 * Real.exp (-poleAction D hh j * d) / (d * Real.sqrt d) := by
  let T : ℝ := 2 * (placementDiagonal j : ℝ) * d
  have hTd : d ≤ T := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (placementDiagonal_residue_bounds j).1 hd.le
  have hT : 0 < T := hd.trans_le hTd
  have he := selectedGaussian_residue_asymptotic D hh j hT
  have hc : ((selectedGaussianCoefficient D hh j : ℝ) : ℂ) / (T : ℂ) =
      ((selectedLeadingCoefficient D hh j / d : ℝ) : ℂ) := by
    unfold selectedLeadingCoefficient
    dsimp only [T]
    push_cast
    ring
  rw [hc] at he
  unfold selectedPoleResidueContribution
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hden : d * Real.sqrt d ≤ T * Real.sqrt T :=
    mul_le_mul hTd (Real.sqrt_le_sqrt hTd) (Real.sqrt_nonneg d) hT.le
  calc
    _ ≤ Real.exp (-poleAction D hh j * d) * ((2 : ℝ)^4603 / (T * Real.sqrt T)) :=
      mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
    _ ≤ Real.exp (-poleAction D hh j * d) * ((2 : ℝ)^4603 / (d * Real.sqrt d)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) (by positivity) hden) (Real.exp_pos _).le
    _ = _ := by ring

#print axioms selectedLeadingCoefficient_paper_lower
#print axioms selectedPoleResidueContribution_asymptotic

end Maxwell.Continuum.PeriodicBand
