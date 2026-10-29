import Maxwell.Continuum.PeriodicTransverseHessian
import Maxwell.Continuum.PeriodicPoleSlope
import Maxwell.Continuum.AnalyticBallBounds

/-! The actual rescaled selected-band denominator centered at its constructed
imaginary pole. Its analytic neighborhood and uniform bound are independent
of the inverse length. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric

attribute [local irreducible] dielectricBand hessian imaginaryPole physicalQuadratic

theorem physicalQuadratic_norm (q : Momentum) :
    ‖physicalQuadratic q‖ ≤ (2 : ℝ) ^ 110 * ‖q‖ ^ 2 := by
  rw [physicalQuadratic_diagonal]
  calc
    _ ≤ ∑ j : Fin 3, ‖(hessian j j : ℂ) * q j ^ 2‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, (256 / backgroundAmplitude) * ‖q‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hessian_diagonal_positive j)]
      exact mul_le_mul (hessian_diagonal_bounds j).2
        (pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm q j) 2)
        (by positivity) (div_nonneg (by norm_num) backgroundAmplitude_pos.le)
    _ = (3 * (256 / backgroundAmplitude)) * ‖q‖ ^ 2 := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num [backgroundAmplitude]) (sq_nonneg _)

def poleCenter {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1 / (2 : ℝ) ^ 1024)
    (j : Fin 3) : Momentum := ((imaginaryPole D hh j : ℂ) * Complex.I) • basisVector j

def poleMomentum {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1 / (2 : ℝ) ^ 1024)
    (j : Fin 3) (k : Momentum) : Momentum := poleCenter D hh j + (h : ℂ) • k

def poleDenominator {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1 / (2 : ℝ) ^ 1024)
    (j : Fin 3) (k : Momentum) : ℂ :=
  ((h : ℂ) ^ 2)⁻¹ * (dielectricBand (poleMomentum D hh j k) - (z : ℂ))

theorem poleCenter_norm {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ) ^ 1024) (j : Fin 3) :
    ‖poleCenter D hh j‖ = imaginaryPole D hh j := by
  simp only [poleCenter, norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, basisVector_norm, mul_one, abs_of_pos (imaginaryPole_pos D hh j)]

theorem poleMomentum_norm_le {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ) ^ 1024) (j : Fin 3) (k : Momentum) :
    ‖poleMomentum D hh j k‖ ≤ h * (1 + ‖k‖) := by
  unfold poleMomentum
  calc
    _ ≤ ‖poleCenter D hh j‖ + ‖(h : ℂ) • k‖ := norm_add_le _ _
    _ = imaginaryPole D hh j + h * ‖k‖ := by
      rw [poleCenter_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos D.h_pos]
    _ ≤ _ := by nlinarith only [imaginaryPole_le_inverse_scale D hh j]

theorem poleMomentum_mem_chart {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ) ^ 1024) (j : Fin 3) {k : Momentum} (hk : ‖k‖ ≤ 1) :
    poleMomentum D hh j k ∈ physicalChart := by
  have hnorm : ‖poleMomentum D hh j k‖ ≤ 2 * h :=
    (poleMomentum_norm_le D hh j k).trans (by nlinarith only [mul_le_mul_of_nonneg_left hk D.h_pos.le])
  intro i
  exact (norm_le_pi_norm _ i).trans_lt (hnorm.trans_lt
    ((imaginary_scale_bounds D.h_pos.le hh).1.trans_lt (by linarith only [analyticRadius_pos])))

theorem poleDenominator_analytic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ) ^ 1024) (j : Fin 3) :
    AnalyticOnNhd ℂ (poleDenominator D hh j) (ball 0 1) := by
  intro k hk
  have hq := poleMomentum_mem_chart D hh j (le_of_lt (by simpa only [mem_ball, dist_zero_right] using hk))
  have hm : AnalyticAt ℂ (poleMomentum D hh j) k := by
    unfold poleMomentum
    exact analyticAt_const.add (analyticAt_id.const_smul (c := (h : ℂ)))
  exact analyticAt_const.mul ((AnalyticAt.comp (f := poleMomentum D hh j)
    (dielectricBand_analytic _ hq) hm).sub analyticAt_const)

theorem poleDenominator_zero {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ) ^ 1024) (j : Fin 3) : poleDenominator D hh j 0 = 0 := by
  simp only [poleDenominator, poleMomentum, smul_zero, add_zero, poleCenter,
    imaginaryPole_equation, sub_self, mul_zero]

theorem poleDenominator_bound {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ) ^ 1024) (j : Fin 3) {k : Momentum} (hk : ‖k‖ ≤ 1) :
    ‖poleDenominator D hh j k‖ ≤ (2 : ℝ) ^ 120 := by
  let q := poleMomentum D hh j k
  let q₀ := poleCenter D hh j
  have hq : ‖q‖ ≤ 2 * h := (poleMomentum_norm_le D hh j k).trans
    (by nlinarith only [mul_le_mul_of_nonneg_left hk D.h_pos.le])
  have hq₀ : ‖q₀‖ ≤ h := (poleCenter_norm D hh j).le.trans (imaginaryPole_le_inverse_scale D hh j)
  have hs := imaginary_scale_bounds D.h_pos.le hh
  have he₁ := physical_quartic (hq.trans (by linarith only [hs.1, analyticRadius_pos]))
  have he₀ := physical_quartic (hq₀.trans (by linarith only [hs.1, D.h_pos, analyticRadius_pos]))
  have hroot : dielectricBand q₀ = (z : ℂ) := imaginaryPole_equation D hh j
  have hdecomp : dielectricBand q - (z : ℂ) =
      (dielectricBand q - dielectricBand 0 - physicalQuadratic q) -
      (dielectricBand q₀ - dielectricBand 0 - physicalQuadratic q₀) +
      physicalQuadratic q - physicalQuadratic q₀ := by rw [hroot]; ring
  have hnorm : ‖dielectricBand q - (z : ℂ)‖ ≤
      quarticConstant * (2 * h) ^ 4 + quarticConstant * h ^ 4 +
        (2 : ℝ) ^ 110 * (2 * h) ^ 2 + (2 : ℝ) ^ 110 * h ^ 2 := by
    rw [hdecomp]
    calc
      _ ≤ (‖dielectricBand q - dielectricBand 0 - physicalQuadratic q‖ +
          ‖dielectricBand q₀ - dielectricBand 0 - physicalQuadratic q₀‖) +
          ‖physicalQuadratic q‖ + ‖physicalQuadratic q₀‖ :=
        (norm_sub_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
      _ ≤ _ := by
        apply add_le_add
        · apply add_le_add
          · exact add_le_add
              (he₁.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hq 4)
                quarticConstant_nonneg))
              (he₀.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hq₀ 4)
                quarticConstant_nonneg))
          · exact (physicalQuadratic_norm q).trans
              (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hq 2) (by positivity))
        · exact (physicalQuadratic_norm q₀).trans
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hq₀ 2) (by positivity))
  have hpoly : quarticConstant * (2 * h) ^ 4 + quarticConstant * h ^ 4 ≤ h ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hs.2.2.1 (sq_nonneg h)
    nlinarith only [hm, sq_nonneg h]
  have ht : ‖dielectricBand q - (z : ℂ)‖ ≤ (2 : ℝ) ^ 120 * h ^ 2 := by
    have hn : 5 * (2 : ℝ) ^ 110 + 1 ≤ (2 : ℝ) ^ 120 := by norm_num
    have hm := mul_le_mul_of_nonneg_right hn (sq_nonneg h)
    nlinarith only [hnorm, hpoly, hm]
  change ‖((h : ℂ) ^ 2)⁻¹ * (dielectricBand q - (z : ℂ))‖ ≤ _
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos D.h_pos]
  exact (mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr (sq_nonneg h))).trans_eq
    (by field_simp [D.h_pos.ne'])

end Maxwell.Continuum.PeriodicBand
