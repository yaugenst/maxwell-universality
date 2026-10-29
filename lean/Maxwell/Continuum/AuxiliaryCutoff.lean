import Maxwell.Continuum.AuxiliaryEnergy
import Maxwell.Continuum.WellCutoff

/-! The literal smooth cutoff at the certified small-band scale. -/

noncomputable section

namespace Maxwell.Continuum.Auxiliary

open FreeFiber PeriodicBand

def cutoff (q : Space) : ℝ := Well.chi smallRadius q

theorem cutoff_nonneg (q : Space) : 0 ≤ cutoff q := Well.chi_nonneg _ _

theorem cutoff_le_one (q : Space) : cutoff q ≤ 1 := Well.chi_le_one _ _

theorem cutoff_continuous : Continuous cutoff := (Well.chi_contDiff smallRadius).continuous

theorem cutoff_ne_zero_coordinate_lt {q : Space} (hq : cutoff q ≠ 0) (j : Fin 3) :
    |q j| < 2 * smallRadius := by
  have hr : |q j / smallRadius| < 2 := by
    by_contra h
    exact hq (Well.chi_eq_zero smallRadius q j (le_of_not_gt h))
  rw [abs_div, abs_of_pos smallRadius_pos] at hr
  exact (div_lt_iff₀ smallRadius_pos).mp hr

theorem cutoff_ne_zero_sup_le {q : Space} (hq : cutoff q ≠ 0) :
    ‖realMomentum (fun j => q j)‖ ≤ 2 * smallRadius := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) smallRadius_pos.le)).mpr
  intro j
  simpa only [realMomentum, Complex.norm_real, Real.norm_eq_abs] using
    (cutoff_ne_zero_coordinate_lt hq j).le

/-- The support of the actual product cutoff lies in the Euclidean
radius used in the quartic remainder bound. -/
theorem cutoff_ne_zero_norm_le {q : Space} (hq : cutoff q ≠ 0) :
    ‖q‖ ≤ 4 * smallRadius := by
  have hc (j : Fin 3) : ‖q j‖ ^ 2 ≤ (2 * smallRadius)^2 := by
    have hj := cutoff_ne_zero_coordinate_lt hq j
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (q j), smallRadius_pos]
  have hs : ‖q‖ ^ 2 ≤ 3 * (2 * smallRadius)^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Fin.sum_univ_three]
    linarith [hc 0, hc 1, hc 2]
  nlinarith [norm_nonneg q, smallRadius_pos]

theorem cutoff_eq_one_of_norm_le {q : Space} (hq : ‖q‖ ≤ smallRadius) : cutoff q = 1 := by
  apply Well.chi_eq_one
  intro j
  rw [abs_div, abs_of_pos smallRadius_pos]
  apply (div_le_one smallRadius_pos).mpr
  simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le q j).trans hq

theorem cutoff_eq_zero_outside {q : Space}
    (hq : ¬ ‖realMomentum (fun j => q j)‖ < 4 * smallRadius) : cutoff q = 0 := by
  by_contra hne
  exact hq (lt_of_le_of_lt (cutoff_ne_zero_sup_le hne) (by linarith [smallRadius_pos]))

end Maxwell.Continuum.Auxiliary
