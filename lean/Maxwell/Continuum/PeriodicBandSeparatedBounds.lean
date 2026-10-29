import Maxwell.Continuum.PeriodicBandProjectionAnalytic
import Mathlib.Analysis.Complex.AbsMax

/-! The paper's literal `2^112` bound for the complete separated inverse.
The maximum-modulus principle is applied to the actual operator-valued
analytic remainder, including its value at the band root. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber FiberAnalytic Metric Set

theorem centeredEnergyDisk_subset {t : Momentum} (ht : t ∈ chart) :
    closedBall (scaledBand t) (1 / 200) ⊆ energyDisk := by
  intro e he
  have hd : ‖e - scaledBand t‖ ≤ 1 / 200 := by
    simpa only [mem_closedBall, dist_eq_norm] using he
  have htri := norm_add_le (e - scaledBand t) (scaledBand t - (Corner.lambdaStar : ℂ))
  rw [sub_add_sub_cancel] at htri
  change e ∈ closedBall (Corner.lambdaStar : ℂ) (1 / 100)
  rw [mem_closedBall, dist_eq_norm]
  linarith [scaledBand_center_bound ht]

theorem fullSeparatedResolvent_eq_sub_pole {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) (hne : e ≠ scaledBand t) :
    fullSeparatedResolvent t e = fullResolventExtension (t, e) -
      ((backgroundAmplitude : ℂ) * (e - scaledBand t))⁻¹ • fullPoleResidue t := by
  rw [fullResolvent_pole_formula ht he hne]
  abel

theorem fullPoleResidue_norm_le {t : Momentum} (ht : t ∈ chart) :
    ‖fullPoleResidue t‖ ≤ 81 / 25 := by
  have h := fullSpectralProjection_norm_le ht
  change ‖-fullPoleResidue t‖ ≤ _ at h
  rwa [norm_neg] at h

theorem fullSeparatedResolvent_norm_sphere {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ sphere (scaledBand t) (1 / 200)) :
    ‖fullSeparatedResolvent t e‖ ≤ (2 : ℝ) ^ 112 := by
  have hd : ‖e - scaledBand t‖ = 1 / 200 := by
    simpa only [mem_sphere, dist_eq_norm] using he
  have hne : e ≠ scaledBand t := by
    intro hz
    rw [hz, sub_self, norm_zero] at hd
    norm_num at hd
  have hmem := centeredEnergyDisk_subset ht (sphere_subset_closedBall he)
  have hR := fullResolventExtension_norm_le_band ht hmem hne
  rw [hd] at hR
  have hP : ‖((backgroundAmplitude : ℂ) * (e - scaledBand t))⁻¹ • fullPoleResidue t‖ ≤
      800 * backgroundAmplitude⁻¹ := by
    rw [norm_smul, norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos backgroundAmplitude_pos, hd, mul_inv_rev]
    have h := mul_le_mul_of_nonneg_left ((fullPoleResidue_norm_le ht).trans
      (show (81 : ℝ) / 25 ≤ 4 by norm_num))
      (mul_nonneg (inv_nonneg.mpr (show (0 : ℝ) ≤ 1 / 200 by norm_num))
        (inv_nonneg.mpr backgroundAmplitude_pos.le))
    norm_num at h ⊢
    nlinarith
  rw [fullSeparatedResolvent_eq_sub_pole ht hmem hne]
  have htri := norm_sub_le (fullResolventExtension (t, e))
    (((backgroundAmplitude : ℂ) * (e - scaledBand t))⁻¹ • fullPoleResidue t)
  have hconst : 2 + 3360 * backgroundAmplitude⁻¹ ≤ (2 : ℝ) ^ 112 := by
    norm_num [backgroundAmplitude]
  norm_num at hR
  linarith

/-- Uniform bound on a complex neighborhood of the entire momentum chart. -/
theorem fullSeparatedResolvent_norm_le {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ closedBall (scaledBand t) (1 / 200)) :
    ‖fullSeparatedResolvent t e‖ ≤ (2 : ℝ) ^ 112 := by
  have ha : AnalyticOnNhd ℂ (fullSeparatedResolvent t) (closedBall (scaledBand t) (1 / 200)) :=
    fun f hf => analyticAt_fullSeparatedResolvent ht (centeredEnergyDisk_subset ht hf)
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := ball (scaledBand t) (1 / 200)) isBounded_ball
    (ha.differentiableOn.diffContOnCl_ball subset_rfl)
  · intro f hf
    exact fullSeparatedResolvent_norm_sphere ht (frontier_ball_subset_sphere hf)
  · rw [closure_ball (scaledBand t) (by norm_num : (1 : ℝ) / 200 ≠ 0)]
    exact he

end Maxwell.Continuum.PeriodicBand
