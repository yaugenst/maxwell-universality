import Maxwell.Continuum.AuxiliaryResolvent

/-! The actual full Maxwell fiber inverse is uniformly bounded away
from the corner. The denominator bound is derived from the proved
physical curvature and the calibrated real energy. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.Auxiliary

open FreeFiber PeriodicBand FiberAnalytic Bloch

attribute [local irreducible] fullResolventExtension dielectricBand

theorem highMomentum_denominator_lower {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (q : Corner.Vec)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    (hhigh : smallRadius/4 ≤ ‖(WithLp.toLp 2 q : Space)‖) :
    (1 : ℝ)/(2 : ℝ)^187 ≤ (dielectricBand (realMomentum q)).re - (z+σ) := by
  have hz : 0 ≤ centerEnergy - (z+σ) := by
    have he : realMomentum (0 : Corner.Vec) = 0 := by funext j; simp [realMomentum]
    have h0 : ‖realMomentum (0 : Corner.Vec)‖ ≤ 4*smallRadius := by
      rw [he, norm_zero]
      exact mul_nonneg (by norm_num) smallRadius_pos.le
    have hb := (calibration_denominator_bounds D hσ0 hσ 0 h0).1
    rw [he] at hb
    change h^2/2 ≤ centerEnergy-(z+σ) at hb
    exact (by positivity : (0 : ℝ) ≤ h^2/2).trans hb
  have hnorm : (smallRadius/4)^2 ≤ dotProduct q q := by
    have hs := (sq_le_sq₀ (div_nonneg smallRadius_pos.le (by norm_num)) (norm_nonneg _)).mpr hhigh
    have he : ‖(WithLp.toLp 2 q : Space)‖^2 = dotProduct q q := by
      rw [EuclideanSpace.norm_sq_eq]
      apply Finset.sum_congr rfl
      intro j _
      change ‖q j‖^2 = q j*q j
      rw [Real.norm_eq_abs, sq_abs, pow_two]
    rwa [he] at hs
  have hc := (physical_small_curvature q hq).1
  have hhess := (hessian_bounds q).1
  have hl := mul_le_mul_of_nonneg_left hnorm
    (show 0 ≤ (2*backgroundAmplitude)⁻¹ from
      inv_nonneg.mpr (mul_nonneg (by norm_num) backgroundAmplitude_pos.le))
  have hn : (1 : ℝ)/(2 : ℝ)^187 ≤
      (1/2 : ℝ) * ((2*backgroundAmplitude)⁻¹ * (smallRadius/4)^2) := by
    norm_num [backgroundAmplitude, smallRadius]
  change (1/2 : ℝ) * dotProduct q (hessian.mulVec q) ≤
    (dielectricBand (realMomentum q)).re - centerEnergy at hc
  nlinarith

theorem highMomentum_fiberResolvent_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (q : Corner.Vec)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    (hhigh : smallRadius/4 ≤ ‖(WithLp.toLp 2 q : Space)‖) :
    ‖fiberResolvent z σ q‖ ≤ (2 : ℝ)^188 := by
  have hn := fullResolventExtension_norm_le_real_band
    (fun j => q j / backgroundAmplitude)
    (e := sampledScaledEnergy z σ)
    (by rw [← fiberParameter_real]; exact fiberParameter_chart q hq)
    (by rw [← fiberParameter_real]; exact sampledScaledEnergy_mem D hσ0 hσ q hq)
    (by rw [← fiberParameter_real]; exact sampledScaledEnergy_ne_band D hσ0 hσ q hq)
  rw [← fiberParameter_real, sampledScaledEnergy, totalEnergy_scaledEnergy] at hn
  change ‖fiberResolvent z σ q‖ ≤ _ at hn
  have hd : (1 : ℝ)/(2 : ℝ)^187 ≤ ‖sampledEnergy z σ-physicalBand (fiberParameter q)‖ := by
    rw [sampledEnergy_band_distance D hσ0 hσ q hq]
    exact highMomentum_denominator_lower D hσ0 hσ q hq hhigh
  have hi : ‖sampledEnergy z σ-physicalBand (fiberParameter q)‖⁻¹ ≤ (2 : ℝ)^187 := by
    have hb := inv_anti₀ (by positivity : (0 : ℝ) < 1/(2 : ℝ)^187) hd
    simpa only [one_div, inv_inv] using hb
  have hnum : (2 : ℝ)^187+(2 : ℝ)^112 ≤ (2 : ℝ)^188 := by norm_num
  linarith

theorem highMomentum_cutoffFiber_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (q : QuasiCell)
    (hhigh : smallRadius/4 ≤ ‖q.val‖) : ‖cutoffFiber z σ q‖ ≤ (2 : ℝ)^188 := by
  by_cases hq : q ∈ cutoffRegion
  · rw [cutoffFiber_eq hq, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (cutoff_nonneg q.val)]
    have hq' : ‖realMomentum (fun j => q.val j)‖ ≤ 4 * smallRadius :=
      (show ‖quasiMomentum q‖ < 4 * smallRadius from hq).le
    exact (mul_le_mul_of_nonneg_right (cutoff_le_one q.val) (norm_nonneg _)).trans
      (by simpa only [one_mul] using highMomentum_fiberResolvent_norm_le D hσ0 hσ _ hq' hhigh)
  · rw [cutoffFiber_zero hq, norm_zero]
    positivity

#print axioms highMomentum_denominator_lower
#print axioms highMomentum_fiberResolvent_norm_le

end Maxwell.Continuum.Auxiliary
