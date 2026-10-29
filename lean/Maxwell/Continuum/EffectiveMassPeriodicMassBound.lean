import Maxwell.Continuum.EffectiveMassPeriodicMass
import Maxwell.Continuum.AliasDecayMajorant

/-! Quantitative averaging of the actual periodic mode against the well.
The bound uses the full alias sum, not a finite Fourier approximation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber PeriodicBand

theorem fourierNormalization_nonneg : 0 ≤ fourierNormalization := by
  unfold fourierNormalization
  positivity

theorem fourierNormalization_lower : (1 / 32 : ℝ) ≤ fourierNormalization := by
  have hp : (2 * Real.pi)^3 ≤ (1024 : ℝ) := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * Real.pi)
      (show 2 * Real.pi ≤ 8 by linarith [Real.pi_lt_four]) 3
    norm_num at h
    linarith
  have hs : (1 / 1024 : ℝ) ≤ fourierNormalization^2 := by
    rw [fourierNormalization_square]
    simpa only [angularDensity, one_div] using one_div_le_one_div_of_le (by positivity) hp
  nlinarith [fourierNormalization_nonneg]

theorem offAliasKernel_zero_error {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    ‖offAliasKernel h 0 0‖ ≤ (2 : ℝ)^512 * h := by
  have hz : h * ‖(0 : Space)‖ ≤ 4 * smallRadius := by
    simpa only [norm_zero, mul_zero] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) smallRadius_pos.le
  have hi : 1 ≤ h⁻¹ := (one_le_inv₀ hh).mpr hh1
  have hip : 1 ≤ (h⁻¹)^3 := one_le_pow₀ hi
  calc
    _ ≤ (2 : ℝ)^30 * Real.exp (-1 / (512 * Real.sqrt h)) :=
      offAliasKernel_bound hh 0 0 hz hz
    _ ≤ (2 : ℝ)^100 * (h⁻¹)^3 * Real.exp (-1 / (512 * Real.sqrt h)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      have hp : (2 : ℝ)^30 ≤ (2 : ℝ)^100 := by norm_num
      nlinarith
    _ ≤ _ := alias_decay_majorant hh

theorem periodicWellMass_error {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    |periodicWellMass h - ∫ x : Space, Well.w x| ≤ (2 : ℝ)^517 * h := by
  have he := congrArg norm (periodicWellMass_alias_identity hh)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg fourierNormalization_nonneg] at he
  have hm := mul_le_mul_of_nonneg_right fourierNormalization_lower
    (abs_nonneg (periodicWellMass h - ∫ x : Space, Well.w x))
  rw [he] at hm
  have ht := hm.trans (offAliasKernel_zero_error hh hh1)
  have hp : (2 : ℝ)^517 = 32 * (2 : ℝ)^512 := by
    rw [show 517 = 512 + 5 from rfl, pow_add]
    ring
  rw [hp]
  linarith

theorem periodicWellMass_lower {h : ℝ} (hh : 0 < h) (hsmall : h ≤ 1 / (2 : ℝ)^1024) :
    (1 / 16 : ℝ) ≤ periodicWellMass h := by
  have hh1 : h ≤ 1 := hsmall.trans (by
    rw [one_div]
    exact (inv_le_one₀ (by positivity)).mpr (one_le_pow₀ (by norm_num)))
  have he := periodicWellMass_error hh hh1
  have he' := (abs_le.mp he).1
  have hc : (2 : ℝ)^517 * (1 / (2 : ℝ)^1024) ≤ 1 / 16 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
    have he : ((2 : ℝ)^517 * (1 / (2 : ℝ)^1024)) * 16 = (2 : ℝ)^521 / (2 : ℝ)^1024 := by
      rw [show 521 = 517 + 4 from rfl, pow_add]
      ring
    rw [he]
    exact (div_le_one (by positivity)).mpr (pow_le_pow_right₀ (by norm_num) (by omega))
  have hs := (mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ (2 : ℝ)^517)).trans hc
  have hw := Well.w_integral_lower
  linarith

end Maxwell.Continuum.EffectiveMass
