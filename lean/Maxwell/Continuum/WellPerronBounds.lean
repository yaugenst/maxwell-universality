import Maxwell.Continuum.WellKernelRow

/-! A nonnegative pointwise representative and quantitative bounds for
the actual Perron eigenvector of the auxiliary scalar well. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.Well

open MeasureTheory

theorem absolute_topVector : absolute topVector = topVector := by
  apply Lp.ext
  filter_upwards [absolute_ae topVector, topVector_nonnegative] with x ha hu
  rw [ha, hu.1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.2]

def topProfile (x : Space) : ℝ := absoluteAction topVector x / mu

theorem topProfile_nonneg (x : Space) : 0 ≤ topProfile x :=
  div_nonneg (absoluteAction_nonneg _ _) mu_pos.le

theorem topVector_ae : topVector =ᵐ[volume] fun x => (topProfile x : ℂ) := by
  have ha := physicalBirmanSchwinger_absolute_ae topVector
  rw [absolute_topVector, topVector_eigen] at ha
  filter_upwards [ha, Lp.coeFn_smul (mu : ℂ) topVector] with x hx hs
  rw [hs] at hx
  change (mu : ℂ) * topVector x = (absoluteAction topVector x : ℂ) at hx
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr mu_pos.ne')
  rw [hx, topProfile, Complex.ofReal_div, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr mu_pos.ne')]

theorem topVector_norm_ae : (fun x => ‖topVector x‖) =ᵐ[volume] topProfile := by
  filter_upwards [topVector_ae] with x hx
  rw [hx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (topProfile_nonneg x)]

theorem topProfile_upper (x : Space) :
    topProfile x ≤ kernelRowBound / mu * qw x := by
  unfold topProfile
  apply (div_le_iff₀ mu_pos).mpr
  have h := absoluteAction_upper topVector x
  rw [topVector_norm, mul_one] at h
  convert h using 1
  field_simp [mu_pos.ne']

theorem topProfile_supported (x : Space) (hx : 1 ≤ ‖x‖) : topProfile x = 0 := by
  have h := topProfile_upper x
  rw [(qw_zero_iff x).mpr hx, mul_zero] at h
  exact le_antisymm h (topProfile_nonneg x)

theorem topProfile_square_integrable : Integrable (fun x => topProfile x ^ 2) := by
  have h := (Lp.memLp topVector).norm
  have hi := (memLp_two_iff_integrable_sq h.aestronglyMeasurable).mp h
  apply hi.congr
  filter_upwards [topVector_norm_ae] with x hx
  rw [hx]

theorem topProfile_square_integral : (∫ x, topProfile x ^ 2) = 1 := by
  have h := ScalarDielectric.scalar_norm_sq_eq_integral topVector
  rw [topVector_norm, one_pow] at h
  apply Eq.trans _ h.symm
  apply integral_congr_ae
  filter_upwards [topVector_norm_ae] with x hx
  rw [hx]

theorem topProfile_kernel_integrable (x : Space) :
    Integrable (fun y => wellKernel x y * topProfile y) :=
  (absoluteAction_integrable topVector x).congr (by
    filter_upwards [topVector_norm_ae] with y hy
    rw [hy])

theorem topProfile_eigen (x : Space) :
    mu * topProfile x = ∫ y : Space, wellKernel x y * topProfile y := by
  rw [topProfile, mul_div_cancel₀ _ mu_pos.ne']
  unfold absoluteAction
  apply integral_congr_ae
  filter_upwards [topVector_norm_ae] with y hy
  rw [hy]

def topOverlap : ℝ := ∫ x : Space, qw x * topProfile x

theorem topOverlap_integrable : Integrable (fun x => qw x * topProfile x) := by
  apply ((L2.integrable_inner (𝕜 := ℂ) rootVector topVector).re).congr
  filter_upwards [rootVector_ae, topVector_ae] with x hx hu
  rw [hx, hu]
  exact complex_inner_re_ofReal _ _

theorem topOverlap_nonneg : 0 ≤ topOverlap :=
  integral_nonneg (fun x => mul_nonneg (qw_nonneg x) (topProfile_nonneg x))

theorem topOverlap_lower : mu / kernelRowBound ≤ topOverlap := by
  have h : (∫ x, topProfile x ^ 2) ≤
      ∫ x, (kernelRowBound / mu) * (qw x * topProfile x) := by
    apply integral_mono topProfile_square_integrable (topOverlap_integrable.const_mul _)
    intro x
    have hm := mul_le_mul_of_nonneg_right (topProfile_upper x) (topProfile_nonneg x)
    dsimp only
    nlinarith
  rw [topProfile_square_integral, integral_const_mul] at h
  apply (div_le_iff₀ kernelRowBound_pos).mpr
  have hh : (1 : ℝ) ≤ (kernelRowBound * topOverlap) / mu := by
    convert h using 1
    unfold topOverlap
    ring
  have hm := (le_div_iff₀ mu_pos).mp hh
  nlinarith

theorem topProfile_lower_overlap (x : Space) :
    kernelFloor / mu * topOverlap * qw x ≤ topProfile x := by
  by_cases hx : ‖x‖ < 1
  · have h : (∫ y : Space, (kernelFloor * qw x) * (qw y * topProfile y)) ≤
        ∫ y : Space, wellKernel x y * topProfile y := by
      apply integral_mono_ae (topOverlap_integrable.const_mul _) (topProfile_kernel_integrable x)
      filter_upwards [volume.ae_ne x] with y hy
      by_cases hyball : ‖y‖ < 1
      · have hk := wellKernel_lower x y hx.le hyball.le (Ne.symm hy)
        have hm := mul_le_mul_of_nonneg_right hk (topProfile_nonneg y)
        unfold kernelFloor
        convert hm using 1
        ring
      · have hq : qw y = 0 := (qw_zero_iff y).mpr (le_of_not_gt hyball)
        simp only [hq, zero_mul, mul_zero]
        exact mul_nonneg (wellKernel_nonneg x y) (topProfile_nonneg y)
    rw [integral_const_mul, ← topProfile_eigen] at h
    apply (mul_le_mul_iff_right₀ mu_pos).mp
    unfold topOverlap
    convert h using 1
    field_simp [mu_pos.ne']
  · have hq : qw x = 0 := (qw_zero_iff x).mpr (le_of_not_gt hx)
    rw [hq, mul_zero]
    exact topProfile_nonneg x

theorem topProfile_lower (x : Space) :
    (1 / (2 : ℝ) ^ 29) * qw x ≤ topProfile x := by
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left topOverlap_lower (div_nonneg kernelFloor_pos.le mu_pos.le))
    (qw_nonneg x)
  apply le_trans _ (hm.trans (topProfile_lower_overlap x))
  have hρ := FreeFiber.backgroundAmplitude_pos.ne'
  apply le_of_eq
  unfold kernelFloor kernelRowBound
  field_simp [mu_pos.ne', hρ]
  ring

theorem topOverlap_lower_numeric : (1 / (2 : ℝ) ^ 32) ≤ topOverlap := by
  have h : (∫ x : Space, (1 / (2 : ℝ) ^ 29) * w x) ≤ topOverlap := by
    apply integral_mono (w_integrable.const_mul _) topOverlap_integrable
    intro x
    dsimp only
    have hm := mul_le_mul_of_nonneg_left (topProfile_lower x) (qw_nonneg x)
    rw [← qw_sq x]
    nlinarith
  rw [integral_const_mul] at h
  have hw := w_integral_lower
  nlinarith

theorem rootVector_norm_le : ‖rootVector‖ ≤ 3 := by
  have h := w_integral_upper
  rw [← rootVector_norm_sq] at h
  nlinarith [norm_nonneg rootVector]

theorem mu_upper : mu ≤ 256 * FreeFiber.backgroundAmplitude := by
  have h : ‖physicalBirmanSchwinger topVector‖ ≤ ‖(kernelRowBound : ℂ) • rootVector‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [physicalBirmanSchwinger_norm_pointwise topVector,
      Lp.coeFn_smul (kernelRowBound : ℂ) rootVector, rootVector_ae] with x hx hs hr
    rw [hs]
    change _ ≤ ‖(kernelRowBound : ℂ) • rootVector x‖
    rw [hr, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg kernelRowBound_pos.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (qw_nonneg x)]
    rw [topVector_norm, mul_one] at hx
    nlinarith
  rw [topVector_eigen, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg mu_pos.le, topVector_norm, mul_one, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg kernelRowBound_pos.le] at h
  have hu := mul_le_mul_of_nonneg_left rootVector_norm_le kernelRowBound_pos.le
  unfold kernelRowBound at h hu
  have hp := FreeFiber.backgroundAmplitude_pos
  linarith

end Maxwell.Continuum.Well
