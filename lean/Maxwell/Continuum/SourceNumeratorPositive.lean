import Maxwell.Continuum.SourceNumeratorFrozenLower
import Maxwell.Continuum.EffectiveMassRealMode

/-! Quantitative nonvanishing of the actual real continuum source at
imaginary physical momentum. The errors are discharged by the actual
mode and full Fourier cell variation estimates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace Maxwell.Continuum.EffectiveMass

open Auxiliary FreeFiber PeriodicBand

attribute [local irreducible] realMode referencePhysicalMode sourceFactor sourceFrozenFactor

theorem numerator_lower_from_errors {t h : ℝ} {a b c : ℂ} (ht : 0 ≤ t)
    (hsmall : h ≤ 1 / (2 : ℝ)^1024)
    (hb : 1 / (2 : ℝ)^40 ≤ t * c.re)
    (h₁ : t * ‖a-b‖ ≤ (2 : ℝ)^930 * h)
    (h₂ : t * ‖b-c‖ ≤ (2 : ℝ)^133 * h) :
    1 / (2 : ℝ)^48 ≤ t * a.re := by
  have he : t * ‖a-c‖ ≤ 1 / (2 : ℝ)^41 := by
    have htri := mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub a b c) ht
    rw [mul_add] at htri
    apply (htri.trans (add_le_add h₁ h₂)).trans
    have hs := mul_le_mul_of_nonneg_left hsmall
      (add_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) 930)
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) 133))
    rw [add_mul] at hs
    exact hs.trans (by norm_num)
  have hr := mul_le_mul_of_nonneg_left (Complex.re_le_norm (c-a)) ht
  rw [Complex.sub_re, norm_sub_rev c a] at hr
  norm_num at hb he ⊢
  nlinarith only [hb, he, hr]

theorem imaginaryMomentum_norm_le (β : Space) :
    ‖Complex.I • physicalMomentum β‖ ≤ ‖β‖ := by
  rw [norm_smul, Complex.norm_I, one_mul]
  exact physicalMomentum_norm_le β

theorem imaginaryMomentum_small {h : ℝ} (hsmall : h ≤ 1 / (2 : ℝ)^1024)
    {β : Space} (hβ : ‖β‖ ≤ h) :
    ‖Complex.I • physicalMomentum β‖ ≤ analyticRadius / 4 :=
  (imaginaryMomentum_norm_le β).trans (hβ.trans
    (hsmall.trans (by norm_num [analyticRadius, backgroundAmplitude])))

theorem imaginaryMomentum_chart {h : ℝ} (hsmall : h ≤ 1 / (2 : ℝ)^1024)
    {β : Space} (hβ : ‖β‖ ≤ h) : Complex.I • physicalMomentum β ∈ physicalChart := by
  intro j
  exact (norm_le_pi_norm _ j).trans_lt ((imaginaryMomentum_small hsmall hβ).trans_lt
    (by linarith only [analyticRadius_pos]))

theorem sourceFactor_realMode_lower {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) {β : Space} (hβ : ‖β‖ ≤ h) :
    1 / (2 : ℝ)^48 ≤ sourceScale h *
      (sourceFactor h (realMode D hh) (Complex.I • physicalMomentum β)).re := by
  have hq := imaginaryMomentum_chart hh hβ
  have hi : ‖sourceImaginary (Complex.I • physicalMomentum β)‖ ≤ h := by
    rwa [sourceImaginary_imaginary]
  have h₁ : sourceScale h * ‖sourceFactor h (realMode D hh) (Complex.I • physicalMomentum β) -
      sourceFactor h (referencePhysicalMode D.h_pos) (Complex.I • physicalMomentum β)‖ ≤
      (2 : ℝ)^930 * h := by
    apply (sourceFactor_scaled_sub_le D.h_pos _ _ hq hi).trans
    have he := mul_le_mul_of_nonneg_left (realMode_spatial_error D hh) (by norm_num : (0 : ℝ) ≤ 512)
    convert he using 1
    ring
  have h₂ : sourceScale h * ‖sourceFactor h (referencePhysicalMode D.h_pos)
      (Complex.I • physicalMomentum β) - sourceFrozenFactor h (referencePhysicalMode D.h_pos)
        (Complex.I • physicalMomentum β)‖ ≤ (2 : ℝ)^133 * h := by
    apply (sourceFactor_frozen_sub_le D.h_pos _ (imaginaryMomentum_small hh hβ) hi).trans
    have hnorm := (imaginaryMomentum_norm_le β).trans hβ
    have hm := mul_le_mul_of_nonneg_left hnorm
      (div_nonneg (by norm_num : (0 : ℝ) ≤ 128) analyticRadius_pos.le)
    have hmp := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 12)
    have he := mul_le_mul hmp (referencePhysicalMode_norm_le D.h_pos) (norm_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12)
        (mul_nonneg (div_nonneg (by norm_num) analyticRadius_pos.le) D.h_pos.le))
    apply he.trans
    have hc : 12 * (128 / analyticRadius) * 32 ≤ (2 : ℝ)^133 := by
      norm_num [analyticRadius, backgroundAmplitude]
    have h := mul_le_mul_of_nonneg_right hc D.h_pos.le
    convert h using 1
    ring
  exact numerator_lower_from_errors (sourceScale_pos D.h_pos).le hh
    (sourceFrozenFactor_reference_lower D.h_pos hh hβ) h₁ h₂

theorem imaginaryMomentum_star (β : Space) :
    star (Complex.I • physicalMomentum β) = -(Complex.I • physicalMomentum β) := by
  funext j
  change star (Complex.I * (β j : ℂ)) = -(Complex.I * (β j : ℂ))
  simp

theorem sourceFactor_realMode_real {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) {β : Space} (hβ : ‖β‖ ≤ h) :
    star (sourceFactor h (realMode D hh) (Complex.I • physicalMomentum β)) =
      sourceFactor h (realMode D hh) (Complex.I • physicalMomentum β) :=
  sourceFactor_real (realMode_real D hh) (imaginaryMomentum_chart hh hβ) (imaginaryMomentum_star β)

end Maxwell.Continuum.EffectiveMass
