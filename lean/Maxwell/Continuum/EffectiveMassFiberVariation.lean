import Maxwell.Continuum.EffectiveMassCutoffMultiplier
import Maxwell.Continuum.PhysicalFiberVariation

/-! The effective-mass comparison for the actual complete Fourier mode,
including its change with momentum and the cutoff multiplier. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open FreeFiber PeriodicBand Auxiliary

def scaledFiber (h : ℝ) (p : Space) : FiberSpace :=
  physicalFiberVector (physicalMomentum (h • p))

theorem four_smallRadius_le_quarter : 4 * smallRadius ≤ analyticRadius / 4 := by
  have hρ := backgroundAmplitude_pos
  unfold smallRadius analyticRadius
  have h := mul_le_mul_of_nonneg_left
    (by norm_num : 4 * ((2 : ℝ)^40)⁻¹ ≤ ((2 : ℝ)^12)⁻¹ / 4) hρ.le
  nlinarith

theorem scaledFiber_weighted_variation {h z : ℝ} (D : Calibration h z)
    (p : Space) (hp : h * ‖p‖ ≤ 4 * smallRadius) :
    referenceMultiplier p * ‖scaledFiber h p - physicalFiberVector 0‖ ≤ (2 : ℝ)^66 * h := by
  have hnorm : ‖physicalMomentum (h • p)‖ ≤ h * ‖p‖ := by
    simpa only [scaled_norm D.h_pos.le] using physicalMomentum_norm_le (h • p)
  have hv := physicalFiberVector_sub_zero (hnorm.trans (hp.trans four_smallRadius_le_quarter))
  have hC : 0 ≤ 8 / analyticRadius := div_nonneg (by norm_num) analyticRadius_pos.le
  have heq : (8 / analyticRadius) * ((2 : ℝ)^49)⁻¹ = (2 : ℝ)^66 := by
    norm_num [analyticRadius, backgroundAmplitude]
  calc
    _ ≤ referenceMultiplier p * ((8 / analyticRadius) * ‖physicalMomentum (h • p)‖) :=
      mul_le_mul_of_nonneg_left hv (referenceMultiplier_nonneg p)
    _ ≤ referenceMultiplier p * ((8 / analyticRadius) * (h * ‖p‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnorm hC)
        (referenceMultiplier_nonneg p)
    _ = h * (8 / analyticRadius) * (‖p‖ * referenceMultiplier p) := by ring
    _ ≤ h * (8 / analyticRadius) * ((2 : ℝ)^49)⁻¹ :=
      mul_le_mul_of_nonneg_left (referenceMultiplier_weighted p) (mul_nonneg D.h_pos.le hC)
    _ = (2 : ℝ)^66 * h := by rw [mul_assoc, heq]; ring

theorem scaledFiber_norm_le {h : ℝ} (hh : 0 ≤ h) (p : Space)
    (hp : h * ‖p‖ ≤ 4 * smallRadius) : ‖scaledFiber h p‖ ≤ 2 := by
  apply physicalFiberVector_norm_le
  apply small_momentum_mem_physicalChart
  have hnorm := physicalMomentum_norm_le (h • p)
  rw [scaled_norm hh] at hnorm
  exact hnorm.trans hp

theorem physicalFiberVector_zero_norm_le : ‖physicalFiberVector 0‖ ≤ 2 :=
  physicalFiberVector_norm_le (by intro j; simpa using analyticRadius_pos)

def vectorMultiplier (h z : ℝ) (p : Space) : FiberSpace :=
  (cutoffBandMultiplier h z p : ℂ) • scaledFiber h p

def referenceVectorMultiplier (p : Space) : FiberSpace :=
  (referenceMultiplier p : ℂ) • physicalFiberVector 0

theorem vectorMultiplier_error {h z : ℝ} (D : Calibration h z) (p : Space) :
    ‖vectorMultiplier h z p - referenceVectorMultiplier p‖ ≤ (2 : ℝ)^130 * h := by
  have hh := D.h_pos
  by_cases hc : cutoff (h • p) = 0
  · have ht := referenceMultiplier_tail D p (by rw [hc]; norm_num)
    have hz : cutoffBandMultiplier h z p = 0 := by
      simp only [cutoffBandMultiplier, hc, Real.sqrt_zero, zero_mul]
    simp only [vectorMultiplier, referenceVectorMultiplier, hz, Complex.ofReal_zero,
      zero_smul, zero_sub, norm_neg, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (referenceMultiplier_nonneg p)]
    have hm := mul_le_mul ht physicalFiberVector_zero_norm_le (norm_nonneg _) (by positivity)
    nlinarith
  have hp := cutoff_ne_zero_norm_le hc
  rw [scaled_norm D.h_pos.le] at hp
  have hv := scaledFiber_weighted_variation D p hp
  have hs := cutoffBandMultiplier_error D p
  have hn := scaledFiber_norm_le D.h_pos.le p hp
  have hid : vectorMultiplier h z p - referenceVectorMultiplier p =
      ((cutoffBandMultiplier h z p - referenceMultiplier p : ℝ) : ℂ) • scaledFiber h p +
        (referenceMultiplier p : ℂ) • (scaledFiber h p - physicalFiberVector 0) := by
    simp only [vectorMultiplier, referenceVectorMultiplier, Complex.ofReal_sub, sub_smul, smul_sub]
    abel
  rw [hid]
  calc
    _ ≤ ‖((cutoffBandMultiplier h z p - referenceMultiplier p : ℝ) : ℂ) • scaledFiber h p‖ +
        ‖(referenceMultiplier p : ℂ) • (scaledFiber h p - physicalFiberVector 0)‖ := norm_add_le _ _
    _ = |cutoffBandMultiplier h z p - referenceMultiplier p| * ‖scaledFiber h p‖ +
        referenceMultiplier p * ‖scaledFiber h p - physicalFiberVector 0‖ := by
      simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (referenceMultiplier_nonneg p)]
    _ ≤ ((2 : ℝ)^128 * h) * 2 + (2 : ℝ)^66 * h :=
      add_le_add (mul_le_mul hs hn (norm_nonneg _) (by positivity)) hv
    _ ≤ (2 : ℝ)^130 * h := by nlinarith

end Maxwell.Continuum.EffectiveMass
