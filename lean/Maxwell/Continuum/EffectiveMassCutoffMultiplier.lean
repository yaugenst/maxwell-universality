import Maxwell.Continuum.EffectiveMassMultiplier
import Maxwell.Continuum.AuxiliaryCutoff

/-! The complete scalar multiplier comparison, including the literal
smooth cutoff and extension by zero outside its support. -/

noncomputable section

namespace Maxwell.Continuum.EffectiveMass

open FreeFiber PeriodicBand Auxiliary

def cutoffBandMultiplier (h z : ℝ) (p : Space) : ℝ :=
  Real.sqrt (cutoff (h • p)) * bandMultiplier h z p

theorem cutoffBandMultiplier_physical {h z : ℝ} (D : Calibration h z) (p : Space) :
    cutoffBandMultiplier h z p = h * Real.sqrt (cutoff (h • p)) /
      Real.sqrt (bandValue (h • p) - z) := by
  rw [cutoffBandMultiplier, bandMultiplier_physical D]
  ring

theorem cutoffSqrt_le_one (q : Space) : Real.sqrt (cutoff q) ≤ 1 := by
  nlinarith [Real.sq_sqrt (cutoff_nonneg q), Real.sqrt_nonneg (cutoff q), cutoff_le_one q]

theorem referenceMultiplier_tail {h z : ℝ} (D : Calibration h z) (p : Space)
    (hp : cutoff (h • p) ≠ 1) : referenceMultiplier p ≤ (2 : ℝ)^91 * h := by
  have hnorm : smallRadius < ‖h • p‖ := by
    by_contra hn
    exact hp (cutoff_eq_one_of_norm_le (le_of_not_gt hn))
  rw [scaled_norm D.h_pos.le] at hnorm
  have hweighted := mul_le_mul_of_nonneg_left (referenceMultiplier_weighted p) D.h_pos.le
  have hsmall := mul_le_mul_of_nonneg_right hnorm.le (referenceMultiplier_nonneg p)
  have heq : smallRadius * (2 : ℝ)^91 = ((2 : ℝ)^49)⁻¹ := by
    norm_num [smallRadius, backgroundAmplitude]
  apply (mul_le_mul_iff_right₀ smallRadius_pos).mp
  calc
    _ ≤ h * ‖p‖ * referenceMultiplier p := hsmall
    _ = h * (‖p‖ * referenceMultiplier p) := by ring
    _ ≤ h * ((2 : ℝ)^49)⁻¹ := hweighted
    _ = smallRadius * ((2 : ℝ)^91 * h) := by rw [← heq]; ring

theorem cutoff_multiplier_loss {h z : ℝ} (D : Calibration h z) (p : Space) :
    (1 - Real.sqrt (cutoff (h • p))) * referenceMultiplier p ≤ (2 : ℝ)^91 * h := by
  have hh := D.h_pos
  by_cases hc : cutoff (h • p) = 1
  · rw [hc, Real.sqrt_one, sub_self, zero_mul]
    positivity
  · have ht := referenceMultiplier_tail D p hc
    have hs := Real.sqrt_nonneg (cutoff (h • p))
    nlinarith [mul_nonneg hs (referenceMultiplier_nonneg p)]

/-- The displayed uniform bound for `s_h - s_H`, on all momenta. -/
theorem cutoffBandMultiplier_error {h z : ℝ} (D : Calibration h z) (p : Space) :
    |cutoffBandMultiplier h z p - referenceMultiplier p| ≤ (2 : ℝ)^128 * h := by
  have hh := D.h_pos
  by_cases hc : cutoff (h • p) = 0
  · have hn : cutoff (h • p) ≠ 1 := by rw [hc]; norm_num
    have ht := referenceMultiplier_tail D p hn
    simp only [cutoffBandMultiplier, hc, Real.sqrt_zero, zero_mul, zero_sub, abs_neg,
      abs_of_nonneg (referenceMultiplier_nonneg p)]
    exact ht.trans (mul_le_mul_of_nonneg_right (by norm_num) D.h_pos.le)
  have hnorm := cutoff_ne_zero_norm_le hc
  rw [scaled_norm D.h_pos.le] at hnorm
  have herr := bandMultiplier_error D p hnorm
  have hs0 := Real.sqrt_nonneg (cutoff (h • p))
  have hs1 := cutoffSqrt_le_one (h • p)
  have hloss := cutoff_multiplier_loss D p
  have hid : cutoffBandMultiplier h z p - referenceMultiplier p =
      Real.sqrt (cutoff (h • p)) * (bandMultiplier h z p - referenceMultiplier p) -
        (1 - Real.sqrt (cutoff (h • p))) * referenceMultiplier p := by
    unfold cutoffBandMultiplier
    ring
  rw [hid]
  calc
    _ ≤ |Real.sqrt (cutoff (h • p)) * (bandMultiplier h z p - referenceMultiplier p)| +
        |(1 - Real.sqrt (cutoff (h • p))) * referenceMultiplier p| := abs_sub _ _
    _ = Real.sqrt (cutoff (h • p)) * |bandMultiplier h z p - referenceMultiplier p| +
        (1 - Real.sqrt (cutoff (h • p))) * referenceMultiplier p := by
      rw [abs_mul, abs_of_nonneg hs0,
        abs_of_nonneg (mul_nonneg (by linarith) (referenceMultiplier_nonneg p))]
    _ ≤ (2 : ℝ)^100 * h + (2 : ℝ)^91 * h := by
      have hm := mul_le_mul hs1 herr (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      simpa only [one_mul] using add_le_add hm hloss
    _ ≤ (2 : ℝ)^128 * h := by nlinarith [D.h_pos]

end Maxwell.Continuum.EffectiveMass
