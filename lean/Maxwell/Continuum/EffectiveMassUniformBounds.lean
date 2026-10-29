import Maxwell.Continuum.EffectiveMassFiberVariation
import Maxwell.Continuum.AliasChart

/-! Uniform boundedness and exact support of the actual scalar and vector
multipliers in the effective-mass comparison. -/

noncomputable section

namespace Maxwell.Continuum.EffectiveMass

open Auxiliary PeriodicBand

theorem bandMultiplier_nonneg (h z : ℝ) (p : Space) : 0 ≤ bandMultiplier h z p := by
  unfold bandMultiplier
  positivity

theorem bandMultiplier_le_two {h z : ℝ} (D : Calibration h z) (p : Space)
    (hp : h * ‖p‖ ≤ 4 * smallRadius) : bandMultiplier h z p ≤ 2 := by
  have ha := bandDenominator_lower D p hp
  have hb := referenceDenominator_ge_one p
  have hapos : 0 < bandDenominator h z p := by linarith
  have hs := Real.sq_sqrt hapos.le
  have hs0 := Real.sqrt_pos.mpr hapos
  unfold bandMultiplier
  rw [← one_div, div_le_iff₀ hs0]
  nlinarith

theorem cutoffBandMultiplier_nonneg (h z : ℝ) (p : Space) :
    0 ≤ cutoffBandMultiplier h z p :=
  mul_nonneg (Real.sqrt_nonneg _) (bandMultiplier_nonneg h z p)

theorem cutoffBandMultiplier_le_two {h z : ℝ} (D : Calibration h z) (p : Space) :
    cutoffBandMultiplier h z p ≤ 2 := by
  by_cases hc : cutoff (h • p) = 0
  · simp [cutoffBandMultiplier, hc]
  have hp := cutoff_ne_zero_norm_le hc
  rw [scaled_norm D.h_pos.le] at hp
  have hm := mul_le_mul (cutoffSqrt_le_one (h • p)) (bandMultiplier_le_two D p hp)
    (bandMultiplier_nonneg h z p) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [cutoffBandMultiplier, one_mul] using hm

theorem cutoffBandMultiplier_zero_off_chart {h z : ℝ} (hh : 0 < h) (p : Space)
    (hp : p ∉ aliasChart h) : cutoffBandMultiplier h z p = 0 := by
  have hc : cutoff (h • p) = 0 := by
    by_contra hc
    have hn := cutoff_ne_zero_norm_le hc
    rw [scaled_norm hh.le] at hn
    exact hp ((mem_aliasChart hh p).mpr hn)
  simp only [cutoffBandMultiplier, hc, Real.sqrt_zero, zero_mul]

theorem vectorMultiplier_norm_le {h z : ℝ} (D : Calibration h z) (p : Space) :
    ‖vectorMultiplier h z p‖ ≤ 4 := by
  by_cases hc : cutoff (h • p) = 0
  · simp [vectorMultiplier, cutoffBandMultiplier, hc]
  have hp := cutoff_ne_zero_norm_le hc
  rw [scaled_norm D.h_pos.le] at hp
  rw [vectorMultiplier, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (cutoffBandMultiplier_nonneg h z p)]
  have hm := mul_le_mul (cutoffBandMultiplier_le_two D p)
    (scaledFiber_norm_le D.h_pos.le p hp) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  norm_num at hm ⊢
  exact hm

theorem referenceVectorMultiplier_norm_le (p : Space) :
    ‖referenceVectorMultiplier p‖ ≤ 2 := by
  rw [referenceVectorMultiplier, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (referenceMultiplier_nonneg p)]
  have hm := mul_le_mul (referenceMultiplier_le_one p) physicalFiberVector_zero_norm_le
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [one_mul] using hm

end Maxwell.Continuum.EffectiveMass
