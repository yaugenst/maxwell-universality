import Maxwell.Continuum.AliasSeparation
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! A finite-measure support set containing the actual rescaled cutoff.
Its measure is bounded by h⁻³ with the literal small momentum radius. -/

noncomputable section

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber PeriodicBand
open scoped ENNReal

def aliasChart (h : ℝ) : Set Space := Metric.closedBall 0 (4 * smallRadius / h)

theorem mem_aliasChart {h : ℝ} (hh : 0 < h) (p : Space) :
    p ∈ aliasChart h ↔ h * ‖p‖ ≤ 4 * smallRadius := by
  simp only [aliasChart, Metric.mem_closedBall, dist_zero_right]
  rw [le_div_iff₀ hh, mul_comm ‖p‖ h]

theorem aliasChart_measurable (h : ℝ) : MeasurableSet (aliasChart h) :=
  measurableSet_closedBall

theorem aliasChart_finite (h : ℝ) : volume (aliasChart h) ≠ ∞ :=
  (isCompact_closedBall (0 : Space) (4 * smallRadius / h)).measure_ne_top

theorem aliasChart_volume {h : ℝ} (hh : 0 < h) :
    volume.real (aliasChart h) ≤ (h⁻¹)^3 := by
  have hq := smallRadius_pos
  have hr : 0 ≤ 4 * smallRadius / h := div_nonneg (by positivity) hh.le
  have hvol : volume.real (aliasChart h) =
      (4 * smallRadius / h)^3 * (Real.pi * 4 / 3) := by
    rw [measureReal_def, aliasChart, EuclideanSpace.volume_closedBall_fin_three,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
      ENNReal.toReal_ofReal (by positivity)]
  have hsmall : 4 * smallRadius ≤ (1 : ℝ) / 2 := by
    norm_num [smallRadius, backgroundAmplitude]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 4 * smallRadius) hsmall 3
  have hpi : Real.pi * 4 / 3 ≤ 8 := by linarith [Real.pi_lt_four]
  have hfactor : (4 * smallRadius)^3 * (Real.pi * 4 / 3) ≤ 1 := by
    have hm := mul_le_mul hpow hpi (by positivity) (by norm_num : (0 : ℝ) ≤ (1/2 : ℝ)^3)
    norm_num at hm
    exact hm
  rw [hvol]
  calc
    _ = ((4 * smallRadius)^3 * (Real.pi * 4 / 3)) * (h⁻¹)^3 := by ring
    _ ≤ 1 * (h⁻¹)^3 := mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ = _ := one_mul _

end Maxwell.Continuum.EffectiveMass
