import Maxwell.Continuum.WellCutoffBase
import Maxwell.Continuum.WellFourierDeriv

/-! Explicit mass bounds used to normalize the scalar Birman--Schwinger well. -/

noncomputable section

namespace Maxwell.Continuum.Well

open MeasureTheory Set Metric

theorem w_eq_cutoffBase_norm_half (y : Space) : w y = cutoffBase (‖y‖ / 2) := by
  rw [w_eq_glue, cutoffBase]
  congr 1
  ring

theorem w_lower_half (y : Space) (hy : ‖y‖ ≤ 1 / 2) : 1 / 4 ≤ w y := by
  rw [w_eq_cutoffBase_norm_half]
  apply cutoffBase_lower_quarter
  rw [abs_of_nonneg (by positivity : 0 ≤ ‖y‖ / 2)]
  linarith

theorem w_integral_lower : (1 / 8 : ℝ) ≤ ∫ y : Space, w y := by
  have hi : Integrable ((closedBall (0 : Space) (1 / 2)).indicator (fun _ : Space => (1 / 4 : ℝ))) volume :=
    (integrableOn_const (isCompact_closedBall (0 : Space) (1 / 2)).measure_lt_top.ne).integrable_indicator
      measurableSet_closedBall
  have h := integral_mono hi w_integrable (fun y => by
    by_cases hy : y ∈ closedBall (0 : Space) (1 / 2)
    · rw [indicator_of_mem hy]
      exact w_lower_half y (by simpa using hy)
    · rw [indicator_of_notMem hy]
      exact w_nonneg y)
  rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, measureReal_def,
    EuclideanSpace.volume_closedBall_fin_three] at h
  norm_num [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)] at h
  linarith [Real.pi_gt_three]

theorem w_integral_upper : (∫ y : Space, w y) ≤ 8 := by
  have h := integral_abs_directional_le w (by rw [w_tsupport]) 0 0 1 (by norm_num)
    (fun y => by simpa [directionalDerivative, abs_of_nonneg (w_nonneg y)] using w_le_one y)
  simpa [directionalDerivative, abs_of_nonneg (w_nonneg _)] using h

theorem w_integral_pos : 0 < ∫ y : Space, w y :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 8) w_integral_lower

end Maxwell.Continuum.Well
