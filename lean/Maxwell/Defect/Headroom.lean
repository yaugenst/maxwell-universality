import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Scalar material bounds for the two-sided tuning interval. -/

namespace Maxwell.Defect

/-- The reciprocal of a sufficiently large compressed eigenvalue uses less
than one quarter of the available material contrast. -/
theorem reciprocal_tuning_bounds {t h μ ξ : ℝ}
    (ht : 0 < t) (hh : 0 < h) (hξ : 0 < ξ)
    (hμ : 4 / (t * h) < μ) (hgap : μ ≤ 1 / ξ) :
    0 < 1 / μ ∧ ξ ≤ 1 / μ ∧ 1 / μ < t * h / 4 := by
  have hth : 0 < t * h := mul_pos ht hh
  have hμpos : 0 < μ := lt_trans (div_pos (by norm_num) hth) hμ
  have hmul : 4 < μ * (t * h) := (div_lt_iff₀ hth).mp hμ
  have hgap' : μ * ξ ≤ 1 := (le_div_iff₀ hξ).mp hgap
  refine ⟨div_pos zero_lt_one hμpos, ?_, ?_⟩
  · exact (le_div_iff₀ hμpos).mpr (by nlinarith)
  · apply (div_lt_iff₀ hμpos).mpr
    nlinarith

/-- Every point in the symmetric tuning interval is positive and keeps
more than half of the original upper material headroom. -/
theorem scalar_tuning_headroom {t h vstar ξlow v background : ℝ}
    (ht : 0 < t) (hh : 0 < h) (hvstar : 0 < vstar)
    (hsmall : vstar < t * h / 4)
    (hξ : ξlow ≤ vstar) (hv : |v - vstar| ≤ ξlow / 4)
    (hbackground : 1 ≤ background ∧ background ≤ 25 - h) :
    3 * vstar / 4 ≤ v ∧ v ≤ 5 * vstar / 4 ∧ 0 < v ∧
      1 ≤ background + v / t ∧ background + v / t < 25 - h / 2 := by
  obtain ⟨hvlo, hvhi⟩ := abs_le.mp hv
  have hlo : 3 * vstar / 4 ≤ v := by linarith
  have hhi : v ≤ 5 * vstar / 4 := by linarith
  have hvpos : 0 < v := by linarith
  have hvt : v / t < 5 * h / 16 := by
    apply (div_lt_iff₀ ht).mpr
    nlinarith
  exact ⟨hlo, hhi, hvpos,
    le_trans hbackground.1 (le_add_of_nonneg_right (div_nonneg hvpos.le ht.le)),
    by linarith [hbackground.2]⟩

/-- A shift chosen strictly below the band edge preserves the certified
headroom of the edge-shifted background. -/
theorem uniform_shift_headroom {base edge z t h : ℝ}
    (ht : 0 < t) (hbase : 1 ≤ base) (hz : 0 < z) (hze : z < edge)
    (hupper : base + edge / t ≤ 25 - h) :
    1 ≤ base + z / t ∧ base + z / t < 25 - h := by
  have hshift : z / t < edge / t := (div_lt_div_iff_of_pos_right ht).mpr hze
  exact ⟨le_trans hbase (le_add_of_nonneg_right (div_pos hz ht).le), by linarith⟩

end Maxwell.Defect
