import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-! Quantitative nonvanishing and the stronger real-axis positivity test. -/

namespace Maxwell.Defect

/-- A strict half-margin test certifies every point of a complex ball at
once. The hypothesis is the norm bound supplied by the analytic chart. -/
theorem numerator_modulus_lower {N : ℂ} {overlap radiusBound : ℝ}
    (hvariation : ‖N - (overlap ^ 2 : ℂ)‖ ≤ radiusBound)
    (hmargin : 2 * radiusBound < overlap ^ 2) :
    overlap ^ 2 / 2 < ‖N‖ := by
  have htriangle := norm_le_norm_add_norm_sub N (overlap ^ 2 : ℂ)
  have hnorm : ‖(overlap ^ 2 : ℂ)‖ = overlap ^ 2 := by
    simp [← Complex.ofReal_pow, Complex.norm_real]
  rw [hnorm] at htriangle
  linarith

theorem numerator_nonzero {N : ℂ} {overlap radiusBound : ℝ}
    (hvariation : ‖N - (overlap ^ 2 : ℂ)‖ ≤ radiusBound)
    (hmargin : 2 * radiusBound < overlap ^ 2) : N ≠ 0 := by
  have h := numerator_modulus_lower hvariation hmargin
  intro hzero
  rw [hzero, norm_zero] at h
  nlinarith [sq_nonneg overlap]

/-- At imaginary Bloch displacement the numerator is real; positivity
then follows from the same quantitative certificate. -/
theorem real_numerator_positive {N overlap radiusBound : ℝ}
    (hvariation : |N - overlap ^ 2| ≤ radiusBound)
    (hmargin : 2 * radiusBound < overlap ^ 2) :
    overlap ^ 2 / 2 < N ∧ 0 < N := by
  have h := (abs_le.mp hvariation).1
  constructor
  · linarith
  · nlinarith [sq_nonneg overlap]

end Maxwell.Defect
