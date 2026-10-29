import Maxwell.Continuum.WeakCurl
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The literal compact radial bump and its square root from the continuum construction. -/

noncomputable section

namespace Maxwell.Continuum.Well

open MeasureTheory Set Metric

def w (y : Space) : ℝ :=
  if ‖y‖ < 1 then Real.exp (-1 / (1 - ‖y‖ ^ 2)) else 0

def qw (y : Space) : ℝ := Real.sqrt (w y)

theorem w_nonneg (y : Space) : 0 ≤ w y := by
  unfold w
  split_ifs <;> positivity

theorem w_eq_glue (y : Space) : w y = expNegInvGlue (1 - ‖y‖ ^ 2) := by
  by_cases h : ‖y‖ < 1
  · have hs : 0 < 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
    simp [w, expNegInvGlue, h, hs.not_ge, div_eq_mul_inv]
  · have hs : 1 - ‖y‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg y]
    simp [w, expNegInvGlue, h, hs]

theorem qw_eq_glue (y : Space) : qw y = expNegInvGlue (2 * (1 - ‖y‖ ^ 2)) := by
  by_cases h : ‖y‖ < 1
  · have hs : 0 < 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
    have h2 : 0 < 2 * (1 - ‖y‖ ^ 2) := by positivity
    simp only [qw, w, ite_eq_left h, expNegInvGlue, ite_eq_right h2.not_ge, ← Real.exp_half]
    congr 1
    field_simp
  · have hs : 2 * (1 - ‖y‖ ^ 2) ≤ 0 := by nlinarith [norm_nonneg y]
    simp [qw, w, expNegInvGlue, h, hs]

/-- Smoothness includes the zero extension across the unit sphere. -/
theorem w_contDiff : ContDiff ℝ (⊤ : ℕ∞) w := by
  have he : w = fun y : Space => expNegInvGlue (1 - ‖y‖ ^ 2) := funext w_eq_glue
  rw [he]
  exact expNegInvGlue.contDiff.comp
    (contDiff_const.sub (contDiff_norm_sq (E := Space) ℝ))

/-- The square root is smooth because it is another flat exponential bump. -/
theorem qw_contDiff : ContDiff ℝ (⊤ : ℕ∞) qw := by
  have he : qw = fun y : Space => expNegInvGlue (2 * (1 - ‖y‖ ^ 2)) := funext qw_eq_glue
  rw [he]
  exact expNegInvGlue.contDiff.comp
    (contDiff_const.mul (contDiff_const.sub (contDiff_norm_sq (E := Space) ℝ)))

theorem w_positive_iff (y : Space) : 0 < w y ↔ ‖y‖ < 1 := by
  by_cases h : ‖y‖ < 1 <;> simp [w, h, Real.exp_pos]

theorem w_zero_iff (y : Space) : w y = 0 ↔ 1 ≤ ‖y‖ := by
  rw [← not_lt, ← w_positive_iff, not_lt]
  exact le_antisymm_iff.trans (and_iff_left (w_nonneg y))

theorem w_le_one (y : Space) : w y ≤ 1 := by
  by_cases h : ‖y‖ < 1
  · have hs : 0 < 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
    rw [w, ite_eq_left h, Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hs.le
  · simp [w, h]

theorem qw_nonneg (y : Space) : 0 ≤ qw y := Real.sqrt_nonneg _

theorem qw_sq (y : Space) : qw y ^ 2 = w y := Real.sq_sqrt (w_nonneg y)

theorem qw_le_one (y : Space) : qw y ≤ 1 := by
  have h := qw_sq y
  nlinarith [qw_nonneg y, w_le_one y]

theorem qw_zero_iff (y : Space) : qw y = 0 ↔ 1 ≤ ‖y‖ := by
  rw [qw, Real.sqrt_eq_zero (w_nonneg y), w_zero_iff]

theorem w_support : Function.support w = ball (0 : Space) 1 := by
  ext y
  simp only [Function.mem_support, mem_ball_zero_iff]
  exact not_congr (w_zero_iff y) |>.trans not_le

theorem qw_support : Function.support qw = ball (0 : Space) 1 := by
  ext y
  simp only [Function.mem_support, mem_ball_zero_iff]
  exact not_congr (qw_zero_iff y) |>.trans not_le

theorem w_tsupport : tsupport w = closedBall (0 : Space) 1 := by
  rw [tsupport, w_support, closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]

theorem qw_tsupport : tsupport qw = closedBall (0 : Space) 1 := by
  rw [tsupport, qw_support, closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]

theorem w_hasCompactSupport : HasCompactSupport w := by
  rw [HasCompactSupport, w_tsupport]
  exact isCompact_closedBall _ _

theorem qw_hasCompactSupport : HasCompactSupport qw := by
  rw [HasCompactSupport, qw_tsupport]
  exact isCompact_closedBall _ _

theorem w_integrable : Integrable w (volume : Measure Space) :=
  w_contDiff.continuous.integrable_of_hasCompactSupport w_hasCompactSupport

theorem qw_integrable : Integrable qw (volume : Measure Space) :=
  qw_contDiff.continuous.integrable_of_hasCompactSupport qw_hasCompactSupport

end Maxwell.Continuum.Well
