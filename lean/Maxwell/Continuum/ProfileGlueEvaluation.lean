import Maxwell.Continuum.WellComplex
import Maxwell.Continuum.CalibrationElementary
import Maxwell.Continuum.CalibrationPowerRate
import Mathlib.Analysis.Calculus.MeanValue

/-! Rational evaluation of the flat exponential with a polynomial work bound.
The small-denominator branch uses its proved exponentially small value. -/

namespace Maxwell.Continuum.Profile

open Maxwell.Certificate

theorem glue_hasDerivAt (x : ℝ) :
    HasDerivAt expNegInvGlue (x⁻¹^2*expNegInvGlue x) x := by
  simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) x

theorem glue_derivative_bound (x : ℝ) : |deriv expNegInvGlue x| ≤ 2 := by
  rw [(glue_hasDerivAt x).deriv]
  by_cases hx : x ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos hx]
    norm_num
  · have hx0 : 0 < x := lt_of_not_ge hx
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (expNegInvGlue.nonneg x))]
    simp only [expNegInvGlue, ite_eq_right hx]
    simpa using Well.pow_mul_exp_neg_le_factorial x⁻¹ (inv_pos.mpr hx0).le 2

theorem glue_lipschitz : LipschitzWith 2 expNegInvGlue := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (glue_hasDerivAt x).differentiableAt)
  intro x
  exact_mod_cast (show ‖deriv expNegInvGlue x‖ ≤ (2 : ℝ) by
    simpa only [Real.norm_eq_abs] using glue_derivative_bound x)

theorem glue_small (N : ℕ) {x : ℝ} (hx : x ≤ 1/((N : ℝ)+1)) :
    expNegInvGlue x ≤ (1/2 : ℝ)^N := by
  by_cases hx0 : x ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos hx0]
    positivity
  have hp : 0 < x := lt_of_not_ge hx0
  have hnx : (N : ℝ)+1 ≤ x⁻¹ := by
    have h := (le_div_iff₀ (show 0 < (N : ℝ)+1 by positivity)).mp hx
    rw [← one_div]
    exact (le_div_iff₀ hp).mpr (by nlinarith only [h])
  simp only [expNegInvGlue, ite_eq_right hx0]
  calc
    _ ≤ Real.exp (-(N : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-1)^N := by simpa using Real.exp_nat_mul (-1) N
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) Calibration.exp_neg_one_le_half _

def glueApprox (q : ℚ) (N : ℕ) : Ball :=
  if q ≤ 1/((N : ℚ)+1) then ⟨0,(1/2 : ℚ)^N,by positivity⟩
  else Elementary.expApprox (-1/q) (N+1) N

theorem glueApprox_radius (q : ℚ) (N : ℕ) : (glueApprox q N).radius = (1/2 : ℚ)^N := by
  unfold glueApprox
  split_ifs
  · rfl
  · exact (Elementary.elementary_radii _ _ _).1

theorem glueApprox_contains (q : ℚ) (N : ℕ) : (glueApprox q N).Contains (expNegInvGlue q) := by
  unfold glueApprox
  split_ifs with hq
  · simp only [Ball.Contains, Rat.cast_zero, sub_zero,
      abs_of_nonneg (expNegInvGlue.nonneg _)]
    push_cast
    apply glue_small N
    have hr : (q : ℝ) ≤ ((1/((N : ℚ)+1) : ℚ) : ℝ) := Rat.cast_le.mpr hq
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_natCast] using hr
  · have hq0 : 0 < q := lt_trans (by positivity : (0 : ℚ) < 1/((N : ℚ)+1)) (lt_of_not_ge hq)
    have hbound : |(-1/q : ℚ)| ≤ (N+1 : ℕ) := by
      rw [neg_div, abs_neg, abs_of_pos (by positivity : (0 : ℚ) < 1/q)]
      have h := (div_lt_iff₀ (show (0 : ℚ) < (N : ℚ)+1 by positivity)).mp (lt_of_not_ge hq)
      apply (div_le_iff₀ hq0).mpr
      push_cast
      nlinarith only [h]
    have h := Elementary.expApprox_contains (-1/q) (N+1) N hbound
    have hr : 0 < (q : ℝ) := by exact_mod_cast hq0
    simpa only [expNegInvGlue, ite_eq_right (not_le_of_gt hr), Rat.cast_div,
      Rat.cast_neg, Rat.cast_one, neg_div, one_div, Rat.cast_inv] using h

theorem glueApprox_error {x : ℝ} (q : ℚ) (N : ℕ) {δ : ℝ} (hx : |x-(q : ℝ)| ≤ δ) :
    |expNegInvGlue x-((glueApprox q N).center : ℝ)| ≤ 2*δ+(1/2 : ℝ)^N := by
  have hg := glueApprox_contains q N
  rw [Ball.Contains, glueApprox_radius] at hg
  push_cast at hg
  have hl := glue_lipschitz.dist_le_mul x (q : ℝ)
  simp only [Real.dist_eq, NNReal.coe_ofNat] at hl
  calc
    _ ≤ |expNegInvGlue x-expNegInvGlue (q : ℝ)|+
        |expNegInvGlue (q : ℝ)-((glueApprox q N).center : ℝ)| := abs_sub_le _ _ _
    _ ≤ _ := by linarith

#print axioms glueApprox_contains
#print axioms glueApprox_error

end Maxwell.Continuum.Profile
