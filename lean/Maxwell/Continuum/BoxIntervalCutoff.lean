import Maxwell.Continuum.BoxRamp
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! The two reflected unit-width ramps defining a finite-interval
cutoff have uniform first and second derivative bounds. -/

noncomputable section

namespace Maxwell.Continuum.BoxCutoff

open Set Filter
open scoped Topology

def interval (N x : ℝ) : ℝ := ramp x*ramp (N-x)

theorem interval_nonneg (N x : ℝ) : 0 ≤ interval N x :=
  mul_nonneg (ramp_nonneg x) (ramp_nonneg (N-x))

theorem interval_le_one (N x : ℝ) : interval N x ≤ 1 := by
  exact (mul_le_mul (ramp_le_one x) (ramp_le_one (N-x)) (ramp_nonneg _) (by norm_num)).trans_eq (one_mul 1)

theorem interval_zero_left (N : ℝ) {x : ℝ} (hx : x ≤ 1) : interval N x = 0 := by
  rw [interval, ramp_zero hx, zero_mul]

theorem interval_zero_right (N : ℝ) {x : ℝ} (hx : N-1 ≤ x) : interval N x = 0 := by
  rw [interval, ramp_zero (show N-x ≤ 1 by linarith), mul_zero]

theorem interval_one (N : ℝ) {x : ℝ} (hx : 2 ≤ x) (hy : x ≤ N-2) : interval N x = 1 := by
  rw [interval, ramp_one hx, ramp_one (show 2 ≤ N-x by linarith), one_mul]

theorem interval_contDiff (N : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (interval N) :=
  ramp_contDiff.mul (ramp_contDiff.comp (contDiff_const.sub contDiff_id))

theorem ramp_hasDerivAt (x : ℝ) : HasDerivAt ramp (deriv ramp x) x :=
  (ramp_contDiff.differentiable (by simp) x).hasDerivAt

theorem ramp_deriv_hasDerivAt (x : ℝ) : HasDerivAt (deriv ramp) (deriv (deriv ramp) x) x :=
  ((contDiff_infty_iff_deriv.mp ramp_contDiff).2.differentiable (by simp) x).hasDerivAt

theorem interval_deriv (N : ℝ) : deriv (interval N) = fun x =>
    deriv ramp x*ramp (N-x)-ramp x*deriv ramp (N-x) := by
  funext x
  change deriv (ramp*(fun y => ramp (N-y))) x = _
  have h := (ramp_hasDerivAt x).mul ((ramp_hasDerivAt (N-x)).comp_const_sub N x)
  simpa only [mul_neg, ← sub_eq_add_neg] using h.deriv

theorem interval_second (N : ℝ) : deriv (deriv (interval N)) = fun x =>
    deriv (deriv ramp) x*ramp (N-x)-2*deriv ramp x*deriv ramp (N-x)+
      ramp x*deriv (deriv ramp) (N-x) := by
  rw [interval_deriv]
  funext x
  change deriv ((deriv ramp*(fun y => ramp (N-y)))-ramp*(fun y => deriv ramp (N-y))) x = _
  have h := ((ramp_deriv_hasDerivAt x).mul ((ramp_hasDerivAt (N-x)).comp_const_sub N x)).sub
    ((ramp_hasDerivAt x).mul ((ramp_deriv_hasDerivAt (N-x)).comp_const_sub N x))
  rw [h.deriv]
  ring

theorem interval_deriv_bound (N x : ℝ) : |deriv (interval N) x| ≤ 32 := by
  rw [interval_deriv]
  have ha : |deriv ramp x*ramp (N-x)| ≤ 16 := by
    rw [abs_mul, abs_of_nonneg (ramp_nonneg _)]
    exact (mul_le_mul (ramp_deriv_bound x) (ramp_le_one _) (ramp_nonneg _) (by norm_num)).trans_eq (mul_one 16)
  have hb : |ramp x*deriv ramp (N-x)| ≤ 16 := by
    rw [abs_mul, abs_of_nonneg (ramp_nonneg _)]
    exact (mul_le_mul (ramp_le_one x) (ramp_deriv_bound _) (abs_nonneg _) (by norm_num)).trans_eq (one_mul 16)
  linarith [abs_sub (deriv ramp x*ramp (N-x)) (ramp x*deriv ramp (N-x))]

theorem interval_second_bound (N x : ℝ) : |deriv (deriv (interval N)) x| ≤ 26112 := by
  rw [interval_second]
  have ha : |deriv (deriv ramp) x*ramp (N-x)| ≤ 12800 := by
    rw [abs_mul, abs_of_nonneg (ramp_nonneg _)]
    exact (mul_le_mul (ramp_second_bound x) (ramp_le_one _) (ramp_nonneg _) (by norm_num)).trans_eq (mul_one 12800)
  have hb : |2*deriv ramp x*deriv ramp (N-x)| ≤ 512 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ ≤ ((2 : ℝ)*16)*16 := mul_le_mul
        (mul_le_mul_of_nonneg_left (ramp_deriv_bound x) (by norm_num))
        (ramp_deriv_bound (N-x)) (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hc : |ramp x*deriv (deriv ramp) (N-x)| ≤ 12800 := by
    rw [abs_mul, abs_of_nonneg (ramp_nonneg _)]
    exact (mul_le_mul (ramp_le_one x) (ramp_second_bound _) (abs_nonneg _) (by norm_num)).trans_eq (one_mul 12800)
  linarith [abs_add_le (deriv (deriv ramp) x*ramp (N-x)-2*deriv ramp x*deriv ramp (N-x))
    (ramp x*deriv (deriv ramp) (N-x)),
    abs_sub (deriv (deriv ramp) x*ramp (N-x)) (2*deriv ramp x*deriv ramp (N-x))]

#print axioms interval_second_bound

end Maxwell.Continuum.BoxCutoff
