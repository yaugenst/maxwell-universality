import Maxwell.Continuum.CauchyBounds
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! The derivative of an actual quartic remainder is cubically small.
The estimate follows from Cauchy's formula on a disk of radius |z|. -/

noncomputable section

namespace Maxwell.Continuum.AnalyticQuartic

open Set Metric

theorem derivative_remainder_bound {f : ℂ → ℂ} {a : ℂ} {R C : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (hC : 0 ≤ C)
    (herr : ∀ w : ℂ, ‖w‖ ≤ R / 2 → ‖f w - f 0 - a * w^2‖ ≤ C * ‖w‖^4)
    {z : ℂ} (hz0 : 0 < ‖z‖) (hz : ‖z‖ ≤ R / 4) :
    ‖deriv f z - 2 * a * z‖ ≤ 16 * C * ‖z‖^3 := by
  let g : ℂ → ℂ := fun w => f w - f 0 - a * w^2
  have hR : 0 < R := by linarith
  have hsub : closedBall (0 : ℂ) (2 * ‖z‖) ⊆ ball 0 R := by
    apply closedBall_subset_ball
    linarith
  have hg : AnalyticOnNhd ℂ g (closedBall 0 (2 * ‖z‖)) := by
    intro w hw
    exact ((hf w (hsub hw)).sub analyticAt_const).sub
      (analyticAt_const.mul (analyticAt_id.pow 2))
  have hbound : ∀ w ∈ closedBall (0 : ℂ) (2 * ‖z‖), ‖g w‖ ≤ C * (2 * ‖z‖)^4 := by
    intro w hw
    have hw' : ‖w‖ ≤ 2 * ‖z‖ := by simpa using hw
    exact (herr w (by linarith)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hw' 4) hC)
  have hd : deriv g z = deriv f z - 2 * a * z := by
    have hdf := (hf z (by simpa using (show ‖z‖ < R by linarith))).differentiableAt.hasDerivAt
    have h := (hdf.sub_const (f 0)).sub (((hasDerivAt_id z).pow 2).const_mul a)
    change HasDerivAt g (deriv f z - a * ((2 : ℂ) * z^1 * 1)) z at h
    simpa only [pow_one, mul_one, mul_assoc, mul_left_comm] using h.deriv
  have hb := CauchyBounds.norm_deriv_le hg hbound hz0
    (by linarith : ‖z‖ + ‖z‖ ≤ 2 * ‖z‖)
  rw [hd] at hb
  exact hb.trans_eq (by field_simp; ring)

end Maxwell.Continuum.AnalyticQuartic
