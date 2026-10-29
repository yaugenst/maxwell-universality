import Maxwell.Continuum.CauchyBounds
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Operator-norm Cauchy bounds in a complex Banach space. Scalar complex
lines give estimates independent of the number of momentum coordinates. -/

noncomputable section

namespace Maxwell.Continuum.AnalyticBallBounds

open Set Metric

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem fderiv_bound {f : E → F} {R C : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f (ball 0 R))
    (hb : ∀ x ∈ ball 0 R, ‖f x‖ ≤ C)
    {x : E} (hx : ‖x‖ ≤ R / 2) : ‖fderiv ℂ f x‖ ≤ 2 * C / R := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  have hline : AnalyticOnNhd ℂ (fun z : ℂ => f (x + z • v)) (ball 0 (R / 2)) := by
    intro z hz
    have hz' : ‖z‖ < R / 2 := by simpa only [mem_ball, dist_zero_right] using hz
    have hp : x + z • v ∈ ball 0 R := by
      rw [mem_ball, dist_zero_right]
      calc
        ‖x + z • v‖ ≤ ‖x‖ + ‖z‖ := by simpa only [norm_smul, hv, mul_one] using norm_add_le x (z • v)
        _ < R := by linarith only [hx, hz']
    exact AnalyticAt.comp (f := fun w : ℂ => x + w • v) (hf _ hp)
      (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
  have hbline : ∀ z ∈ ball (0 : ℂ) (R / 2), ‖f (x + z • v)‖ ≤ C := by
    intro z hz
    apply hb
    rw [mem_ball, dist_zero_right]
    have hz' : ‖z‖ < R / 2 := by simpa only [mem_ball, dist_zero_right] using hz
    have hn := norm_add_le x (z • v)
    rw [norm_smul, hv, mul_one] at hn
    linarith only [hn, hx, hz']
  have hder := CauchyBounds.norm_iteratedDeriv_zero_le_of_open 1 hline hbline (half_pos hR)
  have hfx : DifferentiableAt ℂ f x :=
    (hf x (by rw [mem_ball, dist_zero_right]; linarith only [hx, hR])).differentiableAt
  have hm : HasDerivAt (fun z : ℂ => x + z • v) v 0 := by
    convert! ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x using 1
    simp only [one_smul]
  have hd := hfx.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hm (by simp)
  have hd' : deriv (fun z : ℂ => f (x + z • v)) 0 = fderiv ℂ f x v := hd.deriv
  rw [iteratedDeriv_one, hd'] at hder
  exact hder.trans_eq (by norm_num; ring)

theorem second_fderiv_bound {f : E → F} {R C : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f (ball 0 R))
    (hb : ∀ x ∈ ball 0 R, ‖f x‖ ≤ C)
    {x : E} (hx : ‖x‖ ≤ R / 4) :
    ‖fderiv ℂ (fderiv ℂ f) x‖ ≤ 8 * C / R ^ 2 := by
  have hf' : AnalyticOnNhd ℂ (fderiv ℂ f) (ball 0 (R / 2)) := by
    intro y hy
    exact (hf y (ball_subset_ball (by linarith only [hR]) hy)).fderiv
  have hb' : ∀ y ∈ ball (0 : E) (R / 2), ‖fderiv ℂ f y‖ ≤ 2 * C / R := by
    intro y hy
    exact fderiv_bound hR hC hf hb (le_of_lt (by simpa only [mem_ball, dist_zero_right] using hy))
  have h := fderiv_bound (half_pos hR) (by positivity : 0 ≤ 2 * C / R) hf' hb'
    (x := x) (by linarith only [hx])
  exact h.trans_eq (by ring)

theorem fderiv_sub_bound {f : E → F} {R C : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f (ball 0 R))
    (hb : ∀ x ∈ ball 0 R, ‖f x‖ ≤ C)
    {x y : E} (hx : ‖x‖ ≤ R / 4) (hy : ‖y‖ ≤ R / 4) :
    ‖fderiv ℂ f x - fderiv ℂ f y‖ ≤ (8 * C / R ^ 2) * ‖x - y‖ := by
  apply (convex_closedBall (0 : E) (R / 4)).norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℂ) (f := fderiv ℂ f) ?_ ?_
    (by simpa only [mem_closedBall, dist_zero_right] using hy)
    (by simpa only [mem_closedBall, dist_zero_right] using hx)
  · intro z hz
    have hz' : ‖z‖ ≤ R / 4 := by simpa only [mem_closedBall, dist_zero_right] using hz
    exact (hf z (by rw [mem_ball, dist_zero_right]; linarith only [hz', hR])).fderiv.differentiableAt
  · intro z hz
    exact second_fderiv_bound hR hC hf hb
      (by simpa only [mem_closedBall, dist_zero_right] using hz)

end Maxwell.Continuum.AnalyticBallBounds
