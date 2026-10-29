import Maxwell.Continuum.CauchyLipschitz

/-! A local Lipschitz estimate at the center of a complex Banach-space
ball, obtained by restricting the actual map to a complex line. -/

noncomputable section

namespace Maxwell.Continuum.CauchyBounds

open Set Metric

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem bounded_map_sub_zero_le {f : E → F} {R C : ℝ}
    (hR : 0 < R) (hC0 : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hC : ∀ z ∈ closedBall 0 R, ‖f z‖ ≤ C)
    {x : E} (hx : ‖x‖ ≤ R / 2) :
    ‖f x - f 0‖ ≤ (2 * C / R) * ‖x‖ := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let v : E := (‖x‖ : ℂ)⁻¹ • x
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hn, inv_mul_cancel₀ hn.ne']
  have hline (z : ℂ) (hz : z ∈ closedBall 0 R) : z • v ∈ closedBall 0 R := by
    simpa only [mem_closedBall, dist_zero_right, norm_smul, hv, mul_one] using hz
  have han : AnalyticOnNhd ℂ (fun z : ℂ => f (z • v)) (closedBall 0 R) := by
    intro z hz
    exact AnalyticAt.comp (f := fun z : ℂ => z • v)
      (hf (z • v) (hline z hz)) (analyticAt_id.smul analyticAt_const)
  have hb : ∀ z ∈ closedBall (0 : ℂ) R, ‖f (z • v)‖ ≤ C :=
    fun z hz => hC _ (hline z hz)
  have hc : (‖x‖ : ℂ) ∈ closedBall 0 (R / 2) := by
    simpa only [mem_closedBall, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hn] using hx
  have hzero : (0 : ℂ) ∈ closedBall 0 (R / 2) := by
    simp only [mem_closedBall, dist_self]
    positivity
  have h := bounded_curve_sub_le hR hC0 han hb hc hzero
  have he : (‖x‖ : ℂ) • v = x := by
    dsimp only [v]
    rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
  simpa only [he, zero_smul, sub_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hn] using h

end Maxwell.Continuum.CauchyBounds
