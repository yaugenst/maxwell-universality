import Maxwell.Continuum.CauchyBounds

/-! A dimension-free local Lipschitz bound for bounded holomorphic curves. -/

noncomputable section

namespace Maxwell.Continuum.CauchyBounds

open Set Metric

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem bounded_curve_sub_le {f : ℂ → F} {R C : ℝ}
    (hR : 0 < R) (hC0 : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hC : ∀ z ∈ closedBall 0 R, ‖f z‖ ≤ C)
    {c d : ℂ} (hc : c ∈ closedBall 0 (R / 2)) (hd : d ∈ closedBall 0 (R / 2)) :
    ‖f c - f d‖ ≤ (2 * C / R) * ‖c - d‖ := by
  let K : NNReal := ⟨2 * C / R, by positivity⟩
  have hsub : closedBall (0 : ℂ) (R / 2) ⊆ closedBall 0 R :=
    closedBall_subset_closedBall (by linarith)
  have hLip : LipschitzOnWith K f (closedBall 0 (R / 2)) := by
    apply (convex_closedBall (0 : ℂ) (R / 2)).lipschitzOnWith_of_nnnorm_deriv_le
    · intro z hz
      exact (hf z (hsub hz)).differentiableAt
    · intro z hz
      have hz' : ‖z‖ ≤ R / 2 := by simpa only [mem_closedBall, dist_zero_right] using hz
      have h := norm_deriv_le hf hC (c := z) (r := R / 2) (by positivity) (by linarith)
      change ‖deriv f z‖ ≤ 2 * C / R
      convert h using 1
      ring
  have hK : (K : ℝ) = 2 * C / R := rfl
  have hdist := hLip.dist_le_mul c hc d hd
  rw [hK] at hdist
  simpa only [dist_eq_norm] using hdist

end Maxwell.Continuum.CauchyBounds
