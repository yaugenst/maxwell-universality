import Maxwell.Continuum.PeriodicPoleDivisionBound

/-! All longitudinal derivatives of the actual regular divided part.
The fixed small chart contributes an explicit power per derivative, so
the integration-by-parts constants stay inside the symbolic ledger. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric

attribute [local irreducible] selectedRegularPart transversePole imaginaryPole

theorem selectedRegularPart_iteratedDeriv {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius)
    {u : ℂ} (hu : ‖u‖ ≤ longitudinalPoleRadius / 8) (n : ℕ) :
    ‖iteratedDeriv n (selectedRegularPart D hh j w) u‖ ≤
      (n.factorial : ℝ) * (2 : ℝ)^(1091 + 1027 * n) := by
  have hmap {v : ℂ} (hv : v ∈ closedBall 0 (longitudinalPoleRadius / 4)) :
      ‖v‖ ≤ longitudinalPoleRadius / 4 := by
    simpa only [mem_closedBall, dist_zero_right] using hv
  have ha : AnalyticOnNhd ℂ (selectedRegularPart D hh j w) (closedBall 0 (longitudinalPoleRadius / 4)) := by
    intro v hv
    apply selectedRegularPart_analytic D hh j hw
    exact (hmap hv).trans (by linarith only [pole_radii.1])
  have he := CauchyBounds.norm_iteratedDeriv_le n ha
    (fun v hv => selectedRegularPart_bound D hh j hw (hmap hv))
    (r := longitudinalPoleRadius / 8) (c := u)
    (div_pos pole_radii.1 (by norm_num)) (by linarith only [hu])
  have hinv : (longitudinalPoleRadius / 8)⁻¹ = (2 : ℝ)^1027 := by norm_num [longitudinalPoleRadius]
  apply he.trans_eq
  rw [div_eq_mul_inv, ← inv_pow, hinv, ← pow_mul, mul_assoc, ← pow_add]

#print axioms selectedRegularPart_iteratedDeriv

end Maxwell.Continuum.PeriodicBand
