import Maxwell.Continuum.EvenTaylor

/-! A bounded even holomorphic function changes quadratically at its
center, with an explicit Cauchy-series bound. -/

noncomputable section

namespace Maxwell.Continuum.EvenTaylor

open Set Metric Filter
open scoped Topology

theorem quadratic_difference_bound {f : ℂ → ℂ} {R C : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball 0 R))
    (hC : ∀ z ∈ ball 0 R, ‖f z‖ ≤ C) (hR : 0 < R) (hC0 : 0 ≤ C)
    (heven : (fun z => f (-z)) =ᶠ[𝓝 0] f) {z : ℂ} (hz : ‖z‖ ≤ R / 2) :
    ‖f z - f 0‖ ≤ 2 * C / R^2 * ‖z‖^2 := by
  have hz' : ‖z‖ < R := by linarith
  have ha : 0 ≤ ‖z‖ / R := div_nonneg (norm_nonneg _) hR.le
  have ha' : ‖z‖ / R ≤ 1 / 2 := (div_le_iff₀ hR).mpr (by linarith)
  have hasq : (‖z‖ / R)^2 ≤ 1 / 4 := by nlinarith
  have har : (‖z‖ / R)^2 < 1 := by linarith
  have hbound (n : ℕ) : ‖coefficient f (2 * n) * z^(2*n)‖ ≤
      C * ((‖z‖ / R)^2)^n := by
    rw [norm_mul, norm_pow]
    calc
      _ ≤ (C / R^(2*n)) * ‖z‖^(2*n) :=
        mul_le_mul_of_nonneg_right (coefficient_norm_le hf hC hR _) (by positivity)
      _ = _ := by rw [← pow_mul, div_pow]; ring
  have hb := norm_sub_le_of_geometric_bound_of_hasSum har hbound
    (hasSum_even_coefficients hf heven hz') 1
  have hpartial : (∑ n ∈ Finset.range 1, coefficient f (2*n) * z^(2*n)) = f 0 := by
    simp [coefficient, iteratedDeriv_zero]
  rw [hpartial, norm_sub_rev, pow_one] at hb
  have hden : 0 < 1 - (‖z‖ / R)^2 := by linarith
  have he : C * (‖z‖ / R)^2 / (1 - (‖z‖ / R)^2) ≤ 2 * C * (‖z‖ / R)^2 := by
    apply (div_le_iff₀ hden).mpr
    have hn : 0 ≤ C * (‖z‖ / R)^2 := mul_nonneg hC0 (sq_nonneg _)
    nlinarith
  exact (hb.trans he).trans_eq (by rw [div_pow]; ring)

end Maxwell.Continuum.EvenTaylor
