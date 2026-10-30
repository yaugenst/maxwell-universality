import Maxwell.Continuum.AnalyticBallTaylor

/-! Uniformly bounded actual holomorphic line restrictions imply a local
Lipschitz bound. This avoids imposing unproved joint regularity on parameter
dependent integrals. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.AnalyticLineLipschitz

open Set Metric
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem norm_sub_le {f : E → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ a v : E, AnalyticOnNhd ℂ (fun ζ : ℂ => f (a + ζ • v))
      {ζ | ‖a + ζ • v‖ < 1})
    (hb : ∀ x : E, ‖x‖ < 1 → ‖f x‖ ≤ C)
    {x y : E} (hx : ‖x‖ ≤ 1 / 8) (hy : ‖y‖ ≤ 1 / 8) :
    ‖f y - f x‖ ≤ 4 * C * ‖y - x‖ := by
  by_cases he : y = x
  · subst y
    simp only [sub_self, norm_zero, mul_zero, le_refl]
  have hd : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  have hdb : ‖y - x‖ ≤ 1 / 4 := (_root_.norm_sub_le y x).trans (by linarith only [hx, hy])
  have hmap {ζ : ℂ} (hζ : ζ ∈ ball 0 (1 / (2 * ‖y - x‖))) :
      ‖x + ζ • (y - x)‖ < 1 := by
    have hζ' : ‖ζ‖ < 1 / (2 * ‖y - x‖) := by simpa only [mem_ball, dist_zero_right] using hζ
    have hm := (lt_div_iff₀ (by positivity : 0 < 2 * ‖y - x‖)).mp hζ'
    have hn := norm_add_le x (ζ • (y - x))
    rw [norm_smul] at hn
    nlinarith only [hn, hx, hm]
  have hag : AnalyticOnNhd ℂ (fun ζ : ℂ => f (x + ζ • (y - x)))
      (ball 0 (1 / (2 * ‖y - x‖))) := fun ζ hζ => ha x (y - x) ζ (hmap hζ)
  have h := AnalyticBallBounds.scalar_tail_half (by positivity : 0 < 1 / (2 * ‖y - x‖))
    hC hag (fun ζ hζ => hb _ (hmap hζ)) (z := 1)
    (by rw [norm_one]; apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr;
        apply (le_div_iff₀ (by positivity : 0 < 2 * ‖y - x‖)).mpr;
        linarith only [hdb]) 1
  simp only [Finset.sum_range_one, EvenTaylor.coefficient, Nat.factorial_zero,
    Nat.cast_one, inv_one, iteratedDeriv_zero, zero_smul, add_zero, one_mul,
    mul_one, one_smul, add_sub_cancel, norm_one, one_pow, pow_one] at h
  exact h.trans_eq (by field_simp; ring)

theorem lipschitzOn {f : E → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ a v : E, AnalyticOnNhd ℂ (fun ζ : ℂ => f (a + ζ • v))
      {ζ | ‖a + ζ • v‖ < 1})
    (hb : ∀ x : E, ‖x‖ < 1 → ‖f x‖ ≤ C) :
    LipschitzOnWith ⟨4 * C, by positivity⟩ f (closedBall 0 (1 / 8)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simp only [dist_eq_norm]
  convert! norm_sub_le hC ha hb
    (by simpa only [mem_closedBall, dist_zero_right] using hy)
    (by simpa only [mem_closedBall, dist_zero_right] using hx)

end Maxwell.Continuum.AnalyticLineLipschitz
