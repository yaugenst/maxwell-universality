import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Quantitative pointwise bounds for replacing the dispersion and finite
source numerator in the compressed resolvent integral. -/

namespace Maxwell.Defect

noncomputable def resolventDifference (ξ d : ℝ) : ℝ := ξ / (d * (d + ξ))

theorem resolventDifference_nonneg {ξ d : ℝ} (hξ : 0 ≤ ξ) (hd : 0 < d) :
    0 ≤ resolventDifference ξ d := by unfold resolventDifference; positivity

theorem resolventDifference_le {ξ d : ℝ} (hξ : 0 ≤ ξ) (hd : 0 < d) :
    resolventDifference ξ d ≤ ξ / d ^ 2 := by
  unfold resolventDifference
  apply div_le_div_of_nonneg_left hξ (sq_pos_of_pos hd)
  nlinarith

theorem resolventDifference_lipschitz {ξ d e s : ℝ}
    (hξ : 0 ≤ ξ) (hs : 0 < s) (hd : s ≤ d) (he : s ≤ e) :
    |resolventDifference ξ d - resolventDifference ξ e| ≤
      2 * ξ * |d - e| / s ^ 3 := by
  have hd0 : 0 < d := lt_of_lt_of_le hs hd
  have he0 : 0 < e := lt_of_lt_of_le hs he
  have hdx : 0 < d + ξ := by positivity
  have hex : 0 < e + ξ := by positivity
  have h1 : s ^ 3 ≤ d * e * (d + ξ) := by
    calc s ^ 3 = s * s * s := by ring
         _ ≤ d * e * (d + ξ) := by gcongr; linarith
  have h2 : s ^ 3 ≤ e * (d + ξ) * (e + ξ) := by
    calc s ^ 3 = s * s * s := by ring
         _ ≤ e * (d + ξ) * (e + ξ) := by gcongr <;> linarith
  have h1' : 1 / (d * e * (d + ξ)) ≤ 1 / s ^ 3 :=
    one_div_le_one_div_of_le (pow_pos hs 3) h1
  have h2' : 1 / (e * (d + ξ) * (e + ξ)) ≤ 1 / s ^ 3 :=
    one_div_le_one_div_of_le (pow_pos hs 3) h2
  have hid : resolventDifference ξ d - resolventDifference ξ e =
      ξ * (e - d) *
        (1 / (d * e * (d + ξ)) + 1 / (e * (d + ξ) * (e + ξ))) := by
    unfold resolventDifference
    field_simp
    ring
  have hsumpos : 0 ≤ 1 / (d * e * (d + ξ)) + 1 / (e * (d + ξ) * (e + ξ)) := by
    positivity
  rw [hid, abs_mul, abs_mul, abs_of_nonneg hξ, abs_of_nonneg hsumpos, abs_sub_comm e d]
  have hsum : 1 / (d * e * (d + ξ)) + 1 / (e * (d + ξ) * (e + ξ)) ≤ 2 / s ^ 3 := by
    calc
      _ ≤ 1 / s ^ 3 + 1 / s ^ 3 := add_le_add h1' h2'
      _ = 2 / s ^ 3 := by ring
  have := mul_le_mul_of_nonneg_left hsum (mul_nonneg hξ (abs_nonneg (d - e)))
  convert this using 1; ring

/-- A quartic dispersion remainder has an integrable three-dimensional
`1/r²` majorant after taking the resolvent difference. -/
theorem dispersion_replacement_bound {ξ d e c r M : ℝ}
    (hξ : 0 ≤ ξ) (hc : 0 < c) (hr : 0 < r)
    (hd : c * r ^ 2 ≤ d) (he : c * r ^ 2 ≤ e)
    (hquartic : |d - e| ≤ M * r ^ 4) :
    |resolventDifference ξ d - resolventDifference ξ e| ≤
      2 * M * ξ / (c ^ 3 * r ^ 2) := by
  have hs : 0 < c * r ^ 2 := by positivity
  apply (resolventDifference_lipschitz hξ hs hd he).trans
  calc
    2 * ξ * |d - e| / (c * r ^ 2) ^ 3 ≤
        2 * ξ * (M * r ^ 4) / (c * r ^ 2) ^ 3 := by gcongr
    _ = 2 * M * ξ / (c ^ 3 * r ^ 2) := by field_simp

/-- The even numerator's quadratic Taylor remainder has the same locally
integrable majorant. -/
theorem numerator_replacement_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ξ d c r M : ℝ} {B W : F}
    (hξ : 0 ≤ ξ) (hc : 0 < c) (hr : 0 < r) (hM : 0 ≤ M)
    (hd : c * r ^ 2 ≤ d) (hquadratic : ‖B - W‖ ≤ M * r ^ 2) :
    ‖resolventDifference ξ d • (B - W)‖ ≤ M * ξ / (c ^ 2 * r ^ 2) := by
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hd
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (resolventDifference_nonneg hξ hd0)]
  calc
    resolventDifference ξ d * ‖B - W‖ ≤ (ξ / d ^ 2) * (M * r ^ 2) := by
      gcongr
      exact resolventDifference_le hξ hd0
    _ ≤ (ξ / (c * r ^ 2) ^ 2) * (M * r ^ 2) := by gcongr
    _ = M * ξ / (c ^ 2 * r ^ 2) := by field_simp

/-- Uniformly separated positive and negative bands both vary linearly
under the positive operating shift. -/
theorem separated_reciprocal_difference_bound {d ξ g : ℝ}
    (hg : 0 < g) (hξ : 0 ≤ ξ) (hsmall : ξ ≤ g / 2) (hd : g ≤ |d|) :
    |(d + ξ)⁻¹ - d⁻¹| ≤ 2 * ξ / g ^ 2 := by
  have hdx : g / 2 ≤ |d + ξ| := by
    have ht := abs_add_le (d + ξ) (-ξ)
    simp only [add_neg_cancel_right, abs_neg, abs_of_nonneg hξ] at ht
    linarith
  have hd0 : d ≠ 0 := abs_pos.mp (lt_of_lt_of_le hg hd)
  have hdx0 : d + ξ ≠ 0 := abs_pos.mp (lt_of_lt_of_le (half_pos hg) hdx)
  have hid : (d + ξ)⁻¹ - d⁻¹ = -ξ / ((d + ξ) * d) := by
    field_simp
    ring
  rw [hid, abs_div, abs_neg, abs_of_nonneg hξ, abs_mul]
  calc
    ξ / (|d + ξ| * |d|) ≤ ξ / ((g / 2) * g) := by gcongr
    _ = 2 * ξ / g ^ 2 := by ring

end Maxwell.Defect
