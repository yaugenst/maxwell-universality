import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Maxwell.Defect.Radial

/-! Finite coherent-source estimates and extraction of an edge-overlapping
large spectral component from its weighted Rayleigh sum. -/

namespace Maxwell.Defect

open MeasureTheory

theorem weighted_source_norm_le {ι : Type*} [Fintype ι]
    (W v : ι → ℝ) (hW : ∀ i, 0 ≤ W i ∧ W i ≤ 1) :
    ∑ i, (W i * v i) ^ 2 ≤ ∑ i, W i * v i ^ 2 := by
  apply Finset.sum_le_sum
  intro i _
  have hWi := hW i
  have hsq : W i ^ 2 ≤ W i := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg (v i))]

/-- The constants chosen in the paper leave ample room for the coherent
overlap throughout the shrinking momentum ball. -/
theorem coherent_overlap_lower {amplitude : ℂ} {a L q r C : ℝ}
    (hL : 8 ≤ L) (ha : L ^ 3 ≤ a) (hq : 0 ≤ q)
    (hr : 0 ≤ r) (hC : 0 ≤ C) (hqr : q ≤ r / L)
    (hrsmall : r ≤ 1 / 64) (hrC : r ≤ 1 / (64 * (1 + C)))
    (herror : ‖amplitude - (a : ℂ)‖ ≤ 4 * L * q * a + 8 * C * L ^ 3 * q) :
    a / 2 ≤ ‖amplitude‖ := by
  have hLpos : 0 < L := by linarith
  have ha0 : 0 ≤ a := le_trans (pow_nonneg hLpos.le 3) ha
  have hLq : L * q ≤ r := by
    have := (le_div_iff₀ hLpos).mp hqr
    nlinarith
  have hqsmall : q ≤ r / 8 := by nlinarith
  have hCr : C * r ≤ 1 / 64 := by
    have hd : 0 < 64 * (1 + C) := by positivity
    have := (le_div_iff₀ hd).mp hrC
    nlinarith
  have hfirst : 4 * L * q * a ≤ a / 16 := by
    have := mul_le_mul_of_nonneg_right hLq ha0
    have := mul_le_mul_of_nonneg_right hrsmall ha0
    nlinarith
  have hsecond : 8 * C * L ^ 3 * q ≤ a / 64 := by
    have hCa : C * L ^ 3 ≤ C * a := mul_le_mul_of_nonneg_left ha hC
    have h1 := mul_le_mul_of_nonneg_right hCa hq
    have h2 := mul_le_mul_of_nonneg_left hqsmall (mul_nonneg hC ha0)
    have h3 := mul_le_mul_of_nonneg_right hCr ha0
    nlinarith
  have htriangle := norm_le_norm_add_norm_sub amplitude (a : ℂ)
  have hnorm : ‖(a : ℂ)‖ = a := by simp [Complex.norm_real, abs_of_nonneg ha0]
  rw [hnorm] at htriangle
  linarith

theorem pi_sq_lt_ten : Real.pi ^ 2 < 10 := by
  have hp := Real.pi_pos
  have hbound := Real.pi_lt_d2
  nlinarith

/-- The rational cube-growth coefficient is dominated by the exact radial
coefficient. -/
theorem rational_cube_coefficient_le {r d : ℝ} (hr : 0 < r) (hd : 0 < d) :
    0 < r / (80 * d) ∧ r / (80 * d) ≤ r / (8 * Real.pi ^ 2 * d) := by
  have hden : 0 < 8 * Real.pi ^ 2 * d := by positivity
  refine ⟨by positivity, ?_⟩
  apply (div_le_div_iff₀ (by positivity : 0 < 80 * d) hden).mpr
  have := mul_le_mul_of_nonneg_right pi_sq_lt_ten.le (mul_nonneg hr.le hd.le)
  nlinarith

theorem exists_cube_above_threshold {c B T : ℝ} (hc : 0 < c) :
    ∃ L : ℕ, 8 ≤ L ∧ T < c * (L : ℝ) ^ 2 - B := by
  obtain ⟨L, hL⟩ := exists_nat_gt (max 8 ((|T + B| + 1) / c))
  have hL8 : (8 : ℝ) < L := lt_of_le_of_lt (le_max_left _ _) hL
  have hLg : (|T + B| + 1) / c < L := lt_of_le_of_lt (le_max_right _ _) hL
  have hmul : |T + B| + 1 < (L : ℝ) * c := (div_lt_iff₀ hc).mp hLg
  have hsq : (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  have hgrow := mul_le_mul_of_nonneg_left hsq hc.le
  refine ⟨L, ?_, ?_⟩
  · have : (8 : ℝ) ≤ L := hL8.le
    exact_mod_cast this
  · have := le_abs_self (T + B)
    nlinarith

/-- A Rayleigh quotient above a threshold has a nonzero spectral weight
above that threshold. Zero weights cannot supply the witness. -/
theorem spectral_weight_above_threshold {ι : Type*} [Fintype ι]
    (eigenvalue weight : ι → ℝ) (threshold : ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hRayleigh : threshold * ∑ i, weight i < ∑ i, eigenvalue i * weight i) :
    ∃ i, threshold < eigenvalue i ∧ weight i ≠ 0 := by
  by_contra hnone
  have hterm : ∀ i, eigenvalue i * weight i ≤ threshold * weight i := by
    intro i
    by_cases hz : weight i = 0
    · simp [hz]
    · have he : eigenvalue i ≤ threshold := by
        by_contra hnle
        exact hnone ⟨i, lt_of_not_ge hnle, hz⟩
      exact mul_le_mul_of_nonneg_right he (hweight i)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  rw [← Finset.mul_sum] at hsum
  linarith

/-- The coherent momentum ball contributes the exact lower bound in the
paper, with normalized Bloch measure and no numerical quadrature. -/
theorem coherent_ball_integral_lower
    (amplitude : EuclideanSpace ℝ (Fin 3) → ℂ)
    (dispersion : EuclideanSpace ℝ (Fin 3) → ℝ)
    {a radius dmax : ℝ} (ha : 0 ≤ a) (hR : 0 < radius) (hdmax : 0 < dmax)
    (hint : IntegrableOn (fun q => ‖amplitude q‖ ^ 2 / dispersion q)
      (Metric.ball 0 radius))
    (hamp : ∀ q ∈ Metric.ball 0 radius, q ≠ 0 → a / 2 ≤ ‖amplitude q‖)
    (hd : ∀ q ∈ Metric.ball 0 radius, q ≠ 0 →
      0 < dispersion q ∧ dispersion q ≤ dmax * ‖q‖ ^ 2) :
    a ^ 2 * radius / (8 * Real.pi ^ 2 * dmax) ≤
      (∫ q in Metric.ball 0 radius, ‖amplitude q‖ ^ 2 / dispersion q) /
        (2 * Real.pi) ^ 3 := by
  have hminor := (inverse_square_integrable_ball radius).const_mul (a ^ 2 / (4 * dmax))
  have hne : ∀ᵐ q : EuclideanSpace ℝ (Fin 3), q ≠ 0 := by simp [ae_iff]
  have hi := integral_mono_ae hminor hint (by
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hne] with q hq hq0
    have hr : 0 < ‖q‖ := norm_pos_iff.mpr hq0
    have hdq := hd q hq hq0
    have haq := hamp q hq hq0
    have hsquare : (a / 2) ^ 2 ≤ ‖amplitude q‖ ^ 2 := by nlinarith
    calc
      a ^ 2 / (4 * dmax) * (1 / ‖q‖ ^ 2) =
          (a / 2) ^ 2 / (dmax * ‖q‖ ^ 2) := by ring
      _ ≤ ‖amplitude q‖ ^ 2 / dispersion q := by
        gcongr
        · exact hdq.1
        · exact hdq.2)
  rw [integral_const_mul, inverse_square_ball_integral hR] at hi
  have hscaled := div_le_div_of_nonneg_right hi
    (by positivity : 0 ≤ (2 * Real.pi) ^ 3)
  convert hscaled using 1; field_simp; ring

/-- Combining the positive coherent contribution with the lower-band gap
gives the quadratic-in-side-length Rayleigh quotient. -/
theorem coherent_cube_rayleigh_lower {a L r d g quadratic : ℝ}
    (hL : 0 < L) (ha : L ^ 3 ≤ a) (hr : 0 < r) (hd : 0 < d) (hg : 0 < g)
    (hquadratic : a ^ 2 * r / (8 * Real.pi ^ 2 * d * L) - a / g ≤ quadratic) :
    (r / (80 * d)) * L ^ 2 - 1 / g ≤ quadratic / a := by
  have ha0 : 0 < a := lt_of_lt_of_le (pow_pos hL 3) ha
  have hcoeff := (rational_cube_coefficient_le hr hd).2
  calc
    (r / (80 * d)) * L ^ 2 - 1 / g ≤
        (r / (8 * Real.pi ^ 2 * d)) * L ^ 2 - 1 / g := by gcongr
    _ = L ^ 3 * r / (8 * Real.pi ^ 2 * d * L) - 1 / g := by field_simp
    _ ≤ a * r / (8 * Real.pi ^ 2 * d * L) - 1 / g := by gcongr
    _ = (a ^ 2 * r / (8 * Real.pi ^ 2 * d * L) - a / g) / a := by field_simp
    _ ≤ quadratic / a := div_le_div_of_nonneg_right hquadratic ha0.le

end Maxwell.Defect
