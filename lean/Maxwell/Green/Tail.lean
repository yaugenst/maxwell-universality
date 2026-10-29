import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Two-dimensional Gaussian normalization and exponentially small cutoff tails.
The complex plane carries its standard two-dimensional Lebesgue volume. -/

namespace Maxwell.Green

open MeasureTheory Filter
open scoped Topology

/-- Exact normalization of the radial Gaussian in two real dimensions. -/
theorem integral_radial_gaussian (b : ℝ) (hb : 0 < b) :
    (∫ w : ℂ, Real.exp (-b * ‖w‖ ^ 2)) = Real.pi / b := by
  have h := Complex.integral_exp_neg_mul_rpow (p := 2) (by norm_num) hb
  have hg : Real.Gamma (2 : ℝ) = 1 := by
    simp
  norm_num [Real.rpow_two, Real.rpow_neg_one, hg] at h
  simpa only [div_eq_mul_inv, neg_mul] using h

theorem integrable_radial_gaussian (b : ℝ) (hb : 0 < b) :
    Integrable (fun w : ℂ => Real.exp (-b * ‖w‖ ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_radial_gaussian b hb]
  exact (div_pos Real.pi_pos hb).ne'

/-- Half of the Gaussian exponent pays for the removed disk, while the other
half remains as an integrable majorant. -/
theorem radial_gaussian_tail_split (b δ : ℝ) (hb : 0 ≤ b) (hδ : 0 ≤ δ)
    (w : ℂ) (hw : δ ≤ ‖w‖) :
    Real.exp (-b * ‖w‖ ^ 2) ≤
      Real.exp (-b * δ ^ 2 / 2) * Real.exp (-(b / 2) * ‖w‖ ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs : δ ^ 2 ≤ ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  nlinarith [mul_le_mul_of_nonneg_left hs hb]

/-- Pointwise majorant for a cutoff error that vanishes inside a disk. -/
theorem cutoff_tail_majorant (E : ℂ → ℂ) (K b δ : ℝ)
    (hK : 0 ≤ K) (hb : 0 ≤ b) (hδ : 0 ≤ δ)
    (hzero : ∀ w, ‖w‖ < δ → E w = 0)
    (hbound : ∀ w, ‖E w‖ ≤ K * Real.exp (-b * ‖w‖ ^ 2)) (w : ℂ) :
    ‖E w‖ ≤ (K * Real.exp (-b * δ ^ 2 / 2)) *
      Real.exp (-(b / 2) * ‖w‖ ^ 2) := by
  by_cases hw : ‖w‖ < δ
  · rw [hzero w hw, norm_zero]
    positivity
  · calc
      ‖E w‖ ≤ K * Real.exp (-b * ‖w‖ ^ 2) := hbound w
      _ ≤ K * (Real.exp (-b * δ ^ 2 / 2) * Real.exp (-(b / 2) * ‖w‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (radial_gaussian_tail_split b δ hb hδ w (le_of_not_gt hw)) hK
      _ = _ := by ring

/-- A measurable cutoff error satisfying the Gaussian bound is integrable. -/
theorem integrable_cutoff_tail (E : ℂ → ℂ) (K b δ : ℝ)
    (hE : AEStronglyMeasurable E) (hK : 0 ≤ K) (hb : 0 < b) (hδ : 0 ≤ δ)
    (hzero : ∀ w, ‖w‖ < δ → E w = 0)
    (hbound : ∀ w, ‖E w‖ ≤ K * Real.exp (-b * ‖w‖ ^ 2)) : Integrable E := by
  apply ((integrable_radial_gaussian (b / 2) (by positivity)).const_mul
    (K * Real.exp (-b * δ ^ 2 / 2))).mono' hE
  exact Filter.Eventually.of_forall (cutoff_tail_majorant E K b δ hK hb.le hδ hzero hbound)

/-- The absolute cutoff-tail integral is exponentially small, with the exact
two-dimensional Gaussian normalization. -/
theorem norm_integral_cutoff_tail (E : ℂ → ℂ) (K b δ : ℝ)
    (hK : 0 ≤ K) (hb : 0 < b) (hδ : 0 ≤ δ)
    (hzero : ∀ w, ‖w‖ < δ → E w = 0)
    (hbound : ∀ w, ‖E w‖ ≤ K * Real.exp (-b * ‖w‖ ^ 2)) :
    ‖∫ w : ℂ, E w‖ ≤ (2 * Real.pi * K / b) * Real.exp (-b * δ ^ 2 / 2) := by
  have hmaj := (integrable_radial_gaussian (b / 2) (by positivity)).const_mul
    (K * Real.exp (-b * δ ^ 2 / 2))
  have h := norm_integral_le_of_norm_le hmaj
    (Filter.Eventually.of_forall (cutoff_tail_majorant E K b δ hK hb.le hδ hzero hbound))
  rw [integral_const_mul, integral_radial_gaussian (b / 2) (by positivity)] at h
  convert h using 1
  ring

/-- The scale-explicit version used when the Gaussian exponent is `c T`. -/
theorem norm_integral_scaled_cutoff_tail (E : ℂ → ℂ) (K c T δ : ℝ)
    (hK : 0 ≤ K) (hc : 0 < c) (hT : 0 < T) (hδ : 0 ≤ δ)
    (hzero : ∀ w, ‖w‖ < δ → E w = 0)
    (hbound : ∀ w, ‖E w‖ ≤ K * Real.exp (-(c * T) * ‖w‖ ^ 2)) :
    ‖∫ w : ℂ, E w‖ ≤ (2 * Real.pi * K / (c * T)) *
      Real.exp (-(c * T) * δ ^ 2 / 2) :=
  norm_integral_cutoff_tail E K (c * T) δ hK (mul_pos hc hT) hδ hzero hbound

/-- An exponential tail divided by its Gaussian scale eventually beats any
prescribed inverse power, including the `T⁻³ᐟ²` remainder scale. -/
theorem eventually_exponential_over_linear_le_rpow (A k p : ℝ) (hk : 0 < k) :
    ∀ᶠ T : ℝ in atTop,
      (A / T) * Real.exp (-k * T) ≤ 1 / T ^ p := by
  have ht : Tendsto (fun T : ℝ => A * (T ^ (p - 1) * Real.exp (-k * T)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p - 1) k hk).const_mul A
  have he := ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with T h hT
  have hp : 0 < T ^ p := Real.rpow_pos_of_pos hT p
  have heq : T ^ p = T ^ (p - 1) * T := by
    calc
      T ^ p = T ^ ((p - 1) + 1) := by congr 1; ring
      _ = T ^ (p - 1) * T := by rw [Real.rpow_add hT, Real.rpow_one]
  apply (le_div_iff₀ hp).2
  calc
    (A / T) * Real.exp (-k * T) * T ^ p =
        A * (T ^ (p - 1) * Real.exp (-k * T)) := by
      rw [heq]
      field_simp
    _ ≤ 1 := h.le

/-- The two-dimensional cutoff-tail bound is eventually bounded by `T⁻³ᐟ²`
for every fixed positive cutoff radius and Gaussian coefficient. -/
theorem eventually_scaled_cutoff_tail_bound (K c δ : ℝ)
    (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop,
      (2 * Real.pi * K / (c * T)) * Real.exp (-(c * T) * δ ^ 2 / 2) ≤
        1 / T ^ ((3 : ℝ) / 2) := by
  have hk : 0 < c * δ ^ 2 / 2 := by positivity
  have he := eventually_exponential_over_linear_le_rpow
    (2 * Real.pi * K / c) (c * δ ^ 2 / 2) (3 / 2) hk
  filter_upwards [he] with T h
  have hex : -(c * T) * δ ^ 2 / 2 = -(c * δ ^ 2 / 2) * T := by ring
  rw [hex]
  simpa only [div_div] using h

/-- A whole scaled cutoff family has the required inverse-three-halves
integral remainder, with a single large-scale threshold. -/
theorem eventually_norm_integral_cutoff_family (E : ℝ → ℂ → ℂ) (K c δ : ℝ)
    (hK : 0 ≤ K) (hc : 0 < c) (hδ : 0 < δ)
    (hzero : ∀ T > 0, ∀ w, ‖w‖ < δ → E T w = 0)
    (hbound : ∀ T > 0, ∀ w, ‖E T w‖ ≤ K * Real.exp (-(c * T) * ‖w‖ ^ 2)) :
    ∀ᶠ T : ℝ in atTop,
      ‖∫ w : ℂ, E T w‖ ≤ 1 / T ^ ((3 : ℝ) / 2) := by
  filter_upwards [eventually_scaled_cutoff_tail_bound K c δ hc hδ,
    eventually_gt_atTop (0 : ℝ)] with T ht hT
  exact (norm_integral_scaled_cutoff_tail (E T) K c T δ hK hc hT hδ.le
    (hzero T hT) (hbound T hT)).trans ht

end Maxwell.Green
