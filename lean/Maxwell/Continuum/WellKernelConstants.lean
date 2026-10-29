import Maxwell.Continuum.WellKernelEstimates
import Mathlib.Analysis.Real.Pi.Bounds

/-! The explicit prefactor estimates needed for the manuscript's fixed
ellipticity interval. -/

noncomputable section

namespace Maxwell.Continuum.Well

open scoped NNReal

theorem heatPrefactor_weighted_upper (a : Fin 3 → ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ)
    (hal : ∀ i, (2 * ρ)⁻¹ ≤ (a i : ℝ)) :
    heatPrefactor a * Real.sqrt Real.pi ≤ ρ * Real.sqrt ρ / 8 := by
  have hb : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hC := heatPrefactor_upper a ((2 * ρ)⁻¹) (by positivity) hal
  have he : 4 * Real.pi * (2 * ρ)⁻¹ = 2 * Real.pi / ρ := by field_simp; ring
  rw [he, Real.sqrt_div (by positivity), inv_div, div_pow] at hC
  have hCmul := (le_div_iff₀ (pow_pos hb 3)).mp hC
  have hroot : (4 / 3 : ℝ) * Real.sqrt Real.pi ≤ Real.sqrt (2 * Real.pi) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le, Real.sq_sqrt (by positivity)]
    nlinarith [Real.pi_pos]
  have hcube : 8 * Real.sqrt Real.pi ≤ Real.sqrt (2 * Real.pi) ^ 3 := by
    calc
      _ ≤ (2 * Real.pi) * ((4 / 3 : ℝ) * Real.sqrt Real.pi) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) (Real.sqrt_nonneg Real.pi)]
      _ ≤ (2 * Real.pi) * Real.sqrt (2 * Real.pi) :=
        mul_le_mul_of_nonneg_left hroot (by positivity)
      _ = _ := by rw [pow_succ, Real.sq_sqrt (by positivity)]
  have hbound : 8 * (heatPrefactor a * Real.sqrt Real.pi) ≤ Real.sqrt ρ ^ 3 := by
    calc
      _ = heatPrefactor a * (8 * Real.sqrt Real.pi) := by ring
      _ ≤ heatPrefactor a * Real.sqrt (2 * Real.pi) ^ 3 :=
        mul_le_mul_of_nonneg_left hcube (heatPrefactor_nonneg a)
      _ ≤ _ := hCmul
  rw [pow_succ, Real.sq_sqrt hρ.le] at hbound
  linarith

theorem heatPrefactor_numeric_lower (a : Fin 3 → ℝ≥0) (ha : ∀ i, a i ≠ 0)
    (ρ : ℝ) (hρ : 0 < ρ) (hau : ∀ i, (a i : ℝ) ≤ 256 / ρ) :
    Real.sqrt ρ ^ 3 / (2 : ℝ) ^ 18 ≤ heatPrefactor a := by
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hC := heatPrefactor_lower a ha (256 / ρ) (by positivity) hau
  have he : 4 * Real.pi * (256 / ρ) = (1024 * Real.pi) / ρ := by ring
  rw [he, Real.sqrt_div (by positivity)] at hC
  have hroot : Real.sqrt (1024 * Real.pi) ≤ 64 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · nlinarith [Real.pi_lt_four]
  have hinv : Real.sqrt ρ / 64 ≤ (Real.sqrt (1024 * Real.pi) / Real.sqrt ρ)⁻¹ := by
    rw [inv_div]
    exact div_le_div_of_nonneg_left hs.le (by positivity) hroot
  calc
    _ = (Real.sqrt ρ / 64) ^ 3 := by ring
    _ ≤ (Real.sqrt (1024 * Real.pi) / Real.sqrt ρ)⁻¹ ^ 3 :=
      pow_le_pow_left₀ (by positivity) hinv 3
    _ ≤ _ := hC

theorem resolventKernel_quantitative_upper (a : Fin 3 → ℝ≥0) (ha : ∀ i, a i ≠ 0)
    (ρ : ℝ) (hρ : 0 < ρ) (hal : ∀ i, (2 * ρ)⁻¹ ≤ (a i : ℝ))
    (hau : ∀ i, (a i : ℝ) ≤ 256 / ρ) (x : Space) (hx : x ≠ 0) :
    resolventKernel a x ≤ 4 * ρ / ‖x‖ := by
  have h := resolventKernel_norm_bound a ha (256 / ρ) (by positivity) hau x hx
  have hC := heatPrefactor_weighted_upper a ρ hρ hal
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hroot : Real.sqrt (256 / ρ) = 16 / Real.sqrt ρ := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 256)]
    congr 1
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
    norm_num
  apply h.trans
  apply div_le_div_of_nonneg_right _ (norm_nonneg x)
  rw [hroot]
  calc
    _ = (heatPrefactor a * Real.sqrt Real.pi) * (32 / Real.sqrt ρ) := by ring
    _ ≤ (ρ * Real.sqrt ρ / 8) * (32 / Real.sqrt ρ) :=
      mul_le_mul_of_nonneg_right hC (by positivity)
    _ = 4 * ρ := by field_simp; ring

end Maxwell.Continuum.Well
