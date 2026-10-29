import Maxwell.Continuum.WellHeatKernel
import Mathlib.MeasureTheory.Integral.Gamma

/-! The inverse-time Gaussian integral controlling the singularity of the
actual Green kernel. Its `1/r` bound is derived by change of variables. -/

noncomputable section

namespace Maxwell.Continuum.Well

open MeasureTheory Set
open scoped NNReal

def inverseTimeGaussian (c t : ℝ) : ℝ :=
  t ^ (-3 / 2 : ℝ) * Real.exp (-c / t)

theorem inverseTimeGaussian_change (c t : ℝ) (ht : 0 < t) :
    (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) • inverseTimeGaussian c (t ^ (-1 : ℝ)) =
      t ^ (-1 / 2 : ℝ) * Real.exp (-c * t) := by
  simp only [inverseTimeGaussian, abs_neg, abs_one, one_mul, smul_eq_mul]
  rw [← Real.rpow_mul ht.le]
  rw [← mul_assoc, ← Real.rpow_add ht]
  norm_num only [show (-1 : ℝ) * (-3 / 2) = 3 / 2 by norm_num,
    show ((-1 : ℝ) - 1) + (-1) * (-3 / 2) = -1 / 2 by norm_num]
  rw [Real.rpow_neg_one, div_inv_eq_mul]

theorem inverseTimeGaussian_integrable (c : ℝ) (hc : 0 < c) :
    IntegrableOn (inverseTimeGaussian c) (Ioi 0) := by
  apply (integrableOn_Ioi_comp_rpow_iff (inverseTimeGaussian c) (p := (-1 : ℝ))
    (by norm_num)).mp
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ))
    (s := (-1 / 2 : ℝ)) (b := c) (by norm_num) (by norm_num) hc
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [inverseTimeGaussian_change c t ht, Real.rpow_one]

theorem inverseTimeGaussian_integral (c : ℝ) (hc : 0 < c) :
    (∫ t : ℝ in Ioi 0, inverseTimeGaussian c t) = Real.sqrt Real.pi / Real.sqrt c := by
  rw [← integral_comp_rpow_Ioi (inverseTimeGaussian c) (p := (-1 : ℝ)) (by norm_num)]
  have he : (fun t : ℝ => (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) •
      inverseTimeGaussian c (t ^ (-1 : ℝ))) =ᵐ[volume.restrict (Ioi 0)]
      fun t => t ^ (-1 / 2 : ℝ) * Real.exp (-c * t ^ (1 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [inverseTimeGaussian_change c t ht, Real.rpow_one]
  rw [integral_congr_ae he, integral_rpow_mul_exp_neg_mul_rpow
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (-1 : ℝ) < -1 / 2) hc]
  norm_num only [show -((-1 / 2 : ℝ) + 1) / 1 = -(1 / 2 : ℝ) by norm_num,
    show ((-1 / 2 : ℝ) + 1) / 1 = (1 / 2 : ℝ) by norm_num, one_div_one, mul_one]
  rw [Real.Gamma_one_half_eq, Real.rpow_neg hc.le, ← Real.sqrt_eq_rpow]
  ring

def heatPrefactor (a : Fin 3 → ℝ≥0) : ℝ :=
  ∏ i : Fin 3, (Real.sqrt (4 * Real.pi * (a i : ℝ)))⁻¹

def heatRadiusSq (a : Fin 3 → ℝ≥0) (x : Space) : ℝ :=
  ∑ i : Fin 3, (x i) ^ 2 / (4 * (a i : ℝ))

theorem heatPrefactor_nonneg (a : Fin 3 → ℝ≥0) : 0 ≤ heatPrefactor a := by
  apply Finset.prod_nonneg
  intro i _
  positivity

theorem heatPrefactor_pos (a : Fin 3 → ℝ≥0) (ha : ∀ i, a i ≠ 0) :
    0 < heatPrefactor a := by
  apply Finset.prod_pos
  intro i _
  have hi : 0 < (a i : ℝ) := (NNReal.coe_pos).mpr (pos_iff_ne_zero.mpr (ha i))
  positivity

theorem heatRadiusSq_nonneg (a : Fin 3 → ℝ≥0) (x : Space) :
    0 ≤ heatRadiusSq a x := by
  apply Finset.sum_nonneg
  intro i _
  positivity

theorem heatRadiusSq_pos (a : Fin 3 → ℝ≥0) (ha : ∀ i, a i ≠ 0)
    (x : Space) (hx : x ≠ 0) : 0 < heatRadiusSq a x := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    apply PiLp.ext
    intro i
    exact h i
  apply Finset.sum_pos'
  · intro j _
    positivity
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    have hpos : 0 < (a i : ℝ) := (NNReal.coe_pos).mpr (pos_iff_ne_zero.mpr (ha i))
    exact div_pos (sq_pos_of_ne_zero hi) (mul_pos (by norm_num) hpos)

end Maxwell.Continuum.Well
