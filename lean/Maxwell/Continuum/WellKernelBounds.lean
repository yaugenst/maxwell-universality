import Maxwell.Continuum.WellCoulomb

/-! Pointwise bounds for the literal heat-mixture Green function away from
its integrable diagonal singularity. -/

noncomputable section

namespace Maxwell.Continuum.Well

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

set_option backward.isDefEq.respectTransparency false

theorem gaussian_heat_factor (a : ℝ≥0) (t x : ℝ) (ht : 0 < t) :
    gaussianPDFReal 0 (2 * t.toNNReal * a) x =
      (Real.sqrt (4 * Real.pi * (a : ℝ)))⁻¹ * (Real.sqrt t)⁻¹ *
        Real.exp (-(x ^ 2 / (4 * (a : ℝ))) / t) := by
  unfold gaussianPDFReal
  simp only [sub_zero, NNReal.coe_mul, NNReal.coe_ofNat, Real.coe_toNNReal t ht.le]
  have hroot : 2 * Real.pi * (2 * t * (a : ℝ)) = (4 * Real.pi * (a : ℝ)) * t := by ring
  rw [hroot, Real.sqrt_mul (by positivity : 0 ≤ 4 * Real.pi * (a : ℝ)), mul_inv_rev]
  congr 1
  · ring
  · congr 1
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem heatKernel_literal (a : Fin 3 → ℝ≥0) (t : ℝ) (ht : 0 < t) (x : Space) :
    heatKernel a t x = heatPrefactor a * inverseTimeGaussian (heatRadiusSq a x) t := by
  have hp : (Real.sqrt t)⁻¹ ^ 3 = t ^ (-3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ht.le, ← Real.rpow_natCast,
      ← Real.rpow_mul ht.le]
    norm_num
  unfold heatKernel gaussianProduct
  simp_rw [gaussian_heat_factor _ t _ ht]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, hp, ← Real.exp_sum]
  unfold heatPrefactor inverseTimeGaussian heatRadiusSq
  rw [mul_assoc]
  congr 2
  congr 1
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

theorem heatMixture_pointwise_bound (a : Fin 3 → ℝ≥0) (t : ℝ) (ht : 0 < t) (x : Space) :
    Real.exp (-t) * heatKernel a t x ≤
      heatPrefactor a * inverseTimeGaussian (heatRadiusSq a x) t := by
  rw [heatKernel_literal a t ht x]
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  exact (mul_le_mul_of_nonneg_right he (mul_nonneg (heatPrefactor_nonneg a)
    (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le))).trans_eq (one_mul _)

theorem heatMixture_pointwise_integrable (a : Fin 3 → ℝ≥0) (ha : ∀ i, a i ≠ 0)
    (x : Space) (hx : x ≠ 0) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * heatKernel a t x) (Ioi 0) := by
  have hg := (inverseTimeGaussian_integrable (heatRadiusSq a x)
    (heatRadiusSq_pos a ha x hx)).const_mul (heatPrefactor a)
  apply hg.mono'
  · have hm : Measurable (fun t : ℝ => heatKernel a t x) := by
      unfold heatKernel gaussianProduct
      fun_prop
    exact ((Real.measurable_exp.comp measurable_neg).mul hm).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (heatKernel_nonneg a t x))]
    exact heatMixture_pointwise_bound a t ht x

theorem resolventKernel_coulomb_bound (a : Fin 3 → ℝ≥0) (ha : ∀ i, a i ≠ 0)
    (x : Space) (hx : x ≠ 0) :
    resolventKernel a x ≤ heatPrefactor a *
      (Real.sqrt Real.pi / Real.sqrt (heatRadiusSq a x)) := by
  have hg := (inverseTimeGaussian_integrable (heatRadiusSq a x)
    (heatRadiusSq_pos a ha x hx)).const_mul (heatPrefactor a)
  have h := integral_mono_ae (heatMixture_pointwise_integrable a ha x hx) hg
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact heatMixture_pointwise_bound a t ht x)
  rw [integral_const_mul, inverseTimeGaussian_integral _ (heatRadiusSq_pos a ha x hx)] at h
  exact h

end Maxwell.Continuum.Well
