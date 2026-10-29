import Maxwell.Continuum.WellGaussian
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The actual positive Gaussian mixture for the anisotropic resolvent. -/

noncomputable section

namespace Maxwell.Continuum.Well

open MeasureTheory ProbabilityTheory FourierTransform Set
open scoped NNReal

set_option backward.isDefEq.respectTransparency false

def diagonalTensor (a : Fin 3 → ℝ≥0) : Space →L[ℝ] Space :=
  (Matrix.diagonal (fun i => (a i : ℝ))).toEuclideanLin.toContinuousLinearMap

theorem diagonalTensor_apply (a : Fin 3 → ℝ≥0) (x : Space) (i : Fin 3) :
    diagonalTensor a x i = (a i : ℝ) * x i := by
  simp [diagonalTensor, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]

theorem diagonalTensor_inner (a : Fin 3 → ℝ≥0) (x : Space) :
    inner ℝ x (diagonalTensor a x) = ∑ i : Fin 3, (a i : ℝ) * (x i) ^ 2 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [diagonalTensor_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem diagonalTensor_nonneg (a : Fin 3 → ℝ≥0) (x : Space) :
    0 ≤ inner ℝ x (diagonalTensor a x) := by
  rw [diagonalTensor_inner]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (a i).coe_nonneg (sq_nonneg _))

def heatKernel (a : Fin 3 → ℝ≥0) (t : ℝ) (x : Space) : ℝ :=
  gaussianProduct (fun i => 2 * t.toNNReal * a i) x

theorem heatKernel_nonneg (a : Fin 3 → ℝ≥0) (t : ℝ) (x : Space) :
    0 ≤ heatKernel a t x := gaussianProduct_nonneg _ _

theorem heatKernel_pos (a : Fin 3 → ℝ≥0) (ha : ∀ i, a i ≠ 0)
    (t : ℝ) (ht : 0 < t) (x : Space) : 0 < heatKernel a t x := by
  apply gaussianProduct_pos
  intro i
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Real.toNNReal_pos.mpr ht).ne') (ha i)

theorem heatKernel_integrable (a : Fin 3 → ℝ≥0) (t : ℝ) : Integrable (heatKernel a t) :=
  gaussianProduct_integrable _

theorem heatKernel_integral (a : Fin 3 → ℝ≥0) (ha : ∀ i, a i ≠ 0)
    (t : ℝ) (ht : 0 < t) : (∫ x : Space, heatKernel a t x) = 1 := by
  apply gaussianProduct_integral
  intro i
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Real.toNNReal_pos.mpr ht).ne') (ha i)

theorem heatKernel_joint_measurable (a : Fin 3 → ℝ≥0) :
    Measurable (fun z : ℝ × Space => heatKernel a z.1 z.2) := by
  unfold heatKernel gaussianProduct
  fun_prop

theorem heatKernel_fourier (a : Fin 3 → ℝ≥0) (ha : ∀ i, a i ≠ 0)
    (t : ℝ) (ht : 0 < t) (ξ : Space) :
    𝓕 (fun x : Space => (heatKernel a t x : ℂ)) ξ =
      (Real.exp (-t * ellipticSymbol (diagonalTensor a) ξ) : ℂ) := by
  change 𝓕 (fun x : Space => (gaussianProduct (fun i => 2 * t.toNNReal * a i) x : ℂ)) ξ = _
  rw [gaussianProduct_fourier _ (fun i =>
    mul_ne_zero (mul_ne_zero (by norm_num) (Real.toNNReal_pos.mpr ht).ne') (ha i))]
  rw [Complex.ofReal_exp]
  congr 1
  simp only [ellipticSymbol, diagonalTensor_inner, NNReal.coe_mul, NNReal.coe_ofNat,
    Real.coe_toNNReal t ht.le, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow,
    Complex.ofReal_ofNat, Complex.ofReal_sum, Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The Green kernel constructed as an actual absolutely integrable heat mixture. -/
def resolventKernel (a : Fin 3 → ℝ≥0) (x : Space) : ℝ :=
  ∫ t : ℝ in Ioi 0, Real.exp (-t) * heatKernel a t x

theorem resolventKernel_nonneg (a : Fin 3 → ℝ≥0) (x : Space) :
    0 ≤ resolventKernel a x :=
  integral_nonneg (fun t => mul_nonneg (Real.exp_pos (-t)).le (heatKernel_nonneg a t x))

theorem heatMixture_integrable (a : Fin 3 → ℝ≥0) (ha : ∀ i, a i ≠ 0) :
    Integrable (fun z : ℝ × Space => Real.exp (-z.1) * heatKernel a z.1 z.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  apply (integrable_prod_iff (by
    exact ((Real.measurable_exp.comp measurable_fst.neg).mul
      (heatKernel_joint_measurable a)).aestronglyMeasurable)).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun t => by
      convert! (heatKernel_integrable a t).const_mul (Real.exp (-t)) using 1)
  · apply (integrableOn_exp_neg_Ioi 0).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
      (heatKernel_nonneg a t _)), integral_const_mul, heatKernel_integral a ha t ht, mul_one]

theorem resolventKernel_integrable (a : Fin 3 → ℝ≥0) (ha : ∀ i, a i ≠ 0) :
    Integrable (resolventKernel a) :=
  (heatMixture_integrable a ha).integral_prod_right

theorem resolventKernel_integral (a : Fin 3 → ℝ≥0) (ha : ∀ i, a i ≠ 0) :
    (∫ x : Space, resolventKernel a x) = 1 := by
  change (∫ x : Space, ∫ t : ℝ in Ioi 0, Real.exp (-t) * heatKernel a t x) = 1
  rw [← integral_integral_swap (heatMixture_integrable a ha)]
  have he : (fun t : ℝ => ∫ x : Space, Real.exp (-t) * heatKernel a t x) =ᵐ[
      volume.restrict (Ioi 0)] fun t => Real.exp (-t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [integral_const_mul, heatKernel_integral a ha t ht, mul_one]
  rw [integral_congr_ae he, integral_exp_neg_Ioi_zero]

theorem laplace_symbol (a : Fin 3 → ℝ≥0) (ξ : Space) :
    (∫ t : ℝ in Ioi 0, Real.exp (-t) *
      Real.exp (-t * ellipticSymbol (diagonalTensor a) ξ)) =
      (1 + ellipticSymbol (diagonalTensor a) ξ)⁻¹ := by
  have hpos : 0 < 1 + ellipticSymbol (diagonalTensor a) ξ := by
    linarith [ellipticSymbol_nonneg (diagonalTensor a) (diagonalTensor_nonneg a) ξ]
  have hfun : (fun t : ℝ => Real.exp (-t) *
      Real.exp (-t * ellipticSymbol (diagonalTensor a) ξ)) =
      fun t => Real.exp ((-(1 + ellipticSymbol (diagonalTensor a) ξ)) * t) := by
    funext t
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfun, integral_exp_mul_Ioi (by linarith) 0]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]

end Maxwell.Continuum.Well
