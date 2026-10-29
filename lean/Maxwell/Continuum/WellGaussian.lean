import Maxwell.Continuum.WellResolvent
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi

/-! Normalized Gaussian kernels on literal physical three-space, including
their exact Fourier transform in the `2π` convention. -/

noncomputable section

namespace Maxwell.Continuum.Well

open MeasureTheory ProbabilityTheory FourierTransform
open scoped NNReal

set_option backward.isDefEq.respectTransparency false

theorem gaussian_fourier_integral (v : ℝ≥0) (hv : v ≠ 0) (p : ℝ) :
    (∫ x : ℝ, Complex.exp (-(p : ℂ) * x * Complex.I) * (gaussianPDFReal 0 v x : ℂ)) =
      Complex.exp (-(v : ℂ) * p ^ 2 / 2) := by
  have h := charFun_gaussianReal (μ := 0) (v := v) (-p)
  rw [charFun_apply_real, integral_gaussianReal_eq_integral_smul hv] at h
  convert h using 1
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp only [Complex.ofReal_neg, Complex.real_smul]
      exact mul_comm _ _
  · congr 1
    push_cast
    ring

def gaussianProduct (v : Fin 3 → ℝ≥0) (x : Space) : ℝ :=
  ∏ i : Fin 3, gaussianPDFReal 0 (v i) (x i)

theorem gaussianProduct_nonneg (v : Fin 3 → ℝ≥0) (x : Space) : 0 ≤ gaussianProduct v x :=
  Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg 0 (v i) (x i))

theorem gaussianProduct_pos (v : Fin 3 → ℝ≥0) (hv : ∀ i, v i ≠ 0) (x : Space) :
    0 < gaussianProduct v x :=
  Finset.prod_pos (fun i _ => gaussianPDFReal_pos 0 (v i) (x i) (hv i))

theorem gaussianProduct_integrable (v : Fin 3 → ℝ≥0) : Integrable (gaussianProduct v) := by
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  exact Integrable.fintype_prod (fun i => integrable_gaussianPDFReal 0 (v i))

theorem gaussianProduct_integral (v : Fin 3 → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    (∫ x : Space, gaussianProduct v x) = 1 := by
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  change (∫ x : Fin 3 → ℝ, ∏ i, gaussianPDFReal 0 (v i) (x i)) = 1
  rw [integral_fintype_prod_volume_eq_prod]
  simp only [integral_gaussianPDFReal_eq_one 0 (hv _), Finset.prod_const_one]

theorem gaussianProduct_fourier_integral (v : Fin 3 → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    (p : Space) :
    (∫ x : Space, Complex.exp (-(inner ℝ p x : ℂ) * Complex.I) *
      (gaussianProduct v x : ℂ)) =
      Complex.exp (-(∑ i : Fin 3, (v i : ℂ) * (p i : ℂ) ^ 2 / 2)) := by
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  have hpoint (x : Fin 3 → ℝ) :
      Complex.exp (-(inner ℝ p (WithLp.toLp 2 x) : ℂ) * Complex.I) *
        (gaussianProduct v (WithLp.toLp 2 x) : ℂ) =
      ∏ i : Fin 3, Complex.exp (-(p i : ℂ) * x i * Complex.I) *
        (gaussianPDFReal 0 (v i) (x i) : ℂ) := by
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 1
    · congr 1
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]
      push_cast
      ring
    · simp [gaussianProduct]
  simp_rw [hpoint]
  have hp := integral_fintype_prod_volume_eq_prod (fun i (x : ℝ) =>
    Complex.exp (-(p i : ℂ) * x * Complex.I) * (gaussianPDFReal 0 (v i) x : ℂ))
  trans ∏ i : Fin 3, ∫ x : ℝ,
    Complex.exp (-(p i : ℂ) * x * Complex.I) * (gaussianPDFReal 0 (v i) x : ℂ)
  · convert! hp using 1
  simp_rw [gaussian_fourier_integral _ (hv _), ← Complex.exp_sum]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem gaussianProduct_fourier (v : Fin 3 → ℝ≥0) (hv : ∀ i, v i ≠ 0) (ξ : Space) :
    𝓕 (fun x : Space => (gaussianProduct v x : ℂ)) ξ =
      Complex.exp (-(∑ i : Fin 3, (v i : ℂ) * (2 * Real.pi * (ξ i : ℂ)) ^ 2 / 2)) := by
  rw [Real.fourier_eq']
  have h := gaussianProduct_fourier_integral v hv ((2 * Real.pi) • ξ)
  convert h using 1
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp only [smul_eq_mul, inner_smul_left, conj_trivial, Complex.ofReal_mul,
        Complex.ofReal_ofNat, Complex.ofReal_neg, real_inner_comm x ξ]
      congr 1
      congr 1
      ring
  · congr 1
    simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]

end Maxwell.Continuum.Well
