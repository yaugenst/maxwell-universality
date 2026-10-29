import Maxwell.Continuum.WellHeatKernel

/-! The Fourier transform of the constructed positive heat mixture is the
literal anisotropic resolvent symbol. The change of integration order is
justified by an actual global `L¹` estimate. -/

noncomputable section

namespace Maxwell.Continuum.Well

open MeasureTheory FourierTransform Set
open scoped NNReal

set_option backward.isDefEq.respectTransparency false

def fourierPhase (ξ x : Space) : ℂ :=
  Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I)

theorem fourierPhase_norm (ξ x : Space) : ‖fourierPhase ξ x‖ = 1 := by
  rw [fourierPhase, Complex.norm_exp]
  simp

theorem modulatedHeatMixture_integrable (a : Fin 3 → ℝ≥0) (ha : ∀ i, a i ≠ 0)
    (ξ : Space) :
    Integrable (fun z : ℝ × Space => fourierPhase ξ z.2 *
      ((Real.exp (-z.1) * heatKernel a z.1 z.2 : ℝ) : ℂ))
      ((volume.restrict (Ioi 0)).prod volume) := by
  apply (heatMixture_integrable a ha).mono'
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · unfold fourierPhase
      fun_prop
    · exact Complex.continuous_ofReal.measurable.comp
        ((Real.measurable_exp.comp measurable_fst.neg).mul (heatKernel_joint_measurable a))
  · exact Filter.Eventually.of_forall fun z => by
      rw [norm_mul, fourierPhase_norm, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (heatKernel_nonneg _ _ _))]

theorem resolventKernel_fourier (a : Fin 3 → ℝ≥0) (ha : ∀ i, a i ≠ 0) (ξ : Space) :
    𝓕 (fun x : Space => (resolventKernel a x : ℂ)) ξ =
      ((1 + ellipticSymbol (diagonalTensor a) ξ)⁻¹ : ℝ) := by
  calc
    _ = ∫ x : Space, ∫ t : ℝ in Ioi 0, fourierPhase ξ x *
        ((Real.exp (-t) * heatKernel a t x : ℝ) : ℂ) := by
      rw [Real.fourier_eq']
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [resolventKernel, ← integral_complex_ofReal, integral_const_mul]
        rfl
    _ = ∫ t : ℝ in Ioi 0, ∫ x : Space, fourierPhase ξ x *
        ((Real.exp (-t) * heatKernel a t x : ℝ) : ℂ) :=
      (integral_integral_swap (modulatedHeatMixture_integrable a ha ξ)).symm
    _ = ∫ t : ℝ in Ioi 0, (Real.exp (-t) : ℂ) *
        𝓕 (fun x : Space => (heatKernel a t x : ℂ)) ξ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        dsimp only
        rw [Real.fourier_eq', ← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          simp only [fourierPhase, Complex.ofReal_mul, smul_eq_mul]
          ring
    _ = ∫ t : ℝ in Ioi 0, ((Real.exp (-t) *
        Real.exp (-t * ellipticSymbol (diagonalTensor a) ξ) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [heatKernel_fourier a ha t ht, Complex.ofReal_mul]
    _ = ((1 + ellipticSymbol (diagonalTensor a) ξ)⁻¹ : ℝ) := by
      rw [integral_complex_ofReal, laplace_symbol]

theorem heatKernel_neg (a : Fin 3 → ℝ≥0) (t : ℝ) (x : Space) :
    heatKernel a t (-x) = heatKernel a t x := by
  unfold heatKernel gaussianProduct
  apply Finset.prod_congr rfl
  intro i _
  simp [ProbabilityTheory.gaussianPDFReal]

theorem resolventKernel_neg (a : Fin 3 → ℝ≥0) (x : Space) :
    resolventKernel a (-x) = resolventKernel a x := by
  unfold resolventKernel
  simp only [heatKernel_neg]

end Maxwell.Continuum.Well
