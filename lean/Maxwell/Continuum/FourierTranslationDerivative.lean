import Maxwell.Continuum.FourierSobolevCharacterization
import Maxwell.Continuum.L2DominatedConvergence

/-! Strong L² differentiation of the literal translation group from
actual weak Sobolev derivatives, proved by Fourier dominated convergence. -/

noncomputable section

namespace Maxwell.Continuum.FourierSobolev

open MeasureTheory FourierTransform Bloch Filter
open scoped Topology

theorem quotientFactor_norm_le (j : Fin 3) (t : ℝ) (ξ : Space) :
    ‖quotientFactor j t ξ‖ ≤ ‖derivativeFactor j ξ‖ := by
  by_cases ht : t = 0
  · simp [quotientFactor, ht]
  have he : (t : ℂ) * derivativeFactor j ξ =
      Complex.I * ((2 * Real.pi * t * ξ j : ℝ) : ℂ) := by
    unfold derivativeFactor
    push_cast
    ring
  have hn : ‖(2 * Real.pi * t * ξ j : ℝ)‖ = |t| * ‖derivativeFactor j ξ‖ := by
    have h := congrArg norm he.symm
    simpa only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] using h
  have hp : ‖phase (t • coordinateDirection j) ξ-1‖ ≤ |t| * ‖derivativeFactor j ξ‖ := by
    rw [phase_coordinate, he]
    exact Real.norm_exp_I_mul_ofReal_sub_one_le.trans_eq hn
  rw [quotientFactor, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |t|⁻¹ * (|t| * ‖derivativeFactor j ξ‖) :=
      mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr (abs_nonneg t))
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr ht), one_mul]

theorem scalarQuotient_tendsto (j : Fin 3) (f g : ScalarL2)
    (hg : partialDistribution j (Lp.toTemperedDistribution f) = Lp.toTemperedDistribution g) :
    Tendsto (fun t : ℝ => scalarQuotient j t f) (𝓝[≠] 0) (𝓝 (𝓕 g)) := by
  have hf := (weakDerivative_frequency_iff j f g).mp hg
  apply L2Convergence.tendsto_of_dominated volume
    (fun t : ℝ => scalarQuotient j t f) (𝓕 g)
    (fun t ξ => quotientFactor j t ξ * 𝓕 f ξ) (fun ξ => 𝓕 g ξ) (fun ξ => ‖𝓕 g ξ‖)
    (fun t => scalarQuotient_ae j t f) Filter.EventuallyEq.rfl
  · exact Filter.Eventually.of_forall fun t =>
      (quotientFactor_continuous j t).aestronglyMeasurable.mul (Lp.aestronglyMeasurable (𝓕 f))
  · exact Lp.aestronglyMeasurable _
  · exact (Lp.memLp (𝓕 g)).norm.integrable_sq
  · exact Filter.Eventually.of_forall fun t => by
      filter_upwards [hf] with ξ hξ
      rw [norm_mul]
      calc
        _ ≤ ‖derivativeFactor j ξ‖ * ‖𝓕 f ξ‖ :=
          mul_le_mul_of_nonneg_right (quotientFactor_norm_le j t ξ) (norm_nonneg _)
        _ = ‖𝓕 g ξ‖ := by rw [← norm_mul, hξ]
  · exact Filter.Eventually.of_forall fun _ => le_rfl
  · filter_upwards [hf] with ξ hξ
    simpa only [hξ] using (quotientFactor_tendsto j ξ).mul_const (𝓕 f ξ)

theorem translation_hasDerivAt (j : Fin 3) (f g : ScalarL2)
    (hg : partialDistribution j (Lp.toTemperedDistribution f) = Lp.toTemperedDistribution g) :
    HasDerivAt (fun t : ℝ => translation (t • coordinateDirection j) f) g 0 := by
  have ht := continuous_fourierInv.continuousAt.tendsto.comp (scalarQuotient_tendsto j f g hg)
  rw [fourierInv_fourier_eq] at ht
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have hz : translation (0 : Space) f = f := by
    apply Lp.ext
    simpa only [add_zero] using translation_ae 0 f
  have he (t : ℝ) : 𝓕⁻ (scalarQuotient j t f) =
      t⁻¹ • (translation (t • coordinateDirection j) f-f) := by
    rw [scalarQuotient, ← fourier_translation]
    change (Lp.fourierTransformₗᵢ Space ℂ).symm
      ((t : ℂ)⁻¹ • ((Lp.fourierTransformₗᵢ Space ℂ) (translation (t • coordinateDirection j) f) -
        (Lp.fourierTransformₗᵢ Space ℂ) f)) = _
    rw [map_smul, map_sub, (Lp.fourierTransformₗᵢ Space ℂ).symm_apply_apply,
      (Lp.fourierTransformₗᵢ Space ℂ).symm_apply_apply]
    rw [← Complex.ofReal_inv]
    exact IsScalarTower.algebraMap_smul ℂ (t⁻¹ : ℝ) (translation (t • coordinateDirection j) f-f)
  simpa only [Function.comp_def, he, zero_add, zero_smul, hz] using ht

#print axioms scalarQuotient_tendsto
#print axioms translation_hasDerivAt

end Maxwell.Continuum.FourierSobolev
