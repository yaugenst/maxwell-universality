import Maxwell.Continuum.FourierDifferenceQuotient

/-! Fatou's lemma converts an actual local L² translation estimate into
square integrability of each literal Fourier derivative multiplier. -/

noncomputable section

namespace Maxwell.Continuum.FourierSobolev

open MeasureTheory FourierTransform Bloch Filter
open scoped Topology ENNReal

theorem quotient_eLpNorm_eventually_le (j : Fin 3) (f : ScalarL2) {M : ℝ}
    (hbound : ∀ᶠ t : ℝ in 𝓝 0,
      ‖translation (t • coordinateDirection j) f - f‖ ≤ M * |t|) :
    ∀ᶠ t : ℝ in 𝓝[≠] 0,
      eLpNorm (fun ξ => quotientFactor j t ξ * 𝓕 f ξ) 2 volume ≤ ENNReal.ofReal M := by
  filter_upwards [hbound.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t hb ht
  have ht0 : t ≠ 0 := ht
  have hn : ‖scalarQuotient j t f‖ ≤ M := by
    rw [scalarQuotient_norm]
    calc
      _ ≤ |t|⁻¹ * (M * |t|) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (abs_nonneg t))
      _ = M := by field_simp [ht0]
  have he := ENNReal.ofReal_le_ofReal hn
  rw [eLpNorm_congr_ae (scalarQuotient_ae j t f).symm]
  simpa only [ofReal_norm, Lp.enorm_def] using he

/-- This is Fatou applied to the genuine exponential Fourier difference
quotients, with their derivative limit proved in the preceding module. -/
theorem derivative_eLpNorm_le (j : Fin 3) (f : ScalarL2) {M : ℝ}
    (hbound : ∀ᶠ t : ℝ in 𝓝 0,
      ‖translation (t • coordinateDirection j) f - f‖ ≤ M * |t|) :
    eLpNorm (fun ξ => derivativeFactor j ξ * 𝓕 f ξ) 2 volume ≤ ENNReal.ofReal M := by
  apply Lp.eLpNorm_le_of_ae_tendsto (quotient_eLpNorm_eventually_le j f hbound)
  · intro t
    exact (quotientFactor_continuous j t).aestronglyMeasurable.mul (Lp.aestronglyMeasurable (𝓕 f))
  · exact (derivativeFactor_continuous j).aestronglyMeasurable.mul (Lp.aestronglyMeasurable (𝓕 f))
  · exact Filter.Eventually.of_forall fun ξ => (quotientFactor_tendsto j ξ).mul_const (𝓕 f ξ)

theorem derivative_memLp (j : Fin 3) (f : ScalarL2) {M : ℝ}
    (hbound : ∀ᶠ t : ℝ in 𝓝 0,
      ‖translation (t • coordinateDirection j) f - f‖ ≤ M * |t|) :
    MemLp (fun ξ => derivativeFactor j ξ * 𝓕 f ξ) 2 volume :=
  (derivative_eLpNorm_le j f hbound).trans_lt ENNReal.ofReal_lt_top

def frequencyDerivative (j : Fin 3) (f : ScalarL2) {M : ℝ}
    (hbound : ∀ᶠ t : ℝ in 𝓝 0,
      ‖translation (t • coordinateDirection j) f - f‖ ≤ M * |t|) : ScalarL2 :=
  (derivative_memLp j f hbound).toLp (fun ξ => derivativeFactor j ξ * 𝓕 f ξ)

theorem frequencyDerivative_ae (j : Fin 3) (f : ScalarL2) {M : ℝ}
    (hbound : ∀ᶠ t : ℝ in 𝓝 0,
      ‖translation (t • coordinateDirection j) f - f‖ ≤ M * |t|) :
    frequencyDerivative j f hbound =ᵐ[volume] (fun ξ => derivativeFactor j ξ * 𝓕 f ξ) :=
  (derivative_memLp j f hbound).coeFn_toLp

theorem frequencyDerivative_norm_le (j : Fin 3) (f : ScalarL2) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᶠ t : ℝ in 𝓝 0,
      ‖translation (t • coordinateDirection j) f - f‖ ≤ M * |t|) :
    ‖frequencyDerivative j f hbound‖ ≤ M := by
  rw [frequencyDerivative, Lp.norm_toLp]
  exact ENNReal.toReal_le_of_le_ofReal hM (derivative_eLpNorm_le j f hbound)

end Maxwell.Continuum.FourierSobolev
