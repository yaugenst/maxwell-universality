import Maxwell.Continuum.TranslationH1

/-! Exact L² Fourier characterization of physical weak derivatives.
The exponential difference-quotient proof supplies the right side without
assuming any pre-existing regularity of a mode. -/

noncomputable section

namespace Maxwell.Continuum.FourierSobolev

open MeasureTheory FourierTransform Bloch Filter
open scoped Topology

theorem weakDerivative_frequency_iff (j : Fin 3) (f g : ScalarL2) :
    partialDistribution j (Lp.toTemperedDistribution f) = Lp.toTemperedDistribution g ↔
      (fun ξ => derivativeFactor j ξ * 𝓕 f ξ) =ᵐ[volume] ((𝓕 g : ScalarL2) : Space → ℂ) := by
  have hrow : distributionRow (fun _ : Fin 1 => derivativeFactor j) (fun _ => 𝓕 f) =
      (2 * Real.pi * Complex.I) • coordinateMultiplier j (Lp.toTemperedDistribution (𝓕 f)) := by
    simp only [distributionRow, Fin.sum_univ_one]
    have he : derivativeFactor j = (2 * Real.pi * Complex.I) • frequencyCoordinate j := rfl
    rw [he, TemperedDistribution.smulLeftCLM_smul (frequencyCoordinate_temperate j),
      smul_apply, ← coordinateMultiplier_eq]
  have hfour : 𝓕 (partialDistribution j (Lp.toTemperedDistribution f)) =
      (2 * Real.pi * Complex.I) • coordinateMultiplier j (Lp.toTemperedDistribution (𝓕 f)) := by
    simp only [partialDistribution, LineDeriv.lineDerivOpCLM_apply,
      TemperedDistribution.fourier_lineDerivOp_eq, Lp.fourier_toTemperedDistribution_eq,
      coordinateMultiplier]
  constructor
  · intro h
    have hF := congrArg (fun T : ScalarDistribution => 𝓕 T) h
    rw [hfour, Lp.fourier_toTemperedDistribution_eq] at hF
    have hr := (distributionRow_eq_iff (fun _ : Fin 1 => derivativeFactor j)
      (fun _ => derivativeFactor_temperate j) (fun _ => 𝓕 f) (𝓕 g)).mp (hrow.trans hF)
    filter_upwards [hr] with ξ hξ
    simpa only [rowValue, Fin.sum_univ_one] using hξ
  · intro h
    have hr := (distributionRow_eq_iff (fun _ : Fin 1 => derivativeFactor j)
      (fun _ => derivativeFactor_temperate j) (fun _ => 𝓕 f) (𝓕 g)).mpr (by
        filter_upwards [h] with ξ hξ
        simpa only [rowValue, Fin.sum_univ_one] using hξ)
    have hF : 𝓕 (partialDistribution j (Lp.toTemperedDistribution f)) =
        𝓕 (Lp.toTemperedDistribution g) := by
      rw [hfour, Lp.fourier_toTemperedDistribution_eq]
      exact hrow.symm.trans hr
    have hi := congrArg (fun T : ScalarDistribution => 𝓕⁻ T) hF
    simpa only [fourierInv_fourier_eq] using hi

theorem exists_weakDerivative_iff_memLp (j : Fin 3) (f : ScalarL2) :
    (∃ g : ScalarL2, partialDistribution j (Lp.toTemperedDistribution f) =
      Lp.toTemperedDistribution g) ↔
      MemLp (fun ξ => derivativeFactor j ξ * 𝓕 f ξ) 2 volume := by
  constructor
  · rintro ⟨g, hg⟩
    exact (Lp.memLp (𝓕 g)).ae_eq ((weakDerivative_frequency_iff j f g).mp hg).symm
  · intro h
    let G : ScalarL2 := h.toLp (fun ξ => derivativeFactor j ξ * 𝓕 f ξ)
    refine ⟨𝓕⁻ G, (weakDerivative_frequency_iff j f (𝓕⁻ G)).mpr ?_⟩
    rw [fourier_fourierInv_eq]
    exact h.coeFn_toLp.symm

theorem h1Data_iff_frequency (f : FieldL2) :
    Nonempty (H1Data f) ↔
      ∀ j k : Fin 3, MemLp (fun ξ => derivativeFactor j ξ * 𝓕 (f k) ξ) 2 volume := by
  constructor
  · rintro ⟨D⟩ j k
    exact (exists_weakDerivative_iff_memLp j (f k)).mp ⟨D.derivative j k, D.weak_derivative j k⟩
  · intro h
    choose g hg using fun j k => (exists_weakDerivative_iff_memLp j (f k)).mpr (h j k)
    exact ⟨⟨fun j => WithLp.toLp 2 (g j), hg⟩⟩

#print axioms h1Data_iff_frequency

end Maxwell.Continuum.FourierSobolev
