import Maxwell.Continuum.FourierDifferenceFatou

/-! Fourier integrability obtained from difference quotients gives actual
L² weak coordinate derivatives, through the injective distribution transform. -/

noncomputable section

namespace Maxwell.Continuum.FourierSobolev

open MeasureTheory FourierTransform Bloch Filter
open scoped Topology

@[fun_prop] theorem derivativeFactor_temperate (j : Fin 3) :
    (derivativeFactor j).HasTemperateGrowth := by
  change (fun ξ : Space => fourierDerivativeConstant * frequencyCoordinate j ξ).HasTemperateGrowth
  fun_prop

theorem frequencyDerivative_distribution (j : Fin 3) (f : ScalarL2) {M : ℝ}
    (hbound : ∀ᶠ t : ℝ in 𝓝 0,
      ‖translation (t • coordinateDirection j) f - f‖ ≤ M * |t|) :
    Lp.toTemperedDistribution (frequencyDerivative j f hbound) =
      (2 * Real.pi * Complex.I) • coordinateMultiplier j (Lp.toTemperedDistribution (𝓕 f)) := by
  have hrow := (distributionRow_eq_iff (fun _ : Fin 1 => derivativeFactor j)
    (fun _ => derivativeFactor_temperate j) (fun _ => 𝓕 f)
    (frequencyDerivative j f hbound)).mpr (by
      filter_upwards [frequencyDerivative_ae j f hbound] with ξ hξ
      simpa only [rowValue, Fin.sum_univ_one] using hξ.symm)
  simp only [distributionRow, Fin.sum_univ_one] at hrow
  have hg : derivativeFactor j = (2 * Real.pi * Complex.I) • frequencyCoordinate j := rfl
  rw [hg, TemperedDistribution.smulLeftCLM_smul (frequencyCoordinate_temperate j),
    smul_apply, ← coordinateMultiplier_eq] at hrow
  exact hrow.symm

def weakDerivative (j : Fin 3) (f : ScalarL2) {M : ℝ}
    (hbound : ∀ᶠ t : ℝ in 𝓝 0,
      ‖translation (t • coordinateDirection j) f - f‖ ≤ M * |t|) : ScalarL2 :=
  𝓕⁻ (frequencyDerivative j f hbound)

theorem weakDerivative_distribution (j : Fin 3) (f : ScalarL2) {M : ℝ}
    (hbound : ∀ᶠ t : ℝ in 𝓝 0,
      ‖translation (t • coordinateDirection j) f - f‖ ≤ M * |t|) :
    partialDistribution j (Lp.toTemperedDistribution f) =
      Lp.toTemperedDistribution (weakDerivative j f hbound) := by
  have hF : 𝓕 (partialDistribution j (Lp.toTemperedDistribution f)) =
      𝓕 (Lp.toTemperedDistribution (weakDerivative j f hbound)) := by
    rw [Lp.fourier_toTemperedDistribution_eq]
    change 𝓕 (partialDistribution j (Lp.toTemperedDistribution f)) =
      Lp.toTemperedDistribution (𝓕 (𝓕⁻ (frequencyDerivative j f hbound)))
    rw [fourier_fourierInv_eq, frequencyDerivative_distribution]
    simp only [partialDistribution, LineDeriv.lineDerivOpCLM_apply,
      TemperedDistribution.fourier_lineDerivOp_eq, Lp.fourier_toTemperedDistribution_eq,
      coordinateMultiplier]
  have hi := congrArg (fun T : ScalarDistribution => 𝓕⁻ T) hF
  simpa only [fourierInv_fourier_eq] using hi

theorem weakDerivative_norm_le (j : Fin 3) (f : ScalarL2) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᶠ t : ℝ in 𝓝 0,
      ‖translation (t • coordinateDirection j) f - f‖ ≤ M * |t|) :
    ‖weakDerivative j f hbound‖ ≤ M := by
  change ‖(Lp.fourierTransformₗᵢ Space ℂ).symm (frequencyDerivative j f hbound)‖ ≤ M
  rw [(Lp.fourierTransformₗᵢ Space ℂ).symm.norm_map]
  exact frequencyDerivative_norm_le j f hM hbound

end Maxwell.Continuum.FourierSobolev
