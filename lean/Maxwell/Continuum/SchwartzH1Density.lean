import Maxwell.Continuum.SobolevUnweight
import Mathlib.Topology.Sequences

/-! Schwartz approximations converge in the actual first-derivative
graph norm, proved by the physical L² Fourier transform and Bessel weight. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FourierSobolev

open MeasureTheory FourierTransform Filter
open scoped SchwartzMap Topology

theorem schwartz_weakDerivative (φ : SchwartzMap Space ℂ) (j : Fin 3) :
    partialDistribution j (Lp.toTemperedDistribution (φ.toLp 2 volume)) =
      Lp.toTemperedDistribution ((partialSchwartz j φ).toLp 2 volume) := by
  simp only [Lp.toTemperedDistribution_toLp_eq, partialDistribution, partialSchwartz,
    LineDeriv.lineDerivOpCLM_apply,
    TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq]

theorem schwartz_derivative_fourier (φ : SchwartzMap Space ℂ) (j : Fin 3) :
    𝓕 ((partialSchwartz j φ).toLp 2 volume) =
      (SchwartzMap.smulLeftCLM ℂ (derivativeFactor j) (𝓕 φ)).toLp 2 volume := by
  apply Lp.ext
  have he := (weakDerivative_frequency_iff j (φ.toLp 2 volume)
    ((partialSchwartz j φ).toLp 2 volume)).mp (schwartz_weakDerivative φ j)
  rw [SchwartzMap.toLp_fourier_eq] at he
  filter_upwards [he, (𝓕 φ).coeFn_toLp 2 volume,
    (SchwartzMap.smulLeftCLM ℂ (derivativeFactor j) (𝓕 φ)).coeFn_toLp 2 volume] with ξ hd hφ hr
  rw [← hd, hφ, hr, SchwartzMap.smulLeftCLM_apply_apply (derivativeFactor_temperate j), smul_eq_mul]

theorem schwartz_inverse_derivative (φ : SchwartzMap Space ℂ) (j : Fin 3) :
    (partialSchwartz j (𝓕⁻ φ)).toLp 2 volume =
      𝓕⁻ ((SchwartzMap.smulLeftCLM ℂ (derivativeFactor j) φ).toLp 2 volume) := by
  apply (Lp.fourierTransformₗᵢ Space ℂ).injective
  change 𝓕 ((partialSchwartz j (𝓕⁻ φ)).toLp 2 volume) =
    𝓕 (𝓕⁻ ((SchwartzMap.smulLeftCLM ℂ (derivativeFactor j) φ).toLp 2 volume))
  rw [schwartz_derivative_fourier, fourier_fourierInv_eq, fourier_fourierInv_eq]

theorem scalar_schwartz_H1_approximation (f : ScalarL2) (g : Fin 3 → ScalarL2)
    (hg : ∀ j, partialDistribution j (Lp.toTemperedDistribution f) = Lp.toTemperedDistribution (g j)) :
    ∃ φ : ℕ → SchwartzMap Space ℂ,
      Tendsto (fun n => (φ n).toLp 2 volume) atTop (𝓝 f) ∧
      ∀ j, Tendsto (fun n => (partialSchwartz j (φ n)).toLp 2 volume) atTop (𝓝 (g j)) := by
  have hF (j : Fin 3) : MemLp (fun ξ => derivativeFactor j ξ*𝓕 f ξ) 2 volume :=
    (exists_weakDerivative_iff_memLp j f).mp ⟨g j, hg j⟩
  let G : ScalarL2 := weightedL2 (𝓕 f) hF
  obtain ⟨U, hU, hlim⟩ := mem_closure_iff_seq_limit.mp
    ((SchwartzMap.denseRange_toLpCLM (F := ℂ) (μ := (volume : Measure Space)) (p := 2)
      (by norm_num)) G)
  choose ψ hψ using hU
  have hψlim : Tendsto (fun n => (ψ n).toLp 2 volume) atTop (𝓝 G) := by
    exact hlim.congr (fun n => (hψ n).symm)
  have hG : unweight G = 𝓕 f := unweight_weighted (𝓕 f) hF
  have hdG (j : Fin 3) : derivativeUnweight j G = 𝓕 (g j) := by
    apply Lp.ext
    exact (derivativeUnweight_weighted (𝓕 f) hF j).trans
      ((weakDerivative_frequency_iff j f (g j)).mp (hg j))
  refine ⟨fun n => 𝓕⁻ (unweightSchwartz (ψ n)), ?_, fun j => ?_⟩
  · have ht := continuous_fourierInv.continuousAt.tendsto.comp (unweight.continuous.continuousAt.tendsto.comp hψlim)
    simpa only [Function.comp_def, hG, fourierInv_fourier_eq,
      SchwartzMap.toLp_fourierInv_eq, ← unweightSchwartz_toLp] using ht
  · have ht := continuous_fourierInv.continuousAt.tendsto.comp
      ((derivativeUnweight j).continuous.continuousAt.tendsto.comp hψlim)
    simpa only [Function.comp_def, hdG, fourierInv_fourier_eq,
      ← derivativeUnweightSchwartz_toLp, ← schwartz_inverse_derivative] using ht

#print axioms scalar_schwartz_H1_approximation

end Maxwell.Continuum.FourierSobolev
