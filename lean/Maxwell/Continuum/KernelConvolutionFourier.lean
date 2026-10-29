import Maxwell.Continuum.KernelConvolution
import Maxwell.Continuum.FourierL1L2
import Mathlib.Analysis.Fourier.Convolution

/-! The actual compact weighted convolution is intertwined with the
literal Fourier multipliers, with both Plancherel and integral conventions
proved to agree. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.KernelIntegral

open MeasureTheory FourierTransform

theorem weightedConvolution_fourier_ae (w : Space → ℂ) (hw : MemLp w 2 volume)
    (u : ScalarL2) (hu : Integrable (fun x => u x)) (f : ScalarL2) :
    (𝓕 (weightedConvolution w hw u f) : ScalarL2) =ᵐ[volume]
      fun ξ => 𝓕 (fun x => f x * w x) ξ * 𝓕 (fun x => u x) ξ := by
  have hc := weightedConvolution_integrable_result w hw u hu f
  filter_upwards [fourierL2_ae_integral (weightedConvolution w hw u f) hc] with ξ hξ
  rw [hξ, Real.fourier_congr_ae (weightedConvolution_ae w hw u hu f) ξ]
  exact Real.fourier_mul_convolution_eq (weighted_source_integrable w hw f) hu ξ

end Maxwell.Continuum.KernelIntegral
