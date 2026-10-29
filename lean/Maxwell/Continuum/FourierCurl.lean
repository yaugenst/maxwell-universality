import Maxwell.Continuum.WeakCurl
import Mathlib.Analysis.Fourier.LpSpace

/-!
# The exact continuum Fourier representation of curl

The Fourier transform is the L² Plancherel isometry, component by component.
Its intertwining with the weak curl is proved through the injective map into
tempered distributions.  Frequency multiplication is unbounded on L² and
is therefore kept on distributions until its L² domain has been established.
-/

noncomputable section

namespace Maxwell.Continuum

open MeasureTheory FourierTransform
open scoped SchwartzMap

def fieldFourier : FieldL2 ≃ₗᵢ[ℂ] FieldL2 :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin 3 => Lp.fourierTransformₗᵢ Space ℂ)

@[simp] theorem fieldFourier_apply (u : FieldL2) (i : Fin 3) :
    fieldFourier u i = 𝓕 (u i) := rfl

theorem fieldFourier_norm (u : FieldL2) : ‖fieldFourier u‖ = ‖u‖ :=
  fieldFourier.norm_map u

theorem fieldFourier_inner (u v : FieldL2) :
    inner ℂ (fieldFourier u) (fieldFourier v) = inner ℂ u v :=
  fieldFourier.inner_map_map u v

def distributionFourier : FieldDistribution →L[ℂ] FieldDistribution :=
  ContinuousLinearMap.pi fun i =>
    (fourierCLM ℂ ScalarDistribution).comp (ContinuousLinearMap.proj i)

@[simp] theorem distributionFourier_apply (u : FieldDistribution) (i : Fin 3) :
    distributionFourier u i = 𝓕 (u i) := rfl

theorem distributionFourier_injective : Function.Injective distributionFourier := by
  intro u v h
  funext i
  have hi := congrFun h i
  change 𝓕 (u i) = 𝓕 (v i) at hi
  have hi' := congrArg (fun f : ScalarDistribution => 𝓕⁻ f) hi
  simpa only [fourierInv_fourier_eq] using hi'

theorem fieldDistribution_fourier (u : FieldL2) :
    distributionFourier (fieldDistribution u) = fieldDistribution (fieldFourier u) := by
  funext i
  exact Lp.fourier_toTemperedDistribution_eq (u i)

/-- Multiplication by the jth Fourier coordinate, on distributions. -/
def coordinateMultiplier (i : Fin 3) : ScalarDistribution →L[ℂ] ScalarDistribution :=
  TemperedDistribution.smulLeftCLM ℂ
    (fun ξ : Space => (inner ℝ ξ (coordinateDirection i) : ℂ))

def frequencyCross : FieldDistribution →L[ℂ] FieldDistribution :=
  ContinuousLinearMap.pi fun i =>
    (coordinateMultiplier (i + 1)).comp (ContinuousLinearMap.proj (i + 2)) -
      (coordinateMultiplier (i + 2)).comp (ContinuousLinearMap.proj (i + 1))

@[simp] theorem frequencyCross_apply (u : FieldDistribution) (i : Fin 3) :
    frequencyCross u i = coordinateMultiplier (i + 1) (u (i + 2)) -
      coordinateMultiplier (i + 2) (u (i + 1)) := rfl

/-- Exact Fourier normalization: differentiation corresponds to 2πiξ. -/
theorem distributionFourier_curl (u : FieldDistribution) :
    distributionFourier (curlDistribution u) =
      (2 * Real.pi * Complex.I) • frequencyCross (distributionFourier u) := by
  funext i
  change (fourierCLM ℂ ScalarDistribution)
    (partialDistribution (i + 1) (u (i + 2)) -
      partialDistribution (i + 2) (u (i + 1))) = _
  rw [map_sub]
  simp only [fourierCLM_apply, partialDistribution,
    LineDeriv.lineDerivOpCLM_apply,
    TemperedDistribution.fourier_lineDerivOp_eq, Pi.smul_apply,
    frequencyCross_apply, coordinateMultiplier, distributionFourier_apply, smul_sub]

/-- The full weak-curl graph has the literal Fourier multiplier description. -/
theorem weakCurl_fourier_iff (u v : FieldL2) :
    curlDistribution (fieldDistribution u) = fieldDistribution v ↔
      (2 * Real.pi * Complex.I) • frequencyCross (fieldDistribution (fieldFourier u)) =
        fieldDistribution (fieldFourier v) := by
  rw [← distributionFourier_injective.eq_iff, distributionFourier_curl,
    fieldDistribution_fourier, fieldDistribution_fourier]

end Maxwell.Continuum
