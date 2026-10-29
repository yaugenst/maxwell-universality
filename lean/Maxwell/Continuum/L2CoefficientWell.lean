import Maxwell.Continuum.L2CoefficientMap
import Maxwell.Continuum.AngularWell
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The constant unit-vector embedding intertwines the literal well
operators and has adjoint left inverse. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.L2CoefficientMap

open MeasureTheory EffectiveMass
open scoped InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem embedding_norm (v : H) (hv : ‖v‖ = 1) (f : L2Dilation.L2 (H := ℂ)) :
    ‖embedding v f‖ = ‖f‖ := by
  have he : ‖embedding v f‖^2 = ‖f‖^2 := by
    rw [L2Dilation.norm_sq, L2Dilation.norm_sq]
    apply integral_congr_ae
    filter_upwards [embedding_ae v f] with x hx
    simp only [hx, norm_smul, hv, mul_one]
  nlinarith [norm_nonneg (embedding v f), norm_nonneg f]

theorem embedding_adjoint_left (v : H) (hv : ‖v‖ = 1) :
    (embedding v)†.comp (embedding v) = 1 :=
  (embedding v).norm_map_iff_adjoint_comp_self.mp (embedding_norm v hv)

omit [CompleteSpace H] in
theorem well_embedding (v : H) (f : L2Dilation.L2 (H := ℂ)) :
    physicalWellMultiplier H (embedding v f) = embedding v (physicalWellMultiplier ℂ f) := by
  apply Lp.ext
  filter_upwards [physicalWellMultiplier_ae H (embedding v f), embedding_ae v f,
    embedding_ae v (physicalWellMultiplier ℂ f), physicalWellMultiplier_ae ℂ f] with x hw he ho hs
  rw [hw, he, ho, hs]
  simp only [smul_smul, smul_eq_mul]

theorem convolution_embedding (v : H) (f : L2Dilation.L2 (H := ℂ)) :
    angularWellConvolution H (embedding v f) = embedding v (angularWellConvolution ℂ f) := by
  rw [angularWellConvolution_apply, angular_inverse_embedding, well_embedding,
    angular_embedding, angularWellConvolution_apply]

theorem convolution_compression (v : H) (hv : ‖v‖ = 1) :
    (embedding v)†.comp ((angularWellConvolution H).comp (embedding v)) =
      angularWellConvolution ℂ := by
  apply ContinuousLinearMap.ext
  intro f
  change ((embedding v)†) (angularWellConvolution H (embedding v f)) = _
  rw [convolution_embedding]
  have he := congrArg (fun T : L2Dilation.L2 (H := ℂ) →L[ℂ] L2Dilation.L2 (H := ℂ) =>
    T (angularWellConvolution ℂ f)) (embedding_adjoint_left v hv)
  exact he

theorem convolution_sandwich (v : H) (hv : ‖v‖ = 1)
    (M : L2Dilation.L2 (H := ℂ) →L[ℂ] L2Dilation.L2 (H := ℂ)) :
    ((embedding v).comp M)†.comp
      ((angularWellConvolution H).comp ((embedding v).comp M)) =
      M†.comp ((angularWellConvolution ℂ).comp M) := by
  rw [ContinuousLinearMap.adjoint_comp]
  apply ContinuousLinearMap.ext
  intro f
  exact congrArg (M†)
    (congrArg (fun T : L2Dilation.L2 (H := ℂ) →L[ℂ] L2Dilation.L2 (H := ℂ) => T (M f))
      (convolution_compression v hv))

end Maxwell.Continuum.L2CoefficientMap
