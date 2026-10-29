import Maxwell.Continuum.EffectiveMassDiagonal
import Maxwell.Continuum.L2CoefficientWell

/-! The reference vector sandwich equals the actual scalar angular-Fourier
well sandwich. No fiber component or alias is omitted. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber PeriodicBand FiberNormalization
open scoped InnerProduct

attribute [local irreducible] normalizedFiberVector

theorem physicalFiberVector_zero_norm : ‖physicalFiberVector 0‖ = 1 := by
  have hzero : realMomentum (0 : Fin 3 → ℝ) = 0 := by ext j; simp [realMomentum]
  have hchart : realMomentum (0 : Fin 3 → ℝ) ∈ chart := by
    rw [hzero]
    exact chart_zero
  simpa only [physicalFiberVector, unscale, smul_zero, hzero] using
    normalizedFiberVector_norm_real 0 hchart

def referenceProfile : Well.UnitProfile where
  coefficient := referenceMultiplier
  measurable := referenceMultiplier_continuous.measurable
  nonneg := referenceMultiplier_nonneg
  le_one := referenceMultiplier_le_one

def referenceScalarOperator : ScalarL2 →L[ℂ] ScalarL2 := referenceProfile.multiplier

theorem referenceScalarOperator_ae (f : ScalarL2) :
    referenceScalarOperator f =ᵐ[volume] fun p => (referenceMultiplier p : ℂ) * f p :=
  referenceProfile.multiplier_ae f

theorem referenceScalarOperator_adjoint : referenceScalarOperator† = referenceScalarOperator :=
  referenceProfile.multiplier_selfAdjoint.adjoint_eq

theorem referenceVectorOperator_factor :
    referenceVectorOperator =
      (L2CoefficientMap.embedding (physicalFiberVector 0)).comp referenceScalarOperator := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [referenceVectorOperator_ae f,
    L2CoefficientMap.embedding_ae (physicalFiberVector 0) (referenceScalarOperator f),
    referenceScalarOperator_ae f] with p hv he hs
  change referenceVectorOperator f p =
    L2CoefficientMap.embedding (physicalFiberVector 0) (referenceScalarOperator f) p
  rw [hv, he, hs]
  simp only [referenceVectorMultiplier, smul_smul, mul_comm]

attribute [local irreducible] referenceScalarOperator L2CoefficientMap.embedding angularWellConvolution

theorem diagonalReferenceOperator_scalar :
    diagonalReferenceOperator = referenceScalarOperator.comp
      ((angularWellConvolution ℂ).comp referenceScalarOperator) := by
  have hc := L2CoefficientMap.convolution_sandwich (physicalFiberVector 0)
    physicalFiberVector_zero_norm referenceScalarOperator
  have hf := congrArg (fun V : ScalarL2 →L[ℂ] MomentumFiberL2 =>
    V†.comp ((angularWellConvolution FiberSpace).comp V)) referenceVectorOperator_factor
  have hs := congrArg (fun M : ScalarL2 →L[ℂ] ScalarL2 =>
    M.comp ((angularWellConvolution ℂ).comp referenceScalarOperator)) referenceScalarOperator_adjoint
  exact hf.trans (hc.trans hs)

end Maxwell.Continuum.EffectiveMass
