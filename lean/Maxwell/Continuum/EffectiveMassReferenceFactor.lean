import Maxwell.Continuum.EffectiveMassReferenceResolvent

/-! A literal rectangular factor identifies the two effective-mass Gram
operators with the scalar well and the reference momentum sandwich. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.EffectiveMass

open scoped InnerProduct

attribute [local irreducible] referenceScalarOperator angularFourier Well.UnitProfile.multiplier

def referenceFactor : ScalarL2 →L[ℂ] ScalarL2 :=
  Well.rootProfile.multiplier.comp
    ((angularFourier ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      referenceScalarOperator)

theorem referenceFactor_apply (f : ScalarL2) :
    referenceFactor f = Well.rootProfile.multiplier
      ((angularFourier ℂ).symm (referenceScalarOperator f)) := rfl

theorem referenceFactor_adjoint : referenceFactor† = referenceScalarOperator.comp
    ((angularFourier ℂ).toContinuousLinearEquiv.toContinuousLinearMap.comp
      Well.rootProfile.multiplier) := by
  rw [referenceFactor, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    referenceScalarOperator_adjoint, Well.rootProfile.multiplier_selfAdjoint.adjoint_eq]
  rw [show ContinuousLinearMap.adjoint
      (angularFourier ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap =
      (angularFourier ℂ).toContinuousLinearEquiv.toContinuousLinearMap from
    (angularFourier ℂ).symm.adjoint_eq_symm]
  rfl

theorem referenceFactor_adjoint_apply (f : ScalarL2) :
    (referenceFactor†) f = referenceScalarOperator
      (angularFourier ℂ (Well.rootProfile.multiplier f)) := by
  rw [referenceFactor_adjoint]
  rfl

theorem referenceFactor_leftGram :
    referenceFactor.comp (referenceFactor†) = Well.physicalBirmanSchwinger := by
  apply ContinuousLinearMap.ext
  intro f
  change referenceFactor ((referenceFactor†) f) = _
  rw [referenceFactor_apply, referenceFactor_adjoint_apply, referenceSquare_resolvent]
  rfl

theorem referenceFactor_rightGram :
    (referenceFactor†).comp referenceFactor = diagonalReferenceOperator := by
  apply ContinuousLinearMap.ext
  intro f
  change (referenceFactor†) (referenceFactor f) = _
  rw [referenceFactor_adjoint_apply, referenceFactor_apply]
  have hQ := congrArg (fun T : ScalarL2 →L[ℂ] ScalarL2 =>
    T ((angularFourier ℂ).symm (referenceScalarOperator f))) Well.rootMultiplier_square
  change Well.rootProfile.multiplier
      (Well.rootProfile.multiplier ((angularFourier ℂ).symm (referenceScalarOperator f))) = _ at hQ
  rw [hQ, diagonalReferenceOperator_scalar]
  change _ = referenceScalarOperator (angularWellConvolution ℂ (referenceScalarOperator f))
  rw [angularWellConvolution_apply, physicalWellMultiplier_scalar]

end Maxwell.Continuum.EffectiveMass
