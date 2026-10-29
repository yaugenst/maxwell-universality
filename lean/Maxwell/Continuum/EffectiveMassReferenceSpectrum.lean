import Maxwell.Continuum.EffectiveMassReferenceFactor
import Maxwell.Continuum.GramSpectralGap
import Maxwell.Continuum.WellGap
import Maxwell.Continuum.TopEigenPerturbationBasic

/-! The literal reference momentum operator has the proved scalar-well
eigenvalue, normalized mode and quantitative complementary gap. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.EffectiveMass

open scoped InnerProduct

attribute [local irreducible] referenceFactor diagonalReferenceOperator
  Well.physicalBirmanSchwinger Well.topVector

theorem referenceFactor_well_eigen :
    referenceFactor ((referenceFactor†) Well.topVector) = (Well.mu : ℂ) • Well.topVector := by
  have he := congrArg (fun T : ScalarL2 →L[ℂ] ScalarL2 => T Well.topVector)
    referenceFactor_leftGram
  exact he.trans Well.topVector_eigen

def referenceMode : ScalarL2 := GramSpectral.vector referenceFactor Well.mu Well.topVector

theorem referenceMode_norm : ‖referenceMode‖ = 1 :=
  GramSpectral.vector_norm referenceFactor Well.topVector Well.topVector_norm Well.mu_pos
    referenceFactor_well_eigen

theorem referenceMode_eigen :
    diagonalReferenceOperator referenceMode = (Well.mu : ℂ) • referenceMode := by
  have he := GramSpectral.vector_eigen referenceFactor Well.topVector Well.mu_pos
    referenceFactor_well_eigen
  have hT := congrArg (fun T : ScalarL2 →L[ℂ] ScalarL2 => T referenceMode)
    referenceFactor_rightGram
  exact hT.symm.trans he

theorem diagonalReference_positive : diagonalReferenceOperator.IsPositive := by
  rw [← referenceFactor_rightGram]
  exact ContinuousLinearMap.isPositive_adjoint_comp_self referenceFactor

theorem reference_complement_norm (f : ScalarL2) (hf : inner ℂ referenceMode f = 0) :
    ‖diagonalReferenceOperator f‖ ≤ (Well.mu - Well.gap) * ‖f‖ := by
  have hc (g : ScalarL2) (hg : inner ℂ Well.topVector g = 0) :
      ‖referenceFactor ((referenceFactor†) g)‖ ≤ (Well.mu - Well.gap) * ‖g‖ := by
    have he := congrArg (fun T : ScalarL2 →L[ℂ] ScalarL2 => T g) referenceFactor_leftGram
    change referenceFactor ((referenceFactor†) g) = Well.physicalBirmanSchwinger g at he
    rw [he]
    exact Well.well_complement_norm g hg
  have hb := GramSpectral.gram_complement referenceFactor Well.topVector Well.mu_pos
    (sub_nonneg.mpr Well.gap_le_mu) hc f hf
  have he := congrArg (fun T : ScalarL2 →L[ℂ] ScalarL2 => T f) referenceFactor_rightGram
  change (referenceFactor†) (referenceFactor f) = diagonalReferenceOperator f at he
  rwa [he] at hb

theorem referencePerturbationData :
    TopEigenPerturbation.Data diagonalReferenceOperator referenceMode Well.mu Well.gap where
  unit_norm := referenceMode_norm
  symmetric := diagonalReference_positive.isSelfAdjoint.isSymmetric
  eigenvector := referenceMode_eigen
  gap_pos := Well.gap_pos
  gap_le_mu := Well.gap_le_mu
  complement := reference_complement_norm

end Maxwell.Continuum.EffectiveMass
