import Maxwell.Certificate.PointWitness.JetStructure
import Maxwell.Spectral.QuadraticResidual

namespace Maxwell.Certificate.PointWitness
open Maxwell.Spectral Maxwell.Spectral.YeeTaylor Maxwell.Certificate.CurvatureTransfer
noncomputable section

def savedQuadraticResidual (q : PeriodicYee.Momentum) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] PointSpace :=
  (pointTaylorCoefficient q 2).comp pointReferenceMap -
    (pointTaylorCoefficient q 1).comp (CorrectorWitness.savedCorrector q)

theorem pointQuadraticResidual_saved_error (hgap : PointClusterComplementGap)
    (q : PeriodicYee.Momentum) :
    ‖residualTaylorTerm (pointTaylorCoefficient q) (pointExactIsometry hgap).toContinuousLinearMap
        (pointCorrector hgap q) 1 - savedQuadraticResidual q‖ ≤
      (1/1000000 : ℝ) * radius q^2 := by
  have h := JetTransfer.residual_error (pointTaylorCoefficient q 1) (pointTaylorCoefficient q 2)
    (pointExactIsometry hgap).toContinuousLinearMap pointReferenceMap
    (pointCorrector hgap q) (CorrectorWitness.savedCorrector q)
  have hframe := (pointExactIsometry_close hgap).le
  have hfirst := pointTaylorCoefficient_first_norm q
  have hsecond := pointTaylorCoefficient_second_norm q
  have hdiff := pointCorrector_saved_close hgap q
  have hr := radius_nonneg q
  change ‖residualTaylorTerm (pointTaylorCoefficient q) (pointExactIsometry hgap).toContinuousLinearMap
    (pointCorrector hgap q) 1 - savedQuadraticResidual q‖ ≤ _ at h
  calc
    _ ≤ _ := h
    _ ≤ ((7/25 : ℝ) * radius q^2) * (1/10000000000) +
        ((11/5 : ℝ) * radius q) * ((1/2^24) * radius q) := by gcongr
    _ ≤ _ := by nlinarith [sq_nonneg (radius q)]

theorem pointEffectiveCoefficient_rounded_error (hgap : PointClusterComplementGap)
    (q : PeriodicYee.Momentum)
    (hbinding : savedEffectiveCoefficient q = directionalHalf CurvatureWitness.hessianApprox q) :
    ‖pointEffectiveCoefficient hgap q - directionalHalf FrozenHessian.lppm q‖ ≤
      (2/1000000 : ℝ) * radius q^2 := by
  have hsaved := pointEffectiveCoefficient_saved_error hgap q
  have hround := directionalHalf_error CurvatureWitness.hessianApprox FrozenHessian.lppm q
    (1/10^11) (by positivity) CurvatureWitness.entry_rounding_error
  rw [hbinding] at hsaved
  have h := norm_sub_le_norm_sub_add_norm_sub (pointEffectiveCoefficient hgap q)
    (directionalHalf CurvatureWitness.hessianApprox q) (directionalHalf FrozenHessian.lppm q)
  nlinarith [sq_nonneg (radius q)]

/-- The remaining finite stacked-Gram checks imply the full exact residual
inequality after all frame/corrector replacement errors are included. -/
theorem pointResidualGram_of_saved (hgap : PointClusterComplementGap)
    (q : PeriodicYee.Momentum)
    (hbinding : savedEffectiveCoefficient q = directionalHalf CurvatureWitness.hessianApprox q)
    (hnorm : ‖savedQuadraticResidual q‖ ≤ 2 * radius q^2)
    (hrelative : ∀ x, ‖savedQuadraticResidual q x‖^2 ≤
      (18/5 : ℝ) * radius q^2 * Complex.re (inner ℂ x (directionalHalf FrozenHessian.lppm q x)) -
        (1/10000 : ℝ) * radius q^4 * ‖x‖^2) (x : EuclideanSpace ℂ (Fin 2)) :
    ‖residualTaylorTerm (pointTaylorCoefficient q) (pointExactIsometry hgap).toContinuousLinearMap
        (pointCorrector hgap q) 1 x‖^2 ≤
      (18/5 : ℝ) * radius q^2 * Complex.re (inner ℂ x (pointEffectiveCoefficient hgap q x)) :=
  QuadraticResidual.relative_bound_of_saved _ _ _ _ (radius q) hnorm
    (pointQuadraticResidual_saved_error hgap q)
    (pointEffectiveCoefficient_rounded_error hgap q hbinding) hrelative x

end
end Maxwell.Certificate.PointWitness
