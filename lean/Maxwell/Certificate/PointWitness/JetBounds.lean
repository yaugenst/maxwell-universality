import Maxwell.Certificate.PointWitness.VerifiedCorrector
import Maxwell.Certificate.CurvatureTransfer
import Maxwell.Certificate.CurvatureWitness.Rounding

namespace Maxwell.Certificate.PointWitness

open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.YeeTaylor Maxwell.Certificate.CurvatureTransfer

noncomputable section

def pointEffectiveCoefficient (hgap : PointClusterComplementGap) (q : PeriodicYee.Momentum) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (pointExactIsometry hgap).toContinuousLinearMap.adjoint.comp
      ((pointTaylorCoefficient q 2).comp (pointExactIsometry hgap).toContinuousLinearMap) -
    (pointExactIsometry hgap).toContinuousLinearMap.adjoint.comp
      ((pointTaylorCoefficient q 1).comp (pointCorrector hgap q))

def savedEffectiveCoefficient (q : PeriodicYee.Momentum) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  pointReferenceMap.adjoint.comp ((pointTaylorCoefficient q 2).comp pointReferenceMap) -
    pointReferenceMap.adjoint.comp ((pointTaylorCoefficient q 1).comp
      (CorrectorWitness.savedCorrector q))

theorem pointReferenceMap_norm_le (hgap : PointClusterComplementGap) : ‖pointReferenceMap‖ ≤ 2 := by
  have he := (pointExactIsometry_close hgap).le
  have hn := (pointExactIsometry hgap).norm_toContinuousLinearMap_le
  have ht := norm_le_norm_add_norm_sub
    (pointExactIsometry hgap).toContinuousLinearMap pointReferenceMap
  linarith

theorem pointTaylorCoefficient_second_norm (q : PeriodicYee.Momentum) :
    ‖pointTaylorCoefficient q 2‖ ≤ (7/25 : ℝ) * radius q^2 := by
  have h := shiftedOperatorCoefficient_norm_le Concrete.material
    (timeReversalMomentum ![1,1,0]) q pointEnergy 2 (by omega)
  have hc : taylorCoefficientMajorant 2 ≤ (7/25 : ℝ) := by
    norm_num [taylorCoefficientMajorant]
  exact h.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _))

/-- Literal frame and saved-corrector checks control the actual compressed
quadratic coefficient. No Hessian replacement error is assumed. -/
theorem pointEffectiveCoefficient_saved_error (hgap : PointClusterComplementGap)
    (q : PeriodicYee.Momentum) :
    ‖pointEffectiveCoefficient hgap q - savedEffectiveCoefficient q‖ ≤
      (1/1000000 : ℝ) * radius q^2 := by
  have h := JetTransfer.effective_quadratic_error
    (pointTaylorCoefficient q 1) (pointTaylorCoefficient q 2)
    (pointExactIsometry hgap).toContinuousLinearMap pointReferenceMap
    (pointCorrector hgap q) (CorrectorWitness.savedCorrector q)
  have hΦ := (pointExactIsometry hgap).norm_toContinuousLinearMap_le
  have hU := pointReferenceMap_norm_le hgap
  have hframe := (pointExactIsometry_close hgap).le
  have hfirst := pointTaylorCoefficient_first_norm q
  have hsecond := pointTaylorCoefficient_second_norm q
  have hY := pointCorrector_norm_le hgap q
  have hdiff := pointCorrector_saved_close hgap q
  have hr := radius_nonneg q
  change ‖pointEffectiveCoefficient hgap q - savedEffectiveCoefficient q‖ ≤ _ at h
  calc
    _ ≤ _ := h
    _ ≤ (1/10000000000 : ℝ) * ((7/25) * radius q^2) * (1+2) +
        ((1/10000000000 : ℝ) * ((11/5) * radius q) * (3 * radius q) +
          2 * ((11/5) * radius q) * ((1/2^24) * radius q)) := by
      gcongr
    _ ≤ _ := by nlinarith [sq_nonneg (radius q)]

/-- Once the independently checked sparse derivative sums identify their
six-by-six block with the saved coefficient, both finite directional form
bounds follow for the actual exact spectral frame and exact corrector. -/
theorem pointEffectiveCoefficient_bounds (hgap : PointClusterComplementGap)
    (q : PeriodicYee.Momentum)
    (hbinding : savedEffectiveCoefficient q = directionalHalf CurvatureWitness.hessianApprox q)
    (x : EuclideanSpace ℂ (Fin 2)) :
    radius q^2 * ‖x‖^2 / 50 ≤ Complex.re (inner ℂ x (pointEffectiveCoefficient hgap q x)) ∧
      Complex.re (inner ℂ x (pointEffectiveCoefficient hgap q x)) ≤ radius q^2 * ‖x‖^2 := by
  apply directional_bounds_of_approximation CurvatureWitness.hessianApprox q
    (pointEffectiveCoefficient hgap q) CurvatureWitness.entry_rounding_error
  rw [← hbinding]
  exact pointEffectiveCoefficient_saved_error hgap q

end
end Maxwell.Certificate.PointWitness
