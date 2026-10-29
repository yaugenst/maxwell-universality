import Maxwell.Certificate.CurvatureWitness.Assembly
import Maxwell.Certificate.PointWitness.ConventionalHessian

namespace Maxwell.Certificate.PointWitness

open Maxwell.Spectral
noncomputable section

/-- The actual finite integer Hessian checks, rounding enclosure and exact
frame/corrector transfer prove the compressed lower form. Only point
isolation remains an input to the construction of that exact frame. -/
theorem pointCompressedLower_verified (hgap : PointClusterComplementGap) :
    PointCompressedLower hgap := by
  intro q x
  exact (pointEffectiveCoefficient_bounds hgap q
    (CurvatureWitness.savedEffectiveCoefficient_binding q) x).1

theorem pointEffectiveCoefficient_verified (hgap : PointClusterComplementGap)
    (q : PeriodicYee.Momentum) (x : EuclideanSpace ℂ (Fin 2)) :
    YeeTaylor.radius q^2 * ‖x‖^2 / 50 ≤
        Complex.re (inner ℂ x (pointEffectiveCoefficient hgap q x)) ∧
      Complex.re (inner ℂ x (pointEffectiveCoefficient hgap q x)) ≤
        YeeTaylor.radius q^2 * ‖x‖^2 :=
  pointEffectiveCoefficient_bounds hgap q (CurvatureWitness.savedEffectiveCoefficient_binding q) x

end
end Maxwell.Certificate.PointWitness
