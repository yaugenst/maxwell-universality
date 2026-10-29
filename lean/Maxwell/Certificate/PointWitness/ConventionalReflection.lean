import Maxwell.Certificate.PointWitness.ConventionalBranch
import Maxwell.Certificate.PointWitness.ConventionalReal
import Maxwell.Spectral.ConventionalReflection

namespace Maxwell.Certificate.PointWitness

open Maxwell.Spectral Maxwell.Spectral.ConventionalAnalytic
open Filter
open scoped Topology
noncomputable section

theorem conventionalPointOperator_reflection
    (z : ComplexMomentum) (v : ConventionalPointSpace) :
    conventionalPointOperator (reflectMomentum z) (conjugateVector v) =
      conjugateVector (conventionalPointOperator z v) := by
  unfold conventionalPointOperator conventionalPointMomentum pointPrimitiveMomentum
  rw [conventionalMomentum_trim]
  exact operator_trim_reflection Concrete.material (conventionalTrimCoordinates ![1,1,0]) z v

/-- The actual time-reversal covariance and the off-pole inverse identify
the reflected eigenvalue with this same analytic branch. No separately
chosen branch or unproved reflection principle is used. -/
theorem conventional_point_branch_reflection
    (value : ComplexMomentum → ℂ) (u : ComplexMomentum → ConventionalPointSpace)
    (hv : ContinuousAt value 0) (hv0 : value 0 = (pointEnergy : ℂ))
    (heigen : ∀ᶠ z in 𝓝 (0 : ComplexMomentum), u z ≠ 0 ∧
      conventionalPointOperator z (u z) = value z • u z)
    (hresolvent : ∀ᶠ z in 𝓝 ((0, 0) : ComplexMomentum × ℂ),
      value z.1 ≠ (pointEnergy : ℂ) + z.2 →
        (conventionalPointOperator z.1 - ((pointEnergy : ℂ) + z.2) • 1).IsInvertible) :
    ∀ᶠ z in 𝓝 (0 : ComplexMomentum), value (reflectMomentum z) = star (value z) := by
  apply BranchIdentification.eventuallyEq_of_continuous_eigenpair
    conventionalPointOperator value reflectMomentum (fun z => star (value z))
    (fun z => conjugateVector (u z)) 0 0 (pointEnergy : ℂ)
  · simpa only [reflectMomentum_zero] using reflectMomentum_continuous.continuousAt.tendsto
      (x := (0 : ComplexMomentum))
  · exact continuous_star.continuousAt.comp hv
  · simp only [hv0, Complex.star_def, Complex.conj_ofReal]
  · exact hresolvent
  · filter_upwards [heigen] with z hz
    exact conjugateVector_ne_zero _ hz.1
  · filter_upwards [heigen] with z hz
    rw [conventionalPointOperator_reflection, hz.2, conjugateVector_smul]

end
end Maxwell.Certificate.PointWitness
