import Maxwell.Certificate.PointWitness.CorrectorConstruction
import Maxwell.Certificate.PointWitness.EvenAnalyticBranch
import Maxwell.Spectral.EigenbranchJet
import Maxwell.Spectral.Trial

/-! The second derivative of the constructed actual point band is the
compressed exact-corrector quadratic form in the certified two-column frame. -/

namespace Maxwell.Certificate.PointWitness

open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee Filter
open scoped Topology

noncomputable section

def pointCenterCoordinates (hgap : PointClusterComplementGap) : EuclideanSpace ℂ (Fin 2) :=
  (pointExactIsometry hgap).toContinuousLinearMap.adjoint (pointEigenbasis pointIndex0)

theorem pointCenterCoordinates_image (hgap : PointClusterComplementGap) :
    pointExactIsometry hgap (pointCenterCoordinates hgap) = pointEigenbasis pointIndex0 := by
  have hp := congrArg (fun L : PointSpace →L[ℂ] PointSpace => L (pointEigenbasis pointIndex0))
    (pointExactIsometry_comp_adjoint hgap)
  change pointExactIsometry hgap (pointCenterCoordinates hgap) =
    pointClusterProjection (pointEigenbasis pointIndex0) at hp
  rw [pointClusterProjection, ClusterProjection.projection_basis] at hp
  simpa only [pointCluster, Finset.mem_insert_self, ite_true] using hp

theorem pointCenterCoordinates_norm (hgap : PointClusterComplementGap) :
    ‖pointCenterCoordinates hgap‖ = 1 := by
  rw [← (pointExactIsometry hgap).norm_map, pointCenterCoordinates_image]
  exact pointEigenbasis.orthonormal.norm_eq_one pointIndex0

def pointCenterCorrector (hgap : PointClusterComplementGap) (q : PeriodicYee.Momentum) :
    PointSpace := pointCorrector hgap q (pointCenterCoordinates hgap)

theorem pointCenterCorrector_orthogonal (hgap : PointClusterComplementGap)
    (q : PeriodicYee.Momentum) :
    inner ℂ (pointEigenbasis pointIndex0) (pointCenterCorrector hgap q) = 0 := by
  rw [← pointCenterCoordinates_image hgap]
  exact inner_zero_of_opposite_parity pointInversion 1 (Or.inl rfl)
    (pointExactIsometry hgap).toContinuousLinearMap (pointCorrector hgap q)
    (pointExactIsometry_even hgap) (pointCorrector_odd hgap q)
    (pointCenterCoordinates hgap) (pointCenterCoordinates hgap)

theorem pointTaylorCoefficient_positive_shift (q : PeriodicYee.Momentum)
    (n : ℕ) (hn : n ≠ 0) :
    pointTaylorCoefficient q n = YeeTaylor.shiftedOperatorCoefficient Concrete.material
      (timeReversalMomentum ![1,1,0]) q 0 n := by
  simp only [pointTaylorCoefficient, YeeTaylor.shiftedOperatorCoefficient,
    YeeTaylor.shiftedFiberCoefficient, hn, ite_false, sub_zero]

theorem pointCenterCorrector_equation (hgap : PointClusterComplementGap)
    (q : PeriodicYee.Momentum) :
    (YeeTaylor.euclideanMap (PrimitiveYee.fiber Concrete.material
      (timeReversalMomentum ![1,1,0])) - (pointEnergy : ℂ) • 1)
        (pointCenterCorrector hgap q) =
      YeeTaylor.shiftedOperatorCoefficient Concrete.material
        (timeReversalMomentum ![1,1,0]) q 0 1 (pointEigenbasis pointIndex0) := by
  have h := congrArg
    (fun L : EuclideanSpace ℂ (Fin 2) →L[ℂ] PointSpace => L (pointCenterCoordinates hgap))
    (pointCorrector_equation hgap q)
  change (pointTaylorCoefficient q 0) (pointCenterCorrector hgap q) =
    (pointTaylorCoefficient q 1) (pointExactIsometry hgap (pointCenterCoordinates hgap)) at h
  rw [pointCenterCoordinates_image, pointTaylorCoefficient_positive_shift q 1 (by omega)] at h
  change (YeeTaylor.shiftedOperatorCoefficient Concrete.material
    (timeReversalMomentum ![1,1,0]) q pointEnergy 0) _ = _ at h
  rw [pointShiftedOperator_eq_coefficient] at h
  exact h

def pointCompressedJet (hgap : PointClusterComplementGap) (q : PeriodicYee.Momentum) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (pointExactIsometry hgap).toContinuousLinearMap.adjoint.comp
      ((pointTaylorCoefficient q 2).comp (pointExactIsometry hgap).toContinuousLinearMap) -
    (pointExactIsometry hgap).toContinuousLinearMap.adjoint.comp
      ((pointTaylorCoefficient q 1).comp (pointCorrector hgap q))

theorem pointCompressedJet_inner (hgap : PointClusterComplementGap)
    (q : PeriodicYee.Momentum) (x : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ x (pointCompressedJet hgap q x) =
      inner ℂ (pointExactIsometry hgap x)
        (pointTaylorCoefficient q 2 (pointExactIsometry hgap x) -
          pointTaylorCoefficient q 1 (pointCorrector hgap q x)) := by
  simp only [pointCompressedJet, sub_apply, ContinuousLinearMap.comp_apply,
    inner_sub_right, ContinuousLinearMap.adjoint_inner_right]
  rfl

/-- Actual-Yee ray jet with the corrector and simplicity derived from the
selected exact cluster. The branch hypotheses are precisely those furnished
by the normalized even analytic eigenbranch construction. -/
theorem pointBranch_second_derivative (hgap : PointClusterComplementGap)
    (q : PeriodicYee.Momentum) (value : ℂ → ℂ) (u : ℂ → PointSpace)
    (hv : AnalyticAt ℂ value 0) (hu : AnalyticAt ℂ u 0)
    (hsolve : ∀ᶠ t in 𝓝 (0 : ℂ), pointHolomorphicOperator
      (t • YeeAnalytic.realMomentum q) (u t) = value t • u t)
    (hv0 : value 0 = (pointEnergy : ℂ)) (hu0 : u 0 = pointEigenbasis pointIndex0)
    (hnorm : ∀ᶠ t in 𝓝 (0 : ℂ), inner ℂ (pointEigenbasis pointIndex0) (u t) = 1)
    (heven : ∀ᶠ t in 𝓝 (0 : ℂ), value (-t) = value t) :
    deriv (deriv value) 0 = (2 : ℂ) * inner ℂ (pointCenterCoordinates hgap)
      (pointCompressedJet hgap q (pointCenterCoordinates hgap)) := by
  have hsimple (v : PointSpace) (horth : inner ℂ (pointEigenbasis pointIndex0) v = 0)
      (hker : (YeeTaylor.euclideanMap (PrimitiveYee.fiber Concrete.material
        (timeReversalMomentum ![1,1,0])) - (pointEnergy : ℂ) • 1) v = 0) : v = 0 := by
    apply SimpleSplitting.simple_complement_kernel pointOperator pointOperator_symmetric
      pointIndex0 (pointIndex0_simple hgap) v horth
    change pointContinuousOperator v - (pointEnergy : ℂ) • v = 0 at hker
    have he := LinearMap.congr_fun pointContinuousOperator_toLinearMap v
    change pointContinuousOperator v = pointOperator v at he
    rwa [← he]
  have h := EigenbranchJet.yee_eigenvalue_second_derivative Concrete.material
    (timeReversalMomentum ![1,1,0]) q value u hv hu hsolve pointEnergy
    (pointEigenbasis pointIndex0) (pointCenterCorrector hgap q) hv0 hu0 hnorm heven
    (pointCenterCorrector_orthogonal hgap q) (pointCenterCorrector_equation hgap q) hsimple
  rw [pointCompressedJet_inner, pointCenterCoordinates_image]
  rw [pointTaylorCoefficient_positive_shift q 2 (by omega),
    pointTaylorCoefficient_positive_shift q 1 (by omega)]
  exact h

theorem pointBranch_second_derivative_lower (hgap : PointClusterComplementGap)
    (q : PeriodicYee.Momentum) (value : ℂ → ℂ) (u : ℂ → PointSpace)
    (hv : AnalyticAt ℂ value 0) (hu : AnalyticAt ℂ u 0)
    (hsolve : ∀ᶠ t in 𝓝 (0 : ℂ), pointHolomorphicOperator
      (t • YeeAnalytic.realMomentum q) (u t) = value t • u t)
    (hv0 : value 0 = (pointEnergy : ℂ)) (hu0 : u 0 = pointEigenbasis pointIndex0)
    (hnorm : ∀ᶠ t in 𝓝 (0 : ℂ), inner ℂ (pointEigenbasis pointIndex0) (u t) = 1)
    (heven : ∀ᶠ t in 𝓝 (0 : ℂ), value (-t) = value t)
    (δ : ℝ) (hjet : FiniteJetBounds (pointTaylorCoefficient q)
      (pointExactIsometry hgap).toContinuousLinearMap (pointCorrector hgap q)
      (YeeTaylor.radius q) δ pointEnergy) :
    YeeTaylor.radius q ^ 2 / 25 ≤ (deriv (deriv value) 0).re := by
  rw [pointBranch_second_derivative hgap q value u hv hu hsolve hv0 hu0 hnorm heven]
  have hl := hjet.compressedLower (pointCenterCoordinates hgap)
  rw [pointCenterCoordinates_norm, one_pow, mul_one] at hl
  change YeeTaylor.radius q ^ 2 / 50 ≤
    (inner ℂ (pointCenterCoordinates hgap)
      (pointCompressedJet hgap q (pointCenterCoordinates hgap))).re at hl
  norm_num [Complex.mul_re]
  linarith

/-- Restrict the same multivariate analytic branch to an arbitrary physical
momentum ray. This consumes the joint branch returned with its projector and
regular resolvent, without selecting a new eigenvalue. -/
theorem pointAnalyticBranch_ray_second_derivative (hgap : PointClusterComplementGap)
    (value : YeeAnalytic.ComplexMomentum → ℂ) (u : YeeAnalytic.ComplexMomentum → PointSpace)
    (hv : AnalyticAt ℂ value 0) (hu : AnalyticAt ℂ u 0)
    (hsolve : ∀ᶠ w in 𝓝 (0 : YeeAnalytic.ComplexMomentum),
      pointHolomorphicOperator w (u w) = value w • u w)
    (hv0 : value 0 = (pointEnergy : ℂ)) (hu0 : u 0 = pointEigenbasis pointIndex0)
    (hnorm : ∀ w, inner ℂ (pointEigenbasis pointIndex0) (u w) = 1)
    (heven : ∀ᶠ w in 𝓝 (0 : YeeAnalytic.ComplexMomentum), value (-w) = value w)
    (q : PeriodicYee.Momentum) :
    deriv (deriv (fun t : ℂ => value (t • YeeAnalytic.realMomentum q))) 0 =
      (2 : ℂ) * inner ℂ (pointCenterCoordinates hgap)
        (pointCompressedJet hgap q (pointCenterCoordinates hgap)) := by
  have hray : AnalyticAt ℂ (fun t : ℂ => t • YeeAnalytic.realMomentum q) 0 :=
    analyticAt_id.smul analyticAt_const
  have ht : Tendsto (fun t : ℂ => t • YeeAnalytic.realMomentum q) (𝓝 0) (𝓝 0) := by
    simpa only [zero_smul] using hray.continuousAt.tendsto
  apply pointBranch_second_derivative hgap q
    (fun t : ℂ => value (t • YeeAnalytic.realMomentum q))
    (fun t : ℂ => u (t • YeeAnalytic.realMomentum q))
    (hv.comp_of_eq hray (by simp only [zero_smul]))
    (hu.comp_of_eq hray (by simp only [zero_smul])) (ht.eventually hsolve)
  · simpa only [zero_smul] using hv0
  · simpa only [zero_smul] using hu0
  · exact Eventually.of_forall fun t => hnorm (t • YeeAnalytic.realMomentum q)
  · simpa only [neg_smul] using ht.eventually heven

theorem pointAnalyticBranch_ray_second_derivative_lower (hgap : PointClusterComplementGap)
    (value : YeeAnalytic.ComplexMomentum → ℂ) (u : YeeAnalytic.ComplexMomentum → PointSpace)
    (hv : AnalyticAt ℂ value 0) (hu : AnalyticAt ℂ u 0)
    (hsolve : ∀ᶠ w in 𝓝 (0 : YeeAnalytic.ComplexMomentum),
      pointHolomorphicOperator w (u w) = value w • u w)
    (hv0 : value 0 = (pointEnergy : ℂ)) (hu0 : u 0 = pointEigenbasis pointIndex0)
    (hnorm : ∀ w, inner ℂ (pointEigenbasis pointIndex0) (u w) = 1)
    (heven : ∀ᶠ w in 𝓝 (0 : YeeAnalytic.ComplexMomentum), value (-w) = value w)
    (q : PeriodicYee.Momentum) (δ : ℝ)
    (hjet : FiniteJetBounds (pointTaylorCoefficient q)
      (pointExactIsometry hgap).toContinuousLinearMap (pointCorrector hgap q)
      (YeeTaylor.radius q) δ pointEnergy) :
    YeeTaylor.radius q ^ 2 / 25 ≤
      (deriv (deriv (fun t : ℂ => value (t • YeeAnalytic.realMomentum q))) 0).re := by
  rw [pointAnalyticBranch_ray_second_derivative hgap value u hv hu hsolve hv0 hu0 hnorm heven q]
  have hl := hjet.compressedLower (pointCenterCoordinates hgap)
  rw [pointCenterCoordinates_norm, one_pow, mul_one] at hl
  change YeeTaylor.radius q ^ 2 / 50 ≤
    (inner ℂ (pointCenterCoordinates hgap)
      (pointCompressedJet hgap q (pointCenterCoordinates hgap))).re at hl
  norm_num [Complex.mul_re]
  linarith

end
end Maxwell.Certificate.PointWitness
