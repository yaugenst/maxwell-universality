import Maxwell.Certificate.PointWitness.CenterBounds
import Maxwell.Certificate.PointWitness.ExactFrameParity
import Maxwell.Spectral.AnalyticEigenbranch
import Maxwell.Spectral.YeeAnalytic

namespace Maxwell.Certificate.PointWitness

open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee

noncomputable section

def pointHolomorphicOperator (z : YeeAnalytic.ComplexMomentum) : PointSpace →L[ℂ] PointSpace :=
  YeeAnalytic.holomorphicOperator Concrete.material
    (timeReversalMomentum ![1,1,0]) 0 z

theorem pointHolomorphicOperator_zero : pointHolomorphicOperator 0 = pointContinuousOperator := by
  rw [pointHolomorphicOperator, YeeAnalytic.holomorphicOperator_zero]
  simp only [Complex.ofReal_zero, zero_smul, sub_zero]
  rfl

theorem pointHolomorphicOperator_analytic : AnalyticAt ℂ pointHolomorphicOperator 0 :=
  YeeAnalytic.holomorphicOperator_analyticAt _ _ _ _

theorem pointHolomorphicOperator_real_symmetric (q : PeriodicYee.Momentum) :
    (pointHolomorphicOperator (YeeAnalytic.realMomentum q)).toLinearMap.IsSymmetric := by
  unfold pointHolomorphicOperator YeeAnalytic.holomorphicOperator
  simp only [Complex.ofReal_zero, zero_smul, sub_zero]
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  exact YeeAnalytic.holomorphicFiber_real_hermitian _ _ _

/-- Reality follows from the actual selfadjoint real-momentum fiber and the
eigenpair equation, without assuming reality of an analytic branch. -/
theorem point_eigenvalue_real (q : PeriodicYee.Momentum) (c : ℂ) (v : PointSpace)
    (hv : v ≠ 0) (heq : pointHolomorphicOperator (YeeAnalytic.realMomentum q) v = c • v) :
    c.im = 0 := by
  have he : Module.End.HasEigenvalue
      (pointHolomorphicOperator (YeeAnalytic.realMomentum q)).toLinearMap c :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr heq, hv⟩
  have hc := (pointHolomorphicOperator_real_symmetric q).conj_eigenvalue_eq_self he
  have hi := congrArg Complex.im hc
  change -c.im = c.im at hi
  linarith

/-- The actual primitive Yee family has a constructed analytic selected
eigenvalue, projector and regular resolvent. Only the named finite point
isolation remains as input; no analytic branch is supplied. -/
theorem exists_point_analytic_resolvent (hgap : PointClusterComplementGap) :
    ∃ value : YeeAnalytic.ComplexMomentum → ℂ,
    ∃ P : YeeAnalytic.ComplexMomentum → PointSpace →L[ℂ] PointSpace,
    ∃ R : YeeAnalytic.ComplexMomentum × ℂ → PointSpace →L[ℂ] PointSpace,
      value 0 = (pointEnergy : ℂ) ∧
      P 0 = (innerSL ℂ (pointEigenbasis pointIndex0)).smulRight
        (pointEigenbasis pointIndex0) ∧
      AnalyticAt ℂ value 0 ∧ AnalyticAt ℂ P 0 ∧ AnalyticAt ℂ R (0, 0) ∧
      (∀ᶠ w in nhds (0 : YeeAnalytic.ComplexMomentum),
        P w * P w = P w ∧ pointHolomorphicOperator w * P w = value w • P w ∧
        P w * pointHolomorphicOperator w = value w • P w) ∧
      (∀ᶠ z in nhds ((0, 0) : YeeAnalytic.ComplexMomentum × ℂ),
        value z.1 ≠ (pointEnergy : ℂ) + z.2 →
        (pointHolomorphicOperator z.1 - ((pointEnergy : ℂ) + z.2) • 1).IsInvertible ∧
        (pointHolomorphicOperator z.1 - ((pointEnergy : ℂ) + z.2) • 1).inverse =
          (value z.1 - ((pointEnergy : ℂ) + z.2))⁻¹ • P z.1 + R z) := by
  have hT : (pointHolomorphicOperator 0).toLinearMap.IsSymmetric := by
    rw [pointHolomorphicOperator_zero]
    exact pointContinuousOperator_symmetric
  have hs (j : PointIndex) (hj : j ≠ pointIndex0) :
      hT.eigenvalues rfl j ≠ hT.eigenvalues rfl pointIndex0 := by
    simpa only [pointHolomorphicOperator_zero, pointContinuousOperator_toLinearMap]
      using pointIndex0_simple hgap j hj
  simpa only [pointHolomorphicOperator_zero, pointContinuousOperator_toLinearMap,
    pointEnergy, pointEigenbasis] using
      AnalyticEigenbranch.exists_analytic_resolvent_of_hermitian_simple
        pointHolomorphicOperator pointHolomorphicOperator_analytic hT pointIndex0 hs

end
end Maxwell.Certificate.PointWitness
