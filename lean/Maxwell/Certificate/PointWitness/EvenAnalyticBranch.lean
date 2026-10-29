import Maxwell.Certificate.PointWitness.AnalyticBranch
import Maxwell.Spectral.AnalyticEvenBranch
import Maxwell.Spectral.SimpleReflection

namespace Maxwell.Certificate.PointWitness

open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee

noncomputable section

def pointDecomposition :
    (ℂ × SimpleSplitting.Complement pointIndex0) ≃L[ℂ] PointSpace :=
  SimpleSplitting.decomposition pointEigenbasis pointIndex0

def pointComplementReflection (hgap : PointClusterComplementGap) :
    SimpleSplitting.Complement pointIndex0 ≃L[ℂ] SimpleSplitting.Complement pointIndex0 :=
  (SimpleSplitting.complementReflectionIsometry pointEigenbasis pointIndex0 pointInversion
    (pointCluster_eigenbasis_even hgap pointIndex0 (by simp [pointCluster]))
    (YeeInversion.electricIsometry_involutive ![1,1,0])).toContinuousLinearEquiv

theorem pointReflection_intertwining (hgap : PointClusterComplementGap)
    (z : ℂ × SimpleSplitting.Complement pointIndex0) :
    pointInversion (pointDecomposition z) =
      pointDecomposition (z.1, pointComplementReflection hgap z.2) :=
  SimpleSplitting.reflection_intertwining pointEigenbasis pointIndex0 pointInversion
    (pointCluster_eigenbasis_even hgap pointIndex0 (by simp [pointCluster])) z

theorem pointHolomorphicOperator_reflection (w : YeeAnalytic.ComplexMomentum) (v : PointSpace) :
    pointInversion (pointHolomorphicOperator w v) =
      pointHolomorphicOperator (-w) (pointInversion v) :=
  YeeAnalyticInversion.holomorphicOperator_reflection ![1,1,0] 0 w v

theorem point_branch_real_germ
    (value : YeeAnalytic.ComplexMomentum → ℂ)
    (u : YeeAnalytic.ComplexMomentum → PointSpace)
    (hu : ∀ w, u w ≠ 0)
    (hsolve : ∀ᶠ w in nhds (0 : YeeAnalytic.ComplexMomentum),
      pointHolomorphicOperator w (u w) = value w • u w) :
    ∀ᶠ q in nhds (0 : PeriodicYee.Momentum), (value (YeeAnalytic.realMomentum q)).im = 0 := by
  have hc : Continuous YeeAnalytic.realMomentum := by
    unfold YeeAnalytic.realMomentum
    fun_prop
  have ht : Filter.Tendsto YeeAnalytic.realMomentum
      (nhds (0 : PeriodicYee.Momentum)) (nhds (0 : YeeAnalytic.ComplexMomentum)) := by
    have hz : YeeAnalytic.realMomentum 0 = 0 := by ext j; simp [YeeAnalytic.realMomentum]
    rw [← hz]
    exact hc.continuousAt.tendsto
  filter_upwards [ht.eventually hsolve] with q hq
  exact point_eigenvalue_real q _ _ (hu _) hq

/-- One actual primitive-band construction simultaneously supplies the
normalized analytic eigenvector, even dispersion, analytic projector and
regular resolvent. Thus the later Hessian and pole integral refer to the
same branch. -/
theorem exists_even_point_analytic_resolvent (hgap : PointClusterComplementGap) :
    ∃ value : YeeAnalytic.ComplexMomentum → ℂ,
    ∃ u : YeeAnalytic.ComplexMomentum → PointSpace,
    ∃ P : YeeAnalytic.ComplexMomentum → PointSpace →L[ℂ] PointSpace,
    ∃ R : YeeAnalytic.ComplexMomentum × ℂ → PointSpace →L[ℂ] PointSpace,
      value 0 = (pointEnergy : ℂ) ∧ u 0 = pointEigenbasis pointIndex0 ∧
      P 0 = (innerSL ℂ (pointEigenbasis pointIndex0)).smulRight
        (pointEigenbasis pointIndex0) ∧
      AnalyticAt ℂ value 0 ∧ AnalyticAt ℂ u 0 ∧ AnalyticAt ℂ P 0 ∧
      AnalyticAt ℂ R (0, 0) ∧
      (∀ w, inner ℂ (pointEigenbasis pointIndex0) (u w) = 1 ∧ u w ≠ 0) ∧
      (∀ᶠ w in nhds (0 : YeeAnalytic.ComplexMomentum),
        pointHolomorphicOperator w (u w) = value w • u w ∧ value (-w) = value w ∧
        P w * P w = P w ∧ pointHolomorphicOperator w * P w = value w • P w ∧
        P w * pointHolomorphicOperator w = value w • P w) ∧
      (∀ᶠ z in nhds ((0, 0) : YeeAnalytic.ComplexMomentum × ℂ),
        value z.1 ≠ (pointEnergy : ℂ) + z.2 →
        (pointHolomorphicOperator z.1 - ((pointEnergy : ℂ) + z.2) • 1).IsInvertible ∧
        (pointHolomorphicOperator z.1 - ((pointEnergy : ℂ) + z.2) • 1).inverse =
          (value z.1 - ((pointEnergy : ℂ) + z.2))⁻¹ • P z.1 + R z) := by
  let B := SimpleSplitting.complementaryEquiv
    (pointOperator_symmetric.eigenvalues rfl) pointIndex0 (pointIndex0_simple hgap)
  have hc (z : ℂ × SimpleSplitting.Complement pointIndex0) :
      pointHolomorphicOperator 0 (pointDecomposition z) =
        pointDecomposition ((pointEnergy : ℂ) * z.1, (pointEnergy : ℂ) • z.2 + B z.2) := by
    rw [pointHolomorphicOperator_zero]
    change pointOperator (pointDecomposition z) = _
    exact SimpleSplitting.spectral_decomposition pointOperator pointOperator_symmetric pointIndex0 z
  have hs (w : YeeAnalytic.ComplexMomentum)
      (z : ℂ × SimpleSplitting.Complement pointIndex0) :
      pointHolomorphicOperator (-w) (pointDecomposition (z.1, pointComplementReflection hgap z.2)) =
        pointDecomposition
          ((pointDecomposition.symm (pointHolomorphicOperator w (pointDecomposition z))).1,
          pointComplementReflection hgap
            (pointDecomposition.symm (pointHolomorphicOperator w (pointDecomposition z))).2) := by
    rw [← pointReflection_intertwining hgap, ← pointHolomorphicOperator_reflection]
    simpa only [pointDecomposition.apply_symm_apply] using
      pointReflection_intertwining hgap
        (pointDecomposition.symm (pointHolomorphicOperator w (pointDecomposition z)))
  obtain ⟨value, u, P, R, hv0, hu0, hP0, hv, hu, hP, hR, hn, hg, hr⟩ :=
    AnalyticEigenbranch.exists_even_analytic_resolvent_in_coordinates
      pointHolomorphicOperator (pointEnergy : ℂ) pointDecomposition B
      (pointComplementReflection hgap) pointHolomorphicOperator_analytic hc hs
  refine ⟨value, u, P, R, hv0, ?_, ?_, hv, hu, hP, hR, ?_, hg, hr⟩
  · simpa only [pointDecomposition, SimpleSplitting.decomposition_one_zero] using hu0
  · rw [hP0]
    exact AnalyticEigenbranch.spectral_first_projection pointEigenbasis pointIndex0
  · intro w
    simpa only [pointDecomposition, SimpleSplitting.decomposition_symm_fst] using hn w

end
end Maxwell.Certificate.PointWitness
