import Maxwell.Certificate.PointWitness.ExactFrame
import Maxwell.Spectral.YeeTaylor

/-! Exact range invariance of the actual orthonormal point frame, including
the identity needed for the mixed center-offset estimate. -/

namespace Maxwell.Certificate.PointWitness

open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee

noncomputable section

def pointContinuousOperator : PointSpace →L[ℂ] PointSpace :=
  Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) pointFiber

theorem pointContinuousOperator_toLinearMap :
    pointContinuousOperator.toLinearMap = pointOperator :=
  Matrix.coe_toEuclideanCLM_eq_toEuclideanLin pointFiber

def pointShiftedOperator (E : ℝ) : PointSpace →L[ℂ] PointSpace :=
  pointContinuousOperator - (E : ℂ) • ContinuousLinearMap.id ℂ PointSpace

theorem pointShiftedOperator_eq_coefficient (q : PeriodicYee.Momentum) (E : ℝ) :
    YeeTaylor.shiftedOperatorCoefficient Concrete.material
      (timeReversalMomentum ![1,1,0]) q E 0 = pointShiftedOperator E := by
  change Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
      (YeeTaylor.shiftedFiberCoefficient Concrete.material
        (timeReversalMomentum ![1,1,0]) q E 0) = _
  rw [YeeTaylor.shiftedFiberCoefficient_zero, map_sub, map_smul, map_one]
  rfl

theorem pointClusterProjection_commutes_operator (x : PointSpace) :
    pointClusterProjection (pointOperator x) = pointOperator (pointClusterProjection x) := by
  apply pointEigenbasis.repr.injective
  ext i
  unfold pointClusterProjection pointEigenbasis
  rw [ClusterProjection.repr_projection,
    pointOperator_symmetric.eigenvectorBasis_apply_self_apply,
    pointOperator_symmetric.eigenvectorBasis_apply_self_apply,
    ClusterProjection.repr_projection]
  split_ifs <;> simp

theorem pointExactIsometry_projection (hgap : PointClusterComplementGap) :
    pointClusterProjection.comp (pointExactIsometry hgap).toContinuousLinearMap =
      (pointExactIsometry hgap).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  have hm : pointExactIsometry hgap x ∈ LinearMap.range pointClusterProjection.toLinearMap := by
    rw [← pointExactIsometry_range hgap]
    exact ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hm
  change pointClusterProjection (pointExactIsometry hgap x) = pointExactIsometry hgap x
  rw [← hy]
  exact congrArg (fun L : PointSpace →L[ℂ] PointSpace => L y)
    (ClusterProjection.projection_idempotent pointEigenbasis pointCluster)

/-- The orthonormal frame reconstructs precisely the actual spectral projector. -/
theorem pointExactIsometry_comp_adjoint (hgap : PointClusterComplementGap) :
    (pointExactIsometry hgap).toContinuousLinearMap.comp
      (pointExactIsometry hgap).toContinuousLinearMap.adjoint = pointClusterProjection := by
  let Φ := pointExactIsometry hgap
  have hrange : LinearMap.range Φ.toLinearMap =
      LinearMap.range pointClusterProjection.toLinearMap := pointExactIsometry_range hgap
  have hp : pointClusterProjection =
      (LinearMap.range pointClusterProjection.toLinearMap).starProjection :=
    ClusterProjection.projection_eq_starProjection_range pointEigenbasis pointCluster
  apply ContinuousLinearMap.ext
  intro x
  change Φ (Φ.toContinuousLinearMap.adjoint x) = pointClusterProjection x
  rw [hp]
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [← hrange]
    exact ⟨Φ.toContinuousLinearMap.adjoint x, rfl⟩
  · intro w hw
    rw [← hrange] at hw
    obtain ⟨v, rfl⟩ := hw
    change inner ℂ (x - Φ (Φ.toContinuousLinearMap.adjoint x)) (Φ v) = 0
    rw [inner_sub_left, Φ.inner_map_map]
    exact sub_eq_zero.mpr (Φ.toContinuousLinearMap.adjoint_inner_left v x).symm

/-- All real shifts of the center operator preserve the exact frame range. -/
theorem pointShiftedOperator_exactFrame_invariant (hgap : PointClusterComplementGap) (E : ℝ) :
    (pointExactIsometry hgap).toContinuousLinearMap.comp
        ((pointExactIsometry hgap).toContinuousLinearMap.adjoint.comp
          ((pointShiftedOperator E).comp (pointExactIsometry hgap).toContinuousLinearMap)) =
      (pointShiftedOperator E).comp (pointExactIsometry hgap).toContinuousLinearMap := by
  rw [← ContinuousLinearMap.comp_assoc, pointExactIsometry_comp_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  have hfix := congrArg
    (fun L : EuclideanSpace ℂ (Fin 2) →L[ℂ] PointSpace => L x)
    (pointExactIsometry_projection hgap)
  change pointClusterProjection (pointExactIsometry hgap x) = pointExactIsometry hgap x at hfix
  have hc := pointClusterProjection_commutes_operator (pointExactIsometry hgap x)
  change pointClusterProjection
      (pointContinuousOperator (pointExactIsometry hgap x) -
        (E : ℂ) • pointExactIsometry hgap x) =
    pointContinuousOperator (pointExactIsometry hgap x) -
      (E : ℂ) • pointExactIsometry hgap x
  rw [map_sub, map_smul, hfix]
  have he (v : PointSpace) : pointContinuousOperator v = pointOperator v :=
    LinearMap.congr_fun pointContinuousOperator_toLinearMap v
  rw [he, hc, hfix]

end
end Maxwell.Certificate.PointWitness
