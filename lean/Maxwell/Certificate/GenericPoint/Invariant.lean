import Maxwell.Certificate.GenericPoint.ExactFrame

namespace Maxwell.Certificate.GenericPoint.Data
open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
noncomputable section
variable (D : GenericPoint.Data)

def continuousOperator : Space →L[ℂ] Space :=
  Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (PrimitiveYee.fiber Concrete.material (timeReversalMomentum D.k))

theorem continuousOperator_toLinearMap :
    D.continuousOperator.toLinearMap = (operator D.k) :=
  Matrix.coe_toEuclideanCLM_eq_toEuclideanLin (PrimitiveYee.fiber Concrete.material (timeReversalMomentum D.k))

def shiftedOperator (E : ℝ) : Space →L[ℂ] Space :=
  D.continuousOperator - (E : ℂ) • ContinuousLinearMap.id ℂ Space

theorem shiftedOperator_eq_coefficient (q : PeriodicYee.Momentum) (E : ℝ) :
    YeeTaylor.shiftedOperatorCoefficient Concrete.material
      (timeReversalMomentum D.k) q E 0 = D.shiftedOperator E := by
  change Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
      (YeeTaylor.shiftedFiberCoefficient Concrete.material
        (timeReversalMomentum D.k) q E 0) = _
  rw [YeeTaylor.shiftedFiberCoefficient_zero, map_sub, map_smul, map_one]
  rfl

theorem projection_commutes_operator (x : Space) :
    D.projection ((operator D.k) x) = (operator D.k) (D.projection x) := by
  apply D.eigenbasis.repr.injective
  ext i
  unfold projection eigenbasis
  rw [ClusterProjection.repr_projection,
    (operator_symmetric D.k).eigenvectorBasis_apply_self_apply,
    (operator_symmetric D.k).eigenvectorBasis_apply_self_apply,
    ClusterProjection.repr_projection]
  split_ifs <;> simp

theorem exactIsometry_projection (hgap : D.ComplementGap) :
    D.projection.comp (D.exactIsometry hgap).toContinuousLinearMap =
      (D.exactIsometry hgap).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  have hm : D.exactIsometry hgap x ∈ LinearMap.range D.projection.toLinearMap := by
    rw [← D.exactIsometry_range hgap]
    exact ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hm
  change D.projection (D.exactIsometry hgap x) = D.exactIsometry hgap x
  rw [← hy]
  exact congrArg (fun L : Space →L[ℂ] Space => L y)
    (ClusterProjection.projection_idempotent D.eigenbasis D.cluster)

/-- The orthonormal frame reconstructs precisely the actual spectral projector. -/
theorem exactIsometry_comp_adjoint (hgap : D.ComplementGap) :
    (D.exactIsometry hgap).toContinuousLinearMap.comp
      (D.exactIsometry hgap).toContinuousLinearMap.adjoint = D.projection := by
  let Φ := D.exactIsometry hgap
  have hrange : LinearMap.range Φ.toLinearMap =
      LinearMap.range D.projection.toLinearMap := D.exactIsometry_range hgap
  have hp : D.projection =
      (LinearMap.range D.projection.toLinearMap).starProjection :=
    ClusterProjection.projection_eq_starProjection_range D.eigenbasis D.cluster
  apply ContinuousLinearMap.ext
  intro x
  change Φ (Φ.toContinuousLinearMap.adjoint x) = D.projection x
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
theorem shiftedOperator_exactFrame_invariant (hgap : D.ComplementGap) (E : ℝ) :
    (D.exactIsometry hgap).toContinuousLinearMap.comp
        ((D.exactIsometry hgap).toContinuousLinearMap.adjoint.comp
          ((D.shiftedOperator E).comp (D.exactIsometry hgap).toContinuousLinearMap)) =
      (D.shiftedOperator E).comp (D.exactIsometry hgap).toContinuousLinearMap := by
  rw [← ContinuousLinearMap.comp_assoc, D.exactIsometry_comp_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  have hfix := congrArg
    (fun L : EuclideanSpace ℂ (Fin 2) →L[ℂ] Space => L x)
    (D.exactIsometry_projection hgap)
  change D.projection (D.exactIsometry hgap x) = D.exactIsometry hgap x at hfix
  have hc := D.projection_commutes_operator (D.exactIsometry hgap x)
  change D.projection
      (D.continuousOperator (D.exactIsometry hgap x) -
        (E : ℂ) • D.exactIsometry hgap x) =
    D.continuousOperator (D.exactIsometry hgap x) -
      (E : ℂ) • D.exactIsometry hgap x
  rw [map_sub, map_smul, hfix]
  have he (v : Space) : D.continuousOperator v = (operator D.k) v :=
    LinearMap.congr_fun D.continuousOperator_toLinearMap v
  rw [he, hc, hfix]


end
end Maxwell.Certificate.GenericPoint.Data
