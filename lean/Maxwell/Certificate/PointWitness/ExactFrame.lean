import Maxwell.Certificate.PointWitness
import Maxwell.Certificate.PointWitness.FrameBounds
import Maxwell.Spectral.ClusterOrthonormalization

/-!
# Exact spectral frame from the literal checked point witnesses

The two eigenvalue indices below are selected from the proved residual
certificates for the actual 6000-dimensional primitive Yee fiber.  Every
normalization, overlap, and projection-budget estimate is discharged by the
literal witness checks.  The named complement-gap predicate is the remaining
spectral-isolation input; this file does not assert that predicate.
-/

namespace Maxwell.Certificate.PointWitness

open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee

noncomputable section

abbrev PointSpace := EuclideanSpace ℂ Electric
abbrev PointIndex := Fin (Module.finrank ℂ PointSpace)

private theorem exists_verified_pair : ∃ p : PointIndex × PointIndex,
    p.1 ≠ p.2 ∧
    |pointOperator_symmetric.eigenvalues rfl p.1 - pointCenter0| ≤ 1 / 2^47 ∧
    |pointOperator_symmetric.eigenvalues rfl p.2 - pointCenter1| ≤ 1 / 2^47 := by
  obtain ⟨i, j, hij, hi, hj⟩ := two_verified_eigenvalues
  exact ⟨(i, j), hij, hi, hj⟩

private def verifiedPair : PointIndex × PointIndex := Classical.choose exists_verified_pair

def pointIndex0 : PointIndex := verifiedPair.1

def pointIndex1 : PointIndex := verifiedPair.2

theorem pointIndices_distinct : pointIndex0 ≠ pointIndex1 :=
  (Classical.choose_spec exists_verified_pair).1

theorem pointIndex0_interval :
    |pointOperator_symmetric.eigenvalues rfl pointIndex0 - pointCenter0| ≤ 1 / 2^47 :=
  (Classical.choose_spec exists_verified_pair).2.1

theorem pointIndex1_interval :
    |pointOperator_symmetric.eigenvalues rfl pointIndex1 - pointCenter1| ≤ 1 / 2^47 :=
  (Classical.choose_spec exists_verified_pair).2.2

def pointCluster : Finset PointIndex := {pointIndex0, pointIndex1}

theorem pointCluster_card : pointCluster.card = 2 := by
  simp [pointCluster, pointIndices_distinct]

def pointCenters : Fin 2 → ℝ := ![pointCenter0, pointCenter1]

/-- The still-open complement isolation, stated for the actual fiber spectrum
and both certified point centers. It is the only hypothesis of the adapter. -/
def PointClusterComplementGap : Prop :=
  ∀ i : PointIndex, i ∉ pointCluster → ∀ j : Fin 2,
    11 / 2000 ≤ |pointOperator_symmetric.eigenvalues rfl i - pointCenters j|

def pointEigenbasis : OrthonormalBasis PointIndex ℂ PointSpace :=
  pointOperator_symmetric.eigenvectorBasis rfl

def pointClusterProjection : PointSpace →L[ℂ] PointSpace :=
  ClusterProjection.projection pointEigenbasis pointCluster

def pointProjected0 : PointSpace := pointClusterProjection pointVector0

def pointProjected1 : PointSpace := pointClusterProjection pointVector1

def pointExactFrame : Fin 2 → PointSpace :=
  ClusterOrthonormalization.frame pointProjected0 pointProjected1

def pointReferenceMap : EuclideanSpace ℂ (Fin 2) →L[ℂ] PointSpace :=
  ClusterOrthonormalization.frameMap ![pointVector0, pointVector1]

private theorem pointVector0_residual_norm :
    ‖pointOperator pointVector0 - (pointCenter0 : ℂ) • pointVector0‖ ≤
      ((1 : ℝ) / 2^47) * ‖pointVector0‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))).mp
  simpa only [mul_pow] using pointVector0_residual

private theorem pointVector1_residual_norm :
    ‖pointOperator pointVector1 - (pointCenter1 : ℂ) • pointVector1‖ ≤
      ((1 : ℝ) / 2^47) * ‖pointVector1‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))).mp
  simpa only [mul_pow] using pointVector1_residual

theorem pointProjected0_close (hgap : PointClusterComplementGap) :
    ‖pointProjected0 - pointVector0‖ ≤ (1 : ℝ) / 2^39 := by
  have hp := ClusterProjection.hermitian_projection_error pointOperator_symmetric
    pointCluster pointCenter0 (11/2000) (by norm_num)
    (fun i hi => hgap i hi 0) pointVector0
  have hr := div_le_div_of_nonneg_right pointVector0_residual_norm
    (show (0 : ℝ) ≤ 11/2000 by norm_num)
  have h := hp.trans (hr.trans pointVector0_projection_budget)
  simpa only [pointProjected0, pointClusterProjection, pointEigenbasis, norm_sub_rev] using h

theorem pointProjected1_close (hgap : PointClusterComplementGap) :
    ‖pointProjected1 - pointVector1‖ ≤ (1 : ℝ) / 2^39 := by
  have hp := ClusterProjection.hermitian_projection_error pointOperator_symmetric
    pointCluster pointCenter1 (11/2000) (by norm_num)
    (fun i hi => hgap i hi 1) pointVector1
  have hr := div_le_div_of_nonneg_right pointVector1_residual_norm
    (show (0 : ℝ) ≤ 11/2000 by norm_num)
  have h := hp.trans (hr.trans pointVector1_projection_budget)
  simpa only [pointProjected1, pointClusterProjection, pointEigenbasis, norm_sub_rev] using h

theorem pointExactFrame_orthonormal (hgap : PointClusterComplementGap) :
    Orthonormal ℂ pointExactFrame :=
  (ClusterOrthonormalization.frame_orthonormal_and_close pointVector0 pointVector1
    pointProjected0 pointProjected1 ((1 : ℝ) / 2^39) (by norm_num) (by norm_num)
    pointVector0_norm_near_one pointVector1_norm_near_one pointVector_inner_small
    (pointProjected0_close hgap) (pointProjected1_close hgap)).1

def pointExactIsometry (hgap : PointClusterComplementGap) :
    EuclideanSpace ℂ (Fin 2) →ₗᵢ[ℂ] PointSpace :=
  ClusterOrthonormalization.frameIsometry pointExactFrame (pointExactFrame_orthonormal hgap)

theorem pointClusterProjection_range :
    LinearMap.range pointClusterProjection.toLinearMap =
      Submodule.span ℂ (Set.range ![pointEigenbasis pointIndex0, pointEigenbasis pointIndex1]) := by
  rw [pointClusterProjection, ClusterProjection.projection_range]
  congr 1
  simp only [pointCluster, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
    Set.image_singleton, Matrix.range_cons_cons_empty]

theorem pointClusterProjection_finrank_le_two :
    Module.finrank ℂ (LinearMap.range pointClusterProjection.toLinearMap) ≤ 2 := by
  rw [pointClusterProjection_range]
  simpa only [Set.finrank, Fintype.card_fin] using
    (finrank_range_le_card (R := ℂ) ![pointEigenbasis pointIndex0, pointEigenbasis pointIndex1])

theorem pointExactFrame_span (hgap : PointClusterComplementGap) :
    Submodule.span ℂ (Set.range pointExactFrame) =
      LinearMap.range pointClusterProjection.toLinearMap := by
  have hincl : Submodule.span ℂ (Set.range pointExactFrame) ≤
      LinearMap.range pointClusterProjection.toLinearMap := by
    rw [pointExactFrame, ClusterOrthonormalization.frame_span]
    apply Submodule.span_le.mpr
    exact Set.pair_subset_iff.mpr ⟨⟨pointVector0, rfl⟩, ⟨pointVector1, rfl⟩⟩
  apply Submodule.eq_of_le_of_finrank_le hincl
  have hd := finrank_span_eq_card (pointExactFrame_orthonormal hgap).linearIndependent
  rw [hd]
  exact pointClusterProjection_finrank_le_two

theorem pointExactIsometry_range (hgap : PointClusterComplementGap) :
    LinearMap.range (pointExactIsometry hgap).toLinearMap =
      LinearMap.range pointClusterProjection.toLinearMap := by
  change LinearMap.range (ClusterOrthonormalization.frameMap pointExactFrame).toLinearMap = _
  rw [ClusterOrthonormalization.frameMap_range]
  exact pointExactFrame_span hgap

/-- The actual constructed exact spectral frame is within `10⁻¹⁰` of the
literal checked two-column point witness in operator norm. -/
theorem pointExactIsometry_close (hgap : PointClusterComplementGap) :
    ‖(pointExactIsometry hgap).toContinuousLinearMap - pointReferenceMap‖ <
      1 / 10000000000 := by
  change ‖ClusterOrthonormalization.frameMap pointExactFrame -
    ClusterOrthonormalization.frameMap ![pointVector0, pointVector1]‖ < _
  apply (ClusterOrthonormalization.frameMap_close pointVector0 pointVector1
    pointProjected0 pointProjected1 ((1 : ℝ) / 2^39) (by norm_num) (by norm_num)
    pointVector0_norm_near_one pointVector1_norm_near_one pointVector_inner_small
    (pointProjected0_close hgap) (pointProjected1_close hgap)).trans_lt
  norm_num

end
end Maxwell.Certificate.PointWitness
