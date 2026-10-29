import Maxwell.Certificate.PointWitness.ExactFrame
import Maxwell.Certificate.PointWitness.ParityComplete
import Maxwell.Certificate.InversionBinding
import Maxwell.Spectral.ClusterSymmetry
import Maxwell.Spectral.YeeSimpleSymmetry

/-! The actual point spectral projection commutes with physical inversion.
Consequently the literal witnesses' common exact parity passes to the exact
orthonormal frame and to the entire isolated two-dimensional eigenspace. -/

namespace Maxwell.Certificate.PointWitness

open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee

noncomputable section

def pointInversion : PointSpace ≃ₗᵢ[ℂ] PointSpace :=
  YeeInversion.electricIsometry ![1,1,0]

theorem pointOperator_commutes_inversion (x : PointSpace) :
    pointOperator (pointInversion x) = pointInversion (pointOperator x) := by
  have h := YeeSimpleSymmetry.centeredOperator_commutes ![1,1,0] x
  simpa only [YeeTaylorRemainder.centeredOperator, YeeDisplacement.centeredFiber_zero,
    pointOperator, pointFiber, pointInversion,
    ← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, ContinuousLinearMap.coe_coe]
    using h

theorem pointCluster_separated (hgap : PointClusterComplementGap)
    (i : PointIndex) (hi : i ∈ pointCluster) (j : PointIndex) (hj : j ∉ pointCluster) :
    pointOperator_symmetric.eigenvalues rfl i ≠
      pointOperator_symmetric.eigenvalues rfl j := by
  simp only [pointCluster, Finset.mem_insert, Finset.mem_singleton] at hi
  intro heq
  rcases hi with rfl | rfl
  · have hg := hgap j hj 0
    change 11 / 2000 ≤ |pointOperator_symmetric.eigenvalues rfl j - pointCenter0| at hg
    rw [← heq] at hg
    have hr := pointIndex0_interval
    norm_num at hr ⊢
    linarith
  · have hg := hgap j hj 1
    change 11 / 2000 ≤ |pointOperator_symmetric.eigenvalues rfl j - pointCenter1| at hg
    rw [← heq] at hg
    have hr := pointIndex1_interval
    norm_num at hr ⊢
    linarith

theorem pointSelected_eigenvalues_distinct :
    pointOperator_symmetric.eigenvalues rfl pointIndex0 ≠
      pointOperator_symmetric.eigenvalues rfl pointIndex1 := by
  intro heq
  have h0 := (abs_le.mp pointIndex0_interval).2
  have h1 := (abs_le.mp pointIndex1_interval).1
  have hc : pointCenter0 + 2 * ((1 : ℝ) / 2^47) < pointCenter1 := by
    norm_num [pointCenter0, pointCenter1, lambdaNumerator0, lambdaNumerator1]
  rw [heq] at h0
  linarith

theorem pointIndex0_simple (hgap : PointClusterComplementGap)
    (j : PointIndex) (hj : j ≠ pointIndex0) :
    pointOperator_symmetric.eigenvalues rfl j ≠
      pointOperator_symmetric.eigenvalues rfl pointIndex0 := by
  by_cases hmem : j ∈ pointCluster
  · have heq : j = pointIndex1 := by
      simpa only [pointCluster, Finset.mem_insert, Finset.mem_singleton, hj, false_or] using hmem
    exact heq ▸ Ne.symm pointSelected_eigenvalues_distinct
  · exact Ne.symm (pointCluster_separated hgap pointIndex0 (by simp [pointCluster]) j hmem)

theorem pointIndex1_simple (hgap : PointClusterComplementGap)
    (j : PointIndex) (hj : j ≠ pointIndex1) :
    pointOperator_symmetric.eigenvalues rfl j ≠
      pointOperator_symmetric.eigenvalues rfl pointIndex1 := by
  by_cases hmem : j ∈ pointCluster
  · have heq : j = pointIndex0 := by
      simpa only [pointCluster, Finset.mem_insert, Finset.mem_singleton, hj, or_false] using hmem
    exact heq ▸ pointSelected_eigenvalues_distinct
  · exact Ne.symm (pointCluster_separated hgap pointIndex1 (by simp [pointCluster]) j hmem)

theorem pointClusterProjection_commutes_inversion (hgap : PointClusterComplementGap)
    (x : PointSpace) :
    pointClusterProjection (pointInversion x) = pointInversion (pointClusterProjection x) :=
  ClusterProjection.projection_commutes_of_separated pointEigenbasis pointOperator
    (pointOperator_symmetric.eigenvalues rfl)
    (pointOperator_symmetric.eigenvectorBasis_apply_self_apply rfl)
    pointCluster (pointCluster_separated hgap) pointInversion.toLinearMap
    pointOperator_commutes_inversion x

theorem pointExactFrame_parity (hgap : PointClusterComplementGap) (σ : ℂ)
    (h0 : pointInversion pointVector0 = σ • pointVector0)
    (h1 : pointInversion pointVector1 = σ • pointVector1) (i : Fin 2) :
    pointInversion (pointExactFrame i) = σ • pointExactFrame i := by
  apply ClusterOrthonormalization.frame_parity pointInversion.toLinearMap σ
    pointProjected0 pointProjected1
  · change pointInversion (pointClusterProjection pointVector0) =
      σ • pointClusterProjection pointVector0
    rw [← pointClusterProjection_commutes_inversion hgap, h0, map_smul]
  · change pointInversion (pointClusterProjection pointVector1) =
      σ • pointClusterProjection pointVector1
    rw [← pointClusterProjection_commutes_inversion hgap, h1, map_smul]

theorem pointExactIsometry_parity (hgap : PointClusterComplementGap) (σ : ℂ)
    (h0 : pointInversion pointVector0 = σ • pointVector0)
    (h1 : pointInversion pointVector1 = σ • pointVector1) :
    HasParity pointInversion σ (pointExactIsometry hgap).toContinuousLinearMap := by
  intro x
  change pointInversion (ClusterOrthonormalization.frameMap pointExactFrame x) =
    σ • ClusterOrthonormalization.frameMap pointExactFrame x
  simp only [ClusterOrthonormalization.frameMap_apply, map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pointExactFrame_parity hgap σ h0 h1, smul_comm]

/-- The selected eigenvectors have the common parity because the constructed
same-parity frame spans their full spectral cluster. -/
theorem pointCluster_eigenbasis_parity (hgap : PointClusterComplementGap) (σ : ℂ)
    (h0 : pointInversion pointVector0 = σ • pointVector0)
    (h1 : pointInversion pointVector1 = σ • pointVector1)
    (i : PointIndex) (hi : i ∈ pointCluster) :
    pointInversion (pointEigenbasis i) = σ • pointEigenbasis i := by
  have hmem : pointEigenbasis i ∈ LinearMap.range pointClusterProjection.toLinearMap := by
    refine ⟨pointEigenbasis i, ?_⟩
    simpa only [ContinuousLinearMap.coe_coe, pointClusterProjection, hi, ite_true] using
      (ClusterProjection.projection_basis pointEigenbasis pointCluster i)
  rw [← pointExactIsometry_range hgap] at hmem
  obtain ⟨x, hx⟩ := hmem
  rw [← hx]
  exact pointExactIsometry_parity hgap σ h0 h1 x

theorem pointVector0_inversion_fixed : pointInversion pointVector0 = pointVector0 := by
  have h := PrimitiveBinding.integerVector_parity ![1,1,0] numerator0 (2^101) 1
    (fun e => by simpa only [one_mul] using numerator0_parity e)
  simpa only [pointInversion, pointVector0, Int.cast_one, one_smul] using h

theorem pointVector1_inversion_fixed : pointInversion pointVector1 = pointVector1 := by
  have h := PrimitiveBinding.integerVector_parity ![1,1,0] numerator1 (2^101) 1
    (fun e => by simpa only [one_mul] using numerator1_parity e)
  simpa only [pointInversion, pointVector1, Int.cast_one, one_smul] using h

/-- Both literal point witnesses have checked even parity, so the exact
spectral frame is even with only the complement-isolation input remaining. -/
theorem pointExactIsometry_even (hgap : PointClusterComplementGap) :
    HasParity pointInversion 1 (pointExactIsometry hgap).toContinuousLinearMap :=
  pointExactIsometry_parity hgap 1
    (by simpa only [one_smul] using pointVector0_inversion_fixed)
    (by simpa only [one_smul] using pointVector1_inversion_fixed)

theorem pointCluster_eigenbasis_even (hgap : PointClusterComplementGap)
    (i : PointIndex) (hi : i ∈ pointCluster) :
    pointInversion (pointEigenbasis i) = pointEigenbasis i := by
  simpa only [one_smul] using pointCluster_eigenbasis_parity hgap 1
    (by simpa only [one_smul] using pointVector0_inversion_fixed)
    (by simpa only [one_smul] using pointVector1_inversion_fixed) i hi

end
end Maxwell.Certificate.PointWitness
