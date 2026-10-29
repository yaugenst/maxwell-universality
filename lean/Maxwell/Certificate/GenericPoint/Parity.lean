import Maxwell.Certificate.GenericPoint.ExactFrame
import Maxwell.Spectral.ClusterSymmetry
import Maxwell.Spectral.YeeSimpleSymmetry

namespace Maxwell.Certificate.GenericPoint.Data
open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
noncomputable section
variable (D : GenericPoint.Data)

def inversion : Space ≃ₗᵢ[ℂ] Space := YeeInversion.electricIsometry D.k

theorem operator_commutes_inversion (x : Space) :
    operator D.k (D.inversion x) = D.inversion (operator D.k x) := by
  have h := YeeSimpleSymmetry.centeredOperator_commutes D.k x
  simpa only [YeeTaylorRemainder.centeredOperator,YeeDisplacement.centeredFiber_zero,
    operator,inversion,← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
    ContinuousLinearMap.coe_coe] using h

theorem cluster_separated (hgap : D.ComplementGap)
    (i : Index) (hi : i ∈ D.cluster) (j : Index) (hj : j ∉ D.cluster) :
    (operator_symmetric D.k).eigenvalues rfl i ≠ (operator_symmetric D.k).eigenvalues rfl j := by
  simp only [cluster,Finset.mem_insert,Finset.mem_singleton] at hi
  intro heq
  rcases hi with rfl | rfl
  · have hg := hgap j hj 0
    rw [← heq] at hg
    exact (not_le_of_gt D.gap_gt) (hg.trans (D.interval 0))
  · have hg := hgap j hj 1
    rw [← heq] at hg
    exact (not_le_of_gt D.gap_gt) (hg.trans (D.interval 1))

theorem selected_eigenvalues_distinct :
    (operator_symmetric D.k).eigenvalues rfl (D.index 0) ≠
      (operator_symmetric D.k).eigenvalues rfl (D.index 1) := by
  intro heq
  have h0 := (abs_le.mp (D.interval 0)).2
  have h1 := (abs_le.mp (D.interval 1)).1
  have hc := D.center_separated
  rw [heq] at h0
  linarith

theorem projection_commutes_inversion (hgap : D.ComplementGap) (x : Space) :
    D.projection (D.inversion x) = D.inversion (D.projection x) :=
  ClusterProjection.projection_commutes_of_separated D.eigenbasis (operator D.k)
    ((operator_symmetric D.k).eigenvalues rfl)
    ((operator_symmetric D.k).eigenvectorBasis_apply_self_apply rfl)
    D.cluster (D.cluster_separated hgap) D.inversion.toLinearMap D.operator_commutes_inversion x

theorem exactFrame_parity (hgap : D.ComplementGap) (σ : ℂ)
    (hv : ∀ j, D.inversion (D.vector j) = σ • D.vector j) (i : Fin 2) :
    D.inversion (D.exactFrame i) = σ • D.exactFrame i := by
  apply ClusterOrthonormalization.frame_parity D.inversion.toLinearMap σ
    (D.projected 0) (D.projected 1)
  · change D.inversion (D.projection (D.vector 0)) = σ • D.projection (D.vector 0)
    rw [← D.projection_commutes_inversion hgap,hv,map_smul]
  · change D.inversion (D.projection (D.vector 1)) = σ • D.projection (D.vector 1)
    rw [← D.projection_commutes_inversion hgap,hv,map_smul]

theorem exactIsometry_parity (hgap : D.ComplementGap) (σ : ℂ)
    (hv : ∀ j, D.inversion (D.vector j) = σ • D.vector j) :
    HasParity D.inversion σ (D.exactIsometry hgap).toContinuousLinearMap := by
  intro x
  change D.inversion (ClusterOrthonormalization.frameMap D.exactFrame x) =
    σ • ClusterOrthonormalization.frameMap D.exactFrame x
  simp only [ClusterOrthonormalization.frameMap_apply,map_sum,map_smul,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [D.exactFrame_parity hgap σ hv,smul_comm]

theorem cluster_eigenbasis_parity (hgap : D.ComplementGap) (σ : ℂ)
    (hv : ∀ j, D.inversion (D.vector j) = σ • D.vector j)
    (i : Index) (hi : i ∈ D.cluster) :
    D.inversion (D.eigenbasis i) = σ • D.eigenbasis i := by
  have hm : D.eigenbasis i ∈ LinearMap.range D.projection.toLinearMap := by
    refine ⟨D.eigenbasis i,?_⟩
    simpa only [ContinuousLinearMap.coe_coe,projection,hi,ite_true] using
      (ClusterProjection.projection_basis D.eigenbasis D.cluster i)
  rw [← D.exactIsometry_range hgap] at hm
  obtain ⟨x,hx⟩ := hm
  rw [← hx]
  exact D.exactIsometry_parity hgap σ hv x

end
end Maxwell.Certificate.GenericPoint.Data
