import Maxwell.Continuum.CornerBridgeSelected
import Maxwell.Continuum.CornerBridgeSpectral

/-! The corner spectral gap as an actual quadratic-form inequality. -/

noncomputable section
namespace Maxwell.Continuum.CornerBridge

open Corner

variable {ι : Type*} [Fintype ι]

theorem clusterDot_finite_sum_left (f : ι → ClusterField) (u : ClusterField) :
    clusterDot (∑ i, f i) u = ∑ i, clusterDot (f i) u := by
  simp only [clusterDot,Finset.sum_apply,sum_dotProduct]
  exact Finset.sum_comm

theorem clusterDot_finite_sum_right (u : ClusterField) (f : ι → ClusterField) :
    clusterDot u (∑ i, f i) = ∑ i, clusterDot u (f i) := by
  simp only [clusterDot,Finset.sum_apply,dotProduct_sum]
  exact Finset.sum_comm

theorem cornerOperator_sum (f : ι → ClusterField) :
    clusterOperator (∑ i, f i) = ∑ i, clusterOperator (f i) := by
  funext s
  simp only [clusterOperator,Finset.sum_apply,Matrix.mulVec_sum,Finset.smul_sum]
  exact Finset.sum_comm

theorem embedding_sum_gram (a b : Parity → Vec) :
    clusterDot (∑ p, embedding p (a p)) (∑ p, embedding p (b p)) =
      8 * ∑ p, dotProduct (a p) (b p) := by
  rw [clusterDot_finite_sum_left]
  simp_rw [clusterDot_finite_sum_right,embedding_gram]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,← Finset.mul_sum]

def transverseCoefficient (p : Parity) (u : ClusterField) : Vec :=
  projection.mulVec (parityCoefficient p u)

theorem transverseCoefficient_sum (p : Parity) (u : ClusterField) :
    ∑ j, transverseCoefficient p u j = 0 := sum_projection_mulVec _

theorem transverse_decomposition (u : ClusterField) (hu : clusterProjection u = u) :
    u = ∑ p, embedding p (transverseCoefficient p u) :=
  (projected_decomposition u).trans hu |>.symm

theorem cornerOperator_embedding (p : Parity) (v : Vec) (hv : ∑ j, v j = 0) :
    clusterOperator (embedding p v) = embedding p ((parityBlock p).mulVec v) := by
  have he : projectedEmbedding p v = embedding p v := by
    rw [projectedEmbedding,projection_mulVec_transverse v hv]
  rw [← he,clusterOperator_intertwines]

theorem normalized_perp_selected_coefficient (u : ClusterField)
    (hu : clusterProjection u = u) (ho : clusterDot normalizedClusterVector u = 0) :
    dotProduct normalizedTopVector (transverseCoefficient selectedParity u) = 0 := by
  rw [normalizedClusterVector,clusterDot_smul_left,transverse_decomposition u hu,
    clusterDot_finite_sum_right] at ho
  simp only [embedding_gram,Finset.sum_ite_eq,Finset.mem_univ,ite_true] at ho
  have hr : (Real.sqrt 8)⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  have hh := (mul_eq_zero.mp ho).resolve_left hr
  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)

theorem real_corner_rayleigh_perp (u : ClusterField) (hu : clusterProjection u = u)
    (ho : clusterDot normalizedClusterVector u = 0) :
    clusterDot u (clusterOperator u) ≤ lambdaNext * clusterDot u u := by
  have hsel := normalized_perp_selected_coefficient u hu ho
  have hnorm : clusterDot u u = 8 * ∑ p, dotProduct (transverseCoefficient p u)
      (transverseCoefficient p u) := by
    conv_lhs => rw [transverse_decomposition u hu]
    exact embedding_sum_gram _ _
  have hform : clusterDot u (clusterOperator u) = 8 * ∑ p,
      dotProduct (transverseCoefficient p u) ((parityBlock p).mulVec (transverseCoefficient p u)) := by
    conv_lhs => rw [transverse_decomposition u hu,cornerOperator_sum]
    simp_rw [cornerOperator_embedding _ _ (transverseCoefficient_sum _ u)]
    exact embedding_sum_gram _ _
  rw [hform,hnorm]
  calc
    _ ≤ 8 * ∑ p, lambdaNext * dotProduct (transverseCoefficient p u) (transverseCoefficient p u) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : p = selectedParity
      · subst p
        exact selected_rayleigh _ (transverseCoefficient_sum _ u) hsel
      · exact other_parity_rayleigh p hp _
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The strict numerical root gap yields the paper's non-strict `1/20` bound. -/
theorem real_corner_gap (u : ClusterField) (hu : clusterProjection u = u)
    (ho : clusterDot normalizedClusterVector u = 0) :
    (1 / 20 : ℝ) * clusterDot u u ≤
      lambdaStar * clusterDot u u - clusterDot u (clusterOperator u) := by
  have hn : 0 ≤ clusterDot u u :=
    Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun j _ => mul_self_nonneg (u s j)))
  have hgap := mul_le_mul_of_nonneg_right top_gap.le hn
  have hform := real_corner_rayleigh_perp u hu ho
  nlinarith

end Maxwell.Continuum.CornerBridge
