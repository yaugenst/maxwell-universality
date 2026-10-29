import Maxwell.Certificate.GenericPoint.ExactFrame
import Maxwell.Spectral.ResidualCertificate

/-! The data record consumed by the analytic wrappers is constructed from
finite residual/Gram facts. In particular, the two actual eigenvalue indices
are selected by the proved residual theorem, not asserted by an input oracle. -/
namespace Maxwell.Certificate.GenericPoint
open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
noncomputable section

structure Witness where
  k : Translation
  center : Fin 2 → ℝ
  vector : Fin 2 → Space
  residualRadius : ℝ
  gramRadius : ℝ
  gap : ℝ
  residual_nonneg : 0 ≤ residualRadius
  gram_nonneg : 0 ≤ gramRadius
  gram_small : gramRadius ≤ 1/32
  gap_gt : residualRadius < gap
  residual_sq : ∀ j, ‖operator k (vector j)-(center j:ℂ) • vector j‖^2 ≤
    residualRadius^2*‖vector j‖^2
  norm_near : ∀ j, |‖vector j‖-1| ≤ gramRadius
  inner_small : ‖inner ℂ (vector 0) (vector 1)‖ ≤ gramRadius
  projection_budget : ∀ j, residualRadius*‖vector j‖/gap ≤ gramRadius
  center_separated : center 0+2*residualRadius < center 1

namespace Witness
variable (W : Witness)

theorem vector_ne_zero (j : Fin 2) : W.vector j ≠ 0 := by
  intro hz
  have h := W.norm_near j
  rw [hz,norm_zero] at h
  norm_num at h
  have hs := W.gram_small
  linarith

private theorem exists_pair : ∃ p : Index × Index, p.1 ≠ p.2 ∧
    |(operator_symmetric W.k).eigenvalues rfl p.1-W.center 0| ≤ W.residualRadius ∧
    |(operator_symmetric W.k).eigenvalues rfl p.2-W.center 1| ≤ W.residualRadius := by
  obtain ⟨i,j,hij,hi,hj⟩ := two_distinct_eigenvalues_of_disjoint_residuals
    (operator W.k) (operator_symmetric W.k) (W.vector 0) (W.vector 1)
    (W.vector_ne_zero 0) (W.vector_ne_zero 1) (W.center 0) (W.center 1)
    W.residualRadius W.residualRadius W.residual_nonneg W.residual_nonneg
    (by linarith [W.center_separated]) (W.residual_sq 0) (W.residual_sq 1)
  exact ⟨(i,j),hij,hi,hj⟩

private def pair : Index × Index := Classical.choose W.exists_pair

def toData : Data where
  k := W.k
  center := W.center
  vector := W.vector
  index := ![W.pair.1,W.pair.2]
  distinct := (Classical.choose_spec W.exists_pair).1
  residualRadius := W.residualRadius
  gramRadius := W.gramRadius
  gap := W.gap
  residual_nonneg := W.residual_nonneg
  gram_nonneg := W.gram_nonneg
  gram_small := W.gram_small
  gap_gt := W.gap_gt
  interval := by
    intro j
    fin_cases j
    · exact (Classical.choose_spec W.exists_pair).2.1
    · exact (Classical.choose_spec W.exists_pair).2.2
  residual := by
    intro j
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg W.residual_nonneg (norm_nonneg _))).mp
    simpa only [mul_pow] using W.residual_sq j
  norm_near := W.norm_near
  inner_small := W.inner_small
  projection_budget := W.projection_budget
  center_separated := W.center_separated

@[simp] theorem toData_k : W.toData.k=W.k := rfl
@[simp] theorem toData_center : W.toData.center=W.center := rfl
@[simp] theorem toData_vector : W.toData.vector=W.vector := rfl
@[simp] theorem toData_residualRadius : W.toData.residualRadius=W.residualRadius := rfl
@[simp] theorem toData_gramRadius : W.toData.gramRadius=W.gramRadius := rfl
@[simp] theorem toData_gap : W.toData.gap=W.gap := rfl

end Witness
end
end Maxwell.Certificate.GenericPoint
