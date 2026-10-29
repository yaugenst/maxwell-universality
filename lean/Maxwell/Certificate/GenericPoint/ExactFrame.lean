import Maxwell.Spectral.ClusterOrthonormalization
import Maxwell.Spectral.YeeTaylor
import Maxwell.Spectral.Concrete

/-! A single exact-frame construction for every checked primitive TRIM.
The input fields are finite witness inequalities; the exact frame is constructed
from the actual Yee spectral projection, rather than supplied by the checker. -/
namespace Maxwell.Certificate.GenericPoint
open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
noncomputable section
abbrev Space := EuclideanSpace ℂ Electric
abbrev Index := Fin (Module.finrank ℂ Space)

def operator (k : Translation) : Space →ₗ[ℂ] Space :=
  (PrimitiveYee.fiber Concrete.material (timeReversalMomentum k)).toEuclideanLin

theorem operator_symmetric (k : Translation) : (operator k).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (PrimitiveYee.fiber_hermitian _ _)

/-- Checked residual and Gram budgets, with no hard-coded selected L point. -/
structure Data where
  k : Translation
  center : Fin 2 → ℝ
  vector : Fin 2 → Space
  index : Fin 2 → Index
  distinct : index 0 ≠ index 1
  residualRadius : ℝ
  gramRadius : ℝ
  gap : ℝ
  residual_nonneg : 0 ≤ residualRadius
  gram_nonneg : 0 ≤ gramRadius
  gram_small : gramRadius ≤ 1/32
  gap_gt : residualRadius < gap
  interval : ∀ j, |(operator_symmetric k).eigenvalues rfl (index j) - center j| ≤ residualRadius
  residual : ∀ j, ‖operator k (vector j) - (center j : ℂ) • vector j‖ ≤ residualRadius * ‖vector j‖
  norm_near : ∀ j, |‖vector j‖ - 1| ≤ gramRadius
  inner_small : ‖inner ℂ (vector 0) (vector 1)‖ ≤ gramRadius
  projection_budget : ∀ j, residualRadius * ‖vector j‖ / gap ≤ gramRadius
  center_separated : center 0 + 2 * residualRadius < center 1

namespace Data
variable (D : Data)
def cluster : Finset Index := {D.index 0,D.index 1}
def ComplementGap : Prop := ∀ i : Index, i ∉ D.cluster → ∀ j : Fin 2,
  D.gap ≤ |(operator_symmetric D.k).eigenvalues rfl i - D.center j|
def eigenbasis : OrthonormalBasis Index ℂ Space := (operator_symmetric D.k).eigenvectorBasis rfl
def projection : Space →L[ℂ] Space := ClusterProjection.projection D.eigenbasis D.cluster
def projected (j : Fin 2) : Space := D.projection (D.vector j)
def exactFrame : Fin 2 → Space := ClusterOrthonormalization.frame (D.projected 0) (D.projected 1)
def referenceMap : EuclideanSpace ℂ (Fin 2) →L[ℂ] Space :=
  ClusterOrthonormalization.frameMap ![D.vector 0,D.vector 1]

theorem gap_pos : 0 < D.gap := D.residual_nonneg.trans_lt D.gap_gt

theorem projected_close (hgap : D.ComplementGap) (j : Fin 2) :
    ‖D.projected j-D.vector j‖ ≤ D.gramRadius := by
  have hp := ClusterProjection.hermitian_projection_error (operator_symmetric D.k)
    D.cluster (D.center j) D.gap D.gap_pos (fun i hi => hgap i hi j) (D.vector j)
  have hr := div_le_div_of_nonneg_right (D.residual j) D.gap_pos.le
  have h := hp.trans (hr.trans (D.projection_budget j))
  simpa only [projected,projection,eigenbasis,norm_sub_rev] using h

theorem exactFrame_orthonormal (hgap : D.ComplementGap) : Orthonormal ℂ D.exactFrame :=
  (ClusterOrthonormalization.frame_orthonormal_and_close (D.vector 0) (D.vector 1)
    (D.projected 0) (D.projected 1) D.gramRadius D.gram_nonneg D.gram_small
    (D.norm_near 0) (D.norm_near 1) D.inner_small (D.projected_close hgap 0)
    (D.projected_close hgap 1)).1

def exactIsometry (hgap : D.ComplementGap) : EuclideanSpace ℂ (Fin 2) →ₗᵢ[ℂ] Space :=
  ClusterOrthonormalization.frameIsometry D.exactFrame (D.exactFrame_orthonormal hgap)

theorem projection_range : LinearMap.range D.projection.toLinearMap =
    Submodule.span ℂ (Set.range ![D.eigenbasis (D.index 0),D.eigenbasis (D.index 1)]) := by
  rw [projection,ClusterProjection.projection_range]
  congr 1
  simp only [cluster,Finset.coe_insert,Finset.coe_singleton,Set.image_insert_eq,
    Set.image_singleton,Matrix.range_cons_cons_empty]

theorem projection_finrank_le_two : Module.finrank ℂ (LinearMap.range D.projection.toLinearMap) ≤ 2 := by
  rw [D.projection_range]
  simpa only [Set.finrank,Fintype.card_fin] using
    (finrank_range_le_card (R := ℂ) ![D.eigenbasis (D.index 0),D.eigenbasis (D.index 1)])

theorem exactFrame_span (hgap : D.ComplementGap) :
    Submodule.span ℂ (Set.range D.exactFrame) = LinearMap.range D.projection.toLinearMap := by
  have hi : Submodule.span ℂ (Set.range D.exactFrame) ≤ LinearMap.range D.projection.toLinearMap := by
    rw [exactFrame,ClusterOrthonormalization.frame_span]
    apply Submodule.span_le.mpr
    exact Set.pair_subset_iff.mpr ⟨⟨D.vector 0,rfl⟩,⟨D.vector 1,rfl⟩⟩
  apply Submodule.eq_of_le_of_finrank_le hi
  rw [finrank_span_eq_card (D.exactFrame_orthonormal hgap).linearIndependent]
  exact D.projection_finrank_le_two

theorem exactIsometry_range (hgap : D.ComplementGap) :
    LinearMap.range (D.exactIsometry hgap).toLinearMap = LinearMap.range D.projection.toLinearMap := by
  change LinearMap.range (ClusterOrthonormalization.frameMap D.exactFrame).toLinearMap = _
  rw [ClusterOrthonormalization.frameMap_range]
  exact D.exactFrame_span hgap

theorem exactIsometry_close (hgap : D.ComplementGap) :
    ‖(D.exactIsometry hgap).toContinuousLinearMap-D.referenceMap‖ ≤ 16*D.gramRadius :=
  ClusterOrthonormalization.frameMap_close (D.vector 0) (D.vector 1)
    (D.projected 0) (D.projected 1) D.gramRadius D.gram_nonneg D.gram_small
    (D.norm_near 0) (D.norm_near 1) D.inner_small (D.projected_close hgap 0)
    (D.projected_close hgap 1)

end Data
end
end Maxwell.Certificate.GenericPoint
