import Maxwell.Continuum.FiniteAuxiliaryBlocks
import Maxwell.Continuum.AuxiliaryResolvent

/-! Literal finite auxiliary response V_d^-1 - Q R_sigma Q*. The
compression and its detuning bound use the whole infinite-dimensional
well union and are independent of the number of sites. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary

variable {ι : Type*} [Fintype ι]

def compressed (h : ℝ) (r : ι → Space) (R : FieldL2 →L[ℂ] FieldL2) :
    DefectSpace ι →L[ℂ] DefectSpace ι :=
  (collection h r).comp (R.comp (collection h r).adjoint)

def interactionBlock (h : ℝ) (r : ι → Space) (R : FieldL2 →L[ℂ] FieldL2) (i j : ι) :
    FieldL2 →L[ℂ] FieldL2 := (siteRestriction h (r i)).comp (R.comp (siteInsertion h (r j)))

theorem compressed_apply (h : ℝ) (r : ι → Space) (R : FieldL2 →L[ℂ] FieldL2)
    (f : DefectSpace ι) (i : ι) : compressed h r R f i = ∑ j, interactionBlock h r R i j (f j) := by
  change siteRestriction h (r i) (R ((collection h r).adjoint f)) = _
  rw [collection_adjoint, insertion_apply, map_sum, map_sum]
  rfl

theorem compressed_eq_blocks (h : ℝ) (r : ι → Space) (R : FieldL2 →L[ℂ] FieldL2) :
    compressed h r R = blockOperator (interactionBlock h r R) := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro i
  rw [compressed_apply, blockOperator_apply]

theorem compressed_sub (h : ℝ) (r : ι → Space) (R S : FieldL2 →L[ℂ] FieldL2) :
    compressed h r R-compressed h r S = compressed h r (R-S) := by
  simp only [compressed, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]

theorem compressed_norm {h : ℝ} (hh : 0 < h) (r : ι → Space)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) h⁻¹) (Metric.ball (r j) h⁻¹))
    (R : FieldL2 →L[ℂ] FieldL2) : ‖compressed h r R‖ ≤ ‖R‖ := by
  have hQ := collection_norm hh r hdisj
  have hQa : ‖(collection h r).adjoint‖ ≤ 1 := by rw [LinearIsometryEquiv.norm_map]; exact hQ
  unfold compressed
  calc
    _ ≤ ‖collection h r‖*(‖R‖*‖(collection h r).adjoint‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1*(‖R‖*1) := mul_le_mul hQ
      (mul_le_mul_of_nonneg_left hQa (norm_nonneg R)) (by positivity) zero_le_one
    _ = _ := by rw [one_mul, mul_one]

theorem compressed_selfAdjoint (h : ℝ) (r : ι → Space) (R : FieldL2 →L[ℂ] FieldL2)
    (hR : IsSelfAdjoint R) : IsSelfAdjoint (compressed h r R) := by
  change (compressed h r R).adjoint = compressed h r R
  simp only [compressed, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    hR.adjoint_eq, ContinuousLinearMap.comp_assoc]

theorem diagonal_selfAdjoint (v : ι → ℝ) : IsSelfAdjoint (diagonal v) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℂ (diagonal v f) g = inner ℂ f (diagonal v g)
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [diagonal_apply, diagonal_apply, inner_smul_left, inner_smul_right]
  simp

def auxiliaryMatrix {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space) (v : ι → ℝ) :
    DefectSpace ι →L[ℂ] DefectSpace ι :=
  diagonal (fun i => (v i)⁻¹)-compressed h r (resolvent D hσ0 hσ)

theorem auxiliaryMatrix_selfAdjoint {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space) (v : ι → ℝ) :
    IsSelfAdjoint (auxiliaryMatrix D hσ0 hσ r v) := by
  change (auxiliaryMatrix D hσ0 hσ r v).adjoint = auxiliaryMatrix D hσ0 hσ r v
  rw [auxiliaryMatrix, map_sub,
    (diagonal_selfAdjoint (fun i : ι => (v i)⁻¹)).adjoint_eq,
    (compressed_selfAdjoint h r (resolvent D hσ0 hσ) (resolvent_selfAdjoint D hσ0 hσ)).adjoint_eq]

theorem compressed_detuning {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) h⁻¹) (Metric.ball (r j) h⁻¹)) :
    ‖compressed h r (resolvent D hσ0 hσ)-compressed h r (resolvent D le_rfl (by positivity))‖ ≤
      16*σ*(h^4)⁻¹ := by
  rw [compressed_sub]
  exact (compressed_norm D.h_pos r hdisj _).trans (resolvent_difference_norm_le D hσ0 hσ)

#print axioms compressed_eq_blocks
#print axioms auxiliaryMatrix_selfAdjoint
#print axioms compressed_detuning

end Maxwell.Continuum.FiniteAuxiliary
