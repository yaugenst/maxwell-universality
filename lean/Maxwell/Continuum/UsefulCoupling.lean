import Maxwell.Continuum.AxialSourceAsymptotic

/-! The paper's full well blocks and useful scalar couplings, realized
by the actual continuum Maxwell resolvent on the even placement lattice. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.EffectiveMass

open Auxiliary CellGauge Bloch PeriodicBand MasterConstants

attribute [local irreducible] realMode

def physicalWellBlock {L : ℕ} {z σ : ℝ} (D : Calibration (L : ℝ)⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64) (d : ℕ) (ν : Bloch.Alias) :
    FieldL2 →L[ℂ] FieldL2 := wellInteraction D hσ0 hσ (-placementCell L d ν)

theorem physicalWellBlock_apply {L : ℕ} {z σ : ℝ} (D : Calibration (L : ℝ)⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64) (d : ℕ) (ν : Bloch.Alias) (f : FieldL2) :
    physicalWellBlock D hσ0 hσ d ν f = Qh (L : ℝ)⁻¹
      (resolvent D hσ0 hσ (fieldTranslation (latticeShift (placementCell L d ν)) (Qh (L : ℝ)⁻¹ f))) := by
  simp only [physicalWellBlock, wellInteraction, ContinuousLinearMap.comp_apply,
    latticeShift_neg, neg_neg]
  rfl

theorem placementCell_neg (L d : ℕ) (ν : Bloch.Alias) :
    placementCell L d (-ν) = -placementCell L d ν := by
  funext j
  simp only [placementCell, Matrix.mulVec_neg, Pi.neg_apply]
  ring

theorem latticeOneNorm_neg (ν : Bloch.Alias) : latticeOneNorm (-ν) = latticeOneNorm ν := by
  simp only [latticeOneNorm, Pi.neg_apply, Int.natAbs_neg]

theorem physicalWellBlock_norm {L : ℕ} {z σ : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Calibration (L : ℝ)⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64)
    (d : ℕ) (ν : Bloch.Alias) :
    ‖physicalWellBlock D hσ0 hσ d ν‖ ≤ Cs*(L : ℝ)^5*
      (((3 : ℝ)^(d*latticeOneNorm ν))⁻¹+Real.exp (-cs*(L : ℝ))) := by
  simpa only [physicalWellBlock, placementCell_neg, latticeOneNorm_neg] using
    full_interaction_bound hL D hσ0 hσ d (-ν)

theorem axialSourceCoupling_eq_block {L : ℕ} {z : ℝ} (D : Calibration (L : ℝ)⁻¹ z)
    (hh : (L : ℝ)⁻¹ ≤ 1/(2 : ℝ)^1024) (d : ℕ) (j : Fin 3) :
    axialSourceCoupling D hh j (d : ℝ) = inner ℂ (realMode D hh)
      (physicalWellBlock D le_rfl (by positivity) d (Pi.single j 1) (realMode D hh)) := by
  rw [physicalWellBlock_apply, placementCell_axial]
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (Qh_selfAdjoint (L : ℝ)⁻¹))
    (realMode D hh)
    (resolvent D le_rfl (by positivity)
      (fieldTranslation (poleAxialDisplacement (L : ℝ)⁻¹ (d : ℝ) j) (sourceMode (L : ℝ)⁻¹ (realMode D hh))))

def usefulCoupling {L : ℕ} {z : ℝ} (hL : Ls ≤ (L : ℝ)) (D : Calibration (L : ℝ)⁻¹ z)
    (d : ℕ) (j : Fin 3) : ℝ :=
  (inner ℂ (realMode D (inverse_length_le_1024 hL))
    (physicalWellBlock D le_rfl (by positivity) d (Pi.single j 1)
      (realMode D (inverse_length_le_1024 hL)))).re

theorem usefulCoupling_real {L : ℕ} {z : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Calibration (L : ℝ)⁻¹ z) (d : ℕ) (j : Fin 3) :
    inner ℂ (realMode D (inverse_length_le_1024 hL))
      (physicalWellBlock D le_rfl (by positivity) d (Pi.single j 1)
        (realMode D (inverse_length_le_1024 hL))) = (usefulCoupling hL D d j : ℂ) := by
  apply Complex.ext
  · rfl
  · rw [← axialSourceCoupling_eq_block, axialSourceCoupling_real, Complex.ofReal_im]

theorem usefulCoupling_lower {L : ℕ} {z : ℝ} (hL : Ls ≤ (L : ℝ)) (hLe : Even L)
    (D : Calibration (L : ℝ)⁻¹ z) {d : ℕ} (hd : ds ≤ (d : ℝ))
    (hspace : Cs^4*(L : ℝ) ≤ (d : ℝ)^15)
    (htail : Cs*(L : ℝ)^5*Real.exp (-cs*(L : ℝ)) ≤
      (cu/4)*(L : ℝ)^2*(8 : ℝ)^(-(d : ℝ))) (j : Fin 3) :
    cu*(L : ℝ)^2*(8 : ℝ)^(-(d : ℝ)) ≤ usefulCoupling hL D d j := by
  unfold usefulCoupling
  rw [← axialSourceCoupling_eq_block]
  exact axialSourceCoupling_lower hL hLe D j hd hspace htail

theorem useful_unwanted_base_margin : ((1 : ℝ)/3)^2 < 1/8 := by norm_num

#print axioms physicalWellBlock_norm
#print axioms usefulCoupling_lower

end Maxwell.Continuum.EffectiveMass
