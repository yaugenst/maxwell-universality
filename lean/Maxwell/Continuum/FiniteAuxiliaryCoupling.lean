import Maxwell.Continuum.FiniteAuxiliaryOperator
import Maxwell.Continuum.FiniteAuxiliaryLattice

/-! Opposite physical lattice displacements have adjoint Green blocks.
The actual axial scalar couplings are therefore identical in both orientations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass MasterConstants

attribute [local irreducible] realMode

theorem interactionBlock_adjoint {ι : Type*} (h : ℝ) (r : ι → Space)
    (R : FieldL2 →L[ℂ] FieldL2) (hR : IsSelfAdjoint R) (i j : ι) :
    (interactionBlock h r R i j).adjoint = interactionBlock h r R j i := by
  simp only [interactionBlock, ContinuousLinearMap.adjoint_comp, siteInsertion_adjoint,
    siteRestriction_adjoint, hR.adjoint_eq, ContinuousLinearMap.comp_assoc]

theorem physicalWellBlock_adjoint {L : ℕ} {z σ : ℝ} (D : Calibration (L : ℝ)⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64) (d : ℕ) (a : Bloch.Alias) :
    (physicalWellBlock D hσ0 hσ d a).adjoint = physicalWellBlock D hσ0 hσ d (-a) := by
  let p : Bool → Bloch.Alias := fun b => if b then a else 0
  have hp : interactionBlock (L : ℝ)⁻¹ (centers L d p) (resolvent D hσ0 hσ) true false =
      physicalWellBlock D hσ0 hσ d a := by
    simpa [p, interactionBlock] using
      centers_interaction D hσ0 hσ d p true false
  have hm : interactionBlock (L : ℝ)⁻¹ (centers L d p) (resolvent D hσ0 hσ) false true =
      physicalWellBlock D hσ0 hσ d (-a) := by
    simpa [p, interactionBlock] using
      centers_interaction D hσ0 hσ d p false true
  rw [← hp, interactionBlock_adjoint _ _ _ (resolvent_selfAdjoint D hσ0 hσ), hm]

theorem opposite_usefulCoupling {L : ℕ} {z : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Calibration (L : ℝ)⁻¹ z) (d : ℕ) (j : Fin 3) :
    inner ℂ (realMode D (inverse_length_le_1024 hL))
      (physicalWellBlock D le_rfl (by positivity) d (-Pi.single j 1)
        (realMode D (inverse_length_le_1024 hL))) = (usefulCoupling hL D d j : ℂ) := by
  rw [← physicalWellBlock_adjoint, ContinuousLinearMap.adjoint_inner_right,
    ← inner_conj_symm, usefulCoupling_real hL D d j]
  simp

#print axioms physicalWellBlock_adjoint
#print axioms opposite_usefulCoupling

end Maxwell.Continuum.FiniteAuxiliary
