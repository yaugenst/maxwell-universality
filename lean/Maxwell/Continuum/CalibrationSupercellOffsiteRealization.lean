import Maxwell.Continuum.CalibrationSupercellTranslatedAlgebra
import Maxwell.Continuum.CalibrationSupercellTranslationPhysical
import Maxwell.Continuum.CalibrationSupercellOffsite
import Maxwell.Continuum.FiniteAuxiliaryTranslation

/-! The literal Fourier translation sandwich realizes the physical
two-well operator. The support and torus geometry conditions are proved
for the actual well, and the error is global in physical L². -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge Auxiliary EffectiveMass MasterConstants
open Bloch (translationOperator)

variable (M : ℕ) [NeZero M]

attribute [local irreducible] physicalLift physicalOperator aliasMultiplier exactInverse
  Qh Auxiliary.fiberResolvent

theorem translatedProduct_physical {L z σ : ℝ} (hL : Ls≤L)
    (D : Auxiliary.Calibration L⁻¹ z) (hσ0 : 0≤σ) (hσ : σ≤(L⁻¹)^4/64)
    (hEven : Even M) (a : Alias) (hM : 16*(L+(imageRadius a : ℝ)+1)≤(M : ℝ))
    (s : ℝ) (hs : 4≤s) (hscale : s=2*(M : ℝ)/L) :
    physicalLift M (aliasMultiplier (rootTorus s hs)*exactInverse M z σ*
      exactTranslation M a*aliasMultiplier (rootTorus s hs))=
      physicalWellInteraction M D hσ0 hσ (-a) := by
  have hM0 : 16*(L+1)≤(M : ℝ) := by
    have hr : (0 : ℝ)≤(imageRadius a : ℝ) := by positivity
    linarith only [hM,hr]
  have hQ (u : FiberSpace) : Qh L⁻¹ (embedding M u)=
      embedding M (aliasMultiplier (rootTorus s hs) u) := by
    subst s
    exact Qh_embedding M hEven (length_ge_one hL) hM0 hs u
  have hF (u : FiberSpace) :
      embedding M (exactTranslation M a (aliasMultiplier (rootTorus s hs) u))=
      translationOperator (latticeShift a) (Qh L⁻¹ (embedding M u)) := by
    subst s
    exact embedding_translation_well M hEven (length_ge_one hL) a hM hs u
  rw [physicalLift_translated_sandwich M _ _ _ _ _ (Qh_selfAdjoint L⁻¹) hQ
    (embedding_range_Qh M (length_ge_one hL) hM0) hF,exactInverse,physicalLift_operator]
  unfold physicalWellInteraction
  rw [FiniteAuxiliary.latticeShift_neg,neg_neg]
  rfl

theorem translatedProduct_physical_error {L z σ : ℝ} (hL : Ls≤L)
    (D : Auxiliary.Calibration L⁻¹ z) (hσ0 : 0≤σ) (hσ : σ≤(L⁻¹)^4/64)
    (hEven : Even M) (a : Alias) (hM : 16*(L+(imageRadius a : ℝ)+1)≤(M : ℝ))
    (s : ℝ) (hs : 4≤s) (hscale : s=2*(M : ℝ)/L)
    (N ell : ℕ) (hlog : L≤(2 : ℝ)^ell)
    (hsize : Cs^4*L*((N : ℝ)+(ell : ℝ)+2)^2≤(M : ℝ)) :
    ‖physicalLift M (aliasMultiplier (rootTorus s hs)*exactInverse M z σ*
      exactTranslation M a*aliasMultiplier (rootTorus s hs))-
      wellInteraction D hσ0 hσ (-a)‖≤(1/2 : ℝ)^(N+20) := by
  rw [translatedProduct_physical M hL D hσ0 hσ hEven a hM s hs hscale]
  exact physicalWellInteraction_requested_error M hL D hσ0 hσ hEven (-a) N ell
    (by simpa only [radius_neg] using hM) hlog hsize

#print axioms translatedProduct_physical
#print axioms translatedProduct_physical_error

end Maxwell.Continuum.Calibration.Supercell
