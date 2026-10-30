import Maxwell.Continuum.CalibrationSupercellOffsiteRealization
import Maxwell.Continuum.CalibrationTranslatedSandwich

/-! Global physical error for the executable rational two-well
calibration sandwich, including finite-grid and phase errors. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge Auxiliary EffectiveMass MasterConstants

variable (M : ℕ) [NeZero M]

attribute [local irreducible] physicalLift physicalOperator aliasMultiplier exactInverse
  Qh Auxiliary.fiberResolvent exactTranslatedSandwich roundedTranslatedSandwich

private theorem physicalLift_two_errors (N : ℕ)
    (A B : FiberSpace →L[ℂ] FiberSpace) (T : FieldL2 →L[ℂ] FieldL2)
    (hAB : ‖B-A‖≤(1/2 : ℝ)^(N+1))
    (hBT : ‖physicalLift M B-T‖≤(1/2 : ℝ)^(N+20)) :
    ‖physicalLift M A-T‖≤(1/2 : ℝ)^N := by
  have he : ‖physicalLift M A-physicalLift M B‖≤(1/2 : ℝ)^(N+1) := by
    apply (physicalLift_error M A B).trans
    rw [norm_sub_rev]
    exact hAB
  calc
    _ ≤ ‖physicalLift M A-physicalLift M B‖+‖physicalLift M B-T‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (1/2 : ℝ)^(N+1)+(1/2 : ℝ)^(N+20) := add_le_add he hBT
    _ ≤ (1/2 : ℝ)^(N+1)+(1/2 : ℝ)^(N+1) := by
      apply add_le_add le_rfl
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ = _ := by rw [pow_succ]; ring

theorem exactTranslatedSandwich_physical_error {L z σ : ℝ} (hL : Ls≤L)
    (D : Auxiliary.Calibration L⁻¹ z) (hσ0 : 0≤σ) (hσ : σ≤(L⁻¹)^4/64)
    (hEven : Even M) (a : Alias) (hM : 16*(L+(imageRadius a : ℝ)+1)≤(M : ℝ))
    (s : ℝ) (hs : 4≤s) (hscale : s=2*(M : ℝ)/L)
    (N ell : ℕ) (hlog : L≤(2 : ℝ)^ell)
    (hsize : Cs^4*L*((N : ℝ)+(ell : ℝ)+2)^2≤(M : ℝ)) :
    ‖physicalLift M (exactTranslatedSandwich M s hs z σ a)-
      wellInteraction D hσ0 hσ (-a)‖≤(1/2 : ℝ)^(N+20) := by
  rw [exactTranslatedSandwich]
  exact translatedProduct_physical_error M hL D hσ0 hσ hEven a hM s hs hscale N ell hlog hsize

theorem roundedTranslatedSandwich_physical_error {L : ℝ} (hL : Ls≤L)
    (s z σ : ℚ) (hs : 4≤(s : ℝ)) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ)≤σ) (hσ : (σ : ℝ)≤(L⁻¹)^4/64)
    (hEven : Even M) (a : Alias) (hM : 16*(L+(imageRadius a : ℝ)+1)≤(M : ℝ))
    (hscale : (s : ℝ)=2*(M : ℝ)/L)
    (N W ellRoot ellLength K P : ℕ) (hslog : (s : ℝ)≤(2 : ℝ)^ellRoot)
    (hLlog : L≤(2 : ℝ)^ellLength) (hW : cutoffWorkBits (N+1) ellLength≤W)
    (hK : aliasSteps (W+2) ellLength≤K) (hP : cutoffWorkBits W ellLength≤P)
    (hsize : Cs^4*L*((N : ℝ)+(ellLength : ℝ)+2)^2≤(M : ℝ)) :
    ‖physicalLift M (roundedTranslatedSandwich M s z σ D hσ0 hσ a W ellRoot K P)-
      wellInteraction D hσ0 hσ (-a)‖≤(1/2 : ℝ)^N := by
  exact physicalLift_two_errors M N
    (roundedTranslatedSandwich M s z σ D hσ0 hσ a W ellRoot K P)
    (exactTranslatedSandwich M s hs z σ a) (wellInteraction D hσ0 hσ (-a))
    (roundedTranslatedSandwich_requested_error M (length_ge_one hL) s z σ hs D hσ0 hσ
      a (N+1) W ellRoot ellLength K P hslog hLlog hW hK hP)
    (exactTranslatedSandwich_physical_error M hL D hσ0 hσ hEven a hM s hs hscale
      N ellLength hLlog hsize)

#print axioms roundedTranslatedSandwich_physical_error

end Maxwell.Continuum.Calibration.Supercell
