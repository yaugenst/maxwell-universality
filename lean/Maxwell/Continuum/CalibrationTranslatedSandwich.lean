import Maxwell.Continuum.CalibrationSandwichPrecision
import Maxwell.Continuum.CalibrationSupercellTranslation
import Maxwell.Continuum.CalibrationFiniteApplication
import Maxwell.Continuum.CalibrationTranslatedSandwichEstimate
import Maxwell.Continuum.CalibrationRootOperatorBounds

/-! The actual finite two-well calibration application, including its
translation character and all inverse aliases. -/

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000

attribute [local irreducible] roundedGridFull roundedInverse exactInverse
  Auxiliary.fiberResolvent PeriodicBand.scaledBand PeriodicPerturbation.perturbation
  PeriodicPerturbation.finiteK CornerBridge.topState
  rootDegree rootDegreeValue computedRootConvolution

variable (M : ℕ) [NeZero M]

noncomputable def exactTranslatedSandwich (s : ℝ) (hs : 4 ≤ s) (z σ : ℝ) (a : Alias) :
    FiberSpace →L[ℂ] FiberSpace :=
  aliasMultiplier (rootTorus s hs)*exactInverse M z σ*exactTranslation M a*
    aliasMultiplier (rootTorus s hs)

noncomputable def roundedTranslatedSandwich {L : ℝ} (s z σ : ℚ)
    (D : Auxiliary.Calibration L⁻¹ z) (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64)
    (a : Alias) (W ell K P : ℕ) : FiberSpace →L[ℂ] FiberSpace :=
  computedRootConvolution s W ell*roundedInverse M z σ D hσ0 hσ K P*
    roundedTranslation M a W*computedRootConvolution s W ell

attribute [local irreducible] exactTranslatedSandwich roundedTranslatedSandwich

omit [NeZero M] in
private theorem fiber_translated_bound {L ε : ℝ}
    (A B Q Qb R Rb U Ub : FiberSpace →L[ℂ] FiberSpace)
    (hQ : ‖Q‖ ≤ 1) (hQb : ‖Qb‖ ≤ 2) (hQe : ‖Q-Qb‖ ≤ ε)
    (hR : ‖R‖ ≤ 4*L^2) (hRb : ‖Rb‖ ≤ 5*L^2) (hRe : ‖R-Rb‖ ≤ ε)
    (hU : ‖U‖ ≤ 1) (hUb : ‖Ub‖ ≤ 2) (hUe : ‖U-Ub‖ ≤ ε)
    (hA : A=Q*R*U*Q) (hB : B=Qb*Rb*Ub*Qb) :
    ‖A-B‖ ≤ (34*L^2+2)*ε := by
  rw [hA,hB]
  exact translated_sandwich_difference Q Qb R Rb U Ub hQ hQb hQe hR hRb hRe hU hUb hUe

theorem roundedTranslatedSandwich_error {L : ℝ} (hL : 1 ≤ L) (s z σ : ℚ)
    (hs : 4 ≤ (s : ℝ)) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64)
    (a : Alias) (W ellRoot ellLength K P : ℕ) (hslog : (s : ℝ) ≤ (2 : ℝ)^ellRoot)
    (hLlog : L ≤ (2 : ℝ)^ellLength)
    (hK : aliasSteps (W+2) ellLength ≤ K) (hP : cutoffWorkBits W ellLength ≤ P) :
    ‖exactTranslatedSandwich M s hs z σ a-
        roundedTranslatedSandwich M s z σ D hσ0 hσ a W ellRoot K P‖ ≤
      (34*L^2+2)*(1/2 : ℝ)^W := by
  exact fiber_translated_bound
    (exactTranslatedSandwich M s hs z σ a)
    (roundedTranslatedSandwich M s z σ D hσ0 hσ a W ellRoot K P)
    (aliasMultiplier (rootTorus (s : ℝ) hs)) (computedRootConvolution s W ellRoot)
    (exactInverse M z σ) (roundedInverse M z σ D hσ0 hσ K P)
    (exactTranslation M a) (roundedTranslation M a W)
    (exactRootOperator_norm s hs)
    (computedRootConvolution_norm s hs W ellRoot hslog)
    (computedRootConvolution_error s hs W ellRoot hslog)
    (exactInverse_norm M D hσ0 hσ)
    (roundedInverse_norm M hL z σ D hσ0 hσ W ellLength K P hLlog hK hP)
    (roundedInverse_error M hL z σ D hσ0 hσ W ellLength K P hLlog hK hP)
    (exactTranslation_norm M a) (roundedTranslation_norm M a W)
    ((norm_sub_rev _ _).trans_le (roundedTranslation_error M a W))
    (by unfold exactTranslatedSandwich; rfl) (by unfold roundedTranslatedSandwich; rfl)

theorem translated_precision_error {L : ℝ} (hL : 1 ≤ L) (N ell W : ℕ)
    (hlog : L ≤ (2 : ℝ)^ell) (hW : cutoffWorkBits N ell ≤ W) :
    (34*L^2+2)*(1/2 : ℝ)^W ≤ (1/2 : ℝ)^N := by
  have hpow : L^2 ≤ (2 : ℝ)^(2*ell) := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ L) hlog 2
    simpa only [← pow_mul,Nat.mul_comm ell 2] using h
  have hLsq : 1 ≤ L^2 := by nlinarith
  have hhalf := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) hW
  calc
    _ ≤ 36*(2 : ℝ)^(2*ell)*(1/2 : ℝ)^cutoffWorkBits N ell := by
      have hc : 34*L^2+2 ≤ 36*(2 : ℝ)^(2*ell) := by nlinarith
      exact mul_le_mul hc hhalf (by positivity) (by positivity)
    _ = 36*((2 : ℝ)^(2*ell)*(1/2 : ℝ)^(2*ell+(N+6))) := by
      rw [show cutoffWorkBits N ell = 2*ell+(N+6) by unfold cutoffWorkBits; omega]
      ring
    _ = 36*(1/2 : ℝ)^(N+6) := by rw [dyadic_scale_cancel]
    _ ≤ _ := by
      rw [pow_add]
      norm_num
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) N]

theorem roundedTranslatedSandwich_requested_error {L : ℝ} (hL : 1 ≤ L)
    (s z σ : ℚ) (hs : 4 ≤ (s : ℝ)) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64)
    (a : Alias) (N W ellRoot ellLength K P : ℕ) (hslog : (s : ℝ) ≤ (2 : ℝ)^ellRoot)
    (hLlog : L ≤ (2 : ℝ)^ellLength) (hW : cutoffWorkBits N ellLength ≤ W)
    (hK : aliasSteps (W+2) ellLength ≤ K) (hP : cutoffWorkBits W ellLength ≤ P) :
    ‖exactTranslatedSandwich M s hs z σ a-
        roundedTranslatedSandwich M s z σ D hσ0 hσ a W ellRoot K P‖ ≤ (1/2 : ℝ)^N :=
  (roundedTranslatedSandwich_error M hL s z σ hs D hσ0 hσ a W ellRoot ellLength K P
    hslog hLlog hK hP).trans (translated_precision_error hL N ellLength W hLlog hW)

def finiteTranslatedSandwich (s z σ : ℚ) (a : Alias) (W ell K P : ℕ) (v : FourierData) : FourierData :=
  FourierData.rootApply s W ell (FourierData.inverseApply M z σ K P
    (finiteTranslation M a W (FourierData.rootApply s W ell v)))

theorem finiteTranslatedSandwich_value {L : ℝ} (hL : 1 ≤ L)
    (s z σ : ℚ) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64)
    (a : Alias) (N ellLength W ellRoot K P : ℕ) (hlog : L ≤ (2 : ℝ)^ellLength)
    (hK : aliasSteps N ellLength ≤ K) (v : FourierData) :
    (finiteTranslatedSandwich M s z σ a W ellRoot K P v).value =
      roundedTranslatedSandwich M s z σ D hσ0 hσ a W ellRoot K P v.value := by
  rw [finiteTranslatedSandwich,FourierData.rootApply_value,
    FourierData.inverseApply_value M hL z σ D hσ0 hσ N ellLength K P hlog hK,
    finiteTranslation_value,FourierData.rootApply_value,roundedTranslatedSandwich]
  simp only [mul_apply_eq_comp]

#print axioms roundedTranslatedSandwich_requested_error
#print axioms finiteTranslatedSandwich_value

end Maxwell.Continuum.Calibration.Supercell
