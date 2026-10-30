import Maxwell.Continuum.CalibrationSandwich

/-! A requested accuracy for the literal finite supercell sandwich.
The extra length bits pay for the two occurrences of the well root
and for the full physical inverse norm before iteration. -/

namespace Maxwell.Continuum.Calibration

theorem sandwich_precision_error {L : ℝ} (hL : 1 ≤ L) (N ell W : ℕ)
    (hlog : L ≤ (2 : ℝ)^ell) (hW : cutoffWorkBits N ell ≤ W) :
    (14*L^2+2)*(1/2 : ℝ)^W ≤ (1/2 : ℝ)^N := by
  have hpow : L^2 ≤ (2 : ℝ)^(2*ell) := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ L) hlog 2
    simpa only [← pow_mul,Nat.mul_comm ell 2] using h
  have hLsq : 1 ≤ L^2 := by nlinarith
  have hhalf := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) hW
  calc
    _ ≤ 16*(2 : ℝ)^(2*ell)*(1/2 : ℝ)^cutoffWorkBits N ell := by
      have hc : 14*L^2+2 ≤ 16*(2 : ℝ)^(2*ell) := by nlinarith
      exact mul_le_mul hc hhalf (by positivity) (by positivity)
    _ = 16*((2 : ℝ)^(2*ell)*(1/2 : ℝ)^(2*ell+(N+6))) := by
      rw [show cutoffWorkBits N ell = 2*ell+(N+6) by unfold cutoffWorkBits; omega]
      ring
    _ = 16*(1/2 : ℝ)^(N+6) := by rw [dyadic_scale_cancel]
    _ ≤ _ := by
      rw [pow_add]
      norm_num
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) N]

namespace Supercell

theorem roundedSandwich_requested_error (M : ℕ) [NeZero M] {L : ℝ} (hL : 1 ≤ L)
    (s z σ : ℚ) (hs : 4 ≤ (s : ℝ)) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64)
    (N W ellRoot ellLength K P : ℕ) (hslog : (s : ℝ) ≤ (2 : ℝ)^ellRoot)
    (hLlog : L ≤ (2 : ℝ)^ellLength) (hW : cutoffWorkBits N ellLength ≤ W)
    (hK : aliasSteps (W+2) ellLength ≤ K) (hP : cutoffWorkBits W ellLength ≤ P) :
    ‖exactSandwich M s hs z σ-roundedSandwich M s z σ D hσ0 hσ W ellRoot K P‖ ≤
      (1/2 : ℝ)^N :=
  (roundedSandwich_error M hL s z σ hs D hσ0 hσ W ellRoot ellLength K P
    hslog hLlog hK hP).trans (sandwich_precision_error hL N ellLength W hLlog hW)

end Supercell

#print axioms Supercell.roundedSandwich_requested_error

end Maxwell.Continuum.Calibration
