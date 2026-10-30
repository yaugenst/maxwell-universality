import Maxwell.Continuum.CalibrationInversePrecision
import Maxwell.Continuum.CalibrationRationalFree

/-! The same symbolic iteration budget pays for both Neumann truncation
and the concrete rational approximation to pi in every inverse block. -/

namespace Maxwell.Continuum.Calibration

theorem rounded_inverse_precision_small {L : ℝ} (hL : 1 ≤ L) (ell N K : ℕ)
    (hlog : L ≤ (2 : ℝ)^ell) (hK : aliasSteps N ell ≤ K) :
    (4*L^2)*(4*(1/2 : ℝ)^K) ≤ 1/2 := by
  have hpow : L^2 ≤ (2 : ℝ)^(2*ell) := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ L) hlog 2
    simpa only [← pow_mul,Nat.mul_comm ell 2] using h
  have hk : 2*ell+5 ≤ K := by have := aliasSteps_lower N ell; omega
  have hhalf := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) hk
  calc
    _ = 16*L^2*(1/2 : ℝ)^K := by ring
    _ ≤ 16*(2 : ℝ)^(2*ell)*(1/2 : ℝ)^(2*ell+5) := by gcongr
    _ = 1/2 := by rw [mul_assoc,dyadic_scale_cancel]; norm_num

theorem rounded_inverse_precision_error {L : ℝ} (hL : 1 ≤ L) (ell N K : ℕ)
    (hlog : L ≤ (2 : ℝ)^ell) (hK : aliasSteps N ell ≤ K) :
    2048*L^4*(1/2 : ℝ)^K ≤ (1/2 : ℝ)^N := by
  have hpow : L^4 ≤ (2 : ℝ)^(4*ell) := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ L) hlog 4
    simpa only [← pow_mul,Nat.mul_comm ell 4] using h
  have hk : (4*ell+11)+N ≤ K := by
    unfold aliasSteps at hK
    norm_num at hK
    omega
  have hhalf := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) hk
  calc
    _ ≤ 2048*(2 : ℝ)^(4*ell)*(1/2 : ℝ)^((4*ell+11)+N) := by gcongr
    _ = (2 : ℝ)^(4*ell+11)*(1/2 : ℝ)^((4*ell+11)+N) := by rw [pow_add]; norm_num; ring
    _ = _ := dyadic_scale_cancel _ _

theorem rounded_inverse_coefficient_error (K : ℕ) :
    2*(1/2 : ℝ)^K+32*|Real.pi-(piCenter K : ℝ)| ≤ 4*(1/2 : ℝ)^K := by
  have h := piCenter_error K
  rw [pow_add] at h
  norm_num at h
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) K]

#print axioms rounded_inverse_precision_error

end Maxwell.Continuum.Calibration
