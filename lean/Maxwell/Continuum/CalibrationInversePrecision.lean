import Maxwell.Continuum.CalibrationTaylorBound

/-! The manuscript's symbolic Neumann iteration budget. `ell` is any
certified upper dyadic exponent for the length, so the lemma does not
evaluate enormous powers or enumerate the iterations. -/

namespace Maxwell.Continuum.Calibration

def aliasSteps (N ell : ℕ) : ℕ := N+16*ell+2^20

theorem dyadic_scale_cancel (a b : ℕ) :
    (2 : ℝ)^a*(1/2 : ℝ)^(a+b) = (1/2 : ℝ)^b := by
  rw [pow_add,← mul_assoc,← mul_pow]
  norm_num

theorem aliasSteps_lower (N ell : ℕ) : N+4*ell+10 ≤ aliasSteps N ell := by
  unfold aliasSteps
  norm_num
  omega

theorem inverse_precision_small {L : ℝ} (hL : 1 ≤ L) (ell N K : ℕ)
    (hlog : L ≤ (2 : ℝ)^ell) (hK : aliasSteps N ell ≤ K) :
    (4*L^2)*(2*(1/2 : ℝ)^K) ≤ 1/2 := by
  have hpow : L^2 ≤ (2 : ℝ)^(2*ell) := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ L) hlog 2
    simpa only [← pow_mul,Nat.mul_comm ell 2] using h
  have hk : 2*ell+4 ≤ K := by have := aliasSteps_lower N ell; omega
  have hhalf := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) hk
  calc
    _ = 8*L^2*(1/2 : ℝ)^K := by ring
    _ ≤ 8*(2 : ℝ)^(2*ell)*(1/2 : ℝ)^(2*ell+4) := by gcongr
    _ = 1/2 := by rw [mul_assoc,dyadic_scale_cancel]; norm_num

theorem inverse_precision_error {L : ℝ} (hL : 1 ≤ L) (ell N K : ℕ)
    (hlog : L ≤ (2 : ℝ)^ell) (hK : aliasSteps N ell ≤ K) :
    1024*L^4*(1/2 : ℝ)^K ≤ (1/2 : ℝ)^N := by
  have hpow : L^4 ≤ (2 : ℝ)^(4*ell) := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ L) hlog 4
    simpa only [← pow_mul,Nat.mul_comm ell 4] using h
  have hk : (4*ell+10)+N ≤ K := by have := aliasSteps_lower N ell; omega
  have hhalf := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) hk
  calc
    _ ≤ 1024*(2 : ℝ)^(4*ell)*(1/2 : ℝ)^((4*ell+10)+N) := by gcongr
    _ = (2 : ℝ)^(4*ell+10)*(1/2 : ℝ)^((4*ell+10)+N) := by rw [pow_add]; norm_num; ring
    _ = _ := dyadic_scale_cancel _ _

#print axioms inverse_precision_small
#print axioms inverse_precision_error

end Maxwell.Continuum.Calibration
