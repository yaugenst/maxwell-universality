import Maxwell.Continuum.CalibrationRoundedPrecision

/-! Explicit precision for the cutoff product at the physical length.
This pays for the full inverse norm before the sampled operators are
assembled by a unitary finite Fourier transform. -/

namespace Maxwell.Continuum.Calibration

def cutoffWorkBits (N ell : ℕ) : ℕ := N+2*ell+6

theorem cutoff_precision_error {L : ℝ} (hL : 1 ≤ L) (N ell P : ℕ)
    (hlog : L ≤ (2 : ℝ)^ell) (hP : cutoffWorkBits N ell ≤ P) :
    (1/2 : ℝ)^(N+2)+5*L^2*(1/2 : ℝ)^P ≤ (1/2 : ℝ)^N := by
  have hpow : L^2 ≤ (2 : ℝ)^(2*ell) := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ L) hlog 2
    simpa only [← pow_mul,Nat.mul_comm ell 2] using h
  have hhalf := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) hP
  have hm : 5*L^2*(1/2 : ℝ)^P ≤ 5*(1/2 : ℝ)^(N+6) := by
    calc
      _ ≤ 5*(2 : ℝ)^(2*ell)*(1/2 : ℝ)^cutoffWorkBits N ell := by gcongr
      _ = 5*((2 : ℝ)^(2*ell)*(1/2 : ℝ)^(2*ell+(N+6))) := by
        rw [show cutoffWorkBits N ell = 2*ell+(N+6) by unfold cutoffWorkBits; omega]
        ring
      _ = _ := by rw [dyadic_scale_cancel]
  simp only [pow_add] at hm ⊢
  norm_num at hm ⊢
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) N]

end Maxwell.Continuum.Calibration
