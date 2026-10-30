import Maxwell.Continuum.CalibrationBumpSampling

/-! Logarithmic guard bits turn the certified rational DFT into a
uniform approximation to the actual well multiplier. -/

noncomputable section

namespace Maxwell.Continuum.Calibration

open PeriodicSampling UnitAddTorus MasterConstants

def rootCoefficientGuard (D : ℕ) : ℕ := 3*Nat.clog 2 (2*D+1)

theorem rootCoefficientGuard_card (D : ℕ) :
    (((2*D+1 : ℕ) : ℝ)^3) ≤ (2 : ℝ)^rootCoefficientGuard D := by
  have h : ((2*D+1 : ℕ) : ℝ) ≤ (2 : ℝ)^Nat.clog 2 (2*D+1) := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (2*D+1)
  calc
    _ ≤ ((2 : ℝ)^Nat.clog 2 (2*D+1))^3 := pow_le_pow_left₀ (by positivity) h 3
    _ = _ := by rw [← pow_mul]; congr 1; unfold rootCoefficientGuard; omega

theorem root_guard_budget (N G : ℕ) (c : ℝ) (hc : c ≤ (2 : ℝ)^G) :
    (1/2 : ℝ)^(N+G+8)+c*((1/2 : ℝ)^(N+G+8)+8*(1/2 : ℝ)^(N+G+8)) ≤
      (1/2 : ℝ)^N := by
  have he : (2 : ℝ)^G*(1/2 : ℝ)^(N+G+8) = (1/2 : ℝ)^N/256 := by
    rw [show N+G+8 = N+8+G by omega, pow_add (1/2 : ℝ), mul_left_comm, ← mul_pow]
    norm_num [pow_add]
    ring
  have hm := mul_le_mul_of_nonneg_right hc (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (N+G+8))
  rw [he] at hm
  have hp : (1/2 : ℝ)^(N+G+8) ≤ (1/2 : ℝ)^N/256 := by
    have hg : (1 : ℝ) ≤ (2 : ℝ)^G := one_le_pow₀ (by norm_num)
    have h := mul_le_mul_of_nonneg_right hg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (N+G+8))
    simpa only [one_mul, he] using h
  nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1/2 by norm_num) N]

theorem rationalRootPolynomial_requested (grid D R N ell : ℕ) [NeZero grid]
    (s : ℚ) (hs : 4 ≤ (s : ℝ))
    (hgrid : D+R ≤ grid) (hR0 : 0 < R) (hRD : R ≤ D+1)
    (hlog : (s : ℝ) ≤ (2 : ℝ)^ell)
    (hR : Cs^2*(s : ℝ)*((N+rootCoefficientGuard D : ℕ)+(ell : ℝ)+2)^2 ≤ (R : ℝ))
    (x : UnitAddTorus (Fin 3)) :
    ‖rootTorus s hs x-rationalRootPolynomial grid D (N+rootCoefficientGuard D+8) s x‖ ≤
      (1/2 : ℝ)^N := by
  have he := rationalRootPolynomial_error grid D R (N+rootCoefficientGuard D) ell
    (N+rootCoefficientGuard D+8) s hs hgrid hR0 hRD hlog hR x
  exact he.trans (root_guard_budget N (rootCoefficientGuard D) _ (rootCoefficientGuard_card D))

#print axioms rationalRootPolynomial_requested

end Maxwell.Continuum.Calibration
