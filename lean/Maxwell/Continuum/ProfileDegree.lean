import Maxwell.Continuum.ProfileDecayMajorant
import Maxwell.Continuum.CalibrationPowerRate

/-! A literal quadratic degree suffices for the complete differentiated profile tail. -/

namespace Maxwell.Continuum.Profile

def profileDegree (N : ℕ) : ℕ := (128*(N+256))^2

theorem profileDegree_pos (N : ℕ) : 0 < profileDegree N := by unfold profileDegree; positivity

theorem profileDegree_bound (N : ℕ) : profileDegree N ≤ 2^30*(N+1)^2 := by
  unfold profileDegree
  have h : 128*(N+256) ≤ 32768*(N+1) := by omega
  calc
    _ ≤ (32768*(N+1))^2 := Nat.pow_le_pow_left h 2
    _ = _ := by ring

theorem profileDegree_sqrt (N : ℕ) :
    Real.sqrt (profileDegree N : ℝ)/128 = (N : ℝ)+256 := by
  simp only [profileDegree, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add]
  rw [Real.sqrt_sq (by positivity)]
  ring

theorem profileDegree_precision (N : ℕ) :
    (2 : ℝ)^100*Real.exp (-Real.sqrt (profileDegree N : ℝ)/128) ≤ (1/2 : ℝ)^(N+100) := by
  rw [neg_div, profileDegree_sqrt]
  have he : Real.exp (-((N : ℝ)+256)) ≤ (1/2 : ℝ)^(N+256) := by
    have hid : -((N : ℝ)+256) = ((N+256 : ℕ) : ℝ)*(-1) := by push_cast; ring
    rw [hid, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) Calibration.exp_neg_one_le_half _
  calc
    _ ≤ (2 : ℝ)^100*(1/2 : ℝ)^(N+256) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = (1/2 : ℝ)^(N+100)*((2 : ℝ)^100*(1/2 : ℝ)^156) := by
      rw [show N+256=(N+100)+156 by omega, pow_add]
      ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) (by norm_num)

#print axioms profileDegree_bound
#print axioms profileDegree_precision

end Maxwell.Continuum.Profile
