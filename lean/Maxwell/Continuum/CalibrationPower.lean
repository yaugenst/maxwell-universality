import Maxwell.Continuum.CalibrationPowerData
import Maxwell.Continuum.CalibrationPowerRate

/-! Certified convergence of the prescribed power iteration on the
literal continuum auxiliary operator, with the paper's iteration count. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration

open EffectiveMass NormedSpace

attribute [local irreducible] Sh muH realMode Bloch.unitary Auxiliary.resolvent
  startingVector powerOperator powerValue startingCoefficient

def powerIterate {h z : ℝ} (D : Auxiliary.Calibration h z) (n : ℕ) : FieldL2 :=
  (powerOperator D^n) (startingVector D.h_pos)

theorem powerIterate_ne_zero {h z : ℝ} (D : Auxiliary.Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (n : ℕ) : powerIterate D n ≠ 0 := by
  have hc : inner ℂ (realMode D hh) (startingVector D.h_pos) ≠ 0 := by
    rw [startingCoefficient_inner]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le (by positivity) (startingCoefficient_lower D hh)))
  exact power_ne_zero (powerData D hh) (startingVector D.h_pos) hc n

theorem powerIterate_norm_lower {h z : ℝ} (D : Auxiliary.Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (n : ℕ) :
    (1/2 : ℝ)^(48+38*n) ≤ ‖powerIterate D n‖ := by
  have ha : 0 < startingCoefficient D hh :=
    lt_of_lt_of_le (by positivity) (startingCoefficient_lower D hh)
  have hb := power_norm_lower (powerData D hh) (startingVector D.h_pos) n
  rw [startingCoefficient_inner,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha] at hb
  apply le_trans _ hb
  have hl : (1/2 : ℝ)^38 ≤ powerValue D hh := by
    simpa only [div_pow,one_pow] using (powerValue_bounds D hh).1
  have hc : (1/2 : ℝ)^48 ≤ startingCoefficient D hh := by
    simpa only [div_pow,one_pow] using startingCoefficient_lower D hh
  calc
    _ = ((1/2 : ℝ)^38)^n*(1/2 : ℝ)^48 := by rw [pow_add,pow_mul]; ring
    _ ≤ _ := mul_le_mul (pow_le_pow_left₀ (by positivity) hl n) hc (by positivity)
      (pow_nonneg ((powerValue_bounds D hh).1.trans' (by positivity)) n)

theorem powerIterate_normalized_error {h z : ℝ} (D : Auxiliary.Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (n : ℕ) :
    ‖normalize (powerIterate D n)-realMode D hh‖ ≤
      (2 : ℝ)^49*(1-1/(2 : ℝ)^104)^n := by
  have ha : 0 < startingCoefficient D hh :=
    lt_of_lt_of_le (by positivity) (startingCoefficient_lower D hh)
  have hb := normalized_power_error_real_overlap (powerData D hh) (startingVector D.h_pos) n
    ha (startingCoefficient_inner D hh) (power_ratio D hh)
  rw [startingVector_norm D.h_pos hh,mul_one] at hb
  apply hb.trans
  calc
    _ ≤ 2*(1-1/(2 : ℝ)^104)^n/(1/(2 : ℝ)^48) := div_le_div_of_nonneg_left
      (by positivity) (by positivity) (startingCoefficient_lower D hh)
    _ = _ := by ring

theorem powerIterate_requested_error {h z : ℝ} (D : Auxiliary.Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (N : ℕ) :
    ‖normalize (powerIterate D (powerSteps N))-realMode D hh‖ ≤ (1/2 : ℝ)^(N+20) :=
  (powerIterate_normalized_error D hh (powerSteps N)).trans (normalized_powerSteps_decay N)

#print axioms powerIterate_norm_lower
#print axioms powerIterate_requested_error

end Maxwell.Continuum.Calibration
