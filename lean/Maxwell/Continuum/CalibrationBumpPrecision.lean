import Maxwell.Continuum.CalibrationBumpTail
import Maxwell.Continuum.CalibrationPeriodizationPrecision

/-! A quadratic-in-precision Fourier radius for the actual rescaled
compact root, with fully symbolic master-constant arithmetic. -/

noncomputable section

namespace Maxwell.Continuum.Calibration

open MasterConstants UnitAddTorus

theorem rootDecay_power (s : ℝ) (hs : 0 < s) :
    (rootDecayRate s/2)^12 = (2*Real.pi)^6/((128 : ℝ)^12*s^6) := by
  have he : rootDecayRate s/2 = Real.sqrt (2*Real.pi/s)/128 := by unfold rootDecayRate; ring
  rw [he, div_pow]
  have hp : (Real.sqrt (2*Real.pi/s))^12 = (2*Real.pi/s)^6 := by
    rw [show (12 : ℕ) = 2*6 by omega, pow_mul, Real.sq_sqrt (by positivity)]
  rw [hp, div_pow]
  ring

theorem rootTail_prefactor_bound (s : ℝ) (hs : 4 ≤ s) :
    (24/s^3)*(64*latticeDecayConstant (rootDecayRate s/2)) ≤ (2 : ℝ)^132*s^6 := by
  have hs0 : 0 < s := by linarith
  have hx : latticeDecayConstant (rootDecayRate s/2) =
      (64*(12 : ℕ).factorial*(128 : ℝ)^12*s^6)/(2*Real.pi)^6 := by
    rw [latticeDecayConstant, rootDecay_power s hs0]
    field_simp
  have hp : (1 : ℝ) ≤ (2*Real.pi)^6 := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hc : latticeDecayConstant (rootDecayRate s/2) ≤
      64*(12 : ℕ).factorial*(128 : ℝ)^12*s^6 := by
    rw [hx]
    exact div_le_self (by positivity) hp
  have hq : 24/s^3 ≤ (24 : ℝ) := div_le_self (by norm_num) (one_le_pow₀ (by linarith))
  calc
    _ ≤ 24*(64*(64*(12 : ℕ).factorial*(128 : ℝ)^12*s^6)) :=
      mul_le_mul hq (mul_le_mul_of_nonneg_left hc (by norm_num))
        (mul_nonneg (by norm_num) (latticeDecayConstant_nonneg (by exact div_pos (rootDecayRate_pos hs0) (by norm_num))))
        (by norm_num)
    _ ≤ _ := by norm_num [Nat.factorial]; nlinarith [pow_nonneg hs0.le 6]

theorem rootDecay_scaled (s : ℝ) (hs : 0 < s) :
    (1/128 : ℝ) ≤ (rootDecayRate s/2)*Real.sqrt s := by
  have he : (rootDecayRate s/2)*Real.sqrt s = Real.sqrt (2*Real.pi)/128 := by
    unfold rootDecayRate
    rw [div_div, div_mul_eq_mul_div, ← Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi/s),
      div_mul_cancel₀ _ hs.ne']
    norm_num
  rw [he]
  have hp : (1 : ℝ) ≤ Real.sqrt (2*Real.pi) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2*Real.pi by linarith [Real.pi_gt_three])
  linarith

theorem root_sqrt_budget {s R : ℝ} (hs : 0 < s) (N ell : ℕ)
    (hR : Cs^2*s*((N : ℝ)+(ell : ℝ)+2)^2 ≤ R) :
    (N+140+6*ell : ℕ) ≤ (rootDecayRate s/2)*Real.sqrt R := by
  let X : ℝ := (N : ℝ)+(ell : ℝ)+2
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hsq : (Cs*Real.sqrt s*X)^2 ≤ R := by
    convert hR using 1
    rw [mul_pow, mul_pow, Real.sq_sqrt hs.le]
  have hl : Cs*Real.sqrt s*X ≤ Real.sqrt R :=
    (Real.le_sqrt (mul_nonneg (mul_nonneg Cs_pos.le (Real.sqrt_nonneg s)) hX)
      (le_trans (sq_nonneg _) hsq)).mpr hsq
  have ha : 0 ≤ rootDecayRate s/2 := (div_pos (rootDecayRate_pos hs) (by norm_num)).le
  have hb := mul_le_mul_of_nonneg_left hl ha
  have hc := mul_le_mul_of_nonneg_left (rootDecay_scaled s hs) (mul_nonneg Cs_pos.le hX)
  have hlarge : (140 : ℝ) ≤ Cs/128 := by
    have ht : (2 : ℝ)^18 ≤ Cs := fixed_power_le_Cs (by have := exponent_large; omega)
    norm_num at ht
    linarith
  have hN := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ Cs/128 by linarith) (Nat.cast_nonneg (α := ℝ) N)
  have hell := mul_le_mul_of_nonneg_right (show (6 : ℝ) ≤ Cs/128 by linarith) (Nat.cast_nonneg (α := ℝ) ell)
  dsimp [X] at hc hb
  push_cast
  nlinarith

theorem rootTorus_tail_requested (s : ℝ) (hs : 4 ≤ s) (N ell R : ℕ) (hR0 : 0 < R)
    (hlog : s ≤ (2 : ℝ)^ell)
    (hR : Cs^2*s*((N : ℝ)+(ell : ℝ)+2)^2 ≤ (R : ℝ)) :
    PeriodicSampling.Product.cubeTail (mFourierCoeff (rootTorus s hs)) (R : ℤ) ≤ (1/2 : ℝ)^(N+8) := by
  have hb := root_sqrt_budget (show 0 < s by linarith) N ell hR
  have he : Real.exp (-(rootDecayRate s/2)*Real.sqrt R) ≤ (1/2 : ℝ)^(N+140+6*ell) := by
    calc
      _ ≤ Real.exp (-((N+140+6*ell : ℕ) : ℝ)) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (-1)^(N+140+6*ell) := by simpa using Real.exp_nat_mul (-1) (N+140+6*ell)
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) exp_neg_one_le_half _
  have hp : (24/s^3)*(64*latticeDecayConstant (rootDecayRate s/2)) ≤ (2 : ℝ)^(132+6*ell) := by
    calc
      _ ≤ (2 : ℝ)^132*s^6 := rootTail_prefactor_bound s hs
      _ ≤ (2 : ℝ)^132*((2 : ℝ)^ell)^6 := by gcongr
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  calc
    _ ≤ ((24/s^3)*(64*latticeDecayConstant (rootDecayRate s/2)))*
        Real.exp (-(rootDecayRate s/2)*Real.sqrt R) := by
      simpa only [mul_assoc] using rootTorus_cubeTail s hs R hR0
    _ ≤ (2 : ℝ)^(132+6*ell)*(1/2 : ℝ)^(N+140+6*ell) :=
      mul_le_mul hp he (Real.exp_pos _).le (by positivity)
    _ = _ := by
      rw [show N+140+6*ell = (N+8)+(132+6*ell) by omega, pow_add (1/2 : ℝ),
        mul_left_comm, ← mul_pow]
      norm_num

#print axioms rootTorus_tail_requested

end Maxwell.Continuum.Calibration
