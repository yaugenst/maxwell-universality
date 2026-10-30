import Maxwell.Continuum.ProfileFourierDecay
import Maxwell.Continuum.ProfileDecayMajorant
import Maxwell.Continuum.PeriodicSampling

/-! Absolute Fourier reconstruction of the literal profile, including the sampling convention. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Profile

open AddCircle MeasureTheory

local instance : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩

theorem angularCoefficient_nat_majorant (n : ℕ) :
    ‖angularCoefficient 0 (n : ℤ)‖ ≤
      24*((1+(n : ℝ)^2)*Real.exp (-Real.sqrt n/128)) := by
  have h := angularCoefficient_decay (n : ℤ)
  simp only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] at h
  apply h.trans
  have he : Real.exp (-Real.sqrt (n : ℝ)/64) ≤ Real.exp (-Real.sqrt n/128) :=
    Real.exp_le_exp.mpr (by linarith [Real.sqrt_nonneg (n : ℝ)])
  have hh : 1 ≤ 1+(n : ℝ)^2 := le_add_of_nonneg_right (sq_nonneg _)
  have hp := mul_le_mul hh he (Real.exp_pos _).le (by positivity : 0 ≤ 1+(n : ℝ)^2)
  nlinarith only [hp]

theorem angularCoefficient_neg_nat_majorant (n : ℕ) :
    ‖angularCoefficient 0 (-(n : ℤ))‖ ≤
      24*((1+(n : ℝ)^2)*Real.exp (-Real.sqrt n/128)) := by
  have h := angularCoefficient_decay (-(n : ℤ))
  simp only [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] at h
  apply h.trans
  have he : Real.exp (-Real.sqrt (n : ℝ)/64) ≤ Real.exp (-Real.sqrt n/128) :=
    Real.exp_le_exp.mpr (by linarith [Real.sqrt_nonneg (n : ℝ)])
  have hh : 1 ≤ 1+(n : ℝ)^2 := le_add_of_nonneg_right (sq_nonneg _)
  have hp := mul_le_mul hh he (Real.exp_pos _).le (by positivity : 0 ≤ 1+(n : ℝ)^2)
  nlinarith only [hp]

theorem angularCoefficient_summable_norm : Summable (fun n : ℤ => ‖angularCoefficient 0 n‖) := by
  apply Summable.of_nat_of_neg
  · exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) angularCoefficient_nat_majorant
      (weighted_exp_summable.mul_left 24)
  · exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) angularCoefficient_neg_nat_majorant
      (weighted_exp_summable.mul_left 24)

theorem angular_complex_periodic : Function.Periodic (fun φ => (angular φ : ℂ)) (2*Real.pi) := by
  intro φ
  exact congrArg Complex.ofReal (angular_periodic φ)

def angularCircle : C(AddCircle (2*Real.pi), ℂ) :=
  ⟨angular_complex_periodic.lift, continuous_quot_lift _
    (Complex.continuous_ofReal.comp angular_contDiff.continuous)⟩

theorem angularCircle_coe (φ : ℝ) : angularCircle (φ : AddCircle (2*Real.pi)) = (angular φ : ℂ) := rfl

theorem angularCircle_coefficient (n : ℤ) :
    fourierCoeff angularCircle n = angularCoefficient 0 n := by
  rw [fourierCoeff_eq_intervalIntegral angularCircle n 0, angularCoefficient,
    fourierCoeffOn_eq_integral]
  simp only [zero_add, sub_zero, angularCircle_coe, iteratedDeriv_zero]
  simp only [fourier_coe_apply, sub_zero]

def mode (n : ℤ) (φ : ℝ) : ℂ := Complex.exp (Complex.I*(n : ℂ)*(φ : ℂ))

theorem mode_eq_fourier (n : ℤ) (φ : ℝ) :
    mode n φ = fourier n (φ : AddCircle (2*Real.pi)) := by
  rw [fourier_coe_apply, mode]
  congr 1
  push_cast
  field_simp

theorem angular_hasSum (φ : ℝ) :
    HasSum (fun n : ℤ => mode n φ*angularCoefficient 0 n) (angular φ : ℂ) := by
  have hs : Summable (fourierCoeff angularCircle) := by
    have he : fourierCoeff angularCircle = angularCoefficient 0 := funext angularCircle_coefficient
    rw [he]
    exact angularCoefficient_summable_norm.of_norm
  have h := has_pointwise_sum_fourier_series_of_summable hs (φ : AddCircle (2*Real.pi))
  simpa only [angularCircle_coefficient, angularCircle_coe, ← mode_eq_fourier, smul_eq_mul, mul_comm] using h

theorem sampling_phase_mode (n : ℤ) (x : ℝ) : PeriodicSampling.phase n x = mode n (2*Real.pi*x) := by
  unfold PeriodicSampling.phase mode
  congr 1
  push_cast
  ring

theorem angular_sampling_synthesis (x : ℝ) :
    PeriodicSampling.synthesis (angularCoefficient 0) x = (angular (2*Real.pi*x) : ℂ) := by
  unfold PeriodicSampling.synthesis
  simp only [sampling_phase_mode, smul_eq_mul]
  exact (angular_hasSum (2*Real.pi*x)).tsum_eq

#print axioms angular_hasSum
#print axioms angular_sampling_synthesis

end Maxwell.Continuum.Profile
