import Maxwell.Continuum.PeriodicPhysicalTaylor

/-! The matrix H is exactly one half of the physical second derivative,
and the central energy has the stated quantitative displacement. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber

def freeEdge : ℝ := 3 * Real.pi ^ 2 / 4 - 7

theorem physical_line_second_coefficient (t : Momentum) :
    EvenTaylor.coefficient (fun z : ℂ => dielectricBand (z • t)) 2 = physicalQuadratic t := by
  have hρ : (backgroundAmplitude : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr backgroundAmplitude_pos.ne'
  have heq : (fun z : ℂ => dielectricBand (z • t)) =
      fun z => (freeEdge : ℂ) + (backgroundAmplitude : ℂ) * scaledSlice (unscale t) z := by
    funext z
    rw [dielectricBand_formula, unscale_smul]
    simp only [freeEdge, Complex.ofReal_sub, Complex.ofReal_ofNat, scaledSlice]
  unfold EvenTaylor.coefficient
  rw [heq, iteratedDeriv_const_add (by norm_num : (0 : ℕ) < 2),
    iteratedDeriv_const_mul _ (scaledSlice_analyticAt_zero (unscale t)).contDiffAt]
  calc
    _ = (backgroundAmplitude : ℂ) * EvenTaylor.coefficient (scaledSlice (unscale t)) 2 := by
      unfold EvenTaylor.coefficient
      ring
    _ = (backgroundAmplitude : ℂ) * bandQuadratic (unscale t) := by
      rw [← bandQuadratic_eq_coefficient]
    _ = physicalQuadratic t := by
      rw [unscale, bandQuadratic_smul, physicalQuadratic]
      field_simp

theorem physicalQuadratic_real_form (t : Corner.Vec) :
    physicalQuadratic (realMomentum t) = ((dotProduct t (hessian.mulVec t) : ℝ) : ℂ) := by
  rw [hessian_form, physicalQuadratic, ← bandQuadratic_ofReal_re]
  push_cast
  simp only [Complex.ofReal_re]
  ring

/-- This identifies the actual Hessian in every real direction. -/
theorem physical_half_second_derivative (t : Corner.Vec) :
    (1 / 2 : ℂ) * deriv (deriv (fun z : ℂ => dielectricBand (z • realMomentum t))) 0 =
      ((dotProduct t (hessian.mulVec t) : ℝ) : ℂ) := by
  have h := physical_line_second_coefficient (realMomentum t)
  rw [physicalQuadratic_real_form] at h
  simpa only [EvenTaylor.coefficient, iteratedDeriv_succ', iteratedDeriv_zero,
    show (2 : ℕ).factorial = 2 from rfl, Nat.cast_ofNat, one_div] using h

theorem center_energy_bound :
    ‖dielectricBand 0 - ((freeEdge : ℂ) +
      (backgroundAmplitude : ℂ) * (Corner.lambdaStar : ℂ))‖ ≤
        (2 : ℝ)^16 * backgroundAmplitude^2 := by
  have heq : dielectricBand 0 - ((freeEdge : ℂ) +
      (backgroundAmplitude : ℂ) * (Corner.lambdaStar : ℂ)) =
        (backgroundAmplitude : ℂ) * (scaledBand 0 - (Corner.lambdaStar : ℂ)) := by
    rw [dielectricBand_formula]
    simp only [unscale, smul_zero, freeEdge, Complex.ofReal_sub, Complex.ofReal_ofNat]
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos backgroundAmplitude_pos]
  have h := mul_le_mul_of_nonneg_left scaledBand_zero_bound backgroundAmplitude_pos.le
  nlinarith [sq_nonneg backgroundAmplitude]

end Maxwell.Continuum.PeriodicBand
