import Maxwell.Continuum.AlmostAnalyticContourBound

/-! Reparameterization of the literal finite cutoff extension while
keeping its truncation order fixed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.AlmostAnalytic

open Complex FreeFiber PeriodicBand Auxiliary MasterConstants MeasureTheory Set Metric

theorem coefficient_mul (j : ℕ) (s t : ℝ) :
    coefficient j (s*t) = (s : ℂ)^j*coefficient j t := by
  simp only [coefficient, Complex.ofReal_mul, mul_pow]
  ring

theorem cutoffTaylor_smul (K : ℕ) (q₀ : ℝ) (q β : Space) (s t : ℝ) :
    cutoffTaylor K q₀ q (s • β) t = cutoffTaylor K q₀ q β (s*t) := by
  unfold cutoffTaylor
  apply Finset.sum_congr rfl
  intro j _
  rw [directionalDerivative_smul, Complex.ofReal_mul, Complex.ofReal_pow, coefficient_mul]
  ring

theorem shiftedMomentum_smul (q β : Space) (s t : ℝ) :
    shiftedMomentum q (s • β) t = shiftedMomentum q β (s*t) := by
  rw [shiftedMomentum, shiftedMomentum, map_smul]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul, Complex.ofReal_mul]
  ring

theorem cutoffDefect_smul (K : ℕ) (β : Space) (s t : ℝ) (q : Space) :
    cutoffDefect K (s • β) t q = (s : ℂ)*cutoffDefect K β (s*t) q := by
  simp only [cutoffDefect, cutoffDerivative, directionalDerivative_smul,
    Complex.ofReal_mul, Complex.ofReal_pow, coefficient_mul, pow_succ]
  ring

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem contourProduct_smul (K : ℕ) (β : Space) (Y : Momentum → F) (s t : ℝ) (q : Space) :
    contourProduct K (s • β) Y t q = contourProduct K β Y (s*t) q := by
  rw [contourProduct, contourProduct, cutoffTaylor_smul, shiftedMomentum_smul]

theorem contourRemainder_smul (K : ℕ) (β : Space) (Y : Momentum → F) (s t : ℝ) (q : Space) :
    contourRemainder K (s • β) Y t q = (s : ℂ) • contourRemainder K β Y (s*t) q := by
  rw [contourRemainder, contourRemainder, cutoffDefect_smul, shiftedMomentum_smul, mul_smul]

#print axioms contourRemainder_smul

end Maxwell.Continuum.AlmostAnalytic
