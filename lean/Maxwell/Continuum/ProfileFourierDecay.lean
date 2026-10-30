import Maxwell.Continuum.ProfileAngularGevrey
import Maxwell.Continuum.WellDecayOptimization
import Mathlib.Analysis.Fourier.AddCircle

/-! Integration by parts and quantitative Fourier decay for the literal angular profile. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Profile

open AddCircle MeasureTheory Set

def angularCoefficient (K : ℕ) (n : ℤ) : ℂ :=
  fourierCoeffOn Real.two_pi_pos (fun x => ((iteratedDeriv K angular x : ℝ) : ℂ)) n

theorem angularCoefficient_bound (K : ℕ) (n : ℤ) :
    ‖angularCoefficient K n‖ ≤ (400 : ℝ)^K*(K.factorial : ℝ)^2 := by
  unfold angularCoefficient
  rw [fourierCoeffOn_eq_integral, norm_smul, Real.norm_eq_abs, sub_zero,
    abs_of_pos (by positivity : 0 < 1/(2*Real.pi))]
  have hi : ‖∫ x in (0 : ℝ)..2*Real.pi,
      fourier (-n) (x : AddCircle (2*Real.pi)) • ((iteratedDeriv K angular x : ℝ) : ℂ)‖ ≤
      ((400 : ℝ)^K*(K.factorial : ℝ)^2)*(2*Real.pi) := by
    have hh : ‖∫ x in (0 : ℝ)..2*Real.pi,
        fourier (-n) (x : AddCircle (2*Real.pi)) • ((iteratedDeriv K angular x : ℝ) : ℂ)‖ ≤
        ((400 : ℝ)^K*(K.factorial : ℝ)^2)*|2*Real.pi-0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun x _ => by
        rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs]
        exact angular_gevrey x K)
    simpa only [sub_zero, abs_of_pos Real.two_pi_pos] using hh
  apply (mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 1/(2*Real.pi))).trans_eq
  field_simp

theorem angularCoefficient_step (K : ℕ) {n : ℤ} (hn : n ≠ 0) :
    Complex.I*(n : ℂ)*angularCoefficient K n = angularCoefficient (K+1) n := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => ((iteratedDeriv K angular x : ℝ) : ℂ))
      ((iteratedDeriv (K+1) angular x : ℝ) : ℂ) x := by
    intro x
    have hc : ContDiff ℝ (K+1) angular := angular_contDiff.of_le (by simp)
    simpa only [iteratedDeriv_succ] using
      ((hc.differentiable_iteratedDeriv' K) x).hasDerivAt.ofReal_comp
  have hi : IntervalIntegrable (fun x => ((iteratedDeriv (K+1) angular x : ℝ) : ℂ)) volume 0 (2*Real.pi) :=
    (Complex.continuous_ofReal.comp (angular_contDiff.continuous_iteratedDeriv (K+1) (by simp))).intervalIntegrable _ _
  have hb : iteratedDeriv K angular (2*Real.pi) = iteratedDeriv K angular 0 := by
    simpa only [zero_add] using angular_derivative_periodic K 0
  have h := fourierCoeffOn_of_hasDerivAt Real.two_pi_pos hn (fun x _ => hd x) hi
  simp only [hb, sub_self, mul_zero, zero_sub, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_zero, sub_zero] at h
  change angularCoefficient K n = _ at h
  rw [h]
  change Complex.I*(n : ℂ)*(1/(-2*(Real.pi : ℂ)*Complex.I*(n : ℂ))*
    (-((2*(Real.pi : ℂ))*angularCoefficient (K+1) n))) = _
  field_simp

theorem angularCoefficient_iterated_norm {n : ℤ} (hn : n ≠ 0) (K : ℕ) :
    ‖angularCoefficient K n‖ = |(n : ℝ)|^K*‖angularCoefficient 0 n‖ := by
  induction K with
  | zero => simp only [pow_zero, one_mul]
  | succ K ih =>
    rw [← angularCoefficient_step K hn, norm_mul, norm_mul, Complex.norm_I,
      Complex.norm_intCast, one_mul, ih, pow_succ]
    ring

theorem angularCoefficient_decay (n : ℤ) :
    ‖angularCoefficient 0 n‖ ≤ 24*Real.exp (-Real.sqrt |(n : ℝ)|/64) := by
  by_cases hn : n = 0
  · subst n
    have h := angularCoefficient_bound 0 0
    norm_num at h ⊢
    linarith
  · apply Well.gevrey_decay_optimization |(n : ℝ)| _
      (abs_pos.mpr (by exact_mod_cast hn))
    intro K
    rw [← angularCoefficient_iterated_norm hn]
    exact (angularCoefficient_bound K n).trans (by
      nlinarith only [show 0 ≤ (400 : ℝ)^K*(K.factorial : ℝ)^2 by positivity])

#print axioms angularCoefficient_decay

end Maxwell.Continuum.Profile
