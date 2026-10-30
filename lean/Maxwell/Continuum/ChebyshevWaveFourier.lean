import Maxwell.Continuum.ChebyshevWaveAnalytic
import Maxwell.Continuum.PeriodicDerivativeCoefficient
import Maxwell.Continuum.HalfGeometricTail

/-! Exponential coefficient decay and absolute reconstruction for literal plane waves. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Profile

open AddCircle

theorem waveAngular_contDiff (k : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (waveAngular k) := by
  unfold waveAngular
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp Real.contDiff_cos)).cexp

def waveCoefficient (k : ℝ) (n : ℤ) : ℂ := derivativeCoefficient (waveAngular k) 0 n

theorem waveCoefficient_bound (k : ℝ) (n : ℤ) : ‖waveCoefficient k n‖ ≤ 1 := by
  apply derivativeCoefficient_bound
  intro x
  simpa only [iteratedDeriv_zero] using (waveAngular_norm k x).le

theorem waveCoefficient_decay (k : ℝ) (n : ℤ) :
    ‖waveCoefficient k n‖ ≤ Real.exp (4*|k|)*(1/2 : ℝ)^(n.natAbs/2) := by
  apply factorial_decay_optimization n.natAbs (Real.exp_nonneg _)
  intro K
  by_cases hn : n=0
  · subst n
    by_cases hK : K=0
    · subst K
      simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one]
      exact (waveCoefficient_bound k 0).trans (Real.one_le_exp_iff.mpr (by positivity))
    · simp only [Int.natAbs_zero, Nat.cast_zero, zero_pow hK, zero_mul]
      positivity
  · have h := derivativeCoefficient_iterated_norm (waveAngular_contDiff k) (waveAngular_periodic k) hn K
    have habs : (n.natAbs : ℝ)=|(n : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    rw [habs]
    change |(n : ℝ)|^K*‖derivativeCoefficient (waveAngular k) 0 n‖ ≤ _
    rw [← h]
    exact derivativeCoefficient_bound _ K n (fun x => waveAngular_derivative_bound k x K)

theorem waveCoefficient_summable_norm (k : ℝ) : Summable (fun n : ℤ => ‖waveCoefficient k n‖) := by
  apply Summable.of_nat_of_neg
  · apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ (half_geometric_summable.mul_left (Real.exp (4*|k|)))
    intro n
    simpa only [Int.natAbs_natCast] using waveCoefficient_decay k (n : ℤ)
  · apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ (half_geometric_summable.mul_left (Real.exp (4*|k|)))
    intro n
    simpa only [Int.natAbs_neg, Int.natAbs_natCast] using waveCoefficient_decay k (-(n : ℤ))

#print axioms waveCoefficient_decay
#print axioms waveCoefficient_summable_norm

end Maxwell.Continuum.Profile
