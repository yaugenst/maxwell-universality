import Maxwell.Continuum.BoxModes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact one-dimensional PEC mode inner products

Sines with positive integer indices and cosines with nonnegative integer
indices are orthogonal on a box interval.  This supplies the exact scalar
normalization factors for tensor-product PEC modes.  Completeness is a
separate assertion and is not presupposed in these integral identities.
-/

noncomputable section

namespace Maxwell.Continuum.BoxModes

open MeasureTheory

/-- The scalar sine mode on an interval of length `N`. Integer indices make
sum/difference identities exact without natural subtraction. -/
def intervalSin (N : ℝ) (n : ℤ) (x : ℝ) : ℝ := Real.sin ((n : ℝ) * Real.pi / N * x)

def intervalCos (N : ℝ) (n : ℤ) (x : ℝ) : ℝ := Real.cos ((n : ℝ) * Real.pi / N * x)

theorem continuous_intervalSin (N : ℝ) (n : ℤ) :
    Continuous (intervalSin N n) := Real.continuous_sin.comp (continuous_const.mul continuous_id)

theorem continuous_intervalCos (N : ℝ) (n : ℤ) :
    Continuous (intervalCos N n) := Real.continuous_cos.comp (continuous_const.mul continuous_id)

/-- The exact average of each cosine integer frequency. -/
theorem integral_intervalCos (N : ℝ) (hN : 0 < N) (n : ℤ) :
    (∫ x in (0 : ℝ)..N, intervalCos N n x) = if n = 0 then N else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [intervalCos]
  · rw [ite_eq_right hn]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hw : (n : ℝ) * Real.pi / N ≠ 0 :=
      div_ne_zero (mul_ne_zero hn' Real.pi_ne_zero) hN.ne'
    unfold intervalCos
    rw [intervalIntegral.integral_comp_mul_left Real.cos hw, integral_cos]
    simp [div_mul_cancel₀ _ hN.ne', Real.sin_int_mul_pi]

private theorem sin_product_identity (N : ℝ) (n m : ℤ) (x : ℝ) :
    intervalSin N n x * intervalSin N m x =
      (intervalCos N (n - m) x - intervalCos N (n + m) x) / 2 := by
  unfold intervalSin intervalCos
  push_cast
  have hsub : ((n : ℝ) - m) * Real.pi / N * x =
      (n : ℝ) * Real.pi / N * x - (m : ℝ) * Real.pi / N * x := by ring
  have hadd : ((n : ℝ) + m) * Real.pi / N * x =
      (n : ℝ) * Real.pi / N * x + (m : ℝ) * Real.pi / N * x := by ring
  rw [hsub, hadd]
  linarith [Real.two_mul_sin_mul_sin ((n : ℝ) * Real.pi / N * x)
    ((m : ℝ) * Real.pi / N * x)]

private theorem cos_product_identity (N : ℝ) (n m : ℤ) (x : ℝ) :
    intervalCos N n x * intervalCos N m x =
      (intervalCos N (n - m) x + intervalCos N (n + m) x) / 2 := by
  unfold intervalCos
  push_cast
  have hsub : ((n : ℝ) - m) * Real.pi / N * x =
      (n : ℝ) * Real.pi / N * x - (m : ℝ) * Real.pi / N * x := by ring
  have hadd : ((n : ℝ) + m) * Real.pi / N * x =
      (n : ℝ) * Real.pi / N * x + (m : ℝ) * Real.pi / N * x := by ring
  rw [hsub, hadd]
  linarith [Real.two_mul_cos_mul_cos ((n : ℝ) * Real.pi / N * x)
    ((m : ℝ) * Real.pi / N * x)]

/-- Sine modes of distinct positive integer frequency are orthogonal;
the square norm of every positive frequency is exactly `N / 2`. -/
theorem integral_intervalSin_mul (N : ℝ) (hN : 0 < N) (n m : ℤ)
    (hn : 0 < n) (hm : 0 < m) :
    (∫ x in (0 : ℝ)..N, intervalSin N n x * intervalSin N m x) =
      if n = m then N / 2 else 0 := by
  simp_rw [sin_product_identity]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_sub
      ((continuous_intervalCos N (n - m)).intervalIntegrable 0 N)
      ((continuous_intervalCos N (n + m)).intervalIntegrable 0 N),
    integral_intervalCos N hN, integral_intervalCos N hN]
  have hsum : n + m ≠ 0 := by omega
  simp [sub_eq_zero, hsum]
  split_ifs <;> simp_all

/-- Cosine modes have the same norm except for the constant mode, whose
square norm is exactly the interval length. -/
theorem integral_intervalCos_mul (N : ℝ) (hN : 0 < N) (n m : ℤ)
    (hn : 0 ≤ n) (hm : 0 ≤ m) :
    (∫ x in (0 : ℝ)..N, intervalCos N n x * intervalCos N m x) =
      if n = m then (if n = 0 then N else N / 2) else 0 := by
  simp_rw [cos_product_identity]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add
      ((continuous_intervalCos N (n - m)).intervalIntegrable 0 N)
      ((continuous_intervalCos N (n + m)).intervalIntegrable 0 N),
    integral_intervalCos N hN, integral_intervalCos N hN]
  by_cases heq : n = m
  · subst m
    by_cases hz : n = 0
    · simp [hz]
    · have hsum : n + n ≠ 0 := by omega
      simp [hz, hsum]
  · have hsub : n - m ≠ 0 := sub_ne_zero.mpr heq
    have hsum : n + m ≠ 0 := by omega
    simp [heq, hsub, hsum]

#print axioms integral_intervalSin_mul
#print axioms integral_intervalCos_mul

end Maxwell.Continuum.BoxModes
