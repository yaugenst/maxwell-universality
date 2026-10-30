import Maxwell.Continuum.ChebyshevWaveSeries

/-! A linear degree in frequency and accuracy, with a literal dyadic error bound. -/

namespace Maxwell.Continuum.Profile

def waveDegree (K N : ℕ) : ℕ := 16*(K+N+16)

theorem waveDegree_pos (K N : ℕ) : 0<waveDegree K N := by unfold waveDegree; positivity

theorem wave_exponential_bound (K : ℕ) {k : ℝ} (hk : |k| ≤ K) :
    Real.exp (4*|k|) ≤ (2 : ℝ)^(8*K) := by
  calc
    _ ≤ Real.exp (4*(K : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp 1^(4*K) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    _ ≤ (4 : ℝ)^(4*K) := pow_le_pow_left₀ (Real.exp_nonneg _)
      (Real.exp_one_lt_three.le.trans (by norm_num)) _
    _ = _ := by rw [show (4 : ℝ)=2^2 by norm_num, ← pow_mul]; congr 1; omega

theorem waveDegree_precision (K N : ℕ) {k : ℝ} (hk : |k| ≤ K) :
    16*Real.exp (4*|k|)*(1/2 : ℝ)^(waveDegree K N/2) ≤ (1/2 : ℝ)^(N+100) := by
  have hD : waveDegree K N/2=8*K+(8*N+128) := by unfold waveDegree; omega
  have hc : (2 : ℝ)^(8*K)*(1/2 : ℝ)^(8*K)=1 := by rw [← mul_pow]; norm_num
  calc
    _ ≤ 16*((2 : ℝ)^(8*K))*(1/2 : ℝ)^(waveDegree K N/2) := by
      gcongr
      exact wave_exponential_bound K hk
    _ = 16*(1/2 : ℝ)^(8*N+128) := by
      rw [hD, pow_add]
      calc
        _ = 16*((2 : ℝ)^(8*K)*(1/2 : ℝ)^(8*K))*(1/2 : ℝ)^(8*N+128) := by ring
        _ = _ := by rw [hc, mul_one]
    _ = (1/2 : ℝ)^(8*N+124) := by
      rw [show 8*N+128=(8*N+124)+4 by omega, pow_add]
      ring
    _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

theorem waveChebyshevPolynomial_precision (K N : ℕ) {k x : ℝ}
    (hk : |k| ≤ K) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖Complex.exp (Complex.I*(k : ℂ)*(x : ℂ))-waveChebyshevPolynomial k (waveDegree K N) x‖ ≤
      (1/2 : ℝ)^(N+100) :=
  (waveChebyshevPolynomial_error k (waveDegree K N) hx).trans (waveDegree_precision K N hk)

#print axioms waveChebyshevPolynomial_precision

end Maxwell.Continuum.Profile
