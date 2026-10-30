import Maxwell.Continuum.ChebyshevWaveRounded

/-! Uniform approximation by the actual finite dyadic Chebyshev output. -/

namespace Maxwell.Continuum.Profile

def waveData (q : ℚ) (Q N : ℕ) : List (ComplexDyadic (waveWorkBits (8*Q) N)) :=
  (List.range (waveDegree (8*Q) N)).map (waveRoundedCoefficient q Q N)

theorem waveData_length (q : ℚ) (Q N : ℕ) :
    (waveData q Q N).length=waveDegree (8*Q) N := by simp [waveData]

noncomputable def encodedWave (q : ℚ) (Q N : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (waveDegree (8*Q) N),
    complexDyadicValue (waveRoundedCoefficient q Q N j)*(cubeBasis j x : ℂ)

theorem encodedWave_coefficient_error (q : ℚ) (Q N : ℕ) (hq : |q|≤Q)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖waveChebyshevPolynomial (2*Real.pi*(q : ℝ)) (waveDegree (8*Q) N) x-encodedWave q Q N x‖ ≤
      (1/2 : ℝ)^(N+27) := by
  unfold waveChebyshevPolynomial encodedWave
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range (waveDegree (8*Q) N),
      ‖waveCosineCoefficient (2*Real.pi*(q : ℝ)) j*(cubeBasis j x : ℂ)-
        complexDyadicValue (waveRoundedCoefficient q Q N j)*(cubeBasis j x : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (waveDegree (8*Q) N), 20*(1/2 : ℝ)^waveWorkBits (8*Q) N := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul (waveRoundedCoefficient_error q Q N j hq (Finset.mem_range.mp hj).le)
        (cubeBasis_bound j hx) (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
    _ ≤ 20*((waveDegree (8*Q) N : ℝ)+1)*(1/2 : ℝ)^waveWorkBits (8*Q) N := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      nlinarith only [pow_nonneg (by norm_num : (0 : ℝ)≤1/2) (waveWorkBits (8*Q) N)]
    _ ≤ _ := waveWorkBits_error (8*Q) N

theorem encodedWave_error (q : ℚ) (Q N : ℕ) (hq : |q|≤Q)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖Complex.exp (Complex.I*((2*Real.pi*(q : ℝ) : ℝ) : ℂ)*(x : ℂ))-encodedWave q Q N x‖ ≤
      (1/2 : ℝ)^(N+26) := by
  have he := encodedWave_coefficient_error q Q N hq hx
  have ht := waveChebyshevPolynomial_precision (8*Q) N (waveFrequency_bound q Q hq) hx
  have h := norm_sub_le_norm_sub_add_norm_sub
    (Complex.exp (Complex.I*((2*Real.pi*(q : ℝ) : ℝ) : ℂ)*(x : ℂ)))
    (waveChebyshevPolynomial (2*Real.pi*(q : ℝ)) (waveDegree (8*Q) N) x) (encodedWave q Q N x)
  have hp : (1/2 : ℝ)^(N+100)≤(1/2 : ℝ)^(N+27) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hs : (1/2 : ℝ)^(N+27)+(1/2 : ℝ)^(N+27)=(1/2 : ℝ)^(N+26) := by
    rw [show N+27=(N+26)+1 by omega, pow_succ]
    ring
  linarith

theorem encodedWave_norm (q : ℚ) (Q N : ℕ) (hq : |q|≤Q)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : ‖encodedWave q Q N x‖≤2 := by
  have he := encodedWave_error q Q N hq hx
  have hn : ‖Complex.exp (Complex.I*((2*Real.pi*(q : ℝ) : ℝ) : ℂ)*(x : ℂ))‖=1 := by
    simp [Complex.norm_exp]
  have hp : (1/2 : ℝ)^(N+26)≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ht := norm_sub_le_norm_sub_add_norm_sub (encodedWave q Q N x)
    (Complex.exp (Complex.I*((2*Real.pi*(q : ℝ) : ℝ) : ℂ)*(x : ℂ))) 0
  simp only [sub_zero, hn] at ht
  rw [norm_sub_rev (encodedWave q Q N x) _] at ht
  linarith

theorem encodedWave_continuous (q : ℚ) (Q N : ℕ) : Continuous (encodedWave q Q N) := by
  unfold encodedWave
  apply continuous_finsetSum
  intro j _
  have hb : Continuous (cubeBasis j) := by
    change Continuous (fun x => cubeBasis j x)
    simpa only [cubeBasis_eq] using (Polynomial.Chebyshev.T ℝ (j : ℤ)).continuous
  exact continuous_const.mul (Complex.continuous_ofReal.comp hb)

#print axioms encodedWave_error
#print axioms encodedWave_norm

end Maxwell.Continuum.Profile
