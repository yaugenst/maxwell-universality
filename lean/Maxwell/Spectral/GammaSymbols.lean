import Maxwell.Spectral.BoxGeometry
import Maxwell.Certificate.CoverSemantics

/-! Uniform free-symbol separation on the closed Gamma cube. The zero
frequency is treated separately, including its vanishing symbol at the origin. -/

noncomputable section
namespace Maxwell.Spectral.GammaSymbols
open Maxwell.Certificate.FourierBinding Maxwell.Spectral.PeriodicYee
open BoxSymbols BoxFourierProjection

/-- Centered representatives of the actual reciprocal frequency indices. -/
def residue (n : ℤ) : ℤ := (n + 10) % 20 - 10

theorem residue_bounds (n : ℤ) : -10 ≤ residue n ∧ residue n ≤ 10 := by
  have hlo := Int.emod_nonneg (n + 10) (by norm_num : (20 : ℤ) ≠ 0)
  have hhi := Int.emod_lt_of_pos (n + 10) (by norm_num : (0 : ℤ) < 20)
  unfold residue
  omega

theorem residue_decomposition (n : ℤ) : n = residue n + 20 * ((n + 10) / 20) := by
  have h := Int.emod_add_ediv_mul (n + 10) 20
  unfold residue
  omega

theorem residue_parity (n : ℤ) : residue n % 2 = n % 2 := by
  have h := residue_decomposition n
  omega

theorem normSq_imaginary_exp (x : ℝ) :
    Complex.normSq (Complex.exp (Complex.I * (x : ℂ)) - 1) = 2 - 2 * Real.cos x := by
  rw [Complex.normSq_sub]
  have hn : Complex.normSq (Complex.exp (Complex.I * (x : ℂ))) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_I_mul_ofReal]
    norm_num
  rw [hn]
  simp [Complex.exp_re]
  ring

theorem symbol_zero_normSq (f : Frequency) (j : Direction) :
    Complex.normSq (symbol 0 f j) =
      4 * Real.sin (Real.pi / 20 * |(residue (reciprocalIndex f j) : ℝ)|)^2 := by
  let n := reciprocalIndex f j
  have he : 2 * Real.pi / 20 * (n : ℝ) =
      2 * (Real.pi / 20 * (residue n : ℝ)) + ((n + 10) / 20 : ℤ) * (2 * Real.pi) := by
    have h := congrArg (fun k : ℤ => (k : ℝ)) (residue_decomposition n)
    push_cast at h
    rw [h]
    ring
  simp only [symbol, shiftSymbol, Pi.zero_apply, Complex.ofReal_zero, add_zero]
  change Complex.normSq (Complex.exp (Complex.I *
    ((2 * Real.pi / 20 * (n : ℝ)) : ℂ)) - 1) = _
  have hid := normSq_imaginary_exp (2 * Real.pi / 20 * (n : ℝ))
  push_cast at hid
  push_cast
  rw [hid, he, Real.cos_add_int_mul_two_pi,
    Real.cos_two_mul]
  have hsq : Real.sin (Real.pi / 20 * |(residue n : ℝ)|)^2 =
      Real.sin (Real.pi / 20 * (residue n : ℝ))^2 := by
    by_cases h : 0 ≤ (residue n : ℝ)
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h), mul_neg, Real.sin_neg, neg_sq]
  rw [hsq]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi / 20 * (residue n : ℝ))]

private theorem sin_unit_lower : (31/200 : ℝ) ≤ Real.sin (Real.pi/20) := by
  have h := Real.sin_ge_sub_cube (x := Real.pi/20) (by positivity)
  have hlo := Real.pi_gt_d4
  have hhi := Real.pi_lt_d4
  have hcube : (Real.pi/20)^3 ≤ (4/25 : ℝ)^3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 3
  nlinarith

private theorem sin_double_lower : (3/10 : ℝ) ≤ Real.sin (Real.pi/10) := by
  have h := Real.sin_ge_sub_cube (x := Real.pi/10) (by positivity)
  have hlo := Real.pi_gt_d4
  have hhi := Real.pi_lt_d4
  have hcube : (Real.pi/10)^3 ≤ (8/25 : ℝ)^3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 3
  nlinarith

/-- Every nonzero centered coordinate supplies the explicit scalar margin. -/
theorem symbol_zero_lower_one (f : Frequency) (j : Direction)
    (h : residue (reciprocalIndex f j) ≠ 0) :
    (31/100 : ℝ)^2 ≤ Complex.normSq (symbol 0 f j) := by
  rw [symbol_zero_normSq]
  have hb := residue_bounds (reciprocalIndex f j)
  have ha : (1 : ℝ) ≤ |(residue (reciprocalIndex f j) : ℝ)| := by
    have hp := abs_pos.mpr h
    have hz : 1 ≤ |residue (reciprocalIndex f j)| := by omega
    exact_mod_cast hz
  have hu : |(residue (reciprocalIndex f j) : ℝ)| ≤ 10 := by
    exact abs_le.mpr ⟨by exact_mod_cast hb.1, by exact_mod_cast hb.2⟩
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (x := Real.pi/20) (y := Real.pi/20*|(residue (reciprocalIndex f j) : ℝ)|)
    (by linarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    (by nlinarith [Real.pi_pos])
  have hlo := sin_unit_lower.trans hs
  nlinarith [sq_nonneg (Real.sin (Real.pi/20*|(residue (reciprocalIndex f j) : ℝ)|)-31/200)]

/-- An even nonzero centered coordinate gives the larger single-axis margin. -/
theorem symbol_zero_lower_two (f : Frequency) (j : Direction)
    (h : 2 ≤ |residue (reciprocalIndex f j)|) :
    (3/5 : ℝ)^2 ≤ Complex.normSq (symbol 0 f j) := by
  rw [symbol_zero_normSq]
  have hb := residue_bounds (reciprocalIndex f j)
  have ha : (2 : ℝ) ≤ |(residue (reciprocalIndex f j) : ℝ)| := by exact_mod_cast h
  have hu : |(residue (reciprocalIndex f j) : ℝ)| ≤ 10 := by
    exact abs_le.mpr ⟨by exact_mod_cast hb.1, by exact_mod_cast hb.2⟩
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (x := Real.pi/10) (y := Real.pi/20*|(residue (reciprocalIndex f j) : ℝ)|)
    (by linarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    (by nlinarith [Real.pi_pos])
  have hlo := sin_double_lower.trans hs
  nlinarith [sq_nonneg (Real.sin (Real.pi/20*|(residue (reciprocalIndex f j) : ℝ)|)-3/10)]

/-- FCC reciprocal indices either have three odd coordinates, or a nonzero
coordinate of even magnitude at least two. This uses the actual 2000 frequencies. -/
theorem reciprocal_residue_classification (f : Frequency) (hf : f ≠ 0) :
    (∀ j, residue (reciprocalIndex f j) ≠ 0) ∨
      ∃ j, 2 ≤ |residue (reciprocalIndex f j)| := by
  by_cases hp : (f.1.val : ℤ) % 2 = 0
  · right
    by_contra hn
    push Not at hn
    have hz (j : Direction) : residue (reciprocalIndex f j) = 0 := by
      have hpar := residue_parity (reciprocalIndex f j)
      have ha := abs_lt.mp (hn j)
      fin_cases j <;> norm_num [reciprocalIndex] at hpar ha ⊢ <;> omega
    have h0 := residue_decomposition (reciprocalIndex f 0)
    have h1 := residue_decomposition (reciprocalIndex f 1)
    have h2 := residue_decomposition (reciprocalIndex f 2)
    rw [hz 0] at h0
    rw [hz 1] at h1
    rw [hz 2] at h2
    norm_num [reciprocalIndex] at h0 h1 h2
    have hf0 : f.1.val = 0 := by omega
    have hf1 : f.2.1.val = 0 := by omega
    have hf2 : f.2.2.val = 0 := by omega
    exact hf (Prod.ext (Fin.ext hf0) (Prod.ext (Fin.ext hf1) (Fin.ext hf2)))
  · left
    intro j hj
    have hpar := residue_parity (reciprocalIndex f j)
    rw [hj] at hpar
    fin_cases j <;> norm_num [reciprocalIndex] at hpar <;> omega

/-- A rational lower bound on every actual nonzero Gamma-center frequency. -/
theorem nonzero_center_norm (f : Frequency) (hf : f ≠ 0) :
    (53/100 : ℝ) ≤ ‖longitudinalVector 0 f‖ := by
  have hsq : (53/100 : ℝ)^2 ≤ laplacianSymbol 0 f := by
    rcases reciprocal_residue_classification f hf with hall | ⟨j, hj⟩
    · have h0 := symbol_zero_lower_one f 0 (hall 0)
      have h1 := symbol_zero_lower_one f 1 (hall 1)
      have h2 := symbol_zero_lower_one f 2 (hall 2)
      simp only [laplacianSymbol, Fin.sum_univ_three]
      linarith
    · have hlo := symbol_zero_lower_two f j hj
      have hs := Finset.single_le_sum
        (f := fun j => Complex.normSq (symbol 0 f j))
        (fun i _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
      change Complex.normSq (symbol 0 f j) ≤ laplacianSymbol 0 f at hs
      linarith
  rw [← longitudinalVector_norm_sq] at hsq
  exact (sq_le_sq₀ (by norm_num) (norm_nonneg _)).mp hsq

/-- The entire closed Gamma cube has symbol displacement below seven hundredths. -/
theorem gamma_displacement (c : Momentum) (hc : ∀ j, |c j| ≤ 1/8) :
    phaseScale * momentumNorm c ≤ 7/100 := by
  have hn : momentumNorm c^2 ≤ 3/64 := by
    rw [momentumNorm_sq, Fin.sum_univ_three]
    have h (j : Direction) : (c j)^2 ≤ (1/8 : ℝ)^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hc j) 2
    linarith [h 0, h 1, h 2]
  have hp : phaseScale ≤ 22/70 := by
    unfold phaseScale
    linarith [Real.pi_lt_d4]
  have hn0 : 0 ≤ momentumNorm c := norm_nonneg _
  have hn1 : momentumNorm c ≤ 11/50 := by nlinarith
  have hm := mul_le_mul hp hn1 hn0 (by norm_num : (0 : ℝ) ≤ 22/70)
  norm_num at hm ⊢
  linarith

/-- The Gamma low frequency stays below the entire certificate spectral window. -/
theorem gamma_low (c : Momentum) (hc : ∀ j, |c j| ≤ 1/8) :
    laplacianSymbol c 0 < 1/64 - 1/2^24 := by
  have hz : longitudinalVector 0 0 = 0 := by
    ext j
    fin_cases j <;> simp [longitudinalVector, symbol, shiftSymbol, reciprocalIndex]
  have h := (longitudinal_increment_bound 0 c 0).trans (gamma_displacement c hc)
  simp only [zero_add, hz, sub_zero] at h
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [longitudinalVector_norm_sq] at hsq
  linarith

/-- All other actual Fourier frequencies lie strictly above the mass-13
comparison, uniformly on the closed Gamma cube. -/
theorem gamma_high (c : Momentum) (hc : ∀ j, |c j| ≤ 1/8)
    (f : Frequency) (hf : f ≠ 0) :
    13*(1/64 + 1/2^24) < laplacianSymbol c f := by
  have h := BoxGeometry.longitudinal_norm_shift_lower_uniform 0 c f
    (7/100) (53/100) (gamma_displacement c hc) (nonzero_center_norm f hf)
  simp only [zero_add] at h
  have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 53/100-7/100) h 2
  rw [longitudinalVector_norm_sq] at hsq
  linarith

end Maxwell.Spectral.GammaSymbols
