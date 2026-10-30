import Maxwell.Continuum.ChebyshevWaveFourier
import Maxwell.Continuum.ProfileCosineSeries
import Maxwell.Continuum.ProfileChebyshevBasis
import Maxwell.Continuum.SeriesTruncation

/-! Actual cosine/Chebyshev reconstruction of each plane wave on the closed interval. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Profile

open AddCircle Set
local instance : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩

def waveCircle (k : ℝ) : C(AddCircle (2*Real.pi), ℂ) :=
  ⟨(waveAngular_periodic k).lift, continuous_quot_lift _ (waveAngular_contDiff k).continuous⟩

theorem waveCircle_coe (k φ : ℝ) : waveCircle k (φ : AddCircle (2*Real.pi))=waveAngular k φ := rfl

theorem waveCircle_coefficient (k : ℝ) (n : ℤ) : fourierCoeff (waveCircle k) n=waveCoefficient k n := by
  rw [fourierCoeff_eq_intervalIntegral (waveCircle k) n 0, waveCoefficient, derivativeCoefficient,
    fourierCoeffOn_eq_integral]
  simp only [zero_add, sub_zero, waveCircle_coe, iteratedDeriv_zero]
  simp only [fourier_coe_apply, sub_zero]

theorem wave_hasSum (k φ : ℝ) :
    HasSum (fun n : ℤ => mode n φ*waveCoefficient k n) (waveAngular k φ) := by
  have hs : Summable (fourierCoeff (waveCircle k)) := by
    have he : fourierCoeff (waveCircle k)=waveCoefficient k := funext (waveCircle_coefficient k)
    rw [he]
    exact (waveCoefficient_summable_norm k).of_norm
  have h := has_pointwise_sum_fourier_series_of_summable hs (φ : AddCircle (2*Real.pi))
  simpa only [waveCircle_coefficient, waveCircle_coe, ← mode_eq_fourier, smul_eq_mul, mul_comm] using h

theorem mode_pair (n : ℤ) (φ : ℝ) (c : ℂ) :
    (mode n φ*c+mode n (-φ)*c)/2=c*(Real.cos ((n : ℝ)*φ) : ℂ) := by
  have hm : mode n φ+mode n (-φ)=2*(Real.cos ((n : ℝ)*φ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.add_re, mode_re, mul_neg, Real.cos_neg, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im]
      norm_num
      ring
    · simp only [Complex.add_im, mode_im, mul_neg, Real.sin_neg, add_neg_cancel,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      norm_num
  calc
    _ = (mode n φ+mode n (-φ))*c/2 := by ring
    _ = _ := by rw [hm]; ring

def waveCosineCoefficient (k : ℝ) (j : ℕ) : ℂ :=
  if j=0 then waveCoefficient k 0 else waveCoefficient k (j : ℤ)+waveCoefficient k (-(j : ℤ))

theorem waveCosineCoefficient_hasSum (k φ : ℝ) :
    HasSum (fun j : ℕ => waveCosineCoefficient k j*(Real.cos ((j : ℝ)*φ) : ℂ)) (waveAngular k φ) := by
  have h := ((wave_hasSum k φ).add (wave_hasSum k (-φ))).div_const 2
  simp only [mode_pair, waveAngular_even, add_self_div_two] at h
  have hp := h.nat_add_neg.sub (hasSum_ite_eq (0 : ℕ) (waveCoefficient k 0))
  simp only [Int.cast_zero, zero_mul, Real.cos_zero, Complex.ofReal_one, mul_one,
    add_sub_cancel_right] at hp
  convert hp using 1
  funext j
  by_cases hj : j=0
  · subst j
    simp only [waveCosineCoefficient, ↓reduceIte, Nat.cast_zero, Int.cast_zero,
      neg_zero, zero_mul, Real.cos_zero, Complex.ofReal_one, mul_one]
    ring
  · simp only [waveCosineCoefficient, hj, ↓reduceIte, Int.cast_natCast,
      Int.cast_neg, neg_mul, Real.cos_neg, sub_zero]
    ring

theorem waveCosineCoefficient_bound (k : ℝ) (j : ℕ) : ‖waveCosineCoefficient k j‖ ≤ 2 := by
  unfold waveCosineCoefficient
  split_ifs
  · exact (waveCoefficient_bound k 0).trans (by norm_num)
  · have hp := waveCoefficient_bound k (j : ℤ)
    have hm := waveCoefficient_bound k (-(j : ℤ))
    exact (norm_add_le _ _).trans (by linarith)

theorem waveCosineCoefficient_decay (k : ℝ) (j : ℕ) :
    ‖waveCosineCoefficient k j‖ ≤ 2*Real.exp (4*|k|)*(1/2 : ℝ)^(j/2) := by
  have hp := waveCoefficient_decay k (j : ℤ)
  have hm := waveCoefficient_decay k (-(j : ℤ))
  simp only [Int.natAbs_natCast, Int.natAbs_neg] at hp hm
  by_cases hj : j=0
  · subst j
    simp only [waveCosineCoefficient, ↓reduceIte, Nat.zero_div, pow_zero, mul_one]
    have he : 1 ≤ Real.exp (4*|k|) := Real.one_le_exp_iff.mpr (by positivity)
    exact (waveCoefficient_bound k 0).trans (by linarith)
  · rw [waveCosineCoefficient, ite_eq_right hj]
    exact (norm_add_le _ _).trans (by nlinarith only [hp,hm])

theorem waveCosineCoefficient_summable (k : ℝ) :
    Summable (fun j : ℕ => ‖waveCosineCoefficient k j‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (waveCosineCoefficient_decay k)
    (half_geometric_summable.mul_left (2*Real.exp (4*|k|)))

def cubeBasis (j : ℕ) (x : ℝ) : ℝ := basis j ((x+1)/2)

theorem cubeBasis_eq (j : ℕ) (x : ℝ) : cubeBasis j x=(Polynomial.Chebyshev.T ℝ (j : ℤ)).eval x := by
  rw [cubeBasis, basis_eq, show 2*((x+1)/2)-1=x by ring]

theorem cubeBasis_bound (j : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : |cubeBasis j x| ≤ 1 :=
  basis_bound j ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem wave_chebyshev_hasSum (k : ℝ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun j : ℕ => waveCosineCoefficient k j*(cubeBasis j x : ℂ))
      (Complex.exp (Complex.I*(k : ℂ)*(x : ℂ))) := by
  let φ := Real.arccos x
  have hc : Real.cos φ=x := Real.cos_arccos hx.1 hx.2
  have h := waveCosineCoefficient_hasSum k φ
  simp only [waveAngular, hc] at h
  convert h using 1
  funext j
  have he : cubeBasis j x=Real.cos ((j : ℝ)*φ) := by
    unfold cubeBasis
    rw [← hc, add_comm, basis_cosine]
  rw [he]

def waveChebyshevPolynomial (k : ℝ) (D : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.range D, waveCosineCoefficient k j*(cubeBasis j x : ℂ)

theorem waveChebyshevPolynomial_error (k : ℝ) (D : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖Complex.exp (Complex.I*(k : ℂ)*(x : ℂ))-waveChebyshevPolynomial k D x‖ ≤
      16*Real.exp (4*|k|)*(1/2 : ℝ)^(D/2) := by
  have hb (j : ℕ) : ‖waveCosineCoefficient k j*(cubeBasis j x : ℂ)‖ ≤ ‖waveCosineCoefficient k j‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (norm_nonneg _) (cubeBasis_bound j hx)
  have h := series_truncation_norm _ _ (waveCosineCoefficient_summable k) hb D
  rw [(wave_chebyshev_hasSum k hx).tsum_eq] at h
  change ‖Complex.exp (Complex.I*(k : ℂ)*(x : ℂ))-waveChebyshevPolynomial k D x‖ ≤ _ at h
  have htail : Summable (fun j : ℕ => if D≤j then (1/2 : ℝ)^(j/2) else 0) := by
    apply Summable.of_nonneg_of_le (fun j => by split_ifs <;> positivity) _ half_geometric_summable
    intro j
    split_ifs
    · exact le_rfl
    · positivity
  have hcs : Summable (fun j : ℕ => if D≤j then ‖waveCosineCoefficient k j‖ else 0) := by
    apply Summable.of_nonneg_of_le (fun j => by split_ifs <;> positivity) _ (waveCosineCoefficient_summable k)
    intro j
    split_ifs <;> simp
  apply h.trans
  calc
    _ ≤ ∑' j : ℕ, (2*Real.exp (4*|k|))*(if D≤j then (1/2 : ℝ)^(j/2) else 0) := by
      apply Summable.tsum_le_tsum _ hcs (htail.mul_left _)
      intro j
      split_ifs
      · exact waveCosineCoefficient_decay k j
      · simp
    _ = (2*Real.exp (4*|k|))*(∑' j : ℕ, if D≤j then (1/2 : ℝ)^(j/2) else 0) := tsum_mul_left
    _ ≤ (2*Real.exp (4*|k|))*(8*(1/2 : ℝ)^(D/2)) :=
      mul_le_mul_of_nonneg_left (half_geometric_tail D) (by positivity)
    _ = _ := by ring

#print axioms wave_chebyshev_hasSum
#print axioms waveChebyshevPolynomial_error

end Maxwell.Continuum.Profile
