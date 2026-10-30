import Maxwell.Continuum.TensorChebyshev

/-! Conversion of a finite rational Fourier sum into one dyadic tensor array. -/

namespace Maxwell.Continuum.Profile

variable {ι : Type*} {B : ℕ}

def fourierTensorCoefficient (s : Finset ι) (q : ι → Fin 3 → ℚ) (a : ι → ComplexDyadic B)
    (Q N : ℕ) (j : Fin 3 → Fin (waveDegree (8*Q) N)) :
    ComplexDyadic (B+(waveWorkBits (8*Q) N+waveWorkBits (8*Q) N+waveWorkBits (8*Q) N)) :=
  complexDyadicSum s (fun ν => complexDyadicMul (a ν) (tensorWaveCoefficient (q ν) Q N j))

noncomputable def finiteFourier (s : Finset ι) (q : ι → Fin 3 → ℚ) (a : ι → ComplexDyadic B)
    (x : Fin 3 → ℝ) : ℂ :=
  ∑ ν ∈ s, complexDyadicValue (a ν)*spatialPlaneWave (q ν) x

noncomputable def fourierTensor (s : Finset ι) (q : ι → Fin 3 → ℚ) (a : ι → ComplexDyadic B)
    (Q N : ℕ) (x : Fin 3 → ℝ) : ℂ :=
  ∑ j : Fin 3 → Fin (waveDegree (8*Q) N),
    complexDyadicValue (fourierTensorCoefficient s q a Q N j)*∏ i, (cubeBasis (j i) (x i) : ℂ)

theorem fourierTensor_sum (s : Finset ι) (q : ι → Fin 3 → ℚ) (a : ι → ComplexDyadic B)
    (Q N : ℕ) (x : Fin 3 → ℝ) :
    fourierTensor s q a Q N x=∑ ν ∈ s, complexDyadicValue (a ν)*tensorWave (q ν) Q N x := by
  unfold fourierTensor fourierTensorCoefficient
  simp_rw [complexDyadicSum_value, complexDyadicMul_value, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ν _
  unfold tensorWave
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem finiteFourier_norm (s : Finset ι) (q : ι → Fin 3 → ℚ) (a : ι → ComplexDyadic B)
    (x : Fin 3 → ℝ) :
    ‖finiteFourier s q a x‖≤∑ ν ∈ s, ‖complexDyadicValue (a ν)‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ν _
  rw [norm_mul, spatialPlaneWave_norm, mul_one]

theorem fourierTensor_error (s : Finset ι) (q : ι → Fin 3 → ℚ) (a : ι → ComplexDyadic B)
    (Q N : ℕ) (hq : ∀ ν ∈ s, ∀ i, |q ν i|≤Q)
    {x : Fin 3 → ℝ} (hx : ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1) :
    ‖finiteFourier s q a x-fourierTensor s q a Q N x‖≤
      (∑ ν ∈ s, ‖complexDyadicValue (a ν)‖)*(1/2 : ℝ)^(N+23) := by
  rw [fourierTensor_sum]
  unfold finiteFourier
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ν hν
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left (tensorWave_error (q ν) Q N (hq ν hν) hx) (norm_nonneg _)

theorem fourierTensorCoefficient_norm (s : Finset ι) (q : ι → Fin 3 → ℚ) (a : ι → ComplexDyadic B)
    (Q N : ℕ) (hq : ∀ ν ∈ s, ∀ i, |q ν i|≤Q)
    (j : Fin 3 → Fin (waveDegree (8*Q) N)) :
    ‖complexDyadicValue (fourierTensorCoefficient s q a Q N j)‖≤
      (∑ ν ∈ s, ‖complexDyadicValue (a ν)‖)*22^3 := by
  unfold fourierTensorCoefficient
  rw [complexDyadicSum_value, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ν hν
  rw [complexDyadicMul_value, norm_mul]
  exact mul_le_mul_of_nonneg_left (tensorWaveCoefficient_norm (q ν) Q N (hq ν hν) j) (norm_nonneg _)

theorem fourierTensor_norm (s : Finset ι) (q : ι → Fin 3 → ℚ) (a : ι → ComplexDyadic B)
    (Q N : ℕ) (hq : ∀ ν ∈ s, ∀ i, |q ν i|≤Q)
    {x : Fin 3 → ℝ} (hx : ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1) :
    ‖fourierTensor s q a Q N x‖≤2*∑ ν ∈ s, ‖complexDyadicValue (a ν)‖ := by
  have he := fourierTensor_error s q a Q N hq hx
  have hf := finiteFourier_norm s q a x
  have ht := norm_sub_le_norm_sub_add_norm_sub (fourierTensor s q a Q N x) (finiteFourier s q a x) 0
  simp only [sub_zero] at ht
  rw [norm_sub_rev (fourierTensor s q a Q N x) _] at ht
  have hp : (1/2 : ℝ)^(N+23)≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hp
    (Finset.sum_nonneg (s := s) (fun ν _ => norm_nonneg (complexDyadicValue (a ν))))
  linarith

theorem fourierTensor_continuous (s : Finset ι) (q : ι → Fin 3 → ℚ) (a : ι → ComplexDyadic B)
    (Q N : ℕ) : Continuous (fourierTensor s q a Q N) := by
  have he : fourierTensor s q a Q N=fun x => ∑ ν ∈ s, complexDyadicValue (a ν)*tensorWave (q ν) Q N x :=
    funext (fourierTensor_sum s q a Q N)
  rw [he]
  apply continuous_finsetSum
  intro ν _
  exact continuous_const.mul (tensorWave_continuous (q ν) Q N)

#print axioms fourierTensor_error
#print axioms fourierTensorCoefficient_norm

end Maxwell.Continuum.Profile
