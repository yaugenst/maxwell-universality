import Maxwell.Continuum.ChebyshevWaveEncoded
import Maxwell.Continuum.ComplexDyadicAlgebra

/-! Exact finite tensor coefficients for the three-dimensional plane waves. -/

namespace Maxwell.Continuum.Profile

noncomputable def spatialPlaneWave (q : Fin 3 → ℚ) (x : Fin 3 → ℝ) : ℂ :=
  Complex.exp (Complex.I*((2*Real.pi*∑ i, (q i : ℝ)*x i : ℝ) : ℂ))

theorem spatialPlaneWave_product (q : Fin 3 → ℚ) (x : Fin 3 → ℝ) :
    spatialPlaneWave q x=∏ i, Complex.exp (Complex.I*((2*Real.pi*(q i : ℝ) : ℝ) : ℂ)*(x i : ℂ)) := by
  unfold spatialPlaneWave
  rw [Fin.sum_univ_three, Fin.prod_univ_three]
  push_cast
  rw [show Complex.I*(2*(Real.pi : ℂ)*((q 0 : ℂ)*(x 0 : ℂ)+(q 1 : ℂ)*(x 1 : ℂ)+(q 2 : ℂ)*(x 2 : ℂ)))=
    (Complex.I*(2*(Real.pi : ℂ)*(q 0 : ℂ))*(x 0 : ℂ)+
      Complex.I*(2*(Real.pi : ℂ)*(q 1 : ℂ))*(x 1 : ℂ))+
      Complex.I*(2*(Real.pi : ℂ)*(q 2 : ℂ))*(x 2 : ℂ) by ring]
  rw [Complex.exp_add, Complex.exp_add]

theorem spatialPlaneWave_norm (q : Fin 3 → ℚ) (x : Fin 3 → ℝ) : ‖spatialPlaneWave q x‖=1 := by
  simp [spatialPlaneWave, Complex.norm_exp]

def tensorWaveCoefficient (q : Fin 3 → ℚ) (Q N : ℕ)
    (j : Fin 3 → Fin (waveDegree (8*Q) N)) :
    ComplexDyadic (waveWorkBits (8*Q) N+waveWorkBits (8*Q) N+waveWorkBits (8*Q) N) :=
  complexDyadicTriple (fun i => waveRoundedCoefficient (q i) Q N (j i))

noncomputable def tensorWave (q : Fin 3 → ℚ) (Q N : ℕ) (x : Fin 3 → ℝ) : ℂ :=
  ∑ j : Fin 3 → Fin (waveDegree (8*Q) N),
    complexDyadicValue (tensorWaveCoefficient q Q N j)*∏ i, (cubeBasis (j i) (x i) : ℂ)

theorem tensorWave_product (q : Fin 3 → ℚ) (Q N : ℕ) (x : Fin 3 → ℝ) :
    tensorWave q Q N x=∏ i, encodedWave (q i) Q N (x i) := by
  have he (i : Fin 3) : encodedWave (q i) Q N (x i)=
      ∑ j : Fin (waveDegree (8*Q) N),
        complexDyadicValue (waveRoundedCoefficient (q i) Q N j)*(cubeBasis j (x i) : ℂ) := by
    exact (Fin.sum_univ_eq_sum_range
      (fun j : ℕ => complexDyadicValue (waveRoundedCoefficient (q i) Q N j)*(cubeBasis j (x i) : ℂ))
      (waveDegree (8*Q) N)).symm
  simp_rw [he]
  rw [Fintype.prod_sum]
  unfold tensorWave tensorWaveCoefficient
  simp_rw [complexDyadicTriple_value, ← Finset.prod_mul_distrib]

theorem triple_product_error (a b : Fin 3 → ℂ) {δ : ℝ} (hδ : 0≤δ)
    (ha : ∀ i, ‖a i‖≤1) (hb : ∀ i, ‖b i‖≤2) (he : ∀ i, ‖a i-b i‖≤δ) :
    ‖(∏ i, a i)-(∏ i, b i)‖≤7*δ := by
  rw [Fin.prod_univ_three, Fin.prod_univ_three]
  calc
    _ = ‖((a 0-b 0)*a 1*a 2+b 0*(a 1-b 1)*a 2)+b 0*b 1*(a 2-b 2)‖ := by congr 1; ring
    _ ≤ (‖(a 0-b 0)*a 1*a 2‖+‖b 0*(a 1-b 1)*a 2‖)+‖b 0*b 1*(a 2-b 2)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ((δ*1*1)+(2*δ*1))+(2*2*δ) := by
      simp only [norm_mul]
      gcongr
      · exact he 0
      · exact ha 1
      · exact ha 2
      · exact hb 0
      · exact he 1
      · exact ha 2
      · exact hb 0
      · exact hb 1
      · exact he 2
    _ = _ := by ring

theorem tensorWave_error (q : Fin 3 → ℚ) (Q N : ℕ) (hq : ∀ i, |q i|≤Q)
    {x : Fin 3 → ℝ} (hx : ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1) :
    ‖spatialPlaneWave q x-tensorWave q Q N x‖≤(1/2 : ℝ)^(N+23) := by
  rw [spatialPlaneWave_product, tensorWave_product]
  have he := triple_product_error
    (fun i => Complex.exp (Complex.I*((2*Real.pi*(q i : ℝ) : ℝ) : ℂ)*(x i : ℂ)))
    (fun i => encodedWave (q i) Q N (x i))
    (by positivity : 0≤(1/2 : ℝ)^(N+26))
    (fun i => by simp [Complex.norm_exp])
    (fun i => encodedWave_norm (q i) Q N (hq i) (hx i))
    (fun i => encodedWave_error (q i) Q N (hq i) (hx i))
  apply he.trans
  rw [show N+26=(N+23)+3 by omega, pow_add]
  nlinarith only [pow_nonneg (by norm_num : (0 : ℝ)≤1/2) (N+23)]

theorem tensorWaveCoefficient_norm (q : Fin 3 → ℚ) (Q N : ℕ) (hq : ∀ i, |q i|≤Q)
    (j : Fin 3 → Fin (waveDegree (8*Q) N)) :
    ‖complexDyadicValue (tensorWaveCoefficient q Q N j)‖≤22^3 := by
  unfold tensorWaveCoefficient
  rw [complexDyadicTriple_value, norm_prod]
  calc
    _ ≤ ∏ _i : Fin 3, (22 : ℝ) := by
      apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
      intro i _
      exact waveRoundedCoefficient_bound (q i) Q N (j i) (hq i) (j i).isLt.le
    _ = _ := by simp

theorem tensorWave_count (Q N : ℕ) :
    Fintype.card (Fin 3 → Fin (waveDegree (8*Q) N))=(waveDegree (8*Q) N)^3 := by simp

theorem tensorWave_continuous (q : Fin 3 → ℚ) (Q N : ℕ) : Continuous (tensorWave q Q N) := by
  have he : tensorWave q Q N=fun x => ∏ i, encodedWave (q i) Q N (x i) := funext (tensorWave_product q Q N)
  rw [he]
  apply continuous_finsetProd
  intro i _
  exact (encodedWave_continuous (q i) Q N).comp (continuous_apply i)

#print axioms tensorWave_error
#print axioms tensorWaveCoefficient_norm

end Maxwell.Continuum.Profile
