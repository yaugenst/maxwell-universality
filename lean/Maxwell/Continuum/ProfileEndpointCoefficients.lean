import Maxwell.Continuum.ProfileFiniteSeries
import Maxwell.Continuum.DyadicRounding

/-! Exact endpoint correction in the original dyadic Chebyshev representation. -/

namespace Maxwell.Continuum.Profile

def endpointValueNumerator {P : ℕ} (D : ℕ) (c : ℕ → Dyadic P) : ℤ :=
  ∑ j ∈ Finset.range D, (c j).numerator

def endpointSlopeNumerator {P : ℕ} (D : ℕ) (c : ℕ → Dyadic P) : ℤ :=
  ∑ j ∈ Finset.range D, (c j).numerator*(j : ℤ)^2

def matchedCoefficient {P : ℕ} (D : ℕ) (c : ℕ → Dyadic P) (j : ℕ) : Dyadic P :=
  ⟨(c j).numerator+
    (if j=0 then -endpointValueNumerator D c+endpointSlopeNumerator D c else 0)+
    (if j=1 then -endpointSlopeNumerator D c else 0)⟩

theorem endpointValueNumerator_value {P : ℕ} (D : ℕ) (c : ℕ → Dyadic P) :
    (endpointValueNumerator D c : ℚ)/(2 : ℚ)^P=∑ j ∈ Finset.range D, (c j).value := by
  simp only [endpointValueNumerator, Int.cast_sum, Finset.sum_div, Dyadic.value]

theorem endpointSlopeNumerator_value {P : ℕ} (D : ℕ) (c : ℕ → Dyadic P) :
    (endpointSlopeNumerator D c : ℚ)/(2 : ℚ)^P=∑ j ∈ Finset.range D, (c j).value*(j : ℚ)^2 := by
  simp only [endpointSlopeNumerator, Int.cast_sum, Int.cast_mul, Int.cast_pow,
    Int.cast_natCast, Finset.sum_div, Dyadic.value]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem matchedCoefficient_value {P : ℕ} (D : ℕ) (c : ℕ → Dyadic P) (j : ℕ) :
    (matchedCoefficient D c j).value=(c j).value+
      (if j=0 then -(∑ k ∈ Finset.range D, (c k).value)+
        ∑ k ∈ Finset.range D, (c k).value*(k : ℚ)^2 else 0)+
      (if j=1 then -(∑ k ∈ Finset.range D, (c k).value*(k : ℚ)^2) else 0) := by
  rw [← endpointValueNumerator_value, ← endpointSlopeNumerator_value]
  unfold matchedCoefficient Dyadic.value
  split_ifs <;> push_cast <;> ring

theorem finiteProfile_adjust_two (D : ℕ) (hD : 2 ≤ D) (c : ℕ → ℝ) (a b t : ℝ) :
    finiteProfile D (fun j => c j+(if j=0 then a else 0)+(if j=1 then b else 0)) t=
      finiteProfile D c t+a+b*(2*t-1) := by
  have h0 : 0<D := by omega
  have h1 : 1<D := by omega
  simp only [finiteProfile, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_range, h0, h1, ↓reduceIte,
    basis_eq, Int.natCast_zero, Int.natCast_one, Polynomial.Chebyshev.T_zero,
    Polynomial.Chebyshev.T_one, Polynomial.eval_one, Polynomial.eval_X, mul_one]

theorem matchedCoefficient_evaluation {P : ℕ} (D : ℕ) (hD : 2 ≤ D)
    (c : ℕ → Dyadic P) (t : ℝ) :
    finiteProfile D (fun j => ((matchedCoefficient D c j).value : ℝ)) t=
      finiteProfile D (fun j => ((c j).value : ℝ)) t-
      finiteProfile D (fun j => ((c j).value : ℝ)) 1-
      finiteProfileDerivative D (fun j => ((c j).value : ℝ)) 1*(t-1) := by
  have he (j : ℕ) : ((matchedCoefficient D c j).value : ℝ)=((c j).value : ℝ)+
      (if j=0 then -(∑ k ∈ Finset.range D, ((c k).value : ℝ))+
        ∑ k ∈ Finset.range D, ((c k).value : ℝ)*(k : ℝ)^2 else 0)+
      (if j=1 then -(∑ k ∈ Finset.range D, ((c k).value : ℝ)*(k : ℝ)^2) else 0) := by
    rw [matchedCoefficient_value]
    split_ifs <;> push_cast <;> rfl
  simp_rw [he]
  rw [finiteProfile_adjust_two D hD, finiteProfile_endpoint, finiteProfileDerivative_endpoint]
  ring

#print axioms matchedCoefficient_evaluation

end Maxwell.Continuum.Profile
