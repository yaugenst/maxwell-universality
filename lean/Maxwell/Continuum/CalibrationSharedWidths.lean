import Maxwell.Continuum.CalibrationSharedDenominator

/-! Integer numerator growth is geometric in the layer count, so its
bit width grows linearly in that count. The one shared denominator has
the same property. These are raw integer bounds, without normalization. -/

namespace Maxwell.Continuum.Calibration

variable {ι : Type*} [Fintype ι]

theorem sharedNumerator_abs_le (D : ℕ) (hD : 1 ≤ D) (A : ι → ι → ℤ) (b : ι → ℤ)
    {B C : ℤ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ i, |b i| ≤ B) (hA : ∀ i, ∑ j, |A i j| ≤ C) (K : ℕ) (i : ι) :
    |sharedNumerator D A b K i| ≤ B*((D : ℤ)+C+1)^K := by
  have hD' : (1 : ℤ) ≤ D := by exact_mod_cast hD
  have hS : 0 ≤ (D : ℤ)+C+1 := by omega
  induction K generalizing i with
  | zero => simpa only [sharedNumerator,Pi.zero_apply,abs_zero,pow_zero,mul_one] using hB
  | succ K ih =>
    have hp : (D : ℤ)^K ≤ ((D : ℤ)+C+1)^K := pow_le_pow_left₀ (by positivity) (by omega) K
    calc
      _ ≤ |(D : ℤ)^K*b i|+|∑ j, A i j*sharedNumerator D A b K j| := abs_add_le _ _
      _ ≤ (D : ℤ)^K*B+∑ j, |A i j| * (B*((D : ℤ)+C+1)^K) := by
        apply add_le_add
        · rw [abs_mul,abs_pow,abs_of_nonneg (by positivity : (0 : ℤ) ≤ D)]
          exact mul_le_mul_of_nonneg_left (hb i) (by positivity)
        · apply (Finset.abs_sum_le_sum_abs _ _).trans
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (ih j) (abs_nonneg _)
      _ = (D : ℤ)^K*B+(∑ j, |A i j|)*(B*((D : ℤ)+C+1)^K) := by rw [Finset.sum_mul]
      _ ≤ ((D : ℤ)+C+1)^K*B+C*(B*((D : ℤ)+C+1)^K) :=
        add_le_add (mul_le_mul_of_nonneg_right hp hB)
          (mul_le_mul_of_nonneg_right (hA i) (mul_nonneg hB (pow_nonneg hS K)))
      _ ≤ B*((D : ℤ)+C+1)^(K+1) := by
        rw [pow_succ]
        have hh := mul_le_mul_of_nonneg_right (by omega : 1+C ≤ (D : ℤ)+C+1)
          (mul_nonneg hB (pow_nonneg hS K))
        convert! hh using 1 <;> ring

theorem sharedNumerator_bit_bound (D : ℕ) (hD : 1 ≤ D) (A : ι → ι → ℤ) (b : ι → ℤ)
    (W : ℕ) (hb : ∀ i, |b i| ≤ (2 : ℤ)^W)
    (hA : ∀ i, ∑ j, |A i j| ≤ (2 : ℤ)^W)
    (hwidth : (D : ℤ)+(2 : ℤ)^W+1 ≤ (2 : ℤ)^(W+2)) (K : ℕ) (i : ι) :
    |sharedNumerator D A b K i| ≤ (2 : ℤ)^(W+(W+2)*K) := by
  have h := sharedNumerator_abs_le D hD A b (by positivity) (by positivity) hb hA K i
  apply h.trans
  calc
    _ ≤ (2 : ℤ)^W*((2 : ℤ)^(W+2))^K := by
      gcongr
    _ = (2 : ℤ)^(W+(W+2)*K) := by rw [← pow_mul,← pow_add]

#print axioms sharedNumerator_bit_bound

end Maxwell.Continuum.Calibration
