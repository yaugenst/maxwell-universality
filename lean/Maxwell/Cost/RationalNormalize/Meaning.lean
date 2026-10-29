import Maxwell.Cost.RationalNormalize.Sqrt
import Maxwell.Cost.CalibrationMatrix.Scale.Semantics

namespace Maxwell.Cost.RationalNormalize

open CalibrationMatrix

def outputDenominator {n : ℕ} (y : Fin n → ℤ) (C D p : ℕ) : ℕ :=
  C*upperNumerator (Maxwell.Defect.integerNormSq y) C D p

theorem outputDenominator_pos {n : ℕ} (y : Fin n → ℤ) (C D p : ℕ) (hC : 0 < C) :
    0 < outputDenominator y C D p := by
  unfold outputDenominator upperNumerator
  positivity

/-- The numerator multiplier and denominator words represent exactly the
already proved bounded rational normalization routine. -/
theorem output_pair_eq {n : ℕ} (y : Fin n → ℤ) (C D p : ℕ) (hC : 0 < C) (i : Fin n) :
    ((D*2^p : ℕ) : ℚ)*(y i : ℚ)/(outputDenominator y C D p : ℚ) =
      Maxwell.Defect.RationalNormalize.vector (fun j => (y j : ℚ)) ((C : ℚ)/D) p i := by
  have hu := upperNumerator_binding (Maxwell.Defect.integerNormSq y) C D p hC
  have hv := Maxwell.Defect.RationalNormalize.integer_output_eq y C D
    (upperNumerator (Maxwell.Defect.integerNormSq y) C D p) p
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hu) i
  rw [hv]
  simp only [outputDenominator, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

theorem scaled_output_eq {n : ℕ} (d : Scale.Data n)
    (words : Fin 4 → Vector (List Bool) n) (y : Fin n → ℤ) (C D p : ℕ)
    (hC : 0 < C) (hK : d.K = D*2^p) (hy : (Scale.channels words 0 1).value = y)
    (hp : ∀ i, (Scale.positive d words i).bits.length ≤ addressValue d.width)
    (hn : ∀ i, (Scale.negative d words i).bits.length ≤ addressValue d.width) (i : Fin n) :
    (((Scale.channels (Scale.filledWords d words n) 2 3).value i : ℤ) : ℚ) /
        (outputDenominator y C D p : ℚ) =
      Maxwell.Defect.RationalNormalize.vector (fun j => (y j : ℚ)) ((C : ℚ)/D) p i := by
  rw [Scale.filled_channels d words hp hn, value_scale, hy, hK]
  push_cast
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using output_pair_eq y C D p hC i

end Maxwell.Cost.RationalNormalize
