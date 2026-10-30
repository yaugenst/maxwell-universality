import Maxwell.Interfaces
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Algebra.Order.Floor.Ring

/-! Executable fixed-point rounding with a proved absolute error. -/

namespace Maxwell.Continuum

def roundDyadic (P : ℕ) (q : ℚ) : Dyadic P := ⟨⌊q*(2 : ℚ)^P⌋⟩

theorem roundDyadic_error_rat (P : ℕ) (q : ℚ) :
    |q-(roundDyadic P q).value| ≤ (1/2 : ℚ)^P := by
  have h0 := Int.floor_le (q*(2 : ℚ)^P)
  have h1 := (Int.lt_floor_add_one (q*(2 : ℚ)^P)).le
  have hp : 0 < (2 : ℚ)^P := by positivity
  have he : (1/2 : ℚ)^P = 1/(2 : ℚ)^P := by rw [div_pow, one_pow]
  rw [he, roundDyadic, Dyadic.value]
  have hn : 0 ≤ q-(⌊q*(2 : ℚ)^P⌋ : ℚ)/(2 : ℚ)^P := by
    apply sub_nonneg.mpr
    exact (div_le_iff₀ hp).mpr h0
  rw [abs_of_nonneg hn]
  apply (le_div_iff₀ hp).mpr
  have hc : (q-(⌊q*(2 : ℚ)^P⌋ : ℚ)/(2 : ℚ)^P)*(2 : ℚ)^P =
      q*(2 : ℚ)^P-(⌊q*(2 : ℚ)^P⌋ : ℚ) := by field_simp
  rw [hc]
  linarith

theorem roundDyadic_error (P : ℕ) (q : ℚ) :
    |(q : ℝ)-((roundDyadic P q).value : ℝ)| ≤ (1/2 : ℝ)^P := by
  have h : ((|q-(roundDyadic P q).value| : ℚ) : ℝ) ≤ (((1/2 : ℚ)^P : ℚ) : ℝ) :=
    Rat.cast_le.mpr (roundDyadic_error_rat P q)
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_pow, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat] using h

theorem roundDyadic_numerator_bound (P : ℕ) (q : ℚ) :
    |((roundDyadic P q).numerator : ℚ)| ≤ |q| * (2 : ℚ)^P+1 := by
  have h0 := Int.floor_le (q*(2 : ℚ)^P)
  have h1 := (Int.lt_floor_add_one (q*(2 : ℚ)^P)).le
  have hp : 0 ≤ (2 : ℚ)^P := by positivity
  change |(⌊q*(2 : ℚ)^P⌋ : ℚ)| ≤ _
  apply abs_le.mpr
  constructor
  · have h := mul_le_mul_of_nonneg_right (neg_abs_le q) hp
    linarith
  · have h := mul_le_mul_of_nonneg_right (le_abs_self q) hp
    linarith

#print axioms roundDyadic_error

end Maxwell.Continuum
