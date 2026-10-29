import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic

/-! Executable dyadic Horner gates with independent errors at every gate.
The input list is most-significant fractional bit first. Recursion evaluates
the tail before appending the next half/add gate, as in the manuscript.
-/

namespace Maxwell.Logical.Horner

open scoped BigOperators

def numerator : List Bool → ℕ
  | [] => 0
  | b :: bits => (if b then 2 ^ bits.length else 0) + numerator bits

def coefficient : List Bool → ℚ
  | [] => 0
  | b :: bits => ((if b then (1 : ℚ) else 0) + coefficient bits) / 2

def evaluate : List Bool → ℚ → (ℕ → ℚ) → ℚ
  | [], _, _ => 0
  | b :: bits, input, error =>
      ((if b then input else 0) + evaluate bits input (fun j => error (j + 1))) / 2 + error 0

theorem numerator_lt_denominator (bits : List Bool) :
    numerator bits < 2 ^ bits.length := by
  induction bits with
  | nil => norm_num [numerator]
  | cons b bits ih =>
      have hp : 0 < 2 ^ bits.length := pow_pos (by omega) _
      cases b <;> simp only [numerator, Bool.false_eq_true, ↓reduceIte,
        List.length_cons, pow_succ] <;> omega

/-- Exact finite dyadic value; this is valid for every bit list length. -/
theorem coefficient_eq_dyadic (bits : List Bool) :
    coefficient bits = (numerator bits : ℚ) / (2 : ℚ) ^ bits.length := by
  induction bits with
  | nil => norm_num [coefficient, numerator]
  | cons b bits ih =>
      have hp : (2 : ℚ) ^ bits.length ≠ 0 := pow_ne_zero _ (by norm_num)
      cases b <;> simp [coefficient, numerator, ih, pow_succ]
      · ring
      · field_simp

theorem coefficient_nonneg (bits : List Bool) : 0 ≤ coefficient bits := by
  rw [coefficient_eq_dyadic]
  positivity

theorem coefficient_lt_one (bits : List Bool) : coefficient bits < 1 := by
  rw [coefficient_eq_dyadic]
  apply (div_lt_one (by positivity)).2
  exact_mod_cast numerator_lt_denominator bits

/-- Fixed-width binary compilation of a nonnegative integer numerator. -/
def encode : ℕ → ℕ → List Bool
  | 0, _ => []
  | precision + 1, value =>
      decide (2 ^ precision ≤ value) :: encode precision (value % 2 ^ precision)

@[simp] theorem encode_length (precision value : ℕ) :
    (encode precision value).length = precision := by
  induction precision generalizing value with
  | zero => rfl
  | succ precision ih => simp [encode, ih]

/-- The executable bit compiler reconstructs every admitted dyadic numerator. -/
theorem numerator_encode (precision value : ℕ) (h : value < 2 ^ precision) :
    numerator (encode precision value) = value := by
  induction precision generalizing value with
  | zero =>
      simp only [pow_zero] at h
      have hv : value = 0 := by omega
      simp [encode, numerator, hv]
  | succ precision ih =>
      have hp : 0 < 2 ^ precision := pow_pos (by omega) _
      have hm : value % 2 ^ precision < 2 ^ precision := Nat.mod_lt _ hp
      simp only [encode, numerator, encode_length, ih _ hm, decide_eq_true_eq]
      by_cases hv : 2 ^ precision ≤ value
      · simp only [hv, ↓reduceIte]
        rw [Nat.mod_eq_sub_mod hv]
        have ht : value - 2 ^ precision < 2 ^ precision := by
          rw [pow_succ] at h
          omega
        rw [Nat.mod_eq_of_lt ht]
        omega
      · simp only [hv, ↓reduceIte, zero_add]
        exact Nat.mod_eq_of_lt (by omega)

theorem coefficient_encode (precision value : ℕ) (h : value < 2 ^ precision) :
    coefficient (encode precision value) = (value : ℚ) / (2 : ℚ) ^ precision := by
  rw [coefficient_eq_dyadic, numerator_encode precision value h, encode_length]

/-- With zero equation residuals the gates compute the dyadic product exactly. -/
theorem evaluate_zero_error (bits : List Bool) (input : ℚ) :
    evaluate bits input 0 = coefficient bits * input := by
  induction bits with
  | nil => simp [evaluate, coefficient]
  | cons b bits ih =>
      simp only [evaluate, coefficient, Pi.zero_apply, add_zero]
      change ((if b then input else 0) + evaluate bits input 0) / 2 =
        ((if b then 1 else 0) + coefficient bits) / 2 * input
      rw [ih]
      cases b <;> simp <;> ring

/-- Exact separation of the intended product and all auxiliary errors. -/
theorem evaluate_error_superposition (bits : List Bool) (input : ℚ)
    (error : ℕ → ℚ) :
    evaluate bits input error = coefficient bits * input + evaluate bits 0 error := by
  induction bits generalizing error with
  | nil => simp [evaluate, coefficient]
  | cons b bits ih =>
      rw [evaluate, ih, evaluate, coefficient]
      cases b <;> simp <;> ring

/-- Arbitrary residuals on Horner equations accumulate at most linearly.
This statement does not assume that the auxiliary variables are exact. -/
theorem evaluate_zero_input_bound (bits : List Bool) (error : ℕ → ℚ) :
    |evaluate bits 0 error| ≤ ∑ j ∈ Finset.range bits.length, |error j| := by
  induction bits generalizing error with
  | nil => simp [evaluate]
  | cons b bits ih =>
      have hi := ih (fun j => error (j + 1))
      have hs : 0 ≤ ∑ j ∈ Finset.range bits.length, |error (j + 1)| :=
        Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      simp only [evaluate, ite_self, zero_add, List.length_cons]
      rw [Finset.sum_range_succ']
      calc
        |evaluate bits 0 (fun j => error (j + 1)) / 2 + error 0| ≤
            |evaluate bits 0 (fun j => error (j + 1)) / 2| + |error 0| := abs_add_le _ _
        _ ≤ (∑ j ∈ Finset.range bits.length, |error (j + 1)|) + |error 0| := by
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℚ) < 2)]
          linarith

theorem arbitrary_residual_bound (bits : List Bool) (input : ℚ) (error : ℕ → ℚ) :
    |evaluate bits input error - coefficient bits * input| ≤
      ∑ j ∈ Finset.range bits.length, |error j| := by
  rw [evaluate_error_superposition]
  simpa using evaluate_zero_input_bound bits error

/-- Appending the sign gate cannot amplify the inherited absolute error.
Its own residual is included separately. -/
theorem signed_output_error (sign product target gateError : ℚ)
    (hsign : |sign| ≤ 1) :
    |(sign * product + gateError) - sign * target| ≤
      |product - target| + |gateError| := by
  calc
    |(sign * product + gateError) - sign * target| =
        |sign * (product - target) + gateError| := by congr 1; ring
    _ ≤ |sign * (product - target)| + |gateError| := abs_add_le _ _
    _ ≤ |product - target| + |gateError| := by
      rw [abs_mul]
      exact add_le_add (by nlinarith [abs_nonneg (product - target)]) (le_refl _)

end Maxwell.Logical.Horner
