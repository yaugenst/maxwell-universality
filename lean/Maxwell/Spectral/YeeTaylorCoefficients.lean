import Maxwell.Spectral.YeeTaylor

/-! Exact low-order centered-gauge coefficients in the sparse arithmetic
convention: first differences use shifted plus anchor, second differences
use shifted minus anchor. -/
namespace Maxwell.Spectral.YeeTaylorCoefficients
noncomputable section
open Matrix
open Maxwell.Spectral.PeriodicYee Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.YeeTaylor
open scoped Classical Matrix.Norms.L2Operator

/-- The real first-derivative stencil before the common factor `iθ`. -/
def firstCurl (k q : Momentum) : Matrix Electric Electric ℂ :=
  curlBlock fun j => (q j : ℂ) • (PrimitiveYee.shift k j + 1)

/-- The second-derivative stencil before the common factor `−θ²/2`. -/
def secondCurl (k q : Momentum) : Matrix Electric Electric ℂ :=
  curlBlock fun j => ((q j : ℂ)^2) • PrimitiveYee.difference k j

theorem differenceCoefficient_one (k q : Momentum) (j : Direction) :
    differenceCoefficient k q 1 j =
      (Complex.I * (theta * q j : ℝ)) • (PrimitiveYee.shift k j + 1) := by
  simp [differenceCoefficient, smul_add, neg_smul, sub_neg_eq_add]

theorem differenceCoefficient_two (k q : Momentum) (j : Direction) :
    differenceCoefficient k q 2 j =
      (-((theta * q j : ℝ) : ℂ)^2 / 2) • PrimitiveYee.difference k j := by
  have hp : (Complex.I * ((theta * q j : ℝ) : ℂ))^2 = -((theta * q j : ℝ) : ℂ)^2 := by
    rw [mul_pow, Complex.I_sq, neg_one_mul]
  have hn : (-Complex.I * ((theta * q j : ℝ) : ℂ))^2 = -((theta * q j : ℝ) : ℂ)^2 := by
    rw [mul_pow, neg_sq, Complex.I_sq, neg_one_mul]
  rw [differenceCoefficient, hp, hn]
  norm_num [difference_eq_shift_sub_one, smul_sub]

/-- Exact first Taylor coefficient of the actual curl. -/
theorem curlCoefficient_one (k q : Momentum) :
    curlCoefficient k q 1 = (Complex.I * (theta : ℂ)) • firstCurl k q := by
  ext ⟨i,p⟩ ⟨j,r⟩
  fin_cases i <;> fin_cases j <;>
    simp [curlCoefficient, firstCurl, curlBlock, differenceCoefficient_one,
      smul_add, mul_assoc, mul_add]

/-- Exact second Taylor coefficient of the actual curl. -/
theorem curlCoefficient_two (k q : Momentum) :
    curlCoefficient k q 2 = (-((theta : ℂ)^2) / 2) • secondCurl k q := by
  ext ⟨i,p⟩ ⟨j,r⟩
  fin_cases i <;> fin_cases j <;>
    simp [curlCoefficient, secondCurl, curlBlock, differenceCoefficient_two,
      mul_pow]
  all_goals ring

/-- Exact first coefficient of the actual Maxwell matrix. -/
theorem fiberCoefficient_one (material : Cell20 → ℝ) (k q : Momentum) :
    fiberCoefficient material k q 1 =
      (PrimitiveYee.curl k).conjTranspose * curlCoefficient k q 1 +
        (curlCoefficient k q 1).conjTranspose * PrimitiveYee.curl k := by
  simp [fiberCoefficient, YeeTaylorConvolution.coefficient, Finset.Nat.sum_antidiagonal_succ,
    curlCoefficient_zero, Matrix.star_eq_conjTranspose]

/-- Exact quadratic coefficient, including both endpoint second derivatives
and the product of first derivatives. -/
theorem fiberCoefficient_two (material : Cell20 → ℝ) (k q : Momentum) :
    fiberCoefficient material k q 2 =
      (PrimitiveYee.curl k).conjTranspose * curlCoefficient k q 2 +
        (curlCoefficient k q 1).conjTranspose * curlCoefficient k q 1 +
        (curlCoefficient k q 2).conjTranspose * PrimitiveYee.curl k := by
  simp [fiberCoefficient, YeeTaylorConvolution.coefficient, Finset.Nat.sum_antidiagonal_succ,
    curlCoefficient_zero, Matrix.star_eq_conjTranspose, add_assoc, add_comm, add_left_comm]

/-- The rational-arithmetic first derivative convention used by the certificate
is obtained after extracting its single physical factor `iθ`. -/
theorem fiberCoefficient_one_factored (material : Cell20 → ℝ) (k q : Momentum) :
    fiberCoefficient material k q 1 = (Complex.I * (theta : ℂ)) •
      ((PrimitiveYee.curl k).conjTranspose * firstCurl k q -
        (firstCurl k q).conjTranspose * PrimitiveYee.curl k) := by
  rw [fiberCoefficient_one, curlCoefficient_one, Matrix.conjTranspose_smul]
  have hs : star (Complex.I * (theta : ℂ)) = -(Complex.I * (theta : ℂ)) := by simp
  rw [hs]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  module

/-- The rational-arithmetic quadratic derivative convention used by the
certificate, with the physical factor `θ²` extracted exactly. -/
theorem fiberCoefficient_two_factored (material : Cell20 → ℝ) (k q : Momentum) :
    fiberCoefficient material k q 2 = ((theta : ℂ)^2) •
      ((firstCurl k q).conjTranspose * firstCurl k q - (1 / 2 : ℂ) •
        ((PrimitiveYee.curl k).conjTranspose * secondCurl k q +
          (secondCurl k q).conjTranspose * PrimitiveYee.curl k)) := by
  rw [fiberCoefficient_two, curlCoefficient_one, curlCoefficient_two]
  simp only [Matrix.conjTranspose_smul]
  have hfirst : star (Complex.I * (theta : ℂ)) = -(Complex.I * (theta : ℂ)) := by simp
  have hsecond : star (-((theta : ℂ)^2) / 2) = -((theta : ℂ)^2) / 2 := by simp
  have hprod : (Complex.I * (theta : ℂ)) * (-(Complex.I * (theta : ℂ))) = (theta : ℂ)^2 := by
    calc
      _ = -(Complex.I^2 * (theta : ℂ)^2) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [hfirst, hsecond]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [hprod]
  module

end
end Maxwell.Spectral.YeeTaylorCoefficients
