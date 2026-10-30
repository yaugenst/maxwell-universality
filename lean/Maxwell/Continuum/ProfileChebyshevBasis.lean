import Maxwell.Continuum.ProfileAngularGevrey
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-! The actual shifted Chebyshev basis, including derivative and endpoint bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Profile

open Polynomial Polynomial.Chebyshev Set

def basisPolynomial (j : ℕ) : Polynomial ℝ := (T ℝ (j : ℤ)).comp (C 2*X-1)
def basis (j : ℕ) (t : ℝ) : ℝ := (basisPolynomial j).eval t
def basisDerivative (j : ℕ) (t : ℝ) : ℝ := 2*(T ℝ (j : ℤ)).derivative.eval (2*t-1)

theorem basis_eq (j : ℕ) (t : ℝ) : basis j t = (T ℝ (j : ℤ)).eval (2*t-1) := by
  simp only [basis, basisPolynomial, eval_comp, eval_sub, eval_mul, eval_C, eval_X, eval_one]

theorem basis_hasDerivAt (j : ℕ) (t : ℝ) : HasDerivAt (basis j) (basisDerivative j t) t := by
  have hi : HasDerivAt (fun t : ℝ => 2*t-1) 2 t := by
    convert ((hasDerivAt_id t).const_mul 2).sub_const 1 using 1 <;> norm_num
  have h := ((T ℝ (j : ℤ)).hasDerivAt (2*t-1)).comp t hi
  convert h using 1
  · funext s
    exact basis_eq j s
  · unfold basisDerivative
    ring

theorem basis_bound (j : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : |basis j t| ≤ 1 := by
  rw [basis_eq]
  exact abs_eval_T_real_le_one (j : ℤ) (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)

theorem basisDerivative_bound (j : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |basisDerivative j t| ≤ 2*(j : ℝ)^2 := by
  have hx : |2*t-1| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h := abs_iterate_derivative_T_real_le (j : ℤ) 1 hx
  simp only [Function.iterate_one, derivative_T_eval_one, Int.cast_natCast] at h
  unfold basisDerivative
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ)<2)]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

theorem basis_endpoint (j : ℕ) : basis j 1 = 1 := by
  rw [basis_eq]
  norm_num

theorem basisDerivative_endpoint (j : ℕ) : basisDerivative j 1 = 2*(j : ℝ)^2 := by
  unfold basisDerivative
  norm_num [derivative_T_eval_one]

theorem basis_cosine (j : ℕ) (φ : ℝ) : basis j ((1+Real.cos φ)/2) = Real.cos ((j : ℝ)*φ) := by
  rw [basis_eq, show 2*((1+Real.cos φ)/2)-1=Real.cos φ by ring, T_real_cos]
  rfl

theorem basis_neg_index (j : ℕ) (φ : ℝ) : Real.cos ((-(j : ℤ) : ℤ)*φ) = Real.cos ((j : ℝ)*φ) := by
  simp only [Int.cast_neg, Int.cast_natCast, neg_mul, Real.cos_neg]

#print axioms basis_hasDerivAt
#print axioms basisDerivative_bound

end Maxwell.Continuum.Profile
