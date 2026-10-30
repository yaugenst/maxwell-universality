import Maxwell.Continuum.ProfileChebyshevSeries

/-! Actual finite Chebyshev polynomials and uniform coefficient perturbation bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Profile

open Set Polynomial

def finiteProfile (D : ℕ) (c : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range D, c j*basis j t

def finiteProfileDerivative (D : ℕ) (c : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range D, c j*basisDerivative j t

def finiteProfilePolynomial (D : ℕ) (c : ℕ → ℝ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range D, C (c j)*basisPolynomial j

theorem finiteProfilePolynomial_eval (D : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    (finiteProfilePolynomial D c).eval t=finiteProfile D c t := by
  simp only [finiteProfilePolynomial, finiteProfile, eval_finsetSum, eval_mul, eval_C, basis]

theorem finiteProfile_contDiff (D : ℕ) (c : ℕ → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (finiteProfile D c) := by
  have he : (finiteProfilePolynomial D c).eval=finiteProfile D c :=
    funext (finiteProfilePolynomial_eval D c)
  rw [← he]
  have hp (p : Polynomial ℝ) : ContDiff ℝ (⊤ : ℕ∞) p.eval := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [eval_add] using hp.add hq
    | monomial n a => simpa only [eval_monomial] using
        (contDiff_const.mul (contDiff_id.pow n) : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => a*x^n))
  exact hp _

theorem finiteProfile_hasDerivAt (D : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    HasDerivAt (finiteProfile D c) (finiteProfileDerivative D c t) t :=
  HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.range D) => (basis_hasDerivAt j t).const_mul (c j))

theorem finiteProfile_coefficient_error (D : ℕ) (c d : ℕ → ℝ) {η : ℝ}
    (hη : 0 ≤ η) (hc : ∀ j < D, |c j-d j| ≤ η) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |finiteProfile D c t-finiteProfile D d t| ≤ (D : ℝ)*η := by
  unfold finiteProfile
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range D, |c j*basis j t-d j*basis j t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range D, η := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← sub_mul, abs_mul]
      exact (mul_le_mul (hc j (Finset.mem_range.mp hj)) (basis_bound j ht)
        (abs_nonneg _) hη).trans_eq (mul_one η)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem finiteProfile_derivative_coefficient_error (D : ℕ) (c d : ℕ → ℝ) {η : ℝ}
    (hη : 0 ≤ η) (hc : ∀ j < D, |c j-d j| ≤ η) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |finiteProfileDerivative D c t-finiteProfileDerivative D d t| ≤ 2*(D : ℝ)^3*η := by
  unfold finiteProfileDerivative
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range D, |c j*basisDerivative j t-d j*basisDerivative j t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range D, η*(2*(D : ℝ)^2) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjD : (j : ℝ) ≤ D := by exact_mod_cast (Finset.mem_range.mp hj).le
      have hb := (basisDerivative_bound j ht).trans
        (show 2*(j : ℝ)^2 ≤ 2*(D : ℝ)^2 by gcongr)
      rw [← sub_mul, abs_mul]
      exact mul_le_mul (hc j (Finset.mem_range.mp hj)) hb (abs_nonneg _) hη
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem finiteProfile_endpoint (D : ℕ) (c : ℕ → ℝ) :
    finiteProfile D c 1=∑ j ∈ Finset.range D, c j := by
  simp only [finiteProfile, basis_endpoint, mul_one]

theorem finiteProfileDerivative_endpoint (D : ℕ) (c : ℕ → ℝ) :
    finiteProfileDerivative D c 1=2*∑ j ∈ Finset.range D, c j*(j : ℝ)^2 := by
  simp only [finiteProfileDerivative, basisDerivative_endpoint, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

#print axioms finiteProfile_derivative_coefficient_error

end Maxwell.Continuum.Profile
