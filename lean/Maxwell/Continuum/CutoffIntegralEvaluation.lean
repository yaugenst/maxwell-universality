import Maxwell.Continuum.CutoffPolynomial
import Maxwell.Continuum.RationalChebyshevTable
import Maxwell.Continuum.RationalPolynomialIntegral

/-! Executable exact integration of the finite cutoff polynomial. -/

namespace Maxwell.Continuum.Calibration

open Polynomial Profile MeasureTheory

def chebyshevSquareIntegral (j : ℕ) (a b : ℚ) : ℚ :=
  let c := chebyshevRow (j+1) j
  ∑ k : Fin (j+1), (c.get k : ℚ)*(4 : ℚ)^k.val*
    (b^(2*k.val+1)-a^(2*k.val+1))/(2*(k.val : ℚ)+1)

theorem chebyshevSquareIntegral_eq (j : ℕ) (a b : ℚ) :
    (chebyshevSquareIntegral j a b : ℝ)=
      ∫ s in (a : ℝ)..(b : ℝ), (Chebyshev.T ℚ (j : ℤ)).eval₂ (Rat.castHom ℝ) (4*s^2) := by
  have hd : (Chebyshev.T ℚ (j : ℤ)).natDegree<j+1 := by
    rw [Chebyshev.natDegree_T,Int.natAbs_natCast]
    omega
  simp_rw [Polynomial.eval₂_eq_sum_range' (Rat.castHom ℝ) hd]
  have he (k : ℕ) (s : ℝ) : (Rat.castHom ℝ) ((Chebyshev.T ℚ (j : ℤ)).coeff k)*(4*s^2)^k=
      ((Chebyshev.T ℚ (j : ℤ)).coeff k : ℝ)*(4 : ℝ)^k*s^(2*k) := by
    change ((Chebyshev.T ℚ (j : ℤ)).coeff k : ℝ)*(4*s^2)^k=_
    rw [mul_pow,← pow_mul]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum]
  · unfold chebyshevSquareIntegral
    dsimp only
    push_cast
    have hcr (k : Fin (j+1)) : ((chebyshevRow (j+1) j).get k : ℝ)=
        ((Chebyshev.T ℚ (j : ℤ)).coeff k : ℝ) := by
      exact_mod_cast chebyshevRow_coeff_rat (j+1) j k
    simp_rw [hcr]
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
      ((Chebyshev.T ℚ (j : ℤ)).coeff k : ℝ)*(4 : ℝ)^k*
        ((b : ℝ)^(2*k+1)-(a : ℝ)^(2*k+1))/(2*(k : ℝ)+1)) (j+1)]
    apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const_mul,integral_pow]
    push_cast
    ring
  · intro k _
    exact (continuous_const.mul (continuous_id.pow (2*k))).intervalIntegrable _ _

def cutoffIntegralApprox (N : ℕ) (a b : ℚ) : ℚ :=
  ∑ j ∈ Finset.range (profileDegree N), (encodedCoefficient N j).value*chebyshevSquareIntegral j a b

theorem cutoffIntegralApprox_eq (N : ℕ) (a b : ℚ) :
    (cutoffIntegralApprox N a b : ℝ)=
      ∫ s in (a : ℝ)..(b : ℝ), (cutoffPolynomial N).eval₂ (Rat.castHom ℝ) s := by
  simp only [cutoffPolynomial,eval₂_finsetSum,eval₂_mul,eval₂_C,eval₂_comp,eval₂_pow,eval₂_X]
  change (cutoffIntegralApprox N a b : ℝ)=
    ∫ s in (a : ℝ)..(b : ℝ), ∑ j ∈ Finset.range (profileDegree N),
      ((encodedCoefficient N j).value : ℝ)*(Chebyshev.T ℚ (j : ℤ)).eval₂ (Rat.castHom ℝ) (4*s^2)
  rw [intervalIntegral.integral_finsetSum]
  · unfold cutoffIntegralApprox
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_const_mul,chebyshevSquareIntegral_eq]
  · intro j _
    apply Continuous.intervalIntegrable
    exact continuous_const.mul ((Chebyshev.T ℚ (j : ℤ)).continuous_eval₂ (Rat.castHom ℝ) |>.comp
      (continuous_const.mul (continuous_id.pow 2)))

theorem cutoffIntegralApprox_error (N : ℕ) {a b : ℚ}
    (ha : -1/2≤a) (hb : b≤1/2) (hab : a≤b) :
    |(∫ s in (a : ℝ)..(b : ℝ), Well.cutoffBase s)-(cutoffIntegralApprox N a b : ℝ)|≤
      (1/2 : ℝ)^(N+24) := by
  rw [cutoffIntegralApprox_eq,← polynomialIntegral_eq]
  have he := polynomialIntegral_error (p := cutoffPolynomial N) Well.cutoffBase_contDiff.continuous hab
    (by
      intro s hs
      apply cutoffPolynomial_error N
      apply abs_le.mpr
      have har : (-1/2 : ℝ)≤(a : ℝ) := by exact_mod_cast ha
      have hbr : (b : ℝ)≤1/2 := by
        simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
          (Rat.cast_le.mpr hb : (b : ℝ)≤((1/2 : ℚ) : ℝ))
      constructor <;> linarith [hs.1,hs.2])
  apply he.trans
  have hlen : ((b-a : ℚ) : ℝ)≤1 := by exact_mod_cast (show b-a≤1 by linarith)
  exact (mul_le_mul_of_nonneg_right hlen (by positivity)).trans_eq (one_mul _)

#print axioms chebyshevSquareIntegral_eq
#print axioms cutoffIntegralApprox_error

end Maxwell.Continuum.Calibration
