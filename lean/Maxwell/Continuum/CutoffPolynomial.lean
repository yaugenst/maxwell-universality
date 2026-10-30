import Maxwell.Continuum.ProfileCoefficientBounds
import Maxwell.Continuum.WellCutoffBase

/-! A literal rational polynomial approximation of the cutoff's compact bump. -/

namespace Maxwell.Continuum.Calibration

open Polynomial Profile

noncomputable def cutoffPolynomial (N : ℕ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (profileDegree N),
    C ((encodedCoefficient N j).value)*(Chebyshev.T ℚ (j : ℤ)).comp (C 4*X^2)

theorem cutoffPolynomial_eval (N : ℕ) (s : ℝ) :
    (cutoffPolynomial N).eval₂ (Rat.castHom ℝ) s=encodedProfile N ((1+4*s^2)/2) := by
  unfold cutoffPolynomial encodedProfile finiteProfile
  rw [eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [eval₂_mul,eval₂_C,eval₂_comp,eval₂_pow,eval₂_X,basis_eq,
    show 2*((1+4*s^2)/2)-1=4*s^2 by ring]
  rw [eval₂_eq_eval_map, Chebyshev.map_T]
  rfl

theorem cutoffPolynomial_error (N : ℕ) {s : ℝ} (hs : |s|≤1/2) :
    |Well.cutoffBase s-(cutoffPolynomial N).eval₂ (Rat.castHom ℝ) s|≤(1/2 : ℝ)^(N+24) := by
  have hsq : s^2≤1/4 := by
    have h := mul_self_le_mul_self (abs_nonneg s) hs
    nlinarith only [h,sq_abs s]
  have he := (encodedProfile_error N
    (show (1+4*s^2)/2 ∈ Set.Icc (0 : ℝ) 1 from ⟨by positivity, by linarith⟩)).1
  rw [cutoffPolynomial_eval]
  convert he using 1
  unfold Well.cutoffBase radial
  congr 3
  ring

theorem cutoffPolynomial_degree (N : ℕ) : (cutoffPolynomial N).natDegree≤2*profileDegree N := by
  unfold cutoffPolynomial
  apply natDegree_sum_le_of_forall_le
  intro j hj
  apply (natDegree_C_mul_le _ _).trans
  rw [natDegree_comp, Chebyshev.natDegree_T, Int.natAbs_natCast]
  have hd : (C (4 : ℚ)*X^2 : Polynomial ℚ).natDegree=2 := by
    rw [natDegree_C_mul (by norm_num : (4 : ℚ)≠0)]
    simp
  rw [hd]
  have hjD := (Finset.mem_range.mp hj).le
  omega

#print axioms cutoffPolynomial_error
#print axioms cutoffPolynomial_degree

end Maxwell.Continuum.Calibration
