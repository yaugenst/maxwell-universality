import Maxwell.Continuum.ProfileEncoded

/-! Degree and coefficient-magnitude bounds for the finite endpoint-corrected data. -/

namespace Maxwell.Continuum.Profile

open Polynomial

theorem basisPolynomial_natDegree (j : ℕ) : (basisPolynomial j).natDegree=j := by
  have hl : (C (2 : ℝ)*X-1 : Polynomial ℝ).natDegree=1 := by
    rw [← C_1, natDegree_sub_C, natDegree_C_mul_X _ (by norm_num)]
  rw [basisPolynomial, natDegree_comp, Chebyshev.natDegree_T, Int.natAbs_natCast, hl, mul_one]

theorem finiteProfilePolynomial_natDegree (D : ℕ) (c : ℕ → ℝ) :
    (finiteProfilePolynomial D c).natDegree ≤ D := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_C_mul_le _ _).trans
    ((basisPolynomial_natDegree j).le.trans (Finset.mem_range.mp hj).le)

theorem matchedCoefficient_bound {P : ℕ} (D : ℕ) (c : ℕ → Dyadic P) {B : ℚ}
    (hB : 0 ≤ B) (hc : ∀ j < D, |(c j).value| ≤ B) (j : ℕ) (hj : j<D) :
    |(matchedCoefficient D c j).value| ≤ 4*B*((D : ℚ)+1)^3 := by
  have hv : |∑ k ∈ Finset.range D, (c k).value| ≤ (D : ℚ)*B := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _k ∈ Finset.range D, B := Finset.sum_le_sum (fun k hk => hc k (Finset.mem_range.mp hk))
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hs : |∑ k ∈ Finset.range D, (c k).value*(k : ℚ)^2| ≤ (D : ℚ)^3*B := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _k ∈ Finset.range D, B*(D : ℚ)^2 := by
        apply Finset.sum_le_sum
        intro k hk
        have hkD : (k : ℚ) ≤ D := by exact_mod_cast (Finset.mem_range.mp hk).le
        rw [abs_mul, abs_of_nonneg (sq_nonneg (k : ℚ))]
        apply mul_le_mul (hc k (Finset.mem_range.mp hk)) _ (sq_nonneg _) hB
        gcongr
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  rw [matchedCoefficient_value]
  have h1 : |if j=0 then -(∑ k ∈ Finset.range D, (c k).value)+
      ∑ k ∈ Finset.range D, (c k).value*(k : ℚ)^2 else 0| ≤ (D : ℚ)*B+(D : ℚ)^3*B := by
    split_ifs
    · exact (abs_add_le _ _).trans (add_le_add (by simpa only [abs_neg] using hv) hs)
    · simp only [abs_zero]
      positivity
  have h2 : |if j=1 then -(∑ k ∈ Finset.range D, (c k).value*(k : ℚ)^2) else 0| ≤
      (D : ℚ)^3*B := by
    split_ifs
    · simpa only [abs_neg] using hs
    · simp only [abs_zero]
      positivity
  have ht := (abs_add_le ((c j).value+(if j=0 then -(∑ k ∈ Finset.range D, (c k).value)+
      ∑ k ∈ Finset.range D, (c k).value*(k : ℚ)^2 else 0))
      (if j=1 then -(∑ k ∈ Finset.range D, (c k).value*(k : ℚ)^2) else 0)).trans
    (add_le_add (abs_add_le _ _) le_rfl)
  have hD0 : 0 ≤ (D : ℚ) := Nat.cast_nonneg _
  have hD1 : 1 ≤ ((D : ℚ)+1)^3 := one_le_pow₀ (by linarith)
  have hDp : (D : ℚ) ≤ ((D : ℚ)+1)^3 :=
    (by linarith : (D : ℚ) ≤ (D : ℚ)+1).trans (le_self_pow₀ (by linarith) (by decide : (3 : ℕ) ≠ 0))
  have hD3 : (D : ℚ)^3 ≤ ((D : ℚ)+1)^3 := by gcongr; linarith
  nlinarith only [ht, hc j hj, h1, h2, mul_le_mul_of_nonneg_right hD1 hB,
    mul_le_mul_of_nonneg_right hDp hB, mul_le_mul_of_nonneg_right hD3 hB]

theorem encodedCoefficient_bound (N j : ℕ) (hj : j<profileDegree N) :
    |(encodedCoefficient N j).value| ≤ 256*((profileDegree N : ℚ)+1)^3 := by
  have h := matchedCoefficient_bound (profileDegree N) (roundedCoefficient N)
    (by norm_num : (0 : ℚ) ≤ 57) (fun k hk => roundedCoefficient_bound N k hk.le) j hj
  change |(encodedCoefficient N j).value| ≤ 4*57*((profileDegree N : ℚ)+1)^3 at h
  exact h.trans (by nlinarith only [show 0 ≤ ((profileDegree N : ℚ)+1)^3 by positivity])

theorem encodedProfile_degree (N : ℕ) :
    (finiteProfilePolynomial (profileDegree N) (fun j => ((encodedCoefficient N j).value : ℝ))).natDegree ≤
      profileDegree N := finiteProfilePolynomial_natDegree _ _

#print axioms encodedCoefficient_bound
#print axioms encodedProfile_degree

end Maxwell.Continuum.Profile
