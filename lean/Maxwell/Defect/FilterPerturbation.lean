import Maxwell.Defect.PowerRefinement

/-! An explicit rational input-accuracy budget for the fixed mode filter. -/
namespace Maxwell.Defect

theorem norm_sq_difference_le {A : Type*} [NormedRing A] (a b : A) :
    ‖a ^ 2 - b ^ 2‖ ≤ (‖a‖ + ‖b‖) * ‖a - b‖ := by
  have hid : a ^ 2 - b ^ 2 = a * (a - b) + (a - b) * b := by
    rw [pow_two, pow_two, mul_sub, sub_mul]
    abel
  calc
    _ ≤ ‖a‖ * ‖a - b‖ + ‖a - b‖ * ‖b‖ := by
      rw [hid]
      exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ = _ := by ring

section Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem modeFilter_difference (S T : E →L[ℝ] E) (target scale M : ℝ)
    (hM : ‖S‖ + |target| ≤ M) (hST : ‖S - T‖ ≤ 1) :
    ‖modeFilter S target scale - modeFilter T target scale‖ ≤
      |scale| * (2 * M + 1) * ‖S - T‖ := by
  have hSn : ‖S - target • (1 : E →L[ℝ] E)‖ ≤ M := by
    apply (norm_sub_le _ _).trans
    have ht : ‖target • (1 : E →L[ℝ] E)‖ ≤ |target| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E))
        (abs_nonneg _)).trans_eq (mul_one _)
    exact (add_le_add (le_refl ‖S‖) ht).trans hM
  have hTn : ‖T - target • (1 : E →L[ℝ] E)‖ ≤ M + 1 := by
    calc
      _ ≤ ‖T - S‖ + ‖S - target • (1 : E →L[ℝ] E)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 1 + M := add_le_add (by simpa only [norm_sub_rev] using hST) hSn
      _ = _ := by ring
  have hid : modeFilter S target scale - modeFilter T target scale =
      -(scale • ((S - target • 1) ^ 2 - (T - target • 1) ^ 2)) := by
    simp only [modeFilter, smul_sub]
    abel
  rw [hid, norm_neg, norm_smul, Real.norm_eq_abs]
  have hdiff : (S - target • 1) - (T - target • 1) = S - T := by abel
  have hs := norm_sq_difference_le (S - target • (1 : E →L[ℝ] E)) (T - target • 1)
  rw [hdiff] at hs
  calc
    _ ≤ |scale| * ((‖S - target • 1‖ + ‖T - target • 1‖) * ‖S - T‖) :=
      mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ ≤ |scale| * ((M + (M + 1)) * ‖S - T‖) := by gcongr
    _ = _ := by ring

end Operator
end Maxwell.Defect
