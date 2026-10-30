import Maxwell.Continuum.CalibrationSandwichEstimate

/-! Operator error for the literal two-well Fourier application. -/

namespace Maxwell.Continuum.Calibration

variable {A : Type*} [NormedRing A]

private theorem norm_product_four (a b c d : A) :
    ‖a*b*c*d‖ ≤ ‖a‖*‖b‖*‖c‖*‖d‖ := by
  apply (norm_mul_le _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (norm_mul_le _ _).trans
  exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)

theorem translated_sandwich_difference {L ε : ℝ} (Q Qb R Rb U Ub : A)
    (hQ : ‖Q‖ ≤ 1) (hQb : ‖Qb‖ ≤ 2) (hQe : ‖Q-Qb‖ ≤ ε)
    (hR : ‖R‖ ≤ 4*L^2) (hRb : ‖Rb‖ ≤ 5*L^2) (hRe : ‖R-Rb‖ ≤ ε)
    (hU : ‖U‖ ≤ 1) (hUb : ‖Ub‖ ≤ 2) (hUe : ‖U-Ub‖ ≤ ε) :
    ‖Q*R*U*Q-Qb*Rb*Ub*Qb‖ ≤ (34*L^2+2)*ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hQe
  have he : Q*R*U*Q-Qb*Rb*Ub*Qb = (Q-Qb)*R*U*Q+
      Qb*(R-Rb)*U*Q+Qb*Rb*(U-Ub)*Q+Qb*Rb*Ub*(Q-Qb) := by
    simp only [sub_mul,mul_sub,mul_assoc]
    abel
  rw [he]
  have h1 : ‖(Q-Qb)*R*U*Q‖ ≤ 4*L^2*ε := by
    apply (norm_product_four _ _ _ _).trans
    calc
      _ ≤ ε*(4*L^2)*1*1 := by gcongr
      _ = _ := by ring
  have h2 : ‖Qb*(R-Rb)*U*Q‖ ≤ 2*ε := by
    apply (norm_product_four _ _ _ _).trans
    calc
      _ ≤ 2*ε*1*1 := by gcongr
      _ = _ := by ring
  have h3 : ‖Qb*Rb*(U-Ub)*Q‖ ≤ 10*L^2*ε := by
    apply (norm_product_four _ _ _ _).trans
    calc
      _ ≤ 2*(5*L^2)*ε*1 := by gcongr
      _ = _ := by ring
  have h4 : ‖Qb*Rb*Ub*(Q-Qb)‖ ≤ 20*L^2*ε := by
    apply (norm_product_four _ _ _ _).trans
    calc
      _ ≤ 2*(5*L^2)*2*ε := by gcongr
      _ = _ := by ring
  have h := (norm_add_le ((Q-Qb)*R*U*Q+Qb*(R-Rb)*U*Q+Qb*Rb*(U-Ub)*Q)
    (Qb*Rb*Ub*(Q-Qb))).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  have h' := norm_add_le ((Q-Qb)*R*U*Q) (Qb*(R-Rb)*U*Q)
  linarith

#print axioms translated_sandwich_difference

end Maxwell.Continuum.Calibration
