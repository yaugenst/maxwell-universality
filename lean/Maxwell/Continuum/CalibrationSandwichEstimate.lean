import Maxwell.Continuum.CalibrationFeshbachEstimate

/-! Error accounting for the three literal factors of a well-sandwich
operator, independent of any Fourier coordinate representation. -/

namespace Maxwell.Continuum.Calibration

theorem sandwich_difference_norm {A : Type*} [NormedRing A]
    (Q Qb R Rb : A) {L ε : ℝ}
    (hQ : ‖Q‖ ≤ 1) (hQb : ‖Qb‖ ≤ 2) (hQe : ‖Q-Qb‖ ≤ ε)
    (hR : ‖R‖ ≤ 4*L^2) (hRb : ‖Rb‖ ≤ 5*L^2) (hRe : ‖R-Rb‖ ≤ ε) :
    ‖Q*R*Q-Qb*Rb*Qb‖ ≤ (14*L^2+2)*ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hQe
  have hid : Q*R*Q-Qb*Rb*Qb = (Q-Qb)*R*Q+Qb*(R-Rb)*Q+Qb*Rb*(Q-Qb) := by
    simp only [sub_mul,mul_sub,mul_assoc]
    abel
  rw [hid]
  have hb := (norm_add_le ((Q-Qb)*R*Q+Qb*(R-Rb)*Q) (Qb*Rb*(Q-Qb))).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  apply hb.trans
  have ha : ‖(Q-Qb)*R*Q‖ ≤ ε*(4*L^2)*1 := by
    calc
      _ ≤ ‖Q-Qb‖*‖R‖*‖Q‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ _ := by gcongr
  have hb' : ‖Qb*(R-Rb)*Q‖ ≤ 2*ε*1 := by
    calc
      _ ≤ ‖Qb‖*‖R-Rb‖*‖Q‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ _ := by gcongr
  have hc : ‖Qb*Rb*(Q-Qb)‖ ≤ 2*(5*L^2)*ε := by
    calc
      _ ≤ ‖Qb‖*‖Rb‖*‖Q-Qb‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ _ := by gcongr
  nlinarith

end Maxwell.Continuum.Calibration
