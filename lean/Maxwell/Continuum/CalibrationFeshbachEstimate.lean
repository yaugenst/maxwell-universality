import Maxwell.Continuum.CalibrationInverseError

/-! Operator error propagation through the actual Feshbach inverse
formula. These estimates will be applied to finite Neumann polynomials
and the inverse of the finite Schur approximation. -/

namespace Maxwell.Continuum.Calibration

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem triple_product_difference (L L' J J' X X' : H →L[ℂ] H) :
    ‖L*J*X-L'*J'*X'‖ ≤
      ‖L-L'‖*‖J‖*‖X‖+‖L'‖*‖J-J'‖*‖X‖+‖L'‖*‖J'‖*‖X-X'‖ := by
  have hid : L*J*X-L'*J'*X' =
      (L-L')*J*X+L'*(J-J')*X+L'*J'*(X-X') := by noncomm_ring
  rw [hid]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_add_le _ _).trans
    exact add_le_add
      ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
      ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
  · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

theorem feshbach_inverse_difference (C C' L L' J J' X X' : H →L[ℂ] H)
    {M δ : ℝ} (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (hC : ‖C-C'‖ ≤ δ) (hL : ‖L-L'‖ ≤ δ) (hL' : ‖L'‖ ≤ 3)
    (hJ : ‖J‖ ≤ M) (hJ' : ‖J'‖ ≤ 2*M) (hJJ' : ‖J-J'‖ ≤ 2*M^2*δ)
    (hX : ‖X‖ ≤ 2) (hXX' : ‖X-X'‖ ≤ δ) :
    ‖(C+L*J*X)-(C'+L'*J'*X')‖ ≤ 32*M^2*δ := by
  have ht := triple_product_difference L L' J J' X X'
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hb : ‖L*J*X-L'*J'*X'‖ ≤ δ*M*2+3*(2*M^2*δ)*2+3*(2*M)*δ := by
    apply ht.trans
    gcongr
  have hid : (C+L*J*X)-(C'+L'*J'*X') = (C-C')+(L*J*X-L'*J'*X') := by abel
  rw [hid]
  apply ((norm_add_le _ _).trans (add_le_add hC hb)).trans
  have hm2 : M ≤ M^2 := by nlinarith
  have h12 : 1 ≤ M^2 := hM.trans hm2
  have hmul1 := mul_le_mul_of_nonneg_right h12 hδ
  have hmulM := mul_le_mul_of_nonneg_right hm2 hδ
  nlinarith [mul_nonneg (sq_nonneg M) hδ]

#print axioms feshbach_inverse_difference

end Maxwell.Continuum.Calibration
