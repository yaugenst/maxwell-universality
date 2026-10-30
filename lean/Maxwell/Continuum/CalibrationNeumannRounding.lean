import Maxwell.Continuum.CalibrationNeumann

/-! Uniform finite-Neumann arithmetic stability. The error is bounded
independently of the number of terms; the contraction damps the errors
instead of accumulating a factor proportional to the truncation length. -/

noncomputable section

namespace Maxwell.Continuum.Calibration.Neumann

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem partialSeries_recurrence (T : H →L[ℂ] H) (K : ℕ) :
    partialSeries T (K+1) = 1+partialSeries T K*T := by
  simp only [partialSeries, Finset.sum_range_succ', pow_zero, pow_succ, Finset.sum_mul]
  exact add_comm _ _

theorem inverseApprox_recurrence (R B : H →L[ℂ] H) (K : ℕ) :
    inverseApprox R B (K+1) = R-inverseApprox R B K*B*R := by
  rw [inverseApprox, partialSeries_recurrence, inverseApprox]
  noncomm_ring

theorem inverseApprox_left_recurrence (R B : H →L[ℂ] H) (K : ℕ) :
    inverseApprox R B (K+1) = R-R*B*inverseApprox R B K := by
  have hp : partialSeries (-(B*R)) (K+1) = 1+(-(B*R))*partialSeries (-(B*R)) K := by
    simp only [partialSeries, Finset.sum_range_succ', pow_zero, pow_succ', Finset.mul_sum]
    exact add_comm _ _
  rw [inverseApprox, hp, inverseApprox]
  noncomm_ring

theorem inverseApprox_norm (R B : H →L[ℂ] H) (hR : ‖R‖ ≤ 1) (hB : ‖B‖ ≤ 1/2) (K : ℕ) :
    ‖inverseApprox R B K‖ ≤ 2 := by
  induction K with
  | zero => simp [inverseApprox, partialSeries]
  | succ K ih =>
    rw [inverseApprox_recurrence]
    calc
      _ ≤ ‖R‖+‖inverseApprox R B K*B*R‖ := norm_sub_le _ _
      _ ≤ 1+(2*(1/2))*1 := add_le_add hR ((norm_mul_le _ _).trans
        (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul ih hB (norm_nonneg _) (by norm_num)))
          hR (norm_nonneg _) (by norm_num)))
      _ = 2 := by norm_num

theorem inverseApprox_rounding (R S B : H →L[ℂ] H)
    (hR : ‖R‖ ≤ 1) (hS : ‖S‖ ≤ 1) (hB : ‖B‖ ≤ 1/2) (K : ℕ) :
    ‖inverseApprox R B K-inverseApprox S B K‖ ≤ 4*‖R-S‖ := by
  induction K with
  | zero => simp [inverseApprox, partialSeries]
  | succ K ih =>
    rw [inverseApprox_recurrence, inverseApprox_recurrence]
    have hid : R-inverseApprox R B K*B*R-(S-inverseApprox S B K*B*S) =
        (R-S)-(inverseApprox R B K-inverseApprox S B K)*B*R-
          inverseApprox S B K*B*(R-S) := by noncomm_ring
    rw [hid]
    calc
      _ ≤ ‖R-S‖+‖(inverseApprox R B K-inverseApprox S B K)*B*R‖+
          ‖inverseApprox S B K*B*(R-S)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ ‖R-S‖+((4*‖R-S‖)*(1/2))*1+(2*(1/2))*‖R-S‖ := by
        apply add_le_add
        · apply add_le_add le_rfl
          exact (norm_mul_le _ _).trans (mul_le_mul
            ((norm_mul_le _ _).trans (mul_le_mul ih hB (norm_nonneg _) (by positivity)))
            hR (norm_nonneg _) (by positivity))
        · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            ((norm_mul_le _ _).trans (mul_le_mul (inverseApprox_norm S B hS hB K)
              hB (norm_nonneg _) (by norm_num))) (norm_nonneg _))
      _ = _ := by ring

#print axioms inverseApprox_rounding

end Maxwell.Continuum.Calibration.Neumann
