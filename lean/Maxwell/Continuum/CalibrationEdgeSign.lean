import Maxwell.Continuum.CalibrationEdgeKernel

/-! Robust sign margins for finite approximations of the literal calibration
Schur matrix. These margins justify the executable rational edge search. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration

open FreeFiber
open scoped InnerProductSpace

theorem edge_form_error (A B : centralSpace →L[ℂ] centralSpace)
    {η : ℝ} (h : ‖A-B‖ ≤ η) (u : centralSpace) :
    |(inner ℂ u (A u)).re-(inner ℂ u (B u)).re| ≤ η*‖u‖^2 := by
  have hi : inner ℂ u (A u)-inner ℂ u (B u) = inner ℂ u ((A-B) u) := by
    rw [sub_apply, inner_sub_right]
  calc
    _ = |(inner ℂ u ((A-B) u)).re| := by rw [← hi, Complex.sub_re]
    _ ≤ ‖inner ℂ u ((A-B) u)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖u‖*‖(A-B) u‖ := norm_inner_le_norm _ _
    _ ≤ ‖u‖*(η*‖u‖) :=
      mul_le_mul_of_nonneg_left ((A-B).le_of_opNorm_le h u) (norm_nonneg _)
    _ = _ := by ring

theorem edgeSchur_negative_margin (e : ℝ) (he : |e| ≤ 8)
    (B : centralSpace →L[ℂ] centralSpace) {η : ℝ}
    (herr : ‖B-calibrationFiniteSchur 0 e edgeParameterBound (edgeEnergyBound he)‖ ≤ η)
    (hB : ∀ u : centralSpace, u ≠ 0 → (inner ℂ u (B u)).re < 0) :
    backgroundAmplitude*(edgeScaled-e) ≤ η := by
  have hη : 0 ≤ η := (norm_nonneg
    (B-calibrationFiniteSchur 0 e edgeParameterBound (edgeEnergyBound he))).trans herr
  by_cases hee : e ≤ edgeScaled
  · obtain ⟨w, hw, hAw⟩ := edgeSchur_kernel
    have hdec := (edgeSchur_decrease e edgeScaled he edgeScaled_abs hee w).2
    rw [hAw, inner_zero_right, Complex.zero_re] at hdec
    have herror := (abs_le.mp (edge_form_error B _ herr w)).1
    have hnegative := hB w hw
    have hn : 0 < ‖w‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
    have hbound : (backgroundAmplitude*(edgeScaled-e))*‖w‖^2 ≤ η*‖w‖^2 := by
      linarith only [hdec, herror, hnegative]
    exact (mul_le_mul_iff_left₀ hn).mp hbound
  · exact (mul_nonpos_of_nonneg_of_nonpos backgroundAmplitude_pos.le
      (sub_nonpos.mpr (le_of_not_ge hee))).trans hη

theorem edgeSchur_nonnegative_margin (e : ℝ) (he : |e| ≤ 8)
    (B : centralSpace →L[ℂ] centralSpace) {η : ℝ}
    (herr : ‖B-calibrationFiniteSchur 0 e edgeParameterBound (edgeEnergyBound he)‖ ≤ η)
    (hB : ∃ u : centralSpace, u ≠ 0 ∧ 0 ≤ (inner ℂ u (B u)).re) :
    backgroundAmplitude*(e-edgeScaled) ≤ η := by
  have hη : 0 ≤ η := (norm_nonneg
    (B-calibrationFiniteSchur 0 e edgeParameterBound (edgeEnergyBound he))).trans herr
  by_cases hee : edgeScaled ≤ e
  · obtain ⟨u, hu, hBu⟩ := hB
    have hdec := (edgeSchur_decrease edgeScaled e edgeScaled_abs he hee u).2
    have hedge := edgeSchur_at_edge_nonpositive u
    have herror := (abs_le.mp (edge_form_error B _ herr u)).2
    have hn : 0 < ‖u‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
    have hbound : (backgroundAmplitude*(e-edgeScaled))*‖u‖^2 ≤ η*‖u‖^2 := by
      linarith only [hdec, hedge, herror, hBu]
    exact (mul_le_mul_iff_left₀ hn).mp hbound
  · exact (mul_nonpos_of_nonneg_of_nonpos backgroundAmplitude_pos.le
      (sub_nonpos.mpr (le_of_not_ge hee))).trans hη

#print axioms edgeSchur_negative_margin
#print axioms edgeSchur_nonnegative_margin

end Maxwell.Continuum.Calibration
