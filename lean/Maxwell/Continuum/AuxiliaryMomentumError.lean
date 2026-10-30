import Maxwell.Continuum.AuxiliaryMomentumProjection

/-! The actual cutoff error is dominated by high-momentum mass; no
polarization or source support restriction is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open FreeFiber PeriodicBand Bloch MeasureTheory

attribute [local irreducible] Bloch.unitary cutoffOperator highMomentumProjection

theorem cutoff_error_norm_le_high (f : FieldL2) :
    ‖f-cutoffOperator f‖ ≤ ‖highMomentumProjection smallRadius f‖ := by
  rw [← unitary.norm_map (f-cutoffOperator f), ← unitary.norm_map (highMomentumProjection smallRadius f),
    map_sub]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub (unitary f) (unitary (cutoffOperator f)),
    cutoffOperator_ae f, highMomentumProjection_ae smallRadius f] with q hsub hc hp
  rw [hsub, Pi.sub_apply, hc, hp]
  have he : unitary f q - (cutoff q.val : ℂ) • unitary f q =
      ((1-cutoff q.val : ℝ) : ℂ) • unitary f q := by
    push_cast
    rw [sub_smul, one_smul]
  rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (cutoff_le_one q.val))]
  by_cases hq : smallRadius ≤ ‖q.val‖
  · simp only [hq, ↓reduceIte]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [cutoff_nonneg q.val])
  · rw [cutoff_eq_one_of_norm_le (le_of_lt (lt_of_not_ge hq))]
    simp [hq]

theorem highMomentumProjection_norm_mono {r s : ℝ} (hrs : r ≤ s) (f : FieldL2) :
    ‖highMomentumProjection s f‖ ≤ ‖highMomentumProjection r f‖ := by
  have he := congrArg (fun T : FieldL2 →L[ℂ] FieldL2 => T f) (highMomentumProjection_nested hrs)
  change highMomentumProjection s (highMomentumProjection r f) = highMomentumProjection s f at he
  rw [← he]
  simpa only [one_mul] using (highMomentumProjection s).le_of_opNorm_le
    (highMomentumProjection_norm_le s) (highMomentumProjection r f)

#print axioms cutoff_error_norm_le_high

end Maxwell.Continuum.Auxiliary
