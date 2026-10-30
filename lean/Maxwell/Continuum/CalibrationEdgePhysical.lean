import Maxwell.Continuum.CalibrationEdgeSign
import Maxwell.Continuum.EdgeInitialBracket

/-! The Schur sign decisions in the exact dielectric-energy units used
by the finite rational edge bisection. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration

open FreeFiber PeriodicBand
open scoped InnerProductSpace

def edgeTrialScaled (q : ℝ) : ℝ := (q-freeEdge)/backgroundAmplitude

theorem dielectricEdge_scaled :
    (dielectricBand 0).re = freeEdge+backgroundAmplitude*edgeScaled := by
  rw [dielectricBand_formula]
  simp only [unscale, smul_zero, Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

theorem edgeTrialScaled_energy (q : ℝ) :
    backgroundAmplitude*edgeTrialScaled q = q-freeEdge := by
  unfold edgeTrialScaled
  field_simp [backgroundAmplitude_pos.ne']

theorem edgeTrialScaled_bound (q : ℝ)
    (hq : |edgeTrialScaled q-Corner.lambdaStar| ≤ 1/100) : |edgeTrialScaled q| ≤ 8 := by
  have h := abs_add_le (edgeTrialScaled q-Corner.lambdaStar) Corner.lambdaStar
  rw [sub_add_cancel, abs_of_pos Corner.lambdaStar_pos] at h
  linarith only [h, hq, lambdaStar_le]

theorem edgeInitial_trial_bound (q : ℚ) (hq : edgeInitial.lo ≤ q ∧ q ≤ edgeInitial.hi) :
    |edgeTrialScaled q| ≤ 8 :=
  edgeTrialScaled_bound q (edgeInitial_scaled_error q hq)

theorem edge_negative_sign (q : ℝ) (he : |edgeTrialScaled q| ≤ 8)
    (B : centralSpace →L[ℂ] centralSpace) {η : ℝ}
    (herr : ‖B-calibrationFiniteSchur 0 (edgeTrialScaled q)
      edgeParameterBound (edgeEnergyBound he)‖ ≤ η)
    (hB : ∀ u : centralSpace, u ≠ 0 → (inner ℂ u (B u)).re < 0) :
    (dielectricBand 0).re ≤ q+η := by
  have h := edgeSchur_negative_margin (edgeTrialScaled q) he B herr hB
  have hE := edgeTrialScaled_energy q
  rw [dielectricEdge_scaled]
  linarith only [h, hE]

theorem edge_nonnegative_sign (q : ℝ) (he : |edgeTrialScaled q| ≤ 8)
    (B : centralSpace →L[ℂ] centralSpace) {η : ℝ}
    (herr : ‖B-calibrationFiniteSchur 0 (edgeTrialScaled q)
      edgeParameterBound (edgeEnergyBound he)‖ ≤ η)
    (hB : ∃ u : centralSpace, u ≠ 0 ∧ 0 ≤ (inner ℂ u (B u)).re) :
    q-η ≤ (dielectricBand 0).re := by
  have h := edgeSchur_nonnegative_margin (edgeTrialScaled q) he B herr hB
  have hE := edgeTrialScaled_energy q
  rw [dielectricEdge_scaled]
  linarith only [h, hE]

#print axioms edge_negative_sign
#print axioms edge_nonnegative_sign

end Maxwell.Continuum.Calibration
