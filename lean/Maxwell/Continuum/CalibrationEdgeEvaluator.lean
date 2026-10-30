import Maxwell.Continuum.CalibrationCentralOperator
import Maxwell.Continuum.CalibrationMatrixSymmetrization
import Maxwell.Continuum.CalibrationEdgePhysical

/-! A concrete rational symmetric 24-by-24 evaluator for the actual
dielectric-edge Schur operator, with arbitrary dyadic operator error.
The finite recurrence is semantic; charged cached-array execution is
handled separately. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber PeriodicBand

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def edgeMatrix (q : ℚ) (N : ℕ) : Matrix (Fin 24) (Fin 24) ℚ :=
  symmetricRationalMatrix (rationalSchurMatrix (piCenter (N+1)) (q+7) (fun _ => 0) (N+3))

theorem edgeMatrix_symmetric (q : ℚ) (N : ℕ) : (edgeMatrix q N).transpose = edgeMatrix q N :=
  symmetricRationalMatrix_transpose _

theorem edgeTrialScaled_totalEnergy (q : ℝ) : totalEnergy (edgeTrialScaled q) = ((q+7 : ℝ) : ℂ) := by
  have h := edgeTrialScaled_energy q
  apply Complex.ext
  · simp only [totalEnergy, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    rw [h]
    unfold freeEdge
    ring
  · simp only [totalEnergy, Complex.add_im, Complex.mul_im, Complex.ofReal_im,
      mul_zero, zero_mul, add_zero]

theorem edgeTrial_totalEnergy_bounds (q : ℝ) (he : |edgeTrialScaled q| ≤ 8) :
    7 ≤ q+7 ∧ q+7 ≤ 8 := by
  have hp := energy_perturbation_norm_le (edgeTrialScaled q) (edgeEnergyBound he)
  rw [Complex.norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos backgroundAmplitude_pos] at hp
  have hb := abs_le.mp (show |backgroundAmplitude*edgeTrialScaled q| ≤ 1/100 by
    simpa only [abs_mul, abs_of_pos backgroundAmplitude_pos] using hp)
  have hi := edgeTrialScaled_energy q
  unfold freeEdge at hi
  constructor <;> nlinarith [Real.pi_gt_d2, Real.pi_lt_d2, Real.pi_pos]

theorem edgeFiniteApprox_error (q : ℚ) (N : ℕ) (he : |edgeTrialScaled q| ≤ 8) :
    ‖calibrationFiniteSchur 0 (edgeTrialScaled q) edgeParameterBound (edgeEnergyBound he)-
      scaledFiniteSchurApprox (piCenter (N+1)) (q+7 : ℚ) (fun _ => 0)
        (by intro _j; norm_num) (piCenter_bounds (N+1))
        (by simpa only [Rat.cast_add, Rat.cast_ofNat] using edgeTrial_totalEnergy_bounds q he) (N+3)‖ ≤
      (1/2 : ℝ)^N := by
  have hr : ∀ j : Fin 3, |(0 : ℝ)| ≤ 1/16 := by intro j; norm_num
  have hF : (7 : ℝ) ≤ (q+7 : ℚ) ∧ ((q+7 : ℚ) : ℝ) ≤ 8 := by
    simpa only [Rat.cast_add, Rat.cast_ofNat] using edgeTrial_totalEnergy_bounds q he
  have hq : scaledMomentum 0 = realMomentum (fun _ => Real.pi*0) := by
    funext j
    simp only [scaledMomentum, Pi.zero_apply, mul_zero, realMomentum, Complex.ofReal_zero]
  have henergy : totalEnergy (edgeTrialScaled q) = (((q+7 : ℚ) : ℝ) : ℂ) := by
    simpa only [Rat.cast_add, Rat.cast_ofNat] using edgeTrialScaled_totalEnergy q
  have h := scaledSchurApprox_actual_error 0 (edgeTrialScaled q) (q+7 : ℚ)
    (piCenter (N+1)) (q+7 : ℚ) (fun _ => 0) edgeParameterBound (edgeEnergyBound he)
    hr hF (piCenter_bounds (N+1)) hF hq henergy (N+3)
  have hp := piCenter_error (N+1)
  have hn : 2*(1/2 : ℝ)^(N+3)+32*(|Real.pi-(piCenter (N+1) : ℝ)|+
      |((q+7 : ℚ) : ℝ)-((q+7 : ℚ) : ℝ)|) ≤
      (1/2 : ℝ)^N := by
    simp only [sub_self, abs_zero, add_zero]
    calc
      _ ≤ 2*(1/2 : ℝ)^(N+3)+32*(1/2 : ℝ)^(N+1+6) := by gcongr
      _ ≤ (1/2 : ℝ)^N := by
        simp only [pow_add]
        norm_num
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) N]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  change ‖calibrationSchur 0 (edgeTrialScaled q) edgeParameterBound (edgeEnergyBound he) u.val-
    scaledSchurApprox (piCenter (N+1)) (q+7 : ℚ) (fun _ => 0) hr (piCenter_bounds (N+1)) hF (N+3) u.val‖ ≤ _
  exact ((calibrationSchur 0 (edgeTrialScaled q) edgeParameterBound (edgeEnergyBound he)-
    scaledSchurApprox (piCenter (N+1)) (q+7 : ℚ) (fun _ => 0) hr (piCenter_bounds (N+1)) hF (N+3)).le_opNorm u.val).trans
      (mul_le_mul_of_nonneg_right (h.trans hn) (norm_nonneg _))

attribute [local irreducible] calibrationFiniteSchur scaledFiniteSchurApprox centralFinOperator

theorem edgeMatrix_error (q : ℚ) (N : ℕ) (he : |edgeTrialScaled q| ≤ 8) :
    ‖centralMatrixCLM ((edgeMatrix q N).map (Rat.castHom ℂ))-
      centralFinOperator (calibrationFiniteSchur 0 (edgeTrialScaled q)
        edgeParameterBound (edgeEnergyBound he))‖ ≤ (1/2 : ℝ)^N := by
  let hr : ∀ j : Fin 3, |((0 : ℚ) : ℝ)| ≤ 1/16 := by intro j; norm_num
  let hF : (7 : ℝ) ≤ (q+7 : ℚ) ∧ ((q+7 : ℚ) : ℝ) ≤ 8 := by
    simpa only [Rat.cast_add, Rat.cast_ofNat] using edgeTrial_totalEnergy_bounds q he
  rw [edgeMatrix, symmetricRationalMatrix_operator,
    rationalSchurMatrix_sound _ _ _ hr (piCenter_bounds (N+1)) hF]
  have hsym := centralFinOperator_selfAdjoint _ (edgeSchur_isSymmetric (edgeTrialScaled q) he)
  apply (symmetric_operator_error _ _ hsym).trans
  rw [← centralFinOperator_sub, centralFinOperator_norm]
  apply (norm_sub_rev
    (scaledFiniteSchurApprox (piCenter (N+1)) (q+7 : ℚ) (fun _ => ((0 : ℚ) : ℝ))
      hr (piCenter_bounds (N+1)) hF (N+3))
    (calibrationFiniteSchur 0 (edgeTrialScaled q) edgeParameterBound (edgeEnergyBound he))).trans_le
  simpa only [Rat.cast_zero] using edgeFiniteApprox_error q N he

#print axioms edgeMatrix_error

end Maxwell.Continuum.Calibration
