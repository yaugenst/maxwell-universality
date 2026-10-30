import Maxwell.Continuum.CalibrationCentralOperator
import Maxwell.Continuum.CalibrationRationalInverse

/-! Finite central inversion commutes with the literal orthonormal
coordinate map. This joins the rational inverse to the full Feshbach
operator without an additional finite-dimensional inverse oracle. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.Calibration

theorem centralFinOperator_one : centralFinOperator 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change centralFinUnitary.symm (centralFinUnitary x) = x
  exact centralFinUnitary.symm_apply_apply x

theorem centralFinOperator_mul (A B : centralSpace →L[ℂ] centralSpace) :
    centralFinOperator (A*B) = centralFinOperator A*centralFinOperator B := by
  apply ContinuousLinearMap.ext
  intro x
  change centralFinUnitary.symm (A (B (centralFinUnitary x))) =
    centralFinUnitary.symm (A (centralFinUnitary (centralFinUnitary.symm (B (centralFinUnitary x)))))
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem centralFinOperator_isUnit (A : centralSpace →L[ℂ] centralSpace) (hA : IsUnit A) :
    IsUnit (centralFinOperator A) := by
  refine ⟨⟨centralFinOperator A,centralFinOperator (Ring.inverse A),?_,?_⟩,rfl⟩
  · rw [← centralFinOperator_mul,Ring.mul_inverse_cancel _ hA,centralFinOperator_one]
  · rw [← centralFinOperator_mul,Ring.inverse_mul_cancel _ hA,centralFinOperator_one]

theorem centralFinOperator_inverse (A : centralSpace →L[ℂ] centralSpace) (hA : IsUnit A) :
    centralFinOperator (Ring.inverse A) = Ring.inverse (centralFinOperator A) := by
  have hC := centralFinOperator_isUnit A hA
  calc
    _ = centralFinOperator (Ring.inverse A)*1 := (mul_one _).symm
    _ = centralFinOperator (Ring.inverse A)*
      (centralFinOperator A*Ring.inverse (centralFinOperator A)) := by
      rw [Ring.mul_inverse_cancel _ hC]
    _ = _ := by
      rw [← mul_assoc,← centralFinOperator_mul,Ring.inverse_mul_cancel _ hA,
        centralFinOperator_one,one_mul]

theorem rationalSchurInverse_sound (t E : ℚ) (r : Fin 3 → ℚ)
    (hr : ∀ j, |(r j : ℝ)| ≤ 1/16) (ht : (3 : ℝ) ≤ t ∧ (t : ℝ) ≤ 4)
    (hE : (7 : ℝ) ≤ E ∧ (E : ℝ) ≤ 8) (K : ℕ)
    (hS : IsUnit (scaledFiniteSchurApprox t E (fun j => (r j : ℝ)) hr ht hE K)) :
    centralMatrixCLM ((rationalMatrixInverse (rationalSchurMatrix t E r K)).map (Rat.castHom ℂ)) =
      centralFinOperator (Ring.inverse (scaledFiniteSchurApprox t E (fun j => (r j : ℝ)) hr ht hE K)) := by
  have hM : IsUnit (centralMatrixCLM ((rationalSchurMatrix t E r K).map (Rat.castHom ℂ))) := by
    rw [rationalSchurMatrix_sound t E r hr ht hE K]
    exact centralFinOperator_isUnit _ hS
  rw [rationalMatrixInverse_sound _ hM,rationalSchurMatrix_sound t E r hr ht hE K,
    ← centralFinOperator_inverse _ hS]

#print axioms rationalSchurInverse_sound

end Maxwell.Continuum.Calibration
