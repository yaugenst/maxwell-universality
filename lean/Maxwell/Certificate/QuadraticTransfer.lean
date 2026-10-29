import Maxwell.Certificate.CurvatureTransfer
import Maxwell.Spectral.QuadraticResidual

namespace Maxwell.Certificate.QuadraticTransfer

open Maxwell.Spectral Maxwell.Spectral.YeeTaylor Maxwell.Certificate.CurvatureTransfer Matrix
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def contraction (W : Fin 3 → EuclideanSpace ℂ (Fin 6) →L[ℂ] H)
    (q : PeriodicYee.Momentum) : EuclideanSpace ℂ (Fin 2) →L[ℂ] H :=
  ∑ i, (q i : ℂ) • (W i).comp (CorrectorWitness.directionCoefficients q)

theorem contraction_sq_le (W : Fin 3 → EuclideanSpace ℂ (Fin 6) →L[ℂ] H)
    (G : Matrix (Fin 6) (Fin 6) ℝ)
    (hgram : ∀ z, ∑ i, ‖W i z‖^2 ≤ Complex.re (inner ℂ z (realMatrixOperator G z)))
    (q : PeriodicYee.Momentum) (x : EuclideanSpace ℂ (Fin 2)) :
    ‖contraction W q x‖^2 ≤ radius q^2 *
      Complex.re (inner ℂ (CorrectorWitness.directionCoefficients q x)
        (realMatrixOperator G (CorrectorWitness.directionCoefficients q x))) := by
  have h := QuadraticResidual.weighted_sum_norm_sq q
    (fun i => W i (CorrectorWitness.directionCoefficients q x))
  rw [← radius_sq] at h
  exact h.trans (mul_le_mul_of_nonneg_left (hgram _) (sq_nonneg _))

theorem contraction_norm_le (W : Fin 3 → EuclideanSpace ℂ (Fin 6) →L[ℂ] H)
    (G : Matrix (Fin 6) (Fin 6) ℝ)
    (hgram : ∀ z, ∑ i, ‖W i z‖^2 ≤ Complex.re (inner ℂ z (realMatrixOperator G z)))
    (hupper : ((4 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) - G).PosSemidef)
    (q : PeriodicYee.Momentum) : ‖contraction W q‖ ≤ 2 * radius q^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hu := realMatrixOperator_upper G 4 hupper (CorrectorWitness.directionCoefficients q x)
  rw [CorrectorWitness.directionCoefficients_norm_sq] at hu
  have hs := (contraction_sq_le W G hgram q x).trans
    (mul_le_mul_of_nonneg_left hu (sq_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith only [hs]

theorem matrix_relative_bound (G F : Matrix (Fin 6) (Fin 6) ℝ) (c margin : ℝ)
    (hrel : (c • F - G - margin • (1 : Matrix (Fin 6) (Fin 6) ℝ)).PosSemidef)
    (z : EuclideanSpace ℂ (Fin 6)) :
    Complex.re (inner ℂ z (realMatrixOperator G z)) ≤
      c * Complex.re (inner ℂ z (realMatrixOperator F z)) - margin * ‖z‖^2 := by
  have h := realMatrixOperator_lower (c • F - G) margin hrel z
  rw [realMatrixOperator_quadratic] at h
  simp only [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at h
  rw [realMatrixOperator_quadratic, realMatrixOperator_quadratic]
  linarith

/-- The checked six-by-six relative Gram inequality controls the complete
quadratic residual, including every direction and both polarizations. -/
theorem contraction_relative (W : Fin 3 → EuclideanSpace ℂ (Fin 6) →L[ℂ] H)
    (G : Matrix (Fin 6) (Fin 6) ℝ)
    (hgram : ∀ z, ∑ i, ‖W i z‖^2 ≤ Complex.re (inner ℂ z (realMatrixOperator G z)))
    (hrelative : ((9/5 : ℝ) • FrozenHessian.lppm - G -
      (1/10000 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ)).PosSemidef)
    (q : PeriodicYee.Momentum) (x : EuclideanSpace ℂ (Fin 2)) :
    ‖contraction W q x‖^2 ≤ (18/5 : ℝ) * radius q^2 *
      Complex.re (inner ℂ x (directionalHalf FrozenHessian.lppm q x)) -
        (1/10000 : ℝ) * radius q^4 * ‖x‖^2 := by
  have hr := matrix_relative_bound G FrozenHessian.lppm (9/5) (1/10000)
    hrelative (CorrectorWitness.directionCoefficients q x)
  rw [CorrectorWitness.directionCoefficients_norm_sq] at hr
  have h := (contraction_sq_le W G hgram q x).trans
    (mul_le_mul_of_nonneg_left hr (sq_nonneg _))
  rw [directionalHalf_quadratic]
  nlinarith only [h]

end
end Maxwell.Certificate.QuadraticTransfer
