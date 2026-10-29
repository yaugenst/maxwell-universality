import Maxwell.Certificate.CurvatureTransfer

namespace Maxwell.Certificate.CurvatureTransferGeneric

open Matrix Maxwell.Spectral Maxwell.Spectral.YeeTaylor
open Maxwell.Spectral.PeriodicYee (Momentum)
open CurvatureTransfer

noncomputable section

/-- Certified lower and upper forms for an arbitrary rounded Hessian give
the corresponding directional half-Hessian bounds. -/
theorem directionalHalf_rounded_bounds
    (H : Matrix (Fin 6) (Fin 6) ℝ)
    (hlo : (H - (2003/50000 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ)).PosSemidef)
    (hhi : ((49997/50000 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) - H).PosSemidef)
    (q : Momentum) (x : EuclideanSpace ℂ (Fin 2)) :
    (2003/100000 : ℝ) * radius q^2 * ‖x‖^2 ≤
        Complex.re (inner ℂ x (directionalHalf H q x)) ∧
      Complex.re (inner ℂ x (directionalHalf H q x)) ≤
        (49997/100000 : ℝ) * radius q^2 * ‖x‖^2 := by
  have hl := realMatrixOperator_lower H (2003/50000) hlo
    (CorrectorWitness.directionCoefficients q x)
  have hu := realMatrixOperator_upper H (49997/50000) hhi
    (CorrectorWitness.directionCoefficients q x)
  rw [CorrectorWitness.directionCoefficients_norm_sq] at hl hu
  rw [directionalHalf_quadratic]
  constructor <;> linarith

/-- Entrywise approximation of any certified rounded Hessian, followed by
the actual operator replacement estimate, gives the final directional forms. -/
theorem directional_bounds_of_approximation
    (H G : Matrix (Fin 6) (Fin 6) ℝ)
    (hlo : (H - (2003/50000 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ)).PosSemidef)
    (hhi : ((49997/50000 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) - H).PosSemidef)
    (q : Momentum)
    (K : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
    (hentry : ∀ i j, |G i j - H i j| ≤ 1 / 10^11)
    (hreplace : ‖K - directionalHalf G q‖ ≤ (1/1000000 : ℝ) * radius q^2)
    (x : EuclideanSpace ℂ (Fin 2)) :
    radius q^2 * ‖x‖^2 / 50 ≤ Complex.re (inner ℂ x (K x)) ∧
      Complex.re (inner ℂ x (K x)) ≤ radius q^2 * ‖x‖^2 := by
  have hr := directionalHalf_error G H q (1/10^11) (by positivity) hentry
  have he : ‖K - directionalHalf H q‖ ≤
      (1/1000000 + 3/10^11 : ℝ) * radius q^2 := by
    calc
      _ ≤ ‖K - directionalHalf G q‖ + ‖directionalHalf G q - directionalHalf H q‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by nlinarith only [hreplace, hr]
  have hl := JetTransfer.quadratic_lower_transfer K (directionalHalf H q)
    ((2003/100000 : ℝ) * radius q^2)
    ((1/1000000 + 3/10^11 : ℝ) * radius q^2) he
    (fun y => (directionalHalf_rounded_bounds H hlo hhi q y).1) x
  have hu := JetTransfer.quadratic_upper_transfer K (directionalHalf H q)
    ((49997/100000 : ℝ) * radius q^2)
    ((1/1000000 + 3/10^11 : ℝ) * radius q^2) he
    (fun y => (directionalHalf_rounded_bounds H hlo hhi q y).2) x
  have hp : 0 ≤ radius q^2 * ‖x‖^2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  constructor <;> nlinarith only [hl, hu, hp]

end
end Maxwell.Certificate.CurvatureTransferGeneric
