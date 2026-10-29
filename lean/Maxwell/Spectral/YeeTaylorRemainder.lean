import Maxwell.Spectral.YeeInversion
import Maxwell.Spectral.TaylorRemainder

/-! The Taylor remainder package specialized to the actual frozen primitive
Maxwell operator.  Series convergence, coefficient norms, and inversion parity
are proved from the Yee stencil and material; they are not caller premises. -/
namespace Maxwell.Spectral.YeeTaylorRemainder

open Maxwell.Spectral.PeriodicYee
open Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.YeeTaylor
open Maxwell.Spectral.YeeInversion
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The actual centered primitive fiber as an operator on the Euclidean field space. -/
def centeredOperator (k : Translation) (q : Momentum) :
    EuclideanSpace ℂ Electric →L[ℂ] EuclideanSpace ℂ Electric :=
  Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
    (centeredFiber Concrete.material (timeReversalMomentum k) q)

theorem centeredOperator_symmetric (k : Translation) (q : Momentum) :
    (centeredOperator k q).toLinearMap.IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  apply (Matrix.isHermitian_conjTranspose_mul_self
    (centeredCurl (timeReversalMomentum k) q)).sub
  exact (PrimitiveYee.mass_hermitian Concrete.material).smul (by
    change star (1 / 64 : ℂ) = _
    simp)

/-- The spectral shift used in the Taylor coefficients is the shift of this
same actual selfadjoint operator. -/
theorem shiftedCenteredOperator_toLinearMap (k : Translation) (q : Momentum) (E : ℝ) :
    (shiftedCenteredOperator Concrete.material (timeReversalMomentum k) q E).toLinearMap =
      (centeredOperator k q).toLinearMap -
        (E : ℂ) • (LinearMap.id : EuclideanSpace ℂ Electric →ₗ[ℂ] EuclideanSpace ℂ Electric) := by
  change (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
    (centeredFiber Concrete.material (timeReversalMomentum k) q - (E : ℂ) • 1)).toLinearMap = _
  rw [map_sub, map_smul, map_one]
  rfl

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Actual-Yee remainder theorem with all analytic and inversion-covariance
premises discharged.  The remaining data describe the chosen finite center
space and its exact first-order corrector. -/
theorem local_taylor_decomposition (k : Translation) (q : Momentum) (E : ℝ)
    (Φ Y : V →L[ℂ] EuclideanSpace ℂ Electric)
    (hr : radius q ≤ 1 / 20) (hΦnorm : ‖Φ‖ ≤ 1) (hYnorm : ‖Y‖ ≤ 3 * radius q)
    (hcancel : (shiftedOperatorCoefficient Concrete.material (timeReversalMomentum k) q E 0).comp Y =
      (shiftedOperatorCoefficient Concrete.material (timeReversalMomentum k) q E 1).comp Φ)
    (σ : ℂ) (hσ : σ = 1 ∨ σ = -1)
    (hΦ : HasParity (electricIsometry k) σ Φ)
    (hY : HasParity (electricIsometry k) (-σ) Y) :
    let A := shiftedOperatorCoefficient Concrete.material (timeReversalMomentum k) q E
    let B := shiftedCenteredOperator Concrete.material (timeReversalMomentum k) q E
    ∃ (Krem : V →L[ℂ] V) (Reven Rodd : V →L[ℂ] EuclideanSpace ℂ Electric),
      (Φ - Y).adjoint.comp (B.comp (Φ - Y)) =
        Φ.adjoint.comp ((A 0).comp Φ) +
          (Φ.adjoint.comp ((A 2).comp Φ) - Φ.adjoint.comp ((A 1).comp Y)) + Krem ∧
      B.comp (Φ - Y) = (A 0).comp Φ + residualTaylorTerm A Φ Y 1 + Reven + Rodd ∧
      ‖Krem‖ ≤ (13 / 5) * radius q ^ 4 ∧ ‖Reven‖ ≤ (2 / 25) * radius q ^ 4 ∧
      ‖Rodd‖ ≤ (17 / 20) * radius q ^ 3 ∧
      ((A 0).comp Φ + residualTaylorTerm A Φ Y 1 + Reven).adjoint.comp Rodd = 0 := by
  exact Maxwell.Spectral.local_taylor_decomposition
    (shiftedOperatorCoefficient Concrete.material (timeReversalMomentum k) q E)
    (shiftedCenteredOperator Concrete.material (timeReversalMomentum k) q E)
    (shiftedOperatorCoefficient_hasSum Concrete.material (timeReversalMomentum k) q E)
    Φ Y (radius q) (radius_nonneg q) hr hΦnorm hYnorm
    (shiftedOperatorCoefficient_norm_le Concrete.material (timeReversalMomentum k) q E)
    hcancel (electricIsometry k) σ hσ (shiftedOperator_taylorParity k q E) hΦ hY

end
end Maxwell.Spectral.YeeTaylorRemainder
