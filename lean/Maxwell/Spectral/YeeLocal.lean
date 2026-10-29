import Maxwell.Spectral.Trial
import Maxwell.Spectral.YeeTaylorRemainder

/-!
# Finite jet data force the actual Yee band separation

The operator, convergent series, coefficient estimates and inversion symmetry
are those of the frozen material.  Only the finite trial-space data and the
eligible-band eigenvalue count remain as hypotheses.
-/

namespace Maxwell.Spectral.YeeLocal

open PeriodicYee PrimitiveYee YeeTaylor YeeInversion YeeTaylorRemainder

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [CompleteSpace V] [FiniteDimensional ℂ V]

/-- The local spectral-polynomial argument for the actual primitive Maxwell
fiber.  The finite premises refer to the exact low-order operators, rather
than to a supplied Taylor remainder or band inequality. -/
theorem local_band_gap (k : Translation) (q : Momentum) (δ E : ℝ)
    (Φ Y : V →L[ℂ] EuclideanSpace ℂ Electric)
    (hr0 : 0 < radius q) (hr : radius q ≤ 1 / 20)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (2 : ℝ) ^ 20)
    (hElo : 239 / 25000 ≤ E) (hEhi : E ≤ 957 / 100000)
    (hΦnorm : ‖Φ‖ ≤ 1) (hYnorm : ‖Y‖ ≤ 3 * radius q)
    (hcancel : (shiftedOperatorCoefficient Concrete.material
      (timeReversalMomentum k) q E 0).comp Y =
      (shiftedOperatorCoefficient Concrete.material (timeReversalMomentum k) q E 1).comp Φ)
    (σ : ℂ) (hσ : σ = 1 ∨ σ = -1)
    (hΦ : HasParity (electricIsometry k) σ Φ)
    (hY : HasParity (electricIsometry k) (-σ) Y)
    (hjet : FiniteJetBounds
      (shiftedOperatorCoefficient Concrete.material (timeReversalMomentum k) q E)
      Φ Y (radius q) δ E)
    (hdim : 2 ≤ Module.finrank ℂ V)
    (hinertia : (Finset.univ.filter fun i =>
      0 < (centeredOperator_symmetric k q).eigenvalues rfl i ∧
      (centeredOperator_symmetric k q).eigenvalues rfl i < 7 / 256).card ≤ 2) :
    ∀ i : Fin (Module.finrank ℂ (EuclideanSpace ℂ Electric)),
      0 < (centeredOperator_symmetric k q).eigenvalues rfl i →
      (centeredOperator_symmetric k q).eigenvalues rfl i < 7 / 256 →
      radius q ^ 2 / 600 < (centeredOperator_symmetric k q).eigenvalues rfl i - E := by
  exact local_band_gap_from_taylor
    (centeredOperator k q).toLinearMap (centeredOperator_symmetric k q)
    (shiftedOperatorCoefficient Concrete.material (timeReversalMomentum k) q E)
    (shiftedCenteredOperator Concrete.material (timeReversalMomentum k) q E)
    (shiftedOperatorCoefficient_hasSum Concrete.material (timeReversalMomentum k) q E)
    Φ Y (radius q) δ E (shiftedCenteredOperator_toLinearMap k q E)
    hr0 hr hδ0 hδ hElo hEhi hΦnorm hYnorm
    (shiftedOperatorCoefficient_norm_le Concrete.material (timeReversalMomentum k) q E)
    hcancel (electricIsometry k) σ hσ (shiftedOperator_taylorParity k q E)
    hΦ hY hjet hdim hinertia

end
end Maxwell.Spectral.YeeLocal
