import Maxwell.Spectral.SimpleParity
import Maxwell.Spectral.YeeDisplacement
import Maxwell.Spectral.YeeAnalyticInversion

namespace Maxwell.Spectral.YeeSimpleSymmetry

noncomputable section

open PeriodicYee PrimitiveYee YeeTaylorRemainder YeeInversion YeeAnalytic

theorem centeredOperator_commutes (k : Translation) (v : EuclideanSpace ℂ Electric) :
    centeredOperator k 0 (electricIsometry k v) =
      electricIsometry k (centeredOperator k 0 v) := by
  have h := shiftedOperator_taylorParity k 0 0 0 v
  rw [YeeDisplacement.shiftedOperatorCoefficient_zero] at h
  simpa only [pow_zero, one_smul] using h.symm

/-- At an actual simple center eigenvalue, the physical inversion can be
normalized by its proved sign to fix the eigenvector. It still has the exact
complex-momentum covariance needed by analytic eigenbranch uniqueness. -/
theorem exists_center_fixed_reflection (k : Translation)
    (i : Fin (Module.finrank ℂ (EuclideanSpace ℂ Electric)))
    (hsimple : ∀ j, j ≠ i →
      (centeredOperator_symmetric k 0).eigenvalues rfl j ≠
        (centeredOperator_symmetric k 0).eigenvalues rfl i) :
    ∃ J : EuclideanSpace ℂ Electric ≃ₗᵢ[ℂ] EuclideanSpace ℂ Electric,
      Function.Involutive J ∧
      J ((centeredOperator_symmetric k 0).eigenvectorBasis rfl i) =
        (centeredOperator_symmetric k 0).eigenvectorBasis rfl i ∧
      ∀ (E : ℝ) (z : ComplexMomentum) (v : EuclideanSpace ℂ Electric),
        J (holomorphicOperator Concrete.material (timeReversalMomentum k) E z v) =
          holomorphicOperator Concrete.material (timeReversalMomentum k) E (-z) (J v) := by
  obtain ⟨σ, hσ, hparity⟩ := SimpleSplitting.simple_eigenvector_parity
    (centeredOperator k 0).toLinearMap (centeredOperator_symmetric k 0) i hsimple
    (electricIsometry k) (electricIsometry_involutive k) (centeredOperator_commutes k)
  rcases hσ with rfl | rfl
  · refine ⟨electricIsometry k, electricIsometry_involutive k, ?_, ?_⟩
    · simpa only [one_smul] using hparity
    · exact YeeAnalyticInversion.holomorphicOperator_reflection k
  · let J := (electricIsometry k).trans
      (LinearIsometryEquiv.neg ℂ :
        EuclideanSpace ℂ Electric ≃ₗᵢ[ℂ] EuclideanSpace ℂ Electric)
    have hJ (v : EuclideanSpace ℂ Electric) : J v = - electricIsometry k v := rfl
    refine ⟨J, ?_, ?_, ?_⟩
    · intro v
      simp only [hJ, map_neg, electricIsometry_involutive k v, neg_neg]
    · rw [hJ, hparity, neg_one_smul, neg_neg]
    · intro E z v
      rw [hJ, hJ, YeeAnalyticInversion.holomorphicOperator_reflection, map_neg]

end
end Maxwell.Spectral.YeeSimpleSymmetry
