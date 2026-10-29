import Maxwell.Certificate.PointWitness.Computed0
import Maxwell.Certificate.PointWitness.Computed1

namespace Maxwell.Certificate.PointWitness
open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
noncomputable section

/-- The actual frozen primitive 6000-dimensional Yee fiber has two
separate positive eigenvalues in the certified 2^-47 point intervals. -/
theorem two_verified_eigenvalues :
    ∃ i j : Fin (Module.finrank ℂ (EuclideanSpace ℂ Electric)), i ≠ j ∧
      |pointOperator_symmetric.eigenvalues rfl i - pointCenter0| ≤ 1 / 2^47 ∧
      |pointOperator_symmetric.eigenvalues rfl j - pointCenter1| ≤ 1 / 2^47 := by
  apply two_distinct_eigenvalues_of_disjoint_residuals pointOperator pointOperator_symmetric
    pointVector0 pointVector1 pointVector0_ne_zero pointVector1_ne_zero
    pointCenter0 pointCenter1 (1 / 2^47) (1 / 2^47)
  · positivity
  · positivity
  · norm_num [pointCenter0, pointCenter1, lambdaNumerator0, lambdaNumerator1]
  · exact pointVector0_residual
  · exact pointVector1_residual

/-- Both certified point eigenvalues are strictly positive and lie in the
paper's coarse local spectral window. -/
theorem two_verified_positive_eigenvalues :
    ∃ i j : Fin (Module.finrank ℂ (EuclideanSpace ℂ Electric)), i ≠ j ∧
      pointOperator_symmetric.eigenvalues rfl i ∈ Set.Ioo (239/25000) (957/100000) ∧
      pointOperator_symmetric.eigenvalues rfl j ∈ Set.Ioo (239/25000) (957/100000) := by
  obtain ⟨i, j, hij, hi, hj⟩ := two_verified_eigenvalues
  refine ⟨i, j, hij, ?_, ?_⟩
  · have hr := pointCenter0_range
    have hi' := abs_le.mp hi
    constructor <;> linarith
  · have hr := pointCenter1_range
    have hj' := abs_le.mp hj
    constructor <;> linarith

end
end Maxwell.Certificate.PointWitness
