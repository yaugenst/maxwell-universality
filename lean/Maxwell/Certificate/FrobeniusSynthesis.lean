import Maxwell.Certificate.FourierTransverse
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! A finite column-square certificate bounds the actual synthesis map
in the Euclidean input norm and the target Hilbert norm. -/

noncomputable section

namespace Maxwell.Certificate

theorem norm_synthesis_le_of_column_squares
    {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (v : ι → H) (C : ℝ) (hC : 0 ≤ C) (hv : ∑ j, ‖v j‖ ^ 2 ≤ C ^ 2)
    (p : EuclideanSpace ℂ ι) : ‖∑ j, p j • v j‖ ≤ C * ‖p‖ := by
  calc
    _ ≤ ∑ j, ‖p j • v j‖ := norm_sum_le _ _
    _ = ∑ j, ‖p j‖ * ‖v j‖ := by simp only [norm_smul]
    _ ≤ Real.sqrt (∑ j, ‖p j‖ ^ 2) * Real.sqrt (∑ j, ‖v j‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ ‖p‖ * C := by
      rw [← EuclideanSpace.norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]
      exact mul_le_mul_of_nonneg_left ((Real.sqrt_le_sqrt hv).trans_eq (Real.sqrt_sq hC))
        (norm_nonneg _)
    _ = _ := mul_comm _ _

/-- The same certificate applies after any linear restriction, with the
column norms measured after that restriction. -/
theorem norm_projected_synthesis_le_of_column_squares
    {ι H K : Type*} [Fintype ι] [AddCommGroup H] [Module ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (R : H →ₗ[ℂ] K) (v : ι → H) (C : ℝ) (hC : 0 ≤ C)
    (hv : ∑ j, ‖R (v j)‖ ^ 2 ≤ C ^ 2) (p : EuclideanSpace ℂ ι) :
    ‖R (∑ j, p j • v j)‖ ≤ C * ‖p‖ := by
  rw [map_sum]
  simp only [map_smul]
  exact norm_synthesis_le_of_column_squares (fun j => R (v j)) C hC hv p

end Maxwell.Certificate
