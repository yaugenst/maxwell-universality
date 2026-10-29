import Maxwell.TargetRowGeometry
import Maxwell.SchurBound

/-! The uniform Euclidean operator norm of the actual relative-PEC target.

The exact incidence bounds imply absolute row and column sums at most 16.
The finite Schur estimate converts these to the Euclidean operator norm.
No bound on box side lengths or matrix dimension is assumed.
-/

namespace Maxwell.Target

theorem maxwell_real_toEuclideanCLM_norm_le {B : Box}
    (material : ScalarMaterial B.nx B.ny B.nz) :
    ‖Matrix.toEuclideanCLM (n := B.Edge) (𝕜 := ℝ)
      ((maxwell material).map fun q => (q : ℝ))‖ ≤ 16 := by
  apply Maxwell.matrix_toEuclideanCLM_norm_le _ 16 (by norm_num)
  · intro e
    change (∑ j : B.Edge, |(maxwell material e j : ℝ)|) ≤ 16
    exact_mod_cast maxwell_row_l1 material e
  · intro e
    change (∑ j : B.Edge, |(maxwell material j e : ℝ)|) ≤ 16
    exact_mod_cast maxwell_column_l1 material e

/-- The identical bound holds for the complex physical solver. The proof
applies the real Schur estimate to componentwise magnitudes, so no real-only
restriction is imposed on admissible electric fields. -/
theorem maxwell_complex_toEuclideanCLM_norm_le {B : Box}
    (material : ScalarMaterial B.nx B.ny B.nz) :
    ‖Matrix.toEuclideanCLM (n := B.Edge) (𝕜 := ℂ)
      ((maxwell material).map fun q => (q : ℂ))‖ ≤ 16 := by
  let A : Matrix B.Edge B.Edge ℂ := (maxwell material).map fun q => (q : ℂ)
  let C : Matrix B.Edge B.Edge ℝ := fun e j => |(maxwell material e j : ℝ)|
  have hrow : ∀ e, ∑ j, |C e j| ≤ 16 := by
    intro e
    simp only [C, abs_abs]
    exact_mod_cast maxwell_row_l1 material e
  have hcol : ∀ j, ∑ e, |C e j| ≤ 16 := by
    intro j
    simp only [C, abs_abs]
    exact_mod_cast maxwell_column_l1 material j
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have hp : ∀ e,
      ‖A.mulVec (WithLp.ofLp x) e‖ ≤ C.mulVec (fun j => ‖x j‖) e := by
    intro e
    calc
      ‖A.mulVec (WithLp.ofLp x) e‖ ≤ ∑ j, ‖A e j * x j‖ :=
        norm_sum_le _ _
      _ = C.mulVec (fun j => ‖x j‖) e := by
        simp only [Matrix.mulVec, dotProduct, A, Matrix.map_apply,
          norm_mul, Complex.norm_ratCast, C]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 16 * ‖x‖)).mp
  simpa only [EuclideanSpace.norm_sq_eq, Matrix.ofLp_toEuclideanCLM, mul_pow] using
    (calc
      (∑ e, ‖A.mulVec (WithLp.ofLp x) e‖ ^ 2) ≤
          ∑ e, (C.mulVec (fun j => ‖x j‖) e) ^ 2 := by
        apply Finset.sum_le_sum
        intro e _
        have h := hp e
        have hn := norm_nonneg (A.mulVec (WithLp.ofLp x) e)
        nlinarith
      _ ≤ 16 ^ 2 * ∑ j, ‖x j‖ ^ 2 :=
        Maxwell.matrix_schur_square_bound C 16 (by norm_num) hrow hcol _)

end Maxwell.Target
