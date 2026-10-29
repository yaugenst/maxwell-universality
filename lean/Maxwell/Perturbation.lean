import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-! Quantitative perturbation and residual estimates used by the rational
normalization, physical assembly, and finite-precision decoder. -/

namespace Maxwell

section Neumann

variable {R : Type*} [NormedRing R] [NormOneClass R] [HasSummableGeomSeries R]

/-- The geometric inverse has an explicit bound, not merely continuity. -/
theorem norm_oneSub_inv_le_two (t : R) (ht : ‖t‖ ≤ (1 : ℝ) / 2) :
    ‖(↑((Units.oneSub t (by linarith))⁻¹) : R)‖ ≤ 2 := by
  change ‖∑' n : ℕ, t ^ n‖ ≤ 2
  have hgeom := tsum_geometric_le_of_norm_lt_one t (show ‖t‖ < 1 by linarith)
  have hden : (1 - ‖t‖)⁻¹ ≤ (2 : ℝ) := by
    apply inv_le_of_inv_le₀ (by norm_num)
    linarith
  have hg : ‖∑' n : ℕ, t ^ n‖ ≤ (1 - ‖t‖)⁻¹ := by
    simpa only [norm_one, sub_self, zero_add] using hgeom
  exact hg.trans hden

/-- A norm-small perturbation of an actual unit remains a unit, with the
factor-two inverse estimate used throughout the manuscript. -/
theorem unit_perturbation_inverse_bound (a : Rˣ) (e : R)
    (hsmall : ‖(↑a⁻¹ : R)‖ * ‖e‖ ≤ (1 : ℝ) / 2) :
    ∃ b : Rˣ, (b : R) = (a : R) + e ∧
      ‖(↑b⁻¹ : R)‖ ≤ 2 * ‖(↑a⁻¹ : R)‖ := by
  let t : R := -((↑a⁻¹ : R) * e)
  have ht : ‖t‖ ≤ (1 : ℝ) / 2 := by
    dsimp [t]
    rw [norm_neg]
    exact (norm_mul_le _ _).trans hsmall
  let u : Rˣ := Units.oneSub t (by linarith)
  refine ⟨a * u, ?_, ?_⟩
  · simp [u, t, mul_add, ← mul_assoc]
  · rw [mul_inv_rev, Units.val_mul]
    calc
      ‖(↑u⁻¹ : R) * ↑a⁻¹‖ ≤ ‖(↑u⁻¹ : R)‖ * ‖(↑a⁻¹ : R)‖ := norm_mul_le _ _
      _ ≤ 2 * ‖(↑a⁻¹ : R)‖ :=
        mul_le_mul_of_nonneg_right (norm_oneSub_inv_le_two t ht) (norm_nonneg _)

end Neumann

section Residual

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Matrix and source rounding are both charged to the residual. -/
theorem residual_perturbation_bound (A Ahat : E →L[𝕜] F) (x : E) (b bhat : F) :
    ‖A x - b‖ ≤ ‖Ahat x - bhat‖ + ‖A - Ahat‖ * ‖x‖ + ‖bhat - b‖ := by
  have hid : A x - b = (Ahat x - bhat) + (A - Ahat) x + (bhat - b) := by
    simp only [sub_apply]
    abel
  rw [hid]
  calc
    ‖(Ahat x - bhat) + (A - Ahat) x + (bhat - b)‖ ≤
        ‖(Ahat x - bhat) + (A - Ahat) x‖ + ‖bhat - b‖ := norm_add_le _ _
    _ ≤ (‖Ahat x - bhat‖ + ‖(A - Ahat) x‖) + ‖bhat - b‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ‖Ahat x - bhat‖ + ‖A - Ahat‖ * ‖x‖ + ‖bhat - b‖ := by
      gcongr
      exact (A - Ahat).le_opNorm x

/-- A local finite readout perturbation is paid once through the original
operator, and applies to every supplied approximation. -/
theorem rounded_output_residual_bound (A : E →L[𝕜] F) (x xhat : E) (b : F) :
    ‖A xhat - b‖ ≤ ‖A x - b‖ + ‖A‖ * ‖xhat - x‖ := by
  have hid : A xhat - b = (A x - b) + A (xhat - x) := by
    rw [map_sub]
    abel
  rw [hid]
  exact (norm_add_le _ _).trans
    (add_le_add (le_refl _) (A.le_opNorm (xhat - x)))

end Residual

end Maxwell
