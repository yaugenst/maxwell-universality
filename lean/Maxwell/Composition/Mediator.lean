import Maxwell.Composition.SourceIdentity
import Mathlib.Tactic.Linarith

/-!
# Quantitative mediator elimination

Terminal and mediator coordinates are extracted from a common normed space.
Their projections are contractions, as they are for orthogonal Euclidean
coordinates. The transfer bound is deduced from the actual block Schur
identity and retains arbitrary residuals in the mediator equations.
-/

namespace Maxwell.Composition

variable {D B C : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup B] [NormedSpace ℝ B]
variable [NormedAddCommGroup C] [NormedSpace ℝ C]

/-- Eliminating mediator equations amplifies a full residual by at most four
when the terminal/mediator projections are contractive and the off-diagonal
inverse product has norm at most three. The latter is weaker than the
paper's bound `sqrt 6`. -/
theorem mediator_residual_map_norm_le
    (T : D →L[ℝ] D) (Z : C →L[ℝ] D)
    (P : D →L[ℝ] B) (R : D →L[ℝ] C) (Dm : C ≃L[ℝ] C)
    (hP : ‖P‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hmix : ‖(P.comp (T.comp Z)).comp (Dm.symm : C →L[ℝ] C)‖ ≤ 3) :
    ‖complementaryResidualMap T Z P R Dm‖ ≤ 4 := by
  have hcorrection : ‖((P.comp (T.comp Z)).comp
      (Dm.symm : C →L[ℝ] C)).comp R‖ ≤ 3 := by
    calc
      _ ≤ ‖(P.comp (T.comp Z)).comp (Dm.symm : C →L[ℝ] C)‖ * ‖R‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 3 * 1 := mul_le_mul hmix hR (norm_nonneg _) (by norm_num)
      _ = 3 := by norm_num
  rw [complementaryResidualMap, ← ContinuousLinearMap.comp_assoc]
  exact (norm_sub_le _ _).trans (by linarith)

/-- The exact terminal Schur complement yields a relative transfer bound
for every full vector, without assuming the mediator equations hold exactly.
The source is supported on the terminal coordinates. -/
theorem mediator_residual_transfer
    (T : D →L[ℝ] D) (U : B →L[ℝ] D) (Z : C →L[ℝ] D)
    (P : D →L[ℝ] B) (R : D →L[ℝ] C) (Dm : C ≃L[ℝ] C)
    (Γ : B →L[ℝ] B) (α : ℝ) (hα : 0 < α)
    (hdecomp : ∀ d, d = U (P d) + Z (R d))
    (hDm : ∀ c, R (T (Z c)) = Dm c)
    (hPU : ∀ b, P (U b) = b) (hRU : ∀ b, R (U b) = 0)
    (hSchur : brightSchurOperator T U Z P R Dm = α • Γ)
    (hP : ‖P‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hmix : ‖(P.comp (T.comp Z)).comp (Dm.symm : C →L[ℝ] C)‖ ≤ 3)
    (z : D) (g : B) :
    ‖Γ (P z) - g‖ ≤ (4 / α) * ‖T z - α • U g‖ := by
  let r := T z - U (α • g)
  have hT : T z = U (α • g) + r := by dsimp [r]; abel
  have hexact := complementary_schur_residual T U Z P R Dm
    hdecomp hDm hPU hRU z (α • g) r hT
  rw [hSchur] at hexact
  have hscaled : α • (Γ (P z) - g) = complementaryResidualMap T Z P R Dm r := by
    simp only [smul_apply] at hexact
    rw [smul_sub, hexact]
    abel
  have hnorm : α * ‖Γ (P z) - g‖ ≤ 4 * ‖r‖ := by
    calc
      _ = ‖α • (Γ (P z) - g)‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hα]
      _ = ‖complementaryResidualMap T Z P R Dm r‖ := congrArg norm hscaled
      _ ≤ ‖complementaryResidualMap T Z P R Dm‖ * ‖r‖ :=
        (complementaryResidualMap T Z P R Dm).le_opNorm r
      _ ≤ 4 * ‖r‖ := mul_le_mul_of_nonneg_right
        (mediator_residual_map_norm_le T Z P R Dm hP hR hmix) (norm_nonneg _)
  have hr : r = T z - α • U g := by simp [r]
  rw [hr] at hnorm
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hα).mpr
  simpa only [mul_comm] using hnorm

end Maxwell.Composition
