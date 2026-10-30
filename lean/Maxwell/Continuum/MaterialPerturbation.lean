import Maxwell.Continuum.MaterialForm

/-! Uniform scalar coefficient error bounds the actual vector L2 multiplier error. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.ScalarDielectric

open MeasureTheory

theorem scalarMultiplier_sub_norm (ε η : ScalarDielectric) {B : ℝ}
    (he : ∀ x, |ε.coefficient x-η.coefficient x| ≤ B) (u : ScalarL2) :
    ‖ε.scalarMultiplier u-η.scalarMultiplier u‖ ≤ B*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [ε.scalarProduct_ae u, η.scalarProduct_ae u,
    Lp.coeFn_sub (ε.scalarMultiplier u) (η.scalarMultiplier u)] with x hε hη hs
  rw [hs]
  simp only [Pi.sub_apply]
  change ‖ε.scalarProduct u x-η.scalarProduct u x‖ ≤ _
  rw [hε, hη, ← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (he x) (norm_nonneg _)

theorem multiplier_sub_apply_norm (ε η : ScalarDielectric) {B : ℝ} (hB : 0≤B)
    (he : ∀ x, |ε.coefficient x-η.coefficient x| ≤ B) (u : FieldL2) :
    ‖(ε.multiplier-η.multiplier) u‖ ≤ B*‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [← mul_pow]
  change ‖ε.scalarMultiplier (u j)-η.scalarMultiplier (u j)‖^2 ≤ _
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mpr
    (scalarMultiplier_sub_norm ε η he (u j))

theorem multiplier_sub_norm (ε η : ScalarDielectric) {B : ℝ} (hB : 0≤B)
    (he : ∀ x, |ε.coefficient x-η.coefficient x| ≤ B) :
    ‖ε.multiplier-η.multiplier‖ ≤ B :=
  ContinuousLinearMap.opNorm_le_bound _ hB (multiplier_sub_apply_norm ε η hB he)

#print axioms multiplier_sub_norm

end Maxwell.Continuum.ScalarDielectric
