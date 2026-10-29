import Maxwell.Continuum.Material

/-! Self-adjointness and the positive quadratic form of actual material multiplication. -/

noncomputable section

namespace Maxwell.Continuum.ScalarDielectric

open MeasureTheory
open scoped ComplexConjugate

variable (ε : ScalarDielectric)

theorem scalarMultiplier_symmetric :
    (ε.scalarMultiplier : ScalarL2 →ₗ[ℂ] ScalarL2).IsSymmetric := by
  intro u v
  change inner ℂ (ε.scalarMultiplier u) v = inner ℂ u (ε.scalarMultiplier v)
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ε.scalarProduct_ae u, ε.scalarProduct_ae v] with x hu hv
  change inner ℂ (ε.scalarProduct u x) (v x) = inner ℂ (u x) (ε.scalarProduct v x)
  rw [hu, hv]
  simp only [← smul_eq_mul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]

theorem scalarMultiplier_selfAdjoint : IsSelfAdjoint ε.scalarMultiplier :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr ε.scalarMultiplier_symmetric

theorem multiplier_symmetric :
    (ε.multiplier : FieldL2 →ₗ[ℂ] FieldL2).IsSymmetric := by
  intro u v
  change inner ℂ (ε.multiplier u) v = inner ℂ u (ε.multiplier v)
  rw [PiLp.inner_apply, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => ε.scalarMultiplier_symmetric (u i) (v i)

theorem multiplier_selfAdjoint : IsSelfAdjoint ε.multiplier :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr ε.multiplier_symmetric

theorem pointwise_energy (x : Space) (z : ℂ) :
    RCLike.re (inner ℂ z ((ε.coefficient x : ℂ) * z)) = ε.coefficient x * ‖z‖ ^ 2 := by
  rw [← smul_eq_mul, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

theorem scalar_energy_ae (u : ScalarL2) :
    (fun x => RCLike.re (inner ℂ (u x) (ε.scalarMultiplier u x))) =ᵐ[volume]
      (fun x => ε.coefficient x * ‖u x‖ ^ 2) := by
  filter_upwards [ε.scalarProduct_ae u] with x hx
  change RCLike.re (inner ℂ (u x) (ε.scalarProduct u x)) = _
  rw [hx]
  exact ε.pointwise_energy x (u x)

theorem scalar_energy_integrable (u : ScalarL2) :
    Integrable (fun x => ε.coefficient x * ‖u x‖ ^ 2) (volume : Measure Space) :=
  (L2.integrable_inner (𝕜 := ℂ) u (ε.scalarMultiplier u)).re.congr (ε.scalar_energy_ae u)

theorem scalar_energy_eq (u : ScalarL2) :
    RCLike.re (inner ℂ u (ε.scalarMultiplier u)) =
      ∫ x : Space, ε.coefficient x * ‖u x‖ ^ 2 := by
  rw [L2.inner_def, ← integral_re (L2.integrable_inner (𝕜 := ℂ) u (ε.scalarMultiplier u))]
  exact integral_congr_ae (ε.scalar_energy_ae u)

theorem scalar_norm_sq_eq_integral (u : ScalarL2) :
    ‖u‖ ^ 2 = ∫ x : Space, ‖u x‖ ^ 2 := by
  calc
    ‖u‖ ^ 2 = RCLike.re (inner ℂ u u) := norm_sq_eq_re_inner (𝕜 := ℂ) u
    _ = ∫ x : Space, RCLike.re (inner ℂ (u x) (u x)) := by
      rw [L2.inner_def, integral_re (L2.integrable_inner (𝕜 := ℂ) u u)]
    _ = ∫ x : Space, ‖u x‖ ^ 2 := by
      simp only [inner_self_eq_norm_sq]

theorem scalar_inner_lower (u : ScalarL2) :
    ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (ε.scalarMultiplier u)) := by
  rw [ε.scalar_energy_eq, scalar_norm_sq_eq_integral]
  apply integral_mono_ae ((Lp.memLp u).integrable_norm_pow (by norm_num))
    (ε.scalar_energy_integrable u)
  exact Filter.Eventually.of_forall fun x => by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (ε.lower x) (sq_nonneg ‖u x‖)

theorem scalar_inner_upper (u : ScalarL2) :
    RCLike.re (inner ℂ u (ε.scalarMultiplier u)) ≤ 25 * ‖u‖ ^ 2 := by
  rw [ε.scalar_energy_eq, scalar_norm_sq_eq_integral, ← integral_const_mul]
  apply integral_mono_ae (ε.scalar_energy_integrable u)
    (((Lp.memLp u).integrable_norm_pow (by norm_num)).const_mul 25)
  exact Filter.Eventually.of_forall fun x =>
    mul_le_mul_of_nonneg_right (ε.upper x) (sq_nonneg ‖u x‖)

theorem inner_lower (u : FieldL2) :
    ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (ε.multiplier u)) := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.inner_apply, map_sum]
  exact Finset.sum_le_sum fun i _ => ε.scalar_inner_lower (u i)

theorem inner_upper (u : FieldL2) :
    RCLike.re (inner ℂ u (ε.multiplier u)) ≤ 25 * ‖u‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.inner_apply, map_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => ε.scalar_inner_upper (u i)

theorem inner_nonneg (u : FieldL2) :
    0 ≤ RCLike.re (inner ℂ u (ε.multiplier u)) :=
  (sq_nonneg ‖u‖).trans (ε.inner_lower u)

end Maxwell.Continuum.ScalarDielectric
