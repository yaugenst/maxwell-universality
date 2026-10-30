import Maxwell.Continuum.FiberMultiplier
import Maxwell.Continuum.PEC

/-! Literal multiplication of physical L² fields by Schwartz coefficients,
and its exact compatibility with multiplication of tempered distributions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.SchwartzMultiplier

open MeasureTheory
open scoped SchwartzMap

def data (θ : SchwartzMap Space ℂ) :
    FiberMultiplier.Data (H := ℂ) (volume : Measure Space) (SchwartzMap.seminorm ℂ 0 0 θ) where
  operator x := θ x • ContinuousLinearMap.id ℂ ℂ
  measurable := θ.continuous.aestronglyMeasurable.smul_const _
  nonneg := apply_nonneg _ _
  bound x := by
    rw [norm_smul, ContinuousLinearMap.norm_id, mul_one]
    exact θ.norm_le_seminorm ℂ x

def scalar (θ : SchwartzMap Space ℂ) : ScalarL2 →L[ℂ] ScalarL2 := (data θ).multiplier

theorem scalar_ae (θ : SchwartzMap Space ℂ) (f : ScalarL2) :
    scalar θ f =ᵐ[volume] fun x => θ x*f x := (data θ).multiplier_ae f

theorem scalar_norm_le {C : ℝ} (θ : SchwartzMap Space ℂ)
    (hθ : ∀ x, ‖θ x‖ ≤ C) (f : ScalarL2) : ‖scalar θ f‖ ≤ C*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [scalar_ae θ f] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (hθ x) (norm_nonneg _)

def field (θ : SchwartzMap Space ℂ) : FieldL2 →L[ℂ] FieldL2 :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ScalarL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => (scalar θ).comp (PiLp.proj 2 (fun _ : Fin 3 => ScalarL2) j))

theorem field_apply (θ : SchwartzMap Space ℂ) (f : FieldL2) (j : Fin 3) :
    field θ f j = scalar θ (f j) := rfl

theorem field_ae (θ : SchwartzMap Space ℂ) (f : FieldL2) (j : Fin 3) :
    field θ f j =ᵐ[volume] fun x => θ x*f j x := scalar_ae θ (f j)

theorem field_norm_le {C : ℝ} (hC : 0 ≤ C) (θ : SchwartzMap Space ℂ)
    (hθ : ∀ x, ‖θ x‖ ≤ C) (f : FieldL2) : ‖field θ f‖ ≤ C*‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mpr (scalar_norm_le θ hθ (f j))

theorem scalar_distribution (θ : SchwartzMap Space ℂ) (f : ScalarL2) :
    Lp.toTemperedDistribution (scalar θ f) =
      TemperedDistribution.smulLeftCLM ℂ θ (Lp.toTemperedDistribution f) := by
  ext φ
  rw [TemperedDistribution.smulLeftCLM_apply_apply]
  simp only [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [scalar_ae θ f] with x hx
  rw [hx, SchwartzMap.smulLeftCLM_apply_apply θ.hasTemperateGrowth]
  simp only [smul_eq_mul]
  ring

theorem scalar_schwartz (θ φ : SchwartzMap Space ℂ) :
    scalar θ (φ.toLp 2 volume) = (SchwartzMap.smulLeftCLM ℂ θ φ).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [scalar_ae θ (φ.toLp 2 volume), φ.coeFn_toLp 2 volume,
    (SchwartzMap.smulLeftCLM ℂ θ φ).coeFn_toLp 2 volume] with x hmul hφ hr
  rw [hmul, hφ, hr, SchwartzMap.smulLeftCLM_apply_apply θ.hasTemperateGrowth, smul_eq_mul]

#print axioms scalar_distribution

end Maxwell.Continuum.SchwartzMultiplier
