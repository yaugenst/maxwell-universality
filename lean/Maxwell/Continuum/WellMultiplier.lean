import Maxwell.Continuum.MaterialForm
import Maxwell.Continuum.WellBump

/-! Literal nonnegative contraction multipliers used by the auxiliary scalar well. -/

noncomputable section

namespace Maxwell.Continuum.Well

open MeasureTheory

/-- A measurable scalar profile taking values in the unit interval. -/
structure UnitProfile where
  coefficient : Space → ℝ
  measurable : Measurable coefficient
  nonneg : ∀ x, 0 ≤ coefficient x
  le_one : ∀ x, coefficient x ≤ 1

namespace UnitProfile

variable (b : UnitProfile)

private def offsetMaterial : ScalarDielectric where
  coefficient x := 1 + b.coefficient x
  measurable := measurable_const.add b.measurable
  lower x := by linarith [b.nonneg x]
  upper x := by linarith [b.le_one x]

/-- Multiplication by the literal coefficient, on complex physical `L²`. -/
def multiplier : ScalarL2 →L[ℂ] ScalarL2 :=
  b.offsetMaterial.scalarMultiplier - 1

theorem multiplier_ae (u : ScalarL2) :
    b.multiplier u =ᵐ[volume] fun x => (b.coefficient x : ℂ) * u x := by
  change (b.offsetMaterial.scalarMultiplier u - u : ScalarL2) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub (b.offsetMaterial.scalarMultiplier u) u,
    b.offsetMaterial.scalarProduct_ae u] with x hsub hmul
  change b.offsetMaterial.scalarMultiplier u x = _ at hmul
  rw [hsub, Pi.sub_apply, hmul]
  simp only [offsetMaterial, Complex.ofReal_add, Complex.ofReal_one]
  ring

theorem multiplier_apply_norm_le (u : ScalarL2) : ‖b.multiplier u‖ ≤ ‖u‖ := by
  apply (show ‖b.multiplier u‖ ≤ 1 * ‖u‖ from ?_).trans_eq (one_mul _)
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [b.multiplier_ae u] with x hx
  rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (b.nonneg x)]
  exact mul_le_mul_of_nonneg_right (b.le_one x) (norm_nonneg _)

theorem multiplier_norm_le : ‖b.multiplier‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simpa using b.multiplier_apply_norm_le)

theorem multiplier_symmetric :
    (b.multiplier : ScalarL2 →ₗ[ℂ] ScalarL2).IsSymmetric := by
  intro u v
  change inner ℂ (b.offsetMaterial.scalarMultiplier u - u) v =
    inner ℂ u (b.offsetMaterial.scalarMultiplier v - v)
  rw [inner_sub_left, inner_sub_right]
  have h := b.offsetMaterial.scalarMultiplier_symmetric u v
  change inner ℂ (b.offsetMaterial.scalarMultiplier u) v =
    inner ℂ u (b.offsetMaterial.scalarMultiplier v) at h
  rw [h]

theorem multiplier_selfAdjoint : IsSelfAdjoint b.multiplier :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr b.multiplier_symmetric

theorem inner_nonneg (u : ScalarL2) :
    0 ≤ RCLike.re (inner ℂ u (b.multiplier u)) := by
  change 0 ≤ RCLike.re (inner ℂ u (b.offsetMaterial.scalarMultiplier u - u))
  rw [inner_sub_right, map_sub, inner_self_eq_norm_sq]
  linarith [b.offsetMaterial.scalar_inner_lower u]

theorem inner_le_norm_sq (u : ScalarL2) :
    RCLike.re (inner ℂ u (b.multiplier u)) ≤ ‖u‖ ^ 2 := by
  calc
    _ ≤ ‖u‖ * ‖b.multiplier u‖ := re_inner_le_norm _ _
    _ ≤ ‖u‖ * ‖u‖ := mul_le_mul_of_nonneg_left (b.multiplier_apply_norm_le u) (norm_nonneg u)
    _ = ‖u‖ ^ 2 := (pow_two _).symm

theorem multiplier_vanishes_ae (u : ScalarL2) :
    ∀ᵐ x ∂volume, b.coefficient x = 0 → b.multiplier u x = 0 := by
  filter_upwards [b.multiplier_ae u] with x hx hzero
  simp only [hx, hzero, Complex.ofReal_zero, zero_mul]

end UnitProfile

def wellProfile : UnitProfile where
  coefficient := w
  measurable := w_contDiff.continuous.measurable
  nonneg := w_nonneg
  le_one := w_le_one

def rootProfile : UnitProfile where
  coefficient := qw
  measurable := qw_contDiff.continuous.measurable
  nonneg := qw_nonneg
  le_one := qw_le_one

theorem rootMultiplier_square :
    rootProfile.multiplier.comp rootProfile.multiplier = wellProfile.multiplier := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [rootProfile.multiplier_ae (rootProfile.multiplier u),
    rootProfile.multiplier_ae u, wellProfile.multiplier_ae u] with x houter hinner hwell
  change rootProfile.multiplier (rootProfile.multiplier u) x = wellProfile.multiplier u x
  rw [houter, hinner, hwell]
  change (qw x : ℂ) * ((qw x : ℂ) * u x) = (w x : ℂ) * u x
  rw [← mul_assoc, ← pow_two, ← Complex.ofReal_pow, qw_sq]

end Maxwell.Continuum.Well
