import Maxwell.Continuum.AngularFourier
import Maxwell.Continuum.FiberMultiplier
import Maxwell.Continuum.WellMultiplier

/-! Literal multiplication by the scalar well on Hilbert-valued L² and
its unitary angular-Fourier conjugate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def wellVectorData : FiberMultiplier.Data (H := H) (volume : Measure Space) 1 where
  operator x := (Well.w x : ℂ) • ContinuousLinearMap.id ℂ H
  measurable := ((Complex.continuous_ofReal.comp Well.w_contDiff.continuous).smul
    continuous_const).aestronglyMeasurable
  nonneg := by norm_num
  bound x := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro f
    change ‖(Well.w x : ℂ) • f‖ ≤ 1 * ‖f‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Well.w_nonneg x)]
    exact mul_le_mul_of_nonneg_right (Well.w_le_one x) (norm_nonneg f)

def physicalWellMultiplier : L2Dilation.L2 (H := H) →L[ℂ] L2Dilation.L2 (H := H) :=
  (wellVectorData H).multiplier

theorem physicalWellMultiplier_ae (f : L2Dilation.L2 (H := H)) :
    physicalWellMultiplier H f =ᵐ[volume] fun x => (Well.w x : ℂ) • f x :=
  (wellVectorData H).multiplier_ae f

theorem physicalWellMultiplier_norm : ‖physicalWellMultiplier H‖ ≤ 1 :=
  (wellVectorData H).multiplier_norm_le

theorem physicalWellMultiplier_scalar : physicalWellMultiplier ℂ = Well.wellProfile.multiplier := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [physicalWellMultiplier_ae ℂ f, Well.wellProfile.multiplier_ae f] with x hv hs
  rw [hv, hs]
  rfl

variable [CompleteSpace H]

def angularWellConvolution : L2Dilation.L2 (H := H) →L[ℂ] L2Dilation.L2 (H := H) :=
  (angularFourier H).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((physicalWellMultiplier H).comp
      (angularFourier H).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem angularWellConvolution_apply (f : L2Dilation.L2 (H := H)) :
    angularWellConvolution H f =
      angularFourier H (physicalWellMultiplier H ((angularFourier H).symm f)) := rfl

theorem angularWellConvolution_norm : ‖angularWellConvolution H‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [angularWellConvolution_apply, (angularFourier H).norm_map,
    ← (angularFourier H).symm.norm_map f]
  exact (physicalWellMultiplier H).le_of_opNorm_le (physicalWellMultiplier_norm H) _

end Maxwell.Continuum.EffectiveMass
