import Maxwell.Continuum.EffectiveMassAliasSplit
import Maxwell.Continuum.EffectiveMassEnvelope
import Maxwell.Continuum.WellMass

/-! The literal well-weighted mass of the zero-momentum periodic mode.
Its averaging error is exactly the already controlled off-alias kernel. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber PeriodicBand CellBandFourier

theorem scaledFiber_zero (h : ℝ) : scaledFiber h 0 = physicalFiberVector 0 := by
  rw [scaledFiber, smul_zero]
  rfl

theorem zero_bloch_inner (x : Space) :
    inner ℂ (blochField (physicalMomentum 0) (physicalFiberVector 0) x)
      (blochField (physicalMomentum 0) (physicalFiberVector 0) x) =
      ((‖cellEigenfunction 0 x‖^2 : ℝ) : ℂ) := by
  have hp : physicalMomentum (0 : Space) = 0 := by ext j; simp [physicalMomentum, realMomentum]
  have hv : physicalFiberVector 0 = FiberNormalization.normalizedFiberVector 0 := by
    rw [physicalFiberVector, unscale, smul_zero]
  have hz : spatialPhase 0 x = 1 := by simp [spatialPhase]
  rw [hp, blochField, hz, one_smul, hv, inner_self_eq_norm_sq_to_K]
  simp only [cellEigenfunction, norm_smul, Complex.norm_I, one_mul]
  exact (RCLike.ofReal_pow _ _).symm

def periodicWellMass (h : ℝ) : ℝ :=
  h^3 * ∫ x : Space, Well.w (h • x) * ‖cellEigenfunction 0 x‖^2

theorem periodicWellMass_integrable {h : ℝ} (hh : 0 < h) :
    Integrable (fun x : Space => Well.w (h • x) * ‖cellEigenfunction 0 x‖^2) := by
  apply ((scaled_well_integrable hh).mul_const 1024).mono'
  · exact (((Well.w_contDiff.continuous.comp (continuous_const_smul h)).mul
      ((cellEigenfunction_continuous 0).norm.pow 2)).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Well.w_nonneg _) (sq_nonneg _))]
      apply mul_le_mul_of_nonneg_left _ (Well.w_nonneg _)
      nlinarith [cellEigenfunction_norm_le chart_zero x, norm_nonneg (cellEigenfunction 0 x)]

theorem wellFourier_zero : Well.physicalFourier Well.w 0 =
    (fourierNormalization : ℂ) * ((∫ x : Space, Well.w x : ℝ) : ℂ) := by
  rw [Well.physicalFourier, rawPhysicalFourier_eq_integral]
  simp only [angularPhase, neg_zero, inner_zero_left, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero, mul_one]
  rw [_root_.integral_complex_ofReal, Complex.real_smul]
  rfl

theorem periodicWellMass_alias_identity {h : ℝ} (hh : 0 < h) :
    (fourierNormalization : ℂ) *
      (((periodicWellMass h - ∫ x : Space, Well.w x : ℝ) : ℝ) : ℂ) =
      offAliasKernel h 0 0 := by
  have hzero : h * ‖(0 : Space)‖ ≤ 4 * smallRadius := by
    simp only [norm_zero, mul_zero]
    exact mul_nonneg (by norm_num) smallRadius_pos.le
  have hl1 := (scaledFiber_fourier_l1 hh.le 0 hzero).1
  have hg := normalized_blochField_gram hh 0 0 (scaledFiber h 0) (scaledFiber h 0) hl1 hl1
  change ((h^3 * fourierNormalization^2 : ℝ) : ℂ) *
      (∫ x, (Well.w (h • x) : ℂ) *
        inner ℂ (blochField (physicalMomentum (h • 0)) (scaledFiber h 0) x)
          (blochField (physicalMomentum (h • 0)) (scaledFiber h 0) x)) =
      (fourierNormalization : ℂ) * fullAliasKernel h 0 0 at hg
  rw [fullAliasKernel_split hh 0 0 ((mem_aliasChart hh 0).mpr hzero)
    ((mem_aliasChart hh 0).mpr hzero)] at hg
  simp only [smul_zero, scaledFiber_zero] at hg
  simp_rw [zero_bloch_inner] at hg
  simp only [sub_self,
    inner_self_eq_norm_sq_to_K, physicalFiberVector_zero_norm,
    RCLike.ofReal_one, one_pow, one_mul, wellFourier_zero] at hg
  have hi : (∫ x : Space, (Well.w (h • x) : ℂ) * ((‖cellEigenfunction 0 x‖^2 : ℝ) : ℂ)) =
      ((∫ x : Space, Well.w (h • x) * ‖cellEigenfunction 0 x‖^2 : ℝ) : ℂ) := by
    simp only [← Complex.ofReal_mul]
    exact _root_.integral_complex_ofReal
  rw [hi] at hg
  have hc : (fourierNormalization : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by
    unfold fourierNormalization
    positivity)
  apply mul_left_cancel₀ hc
  calc
    _ = ((h^3 * fourierNormalization^2 : ℝ) : ℂ) *
        ((∫ x : Space, Well.w (h • x) * ‖cellEigenfunction 0 x‖^2 : ℝ) : ℂ) -
        (fourierNormalization : ℂ)^2 * ((∫ x : Space, Well.w x : ℝ) : ℂ) := by
      simp only [periodicWellMass, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow]
      ring
    _ = _ := by rw [hg]; ring

end Maxwell.Continuum.EffectiveMass
