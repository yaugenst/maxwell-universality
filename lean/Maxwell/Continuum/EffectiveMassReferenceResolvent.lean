import Maxwell.Continuum.EffectiveMassReferenceScalar
import Maxwell.Continuum.WellPhysical

/-! The square of the actual reference multiplier is precisely the
physical anisotropic scalar resolvent, including the cycles/angular change. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FourierTransform PeriodicBand

theorem referenceDenominator_cycles (p : Space) :
    referenceDenominator p =
      1 + Well.ellipticSymbol hessianOperator ((2 * Real.pi)⁻¹ • p) := by
  change 1 + quadratic p = 1 + (2 * Real.pi)^2 * quadratic ((2 * Real.pi)⁻¹ • p)
  rw [quadratic_smul, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (by positivity :
    (2 * Real.pi : ℝ) ≠ 0), one_pow, one_mul]

theorem referenceMultiplier_square (p : Space) :
    referenceMultiplier p ^ 2 = (referenceDenominator p)⁻¹ := by
  rw [referenceMultiplier, inv_pow, Real.sq_sqrt (referenceDenominator_pos p).le]

theorem referenceSquare_angular (f : ScalarL2) :
    referenceScalarOperator (referenceScalarOperator (angularFourier ℂ f)) =
      angularFourier ℂ (Well.physicalResolvent f) := by
  apply Lp.ext
  have hr := L2Dilation.inverse_ae (a := 2 * Real.pi) (by positivity)
    (Well.resolvent_fourier_ae hessianOperator hessianOperator_nonneg f)
  filter_upwards [referenceScalarOperator_ae (referenceScalarOperator (angularFourier ℂ f)),
    referenceScalarOperator_ae (angularFourier ℂ f), angularFourier_ae ℂ f,
    angularFourier_ae ℂ (Well.physicalResolvent f), hr] with p ho hi hf hrf hrp
  rw [ho, hi, hf, hrf]
  change (𝓕 (Well.physicalResolvent f) : ScalarL2) ((2 * Real.pi)⁻¹ • p) = _ at hrp
  rw [hrp]
  simp only [smul_eq_mul]
  have he : (referenceMultiplier p : ℂ)^2 =
      (((1 + Well.ellipticSymbol hessianOperator ((2 * Real.pi)⁻¹ • p))⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, referenceMultiplier_square, referenceDenominator_cycles]
  rw [← he]
  rw [show Well.scalarFourier f = (𝓕 f : ScalarL2) from rfl]
  ring

theorem referenceSquare_resolvent (f : ScalarL2) :
    (angularFourier ℂ).symm
      (referenceScalarOperator (referenceScalarOperator (angularFourier ℂ f))) =
      Well.physicalResolvent f := by
  rw [referenceSquare_angular, (angularFourier ℂ).symm_apply_apply]

end Maxwell.Continuum.EffectiveMass
