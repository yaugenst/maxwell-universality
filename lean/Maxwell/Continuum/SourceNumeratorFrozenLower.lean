import Maxwell.Continuum.SourceNumeratorComparison
import Maxwell.Continuum.SourceNumeratorLeading

/-! Exact identification and positivity of the frozen-cell source
factor for the physical effective-mass envelope. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber CellBandFourier PeriodicBand FiberNormalization

theorem sourceFrozenFactor_reference_identity {h : ℝ} (hh : 0 < h) (β : Space) :
    (sourceScale h : ℂ) * sourceFrozenFactor h (referencePhysicalMode hh)
        (Complex.I • physicalMomentum β) =
      (fourierNormalization : ℂ) * (leadingSourceMass h β : ℂ) := by
  calc
    _ = (fourierNormalization : ℂ) * ∫ x,
        (sourceScale h : ℂ) * (spatialPhase (Complex.I • physicalMomentum β) x *
          bilinear (cellEigenfunction 0 x) (sourceValue h (referencePhysicalMode hh) x)) := by
      rw [sourceFrozenFactor_integral hh, integral_const_mul]
      ring
    _ = _ := by
      congr 1
      rw [leadingSourceMass, ← _root_.integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards [sourceValue_reference_ae hh] with x hx
      rw [hx, sourcePhase_imaginary, map_smul, smul_eq_mul,
        bilinear_self_real _ (cellEigenfunction_real_imaginary chart_zero (by simp) x),
        sourceScale_eq_envelope_factor hh, envelopeOverlapDensity,
        ← envelope_factor_square hh]
      push_cast
      ring

theorem sourceFrozenFactor_reference_real_identity {h : ℝ} (hh : 0 < h) (β : Space) :
    sourceScale h * (sourceFrozenFactor h (referencePhysicalMode hh)
        (Complex.I • physicalMomentum β)).re =
      fourierNormalization * leadingSourceMass h β := by
  have he := congrArg Complex.re (sourceFrozenFactor_reference_identity hh β)
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using he

theorem sourceFrozenFactor_reference_lower {h : ℝ} (hh : 0 < h)
    (hsmall : h ≤ 1 / (2 : ℝ)^1024) {β : Space} (hβ : ‖β‖ ≤ h) :
    1 / (2 : ℝ)^40 ≤ sourceScale h * (sourceFrozenFactor h (referencePhysicalMode hh)
      (Complex.I • physicalMomentum β)).re := by
  rw [sourceFrozenFactor_reference_real_identity]
  have he := mul_le_mul fourierNormalization_lower (leadingSourceMass_lower hh hsmall hβ)
    (by positivity) fourierNormalization_nonneg
  convert he using 1
  norm_num

end Maxwell.Continuum.EffectiveMass
