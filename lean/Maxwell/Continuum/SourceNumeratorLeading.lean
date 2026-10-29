import Maxwell.Continuum.SourceNumeratorPhase
import Maxwell.Continuum.EffectiveMassEnvelopeOverlap

/-! The positive leading source mass at imaginary physical momentum.
All densities are the literal scalar well and periodic cell mode. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber CellBandFourier

theorem envelopeOverlapDensity_nonneg {h : ℝ} (hh : 0 ≤ h) (x : Space) :
    0 ≤ envelopeOverlapDensity h x :=
  mul_nonneg (mul_nonneg (pow_nonneg hh 3)
    (mul_nonneg (Well.qw_nonneg _) (Well.topProfile_nonneg _))) (sq_nonneg _)

theorem envelopeOverlapDensity_supported {h : ℝ} (hh : 0 < h) (x : Space)
    (hx : h⁻¹ ≤ ‖x‖) : envelopeOverlapDensity h x = 0 := by
  have hn : 1 ≤ ‖h • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    calc
      _ = h * h⁻¹ := (mul_inv_cancel₀ hh.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hx hh.le
  have hq := (Well.qw_zero_iff (h • x)).mpr hn
  simp only [envelopeOverlapDensity, hq, zero_mul, mul_zero]

def leadingSourceMass (h : ℝ) (β : Space) : ℝ :=
  ∫ x, Real.exp (-inner ℝ β x) * envelopeOverlapDensity h x

theorem leadingSourceMass_integrable {h : ℝ} (hh : 0 < h)
    {β : Space} (hβ : ‖β‖ ≤ h) :
    Integrable (fun x => Real.exp (-inner ℝ β x) * envelopeOverlapDensity h x) := by
  apply ((envelopeOverlapDensity_integrable hh).const_mul 4).mono'
  · exact ((Real.continuous_exp.comp (continuous_const.inner continuous_id).neg).aestronglyMeasurable.mul
      (envelopeOverlapDensity_integrable hh).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (Real.exp_pos _).le (envelopeOverlapDensity_nonneg hh.le x))]
      by_cases hx : ‖x‖ ≤ h⁻¹
      · exact mul_le_mul_of_nonneg_right (sourcePhase_imaginary_bounds hh hβ hx).2
          (envelopeOverlapDensity_nonneg hh.le x)
      · rw [envelopeOverlapDensity_supported hh x (le_of_not_ge hx), mul_zero, mul_zero]

theorem leadingSourceMass_lower {h : ℝ} (hh : 0 < h)
    (hsmall : h ≤ 1 / (2 : ℝ)^1024) {β : Space} (hβ : ‖β‖ ≤ h) :
    1 / (2 : ℝ)^35 ≤ leadingSourceMass h β := by
  have hm : (1 / 4 : ℝ) * (∫ x, envelopeOverlapDensity h x) ≤ leadingSourceMass h β := by
    have hi := integral_mono ((envelopeOverlapDensity_integrable hh).const_mul (1 / 4))
      (leadingSourceMass_integrable hh hβ) (fun x => by
        by_cases hx : ‖x‖ ≤ h⁻¹
        · exact mul_le_mul_of_nonneg_right (sourcePhase_imaginary_bounds hh hβ hx).1
            (envelopeOverlapDensity_nonneg hh.le x)
        · rw [envelopeOverlapDensity_supported hh x (le_of_not_ge hx), mul_zero, mul_zero])
    rwa [integral_const_mul] at hi
  have hb := rootEnvelope_mode_overlap hh hsmall
  rw [rootEnvelope_mode_inner] at hb
  change 1 / (2 : ℝ)^33 ≤ ∫ x, envelopeOverlapDensity h x at hb
  have hl := (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 1 / 4)).trans hm
  convert hl using 1
  norm_num

theorem sourceScale_eq_envelope_factor {h : ℝ} (hh : 0 < h) :
    sourceScale h = L2Dilation.factor h⁻¹ := by
  have hs : sourceScale h ^ 2 = h^3 := by
    rw [sourceScale, mul_pow, Real.sq_sqrt hh.le]
    ring
  nlinarith only [hs, envelope_factor_square hh, (sourceScale_pos hh).le,
    (L2Dilation.factor_pos (inv_pos.mpr hh)).le]

theorem sourceValue_Qh_ae (h : ℝ) (u : FieldL2) :
    sourceValue h u =ᵐ[volume] fun x => (Well.qw (h • x) : ℂ) • fieldValue u x := by
  filter_upwards [ae_all_iff.mpr (sourceMode_ae h u)] with x hx
  apply PiLp.ext
  intro j
  exact hx j

theorem sourceValue_reference_ae {h : ℝ} (hh : 0 < h) :
    sourceValue h (referencePhysicalMode hh) =ᵐ[volume] fun x =>
      ((L2Dilation.factor h⁻¹ * Well.qw (h • x) * Well.topProfile (h • x) : ℝ) : ℂ) •
        cellEigenfunction 0 x := by
  have ht := L2Dilation.inverse_ae (inv_pos.mpr hh) Well.topVector_ae
  filter_upwards [sourceValue_Qh_ae h (referencePhysicalMode hh),
    fieldValue_envelope_ae hh Well.topVector, ht] with x hq he ht
  change fieldValue (referencePhysicalMode hh) x = _ at he
  simp only [inv_inv] at ht
  rw [hq, he, ht, smul_smul]
  congr 1
  push_cast
  ring

end Maxwell.Continuum.EffectiveMass
