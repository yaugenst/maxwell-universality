import Maxwell.Continuum.EffectiveMassPeriodicMassBound
import Maxwell.Continuum.EffectiveMassEnvelopeReality

/-! Positive overlap for the actual spatial effective-mass envelope.
The periodic averaging and the scalar Perron lower bound are both
applied to their literal representatives. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber CellBandFourier

attribute [local irreducible] cellEigenfunction Well.topProfile L2Dilation.factor

theorem fieldValue_envelope_ae {h : ℝ} (hh : 0 < h) (f : ScalarL2) :
    fieldValue (envelopeOperator hh f) =ᵐ[volume] fun x =>
      ((L2Dilation.factor h⁻¹ : ℂ) * f (h • x)) • cellEigenfunction 0 x := by
  filter_upwards [ae_all_iff.mpr (envelopeOperator_ae hh f)] with x hx
  apply PiLp.ext
  intro j
  exact hx j

theorem envelope_factor_square {h : ℝ} (hh : 0 < h) :
    L2Dilation.factor h⁻¹ ^ 2 = h^3 := by
  rw [L2Dilation.factor, inv_pow, Real.sq_sqrt (by positivity), inv_pow, inv_inv]

def rootEnvelope {h : ℝ} (hh : 0 < h) : FieldL2 := envelopeOperator hh Well.rootVector

theorem rootEnvelope_norm_le {h : ℝ} (hh : 0 < h) : ‖rootEnvelope hh‖ ≤ 96 := by
  exact ((envelopeOperator hh).le_of_opNorm_le (envelopeOperator_norm hh) Well.rootVector).trans
    (by have he := Well.rootVector_norm_le; linarith)

def envelopeOverlapDensity (h : ℝ) (x : Space) : ℝ :=
  h^3 * (Well.qw (h • x) * Well.topProfile (h • x)) * ‖cellEigenfunction 0 x‖^2

theorem realScalar_inner_self (a b : ℝ) (v : Polarization) :
    inner ℂ ((a : ℂ) • v) ((b : ℂ) • v) = ((a * b * ‖v‖^2 : ℝ) : ℂ) := by
  rw [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K]
  change star (a : ℂ) * ((b : ℂ) * (‖v‖ : ℂ)^2) = _
  simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

theorem rootEnvelope_mode_inner_ae {h : ℝ} (hh : 0 < h) :
    (fun x => inner ℂ (fieldValue (rootEnvelope hh) x)
      (fieldValue (referencePhysicalMode hh) x)) =ᵐ[volume]
        fun x => (envelopeOverlapDensity h x : ℂ) := by
  have hr := L2Dilation.inverse_ae (inv_pos.mpr hh) Well.rootVector_ae
  have ht := L2Dilation.inverse_ae (inv_pos.mpr hh) Well.topVector_ae
  filter_upwards [fieldValue_envelope_ae hh Well.rootVector,
    fieldValue_envelope_ae hh Well.topVector, hr, ht] with x hroot htop hrx htx
  change inner ℂ (fieldValue (envelopeOperator hh Well.rootVector) x)
    (fieldValue (envelopeOperator hh Well.topVector) x) = _
  simp only [inv_inv] at hrx htx
  rw [hroot, htop, hrx, htx, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    realScalar_inner_self]
  apply congrArg Complex.ofReal
  unfold envelopeOverlapDensity
  rw [← envelope_factor_square hh]
  ring

theorem envelopeOverlapDensity_integrable {h : ℝ} (hh : 0 < h) :
    Integrable (envelopeOverlapDensity h) := by
  apply ((field_inner_integrable (rootEnvelope hh) (referencePhysicalMode hh)).re).congr
  filter_upwards [rootEnvelope_mode_inner_ae hh] with x hx
  rw [hx]
  rfl

theorem rootEnvelope_mode_inner {h : ℝ} (hh : 0 < h) :
    inner ℂ (rootEnvelope hh) (referencePhysicalMode hh) =
      ((∫ x, envelopeOverlapDensity h x : ℝ) : ℂ) := by
  rw [field_inner_eq_integral, integral_congr_ae (rootEnvelope_mode_inner_ae hh)]
  exact _root_.integral_complex_ofReal

theorem rootEnvelope_mode_overlap {h : ℝ} (hh : 0 < h)
    (hsmall : h ≤ 1 / (2 : ℝ)^1024) :
    1 / (2 : ℝ)^33 ≤ (inner ℂ (rootEnvelope hh) (referencePhysicalMode hh)).re := by
  have hm : (1 / (2 : ℝ)^29) * periodicWellMass h ≤ ∫ x, envelopeOverlapDensity h x := by
    have hi := integral_mono
      ((periodicWellMass_integrable hh).const_mul ((1 / (2 : ℝ)^29) * h^3))
      (envelopeOverlapDensity_integrable hh) (fun x => by
        have hl := mul_le_mul_of_nonneg_left (Well.topProfile_lower (h • x))
          (mul_nonneg (mul_nonneg (pow_nonneg hh.le 3) (Well.qw_nonneg (h • x)))
            (sq_nonneg ‖cellEigenfunction 0 x‖))
        dsimp only [envelopeOverlapDensity]
        rw [← Well.qw_sq (h • x)]
        convert hl using 1 <;> ring)
    rw [integral_const_mul] at hi
    convert hi using 1
    unfold periodicWellMass
    ring
  rw [rootEnvelope_mode_inner]
  change _ ≤ ∫ x, envelopeOverlapDensity h x
  have hp := mul_le_mul_of_nonneg_left (periodicWellMass_lower hh hsmall)
    (by positivity : 0 ≤ 1 / (2 : ℝ)^29)
  norm_num at hp ⊢
  linarith

end Maxwell.Continuum.EffectiveMass
