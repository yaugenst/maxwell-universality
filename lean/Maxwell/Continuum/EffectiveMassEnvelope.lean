import Maxwell.Continuum.VectorFieldL2
import Maxwell.Continuum.VectorMultiplier
import Maxwell.Continuum.CellBandFourierReality
import Maxwell.Continuum.EffectiveMassReferenceSpectrum
import Maxwell.Continuum.EffectiveMassWell

/-! Literal spatial effective-mass envelopes and their exact
reconstruction from the scalar reference Gram eigenvector. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber CellBandFourier PeriodicBand
open scoped InnerProduct

def periodicModeData : VectorMultiplier.Data (H := Polarization) (volume : Measure Space) 32 where
  coefficient := cellEigenfunction 0
  measurable := (cellEigenfunction_continuous 0).aestronglyMeasurable
  nonneg := by norm_num
  bound := cellEigenfunction_norm_le chart_zero

def periodicMultiplier : ScalarL2 →L[ℂ] FieldL2 :=
  VectorFieldL2.unpack.comp periodicModeData.operator

theorem periodicMultiplier_ae (f : ScalarL2) (j : Fin 3) :
    periodicMultiplier f j =ᵐ[volume] fun x => f x * cellEigenfunction 0 x j := by
  filter_upwards [VectorFieldL2.unpack_ae (periodicModeData.operator f) j,
    periodicModeData.operator_ae f] with x hp hf
  change VectorFieldL2.unpack (periodicModeData.operator f) j x = _
  rw [hp, hf]
  rfl

theorem periodicMultiplier_norm : ‖periodicMultiplier‖ ≤ 32 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖VectorFieldL2.unpack (periodicModeData.operator f)‖ ≤ _
  rw [VectorFieldL2.unpack_norm]
  exact periodicModeData.operator.le_of_opNorm_le periodicModeData.operator_norm_le f

def envelopeOperator {h : ℝ} (hh : 0 < h) : ScalarL2 →L[ℂ] FieldL2 :=
  periodicMultiplier.comp
    (L2Dilation.equiv (inv_pos.mpr hh)).toContinuousLinearEquiv.toContinuousLinearMap

theorem envelopeOperator_ae {h : ℝ} (hh : 0 < h) (f : ScalarL2) (j : Fin 3) :
    envelopeOperator hh f j =ᵐ[volume] fun x =>
      (L2Dilation.factor h⁻¹ : ℂ) * f (h • x) * cellEigenfunction 0 x j := by
  filter_upwards [periodicMultiplier_ae (L2Dilation.equiv (inv_pos.mpr hh) f) j,
    L2Dilation.equiv_ae (inv_pos.mpr hh) f] with x hp hf
  change periodicMultiplier (L2Dilation.equiv (inv_pos.mpr hh) f) j x = _
  rw [hp, hf]
  simp only [inv_inv, smul_eq_mul]

theorem envelopeOperator_norm {h : ℝ} (hh : 0 < h) : ‖envelopeOperator hh‖ ≤ 32 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖periodicMultiplier (L2Dilation.equiv (inv_pos.mpr hh) f)‖ ≤ _
  exact (periodicMultiplier.le_of_opNorm_le periodicMultiplier_norm _).trans_eq
    (congrArg (fun t : ℝ => 32 * t) ((L2Dilation.equiv (inv_pos.mpr hh)).norm_map f))

theorem envelope_dilation_factor {h : ℝ} (hh : 0 < h) :
    L2Dilation.factor h⁻¹ = h ^ (3 / 2 : ℝ) := by
  rw [L2Dilation.factor, inv_pow, Real.sqrt_inv, inv_inv, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast_mul hh.le]
  norm_num

theorem Qh_envelope {h : ℝ} (hh : 0 < h) (f : ScalarL2) :
    Qh h (envelopeOperator hh f) = envelopeOperator hh (Well.rootProfile.multiplier f) := by
  apply PiLp.ext
  intro j
  apply Lp.ext
  have hr := L2Dilation.inverse_ae (inv_pos.mpr hh) (Well.rootProfile.multiplier_ae f)
  filter_upwards [Qh_ae h (envelopeOperator hh f) j, envelopeOperator_ae hh f j,
    envelopeOperator_ae hh (Well.rootProfile.multiplier f) j, hr] with x hQ he ho hrx
  rw [hQ, he, ho]
  simp only [inv_inv] at hrx
  rw [hrx]
  change (Well.qw (h • x) : ℂ) *
    ((L2Dilation.factor h⁻¹ : ℂ) * f (h • x) * cellEigenfunction 0 x j) =
    (L2Dilation.factor h⁻¹ : ℂ) * ((Well.qw (h • x) : ℂ) * f (h • x)) *
      cellEigenfunction 0 x j
  ring

def referenceReconstruction {h : ℝ} (hh : 0 < h) : ScalarL2 →L[ℂ] FieldL2 :=
  (envelopeOperator hh).comp referenceFactor

def referencePhysicalMode {h : ℝ} (hh : 0 < h) : FieldL2 :=
  envelopeOperator hh Well.topVector

theorem referenceReconstruction_mode {h : ℝ} (hh : 0 < h) :
    referenceReconstruction hh referenceMode =
      (Real.sqrt Well.mu : ℂ) • referencePhysicalMode hh := by
  have he := GramSpectral.vector_image referenceFactor Well.topVector Well.mu_pos
    referenceFactor_well_eigen
  change referenceFactor referenceMode = _ at he
  change envelopeOperator hh (referenceFactor referenceMode) = _
  rw [he, map_smul]
  rfl

theorem referencePhysicalMode_ae {h : ℝ} (hh : 0 < h) (j : Fin 3) :
    referencePhysicalMode hh j =ᵐ[volume] fun x =>
      ((h ^ (3 / 2 : ℝ) : ℝ) : ℂ) * Well.topVector (h • x) * cellEigenfunction 0 x j := by
  simpa only [referencePhysicalMode, envelope_dilation_factor hh] using
    envelopeOperator_ae hh Well.topVector j

end Maxwell.Continuum.EffectiveMass
