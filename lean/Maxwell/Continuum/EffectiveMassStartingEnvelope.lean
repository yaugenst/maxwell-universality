import Maxwell.Continuum.EffectiveMassEnvelopeOverlap
import Maxwell.Continuum.CellBandFourierReference

/-! The literal sine/cosine starting field and its distance to the
actual periodic-band envelope. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber CellBandFourier PeriodicBand

attribute [local irreducible] cellEigenfunction referenceField

theorem referenceField_continuous : Continuous referenceField := by
  have he : referenceField = fun x => Complex.I • antiperiodicField CornerBridge.topState.val x :=
    funext referenceField_eq_fourier
  rw [he]
  exact (continuous_const : Continuous (fun _ : Space => Complex.I)).smul
    (antiperiodicField_continuous _)

theorem referenceField_norm_le (x : Space) : ‖referenceField x‖ ≤ 33 := by
  have hc : (2 : ℝ)^16 * backgroundAmplitude ≤ 1 := by norm_num [backgroundAmplitude]
  have he : ‖referenceField x - cellEigenfunction 0 x‖ ≤ 1 := by
    rw [norm_sub_rev]
    exact (cellEigenfunction_zero_pointwise_reference x).trans hc
  calc
    _ ≤ ‖referenceField x - cellEigenfunction 0 x‖ + ‖cellEigenfunction 0 x‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ 1 + 32 := add_le_add he (cellEigenfunction_norm_le chart_zero x)
    _ = _ := by norm_num

def startingModeData : VectorMultiplier.Data (H := Polarization) (volume : Measure Space) 33 where
  coefficient := referenceField
  measurable := referenceField_continuous.aestronglyMeasurable
  nonneg := by norm_num
  bound := referenceField_norm_le

def startingEnvelope {h : ℝ} (hh : 0 < h) : FieldL2 :=
  VectorFieldL2.unpack (startingModeData.operator
    (L2Dilation.equiv (inv_pos.mpr hh) Well.rootVector))

theorem startingEnvelope_norm_le {h : ℝ} (hh : 0 < h) : ‖startingEnvelope hh‖ ≤ 99 := by
  rw [startingEnvelope, VectorFieldL2.unpack_norm]
  have he := startingModeData.operator.le_of_opNorm_le startingModeData.operator_norm_le
    (L2Dilation.equiv (inv_pos.mpr hh) Well.rootVector)
  rw [(L2Dilation.equiv (inv_pos.mpr hh)).norm_map] at he
  exact he.trans (by
    have hr := mul_le_mul_of_nonneg_left Well.rootVector_norm_le (by norm_num : (0 : ℝ) ≤ 33)
    convert hr using 1
    norm_num)

theorem startingEnvelope_ae {h : ℝ} (hh : 0 < h) (j : Fin 3) :
    startingEnvelope hh j =ᵐ[volume] fun x =>
      ((h ^ (3 / 2 : ℝ) * Well.qw (h • x) : ℝ) : ℂ) * referenceField x j := by
  have hr := L2Dilation.inverse_ae (inv_pos.mpr hh) Well.rootVector_ae
  filter_upwards [VectorFieldL2.unpack_ae (startingModeData.operator
      (L2Dilation.equiv (inv_pos.mpr hh) Well.rootVector)) j,
    startingModeData.operator_ae (L2Dilation.equiv (inv_pos.mpr hh) Well.rootVector),
    L2Dilation.equiv_ae (inv_pos.mpr hh) Well.rootVector, hr] with x hu hs hd hrx
  change VectorFieldL2.unpack (startingModeData.operator
    (L2Dilation.equiv (inv_pos.mpr hh) Well.rootVector)) j x = _
  rw [hu, hs, hd]
  simp only [inv_inv] at hrx ⊢
  rw [hrx, envelope_dilation_factor hh]
  change (((h ^ (3 / 2 : ℝ) : ℝ) : ℂ) * (Well.qw (h • x) : ℂ)) * referenceField x j = _
  rw [Complex.ofReal_mul]

theorem startingEnvelope_root_error {h : ℝ} (hh : 0 < h) :
    ‖startingEnvelope hh - rootEnvelope hh‖ ≤ 3 * (2 : ℝ)^16 * backgroundAmplitude := by
  have he := startingModeData.operator_difference_norm periodicModeData
    (mul_nonneg (by positivity : 0 ≤ (2 : ℝ)^16) backgroundAmplitude_pos.le)
    (fun x => by
      dsimp only [startingModeData, periodicModeData]
      change ‖referenceField x - cellEigenfunction 0 x‖ ≤ _
      rw [norm_sub_rev]
      exact cellEigenfunction_zero_pointwise_reference x)
  change ‖VectorFieldL2.unpack (startingModeData.operator
      (L2Dilation.equiv (inv_pos.mpr hh) Well.rootVector)) -
    VectorFieldL2.unpack (periodicModeData.operator
      (L2Dilation.equiv (inv_pos.mpr hh) Well.rootVector))‖ ≤ _
  rw [← map_sub, VectorFieldL2.unpack_norm]
  have h := (startingModeData.operator - periodicModeData.operator).le_of_opNorm_le he
    (L2Dilation.equiv (inv_pos.mpr hh) Well.rootVector)
  rw [(L2Dilation.equiv (inv_pos.mpr hh)).norm_map] at h
  exact h.trans (by
    have hr := mul_le_mul_of_nonneg_left Well.rootVector_norm_le
      (mul_nonneg (by positivity : 0 ≤ (2 : ℝ)^16) backgroundAmplitude_pos.le)
    nlinarith only [hr])

end Maxwell.Continuum.EffectiveMass
