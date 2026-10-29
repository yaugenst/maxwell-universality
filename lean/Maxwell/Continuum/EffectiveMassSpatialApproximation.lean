import Maxwell.Continuum.EffectiveMassReconstruction
import Maxwell.Continuum.EffectiveMassPerturbation
import Maxwell.Continuum.NormalizedReconstruction

/-! Spatial approximation for the actual continuum eigenvector, derived
from the two concrete Gram comparisons and the physical reconstruction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace Maxwell.Continuum.EffectiveMass

open Auxiliary

attribute [local irreducible] Bh bandEigenvalue bandMode bandPerturbation
  reconstructedMode complexMode auxiliaryPerturbation referenceMode Well.mu Well.gap
  referenceReconstruction referenceScalarOperator angularFourier envelopeOperator

theorem referenceReconstruction_norm {h : ℝ} (hh : 0 < h) :
    ‖referenceReconstruction hh‖ ≤ 32 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  rw [referenceReconstruction_apply]
  calc
    _ ≤ 32 * ‖Well.rootProfile.multiplier
        ((angularFourier ℂ).symm (referenceScalarOperator f))‖ :=
      (envelopeOperator hh).le_of_opNorm_le (envelopeOperator_norm hh) _
    _ ≤ 32 * ‖(angularFourier ℂ).symm (referenceScalarOperator f)‖ :=
      mul_le_mul_of_nonneg_left (Well.rootProfile.multiplier_apply_norm_le _) (by norm_num)
    _ = 32 * ‖referenceScalarOperator f‖ := by rw [(angularFourier ℂ).symm.norm_map]
    _ ≤ _ := by
      have hs : ‖referenceScalarOperator f‖ ≤ ‖f‖ := by
        rw [referenceScalarOperator]
        exact referenceProfile.multiplier_apply_norm_le f
      exact mul_le_mul_of_nonneg_left hs (by norm_num)

theorem referencePhysicalMode_norm_le {h : ℝ} (hh : 0 < h) :
    ‖referencePhysicalMode hh‖ ≤ 32 := by
  rw [referencePhysicalMode]
  have he := (envelopeOperator hh).le_of_opNorm_le (envelopeOperator_norm hh) Well.topVector
  simpa only [Well.topVector_norm, mul_one] using he

theorem referenceMode_normalized_reconstruction {h : ℝ} (hh : 0 < h) :
    ((Real.sqrt Well.mu)⁻¹ : ℂ) • referenceReconstruction hh referenceMode =
      referencePhysicalMode hh := by
  rw [referenceReconstruction_mode, smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Well.mu_pos).ne'), one_smul]

theorem bandMode_error_numeric {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    ‖bandMode D hh - referenceMode‖ ≤ (2 : ℝ)^710 * h := by
  calc
    _ ≤ 4 * ‖bandPerturbation D‖ / Well.gap := bandMode_error D hh
    _ ≤ 4 * ((2 : ℝ)^520 * h) / Well.gap :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (bandPerturbation_norm D) (by norm_num)) Well.gap_pos.le
    _ = _ := by rw [Well.gap_exact]; ring

theorem reconstructedMode_spatial_error {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    ‖reconstructedMode D hh - referencePhysicalMode D.h_pos‖ ≤ (2 : ℝ)^913 * h := by
  have hv := (bandEigenvalue_bounds D hh).1
  have hμ : 1 / (2 : ℝ)^128 ≤ Well.mu :=
    le_trans (by norm_num) Well.mu_lower_numeric
  have ha : 0 < bandEigenvalue D hh := lt_of_lt_of_le (by positivity) hv
  have hi := inv_sqrt_window_bound hv
  have hd := inv_sqrt_window_lipschitz hv hμ
  have he := normalized_image_error (Bh D) (referenceReconstruction D.h_pos)
    (bandMode D hh) referenceMode (b := Well.mu) ha
  rw [← reconstructedMode_eq, referenceMode_normalized_reconstruction] at he
  have hr : ‖referenceReconstruction D.h_pos referenceMode‖ ≤ 32 := by
    simpa only [referenceMode_norm, mul_one] using
      (referenceReconstruction D.h_pos).le_of_opNorm_le
        (referenceReconstruction_norm D.h_pos) referenceMode
  have hinside : ‖Bh D‖ * ‖bandMode D hh - referenceMode‖ +
      ‖Bh D - referenceReconstruction D.h_pos‖ * ‖referenceMode‖ ≤ (2 : ℝ)^712 * h := by
    have hm := mul_le_mul (Bh_norm D) (bandMode_error_numeric D hh)
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    rw [referenceMode_norm, mul_one]
    exact (add_le_add hm (Bh_reconstruction_error D)).trans (by nlinarith only [D.h_pos])
  have heigen : |bandEigenvalue D hh - Well.mu| ≤ (2 : ℝ)^522 * h := by
    have hm := (bandEigenvalue_error D hh).trans
      (mul_le_mul_of_nonneg_left (bandPerturbation_norm D) (by norm_num))
    convert hm using 1
    ring
  have hdiff : |(Real.sqrt (bandEigenvalue D hh))⁻¹ - (Real.sqrt Well.mu)⁻¹| ≤
      (2 : ℝ)^722 * h := by
    apply hd.trans
    have hm := mul_le_mul_of_nonneg_left heigen (by positivity : 0 ≤ (2 : ℝ)^200)
    convert hm using 1
    ring
  have hfirst := mul_le_mul hi hinside
    (add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (by positivity : 0 ≤ (2 : ℝ)^200)
  have hsecond := mul_le_mul hdiff hr (norm_nonneg _)
    (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) 722) D.h_pos.le)
  calc
    _ ≤ _ := he
    _ ≤ (2 : ℝ)^200 * ((2 : ℝ)^712 * h) + ((2 : ℝ)^722 * h) * 32 :=
      add_le_add hfirst hsecond
    _ ≤ _ := by nlinarith only [D.h_pos]

theorem complexMode_spatial_error {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    ‖complexMode D hh - referencePhysicalMode D.h_pos‖ ≤ (2 : ℝ)^920 * h := by
  have hh1 : h ≤ 1 := (calibration_h_small D).trans (by norm_num)
  have hs : h^2 ≤ h := by nlinarith only [D.h_pos, hh1]
  have ha : ‖complexMode D hh - reconstructedMode D hh‖ ≤ (2 : ℝ)^303 * h := by
    calc
      _ ≤ 8 * ‖auxiliaryPerturbation D‖ / Well.gap := complexMode_reconstruction_error D hh
      _ ≤ 8 * ((2 : ℝ)^112 * h^2) / Well.gap :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (auxiliaryPerturbation_norm D) (by norm_num)) Well.gap_pos.le
      _ = (2 : ℝ)^303 * h^2 := by rw [Well.gap_exact]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
  have ht := norm_add_le (complexMode D hh - reconstructedMode D hh)
    (reconstructedMode D hh - referencePhysicalMode D.h_pos)
  rw [sub_add_sub_cancel] at ht
  apply ht.trans
  have hb := add_le_add ha (reconstructedMode_spatial_error D hh)
  exact hb.trans (by nlinarith only [D.h_pos])

end Maxwell.Continuum.EffectiveMass
