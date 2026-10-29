import Maxwell.Continuum.EffectiveMassSpatialApproximation
import Maxwell.Continuum.EffectiveMassEnvelopeReality
import Maxwell.Continuum.FourierConjugationNorm
import Maxwell.Continuum.TopEigenRealPart
import Maxwell.Continuum.EffectiveMassSourceMode

/-! The canonical real continuum mode, with its actual spatial
approximation, isolated-mode gap and zero-extension H¹ estimate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.EffectiveMass

open Auxiliary TopEigenPerturbation EigenTranslation

attribute [local irreducible] complexMode referencePhysicalMode Sh muH Well.gap
  Bloch.unitary Auxiliary.resolvent

theorem complexMode_spatial_error_lt_one {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    ‖complexMode D hh - referencePhysicalMode D.h_pos‖ < 1 := by
  apply lt_of_le_of_lt (complexMode_spatial_error D hh)
  calc
    _ ≤ (2 : ℝ)^920 * (1 / (2 : ℝ)^1024) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ < 1 := by norm_num

theorem modeRealPart_ne_zero {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) : realPart fieldConjugation (complexMode D hh) ≠ 0 :=
  realPart_ne_zero fieldConjugation fieldConjugation_norm (complexMode D hh)
    (referencePhysicalMode D.h_pos) (complexMode_norm D hh)
    (referencePhysicalMode_real D.h_pos) (complexMode_spatial_error_lt_one D hh)

def realMode {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) : FieldL2 := normalizedRealPart fieldConjugation (complexMode D hh)

theorem realModeData {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    Data (Sh D) (realMode D hh) (muH D hh) ((h ^ 2)⁻¹ * (Well.gap / 4)) :=
  (physicalSpectrumData D hh).normalizedRealPart_data fieldConjugation
    (fun f => (Sh_conjugation D f).symm) (modeRealPart_ne_zero D hh)

theorem realMode_norm {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) : ‖realMode D hh‖ = 1 :=
  (realModeData D hh).unit_norm

theorem realMode_real {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) : fieldConjugation (realMode D hh) = realMode D hh :=
  normalizedRealPart_fixed fieldConjugation fieldConjugation_involutive (complexMode D hh)

theorem realMode_eigen {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) : Sh D (realMode D hh) = (muH D hh : ℂ) • realMode D hh :=
  (realModeData D hh).eigenvector

theorem realMode_spatial_error {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    ‖realMode D hh - referencePhysicalMode D.h_pos‖ ≤ (2 : ℝ)^921 * h := by
  have he := normalizedRealPart_error fieldConjugation fieldConjugation_norm
    (complexMode D hh) (referencePhysicalMode D.h_pos) (complexMode_norm D hh)
    (referencePhysicalMode_real D.h_pos) (complexMode_spatial_error_lt_one D hh)
  apply he.trans
  have hb := mul_le_mul_of_nonneg_left (complexMode_spatial_error D hh) (by norm_num : (0 : ℝ) ≤ 2)
  convert hb using 1
  ring

theorem realMode_isolated {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    IsolatedRealMode (Sh D) (muH D hh) (modeGap h) (realMode D hh) where
  unit_norm := realMode_norm D hh
  real := realMode_real D hh
  eigenvector := realMode_eigen D hh
  gap_pos := modeGap_pos D.h_pos
  gap := by
    intro f hf
    have hg : modeGap h ≤ (h ^ 2)⁻¹ * (Well.gap / 4) := by
      rw [modeGap, Well.gap_exact]
      have hc : ((2 : ℝ)^192)⁻¹ ≤ (1 / (2 : ℝ)^188) / 4 := by norm_num
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr (sq_nonneg h))
    exact (mul_le_mul_of_nonneg_right hg (norm_nonneg f)).trans
      ((realModeData D hh).residual_gap f hf)

def realModeH1 {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) : FourierSobolev.H1Data (realMode D hh) :=
  Sh_modeH1 D (realMode_isolated D hh)

theorem realModeH1_norm_le {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    (realModeH1 D hh).norm ≤ (2 : ℝ)^512 * (h ^ 2)⁻¹ :=
  Sh_modeH1_norm_le D (realMode_isolated D hh)

theorem realMode_supported {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure Space),
      h⁻¹ ≤ ‖x‖ → realMode D hh j x = 0 :=
  Sh_eigenvector_supported D (muH_pos D hh).ne' (realMode_eigen D hh) j

end Maxwell.Continuum.EffectiveMass
