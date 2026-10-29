import Maxwell.Continuum.EffectiveMassPerturbationBasic
import Maxwell.Continuum.EffectiveMassAuxiliaryDecomposition

/-! The actual two-stage effective-mass eigenpair for the continuum
auxiliary well operator. Every approximation estimate is discharged by
the literal Fourier/Bloch construction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.EffectiveMass

open Auxiliary TopEigenPerturbation
open scoped InnerProduct

attribute [local irreducible] Bh bandGramOperator diagonalReferenceOperator
  referenceMode Well.mu Well.gap Sh Bloch.unitary Auxiliary.resolvent

def scaledAuxiliary {h z : ℝ} (D : Calibration h z) : FieldL2 →L[ℂ] FieldL2 :=
  (h ^ 2 : ℂ) • Sh D

theorem scaledAuxiliary_symmetric {h z : ℝ} (D : Calibration h z) :
    (scaledAuxiliary D).IsSymmetric :=
  ((show IsSelfAdjoint (h ^ 2 : ℂ) by simp [IsSelfAdjoint]).smul
    (Sh_selfAdjoint D)).isSymmetric

def auxiliaryPerturbation {h z : ℝ} (D : Calibration h z) : FieldL2 →L[ℂ] FieldL2 :=
  TwoStage.fieldError (Bh D) (scaledAuxiliary D)

theorem auxiliaryPerturbation_eq {h z : ℝ} (D : Calibration h z) :
    auxiliaryPerturbation D = (h ^ 2 : ℂ) • Sh D - (Bh D).comp ((Bh D)†) := by
  unfold auxiliaryPerturbation TwoStage.fieldError scaledAuxiliary
  rfl

theorem auxiliaryPerturbation_norm {h z : ℝ} (D : Calibration h z) :
    ‖auxiliaryPerturbation D‖ ≤ (2 : ℝ)^112 * h ^ 2 := by
  rw [auxiliaryPerturbation_eq]
  exact Sh_band_difference_norm_le D

theorem auxiliaryPerturbation_small {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) : ‖auxiliaryPerturbation D‖ ≤ (Well.gap / 2) / 64 := by
  have hh2 : h ^ 2 ≤ h := by nlinarith [calibration_h_small D, D.h_pos]
  calc
    _ ≤ (2 : ℝ)^112 * h ^ 2 := auxiliaryPerturbation_norm D
    _ ≤ (2 : ℝ)^112 * h :=
      mul_le_mul_of_nonneg_left hh2 (by positivity)
    _ ≤ (2 : ℝ)^112 * (1 / (2 : ℝ)^1024) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ (Well.gap / 2) / 64 := by
      rw [Well.gap_exact]
      have hp : (2 : ℝ)^307 ≤ (2 : ℝ)^1024 :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have he : (2 : ℝ)^112 * (1 / (2 : ℝ)^1024) ≤ 1 / (2 : ℝ)^195 := by
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 195)).mpr
        rw [mul_assoc, mul_comm (1 / (2 : ℝ)^1024), ← mul_assoc, ← pow_add]
        simpa only [one_div, div_eq_mul_inv, one_mul] using (div_le_one (by positivity)).mpr hp
      exact he.trans (by norm_num)

end Maxwell.Continuum.EffectiveMass
