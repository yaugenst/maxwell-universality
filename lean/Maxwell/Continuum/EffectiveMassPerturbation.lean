import Maxwell.Continuum.EffectiveMassAuxiliaryPerturbation

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

def scaledEigenvalue {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) : ℝ :=
  TwoStage.finalValue referencePerturbationData diagonalReference_positive (Bh D)
    (bandPerturbation_small D hh) (scaledAuxiliary D) (auxiliaryPerturbation_small D hh)

def complexMode {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) : FieldL2 :=
  TwoStage.finalVector referencePerturbationData diagonalReference_positive (Bh D)
    (bandPerturbation_small D hh) (scaledAuxiliary D) (auxiliaryPerturbation_small D hh)

theorem scaledSpectrumData {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    Data (scaledAuxiliary D) (complexMode D hh) (scaledEigenvalue D hh) (Well.gap / 4) :=
  TwoStage.finalData referencePerturbationData diagonalReference_positive (Bh D)
    (bandPerturbation_small D hh) (scaledAuxiliary D) (scaledAuxiliary_symmetric D)
    (auxiliaryPerturbation_small D hh)

theorem scaledEigenvalue_error {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    |scaledEigenvalue D hh - Well.mu| ≤
      4 * ‖bandPerturbation D‖ + 4 * ‖auxiliaryPerturbation D‖ :=
  TwoStage.finalValue_error referencePerturbationData diagonalReference_positive (Bh D)
    (bandPerturbation_small D hh) (scaledAuxiliary D) (scaledAuxiliary_symmetric D)
    (auxiliaryPerturbation_small D hh)

theorem scaledEigenvalue_bounds {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    1 / (2 : ℝ)^128 ≤ scaledEigenvalue D hh ∧
      scaledEigenvalue D hh ≤ 1 / (2 : ℝ)^91 := by
  apply well_window_bounds (scaledEigenvalue_error D hh) _
    Well.mu_lower_numeric Well.mu_upper_numeric
  calc
    _ ≤ 4 * (Well.gap / 64) + 4 * ((Well.gap / 2) / 64) :=
      add_le_add (mul_le_mul_of_nonneg_left (bandPerturbation_small D hh) (by norm_num))
        (mul_le_mul_of_nonneg_left (auxiliaryPerturbation_small D hh) (by norm_num))
    _ ≤ 1 / (2 : ℝ)^190 := by rw [Well.gap_exact]; norm_num

theorem complexMode_reconstruction_error {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    ‖complexMode D hh - reconstructedMode D hh‖ ≤
      8 * ‖auxiliaryPerturbation D‖ / Well.gap :=
  TwoStage.finalVector_error referencePerturbationData diagonalReference_positive (Bh D)
    (bandPerturbation_small D hh) (scaledAuxiliary D) (auxiliaryPerturbation_small D hh)

def muH {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1 / (2 : ℝ)^1024) : ℝ :=
  (h ^ 2)⁻¹ * scaledEigenvalue D hh

theorem physicalSpectrumData {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    Data (Sh D) (complexMode D hh) (muH D hh) ((h ^ 2)⁻¹ * (Well.gap / 4)) := by
  have hd := (scaledSpectrumData D hh).positive_scale (inv_pos.mpr (sq_pos_of_pos D.h_pos))
  have he : (((h ^ 2)⁻¹ : ℝ) : ℂ) • scaledAuxiliary D = Sh D := by
    rw [scaledAuxiliary, smul_smul, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      inv_mul_cancel₀ (sq_pos_of_pos D.h_pos).ne', Complex.ofReal_one, one_smul]
  rwa [he] at hd

theorem muH_bounds {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    (1 / (2 : ℝ)^128) * (h ^ 2)⁻¹ ≤ muH D hh ∧
      muH D hh ≤ (1 / (2 : ℝ)^90) * (h ^ 2)⁻¹ := by
  have hb := scaledEigenvalue_bounds D hh
  constructor
  · simpa only [muH, mul_comm] using
      mul_le_mul_of_nonneg_left hb.1 (inv_nonneg.mpr (sq_nonneg h))
  · have hu : scaledEigenvalue D hh ≤ 1 / (2 : ℝ)^90 := hb.2.trans (by norm_num)
    simpa only [muH, mul_comm] using
      mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr (sq_nonneg h))

theorem muH_pos {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) : 0 < muH D hh :=
  lt_of_lt_of_le (mul_pos (by positivity) (inv_pos.mpr (sq_pos_of_pos D.h_pos)))
    (muH_bounds D hh).1

theorem muH_mem_spectrum {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) : (muH D hh : ℂ) ∈ spectrum ℂ (Sh D) :=
  (physicalSpectrumData D hh).mem_spectrum

theorem muH_spectrum_gap {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (w : ℂ)
    (hw : w ∈ spectrum ℂ (Sh D)) (hne : w ≠ (muH D hh : ℂ)) :
    (1 / (2 : ℝ)^192) * (h ^ 2)⁻¹ ≤ dist w (muH D hh : ℂ) := by
  apply le_trans _ ((physicalSpectrumData D hh).actual_spectrum_gap w hw hne)
  rw [Well.gap_exact]
  have hn : (1 / (2 : ℝ)^192) ≤ (1 / (2 : ℝ)^188) / 4 := by norm_num
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr (sq_nonneg h))

theorem muH_largest {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (t : ℝ) (ht : (t : ℂ) ∈ spectrum ℂ (Sh D)) :
    t ≤ muH D hh := by
  by_cases he : t = muH D hh
  · exact he.le
  · have hn : (t : ℂ) ≠ (muH D hh : ℂ) := by exact_mod_cast he
    have hb := (physicalSpectrumData D hh).spectrum_remainder_norm (t : ℂ) ht hn
    rw [Complex.norm_real, Real.norm_eq_abs] at hb
    exact (le_abs_self t).trans (hb.trans (sub_le_self _ (physicalSpectrumData D hh).gap_pos.le))

theorem complexMode_norm {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) : ‖complexMode D hh‖ = 1 :=
  (physicalSpectrumData D hh).unit_norm

theorem complexMode_eigen {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    Sh D (complexMode D hh) = (muH D hh : ℂ) • complexMode D hh :=
  (physicalSpectrumData D hh).eigenvector

theorem complexMode_simple {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (f : FieldL2)
    (hf : Sh D f = (muH D hh : ℂ) • f) :
    f = inner ℂ (complexMode D hh) f • complexMode D hh :=
  (physicalSpectrumData D hh).eigenvector_simple f hf

end Maxwell.Continuum.EffectiveMass
