import Maxwell.Continuum.EffectiveMassReferenceSpectrum
import Maxwell.Continuum.EffectiveMassBandComparison
import Maxwell.Continuum.TopEigenTwoStage
import Maxwell.Continuum.WellPerturbation

/-! The actual scalar packet Gram operator inherits the literal well's
simple top eigenpair. The approximation bound is the proved all-alias
Fourier estimate, not a premise of this construction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.EffectiveMass

open Auxiliary TopEigenPerturbation
open scoped InnerProduct

attribute [local irreducible] Bh bandGramOperator diagonalReferenceOperator
  referenceMode Well.mu Well.gap

def bandPerturbation {h z : ℝ} (D : Calibration h z) : ScalarL2 →L[ℂ] ScalarL2 :=
  TwoStage.gramError (A := diagonalReferenceOperator) (Bh D)

theorem bandPerturbation_eq {h z : ℝ} (D : Calibration h z) :
    bandPerturbation D = bandGramOperator D - diagonalReferenceOperator := by
  unfold bandPerturbation TwoStage.gramError bandGramOperator
  rfl

theorem bandPerturbation_norm {h z : ℝ} (D : Calibration h z) :
    ‖bandPerturbation D‖ ≤ (2 : ℝ)^520 * h := by
  rw [bandPerturbation_eq]
  exact bandGram_effectiveMass_error_paper D

theorem bandPerturbation_small {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) : ‖bandPerturbation D‖ ≤ Well.gap / 64 := by
  calc
    _ ≤ (2 : ℝ)^520 * h := bandPerturbation_norm D
    _ ≤ (2 : ℝ)^520 * (1 / (2 : ℝ)^1024) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ Well.gap / 64 := by
      rw [Well.gap_exact]
      have hp : (2 : ℝ)^714 ≤ (2 : ℝ)^1024 :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have he : (2 : ℝ)^520 * (1 / (2 : ℝ)^1024) ≤ 1 / (2 : ℝ)^194 := by
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 194)).mpr
        rw [mul_assoc, mul_comm (1 / (2 : ℝ)^1024), ← mul_assoc, ← pow_add]
        simpa only [one_div, div_eq_mul_inv, one_mul] using (div_le_one (by positivity)).mpr hp
      exact he.trans (by norm_num)

def bandEigenvalue {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1 / (2 : ℝ)^1024) : ℝ :=
  TwoStage.gramValue referencePerturbationData (Bh D) (bandPerturbation_small D hh)

def bandMode {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1 / (2 : ℝ)^1024) : ScalarL2 :=
  TwoStage.gramVector referencePerturbationData (Bh D) (bandPerturbation_small D hh)

theorem bandSpectrumData {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1 / (2 : ℝ)^1024) :
    Data (bandGramOperator D) (bandMode D hh) (bandEigenvalue D hh) (Well.gap / 2) := by
  unfold bandGramOperator
  exact TwoStage.gramData referencePerturbationData diagonalReference_positive (Bh D)
    (bandPerturbation_small D hh)

theorem bandEigenvalue_error {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    |bandEigenvalue D hh - Well.mu| ≤ 4 * ‖bandPerturbation D‖ :=
  TwoStage.gramValue_error referencePerturbationData (Bh D) (bandPerturbation_small D hh)

theorem bandMode_error {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    ‖bandMode D hh - referenceMode‖ ≤ 4 * ‖bandPerturbation D‖ / Well.gap :=
  referencePerturbationData.vector_error (bandPerturbation D) (bandPerturbation_small D hh)

section
attribute [local irreducible] bandEigenvalue bandPerturbation

theorem well_window_bounds {v m r : ℝ} (he : |v - m| ≤ r)
    (hr : r ≤ 1 / (2 : ℝ)^190) (hl : 1 / (2 : ℝ)^127 ≤ m)
    (hu : m ≤ 1 / (2 : ℝ)^92) :
    1 / (2 : ℝ)^128 ≤ v ∧ v ≤ 1 / (2 : ℝ)^91 := by
  have ha := abs_le.mp he
  norm_num at hr hl hu ⊢
  constructor <;> linarith

theorem bandEigenvalue_bounds {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    1 / (2 : ℝ)^128 ≤ bandEigenvalue D hh ∧ bandEigenvalue D hh ≤ 1 / (2 : ℝ)^91 := by
  apply well_window_bounds (bandEigenvalue_error D hh) _
    Well.mu_lower_numeric Well.mu_upper_numeric
  calc
    _ ≤ 4 * (Well.gap / 64) := mul_le_mul_of_nonneg_left
      (bandPerturbation_small D hh) (by norm_num)
    _ ≤ 1 / (2 : ℝ)^190 := by rw [Well.gap_exact]; norm_num

end

def reconstructedMode {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) : FieldL2 :=
  TwoStage.fieldVector referencePerturbationData (Bh D) (bandPerturbation_small D hh)

theorem reconstructedMode_eq {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    reconstructedMode D hh = ((Real.sqrt (bandEigenvalue D hh))⁻¹ : ℂ) •
      Bh D (bandMode D hh) := by
  simp only [reconstructedMode, TwoStage.fieldVector, GramSpectral.vector,
    ContinuousLinearMap.adjoint_adjoint, bandEigenvalue, bandMode]

theorem reconstructedSpectrumData {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    Data ((Bh D).comp ((Bh D)†)) (reconstructedMode D hh) (bandEigenvalue D hh) (Well.gap / 2) :=
  TwoStage.fieldData referencePerturbationData diagonalReference_positive (Bh D)
    (bandPerturbation_small D hh)

end Maxwell.Continuum.EffectiveMass
