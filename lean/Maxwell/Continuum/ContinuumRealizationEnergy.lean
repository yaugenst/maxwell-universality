import Maxwell.Continuum.ContinuumRealizationParameters
import Maxwell.Continuum.EdgeCertifiedBisection
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.Real.Pi.Bounds

/-! A literal rational reference energy from the certified edge algorithm,
with the actual continuum calibration error and material range proved. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

namespace Maxwell.Continuum.RealizationParameters

open MasterConstants Auxiliary PeriodicBand FreeFiber
attribute [local irreducible] Cs exponent Ls Parameters.sourceInput scaledBand

theorem centerEnergy_abs : |centerEnergy| ≤ 1/2 := by
  have hs : |(scaledBand 0).re| ≤ 3 :=
    (Complex.abs_re_le_norm (scaledBand 0)).trans (scaledBand_norm_le chart_zero)
  have hρ : backgroundAmplitude ≤ 1/100 := by norm_num [backgroundAmplitude]
  have hp : |backgroundAmplitude*(scaledBand 0).re| ≤ 3/100 := by
    rw [abs_mul, abs_of_pos backgroundAmplitude_pos]
    exact (mul_le_mul_of_nonneg_left hs backgroundAmplitude_pos.le).trans
      (by nlinarith only [hρ])
  have he : centerEnergy = 3*Real.pi^2/4-7+backgroundAmplitude*(scaledBand 0).re := by
    simp only [centerEnergy, dielectricBand_formula, unscale, smul_zero,
      Complex.add_re, Complex.sub_re, Complex.ofReal_re,
      Complex.re_ofNat, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [he, abs_le]
  have hπlo := Real.pi_gt_three
  have hπhi := Real.pi_lt_d2
  have hplo := (abs_le.mp hp).1
  have hphi := (abs_le.mp hp).2
  constructor <;> nlinarith only [hπlo, hπhi, hplo, hphi]

theorem calibration_energy_abs {h z : ℝ} (D : Auxiliary.Calibration h z) : |z| ≤ 1 := by
  have hh := calibration_h_small D
  have h2 : h^2 ≤ 1/16 := by nlinarith only [D.h_pos, hh]
  have h4 : h^4 ≤ 1/256 := by nlinarith only [h2, sq_nonneg h, sq_nonneg (h^2-1/16)]
  have he := abs_le.mp D.error
  have hc := abs_le.mp centerEnergy_abs
  rw [abs_le]
  constructor <;> nlinarith only [he.1, he.2, hc.1, hc.2, h2, h4, sq_nonneg h]

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)

def energyPrecision : ℕ := 4*(length p S hm).bits.length+8

def energy : ℚ := (Calibration.calibratedEdge (energyPrecision p S hm)).center-
  (length p S hm : ℚ)⁻¹^2

theorem energy_precision_error : (1/2 : ℝ)^(energyPrecision p S hm) ≤
    (length p S hm : ℝ)⁻¹^4/256 := by
  have hn : length p S hm ≤ 2^(length p S hm).bits.length := by
    rw [Nat.size_eq_bits_len]
    exact (Nat.lt_size_self _).le
  have hL : (0 : ℝ) < length p S hm := by exact_mod_cast length_pos p S hm
  have hpow : (length p S hm : ℝ) ≤ (2 : ℝ)^(length p S hm).bits.length := by exact_mod_cast hn
  have hi : (1/2 : ℝ)^(length p S hm).bits.length ≤ (length p S hm : ℝ)⁻¹ := by
    rw [one_div, inv_pow]
    exact (inv_le_inv₀ (by positivity) hL).mpr hpow
  have hh := pow_le_pow_left₀ (by positivity) hi 4
  calc
    (1/2 : ℝ)^(energyPrecision p S hm) =
        ((1/2 : ℝ)^(length p S hm).bits.length)^4/256 := by
      rw [energyPrecision, pow_add, show 4*(length p S hm).bits.length =
        (length p S hm).bits.length*4 by omega, pow_mul]
      norm_num only [show (1/2 : ℝ)^8 = 1/256 by norm_num]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hh (by norm_num)

theorem energy_error : |(energy p S hm : ℝ)-
    (centerEnergy-(length p S hm : ℝ)⁻¹^2)| ≤ (length p S hm : ℝ)⁻¹^4/256 := by
  have h := Calibration.calibratedEdge_contains (energyPrecision p S hm)
  change |centerEnergy-((Calibration.calibratedEdge (energyPrecision p S hm)).center : ℝ)| ≤
    (((1/2 : ℚ)^(energyPrecision p S hm) : ℚ) : ℝ) at h
  have hh : |((Calibration.calibratedEdge (energyPrecision p S hm)).center : ℝ)-centerEnergy| ≤
      (1/2 : ℝ)^(energyPrecision p S hm) := by
    simpa only [abs_sub_comm, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  rw [energy]
  simp only [Rat.cast_sub, Rat.cast_pow, Rat.cast_inv, Rat.cast_natCast, sub_sub_sub_cancel_right]
  exact hh.trans (energy_precision_error p S hm)

theorem energyCalibration : Auxiliary.Calibration (length p S hm : ℝ)⁻¹ (energy p S hm) :=
  calibration_of_length (length_master p S hm)
    ((energy_error p S hm).trans (div_le_self (by positivity) (by norm_num)))

theorem energy_abs : |(energy p S hm : ℝ)| ≤ 1 := calibration_energy_abs (energyCalibration p S hm)

#print axioms centerEnergy_abs
#print axioms energy_error
#print axioms energyCalibration

end Maxwell.Continuum.RealizationParameters
