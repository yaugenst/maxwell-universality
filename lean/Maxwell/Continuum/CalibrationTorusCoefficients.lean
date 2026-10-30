import Maxwell.Continuum.CalibrationTorusSymbol
import Maxwell.Continuum.CalibrationCellDecay
import Maxwell.Continuum.CalibrationImageGeometry
import Maxwell.Continuum.CalibrationImageTail

/-! Exact cell-block Fourier coefficients and their full lattice
summability for the actual continuum cutoff resolvent. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration

open Auxiliary Bloch CellGauge CellBandFourier MasterConstants UnitAddTorus

local instance torusCoefficientRealSpace : NormedSpace ℝ CellMap := NormedSpace.complexToReal

theorem latticeShift_difference (a b : Bloch.Alias) :
    latticeShift b-latticeShift a = latticeShift (b-a) := by
  apply PiLp.ext
  intro i
  simp only [latticeShift, PiLp.sub_apply, PiLp.smul_apply, integerVector_apply, Pi.sub_apply,
    Int.cast_sub, smul_eq_mul]
  ring

theorem resolventCellBlock_coefficient {h z σ : ℝ} (D : Auxiliary.Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (a b : Bloch.Alias) :
    resolventCellBlock D hσ0 hσ a b =
      ((8 : ℂ)*carrier (latticeShift a-latticeShift b)) •
        mFourierCoeff (torusCellSymbol D hσ0 hσ) (b-a) := by
  rw [resolventCellBlock_eq, torusCellSymbol_coefficient]
  simp only [latticeShift_difference]
  change (((64*blochDensity : ℝ) : ℂ)*carrier (latticeShift (a-b))) •
      OperatorFourier.angularFourier (cutoffFullCellSymbol z σ) (latticeShift (b-a)) =
    (8*carrier (latticeShift (a-b))) • ((((Real.pi^3)⁻¹ : ℝ) : ℂ) •
      OperatorFourier.angularFourier (cutoffFullCellSymbol z σ) (latticeShift (b-a)))
  rw [smul_smul]
  congr 1
  unfold blochDensity
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

theorem torusCellSymbol_coefficient_norm {h z σ : ℝ} (D : Auxiliary.Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (n : Bloch.Alias) :
    8*‖mFourierCoeff (torusCellSymbol D hσ0 hσ) n‖ = ‖resolventCellBlock D hσ0 hσ 0 n‖ := by
  rw [resolventCellBlock_coefficient, sub_zero, norm_smul, norm_mul, carrier_norm,
    mul_one, Complex.norm_ofNat]

theorem resolventCellBlock_lattice_summable {L z σ : ℝ} (hL : Ls ≤ L)
    (D : Auxiliary.Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64) :
    Summable (fun j : Bloch.Alias => ‖resolventCellBlock D hσ0 hσ 0 j‖) := by
  let a : ℝ := (cs/2)*Real.sqrt (1/L)
  have ha : 0 < a := mul_pos (div_pos cs_pos (by norm_num))
    (Real.sqrt_pos.mpr (div_pos zero_lt_one (length_pos hL)))
  have hd (j : Bloch.Alias) (hj : j ≠ 0) :
      (imageRadius j : ℝ)/4 ≤ ‖integerVector j‖ := by
    have h := periodic_image_distance (A := 0) 1 (by norm_num) 0 0 j
      (by simp) (by simp) hj
    simpa only [Nat.cast_one, one_mul, one_smul, zero_add, sub_zero] using h
  apply Summable.of_norm_bounded_eventually
    (latticeWeight_summable.mul_left (Cs*L^4*latticeDecayConstant a))
  filter_upwards [Filter.eventually_cofinite_ne (0 : Bloch.Alias)] with j hj
  rw [norm_norm]
  have hb := resolventCellBlock_gevrey hL D hσ0 hσ 0 j
  rw [sub_zero] at hb
  have he := image_distance_decay (length_pos hL) (M := 1) zero_le_one j hj
    (by simpa only [one_mul] using hd j hj)
  rw [imageTail, ite_eq_right hj] at he
  have hf := stretched_lattice_majorant ha j hj
  calc
    _ ≤ Cs*L^4*Real.exp (-cs*Real.sqrt (‖integerVector j‖/L)) := hb
    _ ≤ Cs*L^4*Real.exp (-a*Real.sqrt (imageRadius j)) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg Cs_pos.le (pow_nonneg (length_pos hL).le 4))
    _ ≤ Cs*L^4*(latticeDecayConstant a*latticeWeight j) :=
      mul_le_mul_of_nonneg_left hf (mul_nonneg Cs_pos.le (pow_nonneg (length_pos hL).le 4))
    _ = _ := by ring

theorem torusCellSymbol_coefficients_summable {L z σ : ℝ} (hL : Ls ≤ L)
    (D : Auxiliary.Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64) :
    Summable (fun n : Bloch.Alias => ‖mFourierCoeff (torusCellSymbol D hσ0 hσ) n‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => ?_) (resolventCellBlock_lattice_summable hL D hσ0 hσ)
  rw [← torusCellSymbol_coefficient_norm]
  nlinarith [norm_nonneg (mFourierCoeff (torusCellSymbol D hσ0 hσ) n)]

#print axioms torusCellSymbol_coefficients_summable

end Maxwell.Continuum.Calibration
