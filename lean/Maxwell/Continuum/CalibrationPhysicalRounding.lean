import Maxwell.Continuum.CalibrationFourierRounding
import Maxwell.Continuum.CalibrationSupercellCoefficients

/-! End-to-end physical coefficient rounding. Both the rational square
root normalization and the dyadic words have proved global L² error,
with precision linear in the size and support logarithms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber

variable (M : ℕ) [NeZero M]

theorem physicalFactor_le_one : physicalFactor M≤1 := by
  have hm : (1 : ℝ)≤(M : ℝ)^3 := one_le_pow₀ (by exact_mod_cast NeZero.pos M)
  have hc := physicalFactor_square M
  have hp := physicalFactor_pos M
  have h : physicalFactor M^2*8≤physicalFactor M^2*8*(M : ℝ)^3 :=
    le_mul_of_one_le_right (by positivity) hm
  nlinarith

theorem physicalFactorApprox_abs_le_two (P : ℕ) : |(physicalFactorApprox M P : ℝ)|≤2 := by
  have he := physicalFactorApprox_error M P
  have hp : (1/2 : ℝ)^P≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ht := abs_add_le ((physicalFactorApprox M P : ℝ)-physicalFactor M) (physicalFactor M)
  rw [sub_add_cancel,abs_of_pos (physicalFactor_pos M)] at ht
  have hc := physicalFactor_le_one M
  linarith

theorem physicalCoefficientData_norm (P : ℕ) (v : FourierData) :
    ‖(physicalCoefficientData M P v).value‖≤2*‖v.value‖ := by
  rw [physicalCoefficientData,FourierData.scale_value,norm_smul,
    ← Complex.ofReal_ratCast,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (physicalFactorApprox_abs_le_two M P) (norm_nonneg _)

theorem physicalSeriesField_difference (v w : FourierData) :
    ‖physicalSeriesField M v-physicalSeriesField M w‖=
      (physicalFactor M)⁻¹*‖v.value-w.value‖ := by
  rw [physicalSeriesField,physicalSeriesField,← smul_sub,← map_sub,norm_smul,
    norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (physicalFactor_pos M),embedding_norm]

theorem physicalSeriesField_rounding_error (B : ℕ) (v : FourierData) :
    ‖physicalSeriesField M (roundFourierData B v)-physicalSeriesField M v‖≤
      48*(M : ℝ)^3*((2*v.radius+1 : ℕ) : ℝ)^3*(1/2 : ℝ)^B := by
  rw [physicalSeriesField_difference]
  calc
    _ ≤ (8*(M : ℝ)^3)*(6*((2*v.radius+1 : ℕ) : ℝ)^3*(1/2 : ℝ)^B) :=
      mul_le_mul (physicalFactor_inv_bound M) (roundFourierData_error B v)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem physicalSeriesField_rounding_requested (N ellM ellR B : ℕ) (v : FourierData)
    (hM : (M : ℝ)≤(2 : ℝ)^ellM)
    (hR : ((2*v.radius+1 : ℕ) : ℝ)≤(2 : ℝ)^ellR)
    (hB : N+3*ellM+3*ellR+6≤B) :
    ‖physicalSeriesField M (roundFourierData B v)-physicalSeriesField M v‖≤(1/2 : ℝ)^N := by
  apply (physicalSeriesField_rounding_error M B v).trans
  have hc : 48*(M : ℝ)^3*((2*v.radius+1 : ℕ) : ℝ)^3≤(2 : ℝ)^(3*ellM+3*ellR+6) := by
    calc
      _ ≤ 64*((2 : ℝ)^ellM)^3*((2 : ℝ)^ellR)^3 := by gcongr; norm_num
      _ = _ := by
        rw [show (64 : ℝ)=(2 : ℝ)^6 by norm_num,← pow_mul,← pow_mul,
          ← pow_add,← pow_add]
        congr 1
        omega
  have hp : (1/2 : ℝ)^B≤(1/2 : ℝ)^(N+3*ellM+3*ellR+6) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hB
  calc
    _ ≤ (2 : ℝ)^(3*ellM+3*ellR+6)*(1/2 : ℝ)^(N+3*ellM+3*ellR+6) :=
      mul_le_mul hc hp (by positivity) (by positivity)
    _ = _ := by
      rw [show N+3*ellM+3*ellR+6=N+(3*ellM+3*ellR+6) by omega,
        pow_add (1/2 : ℝ),mul_left_comm,← mul_pow]
      norm_num

theorem roundedPhysicalCoefficientData_error (N ellM ellR P B : ℕ) (v : FourierData)
    (hv : ‖v.value‖≤2) (hM : (M : ℝ)≤(2 : ℝ)^ellM)
    (hR : ((2*v.radius+1 : ℕ) : ℝ)≤(2 : ℝ)^ellR)
    (hP : N+3*ellM+5≤P) (hB : N+3*ellM+3*ellR+7≤B) :
    ‖physicalSeriesField M (roundFourierData B (physicalCoefficientData M P v))-
      embedding M v.value‖≤(1/2 : ℝ)^N := by
  have hr := physicalSeriesField_rounding_requested M (N+1) ellM ellR B
    (physicalCoefficientData M P v) hM (by simpa only [physicalCoefficientData_radius] using hR) (by omega)
  have hp := physicalCoefficientData_requested_error M (N+2) ellM P v hM (by omega)
  have hp' : ‖physicalSeriesField M (physicalCoefficientData M P v)-embedding M v.value‖≤
      (1/2 : ℝ)^(N+1) := by
    apply hp.trans
    calc
      _ ≤ (1/2 : ℝ)^(N+2)*2 := mul_le_mul_of_nonneg_left hv (by positivity)
      _ = _ := by rw [pow_succ]; ring
  calc
    _ ≤ ‖physicalSeriesField M (roundFourierData B (physicalCoefficientData M P v))-
        physicalSeriesField M (physicalCoefficientData M P v)‖+
      ‖physicalSeriesField M (physicalCoefficientData M P v)-embedding M v.value‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (1/2 : ℝ)^(N+1)+(1/2 : ℝ)^(N+1) := add_le_add hr hp'
    _ = _ := by rw [pow_succ]; ring

#print axioms roundedPhysicalCoefficientData_error

end Maxwell.Continuum.Calibration.Supercell
