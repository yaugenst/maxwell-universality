import Maxwell.Continuum.ContinuumRealizationBinary

/-! Explicit linear binary precisions for every remaining finite error
budget in the selected continuum construction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 1024

namespace Maxwell.Continuum.RealizationParameters

open MasterConstants
attribute [local irreducible] Cs exponent Ls Parameters.sourceInput analysisBits inputBits

def sourceTolerance (p : Source.Parameters) (S : Source.SparseSystem) : ℚ :=
  (1/2 : ℚ)^(scaleBits p S+4)
def templatePrecision (p : Source.Parameters) (S : Source.SparseSystem) : ℕ := scaleBits p S+6
def materialPrecision (p : Source.Parameters) (S : Source.SparseSystem) : ℕ :=
  scaleBits p S+inputBits p*logSize S+256
def sourcePrecision (p : Source.Parameters) (S : Source.SparseSystem) : ℕ := scaleBits p S+logSize S+8
def momentPrecision (p : Source.Parameters) (S : Source.SparseSystem) : ℕ := 2*(inputBits p*logSize S)+27
def calibrationPrecision (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) : ℕ :=
  scaleBits p S+4*spacing p S hm+8

theorem two_pow_mul_half_pow_add (a b : ℕ) :
    (2 : ℝ)^a*(1/2 : ℝ)^(a+b) = (1/2 : ℝ)^b := by
  rw [pow_add]
  simp only [div_pow, one_pow]
  field_simp

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)

theorem sourceTolerance_pos : (0 : ℝ) < sourceTolerance p S := by
  apply Rat.cast_pos.mpr
  unfold sourceTolerance
  positivity

theorem sourceTolerance_bound (hm2 : 2 ≤ S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    (sourceTolerance p S : ℝ) ≤ (residual p S hm : ℝ)/4 := by
  have he : (sourceTolerance p S : ℝ) = (1/2 : ℝ)^(scaleBits p S)/16 := by
    simp only [sourceTolerance, pow_add]
    norm_num
    ring
  rw [he]
  have hr := residual_binary_real p S hm hm2 hu
  have hp := residual_pos p S hm
  linarith only [hr, hp]

theorem template_precision_budget (hm2 : 2 ≤ S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    (1/2 : ℝ)^(templatePrecision p S) ≤
      min ((sourceTolerance p S : ℝ)/4) ((residual p S hm : ℝ)/4) := by
  have he : (1/2 : ℝ)^(templatePrecision p S) = (sourceTolerance p S : ℝ)/4 := by
    simp only [templatePrecision, sourceTolerance, pow_add]
    norm_num
    ring
  rw [he]
  apply le_min le_rfl
  exact (div_le_self (sourceTolerance_pos p S).le (by norm_num)).trans
    (sourceTolerance_bound p S hm hm2 hu)

theorem material_precision_budget (hm2 : 2 ≤ S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    Enclosures.materialError p S hm (materialPrecision p S)*
      ((2 : ℝ)^142*(budget p S hm : ℝ)*(length p S hm : ℝ)^2) ≤ (residual p S hm : ℝ)/4 := by
  rw [material_error_weighted]
  have hK : (budget p S hm : ℝ) ≤ (2 : ℝ)^(inputBits p*logSize S) := by
    exact_mod_cast (input_binary p S hm hm2 hu).1
  calc
    _ ≤ 3*(2 : ℝ)^272*(2 : ℝ)^(inputBits p*logSize S)*
        (1/2 : ℝ)^(materialPrecision p S+24) := by gcongr
    _ = (3/256 : ℝ)*(1/2 : ℝ)^(scaleBits p S) := by
      rw [show materialPrecision p S+24 = inputBits p*logSize S+(272+(scaleBits p S+8)) by
        unfold materialPrecision; omega]
      rw [show 3*(2 : ℝ)^272*(2 : ℝ)^(inputBits p*logSize S)*
        (1/2 : ℝ)^(inputBits p*logSize S+(272+(scaleBits p S+8))) =
        3*(2 : ℝ)^272*((2 : ℝ)^(inputBits p*logSize S)*
          (1/2 : ℝ)^(inputBits p*logSize S+(272+(scaleBits p S+8)))) by ring]
      rw [two_pow_mul_half_pow_add, mul_assoc, two_pow_mul_half_pow_add, pow_add]
      norm_num only [show (1/2 : ℝ)^8 = 1/256 by norm_num]
      ring
    _ ≤ (1/4 : ℝ)*(residual p S hm : ℝ) := mul_le_mul
      (by norm_num : (3/256 : ℝ) ≤ 1/4) (residual_binary_real p S hm hm2 hu)
      (by positivity) (by norm_num)
    _ = _ := by ring

theorem source_precision_budget : (S.nnz : ℝ)*(1/2 : ℝ)^(sourcePrecision p S) ≤
    (sourceTolerance p S : ℝ)/16 := by
  have hmR : (S.nnz : ℝ) ≤ (2 : ℝ)^(logSize S) := by exact_mod_cast Parameters.input_le_binary S.nnz
  calc
    _ ≤ (2 : ℝ)^(logSize S)*(1/2 : ℝ)^(sourcePrecision p S) := by gcongr
    _ = (sourceTolerance p S : ℝ)/16 := by
      rw [show sourcePrecision p S = logSize S+(scaleBits p S+8) by unfold sourcePrecision; omega,
        two_pow_mul_half_pow_add]
      simp only [sourceTolerance, pow_add]
      norm_num
      ring

theorem moment_precision_budget (hm2 : 2 ≤ S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    (1/2 : ℝ)^(momentPrecision p S) ≤
      (epsilon p S hm : ℝ)/(2^27*max 1 (sites p S hm : ℝ)) := by
  have hi := input_binary p S hm hm2 hu
  have hJ : (sites p S hm : ℝ) ≤ (2 : ℝ)^(inputBits p*logSize S) := by exact_mod_cast hi.2.1
  have hε : ((epsilon p S hm : ℝ))⁻¹ ≤ (2 : ℝ)^(inputBits p*logSize S) := by exact_mod_cast hi.2.2
  have hεlo : (1/2 : ℝ)^(inputBits p*logSize S) ≤ (epsilon p S hm : ℝ) := by
    have hh := (inv_le_inv₀ (show (0 : ℝ) < 2^(inputBits p*logSize S) by positivity)
      (inv_pos.mpr (epsilon_pos p S hm))).mpr hε
    simpa only [inv_inv, one_div, inv_pow] using hh
  have hmax : max 1 (sites p S hm : ℝ) ≤ (2 : ℝ)^(inputBits p*logSize S) :=
    max_le (one_le_pow₀ (by norm_num)) hJ
  calc
    _ = (1/2 : ℝ)^(inputBits p*logSize S)/((2 : ℝ)^27*(2 : ℝ)^(inputBits p*logSize S)) := by
      rw [momentPrecision, two_mul, pow_add, pow_add]
      simp only [div_pow, one_pow]
      field_simp
    _ ≤ (epsilon p S hm : ℝ)/((2 : ℝ)^27*(2 : ℝ)^(inputBits p*logSize S)) :=
      div_le_div_of_nonneg_right hεlo (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (epsilon_pos p S hm).le
      (by positivity) (mul_le_mul_of_nonneg_left hmax (by positivity))

theorem calibration_source_budget : (1/2 : ℝ)^(calibrationPrecision p S hm) ≤
    (sourceTolerance p S : ℝ)/8 := by
  calc
    _ ≤ (1/2 : ℝ)^(scaleBits p S+7) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by unfold calibrationPrecision; omega)
    _ = _ := by
      simp only [sourceTolerance, pow_add]
      norm_num
      ring

theorem calibration_coupling_budget : (1/2 : ℚ)^(calibrationPrecision p S hm) ≤
    (zeta p S hm)^2/16 := by
  have hz : (1/2 : ℚ)^(4*spacing p S hm) ≤ (zeta p S hm)^2 := by
    rw [pow_mul]
    unfold zeta Parameters.zeta
    conv_rhs => rw [pow_right_comm]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) (spacing p S hm)
  calc
    _ ≤ (1/2 : ℚ)^(4*spacing p S hm+4) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by unfold calibrationPrecision; omega)
    _ = (1/2 : ℚ)^(4*spacing p S hm)/16 := by rw [pow_add]; norm_num; ring
    _ ≤ _ := div_le_div_of_nonneg_right hz (by norm_num)

#print axioms template_precision_budget
#print axioms material_precision_budget
#print axioms source_precision_budget
#print axioms moment_precision_budget
#print axioms calibration_coupling_budget

end Maxwell.Continuum.RealizationParameters
