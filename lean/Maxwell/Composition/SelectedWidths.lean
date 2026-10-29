import Maxwell.Composition.SelectedDimensionBounds
import Maxwell.Realization.Widths
import Maxwell.Green.CouplingOutputBits

/-! Literal logarithmic widths of the selected finite access format and
shared physical calibration. All statements hold before the random draw. -/
noncomputable section
namespace Maxwell.Composition.SelectedWidths
open Maxwell.Realization Maxwell.Composition.SelectedLogicalBounds
open Maxwell.Composition.SelectedSpacingBounds Maxwell.Composition.SelectedDimensionBounds
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1200000

def localCount (R : SelectedPlatform) : ℕ := (Maxwell.Defect.ScalarDefect.edges R.physical.defect).card
def sampleExponent (R : SelectedPlatform) : ℕ := 1+localCount R
def alphaUpperExponent (R : SelectedPlatform) : ℕ :=
  constantExponent (R.physical.spacing.c/4) (div_pos R.physical.spacing.c_pos (by norm_num))
def amplitudeExponent (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  6+alphaUpperExponent R+16+fullExponent p R+1
def readoutExponent (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  R.physical.constants.readoutPrecisionExponent (sampleExponent R) (errorExponent p)
def formatCoefficient (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  2+amplitudeExponent p R+readoutExponent p R
def calibrationExponent (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  R.physical.constants.calibrationPrecisionExponent (backgroundExponent p R)
    (alphaUpperExponent R) (fullExponent p R) (errorExponent p)

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) (R : SelectedPlatform)
local notation "I" => SelectedInput.input p S hm

theorem sample_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    ((S.n*localCount R:ℕ):ℚ) ≤ (S.nnz:ℚ)^sampleExponent R := by
  have hn : (S.n:ℚ) ≤ (S.nnz:ℚ)^1 := by
    simpa only [pow_one] using (show (S.n:ℚ)≤S.nnz by exact_mod_cast Source.dimension_le_nnz S hunit)
  simpa only [Nat.cast_mul,sampleExponent] using mul_bound _ _ _ hn (constant_bound S.nnz (localCount R) hm2) (by positivity)

theorem alpha_upper (hm2 : 2 ≤ S.nnz) : (I).alpha R ≤ (S.nnz:ℚ)^alphaUpperExponent R := by
  have hpow : R.physical.spacing.a^((I).distance R) ≤ 1 :=
    pow_le_one₀ R.physical.spacing.a_pos.le R.physical.spacing.a_lt_one.le
  have h := mul_le_mul_of_nonneg_left hpow
    (show (0:ℚ)≤R.physical.spacing.c/4 from div_nonneg R.physical.spacing.c_pos.le (by norm_num))
  change (I).alpha R ≤ (R.physical.spacing.c/4)*1 at h
  rw [mul_one] at h
  exact h.trans (constant_le_input_power _ (div_pos R.physical.spacing.c_pos (by norm_num)) S.nnz hm2)

theorem amplitude_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (I).amplitude R ≤ (S.nnz:ℚ)^amplitudeExponent p R := by
  have ha := alpha_upper p S hm R hm2
  have hQ := full_bound p S hm R hm2 hunit
  have hj : R.physical.rowBound ≤ (S.nnz:ℚ)^16 := by
    rw [R.rowBound_eq]
    exact constant_bound S.nnz 16 hm2
  have h := mul_bound _ _ _
    (mul_bound _ _ _ (mul_bound _ _ _
      (mul_bound _ _ _ (constant_bound S.nnz 6 hm2) ha ((I).alpha_pos R).le)
      hj R.physical.rowBound_pos.le) hQ ((I).fullBudget_pos R).le)
    (y := (S.nnz:ℚ)) (by simp : (S.nnz:ℚ)≤(S.nnz:ℚ)^1) (by positivity)
  exact h

theorem readout_inverse_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (R.physical.constants.readoutBudget (I).epsilon (S.n*localCount R))⁻¹ ≤
      (S.nnz:ℚ)^readoutExponent p R :=
  R.physical.constants.readoutBudget_inverse_literal (I).epsilon (I).epsilon_pos
    S.nnz (S.n*localCount R) (errorExponent p) (sampleExponent R) hm2
    (error_inverse_bound p S hm hm2 hunit) (sample_bound S R hm2 hunit)

theorem integer_width (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    ((I).format R).integerBits ≤ 1+amplitudeExponent p R*Nat.clog 2 S.nnz := by
  have hc : Nat.ceil ((I).amplitude R) ≤ S.nnz^amplitudeExponent p R := by
    apply Nat.ceil_le.mpr
    exact_mod_cast amplitude_bound p S hm R hm2 hunit
  have hp : S.nnz^amplitudeExponent p R ≤ 2^(amplitudeExponent p R*Nat.clog 2 S.nnz) := by
    have h := Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num : 1<2) S.nnz) (amplitudeExponent p R)
    simpa only [←pow_mul,Nat.mul_comm] using h
  change (Nat.ceil ((I).amplitude R)).size ≤ _
  apply Nat.size_le.mpr
  apply (hc.trans hp).trans_lt
  rw [pow_add,pow_one]
  have hz : 0 < 2^(amplitudeExponent p R*Nat.clog 2 S.nnz) := by positivity
  omega

theorem fractional_width (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    ((I).format R).fractionalBits ≤ readoutExponent p R*Nat.clog 2 S.nnz := by
  have h := precisionBits_le_clog
    (R.physical.constants.readoutBudget (I).epsilon (S.n*localCount R))
    (R.physical.constants.readoutBudget_pos (I).epsilon (S.n*localCount R) (I).epsilon_pos)
    S.nnz 0 (readoutExponent p R)
    (by simpa only [pow_zero,one_mul] using readout_inverse_bound p S hm R hm2 hunit)
  simpa only [SelectedInstance.Input.format,selectedFormat,localCount,SelectedInput.input,zero_add] using h

theorem format_width (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    ((I).format R).width ≤ formatCoefficient p R*unsignedBitLength (2+S.nnz) := by
  have hi := integer_width p S hm R hm2 hunit
  have hf := fractional_width p S hm R hm2 hunit
  have hb := clog_le_inputBitLength S.nnz
  have hp := inputBitLength_pos S.nnz
  unfold Target.FixedPointFormat.width formatCoefficient
  nlinarith [Nat.mul_le_mul_left (amplitudeExponent p R) hb, Nat.mul_le_mul_left (readoutExponent p R) hb]

theorem calibration_inverse_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (R.physical.constants.calibrationBudget (I).epsilon ((I).alpha R)
      ((I).backgroundBudget R) ((I).fullBudget R))⁻¹ ≤ (S.nnz:ℚ)^calibrationExponent p R :=
  R.physical.constants.calibrationBudget_inverse_literal (I).epsilon ((I).alpha R)
    ((I).backgroundBudget R) ((I).fullBudget R) (I).epsilon_pos ((I).alpha_pos R)
    ((I).backgroundBudget_pos R) ((I).fullBudget_pos R)
    S.nnz (errorExponent p) (alphaUpperExponent R) (backgroundExponent p R) (fullExponent p R)
    hm2 (error_inverse_bound p S hm hm2 hunit) (alpha_upper p S hm R hm2)
    (background_bound p S hm R hm2 hunit) (full_bound p S hm R hm2 hunit)

theorem calibration_precision (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    precisionBits (R.physical.constants.calibrationBudget (I).epsilon ((I).alpha R)
      ((I).backgroundBudget R) ((I).fullBudget R))
      (R.physical.constants.calibrationBudget_pos _ _ _ _ (I).epsilon_pos ((I).alpha_pos R)
        ((I).backgroundBudget_pos R) ((I).fullBudget_pos R)) ≤
      calibrationExponent p R*Nat.clog 2 S.nnz := by
  simpa only [pow_zero,one_mul,zero_add] using precisionBits_le_clog
    (R.physical.constants.calibrationBudget (I).epsilon ((I).alpha R) ((I).backgroundBudget R) ((I).fullBudget R))
    (R.physical.constants.calibrationBudget_pos _ _ _ _ (I).epsilon_pos ((I).alpha_pos R)
      ((I).backgroundBudget_pos R) ((I).fullBudget_pos R)) S.nnz 0 (calibrationExponent p R)
    (by simpa only [pow_zero,one_mul] using calibration_inverse_bound p S hm R hm2 hunit)

end Maxwell.Composition.SelectedWidths
