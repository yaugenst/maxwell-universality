import Maxwell.Composition.SelectedBufferBounds

/-! A literal polynomial bound for the complete buffered PEC dimension.
This conservative bound is used for precision/conditioning exponents; it
does not replace the sharper three-halves bound used for output volume. -/
noncomputable section
namespace Maxwell.Composition.SelectedDimensionBounds
open Maxwell.Realization Maxwell.Composition.SelectedLogicalBounds
open Maxwell.Composition.SelectedSpacingBounds Maxwell.Composition.SelectedBufferBounds
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000

def fixedCoefficient (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  ⌈(R.physical.volumeCoefficient : ℝ)*(coefficient p R+2)^3⌉₊
def dimensionExponent (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  fixedCoefficient p R+3*max (extentPower p R) 1
def backgroundExponent (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  PhysicalConstants.backgroundExponent (dimensionExponent p R) (detuningExponent p R)
def fullExponent (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  R.physical.constants.fullExponent (logicalExponent p) (alphaExponent p R) (backgroundExponent p R)
def conditionExponent (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  R.physical.constants.conditionExponent (logicalExponent p) (alphaExponent p R) (backgroundExponent p R)
def toleranceExponent (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  R.physical.constants.toleranceExponent (errorExponent p) (backgroundExponent p R)

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) (R : SelectedPlatform)
local notation "I" => SelectedInput.input p S hm

theorem dimension_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (Fintype.card ((I).box R).Edge : ℚ) ≤ (S.nnz:ℚ)^dimensionExponent p R := by
  have hmR : (1:ℝ) ≤ S.nnz := by exact_mod_cast hm
  have hm0 : (0:ℝ) < S.nnz := by exact_mod_cast hm
  have hb := logarithmic p S hm R hm2 hunit
  have hc := coefficient_pos p R
  have hlog := Real.log_le_sub_one_of_pos hm0
  have hb' : (buffer p S hm R : ℝ) ≤ coefficient p R*(S.nnz:ℝ) :=
    hb.trans (mul_le_mul_of_nonneg_left (by linarith) hc.le)
  have hsR : (((I).distance R*SourceRouting.side S (I).precision : ℕ):ℝ) ≤
      (S.nnz:ℝ)^extentPower p R := by exact_mod_cast extent_power_bound p S hm R hm2 hunit
  have hsmax := pow_le_pow_right₀ hmR (le_max_left (extentPower p R) 1)
  have hmmax : (S.nnz:ℝ) ≤ (S.nnz:ℝ)^max (extentPower p R) 1 := by
    simpa only [pow_one] using pow_le_pow_right₀ hmR (le_max_right (extentPower p R) 1)
  have h1 : (1:ℝ) ≤ (S.nnz:ℝ)^max (extentPower p R) 1 := one_le_pow₀ hmR
  have hsum : (((I).distance R*SourceRouting.side S (I).precision : ℕ):ℝ)+
      (buffer p S hm R : ℝ)+1 ≤ (coefficient p R+2)*(S.nnz:ℝ)^max (extentPower p R) 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hmmax hc.le]
  have hn := R.physical.physical_edge_feedback S (I).precision ((I).distance R) (buffer p S hm R)
  have hcube := pow_le_pow_left₀ (by positivity) hsum 3
  have hvol0 : (0:ℝ) ≤ R.physical.volumeCoefficient := by
    exact_mod_cast R.physical.volumeCoefficient_nonneg
  have hN := hn.trans (mul_le_mul_of_nonneg_left hcube hvol0)
  have hpow : ((coefficient p R+2)*(S.nnz:ℝ)^max (extentPower p R) 1)^3 =
      (coefficient p R+2)^3*(S.nnz:ℝ)^(3*max (extentPower p R) 1) := by
    rw [mul_pow, ←pow_mul, Nat.mul_comm]
  rw [hpow] at hN
  have hbox : DecoratedDefectLayout.physicalBox S (I).precision R.physical.basis R.physical.defect
      ((I).distance R) (buffer p S hm R) = (I).box R := rfl
  rw [hbox] at hN
  have hceil := Nat.le_ceil ((R.physical.volumeCoefficient : ℝ)*(coefficient p R+2)^3)
  have hbN : (Fintype.card ((I).box R).Edge : ℝ) ≤
      (fixedCoefficient p R:ℝ)*(S.nnz:ℝ)^(3*max (extentPower p R) 1) := by
    calc
      _ ≤ (R.physical.volumeCoefficient : ℝ)*(coefficient p R+2)^3*
          (S.nnz:ℝ)^(3*max (extentPower p R) 1) := by simpa only [mul_assoc] using hN
      _ ≤ _ := mul_le_mul_of_nonneg_right hceil (by positivity)
  have hQ : (Fintype.card ((I).box R).Edge : ℚ) ≤
      (fixedCoefficient p R:ℚ)*(S.nnz:ℚ)^(3*max (extentPower p R) 1) := by exact_mod_cast hbN
  exact hQ.trans (mul_bound _ _ _ (constant_bound S.nnz (fixedCoefficient p R) hm2) le_rfl (by positivity))

theorem background_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (I).backgroundBudget R ≤ (S.nnz:ℚ)^backgroundExponent p R :=
  R.physical.constants.backgroundInverseBudget_literal ((I).zeta R) ((I).zeta_pos R)
    S.nnz (Fintype.card ((I).box R).Edge) (dimensionExponent p R) (detuningExponent p R)
    hm2 (dimension_bound p S hm R hm2 hunit) (detuning_bound p S hm R hm2 hunit)

theorem full_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (I).fullBudget R ≤ (S.nnz:ℚ)^fullExponent p R :=
  R.physical.constants.fullInverseBudget_literal (I).logicalBudget ((I).alpha R) ((I).backgroundBudget R)
    (by linarith [(I).logicalBudget_ge_one]) ((I).alpha_pos R) ((I).backgroundBudget_pos R).le
    S.nnz (logicalExponent p) (alphaExponent p R) (backgroundExponent p R) hm2
    (logical_bound p S hm hm2 hunit) (scales_bound p S hm R hm2 hunit).2
    (background_bound p S hm R hm2 hunit)

theorem condition_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    16*((I).fullBudget R : ℝ) ≤ (S.nnz:ℝ)^(conditionExponent p R:ℝ) := by
  have h := R.physical.constants.conditionBudget_literal (I).logicalBudget ((I).alpha R)
    ((I).backgroundBudget R) (by linarith [(I).logicalBudget_ge_one]) ((I).alpha_pos R)
    ((I).backgroundBudget_pos R) S.nnz (logicalExponent p) (alphaExponent p R)
    (backgroundExponent p R) hm2 (logical_bound p S hm hm2 hunit)
    (scales_bound p S hm R hm2 hunit).2 (background_bound p S hm R hm2 hunit)
  change R.physical.rowBound*(I).fullBudget R ≤ _ at h
  rw [R.rowBound_eq] at h
  rw [Real.rpow_natCast]
  exact_mod_cast h

theorem tolerance_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (S.nnz:ℝ)^(-(toleranceExponent p R:ℝ)) ≤ ((I).residualTolerance R:ℝ) := by
  have h := R.physical.constants.residualUnit_lower_literal (I).epsilon ((I).backgroundBudget R)
    (I).epsilon_pos ((I).backgroundBudget_pos R) S.nnz (errorExponent p) (backgroundExponent p R)
    hm2 (error_inverse_bound p S hm hm2 hunit) (background_bound p S hm R hm2 hunit)
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  simp only [one_div] at h
  have hR := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hR
  exact hR

theorem success_probability (C : Constants) (hm2 : 2 ≤ S.nnz)
    (hpromise : Source.Promises p S) (hb : S.source ≠ 0)
    (hpower : conditionExponent p R ≤ C.conditionPower) :
    1-3/(64*(S.nnz:ℝ)) ≤ successProbability p C S
      (randomBits := (I).randomBits R) ((I).target R (2^(I).randomBits R)) := by
  apply SelectedInput.success_probability p S hm R C hm2 hpromise hb
  have hm1 : (1:ℝ) ≤ S.nnz := by exact_mod_cast hm
  rw [max_eq_right hm1]
  exact (condition_bound p S hm R hm2 hpromise.1).trans
    (Real.rpow_le_rpow_of_exponent_le hm1 (by exact_mod_cast hpower))

end Maxwell.Composition.SelectedDimensionBounds
