import Maxwell.Composition.SelectedGoodDraw
import Maxwell.Realization.BinaryPrecision

/-! Instantiate the physical constructor directly from the fixed source
promise. The requested real accuracy is never read by the encoder. -/
noncomputable section
namespace Maxwell.Composition.SelectedInput
open Maxwell.Realization
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1200000

def input (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) :
    SelectedInstance.Input where
  source := S
  precision := binaryCoefficientPrecision S.nnz ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊
  sourceBound := logicalScale S.nnz ⌈p.conditionExponent⌉₊
  accuracy := logicalAccuracy S.nnz ⌈p.accuracyExponent⌉₊
  sourceBound_ge_one := logicalScale_ge_one _ _ hm
  accuracy_pos := logicalAccuracy_pos _ _ hm
  nnz_pos := hm

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)

theorem precision_pos : 1 ≤ (input p S hm).precision :=
  binaryCoefficientPrecision_pos _ _ _

theorem accuracy_le_one : (input p S hm).accuracy ≤ 1 :=
  logicalAccuracy_le_one _ _ hm

theorem accuracy_eq : ((input p S hm).accuracy : ℝ) = Source.fixedAccuracy p S := by
  change ((1/(S.nnz:ℚ)^⌈p.accuracyExponent⌉₊ : ℚ):ℝ) =
    (S.nnz:ℝ)^(-(⌈p.accuracyExponent⌉₊:ℝ))
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  push_cast
  exact one_div _

theorem accuracy_floor : ((input p S hm).accuracy : ℝ) ≤
    (S.nnz : ℝ)^(-p.accuracyExponent) := by
  rw [accuracy_eq]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm)
    (neg_le_neg (Nat.le_ceil p.accuracyExponent))

theorem precision_budget : (S.nnz : ℝ)/(2*2^(input p S hm).precision) ≤
    ((input p S hm).accuracy : ℝ)/(64*(input p S hm).sourceBound) := by
  apply (binaryCoefficientPrecision_matrix_error S.nnz
    ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ hm).trans
  have hL : (0 : ℝ) < logicalScale S.nnz ⌈p.conditionExponent⌉₊ := by
    exact_mod_cast logicalScale_pos _ _ hm
  have he : (0 : ℝ) ≤ logicalAccuracy S.nnz ⌈p.accuracyExponent⌉₊ := by
    exact_mod_cast (logicalAccuracy_pos _ _ hm).le
  change (logicalAccuracy S.nnz ⌈p.accuracyExponent⌉₊ : ℝ)/
      (128*logicalScale S.nnz ⌈p.conditionExponent⌉₊) ≤
    (logicalAccuracy S.nnz ⌈p.accuracyExponent⌉₊ : ℝ)/
      (64*logicalScale S.nnz ⌈p.conditionExponent⌉₊)
  exact div_le_div_of_nonneg_left he (by positivity) (by linarith)

theorem goodDraw (R : SelectedPlatform) (C : Constants) (hm2 : 2 ≤ S.nnz)
    (hpromise : Source.Promises p S) (hb : S.source ≠ 0)
    (hconditionPower : 16*((input p S hm).fullBudget R : ℝ) ≤
      (max 1 S.nnz : ℝ)^(C.conditionPower : ℝ))
    (J : ℕ) (j : Fin J) (hj : j.val ∉ (input p S hm).bad R J) :
    GoodDraw p C S ((input p S hm).target R J j) :=
  (input p S hm).goodDraw R p C J j hj hpromise.1 hm2 hb
    (precision_pos p S hm) (accuracy_le_one p S hm)
    (promise_logicalScale p S hm2 hpromise) (precision_budget p S hm)
    hconditionPower (accuracy_floor p S hm)

theorem success_probability (R : SelectedPlatform) (C : Constants) (hm2 : 2 ≤ S.nnz)
    (hpromise : Source.Promises p S) (hb : S.source ≠ 0)
    (hconditionPower : 16*((input p S hm).fullBudget R : ℝ) ≤
      (max 1 S.nnz : ℝ)^(C.conditionPower : ℝ)) :
    1-3/(64*(S.nnz : ℝ)) ≤
      successProbability p C S (randomBits := (input p S hm).randomBits R)
        ((input p S hm).target R (2^(input p S hm).randomBits R)) :=
  (input p S hm).success_probability R p C hpromise.1 hm2 hb
    (precision_pos p S hm) (accuracy_le_one p S hm)
    (promise_logicalScale p S hm2 hpromise) (precision_budget p S hm)
    hconditionPower (accuracy_floor p S hm)

end Maxwell.Composition.SelectedInput
