import Maxwell.Continuum.ParameterMaster
import Maxwell.Continuum.ParameterSourceInput

/-! Source-specialized termination and the published polylogarithmic resource
exponents. All constants depend only on the fixed source promise and fixed
physical platform. The analysis constant is deliberately conservative. -/

noncomputable section
namespace Maxwell.Continuum.Parameters
open MasterConstants Maxwell.Composition
attribute [local irreducible] exponent Cs sourceInput
set_option backward.isDefEq.respectTransparency true

def sourceMagnitude (p : Source.Parameters) : ℕ :=
  4096+exponent+minimumLengthExponent exponent+sourceBudgetExponent p

def sourceStage (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) : ℕ :=
  selectedOuterExponent (sourceInput p S hm) exponent (minimumLengthExponent exponent)
    (inputLog S.nnz) (inputLog_pos S.nnz)

theorem sourceMagnitude_bounds (p : Source.Parameters) :
    4096 ≤ sourceMagnitude p ∧ exponent ≤ sourceMagnitude p ∧
    sourceBudgetExponent p ≤ sourceMagnitude p ∧
    minimumLengthExponent exponent ≤ sourceMagnitude p := by unfold sourceMagnitude; omega

theorem source_scales (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    let I := sourceInput p S hm
    let k := sourceStage p S hm
    let M := sourceMagnitude p
    let ℓ := inputLog S.nnz
    stageLength k ≤ 2^(6+45*M)*ℓ^6 ∧
    stageSpacing I exponent k ≤ 2^(9*M)*ℓ ∧
    stageBuffer I exponent k ≤ 2^(11*M)*ℓ ∧
    stageLength k*stageBuffer I exponent k ≤ 2^(6+56*M)*ℓ^7 := by
  have hM := sourceMagnitude_bounds p
  exact selected_scales (sourceInput_binary p S hm hm2 hunit)
    hM.1 hM.2.1 hM.2.2.1 hM.2.2.2 (inputLog_pos S.nnz)

theorem source_bits (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    let I := sourceInput p S hm
    let k := sourceStage p S hm
    let M := sourceMagnitude p
    let ℓ := inputLog S.nnz
    (stageLength k).bits.length ≤ 45*M+6*ℓ+7 ∧
    (stageSpacing I exponent k).bits.length ≤ 9*M+ℓ+1 ∧
    (stageBuffer I exponent k).bits.length ≤ 11*M+ℓ+1 ∧
    (stageLength k*stageBuffer I exponent k).bits.length ≤ 56*M+7*ℓ+7 := by
  have hM := sourceMagnitude_bounds p
  exact selected_bits (sourceInput_binary p S hm hm2 hunit)
    hM.1 hM.2.1 hM.2.2.1 hM.2.2.2 (inputLog_pos S.nnz)

theorem source_master_length (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) :
    Ls ≤ (stageLength (sourceStage p S hm) : ℝ) :=
  selectedLength_master_lower (sourceInput p S hm) (inputLog S.nnz) (inputLog_pos S.nnz)

theorem source_tests (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) :
    let I := sourceInput p S hm
    let k := sourceStage p S hm
    SpacingTest exponent (stageLength k) I.K I.epsilon (stageSpacing I exponent k) ∧
    BufferTest exponent I.J I.m (stageLength k) (stageSpacing I exponent k) (stageSpan I exponent k)
      I.K I.epsilon (stageTau I exponent k) (stageBuffer I exponent k) ∧
    LeakageTest I exponent k ∧ TailTest I exponent k :=
  selected_master_tests (sourceInput p S hm) (inputLog S.nnz) (inputLog_pos S.nnz)

theorem source_iteration_bound (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    sourceStage p S hm ≤ 17*sourceMagnitude p*inputLog S.nnz := by
  have hM := sourceMagnitude_bounds p
  exact (selectedOuter_le_candidate (sourceInput_binary p S hm hm2 hunit)
    hM.1 hM.2.1 hM.2.2.1 hM.2.2.2 (inputLog_pos S.nnz)).trans
      (candidate_exponent_le (by omega) (inputLog_pos S.nnz))

#print axioms source_scales
#print axioms source_bits
#print axioms source_tests

end Maxwell.Continuum.Parameters
