import Maxwell.Continuum.ParameterSourceResources
import Maxwell.Continuum.ParameterPrecision
import Maxwell.Continuum.ParameterInverseScales
import Maxwell.Continuum.ParameterExponentialBudgets

/-! The source-specialized precision and inverse-scale conclusions. -/

noncomputable section
namespace Maxwell.Continuum.Parameters
open MasterConstants
attribute [local irreducible] exponent Cs sourceInput
set_option backward.isDefEq.respectTransparency true

def sourcePolynomialExponent (p : Source.Parameters) : ℕ := 3*2^(12*sourceMagnitude p)

theorem source_inverse_scales (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    let I := sourceInput p S hm
    let k := sourceStage p S hm
    let L := stageLength k
    let d := stageSpacing I exponent k
    let t := stageBuffer I exponent k
    let N := boxCount (stageSpan I exponent k) L t
    let P := (S.nnz+2 : ℚ)^sourcePolynomialExponent p
    (alpha L d)⁻¹ ≤ P ∧ (stageTau I exponent k)⁻¹ ≤ P ∧
    inverseBudget I.m N (stageTau I exponent k) ≤ P ∧
    (errorBudget I.m N I.epsilon (stageTau I exponent k))⁻¹ ≤ P ∧
    globalBudget exponent I.J I.m N L d I.K ≤ P := by
  have hI := sourceInput_binary p S hm hm2 hunit
  have hM := sourceMagnitude_bounds p
  have hE := selected_budget_exponent hI hM.1 hM.2.1 hM.2.2.1 hM.2.2.2 (inputLog_pos S.nnz)
  have hp := (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hE).trans
    (binary_inputLog_le_polynomial S.nnz (2^(12*sourceMagnitude p)))
  have hh := stage_numeric_budgets hI exponent (sourceStage p S hm)
    (stageBuffer (sourceInput p S hm) exponent (sourceStage p S hm))
  exact ⟨hh.1.trans hp, hh.2.1.trans hp, hh.2.2.1.trans hp,
    hh.2.2.2.1.trans hp, hh.2.2.2.2.trans hp⟩

theorem source_tau_bits (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    rationalBitLength (stageTau (sourceInput p S hm) exponent (sourceStage p S hm)) ≤
      (28+204*sourceMagnitude p+4*2^(9*sourceMagnitude p))*inputLog S.nnz := by
  have hM := sourceMagnitude_bounds p
  exact selected_tau_bits (sourceInput_binary p S hm hm2 hunit)
    hM.1 hM.2.1 hM.2.2.1 hM.2.2.2 (inputLog_pos S.nnz)

theorem source_decay_bits (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    let I := sourceInput p S hm
    let k := sourceStage p S hm
    let M := sourceMagnitude p
    let ℓ := inputLog S.nnz
    rationalBitLength (rationalDecay (stageLength k)) ≤ 2^(6+45*M)*ℓ^6+3 ∧
    rationalBitLength (rationalDecay (2^k)) ≤ 2^(6+45*M)*ℓ^6+3 ∧
    rationalBitLength (rationalDecay (stageBuffer I exponent k)) ≤ 2^(11*M)*ℓ+3 := by
  have hM := sourceMagnitude_bounds p
  exact selected_decay_bits (sourceInput_binary p S hm hm2 hunit)
    hM.1 hM.2.1 hM.2.2.1 hM.2.2.2 (inputLog_pos S.nnz)

theorem source_exponential_budgets (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) :
    let I := sourceInput p S hm
    let k := sourceStage p S hm
    let L := stageLength k
    let d := stageSpacing I exponent k
    let t := stageBuffer I exponent k
    let N := boxCount (stageSpan I exponent k) L t
    let Ξ := BoxCutoff.globalMajorant N I.J I.m I.K (alpha L d) L
    let e₀ := (errorBudget I.m N I.epsilon (stageTau I exponent k) : ℝ)
    Ξ*Real.exp (-cs*(L : ℝ)^(1/3 : ℝ)) ≤ e₀/4 ∧
    Ξ*Real.exp (-cs*((L : ℝ)*(t : ℝ))/(L : ℝ)) ≤ e₀/4 ∧
    (I.J : ℝ)*Cs*(L : ℝ)^5*Real.exp (-cs*(L : ℝ)) ≤ (zeta d : ℝ)^2/4 :=
  selected_exponential_budgets (sourceInput p S hm) (inputLog S.nnz) (inputLog_pos S.nnz)

#print axioms source_inverse_scales
#print axioms source_tau_bits
#print axioms source_exponential_budgets

end Maxwell.Continuum.Parameters
