import Maxwell.Continuum.ParameterResources

/-! The selected inverse scales and error budgets are polynomial in the
source size, proved directly from their rational formulas. -/

namespace Maxwell.Continuum.Parameters
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000

private theorem component_exponents (e p ℓ k d t : ℕ) :
    1026+3*d ≤ stageBudgetExponent e p ℓ k d t ∧
    25+4*(3*k)+4*d ≤ stageBudgetExponent e p ℓ k d t ∧
    6+p*ℓ+stageCountExponent p ℓ k d t+(25+4*(3*k)+4*d) ≤ stageBudgetExponent e p ℓ k d t ∧
    27+(6+p*ℓ+stageCountExponent p ℓ k d t+(25+4*(3*k)+4*d))+p*ℓ ≤ stageBudgetExponent e p ℓ k d t ∧
    globalExponent e (p*ℓ) (p*ℓ) (stageCountExponent p ℓ k d t) (p*ℓ) (1026+3*d) (3*k) ≤
      stageBudgetExponent e p ℓ k d t := by
  unfold stageBudgetExponent stageCountExponent globalExponent
  rw [Nat.mul_assoc 19 p ℓ, Nat.mul_assoc 3 p ℓ]
  omega

theorem stage_numeric_budgets {I : Input} {p ℓ : ℕ} (hI : I.BinaryBudget p ℓ) (e k t : ℕ) :
    let L := stageLength k
    let d := stageSpacing I e k
    let N := boxCount (stageSpan I e k) L t
    let E := stageBudgetExponent e p ℓ k d t
    (alpha L d)⁻¹ ≤ (2 : ℚ)^E ∧ (stageTau I e k)⁻¹ ≤ (2 : ℚ)^E ∧
    inverseBudget I.m N (stageTau I e k) ≤ (2 : ℚ)^E ∧
    (errorBudget I.m N I.epsilon (stageTau I e k))⁻¹ ≤ (2 : ℚ)^E ∧
    globalBudget e I.J I.m N L d I.K ≤ (2 : ℚ)^E := by
  have hL := (stageLength_binary k).le
  have hα := alpha_inverse_binary (stageLength_pos k) (stageSpacing I e k)
  have hτ := tau_inverse_binary (stageLength_pos k)
    (show stageLength k ≤ 2^(3*k) by exact_mod_cast hL) (stageSpacing I e k)
  have hN := stageCount_binary hI e k t
  have hLb := binary_mul
    (binary_mul (binary_mul (show (64 : ℚ) ≤ 2^6 by norm_num) hI.m (Nat.cast_nonneg I.m))
      hN (Nat.cast_nonneg _)) hτ (inv_nonneg.mpr (stageTau_pos I e k).le)
  change 64*(I.m : ℚ)*(boxCount (stageSpan I e k) (stageLength k) t : ℚ)*(stageTau I e k)⁻¹ ≤ _ at hLb
  rw [← div_eq_mul_inv] at hLb
  change inverseBudget I.m (boxCount (stageSpan I e k) (stageLength k) t) (stageTau I e k) ≤ _ at hLb
  have he₀ := binary_mul (binary_mul (le_refl ((2 : ℚ)^27)) hLb
    (inverseBudget_pos I.m_pos (boxCount_pos _ _ _) (stageTau_pos I e k)).le)
    hI.epsilon (inv_nonneg.mpr I.epsilon_pos.le)
  have hXi := globalBudget_binary hI.J hI.m hN hL I.K_pos.le hI.K hα (e := e)
  have hE := component_exponents e p ℓ k (stageSpacing I e k) t
  refine ⟨hα.trans (pow_le_pow_right₀ (by norm_num) hE.1),
    hτ.trans (pow_le_pow_right₀ (by norm_num) hE.2.1),
    hLb.trans (pow_le_pow_right₀ (by norm_num) hE.2.2.1), ?_,
    hXi.trans (pow_le_pow_right₀ (by norm_num) hE.2.2.2.2)⟩
  have he := he₀.trans (pow_le_pow_right₀ (by norm_num) hE.2.2.2.1)
  rw [errorBudget, inv_div, div_eq_mul_inv]
  exact he

theorem selected_budget_exponent {I : Input} {M e p base ℓ : ℕ} (hI : I.BinaryBudget p ℓ)
    (hM : 4096 ≤ M) (he : e ≤ M) (hp : p ≤ M) (hb : base ≤ M) (hℓ : 0 < ℓ) :
    let k := selectedOuterExponent I e base ℓ hℓ
    stageBudgetExponent e p ℓ k (stageSpacing I e k) (stageBuffer I e k) ≤ 2^(12*M)*ℓ := by
  have hk := selectedOuter_le_candidate hI hM he hp hb hℓ
  have hs := selected_scales hI hM he hp hb hℓ
  have hh := candidate_final_budget hM he hp hℓ hs.2.1 hs.2.2.1
  apply le_trans _ hh
  unfold stageBudgetExponent
  omega

theorem binary_inputLog_le_polynomial (m a : ℕ) :
    (2 : ℚ)^(a*inputLog m) ≤ (m+2 : ℚ)^(3*a) := by
  have hm : 0 < m+2 := by omega
  have hpow : (2 : ℕ)^Nat.clog 2 (m+2) < 2*(m+2) := powerCeiling_upper (by decide) hm
  have hbase : (2 : ℕ)^inputLog m ≤ 4*(m+2) := by
    unfold inputLog
    rw [pow_add, pow_one]
    omega
  have hcube : 4*(m+2) ≤ (m+2)^3 := by
    have hs : 4 ≤ (m+2)^2 := Nat.pow_le_pow_left (by omega : 2 ≤ m+2) 2
    simpa only [pow_succ] using Nat.mul_le_mul_right (m+2) hs
  have hq : (2 : ℚ)^inputLog m ≤ (m+2 : ℚ)^3 := by exact_mod_cast hbase.trans hcube
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℚ) ≤ 2^inputLog m) hq a
  simpa only [← pow_mul, Nat.mul_comm (inputLog m) a] using hp

#print axioms stage_numeric_budgets
#print axioms selected_budget_exponent
#print axioms binary_inputLog_le_polynomial

end Maxwell.Continuum.Parameters
