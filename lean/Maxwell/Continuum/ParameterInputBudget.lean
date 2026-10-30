import Maxwell.Continuum.ParameterStage

/-! Every finite rational input admits an explicit binary analysis budget.
This lemma proves unconditional termination; fixed-promise bounds later
replace this input-dependent witness in the resource theorem. -/

namespace Maxwell.Continuum.Parameters
open scoped BigOperators

 def Input.binarySize (I : Input) : ℕ :=
  I.m+I.J+(∑ j, I.span j)+rationalUpperBits I.K+rationalUpperBits I.epsilon⁻¹+1

 theorem Input.binarySize_budget (I : Input) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    I.BinaryBudget I.binarySize ℓ := by
  have hmul : I.binarySize ≤ I.binarySize*ℓ := Nat.le_mul_of_pos_right _ hℓ
  have hm : I.m ≤ I.binarySize := by unfold Input.binarySize; omega
  have hJ : I.J ≤ I.binarySize := by unfold Input.binarySize; omega
  have hK : rationalUpperBits I.K ≤ I.binarySize := by unfold Input.binarySize; omega
  have hε : rationalUpperBits I.epsilon⁻¹ ≤ I.binarySize := by unfold Input.binarySize; omega
  have hs (j : Fin 3) : I.span j ≤ I.binarySize := by
    have hh : I.span j ≤ ∑ j, I.span j := Finset.single_le_sum (fun _ _ => by omega) (Finset.mem_univ _)
    unfold Input.binarySize
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (nat_binary_self I.m).trans (pow_le_pow_right₀ (by norm_num) (hm.trans hmul))
  · exact (nat_binary_self I.J).trans (pow_le_pow_right₀ (by norm_num) (hJ.trans hmul))
  · intro j
    exact (nat_binary_self (I.span j)).trans (pow_le_pow_right₀ (by norm_num) ((hs j).trans hmul))
  · exact (rationalUpperBits_spec I.K).trans (pow_le_pow_right₀ (by norm_num) (hK.trans hmul))
  · exact (rationalUpperBits_spec I.epsilon⁻¹).trans (pow_le_pow_right₀ (by norm_num) (hε.trans hmul))

 theorem Input.BinaryBudget.mono {I : Input} {p q ℓ : ℕ} (hI : I.BinaryBudget p ℓ) (hpq : p ≤ q) :
    I.BinaryBudget q ℓ := by
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (Nat.mul_le_mul_right ℓ hpq)
  exact ⟨hI.m.trans hp, hI.J.trans hp, fun j => (hI.span j).trans hp, hI.K.trans hp, hI.epsilon.trans hp⟩

end Maxwell.Continuum.Parameters
