import Maxwell.Continuum.ParameterOuterSearch

/-! Quantitative output bounds for the actual first-success encoder. -/

namespace Maxwell.Continuum.Parameters
set_option exponentiation.threshold 4096

 theorem spacing_before_candidate {I : Input} {M e p ℓ k : ℕ} (hI : I.BinaryBudget p ℓ)
    (hM : 4096 ≤ M) (he : e ≤ M) (hp : p ≤ M) (hℓ : 0 < ℓ)
    (hk : k ≤ outerCandidateExponent M ℓ) : stageSpacing I e k ≤ 2^(9*M)*ℓ := by
  have hL : stageLength k ≤ 2^(3*outerCandidateExponent M ℓ) := by
    calc
      _ ≤ 8^outerCandidateExponent M ℓ := Nat.pow_le_pow_right (by decide) hk
      _ = _ := by rw [show (8 : ℕ) = 2^3 by decide, ← pow_mul]
  exact (selectedSpacing_lt_threshold I.K_pos I.epsilon_pos hL hI.K (epsilon_lower_of_binary hI)).le.trans
    (spacingThreshold_candidate_bound hM he hp hℓ)

 theorem buffer_before_candidate {I : Input} {M e p ℓ k : ℕ} (hI : I.BinaryBudget p ℓ)
    (hM : 4096 ≤ M) (he : e ≤ M) (hp : p ≤ M) (hℓ : 0 < ℓ)
    (hk : k ≤ outerCandidateExponent M ℓ) : stageBuffer I e k ≤ 2^(11*M)*ℓ := by
  have hd := spacing_before_candidate hI hM he hp hℓ hk
  have hb := candidate_zero_budget hM he hp hℓ hd
  have hmono : stageBudgetExponent e p ℓ k (stageSpacing I e k) 0+1 ≤
      stageBudgetExponent e p ℓ (outerCandidateExponent M ℓ) (stageSpacing I e k) 0+1 := by
    unfold stageBudgetExponent
    omega
  have ht := (stageBuffer_upper hI e k).le.trans (Nat.mul_le_mul_left (2^2049) (hmono.trans hb))
  calc
    _ ≤ 2^2049*(2^(10*M)*ℓ) := ht
    _ = 2^(2049+10*M)*ℓ := by rw [pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul_right ℓ (Nat.pow_le_pow_right (by decide) (by omega))

/-- The three published asymptotic exponents, with a single explicit fixed
constant for each and with no core error-budget assumption. -/
 theorem selected_scales {I : Input} {M e p base ℓ : ℕ} (hI : I.BinaryBudget p ℓ)
    (hM : 4096 ≤ M) (he : e ≤ M) (hp : p ≤ M) (hb : base ≤ M) (hℓ : 0 < ℓ) :
    let k := selectedOuterExponent I e base ℓ hℓ
    stageLength k ≤ 2^(6+45*M)*ℓ^6 ∧
    stageSpacing I e k ≤ 2^(9*M)*ℓ ∧
    stageBuffer I e k ≤ 2^(11*M)*ℓ ∧
    stageLength k*stageBuffer I e k ≤ 2^(6+56*M)*ℓ^7 := by
  let k := selectedOuterExponent I e base ℓ hℓ
  have hk : k ≤ outerCandidateExponent M ℓ := selectedOuter_le_candidate hI hM he hp hb hℓ
  have hlength : stageLength k ≤ 2^(6+45*M)*ℓ^6 := by
    have hl := (Nat.pow_le_pow_right (by decide : 1 ≤ 8) hk).trans (outerCandidate_upper hℓ).le
    convert hl using 1
    · rfl
    · rw [show (8 : ℕ) = 2^3 by decide, ← pow_mul, pow_add]
      ring
  have hd := spacing_before_candidate hI hM he hp hℓ hk
  have ht := buffer_before_candidate hI hM he hp hℓ hk
  refine ⟨hlength, hd, ht, ?_⟩
  have hm := Nat.mul_le_mul hlength ht
  convert hm using 1
  rw [show 6+56*M = (6+45*M)+11*M by omega, pow_add, show ℓ^7 = ℓ^6*ℓ by rw [pow_succ]]
  ring

 theorem bits_le_polynomial_scale {n a r ℓ : ℕ} (hn : n ≤ 2^a*ℓ^r) :
    n.bits.length ≤ a+r*ℓ+1 := by
  have hℓ : ℓ ≤ 2^ℓ := (Nat.lt_two_pow_self (n := ℓ)).le
  have hp : n ≤ 2^(a+r*ℓ) := by
    calc
      _ ≤ 2^a*ℓ^r := hn
      _ ≤ 2^a*(2^ℓ)^r := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hℓ r)
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; ring
  have hh := Nat.size_le_size hp
  rw [Nat.size_pow] at hh
  simpa only [Nat.size_eq_bits_len] using hh

 theorem selected_bits {I : Input} {M e p base ℓ : ℕ} (hI : I.BinaryBudget p ℓ)
    (hM : 4096 ≤ M) (he : e ≤ M) (hp : p ≤ M) (hb : base ≤ M) (hℓ : 0 < ℓ) :
    let k := selectedOuterExponent I e base ℓ hℓ
    (stageLength k).bits.length ≤ 45*M+6*ℓ+7 ∧
    (stageSpacing I e k).bits.length ≤ 9*M+ℓ+1 ∧
    (stageBuffer I e k).bits.length ≤ 11*M+ℓ+1 ∧
    (stageLength k*stageBuffer I e k).bits.length ≤ 56*M+7*ℓ+7 := by
  have hs := selected_scales hI hM he hp hb hℓ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hh := bits_le_polynomial_scale hs.1
    omega
  · simpa only [Nat.one_mul] using bits_le_polynomial_scale (r := 1)
      (by simpa only [pow_one] using hs.2.1)
  · simpa only [Nat.one_mul] using bits_le_polynomial_scale (r := 1)
      (by simpa only [pow_one] using hs.2.2.1)
  · have hh := bits_le_polynomial_scale hs.2.2.2
    omega

#print axioms selected_scales
#print axioms selected_bits

end Maxwell.Continuum.Parameters
